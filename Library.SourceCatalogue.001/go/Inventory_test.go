// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"archive/zip"
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

// WriteFixture constructs only temporary test data, never the research source tree.
func WriteFixture(t *testing.T, root, rel, content string) {
	t.Helper()
	name := filepath.Join(root, rel)
	if err := os.MkdirAll(filepath.Dir(name), 0755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(name, []byte(content), 0644); err != nil {
		t.Fatal(err)
	}
}

// TestDiscoverExclusions checks that caches and symlinks are recorded without traversal.
func TestDiscoverExclusions(t *testing.T) {
	root := t.TempDir()
	WriteFixture(t, root, "Readable.md", "argument")
	WriteFixture(t, root, ".pi/Private.md", "must not be read")
	WriteFixture(t, root, "Nested/__pycache__/Cache.pyc", "must not be read")
	if err := os.Symlink(filepath.Join(root, "Readable.md"), filepath.Join(root, "Link")); err != nil {
		t.Fatal(err)
	}
	artifacts, exclusions, err := Discover(root)
	if err != nil {
		t.Fatal(err)
	}
	if len(artifacts) != 1 || artifacts[0].Path != "Readable.md" || len(exclusions) != 3 {
		t.Fatalf("unexpected scope: %+v; exclusions=%+v", artifacts, exclusions)
	}
}

// TestHashArtifacts checks disjoint worker results, equal-hash groups, and empty files.
func TestHashArtifacts(t *testing.T) {
	root := t.TempDir()
	WriteFixture(t, root, "A.md", "same bytes")
	WriteFixture(t, root, "B.md", "same bytes")
	WriteFixture(t, root, "Empty.log", "")
	artifacts, _, err := Discover(root)
	if err != nil {
		t.Fatal(err)
	}
	if err := HashArtifacts(root, artifacts, 4); err != nil {
		t.Fatal(err)
	}
	groups, duplicates, extras := GroupArtifacts(artifacts)
	if len(groups) != 2 || duplicates != 1 || extras != 1 {
		t.Fatalf("wrong duplicate counts: %d %d %d", len(groups), duplicates, extras)
	}
	if artifacts[0].SHA256 != artifacts[1].SHA256 || artifacts[0].Bytes != 10 {
		t.Fatalf("wrong hashes or sizes: %+v", artifacts)
	}
	if err := HashArtifacts(root, artifacts, 0); err == nil {
		t.Fatal("accepted zero workers")
	}
	w := NewWorkspace(0, 0)
	if err := os.Symlink(filepath.Join(root, "A.md"), filepath.Join(root, "Link")); err != nil {
		t.Fatal(err)
	}
	if _, _, err := w.HashFile(filepath.Join(root, "Link")); err == nil {
		t.Fatal("followed a symlink")
	}
}

// TestMemberNames checks exclusions independently of whether extraction is attempted.
func TestMemberNames(t *testing.T) {
	bad := []string{"", "/Absolute", "../Escape", "A/../B", "A\\B", "C:File", "A\x00B"}
	for _, name := range bad {
		if SafeMemberName(name) {
			t.Errorf("accepted unsafe name %q", name)
		}
	}
	for _, name := range []string{"README.md", "collatz/A B.md", "Nested/File.json"} {
		if !SafeMemberName(name) {
			t.Errorf("rejected safe name %q", name)
		}
	}
	for _, name := range []string{"Paper.pdf", "A/.pi/Session.json", "A/target/Program"} {
		if !PrivateMember(name) {
			t.Errorf("opened excluded payload %q", name)
		}
	}
	if PrivateMember("research/papers/recovered/irrational-boundaries.pdf") {
		t.Fatal("excluded the relevant recovered research paper")
	}
}

// ZIPFixture creates duplicate names and unsafe/private controls inside a temporary ZIP.
func ZIPFixture(t *testing.T, root string) {
	t.Helper()
	f, err := os.Create(filepath.Join(root, "Bundle.zip"))
	if err != nil {
		t.Fatal(err)
	}
	writer := zip.NewWriter(f)
	rows := []struct{ name, content string }{
		{"A.md", "proof"}, {"A.md", "second occurrence"},
		{"../Escape.md", "unsafe"}, {"Paper.pdf", "unrelated"},
	}
	for _, row := range rows {
		w, err := writer.Create(row.name)
		if err != nil {
			t.Fatal(err)
		}
		if _, err := w.Write([]byte(row.content)); err != nil {
			t.Fatal(err)
		}
	}
	if err := writer.Close(); err != nil {
		t.Fatal(err)
	}
	if err := f.Close(); err != nil {
		t.Fatal(err)
	}
}

// FixtureArtifact records the exact current container bytes for archive acceptance tests.
func FixtureArtifact(t *testing.T, root, name string) Artifact {
	t.Helper()
	w := NewWorkspace(0, 0)
	digest, size, err := w.HashFile(filepath.Join(root, name))
	if err != nil {
		t.Fatal(err)
	}
	return Artifact{Path: name, SHA256: digest, Bytes: size}
}

// TestZIPScope checks content matching, occurrence preservation and fail-closed byte caps.
func TestZIPScope(t *testing.T) {
	root := t.TempDir()
	ZIPFixture(t, root)
	digestBytes := sha256.Sum256([]byte("proof"))
	digest := hex.EncodeToString(digestBytes[:])
	groups := map[string][]string{digest: {"Current.md"}}
	a := FixtureArtifact(t, root, "Bundle.zip")
	w := NewWorkspace(1024, 2048)
	rows, err := w.ReadZIP(root, a, groups)
	if err != nil {
		t.Fatal(err)
	}
	if len(rows) != 4 || rows[0].Occurrence != 1 || rows[1].Occurrence != 2 {
		t.Fatalf("lost a member identity: %+v", rows)
	}
	if !reflect.DeepEqual(rows[0].MatchingCurrentPaths, []string{"Current.md"}) {
		t.Fatalf("content match failed: %+v", rows[0])
	}
	if rows[2].Kind != "unsafe-path" || rows[3].Kind != "excluded-payload" {
		t.Fatalf("wrong exclusion dispositions: %+v", rows)
	}
	if rows[2].SHA256 != "" || rows[3].SHA256 != "" || w.archiveBytes != 22 {
		t.Fatalf("opened an excluded member or counted wrong bytes: %+v", rows)
	}
	limited := NewWorkspace(4, 2048)
	if _, err := limited.ReadZIP(root, a, groups); err == nil {
		t.Fatal("silently accepted a member over the budget")
	}
	cumulative := NewWorkspace(1024, 21)
	if _, err := cumulative.ReadZIP(root, a, groups); err == nil {
		t.Fatal("silently accepted individually small members over the total budget")
	}
}

// TestZIPCRC forces a checksum failure instead of accepting a central-directory hash.
func TestZIPCRC(t *testing.T) {
	root := t.TempDir()
	var raw bytes.Buffer
	writer := zip.NewWriter(&raw)
	header := &zip.FileHeader{Name: "A.md", Method: zip.Store}
	w, err := writer.CreateHeader(header)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := w.Write([]byte("unique-payload")); err != nil {
		t.Fatal(err)
	}
	if err := writer.Close(); err != nil {
		t.Fatal(err)
	}
	payload := raw.Bytes()
	i := bytes.Index(payload, []byte("unique-payload"))
	if i < 0 {
		t.Fatal("missing control payload")
	}
	payload[i] ^= 1
	if err := os.WriteFile(filepath.Join(root, "Bad.zip"), payload, 0644); err != nil {
		t.Fatal(err)
	}
	workspace := NewWorkspace(1024, 2048)
	_, err = workspace.ReadZIP(root, FixtureArtifact(t, root, "Bad.zip"), nil)
	if err == nil || !strings.Contains(err.Error(), "checksum error") {
		t.Fatalf("CRC corruption was not rejected: %v", err)
	}
}

// RawZIPFixture preserves a supplied CRC without adding a data descriptor.
func RawZIPFixture(t *testing.T, root string, payload []byte, checksum uint32) {
	t.Helper()
	var raw bytes.Buffer
	writer := zip.NewWriter(&raw)
	header := &zip.FileHeader{
		Name: "A.md", Method: zip.Store, CRC32: checksum,
		CompressedSize64: uint64(len(payload)), UncompressedSize64: uint64(len(payload)),
	}
	member, err := writer.CreateRaw(header)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := member.Write(payload); err != nil {
		t.Fatal(err)
	}
	if err := writer.Close(); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(root, "Raw.zip"), raw.Bytes(), 0644); err != nil {
		t.Fatal(err)
	}
}

// TestZIPZeroCRC covers the no-descriptor bypass and legitimate zero CRCs.
func TestZIPZeroCRC(t *testing.T) {
	cases := []struct {
		name     string
		payload  []byte
		checksum uint32
		valid    bool
	}{
		{"zero recorded CRC on nonempty payload", []byte("a"), 0, false},
		{"valid empty payload", nil, 0, true},
		{"valid nonempty payload", []byte("a"), 0xe8b7be43, true},
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			root := t.TempDir()
			RawZIPFixture(t, root, test.payload, test.checksum)
			reader, err := zip.OpenReader(filepath.Join(root, "Raw.zip"))
			if err != nil {
				t.Fatal(err)
			}
			if len(reader.File) != 1 || reader.File[0].Flags&8 != 0 ||
				reader.File[0].CRC32 != test.checksum {
				t.Fatal("fixture lost its no-descriptor CRC header")
			}
			if err := reader.Close(); err != nil {
				t.Fatal(err)
			}
			workspace := NewWorkspace(1024, 2048)
			// A repeated read checks checksum reset as well as the first acceptance.
			for pass := 0; pass < 2; pass++ {
				rows, err := workspace.ReadZIP(root, FixtureArtifact(t, root, "Raw.zip"), nil)
				if !test.valid {
					if err == nil || !strings.Contains(err.Error(), "checksum error") ||
						workspace.archiveBytes != 0 {
						t.Fatalf("accepted a corrupt zero CRC or counted its bytes: %v", err)
					}
					continue
				}
				if err != nil {
					t.Fatal(err)
				}
				digest := sha256.Sum256(test.payload)
				if len(rows) != 1 || rows[0].SHA256 != hex.EncodeToString(digest[:]) ||
					workspace.archiveBytes != uint64((pass+1)*len(test.payload)) {
					t.Fatalf("incorrect accepted payload evidence: %+v", rows)
				}
			}
		})
	}
}

// Test7zListing distinguishes headers from contents and retains directory entries.
func Test7zListing(t *testing.T) {
	listing := "Path = Container.7z\nSize = 100\n\n----------\n" +
		"Path = Folder\nSize = 0\nAttributes = D\nFolder = +\n\n" +
		"Path = Folder/A.md\nSize = 5\nCRC = ABCD0123\n\n" +
		"Path = Folder/A.md\nSize = 6\nCRC = DCBA3210\n"
	rows, err := Parse7zListing(listing, "Container.7z", "hash")
	if err != nil {
		t.Fatal(err)
	}
	if len(rows) != 3 || rows[0].Kind != "directory" || rows[2].Occurrence != 2 {
		t.Fatalf("incorrect 7z headers: %+v", rows)
	}
	for _, row := range rows {
		if row.SHA256 != "" || !strings.Contains(row.Inspection, "header-only") {
			t.Fatal("header listing promoted to content evidence")
		}
	}
	if _, err := Parse7zListing("not a listing", "Bad.7z", "hash"); err == nil {
		t.Fatal("accepted a missing member section")
	}
	badSize := "----------\nPath = A\nSize = invalid\n"
	if _, err := Parse7zListing(badSize, "Bad.7z", "hash"); err == nil {
		t.Fatal("accepted an invalid member size")
	}
}

// TestCompare checks stable sorted deltas instead of relying on map iteration order.
func TestCompare(t *testing.T) {
	current := map[string]string{"Same": "a", "Changed": "b", "Added": "c"}
	old := map[string]string{"Same": "a", "Changed": "x", "Missing": "z"}
	got := Compare(current, old)
	want := Comparison{1, []string{"Added"}, []string{"Changed"}, []string{"Missing"}}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("comparison mismatch: got %+v want %+v", got, want)
	}
}

// TestReadJSON rejects a path escape and trailing documents before trusting metadata.
func TestReadJSON(t *testing.T) {
	root := t.TempDir()
	WriteFixture(t, root, "Good.json", "[1,2]")
	WriteFixture(t, root, "Bad.json", "[1,2] [3]")
	var output []int
	if err := ReadJSON(root, "Good.json", &output); err != nil {
		t.Fatal(err)
	}
	if err := ReadJSON(root, "Bad.json", &output); err == nil {
		t.Fatal("accepted trailing JSON")
	}
	if err := ReadJSON(root, "../Escape.json", &output); err == nil {
		t.Fatal("accepted an escaping metadata path")
	}
}

// TestReadJSONNoAliases rejects leaf and ancestor aliases before consuming external metadata.
func TestReadJSONNoAliases(t *testing.T) {
	root, external := t.TempDir(), t.TempDir()
	WriteFixture(t, external, "External.json", "[1]")
	WriteFixture(t, root, ".pi/Private.json", "[2]")
	links := []struct{ path, target string }{
		{"Leaf.json", filepath.Join(external, "External.json")},
		{"Outside", external},
		{"PrivateAlias", filepath.Join(root, ".pi")},
	}
	for _, link := range links {
		if err := os.Symlink(link.target, filepath.Join(root, link.path)); err != nil {
			t.Fatal(err)
		}
	}
	if err := os.Mkdir(filepath.Join(root, "Directory.json"), 0755); err != nil {
		t.Fatal(err)
	}
	for _, rel := range []string{
		"Leaf.json", "Outside/External.json", "PrivateAlias/Private.json",
		".pi/Private.json", "Directory.json",
	} {
		var output []int
		if err := ReadJSON(root, rel, &output); err == nil {
			t.Errorf("accepted excluded or nonregular metadata: %s", rel)
		}
	}
	WriteFixture(t, root, "Allowed/Nested/Metadata.json", "[3]")
	var output []int
	if err := ReadJSON(root, "Allowed/Nested/Metadata.json", &output); err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(output, []int{3}) {
		t.Fatalf("wrong permitted metadata: %+v", output)
	}
}

// TestOriginalRecordPreservation retains the historical digest and future unknown schema fields.
func TestOriginalRecordPreservation(t *testing.T) {
	input := `{"path":"Cache.pyc","bytes":9,"sha256":"original",` +
		`"precleanup_current_sha256":"refreshed","future_provenance":{"revision":4}}`
	var record OriginalArtifact
	if err := json.Unmarshal([]byte(input), &record); err != nil {
		t.Fatal(err)
	}
	if record.PrecleanupCurrentSHA256 != "refreshed" ||
		string(record.HistoricalFields["future_provenance"]) != `{"revision":4}` {
		t.Fatalf("historical information lost: %+v", record)
	}
	encoded, err := json.Marshal(record)
	if err != nil {
		t.Fatal(err)
	}
	var roundTrip OriginalArtifact
	if err := json.Unmarshal(encoded, &roundTrip); err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(record, roundTrip) {
		t.Fatalf("round-trip information loss: %+v versus %+v", record, roundTrip)
	}
}

// ReconcileFixture supplies complete temporary manifests for reconciliation controls.
func ReconcileFixture(t *testing.T) (string, []Artifact) {
	t.Helper()
	root := t.TempDir()
	input := `[{"path":"Old.txt","target":"Active.txt","bytes":3,` +
		`"sha256":"old","action":"moved","precleanup_current_sha256":"prior"},` +
		`{"path":"Removed.txt","target":"/external/not-accessed","bytes":4,` +
		`"sha256":"external","action":"external-backup"}]`
	WriteFixture(t, root, "artifacts/organization/original-file-manifest.json", input)
	WriteFixture(t, root, "artifacts/organization/source-modifications.json",
		`[{"active_path":"Active.txt","current_sha256":"new","reason":"declared repair"}]`)
	WriteFixture(t, root, "artifacts/organization/tree-catalog.json",
		`[{"path":"Active.txt","bytes":3,"sha256":"old"}]`)
	WriteFixture(t, root, "artifacts/organization/zip-members.json",
		`[{"archive":"/external/Archive.zip","member":"Old.txt","bytes":3,"sha256":"old"}]`)
	WriteFixture(t, root, "artifacts/exports/collatz-progress-20261002T231927Z.manifest.json",
		`{"workspace_files":1,"supplemental_files":0,"files":[`+
			`{"kind":"workspace","workspace_path":"Active.txt","sha256":"old"}]}`)
	artifacts := []Artifact{{Path: "Active.txt", SHA256: "new", Bytes: 3}}
	return root, artifacts
}

// TestReconcileFixture checks declared repairs, external metadata and rejection of hidden changes.
func TestReconcileFixture(t *testing.T) {
	root, artifacts := ReconcileFixture(t)
	var summary Summary
	originals, historical, err := Reconcile(root, artifacts, &summary)
	if err != nil {
		t.Fatal(err)
	}
	if summary.OriginalActive != 1 || summary.OriginalExternal != 1 ||
		summary.ModificationRecords != 1 || len(summary.OriginalDeclaredDelta) != 1 {
		t.Fatalf("incorrect reconciliation: %+v", summary)
	}
	if originals[0].PrecleanupCurrentSHA256 != "prior" || originals[1].CurrentSHA256 != "" ||
		!strings.Contains(historical[0].Inspection, "not accessed") {
		t.Fatalf("incorrect historical/external evidence: %+v %+v", originals, historical)
	}
	if !reflect.DeepEqual(summary.Catalog.Changed, []string{"Active.txt"}) ||
		!reflect.DeepEqual(summary.Export.Changed, []string{"Active.txt"}) {
		t.Fatalf("missing deltas: %+v", summary)
	}
	WriteFixture(t, root, "artifacts/organization/source-modifications.json", "[]")
	var badSummary Summary
	if _, _, err := Reconcile(root, artifacts, &badSummary); err == nil {
		t.Fatal("accepted an undeclared original change")
	}
}

// TestReconcilePathIdentity rejects rows that a map would silently overwrite or omit.
func TestReconcilePathIdentity(t *testing.T) {
	cases := []struct {
		name, path, content, message string
	}{
		{"current", "", "", "duplicate current artifact path"},
		{"original", "artifacts/organization/original-file-manifest.json",
			`[{"path":"Old.txt","target":"Active.txt","sha256":"new","action":"moved"},` +
				`{"path":"Old.txt","target":"Active.txt","sha256":"new","action":"moved"}]`,
			"duplicate original artifact path"},
		{"modification", "artifacts/organization/source-modifications.json",
			`[{"active_path":"Active.txt","current_sha256":"new"},` +
				`{"active_path":"Active.txt","current_sha256":"new"}]`,
			"duplicate modification path"},
		{"missing-modification", "artifacts/organization/source-modifications.json",
			`[{"active_path":"Missing.txt","current_sha256":""}]`,
			"declared modification hash mismatch"},
		{"catalogue", "artifacts/organization/tree-catalog.json",
			`[{"path":"Active.txt","sha256":"old"},{"path":"Active.txt","sha256":"old"}]`,
			"duplicate historical catalogue path"},
		{"export", "artifacts/exports/collatz-progress-20261002T231927Z.manifest.json",
			`{"workspace_files":1,"files":[` +
				`{"kind":"workspace","workspace_path":"Active.txt","sha256":"old"},` +
				`{"kind":"workspace","workspace_path":"Active.txt","sha256":"old"}]}`,
			"duplicate export workspace path"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			root, artifacts := ReconcileFixture(t)
			if c.path == "" {
				artifacts = append(artifacts, artifacts[0])
			} else {
				WriteFixture(t, root, c.path, c.content)
			}
			var summary Summary
			_, _, err := Reconcile(root, artifacts, &summary)
			if err == nil || !strings.Contains(err.Error(), c.message) {
				t.Fatalf("path-identity corruption was not rejected: %v", err)
			}
		})
	}
}

// TestRunSourceProtection prevents the most direct accidental write into the source.
func TestRunSourceProtection(t *testing.T) {
	root := t.TempDir()
	if err := Run(root, root, 1, 1024, 2048); err == nil {
		t.Fatal("accepted source-root output")
	}
	if err := Run(root, filepath.Join(root, "Generated"), 1, 1024, 2048); err == nil {
		t.Fatal("accepted output beneath the source")
	}
	outside := t.TempDir()
	link := filepath.Join(outside, "SourceAlias")
	if err := os.Symlink(root, link); err != nil {
		t.Fatal(err)
	}
	if err := Run(root, filepath.Join(link, "Generated"), 1, 1024, 2048); err == nil {
		t.Fatal("accepted a symlinked output beneath the source")
	}
	resolved, err := ResolveOutput(filepath.Join(outside, "New", "Evidence"))
	if err != nil || resolved != filepath.Join(outside, "New", "Evidence") {
		t.Fatalf("failed to resolve a new safe output: %s %v", resolved, err)
	}
}
