// SPDX-License-Identifier: CC-BY-4.0
// Inventory records byte provenance without treating hashes as mathematical verification.
package main

import (
	"archive/zip"
	"bufio"
	"bytes"
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"hash"
	"hash/crc32"
	"io"
	"io/fs"
	"os"
	"os/exec"
	"path"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
)

const (
	MaxContainerBytes int64 = 1 << 30
	MaxListingBytes         = 32 << 20
	ListingTimeout          = 2 * time.Minute
)

// Artifact identifies one current file; reading and theorem status are separate ledgers.
type Artifact struct {
	Path             string   `json:"path"`
	Bytes            int64    `json:"bytes"`
	SHA256           string   `json:"sha256"`
	EqualBytePaths   []string `json:"equal_byte_paths,omitempty"`
	Inspection       string   `json:"inspection"`
	ResultAssignment string   `json:"result_assignment"`
}

// Exclusion records a deliberately unvisited cache, symlink, or nonregular object.
type Exclusion struct {
	Path   string `json:"path"`
	Reason string `json:"reason"`
}

// ArchiveMember retains occurrence numbers, since member names need not be unique.
type ArchiveMember struct {
	Archive              string   `json:"archive"`
	ArchiveSHA256        string   `json:"archive_sha256"`
	Member               string   `json:"member"`
	Occurrence           int      `json:"occurrence"`
	Bytes                uint64   `json:"bytes"`
	CRC32                string   `json:"crc32,omitempty"`
	SHA256               string   `json:"sha256,omitempty"`
	Kind                 string   `json:"kind"`
	Inspection           string   `json:"inspection"`
	MatchingCurrentPaths []string `json:"matching_current_paths,omitempty"`
	ResultAssignment     string   `json:"result_assignment"`
}

// OriginalArtifact preserves the historical record and adds only current-byte evidence.
type OriginalArtifact struct {
	Path                    string                     `json:"path"`
	Bytes                   int64                      `json:"bytes"`
	SHA256                  string                     `json:"sha256"`
	Action                  string                     `json:"action"`
	Target                  *string                    `json:"target"`
	Reason                  string                     `json:"reason"`
	BackupArchive           string                     `json:"backup_archive"`
	BackupMember            string                     `json:"backup_member"`
	Completed               bool                       `json:"completed"`
	PrecleanupCurrentSHA256 string                     `json:"precleanup_current_sha256,omitempty"`
	CurrentSHA256           string                     `json:"current_sha256,omitempty"`
	CurrentEvidence         string                     `json:"current_evidence"`
	HistoricalFields        map[string]json.RawMessage `json:"additional_historical_fields,omitempty"`
}

// UnmarshalJSON retains unknown original-record fields instead of silently dropping provenance.
func (o *OriginalArtifact) UnmarshalJSON(data []byte) error {
	type Record OriginalArtifact
	var record Record
	if err := json.Unmarshal(data, &record); err != nil {
		return err
	}
	var fields map[string]json.RawMessage
	if err := json.Unmarshal(data, &fields); err != nil {
		return err
	}
	known := []string{
		"path", "bytes", "sha256", "action", "target", "reason", "backup_archive",
		"backup_member", "completed", "precleanup_current_sha256", "current_sha256",
		"current_evidence", "additional_historical_fields",
	}
	for _, key := range known {
		delete(fields, key)
	}
	if len(fields) > 0 {
		if record.HistoricalFields == nil {
			record.HistoricalFields = make(map[string]json.RawMessage, len(fields))
		}
		for key, value := range fields {
			record.HistoricalFields[key] = value
		}
	}
	*o = OriginalArtifact(record)
	return nil
}

// Modification is a source-declared repair, not a certificate of semantic equivalence.
type Modification struct {
	ActivePath    string `json:"active_path"`
	CurrentSHA256 string `json:"current_sha256"`
	Reason        string `json:"reason"`
}

// HistoricalMember retains metadata about archives unavailable in the current tree.
type HistoricalMember struct {
	Archive     string `json:"archive"`
	Member      string `json:"member"`
	Bytes       int64  `json:"bytes"`
	SHA256      string `json:"sha256"`
	DuplicateOf string `json:"duplicate_of"`
	Inspection  string `json:"inspection"`
}

// ExportFile is a row of the earlier export, whose workspace is not the current corpus.
type ExportFile struct {
	ArchivePath   string `json:"archive_path"`
	WorkspacePath string `json:"workspace_path"`
	Kind          string `json:"kind"`
	SHA256        string `json:"sha256"`
}

// ExportManifest supplies the historical scope and the rows needed for comparison.
type ExportManifest struct {
	WorkspaceFiles    int          `json:"workspace_files"`
	SupplementalFiles int          `json:"supplemental_files"`
	Files             []ExportFile `json:"files"`
}

// Comparison records exact paths rather than hiding mismatches inside totals.
type Comparison struct {
	Unchanged int      `json:"unchanged"`
	Added     []string `json:"added"`
	Changed   []string `json:"changed"`
	Missing   []string `json:"missing"`
}

// Summary states the scanner's finite scope and expressly excludes semantic conclusions.
type Summary struct {
	Format                string      `json:"format"`
	SourceRoot            string      `json:"source_root"`
	Files                 int         `json:"files"`
	Bytes                 int64       `json:"bytes"`
	DistinctSHA256        int         `json:"distinct_sha256"`
	DuplicateGroups       int         `json:"duplicate_groups"`
	DuplicateExtraCopies  int         `json:"duplicate_extra_copies"`
	Exclusions            []Exclusion `json:"exclusions"`
	CurrentZIPMembers     int         `json:"current_zip_file_members"`
	Current7zMembers      int         `json:"current_7z_file_members"`
	ZIPMemberBytesHashed  uint64      `json:"zip_member_bytes_hashed"`
	OriginalActive        int         `json:"original_active"`
	OriginalExternal      int         `json:"original_external"`
	OriginalDeclaredDelta []string    `json:"original_declared_delta"`
	ModificationRecords   int         `json:"modification_records_checked"`
	Catalog               Comparison  `json:"current_vs_tree_catalog"`
	Export                Comparison  `json:"current_vs_export_workspace"`
	Limitations           []string    `json:"limitations"`
}

// Workspace owns reusable hashing buffers and the bounded archive byte budget.
type Workspace struct {
	buffer       []byte
	hasher       hash.Hash
	checksum     uint32
	archiveBytes uint64
	maxMember    uint64
	maxArchive   uint64
}

// NewWorkspace allocates working memory once, outside file and member loops.
func NewWorkspace(maxMember, maxArchive uint64) *Workspace {
	return &Workspace{
		buffer: make([]byte, 128*1024), hasher: sha256.New(),
		maxMember: maxMember, maxArchive: maxArchive,
	}
}

// Write keeps SHA-256 and IEEE CRC on the same accepted bytes without a per-stream writer.
func (w *Workspace) Write(p []byte) (int, error) {
	n, err := w.hasher.Write(p)
	w.checksum = crc32.Update(w.checksum, crc32.IEEETable, p[:n])
	return n, err
}

// HashReader resets both accumulators and consumes the stream completely.
func (w *Workspace) HashReader(r io.Reader) (string, int64, error) {
	w.hasher.Reset()
	w.checksum = 0
	n, err := io.CopyBuffer(w, r, w.buffer)
	if err != nil {
		return "", n, err
	}
	return hex.EncodeToString(w.hasher.Sum(nil)), n, nil
}

// HashFile rejects symlinks and detects an ordinary concurrent size/time change.
func (w *Workspace) HashFile(name string) (string, int64, error) {
	before, err := os.Lstat(name)
	if err != nil || !before.Mode().IsRegular() {
		return "", 0, fmt.Errorf("not a readable regular file: %s: %v", name, err)
	}
	f, err := os.Open(name)
	if err != nil {
		return "", 0, err
	}
	defer f.Close()
	opened, err := f.Stat()
	if err != nil || !os.SameFile(before, opened) {
		return "", 0, fmt.Errorf("file identity changed: %s", name)
	}
	digest, n, err := w.HashReader(f)
	if err != nil {
		return "", n, err
	}
	after, err := f.Stat()
	if err != nil || n != before.Size() || after.Size() != before.Size() ||
		!after.ModTime().Equal(before.ModTime()) {
		return "", n, fmt.Errorf("file changed while hashing: %s", name)
	}
	return digest, n, nil
}

// Discover walks the current root without entering caches or following symlinks.
func Discover(root string) ([]Artifact, []Exclusion, error) {
	artifacts := make([]Artifact, 0, 2300)
	exclusions := make([]Exclusion, 0, 40)
	err := filepath.WalkDir(root, func(name string, entry fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(root, name)
		if err != nil || rel == "." {
			return err
		}
		rel = filepath.ToSlash(rel)
		if entry.IsDir() {
			switch entry.Name() {
			case ".git", ".pi", ".lake", "__pycache__", "target":
				exclusions = append(exclusions, Exclusion{rel, "private/runtime/build cache"})
				return filepath.SkipDir
			}
			return nil
		}
		if !entry.Type().IsRegular() {
			exclusions = append(exclusions, Exclusion{rel, "symlink or nonregular object"})
			return nil
		}
		artifacts = append(artifacts, Artifact{
			Path: rel, Inspection: "bytes-hashed; no semantic reading inferred",
			ResultAssignment: "pending statement-level catalogue reconciliation",
		})
		return nil
	})
	return artifacts, exclusions, err
}

// HashArtifacts assigns disjoint sorted chunks to workers, each with private buffers.
func HashArtifacts(root string, artifacts []Artifact, workers int) error {
	if workers < 1 {
		return errors.New("workers must be positive")
	}
	var group sync.WaitGroup
	errs := make([]error, workers)
	chunk := (len(artifacts) + workers - 1) / workers
	for worker := 0; worker < workers; worker++ {
		lo := min(worker*chunk, len(artifacts))
		hi := min(lo+chunk, len(artifacts))
		group.Add(1)
		go func(worker, lo, hi int) {
			defer group.Done()
			w := NewWorkspace(0, 0)
			part := artifacts[lo:hi]
			part = part[:len(part)]
			for i := range part {
				digest, n, err := w.HashFile(filepath.Join(root, part[i].Path))
				if err != nil {
					errs[worker] = err
					return
				}
				part[i].SHA256, part[i].Bytes = digest, n
			}
		}(worker, lo, hi)
	}
	group.Wait()
	return errors.Join(errs...)
}

// GroupArtifacts preserves all path identities while identifying exact byte duplicates.
func GroupArtifacts(artifacts []Artifact) (map[string][]string, int, int) {
	groups := make(map[string][]string, len(artifacts))
	for _, a := range artifacts {
		groups[a.SHA256] = append(groups[a.SHA256], a.Path)
	}
	duplicates, extras := 0, 0
	for _, paths := range groups {
		if len(paths) > 1 {
			duplicates++
			extras += len(paths) - 1
		}
	}
	artifacts = artifacts[:len(artifacts)]
	for i := range artifacts {
		paths := groups[artifacts[i].SHA256]
		if len(paths) > 1 {
			artifacts[i].EqualBytePaths = paths
		}
	}
	return groups, duplicates, extras
}

// SafeMemberName forbids absolute/traversing paths even though no extraction is performed.
func SafeMemberName(name string) bool {
	if name == "" || strings.ContainsAny(name, "\\\x00") || strings.HasPrefix(name, "/") {
		return false
	}
	for _, component := range strings.Split(name, "/") {
		if component == ".." || strings.Contains(component, ":") {
			return false
		}
	}
	return path.Clean(name) != "."
}

// PrivateMember excludes explicitly unrelated/private/cached payloads from byte opening.
func PrivateMember(name string) bool {
	for _, component := range strings.Split(name, "/") {
		switch component {
		case ".pi", ".git", ".lake", "__pycache__", "target", "Paper.pdf":
			return true
		}
	}
	return false
}

// SnapshotArchive copies and hashes the same stream before publishing any archive rows.
// Later replacement or in-place mutation of the source cannot change the accepted snapshot.
func (w *Workspace) SnapshotArchive(root string, a Artifact) (string, error) {
	if !SafeMemberName(a.Path) || a.Bytes < 0 || a.Bytes > MaxContainerBytes {
		return "", fmt.Errorf("archive snapshot budget or path rejected: %s", a.Path)
	}
	before, err := os.Lstat(filepath.Join(root, a.Path))
	if err != nil || !before.Mode().IsRegular() {
		return "", fmt.Errorf("archive is not a regular file: %s: %v", a.Path, err)
	}
	source, err := os.Open(filepath.Join(root, a.Path))
	if err != nil {
		return "", err
	}
	defer source.Close()
	opened, err := source.Stat()
	if err != nil || !os.SameFile(before, opened) || opened.Size() != a.Bytes {
		return "", fmt.Errorf("archive identity or size changed: %s", a.Path)
	}
	snapshot, err := os.CreateTemp("", "CollatzArchive-*")
	if err != nil {
		return "", err
	}
	name := snapshot.Name()
	accepted := false
	defer func() {
		if !accepted {
			snapshot.Close()
			os.Remove(name)
		}
	}()
	w.hasher.Reset()
	w.checksum = 0
	// Both the private snapshot and digest consume precisely the same copied bytes.
	n, err := io.CopyBuffer(io.MultiWriter(snapshot, w),
		io.LimitReader(source, a.Bytes+1), w.buffer)
	closeErr := snapshot.Close()
	digest := hex.EncodeToString(w.hasher.Sum(nil))
	if err != nil || closeErr != nil || n != a.Bytes || digest != a.SHA256 {
		return "", fmt.Errorf("archive snapshot hash mismatch: %s: %v; %v", a.Path,
			err, closeErr)
	}
	accepted = true
	return name, nil
}

// ListingBuffer stops external metadata collection at the explicit listing-byte limit.
type ListingBuffer struct {
	buffer bytes.Buffer
}

// Write refuses bytes beyond the cap before growing the underlying buffer.
func (b *ListingBuffer) Write(p []byte) (int, error) {
	if len(p) > MaxListingBytes-b.buffer.Len() {
		return 0, errors.New("archive listing byte budget exceeded")
	}
	return b.buffer.Write(p)
}

// Read7z lists only an accepted archive snapshot, with bounded output and runtime.
func (w *Workspace) Read7z(root string, a Artifact) ([]ArchiveMember, error) {
	snapshot, err := w.SnapshotArchive(root, a)
	if err != nil {
		return nil, err
	}
	defer os.Remove(snapshot)
	ctx, cancel := context.WithTimeout(context.Background(), ListingTimeout)
	defer cancel()
	command := exec.CommandContext(ctx, "7z", "l", "-slt", snapshot)
	var listing ListingBuffer
	command.Stdout = &listing
	if err := command.Run(); err != nil {
		return nil, errors.Join(err, ctx.Err())
	}
	return Parse7zListing(listing.buffer.String(), a.Path, a.SHA256)
}

// ReadZIP hashes safe members from the exact container stream named by ArchiveSHA256.
func (w *Workspace) ReadZIP(root string, a Artifact, groups map[string][]string) (
	[]ArchiveMember, error,
) {
	snapshot, err := w.SnapshotArchive(root, a)
	if err != nil {
		return nil, err
	}
	defer os.Remove(snapshot)
	reader, err := zip.OpenReader(snapshot)
	if err != nil {
		return nil, err
	}
	defer reader.Close()
	members := make([]ArchiveMember, 0, len(reader.File))
	occurrences := make(map[string]int, len(reader.File))
	for _, f := range reader.File {
		occurrences[f.Name]++
		m := ArchiveMember{
			Archive: a.Path, ArchiveSHA256: a.SHA256, Member: f.Name,
			Occurrence: occurrences[f.Name], Bytes: f.UncompressedSize64,
			CRC32: fmt.Sprintf("%08x", f.CRC32), Kind: "file",
			Inspection: "header-only", ResultAssignment: "pending semantic reconciliation",
		}
		switch {
		case f.FileInfo().IsDir():
			m.Kind, m.ResultAssignment = "directory", "non-research directory entry"
		case !SafeMemberName(f.Name):
			m.Kind, m.ResultAssignment = "unsafe-path", "excluded; no extraction"
		case !f.Mode().IsRegular():
			m.Kind, m.ResultAssignment = "nonregular", "excluded; no link following"
		case PrivateMember(f.Name):
			m.Kind, m.ResultAssignment = "excluded-payload", "private/unrelated/cache"
		default:
			if m.Bytes > w.maxMember || m.Bytes > w.maxArchive-w.archiveBytes {
				return nil, fmt.Errorf("archive byte budget exceeded: %s::%s", a.Path, f.Name)
			}
			r, err := f.Open()
			if err != nil {
				return nil, err
			}
			digest, n, readErr := w.HashReader(io.LimitReader(r, int64(m.Bytes)+1))
			closeErr := r.Close()
			if readErr != nil || closeErr != nil || uint64(n) != m.Bytes {
				return nil, fmt.Errorf("invalid ZIP member %s::%s: %v; %v; size %d",
					a.Path, f.Name, readErr, closeErr, n)
			}
			// Go's ZIP reader can skip zero recorded CRCs; compare every member ourselves.
			if w.checksum != f.CRC32 {
				return nil, fmt.Errorf("invalid ZIP member %s::%s: checksum error: "+
					"computed %08x, recorded %08x", a.Path, f.Name, w.checksum, f.CRC32)
			}
			w.archiveBytes += m.Bytes
			m.SHA256, m.Inspection = digest, "bytes-hashed and CRC-checked; not proof-read"
			m.MatchingCurrentPaths = groups[digest]
			if len(m.MatchingCurrentPaths) > 0 {
				m.ResultAssignment = "byte-identical current paths; semantic status retained"
			}
		}
		members = append(members, m)
	}
	return members, nil
}

// Parse7zListing parses member headers only; it makes no content or CRC claim.
func Parse7zListing(listing, archive, archiveSHA256 string) ([]ArchiveMember, error) {
	scanner := bufio.NewScanner(strings.NewReader(listing))
	scanner.Buffer(make([]byte, 4096), 1024*1024)
	started := false
	fields := make(map[string]string)
	members := make([]ArchiveMember, 0, 1600)
	occurrences := make(map[string]int)
	flush := func() error {
		name := fields["Path"]
		if name == "" {
			return nil
		}
		size, err := strconv.ParseUint(fields["Size"], 10, 64)
		if err != nil {
			return fmt.Errorf("7z member size %q: %w", name, err)
		}
		occurrences[name]++
		kind := "file"
		if fields["Folder"] == "+" || strings.HasPrefix(fields["Attributes"], "D") {
			kind = "directory"
		} else if !SafeMemberName(name) {
			kind = "unsafe-path"
		} else if PrivateMember(name) {
			kind = "excluded-payload"
		}
		members = append(members, ArchiveMember{
			Archive: archive, ArchiveSHA256: archiveSHA256, Member: name,
			Occurrence: occurrences[name], Bytes: size, CRC32: fields["CRC"], Kind: kind,
			Inspection:       "7z header-only; content/CRC not independently checked",
			ResultAssignment: "pending archive-format and semantic reconciliation",
		})
		clear(fields)
		return nil
	}
	for scanner.Scan() {
		line := scanner.Text()
		if line == "----------" {
			started = true
			continue
		}
		if !started {
			continue
		}
		if line == "" {
			if err := flush(); err != nil {
				return nil, err
			}
			continue
		}
		key, value, ok := strings.Cut(line, " = ")
		if ok {
			fields[key] = value
		}
	}
	if err := scanner.Err(); err != nil {
		return nil, err
	}
	if err := flush(); err != nil {
		return nil, err
	}
	if !started || len(members) == 0 {
		return nil, errors.New("7z listing contained no member section")
	}
	return members, nil
}

// OpenSourceRegular anchors each directory and refuses symlinks, caches and nonregular leaves.
func OpenSourceRegular(root, rel string) (*os.File, error) {
	if !SafeMemberName(rel) || PrivateMember(rel) {
		return nil, fmt.Errorf("unsafe or excluded source path: %s", rel)
	}
	directory, err := os.OpenRoot(root)
	if err != nil {
		return nil, err
	}
	defer func() { directory.Close() }()
	components := strings.Split(path.Clean(rel), "/")
	for _, component := range components[:len(components)-1] {
		before, err := directory.Lstat(component)
		if err != nil || !before.IsDir() {
			return nil, fmt.Errorf("non-directory or symlink source ancestor: %s", rel)
		}
		next, err := directory.OpenRoot(component)
		if err != nil {
			return nil, err
		}
		after, err := next.Stat(".")
		if err != nil || !os.SameFile(before, after) {
			next.Close()
			return nil, fmt.Errorf("source directory identity changed: %s", rel)
		}
		directory.Close()
		directory = next
	}
	leaf := components[len(components)-1]
	before, err := directory.Lstat(leaf)
	if err != nil || !before.Mode().IsRegular() {
		return nil, fmt.Errorf("nonregular or symlink source leaf: %s", rel)
	}
	f, err := directory.Open(leaf)
	if err != nil {
		return nil, err
	}
	after, err := f.Stat()
	if err != nil || !os.SameFile(before, after) {
		f.Close()
		return nil, fmt.Errorf("source file identity changed: %s", rel)
	}
	return f, nil
}

// ReadJSON reads metadata only through the same in-tree, nonprivate no-alias boundary.
func ReadJSON(root, rel string, output any) error {
	f, err := OpenSourceRegular(root, rel)
	if err != nil {
		return err
	}
	defer f.Close()
	decoder := json.NewDecoder(f)
	if err := decoder.Decode(output); err != nil {
		return err
	}
	var trailing any
	if err := decoder.Decode(&trailing); err != io.EOF {
		return fmt.Errorf("trailing metadata after JSON document: %s", rel)
	}
	return nil
}

// Compare records missing, changed and added paths relative to one historical path set.
func Compare(current, historical map[string]string) Comparison {
	c := Comparison{Added: []string{}, Changed: []string{}, Missing: []string{}}
	for name, digest := range historical {
		now, ok := current[name]
		if !ok {
			c.Missing = append(c.Missing, name)
		} else if now != digest {
			c.Changed = append(c.Changed, name)
		} else {
			c.Unchanged++
		}
	}
	for name := range current {
		if _, ok := historical[name]; !ok {
			c.Added = append(c.Added, name)
		}
	}
	sort.Strings(c.Added)
	sort.Strings(c.Changed)
	sort.Strings(c.Missing)
	return c
}

// Reconcile checks active provenance without accessing any external recovery path.
func Reconcile(root string, artifacts []Artifact, summary *Summary) (
	[]OriginalArtifact, []HistoricalMember, error,
) {
	current := make(map[string]string, len(artifacts))
	for _, a := range artifacts {
		if _, exists := current[a.Path]; exists {
			return nil, nil, fmt.Errorf("duplicate current artifact path: %s", a.Path)
		}
		current[a.Path] = a.SHA256
	}
	var originals []OriginalArtifact
	var modifications []Modification
	var catalog []Artifact
	var historical []HistoricalMember
	var export ExportManifest
	loads := []struct {
		path   string
		output any
	}{
		{"artifacts/organization/original-file-manifest.json", &originals},
		{"artifacts/organization/source-modifications.json", &modifications},
		{"artifacts/organization/tree-catalog.json", &catalog},
		{"artifacts/organization/zip-members.json", &historical},
		{"artifacts/exports/collatz-progress-20261002T231927Z.manifest.json", &export},
	}
	for _, load := range loads {
		if err := ReadJSON(root, load.path, load.output); err != nil {
			return nil, nil, err
		}
	}
	declared := make(map[string]string, len(modifications))
	for _, m := range modifications {
		if _, exists := declared[m.ActivePath]; exists {
			return nil, nil, fmt.Errorf("duplicate modification path: %s", m.ActivePath)
		}
		now, exists := current[m.ActivePath]
		if !exists || now != m.CurrentSHA256 {
			return nil, nil, fmt.Errorf("declared modification hash mismatch: %s", m.ActivePath)
		}
		declared[m.ActivePath] = m.CurrentSHA256
	}
	summary.ModificationRecords = len(modifications)
	originalPaths := make(map[string]struct{}, len(originals))
	originals = originals[:len(originals)]
	for i := range originals {
		o := &originals[i]
		if _, exists := originalPaths[o.Path]; exists {
			return nil, nil, fmt.Errorf("duplicate original artifact path: %s", o.Path)
		}
		originalPaths[o.Path] = struct{}{}
		switch o.Action {
		case "retained", "moved":
			if o.Target == nil || !SafeMemberName(*o.Target) {
				return nil, nil, fmt.Errorf("invalid active original target: %s", o.Path)
			}
			now, ok := current[*o.Target]
			if !ok {
				return nil, nil, fmt.Errorf("missing active original target: %s", *o.Target)
			}
			o.CurrentSHA256 = now
			o.CurrentEvidence = "current bytes match original hash"
			if now != o.SHA256 {
				if declared[*o.Target] != now {
					return nil, nil, fmt.Errorf("undeclared original change: %s", *o.Target)
				}
				o.CurrentEvidence = "declared modified bytes; semantic equivalence not inferred"
				summary.OriginalDeclaredDelta = append(summary.OriginalDeclaredDelta, *o.Target)
			}
			summary.OriginalActive++
		case "external-backup", "external-recovery":
			o.CurrentEvidence = "external metadata only; external bytes not accessed"
			summary.OriginalExternal++
		default:
			return nil, nil, fmt.Errorf("unknown original action: %s: %s", o.Path, o.Action)
		}
	}
	sort.Strings(summary.OriginalDeclaredDelta)
	oldCatalog := make(map[string]string, len(catalog))
	for _, a := range catalog {
		if _, exists := oldCatalog[a.Path]; exists {
			return nil, nil, fmt.Errorf("duplicate historical catalogue path: %s", a.Path)
		}
		oldCatalog[a.Path] = a.SHA256
	}
	summary.Catalog = Compare(current, oldCatalog)
	oldExport := make(map[string]string, export.WorkspaceFiles)
	for _, row := range export.Files {
		if row.Kind == "workspace" {
			if _, exists := oldExport[row.WorkspacePath]; exists {
				return nil, nil, fmt.Errorf("duplicate export workspace path: %s", row.WorkspacePath)
			}
			oldExport[row.WorkspacePath] = row.SHA256
		}
	}
	if len(oldExport) != export.WorkspaceFiles {
		return nil, nil, errors.New("export workspace count or path uniqueness mismatch")
	}
	summary.Export = Compare(current, oldExport)
	historical = historical[:len(historical)]
	for i := range historical {
		historical[i].Inspection = "historical metadata only; original archive not accessed"
	}
	return originals, historical, nil
}

// WriteJSON uses a temporary destination file so a failed encoding preserves old evidence.
func WriteJSON(output, name string, value any) error {
	f, err := os.CreateTemp(output, ".Inventory-*")
	if err != nil {
		return err
	}
	tmp := f.Name()
	defer os.Remove(tmp)
	encoder := json.NewEncoder(f)
	encoder.SetIndent("", "  ")
	if err := encoder.Encode(value); err != nil {
		f.Close()
		return err
	}
	if err := f.Close(); err != nil {
		return err
	}
	return os.Rename(tmp, filepath.Join(output, name))
}

// ResolveOutput resolves existing ancestors, including symlinks, before allowing writes.
func ResolveOutput(name string) (string, error) {
	absolute, err := filepath.Abs(name)
	if err != nil {
		return "", err
	}
	ancestor := absolute
	tail := make([]string, 0, 8)
	for {
		_, err := os.Lstat(ancestor)
		if err == nil {
			resolved, err := filepath.EvalSymlinks(ancestor)
			if err != nil {
				return "", err
			}
			for i := len(tail) - 1; i >= 0; i-- {
				resolved = filepath.Join(resolved, tail[i])
			}
			return resolved, nil
		}
		if !errors.Is(err, fs.ErrNotExist) {
			return "", err
		}
		tail = append(tail, filepath.Base(ancestor))
		ancestor = filepath.Dir(ancestor)
	}
}

// Run builds all evidence in memory before replacing any destination catalogue files.
func Run(source, output string, workers int, maxMember, maxArchive uint64) error {
	root, err := filepath.Abs(source)
	if err != nil {
		return err
	}
	root, err = filepath.EvalSymlinks(root)
	if err != nil {
		return err
	}
	out, err := ResolveOutput(output)
	if err != nil {
		return err
	}
	inside, err := filepath.Rel(root, out)
	outside := inside == ".." || strings.HasPrefix(inside, ".."+string(os.PathSeparator))
	if err != nil || !outside {
		return errors.New("inventory output must be outside the read-only source root")
	}
	artifacts, exclusions, err := Discover(root)
	if err != nil {
		return err
	}
	if err := HashArtifacts(root, artifacts, workers); err != nil {
		return err
	}
	groups, duplicates, extras := GroupArtifacts(artifacts)
	summary := Summary{
		Format: "GeneralizedCollatzLibrary.ByteProvenance.v1", SourceRoot: root,
		Files: len(artifacts), DistinctSHA256: len(groups), DuplicateGroups: duplicates,
		DuplicateExtraCopies: extras, Exclusions: exclusions,
		Limitations: []string{
			"Hashes and CRC checks certify bytes, not mathematical truth or full reading.",
			"7z headers are listed only; format-to-format content equality remains unchecked.",
			"Archives are parsed from verified private snapshots capped at 1 GiB each.",
			"7z listing is capped at 32 MiB and two minutes per archive.",
			"External originals and historical archives are recorded but never accessed.",
			"Excluded caches/private/unrelated payloads are not opened or semantically read.",
			"All statement-level destinations and verification tiers require a separate ledger.",
		},
	}
	for _, a := range artifacts {
		summary.Bytes += a.Bytes
	}
	originals, historical, err := Reconcile(root, artifacts, &summary)
	if err != nil {
		return err
	}
	w := NewWorkspace(maxMember, maxArchive)
	members := make([]ArchiveMember, 0, 3400)
	for _, a := range artifacts {
		var rows []ArchiveMember
		switch strings.ToLower(filepath.Ext(a.Path)) {
		case ".zip":
			rows, err = w.ReadZIP(root, a, groups)
			for _, row := range rows {
				if row.Kind != "directory" {
					summary.CurrentZIPMembers++
				}
			}
		case ".7z":
			rows, err = w.Read7z(root, a)
			for _, row := range rows {
				if row.Kind != "directory" {
					summary.Current7zMembers++
				}
			}
		}
		if err != nil {
			return fmt.Errorf("archive %s: %w", a.Path, err)
		}
		members = append(members, rows...)
	}
	summary.ZIPMemberBytesHashed = w.archiveBytes
	if err := os.MkdirAll(out, 0755); err != nil {
		return err
	}
	outputs := []struct {
		name  string
		value any
	}{
		{"CurrentArtifacts.json", artifacts}, {"OriginalArtifacts.json", originals},
		{"ArchiveMembers.json", members}, {"HistoricalArchiveMembers.json", historical},
		{"Reconciliation.json", summary},
	}
	for _, item := range outputs {
		if err := WriteJSON(out, item.name, item.value); err != nil {
			return err
		}
	}
	fmt.Printf("files=%d bytes=%d unique=%d duplicate-groups=%d extra-copies=%d\n",
		summary.Files, summary.Bytes, summary.DistinctSHA256, duplicates, extras)
	fmt.Printf("original-active=%d external=%d declared-deltas=%d modification-rows=%d\n",
		summary.OriginalActive, summary.OriginalExternal,
		len(summary.OriginalDeclaredDelta), summary.ModificationRecords)
	fmt.Printf("ZIP-members=%d ZIP-bytes-hashed=%d 7z-members-listed=%d\n",
		summary.CurrentZIPMembers, w.archiveBytes, summary.Current7zMembers)
	fmt.Printf("catalog: +%d changed=%d missing=%d; export: changed=%d missing=%d\n",
		len(summary.Catalog.Added), len(summary.Catalog.Changed), len(summary.Catalog.Missing),
		len(summary.Export.Changed), len(summary.Export.Missing))
	return nil
}

// main fixes safe default roots; limits reject a workload rather than silently skipping it.
func main() {
	source := flag.String("source", "/home/dell/collatz", "read-only source directory")
	output := flag.String("output", "Library.SourceCatalogue.001/other", "evidence directory")
	workers := flag.Int("workers", 4, "disjoint hashing chunks")
	maxMember := flag.Uint64("max-member", 256<<20, "maximum opened ZIP member bytes")
	maxArchive := flag.Uint64("max-archive", 1<<30, "total opened ZIP member byte budget")
	flag.Parse()
	if err := Run(*source, *output, *workers, *maxMember, *maxArchive); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
