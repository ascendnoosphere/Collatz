// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

// TestArchiveReplacement rejects later bytes under an earlier container digest.
func TestArchiveReplacement(t *testing.T) {
	root := t.TempDir()
	ZIPFixture(t, root)
	a := FixtureArtifact(t, root, "Bundle.zip")
	if err := os.Rename(filepath.Join(root, a.Path), filepath.Join(root, "Old.zip")); err != nil {
		t.Fatal(err)
	}
	WriteFixture(t, root, a.Path, "different container bytes")
	w := NewWorkspace(1024, 2048)
	if _, err := w.ReadZIP(root, a, nil); err == nil {
		t.Fatal("attached replacement bytes to the old digest")
	}
}

// TestArchiveSnapshot binds accepted bytes independently of later source mutations.
func TestArchiveSnapshot(t *testing.T) {
	root := t.TempDir()
	WriteFixture(t, root, "Container.7z", "original stream")
	a := FixtureArtifact(t, root, "Container.7z")
	w := NewWorkspace(1024, 2048)
	name, err := w.SnapshotArchive(root, a)
	if err != nil {
		t.Fatal(err)
	}
	defer os.Remove(name)
	// Equal-size mutations distinguish digest binding from size-only checks.
	WriteFixture(t, root, a.Path, "modified stream")
	data, err := os.ReadFile(name)
	if err != nil || string(data) != "original stream" {
		t.Fatalf("accepted snapshot changed: %q; %v", data, err)
	}
	if _, err := w.SnapshotArchive(root, a); err == nil ||
		!strings.Contains(err.Error(), "archive snapshot hash mismatch") {
		t.Fatalf("same-size replacement did not fail closed: %v", err)
	}
	bad := a
	bad.Bytes = MaxContainerBytes + 1
	if _, err := w.SnapshotArchive(root, bad); err == nil {
		t.Fatal("accepted a container outside the explicit snapshot budget")
	}
}

// TestListingBudget rejects oversized metadata before storing it in the buffer.
func TestListingBudget(t *testing.T) {
	var listing ListingBuffer
	if n, err := listing.Write([]byte("header")); n != 6 || err != nil {
		t.Fatalf("valid listing rejected: %d; %v", n, err)
	}
	if _, err := listing.Write(make([]byte, MaxListingBytes)); err == nil {
		t.Fatal("accepted metadata beyond the listing byte cap")
	}
	if listing.buffer.String() != "header" {
		t.Fatal("failed oversized write partially altered accepted metadata")
	}
}
