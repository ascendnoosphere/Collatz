// SPDX-License-Identifier: CC-BY-4.0

package main

import "testing"

// TestPrefix accepts only the recomputed ten-term shortcut prefix of 27.
func TestPrefix(t *testing.T) {
	if err := checkPrefix(); err != nil {
		t.Fatal(err)
	}
}

// TestPrefixMismatch rejects the prefix after one stated term is replaced.
func TestPrefixMismatch(t *testing.T) {
	var got [10]uint64
	fillOrbit(got[:], 27)
	want := statedPrefix()
	want[4] = 0
	if !prefixDiffers(got[:], &want) {
		t.Fatal("a corrupted prefix term was accepted")
	}
}

// TestWrongSeed rejects shortcut states that do not start at 27.
func TestWrongSeed(t *testing.T) {
	var got [10]uint64
	fillOrbit(got[:], 26)
	want := statedPrefix()
	if !prefixDiffers(got[:], &want) {
		t.Fatal("a different seed matched the prefix of 27")
	}
}

// TestOrbitAndParent accepts the stated orbit, the first block, and 222.
func TestOrbitAndParent(t *testing.T) {
	if err := checkOrbit(); err != nil {
		t.Fatal(err)
	}
	var orbit [27]uint64
	fillOrbit(orbit[:], 27)
	if err := checkFirstBlock(orbit[:]); err != nil {
		t.Fatal(err)
	}
	if err := checkParent(); err != nil {
		t.Fatal(err)
	}
}
