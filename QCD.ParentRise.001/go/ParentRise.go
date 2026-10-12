// SPDX-License-Identifier: CC-BY-4.0

// Command ParentRise recomputes a finite shortcut orbit and one parent comparison.
// A mismatch stops the check. The arithmetic is not a proof and does not show
// that an iterate equals 1.
package main

import (
	"fmt"
	"os"
)

// shortcut halves an even value and sends an odd value to (3n+1)/2.
func shortcut(n uint64) uint64 {
	if n%2 == 0 {
		return n / 2
	}
	return (3*n + 1) / 2
}

// fillOrbit writes seed and later shortcut states into a caller-owned buffer.
func fillOrbit(dst []uint64, seed uint64) {
	n := len(dst)
	if n == 0 {
		return
	}
	buf := dst[:n]
	buf[0] = seed
	for i := 1; i < n; i++ {
		buf[i] = shortcut(buf[i-1])
	}
}

// statedPrefix returns the ten-term shortcut prefix of 27.
func statedPrefix() [10]uint64 {
	return [10]uint64{27, 41, 62, 31, 47, 71, 107, 161, 242, 121}
}

// statedOrbit returns the shortcut states of 27 through time 26.
func statedOrbit() [27]uint64 {
	return [27]uint64{
		27, 41, 62, 31, 47, 71, 107, 161, 242, 121,
		182, 91, 137, 206, 103, 155, 233, 350, 175, 263,
		395, 593, 890, 445, 668, 334, 167,
	}
}

// prefixDiffers reports whether a computed row differs from the stated prefix.
func prefixDiffers(got []uint64, want *[10]uint64) bool {
	if len(got) != len(want) {
		return true
	}
	n := len(want)
	row := got[:n]
	for i := 0; i < n; i++ {
		if row[i] != want[i] {
			return true
		}
	}
	return false
}

// orbitDiffers reports whether a computed row differs from the stated orbit.
func orbitDiffers(got []uint64, want *[27]uint64) bool {
	if len(got) != len(want) {
		return true
	}
	n := len(want)
	row := got[:n]
	for i := 0; i < n; i++ {
		if row[i] != want[i] {
			return true
		}
	}
	return false
}

// checkPrefix recomputes ten shortcut states from 27 and fails on any mismatch.
func checkPrefix() error {
	var got [10]uint64
	fillOrbit(got[:], 27)
	want := statedPrefix()
	if prefixDiffers(got[:], &want) {
		return fmt.Errorf("shortcut prefix of 27 differs from the stated terms")
	}
	return nil
}

// checkOrbit recomputes the shortcut states through time 26.
func checkOrbit() error {
	var got [27]uint64
	fillOrbit(got[:], 27)
	want := statedOrbit()
	if orbitDiffers(got[:], &want) {
		return fmt.Errorf("shortcut orbit of 27 differs from the stated terms")
	}
	return nil
}

// checkFirstBlock fails if an earlier even pair exists or time 23 is not odd-even-even.
func checkFirstBlock(orbit []uint64) error {
	if len(orbit) < 27 {
		return fmt.Errorf("orbit shorter than the first odd-even-even block")
	}
	row := orbit[:len(orbit)]
	for t := 0; t < 24; t++ {
		if row[t]%2 == 0 && row[t+1]%2 == 0 {
			return fmt.Errorf("consecutive even states before time 24")
		}
	}
	if row[23]%2 != 1 || row[24]%2 != 0 || row[25]%2 != 0 {
		return fmt.Errorf("time 23 is not the first odd-even-even block")
	}
	return nil
}

// checkParent compares 222 with one halving, zero factors of 3, and the seed 27.
func checkParent() error {
	if (445-1)/2 != 222 {
		return fmt.Errorf("one division of 445-1 does not produce 222")
	}
	if shortcut(445) != 668 || shortcut(668) != 334 || shortcut(334) != 167 {
		return fmt.Errorf("three shortcut steps from 445 do not join 167")
	}
	if shortcut(222) != 111 || shortcut(111) != 167 {
		return fmt.Errorf("two shortcut steps from 222 do not join 167")
	}
	if 222%2 != 0 || 222/2 != 111 || 111%2 != 1 {
		return fmt.Errorf("222 does not become odd after exactly one division")
	}
	if 222%3 == 2 {
		return fmt.Errorf("an inverse odd step is legal at 222")
	}
	if (222+1)%3 == 0 {
		return fmt.Errorf("three divides 223")
	}
	if 167%3 != 2 || (2*167-1)/3 != 111 {
		return fmt.Errorf("one inverse odd step at 167 does not return 111")
	}
	ancestor := uint64((1 << 0) * (222 + 1) - 1)
	if ancestor != 222 {
		return fmt.Errorf("the zero-division odd-chain ancestor is not 222")
	}
	if 222 <= 27 {
		return fmt.Errorf("222 is not strictly larger than 27")
	}
	return nil
}

// main runs the finite comparisons and stops when any stated term differs.
func main() {
	if err := checkPrefix(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := checkOrbit(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	var orbit [27]uint64
	fillOrbit(orbit[:], 27)
	if err := checkFirstBlock(orbit[:]); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := checkParent(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	fmt.Println("finite check matched the prefix of 27 and the parent 222")
}
