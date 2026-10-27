// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command RecursiveClose checks the parent-time identity on one finite grid.
package main

import (
	"fmt"
	"os"
)

// Grid bounds for the finite integer certificate.
// Parents run from ParentMin through ParentMax.
// Join and parent times run from 0 through TimeLimit.
// Doubling prefixes run from 0 through SourceSteps.
// The grid does not prove the identity for every natural number.
const (
	ParentMin   = 1
	ParentMax   = 32
	TimeLimit   = 16
	SourceSteps = 6
)

// Workspace holds one parent orbit of length TimeLimit.
type Workspace struct {
	Orbit [TimeLimit + 1]int64
}

// EqualReports reports whether two integers are the same value.
func EqualReports(got, want int64) bool {
	return got == want
}

// ConstantTrue accepts every comparison.
func ConstantTrue(got, want int64) bool {
	return true
}

// PredicateSeparates requires agreement on equals and refusal on a mismatch.
func PredicateSeparates(pred func(got, want int64) bool) bool {
	return pred(1, 1) && !pred(2, 1)
}

// Shortcut halves an even integer and sends an odd integer through (3x+1)/2.
func Shortcut(x int64) int64 {
	if x%2 == 0 {
		return x / 2
	}
	return (3*x + 1) / 2
}

// Iterate applies Shortcut the requested number of times.
func Iterate(x int64, steps int) int64 {
	for i := 0; i < steps; i++ {
		x = Shortcut(x)
	}
	return x
}

// ParentCertifiedTime is a+(t-b) before the parent time and a phase bit after it.
func ParentCertifiedTime(a, b, t int) int {
	if b <= t {
		return a + (t - b)
	}
	return a + (b-t)%2
}

// DecoyTime keeps only the source prefix and drops the parent clock.
func DecoyTime(a, b, t int) int {
	return a
}

// DoublingSource returns join*2^a, or refuses a product outside the safe range.
func DoublingSource(join int64, a int) (int64, bool) {
	source := join
	for i := 0; i < a; i++ {
		if source < 0 || source > 1<<61 {
			return 0, false
		}
		source *= 2
	}
	return source, true
}

// FillOrbit writes the shortcut orbit of start through time TimeLimit.
func FillOrbit(start int64, w *Workspace) {
	w.Orbit[0] = start
	for i := 0; i < TimeLimit; i++ {
		w.Orbit[i+1] = Shortcut(w.Orbit[i])
	}
}

// Note records one exact comparison.
func Note(checks, failures *uint64, ok bool) {
	*checks++
	if !ok {
		*failures++
	}
}

// CheckGrid checks doubling joins into parent orbits that hit 1 inside the window.
// Each admissible row checks the doubling range, the join, and arrival at 1.
// A constantly true predicate is not a separating certificate.
func CheckGrid(pred func(got, want int64) bool) (checks, failures uint64) {
	var w Workspace
	for parent := int64(ParentMin); parent <= ParentMax; parent++ {
		FillOrbit(parent, &w)
		for t := 0; t <= TimeLimit; t++ {
			if w.Orbit[t] != 1 {
				continue
			}
			for b := 0; b <= TimeLimit; b++ {
				join := w.Orbit[b]
				for a := 0; a <= SourceSteps; a++ {
					source, ok := DoublingSource(join, a)
					Note(&checks, &failures, ok)
					if !ok {
						continue
					}
					gotJoin := Iterate(source, a)
					Note(&checks, &failures, pred(gotJoin, join))
					time := ParentCertifiedTime(a, b, t)
					Note(&checks, &failures, pred(Iterate(source, time), 1))
				}
			}
		}
	}
	return checks, failures
}

// CheckDecoy repeats the grid with the parent clock removed.
func CheckDecoy(pred func(got, want int64) bool) (checks, failures uint64) {
	var w Workspace
	for parent := int64(ParentMin); parent <= ParentMax; parent++ {
		FillOrbit(parent, &w)
		for t := 0; t <= TimeLimit; t++ {
			if w.Orbit[t] != 1 {
				continue
			}
			for b := 0; b <= TimeLimit; b++ {
				join := w.Orbit[b]
				for a := 0; a <= SourceSteps; a++ {
					source, ok := DoublingSource(join, a)
					Note(&checks, &failures, ok)
					if !ok {
						continue
					}
					gotJoin := Iterate(source, a)
					Note(&checks, &failures, pred(gotJoin, join))
					time := DecoyTime(a, b, t)
					Note(&checks, &failures, pred(Iterate(source, time), 1))
				}
			}
		}
	}
	return checks, failures
}

// AdmissibleCount counts parent-time pairs whose shortcut image is 1.
func AdmissibleCount() uint64 {
	var w Workspace
	var count uint64
	for parent := int64(ParentMin); parent <= ParentMax; parent++ {
		FillOrbit(parent, &w)
		for t := 0; t <= TimeLimit; t++ {
			if w.Orbit[t] == 1 {
				count++
			}
		}
	}
	return count
}

// ExpectedChecks is three comparisons on every join of an admissible orbit.
func ExpectedChecks() uint64 {
	rows := AdmissibleCount()
	rows *= uint64(TimeLimit + 1)
	rows *= uint64(SourceSteps + 1)
	return rows * 3
}

// main prints the number of exact comparisons in the finite certificate.
func main() {
	checks, failures := CheckGrid(EqualReports)
	fmt.Printf("checks %d\n", checks)
	if failures != 0 {
		os.Exit(1)
	}
}
