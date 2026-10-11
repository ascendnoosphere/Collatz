// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"testing"
)

// ReferenceWord is an independent bounded machine-integer interpreter for the stated test box.
func ReferenceWord(q, c, d, n int64, word []Letter) (int64, bool) {
	for _, letter := range word {
		switch letter {
		case Affine:
			if n%d == 0 {
				return 0, false
			}
			n = q*n + c
		case Divide:
			if n%d != 0 {
				return 0, false
			}
			n /= d
		default:
			return 0, false
		}
	}
	return n, true
}

// TestParameters rejects malformed integers and all three excluded divisors.
func TestParameters(t *testing.T) {
	for _, d := range []string{"0", "1", "-1", "not-an-integer"} {
		if _, err := ParseParameters("3", "1", d); err == nil {
			t.Errorf("accepted invalid divisor %q", d)
		}
	}
	for _, d := range []string{"2", "-2", "1000000000000000000000000000000"} {
		if _, err := ParseParameters("-5", "0", d); err != nil {
			t.Fatal(err)
		}
	}
}

// TestGuardedBox checks 330750 cases; |state| <= 3^5*13-1 ensures the reference has no overflow.
func TestGuardedBox(t *testing.T) {
	var p Parameters
	var w Workspace
	var input, output big.Int
	var data AffineData
	var x, value big.Rat
	buffer := make([]Letter, 5)
	count := 0
	for q := int64(-3); q <= 3; q++ {
		p.Q.SetInt64(q)
		for c := int64(-2); c <= 2; c++ {
			p.C.SetInt64(c)
			for d := int64(-4); d <= 4; d++ {
				if d > -2 && d < 2 {
					continue
				}
				p.D.SetInt64(d)
				for n := int64(-12); n <= 12; n++ {
					input.SetInt64(n)
					x.SetInt(&input)
					for length := 0; length <= 5; length++ {
						word := buffer[:length]
						for mask := 0; mask < 1<<length; mask++ {
							for i := range word {
								word[i] = Letter((mask >> i) & 1)
							}
							reference, legal := ReferenceWord(q, c, d, n, word)
							output.SetInt64(999)
							got := ExecuteWord(&p, word, &input, &output, &w)
							if got != legal || (got && output.Int64() != reference) {
								t.Fatalf("guard mismatch: (%d,%d,%d) n=%d word=%v", q, c, d, n, word)
							}
							if !got && output.Int64() != 999 {
								t.Fatal("illegal execution overwrote its destination")
							}
							if got {
								if err := RawWordAffine(&p, word, &data, &w); err != nil {
									t.Fatal(err)
								}
								if err := RationalAction(&data, &x, &value, &w); err != nil {
									t.Fatal(err)
								}
								if !value.IsInt() || value.Num().Cmp(&output) != 0 {
									t.Fatal("legal word disagrees with its affine presentation")
								}
							}
							count++
						}
					}
				}
			}
		}
	}
	if count != 330750 {
		t.Fatalf("wrong finite test scope: %d", count)
	}
}

// TestTraceRecovery includes signed divisors, zero, and direct input/output aliasing.
func TestTraceRecovery(t *testing.T) {
	var p Parameters
	var w Workspace
	var input, generated, replayed, direct big.Int
	word := make([]Letter, 12)
	for _, triple := range [][3]int64{{3, 1, 2}, {2, 2, -2}, {-5, 31, -6}, {0, 0, 3}} {
		p.Q.SetInt64(triple[0])
		p.C.SetInt64(triple[1])
		p.D.SetInt64(triple[2])
		for n := int64(-10); n <= 10; n++ {
			input.SetInt64(n)
			RawTrace(&p, word, &input, &generated, &w)
			if !ExecuteWord(&p, word, &input, &replayed, &w) || replayed.Cmp(&generated) != 0 {
				t.Fatal("generated trace did not replay")
			}
			direct.Set(&input)
			for range word {
				RawStep(&p, &direct, &direct, &w)
			}
			if direct.Cmp(&generated) != 0 {
				t.Fatal("generated trace changed the raw clock")
			}
		}
	}
}

// TestConductorBox checks 39060 signed scalar cases, not legality or universal orbit capture.
func TestConductorBox(t *testing.T) {
	var w Workspace
	var delta, b, gamma big.Int
	count := 0
	for d := int64(-30); d <= 30; d++ {
		if d == 0 {
			continue
		}
		delta.SetInt64(d)
		for offset := int64(-15); offset <= 15; offset++ {
			b.SetInt64(offset)
			if err := Conductor(&delta, &b, &gamma, &w); err != nil {
				t.Fatal(err)
			}
			if gamma.Sign() <= 0 || !gamma.IsInt64() {
				t.Fatal("nonpositive or unexpectedly large conductor")
			}
			for c := int64(-10); c <= 10; c++ {
				if (c%gamma.Int64() == 0) != ((offset*c)%d == 0) {
					t.Fatalf("conductor mismatch: delta=%d B=%d c=%d", d, offset, c)
				}
				count++
			}
		}
	}
	if count != 39060 {
		t.Fatalf("wrong finite conductor scope: %d", count)
	}
	delta.SetInt64(0)
	if err := Conductor(&delta, &b, &gamma, &w); err == nil {
		t.Fatal("accepted a neutral conductor")
	}
}

// TestAffineComposition checks chronological order and both supported destination aliases.
func TestAffineComposition(t *testing.T) {
	var first, second, composed AffineData
	var w Workspace
	first.P.SetInt64(2)
	first.B.SetInt64(3)
	first.Q.SetInt64(5)
	second.P.SetInt64(-4)
	second.B.SetInt64(7)
	second.Q.SetInt64(-2)
	if err := AffineThen(&first, &second, &composed, &w); err != nil {
		t.Fatal(err)
	}
	if composed.P.Int64() != -8 || composed.B.Int64() != 23 || composed.Q.Int64() != -10 {
		t.Fatal("incorrect chronological composition")
	}
	var x, intermediate, expected, actual big.Rat
	x.SetFrac64(3, 7)
	if err := RationalAction(&first, &x, &intermediate, &w); err != nil {
		t.Fatal(err)
	}
	if err := RationalAction(&second, &intermediate, &expected, &w); err != nil {
		t.Fatal(err)
	}
	if err := RationalAction(&composed, &x, &actual, &w); err != nil {
		t.Fatal(err)
	}
	if actual.Cmp(&expected) != 0 || actual.RatString() != "-137/70" {
		t.Fatal("composition changed the rational function")
	}
	if err := AffineThen(&first, &second, &first, &w); err != nil {
		t.Fatal(err)
	}
	if first.P.Cmp(&composed.P) != 0 || first.B.Cmp(&composed.B) != 0 ||
		first.Q.Cmp(&composed.Q) != 0 {
		t.Fatal("first-input destination alias was corrupted")
	}
	first.P.SetInt64(2)
	first.B.SetInt64(3)
	first.Q.SetInt64(5)
	if err := AffineThen(&first, &second, &second, &w); err != nil {
		t.Fatal(err)
	}
	if second.P.Cmp(&composed.P) != 0 || second.B.Cmp(&composed.B) != 0 ||
		second.Q.Cmp(&composed.Q) != 0 {
		t.Fatal("second-input destination alias was corrupted")
	}
}

// TestOffsetAndGuardControls separates full offset data from legal itinerary closure.
func TestOffsetAndGuardControls(t *testing.T) {
	var w Workspace
	var data AffineData
	var candidate, endpoint big.Int
	p, err := ParseParameters("3", "5", "2")
	if err != nil {
		t.Fatal(err)
	}
	ExponentWord(&p, []uint64{2}, &data, &w)
	if data.P.Int64() != 3 || data.B.Int64() != 5 || data.Q.Int64() != 4 {
		t.Fatal("the full offset lost its additive factor")
	}
	integral, err := IntegralFixedPoint(&data, &candidate, &w)
	if err != nil || !integral || candidate.Int64() != 5 {
		t.Fatal("generalized fixed point was computed with c=1")
	}
	p.C.SetInt64(1)
	ExponentWord(&p, []uint64{0, 0, 3, 4}, &data, &w)
	integral, err = IntegralFixedPoint(&data, &candidate, &w)
	if err != nil || !integral || candidate.Int64() != 1 {
		t.Fatal("rational negative-control candidate changed")
	}
	expanded := []Letter{Affine, Affine, Affine, Divide, Divide, Divide,
		Affine, Divide, Divide, Divide, Divide}
	if ExecuteWord(&p, expanded, &candidate, &endpoint, &w) {
		t.Fatal("an integral relaxed fixed point was incorrectly accepted as a legal word")
	}
	p, err = ParseParameters("-5", "93", "-6")
	if err != nil {
		t.Fatal(err)
	}
	candidate.SetInt64(12)
	if ExecuteWord(&p, []Letter{Affine, Affine, Divide}, &candidate, &endpoint, &w) {
		t.Fatal("the excluded scaling h=3 destroyed guards but was accepted")
	}
	if err := RunChecks(); err != nil {
		t.Fatal(err)
	}
}
