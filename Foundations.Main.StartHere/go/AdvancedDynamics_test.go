// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"testing"
)

// TestLargeArithmetic checks exact growth, signed division and cancellation beyond int64.
func TestLargeArithmetic(t *testing.T) {
	p, err := ParseParameters("3", "1", "2")
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	var power, seed, expected, output big.Int
	power.Lsh(big.NewInt(1), 100)
	seed.Add(&power, big.NewInt(1))
	expected.Lsh(&power, 1)
	expected.Add(&expected, &power)
	expected.Add(&expected, big.NewInt(4))
	if !ExecuteWord(&p, []Letter{Affine}, &seed, &output, &w) ||
		output.Cmp(&expected) != 0 {
		t.Fatal("large affine execution disagrees with 3*2^100+4")
	}
	p.D.SetInt64(-2)
	seed.Neg(&power)
	expected.Rsh(&power, 1)
	if !ExecuteWord(&p, []Letter{Divide}, &seed, &output, &w) ||
		output.Cmp(&expected) != 0 {
		t.Fatal("large signed division disagrees with 2^99")
	}

	// The intermediate affine value is 2^80 and its divisor is -2^70.
	var q, c, d, intermediate big.Int
	q.Lsh(big.NewInt(1), 130)
	q.Add(&q, big.NewInt(3))
	intermediate.Lsh(big.NewInt(1), 80)
	c.Sub(&intermediate, &q)
	d.Lsh(big.NewInt(1), 70)
	d.Neg(&d)
	p, err = ParseParameters(q.String(), c.String(), d.String())
	if err != nil {
		t.Fatal(err)
	}
	seed.SetInt64(1)
	expected.SetInt64(-1024)
	word := []Letter{Affine, Divide}
	if !ExecuteWord(&p, word, &seed, &output, &w) || output.Cmp(&expected) != 0 {
		t.Fatal("large signed cancellation disagrees with -2^10")
	}
	var data AffineData
	var x, value big.Rat
	ExponentWord(&p, []uint64{1}, &data, &w)
	if data.P.Cmp(&q) != 0 || data.B.Cmp(&c) != 0 || data.Q.Cmp(&d) != 0 {
		t.Fatal("large exponent data changed a signed parameter")
	}
	x.SetInt64(1)
	if err := RationalAction(&data, &x, &value, &w); err != nil {
		t.Fatal(err)
	}
	if !value.IsInt() || value.Num().Cmp(&expected) != 0 {
		t.Fatal("large rational relaxation disagrees with guarded execution")
	}
	var delta, offset, conductor big.Int
	delta.Mul(&power, big.NewInt(-21))
	offset.Mul(&power, big.NewInt(14))
	if err := Conductor(&delta, &offset, &conductor, &w); err != nil {
		t.Fatal(err)
	}
	if conductor.Cmp(big.NewInt(3)) != 0 {
		t.Fatal("large signed gcd produced the wrong conductor")
	}
}

// TestWordAndTraceAliasing verifies caller-owned input/output aliases, including failure.
func TestWordAndTraceAliasing(t *testing.T) {
	p, err := ParseParameters("3", "1", "2")
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	var state big.Int
	state.SetInt64(1)
	if ExecuteWord(&p, []Letter{Affine, Affine}, &state, &state, &w) {
		t.Fatal("accepted the second affine instruction at four")
	}
	if state.Int64() != 1 {
		t.Fatal("illegal aliased execution changed its input")
	}
	if !ExecuteWord(&p, []Letter{Affine, Divide}, &state, &state, &w) ||
		state.Int64() != 2 {
		t.Fatal("legal aliased execution lost its endpoint")
	}
	state.SetInt64(1)
	word := make([]Letter, 2)
	RawTrace(&p, word, &state, &state, &w)
	if state.Int64() != 2 || word[0] != Affine || word[1] != Divide {
		t.Fatal("aliased trace changed the itinerary or endpoint")
	}
	state.SetInt64(-11)
	RawTrace(&p, nil, &state, &state, &w)
	if state.Int64() != -11 {
		t.Fatal("empty aliased trace changed its initial state")
	}
}

// TestRepeatedComposition checks simultaneous operand and destination aliasing.
func TestRepeatedComposition(t *testing.T) {
	var data AffineData
	var w Workspace
	data.P.SetInt64(2)
	data.B.SetInt64(3)
	data.Q.SetInt64(5)
	if err := AffineThen(&data, &data, &data, &w); err != nil {
		t.Fatal(err)
	}
	if data.P.Int64() != 4 || data.B.Int64() != 21 || data.Q.Int64() != 25 {
		t.Fatal("self-composition corrupted an affine coefficient")
	}
	var x big.Rat
	x.SetFrac64(3, 7)
	if err := RationalAction(&data, &x, &x, &w); err != nil {
		t.Fatal(err)
	}
	if x.RatString() != "159/175" {
		t.Fatal("aliased rational evaluation changed its value")
	}
}

// TestRejectedArithmetic separates invalid, neutral and nonintegral affine candidates.
func TestRejectedArithmetic(t *testing.T) {
	var w Workspace
	var data, destination AffineData
	var output big.Int
	var x, value big.Rat
	output.SetInt64(77)
	x.SetFrac64(2, 3)
	value.SetFrac64(5, 7)
	destination.P.SetInt64(9)
	destination.B.SetInt64(8)
	destination.Q.SetInt64(7)
	if err := AffineThen(&data, &destination, &destination, &w); err == nil {
		t.Fatal("accepted a zero composition denominator")
	}
	if destination.P.Int64() != 9 || destination.B.Int64() != 8 ||
		destination.Q.Int64() != 7 {
		t.Fatal("failed composition changed its destination")
	}
	if err := RationalAction(&data, &x, &value, &w); err == nil {
		t.Fatal("accepted a zero evaluation denominator")
	}
	if value.RatString() != "5/7" {
		t.Fatal("failed rational evaluation changed its destination")
	}
	if ok, err := IntegralFixedPoint(&data, &output, &w); ok || err == nil {
		t.Fatal("accepted a zero fixed-point denominator")
	}
	for _, offset := range []int64{0, 1} {
		data.P.SetInt64(1)
		data.B.SetInt64(offset)
		data.Q.SetInt64(1)
		if ok, err := IntegralFixedPoint(&data, &output, &w); ok || err == nil {
			t.Fatal("accepted a neutral determinant as a unique fixed point")
		}
	}
	data.Q.SetInt64(3)
	if ok, err := IntegralFixedPoint(&data, &output, &w); ok || err != nil {
		t.Fatal("accepted the nonintegral fixed point 1/2")
	}
	if output.Int64() != 77 {
		t.Fatal("rejected fixed-point computation changed its destination")
	}
	p, err := ParseParameters("3", "1", "2")
	if err != nil {
		t.Fatal(err)
	}
	input := big.NewInt(1)
	if ExecuteWord(&p, []Letter{Letter(2)}, input, &output, &w) {
		t.Fatal("accepted an unknown raw instruction")
	}
	if output.Int64() != 77 {
		t.Fatal("unknown raw instruction changed its destination")
	}
	if err := RawWordAffine(&p, []Letter{Letter(2)}, &data, &w); err == nil {
		t.Fatal("relaxed an unknown raw instruction")
	}
	if _, err := ParseParameters("", "1", "2"); err == nil {
		t.Fatal("accepted an empty multiplier")
	}
	if _, err := ParseParameters("3", "1.0", "2"); err == nil {
		t.Fatal("accepted a noninteger offset")
	}
}
