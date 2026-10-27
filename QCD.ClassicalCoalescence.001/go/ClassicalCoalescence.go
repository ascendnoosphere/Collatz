// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"fmt"
	"math/big"
	"math/bits"
	"os"
	"sync"
)

// Workspace retains big-integer buffers for exact terminal-prefix trajectories.
type Workspace struct {
	Value    big.Int
	Power    big.Int
	Divisor  big.Int
	Quotient big.Int
	Expected big.Int
	Peak     big.Int
	One      big.Int
	Three    big.Int
}

// Prepare reserves the bounded terminal-test precision before stepping trajectories.
func (w *Workspace) Prepare() {
	w.One.SetInt64(1)
	w.Three.SetInt64(3)
	for _, z := range []*big.Int{
		&w.Value, &w.Power, &w.Divisor, &w.Quotient, &w.Expected, &w.Peak,
	} {
		z.Lsh(&w.One, 1024)
		z.SetInt64(0)
	}
}

// Apply takes one positive shortcut tick, reusing the prepared value buffer.
func (w *Workspace) Apply() {
	if w.Value.Bit(0) != 0 {
		w.Value.Mul(&w.Value, &w.Three)
		w.Value.Add(&w.Value, &w.One)
	}
	w.Value.Rsh(&w.Value, 1)
}

// Step evaluates bounded positive test states; the caller supplies overflow-safe ranges.
func Step(n uint64) uint64 {
	if n%2 == 0 {
		return n / 2
	}
	return (3*n + 1) / 2
}

// RawStep evaluates one division-first classical tick on bounded positive states.
func RawStep(n uint64) uint64 {
	if n%2 == 0 {
		return n / 2
	}
	return 3*n + 1
}

// Power computes small exact integer powers used by the finite coefficient checks.
func Power(x uint64, n int) uint64 {
	y := uint64(1)
	for j := 0; j < n; j++ {
		y *= x
	}
	return y
}

// Residual tests the exact odd-burst data of the written residual set.
func Residual(n uint64) bool {
	if n == 0 || n%2 == 0 {
		return false
	}
	a := bits.TrailingZeros64(n + 1)
	u := (n + 1) >> a
	if a < 2 || u%3 == 0 {
		return false
	}
	return Power(3, a)*u%4 == 3
}

// VerifyFamilies compares the universal cylinder formulas with their actual branch words.
func VerifyFamilies(limit int) error {
	for t := 0; t <= limit; t++ {
		j := uint64(t)
		n, p := 4+9*j, 3+8*j
		x := p
		for k, parity := range [3]uint64{1, 1, 0} {
			if x%2 != parity {
				return fmt.Errorf("inverse 110 guard: t=%d tick=%d", t, k)
			}
			x = Step(x)
		}
		if x != n || p >= n || 9*p >= 8*n {
			return fmt.Errorf("inverse 110 identity: t=%d", t)
		}
		n, x = 11+32*j, 11+32*j
		for k, parity := range [5]uint64{1, 1, 0, 1, 0} {
			if x%2 != parity {
				return fmt.Errorf("11010 guard: t=%d tick=%d", t, k)
			}
			x = Step(x)
		}
		if x != 10+27*j || x >= n || (t >= 1 && 9*x > 8*n) {
			return fmt.Errorf("11010 endpoint: t=%d", t)
		}
		n, p = 10+81*j, 7+64*j
		x = p
		for k, parity := range [6]uint64{1, 1, 1, 0, 1, 0} {
			if x%2 != parity {
				return fmt.Errorf("inverse 111010 guard: t=%d tick=%d", t, k)
			}
			x = Step(x)
		}
		if x != n || p >= n || 9*p >= 8*n {
			return fmt.Errorf("inverse 111010 identity: t=%d", t)
		}
		n, p = 31+1152*j, 27+1024*j
		if !Residual(n) || Step(Step(Step(p))) != n || p >= n {
			return fmt.Errorf("residual cylinder: t=%d", t)
		}
		// Both second-burst cylinders are new removals from the earlier residual.
		for _, pair := range [2]struct {
			source, parent         uint64
			sourceTime, parentTime int
		}{
			{411 + 1536*j, 231 + 864*j, 9, 5},
			{615 + 3072*j, 519 + 2592*j, 10, 5},
		} {
			n, p = pair.source, pair.parent
			x, y := n, p
			for k := 0; k < pair.sourceTime; k++ {
				x = Step(x)
			}
			for k := 0; k < pair.parentTime; k++ {
				y = Step(y)
			}
			if x != y || !Residual(n) || n%3 != 0 || n%32 == 11 ||
				n%9 == 4 || n%81 == 10 || 7*p > 6*n {
				return fmt.Errorf("second-burst cylinder: t=%d n=%d", t, n)
			}
		}
	}
	return nil
}

// VerifyResidualRules checks recovery choices on a finite interval, not global completeness.
func VerifyResidualRules(limit uint64) error {
	for n := uint64(2); n <= limit; n++ {
		p := uint64(0)
		sourceTime, parentTime := 0, 0
		switch {
		case n%2 == 0:
			p, sourceTime = n/2, 1
		case n%4 == 1:
			p, sourceTime = (3*n+1)/4, 2
		case n%3 == 2:
			p, parentTime = (2*n-1)/3, 1
		default:
			a := bits.TrailingZeros64(n + 1)
			u := (n + 1) >> a
			if Power(3, a)*u%4 == 1 {
				p, sourceTime, parentTime = (n-1)/2, a+2, a+1
			} else if n%9 == 4 {
				p, parentTime = (8*n-5)/9, 3
			} else if n%32 == 11 {
				p, sourceTime = (27*n+23)/32, 5
			} else if n%81 == 10 {
				p, parentTime = (64*n-73)/81, 6
			} else {
				z := Power(3, a)*u + 1
				b := bits.TrailingZeros64(z) - 1
				v := z >> (b + 1)
				if (a == 2 || a == 3) && b >= 1 && Power(3, b)*v%4 == 1 {
					p, sourceTime, parentTime = (z-4)/4, a+b+3, b+1
				} else if drop, _ := PairedTailChoice(a, b, v); drop != 0 {
					p = (z >> (drop + 1)) - 1
					sourceTime, parentTime = a+b+9, b-drop+8
				}
			}
		}
		if p == 0 {
			if !Residual(n) || n%9 == 4 || n%32 == 11 || n%81 == 10 {
				return fmt.Errorf("residual uncovered guard: n=%d", n)
			}
			continue
		}
		if p >= n || 9*p > 8*n {
			return fmt.Errorf("parent order: n=%d p=%d", n, p)
		}
		x, y := n, p
		for k := 0; k < sourceTime; k++ {
			x = Step(x)
		}
		for k := 0; k < parentTime; k++ {
			y = Step(y)
		}
		if x != y {
			return fmt.Errorf("parent join: n=%d p=%d", n, p)
		}
	}
	return nil
}

// VerifySecondBursts checks both initial lengths with uint64-safe finite budgets.
func VerifySecondBursts(a int, limit uint64) (int, int, int, error) {
	if (a != 2 && a != 3) || limit < 7 || limit > 1000000 {
		return 0, 0, 0, fmt.Errorf("second-burst budget requires a=2 or 3, limit=7..1000000")
	}
	checked, removed, multiples := 0, 0, 0
	for n := uint64(1)<<a - 1; n <= limit; n += uint64(2) << a {
		u := (n + 1) >> a
		z := Power(3, a)*u + 1
		b := bits.TrailingZeros64(z) - 1
		v := z >> (b + 1)
		if b < 1 || (1+2*uint64(b%2))*(v%4)%4 != 1 {
			continue
		}
		p := (z - 4) / 4
		if v%2 == 0 || p == 0 || p >= n || 7*p > 6*n || 4*p+3 != Power(3, a)*u {
			return checked, removed, multiples, fmt.Errorf("second-burst order: n=%d", n)
		}
		x, y := n, p
		for j := 0; j < a; j++ {
			if x%2 != 1 {
				return checked, removed, multiples, fmt.Errorf("first odd run: n=%d", n)
			}
			x = Step(x)
		}
		if x%2 != 0 {
			return checked, removed, multiples, fmt.Errorf("burst entrance guard: n=%d", n)
		}
		x = Step(x)
		if x != (uint64(1)<<b)*v-1 {
			return checked, removed, multiples, fmt.Errorf("burst entrance value: n=%d", n)
		}
		// The odd-run lengths differ by one, including an empty parent run at b=1.
		for j := 0; j < b; j++ {
			if x%2 != 1 {
				return checked, removed, multiples, fmt.Errorf("source odd run: n=%d", n)
			}
			x = Step(x)
		}
		for j := 0; j < b-1; j++ {
			if y%2 != 1 {
				return checked, removed, multiples, fmt.Errorf("parent odd run: n=%d", n)
			}
			y = Step(y)
		}
		for j := 0; j < 2; j++ {
			if x%2 != 0 || y%2 != uint64(j) {
				return checked, removed, multiples, fmt.Errorf("terminal guards: n=%d", n)
			}
			x, y = Step(x), Step(y)
		}
		if x != y || x != (Power(3, b)*v-1)/4 {
			return checked, removed, multiples, fmt.Errorf("second-burst endpoint: n=%d", n)
		}
		checked++
		if Residual(n) && n%9 != 4 && n%32 != 11 && n%81 != 10 {
			removed++
			if n%3 == 0 {
				multiples++
			}
		}
	}
	return checked, removed, multiples, nil
}

// SecondBurstResidual retains exactly the residual before the paired-tail removals.
func SecondBurstResidual(n uint64) bool {
	// Below this cutoff, n+1 <= 2^32 gives 3^a*u <= 3^32, without overflow.
	if n > 1<<32 {
		var value big.Int
		value.SetUint64(n)
		return BigBurstResidual(&value, false)
	}
	if !Residual(n) || n%9 == 4 || n%32 == 11 || n%81 == 10 {
		return false
	}
	a := bits.TrailingZeros64(n + 1)
	if a != 2 && a != 3 {
		return true
	}
	u := (n + 1) >> a
	z := Power(3, a)*u + 1
	b := bits.TrailingZeros64(z) - 1
	v := z >> (b + 1)
	return b < 1 || Power(3, b)*v%4 != 1
}

// FinalResidual retains the residual after both proved paired-tail removals.
func FinalResidual(n uint64) bool {
	// Larger inputs may overflow the burst numerator even when its valuation fits.
	if n > 1<<32 {
		var value big.Int
		value.SetUint64(n)
		return BigBurstResidual(&value, true)
	}
	if !SecondBurstResidual(n) {
		return false
	}
	a := bits.TrailingZeros64(n + 1)
	u := (n + 1) >> a
	z := Power(3, a)*u + 1
	b := bits.TrailingZeros64(z) - 1
	v := z >> (b + 1)
	drop, _ := PairedTailChoice(a, b, v)
	return drop == 0
}

// PairedTailChoice selects only the proved ranks and congruences, with chronological masks.
func PairedTailChoice(a, b int, v uint64) (int, uint64) {
	if a < 2 || a > 6 || b < 2 {
		return 0, 0
	}
	guard := Power(3, b) * v % 256
	if a >= 4 && a <= 6 && b >= 3 && guard == 129 {
		return 3, 128
	}
	if a >= 2 && a <= 4 && b >= 2 && guard == 43 {
		return 2, 130
	}
	return 0, 0
}

// VerifyPairedTails checks uint64-safe source budgets and every chronological guard.
func VerifyPairedTails(drop, a int, limit uint64) (int, int, int, error) {
	valid := (drop == 3 && a >= 4 && a <= 6) || (drop == 2 && a >= 2 && a <= 4)
	if !valid || limit < 63 || limit > 1000000 {
		return 0, 0, 0, fmt.Errorf("paired-tail budget requires proved ranks, limit=63..1000000")
	}
	checked, removed, multiples := 0, 0, 0
	for n := uint64(1)<<a - 1; n <= limit; n += uint64(2) << a {
		u := (n + 1) >> a
		z := Power(3, a)*u + 1
		b := bits.TrailingZeros64(z) - 1
		v := z >> (b + 1)
		actual, sourceMask := PairedTailChoice(a, b, v)
		if actual != drop {
			continue
		}
		p := (z >> (drop + 1)) - 1
		if p == 0 || p >= n || 9*p > 8*n ||
			(drop == 3 && 1024*p > 729*n) || (drop == 2 && 128*p > 81*n) {
			return checked, removed, multiples, fmt.Errorf("paired-tail order: n=%d", n)
		}
		x, y := n, p
		for j := 0; j < a; j++ {
			if x%2 != 1 {
				return checked, removed, multiples, fmt.Errorf("paired first run: n=%d", n)
			}
			x = Step(x)
		}
		if x%2 != 0 {
			return checked, removed, multiples, fmt.Errorf("paired entrance: n=%d", n)
		}
		x = Step(x)
		for j := 0; j < b; j++ {
			if x%2 != 1 {
				return checked, removed, multiples, fmt.Errorf("paired source run: n=%d", n)
			}
			x = Step(x)
		}
		for j := 0; j < b-drop; j++ {
			if y%2 != 1 {
				return checked, removed, multiples, fmt.Errorf("paired parent run: n=%d", n)
			}
			y = Step(y)
		}
		for j := 0; j < 8; j++ {
			if x%2 != sourceMask>>j&1 || y%2 != uint64(58)>>j&1 {
				return checked, removed, multiples, fmt.Errorf("paired tail guard: n=%d j=%d", n, j)
			}
			x, y = Step(x), Step(y)
		}
		if x != y || x != (Power(3, b+4-drop)*v+125)/256 {
			return checked, removed, multiples, fmt.Errorf("paired tail endpoint: n=%d", n)
		}
		checked++
		if SecondBurstResidual(n) {
			removed++
			if n%3 == 0 {
				multiples++
			}
		}
	}
	return checked, removed, multiples, nil
}

// VerifyTailCylinders checks whole-cylinder formulas over a bounded parameter range.
func VerifyTailCylinders(limit int) error {
	if limit < 0 || limit > 10000 {
		return fmt.Errorf("paired-cylinder budget requires limit=0..10000")
	}
	for t := 0; t <= limit; t++ {
		j := uint64(t)
		for _, pair := range [2]struct {
			n, p, endpoint uint64
			sourceTime     int
		}{
			{137199 + 5308416*j, 43410 + 1679616*j, 13736 + 531441*j, 16},
			{7803 + 663552*j, 2194 + 186624*j, 695 + 59049*j, 13},
		} {
			x, y := pair.n, pair.p
			for k := 0; k < pair.sourceTime; k++ {
				x = Step(x)
			}
			for k := 0; k < 8; k++ {
				y = Step(y)
			}
			if x != pair.endpoint || y != x || !SecondBurstResidual(pair.n) ||
				pair.n%3 != 0 || pair.p == 0 || pair.p >= pair.n || 9*pair.p > 8*pair.n {
				return fmt.Errorf("paired cylinder: t=%d n=%d", t, pair.n)
			}
		}
	}
	return nil
}

// DirectCylinder records one uniform direct-descent certificate.
type DirectCylinder struct {
	Source       uint64
	Modulus      uint64
	Parent       uint64
	Slope        uint64
	Word         string
	ShortcutTime int
	RawTime      int
}

// FurtherDirectCylinders records the twenty-one prefix-free direct families.
var FurtherDirectCylinders = [...]DirectCylinder{
	{347, 1024, 248, 729, "1101110100", 10, 16},
	{423, 1024, 302, 729, "1110110100", 10, 16},
	{2203, 4096, 1177, 2187, "110111101000", 12, 19},
	{3675, 4096, 1963, 2187, "110111011000", 12, 19},
	{2907, 4096, 1553, 2187, "110111010100", 12, 19},
	{1787, 4096, 955, 2187, "110110111000", 12, 19},
	{1019, 4096, 545, 2187, "110110110100", 12, 19},
	{3143, 4096, 1679, 2187, "111010110100", 12, 19},
	{3911, 4096, 2089, 2187, "111010111000", 12, 19},
	{1703, 4096, 910, 2187, "111011011000", 12, 19},
	{935, 4096, 500, 2187, "111011010100", 12, 19},
	{231, 4096, 124, 2187, "111011101000", 12, 19},
	{3119, 4096, 1666, 2187, "111101011000", 12, 19},
	{2351, 4096, 1256, 2187, "111101010100", 12, 19},
	{1647, 4096, 880, 2187, "111101101000", 12, 19},
	{879, 4096, 470, 2187, "111101100100", 12, 19},
	{2031, 4096, 1085, 2187, "111101110000", 12, 19},
	{2591, 4096, 1384, 2187, "111110101000", 12, 19},
	{1823, 4096, 974, 2187, "111110100100", 12, 19},
	{2975, 4096, 1589, 2187, "111110110000", 12, 19},
	{2239, 4096, 1196, 2187, "111111010000", 12, 19},
}

// InEarlierDirectCylinder recognizes the eight direct families removed before R_D.
func InEarlierDirectCylinder(n uint64) bool {
	if n%256 == 123 || n%256 == 175 || n%256 == 199 {
		return true
	}
	for _, residue := range [5]uint64{287, 367, 507, 583, 815} {
		if n%1024 == residue {
			return true
		}
	}
	return false
}

// DirectReducedResidual tests membership in the written residual R_D.
func DirectReducedResidual(n uint64) bool {
	return FinalResidual(n) && !InEarlierDirectCylinder(n)
}

// InFurtherDirectCylinder recognizes the twenty-one newly selected dyadic sources.
func InFurtherDirectCylinder(n uint64) bool {
	for _, family := range FurtherDirectCylinders {
		if n%family.Modulus == family.Source {
			return true
		}
	}
	return false
}

// VerifyFurtherDirectCylinders checks all clocks and each complete 1296-class period.
func VerifyFurtherDirectCylinders(limit int) (int, error) {
	if limit < 0 || limit > 10000 {
		return 0, fmt.Errorf("further-cylinder budget requires limit=0..10000")
	}
	densityUnits := 0
	for index, family := range FurtherDirectCylinders {
		for t := 0; t <= limit; t++ {
			j := uint64(t)
			n := family.Source + family.Modulus*j
			p := family.Parent + family.Slope*j
			x, oddCount := n, 0
			for k := 0; k < family.ShortcutTime; k++ {
				parity := x % 2
				if parity != uint64(family.Word[k]-'0') {
					return 0, fmt.Errorf("further-cylinder guard: n=%d tick=%d", n, k)
				}
				oddCount += int(parity)
				x = Step(x)
			}
			if x != p || p == 0 || 4*p >= 3*n ||
				family.ShortcutTime+oddCount != family.RawTime {
				return 0, fmt.Errorf("further-cylinder endpoint: n=%d", n)
			}
			x = n
			for k := 0; k < family.RawTime; k++ {
				x = RawStep(x)
			}
			if x != p {
				return 0, fmt.Errorf("further-cylinder raw clock: n=%d", n)
			}
		}
		count := 0
		for t := uint64(0); t < 1296; t++ {
			n := family.Source + family.Modulus*t
			if DirectReducedResidual(n) {
				count++
			}
		}
		expected := 704
		if index == 0 || index == 1 || family.Source == 2031 {
			expected = 660
		}
		if family.Source == 2203 || family.Source == 231 || family.Source == 1647 {
			expected = 616
		}
		if count != expected {
			return 0, fmt.Errorf("further-cylinder residual count: r=%d count=%d",
				family.Source, count)
		}
		weight := 1
		if family.Modulus == 1024 {
			weight = 4
		}
		densityUnits += weight * count
	}
	if densityUnits != 18348 {
		return 0, fmt.Errorf("further-cylinder density units: %d", densityUnits)
	}
	return densityUnits / 2, nil
}

// BigMod returns the least nonnegative residue of a nonnegative big integer.
func BigMod(n *big.Int, modulus uint64) uint64 {
	var divisor, residue big.Int
	divisor.SetUint64(modulus)
	residue.Mod(n, &divisor)
	return residue.Uint64()
}

// BigTrailingZeros returns the two-adic valuation of a positive big integer.
func BigTrailingZeros(n *big.Int) int {
	valuation := 0
	for n.Bit(valuation) == 0 {
		valuation++
	}
	return valuation
}

// BigBurstResidual tests the second-burst residual and optionally removes paired tails.
// It keeps the burst numerator exact, including its odd factor after a long division run.
func BigBurstResidual(n *big.Int, paired bool) bool {
	if n.Sign() <= 0 || n.Bit(0) == 0 {
		return false
	}
	var shifted, u, power, z, v, product big.Int
	shifted.Add(n, big.NewInt(1))
	a := BigTrailingZeros(&shifted)
	u.Rsh(&shifted, uint(a))
	if a < 2 || BigMod(&u, 3) == 0 {
		return false
	}
	power.Exp(big.NewInt(3), big.NewInt(int64(a)), nil)
	product.Mul(&power, &u)
	if BigMod(&product, 4) != 3 || BigMod(n, 9) == 4 ||
		BigMod(n, 32) == 11 || BigMod(n, 81) == 10 {
		return false
	}
	z.Add(&product, big.NewInt(1))
	b := BigTrailingZeros(&z) - 1
	v.Rsh(&z, uint(b+1))
	power.Exp(big.NewInt(3), big.NewInt(int64(b)), nil)
	product.Mul(&power, &v)
	if (a == 2 || a == 3) && b >= 1 && BigMod(&product, 4) == 1 {
		return false
	}
	if !paired {
		return true
	}
	guard := BigMod(&product, 256)
	return !((a >= 4 && a <= 6 && b >= 3 && guard == 129) ||
		(a >= 2 && a <= 4 && b >= 2 && guard == 43))
}

// BigDirectReducedResidual evaluates every defining guard of R_D without word-size bounds.
func BigDirectReducedResidual(n *big.Int) bool {
	if !BigBurstResidual(n, true) {
		return false
	}
	residue256 := BigMod(n, 256)
	if residue256 == 123 || residue256 == 175 || residue256 == 199 {
		return false
	}
	residue1024 := BigMod(n, 1024)
	for _, residue := range [5]uint64{287, 367, 507, 583, 815} {
		if residue1024 == residue {
			return false
		}
	}
	return true
}

// VerifyDeepCertificates checks the 2075, 27, and 111 families independently.
func VerifyDeepCertificates(limit int) (int, int, error) {
	if limit < 0 || limit > 10000 {
		return 0, 0, fmt.Errorf("deep-certificate budget requires limit=0..10000")
	}
	for t := 0; t <= limit; t++ {
		j := uint64(t)
		n, p := 2075+8192*j, 1663+6561*j
		x, oddCount := n, 0
		word := "1101111101000"
		for k := 0; k < len(word); k++ {
			parity := x % 2
			if parity != uint64(word[k]-'0') {
				return 0, 0, fmt.Errorf("2075-cylinder guard: t=%d tick=%d", t, k)
			}
			oddCount += int(parity)
			x = Step(x)
		}
		if x != p || oddCount != 8 || p == 0 || 6*p > 5*n {
			return 0, 0, fmt.Errorf("2075-cylinder endpoint: t=%d", t)
		}

		n, p = 111+(uint64(1)<<15)*Power(3, 7)*j, 103+(uint64(1)<<26)*j
		x = p
		word = "111011110100"
		for k := 0; k < len(word); k++ {
			if x%2 != uint64(word[k]-'0') {
				return 0, 0, fmt.Errorf("111-parent guard: t=%d tick=%d", t, k)
			}
			x = Step(x)
		}
		if x != Step(n) || p == 0 || p >= n || 123*p > 118*n ||
			!DirectReducedResidual(n) || InFurtherDirectCylinder(n) {
			return 0, 0, fmt.Errorf("111-parent certificate: t=%d", t)
		}
	}

	// Big integers keep every intermediate state exact on the deep cylinder.
	two59 := new(big.Int).Lsh(big.NewInt(1), 59)
	three37 := new(big.Int).Exp(big.NewInt(3), big.NewInt(37), nil)
	one, three := big.NewInt(1), big.NewInt(3)
	six, seven := big.NewInt(6), big.NewInt(7)
	twentyThree, twentySeven := big.NewInt(23), big.NewInt(27)
	var index, n, p, x, left, right big.Int
	for t := 0; t <= limit; t++ {
		index.SetInt64(int64(t))
		n.Mul(two59, &index)
		n.Add(&n, twentySeven)
		p.Mul(three37, &index)
		p.Add(&p, twentyThree)
		x.Set(&n)
		oddCount := 0
		for k := 0; k < 59; k++ {
			if x.Bit(0) == 0 {
				x.Rsh(&x, 1)
			} else {
				oddCount++
				x.Mul(&x, three)
				x.Add(&x, one)
				x.Rsh(&x, 1)
			}
		}
		left.Mul(seven, &p)
		right.Mul(six, &n)
		if x.Cmp(&p) != 0 || oddCount != 37 || left.Cmp(&right) > 0 {
			return 0, 0, fmt.Errorf("27-cylinder endpoint: t=%d", t)
		}
	}

	count2075 := 0
	for t := uint64(0); t < 648; t++ {
		if DirectReducedResidual(2075 + 8192*t) {
			count2075++
		}
	}
	count27 := 0
	for t := uint64(0); t < 81; t++ {
		index.SetUint64(t)
		n.Mul(two59, &index)
		n.Add(&n, twentySeven)
		claimed := t%3 != 1 && t%9 != 8 && t%81 != 2
		actual := BigDirectReducedResidual(&n)
		if actual != claimed {
			return count2075, count27, fmt.Errorf("deep 27 residual guard: t=%d", t)
		}
		if actual {
			count27++
		}
	}
	if count2075 != 308 || count27 != 44 {
		return count2075, count27, fmt.Errorf("deep residual counts: %d %d",
			count2075, count27)
	}
	return count2075, count27, nil
}

// VerifyDirectDescentCylinders checks seven descents and their exact residual periods.
func VerifyDirectDescentCylinders(limit int) (int, error) {
	if limit < 0 || limit > 10000 {
		return 0, fmt.Errorf("direct-cylinder budget requires limit=0..10000")
	}
	families := [...]DirectCylinder{
		{175, 256, 167, 243, "11110100", 8, 13},
		{199, 256, 190, 243, "11101010", 8, 13},
		{287, 1024, 205, 729, "1111101000", 10, 16},
		{367, 1024, 262, 729, "1111011000", 10, 16},
		{507, 1024, 362, 729, "1101101100", 10, 16},
		{583, 1024, 416, 729, "1110101100", 10, 16},
		{815, 1024, 581, 729, "1111010100", 10, 16},
	}
	totalCount := 0
	for _, family := range families {
		for t := 0; t <= limit; t++ {
			j := uint64(t)
			n := family.Source + family.Modulus*j
			p := family.Parent + family.Slope*j
			x := n
			oddCount := 0
			for k := 0; k < family.ShortcutTime; k++ {
				parity := x % 2
				if parity != uint64(family.Word[k]-'0') {
					return 0, fmt.Errorf("direct-cylinder guard: n=%d tick=%d", n, k)
				}
				oddCount += int(parity)
				x = Step(x)
			}
			if x != p || p == 0 || p >= n || 24*p > 23*n ||
				family.ShortcutTime+oddCount != family.RawTime {
				return 0, fmt.Errorf("direct-cylinder endpoint: n=%d", n)
			}
			x = n
			for k := 0; k < family.RawTime; k++ {
				x = RawStep(x)
			}
			if x != p {
				return 0, fmt.Errorf("direct-cylinder raw clock: n=%d", n)
			}
		}
		count := 0
		for t := uint64(0); t < 81; t++ {
			n := family.Source + family.Modulus*t
			a := bits.TrailingZeros64(n + 1)
			u := (n + 1) >> a
			expected := u%3 != 0 && n%9 != 4 && n%81 != 10
			actual := FinalResidual(n)
			if actual != expected || FinalResidual(n+81*family.Modulus) != expected {
				return totalCount, fmt.Errorf("direct-cylinder residual class: n=%d", n)
			}
			if actual {
				count++
			}
		}
		if count != 44 {
			return totalCount, fmt.Errorf("direct-cylinder residual count: %d", count)
		}
		totalCount += count
	}
	return totalCount, nil
}

// VerifyEightLetterCylinder checks both clocks and one complete residual period.
func VerifyEightLetterCylinder(limit int) (int, error) {
	if limit < 0 || limit > 10000 {
		return 0, fmt.Errorf("eight-letter budget requires limit=0..10000")
	}
	for t := 0; t <= limit; t++ {
		j := uint64(t)
		n, p := 123+256*j, 118+243*j
		x := n
		for k, parity := range [8]uint64{1, 1, 0, 1, 1, 0, 1, 0} {
			if x%2 != parity {
				return 0, fmt.Errorf("eight-letter guard: t=%d tick=%d", t, k)
			}
			x = Step(x)
		}
		if x != p || p == 0 || p >= n || 123*p > 118*n {
			return 0, fmt.Errorf("eight-letter endpoint: t=%d", t)
		}
		x = n
		for k := 0; k < 13; k++ {
			x = RawStep(x)
		}
		if x != p {
			return 0, fmt.Errorf("eight-letter raw clock: t=%d", t)
		}
	}
	count := 0
	for t := uint64(0); t < 2592; t++ {
		n := 123 + 256*t
		expected := t%3 != 2 && t%9 != 4 && t%81 != 10 && t%32 != 30
		if FinalResidual(n) != expected {
			return count, fmt.Errorf("eight-letter residual class: t=%d", t)
		}
		if expected {
			count++
		}
	}
	if count != 1364 {
		return count, fmt.Errorf("eight-letter residual count: %d", count)
	}
	return count, nil
}

// WordData composes the shortcut rational branches in chronological bit order.
func WordData(mask uint64, h int) (int64, int64, int64) {
	p, q, b := int64(1), int64(1), int64(0)
	for j := 0; j < h; j++ {
		if mask>>j&1 != 0 {
			p, b = 3*p, 3*b+q
		}
		q *= 2
	}
	return p, q, b
}

// LegalRepeated tests complete copies without allocating a parity slice.
func LegalRepeated(mask uint64, h int, n uint64, k int) bool {
	for copy := 0; copy < k; copy++ {
		for j := 0; j < h; j++ {
			if n%2 != mask>>j&1 {
				return false
			}
			n = Step(n)
		}
	}
	return true
}

// VerifyBudgets checks all words through length eight against exact displacement divisibility.
func VerifyBudgets() (int, error) {
	count := 0
	for h := 1; h <= 8; h++ {
		for mask := uint64(0); mask < uint64(1)<<h; mask++ {
			p, q, b := WordData(mask, h)
			for n := uint64(1); n <= 256; n++ {
				d := (p-q)*int64(n) + b
				qk := int64(1)
				for k := 0; k <= 3; k++ {
					if LegalRepeated(mask, h, n, k) != (d%qk == 0) {
						return count, fmt.Errorf("budget: h=%d mask=%d n=%d k=%d", h, mask, n, k)
					}
					count++
					qk *= q
				}
			}
		}
	}
	return count, nil
}

// SupportNumerator computes ordered suffix weights on the bounded support window.
func SupportNumerator(mask uint64, h int) uint64 {
	a, multiplier := uint64(0), uint64(1)
	for j := h - 1; j >= 0; j-- {
		if mask>>j&1 != 0 {
			a += multiplier * (uint64(1) << j)
			multiplier *= 3
		}
	}
	return a
}

// VerifyCrossings exhausts windows through twelve with at most three interior common letters.
func VerifyCrossings() (int, error) {
	count := 0
	for h := 2; h <= 12; h++ {
		for lo := 0; lo < h; lo++ {
			for hi := lo + 1; hi < h; hi++ {
				endpoints := uint64(1)<<lo | uint64(1)<<hi
				interior := (uint64(1)<<hi - 1) & ^(uint64(1)<<(lo+1) - 1)
				for c := uint64(0); c < uint64(1)<<h; c++ {
					if c&endpoints != 0 || bits.OnesCount64(c&interior) > 3 {
						continue
					}
					r := bits.OnesCount64(c) + 1
					m := uint64(1)<<h + Power(3, r)
					u := SupportNumerator(c|uint64(1)<<lo, h)
					v := SupportNumerator(c|uint64(1)<<hi, h)
					if v <= u || (v-u)%m == 0 {
						return count, fmt.Errorf("crossing: h=%d lo=%d hi=%d c=%d", h, lo, hi, c)
					}
					count++
				}
			}
		}
	}
	return count, nil
}

// VerifyFiveCompositions checks the entire bounded exponent family, without orbit search.
func VerifyFiveCompositions() (int, error) {
	count := 0
	for a := 1; a <= 4; a++ {
		for b := 1; b <= 4; b++ {
			for c := 1; c <= 4; c++ {
				for d := 1; d <= 4; d++ {
					e := 8 - a - b - c - d
					if e < 1 {
						continue
					}
					n := 81 + 27*Power(2, a) + 9*Power(2, a+b) +
						3*Power(2, a+b+c) + Power(2, a+b+c+d)
					if n%13 == 0 {
						return count, fmt.Errorf("five composition: %d,%d,%d,%d,%d", a, b, c, d, e)
					}
					count++
				}
			}
		}
	}
	return count, nil
}

// VerifyTerminal checks endpoint, first-arrival and peak formulas with exact big integers.
func VerifyTerminal() error {
	var w Workspace
	w.Prepare()
	for a := 2; a <= 4; a++ {
		for t := 1; t <= 5; t += 2 {
			l := int(Power(3, a)) * t
			w.Power.Lsh(&w.One, uint(l))
			w.Quotient.Add(&w.Power, &w.One)
			w.Divisor.SetUint64(Power(3, a+1))
			w.Quotient.Quo(&w.Quotient, &w.Divisor)
			w.Value.Lsh(&w.Quotient, uint(a))
			w.Value.Sub(&w.Value, &w.One)
			w.Expected.Lsh(&w.One, uint(l-2))
			w.Peak.Sub(&w.Power, &w.One)
			w.Peak.Sub(&w.Peak, &w.One)
			w.Peak.Quo(&w.Peak, &w.Three)
			for j := 0; j <= a+l; j++ {
				if j < a+l && w.Value.Cmp(&w.One) <= 0 {
					return fmt.Errorf("terminal early hit: a=%d t=%d j=%d", a, t, j)
				}
				if j == a && w.Value.Cmp(&w.Peak) != 0 {
					return fmt.Errorf("terminal peak: a=%d t=%d", a, t)
				}
				if j != a && w.Value.Cmp(&w.Peak) >= 0 {
					return fmt.Errorf("terminal peak uniqueness: a=%d t=%d j=%d", a, t, j)
				}
				if j == a+2 && w.Value.Cmp(&w.Expected) != 0 {
					return fmt.Errorf("terminal endpoint: a=%d t=%d", a, t)
				}
				if j == a+l && w.Value.Cmp(&w.One) != 0 {
					return fmt.Errorf("terminal final hit: a=%d t=%d", a, t)
				}
				w.Apply()
			}
		}
	}
	return nil
}

// main executes the bounded consistency checks accompanying the written proofs.
func main() {
	if err := VerifyFamilies(10000); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := VerifyResidualRules(100000); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	// Each initial burst has its own exhaustive arithmetic-guard check.
	for _, a := range [2]int{2, 3} {
		second, removed, multiples, err := VerifySecondBursts(a, 1000000)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		fmt.Printf("second bursts a=%d through 1000000: %d; removed: %d; multiples: %d\n",
			a, second, removed, multiples)
	}
	if err := VerifyTailCylinders(10000); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	directCount, err := VerifyDirectDescentCylinders(10000)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	eightLetter, err := VerifyEightLetterCylinder(10000)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	furtherDensity, err := VerifyFurtherDirectCylinders(10000)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	count2075, count27, err := VerifyDeepCertificates(10000)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	families := [6]struct{ drop, a int }{
		{3, 4}, {3, 5}, {3, 6}, {2, 2}, {2, 3}, {2, 4},
	}
	var results [6]struct {
		checked, removed, multiples int
		err                         error
	}
	var wait sync.WaitGroup
	// Each independent rank has one writer; reporting waits for all six chunks.
	for i, family := range families {
		wait.Add(1)
		go func(index, drop, a int) {
			defer wait.Done()
			r := &results[index]
			r.checked, r.removed, r.multiples, r.err = VerifyPairedTails(drop, a, 1000000)
		}(i, family.drop, family.a)
	}
	wait.Wait()
	for i, family := range families {
		r := &results[i]
		if r.err != nil {
			fmt.Fprintln(os.Stderr, r.err)
			os.Exit(1)
		}
		fmt.Printf("paired tails drop=%d a=%d: %d; removed: %d; multiples: %d\n",
			family.drop, family.a, r.checked, r.removed, r.multiples)
	}
	budgets, err := VerifyBudgets()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	crossings, err := VerifyCrossings()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	compositions, err := VerifyFiveCompositions()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := VerifyTerminal(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	fmt.Printf("parent cylinders: t=0..10000; residual rules: n=2..100000\n")
	fmt.Printf("seven direct cylinders: t=0..10000; residual classes: %d/567\n", directCount)
	fmt.Printf("eight-letter cylinder: t=0..10000; residual period: %d/2592\n", eightLetter)
	fmt.Printf("further direct density: %d/2654208; deep counts: %d/648, %d/81\n",
		furtherDensity, count2075, count27)
	fmt.Printf("repeated-word instances: %d; crossing configurations: %d\n", budgets, crossings)
	fmt.Printf("five-return compositions: %d; terminal cases: 9\n", compositions)
}
