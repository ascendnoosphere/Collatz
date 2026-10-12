// SPDX-License-Identifier: CC-BY-4.0
//
// Exact integer checks for the divided-branch congruence. Odd positive q and c
// make q*n+c even whenever n is odd. On a finite grid of contracting words,
// the full-phase defect is zero or at least 2/(q+2), and a defect below that
// threshold has vanishing carries. The grid is not the uniform statement.

package main

import (
	"fmt"
	"math/big"
	"os"
	"sync"
)

const (
	phaseRigidMaxQ     = 15
	phaseRigidMaxN     = 40
	phaseRigidWordQMax = 5
	phaseRigidWordCMax = 5
	phaseRigidWordLen  = 4
)

// Totals counts checks and failures for one slice of the grid.
type Totals struct {
	Checks   uint64
	Failures uint64
}

// Workspace holds the integer buffers reused while one word is evaluated.
type Workspace struct {
	P    *big.Int
	B    *big.Int
	Pow  *big.Int
	Acc  *big.Int
	Term  *big.Int
	Left  *big.Int
	Right *big.Int
}

// Cache holds one rational phase and the parity integer selected for it.
type Cache struct {
	Num  *big.Int
	Den  *big.Int
	Near *big.Int
}

// NewWorkspace returns buffers for one word evaluation.
func NewWorkspace() *Workspace {
	return &Workspace{
		P:     big.NewInt(1),
		B:     big.NewInt(0),
		Pow:   big.NewInt(1),
		Acc:   big.NewInt(0),
		Term:  big.NewInt(0),
		Left:  big.NewInt(0),
		Right: big.NewInt(0),
	}
}

// NewCache returns an empty phase slot.
func NewCache() *Cache {
	return &Cache{
		Num:  big.NewInt(0),
		Den:  big.NewInt(1),
		Near: big.NewInt(0),
	}
}

// check records one arithmetic comparison.
func (t *Totals) check(ok bool) {
	t.Checks++
	if !ok {
		t.Failures++
	}
}

// add merges another slice into the receiver.
func (t *Totals) add(o Totals) {
	t.Checks += o.Checks
	t.Failures += o.Failures
}

// phaseRigidOddNumeratorEven reports whether q*n+c is even.
func phaseRigidOddNumeratorEven(q, c, n uint64) bool {
	return (q*n+c)%2 == 0
}

// phaseRigidOddBranchExact reports the odd doubling identity.
func phaseRigidOddBranchExact(q, c, n uint64) bool {
	num := q*n + c
	if num%2 != 0 {
		return false
	}
	return 2*(num/2) == num
}

// phaseRigidEvenHalves reports whether n equals twice its quotient by two.
func phaseRigidEvenHalves(n uint64) bool {
	return 2*(n/2) == n
}

// sweepParityQ checks the parity identities for one odd multiplier.
func sweepParityQ(q uint64) Totals {
	var t Totals
	for c := uint64(1); c <= phaseRigidMaxQ; c += 2 {
		for n := uint64(0); n <= phaseRigidMaxN; n++ {
			if n%2 == 1 {
				t.check(phaseRigidOddNumeratorEven(q, c, n))
				t.check(phaseRigidOddBranchExact(q, c, n))
			} else {
				t.check(phaseRigidEvenHalves(n))
			}
		}
	}
	return t
}

// sweepParity checks the parity grid, one multiplier at a time.
func sweepParity() Totals {
	var qs []uint64
	for q := uint64(1); q <= phaseRigidMaxQ; q += 2 {
		qs = append(qs, q)
	}
	parts := make([]Totals, len(qs))
	var wg sync.WaitGroup
	for i, q := range qs {
		wg.Add(1)
		go func(i int, q uint64) {
			defer wg.Done()
			parts[i] = sweepParityQ(q)
		}(i, q)
	}
	wg.Wait()
	var total Totals
	for _, part := range parts {
		total.add(part)
	}
	return total
}

// sweepControls checks cells outside the odd-odd-odd hypothesis.
func sweepControls() Totals {
	var t Totals
	t.check(!phaseRigidOddNumeratorEven(3, 2, 1))
	t.check(!phaseRigidOddNumeratorEven(3, 1, 2))
	t.check(phaseRigidOddNumeratorEven(3, 1, 1))
	t.check(phaseRigidOddBranchExact(3, 1, 1))
	t.check(!phaseRigidEvenHalves(1))
	t.check(phaseRigidEvenHalves(2))
	return t
}

// ratNorm returns the reduced form of num/den with positive denominator.
func ratNorm(num, den *big.Int) (*big.Int, *big.Int) {
	n := new(big.Int).Set(num)
	d := new(big.Int).Set(den)
	if d.Sign() < 0 {
		n.Neg(n)
		d.Neg(d)
	}
	g := new(big.Int).GCD(nil, nil, n, d)
	n.Quo(n, g)
	d.Quo(d, g)
	return n, d
}

// positiveParity reports whether n is a positive integer of the named parity.
func positiveParity(n *big.Int, odd bool) bool {
	if n.Sign() <= 0 {
		return false
	}
	bit := n.Bit(0) == 1
	if odd {
		return bit
	}
	return !bit
}

// nearestPositive returns the nearest positive integer of the named parity.
// Ties choose the smaller integer. The search window is exact for a spacing
// of two, and the least positive integer covers a phase below that lattice.
func nearestPositive(num, den *big.Int, odd bool) *big.Int {
	floor := new(big.Int).Quo(num, den)
	if num.Sign() < 0 {
		rem := new(big.Int).Rem(num, den)
		if rem.Sign() != 0 {
			floor.Sub(floor, big.NewInt(1))
		}
	}
	var best *big.Int
	var bestAbs *big.Int
	consider := func(n *big.Int) {
		if !positiveParity(n, odd) {
			return
		}
		diff := new(big.Int).Mul(n, den)
		diff.Sub(num, diff)
		diff.Abs(diff)
		if best == nil || diff.Cmp(bestAbs) < 0 ||
			(diff.Cmp(bestAbs) == 0 && n.Cmp(best) < 0) {
			best = new(big.Int).Set(n)
			bestAbs = diff
		}
	}
	start := new(big.Int).Sub(floor, big.NewInt(3))
	cur := new(big.Int).Set(start)
	for i := 0; i <= 6; i++ {
		consider(cur)
		cur.Add(cur, big.NewInt(1))
	}
	if odd {
		consider(big.NewInt(1))
	} else {
		consider(big.NewInt(2))
	}
	return best
}

// applyBranch applies one divided branch to a reduced rational.
func applyBranch(q, c uint64, odd bool, num, den *big.Int) (*big.Int, *big.Int) {
	if odd {
		next := new(big.Int).Mul(new(big.Int).SetUint64(q), num)
		term := new(big.Int).Mul(new(big.Int).SetUint64(c), den)
		next.Add(next, term)
		return ratNorm(next, new(big.Int).Lsh(den, 1))
	}
	return ratNorm(num, new(big.Int).Lsh(den, 1))
}

// intBranch returns the integer divided branch when the parity is legal.
func intBranch(q, c uint64, odd bool, n *big.Int) (*big.Int, bool) {
	if odd {
		num := new(big.Int).Mul(new(big.Int).SetUint64(q), n)
		num.Add(num, new(big.Int).SetUint64(c))
		if num.Bit(0) == 1 {
			return nil, false
		}
		return num.Rsh(num, 1), true
	}
	if n.Bit(0) == 1 {
		return nil, false
	}
	out := new(big.Int).Rsh(n, 1)
	return out, true
}

// wordAffine writes the multiplier and constant of the divided word into w.
// The first letter is applied first. The constant already contains c.
func wordAffine(w *Workspace, q, c uint64, bits []bool) int {
	w.P.SetInt64(1)
	w.B.SetInt64(0)
	w.Pow.SetInt64(1)
	r := 0
	qb := new(big.Int).SetUint64(q)
	cb := new(big.Int).SetUint64(c)
	for _, odd := range bits {
		if odd {
			w.B.Mul(w.B, qb)
			w.Term.Mul(cb, w.Pow)
			w.B.Add(w.B, w.Term)
			w.P.Mul(w.P, qb)
			r++
		}
		w.Pow.Lsh(w.Pow, 1)
	}
	return r
}

// sumA returns the c-free defining sum of a divided word.
func sumA(w *Workspace, q uint64, bits []bool) *big.Int {
	w.Acc.SetInt64(0)
	onesAfter := 0
	qb := new(big.Int).SetUint64(q)
	for j := len(bits) - 1; j >= 0; j-- {
		if bits[j] {
			w.Term.Exp(qb, big.NewInt(int64(onesAfter)), nil)
			w.Term.Lsh(w.Term, uint(j))
			w.Acc.Add(w.Acc, w.Term)
			onesAfter++
		}
	}
	return new(big.Int).Set(w.Acc)
}

// ratLtThreshold reports num/den < 2/(q+2) for a positive denominator.
func ratLtThreshold(num, den *big.Int, q uint64) bool {
	left := new(big.Int).Mul(num, new(big.Int).SetUint64(q+2))
	right := new(big.Int).Lsh(den, 1)
	return left.Cmp(right) < 0
}

// PhaseRigidAudit checks one divided word and returns its reduced defect.
// A nil pair means the word is outside the contracting hypothesis.
func PhaseRigidAudit(q, c uint64, bits []bool, t *Totals) (*big.Int, *big.Int) {
	r := 0
	for _, odd := range bits {
		if odd {
			r++
		}
	}
	qq := uint64(1)
	for i := 0; i < r; i++ {
		qq *= q
	}
	pow := uint64(1)
	for i := 0; i < len(bits); i++ {
		pow *= 2
	}
	if r == 0 || qq >= pow {
		return nil, nil
	}
	w := NewWorkspace()
	gotR := wordAffine(w, q, c, bits)
	a := sumA(w, q, bits)
	pExp := new(big.Int).Exp(new(big.Int).SetUint64(q),
		big.NewInt(int64(gotR)), nil)
	cA := new(big.Int).Mul(new(big.Int).SetUint64(c), a)
	if t != nil {
		t.check(w.P.Cmp(pExp) == 0)
		t.check(w.B.Cmp(cA) == 0)
	}
	delta := new(big.Int).Sub(new(big.Int).Set(w.Pow), w.P)
	num, den := ratNorm(w.B, delta)
	if t != nil {
		t.check(delta.Sign() > 0)
		w.Left.Mul(num, delta)
		w.Right.Mul(w.B, den)
		t.check(w.Left.Cmp(w.Right) == 0)
	}
	start := NewCache()
	start.Num = num
	start.Den = den
	phases := []*Cache{start}
	curN, curD := num, den
	for _, odd := range bits {
		curN, curD = applyBranch(q, c, odd, curN, curD)
		slot := NewCache()
		slot.Num = curN
		slot.Den = curD
		phases = append(phases, slot)
	}
	if t != nil {
		last := len(bits)
		t.check(phases[last].Num.Cmp(phases[0].Num) == 0 &&
			phases[last].Den.Cmp(phases[0].Den) == 0)
	}
	eNum := big.NewInt(0)
	eDen := big.NewInt(1)
	for i, odd := range bits {
		near := nearestPositive(phases[i].Num, phases[i].Den, odd)
		phases[i].Near = near
		if t != nil {
			t.check(positiveParity(near, odd))
		}
		diff := new(big.Int).Mul(near, phases[i].Den)
		diff.Sub(phases[i].Num, diff)
		diff.Abs(diff)
		left := new(big.Int).Mul(diff, eDen)
		right := new(big.Int).Mul(eNum, phases[i].Den)
		if left.Cmp(right) > 0 {
			eNum = diff
			eDen = new(big.Int).Set(phases[i].Den)
		}
	}
	eNum, eDen = ratNorm(eNum, eDen)
	below := ratLtThreshold(eNum, eDen, q)
	if t != nil {
		t.check(eNum.Sign() == 0 || !below)
	}
	for i, odd := range bits {
		branch, ok := intBranch(q, c, odd, phases[i].Near)
		next := phases[0].Near
		if i+1 < len(bits) {
			next = phases[i+1].Near
		}
		if t != nil {
			t.check(ok)
		}
		if ok && below && t != nil {
			carry := new(big.Int).Sub(branch, next)
			t.check(carry.Sign() == 0)
		}
	}
	return eNum, eDen
}

// bitsOf reads a chronological word from the low bits of mask.
func bitsOf(mask uint64, length int) []bool {
	bits := make([]bool, length)
	for j := 0; j < length; j++ {
		bits[j] = (mask>>uint(j))&1 == 1
	}
	return bits
}

// sweepWordsQ checks every contracting word for one odd multiplier.
func sweepWordsQ(q uint64) Totals {
	var t Totals
	for c := uint64(1); c <= phaseRigidWordCMax; c += 2 {
		for length := 1; length <= phaseRigidWordLen; length++ {
			limit := uint64(1) << uint(length)
			for mask := uint64(1); mask < limit; mask++ {
				PhaseRigidAudit(q, c, bitsOf(mask, length), &t)
			}
		}
	}
	return t
}

// sweepWords checks the short-word grid in parallel over the multiplier.
func sweepWords() Totals {
	var qs []uint64
	for q := uint64(1); q <= phaseRigidWordQMax; q += 2 {
		qs = append(qs, q)
	}
	parts := make([]Totals, len(qs))
	var wg sync.WaitGroup
	for i, q := range qs {
		wg.Add(1)
		go func(i int, q uint64) {
			defer wg.Done()
			parts[i] = sweepWordsQ(q)
		}(i, q)
	}
	wg.Wait()
	var total Totals
	for _, part := range parts {
		total.add(part)
	}
	return total
}

// witnessBits is the length-16 word whose defect lies below 3/4.
func witnessBits() []bool {
	s := "1011100111110100"
	bits := make([]bool, len(s))
	for i := 0; i < len(s); i++ {
		bits[i] = s[i] == '1'
	}
	return bits
}

// sweepWitness checks the length-16 defect and the two short anchors.
func sweepWitness() Totals {
	var t Totals
	num, den := PhaseRigidAudit(3, 1, []bool{true, false}, &t)
	t.check(num != nil && num.Sign() == 0 && den.Cmp(big.NewInt(1)) == 0)
	num, den = PhaseRigidAudit(3, 1, []bool{true, false, false}, &t)
	t.check(num != nil && num.Cmp(big.NewInt(8)) == 0 &&
		den.Cmp(big.NewInt(5)) == 0)
	num, den = PhaseRigidAudit(3, 1, witnessBits(), &t)
	t.check(num != nil && num.Cmp(big.NewInt(4858)) == 0 &&
		den.Cmp(big.NewInt(6487)) == 0)
	if num != nil && den != nil {
		t.check(new(big.Int).Mul(big.NewInt(4), num).Cmp(
			new(big.Int).Mul(big.NewInt(3), den)) < 0)
		t.check(new(big.Int).Mul(big.NewInt(5), num).Cmp(
			new(big.Int).Lsh(den, 1)) >= 0)
		t.check(new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), 16),
			new(big.Int).Exp(big.NewInt(3), big.NewInt(10), nil)).Cmp(
			big.NewInt(6487)) == 0)
	} else {
		t.check(false)
		t.check(false)
		t.check(false)
	}
	return t
}

// PhaseRigidSweep runs every exact check and returns the totals.
func PhaseRigidSweep() Totals {
	var total Totals
	total.add(sweepParity())
	total.add(sweepControls())
	total.add(sweepWords())
	total.add(sweepWitness())
	return total
}

// main prints the check count. A positive failure count stops the process.
func main() {
	total := PhaseRigidSweep()
	fmt.Printf("phase rigid checks: %d failures: %d\n",
		total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
