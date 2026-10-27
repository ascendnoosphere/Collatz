// SPDX-License-Identifier: CC-BY-4.0

// Command TwoAffineWindow checks the cleared positivity comparison on one
// finite odd grid. The grid is not the theorem.
package main

import (
	"errors"
	"fmt"
	"math/big"
	"os"
)

const (
	gridKMin uint64 = 3
	gridKMax uint64 = 21
	gridQMin uint64 = 1
	gridQMax uint64 = 181
)

// Workspace owns reusable integer buffers and must not be copied or shared.
type Workspace struct {
	Acc   big.Int
	Hi    big.Int
	Left  big.Int
	Lo    big.Int
	Mid   big.Int
	MidSq big.Int
	Nine  big.Int
	One   big.Int
	Pow   big.Int
	Right big.Int
	Root  big.Int
	Six   big.Int
	Three big.Int
	Tmp   big.Int
	Two   big.Int
}

// GridPredicate reports a boolean at one odd grid cell.
type GridPredicate func(q, K uint64, w *Workspace) (bool, error)

// Prepare stores the fixed coefficients once.
func (w *Workspace) Prepare() {
	if w.Two.Sign() != 0 {
		return
	}
	w.One.SetInt64(1)
	w.Two.SetInt64(2)
	w.Three.SetInt64(3)
	w.Six.SetInt64(6)
	w.Nine.SetInt64(9)
}

// ValidatePair accepts only an odd exponent at least 3 and an odd q.
func ValidatePair(q, K uint64) error {
	if K < 3 || K%2 == 0 {
		return errors.New("K must be an odd integer at least 3")
	}
	if q%2 == 0 {
		return errors.New("q must be odd")
	}
	return nil
}

// PowTwo writes 2^K into out.
func PowTwo(out *big.Int, K uint64) {
	out.SetUint64(1)
	out.Lsh(out, uint(K))
}

// ClearedSquare writes (3q+1)^2 into out.
func ClearedSquare(out *big.Int, q uint64, w *Workspace) {
	w.Prepare()
	w.Tmp.SetUint64(q)
	w.Tmp.Mul(&w.Three, &w.Tmp)
	w.Tmp.Add(&w.Tmp, &w.One)
	out.Mul(&w.Tmp, &w.Tmp)
}

// ExpandedSquare writes 9q^2+6q+1 into out.
func ExpandedSquare(out *big.Int, q uint64, w *Workspace) {
	w.Prepare()
	w.Tmp.SetUint64(q)
	w.Acc.Mul(&w.Tmp, &w.Tmp)
	w.Acc.Mul(&w.Nine, &w.Acc)
	w.Tmp.SetUint64(q)
	w.Tmp.Mul(&w.Six, &w.Tmp)
	w.Acc.Add(&w.Acc, &w.Tmp)
	w.Acc.Add(&w.Acc, &w.One)
	out.Set(&w.Acc)
}

// SquaresMatch reports whether the cleared square equals the expansion.
func SquaresMatch(q uint64, w *Workspace) (bool, error) {
	if q%2 == 0 {
		return false, errors.New("q must be odd")
	}
	if w == nil {
		return false, errors.New("workspace is required")
	}
	w.Prepare()
	ClearedSquare(&w.Left, q, w)
	ExpandedSquare(&w.Right, q, w)
	return w.Left.Cmp(&w.Right) == 0, nil
}

// NinePowTwo writes 9*2^K into out.
func NinePowTwo(out *big.Int, K uint64, w *Workspace) {
	w.Prepare()
	PowTwo(&w.Pow, K)
	out.Mul(&w.Nine, &w.Pow)
}

// Decide reports whether 9*2^K is at most (3q+1)^2.
func Decide(q, K uint64, w *Workspace) (bool, error) {
	if err := ValidatePair(q, K); err != nil {
		return false, err
	}
	if w == nil {
		return false, errors.New("workspace is required")
	}
	w.Prepare()
	NinePowTwo(&w.Left, K, w)
	ClearedSquare(&w.Right, q, w)
	return w.Left.Cmp(&w.Right) <= 0, nil
}

// IntegerSqrt writes the greatest integer whose square is at most pow2.
func IntegerSqrt(root, pow2 *big.Int, w *Workspace) {
	w.Prepare()
	w.Lo.SetInt64(0)
	w.Hi.Set(pow2)
	for w.Lo.Cmp(&w.Hi) < 0 {
		w.Mid.Add(&w.Lo, &w.Hi)
		w.Mid.Add(&w.Mid, &w.One)
		w.Mid.Rsh(&w.Mid, 1)
		w.MidSq.Mul(&w.Mid, &w.Mid)
		if w.MidSq.Cmp(pow2) <= 0 {
			w.Lo.Set(&w.Mid)
			continue
		}
		w.Hi.Sub(&w.Mid, &w.One)
	}
	root.Set(&w.Lo)
}

// FloorOf returns the integer floor of the square root of 2^K.
func FloorOf(K uint64, w *Workspace) (uint64, error) {
	if K < 3 || K%2 == 0 {
		return 0, errors.New("K must be an odd integer at least 3")
	}
	if w == nil {
		return 0, errors.New("workspace is required")
	}
	w.Prepare()
	PowTwo(&w.Pow, K)
	IntegerSqrt(&w.Root, &w.Pow, w)
	if !w.Root.IsUint64() {
		return 0, errors.New("floor square root exceeds uint64")
	}
	return w.Root.Uint64(), nil
}

// SquareBracket checks root^2 < 2^K < (root+1)^2 against the stored power.
func SquareBracket(root uint64, w *Workspace) error {
	if root == ^uint64(0) {
		return errors.New("successor of the floor does not fit")
	}
	w.Tmp.SetUint64(root)
	w.MidSq.Mul(&w.Tmp, &w.Tmp)
	if w.MidSq.Cmp(&w.Pow) >= 0 {
		return errors.New("floor square is not strictly below the power")
	}
	w.Tmp.SetUint64(root + 1)
	w.MidSq.Mul(&w.Tmp, &w.Tmp)
	if w.MidSq.Cmp(&w.Pow) <= 0 {
		return errors.New("successor square does not exceed the power")
	}
	return nil
}

// OddCandidate returns the odd floor or its odd predecessor.
func OddCandidate(root uint64) (uint64, bool, error) {
	if root == 0 {
		return 0, false, errors.New("floor is zero")
	}
	if root%2 == 0 {
		return root - 1, true, nil
	}
	return root, false, nil
}

// CandidateBranch checks the even-floor failure or the odd-floor identity.
func CandidateBranch(K, root uint64, w *Workspace) error {
	q, evenFloor, err := OddCandidate(root)
	if err != nil {
		return err
	}
	positive, err := Decide(q, K, w)
	if err != nil {
		return err
	}
	if evenFloor {
		if positive {
			return fmt.Errorf("even floor candidate q=%d at K=%d is positive", q, K)
		}
		return nil
	}
	if q != root {
		return errors.New("odd floor candidate differs from the floor")
	}
	return nil
}

// AuditGrid rejects a predicate that holds at every odd grid cell.
func AuditGrid(pred GridPredicate, w *Workspace) (uint64, error) {
	if pred == nil || w == nil {
		return 0, errors.New("predicate and workspace are required")
	}
	var n uint64
	var sawFalse bool
	for K := gridKMin; K <= gridKMax; K += 2 {
		for q := gridQMin; q <= gridQMax; q += 2 {
			ok, err := pred(q, K, w)
			if err != nil {
				return n, err
			}
			n++
			if !ok {
				sawFalse = true
			}
		}
	}
	if !sawFalse {
		return n, errors.New("predicate is true at every grid cell")
	}
	return n, nil
}

// CountChecks is the number of exact checks in the stated finite grid.
func CountChecks() uint64 {
	kCount := (gridKMax-gridKMin)/2 + 1
	qCount := (gridQMax-gridQMin)/2 + 1
	cells := kCount * qCount
	return 2*cells + 2*kCount
}

// AuditWindow performs the expanded, comparison, bracket, and candidate checks.
func AuditWindow(w *Workspace) (uint64, error) {
	if w == nil {
		return 0, errors.New("workspace is required")
	}
	var n uint64
	var sawFalse bool
	for K := gridKMin; K <= gridKMax; K += 2 {
		root, err := FloorOf(K, w)
		if err != nil {
			return n, err
		}
		if err := SquareBracket(root, w); err != nil {
			return n, err
		}
		n++
		if err := CandidateBranch(K, root, w); err != nil {
			return n, err
		}
		n++
		for q := gridQMin; q <= gridQMax; q += 2 {
			match, err := SquaresMatch(q, w)
			if err != nil {
				return n, err
			}
			if !match {
				return n, errors.New("expanded square disagrees with the cleared square")
			}
			n++
			positive, err := Decide(q, K, w)
			if err != nil {
				return n, err
			}
			n++
			if !positive {
				sawFalse = true
			}
		}
	}
	if !sawFalse {
		return n, errors.New("comparison is true at every grid cell")
	}
	if n != CountChecks() {
		return n, errors.New("check count disagrees with the stated grid")
	}
	return n, nil
}

// main prints the number of exact checks on the stated grid.
func main() {
	var w Workspace
	n, err := AuditWindow(&w)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	fmt.Println(n)
}
