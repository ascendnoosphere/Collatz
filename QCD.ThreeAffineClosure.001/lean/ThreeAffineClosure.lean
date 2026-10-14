-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Numerator of the three-letter closure on the word `(a, b, c)`. -/
def ClosureNumerator (a b q : ℕ) : ℤ :=
  (q : ℤ) ^ 2 + (q : ℤ) * (2 : ℤ) ^ a + (2 : ℤ) ^ (a + b)

/-- Closure numerator of the word `(c, a, b)`, read at the third odd state. -/
def ThirdComponent (c a q : ℕ) : ℤ :=
  (q : ℤ) ^ 2 + (q : ℤ) * (2 : ℤ) ^ c + (2 : ℤ) ^ (c + a)

/-- Determinant `2^{a+b+c} - q^3` of one pass through three affine letters. -/
def Delta (a b c q : ℕ) : ℤ :=
  (2 : ℤ) ^ (a + b + c) - (q : ℤ) ^ 3

/-- Every power of two is at least one. -/
theorem OneLePowTwo (k : ℕ) : (1 : ℤ) ≤ (2 : ℤ) ^ k := by
  induction k with
  | zero =>
    {
      rw [Int.pow_zero]
      exact Int.le_refl 1
    }
  | succ k ih =>
    {
      rw [Int.pow_succ]
      have hOne : (1 : ℤ) ≤ 2 := Int.ofNat_le.mpr (Nat.le_succ 1)
      have hMul : (1 : ℤ) * 1 ≤ (2 : ℤ) ^ k * 2 :=
        Int.mul_le_mul ih hOne (Int.natCast_nonneg 1)
          (Int.pow_nonneg (Int.ofNat_le.mpr (Nat.zero_le 2)))
      rw [Int.mul_one] at hMul
      exact hMul
    }

/-- A positive power of two is at least two. -/
theorem TwoPowAtLeastTwo (n : ℕ) (hn : 1 ≤ n) : (2 : ℤ) ≤ (2 : ℤ) ^ n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  rw [hk, Int.pow_add, Int.pow_one]
  have hMul : (2 : ℤ) * 1 ≤ (2 : ℤ) * (2 : ℤ) ^ k :=
    Int.mul_le_mul_of_nonneg_left (OneLePowTwo k)
      (Int.ofNat_le.mpr (Nat.zero_le 2))
  rw [Int.mul_one] at hMul
  exact hMul

/-- The square of two is four. -/
theorem TwoSquare : (2 : ℤ) ^ 2 = 4 := by
  decide

/-- The positive lower bound splits as `1 + 2 + 4`. -/
theorem SevenAsSum : (1 : ℤ) + 2 + 4 = 7 := by
  have hNat : (1 + 2 + 4 : ℕ) = 7 := by decide
  have hCast : ((1 + 2 + 4 : ℕ) : ℤ) = 7 :=
    congrArg (fun n : ℕ => (n : ℤ)) hNat
  rw [Int.natCast_add (1 + 2) 4, Int.natCast_add 1 2] at hCast
  exact hCast

/-- Each positive three-letter numerator is at least seven. -/
theorem NumeratorAtLeastSeven
    (e f r : ℕ) (he : 0 < e) (hf : 0 < f) (hr : 0 < r) :
    (7 : ℤ) ≤ (r : ℤ) ^ 2 + (r : ℤ) * (2 : ℤ) ^ e + (2 : ℤ) ^ (e + f) := by
  have hr1 : (1 : ℤ) ≤ (r : ℤ) := Int.ofNat_le.mpr (Nat.succ_le_of_lt hr)
  have hrSq : (r : ℤ) ^ 2 = (r : ℤ) * r := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Int.pow_add, Int.pow_one]
  have hSquare : (1 : ℤ) ≤ (r : ℤ) ^ 2 := by
    have hMul : (1 : ℤ) * 1 ≤ (r : ℤ) * r :=
      Int.mul_le_mul hr1 hr1 (Int.natCast_nonneg 1)
        (Int.ofNat_le.mpr (Nat.zero_le r))
    rw [Int.mul_one, ← hrSq] at hMul
    exact hMul
  have hProd : (2 : ℤ) ≤ (r : ℤ) * (2 : ℤ) ^ e := by
    have hPow : (2 : ℤ) ≤ (2 : ℤ) ^ e :=
      TwoPowAtLeastTwo e (Nat.succ_le_of_lt he)
    have hMul : (1 : ℤ) * 2 ≤ (r : ℤ) * (2 : ℤ) ^ e :=
      Int.mul_le_mul hr1 hPow (Int.ofNat_le.mpr (Nat.zero_le 2))
        (Int.ofNat_le.mpr (Nat.zero_le r))
    rw [Int.one_mul] at hMul
    exact hMul
  have hFour : (4 : ℤ) ≤ (2 : ℤ) ^ (e + f) := by
    have hSum : 2 ≤ e + f :=
      Nat.add_le_add (Nat.succ_le_of_lt he) (Nat.succ_le_of_lt hf)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hSum
    rw [hk, Int.pow_add, TwoSquare]
    have hMul : (4 : ℤ) * 1 ≤ (4 : ℤ) * (2 : ℤ) ^ k :=
      Int.mul_le_mul_of_nonneg_left (OneLePowTwo k)
        (Int.ofNat_le.mpr (Nat.zero_le 4))
    rw [Int.mul_one] at hMul
    exact hMul
  have hParts :
      (1 : ℤ) + 2 + 4 ≤
        (r : ℤ) ^ 2 + (r : ℤ) * (2 : ℤ) ^ e + (2 : ℤ) ^ (e + f) :=
    Int.add_le_add (Int.add_le_add hSquare hProd) hFour
  rw [SevenAsSum] at hParts
  exact hParts

/-- Eliminating one three-cycle of affine letters produces the closure numerator. -/
theorem AffineClosureIdentity
    (e1 e2 e3 : ℕ) (q u v w : ℤ)
    (h1 : (2 : ℤ) ^ e1 * u = q * v + 1)
    (h2 : (2 : ℤ) ^ e2 * v = q * w + 1)
    (h3 : (2 : ℤ) ^ e3 * w = q * u + 1) :
    ((2 : ℤ) ^ (e1 + e2 + e3) - q ^ 3) * u =
      q ^ 2 + q * (2 : ℤ) ^ e3 + (2 : ℤ) ^ (e3 + e2) := by
  show ((2 : ℤ) ^ (e1 + e2 + e3) - q ^ 3) * u =
    q ^ 2 + q * (2 : ℤ) ^ e3 + (2 : ℤ) ^ (e3 + e2)
  -- The first letter contributes the factor `2^{e1}`.
  have hSplit : e1 + e2 + e3 = e1 + (e2 + e3) := Nat.add_assoc e1 e2 e3
  have hPow :
      (2 : ℤ) ^ (e1 + e2 + e3) * u =
        (2 : ℤ) ^ (e2 + e3) * ((2 : ℤ) ^ e1 * u) := by
    rw [hSplit, Int.pow_add (2 : ℤ) e1 (e2 + e3), Int.mul_assoc,
      Int.mul_left_comm ((2 : ℤ) ^ e1) ((2 : ℤ) ^ (e2 + e3)) u]
  have hStep :
      (2 : ℤ) ^ (e1 + e2 + e3) * u =
        (2 : ℤ) ^ (e2 + e3) * (q * v) + (2 : ℤ) ^ (e2 + e3) := by
    rw [hPow, h1, Int.mul_add, Int.mul_one]
  have hComm :
      (2 : ℤ) ^ (e2 + e3) * (q * v) =
        q * ((2 : ℤ) ^ (e2 + e3) * v) := by
    rw [Int.mul_left_comm]
  -- The second letter replaces `v`.
  have hSplitV :
      (2 : ℤ) ^ (e2 + e3) * v =
        (2 : ℤ) ^ e3 * ((2 : ℤ) ^ e2 * v) := by
    rw [Int.pow_add (2 : ℤ) e2 e3, Int.mul_assoc,
      Int.mul_left_comm ((2 : ℤ) ^ e2) ((2 : ℤ) ^ e3) v]
  have hAfterV :
      (2 : ℤ) ^ (e1 + e2 + e3) * u =
        q * ((2 : ℤ) ^ e3 * (q * w + 1)) + (2 : ℤ) ^ (e2 + e3) := by
    rw [hStep, hComm, hSplitV, h2]
  -- The third letter returns to `u` and cancels `q^3 u`.
  have hInner :
      (2 : ℤ) ^ e3 * (q * w + 1) =
        (2 : ℤ) ^ e3 * (q * w) + (2 : ℤ) ^ e3 := by
    rw [Int.mul_add, Int.mul_one]
  have hCommW :
      (2 : ℤ) ^ e3 * (q * w) = q * ((2 : ℤ) ^ e3 * w) := by
    rw [Int.mul_left_comm]
  have hAfterW :
      (2 : ℤ) ^ (e1 + e2 + e3) * u =
        q * (q * ((2 : ℤ) ^ e3 * w) + (2 : ℤ) ^ e3) +
          (2 : ℤ) ^ (e2 + e3) := by
    rw [hAfterV, hInner, hCommW]
  have hReturn :
      (2 : ℤ) ^ (e1 + e2 + e3) * u =
        q * (q * (q * u + 1) + (2 : ℤ) ^ e3) + (2 : ℤ) ^ (e2 + e3) := by
    rw [hAfterW, h3]
  have hq2 : q ^ 2 = q * q := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Int.pow_add q 1 1, Int.pow_one]
  have hq3 : q ^ 3 = q * q * q := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Int.pow_add q 2 1, hq2, Int.pow_one]
  have hCube : q * (q * (q * u)) = q ^ 3 * u := by
    rw [← Int.mul_assoc q q (q * u), ← Int.mul_assoc (q * q) q u, ← hq3]
  have hSquare : q * (q * 1) = q ^ 2 := by
    rw [Int.mul_one q, ← hq2]
  have hExpand :
      q * (q * (q * u + 1) + (2 : ℤ) ^ e3) =
        q * (q * (q * u)) + q * (q * 1) + q * (2 : ℤ) ^ e3 := by
    rw [Int.mul_add q (q * u) 1]
    rw [Int.mul_add q (q * (q * u) + q * 1) ((2 : ℤ) ^ e3)]
    rw [Int.mul_add q (q * (q * u)) (q * 1)]
  have hExpanded :
      (2 : ℤ) ^ (e1 + e2 + e3) * u =
        q ^ 3 * u + q ^ 2 + q * (2 : ℤ) ^ e3 + (2 : ℤ) ^ (e2 + e3) := by
    rw [hReturn, hExpand, hCube, hSquare]
  have hGroup :
      q ^ 3 * u + q ^ 2 + q * (2 : ℤ) ^ e3 + (2 : ℤ) ^ (e2 + e3) =
        q ^ 3 * u +
          (q ^ 2 + q * (2 : ℤ) ^ e3 + (2 : ℤ) ^ (e2 + e3)) := by
    rw [Int.add_assoc (q ^ 3 * u + q ^ 2) (q * (2 : ℤ) ^ e3)
        ((2 : ℤ) ^ (e2 + e3))]
    rw [Int.add_assoc (q ^ 3 * u) (q ^ 2)
        (q * (2 : ℤ) ^ e3 + (2 : ℤ) ^ (e2 + e3))]
    rw [← Int.add_assoc (q ^ 2) (q * (2 : ℤ) ^ e3)
        ((2 : ℤ) ^ (e2 + e3))]
  have hSub :
      ((2 : ℤ) ^ (e1 + e2 + e3) - q ^ 3) * u =
        (2 : ℤ) ^ (e1 + e2 + e3) * u - q ^ 3 * u := by
    exact Int.sub_mul _ _ u
  rw [hSub, hExpanded, hGroup]
  rw [Int.add_comm (q ^ 3 * u)
      (q ^ 2 + q * (2 : ℤ) ^ e3 + (2 : ℤ) ^ (e2 + e3))]
  rw [Int.add_sub_cancel
      (q ^ 2 + q * (2 : ℤ) ^ e3 + (2 : ℤ) ^ (e2 + e3)) (q ^ 3 * u)]
  rw [Nat.add_comm e2 e3]

/-- An integer solution forces divisibility, and the third state is the rotated quotient. -/
theorem ThreeAffineClosure
    (a b c q : ℕ) (x y z : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : 0 < q)
    (hx : (2 : ℤ) ^ a * y = (q : ℤ) * x + 1)
    (hy : (2 : ℤ) ^ b * z = (q : ℤ) * y + 1)
    (hz : (2 : ℤ) ^ c * x = (q : ℤ) * z + 1) :
    Delta a b c q * x = ClosureNumerator a b q ∧
      Delta a b c q ∣ ClosureNumerator a b q ∧
      Delta a b c q * z = ThirdComponent c a q ∧
      z = ThirdComponent c a q / Delta a b c q ∧
      Delta a b c q ≠ 0 ∧
      (7 : ℤ) ≤ ClosureNumerator a b q ∧
      (7 : ℤ) ≤ ThirdComponent c a q := by
  show Delta a b c q * x = ClosureNumerator a b q ∧
    Delta a b c q ∣ ClosureNumerator a b q ∧
    Delta a b c q * z = ThirdComponent c a q ∧
    z = ThirdComponent c a q / Delta a b c q ∧
    Delta a b c q ≠ 0 ∧
    (7 : ℤ) ≤ ClosureNumerator a b q ∧
    (7 : ℤ) ≤ ThirdComponent c a q
  -- Read the identity on `(c, b, a)` for the seed and on `(b, a, c)` for the third state.
  have hRawX :=
    AffineClosureIdentity c b a (q : ℤ) x z y hz hy hx
  have hPermX : c + b + a = a + b + c := by
    rw [Nat.add_comm c b]
    rw [Nat.add_assoc b c a]
    rw [Nat.add_comm c a]
    rw [← Nat.add_left_comm a b c]
    rw [← Nat.add_assoc a b c]
  have hBx : Delta a b c q * x = ClosureNumerator a b q := by
    unfold Delta ClosureNumerator
    rw [← hPermX]
    exact hRawX
  have hRawZ :=
    AffineClosureIdentity b a c (q : ℤ) z y x hy hx hz
  have hPermZ : b + a + c = a + b + c := by
    rw [Nat.add_comm b a]
  have hTz : Delta a b c q * z = ThirdComponent c a q := by
    unfold Delta ThirdComponent
    rw [← hPermZ]
    exact hRawZ
  have hB : (7 : ℤ) ≤ ClosureNumerator a b q := by
    unfold ClosureNumerator
    exact NumeratorAtLeastSeven a b q ha hb hq
  have hT : (7 : ℤ) ≤ ThirdComponent c a q := by
    unfold ThirdComponent
    exact NumeratorAtLeastSeven c a q hc ha hq
  have hNe : Delta a b c q ≠ 0 := by
    intro hZero
    have hZeroB : ClosureNumerator a b q = 0 := by
      rw [← hBx, hZero, Int.zero_mul]
    have hPos : (0 : ℤ) < ClosureNumerator a b q := by
      have hSeven : (0 : ℕ) < 7 := by decide
      exact Int.lt_of_lt_of_le (Int.ofNat_lt.mpr hSeven) hB
    rw [hZeroB] at hPos
    exact Int.lt_irrefl 0 hPos
  have hDvd : Delta a b c q ∣ ClosureNumerator a b q :=
    ⟨x, hBx.symm⟩
  have hQuot : z = ThirdComponent c a q / Delta a b c q := by
    have hCancel : (z * Delta a b c q) / Delta a b c q = z :=
      Int.mul_ediv_cancel z hNe
    rw [← hTz, Int.mul_comm (Delta a b c q) z]
    exact hCancel.symm
  exact ⟨hBx, ⟨hDvd, ⟨hTz, ⟨hQuot, ⟨hNe, ⟨hB, hT⟩⟩⟩⟩⟩⟩

end GeneralizedCollatz
