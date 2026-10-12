-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Arithmetic phase rigidity for the base-two divided branches.

For odd positive integers `q` and `c`, the branches are `x ↦ x / 2` and
`x ↦ (q x + c) / 2`. An integer of the letter's parity is sent to an integer.
If a rational phase and the next phase both lie at distance strictly less than
`2 / (q + 2)` from integers of the prescribed parities, the integer branch
lands on the next integer. Two solutions of the same affine fixed-point
equation agree whenever the multiplier and the denominator differ.

Nothing here continues the branches off the integers, and a defect of zero is
not excluded.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The integer has the parity named by the letter. -/
def PhaseRigidHasParity (odd : Bool) (n : ℤ) : Prop :=
  match odd with
  | true => Odd n
  | false => Even n

/-- Letter scale: `q` on an odd letter and `1` on an even letter. -/
def PhaseRigidLetter (q : ℕ) (odd : Bool) : ℚ :=
  if odd then (q : ℚ) else 1

/-- Constant term: `c` on an odd letter and `0` on an even letter. -/
def PhaseRigidOffset (c : ℕ) (odd : Bool) : ℤ :=
  if odd then (c : ℤ) else 0

/-- One divided branch, odd or even. -/
def PhaseRigidShortcut (q c : ℕ) (odd : Bool) (x : ℚ) : ℚ :=
  if odd then ((q : ℚ) * x + (c : ℚ)) / 2 else x / 2

/-- Integer value of one divided branch. -/
def PhaseRigidIntBranch (q c : ℕ) (odd : Bool) (n : ℤ) : ℤ :=
  if odd then ((q : ℤ) * n + (c : ℤ)) / 2 else n / 2

/-- An odd positive integer is at least one. -/
theorem PhaseRigidOddAtLeastOne (q : ℕ) (hq : Odd q) : 1 ≤ q := by
  rcases hq with ⟨k, hk⟩
  rw [hk, Nat.add_comm]
  exact Nat.le_add_right 1 (2 * k)

/-- The numerator `q n + c` is even when `q`, `c`, and `n` are odd. -/
theorem PhaseRigidOddNumeratorEven (q c : ℕ) (n : ℤ)
    (hq : Odd q) (hc : Odd c) (hn : Odd n) :
    Even ((q : ℤ) * n + (c : ℤ)) := by
  have hqz : Odd (q : ℤ) := Odd.natCast hq
  have hcz : Odd (c : ℤ) := Odd.natCast hc
  exact Odd.add_odd (Odd.mul hqz hn) hcz

/-- Dividing an even integer by two recovers that integer. -/
theorem PhaseRigidEvenHalves (n : ℤ) (hn : Even n) :
    2 * (n / 2) = n := by
  rcases Even.two_dvd hn with ⟨k, hk⟩
  have hdiv : n / 2 = k := Int.ediv_eq_of_eq_mul_right (by decide) hk
  rw [hdiv, hk]

/-- Dividing the odd numerator by two recovers that numerator. -/
theorem PhaseRigidOddBranchExact (q c : ℕ) (n : ℤ)
    (hq : Odd q) (hc : Odd c) (hn : Odd n) :
    2 * (((q : ℤ) * n + (c : ℤ)) / 2) = (q : ℤ) * n + (c : ℤ) := by
  have heven := PhaseRigidOddNumeratorEven q c n hq hc hn
  rcases Even.two_dvd heven with ⟨k, hk⟩
  have hdiv : ((q : ℤ) * n + (c : ℤ)) / 2 = k :=
    Int.ediv_eq_of_eq_mul_right (by decide) hk
  rw [hdiv, hk]

/-- The letter scale lies between `0` and `q` once `q` is positive. -/
theorem PhaseRigidLetterBounds (q : ℕ) (odd : Bool) (hq : 1 ≤ q) :
    0 ≤ PhaseRigidLetter q odd ∧ PhaseRigidLetter q odd ≤ (q : ℚ) := by
  cases odd with
  | true =>
    {
      unfold PhaseRigidLetter
      simp
    }
  | false =>
    {
      unfold PhaseRigidLetter
      simp
      exact hq
    }

/-- The shortcut is the affine expression with the letter scale and offset. -/
theorem PhaseRigidShortcutSpec (q c : ℕ) (odd : Bool) (x : ℚ) :
    PhaseRigidShortcut q c odd x =
      (PhaseRigidLetter q odd * x +
        ((PhaseRigidOffset c odd : ℤ) : ℚ)) / 2 := by
  cases odd with
  | true =>
    {
      unfold PhaseRigidShortcut PhaseRigidLetter PhaseRigidOffset
      simp
    }
  | false =>
    {
      unfold PhaseRigidShortcut PhaseRigidLetter PhaseRigidOffset
      simp
    }

/-- On a parity integer, the rational branch equals integer division. -/
theorem PhaseRigidIntBranchCast (q c : ℕ) (odd : Bool) (n : ℤ)
    (hq : Odd q) (hc : Odd c) (hp : PhaseRigidHasParity odd n) :
    PhaseRigidShortcut q c odd (n : ℚ) =
      ((PhaseRigidIntBranch q c odd n : ℤ) : ℚ) := by
  cases odd with
  | true =>
    {
      unfold PhaseRigidHasParity at hp
      have heven := PhaseRigidOddNumeratorEven q c n hq hc hp
      rcases Even.two_dvd heven with ⟨k, hk⟩
      have hkdiv : PhaseRigidIntBranch q c true n = k := by
        unfold PhaseRigidIntBranch
        simp
        exact Int.ediv_eq_of_eq_mul_right (by decide) hk
      unfold PhaseRigidShortcut
      simp
      rw [hkdiv]
      have hsum : ((q : ℚ) * (n : ℚ) + (c : ℚ)) =
          (((q : ℤ) * n + (c : ℤ) : ℤ) : ℚ) := by
        norm_cast
      rw [hsum, hk]
      have h2 : (2 : ℚ) ≠ 0 := by norm_num
      refine mul_left_cancel₀ h2 ?_
      rw [mul_div_cancel₀ _ h2]
      rw [Int.cast_mul]
      norm_cast
    }
  | false =>
    {
      unfold PhaseRigidHasParity at hp
      rcases Even.two_dvd hp with ⟨k, hk⟩
      have hkdiv : PhaseRigidIntBranch q c false n = k := by
        unfold PhaseRigidIntBranch
        simp
        exact Int.ediv_eq_of_eq_mul_right (by decide) hk
      unfold PhaseRigidShortcut
      simp
      rw [hkdiv]
      have hsum : (n : ℚ) = ((2 * k : ℤ) : ℚ) := by
        rw [hk]
      rw [hsum]
      have h2 : (2 : ℚ) ≠ 0 := by norm_num
      refine mul_left_cancel₀ h2 ?_
      rw [mul_div_cancel₀ _ h2]
      rw [Int.cast_mul]
      norm_cast
    }

/-- The odd letter meets the threshold with equality. -/
theorem PhaseRigidThresholdSaturates (q : ℕ) :
    ((q : ℚ) / 2 + 1) * (2 / ((q : ℚ) + 2)) = 1 := by
  have hden : (q : ℚ) + 2 ≠ 0 := by
    have hq0 : (0 : ℚ) ≤ (q : ℚ) := Nat.cast_nonneg q
    linarith
  apply mul_right_cancel₀ hden
  calc
    (((q : ℚ) / 2 + 1) * (2 / ((q : ℚ) + 2))) * ((q : ℚ) + 2)
        = ((q : ℚ) / 2 + 1) * ((2 / ((q : ℚ) + 2)) * ((q : ℚ) + 2)) := by
          ring
    _ = ((q : ℚ) / 2 + 1) * 2 := by rw [div_mul_cancel₀ _ hden]
    _ = (q : ℚ) + 2 := by ring
    _ = 1 * ((q : ℚ) + 2) := by ring

/-- The even letter produces the smaller threshold value `3 / (q + 2)`. -/
theorem PhaseRigidEvenAtThreshold (q : ℕ) :
    ((1 : ℚ) / 2 + 1) * (2 / ((q : ℚ) + 2)) = 3 / ((q : ℚ) + 2) := by
  have hden : (q : ℚ) + 2 ≠ 0 := by
    have hq0 : (0 : ℚ) ≤ (q : ℚ) := Nat.cast_nonneg q
    linarith
  apply mul_right_cancel₀ hden
  calc
    (((1 : ℚ) / 2 + 1) * (2 / ((q : ℚ) + 2))) * ((q : ℚ) + 2)
        = ((1 : ℚ) / 2 + 1) * ((2 / ((q : ℚ) + 2)) * ((q : ℚ) + 2)) := by
          ring
    _ = ((1 : ℚ) / 2 + 1) * 2 := by rw [div_mul_cancel₀ _ hden]
    _ = 3 := by ring
    _ = (3 / ((q : ℚ) + 2)) * ((q : ℚ) + 2) := by
          exact (div_mul_cancel₀ (3 : ℚ) hden).symm

/-- For `q ≥ 1` the even-letter value does not exceed one. -/
theorem PhaseRigidEvenThresholdLeOne (q : ℕ) (hq : 1 ≤ q) :
    3 / ((q : ℚ) + 2) ≤ 1 := by
  have hdenpos : (0 : ℚ) < (q : ℚ) + 2 := by
    have hq0 : (0 : ℚ) ≤ (q : ℚ) := Nat.cast_nonneg q
    linarith
  have h3 : 1 + 2 ≤ q + 2 := Nat.add_le_add_right hq 2
  rw [div_le_one hdenpos]
  exact_mod_cast h3

/-- A scale at most `q` and a defect below `2 / (q + 2)` stay strictly below one. -/
theorem PhaseRigidScaleBelowOne (q : ℕ) (a E : ℚ)
    (ha0 : 0 ≤ a) (haq : a ≤ (q : ℚ))
    (hE : E < 2 / ((q : ℚ) + 2)) :
    (a / 2 + 1) * E < 1 := by
  have hdenpos : (0 : ℚ) < (q : ℚ) + 2 := by
    have hq0 : (0 : ℚ) ≤ (q : ℚ) := Nat.cast_nonneg q
    linarith
  have hden : (q : ℚ) + 2 ≠ 0 := ne_of_gt hdenpos
  have hcoef : 0 < a / 2 + 1 := by
    have hnn : 0 ≤ a / 2 := div_nonneg ha0 (by norm_num)
    linarith
  have hlt : (a / 2 + 1) * E < (a / 2 + 1) * (2 / ((q : ℚ) + 2)) :=
    mul_lt_mul_of_pos_left hE hcoef
  have hfrac : (a + 2) / ((q : ℚ) + 2) ≤ 1 := by
    rw [div_le_one hdenpos]
    linarith
  have hid : (a / 2 + 1) * (2 / ((q : ℚ) + 2)) =
      (a + 2) / ((q : ℚ) + 2) := by
    apply mul_right_cancel₀ hden
    calc
      ((a / 2 + 1) * (2 / ((q : ℚ) + 2))) * ((q : ℚ) + 2)
          = (a / 2 + 1) * ((2 / ((q : ℚ) + 2)) * ((q : ℚ) + 2)) := by
            ring
      _ = (a / 2 + 1) * 2 := by rw [div_mul_cancel₀ _ hden]
      _ = a + 2 := by ring
      _ = ((a + 2) / ((q : ℚ) + 2)) * ((q : ℚ) + 2) := by
            exact (div_mul_cancel₀ (a + 2) hden).symm
  have hle : (a / 2 + 1) * (2 / ((q : ℚ) + 2)) ≤ 1 := by
    rw [hid]
    exact hfrac
  exact lt_of_lt_of_le hlt hle

/-- The integer branch lies at distance less than one from the next integer. -/
theorem PhaseRigidDiscrepancyLtOne
    (a E xi xiNext : ℚ) (n nNext branch b : ℤ)
    (ha : 0 ≤ a)
    (hxi : |xi - (n : ℚ)| ≤ E)
    (hnext : |xiNext - (nNext : ℚ)| ≤ E)
    (hstep : xiNext = (a * xi + (b : ℚ)) / 2)
    (hbranch : ((branch : ℤ) : ℚ) = (a * (n : ℚ) + (b : ℚ)) / 2)
    (hstrict : (a / 2 + 1) * E < 1) :
    |((branch : ℤ) : ℚ) - (nNext : ℚ)| < 1 := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hdiff : ((branch : ℤ) : ℚ) - xiNext =
      (a / 2) * ((n : ℚ) - xi) := by
    rw [hbranch, hstep]
    refine mul_left_cancel₀ h2 ?_
    rw [mul_sub, mul_div_cancel₀ _ h2, mul_div_cancel₀ _ h2]
    have hr : 2 * ((a / 2) * ((n : ℚ) - xi)) =
        a * ((n : ℚ) - xi) := by
      rw [← mul_assoc, mul_div_cancel₀ _ h2]
    rw [hr]
    ring
  have hsplit : ((branch : ℤ) : ℚ) - (nNext : ℚ) =
      (((branch : ℤ) : ℚ) - xiNext) + (xiNext - (nNext : ℚ)) := by
    ring
  have htri : |((branch : ℤ) : ℚ) - (nNext : ℚ)| ≤
      |((branch : ℤ) : ℚ) - xiNext| + |xiNext - (nNext : ℚ)| := by
    rw [hsplit]
    exact abs_add_le _ _
  have hscale : 0 ≤ a / 2 := div_nonneg ha (by norm_num)
  have habs : |(a / 2) * ((n : ℚ) - xi)| =
      (a / 2) * |(n : ℚ) - xi| := by
    rw [abs_mul, abs_of_nonneg hscale]
  have hswap : |(n : ℚ) - xi| = |xi - (n : ℚ)| := by
    have hneg : (n : ℚ) - xi = -(xi - (n : ℚ)) := by ring
    rw [hneg, abs_neg]
  have hmul : (a / 2) * |xi - (n : ℚ)| ≤ (a / 2) * E :=
    mul_le_mul_of_nonneg_left hxi hscale
  have hadd : (a / 2) * |xi - (n : ℚ)| + |xiNext - (nNext : ℚ)| ≤
      (a / 2) * E + E :=
    add_le_add hmul hnext
  have hident : (a / 2) * E + E = (a / 2 + 1) * E := by ring
  have hle : |((branch : ℤ) : ℚ) - (nNext : ℚ)| ≤ (a / 2 + 1) * E := by
    calc
      |((branch : ℤ) : ℚ) - (nNext : ℚ)|
          ≤ |((branch : ℤ) : ℚ) - xiNext| + |xiNext - (nNext : ℚ)| := htri
      _ = |(a / 2) * ((n : ℚ) - xi)| + |xiNext - (nNext : ℚ)| := by
          rw [hdiff]
      _ = (a / 2) * |(n : ℚ) - xi| + |xiNext - (nNext : ℚ)| := by
          rw [habs]
      _ = (a / 2) * |xi - (n : ℚ)| + |xiNext - (nNext : ℚ)| := by
          rw [hswap]
      _ ≤ (a / 2) * E + E := hadd
      _ = (a / 2 + 1) * E := hident
  exact lt_of_le_of_lt hle hstrict

/-- An integer whose rational absolute value is less than one is zero. -/
theorem PhaseRigidIntAbsLtOne (k : ℤ) (h : |(k : ℚ)| < 1) : k = 0 := by
  have habs : ((|k| : ℤ) : ℚ) < 1 := by
    rw [Int.cast_abs]
    exact h
  have hlt : |k| < 1 := by exact_mod_cast habs
  exact Int.abs_lt_one_iff.mp hlt

/-- A defect below `2 / (q + 2)` forces the integer branch onto the next integer. -/
theorem PhaseRigidCongruence (q c : ℕ) (odd : Bool) (E xi xiNext : ℚ)
    (n nNext : ℤ)
    (hq : Odd q) (hc : Odd c)
    (hp : PhaseRigidHasParity odd n)
    (hE : E < 2 / ((q : ℚ) + 2))
    (hxi : |xi - (n : ℚ)| ≤ E)
    (hnext : |xiNext - (nNext : ℚ)| ≤ E)
    (hstep : xiNext = PhaseRigidShortcut q c odd xi) :
    PhaseRigidIntBranch q c odd n = nNext := by
  have hq1 : 1 ≤ q := PhaseRigidOddAtLeastOne q hq
  rcases PhaseRigidLetterBounds q odd hq1 with ⟨ha0, haq⟩
  have hstrict := PhaseRigidScaleBelowOne q (PhaseRigidLetter q odd) E
    ha0 haq hE
  have hcast := PhaseRigidIntBranchCast q c odd n hq hc hp
  have hspecn := PhaseRigidShortcutSpec q c odd (n : ℚ)
  have hspecx := PhaseRigidShortcutSpec q c odd xi
  have hbranch : ((PhaseRigidIntBranch q c odd n : ℤ) : ℚ) =
      (PhaseRigidLetter q odd * (n : ℚ) +
        ((PhaseRigidOffset c odd : ℤ) : ℚ)) / 2 := by
    rw [← hcast, hspecn]
  have hxiStep : xiNext =
      (PhaseRigidLetter q odd * xi +
        ((PhaseRigidOffset c odd : ℤ) : ℚ)) / 2 := by
    rw [hstep, hspecx]
  have hlt := PhaseRigidDiscrepancyLtOne
    (PhaseRigidLetter q odd) E xi xiNext n nNext
    (PhaseRigidIntBranch q c odd n) (PhaseRigidOffset c odd)
    ha0 hxi hnext hxiStep hbranch hstrict
  have hdiff : |((PhaseRigidIntBranch q c odd n - nNext : ℤ) : ℚ)| < 1 := by
    have hcastDiff :
        ((PhaseRigidIntBranch q c odd n - nNext : ℤ) : ℚ) =
          ((PhaseRigidIntBranch q c odd n : ℤ) : ℚ) - (nNext : ℚ) := by
      norm_cast
    rw [hcastDiff]
    exact hlt
  have hzero : PhaseRigidIntBranch q c odd n - nNext = 0 :=
    PhaseRigidIntAbsLtOne _ hdiff
  exact sub_eq_zero.mp hzero

/-- One exact integer step transports the rational error by the letter scale. -/
theorem PhaseRigidErrorTransport (a xi xiNext : ℚ) (n nNext b : ℤ)
    (hstep : xiNext = (a * xi + (b : ℚ)) / 2)
    (hnext : (nNext : ℚ) = (a * (n : ℚ) + (b : ℚ)) / 2) :
    xiNext - (nNext : ℚ) = (a / 2) * (xi - (n : ℚ)) := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  rw [hstep, hnext]
  refine mul_left_cancel₀ h2 ?_
  rw [mul_sub, mul_div_cancel₀ _ h2, mul_div_cancel₀ _ h2]
  have hr : 2 * ((a / 2) * (xi - (n : ℚ))) = a * (xi - (n : ℚ)) := by
    rw [← mul_assoc, mul_div_cancel₀ _ h2]
  rw [hr]
  ring

/-- Two solutions of one affine equation have difference annihilated by `D - P`. -/
theorem PhaseRigidFixedSubtract (P D : ℕ) (xi n A : ℚ)
    (hxi : (D : ℚ) * xi = (P : ℚ) * xi + A)
    (hn : (D : ℚ) * n = (P : ℚ) * n + A) :
    ((D : ℚ) - (P : ℚ)) * (xi - n) = 0 := by
  have hzero : (D : ℚ) * xi - (P : ℚ) * xi - A = 0 := by
    rw [hxi]
    ring
  have hzn : (D : ℚ) * n - (P : ℚ) * n - A = 0 := by
    rw [hn]
    ring
  have hA : (D : ℚ) * xi - (P : ℚ) * xi = A := sub_eq_zero.mp hzero
  have hAn : (D : ℚ) * n - (P : ℚ) * n = A := sub_eq_zero.mp hzn
  have heq : (D : ℚ) * xi - (P : ℚ) * xi =
      (D : ℚ) * n - (P : ℚ) * n := by
    rw [hA, hAn]
  have hfac : ((D : ℚ) - (P : ℚ)) * (xi - n) =
      ((D : ℚ) * xi - (P : ℚ) * xi) -
        ((D : ℚ) * n - (P : ℚ) * n) := by
    ring
  rw [hfac, heq]
  ring

/-- The fixed-point difference is multiplied by `P / D`. -/
theorem PhaseRigidFixedRatio (P D : ℕ) (xi n A : ℚ)
    (hD : (D : ℚ) ≠ 0)
    (hxi : (D : ℚ) * xi = (P : ℚ) * xi + A)
    (hn : (D : ℚ) * n = (P : ℚ) * n + A) :
    xi - n = ((P : ℚ) / (D : ℚ)) * (xi - n) := by
  have hsub := PhaseRigidFixedSubtract P D xi n A hxi hn
  have hlin : (D : ℚ) * (xi - n) = (P : ℚ) * (xi - n) := by
    have hfac : (D : ℚ) * (xi - n) - (P : ℚ) * (xi - n) =
        ((D : ℚ) - (P : ℚ)) * (xi - n) := by
      ring
    have hz : (D : ℚ) * (xi - n) - (P : ℚ) * (xi - n) = 0 := by
      rw [hfac, hsub]
    exact sub_eq_zero.mp hz
  apply mul_left_cancel₀ hD
  rw [← mul_assoc, mul_div_cancel₀ (P : ℚ) hD]
  exact hlin

/-- A common affine fixed point is unique when the multiplier differs from `D`. -/
theorem PhaseRigidFixedUnique (P D : ℕ) (xi n A : ℚ)
    (hxi : (D : ℚ) * xi = (P : ℚ) * xi + A)
    (hn : (D : ℚ) * n = (P : ℚ) * n + A)
    (hne : P ≠ D) :
    xi = n := by
  have hprod := PhaseRigidFixedSubtract P D xi n A hxi hn
  have hfac : (D : ℚ) - (P : ℚ) ≠ 0 := by
    intro hz
    have heq : (D : ℚ) = (P : ℚ) := sub_eq_zero.mp hz
    apply hne
    exact_mod_cast heq.symm
  cases mul_eq_zero.mp hprod with
  | inl hD =>
    {
      exact absurd hD hfac
    }
  | inr hsub =>
    {
      exact sub_eq_zero.mp hsub
    }

/-- At `q = 3` the threshold is `2 / 5`. -/
theorem PhaseRigidClassicalFifth :
    (2 : ℚ) / ((3 : ℚ) + 2) = (2 : ℚ) / 5 := by
  norm_num

/-- The word odd-even sends `1` to `2` and `2` to `1` at `q = 3`, `c = 1`. -/
theorem PhaseRigidClassicalLoop :
    PhaseRigidIntBranch 3 1 true 1 = 2 ∧
      PhaseRigidIntBranch 3 1 false 2 = 1 := by
  constructor
  · {
      unfold PhaseRigidIntBranch
      decide
    }
  · {
      unfold PhaseRigidIntBranch
      decide
    }

end GeneralizedCollatz
