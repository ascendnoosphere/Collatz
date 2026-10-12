-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# One-excursion cover

An odd seed is written `n = 2 ^ a * u - 1` with `u` odd. The single-even exit is
`y = (3 ^ a * u - 1) / 2`. The quarter parent `(3 ^ (a + 1) * u - 1) / 8` lies
strictly below `n` if and only if `7 < (2 ^ (a + 3) - 3 ^ (a + 1)) * u`, once
`u > 0` and `2 ^ a * u ≥ 1`. The half parent `(3 ^ a * u - 3) / 4` lies strictly
below `n` if and only if `1 < (2 ^ (a + 2) - 3 ^ a) * u`, once
`3 ≤ 3 ^ a * u` and `2 ^ a * u ≥ 1`. The first coefficient is positive exactly for
`a ≤ 2`, and the second exactly for `a ≤ 3`. Thus every positive `u` fails both
comparisons when `a ≥ 4`; both succeed for `a = 2` and `u ≥ 3`; and at `a = 3`
only the second succeeds.

For `a ≥ 2` and odd `u`, the same exit satisfies `9 * (n + 1) ≤ 8 * (y + 1)`.
Six such steps force the exit to be at least `2 * n + 1`, and then none of the
four elementary cleared parent comparisons is strict.

Not proved here: finiteness of residual excursions, a cover by joins of several
excursions, convergence of every orbit, any census, and the terminal-power
classification.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Odd step `(3n + 1) / 2`, even step `n / 2`. -/
def Shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- `j` iterations of `Shortcut`. -/
def IterShortcut : ℕ → ℕ → ℕ
  | 0, n => n
  | j + 1, n => Shortcut (IterShortcut j n)

/-- The `j + 1` step is one application of `Shortcut`. -/
theorem IterShortcutSucc (j n : ℕ) :
    IterShortcut (j + 1) n = Shortcut (IterShortcut j n) := by
  rfl

/-- Even input takes the halving branch. -/
theorem ShortcutEven (n : ℕ) (he : n % 2 = 0) : Shortcut n = n / 2 := by
  unfold Shortcut
  rw [if_pos he]

/-- Odd input takes the branch `(3n + 1) / 2`. -/
theorem ShortcutOdd (n : ℕ) (ho : n % 2 = 1) : Shortcut n = (3 * n + 1) / 2 := by
  unfold Shortcut
  have hnot : ¬ n % 2 = 0 := by
    intro h0
    omega
  rw [if_neg hnot]

/-- Signed coefficient of the quarter-parent comparison. -/
def OneCoeff (a : ℕ) : ℤ := (2 : ℤ) ^ (a + 3) - (3 : ℤ) ^ (a + 1)

/-- Signed coefficient of the half-parent comparison. -/
def TwoCoeff (a : ℕ) : ℤ := (2 : ℤ) ^ (a + 2) - (3 : ℤ) ^ a

/-- The quarter coefficient is the next half coefficient. -/
theorem OneCoeffEq (a : ℕ) : OneCoeff a = TwoCoeff (a + 1) := by
  unfold OneCoeff TwoCoeff
  have hExp : (a + 1) + 2 = a + 3 := by omega
  rw [hExp]

/-- Recurrence `C(a + 1) = 2 C(a) - 3 ^ a` for the half coefficient. -/
theorem TwoCoeffSucc (a : ℕ) :
    TwoCoeff (a + 1) = 2 * TwoCoeff a - (3 : ℤ) ^ a := by
  unfold TwoCoeff
  have hExp : a + 1 + 2 = a + 3 := by omega
  rw [hExp]
  have h3 : (3 : ℤ) ^ (a + 1) = (3 : ℤ) ^ a * 3 := by rw [Int.pow_succ]
  have h2 : (2 : ℤ) ^ (a + 3) = (2 : ℤ) ^ (a + 2) * 2 := by
    rw [show a + 3 = (a + 2) + 1 by omega, Int.pow_succ]
  rw [h3, h2]
  ring

/-- Base value `2 ^ 2 - 3 ^ 0 = 3`. -/
theorem TwoCoeffZero : TwoCoeff 0 = 3 := by
  unfold TwoCoeff
  norm_num

/-- Base value `2 ^ 3 - 3 = 5`. -/
theorem TwoCoeffOne : TwoCoeff 1 = 5 := by
  unfold TwoCoeff
  norm_num

/-- Base value `2 ^ 4 - 3 ^ 2 = 7`. -/
theorem TwoCoeffTwo : TwoCoeff 2 = 7 := by
  unfold TwoCoeff
  norm_num

/-- Base value `2 ^ 5 - 3 ^ 3 = 5`. -/
theorem TwoCoeffThree : TwoCoeff 3 = 5 := by
  unfold TwoCoeff
  norm_num

/-- First negative value `2 ^ 6 - 3 ^ 4 = -17`. -/
theorem TwoCoeffFour : TwoCoeff 4 = -17 := by
  unfold TwoCoeff
  norm_num

/-- The half coefficient stays positive through order three. -/
theorem TwoCoeffPosOfLe (a : ℕ) (ha : a ≤ 3) : 0 < TwoCoeff a := by
  match a with
  | 0 =>
    { rw [TwoCoeffZero]
      decide }
  | 1 =>
    { rw [TwoCoeffOne]
      decide }
  | 2 =>
    { rw [TwoCoeffTwo]
      decide }
  | 3 =>
    { rw [TwoCoeffThree]
      decide }
  | n + 4 =>
    { omega }

/-- Once the half coefficient is negative, the recurrence keeps it negative. -/
theorem TwoCoeffNegOfGe (a : ℕ) (ha : 4 ≤ a) : TwoCoeff a < 0 := by
  induction a with
  | zero =>
    { omega }
  | succ a ih =>
    { by_cases hlt : a < 4
      · have h4 : a + 1 = 4 := by omega
        rw [h4, TwoCoeffFour]
        decide
      · have hge : 4 ≤ a := by omega
        have hltC : TwoCoeff a < 0 := ih hge
        rw [TwoCoeffSucc]
        have hpow : 0 < (3 : ℤ) ^ a := Int.pow_pos (by decide)
        linarith }

/-- Positivity of the half coefficient is exactly the range `a ≤ 3`. -/
theorem TwoCoeffPosIff (a : ℕ) : 0 < TwoCoeff a ↔ a ≤ 3 := by
  constructor
  · intro hpos
    by_contra hgt
    have hge : 4 ≤ a := by omega
    have hneg : TwoCoeff a < 0 := TwoCoeffNegOfGe a hge
    omega
  · intro hle
    exact TwoCoeffPosOfLe a hle

/-- Negativity of the half coefficient is exactly the range `a ≥ 4`. -/
theorem TwoCoeffNegIff (a : ℕ) : TwoCoeff a < 0 ↔ 4 ≤ a := by
  constructor
  · intro hneg
    by_contra hlt
    have hle : a ≤ 3 := by omega
    have hpos : 0 < TwoCoeff a := TwoCoeffPosOfLe a hle
    omega
  · intro hge
    exact TwoCoeffNegOfGe a hge

/-- Positivity of the quarter coefficient is exactly the range `a ≤ 2`. -/
theorem OneCoeffPosIff (a : ℕ) : 0 < OneCoeff a ↔ a ≤ 2 := by
  rw [OneCoeffEq, TwoCoeffPosIff]
  omega

/-- Negativity of the quarter coefficient is exactly the range `a ≥ 3`. -/
theorem OneCoeffNegIff (a : ℕ) : OneCoeff a < 0 ↔ 3 ≤ a := by
  rw [OneCoeffEq, TwoCoeffNegIff]
  omega

/-- Cast of a natural power. -/
theorem IntPowNat (b a : ℕ) : ((b ^ a : ℕ) : ℤ) = (b : ℤ) ^ a := by
  induction a with
  | zero =>
    { simp }
  | succ a ih =>
    { rw [Nat.pow_succ, Int.natCast_mul, ih, Int.pow_succ] }

/-- The quarter comparison is the signed coefficient inequality. -/
theorem OneBranchComparison (a u : ℕ) (hu : 0 < u) (hx : 1 ≤ 2 ^ a * u) :
    3 ^ (a + 1) * u - 1 < 8 * (2 ^ a * u - 1) ↔
      (7 : ℤ) < OneCoeff a * (u : ℤ) := by
  have h3 : 1 ≤ 3 ^ (a + 1) * u := by
    have hpow : 1 ≤ 3 ^ (a + 1) := Nat.one_le_pow (a + 1) 3 (by decide)
    exact Nat.le_trans hpow (Nat.le_mul_of_pos_right (3 ^ (a + 1)) hu)
  have hL : ((3 ^ (a + 1) * u - 1 : ℕ) : ℤ) =
      (3 : ℤ) ^ (a + 1) * (u : ℤ) - 1 := by
    rw [Int.ofNat_sub h3, Int.natCast_mul, IntPowNat]
    norm_cast
  have hR : ((8 * (2 ^ a * u - 1) : ℕ) : ℤ) =
      (8 : ℤ) * ((2 : ℤ) ^ a * (u : ℤ) - 1) := by
    rw [Int.natCast_mul, Int.ofNat_sub hx, Int.natCast_mul, IntPowNat]
    norm_cast
  have hpow : (8 : ℤ) * (2 : ℤ) ^ a = (2 : ℤ) ^ (a + 3) := by
    have h8 : (8 : ℤ) = (2 : ℤ) ^ 3 := by norm_num
    rw [h8, ← Int.pow_add]
    rw [show 3 + a = a + 3 by omega]
  have hExpand : (8 : ℤ) * ((2 : ℤ) ^ a * (u : ℤ) - 1) =
      (2 : ℤ) ^ (a + 3) * (u : ℤ) - 8 := by
    calc
      (8 : ℤ) * ((2 : ℤ) ^ a * (u : ℤ) - 1) =
          (8 : ℤ) * ((2 : ℤ) ^ a * (u : ℤ)) - 8 := by
        rw [Int.mul_sub, Int.mul_one]
      _ = ((8 : ℤ) * (2 : ℤ) ^ a) * (u : ℤ) - 8 := by rw [Int.mul_assoc]
      _ = (2 : ℤ) ^ (a + 3) * (u : ℤ) - 8 := by rw [hpow]
  constructor
  · intro hlt
    have hZ : ((3 ^ (a + 1) * u - 1 : ℕ) : ℤ) <
        ((8 * (2 ^ a * u - 1) : ℕ) : ℤ) := Int.ofNat_lt.mpr hlt
    rw [hL, hR, hExpand] at hZ
    unfold OneCoeff
    linarith
  · intro hlt
    unfold OneCoeff at hlt
    have hZ : (3 : ℤ) ^ (a + 1) * (u : ℤ) - 1 <
        (2 : ℤ) ^ (a + 3) * (u : ℤ) - 8 := by linarith
    rw [← hExpand] at hZ
    rw [← hL, ← hR] at hZ
    exact Int.ofNat_lt.mp hZ

/-- The half comparison is the signed coefficient inequality. -/
theorem TwoBranchComparison (a u : ℕ) (hx : 1 ≤ 2 ^ a * u)
    (h3 : 3 ≤ 3 ^ a * u) :
    3 ^ a * u - 3 < 4 * (2 ^ a * u - 1) ↔
      (1 : ℤ) < TwoCoeff a * (u : ℤ) := by
  have hL : ((3 ^ a * u - 3 : ℕ) : ℤ) =
      (3 : ℤ) ^ a * (u : ℤ) - 3 := by
    rw [Int.ofNat_sub h3, Int.natCast_mul, IntPowNat]
    norm_cast
  have hR : ((4 * (2 ^ a * u - 1) : ℕ) : ℤ) =
      (4 : ℤ) * ((2 : ℤ) ^ a * (u : ℤ) - 1) := by
    rw [Int.natCast_mul, Int.ofNat_sub hx, Int.natCast_mul, IntPowNat]
    norm_cast
  have hpow : (4 : ℤ) * (2 : ℤ) ^ a = (2 : ℤ) ^ (a + 2) := by
    have h4 : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
    rw [h4, ← Int.pow_add]
    rw [show 2 + a = a + 2 by omega]
  have hExpand : (4 : ℤ) * ((2 : ℤ) ^ a * (u : ℤ) - 1) =
      (2 : ℤ) ^ (a + 2) * (u : ℤ) - 4 := by
    calc
      (4 : ℤ) * ((2 : ℤ) ^ a * (u : ℤ) - 1) =
          (4 : ℤ) * ((2 : ℤ) ^ a * (u : ℤ)) - 4 := by
        rw [Int.mul_sub, Int.mul_one]
      _ = ((4 : ℤ) * (2 : ℤ) ^ a) * (u : ℤ) - 4 := by rw [Int.mul_assoc]
      _ = (2 : ℤ) ^ (a + 2) * (u : ℤ) - 4 := by rw [hpow]
  constructor
  · intro hlt
    have hZ : ((3 ^ a * u - 3 : ℕ) : ℤ) <
        ((4 * (2 ^ a * u - 1) : ℕ) : ℤ) := Int.ofNat_lt.mpr hlt
    rw [hL, hR, hExpand] at hZ
    unfold TwoCoeff
    linarith
  · intro hlt
    unfold TwoCoeff at hlt
    have hZ : (3 : ℤ) ^ a * (u : ℤ) - 3 <
        (2 : ℤ) ^ (a + 2) * (u : ℤ) - 4 := by linarith
    rw [← hExpand] at hZ
    rw [← hL, ← hR] at hZ
    exact Int.ofNat_lt.mp hZ

/-- A positive quarter coefficient and exact division give a parent below `n`. -/
theorem OneParentBelow (a u : ℕ) (hu : 0 < u) (hx : 1 ≤ 2 ^ a * u)
    (hd : 8 ∣ 3 ^ (a + 1) * u - 1)
    (hcmp : (7 : ℤ) < OneCoeff a * (u : ℤ)) :
    8 * ((3 ^ (a + 1) * u - 1) / 8) = 3 ^ (a + 1) * u - 1 ∧
      (3 ^ (a + 1) * u - 1) / 8 < 2 ^ a * u - 1 := by
  refine ⟨Nat.mul_div_cancel' hd, ?_⟩
  have hlt : 3 ^ (a + 1) * u - 1 < 8 * (2 ^ a * u - 1) :=
    (OneBranchComparison a u hu hx).mpr hcmp
  have hcomm : 8 * (2 ^ a * u - 1) = (2 ^ a * u - 1) * 8 := by rw [Nat.mul_comm]
  rw [hcomm] at hlt
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 8)).mpr hlt

/-- A positive half coefficient and exact division give a parent below `n`. -/
theorem TwoParentBelow (a u : ℕ) (hx : 1 ≤ 2 ^ a * u)
    (h3 : 3 ≤ 3 ^ a * u) (hd : 4 ∣ 3 ^ a * u - 3)
    (hcmp : (1 : ℤ) < TwoCoeff a * (u : ℤ)) :
    4 * ((3 ^ a * u - 3) / 4) = 3 ^ a * u - 3 ∧
      (3 ^ a * u - 3) / 4 < 2 ^ a * u - 1 := by
  refine ⟨Nat.mul_div_cancel' hd, ?_⟩
  have hlt : 3 ^ a * u - 3 < 4 * (2 ^ a * u - 1) :=
    (TwoBranchComparison a u hx h3).mpr hcmp
  have hcomm : 4 * (2 ^ a * u - 1) = (2 ^ a * u - 1) * 4 := by rw [Nat.mul_comm]
  rw [hcomm] at hlt
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr hlt

/-- At order two and `u ≥ 3`, both signed comparisons are strict. -/
theorem ATwoComparisons (u : ℕ) (hu : 3 ≤ u) :
    (7 : ℤ) < OneCoeff 2 * (u : ℤ) ∧ (1 : ℤ) < TwoCoeff 2 * (u : ℤ) := by
  have h1 : OneCoeff 2 = 5 := by
    rw [OneCoeffEq, TwoCoeffThree]
  have h2 : TwoCoeff 2 = 7 := TwoCoeffTwo
  have huZ : (3 : ℤ) ≤ (u : ℤ) := Int.ofNat_le.mpr hu
  have h5 : (5 : ℤ) * 3 ≤ 5 * (u : ℤ) :=
    Int.mul_le_mul_of_nonneg_left huZ (by decide)
  have h7 : (7 : ℤ) * 3 ≤ 7 * (u : ℤ) :=
    Int.mul_le_mul_of_nonneg_left huZ (by decide)
  constructor
  · rw [h1]
    have hbase : (7 : ℤ) < 5 * 3 := by decide
    linarith
  · rw [h2]
    have hbase : (1 : ℤ) < 7 * 3 := by decide
    linarith

/-- At order three the quarter comparison fails for every positive `u`. -/
theorem AThreeFirstFails (u : ℕ) (hu : 0 < u) :
    ¬ (7 : ℤ) < OneCoeff 3 * (u : ℤ) := by
  have hneg : OneCoeff 3 < 0 := (OneCoeffNegIff 3).mpr (by decide)
  have huZ : (0 : ℤ) < (u : ℤ) := Int.ofNat_lt.mpr hu
  have hmul : OneCoeff 3 * (u : ℤ) < 0 := Int.mul_neg_of_neg_of_pos hneg huZ
  linarith

/-- At order three the half comparison holds for every positive `u`. -/
theorem AThreeSecondHolds (u : ℕ) (hu : 0 < u) :
    (1 : ℤ) < TwoCoeff 3 * (u : ℤ) := by
  have hC : TwoCoeff 3 = 5 := TwoCoeffThree
  have huZ : (1 : ℤ) ≤ (u : ℤ) := Int.ofNat_le.mpr hu
  have hmul : (5 : ℤ) * 1 ≤ 5 * (u : ℤ) :=
    Int.mul_le_mul_of_nonneg_left huZ (by decide)
  rw [hC]
  linarith

/-- For `a ≥ 4` and `u > 0`, neither one-excursion comparison holds. -/
theorem HighValuationExcluded (a u : ℕ) (ha : 4 ≤ a) (hu : 0 < u) :
    ¬ (7 : ℤ) < OneCoeff a * (u : ℤ) ∧
      ¬ (1 : ℤ) < TwoCoeff a * (u : ℤ) := by
  have h1 : OneCoeff a < 0 := (OneCoeffNegIff a).mpr (by omega)
  have h2 : TwoCoeff a < 0 := (TwoCoeffNegIff a).mpr ha
  have huZ : (0 : ℤ) < (u : ℤ) := Int.ofNat_lt.mpr hu
  constructor
  · have hmul : OneCoeff a * (u : ℤ) < 0 := Int.mul_neg_of_neg_of_pos h1 huZ
    linarith
  · have hmul : TwoCoeff a * (u : ℤ) < 0 := Int.mul_neg_of_neg_of_pos h2 huZ
    linarith

/-- `4 * 3 ^ a - 9 * 2 ^ a` is nonnegative for every `a ≥ 2`. -/
theorem FourThreePowGe (a : ℕ) (ha : 2 ≤ a) : 9 * 2 ^ a ≤ 4 * 3 ^ a := by
  induction a with
  | zero =>
    { omega }
  | succ a ih =>
    { by_cases hge : 2 ≤ a
      · have hih := ih hge
        have hstep : 9 * 2 ^ (a + 1) = 2 * (9 * 2 ^ a) := by
          rw [Nat.pow_succ]
          calc
            9 * (2 ^ a * 2) = 9 * 2 ^ a * 2 := by rw [← Nat.mul_assoc]
            _ = 2 * (9 * 2 ^ a) := by rw [Nat.mul_comm]
        have h8 : 2 * (4 * 3 ^ a) = 8 * 3 ^ a := by
          calc
            2 * (4 * 3 ^ a) = (2 * 4) * 3 ^ a := by rw [Nat.mul_assoc]
            _ = 8 * 3 ^ a := by norm_num
        have h12 : 12 * 3 ^ a = 4 * 3 ^ (a + 1) := by
          have hsplit : 12 = 4 * 3 := by norm_num
          rw [hsplit, Nat.mul_assoc, Nat.mul_comm 3 (3 ^ a), ← Nat.pow_succ]
        calc
          9 * 2 ^ (a + 1) = 2 * (9 * 2 ^ a) := hstep
          _ ≤ 2 * (4 * 3 ^ a) := Nat.mul_le_mul_left 2 hih
          _ = 8 * 3 ^ a := h8
          _ ≤ 12 * 3 ^ a := Nat.mul_le_mul_right (3 ^ a) (by decide)
          _ = 4 * 3 ^ (a + 1) := h12
      · have h2 : a + 1 = 2 := by omega
        rw [h2]
        norm_num }

/-- Restoring the two subtracted blocks identifies the growth slack. -/
theorem GrowthRearrangement (A B u : ℕ) (hgap : 9 * B ≤ 4 * A)
    (hBu : 1 ≤ B * u) (hAu : 1 ≤ A * u) :
    9 * (B * u - 1) + u * (4 * A - 9 * B) + 5 = 4 * (A * u - 1) := by
  have hnine : 9 * (B * u - 1) + 9 = 9 * (B * u) := by
    have hsub : 9 * (B * u - 1) = 9 * (B * u) - 9 := Nat.mul_sub_one 9 (B * u)
    have hle : 9 ≤ 9 * (B * u) := Nat.le_mul_of_pos_right 9 hBu
    omega
  have hcancel : u * (4 * A - 9 * B) + u * (9 * B) = u * (4 * A) := by
    have hsub : u * (4 * A - 9 * B) = u * (4 * A) - u * (9 * B) :=
      Nat.mul_sub u (4 * A) (9 * B)
    have hle : u * (9 * B) ≤ u * (4 * A) := Nat.mul_le_mul_left u hgap
    omega
  have hfour : 4 * (A * u - 1) + 4 = 4 * (A * u) := by
    have hsub : 4 * (A * u - 1) = 4 * (A * u) - 4 := Nat.mul_sub_one 4 (A * u)
    have hle : 4 ≤ 4 * (A * u) := Nat.le_mul_of_pos_right 4 hAu
    omega
  have h9B : 9 * (B * u) = 9 * B * u := by rw [← Nat.mul_assoc]
  have h4A : u * (4 * A) = 4 * A * u := by
    rw [Nat.mul_comm u (4 * A), Nat.mul_assoc]
  have hAu4 : 4 * (A * u) = 4 * A * u := by rw [Nat.mul_assoc]
  have h9u : u * (9 * B) = 9 * B * u := by
    rw [Nat.mul_comm u (9 * B), Nat.mul_assoc]
  have h95 : 9 = 4 + 5 := by norm_num
  have hL : 9 * (B * u - 1) + u * (4 * A - 9 * B) + 5 + (9 + u * (9 * B)) =
      4 * A * u + 9 * B * u + 5 := by
    calc
      9 * (B * u - 1) + u * (4 * A - 9 * B) + 5 + (9 + u * (9 * B)) =
          (9 * (B * u - 1) + 9) + (u * (4 * A - 9 * B) + u * (9 * B)) + 5 := by
        ac_rfl
      _ = 9 * (B * u) + u * (4 * A) + 5 := by rw [hnine, hcancel]
      _ = 9 * B * u + 4 * A * u + 5 := by rw [h9B, h4A]
      _ = 4 * A * u + 9 * B * u + 5 := by ac_rfl
  have hR : 4 * (A * u - 1) + (9 + u * (9 * B)) =
      4 * A * u + 9 * B * u + 5 := by
    calc
      4 * (A * u - 1) + (9 + u * (9 * B)) =
          4 * (A * u - 1) + (4 + 5 + u * (9 * B)) := by rw [h95]
      _ = 4 * (A * u - 1) + 4 + (5 + u * (9 * B)) := by
        ac_rfl
      _ = 4 * (A * u) + (5 + u * (9 * B)) := by rw [hfour]
      _ = 4 * (A * u) + 5 + u * (9 * B) := by rw [← Nat.add_assoc]
      _ = 4 * A * u + 5 + 9 * B * u := by rw [hAu4, h9u]
      _ = 4 * A * u + 9 * B * u + 5 := by
        rw [Nat.add_right_comm (4 * A * u) 5 (9 * B * u)]
  have hC : 9 * (B * u - 1) + u * (4 * A - 9 * B) + 5 + (9 + u * (9 * B)) =
      4 * (A * u - 1) + (9 + u * (9 * B)) := by
    rw [hL, hR]
  exact Nat.add_right_cancel hC

/-- Oddness of `u` makes `3 ^ a * u - 1` exactly divisible by two. -/
theorem SingleEvenFromOdd (a u : ℕ) (hu : u % 2 = 1) :
    2 ∣ 3 ^ a * u - 1 := by
  have h3 : 3 ^ a % 2 = 1 := by
    induction a with
    | zero =>
      { simp }
    | succ a ih =>
      { rw [Nat.pow_succ, Nat.mul_mod, ih] }
  have hprod : 3 ^ a * u % 2 = 1 := by
    rw [Nat.mul_mod, h3, hu]
  have hge : 1 ≤ 3 ^ a * u := by
    have hpow : 1 ≤ 3 ^ a := Nat.one_le_pow a 3 (by decide)
    have hu0 : 0 < u := by omega
    exact Nat.le_trans hpow (Nat.le_mul_of_pos_right (3 ^ a) hu0)
  have hsub : (3 ^ a * u - 1) % 2 = 0 := by
    have hsum : (3 ^ a * u - 1 + 1) % 2 = 1 := by
      rw [Nat.sub_add_cancel hge, hprod]
    rcases Nat.mod_two_eq_zero_or_one (3 ^ a * u - 1) with h0 | h1
    · exact h0
    · have : (3 ^ a * u - 1 + 1) % 2 = 0 := by
        rw [Nat.add_mod, h1]
      omega
  exact Nat.dvd_of_mod_eq_zero hsub

/-- Exact slack `8 y = 9 x + u (4 * 3 ^ a - 9 * 2 ^ a) + 5`. -/
theorem NineEighthsSlack (a u : ℕ) (ha : 2 ≤ a) (hu : u % 2 = 1) :
    9 * (2 ^ a * u - 1) + u * (4 * 3 ^ a - 9 * 2 ^ a) + 5 =
      8 * ((3 ^ a * u - 1) / 2) := by
  have hu0 : 0 < u := by omega
  have hBu : 1 ≤ 2 ^ a * u := by
    have h2 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    exact Nat.le_trans h2 (Nat.le_mul_of_pos_right (2 ^ a) hu0)
  have hAu : 1 ≤ 3 ^ a * u := by
    have h3 : 1 ≤ 3 ^ a := Nat.one_le_pow a 3 (by decide)
    exact Nat.le_trans h3 (Nat.le_mul_of_pos_right (3 ^ a) hu0)
  have hgap := FourThreePowGe a ha
  have harr := GrowthRearrangement (3 ^ a) (2 ^ a) u hgap hBu hAu
  have hdvd := SingleEvenFromOdd a u hu
  have hdiv : 2 * ((3 ^ a * u - 1) / 2) = 3 ^ a * u - 1 :=
    Nat.mul_div_cancel' hdvd
  have h8 : 4 * (3 ^ a * u - 1) = 8 * ((3 ^ a * u - 1) / 2) := by
    conv_lhs => rw [← hdiv]
    omega
  rw [h8] at harr
  exact harr

/-- The slack is at least five, so `8 y ≥ 9 x + 5`. -/
theorem StrictNineEighths (a u : ℕ) (ha : 2 ≤ a) (hu : u % 2 = 1) :
    9 * (2 ^ a * u - 1) + 5 ≤ 8 * ((3 ^ a * u - 1) / 2) := by
  have hslack := NineEighthsSlack a u ha hu
  have hnn : 0 ≤ u * (4 * 3 ^ a - 9 * 2 ^ a) := Nat.zero_le _
  omega

/-- One single-even step obeys `9 (x + 1) ≤ 8 (y + 1)`. -/
theorem NineEighthsStep (a u : ℕ) (ha : 2 ≤ a) (hu : u % 2 = 1) :
    9 * (2 ^ a * u) ≤ 8 * ((3 ^ a * u - 1) / 2 + 1) := by
  have hslack := NineEighthsSlack a u ha hu
  have hu0 : 0 < u := by omega
  have hx : 1 ≤ 2 ^ a * u := by
    have h2 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    exact Nat.le_trans h2 (Nat.le_mul_of_pos_right (2 ^ a) hu0)
  have hx1 : (2 ^ a * u - 1) + 1 = 2 ^ a * u := Nat.sub_add_cancel hx
  set x : ℕ := 2 ^ a * u
  set y : ℕ := (3 ^ a * u - 1) / 2
  set g : ℕ := u * (4 * 3 ^ a - 9 * 2 ^ a)
  have hord : 9 * (x - 1) + g + 5 = 9 * (x - 1) + 5 + g := by ac_rfl
  have hEq : 9 * (x - 1) + 5 + g = 8 * y := by
    rw [← hord]
    exact hslack
  have hlow : 9 * (x - 1) + 5 ≤ 8 * y :=
    Nat.le_trans (Nat.le_add_right (9 * (x - 1) + 5) g) (Nat.le_of_eq hEq)
  have hplus : 9 * (x - 1) + 9 ≤ 8 * y + 4 := by omega
  have h9 : 9 * (x - 1) + 9 = 9 * x := by
    calc
      9 * (x - 1) + 9 = 9 * (x - 1) + 9 * 1 := by norm_num
      _ = 9 * ((x - 1) + 1) := by rw [← Nat.mul_add]
      _ = 9 * x := by rw [hx1]
  have h8 : 8 * y + 8 = 8 * (y + 1) := by
    calc
      8 * y + 8 = 8 * y + 8 * 1 := by norm_num
      _ = 8 * (y + 1) := by rw [← Nat.mul_add]
  calc
    9 * x = 9 * (x - 1) + 9 := by rw [h9]
    _ ≤ 8 * y + 4 := hplus
    _ ≤ 8 * y + 8 := Nat.add_le_add_left (by decide : 4 ≤ 8) (8 * y)
    _ = 8 * (y + 1) := h8

/-- Repeated single-even steps multiply the shifted bound. -/
theorem NineEighthsChain (k : ℕ) (x : ℕ → ℕ)
    (hstep : ∀ i, i < k → 9 * (x i + 1) ≤ 8 * (x (i + 1) + 1)) :
    9 ^ k * (x 0 + 1) ≤ 8 ^ k * (x k + 1) := by
  induction k with
  | zero =>
    { simp }
  | succ k ih =>
    { have hprev : ∀ i, i < k → 9 * (x i + 1) ≤ 8 * (x (i + 1) + 1) := by
        intro i hi
        exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self k))
      have hih := ih hprev
      have hk := hstep k (Nat.lt_succ_self k)
      have hmul : 8 ^ k * (9 * (x k + 1)) ≤ 8 ^ k * (8 * (x (k + 1) + 1)) :=
        Nat.mul_le_mul_left (8 ^ k) hk
      calc
        9 ^ (k + 1) * (x 0 + 1) = 9 * 9 ^ k * (x 0 + 1) := by
          rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, ← Nat.mul_assoc]
        _ = 9 * (9 ^ k * (x 0 + 1)) := by rw [Nat.mul_assoc]
        _ ≤ 9 * (8 ^ k * (x k + 1)) := Nat.mul_le_mul_left 9 hih
        _ = 8 ^ k * (9 * (x k + 1)) := by ac_rfl
        _ ≤ 8 ^ k * (8 * (x (k + 1) + 1)) := hmul
        _ = 8 ^ (k + 1) * (x (k + 1) + 1) := by
          rw [Nat.pow_succ]
          ac_rfl }

/-- If the exit is at most `2 n` and `9 ^ k ≥ 2 * 8 ^ k`, the chain breaks. -/
theorem LocalParentBlocked (k n y : ℕ)
    (hchain : 9 ^ k * (n + 1) ≤ 8 ^ k * (y + 1))
    (hpow : 2 * 8 ^ k ≤ 9 ^ k) (hy : y ≤ 2 * n) : False := by
  have hlt : 2 * n + 1 < 2 * (n + 1) := by omega
  have hpos : 0 < 8 ^ k := by
    have : 1 ≤ 8 ^ k := Nat.one_le_pow k 8 (by decide)
    omega
  have hmul : 8 ^ k * (2 * n + 1) < 8 ^ k * (2 * (n + 1)) :=
    Nat.mul_lt_mul_of_pos_left hlt hpos
  have hy1 : y + 1 ≤ 2 * n + 1 := by omega
  have hle : 8 ^ k * (y + 1) ≤ 8 ^ k * (2 * n + 1) :=
    Nat.mul_le_mul_left (8 ^ k) hy1
  have hleft : 2 * 8 ^ k * (n + 1) ≤ 9 ^ k * (n + 1) :=
    Nat.mul_le_mul_right (n + 1) hpow
  have h8 : 8 ^ k * (2 * (n + 1)) = 2 * 8 ^ k * (n + 1) := by
    calc
      8 ^ k * (2 * (n + 1)) = 8 ^ k * 2 * (n + 1) := by rw [← Nat.mul_assoc]
      _ = 2 * 8 ^ k * (n + 1) := by
        rw [Nat.mul_comm (8 ^ k) 2, Nat.mul_assoc]
  have hcontra : 2 * 8 ^ k * (n + 1) < 2 * 8 ^ k * (n + 1) := by
    calc
      2 * 8 ^ k * (n + 1) ≤ 9 ^ k * (n + 1) := hleft
      _ ≤ 8 ^ k * (y + 1) := hchain
      _ ≤ 8 ^ k * (2 * n + 1) := hle
      _ < 8 ^ k * (2 * (n + 1)) := hmul
      _ = 2 * 8 ^ k * (n + 1) := h8
  omega

/-- The sixth power already dominates twice the eighth power. -/
theorem LengthSixPower : 2 * 8 ^ 6 ≤ 9 ^ 6 := by
  decide

/-- The fifth power does not dominate twice the eighth power. -/
theorem LengthFivePowerFails : ¬ (2 * 8 ^ 5 ≤ 9 ^ 5) := by
  decide

/-- Six growth steps force the exit to be at least `2 n + 1`. -/
theorem LengthSixExitLarge (n y : ℕ)
    (hchain : 9 ^ 6 * (n + 1) ≤ 8 ^ 6 * (y + 1)) : 2 * n + 1 ≤ y := by
  by_contra hlt
  have hy : y ≤ 2 * n := by omega
  exact LocalParentBlocked 6 n y hchain LengthSixPower hy

/-- The cleared quarter parent is not strictly below `n`. -/
theorem QuarterClearedBlocked (n y : ℕ) (hy : 2 * n + 1 ≤ y) :
    ¬ (3 * y + 1 < 4 * n) := by
  omega

/-- The cleared half parent is not strictly below `n`. -/
theorem HalfClearedBlocked (n y : ℕ) (hy : 2 * n + 1 ≤ y) :
    ¬ (y - 1 < 2 * n) := by
  omega

/-- The cleared third parent is not strictly below `n`. -/
theorem ThirdClearedBlocked (n y : ℕ) (hy : 2 * n + 1 ≤ y) :
    ¬ (2 * y - 1 < 3 * n) := by
  omega

/-- The cleared even parent is not strictly below `n`. -/
theorem EvenClearedBlocked (n y : ℕ) (hy : 2 * n + 1 ≤ y) :
    ¬ (y < 2 * n) := by
  omega

/-- After six growth steps, no elementary cleared parent lies below `n`. -/
theorem LengthSixParentsFail (n y : ℕ)
    (hchain : 9 ^ 6 * (n + 1) ≤ 8 ^ 6 * (y + 1)) :
    2 * n + 1 ≤ y ∧ ¬ (3 * y + 1 < 4 * n) ∧ ¬ (y - 1 < 2 * n) ∧
      ¬ (2 * y - 1 < 3 * n) ∧ ¬ (y < 2 * n) := by
  have hy := LengthSixExitLarge n y hchain
  exact ⟨hy, QuarterClearedBlocked n y hy, HalfClearedBlocked n y hy,
    ThirdClearedBlocked n y hy, EvenClearedBlocked n y hy⟩

/-- Residue `(-1) ^ (a + 1)` modulo four. -/
def ResidualResidue (a : ℕ) : ℕ :=
  if a % 2 = 0 then 3 else 1

/-- Residue `(-1) ^ a` modulo four. -/
def TwoEvenResidue (a : ℕ) : ℕ :=
  if a % 2 = 0 then 1 else 3

/-- Powers of three alternate between `1` and `3` modulo four. -/
theorem ThreePowModFour (a : ℕ) :
    3 ^ a % 4 = if a % 2 = 0 then 1 else 3 := by
  induction a with
  | zero =>
    { simp }
  | succ a ih =>
    { rw [Nat.pow_succ, Nat.mul_mod, ih]
      rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
      · have hsucc : (a + 1) % 2 = 1 := by omega
        simp [h0, hsucc]
      · have hsucc : (a + 1) % 2 = 0 := by omega
        simp [h1, hsucc] }

/-- A residual odd part makes the weight congruent to three modulo four. -/
theorem ResidualWeightModFour (a u : ℕ) (hu : u % 4 = ResidualResidue a) :
    3 ^ a * u % 4 = 3 := by
  rw [Nat.mul_mod, ThreePowModFour]
  by_cases h : a % 2 = 0
  · simp [ResidualResidue, h, hu]
  · have h1 : a % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
      · exact absurd h0 h
      · exact h1
    simp [ResidualResidue, h1, hu]

/-- A two-even odd part makes the weight congruent to one modulo four. -/
theorem TwoEvenWeightModFour (a u : ℕ) (hu : u % 4 = TwoEvenResidue a) :
    3 ^ a * u % 4 = 1 := by
  rw [Nat.mul_mod, ThreePowModFour]
  by_cases h : a % 2 = 0
  · simp [TwoEvenResidue, h, hu]
  · have h1 : a % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
      · exact absurd h0 h
      · exact h1
    simp [TwoEvenResidue, h1, hu]

/-- Congruence three modulo four is exact 2-adic order one. -/
theorem SingleEvenData (w : ℕ) (hw : w % 4 = 3) :
    2 * ((w - 1) / 2) = w - 1 ∧ (w - 1) / 2 % 2 = 1 := by
  have hrep : w = 4 * (w / 4) + 3 := by
    have h := Nat.div_add_mod w 4
    omega
  have hsub : w - 1 = 2 * (2 * (w / 4) + 1) := by
    have hge : 1 ≤ w := by omega
    rw [hrep]
    omega
  have hdiv : (w - 1) / 2 = 2 * (w / 4) + 1 := by
    rw [hsub]
    exact Nat.mul_div_cancel_left _ (by decide)
  refine ⟨?_, ?_⟩
  · rw [hdiv, hsub]
  · rw [hdiv]
    omega

/-- One odd shortcut on a state with a positive power of two. -/
theorem OddShortcutStep (b j u : ℕ) (hb : 1 ≤ b) (hu : u % 2 = 1) :
    Shortcut (2 ^ b * 3 ^ j * u - 1) =
      2 ^ (b - 1) * 3 ^ (j + 1) * u - 1 := by
  have hu0 : 0 < u := by omega
  have h3pos : 0 < 3 ^ j := by
    have : 1 ≤ 3 ^ j := Nat.one_le_pow j 3 (by decide)
    omega
  set Q : ℕ := 2 ^ (b - 1) * 3 ^ j * u
  set M : ℕ := 2 ^ b * 3 ^ j * u
  set P : ℕ := 2 ^ (b - 1) * 3 ^ (j + 1) * u
  have hsplit : 2 ^ b = 2 ^ (b - 1) * 2 := by
    have hb' : b = (b - 1) + 1 := by omega
    nth_rw 1 [hb']
    rw [Nat.pow_succ]
  have hMQ : M = 2 * Q := by
    unfold M Q
    rw [hsplit]
    calc
      2 ^ (b - 1) * 2 * 3 ^ j * u = 2 * 2 ^ (b - 1) * 3 ^ j * u := by
        rw [Nat.mul_comm (2 ^ (b - 1)) 2]
      _ = 2 * (2 ^ (b - 1) * 3 ^ j * u) := by ac_rfl
  have hPQ : P = 3 * Q := by
    unfold P Q
    rw [Nat.pow_succ]
    calc
      2 ^ (b - 1) * (3 ^ j * 3) * u = 2 ^ (b - 1) * (3 * 3 ^ j) * u := by
        rw [Nat.mul_comm (3 ^ j) 3]
      _ = 2 ^ (b - 1) * 3 * 3 ^ j * u := by ac_rfl
      _ = 3 * (2 ^ (b - 1) * 3 ^ j) * u := by ac_rfl
      _ = 3 * (2 ^ (b - 1) * 3 ^ j * u) := by ac_rfl
  have h2P : 2 * P = 3 * M := by
    calc
      2 * P = 2 * (3 * Q) := by rw [hPQ]
      _ = 3 * (2 * Q) := by rw [Nat.mul_left_comm]
      _ = 3 * M := by rw [← hMQ]
  have hM1 : 1 ≤ M := by
    have h2 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    have h3 : 1 ≤ 3 ^ j := Nat.one_le_pow j 3 (by decide)
    have h23 : 1 ≤ 2 ^ b * 3 ^ j :=
      Nat.le_trans h2 (Nat.le_mul_of_pos_right (2 ^ b) h3pos)
    exact Nat.le_trans h23 (Nat.le_mul_of_pos_right (2 ^ b * 3 ^ j) hu0)
  have hP1 : 1 ≤ P := by
    have hQ1 : 1 ≤ Q := by
      have h2 : 1 ≤ 2 ^ (b - 1) := Nat.one_le_two_pow
      have h3 : 1 ≤ 3 ^ j := Nat.one_le_pow j 3 (by decide)
      have h23 : 1 ≤ 2 ^ (b - 1) * 3 ^ j :=
        Nat.le_trans h2 (Nat.le_mul_of_pos_right (2 ^ (b - 1)) h3pos)
      exact Nat.le_trans h23 (Nat.le_mul_of_pos_right _ hu0)
    rw [hPQ]
    exact Nat.le_trans (by decide : 1 ≤ 3) (Nat.le_mul_of_pos_right 3 (by omega))
  have hnum : 3 * (M - 1) + 1 = 2 * (P - 1) := by
    have h3 : 3 * (M - 1) = 3 * M - 3 := Nat.mul_sub_one 3 M
    have h2 : 2 * (P - 1) = 2 * P - 2 := Nat.mul_sub_one 2 P
    have h3le : 3 ≤ 3 * M := by
      have hmul := Nat.mul_le_mul_left 3 hM1
      omega
    have h2le : 2 ≤ 2 * P := by
      have hmul := Nat.mul_le_mul_left 2 hP1
      omega
    have hL : 3 * (M - 1) + 1 = 3 * M - 2 := by
      rw [h3]
      omega
    have hR : 2 * (P - 1) = 3 * M - 2 := by
      rw [h2, h2P]
    exact hL.trans hR.symm
  have hevenM : M % 2 = 0 := by
    rw [hMQ]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right 2 Q)
  have hodd : (M - 1) % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (M - 1) with h0 | h1
    · have hsum : (M - 1 + 1) % 2 = 1 := by
        rw [Nat.add_mod, h0]
      rw [Nat.sub_add_cancel hM1, hevenM] at hsum
      omega
    · exact h1
  rw [ShortcutOdd (M - 1) hodd, hnum]
  exact Nat.mul_div_cancel_left (P - 1) (by decide)

/-- The first `j ≤ a` odd shortcuts stay on the explicit run. -/
theorem RunIterate (a u : ℕ) (hu : u % 2 = 1) :
    ∀ j, j ≤ a →
      IterShortcut j (2 ^ a * u - 1) = 3 ^ j * 2 ^ (a - j) * u - 1 := by
  intro j
  induction j with
  | zero =>
    { intro _
      simp [IterShortcut, pow_zero] }
  | succ j ih =>
    { intro hj
      have hj' : j ≤ a := Nat.le_of_succ_le hj
      have hlt : j < a := hj
      have hb : 1 ≤ a - j := by
        have hpos : 0 < a - j := Nat.sub_pos_of_lt hlt
        omega
      have hih := ih hj'
      rw [IterShortcutSucc, hih]
      have hcomm : 3 ^ j * 2 ^ (a - j) * u = 2 ^ (a - j) * 3 ^ j * u := by
        rw [Nat.mul_comm (3 ^ j) (2 ^ (a - j))]
      rw [hcomm]
      have hstep := OddShortcutStep (a - j) j u hb hu
      rw [hstep]
      have hsub : (a - j) - 1 = a - (j + 1) := by omega
      rw [hsub]
      rw [Nat.mul_comm (2 ^ (a - (j + 1))) (3 ^ (j + 1))] }

/-- A residual seed reaches its single-even exit in `a + 1` shortcuts. -/
theorem ReachSingleEvenExit (a u : ℕ) (hu : u % 2 = 1)
    (hmod : 3 ^ a * u % 4 = 3) :
    IterShortcut (a + 1) (2 ^ a * u - 1) = (3 ^ a * u - 1) / 2 := by
  have hrun := RunIterate a u hu a (le_refl a)
  rw [IterShortcutSucc, hrun]
  have hstate : 3 ^ a * 2 ^ (a - a) * u - 1 = 3 ^ a * u - 1 := by
    rw [Nat.sub_self, pow_zero, Nat.mul_one]
  rw [hstate]
  have hdata := SingleEvenData (3 ^ a * u) hmod
  have heven : (3 ^ a * u - 1) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd ⟨(3 ^ a * u - 1) / 2, hdata.1.symm⟩
  rw [ShortcutEven _ heven]

/-- Two shortcuts from a seed congruent to one modulo four reach the quarter. -/
theorem QuarterParent (y : ℕ) (hy : y % 4 = 1) :
    4 ∣ 3 * y + 1 ∧ Shortcut (Shortcut y) = (3 * y + 1) / 4 := by
  have hrep : y = 4 * (y / 4) + 1 := by
    have h := Nat.div_add_mod y 4
    omega
  set t : ℕ := y / 4
  have hdiv : 3 * y + 1 = 4 * (3 * t + 1) := by
    rw [hrep]
    omega
  have hdvd : 4 ∣ 3 * y + 1 := ⟨3 * t + 1, hdiv⟩
  have hodd : y % 2 = 1 := by
    have hmod : y % 4 % 2 = y % 2 := Nat.mod_mod_of_dvd y (by decide : 2 ∣ 4)
    rw [hy] at hmod
    norm_num at hmod
    exact hmod.symm
  have h1 : Shortcut y = 2 * (3 * t + 1) := by
    rw [ShortcutOdd y hodd, hdiv]
    have h4 : 4 * (3 * t + 1) = 2 * (2 * (3 * t + 1)) := by omega
    rw [h4]
    exact Nat.mul_div_cancel_left _ (by decide)
  have h2 : Shortcut (Shortcut y) = 3 * t + 1 := by
    rw [h1, ShortcutEven _ (Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right 2 _))]
    exact Nat.mul_div_cancel_left _ (by decide)
  have hquot : (3 * y + 1) / 4 = 3 * t + 1 := by
    rw [hdiv]
    exact Nat.mul_div_cancel_left _ (by decide)
  exact ⟨hdvd, by rw [h2, hquot]⟩

/-- The odd part one step before a two-even weight is still three modulo four. -/
theorem TwoEvenPredModFour (a u : ℕ) (ha : 1 ≤ a)
    (hu : u % 4 = TwoEvenResidue a) : 3 ^ (a - 1) * u % 4 = 3 := by
  rw [Nat.mul_mod, ThreePowModFour]
  by_cases h : a % 2 = 0
  · have hpred : (a - 1) % 2 = 1 := by omega
    simp [TwoEvenResidue, h, hpred, hu]
  · have h1 : a % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
      · exact absurd h0 h
      · exact h1
    have hpred : (a - 1) % 2 = 0 := by omega
    simp [TwoEvenResidue, h1, hpred, hu]

/-- The two-even source and its half parent meet after the stated shortcuts. -/
theorem TwoEvenMeeting (a u : ℕ) (ha : 1 ≤ a) (hu : u % 2 = 1)
    (hmod : u % 4 = TwoEvenResidue a) :
    let y := 2 ^ a * u - 1
    let p := 2 ^ (a - 1) * u - 1
    let m := (3 ^ a * u - 1) / 4
    4 ∣ 3 ^ a * u - 1 ∧ IterShortcut (a + 2) y = m ∧
      IterShortcut (a + 1) p = m := by
  intro y p m
  have hW : 3 ^ a * u % 4 = 1 := TwoEvenWeightModFour a u hmod
  have hge : 1 ≤ 3 ^ a * u := by
    have h3 : 1 ≤ 3 ^ a := Nat.one_le_pow a 3 (by decide)
    have hu0 : 0 < u := by omega
    exact Nat.le_trans h3 (Nat.le_mul_of_pos_right (3 ^ a) hu0)
  have hrep : 3 ^ a * u = 4 * ((3 ^ a * u) / 4) + 1 := by
    have h := Nat.div_add_mod (3 ^ a * u) 4
    omega
  have hdvd : 4 ∣ 3 ^ a * u - 1 := by
    refine ⟨(3 ^ a * u) / 4, ?_⟩
    have hsub : 3 ^ a * u - 1 = 4 * ((3 ^ a * u) / 4) := by
      rw [hrep]
      omega
    exact hsub
  have hyrun := RunIterate a u hu a (le_refl a)
  have hystate : 3 ^ a * 2 ^ (a - a) * u - 1 = 3 ^ a * u - 1 := by
    rw [Nat.sub_self, pow_zero, Nat.mul_one]
  have htwo : IterShortcut (a + 2) y =
      Shortcut (Shortcut (3 ^ a * u - 1)) := by
    rw [show a + 2 = a + 1 + 1 by omega, IterShortcutSucc, IterShortcutSucc]
    rw [hyrun, hystate]
  have he1 : (3 ^ a * u - 1) % 2 = 0 := by
    have h2 : 2 ∣ 3 ^ a * u - 1 := Nat.dvd_trans (by decide : 2 ∣ 4) hdvd
    exact Nat.mod_eq_zero_of_dvd h2
  have hhalf : Shortcut (3 ^ a * u - 1) = (3 ^ a * u - 1) / 2 :=
    ShortcutEven _ he1
  have hquarter : (3 ^ a * u - 1) / 2 / 2 = (3 ^ a * u - 1) / 4 := by
    rw [Nat.div_div_eq_div_mul]
  have he2 : ((3 ^ a * u - 1) / 2) % 2 = 0 := by
    have hmul : 2 * ((3 ^ a * u - 1) / 4) = (3 ^ a * u - 1) / 2 := by
      have hfour : 4 * ((3 ^ a * u - 1) / 4) = 3 ^ a * u - 1 :=
        Nat.mul_div_cancel' hdvd
      have hsplit : 4 * ((3 ^ a * u - 1) / 4) =
          2 * (2 * ((3 ^ a * u - 1) / 4)) := by omega
      apply Nat.mul_left_cancel (by decide : 0 < 2)
      calc
        2 * (2 * ((3 ^ a * u - 1) / 4)) = 4 * ((3 ^ a * u - 1) / 4) := by
          omega
        _ = 3 ^ a * u - 1 := Nat.mul_div_cancel' hdvd
        _ = 2 * ((3 ^ a * u - 1) / 2) :=
          (Nat.mul_div_cancel'
            (Nat.dvd_trans (by decide : 2 ∣ 4) hdvd)).symm
    exact Nat.mod_eq_zero_of_dvd ⟨(3 ^ a * u - 1) / 4, hmul.symm⟩
  have hsource : IterShortcut (a + 2) y = m := by
    rw [htwo, hhalf, ShortcutEven _ he2, hquarter]
  have hpred := TwoEvenPredModFour a u ha hmod
  have hprun := RunIterate (a - 1) u hu (a - 1) (le_refl (a - 1))
  have hpstate : 3 ^ (a - 1) * 2 ^ ((a - 1) - (a - 1)) * u - 1 =
      3 ^ (a - 1) * u - 1 := by
    rw [Nat.sub_self, pow_zero, Nat.mul_one]
  have hs : 3 ^ (a - 1) * u % 4 = 3 := hpred
  have hseven : (3 ^ (a - 1) * u - 1) % 2 = 0 := by
    have hdata := SingleEvenData (3 ^ (a - 1) * u) hs
    exact Nat.mod_eq_zero_of_dvd ⟨_, hdata.1.symm⟩
  have hq : (3 ^ (a - 1) * u - 1) / 2 % 2 = 1 :=
    (SingleEvenData (3 ^ (a - 1) * u) hs).2
  have hparentSteps : IterShortcut (a + 1) p =
      Shortcut ((3 ^ (a - 1) * u - 1) / 2) := by
    rw [show a + 1 = (a - 1) + 1 + 1 by omega, IterShortcutSucc, IterShortcutSucc]
    rw [hprun, hpstate, ShortcutEven _ hseven]
  have hjoin : 4 * ((3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) / 2) =
      3 ^ a * u - 1 := by
    have hdata := SingleEvenData (3 ^ (a - 1) * u) hs
    have hq2 : 2 * ((3 ^ (a - 1) * u - 1) / 2) = 3 ^ (a - 1) * u - 1 := hdata.1
    have hthree : 3 * ((3 ^ (a - 1) * u - 1) / 2) % 2 = 1 := by
      rw [Nat.mul_mod, hdata.2]
    have heven3 : (3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) % 2 = 0 := by
      rw [Nat.add_mod, hthree]
    have hclear : 2 * ((3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) / 2) =
        3 * ((3 ^ (a - 1) * u - 1) / 2) + 1 :=
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero heven3)
    have hmul4 : 4 * ((3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) / 2) =
        2 * (3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) := by
      calc
        4 * ((3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) / 2) =
            (2 * 2) * ((3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) / 2) := by norm_num
        _ = 2 * (2 * ((3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) / 2)) := by
          rw [Nat.mul_assoc]
        _ = 2 * (3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) := by rw [hclear]
    rw [hmul4]
    have hlin : 2 * (3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) =
        3 * (3 ^ (a - 1) * u - 1) + 2 := by
      calc
        2 * (3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) =
            2 * (3 * ((3 ^ (a - 1) * u - 1) / 2)) + 2 := by
          rw [Nat.mul_add, Nat.mul_one]
        _ = 3 * (2 * ((3 ^ (a - 1) * u - 1) / 2)) + 2 := by
          rw [Nat.mul_left_comm]
        _ = 3 * (3 ^ (a - 1) * u - 1) + 2 := by rw [hq2]
    rw [hlin]
    have hpow : 3 * 3 ^ (a - 1) = 3 ^ a := by
      have ha' : a = (a - 1) + 1 := by omega
      calc
        3 * 3 ^ (a - 1) = 3 ^ (a - 1) * 3 := by rw [Nat.mul_comm]
        _ = 3 ^ ((a - 1) + 1) := by rw [← Nat.pow_succ]
        _ = 3 ^ a := by rw [← ha']
    have h3le : 3 ≤ 3 * 3 ^ (a - 1) * u := by
      have hpos : 0 < 3 ^ (a - 1) * u := by
        have h3 : 0 < 3 ^ (a - 1) := by
          have : 1 ≤ 3 ^ (a - 1) := Nat.one_le_pow (a - 1) 3 (by decide)
          omega
        have hu0 : 0 < u := by omega
        exact Nat.mul_pos h3 hu0
      rw [Nat.mul_assoc]
      exact Nat.le_mul_of_pos_right 3 hpos
    calc
      3 * (3 ^ (a - 1) * u - 1) + 2 = 3 * (3 ^ (a - 1) * u) - 3 + 2 := by
        rw [Nat.mul_sub_one]
      _ = 3 * 3 ^ (a - 1) * u - 1 := by
        rw [← Nat.mul_assoc]
        omega
      _ = 3 ^ a * u - 1 := by rw [hpow]
  have hparent : IterShortcut (a + 1) p = m := by
    rw [hparentSteps, ShortcutOdd _ hq]
    have hdiv4 : ((3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) / 2) =
        (3 ^ a * u - 1) / 4 := by
      have hmul := hjoin
      have hpos4 : 0 < 4 := by decide
      have hleft := Nat.mul_div_cancel_left
        ((3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) / 2) hpos4
      have hright := Nat.mul_div_cancel' hdvd
      have hEq : 4 * ((3 * ((3 ^ (a - 1) * u - 1) / 2) + 1) / 2) =
          4 * ((3 ^ a * u - 1) / 4) := by
        rw [hmul, hright]
      exact Nat.mul_left_cancel hpos4 hEq
    exact hdiv4
  exact ⟨hdvd, hsource, hparent⟩

/-- `3 ^ a * u + 1` is never divisible by three for `a ≥ 1`. -/
theorem ThreeFreeSuccessor (a u : ℕ) (ha : 1 ≤ a) : ¬ 3 ∣ 3 ^ a * u + 1 := by
  intro hdvd
  have hmod : (3 ^ a * u + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hpow : 3 ^ a % 3 = 0 := by
    cases a with
    | zero =>
      { omega }
    | succ a =>
      { rw [Nat.pow_succ, Nat.mul_mod]
        norm_num }
  rw [Nat.add_mod, Nat.mul_mod, hpow] at hmod
  norm_num at hmod

/-- A 3-free quotient determines the exponent in `3 ^ a * u`. -/
theorem ThreePowerLe (a u a' u' : ℕ) (hu : ¬ 3 ∣ u) (hle : a ≤ a')
    (h : 3 ^ a * u = 3 ^ a' * u') : a = a' ∧ u = u' := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have hpos : 0 < 3 ^ a := by
    have : 1 ≤ 3 ^ a := Nat.one_le_pow a 3 (by decide)
    omega
  have hmul : u = 3 ^ k * u' := by
    apply Nat.mul_left_cancel hpos
    calc
      3 ^ a * u = 3 ^ a' * u' := h
      _ = 3 ^ (a + k) * u' := by rw [hk]
      _ = 3 ^ a * 3 ^ k * u' := by rw [Nat.pow_add]
      _ = 3 ^ a * (3 ^ k * u') := by rw [Nat.mul_assoc]
  have hk0 : k = 0 := by
    cases k with
    | zero =>
      { rfl }
    | succ k =>
      { have hdvd : 3 ∣ u := by
          rw [hmul, Nat.pow_succ]
          exact ⟨3 ^ k * u', by ac_rfl⟩
        exact absurd hdvd hu }
  have ha : a' = a := by
    rw [hk, hk0, Nat.add_zero]
  have huu : u = u' := by
    simpa [hk0] using hmul
  exact ⟨ha.symm, huu⟩

/-- Equal 3-free factorizations have the same exponent and quotient. -/
theorem ThreePowerUnique (a u a' u' : ℕ) (hu : ¬ 3 ∣ u) (hu' : ¬ 3 ∣ u')
    (h : 3 ^ a * u = 3 ^ a' * u') : a = a' ∧ u = u' := by
  cases Nat.le_total a a' with
  | inl hle =>
    { exact ThreePowerLe a u a' u' hu hle h }
  | inr hge =>
    { have hswap := ThreePowerLe a' u' a u hu' hge h.symm
      exact ⟨hswap.1.symm, hswap.2.symm⟩ }

/-- The seed `75 = 2 ^ 2 * 19 - 1` exits at `85` and meets the parent `64`. -/
theorem ExampleSeventyFive :
    75 = 2 ^ 2 * 19 - 1 ∧ 19 % 2 = 1 ∧ 19 % 4 = 3 ∧
      85 = (3 ^ 2 * 19 - 1) / 2 ∧ 85 % 4 = 1 ∧
      64 = (3 * 85 + 1) / 4 ∧ 64 < 75 := by
  decide

end GeneralizedCollatz
