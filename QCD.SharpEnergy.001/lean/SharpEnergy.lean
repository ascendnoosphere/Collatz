-- SPDX-License-Identifier: CC-BY-4.0
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Data.List.Count
import Init.Data.Nat.Lemmas
import Init.Omega
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Carry energy of the block word `0^b 1^r 0^(b-1) 1 0 1^(r-1)`.

An even letter is `false` and an odd letter is `true`. For integers `b, r ≥ 1`
the two halves both have length `h = b + r` and both contain `r` odd letters.
They differ by the adjacent swap at indices `b - 1` and `b`. The ratio is
`λ = 3^r / 2^h`. The carry energy is the unique rational `E` with
`1 - λ E = E`, hence `E = 2^h / (2^h + 3^r)`. This is strictly above `1 / 2`
exactly when `3^r < 2^h`, and it is never equal to `1 / 2` for `b ≥ 1`.
For fixed `b` the energy tends to `0` as `r` grows. Along a sequence it tends
to `1 / 2` from above exactly when the ratio is below `1` and tends to `1`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Number of odd letters in a parity word. -/
def OddCount (w : List Bool) : ℕ :=
  w.count true

/-- Common half length `b + r`. -/
def SharpHeight (b r : ℕ) : ℕ :=
  b + r

/-- First half `0^b 1^r`. -/
def SharpFirst (b r : ℕ) : List Bool :=
  List.replicate b false ++ List.replicate r true

/-- Second half `0^(b-1) 1 0 1^(r-1)`. -/
def SharpSecond (b r : ℕ) : List Bool :=
  List.replicate (b - 1) false ++
    (true :: false :: List.replicate (r - 1) true)

/-- The block word `0^b 1^r 0^(b-1) 1 0 1^(r-1)`. -/
def SharpWord (b r : ℕ) : List Bool :=
  SharpFirst b r ++ SharpSecond b r

/-- The first half has length `b + r`. -/
theorem SharpFirstLength (b r : ℕ) :
    (SharpFirst b r).length = SharpHeight b r := by
  unfold SharpFirst SharpHeight
  rw [List.length_append, List.length_replicate, List.length_replicate]

/-- The second half has length `b + r` once both exponents are positive. -/
theorem SharpSecondLength (b r : ℕ) (hb : 1 ≤ b) (hr : 1 ≤ r) :
    (SharpSecond b r).length = SharpHeight b r := by
  unfold SharpSecond SharpHeight
  rw [List.length_append, List.length_replicate, List.length_cons,
    List.length_cons, List.length_replicate]
  omega

/-- The concatenated word has length `2(b + r)`. -/
theorem SharpWordLength (b r : ℕ) (hb : 1 ≤ b) (hr : 1 ≤ r) :
    (SharpWord b r).length = 2 * SharpHeight b r := by
  unfold SharpWord
  rw [List.length_append, SharpFirstLength, SharpSecondLength b r hb hr,
    Nat.two_mul]

/-- The first half contains `r` odd letters. -/
theorem SharpFirstOddCount (b r : ℕ) : OddCount (SharpFirst b r) = r := by
  unfold OddCount SharpFirst
  rw [List.count_append]
  have hzero : List.count true (List.replicate b false) = 0 := by
    rw [List.count_replicate]
    have hbeq : (false == true) = false := by decide
    rw [hbeq]
    rfl
  rw [hzero, Nat.zero_add, List.count_replicate_self]

/-- The second half contains `r` odd letters once `r` is positive. -/
theorem SharpSecondOddCount (b r : ℕ) (hr : 1 ≤ r) :
    OddCount (SharpSecond b r) = r := by
  unfold OddCount SharpSecond
  rw [List.count_append]
  have hzero : List.count true (List.replicate (b - 1) false) = 0 := by
    rw [List.count_replicate]
    have hbeq : (false == true) = false := by decide
    rw [hbeq]
    rfl
  rw [hzero, Nat.zero_add, List.count_cons_self,
    List.count_cons_of_ne (by decide : false ≠ true),
    List.count_replicate_self]
  omega

/-- The concatenated word contains `2r` odd letters. -/
theorem SharpWordOddCount (b r : ℕ) (hr : 1 ≤ r) :
    OddCount (SharpWord b r) = 2 * r := by
  unfold SharpWord OddCount
  rw [List.count_append, ← OddCount, ← OddCount, SharpFirstOddCount,
    SharpSecondOddCount b r hr, Nat.two_mul]

/-- Before the odd block, the first half is even. -/
theorem SharpFirstLow (b r i : ℕ) (hi : i < b) :
    (SharpFirst b r).getD i false = false := by
  have hlenEq : (List.replicate b false).length = b := by
    rw [List.length_replicate]
  have hopt : (SharpFirst b r)[i]? = some false := by
    unfold SharpFirst
    rw [List.getElem?_append_left (hlenEq.symm ▸ hi)]
    exact List.getElem?_replicate_of_lt hi
  rw [List.getD, hopt]
  rfl

/-- From the odd block onward, the first half is odd. -/
theorem SharpFirstHigh (b r i : ℕ) (hb : b ≤ i) (hi : i < b + r) :
    (SharpFirst b r).getD i false = true := by
  have hlenEq : (List.replicate b false).length = b := by
    rw [List.length_replicate]
  have hopt : (SharpFirst b r)[i]? = some true := by
    unfold SharpFirst
    rw [List.getElem?_append_right (hlenEq.symm ▸ hb)]
    rw [hlenEq]
    exact List.getElem?_replicate_of_lt (by omega : i - b < r)
  rw [List.getD, hopt]
  rfl

/-- Before index `b - 1`, the second half is even. -/
theorem SharpSecondLow (b r i : ℕ) (hi : i < b - 1) :
    (SharpSecond b r).getD i false = false := by
  have hlenEq : (List.replicate (b - 1) false).length = b - 1 := by
    rw [List.length_replicate]
  have hopt : (SharpSecond b r)[i]? = some false := by
    unfold SharpSecond
    rw [List.getElem?_append_left (hlenEq.symm ▸ hi)]
    exact List.getElem?_replicate_of_lt hi
  rw [List.getD, hopt]
  rfl

/-- On the bridge and after it, the second half is odd except at index `b`. -/
theorem SharpSecondFromBridge (b r i : ℕ) (hb : 1 ≤ b) (hr : 1 ≤ r)
    (hlo : b - 1 ≤ i) (hi : i < b + r) :
    (SharpSecond b r).getD i false =
      if i = b then false else true := by
  have hlenEq : (List.replicate (b - 1) false).length = b - 1 := by
    rw [List.length_replicate]
  have hopt : (SharpSecond b r)[i]? =
      some (if i = b then false else true) := by
    unfold SharpSecond
    rw [List.getElem?_append_right (hlenEq.symm ▸ hlo)]
    rw [hlenEq]
    cases hoffset : i - (b - 1) with
    | zero =>
      {
        have hine : i ≠ b := by omega
        rw [List.getElem?_cons_zero, if_neg hine]
      }
    | succ j =>
      {
        rw [List.getElem?_cons_succ]
        cases j with
        | zero =>
          {
            have hib : i = b := by omega
            rw [List.getElem?_cons_zero, if_pos hib]
          }
        | succ j =>
          {
            have hine : i ≠ b := by omega
            have hlt : j < r - 1 := by omega
            rw [List.getElem?_cons_succ, List.getElem?_replicate_of_lt hlt,
              if_neg hine]
          }
      }
  rw [List.getD, hopt]
  rfl

/-- Off the adjacent swap, the two halves carry the same letter. -/
theorem SharpHalvesAgree (b r i : ℕ) (hb : 1 ≤ b) (hr : 1 ≤ r)
    (hi : i < b + r) (hside : i < b - 1 ∨ b < i) :
    (SharpFirst b r).getD i false =
      (SharpSecond b r).getD i false := by
  cases hside with
  | inl hlt =>
    {
      rw [SharpFirstLow b r i (by omega), SharpSecondLow b r i hlt]
    }
  | inr hgt =>
    {
      rw [SharpFirstHigh b r i (by omega) hi,
        SharpSecondFromBridge b r i hb hr (by omega) hi,
        if_neg (by omega : i ≠ b)]
    }

/-- The halves differ by swapping the adjacent letters at `b - 1` and `b`. -/
theorem SharpHalvesDiffer (b r : ℕ) (hb : 1 ≤ b) (hr : 1 ≤ r) :
    (SharpFirst b r).getD (b - 1) false = false ∧
      (SharpSecond b r).getD (b - 1) false = true ∧
      (SharpFirst b r).getD b false = true ∧
      (SharpSecond b r).getD b false = false ∧
      (b - 1) + 1 = b := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact SharpFirstLow b r (b - 1) (by omega)
  · rw [SharpSecondFromBridge b r (b - 1) hb hr (by omega) (by omega),
      if_neg (by omega : b - 1 ≠ b)]
  · exact SharpFirstHigh b r b (Nat.le_refl _) (by omega)
  · rw [SharpSecondFromBridge b r b hb hr (by omega) (by omega), if_pos rfl]
  · omega

/-- The ratio `3^r / 2^{b+r}` attached to the common half length. -/
def SharpRatio (b r : ℕ) : ℚ :=
  (3 ^ r : ℚ) / (2 ^ SharpHeight b r : ℚ)

/-- The ratio is nonnegative. -/
theorem SharpRatioNonneg (b r : ℕ) : 0 ≤ SharpRatio b r := by
  unfold SharpRatio
  have hnum : (0 : ℚ) ≤ (3 ^ r : ℚ) := by
    exact_mod_cast Nat.zero_le (3 ^ r)
  have hden : (0 : ℚ) ≤ (2 ^ SharpHeight b r : ℚ) := by
    exact_mod_cast Nat.zero_le (2 ^ SharpHeight b r)
  exact div_nonneg hnum hden

/-- The ratio is positive. -/
theorem SharpRatioPos (b r : ℕ) : 0 < SharpRatio b r := by
  unfold SharpRatio
  have hnum : (0 : ℚ) < (3 ^ r : ℚ) := by
    exact_mod_cast Nat.pow_pos (by decide : (0 : ℕ) < 3)
  have hden : (0 : ℚ) < (2 ^ SharpHeight b r : ℚ) := by
    exact_mod_cast Nat.two_pow_pos (SharpHeight b r)
  exact div_pos hnum hden

/-- The ratio is below one exactly when `3^r < 2^{b+r}`. -/
theorem SharpRatioLtOne (b r : ℕ) :
    SharpRatio b r < 1 ↔ 3 ^ r < 2 ^ SharpHeight b r := by
  unfold SharpRatio SharpHeight
  have hQ : (0 : ℚ) < (2 ^ (b + r) : ℚ) := by
    exact_mod_cast Nat.two_pow_pos (b + r)
  rw [div_lt_iff₀ hQ, one_mul]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- A rational solves the terminal carry equation `1 - λ E = E`. -/
def IsSharpEnergy (b r : ℕ) (E : ℚ) : Prop :=
  1 - SharpRatio b r * E = E

/-- The carry energy `1 / (1 + 3^r / 2^{b+r})`. -/
def SharpEnergy (b r : ℕ) : ℚ :=
  1 / (1 + SharpRatio b r)

/-- The denominator `1 + λ` is nonzero. -/
theorem SharpDenomNe (b r : ℕ) : 1 + SharpRatio b r ≠ 0 := by
  have hρ : 0 ≤ SharpRatio b r := SharpRatioNonneg b r
  exact ne_of_gt (by linarith : (0 : ℚ) < 1 + SharpRatio b r)

/-- The carry energy is positive. -/
theorem SharpEnergyPos (b r : ℕ) : 0 < SharpEnergy b r := by
  unfold SharpEnergy
  exact div_pos one_pos (lt_of_le_of_ne (by
    have hρ : 0 ≤ SharpRatio b r := SharpRatioNonneg b r
    linarith) (SharpDenomNe b r).symm)

/-- The carry energy is the closed ratio of the half length against `3^r`. -/
theorem SharpEnergyClosedForm (b r : ℕ) :
    SharpEnergy b r =
      (2 ^ SharpHeight b r : ℚ) /
        ((2 ^ SharpHeight b r : ℚ) + (3 ^ r : ℚ)) := by
  unfold SharpEnergy SharpRatio
  have hQ : (2 ^ SharpHeight b r : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.two_pow_pos (SharpHeight b r)).ne'
  rw [one_add_div hQ, div_div_eq_mul_div, one_mul]

/-- The displayed energy solves the terminal carry equation. -/
theorem SharpEnergySolves (b r : ℕ) :
    IsSharpEnergy b r (SharpEnergy b r) := by
  unfold IsSharpEnergy SharpEnergy
  have hden : 1 + SharpRatio b r ≠ 0 := SharpDenomNe b r
  have hmul : SharpRatio b r * (1 / (1 + SharpRatio b r)) =
      SharpRatio b r / (1 + SharpRatio b r) := by
    rw [mul_div_assoc', mul_one]
  rw [hmul]
  have hself : (1 + SharpRatio b r) / (1 + SharpRatio b r) = 1 := by
    rw [div_eq_mul_inv, mul_inv_cancel₀ hden]
  calc
    1 - SharpRatio b r / (1 + SharpRatio b r)
        = (1 + SharpRatio b r) / (1 + SharpRatio b r) -
            SharpRatio b r / (1 + SharpRatio b r) := by rw [hself]
    _ = ((1 + SharpRatio b r) - SharpRatio b r) /
          (1 + SharpRatio b r) := by rw [← sub_div]
    _ = 1 / (1 + SharpRatio b r) := by
          have hcancel : (1 + SharpRatio b r) - SharpRatio b r = 1 := by
            ring
          rw [hcancel]

/-- The terminal carry equation has only one rational solution. -/
theorem SharpEnergyUnique (b r : ℕ) {E : ℚ}
    (hE : IsSharpEnergy b r E) : E = SharpEnergy b r := by
  unfold IsSharpEnergy at hE
  unfold SharpEnergy
  have hprod : E * (1 + SharpRatio b r) = 1 := by
    have hlin : 1 = E + SharpRatio b r * E := by linarith
    calc
      E * (1 + SharpRatio b r) = E * 1 + E * SharpRatio b r := by
        rw [mul_add]
      _ = E + SharpRatio b r * E := by rw [mul_one, mul_comm]
      _ = 1 := by linarith
  have hden : 1 + SharpRatio b r ≠ 0 := by
    linarith [SharpRatioPos b r]
  rw [eq_div_iff hden]
  exact hprod

/-- The terminal carry equation cuts out the carry energy. -/
theorem IsSharpEnergyIff (b r : ℕ) (E : ℚ) :
    IsSharpEnergy b r E ↔ E = SharpEnergy b r := by
  constructor
  · intro hE
    exact SharpEnergyUnique b r hE
  · intro hE
    rw [hE]
    exact SharpEnergySolves b r

/-- The energy lies above one half exactly when `3^r < 2^{b+r}`. -/
theorem SharpEnergyGtHalf (b r : ℕ) :
    1 / 2 < SharpEnergy b r ↔ 3 ^ r < 2 ^ SharpHeight b r := by
  rw [SharpEnergyClosedForm]
  have hsum : (0 : ℚ) <
      (2 ^ SharpHeight b r : ℚ) + (3 ^ r : ℚ) := by
    have hQ : (0 : ℚ) < (2 ^ SharpHeight b r : ℚ) := by
      exact_mod_cast Nat.two_pow_pos _
    have hp : (0 : ℚ) ≤ (3 ^ r : ℚ) := by
      exact_mod_cast Nat.zero_le (3 ^ r)
    linarith
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 2) hsum]
  have hcross :
      (1 : ℚ) * ((2 ^ SharpHeight b r : ℚ) + (3 ^ r : ℚ)) <
          (2 ^ SharpHeight b r : ℚ) * 2 ↔
        (3 ^ r : ℚ) < (2 ^ SharpHeight b r : ℚ) := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hcross]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- The energy equals one half exactly when the two powers agree. -/
theorem SharpEnergyEqHalf (b r : ℕ) :
    SharpEnergy b r = 1 / 2 ↔ 2 ^ SharpHeight b r = 3 ^ r := by
  rw [SharpEnergyClosedForm]
  have hsum : (2 ^ SharpHeight b r : ℚ) + (3 ^ r : ℚ) ≠ 0 := by
    have hQ : (0 : ℚ) < (2 ^ SharpHeight b r : ℚ) := by
      exact_mod_cast Nat.two_pow_pos _
    have hp : (0 : ℚ) ≤ (3 ^ r : ℚ) := by
      exact_mod_cast Nat.zero_le (3 ^ r)
    exact ne_of_gt (by linarith)
  rw [div_eq_div_iff hsum (by norm_num : (2 : ℚ) ≠ 0)]
  have hcross :
      (2 ^ SharpHeight b r : ℚ) * 2 =
          1 * ((2 ^ SharpHeight b r : ℚ) + (3 ^ r : ℚ)) ↔
        (2 ^ SharpHeight b r : ℚ) = (3 ^ r : ℚ) := by
    constructor
    · intro h
      linarith
    · intro h
      linarith
  rw [hcross]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- A positive power of two is even modulo two. -/
theorem TwoPowModTwo (h : ℕ) (hh : 1 ≤ h) : 2 ^ h % 2 = 0 := by
  cases h with
  | zero => { omega }
  | succ k =>
    {
      rw [Nat.pow_succ]
      exact Nat.mul_mod_left (2 ^ k) 2
    }

/-- Every power of three is odd modulo two. -/
theorem ThreePowModTwo (r : ℕ) : 3 ^ r % 2 = 1 := by
  induction r with
  | zero => { decide }
  | succ r ih =>
    {
      rw [Nat.pow_succ, Nat.mul_mod, ih]
    }

/-- A positive power of two is not a power of three. -/
theorem TwoPowNeThreePow (h r : ℕ) (hh : 1 ≤ h) : 2 ^ h ≠ 3 ^ r := by
  intro heq
  have hmod : 2 ^ h % 2 = 3 ^ r % 2 := by rw [heq]
  rw [TwoPowModTwo h hh, ThreePowModTwo r] at hmod
  omega

/-- For `b ≥ 1` the carry energy is not one half. -/
theorem SharpEnergyNeHalf (b r : ℕ) (hb : 1 ≤ b) :
    SharpEnergy b r ≠ 1 / 2 := by
  intro h
  have heq : 2 ^ SharpHeight b r = 3 ^ r :=
    (SharpEnergyEqHalf b r).mp h
  have hh : 1 ≤ SharpHeight b r := by
    unfold SharpHeight
    omega
  exact TwoPowNeThreePow (SharpHeight b r) r hh heq

/-- `2^n (n + 2) ≤ 2 * 3^n`. -/
theorem TwoThreeGrowth (n : ℕ) : 2 ^ n * (n + 2) ≤ 2 * 3 ^ n := by
  induction n with
  | zero => { decide }
  | succ n ih =>
    {
      have hcoef : 2 * (n + 3) ≤ 3 * (n + 2) := by omega
      have hidx : (n + 1) + 2 = n + 3 := by omega
      rw [hidx]
      calc
        2 ^ (n + 1) * (n + 3) = 2 ^ n * (2 * (n + 3)) := by
          rw [Nat.pow_succ, Nat.mul_assoc]
        _ ≤ 2 ^ n * (3 * (n + 2)) :=
          Nat.mul_le_mul_left (2 ^ n) hcoef
        _ = 3 * (2 ^ n * (n + 2)) := by rw [Nat.mul_left_comm]
        _ ≤ 3 * (2 * 3 ^ n) := Nat.mul_le_mul_left 3 ih
        _ = 2 * 3 ^ (n + 1) := by
          rw [Nat.mul_left_comm, Nat.mul_comm 3 (3 ^ n), ← Nat.pow_succ]
    }

/-- The growth bound scaled by the fixed power `2^b`. -/
theorem TwoThreeScaled (b r : ℕ) :
    2 ^ (b + r) * (r + 2) ≤ 2 ^ (b + 1) * 3 ^ r := by
  calc
    2 ^ (b + r) * (r + 2) = 2 ^ b * (2 ^ r * (r + 2)) := by
      rw [Nat.pow_add, Nat.mul_assoc]
    _ ≤ 2 ^ b * (2 * 3 ^ r) :=
      Nat.mul_le_mul_left (2 ^ b) (TwoThreeGrowth r)
    _ = 2 ^ (b + 1) * 3 ^ r := by
      rw [← Nat.mul_assoc, ← Nat.pow_succ]

/-- The energy is strictly below `2^{b+1} / (r + 2)`. -/
theorem SharpEnergyLtGrowth (b r : ℕ) :
    SharpEnergy b r < (2 ^ (b + 1) : ℚ) / ((r : ℚ) + 2) := by
  rw [SharpEnergyClosedForm, SharpHeight]
  have hQ : (0 : ℚ) < (2 ^ (b + r) : ℚ) := by
    exact_mod_cast Nat.two_pow_pos (b + r)
  have hp : (0 : ℚ) < (3 ^ r : ℚ) := by
    exact_mod_cast (Nat.pow_pos_iff.mpr (Or.inl (by decide : 0 < 3)))
  have ht : (0 : ℚ) < (r : ℚ) + 2 := by
    have hr : 0 < r + 2 := by omega
    exact_mod_cast hr
  have hsum : (0 : ℚ) < (2 ^ (b + r) : ℚ) + (3 ^ r : ℚ) := by
    linarith
  have hstep : (2 ^ (b + r) : ℚ) /
        ((2 ^ (b + r) : ℚ) + (3 ^ r : ℚ)) <
      (2 ^ (b + r) : ℚ) / (3 ^ r : ℚ) := by
    rw [div_lt_div_iff₀ hsum hp]
    exact mul_lt_mul_of_pos_left (by linarith : (3 ^ r : ℚ) <
      (2 ^ (b + r) : ℚ) + (3 ^ r : ℚ)) hQ
  have htail : (2 ^ (b + r) : ℚ) / (3 ^ r : ℚ) ≤
      (2 ^ (b + 1) : ℚ) / ((r : ℚ) + 2) := by
    rw [div_le_div_iff₀ hp ht]
    exact_mod_cast TwoThreeScaled b r
  exact lt_of_lt_of_le hstep htail

/-- Strict two-sided convergence of a rational sequence. -/
def TendsTo (u : ℕ → ℚ) (L : ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    L - ε < u n ∧ u n < L + ε

/-- For each fixed `b`, the energy tends to zero as `r` grows. -/
theorem SharpEnergyFixedBaseVanishes (b : ℕ) :
    TendsTo (fun r : ℕ => SharpEnergy b r) 0 := by
  intro ε hε
  have hquot : (0 : ℚ) < (2 ^ (b + 1) : ℚ) / ε :=
    div_pos (by exact_mod_cast Nat.two_pow_pos (b + 1)) hε
  match exists_nat_gt ((2 ^ (b + 1) : ℚ) / ε) with
  | ⟨N, hN⟩ =>
      refine ⟨N, ?_⟩
      intro n hn
      have hgrow : SharpEnergy b n <
          (2 ^ (b + 1) : ℚ) / ((n : ℚ) + 2) :=
        SharpEnergyLtGrowth b n
      have hncast : (N : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
      have hbig : (2 ^ (b + 1) : ℚ) / ε < (n : ℚ) :=
        lt_of_lt_of_le hN hncast
      have hnpos : (0 : ℚ) < (n : ℚ) := by
        have hNpos : (0 : ℚ) < (N : ℚ) := lt_trans hquot hN
        have hNnat : 0 < N := by exact_mod_cast hNpos
        exact_mod_cast Nat.lt_of_lt_of_le hNnat hn
      have hden : (0 : ℚ) < (n : ℚ) + 2 := by linarith
      have hB : (0 : ℚ) < (2 ^ (b + 1) : ℚ) := by
        exact_mod_cast Nat.two_pow_pos (b + 1)
      have hcomp : (2 ^ (b + 1) : ℚ) / ((n : ℚ) + 2) <
          (2 ^ (b + 1) : ℚ) / (n : ℚ) := by
        rw [div_lt_div_iff₀ hden hnpos]
        exact mul_lt_mul_of_pos_left
          (by linarith : (n : ℚ) < (n : ℚ) + 2) hB
      have hEps : (2 ^ (b + 1) : ℚ) / (n : ℚ) < ε := by
        have hmul : (2 ^ (b + 1) : ℚ) < (n : ℚ) * ε :=
          (div_lt_iff₀ hε).mp hbig
        rw [div_lt_iff₀ hnpos, mul_comm]
        exact hmul
      constructor
      · linarith [SharpEnergyPos b n]
      · have htop := lt_trans hgrow (lt_trans hcomp hEps)
        linarith

/-- A fixed base does not send the energy to one half. -/
theorem SharpEnergyFixedBaseNotHalf (b : ℕ) :
    ¬ TendsTo (fun r : ℕ => SharpEnergy b r) (1 / 2) := by
  intro hhalf
  have hzero : TendsTo (fun r : ℕ => SharpEnergy b r) 0 :=
    SharpEnergyFixedBaseVanishes b
  have hε : (0 : ℚ) < 1 / 4 := by norm_num
  match hzero (1 / 4) hε with
  | ⟨N, hN⟩ =>
      match hhalf (1 / 4) hε with
      | ⟨M, hM⟩ =>
          let n : ℕ := max N M
          have hz := hN n (Nat.le_max_left _ _)
          have hh := hM n (Nat.le_max_right _ _)
          linarith

/-- Distance from the energy to one half, written through the ratio. -/
theorem SharpEnergySubHalf (b r : ℕ) :
    SharpEnergy b r - 1 / 2 =
      (1 - SharpRatio b r) / (2 * (1 + SharpRatio b r)) := by
  unfold SharpEnergy
  have hden : 1 + SharpRatio b r ≠ 0 := SharpDenomNe b r
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  rw [div_sub_div _ _ hden htwo]
  have hnum : (1 : ℚ) * 2 - (1 + SharpRatio b r) * 1 =
      1 - SharpRatio b r := by ring
  have hdenm : (1 + SharpRatio b r) * 2 =
      2 * (1 + SharpRatio b r) := by ring
  rw [hnum, hdenm]

/-- A ratio below one and tending to one forces the energy down to one half. -/
theorem SharpHalfOfRatio (bseq rseq : ℕ → ℕ)
    (hlt : ∀ n, SharpRatio (bseq n) (rseq n) < 1)
    (hlim : TendsTo (fun n => SharpRatio (bseq n) (rseq n)) 1) :
    (∀ n, 1 / 2 < SharpEnergy (bseq n) (rseq n)) ∧
      TendsTo (fun n => SharpEnergy (bseq n) (rseq n)) (1 / 2) := by
  refine ⟨?_, ?_⟩
  · intro n
    have hpow : 3 ^ rseq n < 2 ^ SharpHeight (bseq n) (rseq n) :=
      (SharpRatioLtOne (bseq n) (rseq n)).mp (hlt n)
    exact (SharpEnergyGtHalf (bseq n) (rseq n)).mpr hpow
  · intro ε hε
    let η : ℚ := ε / (1 + ε)
    have hηpos : 0 < η :=
      div_pos hε (by linarith : (0 : ℚ) < 1 + ε)
    match hlim η hηpos with
    | ⟨N, hN⟩ =>
        refine ⟨N, ?_⟩
        intro n hn
        have hband := hN n hn
        have hρlt : SharpRatio (bseq n) (rseq n) < 1 := hlt n
        have hρgt : 1 - η < SharpRatio (bseq n) (rseq n) := hband.1
        have hEgt : 1 / 2 < SharpEnergy (bseq n) (rseq n) := by
          have hpow : 3 ^ rseq n < 2 ^ SharpHeight (bseq n) (rseq n) :=
            (SharpRatioLtOne (bseq n) (rseq n)).mp hρlt
          exact (SharpEnergyGtHalf (bseq n) (rseq n)).mpr hpow
        have hsub := SharpEnergySubHalf (bseq n) (rseq n)
        let ρ : ℚ := SharpRatio (bseq n) (rseq n)
        have hden : (0 : ℚ) < 2 * (1 + ρ) := by
          have hρpos : 0 < ρ := SharpRatioPos (bseq n) (rseq n)
          linarith
        have hnumlt : 1 - ρ < η := by linarith
        have hfrac : (1 - ρ) / (2 * (1 + ρ)) <
            η / (2 * (1 + ρ)) := by
          rw [div_lt_div_iff₀ hden hden]
          exact mul_lt_mul_of_pos_right hnumlt hden
        have hdenbig : (2 : ℚ) < 2 * (1 + ρ) := by
          have hρpos : 0 < ρ := SharpRatioPos (bseq n) (rseq n)
          linarith
        have hsmaller : η / (2 * (1 + ρ)) < η / 2 := by
          rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℚ) < 2)]
          exact mul_lt_mul_of_pos_left hdenbig hηpos
        have hηε : η / 2 < ε := by
          have hltε : η < ε := by
            rw [show η = ε / (1 + ε) from rfl]
            rw [div_lt_iff₀ (by linarith : (0 : ℚ) < 1 + ε)]
            have hone : (1 : ℚ) < 1 + ε := by linarith
            have hmul := mul_lt_mul_of_pos_left hone hε
            simpa [mul_one] using hmul
          rw [div_lt_iff₀ (by norm_num : (0 : ℚ) < 2)]
          linarith
        have hdiff : SharpEnergy (bseq n) (rseq n) - 1 / 2 < ε := by
          rw [hsub]
          exact lt_trans hfrac (lt_trans hsmaller hηε)
        constructor
        · linarith
        · linarith

/-- Energy above one half and tending to one half forces the ratio up to one. -/
theorem SharpRatioOfHalf (bseq rseq : ℕ → ℕ)
    (hgt : ∀ n, 1 / 2 < SharpEnergy (bseq n) (rseq n))
    (hlim : TendsTo (fun n => SharpEnergy (bseq n) (rseq n)) (1 / 2)) :
    (∀ n, SharpRatio (bseq n) (rseq n) < 1) ∧
      TendsTo (fun n => SharpRatio (bseq n) (rseq n)) 1 := by
  refine ⟨?_, ?_⟩
  · intro n
    have hpow : 3 ^ rseq n < 2 ^ SharpHeight (bseq n) (rseq n) :=
      (SharpEnergyGtHalf (bseq n) (rseq n)).mp (hgt n)
    exact (SharpRatioLtOne (bseq n) (rseq n)).mpr hpow
  · intro ε hε
    have hδ : (0 : ℚ) < ε / 4 := div_pos hε (by norm_num)
    match hlim (ε / 4) hδ with
    | ⟨N, hN⟩ =>
        refine ⟨N, ?_⟩
        intro n hn
        have hband := hN n hn
        have hEgt : 1 / 2 < SharpEnergy (bseq n) (rseq n) := hgt n
        have hgap : SharpEnergy (bseq n) (rseq n) - 1 / 2 < ε / 4 := by
          linarith
        let ρ : ℚ := SharpRatio (bseq n) (rseq n)
        have hsub := SharpEnergySubHalf (bseq n) (rseq n)
        have hdenpos : (0 : ℚ) < 2 * (1 + ρ) := by
          have hρpos : 0 < ρ := SharpRatioPos (bseq n) (rseq n)
          linarith
        have hden : 2 * (1 + ρ) ≠ 0 := ne_of_gt hdenpos
        have hmul : (SharpEnergy (bseq n) (rseq n) - 1 / 2) *
            (2 * (1 + ρ)) = 1 - ρ := by
          rw [hsub, div_mul_cancel₀ _ hden]
        have hident : 1 - ρ =
            2 * (1 + ρ) * (SharpEnergy (bseq n) (rseq n) - 1 / 2) := by
          linarith
        have hρlt : ρ < 1 := by
          have hpow : 3 ^ rseq n < 2 ^ SharpHeight (bseq n) (rseq n) :=
            (SharpEnergyGtHalf (bseq n) (rseq n)).mp hEgt
          exact (SharpRatioLtOne (bseq n) (rseq n)).mpr hpow
        have hcoef : 2 * (1 + ρ) < 4 := by linarith
        have hposgap : 0 < SharpEnergy (bseq n) (rseq n) - 1 / 2 := by
          linarith
        have hprod : 2 * (1 + ρ) *
            (SharpEnergy (bseq n) (rseq n) - 1 / 2) <
            4 * (SharpEnergy (bseq n) (rseq n) - 1 / 2) :=
          mul_lt_mul_of_pos_right hcoef hposgap
        have hfour : 4 * (SharpEnergy (bseq n) (rseq n) - 1 / 2) <
            4 * (ε / 4) :=
          mul_lt_mul_of_pos_left hgap (by norm_num : (0 : ℚ) < 4)
        have hcancel : 4 * (ε / 4) = ε :=
          mul_div_cancel₀ ε (by norm_num : (4 : ℚ) ≠ 0)
        have hsmall : 1 - ρ < ε := by
          rw [hident]
          have hfour' : 4 * (SharpEnergy (bseq n) (rseq n) - 1 / 2) < ε := by
            rw [← hcancel]
            exact hfour
          exact lt_trans hprod hfour'
        constructor
        · linarith
        · linarith

/-- Above one half and convergence to one half are the ratio criterion. -/
theorem SharpSequenceHalfIff (bseq rseq : ℕ → ℕ) :
    ((∀ n, SharpRatio (bseq n) (rseq n) < 1) ∧
        TendsTo (fun n => SharpRatio (bseq n) (rseq n)) 1) ↔
      ((∀ n, 1 / 2 < SharpEnergy (bseq n) (rseq n)) ∧
        TendsTo (fun n => SharpEnergy (bseq n) (rseq n)) (1 / 2)) := by
  constructor
  · intro h
    exact SharpHalfOfRatio bseq rseq h.1 h.2
  · intro h
    exact SharpRatioOfHalf bseq rseq h.1 h.2

/-- The block word, its carry energy, the gap above one half, and the limits. -/
theorem SharpCarryEnergy :
    (∀ b r : ℕ, 1 ≤ b → 1 ≤ r →
      (SharpFirst b r).length = SharpHeight b r ∧
      (SharpSecond b r).length = SharpHeight b r ∧
      (SharpWord b r).length = 2 * SharpHeight b r ∧
      OddCount (SharpFirst b r) = r ∧
      OddCount (SharpSecond b r) = r ∧
      OddCount (SharpWord b r) = 2 * r ∧
      (∀ i : ℕ, i < SharpHeight b r →
        (i < b - 1 ∨ b < i) →
          (SharpFirst b r).getD i false =
            (SharpSecond b r).getD i false) ∧
      (SharpFirst b r).getD (b - 1) false = false ∧
      (SharpSecond b r).getD (b - 1) false = true ∧
      (SharpFirst b r).getD b false = true ∧
      (SharpSecond b r).getD b false = false ∧
      (b - 1) + 1 = b ∧
      (∀ E : ℚ, IsSharpEnergy b r E ↔ E = SharpEnergy b r) ∧
      SharpEnergy b r =
        (2 ^ SharpHeight b r : ℚ) /
          ((2 ^ SharpHeight b r : ℚ) + (3 ^ r : ℚ)) ∧
      (1 / 2 < SharpEnergy b r ↔ 3 ^ r < 2 ^ SharpHeight b r) ∧
      SharpEnergy b r ≠ 1 / 2) ∧
    (∀ b : ℕ, 1 ≤ b →
      TendsTo (fun r : ℕ => SharpEnergy b r) 0 ∧
      ¬ TendsTo (fun r : ℕ => SharpEnergy b r) (1 / 2)) ∧
    (∀ bseq rseq : ℕ → ℕ,
      ((∀ n : ℕ, SharpRatio (bseq n) (rseq n) < 1) ∧
          TendsTo (fun n : ℕ => SharpRatio (bseq n) (rseq n)) 1) ↔
        ((∀ n : ℕ, 1 / 2 < SharpEnergy (bseq n) (rseq n)) ∧
          TendsTo (fun n : ℕ => SharpEnergy (bseq n) (rseq n))
            (1 / 2))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b r hb hr
    have hdiff := SharpHalvesDiffer b r hb hr
    exact ⟨SharpFirstLength b r, SharpSecondLength b r hb hr,
      SharpWordLength b r hb hr, SharpFirstOddCount b r,
      SharpSecondOddCount b r hr, SharpWordOddCount b r hr,
      fun i hi hside =>
        SharpHalvesAgree b r i hb hr (by
          unfold SharpHeight at hi
          exact hi) hside,
      hdiff.1, hdiff.2.1, hdiff.2.2.1, hdiff.2.2.2.1, hdiff.2.2.2.2,
      fun E => IsSharpEnergyIff b r E, SharpEnergyClosedForm b r,
      SharpEnergyGtHalf b r, SharpEnergyNeHalf b r hb⟩
  · intro b _hb
    exact ⟨SharpEnergyFixedBaseVanishes b, SharpEnergyFixedBaseNotHalf b⟩
  · intro bseq rseq
    exact SharpSequenceHalfIff bseq rseq

/-- The parameters `b = 2` and `r = 3` give energy `32 / 59`. -/
theorem SharpEnergyAtTwoThree : SharpEnergy 2 3 = 32 / 59 := by
  rw [SharpEnergyClosedForm, SharpHeight]
  norm_num

end GeneralizedCollatz
