-- SPDX-License-Identifier: CC-BY-4.0
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

set_option autoImplicit false

namespace GeneralizedCollatz.ResidueLeakage

open scoped BigOperators

/-- Bad binary words have more than five affine events per eight division blocks. -/
def BadBinaryWords (t : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (8 * t + 1), if 5 * t < a then (8 * t).choose a else 0

/-- Replacing an allowed zero digit by a one digit increases the tilted word weight. -/
theorem TiltedWeightLower (t a : ℕ) (ha : a ≤ 8 * t) (hl : 5 * t ≤ a) :
    5 ^ (5 * t) * 3 ^ (3 * t) ≤ 5 ^ a * 3 ^ (8 * t - a) := by
  let k := a - 5 * t
  have hka : a = 5 * t + k := by dsimp [k]; omega
  have hkb : 3 * t = k + (8 * t - a) := by dsimp [k]; omega
  calc
    5 ^ (5 * t) * 3 ^ (3 * t) =
        5 ^ (5 * t) * (3 ^ k * 3 ^ (8 * t - a)) := by rw [hkb, pow_add]
    _ ≤ 5 ^ (5 * t) * (5 ^ k * 3 ^ (8 * t - a)) := by
      gcongr
      norm_num
    _ = 5 ^ a * 3 ^ (8 * t - a) := by rw [hka, pow_add]; ring

/-- Summing tilted weights gives an exact integer upper bound for the bad-word count. -/
theorem BadBinaryWeightedBound (t : ℕ) :
    BadBinaryWords t * (5 ^ (5 * t) * 3 ^ (3 * t)) ≤ 8 ^ (8 * t) := by
  rw [BadBinaryWords, Finset.sum_mul]
  calc
    (∑ a ∈ Finset.range (8 * t + 1),
        (if 5 * t < a then (8 * t).choose a else 0) *
          (5 ^ (5 * t) * 3 ^ (3 * t))) ≤
        ∑ a ∈ Finset.range (8 * t + 1),
          5 ^ a * 3 ^ (8 * t - a) * (8 * t).choose a := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : 5 * t < a
      · rw [if_pos h]
        have hl := TiltedWeightLower t a (by simpa using ha) (by omega)
        nlinarith [Nat.mul_le_mul_left ((8 * t).choose a) hl]
      · simp only [if_neg h, zero_mul]
        exact Nat.zero_le _
    _ = 8 ^ (8 * t) := by simpa using (add_pow (5 : ℕ) 3 (8 * t)).symm

/-- The binary boundary has a strictly contracting bad-word proportion with explicit constants. -/
theorem BadBinaryDensityBound (t : ℕ) :
    (BadBinaryWords t : ℝ) / (2 : ℝ) ^ (8 * t) ≤ (65536 / 84375 : ℝ) ^ t := by
  have hw : (BadBinaryWords t : ℝ) * ((5 : ℝ) ^ (5 * t) * 3 ^ (3 * t)) ≤
      (8 : ℝ) ^ (8 * t) := by exact_mod_cast BadBinaryWeightedBound t
  have hW : 0 < (5 : ℝ) ^ (5 * t) * 3 ^ (3 * t) := by positivity
  have htwo : 0 < (2 : ℝ) ^ (8 * t) := by positivity
  have hb := (le_div_iff₀ hW).mpr hw
  have hdiv := div_le_div_of_nonneg_right hb htwo.le
  have he : ((8 : ℝ) ^ (8 * t) / ((5 : ℝ) ^ (5 * t) * 3 ^ (3 * t))) /
      (2 : ℝ) ^ (8 * t) = (65536 / 84375 : ℝ) ^ t := by
    rw [div_div]
    simp only [pow_mul, ← mul_pow, ← div_pow]
    norm_num
  simpa only [he] using hdiv

/-- Good binary words have a genuinely subunit multiplier at every positive block group. -/
theorem ClassicalGoodMultiplier (t a : ℕ) (ha : a ≤ 5 * t) :
    (3 : ℝ) ^ a / (2 : ℝ) ^ (8 * t) ≤ (243 / 256 : ℝ) ^ t := by
  have hpow : (3 : ℝ) ^ a ≤ 3 ^ (5 * t) := pow_le_pow_right₀ (by norm_num) ha
  have hden : 0 ≤ (2 : ℝ) ^ (8 * t) := by positivity
  have hdiv := div_le_div_of_nonneg_right hpow hden
  have he : (3 : ℝ) ^ (5 * t) / (2 : ℝ) ^ (8 * t) = (243 / 256 : ℝ) ^ t := by
    simp only [pow_mul, ← div_pow]
    norm_num
  simpa only [he] using hdiv

/-- Both constants needed in the closing classical estimate are strictly below one. -/
theorem ClassicalClosingConstants :
    (0 : ℝ) < 243 / 256 ∧ (243 / 256 : ℝ) < 1 ∧
      (0 : ℝ) < 65536 / 84375 ∧ (65536 / 84375 : ℝ) < 1 := by
  norm_num

/-- From divisor three onward, the least full-cycle multiplier cannot have negative drift. -/
theorem ThreeSquareGrowth (D : ℕ) (hD : 3 ≤ D) :
    D ^ 2 ≤ 3 ^ (D - 1) := by
  induction D, hD using Nat.le_induction with
  | base => { norm_num }
  | succ D hD ih => {
    have hs : (D + 1) ^ 2 ≤ 3 * D ^ 2 := by nlinarith
    have he : D + 1 - 1 = (D - 1) + 1 := by omega
    calc
      (D + 1) ^ 2 ≤ 3 * D ^ 2 := hs
      _ ≤ 3 * 3 ^ (D - 1) := Nat.mul_le_mul_left 3 ih
      _ = 3 ^ (D + 1 - 1) := by rw [he, pow_succ]; ring
  }

/-- With multiplier at least three, strict mean contraction forces the dyadic multiplier three. -/
theorem NegativeGainParameters (q D : ℕ) (hq : 3 ≤ q) (hD : 2 ≤ D)
    (hgain : q ^ (D - 1) < D ^ 2) : D = 2 ∧ q = 3 := by
  have hsmall : D < 3 := by
    by_contra h
    have hthree := ThreeSquareGrowth D (by omega)
    have hpower : 3 ^ (D - 1) ≤ q ^ (D - 1) := Nat.pow_le_pow_left hq _
    omega
  have htwo : D = 2 := by omega
  subst D
  norm_num at hgain
  exact ⟨rfl, by omega⟩

end GeneralizedCollatz.ResidueLeakage
