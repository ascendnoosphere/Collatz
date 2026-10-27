-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation

/-!
# Sign of the mirror quotient

The mirror step divides `3 * n - 1` by a positive power of two. When that
division is exact, the quotient has the sign of `n` for every nonzero
integer `n`. An integral schedule therefore stays negative from a negative
seed and stays positive from a positive seed.

The exponent `1` fixes `1`. The exponents `1` and `2` exchange `5` and `7`.
Those are positive cycles of this quotient. Nothing here says that every
positive integer reaches `1`, and the numerator `3 * n + 1` is not the one
under consideration. A schedule that fails exact division is not given a
sign: the denominator `2^3` does not divide the numerator at the seed `1`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Positive power of two in the mirror denominator. -/
def MirrorDenom (v : ℕ) : ℤ := ((2 : ℕ) ^ v : ℤ)

/-- Integer quotient of `3 * n - 1` by `2 ^ v`. Without divisibility this truncates. -/
def MirrorQuotient (n : ℤ) (v : ℕ) : ℤ :=
  (3 * n - 1) / MirrorDenom v

/-- Schedule of mirror quotients, reading exponents from the head of the list. -/
def MirrorIterate (n : ℤ) : List ℕ → ℤ
  | [] => n
  | v :: vs => MirrorIterate (MirrorQuotient n v) vs

/-- Each remaining head divides the numerator at the state where it is applied. -/
def MirrorPrefixesIntegral (n : ℤ) : List ℕ → Prop
  | [] => True
  | v :: vs =>
      MirrorDenom v ∣ (3 * n - 1) ∧
        MirrorPrefixesIntegral (MirrorQuotient n v) vs

/-- Every power of two is a positive integer, so the denominator is never zero. -/
theorem MirrorDenomPositive (v : ℕ) : 0 < MirrorDenom v := by
  unfold MirrorDenom
  exact Int.natCast_pos.mpr (Nat.two_pow_pos v)

/-- A positive integer is at least `1`, so its mirror numerator is at least `2`. -/
theorem MirrorNumeratorPositive (n : ℤ) (hn : 0 < n) : 2 ≤ 3 * n - 1 := by
  omega

/-- A negative integer is at most `-1`, so its mirror numerator is at most `-4`. -/
theorem MirrorNumeratorNegative (n : ℤ) (hn : n < 0) : 3 * n - 1 ≤ -4 := by
  omega

/-- Exact division reconstructs the numerator as denominator times quotient. -/
theorem MirrorQuotientMul (n : ℤ) (v : ℕ)
    (hdiv : MirrorDenom v ∣ (3 * n - 1)) :
    MirrorDenom v * MirrorQuotient n v = 3 * n - 1 := by
  unfold MirrorQuotient
  exact Int.mul_ediv_cancel_of_dvd hdiv

/-- A positive seed has a positive exact mirror quotient. -/
theorem MirrorQuotientPositive (n : ℤ) (v : ℕ) (hn : 0 < n)
    (hdiv : MirrorDenom v ∣ (3 * n - 1)) :
    0 < MirrorQuotient n v := by
  have hden : 0 < MirrorDenom v := MirrorDenomPositive v
  have hnum : 0 < 3 * n - 1 := by
    have h2 : 2 ≤ 3 * n - 1 := MirrorNumeratorPositive n hn
    omega
  have hprod : 0 < MirrorDenom v * MirrorQuotient n v := by
    rw [MirrorQuotientMul n v hdiv]
    exact hnum
  exact Int.pos_of_mul_pos_right hprod hden

/-- A negative seed has a negative exact mirror quotient. -/
theorem MirrorQuotientNegative (n : ℤ) (v : ℕ) (hn : n < 0)
    (hdiv : MirrorDenom v ∣ (3 * n - 1)) :
    MirrorQuotient n v < 0 := by
  have hden : 0 < MirrorDenom v := MirrorDenomPositive v
  have hnum : 3 * n - 1 < 0 := by
    have h4 : 3 * n - 1 ≤ -4 := MirrorNumeratorNegative n hn
    omega
  have hprod : MirrorDenom v * MirrorQuotient n v < 0 := by
    rw [MirrorQuotientMul n v hdiv]
    exact hnum
  exact Int.neg_of_mul_neg_right hprod hden

/-- Integrality of a concatenation splits into the head block and the tail block. -/
theorem MirrorPrefixesIntegralSplit (n : ℤ) (us ts : List ℕ)
    (h : MirrorPrefixesIntegral n (us ++ ts)) :
    MirrorPrefixesIntegral n us ∧
      MirrorPrefixesIntegral (MirrorIterate n us) ts := by
  induction us generalizing n with
  | nil => {
      -- The empty head contributes no division, so the tail starts at `n`.
      refine ⟨?_, ?_⟩
      · unfold MirrorPrefixesIntegral
        trivial
      · have htail : MirrorPrefixesIntegral n ts := by
          simpa [List.nil_append] using h
        unfold MirrorIterate
        exact htail
    }
  | cons v us ih => {
      -- The head exponent is exact, and the remainder splits by induction.
      have hform : MirrorPrefixesIntegral n (v :: (us ++ ts)) := by
        simpa [List.cons_append] using h
      unfold MirrorPrefixesIntegral at hform
      have hdiv : MirrorDenom v ∣ (3 * n - 1) := hform.1
      have htail :
          MirrorPrefixesIntegral (MirrorQuotient n v) (us ++ ts) :=
        hform.2
      obtain ⟨hus, hrest⟩ := ih (MirrorQuotient n v) htail
      refine ⟨?_, ?_⟩
      · unfold MirrorPrefixesIntegral
        exact ⟨hdiv, hus⟩
      · unfold MirrorIterate
        exact hrest
    }

/-- The final state of an integral schedule keeps a negative seed. -/
theorem MirrorIterateNegative (n : ℤ) (vs : List ℕ) (hn : n < 0)
    (hprefix : MirrorPrefixesIntegral n vs) : MirrorIterate n vs < 0 := by
  induction vs generalizing n with
  | nil => {
      unfold MirrorIterate
      exact hn
    }
  | cons v vs ih => {
      -- One exact step produces a negative integer, and the tail is integral.
      unfold MirrorPrefixesIntegral at hprefix
      have hdiv : MirrorDenom v ∣ (3 * n - 1) := hprefix.1
      have htail : MirrorPrefixesIntegral (MirrorQuotient n v) vs :=
        hprefix.2
      have hstep : MirrorQuotient n v < 0 :=
        MirrorQuotientNegative n v hn hdiv
      have hrec : MirrorIterate (MirrorQuotient n v) vs < 0 :=
        ih (MirrorQuotient n v) hstep htail
      unfold MirrorIterate
      exact hrec
    }

/-- Every prefix state of an integral negative schedule is negative. -/
theorem MirrorLaterNegative (n : ℤ) (vs us ts : List ℕ) (hn : n < 0)
    (hprefix : MirrorPrefixesIntegral n vs) (hcut : us ++ ts = vs) :
    MirrorIterate n us < 0 := by
  rw [← hcut] at hprefix
  exact MirrorIterateNegative n us hn
    (MirrorPrefixesIntegralSplit n us ts hprefix).1

/-- The final state of an integral schedule keeps a positive seed. -/
theorem MirrorIteratePositive (n : ℤ) (vs : List ℕ) (hn : 0 < n)
    (hprefix : MirrorPrefixesIntegral n vs) : 0 < MirrorIterate n vs := by
  induction vs generalizing n with
  | nil => {
      unfold MirrorIterate
      exact hn
    }
  | cons v vs ih => {
      -- One exact step produces a positive integer, and the tail is integral.
      unfold MirrorPrefixesIntegral at hprefix
      have hdiv : MirrorDenom v ∣ (3 * n - 1) := hprefix.1
      have htail : MirrorPrefixesIntegral (MirrorQuotient n v) vs :=
        hprefix.2
      have hstep : 0 < MirrorQuotient n v :=
        MirrorQuotientPositive n v hn hdiv
      have hrec : 0 < MirrorIterate (MirrorQuotient n v) vs :=
        ih (MirrorQuotient n v) hstep htail
      unfold MirrorIterate
      exact hrec
    }

/-- Every prefix state of an integral positive schedule is positive. -/
theorem MirrorLaterPositive (n : ℤ) (vs us ts : List ℕ) (hn : 0 < n)
    (hprefix : MirrorPrefixesIntegral n vs) (hcut : us ++ ts = vs) :
    0 < MirrorIterate n us := by
  rw [← hcut] at hprefix
  exact MirrorIteratePositive n us hn
    (MirrorPrefixesIntegralSplit n us ts hprefix).1

/-- The exponent `1` fixes the positive integer `1`. -/
theorem MirrorFixedPointOne : MirrorQuotient 1 1 = 1 := by
  unfold MirrorQuotient
  have hden : MirrorDenom 1 = 2 := by
    unfold MirrorDenom
    decide
  rw [hden]
  have hnum : (3 : ℤ) * 1 - 1 = 2 := by omega
  rw [hnum]
  exact Int.ediv_self (by omega : (2 : ℤ) ≠ 0)

/-- The exponents `1` and `2` exchange the positive integers `5` and `7`. -/
theorem MirrorCycleFiveSeven :
    MirrorQuotient 5 1 = 7 ∧ MirrorQuotient 7 2 = 5 := by
  refine ⟨?_, ?_⟩
  · unfold MirrorQuotient
    have hden : MirrorDenom 1 = 2 := by
      unfold MirrorDenom
      decide
    rw [hden]
    have hnum : (3 : ℤ) * 5 - 1 = 14 := by omega
    rw [hnum]
    have hfac : (14 : ℤ) = 2 * 7 := by omega
    exact Int.ediv_eq_of_eq_mul_right (by omega : (2 : ℤ) ≠ 0) hfac
  · unfold MirrorQuotient
    have hden : MirrorDenom 2 = 4 := by
      unfold MirrorDenom
      decide
    rw [hden]
    have hnum : (3 : ℤ) * 7 - 1 = 20 := by omega
    rw [hnum]
    have hfac : (20 : ℤ) = 4 * 5 := by omega
    exact Int.ediv_eq_of_eq_mul_right (by omega : (4 : ℤ) ≠ 0) hfac

/-- The exponent `3` is not an exact step at the seed `1`. -/
theorem MirrorOneNotDivisibleByEight :
    ¬ MirrorDenom 3 ∣ (3 * (1 : ℤ) - 1) := by
  have hnum : (3 : ℤ) * 1 - 1 = 2 := by omega
  rw [hnum]
  unfold MirrorDenom
  decide

end GeneralizedCollatz
