-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Sqrt
import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The two-affine positivity test, cleared of denominators.

For an odd exponent `K ≥ 3` and an odd natural number `q`, the rational
comparison `2 ^ K ≤ (q + 1 / 3) ^ 2` is the integer comparison
`9 * 2 ^ K ≤ (3 * q + 1) ^ 2`. The two sides are never equal. At each such
exponent there is one odd natural candidate whose square lies strictly below
the power of two and whose translate by two lies strictly above it.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The integer comparison obtained by clearing the denominator three. -/
def TwoAffinePositivity (q K : ℕ) : Prop :=
  9 * 2 ^ K ≤ (3 * q + 1) ^ 2

/-- The greatest natural number whose square does not exceed `2 ^ K`. -/
def IntegerSqrtFloor (K : ℕ) : ℕ :=
  Nat.sqrt (2 ^ K)

/-- The odd natural number in the square bracket of `2 ^ K`, when it exists. -/
def UniqueOddCandidate (K : ℕ) : ℕ :=
  if Even (IntegerSqrtFloor K) then IntegerSqrtFloor K - 1
  else IntegerSqrtFloor K

/-- Expanding the cleared square gives the quadratic `9q² + 6q + 1`. -/
theorem TwoAffineExpanded (q : ℕ) :
    (3 * q + 1) ^ 2 = 9 * q ^ 2 + 6 * q + 1 := by
  ring

/-- A square of the form `(3q + 1)²` is congruent to one modulo three. -/
theorem SquareModThree (q : ℕ) : (3 * q + 1) ^ 2 % 3 = 1 := by
  have hpoly : (3 * q + 1) ^ 2 = 3 * (3 * q ^ 2 + 2 * q) + 1 := by
    ring
  rw [hpoly, Nat.mul_add_mod_self_left]

/-- The cleared power of two and the cleared affine square are distinct. -/
theorem TwoAffineNotEqual (q K : ℕ) : 9 * 2 ^ K ≠ (3 * q + 1) ^ 2 := by
  intro heq
  have hL : 9 * 2 ^ K % 3 = 0 := by
    have hfactor : 9 * 2 ^ K = 3 * (3 * 2 ^ K) := by
      ring
    rw [hfactor, Nat.mul_mod_right]
  have hR : (3 * q + 1) ^ 2 % 3 = 1 := SquareModThree q
  have hmod : 9 * 2 ^ K % 3 = (3 * q + 1) ^ 2 % 3 := by
    rw [heq]
  rw [hL, hR] at hmod
  contradiction

/-- The integer comparison is strict whenever it holds. -/
theorem TwoAffinePositivityStrict (q K : ℕ) :
    TwoAffinePositivity q K ↔ 9 * 2 ^ K < (3 * q + 1) ^ 2 := by
  unfold TwoAffinePositivity
  constructor
  · intro hle
    exact lt_of_le_of_ne hle (TwoAffineNotEqual q K)
  · intro hlt
    exact Nat.le_of_lt hlt

/-- Clearing the positive denominator nine preserves the rational comparison. -/
theorem TwoAffinePositivityIff (q K : ℕ) :
    ((2 : ℚ) ^ K ≤ ((q : ℚ) + (1 : ℚ) / 3) ^ 2) ↔
      TwoAffinePositivity q K := by
  unfold TwoAffinePositivity
  have h3 : (3 : ℚ) ≠ 0 := by
    norm_num
  have h9 : (0 : ℚ) < 9 := by
    norm_num
  have h9ne : (9 : ℚ) ≠ 0 := by
    norm_num
  have hprod : (3 : ℚ) * (q : ℚ) = ((3 * q : ℕ) : ℚ) := by
    norm_cast
  have hsum : (q : ℚ) + (1 : ℚ) / 3 = ((3 * q + 1 : ℕ) : ℚ) / 3 := by
    calc
      (q : ℚ) + (1 : ℚ) / 3
          = ((3 : ℚ) * (q : ℚ)) / 3 + (1 : ℚ) / 3 := by
            rw [mul_div_cancel_left₀ (q : ℚ) h3]
      _ = ((3 : ℚ) * (q : ℚ) + 1) / 3 := by
            rw [← add_div]
      _ = (((3 * q : ℕ) : ℚ) + 1) / 3 := by
            rw [hprod]
      _ = ((3 * q + 1 : ℕ) : ℚ) / 3 := by
            norm_cast
  have hsq : ((q : ℚ) + (1 : ℚ) / 3) ^ 2 =
      (((3 * q + 1) ^ 2 : ℕ) : ℚ) / 9 := by
    rw [hsum, div_pow]
    have hnum : (((3 * q + 1 : ℕ) : ℚ)) ^ 2 =
        (((3 * q + 1) ^ 2 : ℕ) : ℚ) := by
      norm_cast
    have hden : (3 : ℚ) ^ 2 = 9 := by
      norm_num
    rw [hnum, hden]
  have hleft : (9 : ℚ) * (2 : ℚ) ^ K = ((9 * 2 ^ K : ℕ) : ℚ) := by
    have hpow : (2 : ℚ) ^ K = ((2 ^ K : ℕ) : ℚ) := by
      norm_cast
    rw [hpow]
    norm_cast
  have hclear : (9 : ℚ) * ((((3 * q + 1) ^ 2 : ℕ) : ℚ) / 9) =
      (((3 * q + 1) ^ 2 : ℕ) : ℚ) :=
    mul_div_cancel₀ _ h9ne
  rw [hsq, ← mul_le_mul_iff_of_pos_left h9, hclear, hleft]
  show ((9 * 2 ^ K : ℕ) : ℚ) ≤ (((3 * q + 1) ^ 2 : ℕ) : ℚ) ↔
    9 * 2 ^ K ≤ (3 * q + 1) ^ 2
  exact Nat.cast_le

/-- In the odd window, the rational test is the strict integer comparison. -/
theorem TwoAffineWindowComparison (q K : ℕ) (hK : Odd K) (hK3 : 3 ≤ K)
    (hq : Odd q) :
    ((2 : ℚ) ^ K ≤ ((q : ℚ) + (1 : ℚ) / 3) ^ 2) ↔
      TwoAffinePositivity q K := by
  have _window : Odd K ∧ 3 ≤ K ∧ Odd q := ⟨hK, hK3, hq⟩
  exact TwoAffinePositivityIff q K

/-- An odd power of two is not a square. -/
theorem OddPowTwoNotSquare (k : ℕ) :
    ¬∃ m : ℕ, m ^ 2 = 2 ^ (2 * k + 1) := by
  induction k with
  | zero => {
      intro hex
      obtain ⟨m, hm⟩ := hex
      have hm2 : m ^ 2 = 2 := by
        rw [show 2 * 0 + 1 = 1 by decide, pow_one] at hm
        exact hm
      cases m with
      | zero => {
          rw [pow_two, Nat.zero_mul] at hm2
          omega
        }
      | succ m => {
          cases m with
          | zero => {
              rw [pow_two, Nat.one_mul] at hm2
              omega
            }
          | succ m => {
              have htwo : 2 ≤ m + 2 := by
                omega
              have hpow : 2 ^ 2 ≤ (m + 2) ^ 2 :=
                Nat.pow_le_pow_left htwo 2
              have hsq4 : (2 : ℕ) ^ 2 = 4 := by
                decide
              have hfour : 4 ≤ (m + 2) ^ 2 := by
                rw [hsq4] at hpow
                exact hpow
              have hclosed : 4 ≤ 2 := by
                calc
                  (4 : ℕ) ≤ (m + 2) ^ 2 := hfour
                  _ = 2 := hm2
              have hnot : ¬(4 : ℕ) ≤ 2 := by
                decide
              exact hnot hclosed
            }
        }
    }
  | succ k ih => {
      intro hex
      obtain ⟨m, hm⟩ := hex
      have hexp : 2 * (k + 1) + 1 = 2 * k + 3 := by
        omega
      rw [hexp] at hm
      have hnotOdd : ¬Odd m := by
        intro hodd
        obtain ⟨t, ht⟩ := hodd
        have hmodL : (2 * t + 1) ^ 2 % 2 = 1 := by
          have hpoly : (2 * t + 1) ^ 2 = 2 * (2 * t * (t + 1)) + 1 := by
            ring
          rw [hpoly, Nat.mul_add_mod_self_left]
        have hmodR : 2 ^ (2 * k + 3) % 2 = 0 := by
          have hstep : 2 * k + 3 = (2 * k + 2) + 1 := by
            omega
          rw [hstep, pow_succ, Nat.mul_mod_left]
        rw [ht] at hm
        have hmodEq : (2 * t + 1) ^ 2 % 2 = 2 ^ (2 * k + 3) % 2 := by
          rw [hm]
        rw [hmodL, hmodR] at hmodEq
        contradiction
      have hEven : Even m := (Nat.not_odd_iff_even).mp hnotOdd
      obtain ⟨t, ht⟩ := hEven
      have htwo : m = 2 * t := by
        rw [ht]
        omega
      have hm2 : (2 * t) ^ 2 = 2 ^ (2 * k + 3) := by
        rw [← htwo]
        exact hm
      have hsq : (2 * t) ^ 2 = 4 * t ^ 2 := by
        ring
      have hpow : 2 ^ (2 * k + 3) = 4 * 2 ^ (2 * k + 1) := by
        have hstep : 2 * k + 3 = 2 + (2 * k + 1) := by
          omega
        have hsplit : 2 ^ (2 + (2 * k + 1)) = 2 ^ 2 * 2 ^ (2 * k + 1) :=
          pow_add 2 2 (2 * k + 1)
        have hfour : (2 : ℕ) ^ 2 = 4 := by
          decide
        rw [hstep, hsplit, hfour]
      rw [hsq, hpow] at hm2
      have ht2 : t ^ 2 = 2 ^ (2 * k + 1) :=
        Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) hm2
      exact ih ⟨t, ht2⟩
    }

/-- For an odd exponent at least three, the integer floor is at least two. -/
theorem IntegerSqrtFloorAtLeastTwo (K : ℕ) (hK3 : 3 ≤ K) :
    2 ≤ IntegerSqrtFloor K := by
  have hbase : (2 : ℕ) ^ 3 ≤ 2 ^ K :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hK3
  have hfour : (4 : ℕ) ≤ 2 ^ 3 := by
    decide
  have hpow : 2 ^ 2 ≤ 2 ^ K := by
    have hsq : (2 : ℕ) ^ 2 = 4 := by
      decide
    rw [hsq]
    exact Nat.le_trans hfour hbase
  have hsqrt : 2 ≤ Nat.sqrt (2 ^ K) := (Nat.le_sqrt').mpr hpow
  exact hsqrt

/-- The floor square lies strictly below an odd power of two. -/
theorem OddPowStrictSqrt (K : ℕ) (hK : Odd K) (_ : 3 ≤ K) :
    IntegerSqrtFloor K ^ 2 < 2 ^ K ∧
      2 ^ K < (IntegerSqrtFloor K + 1) ^ 2 := by
  have hlt : 2 ^ K < (IntegerSqrtFloor K + 1) ^ 2 :=
    Nat.lt_succ_sqrt' (2 ^ K)
  have hle : IntegerSqrtFloor K ^ 2 ≤ 2 ^ K :=
    Nat.sqrt_le' (2 ^ K)
  have hne : IntegerSqrtFloor K ^ 2 ≠ 2 ^ K := by
    intro heq
    obtain ⟨k, hk⟩ := hK
    have hpowEq : IntegerSqrtFloor K ^ 2 = 2 ^ (2 * k + 1) := by
      rw [← hk]
      exact heq
    exact OddPowTwoNotSquare k ⟨IntegerSqrtFloor K, hpowEq⟩
  exact ⟨lt_of_le_of_ne hle hne, hlt⟩

/-- An even floor contributes its odd predecessor. -/
theorem UniqueOddCandidateEven (K : ℕ) (hEven : Even (IntegerSqrtFloor K)) :
    UniqueOddCandidate K = IntegerSqrtFloor K - 1 := by
  unfold UniqueOddCandidate
  rw [if_pos hEven]

/-- An odd floor is already the odd candidate. -/
theorem UniqueOddCandidateOdd (K : ℕ) (hOdd : Odd (IntegerSqrtFloor K)) :
    UniqueOddCandidate K = IntegerSqrtFloor K := by
  unfold UniqueOddCandidate
  rw [if_neg ((Nat.not_even_iff_odd).mpr hOdd)]

/-- The odd predecessor of `m` leaves a positive gap below `9m²`. -/
theorem PredecessorSquareGap (m : ℕ) (hm : 1 ≤ m) :
    (3 * (m - 1) + 1) ^ 2 + 4 * (3 * (m - 1) + 2) = 9 * m ^ 2 := by
  set k := m - 1 with _hk
  have hm1 : m = k + 1 := by
    omega
  rw [hm1]
  ring

/-- If the floor is even, its odd predecessor fails the positivity test. -/
theorem EvenFloorPositivityFails (K : ℕ) (hK : Odd K) (hK3 : 3 ≤ K)
    (hEven : Even (IntegerSqrtFloor K)) :
    ¬TwoAffinePositivity (UniqueOddCandidate K) K := by
  let m := IntegerSqrtFloor K
  let q := m - 1
  have hm2 : 2 ≤ m := IntegerSqrtFloorAtLeastTwo K hK3
  have hm1 : 1 ≤ m := Nat.le_trans (by decide : (1 : ℕ) ≤ 2) hm2
  have hqdef : UniqueOddCandidate K = q :=
    UniqueOddCandidateEven K hEven
  have hstrict : m ^ 2 < 2 ^ K := (OddPowStrictSqrt K hK hK3).1
  have hsucc : m ^ 2 + 1 ≤ 2 ^ K := Nat.succ_le_of_lt hstrict
  have hmul : 9 * (m ^ 2 + 1) ≤ 9 * 2 ^ K :=
    Nat.mul_le_mul_left 9 hsucc
  have hsplit : 9 * m ^ 2 + 9 = 9 * (m ^ 2 + 1) := by
    ring
  have hgap : (3 * q + 1) ^ 2 + 4 * (3 * q + 2) = 9 * m ^ 2 :=
    PredecessorSquareGap m hm1
  have hsum : (3 * q + 1) ^ 2 + 4 * (3 * q + 2) + 9 = 9 * m ^ 2 + 9 := by
    omega
  have h17 : 17 ≤ 4 * (3 * q + 2) + 9 := by
    have hex : 4 * (3 * q + 2) = 12 * q + 8 := by
      ring
    have h8 : 8 ≤ 12 * q + 8 := Nat.le_add_left 8 (12 * q)
    have hterm : 8 ≤ 4 * (3 * q + 2) := by
      rw [hex]
      exact h8
    omega
  have hstep : (3 * q + 1) ^ 2 + 17 ≤
      (3 * q + 1) ^ 2 + (4 * (3 * q + 2) + 9) :=
    Nat.add_le_add_left h17 ((3 * q + 1) ^ 2)
  have hle : (3 * q + 1) ^ 2 + 17 ≤ 9 * 2 ^ K := by
    have hright : (3 * q + 1) ^ 2 + (4 * (3 * q + 2) + 9) ≤ 9 * 2 ^ K := by
      rw [← Nat.add_assoc, hsum, hsplit]
      exact hmul
    exact Nat.le_trans hstep hright
  unfold TwoAffinePositivity
  rw [hqdef]
  intro hpos
  have hcontra : 9 * 2 ^ K + 17 ≤ (3 * q + 1) ^ 2 + 17 :=
    Nat.add_le_add_right hpos 17
  have hclosed : 9 * 2 ^ K + 17 ≤ 9 * 2 ^ K :=
    Nat.le_trans hcontra hle
  omega

/-- The odd candidate lies in the open square bracket of width two. -/
theorem UniqueOddCandidateSpec (K : ℕ) (hK : Odd K) (hK3 : 3 ≤ K) :
    Odd (UniqueOddCandidate K) ∧
      1 ≤ UniqueOddCandidate K ∧
      UniqueOddCandidate K ^ 2 < 2 ^ K ∧
      2 ^ K < (UniqueOddCandidate K + 2) ^ 2 := by
  let m := IntegerSqrtFloor K
  have hstrict := OddPowStrictSqrt K hK hK3
  have hm2 : 2 ≤ m := IntegerSqrtFloorAtLeastTwo K hK3
  cases Nat.even_or_odd m with
  | inl hEven => {
      have hq : UniqueOddCandidate K = m - 1 :=
        UniqueOddCandidateEven K hEven
      have hone : 1 ≤ m := Nat.le_trans (by decide : (1 : ℕ) ≤ 2) hm2
      have hqpos : 1 ≤ m - 1 := (Nat.le_sub_iff_add_le hone).mpr hm2
      obtain ⟨t, ht⟩ := hEven
      have hodd : Odd (m - 1) := by
        have htwo : m = 2 * t := by
          rw [ht]
          omega
        have ht1 : 1 ≤ t := by
          omega
        refine ⟨t - 1, ?_⟩
        omega
      have hsqlt : (m - 1) ^ 2 < m ^ 2 := by
        have hexp : m ^ 2 = (m - 1) ^ 2 + 2 * (m - 1) + 1 := by
          set k := m - 1 with _hk
          have hm1 : m = k + 1 := by
            omega
          rw [hm1]
          ring
        omega
      have hlow : (m - 1) ^ 2 < 2 ^ K := lt_trans hsqlt hstrict.1
      have hup : 2 ^ K < ((m - 1) + 2) ^ 2 := by
        have hshift : (m - 1) + 2 = m + 1 := by
          omega
        rw [hshift]
        exact hstrict.2
      rw [hq]
      exact ⟨hodd, hqpos, hlow, hup⟩
    }
  | inr hOdd => {
      have hq : UniqueOddCandidate K = m :=
        UniqueOddCandidateOdd K hOdd
      have hup : 2 ^ K < (m + 2) ^ 2 := by
        have hmono : (m + 1) ^ 2 ≤ (m + 2) ^ 2 :=
          Nat.pow_le_pow_left (Nat.le_succ (m + 1)) 2
        exact lt_of_lt_of_le hstrict.2 hmono
      have hone : 1 ≤ m := by
        omega
      rw [hq]
      exact ⟨hOdd, hone, hstrict.1, hup⟩
    }

/-- An odd natural number in that bracket is the odd candidate. -/
theorem UniqueOddCandidateUnique (K : ℕ) (hK : Odd K) (hK3 : 3 ≤ K)
    (r : ℕ) (hr : Odd r) (hlow : r ^ 2 < 2 ^ K)
    (hhigh : 2 ^ K < (r + 2) ^ 2) :
    r = UniqueOddCandidate K := by
  let m := IntegerSqrtFloor K
  have hstrict := OddPowStrictSqrt K hK hK3
  have hrle : r ≤ m := by
    have hsqle : r ^ 2 ≤ 2 ^ K := Nat.le_of_lt hlow
    have hsqrt : r ≤ Nat.sqrt (2 ^ K) := (Nat.le_sqrt').mpr hsqle
    exact hsqrt
  have hmlt : m < r + 2 := by
    by_contra hge
    have hle2 : r + 2 ≤ m := (not_lt).mp hge
    have hsq : (r + 2) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hle2 2
    have hltPow : (r + 2) ^ 2 < 2 ^ K := lt_of_le_of_lt hsq hstrict.1
    exact lt_asymm hltPow hhigh
  have hband : m = r ∨ m = r + 1 := by
    omega
  cases hband with
  | inl hmr => {
      have hodd : Odd m := by
        rw [hmr]
        exact hr
      have hq : UniqueOddCandidate K = m :=
        UniqueOddCandidateOdd K hodd
      rw [hq, hmr]
    }
  | inr hmr => {
      have heven : Even m := by
        rw [hmr]
        exact (Nat.even_add_one).mpr ((Nat.not_even_iff_odd).mpr hr)
      have hq : UniqueOddCandidate K = m - 1 :=
        UniqueOddCandidateEven K heven
      have hrq : m - 1 = r := by
        omega
      rw [hq, hrq]
    }


end GeneralizedCollatz
