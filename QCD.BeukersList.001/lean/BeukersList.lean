/-
Copyright (c) 2026 ascendnoosphere
SPDX-License-Identifier: CC-BY-4.0
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum.NatSqrt

set_option autoImplicit false

namespace GeneralizedCollatz.BeukersList

/-- The odd exponents checked below stop at this bound. -/
def BoxBound : ℕ := 32

/-- Expand the square of the successor. -/
theorem SuccSquare (a : ℕ) : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
  calc
    (a + 1) * (a + 1) = a * (a + 1) + 1 * (a + 1) := by
      rw [Nat.add_mul]
    _ = a * (a + 1) + (a + 1) := by
      rw [Nat.one_mul]
    _ = a * a + a * 1 + (a + 1) := by
      rw [Nat.mul_add]
    _ = a * a + a + (a + 1) := by
      rw [Nat.mul_one]
    _ = a * a + (a + (a + 1)) := by
      rw [Nat.add_assoc]
    _ = a * a + ((a + a) + 1) := by
      simp only [Nat.add_assoc]
    _ = a * a + (2 * a + 1) := by
      rw [← Nat.two_mul]
    _ = a * a + 2 * a + 1 := by
      rw [← Nat.add_assoc]

/-- A square is recovered by the integer square root. -/
theorem SqrtOfSquare (s : ℕ) : Nat.sqrt (s * s) = s := by
  set q := Nat.sqrt (s * s) with hq
  have hle : q * q ≤ s * s := by
    rw [hq]
    exact Nat.sqrt_le (s * s)
  have hlt : s * s < (q + 1) * (q + 1) := by
    have raw := Nat.lt_succ_sqrt (s * s)
    simpa only [← hq, Nat.succ_eq_add_one] using raw
  have hqs : q ≤ s := by
    {
      by_contra hgt
      have hge : s + 1 ≤ q := by omega
      have hmul : (s + 1) * (s + 1) ≤ q * q := Nat.mul_le_mul hge hge
      have hbad : s * s + 2 * s + 1 ≤ s * s := by
        rw [← SuccSquare s]
        exact Nat.le_trans hmul hle
      omega
    }
  have hsq : s ≤ q := by
    {
      by_contra hltq
      have hge : q + 1 ≤ s := by omega
      have hmul : (q + 1) * (q + 1) ≤ s * s := Nat.mul_le_mul hge hge
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hmul)
    }
  exact Nat.le_antisymm hqs hsq

/-- The positive integer square root of `r`, if `r` is a positive square. -/
def SqrtCandidate (r : ℕ) : Option ℕ :=
  if Nat.sqrt r * Nat.sqrt r = r ∧ 0 < Nat.sqrt r then
    some (Nat.sqrt r)
  else
    none

/-- `SqrtCandidate` returns the positive root exactly on positive squares. -/
theorem SqrtCandidateEqSomeIff (r s : ℕ) :
    SqrtCandidate r = some s ↔ s * s = r ∧ 0 < s := by
  unfold SqrtCandidate
  split
  next hc =>
    constructor
    · intro h
      injection h with hs
      rw [← hs]
      exact hc
    · intro h
      have hs : Nat.sqrt r = s := by
        have hsqrt : Nat.sqrt (s * s) = s := SqrtOfSquare s
        rw [h.1] at hsqrt
        exact hsqrt
      rw [hs]
  next hc =>
    constructor
    · intro h
      cases h
    · intro h
      exfalso
      apply hc
      have hs : Nat.sqrt r = s := by
        have hsqrt : Nat.sqrt (s * s) = s := SqrtOfSquare s
        rw [h.1] at hsqrt
        exact hsqrt
      rw [hs]
      exact h

/-- Positive `s` with `s^2 + D = 2^n`, packaged as an optional root of the remainder. -/
def PositiveRoot (D n : ℕ) : Option ℕ :=
  if 2 ^ n < D then
    none
  else
    SqrtCandidate (2 ^ n - D)

/-- The optional root is a positive solution of `s^2 + D = 2^n`. -/
theorem PositiveRootEqSomeIff (D n s : ℕ) :
    PositiveRoot D n = some s ↔ 0 < s ∧ s ^ 2 + D = 2 ^ n := by
  unfold PositiveRoot
  split
  next hlt =>
    constructor
    · intro h
      cases h
    · intro h
      rcases h with ⟨_hs, hEq⟩
      have hle : D ≤ s ^ 2 + D := Nat.le_add_left D (s ^ 2)
      have hlt' : 2 ^ n < s ^ 2 + D := Nat.lt_of_lt_of_le hlt hle
      rw [hEq] at hlt'
      exact False.elim (Nat.lt_irrefl _ hlt')
  next hlt =>
    rw [SqrtCandidateEqSomeIff]
    have hle : D ≤ 2 ^ n := Nat.le_of_not_lt hlt
    constructor
    · intro h
      rcases h with ⟨hsq, hs⟩
      refine ⟨hs, ?_⟩
      rw [Nat.pow_two]
      have hsum : s * s + D = (2 ^ n - D) + D := by rw [hsq]
      rw [hsum]
      exact Nat.sub_add_cancel hle
    · intro h
      rcases h with ⟨hs, hEq⟩
      refine ⟨?_, hs⟩
      rw [Nat.pow_two] at hEq
      have hsum : (2 ^ n - D) + D = s * s + D := by
        rw [Nat.sub_add_cancel hle, hEq]
      exact (Nat.add_right_cancel hsum).symm

/-- Odd `n ≤ bound` whose remainder `2^n - D` is a positive square. -/
def OddPositivePairs (D bound : ℕ) : List (ℕ × ℕ) :=
  (List.range (bound + 1)).filterMap fun n =>
    if n % 2 = 0 then
      none
    else
      (PositiveRoot D n).map fun s => (s, n)

/-- Membership in the odd positive-root list is the root equation at an odd index. -/
theorem MemOddPositivePairs (D bound x n : ℕ) :
    (x, n) ∈ OddPositivePairs D bound ↔
      n < bound + 1 ∧ n % 2 = 1 ∧ PositiveRoot D n = some x := by
  unfold OddPositivePairs
  rw [List.mem_filterMap]
  constructor
  · intro h
    rcases h with ⟨a, ha, hf⟩
    have ha1 : a < bound + 1 := by
      rw [List.range_eq_range', List.mem_range'_1] at ha
      omega
    by_cases he : a % 2 = 0
    · rw [if_pos he] at hf
      cases hf
    · have ho : a % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
        · exact False.elim (he h0)
        · exact h1
      rw [if_neg he] at hf
      cases hroot : PositiveRoot D a with
      | none =>
        {
          rw [hroot] at hf
          cases hf
        }
      | some s =>
        {
          rw [hroot, Option.map_some] at hf
          obtain ⟨hs, hn⟩ := Prod.ext_iff.mp (Option.some.inj hf)
          subst hs
          subst hn
          exact ⟨ha1, ho, hroot⟩
        }
  · intro h
    rcases h with ⟨hn, ho, hroot⟩
    refine ⟨n, ?_, ?_⟩
    · rw [List.range_eq_range', List.mem_range'_1]
      exact ⟨Nat.zero_le n, by omega⟩
    · have hne : ¬ n % 2 = 0 := by
        intro h0
        omega
      rw [if_neg hne, hroot, Option.map_some]

/-- The odd positive solutions of `x^2 + 7 = 2^n` for `n ≤ 32`. -/
theorem OddPositivePairsSeven :
    OddPositivePairs 7 BoxBound = [(1, 3), (5, 5), (11, 7), (181, 15)] := by
  norm_num [OddPositivePairs, BoxBound, PositiveRoot, SqrtCandidate, List.range_succ,
    List.filterMap_cons, List.filterMap_nil]

/-- The odd positive solutions of `x^2 + 23 = 2^n` for `n ≤ 32`. -/
theorem OddPositivePairsTwentyThree :
    OddPositivePairs 23 BoxBound = [(3, 5), (45, 11)] := by
  norm_num [OddPositivePairs, BoxBound, PositiveRoot, SqrtCandidate, List.range_succ,
    List.filterMap_cons, List.filterMap_nil]

/-- The gap between `(2^m)^2` and `(2^m - 1)^2` is the next Mersenne number. -/
theorem PredSquareGap (m : ℕ) :
    (2 ^ m) ^ 2 - (2 ^ m - 1) ^ 2 = 2 ^ (m + 1) - 1 := by
  have hone : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
  have hsub : 2 ^ m - (2 ^ m - 1) = 1 := Nat.sub_sub_self hone
  have hdouble : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := Nat.two_pow_succ m
  have hsum : 2 ^ m + (2 ^ m - 1) = 2 ^ (m + 1) - 1 := by
    have h1 : 2 ^ m + (2 ^ m - 1) + 1 = 2 ^ (m + 1) := by
      calc
        2 ^ m + (2 ^ m - 1) + 1 = 2 ^ m + ((2 ^ m - 1) + 1) := by
          rw [Nat.add_assoc]
        _ = 2 ^ m + 2 ^ m := by
          rw [Nat.sub_add_cancel hone]
        _ = 2 ^ (m + 1) := by
          rw [← hdouble]
    exact Nat.eq_sub_of_add_eq h1
  calc
    (2 ^ m) ^ 2 - (2 ^ m - 1) ^ 2
        = (2 ^ m + (2 ^ m - 1)) * (2 ^ m - (2 ^ m - 1)) := by
          rw [Nat.pow_two_sub_pow_two]
    _ = (2 ^ (m + 1) - 1) * 1 := by
      rw [hsum, hsub]
    _ = 2 ^ (m + 1) - 1 := by
      rw [Nat.mul_one]

/-- For `m ≥ 3`, `2^{2m} - 7` lies strictly between `(2^m - 1)^2` and `(2^m)^2`. -/
theorem EvenStrictSeven (m : ℕ) (hm : 3 ≤ m) :
    (2 ^ m - 1) ^ 2 < 2 ^ (2 * m) - 7 ∧ 2 ^ (2 * m) - 7 < (2 ^ m) ^ 2 := by
  have hpow : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by
    rw [← Nat.pow_mul, Nat.mul_comm]
  have hle : (2 ^ m - 1) ^ 2 ≤ (2 ^ m) ^ 2 := by
    have hpred : 2 ^ m - 1 ≤ 2 ^ m := Nat.sub_le _ _
    exact Nat.pow_le_pow_left hpred 2
  have hsum : (2 ^ m - 1) ^ 2 + (2 ^ (m + 1) - 1) = (2 ^ m) ^ 2 := by
    calc
      (2 ^ m - 1) ^ 2 + (2 ^ (m + 1) - 1)
          = (2 ^ m - 1) ^ 2 + ((2 ^ m) ^ 2 - (2 ^ m - 1) ^ 2) := by
            rw [PredSquareGap m]
      _ = (2 ^ m) ^ 2 := Nat.add_sub_cancel' hle
  have h16 : 16 ≤ 2 ^ (m + 1) := by
    have h4 : 4 ≤ m + 1 := by omega
    have hpow4 : 2 ^ 4 ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) h4
    have hfour : 2 ^ 4 = 16 := by decide
    rwa [hfour] at hpow4
  have h7 : 7 < 2 ^ (m + 1) - 1 := by
    have h8 : 8 < 2 ^ (m + 1) := Nat.lt_of_lt_of_le (by decide : 8 < 16) h16
    exact Nat.lt_sub_of_add_lt h8
  have hlo0 : (2 ^ m - 1) ^ 2 + 7 < (2 ^ m) ^ 2 := by
    have hlt : (2 ^ m - 1) ^ 2 + 7 < (2 ^ m - 1) ^ 2 + (2 ^ (m + 1) - 1) :=
      Nat.add_lt_add_left h7 _
    rwa [hsum] at hlt
  have hlo : (2 ^ m - 1) ^ 2 < 2 ^ (2 * m) - 7 := by
    have hsub : (2 ^ m - 1) ^ 2 < (2 ^ m) ^ 2 - 7 := Nat.lt_sub_of_add_lt hlo0
    simpa [hpow] using hsub
  have hhi : 2 ^ (2 * m) - 7 < (2 ^ m) ^ 2 := by
    rw [← hpow]
    have h7le : 7 ≤ (2 ^ m) ^ 2 := by
      rw [hpow]
      have h4 : 4 ≤ 2 * m := by omega
      have hpow4 : 2 ^ 4 ≤ 2 ^ (2 * m) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) h4
      have hfour : 2 ^ 4 = 16 := by decide
      rw [hfour] at hpow4
      exact Nat.le_trans (by decide : 7 ≤ 16) hpow4
    have hpos : 0 < 7 := by decide
    have hstep : (2 ^ m) ^ 2 - 7 < (2 ^ m) ^ 2 - 7 + 7 :=
      Nat.lt_add_of_pos_right hpos
    rwa [Nat.sub_add_cancel h7le] at hstep
  exact ⟨hlo, hhi⟩

/-- No square lies strictly between two consecutive squares. -/
theorem NoSquareStrictlyBetween (a t x : ℕ) (hlo : a ^ 2 < t) (hhi : t < (a + 1) ^ 2) :
    x ^ 2 ≠ t := by
  intro hx
  rcases Nat.lt_or_ge x (a + 1) with hlt | hge
  · have hxle : x ≤ a := by omega
    have hsq : x ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hxle 2
    rw [hx] at hsq
    exact Nat.not_lt.mpr hsq hlo
  · have hsq : (a + 1) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hge 2
    rw [hx] at hsq
    exact Nat.not_lt.mpr hsq hhi

/-- The only positive solution of `x^2 + 7 = 2^{2m}` is `x = 3`, `m = 2`. -/
theorem EvenExponentSeven (x m : ℕ) (_hx : 0 < x) (h : x ^ 2 + 7 = 2 ^ (2 * m)) :
    x = 3 ∧ m = 2 := by
  cases m with
  | zero =>
    {
      have h1 : 2 ^ (2 * 0) = 1 := by decide
      rw [h1] at h
      have h7 : 7 ≤ x ^ 2 + 7 := Nat.le_add_left 7 (x ^ 2)
      rw [h] at h7
      omega
    }
  | succ m1 =>
    {
      cases m1 with
      | zero =>
        {
          have h4 : 2 ^ (2 * Nat.succ 0) = 4 := by decide
          rw [h4] at h
          have h7 : 7 ≤ x ^ 2 + 7 := Nat.le_add_left 7 (x ^ 2)
          rw [h] at h7
          omega
        }
      | succ m2 =>
        {
          cases m2 with
          | zero =>
            {
              have h16 : 2 ^ (2 * Nat.succ (Nat.succ 0)) = 16 := by decide
              rw [h16] at h
              have hx2 : x ^ 2 = 9 := by
                have hsub : x ^ 2 = 16 - 7 := Nat.eq_sub_of_add_eq h
                have h9 : 16 - 7 = 9 := by decide
                rw [h9] at hsub
                exact hsub
              have hxle : x ≤ 3 := by
                by_contra hgt
                have h4 : 4 ≤ x := Nat.succ_le_of_lt (Nat.not_le.mp hgt)
                have hmul : 4 * 4 ≤ x * x := Nat.mul_le_mul h4 h4
                have hsq : 16 ≤ x ^ 2 := by simpa [Nat.pow_two] using hmul
                rw [hx2] at hsq
                exact Nat.not_le.mpr (by decide : 9 < 16) hsq
              have hxge : 3 ≤ x := by
                by_contra hlt
                have h2 : x ≤ 2 := Nat.le_of_lt_succ (Nat.not_le.mp hlt)
                have hmul : x * x ≤ 2 * 2 := Nat.mul_le_mul h2 h2
                have hsq : x ^ 2 ≤ 4 := by simpa [Nat.pow_two] using hmul
                rw [hx2] at hsq
                exact Nat.not_le.mpr (by decide : 4 < 9) hsq
              exact ⟨Nat.le_antisymm hxge hxle |>.symm, rfl⟩
            }
          | succ m3 =>
            {
              have hm : m3 + 1 + 1 + 1 = m3 + 3 := by omega
              have hm3 : 3 ≤ m3 + 3 := by omega
              rw [hm] at h
              have h7le : 7 ≤ 2 ^ (2 * (m3 + 3)) := by
                have h4 : 4 ≤ 2 * (m3 + 3) := by omega
                have hpow4 : 2 ^ 4 ≤ 2 ^ (2 * (m3 + 3)) :=
                  Nat.pow_le_pow_right (by decide : 0 < 2) h4
                have hfour : 2 ^ 4 = 16 := by decide
                rw [hfour] at hpow4
                exact Nat.le_trans (by decide : 7 ≤ 16) hpow4
              have hx2 : x ^ 2 = 2 ^ (2 * (m3 + 3)) - 7 :=
                Nat.eq_sub_of_add_eq h
              have hgap := EvenStrictSeven (m3 + 3) hm3
              have ha : (2 ^ (m3 + 3) - 1) + 1 = 2 ^ (m3 + 3) :=
                Nat.sub_add_cancel (Nat.one_le_pow (m3 + 3) 2 (by decide))
              have hhi : 2 ^ (2 * (m3 + 3)) - 7 <
                  ((2 ^ (m3 + 3) - 1) + 1) ^ 2 := by
                simpa [ha] using hgap.2
              exact absurd hx2
                (NoSquareStrictlyBetween (2 ^ (m3 + 3) - 1)
                  (2 ^ (2 * (m3 + 3)) - 7) x hgap.1 hhi)
            }
        }
    }

/-- For `m ≥ 4`, `2^{2m} - 23` lies strictly between `(2^m - 1)^2` and `(2^m)^2`. -/
theorem EvenStrictTwentyThree (m : ℕ) (hm : 4 ≤ m) :
    (2 ^ m - 1) ^ 2 < 2 ^ (2 * m) - 23 ∧ 2 ^ (2 * m) - 23 < (2 ^ m) ^ 2 := by
  have hpow : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by
    rw [← Nat.pow_mul, Nat.mul_comm]
  have hle : (2 ^ m - 1) ^ 2 ≤ (2 ^ m) ^ 2 := by
    have hpred : 2 ^ m - 1 ≤ 2 ^ m := Nat.sub_le _ _
    exact Nat.pow_le_pow_left hpred 2
  have hsum : (2 ^ m - 1) ^ 2 + (2 ^ (m + 1) - 1) = (2 ^ m) ^ 2 := by
    calc
      (2 ^ m - 1) ^ 2 + (2 ^ (m + 1) - 1)
          = (2 ^ m - 1) ^ 2 + ((2 ^ m) ^ 2 - (2 ^ m - 1) ^ 2) := by
            rw [PredSquareGap m]
      _ = (2 ^ m) ^ 2 := Nat.add_sub_cancel' hle
  have h32 : 32 ≤ 2 ^ (m + 1) := by
    have h5 : 5 ≤ m + 1 := by omega
    have hpow5 : 2 ^ 5 ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) h5
    have hfive : 2 ^ 5 = 32 := by decide
    rwa [hfive] at hpow5
  have h23 : 23 < 2 ^ (m + 1) - 1 := by
    have h24 : 24 < 2 ^ (m + 1) :=
      Nat.lt_of_lt_of_le (by decide : 24 < 32) h32
    exact Nat.lt_sub_of_add_lt h24
  have hlo0 : (2 ^ m - 1) ^ 2 + 23 < (2 ^ m) ^ 2 := by
    have hlt : (2 ^ m - 1) ^ 2 + 23 < (2 ^ m - 1) ^ 2 + (2 ^ (m + 1) - 1) :=
      Nat.add_lt_add_left h23 _
    rwa [hsum] at hlt
  have hlo : (2 ^ m - 1) ^ 2 < 2 ^ (2 * m) - 23 := by
    have hsub : (2 ^ m - 1) ^ 2 < (2 ^ m) ^ 2 - 23 := Nat.lt_sub_of_add_lt hlo0
    simpa [hpow] using hsub
  have hhi : 2 ^ (2 * m) - 23 < (2 ^ m) ^ 2 := by
    rw [← hpow]
    have h23le : 23 ≤ (2 ^ m) ^ 2 := by
      rw [hpow]
      have h8 : 8 ≤ 2 * m := by omega
      have hpow8 : 2 ^ 8 ≤ 2 ^ (2 * m) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) h8
      have height : 2 ^ 8 = 256 := by decide
      rw [height] at hpow8
      exact Nat.le_trans (by decide : 23 ≤ 256) hpow8
    have hpos : 0 < 23 := by decide
    have hstep : (2 ^ m) ^ 2 - 23 < (2 ^ m) ^ 2 - 23 + 23 :=
      Nat.lt_add_of_pos_right hpos
    rwa [Nat.sub_add_cancel h23le] at hstep
  exact ⟨hlo, hhi⟩

/-- `x^2 + 23 = 2^{2m}` has no positive solution. -/
theorem EvenExponentTwentyThree (x m : ℕ) (_hx : 0 < x)
    (h : x ^ 2 + 23 = 2 ^ (2 * m)) : False := by
  cases m with
  | zero =>
    {
      have h1 : 2 ^ (2 * 0) = 1 := by decide
      rw [h1] at h
      have h23 : 23 ≤ x ^ 2 + 23 := Nat.le_add_left 23 (x ^ 2)
      rw [h] at h23
      omega
    }
  | succ m1 =>
    {
      cases m1 with
      | zero =>
        {
          have h4 : 2 ^ (2 * Nat.succ 0) = 4 := by decide
          rw [h4] at h
          have h23 : 23 ≤ x ^ 2 + 23 := Nat.le_add_left 23 (x ^ 2)
          rw [h] at h23
          omega
        }
      | succ m2 =>
        {
          cases m2 with
          | zero =>
            {
              have h16 : 2 ^ (2 * Nat.succ (Nat.succ 0)) = 16 := by decide
              rw [h16] at h
              have h23 : 23 ≤ x ^ 2 + 23 := Nat.le_add_left 23 (x ^ 2)
              rw [h] at h23
              omega
            }
          | succ m3 =>
            {
              cases m3 with
              | zero =>
                {
                  have h64 : 2 ^ (2 * Nat.succ (Nat.succ (Nat.succ 0))) = 64 := by
                    decide
                  rw [h64] at h
                  have hx2 : x ^ 2 = 41 := by omega
                  exact absurd hx2
                    (NoSquareStrictlyBetween 6 41 x (by decide) (by decide))
                }
              | succ m4 =>
                {
                  have hm : m4 + 1 + 1 + 1 + 1 = m4 + 4 := by omega
                  have hm4 : 4 ≤ m4 + 4 := by omega
                  rw [hm] at h
                  have h23le : 23 ≤ 2 ^ (2 * (m4 + 4)) := by
                    have h8 : 8 ≤ 2 * (m4 + 4) := by omega
                    have hpow8 : 2 ^ 8 ≤ 2 ^ (2 * (m4 + 4)) :=
                      Nat.pow_le_pow_right (by decide : 0 < 2) h8
                    have height : 2 ^ 8 = 256 := by decide
                    rw [height] at hpow8
                    exact Nat.le_trans (by decide : 23 ≤ 256) hpow8
                  have hx2 : x ^ 2 = 2 ^ (2 * (m4 + 4)) - 23 :=
                    Nat.eq_sub_of_add_eq h
                  have hgap := EvenStrictTwentyThree (m4 + 4) hm4
                  have ha : (2 ^ (m4 + 4) - 1) + 1 = 2 ^ (m4 + 4) :=
                    Nat.sub_add_cancel (Nat.one_le_pow (m4 + 4) 2 (by decide))
                  have hhi : 2 ^ (2 * (m4 + 4)) - 23 <
                      ((2 ^ (m4 + 4) - 1) + 1) ^ 2 := by
                    simpa [ha] using hgap.2
                  exact absurd hx2
                    (NoSquareStrictlyBetween (2 ^ (m4 + 4) - 1)
                      (2 ^ (2 * (m4 + 4)) - 23) x hgap.1 hhi)
                }
            }
        }
    }

/-- Direct check of the displayed pair `(1, 3)` for `D = 7`. -/
theorem DyadicSquareSevenOne : 1 ^ 2 + 7 = 2 ^ 3 := by decide

/-- Direct check of the displayed pair `(3, 4)` for `D = 7`. -/
theorem DyadicSquareSevenThree : 3 ^ 2 + 7 = 2 ^ 4 := by decide

/-- Direct check of the displayed pair `(5, 5)` for `D = 7`. -/
theorem DyadicSquareSevenFive : 5 ^ 2 + 7 = 2 ^ 5 := by decide

/-- Direct check of the displayed pair `(11, 7)` for `D = 7`. -/
theorem DyadicSquareSevenEleven : 11 ^ 2 + 7 = 2 ^ 7 := by decide

/-- Direct check of the displayed pair `(181, 15)` for `D = 7`. -/
theorem DyadicSquareSevenOneEightyOne : 181 ^ 2 + 7 = 2 ^ 15 := by decide

/-- Direct check of the displayed pair `(3, 5)` for `D = 23`. -/
theorem DyadicSquareTwentyThreeThree : 3 ^ 2 + 23 = 2 ^ 5 := by decide

/-- Direct check of the displayed pair `(45, 11)` for `D = 23`. -/
theorem DyadicSquareTwentyThreeFortyFive : 45 ^ 2 + 23 = 2 ^ 11 := by decide

/-- Inside `n ≤ 32`, the positive solutions of `x^2 + 7 = 2^n` are the five displayed pairs. -/
theorem DyadicSquareBoxSeven (x n : ℕ) (hn : n ≤ BoxBound) (hx : 0 < x) :
    x ^ 2 + 7 = 2 ^ n ↔
      (x = 1 ∧ n = 3) ∨ (x = 3 ∧ n = 4) ∨ (x = 5 ∧ n = 5) ∨
        (x = 11 ∧ n = 7) ∨ (x = 181 ∧ n = 15) := by
  constructor
  · intro hEq
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · have hdiv : n / 2 * 2 + n % 2 = n := Nat.div_add_mod' n 2
      have hn2 : n = 2 * (n / 2) := by
        rw [hn0, Nat.add_zero, Nat.mul_comm] at hdiv
        exact hdiv.symm
      have hEven : x ^ 2 + 7 = 2 ^ (2 * (n / 2)) := by
        rw [← hn2]
        exact hEq
      have hem := EvenExponentSeven x (n / 2) hx hEven
      rcases hem with ⟨rfl, hm⟩
      have hn4 : n = 4 := by
        rw [hn2, hm]
      exact Or.inr (Or.inl ⟨rfl, hn4⟩)
    · have hmem : (x, n) ∈ OddPositivePairs 7 BoxBound := by
        rw [MemOddPositivePairs]
        refine ⟨?_, hn1, ?_⟩
        · omega
        · rw [PositiveRootEqSomeIff]
          exact ⟨hx, hEq⟩
      simp only [OddPositivePairsSeven, List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with h | h | h | h
      · obtain ⟨hx1, hn3⟩ := Prod.ext_iff.mp h
        subst hx1
        subst hn3
        exact Or.inl ⟨rfl, rfl⟩
      · obtain ⟨hx5, hn5⟩ := Prod.ext_iff.mp h
        subst hx5
        subst hn5
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · obtain ⟨hx11, hn7⟩ := Prod.ext_iff.mp h
        subst hx11
        subst hn7
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · obtain ⟨hx181, hn15⟩ := Prod.ext_iff.mp h
        subst hx181
        subst hn15
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact DyadicSquareSevenOne
    · exact DyadicSquareSevenThree
    · exact DyadicSquareSevenFive
    · exact DyadicSquareSevenEleven
    · show 181 ^ 2 + 7 = 2 ^ 15
      exact DyadicSquareSevenOneEightyOne

/-- Inside `n ≤ 32`, the positive solutions of `x^2 + 23 = 2^n` are the two displayed pairs. -/
theorem DyadicSquareBoxTwentyThree (x n : ℕ) (hn : n ≤ BoxBound) (hx : 0 < x) :
    x ^ 2 + 23 = 2 ^ n ↔ (x = 3 ∧ n = 5) ∨ (x = 45 ∧ n = 11) := by
  constructor
  · intro hEq
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · have hdiv : n / 2 * 2 + n % 2 = n := Nat.div_add_mod' n 2
      have hn2 : n = 2 * (n / 2) := by
        rw [hn0, Nat.add_zero, Nat.mul_comm] at hdiv
        exact hdiv.symm
      have hEven : x ^ 2 + 23 = 2 ^ (2 * (n / 2)) := by
        rw [← hn2]
        exact hEq
      exact False.elim (EvenExponentTwentyThree x (n / 2) hx hEven)
    · have hmem : (x, n) ∈ OddPositivePairs 23 BoxBound := by
        rw [MemOddPositivePairs]
        refine ⟨?_, hn1, ?_⟩
        · omega
        · rw [PositiveRootEqSomeIff]
          exact ⟨hx, hEq⟩
      simp only [OddPositivePairsTwentyThree, List.mem_cons, List.mem_nil_iff,
        or_false] at hmem
      rcases hmem with h | h
      · obtain ⟨hx3, hn5⟩ := Prod.ext_iff.mp h
        subst hx3
        subst hn5
        exact Or.inl ⟨rfl, rfl⟩
      · obtain ⟨hx45, hn11⟩ := Prod.ext_iff.mp h
        subst hx45
        subst hn11
        exact Or.inr ⟨rfl, rfl⟩
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact DyadicSquareTwentyThreeThree
    · exact DyadicSquareTwentyThreeFortyFive

/-- The unit Mersenne representation `1^2 + (2^k - 1) = 2^k`. -/
theorem MersenneUnitSolution (k : ℕ) : 1 ^ 2 + (2 ^ k - 1) = 2 ^ k := by
  have hone : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  rw [Nat.one_pow]
  exact Nat.add_sub_cancel' hone

/-- The second Mersenne representation. The hypothesis `k ≥ 1` keeps the exponent non-wrapping. -/
theorem MersenneSecondSolution (k : ℕ) (hk : 1 ≤ k) :
    (2 ^ (k - 1) - 1) ^ 2 + (2 ^ k - 1) = 2 ^ (2 * k - 2) := by
  set m := k - 1
  have hk1 : k = m + 1 := (Nat.sub_add_cancel hk).symm
  rw [hk1]
  have hexp : 2 * (m + 1) - 2 = 2 * m := by
    have hmul : 2 * (m + 1) = 2 * m + 2 := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [hmul]
    exact Nat.add_sub_cancel_right (2 * m) 2
  rw [hexp]
  have hgap := PredSquareGap m
  have hle : (2 ^ m - 1) ^ 2 ≤ (2 ^ m) ^ 2 := by
    have hpred : 2 ^ m - 1 ≤ 2 ^ m := Nat.sub_le _ _
    exact Nat.pow_le_pow_left hpred 2
  have hpow : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by
    rw [← Nat.pow_mul, Nat.mul_comm]
  calc
    (2 ^ m - 1) ^ 2 + (2 ^ (m + 1) - 1)
        = (2 ^ m - 1) ^ 2 + ((2 ^ m) ^ 2 - (2 ^ m - 1) ^ 2) := by
          rw [hgap]
    _ = (2 ^ m) ^ 2 := Nat.add_sub_cancel' hle
    _ = 2 ^ (2 * m) := hpow

/-- For `k ≥ 4` the two Mersenne roots and the two exponents are distinct. -/
theorem MersenneSolutionsDistinct (k : ℕ) (hk : 4 ≤ k) :
    1 ≠ 2 ^ (k - 1) - 1 ∧ k ≠ 2 * k - 2 := by
  refine ⟨?_, ?_⟩
  · have h3 : 3 ≤ k - 1 := by omega
    have hpow : 2 ^ 3 ≤ 2 ^ (k - 1) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) h3
    have height : 2 ^ 3 = 8 := by decide
    rw [height] at hpow
    omega
  · omega

/-- Each Mersenne number `2^k - 1` with `k ≥ 4` has two distinct positive representations. -/
theorem MersenneTwoRepresentations (k : ℕ) (hk : 4 ≤ k) :
    1 ^ 2 + (2 ^ k - 1) = 2 ^ k ∧
      (2 ^ (k - 1) - 1) ^ 2 + (2 ^ k - 1) = 2 ^ (2 * k - 2) ∧
        1 ≠ 2 ^ (k - 1) - 1 ∧ k ≠ 2 * k - 2 := by
  refine ⟨MersenneUnitSolution k, MersenneSecondSolution k (by omega), ?_⟩
  exact MersenneSolutionsDistinct k hk

end GeneralizedCollatz.BeukersList
