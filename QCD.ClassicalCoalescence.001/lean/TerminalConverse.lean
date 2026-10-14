-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import ClassicalCoalescence
import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace GeneralizedCollatz.ClassicalCoalescence

/-- The prime fact used by lifting the exponent at three. -/
instance ThreePrime : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The required valuation identity is a specialization of lifting the exponent. -/
theorem ThreeValuation (L : ℕ) (ho : Odd L) :
    padicValNat 3 (2 ^ L + 1) = 1 + padicValNat 3 L := by
  have h := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1)
    (by decide : Odd (3 : ℕ)) (by decide : 3 ∣ 2 + 1)
    (by decide : ¬ (3 : ℕ) ∣ 2) ho
  simpa only [one_pow, Nat.reduceAdd, padicValNat_self] using h

/-- A power of three divides `2^L+1` exactly under the odd-length divisibility condition. -/
theorem PowerDivisibility (a L : ℕ) :
    3 ^ (a + 1) ∣ 2 ^ L + 1 ↔ Odd L ∧ 3 ^ a ∣ L := by
  constructor
  · intro hd
    have hthree : 3 ∣ 2 ^ L + 1 :=
      dvd_trans (dvd_pow_self 3 (by omega : a + 1 ≠ 0)) hd
    have ho : Odd L := by
      rcases Nat.even_or_odd L with he | ho
      · obtain ⟨k, hk⟩ := he
        have hL : L = 2 * k := by omega
        have hr : (2 ^ L + 1) % 3 = 2 := by
          rw [hL, pow_mul]
          norm_num [Nat.add_mod, Nat.pow_mod]
        have hz := Nat.mod_eq_zero_of_dvd hthree
        omega
      · exact ho
    have hv := (padicValNat_dvd_iff_le (by positivity : 2 ^ L + 1 ≠ 0)).mp hd
    rw [ThreeValuation L ho] at hv
    have hle : a ≤ padicValNat 3 L := by omega
    exact ⟨ho, (padicValNat_dvd_iff_le (Odd.pos ho).ne').mpr hle⟩
  · rintro ⟨ho, hd⟩
    have hv := (padicValNat_dvd_iff_le (Odd.pos ho).ne').mp hd
    apply (padicValNat_dvd_iff_le (by positivity : 2 ^ L + 1 ≠ 0)).mpr
    rw [ThreeValuation L ho]
    omega

/-- An affine terminal equation recovers both the odd length parameter and its quotient. -/
theorem TerminalParameters (a u m : ℕ)
    (he : 3 ^ (a + 1) * u = 2 ^ (m + 2) + 1) :
    ∃ t : ℕ, 0 < t ∧ Odd t ∧ m + 2 = 3 ^ a * t ∧
      u = (2 ^ (3 ^ a * t) + 1) / 3 ^ (a + 1) := by
  have hd : 3 ^ (a + 1) ∣ 2 ^ (m + 2) + 1 := ⟨u, he.symm⟩
  obtain ⟨ho, hdiv⟩ := (PowerDivisibility a (m + 2)).mp hd
  obtain ⟨t, ht⟩ := hdiv
  have hto : Odd t := (Nat.odd_mul.mp (by simpa [ht] using ho)).2
  refine ⟨t, Odd.pos hto, hto, ht, ?_⟩
  rw [← ht, ← he, Nat.mul_div_cancel_left u (by positivity : 0 < 3 ^ (a + 1))]

/-- The shifted odd shortcut evaluates without natural-number subtraction. -/
theorem ShiftOddStep (x y : ℕ) (he : x + 1 = 2 * y) : Shortcut x + 1 = 3 * y := by
  have hx : x % 2 = 1 := by omega
  simp only [Shortcut, hx, if_neg (by decide : ¬ (1 : ℕ) = 0)]
  omega

/-- The closed initial odd-run formula retains its original seed throughout induction. -/
theorem OddRunShift (a u j : ℕ) (hu : 0 < u) (hj : j ≤ a) :
    Shortcut^[j] (2 ^ a * u - 1) + 1 = 3 ^ j * 2 ^ (a - j) * u := by
  induction j with
  | zero =>
    {
      simp only [Function.iterate_zero_apply, pow_zero, one_mul, Nat.sub_zero]
      have hp : 0 < 2 ^ a * u := by positivity
      exact Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ a * u)
    }
  | succ j ih =>
    {
      have hj0 : j ≤ a := by omega
      have he : a - j = a - (j + 1) + 1 := by omega
      have hshift : Shortcut^[j] (2 ^ a * u - 1) + 1 =
          2 * (3 ^ j * 2 ^ (a - (j + 1)) * u) := by
        rw [ih hj0, he, pow_succ]
        ring
      rw [Function.iterate_succ_apply', ShiftOddStep _ _ hshift, pow_succ]
      ring
    }

/-- Exact twice-output identity on the even shortcut branch. -/
theorem EvenRelation (x : ℕ) (hx : x % 2 = 0) : 2 * Shortcut x = x := by
  rw [Shortcut, if_pos hx]
  omega

/-- Exact twice-output identity on the odd shortcut branch. -/
theorem OddRelation (x : ℕ) (hx : x % 2 = 1) : 2 * Shortcut x = 3 * x + 1 := by
  simp only [Shortcut, hx, if_neg (by decide : ¬ (1 : ℕ) = 0)]
  omega

/-- The assumed final odd letter gives the terminal equation for every legal prefix `1^a01`. -/
theorem TerminalEquation (a u : ℕ) (hu : 0 < u) (ho : Odd u)
    (hlast : Shortcut^[a + 1] (2 ^ a * u - 1) % 2 = 1) :
    4 * Shortcut^[a + 2] (2 ^ a * u - 1) + 1 = 3 ^ (a + 1) * u := by
  have hrun := OddRunShift a u a hu (le_refl a)
  simp only [Nat.sub_self, pow_zero, mul_one] at hrun
  have hodd : Odd (3 ^ a * u) := (Odd.pow (by decide : Odd (3 : ℕ))).mul ho
  have hmod : Shortcut^[a] (2 ^ a * u - 1) % 2 = 0 := by
    have h := Nat.odd_iff.mp hodd
    omega
  have hhalf := EvenRelation _ hmod
  have haff := OddRelation _ hlast
  rw [← Function.iterate_succ_apply' Shortcut a (2 ^ a * u - 1)] at hhalf
  change 2 * Shortcut^[a + 1] (2 ^ a * u - 1) =
    Shortcut^[a] (2 ^ a * u - 1) at hhalf
  rw [← Function.iterate_succ_apply' Shortcut (a + 1) (2 ^ a * u - 1)] at haff
  change 2 * Shortcut^[a + 2] (2 ^ a * u - 1) =
    3 * Shortcut^[a + 1] (2 ^ a * u - 1) + 1 at haff
  have hpow : 3 ^ (a + 1) * u = 3 * (3 ^ a * u) := by rw [pow_succ]; ring
  rw [hpow]
  omega

/-- A terminal power on a legal prefix has precisely the stated odd parameterization. -/
theorem TerminalPrefixConverse (a u m : ℕ) (hu : 0 < u) (ho : Odd u)
    (hlast : Shortcut^[a + 1] (2 ^ a * u - 1) % 2 = 1)
    (hend : Shortcut^[a + 2] (2 ^ a * u - 1) = 2 ^ m) :
    ∃ t : ℕ, 0 < t ∧ Odd t ∧ m + 2 = 3 ^ a * t ∧
      u = (2 ^ (3 ^ a * t) + 1) / 3 ^ (a + 1) := by
  apply TerminalParameters a u m
  have he := TerminalEquation a u hu ho hlast
  rw [hend] at he
  have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
  omega

/-- The terminal equation also proves the last odd guard and the power endpoint. -/
theorem TerminalEquationRecovery (a u m : ℕ) (hu : 0 < u) (ho : Odd u)
    (he : 3 ^ (a + 1) * u = 2 ^ (m + 2) + 1) :
    Shortcut^[a + 1] (2 ^ a * u - 1) % 2 = 1 ∧
      Shortcut^[a + 2] (2 ^ a * u - 1) = 2 ^ m := by
  have hrun := OddRunShift a u a hu (le_refl a)
  simp only [Nat.sub_self, pow_zero, mul_one] at hrun
  have hodd : Odd (3 ^ a * u) := (Odd.pow (by decide : Odd (3 : ℕ))).mul ho
  have hmod : Shortcut^[a] (2 ^ a * u - 1) % 2 = 0 := by
    have h := Nat.odd_iff.mp hodd
    omega
  have hhalf := EvenRelation _ hmod
  rw [← Function.iterate_succ_apply' Shortcut a (2 ^ a * u - 1)] at hhalf
  change 2 * Shortcut^[a + 1] (2 ^ a * u - 1) =
    Shortcut^[a] (2 ^ a * u - 1) at hhalf
  have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
  have hpow : 3 ^ (a + 1) * u = 3 * (3 ^ a * u) := by rw [pow_succ]; ring
  have hlin : 3 * (Shortcut^[a] (2 ^ a * u - 1) + 1) = 4 * 2 ^ m + 1 := by
    rw [hrun, ← hpow, he, hp]
  have hlast : Shortcut^[a + 1] (2 ^ a * u - 1) % 2 = 1 := by omega
  refine ⟨hlast, ?_⟩
  have hend := TerminalEquation a u hu ho hlast
  rw [he, hp] at hend
  omega

/-- Exact classification of terminal powers within the initial prefix `1^a01`. -/
theorem TerminalPrefixClassification (a u m : ℕ) (hu : 0 < u) (ho : Odd u) :
    (Shortcut^[a + 1] (2 ^ a * u - 1) % 2 = 1 ∧
      Shortcut^[a + 2] (2 ^ a * u - 1) = 2 ^ m) ↔
    ∃ t : ℕ, 0 < t ∧ Odd t ∧ m + 2 = 3 ^ a * t ∧
      u = (2 ^ (3 ^ a * t) + 1) / 3 ^ (a + 1) := by
  constructor
  · rintro ⟨hlast, hend⟩
    exact TerminalPrefixConverse a u m hu ho hlast hend
  · rintro ⟨t, _htpos, htodd, hlen, huquot⟩
    apply TerminalEquationRecovery a u m hu ho
    have hlenodd : Odd (3 ^ a * t) :=
      (Odd.pow (by decide : Odd (3 : ℕ))).mul htodd
    have hd := (PowerDivisibility a (3 ^ a * t)).mpr ⟨hlenodd, dvd_mul_right _ _⟩
    rw [huquot, Nat.mul_div_cancel' hd, ← hlen]

end GeneralizedCollatz.ClassicalCoalescence
