-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Signed trap itineraries

A raw orbit that never divides exactly follows one affine recursion. On such an
orbit the multiplier decides the entire future: a constant fixed point, a
nonzero translation, the two-cycle `n, c - n`, the exact affine fixed point, or
escape in absolute value. Separately, the affine branch modulo `|d|` is the
residue walk `r ↦ q * r + c`, and a seed is trapped exactly when that walk
avoids the zero class at every time. All statements are over `ℤ`, so negative
states, negative divisors and alternating signs are covered.

Not formalized here: the density statements of the signed families, the
first-division return map with its residue-dependent exponent, the signed core
certificate with its boundary bound, the forced prime-power classification of
the independent base, the criticality ledger, and every convergence statement
for the classical target.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Chronological offset sum of an affine itinerary; the empty sum is zero. -/
def TrapSum (q : ℤ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => TrapSum q j + q ^ j

/-- The offset sum is the geometric series with its index shifted by one. -/
theorem TrapSumMulSubOne (q : ℤ) (j : ℕ) : (q - 1) * TrapSum q j = q ^ j - 1 := by
  induction j with
  | zero => {
      simp [TrapSum]
    }
  | succ j ih => {
      have h : (q - 1) * (TrapSum q j + q ^ j) =
          (q - 1) * TrapSum q j + (q - 1) * q ^ j := by ring
      rw [TrapSum, h, ih, pow_succ]
      ring
    }

/-- A zero multiplier leaves the unit offset after the first step. -/
theorem TrapSumZero (j : ℕ) : TrapSum 0 (j + 1) = 1 := by
  induction j with
  | zero => {
      simp [TrapSum]
    }
  | succ j ih => {
      rw [TrapSum, ih]
      simp
    }

/-- A unit multiplier accumulates one unit of offset per step. -/
theorem TrapSumOne (j : ℕ) : TrapSum 1 j = (j : ℤ) := by
  induction j with
  | zero => {
      simp [TrapSum]
    }
  | succ j ih => {
      rw [TrapSum, ih]
      simp
    }

/-- Two further steps extend an offset sum by their own multipliers. -/
theorem TrapSumAddTwo (q : ℤ) (j : ℕ) :
    TrapSum q (j + 2) = TrapSum q j + q ^ j + q ^ (j + 1) := by
  have h : j + 2 = (j + 1) + 1 := by omega
  rw [h, TrapSum, TrapSum]

/-- The one-step recursion of the offset sum: three steps equal one scaled step. -/
theorem TrapSumRec (q : ℤ) (j : ℕ) : TrapSum q (j + 1) = q * TrapSum q j + 1 := by
  have h1 := TrapSumMulSubOne q j
  have h2 : TrapSum q (j + 1) = TrapSum q j + q ^ j := rfl
  have h3 : q ^ j = (q - 1) * TrapSum q j + 1 := by omega
  rw [h2, h3]
  ring

/-- An even number of steps has zero offset sum under the negative unit multiplier. -/
theorem TrapSumNegOneEven (j : ℕ) : TrapSum (-1) (2 * j) = 0 := by
  induction j with
  | zero => {
      simp [TrapSum]
    }
  | succ j ih => {
      have h : 2 * (j + 1) = 2 * j + 2 := by omega
      have h1 : (-1 : ℤ) ^ (2 * j) = 1 := by
        rw [pow_mul]
        norm_num
      have h2 : (-1 : ℤ) ^ (2 * j + 1) = -1 := by
        rw [pow_succ, h1]
        ring
      rw [h, TrapSumAddTwo, ih, h1, h2]
      ring
    }

/-- An odd number of steps has unit offset sum under the negative unit multiplier. -/
theorem TrapSumNegOneOdd (j : ℕ) : TrapSum (-1) (2 * j + 1) = 1 := by
  have h1 : (-1 : ℤ) ^ (2 * j) = 1 := by
    rw [pow_mul]
    norm_num
  rw [TrapSum, TrapSumNegOneEven j, h1]
  ring

/-- A raw orbit on which no state is divisible by the signed divisor. -/
def NeverDivides (p : Parameters) (n : ℤ) : Prop :=
  ∀ j : ℕ, ¬ p.D ∣ Iterate (RawStep p) j n

/-- A state that the divisor does not divide executes the affine branch exactly. -/
theorem RawStepAffine (p : Parameters) (n : ℤ) (h : ¬ p.D ∣ n) :
    RawStep p n = p.Q * n + p.C := by
  simp [RawStep, h]

/-- A division-free orbit stays division-free after one step. -/
theorem NeverDividesShift (p : Parameters) (n : ℤ) (h : NeverDivides p n) :
    NeverDivides p (RawStep p n) := by
  intro j hj
  have hstep : Iterate (RawStep p) j (RawStep p n) = Iterate (RawStep p) (j + 1) n := by
    rw [show j + 1 = 1 + j by omega, IterateAdd]
    rfl
  rw [hstep] at hj
  exact h (j + 1) hj

/-- A division-free orbit is the affine recursion at every time. -/
theorem NeverDividesIterateAffine (p : Parameters) (n : ℤ) (h : NeverDivides p n) (j : ℕ) :
    Iterate (RawStep p) j n = p.Q ^ j * n + p.C * TrapSum p.Q j := by
  induction j with
  | zero => {
      simp [Iterate, TrapSum]
    }
  | succ j ih => {
      have hstep : Iterate (RawStep p) (j + 1) n = RawStep p (Iterate (RawStep p) j n) :=
        rfl
      have haffine : RawStep p (Iterate (RawStep p) j n) =
          p.Q * Iterate (RawStep p) j n + p.C := RawStepAffine p _ (h j)
      rw [hstep, haffine, ih, TrapSumRec]
      ring
    }

/-- With multiplier zero a division-free orbit is at the fixed point `c`. -/
theorem TrapZeroConstant (p : Parameters) (n : ℤ) (h : NeverDivides p n) (hq : p.Q = 0)
    (j : ℕ) (hj : 1 ≤ j) : Iterate (RawStep p) j n = p.C := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [NeverDividesIterateAffine p n h (k + 1), hq, TrapSumZero k]
  ring

/-- With multiplier zero the offset `c` is itself a nondivisible fixed point. -/
theorem TrapZeroFixed (p : Parameters) (n : ℤ) (h : NeverDivides p n) (hq : p.Q = 0) :
    RawStep p p.C = p.C := by
  have hnd : ¬ p.D ∣ p.C := by
    have h1 := h 1
    rw [NeverDividesIterateAffine p n h 1, hq, TrapSumZero 0] at h1
    simpa using h1
  rw [RawStepAffine p p.C hnd, hq]
  ring

/-- With unit multiplier a division-free orbit is a nonzero translation. -/
theorem TrapOneTranslation (p : Parameters) (n : ℤ) (h : NeverDivides p n) (hq : p.Q = 1)
    (j : ℕ) : Iterate (RawStep p) j n = n + (j : ℤ) * p.C := by
  rw [NeverDividesIterateAffine p n h j, hq, TrapSumOne]
  ring

/-- Every integer is exceeded by a natural number. -/
theorem TrapExistsNatAbove (k : ℤ) : ∃ j : ℕ, k < (j : ℤ) := by
  refine ⟨k.natAbs + 1, ?_⟩
  have h : k ≤ (k.natAbs : ℤ) := Int.le_natAbs
  simp only [Nat.cast_add, Nat.cast_one]
  omega

/-- A unit multiplier with nonzero offset escapes in absolute value. -/
theorem TrapOneUnbounded (p : Parameters) (n : ℤ) (h : NeverDivides p n) (hq : p.Q = 1)
    (hc : p.C ≠ 0) (R : ℤ) : ∃ j : ℕ, R < |Iterate (RawStep p) j n| := by
  have hC : (1 : ℤ) ≤ |p.C| := Int.one_le_abs hc
  obtain ⟨j, hj⟩ := TrapExistsNatAbove (|n| + R)
  refine ⟨j, ?_⟩
  rw [TrapOneTranslation p n h hq j]
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
  have hjc : (j : ℤ) ≤ |(j : ℤ) * p.C| := by
    have hmul : (j : ℤ) ≤ (j : ℤ) * |p.C| := by
      have := Int.mul_le_mul_of_nonneg_left hC hj0
      rwa [mul_one] at this
    simpa only [abs_mul, abs_of_nonneg hj0] using hmul
  have htri : |(j : ℤ) * p.C| ≤ |n + (j : ℤ) * p.C| + |n| := by
    have hsplit : n + (j : ℤ) * p.C + -n = (j : ℤ) * p.C := by ring
    have := abs_add_le (n + (j : ℤ) * p.C) (-n)
    rwa [hsplit, abs_neg] at this
  omega

/-- The negative unit multiplier returns to the seed after an even number of steps. -/
theorem TrapNegOneEven (p : Parameters) (n : ℤ) (h : NeverDivides p n) (hq : p.Q = -1)
    (j : ℕ) : Iterate (RawStep p) (2 * j) n = n := by
  rw [NeverDividesIterateAffine p n h (2 * j), hq, TrapSumNegOneEven j]
  rw [show (-1 : ℤ) ^ (2 * j) = 1 by rw [pow_mul]; norm_num]
  ring

/-- The negative unit multiplier maps the seed to `c - n` after an odd number of steps. -/
theorem TrapNegOneOdd (p : Parameters) (n : ℤ) (h : NeverDivides p n) (hq : p.Q = -1)
    (j : ℕ) : Iterate (RawStep p) (2 * j + 1) n = p.C - n := by
  rw [NeverDividesIterateAffine p n h (2 * j + 1), hq, TrapSumNegOneOdd j]
  rw [show (-1 : ℤ) ^ (2 * j + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
  ring

/-- The reflection `n, c - n` is a genuine two-cycle when the two states differ. -/
theorem TrapNegOneTwoCycle (p : Parameters) (n : ℤ) (h : NeverDivides p n) (hq : p.Q = -1) :
    RawStep p n = p.C - n ∧ RawStep p (p.C - n) = n := by
  have h0 : RawStep p n = p.C - n := by
    rw [RawStepAffine p n (h 0), hq]
    ring
  have hone : Iterate (RawStep p) 1 n = p.C - n := by
    rw [NeverDividesIterateAffine p n h 1, hq]
    rw [show TrapSum (-1) 1 = 1 from TrapSumNegOneOdd 0]
    ring
  have hnd : ¬ p.D ∣ p.C - n := by
    have h1 := h 1
    rwa [hone] at h1
  have h1 : RawStep p (p.C - n) = n := by
    rw [RawStepAffine p (p.C - n) hnd, hq]
    ring
  exact ⟨h0, h1⟩

/-- A nondivisible state is fixed exactly on the affine fixed-point equation. -/
theorem TrapFixedIff (p : Parameters) (n : ℤ) (h : ¬ p.D ∣ n) :
    RawStep p n = n ↔ (p.Q - 1) * n + p.C = 0 := by
  rw [RawStepAffine p n h]
  constructor
  · intro heq
    have hid : (p.Q - 1) * n + p.C = p.Q * n + p.C - n := by ring
    rw [hid, heq]
    ring
  · intro heq
    have hid : p.Q * n + p.C = (p.Q - 1) * n + p.C + n := by ring
    rw [hid, heq]
    ring

/-- An expanding multiplier with a nonfixed state escapes in absolute value. -/
theorem TrapExpandingEscape (p : Parameters) (n : ℤ) (h : NeverDivides p n) (hQ : 2 ≤ |p.Q|)
    (hne : (p.Q - 1) * n + p.C ≠ 0) (R : ℤ) : ∃ j : ℕ, R < |Iterate (RawStep p) j n| := by
  have hDabs : (1 : ℤ) ≤ |(p.Q - 1) * n + p.C| := Int.one_le_abs hne
  obtain ⟨j, hj⟩ := TrapExistsNatAbove (|p.C| + |p.Q - 1| * (R + 1) - 1)
  refine ⟨j, ?_⟩
  have hkey : (p.Q - 1) * Iterate (RawStep p) j n
      = p.Q ^ j * ((p.Q - 1) * n + p.C) + -p.C := by
    rw [NeverDividesIterateAffine p n h j]
    calc (p.Q - 1) * (p.Q ^ j * n + p.C * TrapSum p.Q j)
        = p.Q ^ j * ((p.Q - 1) * n) + p.C * ((p.Q - 1) * TrapSum p.Q j) := by ring
      _ = p.Q ^ j * ((p.Q - 1) * n) + p.C * (p.Q ^ j - 1) := by rw [TrapSumMulSubOne]
      _ = p.Q ^ j * ((p.Q - 1) * n + p.C) + -p.C := by ring
  have hpow : (j : ℤ) + 1 ≤ |p.Q| ^ j := by
    have h2 : (2 : ℤ) ^ j ≤ |p.Q| ^ j := pow_le_pow_left₀ (by norm_num) hQ j
    have hj' : j + 1 ≤ 2 ^ j := by
      have := Nat.lt_two_pow_self (n := j)
      omega
    have hcast : ((j + 1 : ℕ) : ℤ) ≤ (2 : ℤ) ^ j := by exact_mod_cast hj'
    simpa using hcast.trans h2
  have hkeyabs : |(p.Q - 1) * Iterate (RawStep p) j n|
      = |p.Q - 1| * |Iterate (RawStep p) j n| := by
    rw [abs_mul]
  have htri : |p.Q ^ j * ((p.Q - 1) * n + p.C)| ≤
      |p.Q ^ j * ((p.Q - 1) * n + p.C) + -p.C| + |p.C| := by
    have hsplit : p.Q ^ j * ((p.Q - 1) * n + p.C) + -p.C + p.C
        = p.Q ^ j * ((p.Q - 1) * n + p.C) := by ring
    have := abs_add_le (p.Q ^ j * ((p.Q - 1) * n + p.C) + -p.C) p.C
    rwa [hsplit] at this
  have hmulabs : |p.Q ^ j * ((p.Q - 1) * n + p.C)|
      = |p.Q| ^ j * |(p.Q - 1) * n + p.C| := by
    rw [abs_mul, abs_pow]
  have hge : (j : ℤ) + 1 ≤ |p.Q ^ j * ((p.Q - 1) * n + p.C)| := by
    rw [hmulabs]
    have hmul := Int.mul_le_mul hpow hDabs (by norm_num) (pow_nonneg (abs_nonneg _) j)
    simpa using hmul
  have hbig : |p.Q - 1| * (R + 1) < (j : ℤ) + 1 - |p.C| := by omega
  have htarget : |p.Q - 1| * (R + 1) < |p.Q - 1| * |Iterate (RawStep p) j n| := by
    rw [← hkeyabs, hkey]
    omega
  have hnonneg : (0 : ℤ) ≤ |p.Q - 1| := abs_nonneg _
  have hfinal := lt_of_mul_lt_mul_left htarget hnonneg
  omega

/-- The residue walk of the affine branch on `ℤ/mℤ`, with `m` the absolute divisor. -/
def ResidueStepZ (p : Parameters) : ZMod p.D.natAbs → ZMod p.D.natAbs :=
  fun r => (p.Q : ZMod p.D.natAbs) * r + (p.C : ZMod p.D.natAbs)

/-- Along a division-free prefix the residue walk is the cast of the raw orbit. -/
theorem CastIterateOfPrefix (p : Parameters) (n : ℤ) (j : ℕ)
    (h : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n) :
    ((Iterate (RawStep p) j n : ℤ) : ZMod p.D.natAbs)
      = Iterate (ResidueStepZ p) j ((n : ℤ) : ZMod p.D.natAbs) := by
  revert h
  induction j with
  | zero => {
      intro h
      rfl
    }
  | succ j ih => {
      intro h
      have hj : ¬ p.D ∣ Iterate (RawStep p) j n := h j (Nat.lt_succ_self j)
      have hprev : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n :=
        fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self j))
      have hstep : Iterate (RawStep p) (j + 1) n = RawStep p (Iterate (RawStep p) j n) := rfl
      have hcast : ((RawStep p (Iterate (RawStep p) j n) : ℤ) : ZMod p.D.natAbs)
          = ResidueStepZ p (((Iterate (RawStep p) j n : ℤ)) : ZMod p.D.natAbs) := by
        rw [RawStepAffine p _ hj, ResidueStepZ, Int.cast_add, Int.cast_mul]
      rw [hstep, hcast, ih hprev]
      rfl
    }

/-- Along a division-free orbit the residue walk is the cast of the raw orbit. -/
theorem NeverDividesCastIterate (p : Parameters) (n : ℤ) (h : NeverDivides p n) (j : ℕ) :
    ((Iterate (RawStep p) j n : ℤ) : ZMod p.D.natAbs)
      = Iterate (ResidueStepZ p) j ((n : ℤ) : ZMod p.D.natAbs) :=
  CastIterateOfPrefix p n j fun i _ => h i

/-- A raw orbit is division-free exactly when its residue walk avoids the zero class. -/
theorem ResidueAvoidsZeroIffNeverDivides (p : Parameters) (n : ℤ) :
    NeverDivides p n ↔
      ∀ j : ℕ, Iterate (ResidueStepZ p) j ((n : ℤ) : ZMod p.D.natAbs) ≠ 0 := by
  constructor
  · intro h j hzero
    have hcast := NeverDividesCastIterate p n h j
    have hzero' : ((Iterate (RawStep p) j n : ℤ) : ZMod p.D.natAbs) = 0 := by
      rw [hcast]
      exact hzero
    exact h j (Int.natAbs_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero'))
  · intro h
    have hmain : ∀ j : ℕ, ¬ p.D ∣ Iterate (RawStep p) j n := by
      intro j
      refine Nat.strong_induction_on j ?_
      intro j ih hdvd
      have hprefix : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n := fun i hi => ih i hi
      have hcast := CastIterateOfPrefix p n j hprefix
      have hzero : ((Iterate (RawStep p) j n : ℤ) : ZMod p.D.natAbs) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natAbs_dvd.mpr hdvd)
      rw [hcast] at hzero
      exact h j hzero
    exact hmain

end GeneralizedCollatz
