/-
SPDX-License-Identifier: CC-BY-4.0
Finite-orbit polynomial models: exact agreement, different multipliers, and escape radius.
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace GeneralizedCollatz.ComplexPolynomials

open Polynomial

/-- The minimal polynomial preserving zero and the raw (3,-1,2) cycle 1,2. -/
noncomputable def Minus : ℂ[X] := C (-3 / 2) * X ^ 2 + C (7 / 2) * X

/-- A finite-node-vanishing perturbation makes the same cycle superattracting. -/
noncomputable def MinusCritical : ℂ[X] := C (1 / 2) * X ^ 3 - C 3 * X ^ 2 + C (9 / 2) * X

/-- This cubic preserves zero and the raw (3,1,2) cycle 1,4,2. -/
noncomputable def Plus : ℂ[X] := C (7 / 6) * X ^ 3 - C 7 * X ^ 2 + C (59 / 6) * X

/-- The same three-cycle can have a zero multiplier in another finite-node model. -/
noncomputable def PlusCritical : ℂ[X] :=
  C (2 / 9) * X ^ 4 - C (7 / 18) * X ^ 3 - C (35 / 9) * X ^ 2 + C (145 / 18) * X

/-- Both minus models recover all three specified raw lattice values exactly. -/
theorem MinusNodes :
    Minus.eval 0 = 0 ∧ Minus.eval 1 = 2 ∧ Minus.eval 2 = 1 ∧
      MinusCritical.eval 0 = 0 ∧ MinusCritical.eval 1 = 2 ∧ MinusCritical.eval 2 = 1 := by
  norm_num [Minus, MinusCritical]

/-- Both plus models recover all four specified raw lattice values exactly. -/
theorem PlusNodes :
    Plus.eval 0 = 0 ∧ Plus.eval 1 = 4 ∧ Plus.eval 4 = 2 ∧ Plus.eval 2 = 1 ∧
      PlusCritical.eval 0 = 0 ∧ PlusCritical.eval 1 = 4 ∧
      PlusCritical.eval 4 = 2 ∧ PlusCritical.eval 2 = 1 := by
  norm_num [Plus, PlusCritical]

/-- These are finite-node models, not extensions of the raw map on all integers. -/
theorem FiniteAgreementOnly :
    Minus.eval 3 = -3 ∧ MinusCritical.eval 3 = 0 ∧ Plus.eval 3 = -2 ∧
      PlusCritical.eval 3 = -10 / 3 := by
  norm_num [Minus, MinusCritical, Plus, PlusCritical]

/-- Derivative evaluation is the actual complex derivative of every polynomial model. -/
theorem ModelDerivative (p : ℂ[X]) (z : ℂ) :
    HasDerivAt (fun w : ℂ => p.eval w) (p.derivative.eval z) z := p.hasDerivAt z

/-- Preserving a two-cycle's values does not preserve its complex stability multiplier. -/
theorem MinusMultipliers :
    Minus.derivative.eval 1 * Minus.derivative.eval 2 = -5 / 4 ∧
      MinusCritical.derivative.eval 1 * MinusCritical.derivative.eval 2 = 0 := by
  norm_num [Minus, MinusCritical, derivative_add, derivative_sub, derivative_mul,
    derivative_pow]

/-- Preserving a three-cycle likewise permits repelling and superattracting models. -/
theorem PlusMultipliers :
    Plus.derivative.eval 1 * Plus.derivative.eval 4 * Plus.derivative.eval 2 = 1475 / 54 ∧
      PlusCritical.derivative.eval 1 * PlusCritical.derivative.eval 4 *
        PlusCritical.derivative.eval 2 = 0 := by
  norm_num [Plus, PlusCritical, derivative_add, derivative_sub, derivative_mul,
    derivative_pow]

/-- Reverse triangle inequality isolates a leading term without losing its sign. -/
theorem LeadingBound (a b z : ℂ) (k : ℕ) :
    ‖a‖ * ‖z‖ ^ k ≤ ‖a * z ^ k + b‖ + ‖b‖ := by
  calc
    _ = ‖a * z ^ k‖ := by rw [norm_mul, norm_pow]
    _ = ‖(a * z ^ k + b) - b‖ := by congr 1; ring
    _ ≤ _ := norm_sub_le _ _

/-- The quadratic minus model expands by at least two outside the common radius eight. -/
theorem MinusGrowth (z : ℂ) (hz : 8 ≤ ‖z‖) : 2 * ‖z‖ ≤ ‖Minus.eval z‖ := by
  have h := LeadingBound (-3 / 2) (7 / 2) z 1
  norm_num [norm_div] at h
  have heq : Minus.eval z = z * ((-3 / 2) * z + 7 / 2) := by
    simp [Minus]
    ring
  rw [heq, norm_mul]
  have hg : 2 ≤ ‖-(3 / 2 * z) + 7 / 2‖ := by nlinarith
  have heq2 : (-3 / 2 : ℂ) * z = -(3 / 2 * z) := by ring
  rw [heq2]
  nlinarith [norm_nonneg z]

/-- The cubic minus model has the same escape radius despite different basin stability. -/
theorem MinusCriticalGrowth (z : ℂ) (hz : 8 ≤ ‖z‖) :
    2 * ‖z‖ ≤ ‖MinusCritical.eval z‖ := by
  have h := LeadingBound (1 / 2) (-3 * z + 9 / 2) z 2
  have ht := norm_add_le (-3 * z) (9 / 2 : ℂ)
  norm_num [norm_mul, norm_div] at h ht
  have hr := mul_nonneg (sub_nonneg.mpr hz) (norm_nonneg z)
  have hg : 2 ≤ ‖(1 / 2 : ℂ) * z ^ 2 + (-(3 * z) + 9 / 2)‖ := by nlinarith
  have heq : MinusCritical.eval z = z * ((1 / 2) * z ^ 2 + (-(3 * z) + 9 / 2)) := by
    simp [MinusCritical]
    ring
  rw [heq, norm_mul]
  nlinarith [norm_nonneg z]

/-- The plus cubic is also expanding beyond radius eight. -/
theorem PlusGrowth (z : ℂ) (hz : 8 ≤ ‖z‖) : 2 * ‖z‖ ≤ ‖Plus.eval z‖ := by
  have h := LeadingBound (7 / 6) (-7 * z + 59 / 6) z 2
  have ht := norm_add_le (-7 * z) (59 / 6 : ℂ)
  norm_num [norm_mul, norm_div] at h ht
  have hr := mul_nonneg (sub_nonneg.mpr hz) (norm_nonneg z)
  have hg : 2 ≤ ‖(7 / 6 : ℂ) * z ^ 2 + (-(7 * z) + 59 / 6)‖ := by nlinarith
  have heq : Plus.eval z = z * ((7 / 6) * z ^ 2 + (-(7 * z) + 59 / 6)) := by
    simp [Plus]
    ring
  rw [heq, norm_mul]
  nlinarith [norm_nonneg z]

/-- The quartic perturbation retains a proved radius, not an arbitrary numerical cutoff. -/
theorem PlusCriticalGrowth (z : ℂ) (hz : 8 ≤ ‖z‖) :
    2 * ‖z‖ ≤ ‖PlusCritical.eval z‖ := by
  let b : ℂ := (-7 / 18) * z ^ 2 + (-35 / 9) * z + 145 / 18
  have h := LeadingBound (2 / 9) b z 3
  have ht : ‖b‖ ≤ (7 / 18 : ℝ) * ‖z‖ ^ 2 + (35 / 9 : ℝ) * ‖z‖ + 145 / 18 := by
    calc
      ‖b‖ ≤ ‖(-7 / 18 : ℂ) * z ^ 2 + (-35 / 9) * z‖ + ‖(145 / 18 : ℂ)‖ :=
        norm_add_le _ _
      _ ≤ ‖(-7 / 18 : ℂ) * z ^ 2‖ + ‖(-35 / 9 : ℂ) * z‖ +
          ‖(145 / 18 : ℂ)‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by norm_num [norm_mul, norm_pow, norm_div]
  norm_num [norm_div] at h
  have hr2 := mul_nonneg (sub_nonneg.mpr hz) (norm_nonneg z)
  have hr3 := mul_nonneg (sub_nonneg.mpr hz) (sq_nonneg ‖z‖)
  have hg : 2 ≤ ‖(2 / 9 : ℂ) * z ^ 3 + b‖ := by nlinarith
  have heq : PlusCritical.eval z = z * ((2 / 9) * z ^ 3 + b) := by
    simp [PlusCritical, b]
    ring
  rw [heq, norm_mul]
  nlinarith [norm_nonneg z]

/-- The recursive clock supplies exact reconstruction for every chosen complex model. -/
def Iterate (f : ℂ → ℂ) (z : ℂ) : ℕ → ℂ
  | 0 => z
  | j + 1 => f (Iterate f z j)

/-- The proved radius implies full-sequence exponential escape, not merely one large value. -/
theorem OutsideEightPowers (f : ℂ → ℂ)
    (hf : ∀ z : ℂ, 8 ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖f z‖) (z : ℂ) (hz : 8 ≤ ‖z‖) (j : ℕ) :
    (2 : ℝ) ^ j * ‖z‖ ≤ ‖Iterate f z j‖ := by
  induction j with
  | zero => { simp [Iterate] }
  | succ j ih => {
      have hp : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hr : 8 ≤ ‖Iterate f z j‖ := by nlinarith
      have hg := hf (Iterate f z j) hr
      simp only [Iterate, pow_succ]
      nlinarith
    }

end GeneralizedCollatz.ComplexPolynomials
