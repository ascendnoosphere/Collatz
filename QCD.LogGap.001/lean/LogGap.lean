-- SPDX-License-Identifier: CC-BY-4.0

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum

/-!
Logarithmic gap of one block of eight positive real factors.

The natural logarithm satisfies `log (256 / 243) = 8 * log 2 - 5 * log 3`.
If the product `P` of eight positive factors has logarithmic deficit at least
this gap, then `P ≤ 243 / 256`, hence `P < 1`. Eight factors each at most one
eighth of the gap below `1` meet the same deficit. The constant is achieved by
a positive block. No hypothesis is claimed for the classical Collatz branches,
and no orbit is claimed to reach `1`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The natural logarithm converts `2 ^ 8 / 3 ^ 5` into an integer combination. -/
theorem LogGapIdentity :
    Real.log ((256 : ℝ) / 243) =
      (8 : ℝ) * Real.log 2 - (5 : ℝ) * Real.log 3 := by
  have h256 : (256 : ℝ) ≠ 0 := by norm_num
  have h243 : (243 : ℝ) ≠ 0 := by norm_num
  have hpow2 : (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
  have hpow3 : (243 : ℝ) = (3 : ℝ) ^ 5 := by norm_num
  rw [Real.log_div h256 h243, hpow2, hpow3, Real.log_pow, Real.log_pow]
  norm_cast

/-- Inversion negates the logarithm and swaps the gap ratio with its reciprocal. -/
theorem GapReciprocal :
    Real.log ((243 : ℝ) / 256) = -Real.log ((256 : ℝ) / 243) := by
  have h243 : (243 : ℝ) ≠ 0 := by norm_num
  have h256 : (256 : ℝ) ≠ 0 := by norm_num
  rw [Real.log_div h243 h256, Real.log_div h256 h243, neg_sub]

/-- The threshold product has logarithmic deficit exactly equal to the gap. -/
theorem GapThreshold :
    -Real.log ((243 : ℝ) / 256) = Real.log ((256 : ℝ) / 243) := by
  rw [GapReciprocal, neg_neg]

/-- `243 < 256`, so the gap ratio exceeds `1` and the logarithm is positive. -/
theorem GapPositive : 0 < Real.log ((256 : ℝ) / 243) := by
  have h243 : (0 : ℝ) < 243 := by norm_num
  have hlt : (243 : ℝ) < 256 := by norm_num
  have hratio : 1 < (256 : ℝ) / 243 := (one_lt_div h243).mpr hlt
  exact Real.log_pos hratio

/-- One eighth of the gap is the reference drift `log 2 - (5 / 8) * log 3`. -/
theorem StepGap :
    Real.log 2 - (5 / 8) * Real.log 3 =
      Real.log ((256 : ℝ) / 243) / 8 := by
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  rw [LogGapIdentity]
  refine (eq_div_iff h8).mpr ?_
  calc
    (Real.log 2 - (5 / 8) * Real.log 3) * 8
      = Real.log 2 * 8 - ((5 / 8) * Real.log 3) * 8 := by rw [sub_mul]
    _ = 8 * Real.log 2 - ((5 / 8) * Real.log 3) * 8 := by
      rw [mul_comm (Real.log 2) 8]
    _ = 8 * Real.log 2 - (5 / 8) * (Real.log 3 * 8) := by rw [mul_assoc]
    _ = 8 * Real.log 2 - (5 / 8) * (8 * Real.log 3) := by
      rw [mul_comm (Real.log 3) 8]
    _ = 8 * Real.log 2 - ((5 / 8) * 8) * Real.log 3 := by rw [← mul_assoc]
    _ = 8 * Real.log 2 - 5 * Real.log 3 := by rw [div_mul_cancel₀ _ h8]

/-- The one-step ceiling is the negative of the reference drift. -/
theorem StepBound :
    -Real.log ((256 : ℝ) / 243) / 8 =
      (5 / 8) * Real.log 3 - Real.log 2 := by
  calc
    -Real.log ((256 : ℝ) / 243) / 8
      = -(Real.log ((256 : ℝ) / 243) / 8) := by rw [neg_div]
    _ = -(Real.log 2 - (5 / 8) * Real.log 3) := by rw [← StepGap]
    _ = (5 / 8) * Real.log 3 - Real.log 2 := by rw [neg_sub]

/-- Product of one block of eight real factors. -/
def BlockProduct (r : Fin 8 → ℝ) : ℝ :=
  ∏ i : Fin 8, r i

/-- Positivity of every factor passes to the block product. -/
theorem BlockProductPos (r : Fin 8 → ℝ) (hpos : ∀ i : Fin 8, 0 < r i) :
    0 < BlockProduct r := by
  unfold BlockProduct
  exact Finset.prod_pos fun i _ => hpos i

/-- A deficit of at least the gap forces the product to be at most `243 / 256`. -/
theorem BlockContraction (r : Fin 8 → ℝ) (hpos : ∀ i : Fin 8, 0 < r i)
    (hgap : Real.log ((256 : ℝ) / 243) ≤ -Real.log (BlockProduct r)) :
    BlockProduct r ≤ (243 : ℝ) / 256 ∧ BlockProduct r < 1 := by
  have hP : 0 < BlockProduct r := BlockProductPos r hpos
  have hTarget : 0 < (243 : ℝ) / 256 := by norm_num
  have hlog : Real.log (BlockProduct r) ≤ Real.log ((243 : ℝ) / 256) := by
    calc
      Real.log (BlockProduct r) = -(-Real.log (BlockProduct r)) := by
        rw [neg_neg]
      _ ≤ -Real.log ((256 : ℝ) / 243) := neg_le_neg hgap
      _ = Real.log ((243 : ℝ) / 256) := by rw [← GapReciprocal]
  have hle : BlockProduct r ≤ (243 : ℝ) / 256 :=
    (Real.log_le_log_iff hP hTarget).mp hlog
  have hlt : (243 : ℝ) / 256 < 1 := (div_lt_one (by norm_num)).mpr (by norm_num)
  exact ⟨hle, lt_of_le_of_lt hle hlt⟩

/-- A strict logarithmic deficit forces a strict product bound. -/
theorem BlockContractionStrict (r : Fin 8 → ℝ)
    (hpos : ∀ i : Fin 8, 0 < r i)
    (hgap : Real.log ((256 : ℝ) / 243) < -Real.log (BlockProduct r)) :
    BlockProduct r < (243 : ℝ) / 256 := by
  have hP : 0 < BlockProduct r := BlockProductPos r hpos
  have hTarget : 0 < (243 : ℝ) / 256 := by norm_num
  have hlog : Real.log (BlockProduct r) < Real.log ((243 : ℝ) / 256) := by
    calc
      Real.log (BlockProduct r) = -(-Real.log (BlockProduct r)) := by
        rw [neg_neg]
      _ < -Real.log ((256 : ℝ) / 243) := neg_lt_neg hgap
      _ = Real.log ((243 : ℝ) / 256) := by rw [← GapReciprocal]
  exact (Real.log_lt_log_iff hP hTarget).mp hlog

/-- Eight factors, each at most one eighth of the gap below `1`, bound the block. -/
theorem EightStepContraction (r : Fin 8 → ℝ) (hpos : ∀ i : Fin 8, 0 < r i)
    (hstep : ∀ i : Fin 8,
      Real.log (r i) ≤ -Real.log ((256 : ℝ) / 243) / 8) :
    Real.log ((256 : ℝ) / 243) ≤ -Real.log (BlockProduct r) ∧
      BlockProduct r ≤ (243 : ℝ) / 256 ∧
      BlockProduct r < 1 ∧
      ∀ i : Fin 8, r i < 1 := by
  have hstepForm : ∀ i : Fin 8,
      Real.log (r i) ≤ (5 / 8) * Real.log 3 - Real.log 2 := by
    intro i
    rw [← StepBound]
    exact hstep i
  have hprodlog : Real.log (BlockProduct r) = ∑ i : Fin 8, Real.log (r i) := by
    unfold BlockProduct
    exact Real.log_prod fun i _ => (hpos i).ne'
  have hsum : (∑ i : Fin 8, Real.log (r i)) ≤
      ∑ _i : Fin 8, (-Real.log ((256 : ℝ) / 243) / 8) :=
    Finset.sum_le_sum fun i _ => hstep i
  have hconst : (∑ _i : Fin 8, (-Real.log ((256 : ℝ) / 243) / 8)) =
      -Real.log ((256 : ℝ) / 243) := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    exact mul_div_cancel₀ _ (by norm_num)
  have hlogle : Real.log (BlockProduct r) ≤ -Real.log ((256 : ℝ) / 243) := by
    rw [hprodlog]
    exact le_trans hsum (le_of_eq hconst)
  have hdef : Real.log ((256 : ℝ) / 243) ≤ -Real.log (BlockProduct r) := by
    calc
      Real.log ((256 : ℝ) / 243)
        = -(-Real.log ((256 : ℝ) / 243)) := by rw [neg_neg]
      _ ≤ -Real.log (BlockProduct r) := neg_le_neg hlogle
  have hblock := BlockContraction r hpos hdef
  have hbelow : ∀ i : Fin 8, r i < 1 := by
    intro i
    have hneg : (5 / 8) * Real.log 3 - Real.log 2 < 0 := by
      rw [← StepBound, neg_div]
      exact neg_lt_zero.mpr (div_pos GapPositive (by norm_num))
    have hlt : Real.log (r i) < 0 := lt_of_le_of_lt (hstepForm i) hneg
    exact (Real.log_neg_iff (hpos i)).mp hlt
  exact ⟨hdef, hblock.1, hblock.2, hbelow⟩

/-- The constant `243 / 256` is achieved by a positive block of length eight. -/
theorem BlockBoundSharp :
    ∃ r : Fin 8 → ℝ,
      (∀ i : Fin 8, 0 < r i) ∧
        BlockProduct r = (243 : ℝ) / 256 ∧
        -Real.log (BlockProduct r) = Real.log ((256 : ℝ) / 243) := by
  let r : Fin 8 → ℝ := fun i => if i = 0 then (243 : ℝ) / 256 else 1
  have hprod : BlockProduct r = (243 : ℝ) / 256 := by
    unfold BlockProduct
    refine (Finset.prod_eq_single_of_mem (0 : Fin 8)
      (Finset.mem_univ (0 : Fin 8)) ?_).trans ?_
    · intro b _ hb
      change (if b = 0 then (243 : ℝ) / 256 else 1) = 1
      rw [if_neg hb]
    · change (if (0 : Fin 8) = 0 then (243 : ℝ) / 256 else 1) =
        (243 : ℝ) / 256
      rw [if_pos rfl]
  refine ⟨r, ?_, hprod, ?_⟩
  · intro i
    by_cases hi : i = 0
    · change 0 < (if i = 0 then (243 : ℝ) / 256 else 1)
      rw [if_pos hi]
      norm_num
    · change 0 < (if i = 0 then (243 : ℝ) / 256 else 1)
      rw [if_neg hi]
      exact zero_lt_one
  · rw [hprod]
    exact GapThreshold

end GeneralizedCollatz
