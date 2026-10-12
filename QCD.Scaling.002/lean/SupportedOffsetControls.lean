-- SPDX-License-Identifier: CC-BY-4.0
import SupportedOffsetAbsorption
import SupportedOffsetFactor
import Mathlib.Tactic.IntervalCases

/-! Concrete proper-factor and full-raw-period controls for offset normalization. -/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- A proper supported factor need not make the entire offset divide any power. -/
theorem SupportedOffsetWholePowerFails (k : ℕ) : ¬ (55 : ℤ) ∣ (11 : ℤ) ^ k := by
  intro divides
  have fiveDivides : (5 : ℤ) ∣ (11 : ℤ) ^ k := dvd_trans (by norm_num) divides
  have naturalDivides : 5 ∣ (11 : ℕ) ^ k := by
    simpa [Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr fiveDivides
  have impossible := PrimeDivisorOfPower 5 11 k (by decide) naturalDivides
  norm_num at impossible

/-- The two example odd-state pairs use this raw core, not a two-step raw map. -/
def SupportedOffsetExampleCore : Parameters where
  Q := 181
  C := 1
  D := 2
  DAdmissible := by decide

/-- All sixteen smaller positive clocks are excluded for the first seventeen-step return. -/
theorem SupportedOffsetCoreCycle27 :
    PrimitiveReturn (RawStep SupportedOffsetExampleCore) 27 17 := by
  refine ⟨by decide, ?_, ?_⟩
  · norm_num [Iterate, RawStep, SupportedOffsetExampleCore]
  · intro r positive returned
    by_contra notLeast
    have below : r < 17 := by omega
    interval_cases r <;> norm_num [Iterate, RawStep, SupportedOffsetExampleCore] at returned

/-- The second odd-state pair also has raw period seventeen against every shorter return. -/
theorem SupportedOffsetCoreCycle35 :
    PrimitiveReturn (RawStep SupportedOffsetExampleCore) 35 17 := by
  refine ⟨by decide, ?_, ?_⟩
  · norm_num [Iterate, RawStep, SupportedOffsetExampleCore]
  · intro r positive returned
    by_contra notLeast
    have below : r < 17 := by omega
    interval_cases r <;> norm_num [Iterate, RawStep, SupportedOffsetExampleCore] at returned

/-- The actual large offset lifts either core control with its full primitive raw clock. -/
theorem SupportedOffsetExampleCycleLift (n : ℤ) (h : ℕ)
    (primitive : PrimitiveReturn (RawStep SupportedOffsetExampleCore) n h) :
    PrimitiveReturn
      (RawStep (ScaleParameters SupportedOffsetExampleCore ((181 : ℤ) ^ 20)))
      ((181 : ℤ) ^ 20 * n) h := by
  have coprime : Int.gcd ((181 : ℤ) ^ 20) 2 = 1 := by
    have base : Nat.Coprime 181 2 := by decide
    change Nat.Coprime (((181 : ℤ) ^ 20).natAbs) 2
    rw [Int.natAbs_pow]
    exact base.pow_left 20
  have relative : RelativeOffsetParameters
      (ScaleParameters SupportedOffsetExampleCore ((181 : ℤ) ^ 20))
      ((181 : ℤ) ^ 20) = SupportedOffsetExampleCore := by
    simp [RelativeOffsetParameters, ScaleParameters, SupportedOffsetExampleCore]
  have offsetDivides : (181 : ℤ) ^ 20 ∣
      (ScaleParameters SupportedOffsetExampleCore ((181 : ℤ) ^ 20)).C := by
    simp [ScaleParameters, SupportedOffsetExampleCore]
  have returns := RelativeOffsetPrimitiveReturnIff
    (ScaleParameters SupportedOffsetExampleCore ((181 : ℤ) ^ 20))
    ((181 : ℤ) ^ 20) n coprime offsetDivides h
  rw [relative] at returns
  exact returns.mpr primitive

end GeneralizedCollatz
