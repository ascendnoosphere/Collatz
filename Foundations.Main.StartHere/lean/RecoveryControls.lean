import AffineWords
import GuardedRecovery
import Mathlib.Tactic.NormNum

/-!
Raw cycles and failures of rational-word legality.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The classical raw parameters use one division, not the shortcut clock. -/
def ClassicalParameters : Parameters where
  Q := 3
  C := 1
  D := 2
  DAdmissible := by norm_num

/-- The signed divisor retains its orientation on both division events. -/
def AbsorptionControl : Parameters where
  Q := 2
  C := 2
  D := -2
  DAdmissible := by norm_num

/-- The signed raw orbit `1,4,-2,1` is closed and never has to enter zero. -/
theorem NegativeDivisorCycle :
    ExecuteWord AbsorptionControl [.Affine, .Divide, .Divide] 1 = some 1 := by
  norm_num [ExecuteWord, PartialThen, PartialIdentity, ExecuteLetter, AbsorptionControl]

/-- Every iterate stays in the three-element nonzero cycle. -/
theorem NegativeDivisorOrbit (k : ℕ) :
    Iterate (RawStep AbsorptionControl) k 1 = 1 ∨
      Iterate (RawStep AbsorptionControl) k 1 = 4 ∨
      Iterate (RawStep AbsorptionControl) k 1 = -2 := by
  induction k with
  | zero => {
      simp [Iterate]
    }
  | succ k ih => {
      simp only [Iterate]
      rcases ih with h | h | h
      · rw [h]
        norm_num [RawStep, AbsorptionControl]
      · rw [h]
        norm_num [RawStep, AbsorptionControl]
      · rw [h]
        norm_num [RawStep, AbsorptionControl]
    }

/-- No step of the signed cycle reaches the fixed point zero. -/
theorem NegativeDivisorNeverZero (k : ℕ) :
    Iterate (RawStep AbsorptionControl) k 1 ≠ 0 := by
  intro hz
  rcases NegativeDivisorOrbit k with h | h | h
  · rw [hz] at h
    norm_num at h
  · rw [hz] at h
    norm_num at h
  · rw [hz] at h
    norm_num at h

/-- The zero-exponent relaxation has fixed point one even though its prescribed word is illegal. -/
theorem RelaxedWordFixedPoint :
    RationalAction (ExponentWord 3 1 2 (by norm_num) [0, 0, 3, 4]) 1 = 1 := by
  norm_num [ExponentWord, ExponentLetter, AffineThen, EmptyAffine, RationalAction]

/-- Expanding that relaxed word exposes the illegal second affine instruction. -/
theorem RelaxedWordIllegal :
    ExecuteWord ClassicalParameters
      [.Affine, .Affine, .Affine, .Divide, .Divide, .Divide,
        .Affine, .Divide, .Divide, .Divide, .Divide] 1 = none := by
  norm_num [ExecuteWord, PartialThen, PartialIdentity, ExecuteLetter, ClassicalParameters]

/-- These parameters retain the additive term in the raw and exponent-word maps. -/
def OffsetParameters : Parameters where
  Q := 3
  C := 5
  D := 2
  DAdmissible := by norm_num

/-- The positive raw cycle is `5,20,10,5`, with all three guards satisfied. -/
theorem OffsetRawCycle :
    ExecuteWord OffsetParameters [.Affine, .Divide, .Divide] 5 = some 5 := by
  norm_num [ExecuteWord, PartialThen, PartialIdentity, ExecuteLetter, OffsetParameters]

/-- The generalized offset `c=5` produces fixed point five for exponent two. -/
theorem GeneralizedOffsetControl :
    RationalAction (ExponentWord 3 5 2 (by norm_num) [2]) 5 = 5 := by
  norm_num [ExponentWord, ExponentLetter, AffineThen, EmptyAffine, RationalAction]

/-- Silently replacing the additive parameter by one changes that fixed point equation. -/
theorem MissingOffsetRefuted :
    RationalAction (ExponentWord 3 1 2 (by norm_num) [2]) 5 ≠ 5 := by
  norm_num [ExponentWord, ExponentLetter, AffineThen, EmptyAffine, RationalAction]

/-- The signed offset-ray examples share `q=-5,d=-6` and retain the actual offset scale. -/
def SignedRayParameters (scale : ℤ) : Parameters where
  Q := -5
  C := 31 * scale
  D := -6
  DAdmissible := by norm_num

/-- The unscaled raw cycle has the prescribed affine-affine-division itinerary. -/
theorem SignedRayBase :
    ExecuteWord (SignedRayParameters 1) [.Affine, .Affine, .Divide] 4 = some 4 := by
  norm_num [ExecuteWord, PartialThen, PartialIdentity, ExecuteLetter, SignedRayParameters]

/-- Scale two preserves this particular word despite sharing a factor with the divisor. -/
theorem SignedRayNoncoprimeScale :
    ExecuteWord (SignedRayParameters 2) [.Affine, .Affine, .Divide] 8 = some 8 := by
  norm_num [ExecuteWord, PartialThen, PartialIdentity, ExecuteLetter, SignedRayParameters]

/-- Scale three makes the first affine letter illegal despite rational scaling. -/
theorem SignedRayScaleFailure :
    ExecuteWord (SignedRayParameters 3) [.Affine, .Affine, .Divide] 12 = none := by
  norm_num [ExecuteWord, PartialThen, PartialIdentity, ExecuteLetter, SignedRayParameters]

end GeneralizedCollatz
