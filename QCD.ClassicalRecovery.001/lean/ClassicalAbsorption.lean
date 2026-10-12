-- SPDX-License-Identifier: CC-BY-4.0
import GeneralizedScaling
import CompressionPeriods

/-!
Exact positive capture recovery and primitive raw cycles in the two-parameter
classical family. No classical all-positive capture hypothesis is proved here.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The common binary coefficient power and the absorbing ternary offset are independent. -/
def ClassicalAbsorptionParameters (a b : ℕ) : Parameters where
  Q := (2 : ℤ) ^ a * 3
  C := (2 : ℤ) ^ a * (3 : ℤ) ^ b
  D := 2
  DAdmissible := by decide

/-- Every ternary offset power is coprime to the binary raw divisor. -/
theorem ClassicalAbsorptionOffsetCoprime (b : ℕ) : Int.gcd ((3 : ℤ) ^ b) 2 = 1 := by
  exact Int.gcd_pow_left_of_gcd_eq_one (by decide : Int.gcd 3 2 = 1)

/-- A ternary scale is positive, including the exponent-zero scale one. -/
theorem ClassicalAbsorptionOffsetPositive (b : ℕ) : 0 < (3 : ℤ) ^ b := by
  exact pow_pos (by decide) b

/-- Binary division cannot hold at the designated odd target. -/
theorem ClassicalAbsorptionTargetOdd (b : ℕ) : ¬(2 : ℤ) ∣ (3 : ℤ) ^ b := by
  intro divisible
  have dividesGcd : (2 : ℤ) ∣ Int.gcd ((3 : ℤ) ^ b) 2 :=
    Int.dvd_coe_gcd divisible (dvd_refl _)
  rw [ClassicalAbsorptionOffsetCoprime b] at dividesGcd
  norm_num at dividesGcd

/-- The absorbing scale conjugates only the invariant ternary sublattice, with no clock change. -/
theorem ClassicalAbsorptionScale (a b : ℕ) :
    ScaleParameters (ClassicalAbsorptionParameters a 0) ((3 : ℤ) ^ b) =
      ClassicalAbsorptionParameters a b := by
  simp [ScaleParameters, ClassicalAbsorptionParameters, mul_comm]

/-- Removing the binary coefficient power leaves exactly the odd-offset map. -/
theorem ClassicalAbsorptionCompressed (a b : ℕ) :
    CompressedParameters (ClassicalAbsorptionParameters a b) 3 ((3 : ℤ) ^ b) =
      ClassicalAbsorptionParameters 0 b := by
  simp [CompressedParameters, ClassicalAbsorptionParameters]

/-- Normalizing the odd offset leaves the classical raw map, not its shortcut. -/
theorem ClassicalAbsorptionUnitOffset (b : ℕ) :
    UnitOffsetParameters (ClassicalAbsorptionParameters 0 b) = ClassicalParameters := by
  simp [UnitOffsetParameters, ClassicalAbsorptionParameters, ClassicalParameters]

/-- The odd singleton target reflects through every binary compression block. -/
theorem ClassicalAbsorptionCompressionCaptureIff (a b : ℕ) (n : ℤ) :
    (∃ r : ℕ, Iterate (RawStep (ClassicalAbsorptionParameters a b)) r n = (3 : ℤ) ^ b) ↔
      ∃ k : ℕ, Iterate (RawStep (ClassicalAbsorptionParameters 0 b)) k n = (3 : ℤ) ^ b := by
  have compression := CompressionCaptureIff (ClassicalAbsorptionParameters a b)
    3 ((3 : ℤ) ^ b) a rfl rfl (fun x => x = (3 : ℤ) ^ b) (by
      intro x divisible reached
      subst x
      exact False.elim (ClassicalAbsorptionTargetOdd b divisible)) n
  simpa only [ClassicalAbsorptionCompressed] using compression

/-- Every positive compressed orbit has a positive classical tail after at most b affine events. -/
theorem ClassicalAbsorptionCompressedTail (b : ℕ) (n : ℤ) (nPositive : 0 < n) :
    ∃ t : ℕ, ∃ m : ℤ, 0 < m ∧
      Iterate (RawStep (ClassicalAbsorptionParameters 0 b)) t n = (3 : ℤ) ^ b * m ∧
      AffineCount (ClassicalAbsorptionParameters 0 b) t n ≤ b ∧
      ∀ s : ℕ, Iterate (RawStep (ClassicalAbsorptionParameters 0 b)) (t + s) n =
        (3 : ℤ) ^ b * Iterate (RawStep ClassicalParameters) s m := by
  have tail := PositiveOffsetOneTail (ClassicalAbsorptionParameters 0 b)
    (by simpa [ClassicalAbsorptionParameters] using ClassicalAbsorptionOffsetCoprime b)
    (by norm_num [ClassicalAbsorptionParameters])
    (by simp [ClassicalAbsorptionParameters])
    (by norm_num [ClassicalAbsorptionParameters])
    b (by simp [ClassicalAbsorptionParameters]) n nPositive
  have offset : (ClassicalAbsorptionParameters 0 b).C = (3 : ℤ) ^ b := by
    simp [ClassicalAbsorptionParameters]
  simpa only [ClassicalAbsorptionUnitOffset, offset] using tail

/-- Finite compressed entry gives one common raw tail on the invariant ternary sublattice. -/
theorem ClassicalAbsorptionRawTail (a b : ℕ) (n : ℤ) (nPositive : 0 < n) :
    ∃ r : ℕ, ∃ m : ℤ, 0 < m ∧
      Iterate (RawStep (ClassicalAbsorptionParameters a b)) r n = (3 : ℤ) ^ b * m ∧
      ∀ s : ℕ, Iterate (RawStep (ClassicalAbsorptionParameters a b)) (r + s) n =
        (3 : ℤ) ^ b * Iterate (RawStep (ClassicalAbsorptionParameters a 0)) s m := by
  obtain ⟨t, m, mPositive, entered, _, _⟩ :=
    ClassicalAbsorptionCompressedTail b n nPositive
  let r := t + a * CompressionAffineCount (ClassicalAbsorptionParameters a b)
    3 ((3 : ℤ) ^ b) t n
  have rawEntry : Iterate (RawStep (ClassicalAbsorptionParameters a b)) r n =
      (3 : ℤ) ^ b * m := by
    rw [← CompressionIteratesAtExpandedTime (ClassicalAbsorptionParameters a b)
      3 ((3 : ℤ) ^ b) a rfl rfl, ClassicalAbsorptionCompressed]
    exact entered
  refine ⟨r, m, mPositive, rawEntry, ?_⟩
  intro s
  rw [IterateAdd, rawEntry]
  have scaled := ScalingIterates (ClassicalAbsorptionParameters a 0)
    ((3 : ℤ) ^ b) m (ClassicalAbsorptionOffsetCoprime b) s
  rw [ClassicalAbsorptionScale] at scaled
  exact scaled

/-- The source family has exactly the classical all-positive target-one obligation. -/
theorem ClassicalAbsorptionPositiveCaptureIff (a b : ℕ) :
    (∀ n : ℤ, 0 < n → ∃ r : ℕ,
      Iterate (RawStep (ClassicalAbsorptionParameters a b)) r n = (3 : ℤ) ^ b) ↔
      ∀ n : ℤ, 0 < n → ∃ r : ℕ, Iterate (RawStep ClassicalParameters) r n = 1 := by
  have normalized := PositiveOffsetTargetEquivalence (ClassicalAbsorptionParameters 0 b)
    (by simpa [ClassicalAbsorptionParameters] using ClassicalAbsorptionOffsetCoprime b)
    (by norm_num [ClassicalAbsorptionParameters])
    (by simp [ClassicalAbsorptionParameters])
    (by norm_num [ClassicalAbsorptionParameters])
    b (by simp [ClassicalAbsorptionParameters]) (fun x => x = (3 : ℤ) ^ b)
  have offset : (ClassicalAbsorptionParameters 0 b).C = (3 : ℤ) ^ b := by
    simp [ClassicalAbsorptionParameters]
  rw [ClassicalAbsorptionUnitOffset, offset] at normalized
  have cancel : ∀ x : ℤ, (3 : ℤ) ^ b * x = (3 : ℤ) ^ b ↔ x = 1 := by
    intro x
    constructor
    · intro equal
      apply mul_left_cancel₀ (ne_of_gt (ClassicalAbsorptionOffsetPositive b))
      simpa using equal
    · intro equal
      simp [equal]
  change (∀ n : ℤ, 0 < n → ∃ r : ℕ,
    (3 : ℤ) ^ b * Iterate (RawStep ClassicalParameters) r n = (3 : ℤ) ^ b) ↔
      ∀ n : ℤ, 0 < n → ∃ r : ℕ,
        Iterate (RawStep (ClassicalAbsorptionParameters 0 b)) r n = (3 : ℤ) ^ b at normalized
  simp_rw [cancel] at normalized
  constructor
  · intro captured
    apply normalized.mpr
    intro n nPositive
    exact (ClassicalAbsorptionCompressionCaptureIff a b n).mp (captured n nPositive)
  · intro captured n nPositive
    exact (ClassicalAbsorptionCompressionCaptureIff a b n).mpr
      (normalized.mp captured n nPositive)

/-- The designated odd state has one affine image with all binary division factors explicit. -/
theorem ClassicalAbsorptionCycleAffine (a b : ℕ) :
    RawStep (ClassicalAbsorptionParameters a b) ((3 : ℤ) ^ b) =
      (2 : ℤ) ^ (a + 2) * (3 : ℤ) ^ b := by
  simp only [RawStep, ClassicalAbsorptionParameters]
  rw [if_neg (ClassicalAbsorptionTargetOdd b), pow_add]
  ring

/-- Every division phase of the designated cycle is legal and uses the original raw clock. -/
theorem ClassicalAbsorptionCycleTrace (a b j : ℕ) (jBound : j ≤ a + 2) :
    Iterate (RawStep (ClassicalAbsorptionParameters a b)) (j + 1) ((3 : ℤ) ^ b) =
      (2 : ℤ) ^ (a + 2 - j) * (3 : ℤ) ^ b := by
  rw [← IterateFirst, ClassicalAbsorptionCycleAffine]
  exact PowerDivisionPrefix (ClassicalAbsorptionParameters a b) (a + 2) j
    ((3 : ℤ) ^ b) jBound

/-- No earlier positive raw return exists, so the designated period is exactly a+3. -/
theorem ClassicalAbsorptionPrimitiveCycle (a b : ℕ) :
    PrimitiveReturn (RawStep (ClassicalAbsorptionParameters a b)) ((3 : ℤ) ^ b) (a + 3) := by
  have scaleNonzero : (3 : ℤ) ^ b ≠ 0 := ne_of_gt (ClassicalAbsorptionOffsetPositive b)
  refine ⟨by omega, ?_, ?_⟩
  · have returned := ClassicalAbsorptionCycleTrace a b (a + 2) (Nat.le_refl _)
    simpa using returned
  · intro r rPositive returned
    by_contra earlier
    have jBound : r - 1 ≤ a + 2 := by omega
    have time : r - 1 + 1 = r := by omega
    have trace := ClassicalAbsorptionCycleTrace a b (r - 1) jBound
    rw [time, returned] at trace
    have powerOne : (2 : ℤ) ^ (a + 2 - (r - 1)) = 1 := by
      apply mul_right_cancel₀ scaleNonzero
      simpa using trace.symm
    have exponentPositive : 0 < a + 2 - (r - 1) := by omega
    have powerLarge : 1 < (2 : ℕ) ^ (a + 2 - (r - 1)) :=
      Nat.one_lt_pow (Nat.ne_of_gt exponentPositive) (by decide)
    have integerLarge : (1 : ℤ) < 2 ^ (a + 2 - (r - 1)) := by exact_mod_cast powerLarge
    omega

end GeneralizedCollatz
