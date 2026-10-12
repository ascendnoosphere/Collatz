/- SPDX-License-Identifier: CC-BY-4.0 -/
import SupportedOffsetAbsorption
import SupportedOffsetFactor

/-!
The computed gcd-only factor supplies the hypotheses of relative raw recovery.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The actual extracted factor is admissible and has a bounded power witness. -/
theorem ExtractedOffsetAdmissible (p : Parameters) (cNonzero : p.C ≠ 0)
    (coprime : Int.gcd p.C p.D = 1) :
    let factor := (SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1
    0 < factor ∧ (factor : ℤ) ∣ p.C ∧ Int.gcd (factor : ℤ) p.D = 1 ∧
      ∃ k : ℕ, k ≤ p.C.natAbs ∧ (factor : ℤ) ∣ p.Q ^ k := by
  have cPositive : 0 < p.C.natAbs := Int.natAbs_pos.mpr cNonzero
  obtain ⟨positive, _, product, _, k, bound, power⟩ :=
    SupportedOffsetPeelCertificate p.Q.natAbs p.C.natAbs cPositive
  have divides : (SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1 ∣ p.C.natAbs :=
    ⟨_, product.symm⟩
  have integerDivides :
      ((SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1 : ℤ) ∣ p.C := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa using divides
  have integerPower :
      ((SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1 : ℤ) ∣ p.Q ^ k := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa only [Int.natAbs_natCast, Int.natAbs_pow] using power
  have naturalCoprime : Nat.Coprime p.C.natAbs p.D.natAbs := coprime
  have factorCoprime :=
    SupportedOffsetPeelCoprime p.Q.natAbs p.C.natAbs p.D.natAbs cPositive naturalCoprime
  have integerCoprime : Int.gcd
      ((SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1 : ℤ) p.D = 1 := by
    simpa only [Int.gcd, Int.natAbs_natCast] using factorCoprime
  exact ⟨positive, integerDivides, integerCoprime, k, bound, integerPower⟩

/-- One computed factor and one power witness recover the same seed at every future raw time. -/
theorem ExtractedOffsetTail (p : Parameters) (cNonzero : p.C ≠ 0)
    (coprime : Int.gcd p.C p.D = 1) (n : ℤ) :
    let factor : ℤ := (SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1
    ∃ k t : ℕ, ∃ m : ℤ, k ≤ p.C.natAbs ∧ factor ∣ p.Q ^ k ∧
      Iterate (RawStep p) t n = factor * m ∧ AffineCount p t n ≤ k ∧
      ∀ r : ℕ, Iterate (RawStep p) (t + r) n =
        factor * Iterate (RawStep (RelativeOffsetParameters p factor)) r m := by
  obtain ⟨_, divides, factorCoprime, k, bound, power⟩ :=
    ExtractedOffsetAdmissible p cNonzero coprime
  obtain ⟨t, m, entry, budget, tail⟩ :=
    RelativeOffsetTail p _ factorCoprime divides k power n
  exact ⟨k, t, m, bound, power, entry, budget, tail⟩

/-- The extracted normalization gives the positive universal equivalence, not seedwise identity. -/
theorem ExtractedOffsetPositiveTargetIff (p : Parameters)
    (coprime : Int.gcd p.C p.D = 1) (qNonnegative : 0 ≤ p.Q)
    (cPositive : 0 < p.C) (dPositive : 0 < p.D) (target : ℤ → Prop) :
    let factor : ℤ := (SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1
    (∀ m : ℤ, 0 < m → ∃ r : ℕ,
      target (factor * Iterate (RawStep (RelativeOffsetParameters p factor)) r m)) ↔
      ∀ n : ℤ, 0 < n → ∃ t : ℕ, target (Iterate (RawStep p) t n) := by
  obtain ⟨positive, divides, factorCoprime, k, _, power⟩ :=
    ExtractedOffsetAdmissible p (ne_of_gt cPositive) coprime
  have integerPositive :
      0 < ((SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1 : ℤ) := by
    exact_mod_cast positive
  exact PositiveRelativeOffsetTargetEquivalence p _ integerPositive factorCoprime divides
    qNonnegative cPositive dPositive k power target

/-- Original cycles use the computed lattice, retaining all phases and primitive raw periods. -/
theorem ExtractedOffsetCycleRecovery (p : Parameters) (cNonzero : p.C ≠ 0)
    (coprime : Int.gcd p.C p.D = 1) (n : ℤ) (h : ℕ)
    (hPositive : 0 < h) (returned : Iterate (RawStep p) h n = n) :
    let factor : ℤ := (SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1
    ∃ m : ℤ, n = factor * m ∧
      (∀ r : ℕ, Iterate (RawStep p) r n =
        factor * Iterate (RawStep (RelativeOffsetParameters p factor)) r m) ∧
      (PrimitiveReturn (RawStep p) n h ↔
        PrimitiveReturn (RawStep (RelativeOffsetParameters p factor)) m h) := by
  obtain ⟨_, divides, factorCoprime, k, _, power⟩ :=
    ExtractedOffsetAdmissible p cNonzero coprime
  exact RelativeOffsetCycleRecovery p _ factorCoprime divides k power n h hPositive returned

/-- Among positive offset divisors, multiplier prime support characterizes extracted divisors. -/
theorem ExtractedOffsetPrimeSupportedIff (q c factor : ℕ) (cPositive : 0 < c)
    (factorPositive : 0 < factor) (divides : factor ∣ c) :
    (∀ r : ℕ, Nat.Prime r → r ∣ factor → r ∣ q) ↔
      factor ∣ (SupportedOffsetPeel q c).1 := by
  constructor
  · intro support
    exact SupportedOffsetPeelMaximalPower q c factor factor cPositive divides
      (PrimeSupportPower factor q factorPositive support)
  · intro extracted r prime rDivides
    exact SupportedOffsetPeelPrimeSupport q c cPositive r prime
      (dvd_trans rDivides extracted)

/-- The integer relative offset has exactly the magnitude of the computed coprime core. -/
theorem ExtractedOffsetCoreMagnitude (p : Parameters) (cNonzero : p.C ≠ 0) :
    let factors := SupportedOffsetPeel p.Q.natAbs p.C.natAbs
    (RelativeOffsetParameters p (factors.1 : ℤ)).C.natAbs = factors.2 := by
  have cPositive : 0 < p.C.natAbs := Int.natAbs_pos.mpr cNonzero
  obtain ⟨positive, _, product, _, _, _, _⟩ :=
    SupportedOffsetPeelCertificate p.Q.natAbs p.C.natAbs cPositive
  have divides : (SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1 ∣ p.C.natAbs :=
    ⟨_, product.symm⟩
  have integerDivides :
      ((SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1 : ℤ) ∣ p.C := by
    apply Int.natAbs_dvd_natAbs.mp
    simpa using divides
  have reconstructed := congrArg Int.natAbs (Int.ediv_mul_cancel integerDivides)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at reconstructed
  change (p.C / ((SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1 : ℤ)).natAbs =
    (SupportedOffsetPeel p.Q.natAbs p.C.natAbs).2
  apply Nat.eq_of_mul_eq_mul_left positive
  rw [Nat.mul_comm]
  exact reconstructed.trans product.symm

/-- The extracted integer offset is coprime in magnitude to the unchanged multiplier. -/
theorem ExtractedOffsetCoreCoprimeMultiplier (p : Parameters) (cNonzero : p.C ≠ 0) :
    let factor : ℤ := (SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1
    Nat.Coprime (RelativeOffsetParameters p factor).C.natAbs p.Q.natAbs := by
  obtain ⟨_, _, _, coreCoprime, _, _, _⟩ :=
    SupportedOffsetPeelCertificate p.Q.natAbs p.C.natAbs (Int.natAbs_pos.mpr cNonzero)
  change Nat.Coprime
    (RelativeOffsetParameters p
      ((SupportedOffsetPeel p.Q.natAbs p.C.natAbs).1 : ℤ)).C.natAbs p.Q.natAbs
  rw [ExtractedOffsetCoreMagnitude p cNonzero]
  exact coreCoprime

end GeneralizedCollatz
