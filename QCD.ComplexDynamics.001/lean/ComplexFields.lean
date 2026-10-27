/-
SPDX-License-Identifier: CC-BY-4.0
Explicit inert quadratic fields, their Frobenius Galois groups and ramified controls.
-/
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Field.ZMod

namespace GeneralizedCollatz.ComplexFields

/-- The coefficient ring modulo three is a field because its modulus is proved prime. -/
instance GaussianPrime : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The coefficient ring modulo two is a field because its modulus is proved prime. -/
instance EisensteinPrime : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The Gaussian inert quotient has the actual multiplication relation w² = -1. -/
abbrev GaussianNine := QuadraticAlgebra (ZMod 3) (-1) 0

/-- The Eisenstein inert quotient has the actual relation w² = -1 - w. -/
abbrev EisensteinFour := QuadraticAlgebra (ZMod 2) (-1) (-1)

/-- Exhausting the prime field supplies the exact no-root hypothesis for a field instance. -/
instance GaussianNoRoot : Fact (∀ r : ZMod 3, r ^ 2 ≠ -1 + 0 * r) := ⟨by decide⟩

/-- The Eisenstein polynomial has no root over the two-element coefficient field. -/
instance EisensteinNoRoot : Fact (∀ r : ZMod 2, r ^ 2 ≠ -1 + (-1) * r) := ⟨by decide⟩

/-- The nine Gaussian residue pairs form an explicit finite enumeration. -/
instance GaussianFinite : Fintype GaussianNine :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3) (QuadraticAlgebra.equivProd (-1) 0).symm

/-- The four Eisenstein residue pairs form an explicit finite enumeration. -/
instance EisensteinFinite : Fintype EisensteinFour :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2) (QuadraticAlgebra.equivProd (-1) (-1)).symm

/-- Conjugation fixes the coefficient ring, so it is an actual algebra automorphism. -/
def Conjugation (R : Type*) [CommRing R] (a b : R) :
    QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a b where
  toRingEquiv := starRingAut
  commutes' r := by
    apply QuadraticAlgebra.ext <;> simp

/-- The inert Gaussian field has nine elements, not nine residue classes in Z/9Z. -/
theorem GaussianCard : Fintype.card GaussianNine = 9 := by decide

/-- The inert Eisenstein field has four elements, not four residue classes in Z/4Z. -/
theorem EisensteinCard : Fintype.card EisensteinFour = 4 := by decide

/-- Gaussian Frobenius is exactly the nontrivial quadratic conjugation. -/
theorem GaussianFrobenius : ∀ z : GaussianNine,
    z ^ 3 = Conjugation (ZMod 3) (-1) 0 z := by decide

/-- Eisenstein Frobenius is exactly the nontrivial quadratic conjugation. -/
theorem EisensteinFrobenius : ∀ z : EisensteinFour,
    z ^ 2 = Conjugation (ZMod 2) (-1) (-1) z := by decide

/-- Conjugation closes after two applications without forgetting either coordinate. -/
theorem ConjugationSquare (R : Type*) [CommRing R] (a b : R)
    (z : QuadraticAlgebra R a b) :
    Conjugation R a b (Conjugation R a b z) = z := by
  exact star_star z

/-- The fixed Gaussian points are precisely the embedded prime subfield. -/
theorem GaussianFixed : ∀ z : GaussianNine,
    z ^ 3 = z ↔ z.im = 0 := by decide

/-- The fixed Eisenstein points are precisely the embedded prime subfield. -/
theorem EisensteinFixed : ∀ z : EisensteinFour,
    z ^ 2 = z ↔ z.im = 0 := by decide

/-- Only the two conjugate generators solve the Gaussian defining equation. -/
theorem GaussianRoots : ∀ z : GaussianNine,
    z * z = (-1 : ZMod 3) • (1 : GaussianNine) + (0 : ZMod 3) • z ↔
      z = QuadraticAlgebra.omega ∨
        z = Conjugation (ZMod 3) (-1) 0 QuadraticAlgebra.omega := by decide

/-- Only the two conjugate generators solve the Eisenstein defining equation. -/
theorem EisensteinRoots : ∀ z : EisensteinFour,
    z * z = (-1 : ZMod 2) • (1 : EisensteinFour) + (-1 : ZMod 2) • z ↔
      z = QuadraticAlgebra.omega ∨
        z = Conjugation (ZMod 2) (-1) (-1) QuadraticAlgebra.omega := by decide

/-- Every Gaussian algebra automorphism is identity or the quadratic Frobenius. -/
theorem GaussianGalois (f : GaussianNine ≃ₐ[ZMod 3] GaussianNine) :
    f = AlgEquiv.refl ∨ f = Conjugation (ZMod 3) (-1) 0 := by
  have hroot := ((QuadraticAlgebra.lift (a := (-1 : ZMod 3)) (b := 0)
    (A := GaussianNine)).symm f.toAlgHom).property
  rcases (GaussianRoots (f QuadraticAlgebra.omega)).mp hroot with h | h
  · left
    apply AlgEquiv.coe_toAlgHom_injective
    exact QuadraticAlgebra.algHom_ext h
  · right
    apply AlgEquiv.coe_toAlgHom_injective
    exact QuadraticAlgebra.algHom_ext h

/-- Every Eisenstein algebra automorphism is identity or the quadratic Frobenius. -/
theorem EisensteinGalois (f : EisensteinFour ≃ₐ[ZMod 2] EisensteinFour) :
    f = AlgEquiv.refl ∨
      f = Conjugation (ZMod 2) (-1) (-1) := by
  have hroot := ((QuadraticAlgebra.lift (a := (-1 : ZMod 2)) (b := (-1))
    (A := EisensteinFour)).symm f.toAlgHom).property
  rcases (EisensteinRoots (f QuadraticAlgebra.omega)).mp hroot with h | h
  · left
    apply AlgEquiv.coe_toAlgHom_injective
    exact QuadraticAlgebra.algHom_ext h
  · right
    apply AlgEquiv.coe_toAlgHom_injective
    exact QuadraticAlgebra.algHom_ext h

/-- Gaussian conjugation is not identity, so the two listed automorphisms are distinct. -/
theorem GaussianNontrivial : Conjugation (ZMod 3) (-1) 0 ≠
    AlgEquiv.refl := by
  have hne : Conjugation (ZMod 3) (-1) 0 (QuadraticAlgebra.omega : GaussianNine) ≠
      QuadraticAlgebra.omega := by decide
  intro h
  exact hne (congrArg (fun f => f (QuadraticAlgebra.omega : GaussianNine)) h)

/-- Eisenstein conjugation is not identity, so the listed Galois group has order two. -/
theorem EisensteinNontrivial : Conjugation (ZMod 2) (-1) (-1) ≠
    AlgEquiv.refl := by
  have hne : Conjugation (ZMod 2) (-1) (-1)
      (QuadraticAlgebra.omega : EisensteinFour) ≠ QuadraticAlgebra.omega := by decide
  intro h
  exact hne (congrArg (fun f => f (QuadraticAlgebra.omega : EisensteinFour)) h)

/-- A finite-field affine model retains its declared multiplier and additive offset. -/
def AffineOrbit {A : Type*} [Ring A] (q c z : A) : ℕ → A
  | 0 => z
  | j + 1 => q * AffineOrbit q c z j + c

/-- Galois conjugation transports affine orbits at the same clock, with both parameters. -/
theorem ConjugationAffineOrbit (R : Type*) [CommRing R] (a b : R)
    (q c z : QuadraticAlgebra R a b) (j : ℕ) :
    Conjugation R a b (AffineOrbit q c z j) =
      AffineOrbit (Conjugation R a b q) (Conjugation R a b c)
        (Conjugation R a b z) j := by
  induction j with
  | zero => { rfl }
  | succ j ih => { simp only [AffineOrbit, map_add, map_mul, ih] }

/-- Ramification gives a nonzero Gaussian nilpotent; this quotient cannot be a field. -/
theorem GaussianRamified :
    let e : QuadraticAlgebra (ZMod 2) (-1) 0 := ⟨1, 1⟩
    e ≠ 0 ∧ e * e = 0 := by decide

/-- Ramification gives a nonzero Eisenstein nilpotent in characteristic three. -/
theorem EisensteinRamified :
    let e : QuadraticAlgebra (ZMod 3) (-1) (-1) := ⟨1, -1⟩
    e ≠ 0 ∧ e * e = 0 := by decide

end GeneralizedCollatz.ComplexFields
