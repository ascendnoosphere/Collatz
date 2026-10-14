/-
SPDX-License-Identifier: CC-BY-4.0
Marked raw 3n-1 cycle and its coefficient-field resonance, independent of residue guards.
-/
import GuardedDynamics
import ComplexLocalSystem
import ComplexFields
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace GeneralizedCollatz.CycleResonance

open GeneralizedCollatz.ComplexCohomology
open GeneralizedCollatz.ComplexLocalSystem

/-- The original integer dynamics keeps literal division by two as its branch guard. -/
def MinusParameters : Parameters := ⟨3, -1, 2, by decide⟩

/-- These are the eighteen distinct vertices at the original raw clock. -/
def States : Fin 18 → ℤ :=
  ![17, 50, 25, 74, 37, 110, 55, 164, 82, 41, 122, 61, 182, 91, 272, 136, 68, 34]

/-- Periodic indexing records the closing edge without adding a nineteenth vertex. -/
def Cycle (j : ℕ) : ℤ := States ⟨j % 18, Nat.mod_lt _ (by decide)⟩

/-- Every edge is checked against the actual guarded foundational map. -/
theorem RawEdges (j : Fin 18) :
    RawStep MinusParameters (Cycle j.val) = Cycle (j.val + 1) := by
  fin_cases j <;> norm_num [Cycle, States, MinusParameters, RawStep]

/-- Periodic indexing extends the verified raw edges without changing their branch guards. -/
theorem RawCycleStep (j : ℕ) :
    RawStep MinusParameters (Cycle j) = Cycle (j + 1) := by
  simpa only [Cycle, Nat.mod_mod, Nat.add_mod] using
    RawEdges ⟨j % 18, Nat.mod_lt _ (by decide)⟩

/-- Every original-clock iterate is the corresponding retained cycle coordinate. -/
theorem RawCycleOrbit (n : ℕ) : (RawStep MinusParameters)^[n] 17 = Cycle n := by
  induction n with
  | zero => { norm_num [Cycle, States] }
  | succ n ih => {
      rw [Function.iterate_succ_apply', ih, RawCycleStep]
    }

/-- Pairwise distinct raw states make this a marked simple cycle, not a repeated word. -/
theorem DistinctStates : Function.Injective States := by
  decide

/-- Closure is at eighteen original raw ticks, not at the seven accelerated affine ticks. -/
theorem RawCycleReturn : (RawStep MinusParameters)^[18] 17 = 17 := by
  rw [RawCycleOrbit]
  norm_num [Cycle, States]

/-- None of the earlier positive raw times is a return to the marked seed. -/
theorem RawCycleMinimal (n : ℕ) (hn : 0 < n) (hl : n < 18) :
    (RawStep MinusParameters)^[n] 17 ≠ 17 := by
  rw [RawCycleOrbit]
  intro h
  have hs : States ⟨n, hl⟩ = States ⟨0, by decide⟩ := by
    change Cycle n = Cycle 0 at h
    simpa only [Cycle, Nat.mod_eq_of_lt hl, Nat.zero_mod] using h
  have hi := congrArg Fin.val (DistinctStates hs)
  change n = 0 at hi
  omega

/-- The seven marked affine positions have multiplier three; division positions use 1/2. -/
def Weights (K : Type*) [Field K] (j : ℕ) : K :=
  if j ∈ ({0, 2, 4, 6, 9, 11, 13} : Finset ℕ) then 3 else (2 : K)⁻¹

/-- The actual affine offset is minus one; actual division adds no offset. -/
def Offsets (K : Type*) [Field K] (j : ℕ) : K :=
  if j ∈ ({0, 2, 4, 6, 9, 11, 13} : Finset ℕ) then -1 else 0

/-- This ordered word has seven affine and eleven division multipliers. -/
theorem WordHolonomy (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    Holonomy (Weights K) 18 = (3 : K) ^ 7 / (2 : K) ^ 11 := by
  have h2048 : (2048 : K) ≠ 0 := by
    convert pow_ne_zero 11 h2 using 1
    norm_num
  norm_num [Holonomy, Weights]
  field_simp [h2, h2048]
  ring

/-- The integer word defect survives as the same numeral in every coefficient ring. -/
theorem PowerDefect (K : Type*) [Ring K] :
    (3 : K) ^ 7 - (2 : K) ^ 11 = 139 := by
  norm_num

/-- With halving defined, neutrality is exactly vanishing of the integer defect. -/
theorem NeutralIff (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    Holonomy (Weights K) 18 = 1 ↔ (139 : K) = 0 := by
  rw [WordHolonomy K h2,
    div_eq_one_iff_eq (pow_ne_zero 11 h2), ← sub_eq_zero, PowerDefect]

/-- Finite offsets retain exactly the eighteen edges of the marked raw word. -/
def FiniteOffsets (K : Type*) [Field K] : Fin 18 → K := fun j => Offsets K j.val

/-- Cast vertex values solve the same affine recurrence without reducing the branch guard. -/
theorem CastEdge (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) (j : Fin 18) :
    (Cycle (j.val + 1) : K) =
      Weights K j.val * (Cycle j.val : K) + Offsets K j.val := by
  fin_cases j <;> norm_num [Cycle, States, Weights, Offsets] <;>
    field_simp [h2] <;> ring

/-- The actual offset cochain is exact even when the coefficient-field quotient is nonzero. -/
theorem ActualOffsetsExact (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    TwistedExact (Weights K) (Extend (FiniteOffsets K)) 18 := by
  refine ⟨fun j => (Cycle j : K), ?_, ?_⟩
  · norm_num [Cycle, States]
  · intro j hj
    have he := CastEdge K h2 ⟨j, hj⟩
    apply eq_sub_iff_add_eq.mpr
    simpa [Extend, FiniteOffsets, hj, add_comm] using he.symm

/-- The actual offset represents zero in the genuine quotient, not a resonant obstruction. -/
theorem ActualOffsetClassZero (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    (Submodule.Quotient.mk (FiniteOffsets K) :
      FirstTwistedCohomology (Weights K) 18) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero (TwistedCoboundaries (Weights K) 18)).mpr
    (ActualOffsetsExact K h2)

/-- A last-edge unit supplies a contrast with the exact dynamical offset. -/
def UnitEdge (K : Type*) [Field K] : Fin 18 → K :=
  fun j => if j.val = 17 then 1 else 0

/-- Its ordered weighted period is one in every coefficient field. -/
theorem UnitPeriod (K : Type*) [Field K] :
    WeightedPeriodMap (Weights K) 18 (UnitEdge K) = 1 := by
  have hz : Offset (Weights K) (Extend (UnitEdge K)) 17 = 0 := by
    apply ZeroOffsetBefore
    intro j hj
    simp [Extend, UnitEdge, show j < 18 by omega, Nat.ne_of_lt hj]
  change Transport (Weights K) (Extend (UnitEdge K)) 0 18 = 1
  rw [Transport]
  change Weights K 17 * Offset (Weights K) (Extend (UnitEdge K)) 17 +
    Extend (UnitEdge K) 17 = 1
  rw [hz]
  norm_num [Extend, UnitEdge]

/-- The resonance characteristic is certified prime, rather than assumed. -/
instance ResonancePrime : Fact (Nat.Prime 139) := ⟨by decide⟩

/-- A nearby prime supplies a nonresonant negative control. -/
instance ControlPrime : Fact (Nat.Prime 137) := ⟨by decide⟩

/-- The holonomy becomes neutral over the prime field of characteristic 139. -/
theorem Neutral139 : Holonomy (Weights (ZMod 139)) 18 = 1 := by
  rw [WordHolonomy (ZMod 139) (by decide)]
  apply (div_eq_one_iff_eq (pow_ne_zero 11
    (by decide : (2 : ZMod 139) ≠ 0))).mpr
  decide

/-- The same integer word is not neutral over the control coefficient field. -/
theorem Nonneutral137 : Holonomy (Weights (ZMod 137)) 18 ≠ 1 := by
  rw [WordHolonomy (ZMod 137) (by decide)]
  intro h
  have hpow : (3 : ZMod 137) ^ 7 = 2 ^ 11 :=
    (div_eq_one_iff_eq (pow_ne_zero 11
      (by decide : (2 : ZMod 137) ≠ 0))).mp h
  exact (by decide : (3 : ZMod 137) ^ 7 ≠ 2 ^ 11) hpow

/-- In characteristic zero the defect 139 remains nonzero. -/
theorem NonneutralComplex : Holonomy (Weights ℂ) 18 ≠ 1 := by
  rw [WordHolonomy ℂ (by norm_num)]
  norm_num

/-- Resonance produces one dimension in the existing genuine quotient of edge cochains. -/
theorem ResonantDimension :
    Module.finrank (ZMod 139) (FirstTwistedCohomology (Weights (ZMod 139)) 18) = 1 := by
  exact NeutralH1Dimension _ _ (by decide) Neutral139

/-- The negative-control quotient has no nonzero class. -/
theorem ControlDimension :
    Module.finrank (ZMod 137) (FirstTwistedCohomology (Weights (ZMod 137)) 18) = 0 := by
  exact NonneutralH1Zero _ _ Nonneutral137

/-- The complex coefficient quotient vanishes despite the legal integer cycle. -/
theorem ComplexDimension :
    Module.finrank ℂ (FirstTwistedCohomology (Weights ℂ) 18) = 0 := by
  exact NonneutralH1Zero _ _ NonneutralComplex

/-- In the resonant field the dynamical offset still has zero ordered period. -/
theorem ActualPeriodZero139 :
    WeightedPeriodMap (Weights (ZMod 139)) 18 (FiniteOffsets (ZMod 139)) = 0 := by
  exact (NeutralTwistedExact _ _ _ Neutral139).mp
    (ActualOffsetsExact (ZMod 139) (by decide))

/-- The unit-edge cochain realizes a nonzero class in the one-dimensional resonant quotient. -/
theorem UnitClassNonzero139 :
    (Submodule.Quotient.mk (UnitEdge (ZMod 139)) :
      FirstTwistedCohomology (Weights (ZMod 139)) 18) ≠ 0 := by
  intro h
  have he := congrArg (NeutralH1Equiv (Weights (ZMod 139)) 18 (by decide) Neutral139) h
  rw [NeutralH1Period, UnitPeriod, map_zero] at he
  exact one_ne_zero he

/-- This quadratic extension retains the Gaussian relation over the resonance prime field. -/
abbrev Gaussian139 := QuadraticAlgebra (ZMod 139) (-1) 0

set_option maxRecDepth 4096 in
/-- Exhaustion of 139 base coefficients certifies irreducibility, not an assumed field name. -/
instance Gaussian139NoRoot : Fact (∀ r : ZMod 139, r ^ 2 ≠ -1 + 0 * r) := ⟨by decide⟩

/-- Enumeration uses coefficient pairs, whereas multiplication remains quadratic. -/
instance Gaussian139Finite : Fintype Gaussian139 :=
  Fintype.ofEquiv (ZMod 139 × ZMod 139) (QuadraticAlgebra.equivProd (-1) 0).symm

/-- The extension has 139 squared elements without a 19,321-case cardinality proof. -/
theorem Gaussian139Card : Fintype.card Gaussian139 = 19321 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd (-1 : ZMod 139) 0)]
  simp

/-- Conjugation is the already defined coefficient-field algebra automorphism. -/
abbrev Sigma := GeneralizedCollatz.ComplexFields.Conjugation (ZMod 139) (-1) 0

set_option maxRecDepth 4096 in
/-- Checking the generator suffices for equality of the two entire algebra morphisms. -/
theorem Gaussian139Frobenius (z : Gaussian139) : z ^ 139 = Sigma z := by
  have hm : FiniteField.frobeniusAlgHom (ZMod 139) Gaussian139 = Sigma.toAlgHom := by
    apply QuadraticAlgebra.algHom_ext
    change (QuadraticAlgebra.omega : Gaussian139) ^ Fintype.card (ZMod 139) =
      Sigma QuadraticAlgebra.omega
    rw [ZMod.card]
    decide
  have hz := congrArg (fun f : Gaussian139 →ₐ[ZMod 139] Gaussian139 => f z) hm
  change z ^ Fintype.card (ZMod 139) = Sigma z at hz
  simpa only [ZMod.card] using hz

/-- Two Frobenius applications recover the same coefficient element. -/
theorem Gaussian139FrobeniusSquare (z : Gaussian139) : (z ^ 139) ^ 139 = z := by
  rw [Gaussian139Frobenius, Gaussian139Frobenius]
  exact GeneralizedCollatz.ComplexFields.ConjugationSquare _ _ _ z

/-- The fixed coefficients have no Gaussian generator component. -/
theorem Gaussian139Fixed (z : Gaussian139) : z ^ 139 = z ↔ z.im = 0 := by
  rw [Gaussian139Frobenius]
  constructor
  · intro h
    have hi : -z.im = z.im := congrArg QuadraticAlgebra.im h
    have htwo : (2 : ZMod 139) * z.im = 0 := by linear_combination -hi
    exact (mul_eq_zero.mp htwo).resolve_left (by decide)
  · intro hi
    apply QuadraticAlgebra.ext <;> simp [Sigma,
      GeneralizedCollatz.ComplexFields.Conjugation, hi]

/-- The generator square relation is checked in the actual extension multiplication. -/
theorem GeneratorSquare : (QuadraticAlgebra.omega : Gaussian139) *
    QuadraticAlgebra.omega = (-1 : ZMod 139) • (1 : Gaussian139) := by decide

/-- The field property reduces every defining-polynomial root to one of two generators. -/
theorem Gaussian139Roots (z : Gaussian139) :
    z * z = (-1 : ZMod 139) • (1 : Gaussian139) + (0 : ZMod 139) • z ↔
      z = QuadraticAlgebra.omega ∨ z = Sigma QuadraticAlgebra.omega := by
  constructor
  · intro hz
    have ho : Sigma (QuadraticAlgebra.omega : Gaussian139) =
        -QuadraticAlgebra.omega := by decide
    have hp : (z - QuadraticAlgebra.omega) * (z + QuadraticAlgebra.omega) = 0 := by
      calc
        _ = z * z - (QuadraticAlgebra.omega : Gaussian139) *
            QuadraticAlgebra.omega := by ring
        _ = 0 := by rw [hz, GeneratorSquare]; simp
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr ((eq_neg_of_add_eq_zero_left h).trans ho.symm)
  · rintro (rfl | rfl) <;> decide

/-- Every base-field algebra automorphism is determined by those two generator images. -/
theorem Gaussian139Galois (f : Gaussian139 ≃ₐ[ZMod 139] Gaussian139) :
    f = AlgEquiv.refl ∨ f = Sigma := by
  have hroot := ((QuadraticAlgebra.lift (a := (-1 : ZMod 139)) (b := 0)
    (A := Gaussian139)).symm f.toAlgHom).property
  rcases (Gaussian139Roots (f QuadraticAlgebra.omega)).mp hroot with h | h
  · left
    apply AlgEquiv.coe_toAlgHom_injective
    exact QuadraticAlgebra.algHom_ext h
  · right
    apply AlgEquiv.coe_toAlgHom_injective
    exact QuadraticAlgebra.algHom_ext h

/-- Finite-field normality and separability apply to this actually constructed field extension. -/
theorem Gaussian139IsGalois : IsGalois (ZMod 139) Gaussian139 := by
  infer_instance

/-- The listed conjugation is not identity, so the Galois group has two distinct elements. -/
theorem Gaussian139Nontrivial : Sigma ≠ AlgEquiv.refl := by
  have hne : Sigma (QuadraticAlgebra.omega : Gaussian139) ≠
      QuadraticAlgebra.omega := by decide
  intro h
  exact hne (congrArg (fun f => f (QuadraticAlgebra.omega : Gaussian139)) h)

/-- The marked cycle is neutral after passing to the genuine Gaussian extension field. -/
theorem Gaussian139Neutral : Holonomy (Weights Gaussian139) 18 = 1 := by
  have h2 : (2 : Gaussian139) ≠ 0 := by
    intro h
    have hr := congrArg QuadraticAlgebra.re h
    exact (by decide : (2 : ZMod 139) ≠ 0) hr
  exact (NeutralIff Gaussian139 h2).mpr (by decide)

/-- Scalar extension keeps one full extension-field dimension in the actual cochain quotient. -/
theorem Gaussian139Dimension :
    Module.finrank Gaussian139 (FirstTwistedCohomology (Weights Gaussian139) 18) = 1 := by
  exact NeutralH1Dimension _ _ (by decide) Gaussian139Neutral

/-- These prime-subfield weights are fixed by coefficient conjugation at every edge. -/
theorem SigmaWeights (j : ℕ) : Sigma (Weights Gaussian139 j) = Weights Gaussian139 j := by
  unfold Weights
  split
  · decide
  · rw [map_inv₀]; rfl

/-- Coefficient conjugation acts semilinearly on actual eighteen-edge cochains. -/
def SigmaEdges : (Fin 18 → Gaussian139) →ₛₗ[Sigma.toRingHom] (Fin 18 → Gaussian139) where
  toFun a j := Sigma (a j)
  map_add' a b := by
    funext j
    exact map_add Sigma (a j) (b j)
  map_smul' r a := by
    funext j
    exact map_mul Sigma r (a j)

/-- Conjugation also respects the zero tail used by ordered finite transport. -/
theorem SigmaExtend (a : Fin 18 → Gaussian139) :
    Extend (SigmaEdges a) = fun j => Sigma (Extend a j) := by
  funext j
  by_cases h : j < 18
  · simp only [Extend, dif_pos h]
    rfl
  · simp only [Extend, dif_neg h, map_zero]

/-- Transport commutes with conjugation because the same ordered edge weights are fixed. -/
theorem SigmaTransport (a : ℕ → Gaussian139) (u : Gaussian139) (n : ℕ) :
    Sigma (Transport (Weights Gaussian139) a u n) =
      Transport (Weights Gaussian139) (fun j => Sigma (a j)) (Sigma u) n := by
  induction n with
  | zero => { rfl }
  | succ n ih => {
      simp only [Transport, map_add, map_mul, SigmaWeights, ih]
    }

/-- The period conjugates on the same cochain, not on an independently selected witness. -/
theorem SigmaPeriod (a : Fin 18 → Gaussian139) :
    Sigma (WeightedPeriodMap (Weights Gaussian139) 18 a) =
      WeightedPeriodMap (Weights Gaussian139) 18 (SigmaEdges a) := by
  change Sigma (Transport (Weights Gaussian139) (Extend a) 0 18) =
    Transport (Weights Gaussian139) (Extend (SigmaEdges a)) 0 18
  rw [SigmaExtend, SigmaTransport, map_zero]

/-- Genuine coboundaries are invariant, establishing the quotient's descent condition. -/
theorem SigmaCoboundaries : TwistedCoboundaries (Weights Gaussian139) 18 ≤
    (TwistedCoboundaries (Weights Gaussian139) 18).comap SigmaEdges := by
  intro a ha
  change SigmaEdges a ∈ TwistedCoboundaries (Weights Gaussian139) 18
  rw [NeutralImageKernel _ _ Gaussian139Neutral] at ha ⊢
  change WeightedPeriodMap (Weights Gaussian139) 18 a = 0 at ha
  change WeightedPeriodMap (Weights Gaussian139) 18 (SigmaEdges a) = 0
  rw [← SigmaPeriod, ha, map_zero]

/-- The induced Frobenius acts on the actual quotient and is not falsely declared K-linear. -/
def SigmaH1 : FirstTwistedCohomology (Weights Gaussian139) 18 →ₛₗ[Sigma.toRingHom]
    FirstTwistedCohomology (Weights Gaussian139) 18 :=
  (TwistedCoboundaries (Weights Gaussian139) 18).mapQ _ SigmaEdges SigmaCoboundaries

/-- Every concrete class is mapped by conjugating each of its original edge coordinates. -/
theorem SigmaH1Class (a : Fin 18 → Gaussian139) :
    SigmaH1 (Submodule.Quotient.mk a) = Submodule.Quotient.mk (SigmaEdges a) := by
  rfl

/-- The checked weighted-period isomorphism supplies one extension-field coordinate. -/
noncomputable abbrev PeriodEquiv :
    FirstTwistedCohomology (Weights Gaussian139) 18 ≃ₗ[Gaussian139] Gaussian139 :=
  NeutralH1Equiv _ _ (by decide) Gaussian139Neutral

/-- Descent and period recovery intertwine with the coefficient-field Frobenius. -/
theorem SigmaH1Period (x : FirstTwistedCohomology (Weights Gaussian139) 18) :
    PeriodEquiv (SigmaH1 x) = Sigma (PeriodEquiv x) := by
  induction x using Quotient.inductionOn with
  | h a => {
      change PeriodEquiv (SigmaH1 (Submodule.Quotient.mk a)) =
        Sigma (PeriodEquiv (Submodule.Quotient.mk a))
      rw [SigmaH1Class]
      change NeutralH1Equiv _ _ _ Gaussian139Neutral
        (Submodule.Quotient.mk (SigmaEdges a)) =
          Sigma (NeutralH1Equiv _ _ _ Gaussian139Neutral (Submodule.Quotient.mk a))
      rw [NeutralH1Period, NeutralH1Period]
      exact (SigmaPeriod a).symm
    }

/-- The quotient action has order two, on the very same cohomology class. -/
theorem SigmaH1Square (x : FirstTwistedCohomology (Weights Gaussian139) 18) :
    SigmaH1 (SigmaH1 x) = x := by
  apply PeriodEquiv.injective
  rw [SigmaH1Period, SigmaH1Period]
  exact GeneralizedCollatz.ComplexFields.ConjugationSquare _ _ _ (PeriodEquiv x)

/-- Frobenius-fixed classes are exactly those with a prime-subfield weighted period. -/
theorem SigmaH1Fixed (x : FirstTwistedCohomology (Weights Gaussian139) 18) :
    SigmaH1 x = x ↔ (PeriodEquiv x).im = 0 := by
  rw [← PeriodEquiv.injective.eq_iff, SigmaH1Period, ← Gaussian139Frobenius]
  exact Gaussian139Fixed (PeriodEquiv x)

/-- A nonfixed scalar separates Frobenius semilinearity from extension-field linearity. -/
theorem SigmaH1NotLinear : ∃ (r : Gaussian139)
    (x : FirstTwistedCohomology (Weights Gaussian139) 18),
    SigmaH1 (r • x) ≠ r • SigmaH1 x := by
  let x := PeriodEquiv.symm (1 : Gaussian139)
  have hx : PeriodEquiv x = 1 := PeriodEquiv.apply_symm_apply 1
  refine ⟨QuadraticAlgebra.omega, x, ?_⟩
  intro h
  have he := congrArg PeriodEquiv h
  rw [SigmaH1Period, PeriodEquiv.map_smul, PeriodEquiv.map_smul, SigmaH1Period] at he
  simp only [hx, smul_eq_mul, mul_one, map_one] at he
  exact (by decide : Sigma (QuadraticAlgebra.omega : Gaussian139) ≠
    QuadraticAlgebra.omega) he

/-- Fixed classes are in bijection with their unique prime-field period coordinate. -/
noncomputable def FixedPeriodEquiv :
    {x : FirstTwistedCohomology (Weights Gaussian139) 18 // SigmaH1 x = x} ≃ ZMod 139 where
  toFun x := (PeriodEquiv x.val).re
  invFun r := ⟨PeriodEquiv.symm (QuadraticAlgebra.C r), by
    apply (SigmaH1Fixed _).mpr
    rw [PeriodEquiv.apply_symm_apply]
    rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply PeriodEquiv.injective
    rw [PeriodEquiv.apply_symm_apply]
    have hi : (PeriodEquiv x.val).im = 0 := (SigmaH1Fixed _).mp x.property
    apply QuadraticAlgebra.ext <;> simp [hi]
  right_inv r := by
    change (PeriodEquiv (PeriodEquiv.symm (QuadraticAlgebra.C r))).re = r
    rw [PeriodEquiv.apply_symm_apply]
    rfl

/-- Enumerating prime-field coordinates avoids enumerating all eighteen-edge representatives. -/
noncomputable instance FixedH1Finite :
    Fintype {x : FirstTwistedCohomology (Weights Gaussian139) 18 // SigmaH1 x = x} :=
  Fintype.ofEquiv (ZMod 139) FixedPeriodEquiv.symm

/-- The fixed-class count comes from the proved bijection, not an exhaustive cochain search. -/
theorem FixedH1Card :
    Fintype.card {x : FirstTwistedCohomology (Weights Gaussian139) 18 // SigmaH1 x = x} = 139 := by
  rw [Fintype.card_congr FixedPeriodEquiv, ZMod.card]

/-- Antifixed field coordinates have zero prime-field real component. -/
theorem Gaussian139Anti (z : Gaussian139) : Sigma z = -z ↔ z.re = 0 := by
  constructor
  · intro h
    have hr : z.re = -z.re := by
      simpa [Sigma, GeneralizedCollatz.ComplexFields.Conjugation] using
        congrArg QuadraticAlgebra.re h
    have htwo : (2 : ZMod 139) * z.re = 0 := by linear_combination hr
    exact (mul_eq_zero.mp htwo).resolve_left (by decide)
  · intro hr
    apply QuadraticAlgebra.ext <;>
      simp [Sigma, GeneralizedCollatz.ComplexFields.Conjugation, hr]

/-- The sign eigenspace of the actual quotient is detected by its same period coordinate. -/
theorem SigmaH1Anti (x : FirstTwistedCohomology (Weights Gaussian139) 18) :
    SigmaH1 x = -x ↔ (PeriodEquiv x).re = 0 := by
  rw [← PeriodEquiv.injective.eq_iff, SigmaH1Period, map_neg]
  exact Gaussian139Anti (PeriodEquiv x)

/-- The fixed part uses one already constructed inverse-period witness. -/
noncomputable def FixedPart (x : FirstTwistedCohomology (Weights Gaussian139) 18) :
    FirstTwistedCohomology (Weights Gaussian139) 18 :=
  PeriodEquiv.symm (QuadraticAlgebra.C (PeriodEquiv x).re)

/-- The sign part keeps the complementary Gaussian coefficient of that same witness. -/
noncomputable def AntiPart (x : FirstTwistedCohomology (Weights Gaussian139) 18) :
    FirstTwistedCohomology (Weights Gaussian139) 18 :=
  PeriodEquiv.symm ⟨0, (PeriodEquiv x).im⟩

/-- The explicitly recovered real-coordinate part is Frobenius fixed. -/
theorem FixedPartFixed (x : FirstTwistedCohomology (Weights Gaussian139) 18) :
    SigmaH1 (FixedPart x) = FixedPart x := by
  apply (SigmaH1Fixed _).mpr
  simp only [FixedPart, PeriodEquiv.apply_symm_apply]
  rfl

/-- The explicitly recovered Gaussian-coordinate part transforms with a minus sign. -/
theorem AntiPartNegative (x : FirstTwistedCohomology (Weights Gaussian139) 18) :
    SigmaH1 (AntiPart x) = -AntiPart x := by
  apply (SigmaH1Anti _).mpr
  simp only [AntiPart, PeriodEquiv.apply_symm_apply]

/-- The two recovered parts reconstruct the original class, not just its observable. -/
theorem GaloisDecomposition (x : FirstTwistedCohomology (Weights Gaussian139) 18) :
    FixedPart x + AntiPart x = x := by
  apply PeriodEquiv.injective
  simp only [map_add, FixedPart, AntiPart, PeriodEquiv.apply_symm_apply]
  apply QuadraticAlgebra.ext <;> simp

/-- All quotient classes are enumerated by field coordinates, not cochain representatives. -/
noncomputable instance Gaussian139H1Finite :
    Fintype (FirstTwistedCohomology (Weights Gaussian139) 18) :=
  Fintype.ofEquiv Gaussian139 PeriodEquiv.toEquiv.symm

/-- The count of all classes follows from the genuine quotient isomorphism. -/
theorem Gaussian139H1Card :
    Fintype.card (FirstTwistedCohomology (Weights Gaussian139) 18) = 19321 := by
  rw [Fintype.card_congr PeriodEquiv.toEquiv, Gaussian139Card]

/-- The scalar color invariant is the actual quadratic norm, not a Euclidean field metric. -/
theorem Gaussian139Norm (z : Gaussian139) :
    z * Sigma z = QuadraticAlgebra.C (z.re ^ 2 + z.im ^ 2) := by
  apply QuadraticAlgebra.ext
  · change z.re * (z.re + 0 * z.im) + (-1) * z.im * (-z.im) =
      z.re ^ 2 + z.im ^ 2
    ring
  · change z.re * (-z.im) + z.im * (z.re + 0 * z.im) + 0 * z.im * (-z.im) = 0
    ring

/-- Fixed and sign witnesses summing to one class are its uniquely recovered two parts. -/
theorem GaloisDecompositionUnique
    (x f a : FirstTwistedCohomology (Weights Gaussian139) 18)
    (hf : SigmaH1 f = f) (ha : SigmaH1 a = -a) (hs : f + a = x) :
    f = FixedPart x ∧ a = AntiPart x := by
  have hfi : (PeriodEquiv f).im = 0 := (SigmaH1Fixed f).mp hf
  have har : (PeriodEquiv a).re = 0 := (SigmaH1Anti a).mp ha
  have hp : PeriodEquiv f + PeriodEquiv a = PeriodEquiv x := by
    rw [← map_add, hs]
  have hr : (PeriodEquiv f).re = (PeriodEquiv x).re := by
    have h := congrArg QuadraticAlgebra.re hp
    change (PeriodEquiv f).re + (PeriodEquiv a).re = (PeriodEquiv x).re at h
    simpa only [har, add_zero] using h
  have hi : (PeriodEquiv a).im = (PeriodEquiv x).im := by
    have h := congrArg QuadraticAlgebra.im hp
    change (PeriodEquiv f).im + (PeriodEquiv a).im = (PeriodEquiv x).im at h
    simpa only [hfi, zero_add] using h
  constructor
  · apply PeriodEquiv.injective
    simp only [FixedPart, PeriodEquiv.apply_symm_apply]
    apply QuadraticAlgebra.ext
    · exact hr
    · exact hfi
  · apply PeriodEquiv.injective
    simp only [AntiPart, PeriodEquiv.apply_symm_apply]
    apply QuadraticAlgebra.ext
    · exact har
    · exact hi

end GeneralizedCollatz.CycleResonance
