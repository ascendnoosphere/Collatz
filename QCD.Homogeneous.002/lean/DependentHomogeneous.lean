import Homogeneous
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Data.Nat.ModEq

namespace GeneralizedCollatz

/-- The exponent update for a homogeneous map with common-base exponents. -/
def ExponentStep (u v k : ℕ) : ℕ := if v ≤ k then k - v else k + u

/-- Inside the recurrent exponent interval, the update is addition modulo its length. -/
theorem ExponentStepEqMod (u v k : ℕ) (_uPositive : 0 < u) (vPos : 0 < v)
    (kBound : k < u + v) :
    ExponentStep u v k = (k + u) % (u + v) := by
  unfold ExponentStep
  split_ifs with division
  · have exponentIdentity : k + u = (k - v) + (u + v) := by omega
    rw [exponentIdentity, Nat.add_mod]
    rw [Nat.mod_self, add_zero, Nat.mod_mod]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · exact (Nat.mod_eq_of_lt (by omega)).symm

/-- The recurrent exponent update remains inside its finite interval. -/
theorem ExponentStepBound (u v k : ℕ) (uPos : 0 < u) (vPos : 0 < v)
    (kBound : k < u + v) :
    ExponentStep u v k < u + v := by
  rw [ExponentStepEqMod u v k uPos vPos kBound]
  exact Nat.mod_lt _ (by omega)

/-- Iteration in the recurrent interval has an exact modular formula. -/
theorem ExponentIterateFormula (u v k j : ℕ) (uPos : 0 < u) (vPos : 0 < v)
    (kBound : k < u + v) :
    (ExponentStep u v)^[j] k = (k + j * u) % (u + v) := by
  induction j with
  | zero => simpa using (Nat.mod_eq_of_lt kBound).symm
  | succ j inductionHypothesis =>
      rw [Function.iterate_succ_apply', inductionHypothesis]
      rw [ExponentStepEqMod u v _ uPos vPos (Nat.mod_lt _ (by omega))]
      rw [Nat.mod_add_mod, Nat.succ_mul]
      congr 1
      omega

end GeneralizedCollatz

namespace GeneralizedCollatz

/-- Every recurrent exponent returns after exactly the interval length. -/
theorem ExponentReturn (u v k : ℕ) (uPos : 0 < u) (vPos : 0 < v)
    (kBound : k < u + v) :
    (ExponentStep u v)^[u + v] k = k := by
  rw [ExponentIterateFormula u v k (u + v) uPos vPos kBound]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt kBound

/-- Coprime common-base exponents have no shorter recurrent return. -/
theorem ExponentNoEarlyReturn (u v k j : ℕ) (uPos : 0 < u) (vPos : 0 < v)
    (uvCoprime : u.Coprime v) (kBound : k < u + v) (jPos : 0 < j)
    (jBound : j < u + v) :
    (ExponentStep u v)^[j] k ≠ k := by
  intro returnEquality
  rw [ExponentIterateFormula u v k j uPos vPos kBound] at returnEquality
  have modEq : k + j * u ≡ k [MOD u + v] := by
    unfold Nat.ModEq
    rw [returnEquality, Nat.mod_eq_of_lt kBound]
  have periodDvdProduct : u + v ∣ j * u := Nat.add_modEq_left_iff.mp modEq
  have periodCoprimeU : (u + v).Coprime u := by
    rw [Nat.add_comm, Nat.coprime_add_self_left]
    exact uvCoprime.symm
  have periodDvdJ : u + v ∣ j := periodCoprimeU.dvd_of_dvd_mul_right periodDvdProduct
  have periodLeJ : u + v ≤ j := Nat.le_of_dvd jPos periodDvdJ
  omega

end GeneralizedCollatz

namespace GeneralizedCollatz

/-- A primitive common-base presentation for a dependent homogeneous map. -/
structure DependentParams where
  Base : ℕ
  U : ℕ
  V : ℕ
  BaseGeTwo : 2 ≤ Base
  UPositive : 0 < U
  VPositive : 0 < V
  UVCoprime : U.Coprime V

namespace DependentParams

/-- The affine multiplier in a dependent homogeneous presentation. -/
def Q (p : DependentParams) : ℕ := p.Base ^ p.U

/-- The division modulus in a dependent homogeneous presentation. -/
def D (p : DependentParams) : ℕ := p.Base ^ p.V

/-- The positive homogeneous raw map in natural-number coordinates. -/
def NatStep (p : DependentParams) (n : ℕ) : ℕ :=
  if p.D ∣ n then n / p.D else p.Q * n

/-- A state written as a base-free factor times a base power follows the exponent update. -/
theorem NatStepRepresentation (p : DependentParams) {r k : ℕ} (rPositive : 0 < r)
    (baseFree : ¬p.Base ∣ r) :
    p.NatStep (r * p.Base ^ k) = r * p.Base ^ ExponentStep p.U p.V k := by
  have basePositive : 0 < p.Base := lt_of_lt_of_le Nat.zero_lt_two p.BaseGeTwo
  have baseNotOne : p.Base ≠ 1 := Nat.ne_of_gt (lt_of_lt_of_le Nat.one_lt_two p.BaseGeTwo)
  have rNonzero : r ≠ 0 := Nat.ne_of_gt rPositive
  have stateNonzero : r * p.Base ^ k ≠ 0 := by
    exact Nat.mul_ne_zero rNonzero (pow_ne_zero _ (Nat.ne_of_gt basePositive))
  have valuationR : padicValNat p.Base r = 0 := by
    have maxPow := Nat.maxPowDvdDiv_of_not_dvd baseFree
    exact congrArg Prod.fst maxPow
  have valuationState : padicValNat p.Base (r * p.Base ^ k) = k := by
    rw [Nat.mul_comm]
    rw [padicValNat_base_pow_mul (by omega) rNonzero]
    simp [valuationR]
  have branchEquivalence : p.Base ^ p.V ∣ r * p.Base ^ k ↔ p.V ≤ k := by
    rw [Nat.pow_dvd_iff_le_padicValNat baseNotOne stateNonzero, valuationState]
  by_cases divisionExponent : p.V ≤ k
  · have divides : p.Base ^ p.V ∣ r * p.Base ^ k :=
      branchEquivalence.mpr divisionExponent
    simp only [NatStep, D, Q]
    rw [if_pos divides]
    rw [ExponentStep, if_pos divisionExponent]
    obtain ⟨l, exponentIdentity⟩ := Nat.exists_eq_add_of_le divisionExponent
    subst k
    rw [Nat.pow_add]
    rw [Nat.mul_comm (p.Base ^ p.V) (p.Base ^ l)]
    rw [← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.pow_pos basePositive)]
    simp
  · have notDivides : ¬p.Base ^ p.V ∣ r * p.Base ^ k :=
      fun divides ↦ divisionExponent (branchEquivalence.mp divides)
    simp only [NatStep, D, Q]
    rw [if_neg notDivides]
    rw [ExponentStep, if_neg divisionExponent]
    simp [Nat.pow_add, Nat.mul_assoc, Nat.mul_comm]

end DependentParams
end GeneralizedCollatz

namespace GeneralizedCollatz.DependentParams

/-- The canonical base-free factor of a positive seed is positive. -/
theorem DivMaxPowPositive (p : DependentParams) {n : ℕ} (nPositive : 0 < n) :
    0 < n.divMaxPow p.Base := by
  have reconstruction := Nat.divMaxPow_mul_pow_padicValNat p.Base n
  by_contra notPositive
  have factorZero : n.divMaxPow p.Base = 0 := Nat.eq_zero_of_not_pos notPositive
  rw [factorZero, zero_mul] at reconstruction
  omega

/-- Every raw iterate is reconstructed from a fixed base-free factor and the exponent iterate. -/
theorem NatIterateRepresentation (p : DependentParams) {n j : ℕ} (nPositive : 0 < n) :
    (p.NatStep)^[j] n =
      n.divMaxPow p.Base * p.Base ^
        ((ExponentStep p.U p.V)^[j] (padicValNat p.Base n)) := by
  have factorPositive := DivMaxPowPositive p nPositive
  have factorFree : ¬p.Base ∣ n.divMaxPow p.Base := by
    exact Nat.not_dvd_divMaxPow (lt_of_lt_of_le Nat.one_lt_two p.BaseGeTwo)
      (Nat.ne_of_gt nPositive)
  induction j with
  | zero =>
      simp only [Function.iterate_zero_apply]
      exact (Nat.divMaxPow_mul_pow_padicValNat p.Base n).symm
  | succ j inductionHypothesis =>
      rw [Function.iterate_succ_apply' p.NatStep, inductionHypothesis]
      rw [Function.iterate_succ_apply' (ExponentStep p.U p.V)]
      exact NatStepRepresentation p factorPositive factorFree

end GeneralizedCollatz.DependentParams

namespace GeneralizedCollatz

/-- Repeated exponent updates enter the recurrent interval. -/
theorem ExponentEventuallyBound (u v k : ℕ) (uPositive : 0 < u) (vPositive : 0 < v) :
    ∃ s, (ExponentStep u v)^[s] k < u + v := by
  induction k using Nat.strong_induction_on with
  | h k inductionHypothesis =>
      by_cases inCore : k < u + v
      · exact ⟨0, by simpa⟩
      · have divisionExponent : v ≤ k := by omega
        have decreases : k - v < k := Nat.sub_lt (by omega) vPositive
        obtain ⟨s, exponentBound⟩ := inductionHypothesis (k - v) decreases
        refine ⟨s + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        rw [ExponentStep, if_pos divisionExponent]
        exact exponentBound

end GeneralizedCollatz

namespace GeneralizedCollatz.DependentParams

/-- Every positive seed eventually enters a primitive cycle of length `U + V`. -/
theorem NatEventuallyPrimitivePeriod (p : DependentParams) {n : ℕ} (nPositive : 0 < n) :
    ∃ s,
      (p.NatStep)^[p.U + p.V] ((p.NatStep)^[s] n) = (p.NatStep)^[s] n ∧
      ∀ j, 0 < j → j < p.U + p.V →
        (p.NatStep)^[j] ((p.NatStep)^[s] n) ≠ (p.NatStep)^[s] n := by
  let k := padicValNat p.Base n
  let r := n.divMaxPow p.Base
  obtain ⟨s, coreBound⟩ := ExponentEventuallyBound p.U p.V k p.UPositive p.VPositive
  have factorPositive : 0 < r := DivMaxPowPositive p nPositive
  have exponentReturn :
      (ExponentStep p.U p.V)^[p.U + p.V]
          ((ExponentStep p.U p.V)^[s] k) = (ExponentStep p.U p.V)^[s] k :=
    ExponentReturn p.U p.V _ p.UPositive p.VPositive coreBound
  refine ⟨s, ?_, ?_⟩
  · rw [← Function.iterate_add_apply]
    rw [NatIterateRepresentation p nPositive, NatIterateRepresentation p nPositive]
    rw [Function.iterate_add_apply, exponentReturn]
  · intro j jPositive jBound rawReturn
    have combinedReturn : (p.NatStep)^[j + s] n = (p.NatStep)^[s] n := by
      rw [Function.iterate_add_apply]
      exact rawReturn
    rw [NatIterateRepresentation p nPositive,
      NatIterateRepresentation p nPositive] at combinedReturn
    have powerReturn :
        p.Base ^ ((ExponentStep p.U p.V)^[j + s] k) =
          p.Base ^ ((ExponentStep p.U p.V)^[s] k) := by
      exact Nat.mul_left_cancel factorPositive combinedReturn
    have exponentEarlyReturn :
        (ExponentStep p.U p.V)^[j] ((ExponentStep p.U p.V)^[s] k) =
          (ExponentStep p.U p.V)^[s] k := by
      rw [← Function.iterate_add_apply]
      exact Nat.pow_right_injective p.BaseGeTwo powerReturn
    exact ExponentNoEarlyReturn p.U p.V _ j p.UPositive p.VPositive p.UVCoprime
      coreBound jPositive jBound exponentEarlyReturn

end GeneralizedCollatz.DependentParams

namespace GeneralizedCollatz

/-- An exponent bound is invariant under one exponent update. -/
theorem ExponentStepBelowBound (u v x bound : ℕ) (vPositive : 0 < v)
    (xBound : x < bound) (intervalBound : u + v ≤ bound) :
    ExponentStep u v x < bound := by
  unfold ExponentStep
  split_ifs with divisionExponent
  · omega
  · omega

/-- Every exponent iterate stays below the initial exponent plus one or the recurrent interval. -/
theorem ExponentIterateBound (u v k j : ℕ) (_uPositive : 0 < u) (vPositive : 0 < v) :
    (ExponentStep u v)^[j] k < max (k + 1) (u + v) := by
  let bound := max (k + 1) (u + v)
  have initialBound : k < bound := by
    have : k + 1 ≤ bound := Nat.le_max_left _ _
    omega
  have intervalBound : u + v ≤ bound := Nat.le_max_right _ _
  induction j with
  | zero => exact initialBound
  | succ j inductionHypothesis =>
      rw [Function.iterate_succ_apply']
      exact ExponentStepBelowBound u v _ bound vPositive inductionHypothesis intervalBound

end GeneralizedCollatz

namespace GeneralizedCollatz.DependentParams

/-- Every positive raw orbit has the uniform source-relative height bound `Q * D * n`. -/
theorem NatIterateHeightBound (p : DependentParams) {n j : ℕ} (nPositive : 0 < n) :
    (p.NatStep)^[j] n ≤ p.Q * p.D * n := by
  let k := padicValNat p.Base n
  let r := n.divMaxPow p.Base
  let exponent := (ExponentStep p.U p.V)^[j] k
  have intervalPositive : 0 < p.U + p.V := Nat.add_pos_left p.UPositive p.V
  have exponentStrictBound : exponent < max (k + 1) (p.U + p.V) :=
    ExponentIterateBound p.U p.V k j p.UPositive p.VPositive
  have exponentBound : exponent ≤ k + (p.U + p.V) := by
    have maxBound : max (k + 1) (p.U + p.V) ≤ k + (p.U + p.V) := by
      apply max_le
      · omega
      · omega
    omega
  have basePositive : 0 < p.Base := lt_of_lt_of_le Nat.zero_lt_two p.BaseGeTwo
  have powerBound : p.Base ^ exponent ≤ p.Base ^ (k + (p.U + p.V)) :=
    Nat.pow_le_pow_right basePositive exponentBound
  rw [NatIterateRepresentation p nPositive]
  change r * p.Base ^ exponent ≤ p.Q * p.D * n
  calc
    r * p.Base ^ exponent ≤ r * p.Base ^ (k + (p.U + p.V)) :=
      Nat.mul_le_mul_left r powerBound
    _ = p.Base ^ (p.U + p.V) * n := by
      dsimp only [r, k]
      rw [Nat.pow_add, ← Nat.mul_assoc]
      rw [Nat.divMaxPow_mul_pow_padicValNat p.Base n]
      exact Nat.mul_comm _ _
    _ = p.Q * p.D * n := by
      simp only [Q, D, ← Nat.pow_add]

end GeneralizedCollatz.DependentParams

namespace GeneralizedCollatz.DependentParams

/-- The dependent division modulus is admissible. -/
theorem DGeTwo (p : DependentParams) : 2 ≤ p.D :=
  p.BaseGeTwo.trans (Nat.le_pow p.VPositive)

/-- The dependent affine multiplier is at least two. -/
theorem QGeTwo (p : DependentParams) : 2 ≤ p.Q :=
  p.BaseGeTwo.trans (Nat.le_pow p.UPositive)

/-- The natural step is the existing positive homogeneous step at the dependent coefficients. -/
theorem NatStepEqPositiveHomogeneous (p : DependentParams) :
    p.NatStep = PositiveHomogeneousStep p.Q p.D := by
  rfl

/-- The natural-number step is exactly the positive restriction of the signed raw map. -/
theorem NatStepAgreesWithRaw (p : DependentParams) (n : ℕ) :
    (p.NatStep n : ℤ) =
      RawStep (HomogeneousParameters p.Q p.D p.DGeTwo) (n : ℤ) := by
  rw [NatStepEqPositiveHomogeneous]
  exact PositiveHomogeneousStepCast p.Q p.D n p.DGeTwo

end GeneralizedCollatz.DependentParams

namespace GeneralizedCollatz

/-- Any positive multiplicative dependence admits a primitive common-base presentation. -/
theorem MultiplicativeDependenceNormalForm {q D a b : ℕ} (qLower : 2 ≤ q)
    (_DLower : 2 ≤ D) (aPositive : 0 < a) (bPositive : 0 < b)
    (dependence : q ^ a = D ^ b) :
    ∃ p : DependentParams, p.Q = q ∧ p.D = D := by
  obtain ⟨t, qIdentity, DIdentity⟩ :=
    Nat.exists_eq_pow_of_pow_eq_pow (Or.inl (Nat.ne_of_gt aPositive)) dependence
  let g := a.gcd b
  let u := b / g
  let v := a / g
  have gPositive : 0 < g := Nat.gcd_pos_of_pos_left b aPositive
  have uPositive : 0 < u := by
    exact Nat.div_pos (Nat.gcd_le_right a bPositive) gPositive
  have vPositive : 0 < v := by
    exact Nat.div_pos (Nat.gcd_le_left b aPositive) gPositive
  have vuCoprime : v.Coprime u := by
    exact Nat.gcd_div_gcd_div_gcd_of_pos_left aPositive
  have uvCoprime : u.Coprime v := vuCoprime.symm
  have baseGeTwo : 2 ≤ t := by
    by_contra baseSmall
    have baseLeOne : t ≤ 1 := by omega
    have qLeOne : q ≤ 1 := by
      rw [qIdentity]
      exact pow_le_one₀ (Nat.zero_le t) baseLeOne
    omega
  let p : DependentParams :=
    { Base := t
      U := u
      V := v
      BaseGeTwo := baseGeTwo
      UPositive := uPositive
      VPositive := vPositive
      UVCoprime := uvCoprime }
  refine ⟨p, ?_, ?_⟩
  · exact qIdentity.symm
  · exact DIdentity.symm

end GeneralizedCollatz

namespace GeneralizedCollatz

/-- Dependent positive dynamics is eventually primitive-periodic with a height bound. -/
theorem DependentHomogeneousClassification {q D a b n : ℕ} (qLower : 2 ≤ q)
    (DLower : 2 ≤ D) (aPositive : 0 < a) (bPositive : 0 < b)
    (dependence : q ^ a = D ^ b) (nPositive : 0 < n) :
    ∃ period s,
      0 < period ∧
      (PositiveHomogeneousStep q D)^[period]
          ((PositiveHomogeneousStep q D)^[s] n) =
        (PositiveHomogeneousStep q D)^[s] n ∧
      (∀ j, 0 < j → j < period →
        (PositiveHomogeneousStep q D)^[j]
            ((PositiveHomogeneousStep q D)^[s] n) ≠
          (PositiveHomogeneousStep q D)^[s] n) ∧
      ∀ j, (PositiveHomogeneousStep q D)^[j] n ≤ q * D * n := by
  obtain ⟨p, qIdentity, DIdentity⟩ :=
    MultiplicativeDependenceNormalForm qLower DLower aPositive bPositive dependence
  obtain ⟨s, periodReturn, noEarlyReturn⟩ := p.NatEventuallyPrimitivePeriod nPositive
  refine ⟨p.U + p.V, s, Nat.add_pos_left p.UPositive p.V, ?_, ?_, ?_⟩
  · rw [← qIdentity, ← DIdentity, ← p.NatStepEqPositiveHomogeneous]
    exact periodReturn
  · intro j jPositive jBound
    rw [← qIdentity, ← DIdentity, ← p.NatStepEqPositiveHomogeneous]
    exact noEarlyReturn j jPositive jBound
  · intro j
    rw [← qIdentity, ← DIdentity, ← p.NatStepEqPositiveHomogeneous]
    exact p.NatIterateHeightBound nPositive

end GeneralizedCollatz
