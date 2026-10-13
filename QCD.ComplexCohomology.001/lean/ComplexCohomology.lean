/-
SPDX-License-Identifier: CC-BY-4.0
Closed affine cochains and their exact reconstruction on an oriented cycle.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace GeneralizedCollatz.ComplexCohomology

variable {K : Type*} [Field K]

/-- Literal divisibility in a field is not a lattice branch guard. -/
theorem FieldGuard (d z : K) (hd : d ≠ 0) : d ∣ z := by
  exact ⟨z / d, by field_simp⟩

/-- The branch definition collapses over a field for every nonzero divisor. -/
theorem FieldBranchCollapse (q c d z : K) [Decidable (d ∣ z)] (hd : d ≠ 0) :
    (if d ∣ z then z / d else q * z + c) = z / d := by
  rw [if_pos (FieldGuard d z hd)]

/-- Edge transport retains both the linear coefficient and the additive cochain. -/
def Transport (lam a : ℕ → K) (u : K) : ℕ → K
  | 0 => u
  | j + 1 => lam j * Transport lam a u j + a j

/-- Ordered edge multipliers give the linear holonomy of the word. -/
def Holonomy (lam : ℕ → K) : ℕ → K
  | 0 => 1
  | j + 1 => lam j * Holonomy lam j

/-- Transport from zero computes the translated holonomy without losing edge order. -/
def Offset (lam a : ℕ → K) : ℕ → K := Transport lam a 0

/-- Every initial vertex value reconstructs by one linear coefficient and one offset. -/
theorem TransportFormula (lam a : ℕ → K) (u : K) (j : ℕ) :
    Transport lam a u j = Holonomy lam j * u + Offset lam a j := by
  induction j with
  | zero => { simp [Transport, Holonomy, Offset] }
  | succ j ih => {
      simp only [Transport, Holonomy, Offset] at ih ⊢
      rw [ih]
      ring
    }

/-- Closing an affine word is exactly one scalar equation; branch legality is separate. -/
theorem ClosedWordIff (lam a : ℕ → K) (u : K) (n : ℕ) :
    Transport lam a u n = u ↔ (1 - Holonomy lam n) * u = Offset lam a n := by
  rw [TransportFormula]
  constructor
  · intro h
    calc
      (1 - Holonomy lam n) * u = u - Holonomy lam n * u := by ring
      _ = Offset lam a n := by
        have heq := congrArg (fun v : K => v - Holonomy lam n * u) h.symm
        simpa only [add_sub_cancel_left] using heq
  · intro h
    calc
      Holonomy lam n * u + Offset lam a n =
          Holonomy lam n * u + (1 - Holonomy lam n) * u := by rw [h]
      _ = u := by ring

/-- Nonneutral holonomy supplies a unique closed affine solution. -/
theorem NonneutralReconstruction (lam a : ℕ → K) (n : ℕ)
    (h : Holonomy lam n ≠ 1) :
    ∃! u : K, Transport lam a u n = u := by
  have hden : 1 - Holonomy lam n ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  refine ⟨Offset lam a n / (1 - Holonomy lam n), ?_, ?_⟩
  · change Transport lam a (Offset lam a n / (1 - Holonomy lam n)) n =
        Offset lam a n / (1 - Holonomy lam n)
    rw [ClosedWordIff]
    field_simp
  · intro u hu
    rw [ClosedWordIff] at hu
    apply (eq_div_iff hden).mpr
    simpa only [mul_comm] using hu

/-- Neutral holonomy leaves exactly the additive obstruction to closing the word. -/
theorem NeutralObstruction (lam a : ℕ → K) (n : ℕ)
    (h : Holonomy lam n = 1) :
    (∃ u : K, Transport lam a u n = u) ↔ Offset lam a n = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    rw [ClosedWordIff, h, sub_self, zero_mul] at hu
    exact hu.symm
  · intro ha
    refine ⟨0, ?_⟩
    rw [ClosedWordIff, ha, mul_zero]

/-- A twisted coboundary uses one common periodic potential on all edges. -/
def TwistedExact (lam a : ℕ → K) (n : ℕ) : Prop :=
  ∃ f : ℕ → K, f n = f 0 ∧ ∀ j : ℕ, j < n → a j = f (j + 1) - lam j * f j

/-- Twisted exactness is equivalent to one closed transport, with explicit recovery. -/
theorem TwistedExactIff (lam a : ℕ → K) (n : ℕ) :
    TwistedExact lam a n ↔ ∃ u : K, Transport lam a u n = u := by
  constructor
  · rintro ⟨f, hf, ha⟩
    have heq : ∀ j : ℕ, j ≤ n → Transport lam a (f 0) j = f j := by
      intro j hj
      induction j with
      | zero => { rfl }
      | succ j ih => {
          rw [Transport, ih (by omega), ha j (by omega)]
          ring
        }
    exact ⟨f 0, (heq n (by omega)).trans hf⟩
  · rintro ⟨u, hu⟩
    refine ⟨Transport lam a u, hu, ?_⟩
    intro j _
    rw [Transport]
    ring

/-- Every edge cochain is exact at nonneutral holonomy, not just a particular offset. -/
theorem NonneutralTwistedExact (lam a : ℕ → K) (n : ℕ)
    (h : Holonomy lam n ≠ 1) : TwistedExact lam a n := by
  rw [TwistedExactIff]
  obtain ⟨u, hu, _⟩ := NonneutralReconstruction lam a n h
  exact ⟨u, hu⟩

/-- Neutral holonomy leaves the weighted additive period as the sole obstruction. -/
theorem NeutralTwistedExact (lam a : ℕ → K) (n : ℕ)
    (h : Holonomy lam n = 1) : TwistedExact lam a n ↔ Offset lam a n = 0 := by
  rw [TwistedExactIff]
  exact NeutralObstruction lam a n h

/-- At neutral holonomy a zero weighted period closes transport for every initial value. -/
theorem NeutralEveryClosed (lam a : ℕ → K) (n : ℕ)
    (h : Holonomy lam n = 1) (ha : Offset lam a n = 0) (u : K) :
    Transport lam a u n = u := by
  rw [TransportFormula, h, ha, one_mul, add_zero]

section Ordinary

variable {A : Type*} [AddCommGroup A]

/-- A cycle potential is written on n+1 vertices with the two endpoint values equal. -/
def CycleExact (a : ℕ → A) (n : ℕ) : Prop :=
  ∃ f : ℕ → A, f n = f 0 ∧ ∀ j : ℕ, j < n → a j = f (j + 1) - f j

/-- Prefix sums are the explicit primitive of an edge cochain. -/
def Primitive (a : ℕ → A) (j : ℕ) : A := ∑ k ∈ Finset.range j, a k

/-- The period is the sole additive obstruction on a nonempty oriented cycle. -/
def Period (a : ℕ → A) (n : ℕ) : A := Primitive a n

/-- Adding one edge recovers its coefficient exactly, without an existence oracle. -/
theorem PrimitiveStep (a : ℕ → A) (j : ℕ) :
    Primitive a (j + 1) - Primitive a j = a j := by
  simp [Primitive, Finset.sum_range_succ]

/-- Telescoping computes the period of every coboundary. -/
theorem DifferencePeriod (f : ℕ → A) (n : ℕ) :
    Period (fun j => f (j + 1) - f j) n = f n - f 0 := by
  induction n with
  | zero => { simp [Period, Primitive] }
  | succ n ih => {
      simp only [Period, Primitive, Finset.sum_range_succ] at ih ⊢
      rw [ih]
      abel
    }

/-- The vanishing period criterion proves both admissibility and explicit recovery. -/
theorem CycleExactIff (a : ℕ → A) (n : ℕ) :
    CycleExact a n ↔ Period a n = 0 := by
  constructor
  · rintro ⟨f, hf, ha⟩
    have heq : Period a n = Period (fun j => f (j + 1) - f j) n := by
      unfold Period Primitive
      apply Finset.sum_congr rfl
      intro j hj
      exact ha j (Finset.mem_range.mp hj)
    rw [heq, DifferencePeriod, hf, sub_self]
  · intro h
    refine ⟨Primitive a, ?_, ?_⟩
    · simpa [Period, Primitive] using h
    · intro j _
      exact (PrimitiveStep a j).symm

/-- Periods respect addition and subtraction of finite edge cochains. -/
theorem PeriodSub (a b : ℕ → A) (n : ℕ) :
    Period (fun j => a j - b j) n = Period a n - Period b n := by
  simp [Period, Primitive, Finset.sum_sub_distrib]

/-- Equal periods characterize the same H1 class; values beyond n are not edges. -/
theorem SameClassIff (a b : ℕ → A) (n : ℕ) :
    CycleExact (fun j => a j - b j) n ↔ Period a n = Period b n := by
  rw [CycleExactIff, PeriodSub, sub_eq_zero]

/-- A single marked edge realizes any period on every nonempty cycle. -/
theorem PeriodSurjective (n : ℕ) (hn : 0 < n) (u : A) :
    ∃ a : ℕ → A, Period a n = u := by
  refine ⟨fun j => if j = 0 then u else 0, ?_⟩
  simp [Period, Primitive, Finset.sum_ite_eq', Finset.mem_range, hn]

/-- A zero coboundary forces one common value on all vertices of a cycle path. -/
theorem ZeroDifferenceConstant (f : ℕ → A) (n : ℕ)
    (h : ∀ j : ℕ, j < n → f (j + 1) - f j = 0) :
    ∀ j : ℕ, j ≤ n → f j = f 0 := by
  intro j hj
  induction j with
  | zero => { rfl }
  | succ j ih => {
      have heq := sub_eq_zero.mp (h j (by omega))
      exact heq.trans (ih (by omega))
    }

end Ordinary

/-- Finite edges extend by zero only to reuse the proved prefix-sum reconstruction. -/
def Extend {n : ℕ} (a : Fin n → K) (j : ℕ) : K :=
  if h : j < n then a ⟨j, h⟩ else 0

/-- The period is a linear observable on the actual n-dimensional edge space. -/
def FinitePeriodMap (n : ℕ) : (Fin n → K) →ₗ[K] K where
  toFun a := ∑ j : Fin n, a j
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum]

/-- The finite period agrees exactly with the prefix observable, without extra edges. -/
theorem ExtensionPeriod {n : ℕ} (a : Fin n → K) :
    Period (Extend a) n = FinitePeriodMap n a := by
  unfold Period Primitive
  rw [← Fin.sum_univ_eq_sum_range (Extend a) n]
  change (∑ j : Fin n, Extend a j.val) = ∑ j : Fin n, a j
  apply Finset.sum_congr rfl
  intro j _
  simp [Extend, j.isLt]

/-- This computable subspace is identified with cycle coboundaries by the next theorem. -/
def ExactCochains (n : ℕ) : Submodule K (Fin n → K) := (FinitePeriodMap n).ker

/-- Subspace membership is equivalent to one common periodic potential on every edge. -/
theorem ExactCochainsIff {n : ℕ} (a : Fin n → K) :
    a ∈ ExactCochains n ↔ CycleExact (Extend a) n := by
  rw [CycleExactIff, ExtensionPeriod]
  rfl

/-- Every coefficient is realized by a cochain on one marked finite edge. -/
theorem FinitePeriodSurjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (FinitePeriodMap n : (Fin n → K) →ₗ[K] K) := by
  intro u
  let i : Fin n := ⟨0, hn⟩
  refine ⟨fun j => if j = i then u else 0, ?_⟩
  simp [FinitePeriodMap, Finset.sum_ite_eq']

/-- Ordinary first cycle cohomology is an actual quotient of finite edge cochains. -/
abbrev FirstCohomology (n : ℕ) := (Fin n → K) ⧸ (ExactCochains n : Submodule K (Fin n → K))

/-- The period gives a checked linear isomorphism, including all positive characteristics. -/
noncomputable def FirstCohomologyEquiv (n : ℕ) (hn : 0 < n) :
    FirstCohomology (K := K) n ≃ₗ[K] K :=
  (FinitePeriodMap (K := K) n).quotKerEquivOfSurjective
    (FinitePeriodSurjective (K := K) n hn)

/-- The quotient isomorphism sends a concrete cochain class to its computed period. -/
theorem FirstCohomologyPeriod {n : ℕ} (hn : 0 < n) (a : Fin n → K) :
    FirstCohomologyEquiv (K := K) n hn (Submodule.Quotient.mk a) = FinitePeriodMap n a := by
  rfl

end GeneralizedCollatz.ComplexCohomology
