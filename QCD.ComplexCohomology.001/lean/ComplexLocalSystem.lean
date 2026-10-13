/-
SPDX-License-Identifier: CC-BY-4.0
Actual finite twisted cochain quotients, with weighted-period recovery.
-/
import ComplexCohomology
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace GeneralizedCollatz.ComplexLocalSystem

open GeneralizedCollatz.ComplexCohomology

variable {K : Type*} [Field K]

/-- Extension preserves finite edge addition, including its zero tail. -/
theorem ExtendAdd {n : ℕ} (a b : Fin n → K) :
    Extend (a + b) = fun j => Extend a j + Extend b j := by
  funext j
  by_cases h : j < n <;> simp [Extend, h, Pi.add_apply]

/-- Extension preserves scalar multiplication without introducing extra edges. -/
theorem ExtendScale {n : ℕ} (r : K) (a : Fin n → K) :
    Extend (r • a) = fun j => r * Extend a j := by
  funext j
  simp [Extend, Pi.smul_apply, smul_eq_mul]

/-- Offsets add by the transport recurrence, before any division or averaging. -/
theorem OffsetAdd (lam a b : ℕ → K) (n : ℕ) :
    Offset lam (fun j => a j + b j) n = Offset lam a n + Offset lam b n := by
  induction n with
  | zero => { simp [Offset, Transport] }
  | succ n ih => {
      simp only [Offset, Transport] at ih ⊢
      rw [ih]
      ring
    }

/-- Scaling every edge offset scales the complete translated holonomy. -/
theorem OffsetScale (lam a : ℕ → K) (r : K) (n : ℕ) :
    Offset lam (fun j => r * a j) n = r * Offset lam a n := by
  induction n with
  | zero => { simp [Offset, Transport] }
  | succ n ih => {
      simp only [Offset, Transport] at ih ⊢
      rw [ih]
      ring
    }

/-- The weighted period is a linear observable on exactly n edge coordinates. -/
def WeightedPeriodMap (lam : ℕ → K) (n : ℕ) : (Fin n → K) →ₗ[K] K where
  toFun a := Offset lam (Extend a) n
  map_add' a b := by rw [ExtendAdd, OffsetAdd]
  map_smul' r a := by
    change Offset lam (Extend (r • a)) n = r * Offset lam (Extend a) n
    rw [ExtendScale, OffsetScale]

/-- A zero offset prefix transports zero to zero for every multiplier sequence. -/
theorem ZeroOffsetBefore (lam a : ℕ → K) (n : ℕ) (ha : ∀ j, j < n → a j = 0) :
    Offset lam a n = 0 := by
  induction n with
  | zero => { rfl }
  | succ n ih => {
      simp only [Offset, Transport] at ih ⊢
      rw [ih (fun j hj => ha j (by omega)), ha n (by omega)]
      simp
    }

/-- The last edge has weight one, so every field coefficient is realized when n is positive. -/
theorem WeightedPeriodSurjective (lam : ℕ → K) (n : ℕ) (hn : 0 < n) :
    Function.Surjective (WeightedPeriodMap lam n) := by
  cases n with
  | zero => { omega }
  | succ n => {
      intro u
      let a : Fin (n + 1) → K := fun j => if j.val = n then u else 0
      have hz : Offset lam (Extend a) n = 0 := by
        apply ZeroOffsetBefore
        intro j hj
        simp [Extend, a, Nat.lt_trans hj (Nat.lt_succ_self n), Nat.ne_of_lt hj]
      refine ⟨a, ?_⟩
      change Transport lam (Extend a) 0 (n + 1) = u
      rw [Transport]
      change lam n * Offset lam (Extend a) n + Extend a n = u
      rw [hz]
      simp [Extend, a]
    }

/-- Genuine coboundaries are those finite edges sharing one periodic twisted potential. -/
def TwistedCoboundaries (lam : ℕ → K) (n : ℕ) : Submodule K (Fin n → K) where
  carrier := {a | TwistedExact lam (Extend a) n}
  zero_mem' := by
    refine ⟨fun _ => 0, rfl, ?_⟩
    intro j _
    simp [Extend]
  add_mem' := by
    rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
    refine ⟨fun j => f j + g j, congrArg₂ (· + ·) hf hg, ?_⟩
    intro j hj
    rw [ExtendAdd]
    change Extend a j + Extend b j = f (j + 1) + g (j + 1) - lam j * (f j + g j)
    rw [ha j hj, hb j hj]
    ring
  smul_mem' := by
    rintro r a ⟨f, hf, ha⟩
    refine ⟨fun j => r * f j, congrArg (fun u => r * u) hf, ?_⟩
    intro j hj
    rw [ExtendScale]
    change r * Extend a j = r * f (j + 1) - lam j * (r * f j)
    rw [ha j hj]
    ring

/-- Neutral holonomy identifies the actual image subspace with the weighted-period kernel. -/
theorem NeutralImageKernel (lam : ℕ → K) (n : ℕ) (hp : Holonomy lam n = 1) :
    TwistedCoboundaries lam n = (WeightedPeriodMap lam n).ker := by
  ext a
  change TwistedExact lam (Extend a) n ↔ Offset lam (Extend a) n = 0
  exact NeutralTwistedExact lam (Extend a) n hp

/-- Nonneutral holonomy makes every finite cochain a genuine coboundary. -/
theorem NonneutralImageTop (lam : ℕ → K) (n : ℕ) (hp : Holonomy lam n ≠ 1) :
    TwistedCoboundaries lam n = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro a
  exact NonneutralTwistedExact lam (Extend a) n hp

/-- The local-system H1 is an actual quotient, not merely an obstruction label. -/
abbrev FirstTwistedCohomology (lam : ℕ → K) (n : ℕ) :=
  (Fin n → K) ⧸ TwistedCoboundaries lam n

/-- At neutral holonomy the weighted period is the full quotient isomorphism. -/
noncomputable def NeutralH1Equiv (lam : ℕ → K) (n : ℕ) (hn : 0 < n)
    (hp : Holonomy lam n = 1) : FirstTwistedCohomology lam n ≃ₗ[K] K :=
  (Submodule.quotEquivOfEq _ _ (NeutralImageKernel lam n hp)).trans
    ((WeightedPeriodMap lam n).quotKerEquivOfSurjective (WeightedPeriodSurjective lam n hn))

/-- The neutral quotient class is sent to its actual ordered weighted period. -/
theorem NeutralH1Period (lam : ℕ → K) (n : ℕ) (hn : 0 < n)
    (hp : Holonomy lam n = 1) (a : Fin n → K) :
    NeutralH1Equiv lam n hn hp (Submodule.Quotient.mk a) = WeightedPeriodMap lam n a := by
  rfl

/-- Nonneutral H1 has no nonzero class because the entire edge space is the image. -/
theorem NonneutralH1Zero (lam : ℕ → K) (n : ℕ) (hp : Holonomy lam n ≠ 1) :
    Module.finrank K (FirstTwistedCohomology lam n) = 0 := by
  change Module.finrank K ((Fin n → K) ⧸ TwistedCoboundaries lam n) = 0
  rw [NonneutralImageTop lam n hp]
  exact Module.finrank_zero_of_subsingleton

/-- Zeroth twisted cohomology consists of actual periodic homogeneous vertex potentials. -/
def HomogeneousPotentials (lam : ℕ → K) (n : ℕ) : Submodule K (Fin (n + 1) → K) where
  carrier := {f | f (Fin.last n) = f 0 ∧
    ∀ j : Fin n, f j.succ = lam j.val * f j.castSucc}
  zero_mem' := by
    constructor
    · rfl
    · intro j; simp
  add_mem' := by
    rintro f g ⟨hf, ha⟩ ⟨hg, hb⟩
    constructor
    · exact congrArg₂ (· + ·) hf hg
    · intro j
      change f j.succ + g j.succ = lam j.val * (f j.castSucc + g j.castSucc)
      rw [ha j, hb j]
      ring
  smul_mem' := by
    rintro r f ⟨hf, ha⟩
    constructor
    · exact congrArg (fun u => r * u) hf
    · intro j
      change r * f j.succ = lam j.val * (r * f j.castSucc)
      rw [ha j]
      ring

/-- One initial value reconstructs every actual homogeneous vertex coordinate. -/
theorem PotentialTransport (lam : ℕ → K) (n : ℕ) (f : HomogeneousPotentials lam n)
    (j : ℕ) (hj : j ≤ n) :
    f.1 ⟨j, by omega⟩ = Transport lam (fun _ => 0) (f.1 0) j := by
  induction j with
  | zero => { rfl }
  | succ j ih => {
      have he := f.property.2 ⟨j, by omega⟩
      change f.1 ⟨j + 1, by omega⟩ = lam j * f.1 ⟨j, by omega⟩ at he
      rw [he, Transport, ih (by omega), add_zero]
    }

/-- Endpoint closure imposes the homogeneous holonomy equation on the same initial value. -/
theorem PotentialSeedEquation (lam : ℕ → K) (n : ℕ) (f : HomogeneousPotentials lam n) :
    (1 - Holonomy lam n) * f.1 0 = 0 := by
  have he : Transport lam (fun _ => 0) (f.1 0) n = f.1 0 :=
    (PotentialTransport lam n f n (by omega)).symm.trans f.property.1
  exact ((ClosedWordIff lam (fun _ => 0) (f.1 0) n).mp he).trans
    (ZeroOffsetBefore lam (fun _ => 0) n (fun _ _ => rfl))

/-- At neutral holonomy evaluation at one vertex is the complete H0 isomorphism. -/
def NeutralH0Equiv (lam : ℕ → K) (n : ℕ) (hp : Holonomy lam n = 1) :
    HomogeneousPotentials lam n ≃ₗ[K] K where
  toFun f := f.1 0
  invFun u := ⟨fun j => Transport lam (fun _ => 0) u j.val, by
    constructor
    · exact NeutralEveryClosed lam (fun _ => 0) n hp
        (ZeroOffsetBefore lam (fun _ => 0) n (fun _ _ => rfl)) u
    · intro j
      simp only [Fin.val_succ, Fin.val_castSucc, Transport, add_zero]⟩
  left_inv f := by
    apply Subtype.ext
    funext j
    exact (PotentialTransport lam n f j.val (by omega)).symm
  right_inv u := by rfl
  map_add' f g := by rfl
  map_smul' r f := by rfl

/-- A nonzero holonomy defect leaves only the zero homogeneous potential. -/
theorem NonneutralH0Zero (lam : ℕ → K) (n : ℕ) (hp : Holonomy lam n ≠ 1) :
    Module.finrank K (HomogeneousPotentials lam n) = 0 := by
  apply finrank_zero_iff_forall_zero.mpr
  intro f
  have hf : f.1 0 = 0 := (mul_eq_zero.mp (PotentialSeedEquation lam n f)).resolve_left
    (sub_ne_zero.mpr (Ne.symm hp))
  apply Subtype.ext
  funext j
  have he := PotentialTransport lam n f j.val (by omega)
  rw [hf] at he
  exact he.trans (ZeroOffsetBefore lam (fun _ => 0) j.val (fun _ _ => rfl))

/-- Neutral H0 has one dimension in every coefficient-field characteristic. -/
theorem NeutralH0Dimension (lam : ℕ → K) (n : ℕ) (hp : Holonomy lam n = 1) :
    Module.finrank K (HomogeneousPotentials lam n) = 1 := by
  rw [(NeutralH0Equiv lam n hp).finrank_eq]
  exact Module.finrank_self K

/-- The positive-length neutral H1 quotient has exactly one independent weighted period. -/
theorem NeutralH1Dimension (lam : ℕ → K) (n : ℕ) (hn : 0 < n)
    (hp : Holonomy lam n = 1) : Module.finrank K (FirstTwistedCohomology lam n) = 1 := by
  rw [(NeutralH1Equiv lam n hn hp).finrank_eq]
  exact Module.finrank_self K

end GeneralizedCollatz.ComplexLocalSystem
