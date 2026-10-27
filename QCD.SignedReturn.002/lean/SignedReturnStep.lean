-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Tactic.Ring

/-!
# One division at a first hit

If `j` is the first time the affine state is divisible by `D`, the raw iterate
at that time equals the affine state, and the next raw step is one exact
division of that state by `D`. The identification is `PrefixAffine`, after a
second induction has shown that a division-free affine prefix is the same
predicate as a division-free raw prefix. The division clause uses the
division branch once. It does not remove a higher power of `D`, and it does
not define a later return.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.SignedReturnStep

/-- The affine state of multiplier `q`, offset `c`, time `j` and seed `n`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- The affine state meets `D` at time `j` and at no earlier time. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n

/-- Divisibility selects one exact division by `D`, not the affine branch. -/
theorem RawStepDivide (p : Parameters) (m : ℤ) (h : p.D ∣ m) :
    RawStep p m = m / p.D := by
  unfold RawStep
  rw [if_pos h]

/-- A raw prefix with no division before time `j` equals the affine state. -/
theorem PrefixAffine (p : Parameters) (n : ℤ) (j : ℕ)
    (h : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n) :
    Iterate (RawStep p) j n = AffineState p.Q p.C j n := by
  induction j with
  | zero => {
      change n = AffineState p.Q p.C 0 n
      unfold AffineState
      have hsum : TrapSum p.Q 0 = 0 := rfl
      rw [hsum]
      ring
    }
  | succ j ih => {
      have hlt : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self j))
      have hj : ¬ p.D ∣ Iterate (RawStep p) j n :=
        h j (Nat.lt_succ_self j)
      have hstep : Iterate (RawStep p) (j + 1) n =
          RawStep p (Iterate (RawStep p) j n) := rfl
      have haffine : RawStep p (Iterate (RawStep p) j n) =
          p.Q * Iterate (RawStep p) j n + p.C :=
        RawStepAffine p _ hj
      rw [hstep, haffine, ih hlt]
      unfold AffineState
      show p.Q * (p.Q ^ j * n + p.C * TrapSum p.Q j) + p.C =
        p.Q ^ (j + 1) * n + p.C * TrapSum p.Q (j + 1)
      rw [TrapSumRec]
      ring
    }

/-- The raw and affine division-free prefixes are the same predicate. -/
theorem DivisionFreePrefixIff (p : Parameters) (n : ℤ) (j : ℕ) :
    (∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n) ↔
      (∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n) := by
  induction j with
  | zero => {
      constructor
      · intro _ i hi
        exact absurd hi (Nat.not_lt_zero i)
      · intro _ i hi
        exact absurd hi (Nat.not_lt_zero i)
    }
  | succ j ih => {
      constructor
      · intro hraw
        -- The guard of length `j` is shorter, so `PrefixAffine` applies to it.
        have splitRaw :
            (∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n) ∧
              ¬ p.D ∣ Iterate (RawStep p) j n :=
          (Nat.forall_lt_succ_right
            (p := fun i => ¬ p.D ∣ Iterate (RawStep p) i n)
            (n := j)).mp hraw
        have hrawlt : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n :=
          splitRaw.left
        have hnd : ¬ p.D ∣ Iterate (RawStep p) j n := splitRaw.right
        have heq : Iterate (RawStep p) j n = AffineState p.Q p.C j n :=
          PrefixAffine p n j hrawlt
        have hndA : ¬ p.D ∣ AffineState p.Q p.C j n := by
          rw [← heq]
          exact hnd
        exact
          (Nat.forall_lt_succ_right
            (p := fun i => ¬ p.D ∣ AffineState p.Q p.C i n)
            (n := j)).mpr ⟨ih.mp hrawlt, hndA⟩
      · intro haff
        -- The inductive equivalence supplies the raw guard. Equality is next.
        have splitAff :
            (∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n) ∧
              ¬ p.D ∣ AffineState p.Q p.C j n :=
          (Nat.forall_lt_succ_right
            (p := fun i => ¬ p.D ∣ AffineState p.Q p.C i n)
            (n := j)).mp haff
        have hafflt : ∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n :=
          splitAff.left
        have hndA : ¬ p.D ∣ AffineState p.Q p.C j n := splitAff.right
        have hrawlt : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n :=
          ih.mpr hafflt
        have heq : Iterate (RawStep p) j n = AffineState p.Q p.C j n :=
          PrefixAffine p n j hrawlt
        have hnd : ¬ p.D ∣ Iterate (RawStep p) j n := by
          rw [heq]
          exact hndA
        exact
          (Nat.forall_lt_succ_right
            (p := fun i => ¬ p.D ∣ Iterate (RawStep p) i n)
            (n := j)).mpr ⟨hrawlt, hnd⟩
    }

/-- A first affine hit is the raw state, and the next raw step divides it once. -/
theorem FirstHitStep (p : Parameters) (n : ℤ) (j : ℕ) (h : IsFirstHit p n j) :
    Iterate (RawStep p) j n = AffineState p.Q p.C j n ∧
      Iterate (RawStep p) (j + 1) n = AffineState p.Q p.C j n / p.D := by
  unfold IsFirstHit at h
  obtain ⟨hdvd, haff⟩ := h
  -- No earlier affine hit, hence no earlier raw hit, by the second induction.
  have hraw : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n :=
    (DivisionFreePrefixIff p n j).mpr haff
  have heq : Iterate (RawStep p) j n = AffineState p.Q p.C j n :=
    PrefixAffine p n j hraw
  refine ⟨heq, ?_⟩
  have hdiv : p.D ∣ Iterate (RawStep p) j n := by
    rw [heq]
    exact hdvd
  have hnext : Iterate (RawStep p) (j + 1) n =
      RawStep p (Iterate (RawStep p) j n) := rfl
  -- One application of the division branch. Higher powers of `D` remain.
  have hbranch : RawStep p (Iterate (RawStep p) j n) =
      Iterate (RawStep p) j n / p.D :=
    RawStepDivide p (Iterate (RawStep p) j n) hdiv
  rw [hnext, hbranch]
  show Iterate (RawStep p) j n / p.D = AffineState p.Q p.C j n / p.D
  rw [heq]

end GeneralizedCollatz.SignedReturnStep
