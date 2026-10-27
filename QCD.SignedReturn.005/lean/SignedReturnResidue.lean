-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Residue criterion for the first affine hit

The affine state `q ^ j * n + c * TrapSum q j` is the closed form of `j`
undivided steps. Its class in `ZMod |D|` is not a new recursion: it is the
`j`-th iterate of the residue step `r ↦ q * r + c`, starting at the class of
the seed. Zero in that ring is divisibility by `D`, so the first time `D`
divides the affine state is exactly the first time the residue walk is zero.
Seeds in the same class start the same walk, and therefore have the same first
hit.

Not proved here: existence of a first hit, any identification of the affine
state with a raw iterate, the orbit after the first division, a return
exponent, and every convergence statement.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.SignedReturnResidue

/-- Affine state after `j` undivided steps, with offset sum `TrapSum q j`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- `j` is the first time `D` divides the affine state of the seed `n`. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n

/-- At time zero the offset sum is empty, so the affine state is the seed. -/
theorem AffineStateZero (q c n : ℤ) : AffineState q c 0 n = n := by
  unfold AffineState
  have hpow : q ^ 0 = 1 := Int.pow_zero q
  have hsum : TrapSum q 0 = 0 := rfl
  rw [hpow, hsum]
  ring

/-- One further undivided step multiplies by `q` and adds `c`. -/
theorem AffineStateSucc (q c n : ℤ) (j : ℕ) :
    AffineState q c (j + 1) n = q * AffineState q c j n + c := by
  unfold AffineState
  -- `TrapSumRec` is the offset recursion `U_{j+1}(q) = q U_j(q) + 1`.
  have hrec : TrapSum q (j + 1) = q * TrapSum q j + 1 := TrapSumRec q j
  have hpow : q ^ (j + 1) = q * q ^ j := Int.pow_succ' q j
  rw [hrec, hpow]
  ring

/-- The zero class in `ZMod |D|` is divisibility by the signed divisor. -/
theorem CastZeroIffDvd (p : Parameters) (m : ℤ) :
    ((m : ℤ) : ZMod p.D.natAbs) = 0 ↔ p.D ∣ m := by
  constructor
  · {
      intro hzero
      -- `|D|` divides `m`, hence so does `D`.
      exact Int.natAbs_dvd.mp
        ((ZMod.intCast_zmod_eq_zero_iff_dvd m p.D.natAbs).mp hzero)
    }
  · {
      intro hdvd
      -- `D` divides `m`, hence so does `|D|`, and the class is zero.
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd m p.D.natAbs).mpr
        (Int.natAbs_dvd.mpr hdvd)
    }

/-- The class of the affine state is the residue walk of the seed. -/
theorem AffineCast (p : Parameters) (n : ℤ) (j : ℕ) :
    ((AffineState p.Q p.C j n : ℤ) : ZMod p.D.natAbs) =
      Iterate (ResidueStepZ p) j ((n : ℤ) : ZMod p.D.natAbs) := by
  induction j with
  | zero => {
      rw [AffineStateZero]
      rfl
    }
  | succ j ih => {
      -- The successor state is `Q * A_j + C`, and the cast is one residue step.
      rw [AffineStateSucc]
      have hiter : Iterate (ResidueStepZ p) (j + 1)
          ((n : ℤ) : ZMod p.D.natAbs) =
          ResidueStepZ p (Iterate (ResidueStepZ p) j
            ((n : ℤ) : ZMod p.D.natAbs)) := rfl
      rw [hiter, ← ih]
      show ((p.Q * AffineState p.Q p.C j n + p.C : ℤ) : ZMod p.D.natAbs) =
        ResidueStepZ p
          ((AffineState p.Q p.C j n : ℤ) : ZMod p.D.natAbs)
      -- The cast of a sum and of a product is one application of the residue step.
      rw [ResidueStepZ, Int.cast_add, Int.cast_mul]
    }

/-- `D` meets the affine state exactly when the residue walk is at zero. -/
theorem AffineDvdIffResidueZero (p : Parameters) (n : ℤ) (j : ℕ) :
    p.D ∣ AffineState p.Q p.C j n ↔
      Iterate (ResidueStepZ p) j ((n : ℤ) : ZMod p.D.natAbs) = 0 := by
  constructor
  · {
      intro hdvd
      have hzero : ((AffineState p.Q p.C j n : ℤ) : ZMod p.D.natAbs) = 0 :=
        (CastZeroIffDvd p (AffineState p.Q p.C j n)).mpr hdvd
      rw [AffineCast] at hzero
      exact hzero
    }
  · {
      intro hzero
      have hcast : ((AffineState p.Q p.C j n : ℤ) : ZMod p.D.natAbs) = 0 := by
        rw [AffineCast]
        exact hzero
      exact (CastZeroIffDvd p (AffineState p.Q p.C j n)).mp hcast
    }

/-- A first hit is the first zero of the residue walk, in both directions. -/
theorem FirstHitIffResidue (p : Parameters) (n : ℤ) (j : ℕ) :
    IsFirstHit p n j ↔
      Iterate (ResidueStepZ p) j ((n : ℤ) : ZMod p.D.natAbs) = 0 ∧
        ∀ i < j, Iterate (ResidueStepZ p) i
          ((n : ℤ) : ZMod p.D.natAbs) ≠ 0 := by
  unfold IsFirstHit
  constructor
  · {
      intro h
      obtain ⟨hj, hearly⟩ := h
      refine ⟨(AffineDvdIffResidueZero p n j).mp hj, ?_⟩
      intro i hi hzero
      exact hearly i hi ((AffineDvdIffResidueZero p n i).mpr hzero)
    }
  · {
      intro h
      obtain ⟨hj, hearly⟩ := h
      refine ⟨(AffineDvdIffResidueZero p n j).mpr hj, ?_⟩
      intro i hi hdvd
      exact hearly i hi ((AffineDvdIffResidueZero p n i).mp hdvd)
    }

/-- Equal starting classes have equal residue iterates at every time. -/
theorem ResidueIterateCongruent (p : Parameters) (n n' : ℤ)
    (h : ((n : ℤ) : ZMod p.D.natAbs) =
      ((n' : ℤ) : ZMod p.D.natAbs)) (i : ℕ) :
    Iterate (ResidueStepZ p) i ((n : ℤ) : ZMod p.D.natAbs) =
      Iterate (ResidueStepZ p) i ((n' : ℤ) : ZMod p.D.natAbs) := by
  induction i with
  | zero => {
      exact h
    }
  | succ i ih => {
      have hleft : Iterate (ResidueStepZ p) (i + 1)
          ((n : ℤ) : ZMod p.D.natAbs) =
          ResidueStepZ p (Iterate (ResidueStepZ p) i
            ((n : ℤ) : ZMod p.D.natAbs)) := rfl
      have hright : Iterate (ResidueStepZ p) (i + 1)
          ((n' : ℤ) : ZMod p.D.natAbs) =
          ResidueStepZ p (Iterate (ResidueStepZ p) i
            ((n' : ℤ) : ZMod p.D.natAbs)) := rfl
      rw [hleft, hright, ih]
    }

/-- A first hit passes from a seed to any seed in the same residue class. -/
theorem FirstHitOfCongruent (p : Parameters) (n n' : ℤ) (j : ℕ)
    (h : ((n : ℤ) : ZMod p.D.natAbs) =
      ((n' : ℤ) : ZMod p.D.natAbs))
    (hhit : IsFirstHit p n j) : IsFirstHit p n' j := by
  have hres : Iterate (ResidueStepZ p) j ((n : ℤ) : ZMod p.D.natAbs) = 0 ∧
      ∀ i < j, Iterate (ResidueStepZ p) i
        ((n : ℤ) : ZMod p.D.natAbs) ≠ 0 :=
    (FirstHitIffResidue p n j).mp hhit
  have hzero' : Iterate (ResidueStepZ p) j
      ((n' : ℤ) : ZMod p.D.natAbs) = 0 := by
    rw [← ResidueIterateCongruent p n n' h j]
    exact hres.left
  have hearly' : ∀ i < j, Iterate (ResidueStepZ p) i
      ((n' : ℤ) : ZMod p.D.natAbs) ≠ 0 := by
    intro i hi hzero
    have hzeroN : Iterate (ResidueStepZ p) i
        ((n : ℤ) : ZMod p.D.natAbs) = 0 := by
      rw [ResidueIterateCongruent p n n' h i]
      exact hzero
    exact hres.right i hi hzeroN
  exact (FirstHitIffResidue p n' j).mpr ⟨hzero', hearly'⟩

/-- Seeds with the same class in `ZMod |D|` have the same first hit. -/
theorem FirstHitCongruent (p : Parameters) (n n' : ℤ) (j : ℕ)
    (h : ((n : ℤ) : ZMod p.D.natAbs) =
      ((n' : ℤ) : ZMod p.D.natAbs)) :
    IsFirstHit p n j ↔ IsFirstHit p n' j := by
  constructor
  · {
      intro hhit
      exact FirstHitOfCongruent p n n' j h hhit
    }
  · {
      intro hhit
      exact FirstHitOfCongruent p n' n j h.symm hhit
    }

end GeneralizedCollatz.SignedReturnResidue
