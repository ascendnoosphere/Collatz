-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# The first-hit clock

If time `j` is the first time the affine state is divisible by the signed
divisor, the residue classes at times `0, …, j - 1` are nonzero and pairwise
distinct. They inject into a set of cardinality `|D| - 1`, so `j ≤ |D| - 1`.
Since `|D| ≥ 2`, this is the same bound as `j < |D|`.

Not proved here: existence of a first hit, equality of a raw iterate with the
affine state, and every construction after the hitting time.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.SignedReturnClock

/-- Affine state after `j` undivided steps, with offset sum `TrapSum q j`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- `j` is the first time `p.D` divides the affine state of the seed `n`. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n

/-- The class of the seed after `i` steps of `r ↦ q r + c` on `ℤ/|D|ℤ`. -/
def ResidueAt (p : Parameters) (n : ℤ) (i : ℕ) : ZMod p.D.natAbs :=
  Iterate (ResidueStepZ p) i ((n : ℤ) : ZMod p.D.natAbs)

/-- One undivided step is multiplication by `q` followed by addition of `c`. -/
theorem AffineStateStep (q c n : ℤ) (j : ℕ) :
    AffineState q c (j + 1) n = q * AffineState q c j n + c := by
  unfold AffineState
  rw [TrapSumRec, pow_succ]
  ring

/-- The affine state and the residue walk determine the same class at every time. -/
theorem AffineStateCast (p : Parameters) (n : ℤ) (j : ℕ) :
    ((AffineState p.Q p.C j n : ℤ) : ZMod p.D.natAbs) =
      ResidueAt p n j := by
  induction j with
  | zero => {
      have hstate : AffineState p.Q p.C 0 n = n := by
        unfold AffineState
        rw [show TrapSum p.Q 0 = 0 from rfl]
        rw [pow_zero, one_mul, mul_zero, add_zero]
      rw [hstate]
      unfold ResidueAt
      rfl
    }
  | succ j ih => {
      rw [AffineStateStep]
      have hstep : ResidueAt p n (j + 1) =
          ResidueStepZ p (ResidueAt p n j) := by
        unfold ResidueAt
        rfl
      rw [hstep, ResidueStepZ, Int.cast_add, Int.cast_mul, ih]
    }

/-- Divisibility by the signed divisor is vanishing in `ℤ/|D|ℤ`. -/
theorem DividesIffCastZero (p : Parameters) (z : ℤ) :
    p.D ∣ z ↔ ((z : ℤ) : ZMod p.D.natAbs) = 0 := by
  constructor
  · intro hdvd
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd z p.D.natAbs).mpr
      (Int.natAbs_dvd.mpr hdvd)
  · intro hzero
    exact Int.natAbs_dvd.mp
      ((ZMod.intCast_zmod_eq_zero_iff_dvd z p.D.natAbs).mp hzero)

/-- Extending the clock by `k` is `k` further steps of the residue walk. -/
theorem ResidueAtAdd (p : Parameters) (n : ℤ) (a k : ℕ) :
    ResidueAt p n (a + k) =
      Iterate (ResidueStepZ p) k (ResidueAt p n a) := by
  unfold ResidueAt
  exact IterateAdd (ResidueStepZ p) a k
    ((n : ℤ) : ZMod p.D.natAbs)

/-- Equal classes remain equal after the same number of further steps. -/
theorem ResidueAtAgree (p : Parameters) (n : ℤ) (a b k : ℕ)
    (h : ResidueAt p n a = ResidueAt p n b) :
    ResidueAt p n (a + k) = ResidueAt p n (b + k) := by
  rw [ResidueAtAdd, ResidueAtAdd, h]

/-- A first hit is the first zero of the residue walk. -/
theorem FirstHitResidue (p : Parameters) (n : ℤ) (j : ℕ)
    (h : IsFirstHit p n j) :
    ResidueAt p n j = 0 ∧
      ∀ i : ℕ, i < j → ResidueAt p n i ≠ 0 := by
  obtain ⟨hdvd, hfree⟩ := h
  refine ⟨?_, ?_⟩
  · have hcast :=
      (DividesIffCastZero p (AffineState p.Q p.C j n)).mp hdvd
    rw [AffineStateCast] at hcast
    exact hcast
  · intro i hi hzero
    have hcast :
        ((AffineState p.Q p.C i n : ℤ) : ZMod p.D.natAbs) = 0 := by
      rw [AffineStateCast]
      exact hzero
    exact hfree i hi ((DividesIffCastZero p _).mpr hcast)

/-- Classes before the first zero are pairwise distinct. -/
theorem ResidueAtDistinct (p : Parameters) (n : ℤ) (j a b : ℕ)
    (hzero : ResidueAt p n j = 0)
    (hnz : ∀ i : ℕ, i < j → ResidueAt p n i ≠ 0)
    (hab : a < b) (hbj : b < j) :
    ResidueAt p n a ≠ ResidueAt p n b := by
  intro heq
  have hbjle : b ≤ j := Nat.le_of_lt hbj
  have hsum : b + (j - b) = j := Nat.add_sub_of_le hbjle
  have hearly : a + (j - b) < j := by
    have hadd : a + (j - b) < b + (j - b) :=
      Nat.add_lt_add_right hab (j - b)
    rw [hsum] at hadd
    exact hadd
  have hshift : ResidueAt p n (a + (j - b)) =
      ResidueAt p n (b + (j - b)) :=
    ResidueAtAgree p n a b (j - b) heq
  rw [hsum, hzero] at hshift
  exact hnz (a + (j - b)) hearly hshift

/-- A nonzero class has canonical representative in `1, …, |D| - 1`. -/
theorem NonzeroIndexLt (p : Parameters) (r : ZMod p.D.natAbs)
    (hr : r ≠ 0) : r.val - 1 < p.D.natAbs - 1 := by
  have hm0 : p.D.natAbs ≠ 0 := by
    intro hzero
    have hadm := p.DAdmissible
    rw [hzero] at hadm
    exact Nat.not_succ_le_zero 1 hadm
  haveI : NeZero p.D.natAbs := ⟨hm0⟩
  have hstep : r.val - 1 < r.val :=
    Nat.sub_one_lt ((ZMod.val_ne_zero r).mpr hr)
  exact lt_of_lt_of_le hstep
    (Nat.le_sub_one_of_lt (ZMod.val_lt r))

/-- The predecessor of the canonical representative, in `Fin (|D| - 1)`. -/
def NonzeroIndex (p : Parameters) (r : ZMod p.D.natAbs) (hr : r ≠ 0) :
    Fin (p.D.natAbs - 1) :=
  ⟨r.val - 1, NonzeroIndexLt p r hr⟩

/-- `NonzeroIndex` subtracts one from the canonical representative. -/
theorem NonzeroIndexVal (p : Parameters) (r : ZMod p.D.natAbs)
    (hr : r ≠ 0) : (NonzeroIndex p r hr).val = r.val - 1 :=
  rfl

/-- A first hit occurs strictly before time `|D|`, hence at time at most `|D| - 1`. -/
theorem FirstHitClock (p : Parameters) (n : ℤ) (j : ℕ)
    (h : IsFirstHit p n j) :
    j < p.D.natAbs ∧ j ≤ p.D.natAbs - 1 := by
  obtain ⟨hzero, hnz⟩ := FirstHitResidue p n j h
  have hm0 : p.D.natAbs ≠ 0 := by
    intro hbad
    have hadm := p.DAdmissible
    rw [hbad] at hadm
    exact Nat.not_succ_le_zero 1 hadm
  haveI : NeZero p.D.natAbs := ⟨hm0⟩
  have hmpos : 0 < p.D.natAbs := Nat.pos_of_ne_zero hm0
  -- Times `0, …, j - 1` land in `Fin (|D| - 1)` through nonzero classes.
  let f : Fin j → Fin (p.D.natAbs - 1) := fun i =>
    NonzeroIndex p (ResidueAt p n i.val) (hnz i.val i.isLt)
  have hinj : Function.Injective f := by
    intro x y hxy
    unfold f at hxy
    have hpred : (ResidueAt p n x.val).val - 1 =
        (ResidueAt p n y.val).val - 1 := by
      have hvals := congrArg Fin.val hxy
      rw [NonzeroIndexVal, NonzeroIndexVal] at hvals
      exact hvals
    have hxpos : 1 ≤ (ResidueAt p n x.val).val := by
      have hxnz : (ResidueAt p n x.val).val ≠ 0 :=
        (ZMod.val_ne_zero _).mpr (hnz x.val x.isLt)
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hxnz)
    have hypos : 1 ≤ (ResidueAt p n y.val).val := by
      have hynz : (ResidueAt p n y.val).val ≠ 0 :=
        (ZMod.val_ne_zero _).mpr (hnz y.val y.isLt)
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hynz)
    have hvals : (ResidueAt p n x.val).val =
        (ResidueAt p n y.val).val := by
      have hxcancel := Nat.sub_add_cancel hxpos
      have hycancel := Nat.sub_add_cancel hypos
      rw [← hxcancel, ← hycancel]
      exact congrArg (fun t => t + 1) hpred
    have hres : ResidueAt p n x.val = ResidueAt p n y.val :=
      ZMod.val_injective p.D.natAbs hvals
    have hidx : x.val = y.val := by
      by_contra hne
      cases Nat.lt_or_gt_of_ne hne with
      | inl hlt => {
          exact ResidueAtDistinct p n j x.val y.val hzero hnz hlt
            y.isLt hres
        }
      | inr hgt => {
          exact ResidueAtDistinct p n j y.val x.val hzero hnz hgt
            x.isLt (Eq.symm hres)
        }
    exact Fin.ext hidx
  -- `Fin j` injects into a type of cardinality `|D| - 1`.
  have hcard : j ≤ p.D.natAbs - 1 := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective f hinj
  have hlt : j < p.D.natAbs := Nat.lt_of_le_sub_one hmpos hcard
  have hpred : j ≤ p.D.natAbs - 1 := Nat.le_sub_one_of_lt hlt
  exact ⟨hlt, hpred⟩

end GeneralizedCollatz.SignedReturnClock
