-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Carry energy of one parity word

For odd positive `q` and `c`, the base-two branches are `x ↦ x / 2` and
`x ↦ (q x + c) / 2`. A finite parity word whose odd letters are strictly
contracting has a rational fixed point. The carry energy is the maximum
distance from the phases of that fixed point to the nearest positive
integer of the prescribed parity, with a tie taken downward. That energy
is either `0` or greater than `1 / 2`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.CarryGapAnalysis

/-- Residue `1` for an odd letter and `0` for an even letter. -/
def ParityBit (odd : Bool) : ℤ :=
  if odd then 1 else 0

/-- Index of the parity class sitting at most two below the rational. -/
def LowerIndex (odd : Bool) (x : ℚ) : ℤ :=
  ⌊(x - (ParityBit odd : ℚ)) / 2⌋

/-- Parity representative `ParityBit + 2 * LowerIndex`. -/
def LowerPoint (odd : Bool) (x : ℚ) : ℤ :=
  ParityBit odd + 2 * LowerIndex odd x

/-- Nearer of the two parity representatives in the length-two interval. -/
def RawNearest (odd : Bool) (x : ℚ) : ℤ :=
  if x ≤ ((LowerPoint odd x : ℤ) : ℚ) + 1 then LowerPoint odd x
  else LowerPoint odd x + 2

/-- Least positive integer of the prescribed parity. -/
def LeastPositive (odd : Bool) : ℤ :=
  if odd then 1 else 2

/-- Nearest positive integer of the prescribed parity, ties downward. -/
def NearestPositive (odd : Bool) (x : ℚ) : ℤ :=
  if RawNearest odd x ≤ 0 then LeastPositive odd else RawNearest odd x

/-- The integer has the parity named by the letter. -/
def HasParity (odd : Bool) (n : ℤ) : Prop :=
  match odd with
  | true => Odd n
  | false => Even n

/-- Positive integer of the parity named by the letter. -/
def PositiveParity (odd : Bool) (n : ℤ) : Prop :=
  0 < n ∧ HasParity odd n

/-- An absolute value on `ℚ` vanishes only at zero. -/
theorem AbsEqZero (a : ℚ) : |a| = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply le_antisymm
    · exact le_trans (le_abs_self a) (le_of_eq h)
    · have hneg : -a ≤ |a| := neg_le_abs a
      have : -a ≤ 0 := by
        rw [h] at hneg
        exact hneg
      linarith
  · intro h
    rw [h]
    simp

/-- The floor interval of length two contains the rational. -/
theorem LowerSandwich (odd : Bool) (x : ℚ) :
    ((LowerPoint odd x : ℤ) : ℚ) ≤ x ∧
      x < ((LowerPoint odd x : ℤ) : ℚ) + 2 := by
  let y : ℚ := (x - (ParityBit odd : ℚ)) / 2
  let k : ℤ := ⌊y⌋
  have hk : (k : ℚ) ≤ y ∧ y < (k : ℚ) + 1 :=
    (Int.floor_eq_iff).mp rfl
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hy : (2 : ℚ) * y = x - (ParityBit odd : ℚ) := by
    unfold y
    exact mul_div_cancel₀ _ h2
  have hle : (2 : ℚ) * (k : ℚ) ≤ (2 : ℚ) * y :=
    mul_le_mul_of_nonneg_left hk.1 (by norm_num : (0 : ℚ) ≤ 2)
  have hlt : (2 : ℚ) * y < (2 : ℚ) * ((k : ℚ) + 1) :=
    mul_lt_mul_of_pos_left hk.2 (by norm_num : (0 : ℚ) < 2)
  have hlo : ((LowerPoint odd x : ℤ) : ℚ) =
      (ParityBit odd : ℚ) + 2 * (k : ℚ) := by
    show ((ParityBit odd + 2 * ⌊y⌋ : ℤ) : ℚ) =
      (ParityBit odd : ℚ) + 2 * (k : ℚ)
    have hkdef : k = ⌊y⌋ := rfl
    rw [hkdef]
    norm_cast
  constructor
  · rw [hlo]
    linarith
  · rw [hlo]
    linarith

/-- The lower representative has the prescribed parity. -/
theorem LowerPointParity (odd : Bool) (x : ℚ) :
    HasParity odd (LowerPoint odd x) := by
  cases odd with
  | false => {
      unfold HasParity LowerPoint ParityBit
      refine ⟨LowerIndex false x, ?_⟩
      simp
      ring
    }
  | true => {
      unfold HasParity LowerPoint ParityBit
      refine ⟨LowerIndex true x, ?_⟩
      simp
      ring
    }

/-- Adding two preserves the prescribed parity. -/
theorem AddTwoParity (odd : Bool) (n : ℤ) (h : HasParity odd n) :
    HasParity odd (n + 2) := by
  cases odd with
  | false => {
      unfold HasParity at h ⊢
      rcases h with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [hk]
      ring
    }
  | true => {
      unfold HasParity at h ⊢
      rcases h with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      rw [hk]
      ring
    }

/-- Both raw representatives have the prescribed parity. -/
theorem RawNearestParity (odd : Bool) (x : ℚ) :
    HasParity odd (RawNearest odd x) := by
  by_cases hx : x ≤ ((LowerPoint odd x : ℤ) : ℚ) + 1
  · rw [RawNearest, if_pos hx]
    exact LowerPointParity odd x
  · rw [RawNearest, if_neg hx]
    exact AddTwoParity odd _ (LowerPointParity odd x)

/-- The least positive parity integer is positive and has that parity. -/
theorem LeastPositiveSpec (odd : Bool) :
    PositiveParity odd (LeastPositive odd) := by
  cases odd with
  | true => {
      unfold LeastPositive PositiveParity HasParity
      refine ⟨by decide, odd_one⟩
    }
  | false => {
      simp [LeastPositive, PositiveParity, HasParity]
    }

/-- The selected integer is a positive integer of the prescribed parity. -/
theorem NearestPositiveParity (odd : Bool) (x : ℚ) :
    PositiveParity odd (NearestPositive odd x) := by
  by_cases hraw : RawNearest odd x ≤ 0
  · rw [NearestPositive, if_pos hraw]
    exact LeastPositiveSpec odd
  · rw [NearestPositive, if_neg hraw]
    refine ⟨?_, RawNearestParity odd x⟩
    have : ¬ RawNearest odd x ≤ 0 := hraw
    omega

/-- Two integers of one parity differ by an even integer. -/
theorem SameParityStep (odd : Bool) (a b : ℤ)
    (ha : HasParity odd a) (hb : HasParity odd b) :
    ∃ t : ℤ, b = a + 2 * t := by
  cases odd with
  | false => {
      unfold HasParity at ha hb
      rcases ha with ⟨ra, hra⟩
      rcases hb with ⟨rb, hrb⟩
      refine ⟨rb - ra, ?_⟩
      rw [hra, hrb]
      ring
    }
  | true => {
      unfold HasParity at ha hb
      rcases ha with ⟨ka, hka⟩
      rcases hb with ⟨kb, hkb⟩
      refine ⟨kb - ka, ?_⟩
      rw [hka, hkb]
      ring
    }

/-- On one parity class, the raw representative is a nearest integer. -/
theorem LatticeDist (x : ℚ) (lo raw m t : ℤ)
    (hlo : (lo : ℚ) ≤ x) (hhi : x < (lo : ℚ) + 2)
    (hraw : raw = if x ≤ (lo : ℚ) + 1 then lo else lo + 2)
    (hm : m = lo + 2 * t) :
    |x - (raw : ℚ)| ≤ |x - (m : ℚ)| := by
  have hmcast : (m : ℚ) = (lo : ℚ) + 2 * (t : ℚ) := by
    rw [hm]
    norm_cast
  by_cases hx : x ≤ (lo : ℚ) + 1
  · have hraw' : raw = lo := by
      simp [hraw, hx]
    rw [hraw', hmcast]
    have habs : |x - (lo : ℚ)| = x - (lo : ℚ) := by
      apply abs_of_nonneg
      linarith
    by_cases ht0 : t = 0
    · simp [ht0]
    · by_cases htpos : 0 < t
      · have ht1 : (1 : ℤ) ≤ t := by omega
        have htq : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht1
        have hge : x - (lo : ℚ) ≤
            (lo : ℚ) + 2 * (t : ℚ) - x := by
          have hx1 : x - (lo : ℚ) ≤ 1 := by linarith
          linarith
        have hnn : 0 ≤ (lo : ℚ) + 2 * (t : ℚ) - x := by linarith
        rw [habs, abs_sub_comm, abs_of_nonneg hnn]
        exact hge
      · have ht1 : t ≤ -1 := by omega
        have htq : (t : ℚ) ≤ -1 := by exact_mod_cast ht1
        have hnn : 0 ≤ x - ((lo : ℚ) + 2 * (t : ℚ)) := by linarith
        rw [habs, abs_of_nonneg hnn]
        linarith
  · have hraw' : raw = lo + 2 := by
      simp [hraw, hx]
    rw [hraw', hmcast]
    have hrawcast : ((lo + 2 : ℤ) : ℚ) = (lo : ℚ) + 2 := by
      norm_cast
    rw [hrawcast]
    have habs : |x - ((lo : ℚ) + 2)| = (lo : ℚ) + 2 - x := by
      have hnonpos : x - ((lo : ℚ) + 2) ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      ring
    by_cases ht1 : t = 1
    · simp [ht1]
    · by_cases hthi : 1 < t
      · have ht2 : (2 : ℤ) ≤ t := by omega
        have htq : (2 : ℚ) ≤ (t : ℚ) := by exact_mod_cast ht2
        have hnn : 0 ≤ (lo : ℚ) + 2 * (t : ℚ) - x := by linarith
        rw [habs, abs_sub_comm, abs_of_nonneg hnn]
        linarith
      · have ht0 : t ≤ 0 := by omega
        have htq : (t : ℚ) ≤ 0 := by exact_mod_cast ht0
        have hnn : 0 ≤ x - ((lo : ℚ) + 2 * (t : ℚ)) := by linarith
        rw [habs, abs_of_nonneg hnn]
        linarith

/-- A parity integer below the raw choice is strictly farther. -/
theorem LatticeStrict (x : ℚ) (lo raw m t : ℤ)
    (hlo : (lo : ℚ) ≤ x) (hhi : x < (lo : ℚ) + 2)
    (hraw : raw = if x ≤ (lo : ℚ) + 1 then lo else lo + 2)
    (hm : m = lo + 2 * t) (hlt : m < raw) :
    |x - (raw : ℚ)| < |x - (m : ℚ)| := by
  have hmcast : (m : ℚ) = (lo : ℚ) + 2 * (t : ℚ) := by
    rw [hm]
    norm_cast
  by_cases hx : x ≤ (lo : ℚ) + 1
  · have hraw' : raw = lo := by
      simp [hraw, hx]
    rw [hraw'] at hlt
    have htneg : t ≤ -1 := by
      rw [hm] at hlt
      omega
    have htq : (t : ℚ) ≤ -1 := by exact_mod_cast htneg
    rw [hraw', hmcast]
    have habs : |x - (lo : ℚ)| = x - (lo : ℚ) := by
      apply abs_of_nonneg
      linarith
    have hnn : 0 ≤ x - ((lo : ℚ) + 2 * (t : ℚ)) := by linarith
    rw [habs, abs_of_nonneg hnn]
    linarith
  · have hraw' : raw = lo + 2 := by
      simp [hraw, hx]
    rw [hraw'] at hlt
    have ht0 : t ≤ 0 := by
      rw [hm] at hlt
      omega
    have htq : (t : ℚ) ≤ 0 := by exact_mod_cast ht0
    rw [hraw', hmcast]
    have hrawcast : ((lo + 2 : ℤ) : ℚ) = (lo : ℚ) + 2 := by
      norm_cast
    rw [hrawcast]
    have habs : |x - ((lo : ℚ) + 2)| = (lo : ℚ) + 2 - x := by
      have hnonpos : x - ((lo : ℚ) + 2) ≤ 0 := by linarith
      rw [abs_of_nonpos hnonpos]
      ring
    have hnn : 0 ≤ x - ((lo : ℚ) + 2 * (t : ℚ)) := by linarith
    rw [habs, abs_of_nonneg hnn]
    have hx1 : (lo : ℚ) + 1 < x := by
      exact lt_of_not_ge hx
    linarith

/-- If the raw representative is not positive, the rational is at most the least one. -/
theorem RawNonposLeLeast (odd : Bool) (x : ℚ)
    (hraw : RawNearest odd x ≤ 0) :
    x ≤ (LeastPositive odd : ℚ) := by
  have hs := LowerSandwich odd x
  have hlo : (LowerPoint odd x : ℚ) ≤ x := hs.1
  have hhi : x < (LowerPoint odd x : ℚ) + 2 := hs.2
  by_cases hx : x ≤ ((LowerPoint odd x : ℤ) : ℚ) + 1
  · have hrawlo : RawNearest odd x = LowerPoint odd x := by
      rw [RawNearest, if_pos hx]
    have hnonpos : LowerPoint odd x ≤ 0 := by
      rw [hrawlo] at hraw
      exact hraw
    have hcast : (LowerPoint odd x : ℚ) ≤ 0 := by
      exact_mod_cast hnonpos
    have hx1 : x ≤ 1 := by
      linarith
    cases odd with
    | true => {
        simp [LeastPositive]
        exact hx1
      }
    | false => {
        simp [LeastPositive]
        linarith
      }
  · have hrawhi : RawNearest odd x = LowerPoint odd x + 2 := by
      rw [RawNearest, if_neg hx]
    have hnonpos : LowerPoint odd x + 2 ≤ 0 := by
      rw [hrawhi] at hraw
      exact hraw
    have hcast : (LowerPoint odd x : ℚ) + 2 ≤ 0 := by
      exact_mod_cast hnonpos
    have hx0 : x < 0 := by
      linarith
    cases odd with
    | true => {
        simp [LeastPositive]
        linarith
      }
    | false => {
        simp [LeastPositive]
        linarith
      }

/-- Every positive parity integer is at least the least one. -/
theorem LeastLe (odd : Bool) (m : ℤ) (hm : PositiveParity odd m) :
    LeastPositive odd ≤ m := by
  cases odd with
  | true => {
      simp [LeastPositive]
      have hodd : Odd m := by
        unfold PositiveParity HasParity at hm
        exact hm.2
      rcases hodd with ⟨k, hk⟩
      have hmpos : 0 < m := hm.1
      rw [hk] at hmpos ⊢
      omega
    }
  | false => {
      simp [LeastPositive]
      have heven : Even m := by
        unfold PositiveParity HasParity at hm
        exact hm.2
      rcases heven with ⟨k, hk⟩
      have hmpos : 0 < m := hm.1
      rw [hk] at hmpos ⊢
      omega
    }

/-- The positive replacement is at least as near as every positive parity integer. -/
theorem ReplacedDist (odd : Bool) (x : ℚ) (m : ℤ)
    (hraw : RawNearest odd x ≤ 0) (hm : PositiveParity odd m) :
    |x - (LeastPositive odd : ℚ)| ≤ |x - (m : ℚ)| := by
  have hx : x ≤ (LeastPositive odd : ℚ) :=
    RawNonposLeLeast odd x hraw
  have hmle : LeastPositive odd ≤ m := LeastLe odd m hm
  have hmcast : (LeastPositive odd : ℚ) ≤ (m : ℚ) := by
    exact_mod_cast hmle
  have hnn : 0 ≤ (LeastPositive odd : ℚ) - x := by linarith
  have hnnm : 0 ≤ (m : ℚ) - x := by linarith
  have habs : |x - (LeastPositive odd : ℚ)| =
      (LeastPositive odd : ℚ) - x := by
    rw [abs_sub_comm]
    exact abs_of_nonneg hnn
  have habsm : |x - (m : ℚ)| = (m : ℚ) - x := by
    rw [abs_sub_comm]
    exact abs_of_nonneg hnnm
  rw [habs, habsm]
  linarith

/-- The selected integer minimizes the distance among positive parity integers. -/
theorem NearestPositiveMin (odd : Bool) (x : ℚ) (m : ℤ)
    (hm : PositiveParity odd m) :
    |x - (NearestPositive odd x : ℚ)| ≤ |x - (m : ℚ)| := by
  by_cases hraw : RawNearest odd x ≤ 0
  · rw [NearestPositive, if_pos hraw]
    exact ReplacedDist odd x m hraw hm
  · rw [NearestPositive, if_neg hraw]
    have hs := LowerSandwich odd x
    rcases SameParityStep odd (LowerPoint odd x) m
        (LowerPointParity odd x) hm.2 with ⟨t, ht⟩
    have hform : RawNearest odd x =
        if x ≤ ((LowerPoint odd x : ℤ) : ℚ) + 1 then
          LowerPoint odd x else LowerPoint odd x + 2 := by
      rfl
    exact LatticeDist x (LowerPoint odd x) (RawNearest odd x) m t
      hs.1 hs.2 hform ht

/-- Equal distance forces the selected integer to be the smaller one. -/
theorem NearestPositiveTie (odd : Bool) (x : ℚ) (m : ℤ)
    (hm : PositiveParity odd m)
    (heq : |x - (NearestPositive odd x : ℚ)| = |x - (m : ℚ)|) :
    NearestPositive odd x ≤ m := by
  by_cases hraw : RawNearest odd x ≤ 0
  · rw [NearestPositive, if_pos hraw]
    exact LeastLe odd m hm
  · rw [NearestPositive, if_neg hraw]
    have hs := LowerSandwich odd x
    rcases SameParityStep odd (LowerPoint odd x) m
        (LowerPointParity odd x) hm.2 with ⟨t, ht⟩
    have hform : RawNearest odd x =
        if x ≤ ((LowerPoint odd x : ℤ) : ℚ) + 1 then
          LowerPoint odd x else LowerPoint odd x + 2 := by
      rfl
    by_cases hlt : m < RawNearest odd x
    · have hstrict := LatticeStrict x (LowerPoint odd x)
        (RawNearest odd x) m t hs.1 hs.2 hform ht hlt
      have hne : |x - (RawNearest odd x : ℚ)| ≠
          |x - (m : ℚ)| := ne_of_lt hstrict
      rw [NearestPositive, if_neg hraw] at heq
      exact False.elim (hne heq)
    · omega

/-- A positive parity integer is its own nearest positive parity integer. -/
theorem NearestPositiveSelf (odd : Bool) (n : ℤ)
    (hn : PositiveParity odd n) :
    NearestPositive odd (n : ℚ) = n := by
  have hmin := NearestPositiveMin odd (n : ℚ) n hn
  have hle : |((n : ℚ) - (NearestPositive odd (n : ℚ) : ℚ))| ≤ 0 := by
    simpa using hmin
  have heq : (n : ℚ) - (NearestPositive odd (n : ℚ) : ℚ) = 0 := by
    exact (AbsEqZero _).mp (le_antisymm hle (abs_nonneg _))
  have hcast : (NearestPositive odd (n : ℚ) : ℚ) = (n : ℚ) := by
    linarith
  exact_mod_cast hcast

/-- One base-two branch: halving, or the odd affine step. -/
def Shortcut (q c : ℕ) (odd : Bool) (x : ℚ) : ℚ :=
  if odd then ((q : ℚ) * x + (c : ℚ)) / 2 else x / 2

/-- Scale of one branch: `q / 2` on an odd letter and `1 / 2` on an even letter. -/
def BranchScale (q : ℕ) (odd : Bool) : ℚ :=
  if odd then (q : ℚ) / 2 else (1 : ℚ) / 2

/-- The branch is affine, with slope `BranchScale`. -/
theorem ShortcutAdd (q c : ℕ) (odd : Bool) (n : ℤ) (eta : ℚ) :
    Shortcut q c odd ((n : ℚ) + eta) =
      Shortcut q c odd (n : ℚ) + BranchScale q odd * eta := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  cases odd with
  | true => {
      unfold Shortcut BranchScale
      simp
      ring
    }
  | false => {
      unfold Shortcut BranchScale
      simp
      ring
    }

/-- Every branch scale is nonnegative. -/
theorem BranchScaleNonneg (q : ℕ) (odd : Bool) :
    0 ≤ BranchScale q odd := by
  cases odd with
  | true => {
      unfold BranchScale
      simp
      exact div_nonneg (Nat.cast_nonneg q) (by norm_num)
    }
  | false => {
      unfold BranchScale
      simp
    }

/-- Iterate a word from the left, one shortcut at a time. -/
def DropShortcut (q c : ℕ) : List Bool → ℚ → ℕ → ℚ
  | _, x, 0 => x
  | [], x, _ => x
  | b :: bs, x, i + 1 =>
    DropShortcut q c bs (Shortcut q c b x) i

/-- The letter at an index, or `false` past the end of the word. -/
def BitAt : List Bool → ℕ → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, i + 1 => BitAt bs i

/-- One more shortcut applies the letter at that index. -/
theorem DropSucc (q c : ℕ) (w : List Bool) (x : ℚ) (i : ℕ)
    (hi : i < w.length) :
    DropShortcut q c w x (i + 1) =
      Shortcut q c (BitAt w i) (DropShortcut q c w x i) := by
  induction i generalizing w x with
  | zero => {
      cases w with
      | nil => {
          simp at hi
        }
      | cons b bs => {
          simp [DropShortcut, BitAt]
        }
    }
  | succ i ih => {
      cases w with
      | nil => {
          simp at hi
        }
      | cons b bs => {
          have hi' : i < bs.length := by
            simp at hi
            omega
          simpa [DropShortcut, BitAt] using
            ih bs (Shortcut q c b x) hi'
        }
    }

/-- Multiplier and offset of the affine word map. -/
structure WordData where
  mult : ℕ
  offset : ℕ

/-- Affine data of a word, first letter applied first. -/
def WordAffine (q : ℕ) : List Bool → WordData
  | [] => ⟨1, 0⟩
  | b :: bs =>
    let r := WordAffine q bs
    if b then ⟨q * r.mult, r.mult + 2 * r.offset⟩
    else ⟨r.mult, 2 * r.offset⟩

/-- Number of odd letters in a word. -/
def OddCount : List Bool → ℕ
  | [] => 0
  | true :: bs => OddCount bs + 1
  | false :: bs => OddCount bs

/-- The affine multiplier is `q` to the number of odd letters. -/
theorem WordAffineMultEq (q : ℕ) (w : List Bool) :
    (WordAffine q w).mult = q ^ OddCount w := by
  induction w with
  | nil => {
      simp [WordAffine, OddCount]
    }
  | cons b bs ih => {
      cases b with
      | false => {
          simp [WordAffine, OddCount, ih]
        }
      | true => {
          simp [WordAffine, OddCount, ih, pow_succ, Nat.mul_comm]
        }
    }

/-- Appending a letter multiplies the multiplier only when the letter is odd. -/
theorem WordAffineMultSnoc (q : ℕ) (u : List Bool) (b : Bool) :
    (WordAffine q (u ++ [b])).mult =
      (if b then q else 1) * (WordAffine q u).mult := by
  induction u with
  | nil => {
      cases b with
      | false => {
          simp [WordAffine]
        }
      | true => {
          simp [WordAffine]
        }
    }
  | cons c cs ih => {
      cases c with
      | false => {
          simp [WordAffine, ih]
        }
      | true => {
          simp [WordAffine, ih]
        }
    }

/-- A prefix of length `t + 1` is the prefix of length `t` plus the next letter. -/
theorem TakeSuccBit (w : List Bool) (t : ℕ) (ht : t < w.length) :
    w.take (t + 1) = w.take t ++ [BitAt w t] := by
  induction t generalizing w with
  | zero => {
      cases w with
      | nil => {
          simp at ht
        }
      | cons b bs => {
          simp [BitAt, List.take]
        }
    }
  | succ t ih => {
      cases w with
      | nil => {
          simp at ht
        }
      | cons b bs => {
          have ht' : t < bs.length := by
            simp at ht
            omega
          have ih' := ih bs ht'
          simp [BitAt, List.take, ih']
        }
    }

/-- Product of the first `t` branch scales. -/
def ScaleTo (q : ℕ) (w : List Bool) : ℕ → ℚ
  | 0 => 1
  | t + 1 => ScaleTo q w t * BranchScale q (BitAt w t)

/-- The partial scale product is the prefix multiplier over `2 ^ t`. -/
theorem ScaleToTake (q : ℕ) (w : List Bool) (t : ℕ)
    (ht : t ≤ w.length) :
    ScaleTo q w t =
      ((WordAffine q (w.take t)).mult : ℚ) / (2 : ℚ) ^ t := by
  induction t with
  | zero => {
      simp [ScaleTo, List.take, WordAffine]
    }
  | succ t ih => {
      have ht' : t < w.length := Nat.lt_of_succ_le ht
      have ih' := ih (Nat.le_of_lt ht')
      have htake := TakeSuccBit w t ht'
      have hsnoc := WordAffineMultSnoc q (w.take t) (BitAt w t)
      rw [← htake] at hsnoc
      rw [ScaleTo, ih']
      have h2 : (2 : ℚ) ≠ 0 := by norm_num
      have hpow : (2 : ℚ) ^ (t + 1) ≠ 0 := pow_ne_zero _ h2
      cases hb : BitAt w t with
      | false => {
          have hmul : (WordAffine q (w.take (t + 1))).mult =
              (WordAffine q (w.take t)).mult := by
            simpa [hb] using hsnoc
          have hscale : BranchScale q false = (1 : ℚ) / 2 := by
            simp [BranchScale]
          rw [hscale, hmul, pow_succ]
          field_simp
        }
      | true => {
          have hmul : (WordAffine q (w.take (t + 1))).mult =
              q * (WordAffine q (w.take t)).mult := by
            simpa [hb] using hsnoc
          have hscale : BranchScale q true = (q : ℚ) / 2 := by
            simp [BranchScale]
          have hcast :
              ((q * (WordAffine q (w.take t)).mult : ℕ) : ℚ) =
                (q : ℚ) *
                  ((WordAffine q (w.take t)).mult : ℚ) := by
            norm_cast
          rw [hscale, hmul, hcast, pow_succ]
          field_simp
        }
    }

/-- Full scale product of a word. -/
theorem ScaleToLength (q : ℕ) (w : List Bool) :
    ScaleTo q w w.length =
      ((WordAffine q w).mult : ℚ) / (2 : ℚ) ^ w.length := by
  rw [ScaleToTake q w w.length (Nat.le_refl _)]
  simp

/-- Rational fixed point of a strictly contracting word. -/
def Fixed (q c : ℕ) (w : List Bool) : ℚ :=
  let a := WordAffine q w
  ((c : ℚ) * (a.offset : ℚ)) /
    ((2 : ℚ) ^ w.length - (a.mult : ℚ))

/-- The word map is the affine polynomial with the stored multiplier and offset. -/
theorem DropLengthFormula (q c : ℕ) (w : List Bool) (x : ℚ) :
    DropShortcut q c w x w.length =
      (((WordAffine q w).mult : ℚ) * x +
        (c : ℚ) * ((WordAffine q w).offset : ℚ)) /
      ((2 : ℚ) ^ w.length) := by
  induction w generalizing x with
  | nil => {
      simp [DropShortcut, WordAffine]
    }
  | cons b bs ih => {
      have hdrop : DropShortcut q c (b :: bs) x (b :: bs).length =
          DropShortcut q c bs (Shortcut q c b x) bs.length := by
        rfl
      rw [hdrop]
      have ihx := ih (Shortcut q c b x)
      rw [ihx]
      have h2 : (2 : ℚ) ≠ 0 := by norm_num
      have hdenL : (2 : ℚ) ^ bs.length ≠ 0 := pow_ne_zero _ h2
      have hdenR : (2 : ℚ) ^ (b :: bs).length ≠ 0 :=
        pow_ne_zero _ h2
      cases b with
      | false => {
          have hS : Shortcut q c false x = x / 2 := by
            simp [Shortcut]
          have hM : (WordAffine q (false :: bs)).mult =
              (WordAffine q bs).mult := by
            simp [WordAffine]
          have hO :
              ((WordAffine q (false :: bs)).offset : ℚ) =
                2 * ((WordAffine q bs).offset : ℚ) := by
            have hnat : (WordAffine q (false :: bs)).offset =
                2 * (WordAffine q bs).offset := by
              simp [WordAffine]
            rw [hnat]
            norm_cast
          rw [hS, hM, hO]
          refine (div_eq_div_iff hdenL hdenR).mpr ?_
          rw [List.length_cons, pow_succ]
          ring
        }
      | true => {
          have hS : Shortcut q c true x =
              ((q : ℚ) * x + (c : ℚ)) / 2 := by
            simp [Shortcut]
          have hM : ((WordAffine q (true :: bs)).mult : ℚ) =
              (q : ℚ) * ((WordAffine q bs).mult : ℚ) := by
            have hnat : (WordAffine q (true :: bs)).mult =
                q * (WordAffine q bs).mult := by
              simp [WordAffine]
            rw [hnat]
            norm_cast
          have hO : ((WordAffine q (true :: bs)).offset : ℚ) =
              ((WordAffine q bs).mult : ℚ) +
                2 * ((WordAffine q bs).offset : ℚ) := by
            have hnat : (WordAffine q (true :: bs)).offset =
                (WordAffine q bs).mult +
                  2 * (WordAffine q bs).offset := by
              simp [WordAffine]
            rw [hnat]
            norm_cast
          rw [hS, hM, hO]
          refine (div_eq_div_iff hdenL hdenR).mpr ?_
          rw [List.length_cons, pow_succ]
          ring
        }
    }

/-- Phase `i` of the fixed point along the word. -/
def Phase (q c : ℕ) (w : List Bool) (i : ℕ) : ℚ :=
  DropShortcut q c w (Fixed q c w) i

/-- The phase at time zero is the fixed point. -/
theorem PhaseZero (q c : ℕ) (w : List Bool) :
    Phase q c w 0 = Fixed q c w := by
  simp [Phase, DropShortcut]

/-- A strict inequality of natural numbers remains nonzero after casting. -/
theorem DenomNeZero (q : ℕ) (w : List Bool)
    (hcon : (WordAffine q w).mult < 2 ^ w.length) :
    ((2 : ℚ) ^ w.length - ((WordAffine q w).mult : ℚ)) ≠ 0 := by
  intro h
  have hEq : (2 : ℚ) ^ w.length = ((WordAffine q w).mult : ℚ) := by
    linarith
  have hnat : 2 ^ w.length = (WordAffine q w).mult := by
    exact_mod_cast hEq
  omega

/-- The fixed point is closed under the whole word. -/
theorem PhaseLength (q c : ℕ) (w : List Bool)
    (hcon : (WordAffine q w).mult < 2 ^ w.length) :
    Phase q c w w.length = Phase q c w 0 := by
  rw [PhaseZero]
  unfold Phase
  rw [DropLengthFormula]
  unfold Fixed
  have hne := DenomNeZero q w hcon
  field_simp
  ring

/-- Letter used by the error at an index, wrapping the final return to the first letter. -/
def WrappedBit (w : List Bool) (t : ℕ) : Bool :=
  if t = w.length then BitAt w 0 else BitAt w t

/-- Before the end of the word, the wrapped letter is the letter itself. -/
theorem WrappedBitLt (w : List Bool) (t : ℕ) (ht : t < w.length) :
    WrappedBit w t = BitAt w t := by
  have hne : t ≠ w.length := by omega
  unfold WrappedBit
  rw [if_neg hne]

/-- The return index uses the first letter. -/
theorem WrappedBitLength (w : List Bool) :
    WrappedBit w w.length = BitAt w 0 := by
  unfold WrappedBit
  rw [if_pos rfl]

/-- A contracting word is nonempty. -/
theorem LengthPos (q : ℕ) (w : List Bool)
    (hcon : q ^ OddCount w < 2 ^ w.length) :
    0 < w.length := by
  cases w with
  | nil => {
      simp [OddCount, pow_zero] at hcon
    }
  | cons _ _ => {
      simp
    }

/-- The index zero uses the first letter when the word is nonempty. -/
theorem WrappedBitZero (w : List Bool) (hw : 0 < w.length) :
    WrappedBit w 0 = BitAt w 0 := by
  have hne : 0 ≠ w.length := by omega
  unfold WrappedBit
  rw [if_neg hne]

/-- Integer value of one branch on an integer input. -/
def IntBranch (q c : ℕ) (odd : Bool) (n : ℤ) : ℤ :=
  if odd then ((q : ℤ) * n + (c : ℤ)) / 2 else n / 2

/-- On a parity integer, the rational branch agrees with integer division. -/
theorem IntBranchCast (q c : ℕ) (odd : Bool) (n : ℤ)
    (hq : Odd q) (hc : Odd c) (hp : HasParity odd n) :
    Shortcut q c odd (n : ℚ) = ((IntBranch q c odd n : ℤ) : ℚ) := by
  cases odd with
  | true => {
      unfold HasParity at hp
      have hqz : Odd (q : ℤ) := Odd.natCast hq
      have hcz : Odd (c : ℤ) := Odd.natCast hc
      have hqn : Odd ((q : ℤ) * n) := Odd.mul hqz hp
      have heven : Even ((q : ℤ) * n + (c : ℤ)) :=
        Odd.add_odd hqn hcz
      rcases Even.two_dvd heven with ⟨k, hk⟩
      have hkdiv : IntBranch q c true n = k := by
        unfold IntBranch
        simp
        exact Int.ediv_eq_of_eq_mul_right (by decide) hk
      unfold Shortcut
      simp
      rw [hkdiv]
      have hsum : ((q : ℚ) * (n : ℚ) + (c : ℚ)) =
          (((q : ℤ) * n + (c : ℤ) : ℤ) : ℚ) := by
        norm_cast
      rw [hsum, hk]
      have hcast : ((2 * k : ℤ) : ℚ) = (2 : ℚ) * (k : ℚ) := by
        norm_cast
      have h2 : (2 : ℚ) ≠ 0 := by norm_num
      rw [hcast, mul_div_cancel_left₀ _ h2]
    }
  | false => {
      unfold HasParity at hp
      rcases Even.two_dvd hp with ⟨k, hk⟩
      have hkdiv : IntBranch q c false n = k := by
        unfold IntBranch
        simp
        exact Int.ediv_eq_of_eq_mul_right (by decide) hk
      unfold Shortcut
      simp
      rw [hkdiv]
      rw [hk]
      have hcast : ((2 * k : ℤ) : ℚ) = (2 : ℚ) * (k : ℚ) := by
        norm_cast
      have h2 : (2 : ℚ) ≠ 0 := by norm_num
      rw [hcast, mul_div_cancel_left₀ _ h2]
    }

/-- Integer carry across one edge. -/
def Carry (q c : ℕ) (odd : Bool) (n nNext : ℤ) : ℤ :=
  IntBranch q c odd n - nNext

/-- Signed distance from a phase to its selected parity integer. -/
def SignedErr (q c : ℕ) (w : List Bool) (t : ℕ) : ℚ :=
  Phase q c w t -
    (NearestPositive (WrappedBit w t) (Phase q c w t) : ℚ)

/-- The return error equals the initial error. -/
theorem SignedErrLength (q c : ℕ) (w : List Bool)
    (hcon : (WordAffine q w).mult < 2 ^ w.length) :
    SignedErr q c w w.length = SignedErr q c w 0 := by
  have hcount : q ^ OddCount w < 2 ^ w.length := by
    rw [← WordAffineMultEq]
    exact hcon
  have hw := LengthPos q w hcount
  unfold SignedErr
  rw [PhaseLength q c w hcon, WrappedBitLength w, WrappedBitZero w hw]

/-- One error step is the branch scale times the previous error, plus an integer carry. -/
theorem SignedErrSucc (q c : ℕ) (w : List Bool) (t : ℕ)
    (hq : Odd q) (hc : Odd c) (ht : t < w.length) :
    SignedErr q c w (t + 1) =
      BranchScale q (BitAt w t) * SignedErr q c w t +
        ((Carry q c (BitAt w t)
          (NearestPositive (BitAt w t) (Phase q c w t))
          (NearestPositive (WrappedBit w (t + 1))
            (Phase q c w (t + 1))) : ℤ) : ℚ) := by
  have hstep : Phase q c w (t + 1) =
      Shortcut q c (BitAt w t) (Phase q c w t) := by
    unfold Phase
    exact DropSucc q c w (Fixed q c w) t ht
  have hwrap : WrappedBit w t = BitAt w t := WrappedBitLt w t ht
  set b : Bool := BitAt w t
  set ξ : ℚ := Phase q c w t
  set ξ' : ℚ := Phase q c w (t + 1)
  set n : ℤ := NearestPositive b ξ
  set n' : ℤ := NearestPositive (WrappedBit w (t + 1)) ξ'
  have hnpar : HasParity b n :=
    (NearestPositiveParity b ξ).2
  have hdec := ShortcutAdd q c b n (ξ - (n : ℚ))
  have hback : (n : ℚ) + (ξ - (n : ℚ)) = ξ := by ring
  rw [hback] at hdec
  have hcast := IntBranchCast q c b n hq hc hnpar
  have hξ' : ξ' = (IntBranch q c b n : ℚ) +
      BranchScale q b * (ξ - (n : ℚ)) := by
    rw [← hcast]
    exact hstep.trans hdec
  have hsign : SignedErr q c w t = ξ - (n : ℚ) := by
    unfold SignedErr
    rw [hwrap]
  unfold SignedErr Carry
  rw [hwrap]
  change ξ' - (n' : ℚ) =
    BranchScale q b * (ξ - (n : ℚ)) +
      ((IntBranch q c b n - n' : ℤ) : ℚ)
  rw [hξ', Int.cast_sub]
  ring

/-- Absolute phase error at an index before the end of the word. -/
def AbsErr (q c : ℕ) (w : List Bool) (i : ℕ) : ℚ :=
  |Phase q c w i - (NearestPositive (BitAt w i) (Phase q c w i) : ℚ)|

/-- Before the end, the absolute error is the absolute signed error. -/
theorem AbsErrEq (q c : ℕ) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    AbsErr q c w i = |SignedErr q c w i| := by
  unfold AbsErr SignedErr
  rw [WrappedBitLt w i hi]

/-- Absolute errors at the indices strictly below `i`. -/
def ErrBelow (q c : ℕ) (w : List Bool) : ℕ → List ℚ
  | 0 => []
  | i + 1 =>
    if _ : i < w.length then
      ErrBelow q c w i ++ [AbsErr q c w i]
    else
      ErrBelow q c w i

/-- One more in-range index appends that absolute error. -/
theorem ErrBelowSucc (q c : ℕ) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    ErrBelow q c w (i + 1) = ErrBelow q c w i ++ [AbsErr q c w i] := by
  simp [ErrBelow, hi]

/-- Maximum of a rational list, with empty list read as zero. -/
def MaxList : List ℚ → ℚ
  | [] => 0
  | a :: as => max a (MaxList as)

/-- Every list entry is at most the list maximum. -/
theorem MaxListMemLe (a : ℚ) (l : List ℚ) (ha : a ∈ l) :
    a ≤ MaxList l := by
  induction l with
  | nil => {
      cases ha
    }
  | cons b bs ih => {
      cases ha with
      | head => {
          exact le_max_left _ _
        }
      | tail _ htail => {
          exact le_trans (ih htail) (le_max_right _ _)
        }
    }

/-- A list of zeros has maximum zero. -/
theorem MaxListZero (l : List ℚ) (h : ∀ a ∈ l, a = 0) :
    MaxList l = 0 := by
  induction l with
  | nil => {
      rfl
    }
  | cons b bs ih => {
      have hb : b = 0 := h b (List.Mem.head _)
      have ht : MaxList bs = 0 := by
        apply ih
        intro a ha
        exact h a (List.Mem.tail _ ha)
      simp [MaxList, hb, ht]
    }

/-- Carry energy of a word: maximum absolute phase error. -/
def CarryEnergy (q c : ℕ) (w : List Bool) : ℚ :=
  MaxList (ErrBelow q c w w.length)

/-- Each absolute error occurs in the energy list. -/
theorem AbsErrMem (q c : ℕ) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    AbsErr q c w j ∈ ErrBelow q c w w.length := by
  have hmem : ∀ i, j < i → i ≤ w.length →
      AbsErr q c w j ∈ ErrBelow q c w i := by
    intro i
    induction i with
    | zero => {
        intro hj0
        omega
      }
    | succ i ih => {
        intro hji hi
        have hi' : i < w.length := by omega
        rw [ErrBelowSucc q c w i hi']
        by_cases hlt : j < i
        · exact List.mem_append_left _ (ih hlt (Nat.le_of_lt hi'))
        · have hjEq : j = i := by omega
          refine List.mem_append_right _ ?_
          rw [hjEq]
          exact List.mem_singleton.mpr rfl
      }
  exact hmem w.length hj (Nat.le_refl _)

/-- Every energy-list entry is an absolute error at an earlier index. -/
theorem MemErrBelow (q c : ℕ) (w : List Bool) (i : ℕ)
    (hi : i ≤ w.length) (a : ℚ) (ha : a ∈ ErrBelow q c w i) :
    ∃ j, j < i ∧ a = AbsErr q c w j := by
  induction i with
  | zero => {
      unfold ErrBelow at ha
      cases ha
    }
  | succ i ih => {
      have hi' : i < w.length := by omega
      rw [ErrBelowSucc q c w i hi'] at ha
      rcases List.mem_append.mp ha with hleft | hright
      · rcases ih (Nat.le_of_lt hi') hleft with ⟨j, hj, rfl⟩
        exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
      · have haEq : a = AbsErr q c w i :=
          (List.mem_singleton).mp hright
        exact ⟨i, Nat.lt_succ_self i, haEq⟩
    }

/-- Each absolute error is at most the carry energy. -/
theorem AbsErrLeEnergy (q c : ℕ) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    AbsErr q c w i ≤ CarryEnergy q c w := by
  unfold CarryEnergy
  exact MaxListMemLe _ _ (AbsErrMem q c w i hi)

/-- The energy vanishes exactly when every absolute error vanishes. -/
theorem CarryEnergyZeroIffAbs (q c : ℕ) (w : List Bool) :
    CarryEnergy q c w = 0 ↔
      ∀ i, i < w.length → AbsErr q c w i = 0 := by
  constructor
  · intro h i hi
    have hle : AbsErr q c w i ≤ 0 := by
      rw [← h]
      exact AbsErrLeEnergy q c w i hi
    exact le_antisymm hle (abs_nonneg _)
  · intro h
    unfold CarryEnergy
    apply MaxListZero
    intro a ha
    rcases MemErrBelow q c w w.length (Nat.le_refl _) a ha with
      ⟨j, hj, rfl⟩
    exact h j hj

/-- Under an error of at most one half, the next error is at most the scaled error. -/
theorem EdgeBound (scale eta nxt : ℚ) (k : ℤ)
    (hrec : nxt = scale * eta + (k : ℚ))
    (habs : |nxt| ≤ (1 : ℚ) / 2) :
    |nxt| ≤ |scale * eta| := by
  by_cases hk : k = 0
  · subst hk
    have hrec' : nxt = scale * eta := by
      rw [hrec]
      ring
    rw [hrec']
  · have habsk : (1 : ℚ) ≤ |(k : ℚ)| := by
      by_cases hkp : 0 ≤ k
      · have h1 : (1 : ℤ) ≤ k := by omega
        have h1q : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast h1
        have h0q : (0 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hkp
        rw [abs_of_nonneg h0q]
        exact h1q
      · have h1 : k ≤ -1 := by omega
        have hneg : k < 0 := by omega
        have h1q : (1 : ℚ) ≤ -(k : ℚ) := by
          have : (1 : ℤ) ≤ -k := by omega
          exact_mod_cast this
        have h0q : (k : ℚ) < 0 := by exact_mod_cast hneg
        rw [abs_of_neg h0q]
        exact h1q
    have hkq : (k : ℚ) = nxt - scale * eta := by
      rw [hrec]
      ring
    have htri : |(k : ℚ)| ≤ |nxt| + |scale * eta| := by
      calc
        |(k : ℚ)| = |nxt + -(scale * eta)| := by
          rw [hkq, sub_eq_add_neg]
        _ ≤ |nxt| + |-(scale * eta)| := abs_add_le _ _
        _ = |nxt| + |scale * eta| := by rw [abs_neg]
    have hhalf : |nxt| ≤ (1 : ℚ) - |nxt| := by linarith
    have hgap : (1 : ℚ) - |nxt| ≤ |scale * eta| := by linarith
    exact le_trans hhalf hgap

/-- A strict contraction of an absolute value forces that value to vanish. -/
theorem AbsLeMul (e lam : ℚ) (hlt : lam < 1)
    (hle : |e| ≤ lam * |e|) : e = 0 := by
  have hdiff : (1 - lam) * |e| ≤ 0 := by
    have hsub : |e| - lam * |e| ≤ 0 := by linarith
    have hfac : |e| - lam * |e| = (1 - lam) * |e| := by ring
    linarith
  have hpos : 0 < 1 - lam := by linarith
  have hcmp : (1 - lam) * |e| ≤ (1 - lam) * 0 := by
    simpa using hdiff
  have hle0 : |e| ≤ 0 :=
    le_of_mul_le_mul_of_pos_left hcmp hpos
  have hz : |e| = 0 := le_antisymm hle0 (abs_nonneg _)
  exact (AbsEqZero e).mp hz

/-- An error bound of one half propagates by the scale product. -/
theorem ErrLeScale (q c : ℕ) (w : List Bool) (t : ℕ)
    (hq : Odd q) (hc : Odd c) (ht : t ≤ w.length)
    (hcon : q ^ OddCount w < 2 ^ w.length)
    (hbound : CarryEnergy q c w ≤ (1 : ℚ) / 2) :
    |SignedErr q c w t| ≤
      ScaleTo q w t * |SignedErr q c w 0| := by
  induction t with
  | zero => {
      simp [ScaleTo]
    }
  | succ t ih => {
      have ht' : t < w.length := by omega
      have ih' := ih (Nat.le_of_lt ht')
      have hrec := SignedErrSucc q c w t hq hc ht'
      have hmul : (WordAffine q w).mult < 2 ^ w.length := by
        rw [WordAffineMultEq]
        exact hcon
      have hnext : |SignedErr q c w (t + 1)| ≤ (1 : ℚ) / 2 := by
        by_cases hlast : t + 1 = w.length
        · have habs0 : |SignedErr q c w 0| = AbsErr q c w 0 := by
            symm
            exact AbsErrEq q c w 0 (LengthPos q w hcon)
          rw [hlast, SignedErrLength q c w hmul, habs0]
          exact le_trans
            (AbsErrLeEnergy q c w 0 (LengthPos q w hcon)) hbound
        · have hlt : t + 1 < w.length := by omega
          rw [← AbsErrEq q c w (t + 1) hlt]
          exact le_trans (AbsErrLeEnergy q c w (t + 1) hlt) hbound
      have hedge := EdgeBound
        (BranchScale q (BitAt w t))
        (SignedErr q c w t)
        (SignedErr q c w (t + 1))
        (Carry q c (BitAt w t)
          (NearestPositive (BitAt w t) (Phase q c w t))
          (NearestPositive (WrappedBit w (t + 1))
            (Phase q c w (t + 1))))
        hrec hnext
      have hsc : 0 ≤ BranchScale q (BitAt w t) :=
        BranchScaleNonneg q (BitAt w t)
      have habs :
          |BranchScale q (BitAt w t) * SignedErr q c w t| =
            BranchScale q (BitAt w t) * |SignedErr q c w t| := by
        rw [abs_mul, abs_of_nonneg hsc]
      calc
        |SignedErr q c w (t + 1)|
            ≤ |BranchScale q (BitAt w t) * SignedErr q c w t| :=
              hedge
        _ = BranchScale q (BitAt w t) * |SignedErr q c w t| := habs
        _ ≤ BranchScale q (BitAt w t) *
              (ScaleTo q w t * |SignedErr q c w 0|) := by
            exact mul_le_mul_of_nonneg_left ih' hsc
        _ = ScaleTo q w (t + 1) * |SignedErr q c w 0| := by
            rw [ScaleTo]
            ring
    }

/-- An energy of at most one half is exactly zero. -/
theorem EnergyZeroOfBound (q c : ℕ) (w : List Bool)
    (hq : Odd q) (hc : Odd c)
    (hcon : q ^ OddCount w < 2 ^ w.length)
    (hbound : CarryEnergy q c w ≤ (1 : ℚ) / 2) :
    CarryEnergy q c w = 0 := by
  have hmul : (WordAffine q w).mult < 2 ^ w.length := by
    rw [WordAffineMultEq]
    exact hcon
  have hscale := ErrLeScale q c w w.length hq hc (Nat.le_refl _)
    hcon hbound
  rw [SignedErrLength q c w hmul, ScaleToLength] at hscale
  have hfrac : ((WordAffine q w).mult : ℚ) / (2 : ℚ) ^ w.length < 1 := by
    have hpos : (0 : ℚ) < (2 : ℚ) ^ w.length :=
      pow_pos (by norm_num) _
    rw [div_lt_one hpos]
    exact_mod_cast hmul
  have hzero : SignedErr q c w 0 = 0 :=
    AbsLeMul _ _ hfrac hscale
  have hall : ∀ i, i < w.length → AbsErr q c w i = 0 := by
    intro i hi
    have hle := ErrLeScale q c w i hq hc (Nat.le_of_lt hi) hcon hbound
    have h0 : |SignedErr q c w 0| = 0 := by
      rw [hzero]
      simp
    rw [h0] at hle
    have hle0 : |SignedErr q c w i| ≤ 0 := by
      simpa using hle
    have hz : |SignedErr q c w i| = 0 :=
      le_antisymm hle0 (abs_nonneg _)
    have hsign : SignedErr q c w i = 0 := (AbsEqZero _).mp hz
    rw [AbsErrEq q c w i hi, hsign]
    simp
  exact (CarryEnergyZeroIffAbs q c w).mpr hall

/-- Carry energy is either zero or strictly larger than one half. -/
theorem CarryEnergyDichotomy (q c : ℕ) (w : List Bool)
    (hq : Odd q) (hc : Odd c)
    (hcon : q ^ OddCount w < 2 ^ w.length) :
    CarryEnergy q c w = 0 ∨ (1 : ℚ) / 2 < CarryEnergy q c w := by
  by_cases hbound : CarryEnergy q c w ≤ (1 : ℚ) / 2
  · exact Or.inl (EnergyZeroOfBound q c w hq hc hcon hbound)
  · exact Or.inr ((not_le).mp hbound)

/-- Zero energy means every phase is a positive integer of its letter's parity. -/
theorem CarryEnergyZeroIff (q c : ℕ) (w : List Bool) :
    CarryEnergy q c w = 0 ↔
      ∀ i, i < w.length →
        ∃ n : ℤ, PositiveParity (BitAt w i) n ∧
          Phase q c w i = (n : ℚ) := by
  constructor
  · intro h i hi
    have hzero := (CarryEnergyZeroIffAbs q c w).mp h i hi
    refine ⟨NearestPositive (BitAt w i) (Phase q c w i),
      NearestPositiveParity (BitAt w i) (Phase q c w i), ?_⟩
    unfold AbsErr at hzero
    have hsub : Phase q c w i -
        (NearestPositive (BitAt w i) (Phase q c w i) : ℚ) = 0 :=
      (AbsEqZero _).mp hzero
    linarith
  · intro h
    apply (CarryEnergyZeroIffAbs q c w).mpr
    intro i hi
    rcases h i hi with ⟨n, hn, hph⟩
    have hself : NearestPositive (BitAt w i) (n : ℚ) = n :=
      NearestPositiveSelf (BitAt w i) n hn
    unfold AbsErr
    rw [hph, hself]
    simp

/-- The word odd-even has carry energy zero for `q = 3` and `c = 1`. -/
theorem CarryEnergyWord10 :
    CarryEnergy 3 1 [true, false] = 0 := by
  set w : List Bool := [true, false]
  have hfix : Fixed 3 1 w = 1 := by
    unfold Fixed
    have hA : WordAffine 3 w = ⟨3, 1⟩ := by
      unfold w
      rfl
    have hlen : w.length = 2 := by
      unfold w
      rfl
    rw [hA, hlen]
    norm_num
  have h0 : Phase 3 1 w 0 = 1 := by
    rw [PhaseZero, hfix]
  have h1 : Phase 3 1 w 1 = 2 := by
    have hstep := DropSucc 3 1 w (Fixed 3 1 w) 0 (by decide)
    unfold Phase
    rw [hstep]
    have hprev : DropShortcut 3 1 w (Fixed 3 1 w) 0 = 1 := by
      unfold Phase at h0
      exact h0
    rw [hprev]
    have hbit : BitAt w 0 = true := by
      unfold w
      simp [BitAt]
    rw [hbit]
    simp [Shortcut]
    norm_num
  have hp0 : PositiveParity true 1 := by
    refine ⟨by decide, ?_⟩
    unfold HasParity
    exact odd_one
  have hp1 : PositiveParity false 2 := by
    refine ⟨by decide, ?_⟩
    unfold HasParity
    exact ⟨1, rfl⟩
  have hn0 : NearestPositive true (1 : ℚ) = 1 :=
    NearestPositiveSelf true 1 hp0
  have hn1 : NearestPositive false (2 : ℚ) = 2 :=
    NearestPositiveSelf false 2 hp1
  have ha0 : AbsErr 3 1 w 0 = 0 := by
    unfold AbsErr
    have hbit : BitAt w 0 = true := by
      unfold w
      simp [BitAt]
    rw [h0, hbit, hn0]
    simp
  have ha1 : AbsErr 3 1 w 1 = 0 := by
    unfold AbsErr
    have hbit : BitAt w 1 = false := by
      unfold w
      simp [BitAt]
    rw [h1, hbit, hn1]
    simp
  have hlen : w.length = 2 := by
    unfold w
    rfl
  have hlist : ErrBelow 3 1 w 2 =
      [AbsErr 3 1 w 0, AbsErr 3 1 w 1] := by
    have hs1 := ErrBelowSucc 3 1 w 1 (by decide)
    have hs0 := ErrBelowSucc 3 1 w 0 (by decide)
    rw [hs1, hs0]
    simp [ErrBelow]
  unfold CarryEnergy
  rw [hlen, hlist, ha0, ha1]
  simp [MaxList]

/-- The word odd-even-even has carry energy `8 / 5` for `q = 3` and `c = 1`. -/
theorem CarryEnergyWord100 :
    CarryEnergy 3 1 [true, false, false] = (8 : ℚ) / 5 := by
  set w : List Bool := [true, false, false]
  have hfix : Fixed 3 1 w = (1 : ℚ) / 5 := by
    unfold Fixed
    have hA : WordAffine 3 w = ⟨3, 1⟩ := by
      unfold w
      rfl
    have hlen : w.length = 3 := by
      unfold w
      rfl
    rw [hA, hlen]
    norm_num
  have h0 : Phase 3 1 w 0 = (1 : ℚ) / 5 := by
    rw [PhaseZero, hfix]
  have h1 : Phase 3 1 w 1 = (4 : ℚ) / 5 := by
    have hstep := DropSucc 3 1 w (Fixed 3 1 w) 0 (by decide)
    unfold Phase
    rw [hstep]
    have hprev : DropShortcut 3 1 w (Fixed 3 1 w) 0 =
        (1 : ℚ) / 5 := by
      unfold Phase at h0
      exact h0
    rw [hprev]
    have hbit : BitAt w 0 = true := by
      unfold w
      simp [BitAt]
    rw [hbit]
    simp [Shortcut]
    norm_num
  have h2 : Phase 3 1 w 2 = (2 : ℚ) / 5 := by
    have hstep := DropSucc 3 1 w (Fixed 3 1 w) 1 (by decide)
    unfold Phase
    rw [hstep]
    have hprev : DropShortcut 3 1 w (Fixed 3 1 w) 1 =
        (4 : ℚ) / 5 := by
      unfold Phase at h1
      exact h1
    rw [hprev]
    have hbit : BitAt w 1 = false := by
      unfold w
      simp [BitAt]
    rw [hbit]
    simp [Shortcut]
    norm_num
  have hnear0 : NearestPositive true ((1 : ℚ) / 5) = 1 := by
    have hlo : LowerPoint true ((1 : ℚ) / 5) = -1 := by
      unfold LowerPoint LowerIndex ParityBit
      norm_num
    have hraw : RawNearest true ((1 : ℚ) / 5) = 1 := by
      unfold RawNearest
      rw [hlo]
      have hcmp : ¬ ((1 : ℚ) / 5 ≤ ((-1 : ℤ) : ℚ) + 1) := by
        norm_num
      rw [if_neg hcmp]
      norm_num
    unfold NearestPositive
    rw [hraw]
    have hpos : ¬ ((1 : ℤ) ≤ 0) := by decide
    rw [if_neg hpos]
  have hnear1 : NearestPositive false ((4 : ℚ) / 5) = 2 := by
    have hlo : LowerPoint false ((4 : ℚ) / 5) = 0 := by
      unfold LowerPoint LowerIndex ParityBit
      norm_num
    have hraw : RawNearest false ((4 : ℚ) / 5) = 0 := by
      unfold RawNearest
      rw [hlo]
      have hcmp : (4 : ℚ) / 5 ≤ ((0 : ℤ) : ℚ) + 1 := by
        norm_num
      rw [if_pos hcmp]
    unfold NearestPositive LeastPositive
    rw [hraw]
    rw [if_pos (le_rfl : (0 : ℤ) ≤ 0)]
    rfl
  have hnear2 : NearestPositive false ((2 : ℚ) / 5) = 2 := by
    have hlo : LowerPoint false ((2 : ℚ) / 5) = 0 := by
      unfold LowerPoint LowerIndex ParityBit
      norm_num
    have hraw : RawNearest false ((2 : ℚ) / 5) = 0 := by
      unfold RawNearest
      rw [hlo]
      have hcmp : (2 : ℚ) / 5 ≤ ((0 : ℤ) : ℚ) + 1 := by
        norm_num
      rw [if_pos hcmp]
    unfold NearestPositive LeastPositive
    rw [hraw]
    rw [if_pos (le_rfl : (0 : ℤ) ≤ 0)]
    rfl
  have ha0 : AbsErr 3 1 w 0 = (4 : ℚ) / 5 := by
    unfold AbsErr
    have hbit : BitAt w 0 = true := by
      unfold w
      simp [BitAt]
    rw [h0, hbit, hnear0]
    norm_num
  have ha1 : AbsErr 3 1 w 1 = (6 : ℚ) / 5 := by
    unfold AbsErr
    have hbit : BitAt w 1 = false := by
      unfold w
      simp [BitAt]
    rw [h1, hbit, hnear1]
    norm_num
  have ha2 : AbsErr 3 1 w 2 = (8 : ℚ) / 5 := by
    unfold AbsErr
    have hbit : BitAt w 2 = false := by
      unfold w
      simp [BitAt]
    rw [h2, hbit, hnear2]
    norm_num
  have hlen : w.length = 3 := by
    unfold w
    rfl
  have hlist : ErrBelow 3 1 w 3 =
      [AbsErr 3 1 w 0, AbsErr 3 1 w 1, AbsErr 3 1 w 2] := by
    have hs2 := ErrBelowSucc 3 1 w 2 (by decide)
    have hs1 := ErrBelowSucc 3 1 w 1 (by decide)
    have hs0 := ErrBelowSucc 3 1 w 0 (by decide)
    rw [hs2, hs1, hs0]
    simp [ErrBelow]
  unfold CarryEnergy
  rw [hlen, hlist, ha0, ha1, ha2]
  have hmax0 : max ((8 : ℚ) / 5) 0 = (8 : ℚ) / 5 := by
    apply max_eq_left
    norm_num
  have hmax1 : max ((6 : ℚ) / 5) ((8 : ℚ) / 5) = (8 : ℚ) / 5 := by
    apply max_eq_right
    norm_num
  have hmax2 : max ((4 : ℚ) / 5) ((8 : ℚ) / 5) = (8 : ℚ) / 5 := by
    apply max_eq_right
    norm_num
  calc
    MaxList [(4 : ℚ) / 5, (6 : ℚ) / 5, (8 : ℚ) / 5]
        = max ((4 : ℚ) / 5)
            (max ((6 : ℚ) / 5) (max ((8 : ℚ) / 5) 0)) := by
          simp [MaxList]
    _ = max ((4 : ℚ) / 5) (max ((6 : ℚ) / 5) ((8 : ℚ) / 5)) := by
          rw [hmax0]
    _ = max ((4 : ℚ) / 5) ((8 : ℚ) / 5) := by
          rw [hmax1]
    _ = (8 : ℚ) / 5 := hmax2

/-- For odd positive `q` and `c`, carry energy on a contracting base-two word
    is zero or greater than one half. -/
theorem CarryGap :
    (∀ (q c : ℕ) (w : List Bool),
      Odd q → Odd c → q ^ OddCount w < 2 ^ w.length →
        (CarryEnergy q c w = 0 ∨
          (1 : ℚ) / 2 < CarryEnergy q c w) ∧
        (CarryEnergy q c w = 0 ↔
          ∀ i, i < w.length →
            ∃ n : ℤ, PositiveParity (BitAt w i) n ∧
              Phase q c w i = (n : ℚ))) ∧
    CarryEnergy 3 1 [true, false] = 0 ∧
    CarryEnergy 3 1 [true, false, false] = (8 : ℚ) / 5 := by
  constructor
  · intro q c w hq hc hcon
    constructor
    · exact CarryEnergyDichotomy q c w hq hc hcon
    · exact CarryEnergyZeroIff q c w
  · constructor
    · exact CarryEnergyWord10
    · exact CarryEnergyWord100
