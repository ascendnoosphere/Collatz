-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.TakeDrop
import Lean.Elab.Tactic.Omega

/-!
Antipodal Hamming gap for a parity word of even length.

The antipodal distance of a word of length `2 * h` counts indices `i < h` whose
letter differs from the letter `h` places later. An even number of odd letters
makes that distance even. The distance is invariant under cyclic shift. While
the first half turns into its complement, its odd-letter count changes by at
most one at each step, so some shift gives the two halves the same odd-letter
count. If the distance is `2`, that shift is a one-bit transport. Excluding
every one-bit transport, and excluding a repeated block, leaves distance at
least `4`.

The exclusion is a hypothesis. The word `10` has distance `1`, and `0101` has
distance `0`. The word `000011101000` has distance `4`. None of these
statements says that the classical shortcut reaches `1`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.HammingGap

/-- Contribution of one odd letter. -/
def GapBit : Bool → ℕ
  | false => 0
  | true => 1

/-- An odd letter contributes one, and an even letter contributes nothing. -/
theorem GapBitLeOne (b : Bool) : GapBit b ≤ 1 := by
  cases b with
  | false => {
      exact Nat.zero_le 1
    }
  | true => {
      exact Nat.le_refl 1
    }

/-- Number of odd letters in a parity word. -/
def GapOddCount : List Bool → ℕ
  | [] => 0
  | false :: bs => GapOddCount bs
  | true :: bs => GapOddCount bs + 1

/-- The empty word has no odd letters. -/
theorem GapOddCountNil : GapOddCount ([] : List Bool) = 0 := rfl

/-- An even head does not increase the odd-letter count. -/
theorem GapOddCountFalse (bs : List Bool) :
    GapOddCount (false :: bs) = GapOddCount bs := rfl

/-- An odd head increases the odd-letter count by one. -/
theorem GapOddCountTrue (bs : List Bool) :
    GapOddCount (true :: bs) = GapOddCount bs + 1 := rfl

/-- The head contribution is `GapBit`. -/
theorem GapOddCountCons (b : Bool) (bs : List Bool) :
    GapOddCount (b :: bs) = GapBit b + GapOddCount bs := by
  cases b with
  | false => {
      rw [GapOddCountFalse, GapBit, Nat.zero_add]
    }
  | true => {
      rw [GapOddCountTrue, GapBit, Nat.add_comm]
    }

/-- Odd-letter counts add under concatenation. -/
theorem GapOddCountAppend (u v : List Bool) :
    GapOddCount (u ++ v) = GapOddCount u + GapOddCount v := by
  induction u with
  | nil => {
      rw [List.nil_append, GapOddCountNil, Nat.zero_add]
    }
  | cons b bs ih => {
      rw [List.cons_append, GapOddCountCons, GapOddCountCons, ih,
        ← Nat.add_assoc]
    }

/-- Prefix and suffix counts recover the full count at any cut. -/
theorem GapOddCountTakeDrop (w : List Bool) (h : ℕ) :
    GapOddCount w = GapOddCount (w.take h) + GapOddCount (w.drop h) := by
  have hsplit := GapOddCountAppend (w.take h) (w.drop h)
  rw [List.take_append_drop] at hsplit
  exact hsplit

/-- One cyclic shift, moving the head letter to the end. -/
def GapShift : List Bool → List Bool
  | [] => []
  | b :: bs => bs ++ [b]

/-- The shift of a nonempty word is the tail followed by the head. -/
theorem GapShiftCons (b : Bool) (bs : List Bool) :
    GapShift (b :: bs) = bs ++ [b] := rfl

/-- A cyclic shift preserves length. -/
theorem GapShiftLength (w : List Bool) :
    (GapShift w).length = w.length := by
  cases w with
  | nil => {
      rfl
    }
  | cons b bs => {
      rw [GapShiftCons, List.length_append, List.length_singleton,
        List.length_cons]
    }

/-- A cyclic shift preserves the odd-letter count. -/
theorem GapShiftOddCount (w : List Bool) :
    GapOddCount (GapShift w) = GapOddCount w := by
  cases w with
  | nil => {
      rfl
    }
  | cons b bs => {
      rw [GapShiftCons, GapOddCountAppend, GapOddCountCons b [],
        GapOddCountNil, Nat.add_zero, GapOddCountCons, Nat.add_comm]
    }

/-- The shift by `k` places. Each step moves the current head to the end. -/
def GapShiftN : ℕ → List Bool → List Bool
  | 0, w => w
  | k + 1, w => GapShift (GapShiftN k w)

/-- Zero shifts leave the word fixed. -/
theorem GapShiftNZero (w : List Bool) : GapShiftN 0 w = w := rfl

/-- One more shift is a shift of the already shifted word. -/
theorem GapShiftNSucc (k : ℕ) (w : List Bool) :
    GapShiftN (k + 1) w = GapShift (GapShiftN k w) := rfl

/-- Shifting `k` times preserves length. -/
theorem GapShiftNLength (k : ℕ) (w : List Bool) :
    (GapShiftN k w).length = w.length := by
  induction k with
  | zero => {
      rw [GapShiftNZero]
    }
  | succ k ih => {
      rw [GapShiftNSucc, GapShiftLength, ih]
    }

/-- Shifting `k` times preserves the odd-letter count. -/
theorem GapShiftNOddCount (k : ℕ) (w : List Bool) :
    GapOddCount (GapShiftN k w) = GapOddCount w := by
  induction k with
  | zero => {
      rw [GapShiftNZero]
    }
  | succ k ih => {
      rw [GapShiftNSucc, GapShiftOddCount, ih]
    }

/-- Shifting once before the remaining shifts agrees with the other order. -/
theorem GapShiftNFront (k : ℕ) (w : List Bool) :
    GapShiftN (k + 1) w = GapShiftN k (GapShift w) := by
  induction k generalizing w with
  | zero => {
      rw [GapShiftNZero, GapShiftNSucc, GapShiftNZero]
    }
  | succ k ih => {
      rw [GapShiftNSucc (k + 1), ih, GapShiftNSucc]
    }

/-- Shifting by the length of the first block exchanges the two blocks. -/
theorem GapShiftNHalves (u v : List Bool) :
    GapShiftN u.length (u ++ v) = v ++ u := by
  induction u generalizing v with
  | nil => {
      rw [List.length_nil, GapShiftNZero, List.nil_append, List.append_nil]
    }
  | cons a us ih => {
      rw [List.length_cons, GapShiftNFront]
      have hshift : GapShift ((a :: us) ++ v) = us ++ (v ++ [a]) := by
        rw [List.cons_append, GapShiftCons, List.append_assoc]
      rw [hshift, ih (v ++ [a]), List.append_assoc, List.singleton_append]
    }

/-- A full turn fixes the word, including the empty word. -/
theorem GapShiftFull (w : List Bool) : GapShiftN w.length w = w := by
  simpa only [List.append_nil, List.nil_append] using GapShiftNHalves w []

/-- One full turn can be removed before any subsequent number of shifts. -/
theorem GapShiftNPeriod (k : ℕ) (w : List Bool) :
    GapShiftN (k + w.length) w = GapShiftN k w := by
  induction k with
  | zero => {
      simpa only [Nat.zero_add, GapShiftNZero] using GapShiftFull w
    }
  | succ k ih => {
      have hindex : k + 1 + w.length = (k + w.length) + 1 := by omega
      rw [hindex, GapShiftNSucc (k + w.length), ih, GapShiftNSucc]
    }

/-- Number of positions at which two words differ. -/
def GapHamming : List Bool → List Bool → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, b :: bs =>
      (if a = b then 0 else 1) + GapHamming as bs

/-- The empty left word differs in no position. -/
theorem GapHammingNilLeft (v : List Bool) : GapHamming [] v = 0 := rfl

/-- The head comparison is added to the distance of the tails. -/
theorem GapHammingHead (a b : Bool) (as bs : List Bool) :
    GapHamming (a :: as) (b :: bs) =
      (if a = b then 0 else 1) + GapHamming as bs := rfl

/-- A word does not differ from itself. -/
theorem GapHammingSelf (u : List Bool) : GapHamming u u = 0 := by
  induction u with
  | nil => {
      rfl
    }
  | cons a as ih => {
      rw [GapHammingHead, if_pos rfl, Nat.zero_add, ih]
    }

/-- Equal length and distance zero force the two words to agree. -/
theorem GapHammingZero (u v : List Bool) (hlen : u.length = v.length)
    (h0 : GapHamming u v = 0) : u = v := by
  induction u generalizing v with
  | nil => {
      cases v with
      | nil => {
          rfl
        }
      | cons _ _ => {
          rw [List.length_nil, List.length_cons] at hlen
          cases hlen
        }
    }
  | cons a as ih => {
      cases v with
      | nil => {
          rw [List.length_nil, List.length_cons] at hlen
          cases hlen
        }
      | cons b bs => {
          have hlen' : as.length = bs.length := by
            rw [List.length_cons, List.length_cons] at hlen
            exact Nat.succ_inj.mp hlen
          by_cases hab : a = b
          · subst hab
            have htail : GapHamming as bs = 0 := by
              rw [GapHammingHead, if_pos rfl, Nat.zero_add] at h0
              exact h0
            exact congrArg (fun t => a :: t) (ih bs hlen' htail)
          · rw [GapHammingHead, if_neg hab] at h0
            have hpos : 1 + GapHamming as bs = 0 := h0
            omega
        }
    }

/-- Marker of an odd letter standing opposite an even letter. -/
def GapMoved : Bool → Bool → ℕ
  | true, false => 1
  | _, _ => 0

/-- The four head pairs have the expected move markers. -/
theorem GapMovedFalseFalse : GapMoved false false = 0 := rfl

/-- An even letter opposite an odd letter is not a left-only move. -/
theorem GapMovedFalseTrue : GapMoved false true = 0 := rfl

/-- Two odd letters are not a move. -/
theorem GapMovedTrueTrue : GapMoved true true = 0 := rfl

/-- An odd letter opposite an even letter is one left-only move. -/
theorem GapMovedTrueFalse : GapMoved true false = 1 := rfl

/-- A mismatch is one left-only move or one right-only move. -/
theorem GapMovedSym (a b : Bool) :
    (if a = b then 0 else 1) = GapMoved a b + GapMoved b a := by
  cases a with
  | false => {
      cases b with
      | false => {
          rfl
        }
      | true => {
          rfl
        }
    }
  | true => {
      cases b with
      | false => {
          rfl
        }
      | true => {
          rfl
        }
    }

/-- The odd-letter change across one column has the same two readings. -/
theorem GapBitMoved (a b : Bool) :
    GapBit a + GapMoved b a = GapBit b + GapMoved a b := by
  cases a with
  | false => {
      cases b with
      | false => {
          rfl
        }
      | true => {
          rfl
        }
    }
  | true => {
      cases b with
      | false => {
          rfl
        }
      | true => {
          rfl
        }
    }

/-- Number of odd letters in the left word opposite an even letter. -/
def GapLeftOnly : List Bool → List Bool → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, b :: bs => GapMoved a b + GapLeftOnly as bs

/-- The empty left word contributes no left-only moves. -/
theorem GapLeftOnlyNilLeft (v : List Bool) : GapLeftOnly [] v = 0 := rfl

/-- A left-only move is the head marker plus the tail count. -/
theorem GapLeftOnlyHead (a b : Bool) (as bs : List Bool) :
    GapLeftOnly (a :: as) (b :: bs) =
      GapMoved a b + GapLeftOnly as bs := rfl

/-- The two ways of grouping four summands agree. -/
theorem GapAddCross (a b p q : ℕ) :
    (a + b) + (p + q) = (a + p) + (b + q) := by
  calc
    (a + b) + (p + q) = ((a + b) + p) + q :=
      (Nat.add_assoc (a + b) p q).symm
    _ = (a + (b + p)) + q := by
      rw [← Nat.add_assoc a b p]
    _ = (a + (p + b)) + q := by
      rw [Nat.add_comm b p]
    _ = ((a + p) + b) + q := by
      rw [← Nat.add_assoc a p b]
    _ = (a + p) + (b + q) := Nat.add_assoc (a + p) b q

/-- Distance is the sum of the two opposite move counts. -/
theorem GapHammingSplit (u v : List Bool) (hlen : u.length = v.length) :
    GapHamming u v = GapLeftOnly u v + GapLeftOnly v u := by
  induction u generalizing v with
  | nil => {
      cases v with
      | nil => {
          rfl
        }
      | cons _ _ => {
          rw [List.length_nil, List.length_cons] at hlen
          cases hlen
        }
    }
  | cons a as ih => {
      cases v with
      | nil => {
          rw [List.length_nil, List.length_cons] at hlen
          cases hlen
        }
      | cons b bs => {
          have hlen' : as.length = bs.length := by
            rw [List.length_cons, List.length_cons] at hlen
            exact Nat.succ_inj.mp hlen
          rw [GapHammingHead, GapLeftOnlyHead, GapLeftOnlyHead, ih bs hlen',
            GapMovedSym]
          exact GapAddCross (GapMoved a b) (GapMoved b a)
            (GapLeftOnly as bs) (GapLeftOnly bs as)
        }
    }

/-- Moving the opposite counts does not change the two odd-letter totals. -/
theorem GapOddMove (u v : List Bool) (hlen : u.length = v.length) :
    GapOddCount u + GapLeftOnly v u =
      GapOddCount v + GapLeftOnly u v := by
  induction u generalizing v with
  | nil => {
      cases v with
      | nil => {
          rfl
        }
      | cons _ _ => {
          rw [List.length_nil, List.length_cons] at hlen
          cases hlen
        }
    }
  | cons a as ih => {
      cases v with
      | nil => {
          rw [List.length_nil, List.length_cons] at hlen
          cases hlen
        }
      | cons b bs => {
          have hlen' : as.length = bs.length := by
            rw [List.length_cons, List.length_cons] at hlen
            exact Nat.succ_inj.mp hlen
          rw [GapOddCountCons, GapOddCountCons, GapLeftOnlyHead,
            GapLeftOnlyHead]
          rw [(GapAddCross (GapBit a) (GapMoved b a) (GapOddCount as)
            (GapLeftOnly bs as)).symm]
          rw [GapBitMoved, ih bs hlen']
          exact GapAddCross (GapBit b) (GapMoved a b) (GapOddCount bs)
            (GapLeftOnly as bs)
        }
    }

/-- Equal odd counts and distance `2` are one move in each direction. -/
theorem GapTransportShape (u v : List Bool) (hlen : u.length = v.length)
    (hham : GapHamming u v = 2) (hodd : GapOddCount u = GapOddCount v) :
    GapLeftOnly u v = 1 ∧ GapLeftOnly v u = 1 := by
  have hsplit := GapHammingSplit u v hlen
  have hmove := GapOddMove u v hlen
  have hsame : GapLeftOnly v u = GapLeftOnly u v := by
    rw [hodd] at hmove
    exact Nat.add_left_cancel hmove
  have hsum : GapLeftOnly u v + GapLeftOnly u v = 2 := by
    have hjoin : GapLeftOnly u v + GapLeftOnly v u = 2 := by
      rw [← hsplit]
      exact hham
    rw [hsame] at hjoin
    exact hjoin
  have hone : GapLeftOnly u v = 1 := by omega
  exact ⟨hone, hsame.trans hone⟩

/-- Odd-letter count and Hamming distance have the same parity. -/
theorem GapHammingModTwo (u v : List Bool) (hlen : u.length = v.length) :
    GapOddCount (u ++ v) % 2 = GapHamming u v % 2 := by
  induction u generalizing v with
  | nil => {
      cases v with
      | nil => {
          rw [List.nil_append, GapOddCountNil, GapHammingNilLeft]
        }
      | cons _ _ => {
          rw [List.length_nil, List.length_cons] at hlen
          cases hlen
        }
    }
  | cons a as ih => {
      cases v with
      | nil => {
          rw [List.length_nil, List.length_cons] at hlen
          cases hlen
        }
      | cons b bs => {
          have hlen' : as.length = bs.length := by
            rw [List.length_cons, List.length_cons] at hlen
            exact Nat.succ_inj.mp hlen
          have hleft : GapOddCount ((a :: as) ++ (b :: bs)) =
              GapBit a + GapBit b + GapOddCount (as ++ bs) := by
            rw [List.cons_append, GapOddCountCons, GapOddCountAppend,
              GapOddCountCons]
            calc
              GapBit a + (GapOddCount as + (GapBit b + GapOddCount bs))
                = GapBit a +
                    ((GapOddCount as + GapBit b) + GapOddCount bs) := by
                    rw [← Nat.add_assoc (GapOddCount as) (GapBit b)
                      (GapOddCount bs)]
              _ = GapBit a +
                    ((GapBit b + GapOddCount as) + GapOddCount bs) := by
                    rw [Nat.add_comm (GapOddCount as) (GapBit b)]
              _ = GapBit a +
                    (GapBit b + (GapOddCount as + GapOddCount bs)) := by
                    rw [Nat.add_assoc (GapBit b) (GapOddCount as)
                      (GapOddCount bs)]
              _ = GapBit a + GapBit b +
                    (GapOddCount as + GapOddCount bs) := by
                    rw [← Nat.add_assoc (GapBit a) (GapBit b)
                      (GapOddCount as + GapOddCount bs)]
              _ = GapBit a + GapBit b + GapOddCount (as ++ bs) := by
                    rw [← GapOddCountAppend]
          have hbits : (GapBit a + GapBit b) % 2 =
              (if a = b then 0 else 1) % 2 := by
            cases a with
            | false => {
                cases b with
                | false => {
                    rfl
                  }
                | true => {
                    rfl
                  }
              }
            | true => {
                cases b with
                | false => {
                    rfl
                  }
                | true => {
                    rfl
                  }
              }
          have hmodL :
              GapOddCount ((a :: as) ++ (b :: bs)) % 2 =
                ((GapBit a + GapBit b) % 2 +
                  GapOddCount (as ++ bs) % 2) % 2 := by
            rw [hleft]
            exact Nat.add_mod (GapBit a + GapBit b)
              (GapOddCount (as ++ bs)) 2
          have hmodR :
              ((if a = b then 0 else 1) + GapHamming as bs) % 2 =
                ((if a = b then 0 else 1) % 2 +
                  GapHamming as bs % 2) % 2 :=
            Nat.add_mod (if a = b then 0 else 1) (GapHamming as bs) 2
          rw [GapHammingHead, hmodL, hmodR, hbits, ih bs hlen']
        }
    }

/-- Both halves of a word of length `2 * h` have length `h`. -/
theorem GapTakeDropLengths (w : List Bool) (h : ℕ)
    (hlen : w.length = 2 * h) :
    (w.take h).length = h ∧ (w.drop h).length = h := by
  have hle : h ≤ w.length := by
    rw [hlen, Nat.two_mul]
    exact Nat.le_add_right h h
  refine ⟨List.length_take_of_le hle, ?_⟩
  rw [List.length_drop, hlen, Nat.two_mul, Nat.add_sub_cancel_left]

/-- Dividing `2 * h` by `2` returns `h`. -/
theorem GapHalfIndex (h : ℕ) : (2 * h) / 2 = h :=
  Nat.mul_div_cancel_left h Nat.zero_lt_two

/-- Mismatches between the two contiguous halves. -/
def GapAntipodal (w : List Bool) : ℕ :=
  GapHamming (w.take (w.length / 2)) (w.drop (w.length / 2))

/-- For length `2 * h`, the antipodal distance compares the two halves. -/
theorem GapAntipodalHalves (w : List Bool) (h : ℕ)
    (hlen : w.length = 2 * h) :
    GapAntipodal w = GapHamming (w.take h) (w.drop h) := by
  unfold GapAntipodal
  rw [hlen, GapHalfIndex]

/-- The antipodal distance has the parity of the odd-letter count. -/
theorem GapAntipodalModTwo (w : List Bool) (h : ℕ)
    (hlen : w.length = 2 * h) :
    GapAntipodal w % 2 = GapOddCount w % 2 := by
  have hlens := GapTakeDropLengths w h hlen
  have hlen' : (w.take h).length = (w.drop h).length := by
    rw [hlens.1, hlens.2]
  have hjoin : w.take h ++ w.drop h = w := List.take_append_drop h w
  have hmod := GapHammingModTwo (w.take h) (w.drop h) hlen'
  rw [hjoin] at hmod
  rw [GapAntipodalHalves w h hlen]
  exact hmod.symm

/-- One shift of a positive even length splits off both heads. -/
theorem GapShiftSplit (w : List Bool) (h : ℕ) (hlen : w.length = 2 * h)
    (hpos : 0 < h) :
    ∃ (a b : Bool) (us vs : List Bool),
      w.take h = a :: us ∧
        w.drop h = b :: vs ∧
          GapShift w = (us ++ [b]) ++ (vs ++ [a]) ∧
            (us ++ [b]).length = h ∧ (vs ++ [a]).length = h := by
  have hlens := GapTakeDropLengths w h hlen
  cases htake : w.take h with
  | nil => {
      have hzero : h = 0 := by
        have hlen0 : (w.take h).length = 0 := by
          simp only [htake, List.length_nil]
        rw [hlens.1] at hlen0
        exact hlen0
      exact absurd hzero (Nat.ne_of_gt hpos)
    }
  | cons a us => {
      cases hdrop : w.drop h with
      | nil => {
          have hzero : h = 0 := by
            have hlen0 : (w.drop h).length = 0 := by
              simp only [hdrop, List.length_nil]
            rw [hlens.2] at hlen0
            exact hlen0
          exact absurd hzero (Nat.ne_of_gt hpos)
        }
      | cons b vs => {
          have hcat : w = (a :: us) ++ (b :: vs) := by
            rw [← htake, ← hdrop]
            exact (List.take_append_drop h w).symm
          have hmid : us ++ (b :: vs) = (us ++ [b]) ++ vs := by
            have hb : b :: vs = [b] ++ vs := rfl
            rw [hb]
            exact (List.append_assoc us [b] vs).symm
          have hshift : GapShift w = (us ++ [b]) ++ (vs ++ [a]) := by
            rw [hcat, List.cons_append, GapShiftCons, hmid, List.append_assoc]
          have hlenL : (us ++ [b]).length = h := by
            have hcons : (a :: us).length = h := by
              rw [← htake]
              exact hlens.1
            have hus : us.length + 1 = h := by
              simpa [List.length_cons] using hcons
            rw [List.length_append, List.length_singleton, hus]
          have hlenR : (vs ++ [a]).length = h := by
            have hcons : (b :: vs).length = h := by
              rw [← hdrop]
              exact hlens.2
            have hvs : vs.length + 1 = h := by
              simpa [List.length_cons] using hcons
            rw [List.length_append, List.length_singleton, hvs]
          exact ⟨a, b, us, vs, rfl, rfl, hshift, hlenL, hlenR⟩
        }
    }

/-- Exchanging the two head letters does not change the distance. -/
theorem GapHammingRotateEnds (a b : Bool) (us vs : List Bool)
    (hlen : us.length = vs.length) :
    GapHamming (us ++ [b]) (vs ++ [a]) =
      GapHamming (a :: us) (b :: vs) := by
  induction us generalizing vs with
  | nil => {
      cases vs with
      | nil => {
          cases a with
          | false => {
              cases b with
              | false => {
                  rfl
                }
              | true => {
                  rfl
                }
            }
          | true => {
              cases b with
              | false => {
                  rfl
                }
              | true => {
                  rfl
                }
            }
        }
      | cons _ _ => {
          rw [List.length_nil, List.length_cons] at hlen
          cases hlen
        }
    }
  | cons c us ih => {
      cases vs with
      | nil => {
          rw [List.length_nil, List.length_cons] at hlen
          cases hlen
        }
      | cons d vs => {
          have hlen' : us.length = vs.length := by
            rw [List.length_cons, List.length_cons] at hlen
            exact Nat.succ_inj.mp hlen
          have hL : GapHamming ((c :: us) ++ [b]) ((d :: vs) ++ [a]) =
              (if c = d then 0 else 1) +
                GapHamming (us ++ [b]) (vs ++ [a]) := by
            rw [List.cons_append, List.cons_append, GapHammingHead]
          rw [hL, ih vs hlen', GapHammingHead, GapHammingHead]
          exact Nat.add_left_comm
            (if c = d then 0 else 1)
            (if a = b then 0 else 1)
            (GapHamming us vs)
        }
    }

/-- One cyclic shift preserves the antipodal distance. -/
theorem GapAntipodalShift (w : List Bool) (h : ℕ)
    (hlen : w.length = 2 * h) :
    GapAntipodal (GapShift w) = GapAntipodal w := by
  cases h with
  | zero => {
      have hw : w = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [hlen]
      subst hw
      rfl
    }
  | succ h' => {
      have hpos : 0 < (h' + 1) := Nat.succ_pos h'
      obtain ⟨a, b, us, vs, htake, hdrop, hshift, hlenL, _hlenR⟩ :=
        GapShiftSplit w (h' + 1) hlen hpos
      have hlenTail : us.length = vs.length := by
        have hlu : (a :: us).length = (h' + 1) := by
          rw [← htake]
          exact (GapTakeDropLengths w (h' + 1) hlen).1
        have hlv : (b :: vs).length = (h' + 1) := by
          rw [← hdrop]
          exact (GapTakeDropLengths w (h' + 1) hlen).2
        have hlu' : us.length + 1 = (h' + 1) := by
          simpa [List.length_cons] using hlu
        have hlv' : vs.length + 1 = (h' + 1) := by
          simpa [List.length_cons] using hlv
        exact Nat.add_right_cancel (hlu'.trans hlv'.symm)
      have hlenS : (GapShift w).length = 2 * (h' + 1) := by
        rw [GapShiftLength, hlen]
      rw [GapAntipodalHalves w (h' + 1) hlen,
        GapAntipodalHalves (GapShift w) (h' + 1) hlenS, htake, hdrop, hshift,
        List.take_left' hlenL, List.drop_left' hlenL,
        GapHammingRotateEnds a b us vs hlenTail]
    }

/-- Every cyclic shift preserves the antipodal distance. -/
theorem GapAntipodalShiftN (k : ℕ) (w : List Bool) (h : ℕ)
    (hlen : w.length = 2 * h) :
    GapAntipodal (GapShiftN k w) = GapAntipodal w := by
  induction k with
  | zero => {
      rw [GapShiftNZero]
    }
  | succ k ih => {
      have hlenk : (GapShiftN k w).length = 2 * h := by
        rw [GapShiftNLength, hlen]
      rw [GapShiftNSucc, GapAntipodalShift (GapShiftN k w) h hlenk, ih]
    }

/-- Odd-letter count of the length-`h` prefix. -/
def GapHalfOdd (w : List Bool) (h : ℕ) : ℕ :=
  GapOddCount (w.take h)

/-- After `h` shifts the prefix count is the original suffix count. -/
theorem GapWalkEnd (w : List Bool) (h : ℕ) (hlen : w.length = 2 * h) :
    GapHalfOdd (GapShiftN h w) h =
      GapOddCount w - GapHalfOdd w h := by
  have hlens := GapTakeDropLengths w h hlen
  have hswap : GapShiftN h w = w.drop h ++ w.take h := by
    have hcat : w.take h ++ w.drop h = w := List.take_append_drop h w
    have hex := GapShiftNHalves (w.take h) (w.drop h)
    rw [hlens.1, hcat] at hex
    exact hex
  have htake : (GapShiftN h w).take h = w.drop h := by
    rw [hswap]
    exact List.take_left' hlens.2
  have hsum := GapOddCountTakeDrop w h
  unfold GapHalfOdd
  rw [htake, hsum, Nat.add_sub_cancel_left]

/-- One shift changes the prefix odd-letter count by at most one. -/
theorem GapHalfOddShift (w : List Bool) (h : ℕ) (hlen : w.length = 2 * h)
    (hpos : 0 < h) :
    GapHalfOdd (GapShift w) h ≤ GapHalfOdd w h + 1 ∧
      GapHalfOdd w h ≤ GapHalfOdd (GapShift w) h + 1 := by
  obtain ⟨a, b, us, vs, htake, _hdrop, hshift, hlenL, _hlenR⟩ :=
    GapShiftSplit w h hlen hpos
  have hold : GapHalfOdd w h = GapBit a + GapOddCount us := by
    unfold GapHalfOdd
    rw [htake, GapOddCountCons]
  have hnew : GapHalfOdd (GapShift w) h =
      GapOddCount us + GapBit b := by
    unfold GapHalfOdd
    rw [hshift, List.take_left' hlenL, GapOddCountAppend, GapOddCountCons,
      GapOddCountNil, Nat.add_zero]
  rw [hold, hnew]
  refine ⟨?_, ?_⟩
  · have h1 : GapOddCount us + GapBit b ≤ GapOddCount us + 1 :=
      Nat.add_le_add_left (GapBitLeOne b) _
    have h2 : GapOddCount us ≤ GapBit a + GapOddCount us :=
      Nat.le_add_left _ _
    have h3 : GapOddCount us + 1 ≤ GapBit a + GapOddCount us + 1 :=
      Nat.add_le_add_right h2 1
    exact Nat.le_trans h1 h3
  · have h1 : GapBit a + GapOddCount us ≤ 1 + GapOddCount us :=
      Nat.add_le_add_right (GapBitLeOne a) _
    have hcomm : 1 + GapOddCount us = GapOddCount us + 1 :=
      Nat.add_comm 1 _
    have hb : 1 ≤ GapBit b + 1 := Nat.le_add_left 1 (GapBit b)
    have hleft : GapOddCount us + 1 ≤
        GapOddCount us + (GapBit b + 1) :=
      Nat.add_le_add_left hb _
    have hassoc : GapOddCount us + (GapBit b + 1) =
        GapOddCount us + GapBit b + 1 := by
      rw [← Nat.add_assoc]
    exact Nat.le_trans h1 (Nat.le_trans (Nat.le_of_eq hcomm)
      (hassoc ▸ hleft))

/-- A unit-step walk hits every natural value between its endpoints. -/
theorem GapUnitStepHits (n : ℕ) :
    ∀ (f : ℕ → ℕ) (m : ℕ),
      (∀ k, k < n →
        f (k + 1) ≤ f k + 1 ∧ f k ≤ f (k + 1) + 1) →
      (f 0 ≤ m ∧ m ≤ f n ∨ f n ≤ m ∧ m ≤ f 0) →
      ∃ k, k ≤ n ∧ f k = m := by
  induction n with
  | zero => {
      intro f m _ hbetween
      refine ⟨0, Nat.le_refl 0, ?_⟩
      rcases hbetween with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
      · exact Nat.le_antisymm hlo hhi
      · exact Nat.le_antisymm hlo hhi
    }
  | succ n ih => {
      intro f m hstep hbetween
      have hstepn : ∀ k, k < n →
          f (k + 1) ≤ f k + 1 ∧ f k ≤ f (k + 1) + 1 := by
        intro k hk
        exact hstep k (Nat.lt_succ_of_lt hk)
      have hlast := hstep n (Nat.lt_succ_self n)
      rcases hbetween with ⟨h0m, hmend⟩ | ⟨hendm, hm0⟩
      · by_cases hmn : m ≤ f n
        · obtain ⟨k, hk, heq⟩ := ih f m hstepn (Or.inl ⟨h0m, hmn⟩)
          exact ⟨k, Nat.le_succ_of_le hk, heq⟩
        · have hlt : f n < m := Nat.not_le.mp hmn
          have hsucc : f n + 1 ≤ m := Nat.succ_le_of_lt hlt
          have hup : f (n + 1) ≤ f n + 1 := hlast.1
          have hme : m ≤ f (n + 1) := hmend
          have hbound : m ≤ f n + 1 := Nat.le_trans hme hup
          have hid : m = f n + 1 := Nat.le_antisymm hbound hsucc
          have hback : f n + 1 ≤ f (n + 1) := by
            rw [← hid]
            exact hme
          have heq : f (n + 1) = m := by
            exact (Nat.le_antisymm hup hback).trans hid.symm
          exact ⟨n + 1, Nat.le_refl _, heq⟩
      · by_cases hnm : f n ≤ m
        · obtain ⟨k, hk, heq⟩ := ih f m hstepn (Or.inr ⟨hnm, hm0⟩)
          exact ⟨k, Nat.le_succ_of_le hk, heq⟩
        · have hlt : m < f n := Nat.not_le.mp hnm
          have hsucc : m + 1 ≤ f n := Nat.succ_le_of_lt hlt
          have hdn : f n ≤ f (n + 1) + 1 := hlast.2
          have hle : f (n + 1) ≤ m := hendm
          have hchain : m + 1 ≤ f (n + 1) + 1 := Nat.le_trans hsucc hdn
          have hmle : m ≤ f (n + 1) := Nat.le_of_succ_le_succ hchain
          exact ⟨n + 1, Nat.le_refl _, Nat.le_antisymm hle hmle⟩
    }

/-- Some cyclic shift gives the two halves the same odd-letter count. -/
theorem GapEqualOddCut (w : List Bool) (h t : ℕ) (hlen : w.length = 2 * h)
    (heven : GapOddCount w = 2 * t) :
    ∃ k, k ≤ h ∧
      GapOddCount ((GapShiftN k w).take h) =
        GapOddCount ((GapShiftN k w).drop h) := by
  let f : ℕ → ℕ := fun k => GapHalfOdd (GapShiftN k w) h
  have hf0 : f 0 = GapHalfOdd w h := by
    unfold f
    rw [GapShiftNZero]
  have hstartLe : GapHalfOdd w h ≤ GapOddCount w := by
    unfold GapHalfOdd
    rw [GapOddCountTakeDrop w h]
    exact Nat.le_add_right _ _
  have hstart : GapHalfOdd w h ≤ 2 * t := by
    rw [← heven]
    exact hstartLe
  have hend : f h = 2 * t - GapHalfOdd w h := by
    unfold f
    rw [GapWalkEnd w h hlen, heven]
  have hstep : ∀ k, k < h →
      f (k + 1) ≤ f k + 1 ∧ f k ≤ f (k + 1) + 1 := by
    intro k hk
    have hpos : 0 < h := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
    have hlenk : (GapShiftN k w).length = 2 * h := by
      rw [GapShiftNLength, hlen]
    have hmove := GapHalfOddShift (GapShiftN k w) h hlenk hpos
    have hfun : f (k + 1) = GapHalfOdd (GapShift (GapShiftN k w)) h := by
      unfold f
      rw [GapShiftNSucc]
    have hcur : f k = GapHalfOdd (GapShiftN k w) h := rfl
    rw [hfun, hcur]
    exact hmove
  have hbetween : f 0 ≤ t ∧ t ≤ f h ∨ f h ≤ t ∧ t ≤ f 0 := by
    rw [hf0, hend]
    by_cases hle : GapHalfOdd w h ≤ t
    · left
      refine ⟨hle, ?_⟩
      have hadd : t + GapHalfOdd w h ≤ t + t :=
        Nat.add_le_add_left hle t
      rw [← Nat.two_mul] at hadd
      exact Nat.le_sub_of_add_le hadd
    · right
      have hlt : t < GapHalfOdd w h := Nat.not_le.mp hle
      have hta : t ≤ GapHalfOdd w h := Nat.le_of_lt hlt
      refine ⟨?_, hta⟩
      have hsub : 2 * t - GapHalfOdd w h ≤ 2 * t - t :=
        Nat.sub_le_sub_left hta (2 * t)
      have hcancel : 2 * t - t = t := by
        rw [Nat.two_mul, Nat.add_sub_cancel_left]
      exact Nat.le_trans hsub (Nat.le_of_eq hcancel)
  obtain ⟨k, hk, heqf⟩ := GapUnitStepHits h f t hstep hbetween
  have hfirst : GapOddCount ((GapShiftN k w).take h) = t := by
    have hfk : f k = GapHalfOdd (GapShiftN k w) h := rfl
    rw [heqf] at hfk
    unfold GapHalfOdd at hfk
    exact hfk.symm
  have hsecond : GapOddCount ((GapShiftN k w).drop h) = t := by
    have hsum := GapOddCountTakeDrop (GapShiftN k w) h
    rw [GapShiftNOddCount, heven, hfirst] at hsum
    have hrev : t + GapOddCount ((GapShiftN k w).drop h) = 2 * t :=
      hsum.symm
    rw [Nat.two_mul] at hrev
    exact Nat.add_left_cancel hrev
  exact ⟨k, hk, hfirst.trans hsecond.symm⟩

/-- Every shifted cut has the original antipodal distance. -/
theorem GapCutHamming (w : List Bool) (h k : ℕ) (hlen : w.length = 2 * h) :
    GapHamming ((GapShiftN k w).take h) ((GapShiftN k w).drop h) =
      GapAntipodal w := by
  have hlenk : (GapShiftN k w).length = 2 * h := by
    rw [GapShiftNLength, hlen]
  rw [← GapAntipodalHalves (GapShiftN k w) h hlenk,
    GapAntipodalShiftN k w h hlen]

/-- Distance two has a balanced transport witness within the first half-turn. -/
theorem GapBoundedTransport (w : List Bool) (h : ℕ) (hlen : w.length = 2 * h)
    (h2 : GapAntipodal w = 2) :
    ∃ k, k ≤ h ∧
      GapOddCount ((GapShiftN k w).take h) =
        GapOddCount ((GapShiftN k w).drop h) ∧
      GapHamming ((GapShiftN k w).take h) ((GapShiftN k w).drop h) = 2 := by
  have hpar := GapAntipodalModTwo w h hlen
  have hmod : GapOddCount w % 2 = 0 := by omega
  obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hmod
  obtain ⟨k, hk, heq⟩ := GapEqualOddCut w h t hlen ht
  have hdist := GapCutHamming w h k hlen
  exact ⟨k, hk, heq, hdist.trans h2⟩

/-- A one-bit transport: equal halves, equal odd counts, and distance `2`. -/
def GapAdmitsTransport (w : List Bool) : Prop :=
  ∃ k u v,
    GapShiftN k w = u ++ v ∧
      u.length = v.length ∧
        GapOddCount u = GapOddCount v ∧
          GapHamming u v = 2

/-- Distance `2` is exactly the existence of a one-bit transport. -/
theorem GapAdmitsIffTwo (w : List Bool) (h : ℕ) (hlen : w.length = 2 * h) :
    GapAdmitsTransport w ↔ GapAntipodal w = 2 := by
  constructor
  · intro htrans
    obtain ⟨k, u, v, hcat, hlenuv, _hodd, hham⟩ := htrans
    have hlenk : (GapShiftN k w).length = 2 * h := by
      rw [GapShiftNLength, hlen]
    have hsum : u.length + v.length = 2 * h := by
      rw [← List.length_append, ← hcat, hlenk]
    have htwice : u.length + u.length = 2 * h := by
      rw [← hlenuv] at hsum
      exact hsum
    have hmul : 2 * u.length = 2 * h := by
      rw [Nat.two_mul]
      exact htwice
    have hu : u.length = h := by
      calc
        u.length = (2 * u.length) / 2 := (GapHalfIndex u.length).symm
        _ = (2 * h) / 2 := by rw [hmul]
        _ = h := GapHalfIndex h
    have htake : (GapShiftN k w).take h = u := by
      rw [hcat]
      exact List.take_left' hu
    have hdrop : (GapShiftN k w).drop h = v := by
      rw [hcat]
      exact List.drop_left' hu
    have hdist := GapCutHamming w h k hlen
    rw [htake, hdrop, hham] at hdist
    exact hdist.symm
  · intro h2
    obtain ⟨k, _hk, heq, hham⟩ := GapBoundedTransport w h hlen h2
    refine ⟨k, (GapShiftN k w).take h, (GapShiftN k w).drop h, ?_, ?_, heq, hham⟩
    · exact (List.take_append_drop h (GapShiftN k w)).symm
    · have hlens := GapTakeDropLengths (GapShiftN k w) h
        (by rw [GapShiftNLength, hlen])
      exact hlens.1.trans hlens.2.symm

/-- Distance zero is a repeated block. -/
theorem GapRepetitionIff (w : List Bool) (h : ℕ) (hlen : w.length = 2 * h) :
    (∃ u : List Bool, w = u ++ u) ↔ GapAntipodal w = 0 := by
  constructor
  · intro hrep
    obtain ⟨u, hu⟩ := hrep
    have htwice : u.length + u.length = 2 * h := by
      have hlenu : (u ++ u).length = u.length + u.length :=
        List.length_append
      rw [← hu, hlen] at hlenu
      exact hlenu.symm
    have hmul : 2 * u.length = 2 * h := by
      rw [Nat.two_mul]
      exact htwice
    have huLen : u.length = h := by
      calc
        u.length = (2 * u.length) / 2 := (GapHalfIndex u.length).symm
        _ = (2 * h) / 2 := by rw [hmul]
        _ = h := GapHalfIndex h
    rw [GapAntipodalHalves w h hlen, hu, List.take_left' huLen,
      List.drop_left' huLen, GapHammingSelf]
  · intro h0
    refine ⟨w.take h, ?_⟩
    have hjoin : w = w.take h ++ w.drop h :=
      (List.take_append_drop h w).symm
    have hlens := GapTakeDropLengths w h hlen
    have heq : w.take h = w.drop h := by
      apply GapHammingZero
      · rw [hlens.1, hlens.2]
      · rw [← GapAntipodalHalves w h hlen, h0]
    calc
      w = w.take h ++ w.drop h := hjoin
      _ = w.take h ++ w.take h := by rw [heq]

/-- An even positive distance other than `2` is at least `4`. -/
theorem GapEvenAtLeastFour (n : ℕ) (hmod : n % 2 = 0) (h0 : n ≠ 0)
    (h2 : n ≠ 2) : 4 ≤ n := by
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hq0 : q ≠ 0 := by
    intro hz
    apply h0
    rw [hq, hz, Nat.mul_zero]
  have hq1 : q ≠ 1 := by
    intro ho
    apply h2
    rw [hq, ho, Nat.mul_one]
  have hone : 1 ≤ q := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hq0)
  have hlt : 1 < q := Nat.lt_of_le_of_ne hone (Ne.symm hq1)
  have h2q : 2 ≤ q := Nat.succ_le_of_lt hlt
  have hmul : 2 * 2 ≤ 2 * q := Nat.mul_le_mul_left 2 h2q
  have hfour : 4 ≤ 2 * q := by
    have h22 : 2 * 2 = 4 := rfl
    rw [← h22]
    exact hmul
  rw [hq]
  exact hfour

/-- Even odd count, no repeated block, and no one-bit transport give distance
at least `4`. -/
theorem GapAntipodalAtLeastFour (w : List Bool) (h : ℕ)
    (hlen : w.length = 2 * h)
    (heven : ∃ t : ℕ, GapOddCount w = 2 * t)
    (hrep : ¬ ∃ u : List Bool, w = u ++ u)
    (htrans : ¬ GapAdmitsTransport w) :
    4 ≤ GapAntipodal w := by
  obtain ⟨t, ht⟩ := heven
  have hmod : GapAntipodal w % 2 = 0 := by
    have hodd : GapOddCount w % 2 = 0 := by
      rw [ht, Nat.mul_mod_right]
    rw [GapAntipodalModTwo w h hlen, hodd]
  have hne0 : GapAntipodal w ≠ 0 := by
    intro h0
    exact hrep ((GapRepetitionIff w h hlen).2 h0)
  have hne2 : GapAntipodal w ≠ 2 := by
    intro h2
    exact htrans ((GapAdmitsIffTwo w h hlen).2 h2)
  exact GapEvenAtLeastFour (GapAntipodal w) hmod hne0 hne2

/-- Halves `000011` and `101000`. -/
def GapSharpWord : List Bool :=
  [false, false, false, false, true, true,
    true, false, true, false, false, false]

/-- The sharp word has length `12`. -/
theorem GapSharpWordLength : GapSharpWord.length = 2 * 6 := rfl

/-- The sharp word has four odd letters. -/
theorem GapSharpWordOdd : GapOddCount GapSharpWord = 2 * 2 := rfl

/-- The sharp word has antipodal distance `4`. -/
theorem GapSharpWordAntipodal : GapAntipodal GapSharpWord = 4 := rfl

/-- The sharp word is not a repeated block. -/
theorem GapSharpWordNotRepetition :
    ¬ ∃ u : List Bool, GapSharpWord = u ++ u := by
  intro hrep
  have h0 : GapAntipodal GapSharpWord = 0 :=
    (GapRepetitionIff GapSharpWord 6 GapSharpWordLength).1 hrep
  rw [GapSharpWordAntipodal] at h0
  exact Nat.succ_ne_zero 3 h0

/-- The sharp word has no one-bit transport. -/
theorem GapSharpWordNoTransport : ¬ GapAdmitsTransport GapSharpWord := by
  intro htrans
  have h2 : GapAntipodal GapSharpWord = 2 :=
    (GapAdmitsIffTwo GapSharpWord 6 GapSharpWordLength).1 htrans
  rw [GapSharpWordAntipodal] at h2
  have h3 : (3 : ℕ) = 1 := Nat.succ_inj.mp h2
  have hzero : (2 : ℕ) = 0 := Nat.succ_inj.mp h3
  exact Nat.succ_ne_zero 1 hzero

/-- Distance `4` satisfies the gap, so the constant is attained. -/
theorem GapSharpWordAttained :
    GapAntipodal GapSharpWord = 4 ∧ 4 ≤ GapAntipodal GapSharpWord := by
  refine ⟨GapSharpWordAntipodal, ?_⟩
  exact GapAntipodalAtLeastFour GapSharpWord 6 GapSharpWordLength
    ⟨2, GapSharpWordOdd⟩ GapSharpWordNotRepetition GapSharpWordNoTransport

/-- The word `10`, with one odd letter. -/
def GapTrivialWord : List Bool := [true, false]

/-- `10` has length `2`, one odd letter, and antipodal distance `1`. -/
theorem GapTrivialWordData :
    GapTrivialWord.length = 2 * 1 ∧
      GapOddCount GapTrivialWord = 1 ∧
        GapAntipodal GapTrivialWord = 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- `10` is not a repetition and admits no one-bit transport. -/
theorem GapTrivialWordHypotheses :
    (¬ ∃ u : List Bool, GapTrivialWord = u ++ u) ∧
      ¬ GapAdmitsTransport GapTrivialWord := by
  refine ⟨?_, ?_⟩
  · intro hrep
    have h0 : GapAntipodal GapTrivialWord = 0 :=
      (GapRepetitionIff GapTrivialWord 1 (rfl : GapTrivialWord.length = 2)).1
        hrep
    have h1 : GapAntipodal GapTrivialWord = 1 := rfl
    rw [h1] at h0
    exact Nat.succ_ne_zero 0 h0
  · intro htrans
    have h2 : GapAntipodal GapTrivialWord = 2 :=
      (GapAdmitsIffTwo GapTrivialWord 1 (rfl : GapTrivialWord.length = 2)).1
        htrans
    have h1 : GapAntipodal GapTrivialWord = 1 := rfl
    rw [h1] at h2
    have hzero : (0 : ℕ) = 1 := Nat.succ_inj.mp h2
    exact Nat.succ_ne_zero 0 hzero.symm

/-- Dropping the even-count hypothesis allows distance `1`. -/
theorem GapTrivialWordBelowFour : ¬ 4 ≤ GapAntipodal GapTrivialWord := by
  intro hle
  have h1 : GapAntipodal GapTrivialWord = 1 := rfl
  rw [h1] at hle
  have h3 : 3 ≤ 0 := Nat.le_of_succ_le_succ hle
  exact Nat.not_succ_le_zero 2 h3

/-- The repeated word `0101`. -/
def GapRepeatWord : List Bool := [false, true, false, true]

/-- `0101` has length `4`, two odd letters, and antipodal distance `0`. -/
theorem GapRepeatWordData :
    GapRepeatWord.length = 2 * 2 ∧
      GapOddCount GapRepeatWord = 2 * 1 ∧
        GapAntipodal GapRepeatWord = 0 := by
  exact ⟨rfl, rfl, rfl⟩

/-- `0101` is a repetition and admits no one-bit transport. -/
theorem GapRepeatWordHypotheses :
    (∃ u : List Bool, GapRepeatWord = u ++ u) ∧
      ¬ GapAdmitsTransport GapRepeatWord := by
  refine ⟨?_, ?_⟩
  · exact ⟨[false, true], rfl⟩
  · intro htrans
    have h2 : GapAntipodal GapRepeatWord = 2 :=
      (GapAdmitsIffTwo GapRepeatWord 2 (rfl : GapRepeatWord.length = 4)).1
        htrans
    have h0 : GapAntipodal GapRepeatWord = 0 := rfl
    rw [h0] at h2
    exact Nat.succ_ne_zero 1 h2.symm

/-- Dropping the non-repetition hypothesis allows distance `0`. -/
theorem GapRepeatWordBelowFour : ¬ 4 ≤ GapAntipodal GapRepeatWord := by
  intro hle
  have h0 : GapAntipodal GapRepeatWord = 0 := rfl
  rw [h0] at hle
  exact Nat.not_succ_le_zero 3 hle

/-- The word `0011` tests the necessity of excluding transports. -/
def GapTransportWord : List Bool := [false, false, true, true]

/-- `0011` has two odd letters and distance two, without being a repetition. -/
theorem GapTransportWordData :
    GapTransportWord.length = 2 * 2 ∧
      GapOddCount GapTransportWord = 2 * 1 ∧
      GapAntipodal GapTransportWord = 2 ∧
      (¬ ∃ u : List Bool, GapTransportWord = u ++ u) ∧
      GapAdmitsTransport GapTransportWord ∧
      ¬ 4 ≤ GapAntipodal GapTransportWord := by
  have hlen : GapTransportWord.length = 2 * 2 := rfl
  have hodd : GapOddCount GapTransportWord = 2 * 1 := rfl
  have hdist : GapAntipodal GapTransportWord = 2 := rfl
  have hrep : ¬ ∃ u : List Bool, GapTransportWord = u ++ u := by
    intro hrep
    have hzero := (GapRepetitionIff GapTransportWord 2 hlen).1 hrep
    omega
  have htrans := (GapAdmitsIffTwo GapTransportWord 2 hlen).2 hdist
  have hbelow : ¬ 4 ≤ GapAntipodal GapTransportWord := by omega
  exact ⟨hlen, hodd, hdist, hrep, htrans, hbelow⟩

/-- The two halves `001` and `100` exchange nonadjacent positions. -/
def GapSeparatedWord : List Bool := [false, false, true, true, false, false]

/-- A balanced transport need not exchange adjacent positions. -/
theorem GapSeparatedWordData :
    GapSeparatedWord.length = 2 * 3 ∧
      GapOddCount (GapSeparatedWord.take 3) = 1 ∧
      GapOddCount (GapSeparatedWord.drop 3) = 1 ∧
      GapAntipodal GapSeparatedWord = 2 ∧
      GapAdmitsTransport GapSeparatedWord := by
  have hlen : GapSeparatedWord.length = 2 * 3 := rfl
  have hleft : GapOddCount (GapSeparatedWord.take 3) = 1 := rfl
  have hright : GapOddCount (GapSeparatedWord.drop 3) = 1 := rfl
  have hdist : GapAntipodal GapSeparatedWord = 2 := rfl
  exact ⟨hlen, hleft, hright, hdist,
    (GapAdmitsIffTwo GapSeparatedWord 3 hlen).2 hdist⟩

end GeneralizedCollatz.HammingGap
