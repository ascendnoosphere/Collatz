-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

/-!
The even row of an overlapping local split.

If `n > 1` is even, the parent `n / 2` is a positive integer strictly smaller
than `n`. The one-letter even word and the empty parent word meet there.
An odd input is outside this row. No other row, and no cover of every integer
greater than one, is asserted.
-/

set_option autoImplicit false

notation "ℕ" => Nat

namespace GeneralizedCollatz

/-- Classical shortcut: halve an even input, and send an odd input to `(3n+1)/2`. -/
def Shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The even branch is ordinary halving. -/
theorem ShortcutEven (n : ℕ) (h : n % 2 = 0) : Shortcut n = n / 2 := by
  unfold Shortcut
  rw [if_pos h]

/-- Exact doubling on an even input: division by two leaves remainder zero. -/
theorem EvenParentIdentity (n : ℕ) (h : n % 2 = 0) : 2 * (n / 2) = n := by
  have hsplit : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  rw [h, Nat.add_zero] at hsplit
  exact hsplit

/-- The parent of an even integer greater than one is positive and strictly smaller. -/
theorem EvenParentStrict (n : ℕ) (hn : 1 < n) (h : n % 2 = 0) :
    0 < n / 2 ∧ n / 2 < n := by
  have hid : 2 * (n / 2) = n := EvenParentIdentity n h
  have hpos : 0 < n / 2 := by
    cases Nat.eq_zero_or_pos (n / 2) with
    | inl hz =>
      {
        have hn0 : n = 0 := by
          rw [hz, Nat.mul_zero] at hid
          exact hid.symm
        rw [hn0] at hn
        exact absurd hn (Nat.not_lt_zero 1)
      }
    | inr hp =>
      {
        exact hp
      }
  have hlt : n / 2 < n := by
    have htwice : n / 2 < 2 * (n / 2) := by
      rw [Nat.two_mul]
      exact Nat.lt_add_of_pos_right hpos
    rw [hid] at htwice
    exact htwice
  exact ⟨hpos, hlt⟩

/-- One parity letter. `false` is the even letter and `true` is the odd letter. -/
def StepBit (b : Bool) (n : ℕ) : ℕ :=
  if b then (3 * n + 1) / 2 else n / 2

/-- The even letter halves its input. -/
theorem StepBitEven (n : ℕ) : StepBit false n = n / 2 := by
  unfold StepBit
  rfl

/-- Evaluate a chronological parity word, applying the head letter first. -/
def RunWord : List Bool → ℕ → ℕ
  | [], n => n
  | b :: bs, n => RunWord bs (StepBit b n)

/-- The empty word leaves its input fixed. -/
theorem RunWordNil (n : ℕ) : RunWord [] n = n := rfl

/-- A nonempty word applies its first letter and then the suffix. -/
theorem RunWordCons (b : Bool) (bs : List Bool) (n : ℕ) :
    RunWord (b :: bs) n = RunWord bs (StepBit b n) := rfl

/-- Source word of the even row: a single even letter. -/
def EvenSourceWord : List Bool := [false]

/-- Parent word of the even row: the empty word. -/
def EvenParentWord : List Bool := []

/-- The even source word and the empty parent word meet at the exact half. -/
theorem EvenSourceMeetsParent (n : ℕ) (h : n % 2 = 0) :
    RunWord EvenSourceWord n = n / 2 ∧
      RunWord EvenParentWord (n / 2) = n / 2 ∧
      2 * RunWord EvenSourceWord n = n := by
  have hsrc : RunWord EvenSourceWord n = n / 2 := by
    unfold EvenSourceWord
    rw [RunWordCons, RunWordNil, StepBitEven]
  have hpar : RunWord EvenParentWord (n / 2) = n / 2 := by
    unfold EvenParentWord
    show RunWord [] (n / 2) = n / 2
    exact RunWordNil (n / 2)
  have hexact : 2 * RunWord EvenSourceWord n = n := by
    rw [hsrc]
    exact EvenParentIdentity n h
  exact ⟨hsrc, hpar, hexact⟩

/-- Even row: exact parent, strict decrease, and agreement of the two words. -/
theorem EvenFamilySplit (n : ℕ) (hn : 1 < n) (h : n % 2 = 0) :
    0 < n / 2 ∧ n / 2 < n ∧ Shortcut n = n / 2 ∧
      2 * (n / 2) = n ∧
      RunWord EvenSourceWord n = RunWord EvenParentWord (n / 2) := by
  have hstrict : 0 < n / 2 ∧ n / 2 < n := EvenParentStrict n hn h
  have hshort : Shortcut n = n / 2 := ShortcutEven n h
  have hid : 2 * (n / 2) = n := EvenParentIdentity n h
  have hmeet := EvenSourceMeetsParent n h
  have hjoin :
      RunWord EvenSourceWord n = RunWord EvenParentWord (n / 2) := by
    show RunWord EvenSourceWord n = RunWord EvenParentWord (n / 2)
    rw [hmeet.1, hmeet.2.1]
  exact ⟨hstrict.1, hstrict.2, hshort, hid, hjoin⟩

/-- Membership in the even row: size, exact half, and agreement of the two words. -/
def EvenFamilyMember (n : ℕ) : Prop :=
  1 < n ∧ n % 2 = 0 ∧ 0 < n / 2 ∧ n / 2 < n ∧ Shortcut n = n / 2 ∧
    2 * (n / 2) = n ∧
    RunWord EvenSourceWord n = RunWord EvenParentWord (n / 2)

/-- Every even integer greater than one lies in the even row. -/
theorem EvenFamilyMemberOfEven (n : ℕ) (hn : 1 < n) (h : n % 2 = 0) :
    EvenFamilyMember n := by
  have hsplit := EvenFamilySplit n hn h
  exact ⟨hn, h, hsplit.1, hsplit.2.1, hsplit.2.2.1, hsplit.2.2.2.1,
    hsplit.2.2.2.2⟩

/-- An odd input fails the even-row parity condition, so it is not a member. -/
theorem OddOutsideEvenFamily (n : ℕ) (h : n % 2 = 1) : ¬ EvenFamilyMember n := by
  intro hmem
  have hmod : n % 2 = 0 := hmem.2.1
  rw [h] at hmod
  exact Nat.one_ne_zero hmod

/-- The integer three is odd, hence outside the even row. -/
theorem ThreeOutsideEvenFamily : ¬ EvenFamilyMember 3 := by
  have hodd : 3 % 2 = 1 := rfl
  exact OddOutsideEvenFamily 3 hodd

end GeneralizedCollatz
