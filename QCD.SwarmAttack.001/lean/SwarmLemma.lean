-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.GCD
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Repeated-word budget for the classical shortcut

The classical shortcut is

`T(n) = n / 2` for even `n`, and `T(n) = (3 n + 1) / 2` for odd `n`.

A binary word records the parity of the input at each tick.  This file proves
that the `k`-fold repetition of a fixed word is legal at `n` exactly when the
`k`-th power of the word denominator divides the signed defect
`(P - Q) n + B`, where `(P, Q, B)` is the affine data of one copy of the word.

The theorem is the repeated-word budget stated in
`QCD.ClassicalCoalescence.001/tex/ClassicalCoalescence.tex`, Section
"Exact repeated-word budget".  It is a general lemma about all finite words;
no particular cylinder is assumed.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.SwarmAttack

/-- The classical shortcut: halve an even input and send an odd input to
`(3 n + 1) / 2`. -/
def Shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- One letter acts by its displayed affine branch.  The boolean `true` is the
odd letter `(3 x + 1) / 2`; `false` is the even letter `x / 2`. -/
def Letter (b : Bool) (x : ℕ) : ℕ :=
  if b then (3 * x + 1) / 2 else x / 2

/-- Execute a word letter by letter from the left. -/
def WordAct : List Bool → ℕ → ℕ
  | [], n => n
  | b :: w, n => WordAct w (Letter b n)

/-- A word is legal at `n` when each letter is the actual shortcut branch at
its input.  The recursion reads the word from the left. -/
def Legal : List Bool → ℕ → Prop
  | [], _ => True
  | b :: w, n =>
      (if b then n % 2 = 1 else n % 2 = 0) ∧ Legal w (Letter b n)

/-- Affine data `(P, Q, B)` for the rational map `x ↦ (P x + B) / Q`. -/
@[ext]
structure AffineData where
  /-- Numerator multiplier. -/
  P : ℕ
  /-- Denominator. -/
  Q : ℕ
  /-- Additive offset. -/
  B : ℕ

/-- Integer data for executing `d` and then `e`. -/
def AffineData.Compose (d e : AffineData) : AffineData where
  P := e.P * d.P
  Q := e.Q * d.Q
  B := e.P * d.B + e.B * d.Q

/-- Affine data of a single letter. -/
def LetterData : Bool → AffineData
  | true => ⟨3, 2, 1⟩
  | false => ⟨1, 2, 0⟩

/-- Affine data of a word, composed from the left. -/
def Affine : List Bool → AffineData
  | [] => ⟨1, 1, 0⟩
  | b :: w => (LetterData b).Compose (Affine w)

/-- The signed defect `(P - Q) n + B` attached to the affine data of a word. -/
def Defect (w : List Bool) (n : ℕ) : ℤ :=
  (((Affine w).P : ℤ) - ((Affine w).Q : ℤ)) * (n : ℤ) + ((Affine w).B : ℤ)

/-- The `k`-fold repetition of a word. -/
def WordPow (w : List Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 => w ++ WordPow w k

/-- A displayed even state halves exactly. -/
theorem ShortcutEven (k : ℕ) : Shortcut (2 * k) = k := by
  simp [Shortcut]

/-- A displayed odd state has the exact odd branch. -/
theorem ShortcutOdd (k : ℕ) : Shortcut (2 * k + 1) = 3 * k + 2 := by
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  simp only [Shortcut, hmod, if_neg (by decide : ¬ (1 : ℕ) = 0)]
  omega

/-- The even letter is exact on an even input. -/
theorem LetterEven (x : ℕ) (hx : x % 2 = 0) : 2 * Letter false x = x := by
  simp only [Letter, Bool.false_eq_true, if_false]
  omega

/-- The odd letter is exact on an odd input. -/
theorem LetterOdd (x : ℕ) (hx : x % 2 = 1) : 2 * Letter true x = 3 * x + 1 := by
  simp only [Letter, if_true]
  omega

/-- A legal letter agrees with the shortcut. -/
theorem LetterShortcut (b : Bool) (x : ℕ)
    (h : if b then x % 2 = 1 else x % 2 = 0) : Letter b x = Shortcut x := by
  cases b with
    | false => {
        have hx : x % 2 = 0 := by simpa using h
        simp only [Letter, Bool.false_eq_true, if_false, Shortcut, hx, if_pos]
    }
    | true => {
        have hx : x % 2 = 1 := by simpa using h
        simp only [Letter, if_true, Shortcut, hx,
          if_neg (by decide : ¬ (1 : ℕ) = 0)]

    }
/-- A legal word executes exactly the corresponding shortcut iterate. -/
theorem LegalWordAct (w : List Bool) (n : ℕ) (h : Legal w n) :
    WordAct w n = Shortcut^[w.length] n := by
  induction w generalizing n with
    | nil => { simp [WordAct] }
    | cons b w ih => {
        obtain ⟨hb, hw⟩ := h
        have hstep : Letter b n = Shortcut n := LetterShortcut b n hb
        rw [WordAct]
        rw [show (b :: w).length = w.length + 1 by simp]
        rw [Function.iterate_succ_apply, ← hstep]
        exact ih (Letter b n) hw

    }
/-- A legal letter satisfies the exact two-times affine identity. -/
theorem LetterDataCorrect (b : Bool) (x : ℕ)
    (h : if b then x % 2 = 1 else x % 2 = 0) :
    2 * Letter b x = (LetterData b).P * x + (LetterData b).B := by
  cases b with
    | false => {
        have hx : x % 2 = 0 := by simpa using h
        simp only [Letter, Bool.false_eq_true, if_false, LetterData]
        omega
    }
    | true => {
        have hx : x % 2 = 1 := by simpa using h
        simp only [Letter, if_true, LetterData]
        omega

    }
/-- The affine data of a legal word satisfies `Q * WordAct = P * n + B`. -/
theorem AffineWordAct (w : List Bool) (n : ℕ) (h : Legal w n) :
    (Affine w).Q * WordAct w n = (Affine w).P * n + (Affine w).B := by
  induction w generalizing n with
    | nil => { simp [Affine, WordAct] }
    | cons b w ih => {
        obtain ⟨hb, hw⟩ := h
        have htail := ih (Letter b n) hw
        have hletter := LetterDataCorrect b n hb
        simp only [Affine, AffineData.Compose, WordAct, LetterData] at htail hletter ⊢
        cases b with
          | false => {
              calc
                ((Affine w).Q * 2) * WordAct w (Letter false n) =
                    2 * ((Affine w).Q * WordAct w (Letter false n)) := by ring
                _ = 2 * ((Affine w).P * Letter false n + (Affine w).B) := by rw [htail]
                _ = (Affine w).P * (2 * Letter false n) + (Affine w).B * 2 := by ring
                _ = (Affine w).P * (1 * n + 0) + (Affine w).B * 2 := by rw [hletter]
                _ = ((Affine w).P * 1) * n +
                    ((Affine w).P * 0 + (Affine w).B * 2) := by ring
          }
          | true => {
              calc
                ((Affine w).Q * 2) * WordAct w (Letter true n) =
                    2 * ((Affine w).Q * WordAct w (Letter true n)) := by ring
                _ = 2 * ((Affine w).P * Letter true n + (Affine w).B) := by rw [htail]
                _ = (Affine w).P * (2 * Letter true n) + (Affine w).B * 2 := by ring
                _ = (Affine w).P * (3 * n + 1) + (Affine w).B * 2 := by rw [hletter]
                _ = ((Affine w).P * 3) * n +
                    ((Affine w).P * 1 + (Affine w).B * 2) := by ring

          }
    }
/-- Word execution is compatible with concatenation. -/
theorem WordActAppend (u v : List Bool) (n : ℕ) :
    WordAct (u ++ v) n = WordAct v (WordAct u n) := by
  induction u generalizing n with
    | nil => { rfl }
    | cons b u ih => { simp only [List.cons_append, WordAct, ih] }

/-- Legality of a concatenation splits at the intermediate state. -/
theorem LegalAppend (u v : List Bool) (n : ℕ) :
    Legal (u ++ v) n ↔ Legal u n ∧ Legal v (WordAct u n) := by
  induction u generalizing n with
    | nil => { simp [Legal, WordAct] }
    | cons b u ih => {
        simp only [List.cons_append, Legal, WordAct, ih]
        tauto

    }
/-- Affine composition is associative. -/
theorem ComposeAssoc (a b c : AffineData) :
    (a.Compose b).Compose c = a.Compose (b.Compose c) := by
  ext <;> simp only [AffineData.Compose] <;> ring

/-- Affine data of a concatenation composes the two presentations. -/
theorem AffineAppend (u v : List Bool) :
    Affine (u ++ v) = (Affine u).Compose (Affine v) := by
  induction u with
    | nil => { ext <;> simp [Affine, AffineData.Compose] }
    | cons b u ih => {
        simp only [List.cons_append, Affine, ih]
        exact (ComposeAssoc _ _ _).symm

    }
/-- The denominator of a word is `2 ^ length`. -/
theorem AffineQ (w : List Bool) : (Affine w).Q = 2 ^ w.length := by
  induction w with
    | nil => { simp [Affine] }
    | cons b w ih => {
        cases b with
          | false => {
              simp only [Affine, AffineData.Compose, LetterData, List.length_cons]
              rw [ih, pow_succ]
          }
          | true => {
              simp only [Affine, AffineData.Compose, LetterData, List.length_cons]
              rw [ih, pow_succ]

          }
    }
/-- The numerator multiplier of a word is odd. -/
theorem AffinePOdd (w : List Bool) : Odd (Affine w).P := by
  induction w with
    | nil => { exact ⟨0, rfl⟩ }
    | cons b w ih => {
        have hb : Odd (LetterData b).P := by
          cases b with
            | false => { exact ⟨0, rfl⟩ }
            | true => { exact ⟨1, rfl⟩ }
        simp only [Affine, AffineData.Compose]
        exact ih.mul hb

    }
/-- The denominator of a word is positive. -/
theorem AffineQPos (w : List Bool) : 0 < (Affine w).Q := by
  rw [AffineQ]
  exact Nat.pow_pos (by decide : 0 < 2)

/-- An odd number is coprime to every power of two. -/
theorem CoprimePowTwo (a m : ℕ) (ha : Odd a) : Nat.Coprime a (2 ^ m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Nat.coprime_pow_right_iff hm]
    exact ha.coprime_two_right

/-- The integer gcd of an odd multiplier with a power of two is one. -/
theorem IntGcdPowTwo (a m : ℕ) (ha : Odd a) :
    Int.gcd (a : ℤ) ((2 : ℤ) ^ m) = 1 := by
  rw [Int.gcd_def]
  simp only [Int.natAbs_natCast, Int.natAbs_pow]
  norm_num
  exact CoprimePowTwo a m ha

/-- The one-letter cylinder condition is exactly the parity condition. -/
theorem LegalSingleton (b : Bool) (n : ℕ) :
    Legal [b] n ↔ (if b then n % 2 = 1 else n % 2 = 0) := by
  simp [Legal]

/-- An exact two-times affine letter relation exposes the corresponding parity. -/
theorem LetterParity (b : Bool) (m : ℕ)
    (h : 2 ∣ (LetterData b).P * m + (LetterData b).B) :
    (if b then m % 2 = 1 else m % 2 = 0) := by
  obtain ⟨t, ht⟩ := h
  cases b with
    | false => {
        simp only [LetterData, Bool.false_eq_true, if_false] at ht ⊢
        omega
    }
    | true => {
        simp only [LetterData, if_true] at ht ⊢
        omega

    }
/-- Appending one letter preserves the cylinder criterion. -/
theorem CylinderStep (u : List Bool) (b : Bool) (n : ℕ)
    (ih : Legal u n ↔
      (Affine u).Q ∣ (Affine u).P * n + (Affine u).B) :
    Legal (u ++ [b]) n ↔
      (Affine (u ++ [b])).Q ∣
        (Affine (u ++ [b])).P * n + (Affine (u ++ [b])).B := by
  have hSingle : Affine [b] = LetterData b := by
    ext <;> simp [Affine, AffineData.Compose]
  rw [AffineAppend, hSingle, LegalAppend, ih]
  generalize hd : Affine u = d
  rw [hd] at ih
  have hdQ : d.Q = 2 ^ u.length := by
    rw [← hd]
    exact AffineQ u
  have hdpos : 0 < d.Q := by
    rw [← hd]
    exact AffineQPos u
  cases b with
    | false => {
        simp only [LetterData, AffineData.Compose, Legal, Bool.false_eq_true, if_false,
          and_true, one_mul, zero_mul, add_zero]
        constructor
        · rintro ⟨hdvd, hpar⟩
          have hlegal : Legal u n := ih.mpr hdvd
          have haff := AffineWordAct u n hlegal
          rw [hd] at haff
          rw [← haff]
          have h2 : 2 ∣ WordAct u n := by omega
          obtain ⟨t, ht⟩ := h2
          exact ⟨t, by rw [ht]; ring⟩
        · intro hdvd
          have hQ : d.Q ∣ 2 * d.Q := ⟨2, by ring⟩
          have hN : d.Q ∣ d.P * n + d.B := dvd_trans hQ hdvd
          have hlegal : Legal u n := ih.mpr hN
          have haff := AffineWordAct u n hlegal
          rw [hd] at haff
          have hdm : d.Q * 2 ∣ d.Q * WordAct u n := by
            rw [show d.Q * 2 = 2 * d.Q by ring, haff]
            exact hdvd
          have h2 : 2 ∣ WordAct u n :=
            Nat.dvd_of_mul_dvd_mul_left hdpos hdm
          exact ⟨hN, Nat.dvd_iff_mod_eq_zero.mp h2⟩
    }
    | true => {
        simp only [LetterData, AffineData.Compose, Legal, if_true, and_true, one_mul]
        constructor
        · rintro ⟨hdvd, hpar⟩
          have hlegal : Legal u n := ih.mpr hdvd
          have haff := AffineWordAct u n hlegal
          rw [hd] at haff
          have h2 : 2 ∣ 3 * WordAct u n + 1 := by omega
          obtain ⟨t, ht⟩ := h2
          refine ⟨t, ?_⟩
          calc
            3 * d.P * n + (3 * d.B + d.Q) =
                3 * (d.P * n + d.B) + d.Q := by ring
            _ = 3 * (d.Q * WordAct u n) + d.Q := by rw [haff]
            _ = d.Q * (3 * WordAct u n + 1) := by ring
            _ = d.Q * (2 * t) := by rw [ht]
            _ = (2 * d.Q) * t := by ring
        · intro hdvd
          have hsum : d.Q ∣ 3 * (d.P * n + d.B) + d.Q := by
            have htrans : d.Q ∣ 2 * d.Q := ⟨2, by ring⟩
            simpa only [mul_add, mul_assoc, add_assoc] using dvd_trans htrans hdvd
          have hX3 : d.Q ∣ 3 * (d.P * n + d.B) :=
            (Nat.dvd_add_iff_left (dvd_refl d.Q)).mpr hsum
          have hcop : Nat.Coprime d.Q 3 := by
            rw [hdQ]
            exact (CoprimePowTwo 3 u.length (by decide : Odd 3)).symm
          have hX : d.Q ∣ d.P * n + d.B :=
            hcop.dvd_of_dvd_mul_left hX3
          have hlegal : Legal u n := ih.mpr hX
          have haff := AffineWordAct u n hlegal
          rw [hd] at haff
          have hdm : d.Q * 2 ∣ d.Q * (3 * WordAct u n + 1) := by
            rw [show d.Q * 2 = 2 * d.Q by ring]
            have heq : d.Q * (3 * WordAct u n + 1) =
                3 * (d.P * n + d.B) + d.Q := by
              calc
                d.Q * (3 * WordAct u n + 1) =
                    3 * (d.Q * WordAct u n) + d.Q := by ring
                _ = 3 * (d.P * n + d.B) + d.Q := by rw [haff]
            rw [heq]
            simpa only [mul_add, mul_assoc, add_assoc] using hdvd
          have h2 : 2 ∣ 3 * WordAct u n + 1 :=
            Nat.dvd_of_mul_dvd_mul_left hdpos hdm
          have hpar : WordAct u n % 2 = 1 := by omega
          exact ⟨hX, hpar⟩

    }
/-- Integer cylinder criterion: a word is legal at `n` exactly when its
denominator divides the numerator `P n + B`. -/
theorem CylinderCriterion (w : List Bool) (n : ℕ) :
    Legal w n ↔ (Affine w).Q ∣ (Affine w).P * n + (Affine w).B := by
  induction w using List.reverseRecOn generalizing n with
    | nil => { simp [Legal, Affine] }
    | append_singleton u b ih => { exact CylinderStep u b n (ih n) }

/-- The cylinder criterion expressed by the signed displacement from the input. -/
theorem DefectCylinderCriterion (w : List Bool) (n : ℕ) :
    Legal w n ↔ ((Affine w).Q : ℤ) ∣ Defect w n := by
  rw [CylinderCriterion, ← Int.natCast_dvd_natCast]
  have heq : Defect w n =
      ((Affine w).P * n + (Affine w).B : ℕ) - ((Affine w).Q : ℤ) * n := by
    simp only [Defect, Nat.cast_add, Nat.cast_mul]
    ring
  rw [heq]
  exact ⟨fun h => h.sub (dvd_mul_right _ _),
    fun h => by simpa using h.add (dvd_mul_right ((Affine w).Q : ℤ) (n : ℤ))⟩

/-- One legal copy factors its displacement and transports the remaining defect. -/
theorem DefectTransport (w : List Bool) (n : ℕ) (h : Legal w n) :
    Defect w n = ((Affine w).Q : ℤ) * ((WordAct w n : ℤ) - n) ∧
      Defect w (WordAct w n) = ((Affine w).P : ℤ) * ((WordAct w n : ℤ) - n) := by
  have haff : ((Affine w).Q : ℤ) * (WordAct w n : ℤ) =
      ((Affine w).P : ℤ) * n + (Affine w).B := by
    exact_mod_cast AffineWordAct w n h
  constructor
  · calc
      Defect w n = (((Affine w).P : ℤ) * n + (Affine w).B) -
          ((Affine w).Q : ℤ) * n := by unfold Defect; ring
      _ = ((Affine w).Q : ℤ) * ((WordAct w n : ℤ) - n) := by rw [← haff]; ring
  · calc
      Defect w (WordAct w n) = ((Affine w).P : ℤ) * (WordAct w n : ℤ) -
          (((Affine w).Q : ℤ) * (WordAct w n : ℤ) - (Affine w).B) := by
        unfold Defect
        ring
      _ = ((Affine w).P : ℤ) * ((WordAct w n : ℤ) - n) := by rw [haff]; ring

/-- An odd numerator cancels against every power of a word's dyadic denominator. -/
theorem DenominatorCancel (w : List Bool) (k : ℕ) (x : ℤ) :
    ((Affine w).Q : ℤ) ^ k ∣ ((Affine w).P : ℤ) * x ↔
      ((Affine w).Q : ℤ) ^ k ∣ x := by
  have hgcd : Int.gcd (((Affine w).Q : ℤ) ^ k) ((Affine w).P : ℤ) = 1 := by
    rw [AffineQ, Nat.cast_pow, ← pow_mul, Int.gcd_comm]
    exact IntGcdPowTwo (Affine w).P (w.length * k) (AffinePOdd w)
  exact ⟨fun h => Int.dvd_of_dvd_mul_right_of_gcd_one h hgcd,
    fun h => dvd_mul_of_dvd_right h _⟩

/-- A legal copy consumes one denominator factor from the exact repetition budget. -/
theorem RepetitionStep (w : List Bool) (n k : ℕ) (h : Legal w n) :
    ((Affine w).Q : ℤ) ^ (k + 1) ∣ Defect w n ↔
      ((Affine w).Q : ℤ) ^ k ∣ Defect w (WordAct w n) := by
  obtain ⟨hsource, hnext⟩ := DefectTransport w n h
  have hQ : ((Affine w).Q : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (AffineQPos w))
  rw [hsource, hnext, pow_succ, mul_comm (((Affine w).Q : ℤ) ^ k),
    mul_dvd_mul_iff_left hQ, DenominatorCancel]

/-- The first `k` copies are legal iff the `k`th denominator power divides the defect. -/
theorem RepeatedWordCriterion (w : List Bool) (n k : ℕ) :
    Legal (WordPow w k) n ↔ ((Affine w).Q : ℤ) ^ k ∣ Defect w n := by
  induction k generalizing n with
    | zero => { simp [WordPow, Legal] }
    | succ k ih => {
        rw [WordPow, LegalAppend, ih]
        constructor
        · rintro ⟨hlegal, hbudget⟩
          exact (RepetitionStep w n k hlegal).mpr hbudget
        · intro hbudget
          have hdiv : ((Affine w).Q : ℤ) ∣ Defect w n :=
            dvd_trans (by simpa only [pow_one] using
              (pow_dvd_pow ((Affine w).Q : ℤ) (show 1 ≤ k + 1 by omega))) hbudget
          have hlegal : Legal w n := (DefectCylinderCriterion w n).mpr hdiv
          exact ⟨hlegal, (RepetitionStep w n k hlegal).mp hbudget⟩

    }
/-- Consecutive odd inputs are controlled exactly by divisibility of `n + 1`. -/
theorem OddRunCriterion (n k : ℕ) :
    Legal (WordPow [true] k) n ↔ (2 : ℤ) ^ k ∣ (n : ℤ) + 1 := by
  simpa [Defect, Affine, AffineData.Compose, LetterData] using
    RepeatedWordCriterion [true] n k

/-- Each legal copy of `110` consumes three binary digits of `n + 5`. -/
theorem ThreeLetterCriterion (n k : ℕ) :
    Legal (WordPow [true, true, false] k) n ↔ (8 : ℤ) ^ k ∣ (n : ℤ) + 5 := by
  simpa [Defect, Affine, AffineData.Compose, LetterData] using
    RepeatedWordCriterion [true, true, false] n k

end GeneralizedCollatz.SwarmAttack
