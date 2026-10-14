-- SPDX-License-Identifier: CC-BY-4.0
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
Adjacent transport of one odd shortcut step, for multiplier `3` and offset `1`.

The shortcut sends an even state to half of itself and an odd state to
`(3 * n + 1) / 2`.  A parity word records which branch is taken.  Moving the
unique odd branch of a two-bit block across the adjacent even branch changes
the shortcut numerator by a pure power `2 ^ a * 3 ^ b`.  Concatenating the two
orders produces a numerator congruent to that power modulo `2 ^ h + 3 ^ r`.
A return would force the modulus to divide the power.  The modulus is greater
than `1` and coprime to `2` and to `3`, so neither concatenation returns.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.OneBit

/-- Shortcut for multiplier `3` and offset `1`. -/
def OneBitStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else (3 * n + 1) / 2

/-- The word uses the even or odd branch actually taken at every state. -/
def OneBitAgrees : List Bool → ℕ → Prop
  | [], _ => True
  | false :: bs, n => Even n ∧ OneBitAgrees bs (OneBitStep n)
  | true :: bs, n => ¬ Even n ∧ OneBitAgrees bs (OneBitStep n)

/-- Iteration of the shortcut along a parity word. -/
def OneBitRun : List Bool → ℕ → ℕ
  | [], n => n
  | _ :: bs, n => OneBitRun bs (OneBitStep n)

/-- Number of odd branches in a parity word. -/
def OneBitOddCount : List Bool → ℕ
  | [] => 0
  | false :: bs => OneBitOddCount bs
  | true :: bs => OneBitOddCount bs + 1

/-- Numerator of the shortcut affine form, accumulated from the tail. -/
def OneBitNumerator : List Bool → ℕ
  | [] => 0
  | false :: bs => 2 * OneBitNumerator bs
  | true :: bs => 3 ^ OneBitOddCount bs + 2 * OneBitNumerator bs

/-- Even branch, then the adjacent odd branch, with surroundings `p` and `s`. -/
def OneBitEvenThenOdd (p s : List Bool) : List Bool :=
  p ++ [false, true] ++ s

/-- Odd branch, then the adjacent even branch, with the same surroundings. -/
def OneBitOddThenEven (p s : List Bool) : List Bool :=
  p ++ [true, false] ++ s

/-- Common length of the two adjacent words. -/
def OneBitHalfLength (p s : List Bool) : ℕ :=
  p.length + 2 + s.length

/-- Common odd-branch count of the two adjacent words. -/
def OneBitHalfOdd (p s : List Bool) : ℕ :=
  OneBitOddCount p + 1 + OneBitOddCount s

/-- Modulus `2 ^ h + 3 ^ r` attached to one adjacent word. -/
def OneBitModulus (p s : List Bool) : ℕ :=
  2 ^ OneBitHalfLength p s + 3 ^ OneBitHalfOdd p s

/-- Power of `2` and `3` by which the two adjacent numerators differ, scaled. -/
def OneBitMonomial (p s : List Bool) : ℕ :=
  2 ^ p.length * 3 ^ (OneBitHalfOdd p s + OneBitOddCount s)

/-- A word has at most one odd branch per letter. -/
theorem OneBitOddCountLeLength (w : List Bool) : OneBitOddCount w ≤ w.length := by
  induction w with
  | nil => {
      simp [OneBitOddCount]
    }
  | cons b bs ih => {
      cases b with
      | false => {
          simp only [OneBitOddCount, List.length_cons]
          omega
        }
      | true => {
          simp only [OneBitOddCount, List.length_cons]
          omega
        }
    }

/-- The all-odd word bounds every numerator of the same length. -/
theorem OneBitNumeratorBound (w : List Bool) :
    OneBitNumerator w + 2 ^ w.length ≤ 3 ^ w.length := by
  induction w with
  | nil => {
      simp [OneBitNumerator]
    }
  | cons b bs ih => {
      cases b with
      | false => {
          simp only [OneBitNumerator, List.length_cons, Nat.pow_succ]
          omega
        }
      | true => {
          have hpower : 3 ^ OneBitOddCount bs ≤ 3 ^ bs.length :=
            Nat.pow_le_pow_right (by decide : (3 : ℕ) > 0) (OneBitOddCountLeLength bs)
          simp only [OneBitNumerator, List.length_cons, Nat.pow_succ]
          omega
        }
    }

/-- Odd-branch count adds under concatenation. -/
theorem OneBitOddCountAppend (u v : List Bool) :
    OneBitOddCount (u ++ v) = OneBitOddCount u + OneBitOddCount v := by
  induction u with
  | nil => {
      simp [OneBitOddCount]
  }
  | cons b bs ih => {
      cases b with
      | false => {
          simp [OneBitOddCount, ih]
      }
      | true => {
          simp only [List.cons_append, OneBitOddCount, ih]
          rw [Nat.add_right_comm]
      }
  }

/-- The numerator of a concatenation is the tail-weighted affine combination. -/
theorem OneBitNumeratorAppend (u v : List Bool) :
    OneBitNumerator (u ++ v) =
      3 ^ OneBitOddCount v * OneBitNumerator u +
        2 ^ u.length * OneBitNumerator v := by
  induction u with
  | nil => {
      simp [OneBitNumerator]
  }
  | cons b bs ih => {
      cases b with
      | false => {
          rw [List.cons_append]
          simp only [OneBitNumerator]
          rw [List.length_cons, ih]
          calc
            2 * (3 ^ OneBitOddCount v * OneBitNumerator bs +
                2 ^ bs.length * OneBitNumerator v)
              = 2 * (3 ^ OneBitOddCount v * OneBitNumerator bs) +
                  2 * (2 ^ bs.length * OneBitNumerator v) := by
                    rw [Nat.mul_add]
            _ = 3 ^ OneBitOddCount v * (2 * OneBitNumerator bs) +
                  2 ^ (bs.length + 1) * OneBitNumerator v := by
                  rw [Nat.mul_left_comm 2 (3 ^ OneBitOddCount v)
                    (OneBitNumerator bs)]
                  have hpow :
                      2 * (2 ^ bs.length * OneBitNumerator v) =
                        2 ^ (bs.length + 1) * OneBitNumerator v := by
                    calc
                      2 * (2 ^ bs.length * OneBitNumerator v)
                        = (2 * 2 ^ bs.length) * OneBitNumerator v := by
                            rw [← Nat.mul_assoc]
                      _ = (2 ^ bs.length * 2) * OneBitNumerator v := by
                            rw [Nat.mul_comm 2 (2 ^ bs.length)]
                      _ = 2 ^ (bs.length + 1) * OneBitNumerator v := by
                            rw [← Nat.pow_succ]
                  rw [hpow]
      }
      | true => {
          rw [List.cons_append]
          simp only [OneBitNumerator]
          rw [List.length_cons, OneBitOddCountAppend, ih]
          calc
            3 ^ (OneBitOddCount bs + OneBitOddCount v) +
                2 * (3 ^ OneBitOddCount v * OneBitNumerator bs +
                  2 ^ bs.length * OneBitNumerator v)
              = 3 ^ (OneBitOddCount bs + OneBitOddCount v) +
                  2 * (3 ^ OneBitOddCount v * OneBitNumerator bs) +
                  2 * (2 ^ bs.length * OneBitNumerator v) := by
                    rw [Nat.mul_add, Nat.add_assoc]
            _ = 3 ^ OneBitOddCount v * 3 ^ OneBitOddCount bs +
                  3 ^ OneBitOddCount v * (2 * OneBitNumerator bs) +
                  2 ^ (bs.length + 1) * OneBitNumerator v := by
                  rw [Nat.pow_add, Nat.mul_comm (3 ^ OneBitOddCount bs)
                    (3 ^ OneBitOddCount v),
                    Nat.mul_left_comm 2 (3 ^ OneBitOddCount v)
                      (OneBitNumerator bs)]
                  have hpow :
                      2 * (2 ^ bs.length * OneBitNumerator v) =
                        2 ^ (bs.length + 1) * OneBitNumerator v := by
                    calc
                      2 * (2 ^ bs.length * OneBitNumerator v)
                        = (2 * 2 ^ bs.length) * OneBitNumerator v := by
                            rw [← Nat.mul_assoc]
                      _ = (2 ^ bs.length * 2) * OneBitNumerator v := by
                            rw [Nat.mul_comm 2 (2 ^ bs.length)]
                      _ = 2 ^ (bs.length + 1) * OneBitNumerator v := by
                            rw [← Nat.pow_succ]
                  rw [hpow]
            _ = 3 ^ OneBitOddCount v *
                    (3 ^ OneBitOddCount bs + 2 * OneBitNumerator bs) +
                  2 ^ (bs.length + 1) * OneBitNumerator v := by
                  rw [← Nat.mul_add]
      }
  }

/-- An agreeing run satisfies the shortcut affine identity. -/
theorem OneBitRunAffine (w : List Bool) (n : ℕ) (h : OneBitAgrees w n) :
    2 ^ w.length * OneBitRun w n =
      3 ^ OneBitOddCount w * n + OneBitNumerator w := by
  induction w generalizing n with
  | nil => {
      simp [OneBitRun, OneBitOddCount, OneBitNumerator]
  }
  | cons b bs ih => {
      cases b with
      | false => {
          rcases h with ⟨heven, htail⟩
          have ihv := ih (OneBitStep n) htail
          have hstep : OneBitStep n = n / 2 := by
            rw [OneBitStep, if_pos heven]
          have hdiv : 2 * (n / 2) = n :=
            Nat.two_mul_div_two_of_even heven
          unfold OneBitRun OneBitOddCount OneBitNumerator
          rw [List.length_cons]
          calc
            2 ^ (bs.length + 1) * OneBitRun bs (OneBitStep n)
              = (2 ^ bs.length * 2) * OneBitRun bs (OneBitStep n) := by
                  rw [Nat.pow_succ]
            _ = 2 * (2 ^ bs.length * OneBitRun bs (OneBitStep n)) := by
                  rw [Nat.mul_comm (2 ^ bs.length) 2, Nat.mul_assoc]
            _ = 2 * (3 ^ OneBitOddCount bs * OneBitStep n +
                  OneBitNumerator bs) := by
                  rw [ihv]
            _ = 2 * (3 ^ OneBitOddCount bs * (n / 2) +
                  OneBitNumerator bs) := by
                  rw [hstep]
            _ = 2 * (3 ^ OneBitOddCount bs * (n / 2)) +
                  2 * OneBitNumerator bs := by
                  rw [Nat.mul_add]
            _ = 3 ^ OneBitOddCount bs * (2 * (n / 2)) +
                  2 * OneBitNumerator bs := by
                  rw [Nat.mul_left_comm 2 (3 ^ OneBitOddCount bs) (n / 2)]
            _ = 3 ^ OneBitOddCount bs * n + 2 * OneBitNumerator bs := by
                  rw [hdiv]
      }
      | true => {
          rcases h with ⟨hodd, htail⟩
          have ihv := ih (OneBitStep n) htail
          have hstep : OneBitStep n = (3 * n + 1) / 2 := by
            rw [OneBitStep, if_neg hodd]
          have hthree : Odd (3 * n) :=
            Odd.mul (show Odd 3 from by decide)
              ((Nat.not_even_iff_odd).mp hodd)
          have hevenSum : Even (3 * n + 1) := by
            rw [Nat.even_add_one, Nat.not_even_iff_odd]
            exact hthree
          have hdiv : 2 * ((3 * n + 1) / 2) = 3 * n + 1 :=
            Nat.two_mul_div_two_of_even hevenSum
          unfold OneBitRun OneBitOddCount OneBitNumerator
          rw [List.length_cons]
          calc
            2 ^ (bs.length + 1) * OneBitRun bs (OneBitStep n)
              = (2 ^ bs.length * 2) * OneBitRun bs (OneBitStep n) := by
                  rw [Nat.pow_succ]
            _ = 2 * (2 ^ bs.length * OneBitRun bs (OneBitStep n)) := by
                  rw [Nat.mul_comm (2 ^ bs.length) 2, Nat.mul_assoc]
            _ = 2 * (3 ^ OneBitOddCount bs * OneBitStep n +
                  OneBitNumerator bs) := by
                  rw [ihv]
            _ = 2 * (3 ^ OneBitOddCount bs * ((3 * n + 1) / 2) +
                  OneBitNumerator bs) := by
                  rw [hstep]
            _ = 2 * (3 ^ OneBitOddCount bs * ((3 * n + 1) / 2)) +
                  2 * OneBitNumerator bs := by
                  rw [Nat.mul_add]
            _ = 3 ^ OneBitOddCount bs * (2 * ((3 * n + 1) / 2)) +
                  2 * OneBitNumerator bs := by
                  rw [Nat.mul_left_comm 2 (3 ^ OneBitOddCount bs)
                    ((3 * n + 1) / 2)]
            _ = 3 ^ OneBitOddCount bs * (3 * n + 1) +
                  2 * OneBitNumerator bs := by
                  rw [hdiv]
            _ = 3 ^ OneBitOddCount bs * (3 * n) + 3 ^ OneBitOddCount bs +
                  2 * OneBitNumerator bs := by
                  rw [Nat.mul_add, Nat.mul_one]
            _ = 3 ^ (OneBitOddCount bs + 1) * n +
                  (3 ^ OneBitOddCount bs + 2 * OneBitNumerator bs) := by
                  rw [← Nat.mul_assoc, ← Nat.pow_succ, Nat.add_assoc]
      }
  }

/-- The even-then-odd block has one odd branch and numerator `2`. -/
theorem OneBitEvenOddBlock :
    OneBitOddCount [false, true] = 1 ∧ OneBitNumerator [false, true] = 2 := by
  decide

/-- The odd-then-even block has one odd branch and numerator `1`. -/
theorem OneBitOddEvenBlock :
    OneBitOddCount [true, false] = 1 ∧ OneBitNumerator [true, false] = 1 := by
  decide

/-- Both adjacent words have length `h = |p| + 2 + |s|`. -/
theorem OneBitEvenThenOddLength (p s : List Bool) :
    (OneBitEvenThenOdd p s).length = OneBitHalfLength p s := by
  unfold OneBitEvenThenOdd OneBitHalfLength
  rw [List.length_append, List.length_append, List.length_cons,
    List.length_cons, List.length_nil]

/-- Both adjacent words have length `h = |p| + 2 + |s|`. -/
theorem OneBitOddThenEvenLength (p s : List Bool) :
    (OneBitOddThenEven p s).length = OneBitHalfLength p s := by
  unfold OneBitOddThenEven OneBitHalfLength
  rw [List.length_append, List.length_append, List.length_cons,
    List.length_cons, List.length_nil]

/-- Both adjacent words have odd-branch count `r = ν(p) + 1 + ν(s)`. -/
theorem OneBitEvenThenOddCount (p s : List Bool) :
    OneBitOddCount (OneBitEvenThenOdd p s) = OneBitHalfOdd p s := by
  unfold OneBitEvenThenOdd OneBitHalfOdd
  rw [OneBitOddCountAppend, OneBitOddCountAppend, OneBitEvenOddBlock.1]

/-- Both adjacent words have odd-branch count `r = ν(p) + 1 + ν(s)`. -/
theorem OneBitOddThenEvenCount (p s : List Bool) :
    OneBitOddCount (OneBitOddThenEven p s) = OneBitHalfOdd p s := by
  unfold OneBitOddThenEven OneBitHalfOdd
  rw [OneBitOddCountAppend, OneBitOddCountAppend, OneBitOddEvenBlock.1]

/-- Transporting the odd branch across the even branch adds `2 ^ |p| * 3 ^ ν(s)`. -/
theorem OneBitTransportGap (p s : List Bool) :
    OneBitNumerator (OneBitEvenThenOdd p s) =
      OneBitNumerator (OneBitOddThenEven p s) +
        2 ^ p.length * 3 ^ OneBitOddCount s := by
  unfold OneBitEvenThenOdd OneBitOddThenEven
  have hL : OneBitNumerator (p ++ [false, true]) =
      3 * OneBitNumerator p + 2 ^ p.length * 2 := by
    rw [OneBitNumeratorAppend, OneBitEvenOddBlock.1, OneBitEvenOddBlock.2,
      Nat.pow_one]
  have hR : OneBitNumerator (p ++ [true, false]) =
      3 * OneBitNumerator p + 2 ^ p.length := by
    rw [OneBitNumeratorAppend, OneBitOddEvenBlock.1, OneBitOddEvenBlock.2,
      Nat.pow_one, Nat.mul_one]
  have hpair : OneBitNumerator (p ++ [false, true]) =
      OneBitNumerator (p ++ [true, false]) + 2 ^ p.length := by
    rw [hL, hR, Nat.mul_two, Nat.add_assoc]
  have hlenL : (p ++ [false, true]).length = p.length + 2 := by
    rw [List.length_append, List.length_cons, List.length_cons, List.length_nil]
  have hlenR : (p ++ [true, false]).length = p.length + 2 := by
    rw [List.length_append, List.length_cons, List.length_cons, List.length_nil]
  rw [OneBitNumeratorAppend (p ++ [false, true]) s,
    OneBitNumeratorAppend (p ++ [true, false]) s, hpair, hlenL, hlenR]
  calc
    3 ^ OneBitOddCount s *
          (OneBitNumerator (p ++ [true, false]) + 2 ^ p.length) +
        2 ^ (p.length + 2) * OneBitNumerator s
      = 3 ^ OneBitOddCount s * OneBitNumerator (p ++ [true, false]) +
          3 ^ OneBitOddCount s * 2 ^ p.length +
          2 ^ (p.length + 2) * OneBitNumerator s := by
            rw [Nat.mul_add, Nat.add_assoc]
    _ = 3 ^ OneBitOddCount s * OneBitNumerator (p ++ [true, false]) +
          2 ^ (p.length + 2) * OneBitNumerator s +
          2 ^ p.length * 3 ^ OneBitOddCount s := by
          rw [Nat.add_assoc, Nat.add_comm
            (3 ^ OneBitOddCount s * 2 ^ p.length)
            (2 ^ (p.length + 2) * OneBitNumerator s), ← Nat.add_assoc,
            Nat.mul_comm (3 ^ OneBitOddCount s) (2 ^ p.length)]

/-- Even-then-odd followed by odd-then-even leaves remainder `μ`. -/
theorem OneBitEvenFirstResidue (p s : List Bool) :
    OneBitNumerator (OneBitEvenThenOdd p s ++ OneBitOddThenEven p s) =
      OneBitModulus p s * OneBitNumerator (OneBitOddThenEven p s) +
        OneBitMonomial p s := by
  rw [OneBitNumeratorAppend, OneBitOddThenEvenCount, OneBitEvenThenOddLength,
    OneBitTransportGap, OneBitModulus, OneBitMonomial]
  calc
    3 ^ OneBitHalfOdd p s *
          (OneBitNumerator (OneBitOddThenEven p s) +
            2 ^ p.length * 3 ^ OneBitOddCount s) +
        2 ^ OneBitHalfLength p s * OneBitNumerator (OneBitOddThenEven p s)
      = 3 ^ OneBitHalfOdd p s * OneBitNumerator (OneBitOddThenEven p s) +
          3 ^ OneBitHalfOdd p s * (2 ^ p.length * 3 ^ OneBitOddCount s) +
          2 ^ OneBitHalfLength p s *
            OneBitNumerator (OneBitOddThenEven p s) := by
            rw [Nat.mul_add, Nat.add_assoc]
    _ = (3 ^ OneBitHalfOdd p s + 2 ^ OneBitHalfLength p s) *
          OneBitNumerator (OneBitOddThenEven p s) +
          3 ^ OneBitHalfOdd p s * (2 ^ p.length * 3 ^ OneBitOddCount s) := by
          rw [Nat.add_assoc, Nat.add_comm
            (3 ^ OneBitHalfOdd p s * (2 ^ p.length * 3 ^ OneBitOddCount s))
            (2 ^ OneBitHalfLength p s *
              OneBitNumerator (OneBitOddThenEven p s)),
            ← Nat.add_assoc, ← Nat.add_mul]
    _ = (2 ^ OneBitHalfLength p s + 3 ^ OneBitHalfOdd p s) *
          OneBitNumerator (OneBitOddThenEven p s) +
          2 ^ p.length * 3 ^ (OneBitHalfOdd p s + OneBitOddCount s) := by
          rw [Nat.add_comm (3 ^ OneBitHalfOdd p s) (2 ^ OneBitHalfLength p s),
            Nat.mul_left_comm (3 ^ OneBitHalfOdd p s) (2 ^ p.length)
              (3 ^ OneBitOddCount s), ← Nat.pow_add]

/-- Odd-then-even followed by even-then-odd leaves the opposite remainder. -/
theorem OneBitOddFirstResidue (p s : List Bool) :
    OneBitNumerator (OneBitOddThenEven p s ++ OneBitEvenThenOdd p s) +
        OneBitMonomial p s =
      OneBitModulus p s * OneBitNumerator (OneBitEvenThenOdd p s) := by
  rw [OneBitNumeratorAppend, OneBitEvenThenOddCount, OneBitOddThenEvenLength,
    OneBitTransportGap, OneBitModulus, OneBitMonomial]
  calc
    3 ^ OneBitHalfOdd p s * OneBitNumerator (OneBitOddThenEven p s) +
          2 ^ OneBitHalfLength p s *
            (OneBitNumerator (OneBitOddThenEven p s) +
              2 ^ p.length * 3 ^ OneBitOddCount s) +
        2 ^ p.length * 3 ^ (OneBitHalfOdd p s + OneBitOddCount s)
      = 3 ^ OneBitHalfOdd p s * OneBitNumerator (OneBitOddThenEven p s) +
          2 ^ OneBitHalfLength p s *
            OneBitNumerator (OneBitOddThenEven p s) +
          2 ^ OneBitHalfLength p s * (2 ^ p.length * 3 ^ OneBitOddCount s) +
          2 ^ p.length * 3 ^ (OneBitHalfOdd p s + OneBitOddCount s) := by
            simp only [Nat.mul_add, Nat.add_assoc]
    _ = (2 ^ OneBitHalfLength p s + 3 ^ OneBitHalfOdd p s) *
          OneBitNumerator (OneBitOddThenEven p s) +
          (2 ^ OneBitHalfLength p s * (2 ^ p.length * 3 ^ OneBitOddCount s) +
            3 ^ OneBitHalfOdd p s *
              (2 ^ p.length * 3 ^ OneBitOddCount s)) := by
          rw [Nat.add_comm (3 ^ OneBitHalfOdd p s *
              OneBitNumerator (OneBitOddThenEven p s))
            (2 ^ OneBitHalfLength p s *
              OneBitNumerator (OneBitOddThenEven p s)),
            ← Nat.add_mul, Nat.add_assoc, Nat.pow_add,
            ← Nat.mul_left_comm (3 ^ OneBitHalfOdd p s) (2 ^ p.length)
              (3 ^ OneBitOddCount s)]
    _ = (2 ^ OneBitHalfLength p s + 3 ^ OneBitHalfOdd p s) *
          (OneBitNumerator (OneBitOddThenEven p s) +
            2 ^ p.length * 3 ^ OneBitOddCount s) := by
          rw [← Nat.add_mul, ← Nat.mul_add]

/-- Difference of squares in the integers. -/
theorem SquareDifference (a b : ℤ) : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by
  have ha : a ^ 2 = a * a := by
    rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
  have hb : b ^ 2 = b * b := by
    rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]
  have expand : (a - b) * (a + b) = a * a - b * b := by
    calc
      (a - b) * (a + b) = a * (a + b) - b * (a + b) := by
        rw [Int.sub_mul]
      _ = (a * a + a * b) - (b * a + b * b) := by
        rw [Int.mul_add, Int.mul_add]
      _ = (a * a + a * b) - (a * b + b * b) := by
        rw [Int.mul_comm b a]
      _ = a * a + a * b - a * b - b * b := by
        rw [← Int.sub_sub]
      _ = a * a - b * b := by
        rw [Int.add_sub_cancel]
  rw [← ha, ← hb] at expand
  exact expand.symm

/-- A return of a doubled word is divisible by `2 ^ h + 3 ^ r`. -/
theorem OneBitClosedDivides (w : List Bool) (x h r : ℕ)
    (hagree : OneBitAgrees w x) (hret : OneBitRun w x = x)
    (hlen : w.length = 2 * h) (hodd : OneBitOddCount w = 2 * r) :
    2 ^ h + 3 ^ r ∣ OneBitNumerator w := by
  have ident := OneBitRunAffine w x hagree
  rw [hret, hlen, hodd] at ident
  have identZ :
      ((2 ^ (2 * h) : ℕ) : ℤ) * (x : ℤ) =
        ((3 ^ (2 * r) : ℕ) : ℤ) * (x : ℤ) + (OneBitNumerator w : ℤ) := by
    have hcast := congrArg (fun t : ℕ => (t : ℤ)) ident
    rw [Int.natCast_mul, Int.natCast_add, Int.natCast_mul] at hcast
    exact hcast
  have subEq :
      (((2 ^ (2 * h) : ℕ) : ℤ) - ((3 ^ (2 * r) : ℕ) : ℤ)) * (x : ℤ) =
        (OneBitNumerator w : ℤ) := by
    calc
      (((2 ^ (2 * h) : ℕ) : ℤ) - ((3 ^ (2 * r) : ℕ) : ℤ)) * (x : ℤ)
        = ((2 ^ (2 * h) : ℕ) : ℤ) * (x : ℤ) -
            ((3 ^ (2 * r) : ℕ) : ℤ) * (x : ℤ) := by
              rw [Int.sub_mul]
      _ = (((3 ^ (2 * r) : ℕ) : ℤ) * (x : ℤ) + (OneBitNumerator w : ℤ)) -
            ((3 ^ (2 * r) : ℕ) : ℤ) * (x : ℤ) := by
              rw [identZ]
      _ = (OneBitNumerator w : ℤ) := by omega
  have eqTwo : 2 ^ (2 * h) = (2 ^ h) ^ 2 := by
    rw [Nat.mul_comm 2 h, Nat.pow_mul]
  have eqThree : 3 ^ (2 * r) = (3 ^ r) ^ 2 := by
    rw [Nat.mul_comm 2 r, Nat.pow_mul]
  -- Cast each square separately so the two bases are not rewritten together.
  have castTwo : ((2 ^ (2 * h) : ℕ) : ℤ) = ((2 ^ h : ℕ) : ℤ) ^ 2 := by
    rw [eqTwo, Int.natCast_pow]
  have castThree : ((3 ^ (2 * r) : ℕ) : ℤ) = ((3 ^ r : ℕ) : ℤ) ^ 2 := by
    rw [eqThree, Int.natCast_pow]
  rw [castTwo, castThree, SquareDifference, ← Int.natCast_add] at subEq
  refine Int.natCast_dvd_natCast.mp ?_
  refine ⟨(((2 ^ h : ℕ) : ℤ) - ((3 ^ r : ℕ) : ℤ)) * (x : ℤ), ?_⟩
  symm
  calc
    ((2 ^ h + 3 ^ r : ℕ) : ℤ) *
        ((((2 ^ h : ℕ) : ℤ) - ((3 ^ r : ℕ) : ℤ)) * (x : ℤ))
      = ((((2 ^ h : ℕ) : ℤ) - ((3 ^ r : ℕ) : ℤ)) *
          ((2 ^ h + 3 ^ r : ℕ) : ℤ)) * (x : ℤ) := by
            rw [Int.mul_left_comm, ← Int.mul_assoc]
    _ = (OneBitNumerator w : ℤ) := subEq

/-- For positive `h`, the modulus `2 ^ h + 3 ^ r` is coprime to `2`. -/
theorem OneBitModulusCoprimeTwo (h r : ℕ) (hh : 1 ≤ h) :
    Nat.Coprime (2 ^ h + 3 ^ r) 2 := by
  rw [Nat.coprime_two_right, ← Nat.not_even_iff_odd, Nat.even_add]
  intro hiff
  have heTwo : Even (2 ^ h) := by
    rw [Nat.even_pow]
    exact ⟨by decide, by omega⟩
  have hnot : ¬ Even (3 ^ r) := by
    intro heThree
    have heBase : Even 3 := (Nat.even_pow.mp heThree).1
    exact (by decide : ¬ Even 3) heBase
  exact hnot (hiff.mp heTwo)

/-- For positive `h` and `r`, the modulus `2 ^ h + 3 ^ r` is coprime to `3`. -/
theorem OneBitModulusCoprimeThree (h r : ℕ) (hh : 1 ≤ h) (hr : 1 ≤ r) :
    Nat.Coprime (2 ^ h + 3 ^ r) 3 := by
  have hd : 3 ∣ 3 ^ r := Nat.pow_dvd_pow 3 hr
  rw [Nat.add_comm, Nat.add_coprime_iff_right hd, Nat.coprime_pow_left_iff hh]
  decide

/-- A factor coprime to the base divides a power of the base only if it divides `1`. -/
theorem OneBitCoprimeDvdPow (M k n : ℕ) (hcop : Nat.Coprime M k) :
    M ∣ k ^ n → M ∣ 1 := by
  induction n with
  | zero => {
      intro hdvd
      simpa [Nat.pow_zero] using hdvd
  }
  | succ n ih => {
      intro hdvd
      rw [Nat.pow_succ'] at hdvd
      exact ih ((Nat.Coprime.dvd_mul_left hcop).mp hdvd)
  }

/-- A factor coprime to `2` and to `3` divides a product of their powers only if it divides `1`. -/
theorem OneBitCoprimeDvdTwoThree (M a b : ℕ)
    (h2 : Nat.Coprime M 2) (h3 : Nat.Coprime M 3) :
    M ∣ 2 ^ a * 3 ^ b → M ∣ 1 := by
  induction a with
  | zero => {
      intro hdvd
      have hthree : M ∣ 3 ^ b := by
        simpa [Nat.pow_zero, Nat.one_mul] using hdvd
      exact OneBitCoprimeDvdPow M 3 b h3 hthree
  }
  | succ a ih => {
      intro hdvd
      have hform : 2 ^ (a + 1) * 3 ^ b = 2 ^ a * 3 ^ b * 2 := by
        calc
          2 ^ (a + 1) * 3 ^ b = (2 ^ a * 2) * 3 ^ b := by
            rw [Nat.pow_succ]
          _ = 2 ^ a * (2 * 3 ^ b) := by
            rw [Nat.mul_assoc]
          _ = 2 ^ a * (3 ^ b * 2) := by
            rw [Nat.mul_comm 2 (3 ^ b)]
          _ = 2 ^ a * 3 ^ b * 2 := by
            rw [← Nat.mul_assoc]
      rw [hform] at hdvd
      exact ih ((Nat.Coprime.dvd_mul_right h2).mp hdvd)
  }

/-- The adjacent modulus does not divide any number of the form `2 ^ a * 3 ^ b`. -/
theorem OneBitModulusMiss (h r a b : ℕ) (hh : 1 ≤ h) (hr : 1 ≤ r) :
    ¬ (2 ^ h + 3 ^ r) ∣ 2 ^ a * 3 ^ b := by
  intro hdvd
  have hone : 2 ^ h + 3 ^ r = 1 := by
    refine Nat.dvd_one.mp ?_
    exact OneBitCoprimeDvdTwoThree (2 ^ h + 3 ^ r) a b
      (OneBitModulusCoprimeTwo h r hh)
      (OneBitModulusCoprimeThree h r hh hr) hdvd
  have htwo : 2 ≤ 2 ^ h := by
    have hpow : 2 ^ 1 ≤ 2 ^ h :=
      Nat.pow_le_pow_right (by decide : (2 : ℕ) > 0) hh
    simpa using hpow
  have hthree : 3 ≤ 3 ^ r := by
    have hpow : 3 ^ 1 ≤ 3 ^ r :=
      Nat.pow_le_pow_right (by decide : (3 : ℕ) > 0) hr
    simpa using hpow
  omega

/-- Every adjacent modulus is at least `7`. -/
theorem OneBitModulusAtLeastSeven (p s : List Bool) : 7 ≤ OneBitModulus p s := by
  unfold OneBitModulus
  have hh : 2 ≤ OneBitHalfLength p s := by
    unfold OneBitHalfLength
    omega
  have hr : 1 ≤ OneBitHalfOdd p s := by
    unfold OneBitHalfOdd
    omega
  have htwo : 4 ≤ 2 ^ OneBitHalfLength p s := by
    have hpow : 2 ^ 2 ≤ 2 ^ OneBitHalfLength p s :=
      Nat.pow_le_pow_right (by decide : (2 : ℕ) > 0) hh
    have hfour : (2 : ℕ) ^ 2 = 4 := by decide
    rwa [hfour] at hpow
  have hthree : 3 ≤ 3 ^ OneBitHalfOdd p s := by
    have hpow : 3 ^ 1 ≤ 3 ^ OneBitHalfOdd p s :=
      Nat.pow_le_pow_right (by decide : (3 : ℕ) > 0) hr
    have hone : (3 : ℕ) ^ 1 = 3 := by decide
    rwa [hone] at hpow
  omega

/-- Transport of one adjacent odd step leaves a non-integral residue and does not return. -/
theorem OneBitAdjacentTransport (p s : List Bool) (x : ℕ) :
    OneBitNumerator (OneBitEvenThenOdd p s ++ OneBitOddThenEven p s) =
      OneBitModulus p s * OneBitNumerator (OneBitOddThenEven p s) +
        OneBitMonomial p s ∧
    OneBitNumerator (OneBitOddThenEven p s ++ OneBitEvenThenOdd p s) +
        OneBitMonomial p s =
      OneBitModulus p s * OneBitNumerator (OneBitEvenThenOdd p s) ∧
    7 ≤ OneBitModulus p s ∧
    ¬ OneBitModulus p s ∣ OneBitMonomial p s ∧
    ¬ (OneBitAgrees (OneBitEvenThenOdd p s ++ OneBitOddThenEven p s) x ∧
        OneBitRun (OneBitEvenThenOdd p s ++ OneBitOddThenEven p s) x = x) ∧
    ¬ (OneBitAgrees (OneBitOddThenEven p s ++ OneBitEvenThenOdd p s) x ∧
        OneBitRun (OneBitOddThenEven p s ++ OneBitEvenThenOdd p s) x = x) := by
  refine ⟨OneBitEvenFirstResidue p s, OneBitOddFirstResidue p s,
    OneBitModulusAtLeastSeven p s, ?_, ?_, ?_⟩
  · have hh : 1 ≤ OneBitHalfLength p s := by
      unfold OneBitHalfLength
      omega
    have hr : 1 ≤ OneBitHalfOdd p s := by
      unfold OneBitHalfOdd
      omega
    exact OneBitModulusMiss (OneBitHalfLength p s) (OneBitHalfOdd p s)
      p.length (OneBitHalfOdd p s + OneBitOddCount s) hh hr
  · intro hclosed
    have hlen : (OneBitEvenThenOdd p s ++ OneBitOddThenEven p s).length =
        2 * OneBitHalfLength p s := by
      rw [List.length_append, OneBitEvenThenOddLength, OneBitOddThenEvenLength,
        ← Nat.two_mul]
    have hodd : OneBitOddCount
        (OneBitEvenThenOdd p s ++ OneBitOddThenEven p s) =
        2 * OneBitHalfOdd p s := by
      rw [OneBitOddCountAppend, OneBitEvenThenOddCount, OneBitOddThenEvenCount,
        ← Nat.two_mul]
    have hdiv := OneBitClosedDivides
      (OneBitEvenThenOdd p s ++ OneBitOddThenEven p s) x
      (OneBitHalfLength p s) (OneBitHalfOdd p s) hclosed.1 hclosed.2 hlen hodd
    rw [OneBitEvenFirstResidue] at hdiv
    have hmul : OneBitModulus p s ∣
        OneBitModulus p s * OneBitNumerator (OneBitOddThenEven p s) :=
      Nat.dvd_mul_right _ _
    have hmono := (Nat.dvd_add_iff_right hmul).mpr hdiv
    have hh : 1 ≤ OneBitHalfLength p s := by
      unfold OneBitHalfLength
      omega
    have hr : 1 ≤ OneBitHalfOdd p s := by
      unfold OneBitHalfOdd
      omega
    exact OneBitModulusMiss (OneBitHalfLength p s) (OneBitHalfOdd p s)
      p.length (OneBitHalfOdd p s + OneBitOddCount s) hh hr hmono
  · intro hclosed
    have hlen : (OneBitOddThenEven p s ++ OneBitEvenThenOdd p s).length =
        2 * OneBitHalfLength p s := by
      rw [List.length_append, OneBitOddThenEvenLength, OneBitEvenThenOddLength,
        ← Nat.two_mul]
    have hodd : OneBitOddCount
        (OneBitOddThenEven p s ++ OneBitEvenThenOdd p s) =
        2 * OneBitHalfOdd p s := by
      rw [OneBitOddCountAppend, OneBitOddThenEvenCount, OneBitEvenThenOddCount,
        ← Nat.two_mul]
    have hdiv := OneBitClosedDivides
      (OneBitOddThenEven p s ++ OneBitEvenThenOdd p s) x
      (OneBitHalfLength p s) (OneBitHalfOdd p s) hclosed.1 hclosed.2 hlen hodd
    have hsum : OneBitModulus p s ∣
        OneBitNumerator (OneBitOddThenEven p s ++ OneBitEvenThenOdd p s) +
          OneBitMonomial p s := by
      rw [OneBitOddFirstResidue]
      exact Nat.dvd_mul_right _ _
    have hmono := (Nat.dvd_add_iff_right hdiv).mpr hsum
    have hh : 1 ≤ OneBitHalfLength p s := by
      unfold OneBitHalfLength
      omega
    have hr : 1 ≤ OneBitHalfOdd p s := by
      unfold OneBitHalfOdd
      omega
    exact OneBitModulusMiss (OneBitHalfLength p s) (OneBitHalfOdd p s)
      p.length (OneBitHalfOdd p s + OneBitOddCount s) hh hr hmono

/-- Empty surroundings give the residue `10 = 7 * 1 + 3` and `11 + 3 = 7 * 2`. -/
theorem OneBitEmptyResidue :
    OneBitHalfLength [] [] = 2 ∧
    OneBitHalfOdd [] [] = 1 ∧
    OneBitModulus [] [] = 7 ∧
    OneBitMonomial [] [] = 3 ∧
    OneBitNumerator (OneBitOddThenEven [] []) = 1 ∧
    OneBitNumerator (OneBitEvenThenOdd [] []) = 2 ∧
    OneBitNumerator (OneBitEvenThenOdd [] [] ++ OneBitOddThenEven [] []) =
      10 ∧
    OneBitNumerator (OneBitOddThenEven [] [] ++ OneBitEvenThenOdd [] []) =
      11 ∧
    10 = 7 * 1 + 3 ∧
    11 + 3 = 7 * 2 := by
  decide

/-- Surroundings `p = 1`, `s = 0` give residues `143` and `157` modulo `25`. -/
theorem OneBitNonemptyResidue :
    OneBitModulus [true] [false] = 25 ∧
    OneBitMonomial [true] [false] = 18 ∧
    OneBitNumerator (OneBitEvenThenOdd [true] [false]) = 7 ∧
    OneBitNumerator (OneBitOddThenEven [true] [false]) = 5 ∧
    OneBitNumerator
      (OneBitEvenThenOdd [true] [false] ++ OneBitOddThenEven [true] [false]) = 143 ∧
    OneBitNumerator
      (OneBitOddThenEven [true] [false] ++ OneBitEvenThenOdd [true] [false]) = 157 := by
  decide

end GeneralizedCollatz.OneBit
