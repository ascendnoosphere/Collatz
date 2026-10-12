-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import Mathlib.Data.Nat.Basic

/-
Five displayed pairs for the equation `x ^ 2 + 7 = 2 ^ n`.

The pairs are `(1, 3)`, `(3, 4)`, `(5, 5)`, `(11, 7)`, and `(181, 15)`.
Each identity is a square, a power of two, and the addition of `7`.
These evaluations do not say that every positive solution is one of the five pairs.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The equation `x ^ 2 + 7 = 2 ^ n` in the natural numbers. -/
def NagellEquation (x n : ℕ) : Prop :=
  x ^ 2 + 7 = 2 ^ n

/-- The third power of two is eight. -/
theorem TwoPowThree : 2 ^ 3 = 8 := by
  rw [Nat.pow_succ 2 2, Nat.pow_succ 2 1, Nat.pow_succ 2 0, Nat.pow_zero]

/-- The fourth power of two is sixteen. -/
theorem TwoPowFour : 2 ^ 4 = 16 := by
  rw [Nat.pow_succ 2 3, TwoPowThree]

/-- The fifth power of two is thirty-two. -/
theorem TwoPowFive : 2 ^ 5 = 32 := by
  rw [Nat.pow_succ 2 4, TwoPowFour]

/-- The sixth power of two is sixty-four. -/
theorem TwoPowSix : 2 ^ 6 = 64 := by
  rw [Nat.pow_succ 2 5, TwoPowFive]

/-- The seventh power of two is one hundred twenty-eight. -/
theorem TwoPowSeven : 2 ^ 7 = 128 := by
  rw [Nat.pow_succ 2 6, TwoPowSix]

/-- The fifteenth power of two is thirty-two thousand seven hundred sixty-eight. -/
theorem TwoPowFifteen : 2 ^ 15 = 32768 := by
  have hten : 2 ^ 10 = 1024 := by
    have hsplit : (10 : ℕ) = 5 + 5 := by decide
    rw [hsplit, Nat.pow_add, TwoPowFive]
  have hsplit : (15 : ℕ) = 10 + 5 := by decide
  rw [hsplit, Nat.pow_add, hten, TwoPowFive]

/-- One squared is one. -/
theorem SquareOne : 1 ^ 2 = 1 := by
  rw [Nat.pow_two, Nat.one_mul]

/-- Three squared is nine. -/
theorem SquareThree : 3 ^ 2 = 9 := by
  rw [Nat.pow_two]

/-- Five squared is twenty-five. -/
theorem SquareFive : 5 ^ 2 = 25 := by
  rw [Nat.pow_two]

/-- Eleven squared is one hundred twenty-one. -/
theorem SquareEleven : 11 ^ 2 = 121 := by
  rw [Nat.pow_two]

/-- One hundred eighty-one squared is thirty-two thousand seven hundred sixty-one. -/
theorem SquareOneEightyOne : 181 ^ 2 = 32761 := by
  rw [Nat.pow_two]

/-- The displayed pair `(1, 3)` satisfies `x ^ 2 + 7 = 2 ^ n`. -/
theorem NagellDisplayedOneThree : NagellEquation 1 3 := by
  unfold NagellEquation
  rw [SquareOne, TwoPowThree]

/-- The displayed pair `(3, 4)` satisfies `x ^ 2 + 7 = 2 ^ n`. -/
theorem NagellDisplayedThreeFour : NagellEquation 3 4 := by
  unfold NagellEquation
  rw [SquareThree, TwoPowFour]

/-- The displayed pair `(5, 5)` satisfies `x ^ 2 + 7 = 2 ^ n`. -/
theorem NagellDisplayedFiveFive : NagellEquation 5 5 := by
  unfold NagellEquation
  rw [SquareFive, TwoPowFive]

/-- The displayed pair `(11, 7)` satisfies `x ^ 2 + 7 = 2 ^ n`. -/
theorem NagellDisplayedElevenSeven : NagellEquation 11 7 := by
  unfold NagellEquation
  rw [SquareEleven, TwoPowSeven]

/-- The displayed pair `(181, 15)` satisfies `x ^ 2 + 7 = 2 ^ n`. -/
theorem NagellDisplayedOneEightyOneFifteen : NagellEquation 181 15 := by
  unfold NagellEquation
  rw [SquareOneEightyOne, TwoPowFifteen]

/-- Each of the five displayed pairs satisfies `x ^ 2 + 7 = 2 ^ n`. -/
theorem NagellDisplayedFive :
    NagellEquation 1 3 ∧ NagellEquation 3 4 ∧ NagellEquation 5 5 ∧
      NagellEquation 11 7 ∧ NagellEquation 181 15 := by
  apply And.intro NagellDisplayedOneThree
  apply And.intro NagellDisplayedThreeFour
  apply And.intro NagellDisplayedFiveFive
  apply And.intro NagellDisplayedElevenSeven
  exact NagellDisplayedOneEightyOneFifteen

end GeneralizedCollatz
