-- SPDX-License-Identifier: CC-BY-4.0
import GeneralizedCollatz
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

/-!
Entry into the residue lattice `cℤ` by the affine map alone.

If `D` does not divide `c`, `gcd(c, D) = 1`, and `c` divides `q ^ k`, then `k`
applications of `n ↦ q * n + c` land in `cℤ`. No division is used. Membership
in that lattice is not capture of the raw state `1`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.LatticeEntryAnalysis

/-- The affine instruction `n ↦ q * n + c`, taken before any division. -/
def AffineBranch (q c n : ℤ) : ℤ :=
  q * n + c

/-- Weights of successive affine instructions. The empty weight is zero. -/
def AffineGeometric (q : ℤ) : ℕ → ℤ
  | 0 => 0
  | j + 1 => q * AffineGeometric q j + 1

/-- The three arithmetic conditions for offset-lattice entry before division. -/
structure LatticeEntryHypotheses (q c d : ℤ) (k : ℕ) : Prop where
  /-- `d` does not divide the offset. -/
  notDiv : ¬ d ∣ c
  /-- The offset and the divisor are coprime. -/
  coprime : Int.gcd c d = 1
  /-- The offset divides the stated multiplier power. -/
  power : c ∣ q ^ k

/-- `k` affine steps expand as `q ^ k * n + c * AffineGeometric q k`. -/
theorem AffineBranchClosedForm (q c n : ℤ) (k : ℕ) :
    Iterate (AffineBranch q c) k n =
      q ^ k * n + c * AffineGeometric q k := by
  induction k with
  | zero => {
      simp [Iterate, AffineGeometric, pow_zero]
    }
  | succ k inductionHypothesis => {
      simp only [Iterate, AffineBranch, inductionHypothesis, AffineGeometric, pow_succ]
      ring
    }

/-- A divisor of `q ^ k` divides every `k`-fold affine image. -/
theorem AffineBranchPowerDivisible (q c n : ℤ) (k : ℕ) (power : c ∣ q ^ k) :
    c ∣ Iterate (AffineBranch q c) k n := by
  rw [AffineBranchClosedForm]
  refine Int.dvd_add ?_ ?_
  · exact Int.dvd_mul_of_dvd_left power
  · exact Int.dvd_mul_right c (AffineGeometric q k)

/-- Coprime `c` and `d`: `d` divides a lattice point `c * m` exactly when it divides `m`. -/
theorem LatticeTransverse (c d m : ℤ) (coprime : Int.gcd c d = 1) :
    d ∣ c * m ↔ d ∣ m := by
  constructor
  · {
      intro dividesProduct
      have bezout : (1 : ℤ) = c * Int.gcdA c d + d * Int.gcdB c d := by
        simpa [coprime, Nat.cast_one] using Int.gcd_eq_gcd_ab c d
      have expanded :
          m = (c * Int.gcdA c d) * m + (d * Int.gcdB c d) * m := by
        have scaled := congrArg (fun t : ℤ => t * m) bezout
        simpa [one_mul, add_mul] using scaled
      rw [expanded]
      refine Int.dvd_add ?_ ?_
      · {
          have reorder : (c * Int.gcdA c d) * m = c * m * Int.gcdA c d := by
            ring
          rw [reorder]
          exact dvd_mul_of_dvd_left dividesProduct (Int.gcdA c d)
        }
      · {
          have reorder : (d * Int.gcdB c d) * m = d * (Int.gcdB c d * m) := by
            ring
          rw [reorder]
          exact dvd_mul_right d (Int.gcdB c d * m)
        }
    }
  · {
      intro dividesCofactor
      exact dvd_mul_of_dvd_right dividesCofactor c
    }

/-- If `d` does not divide `c`, the raw step at the offset is the affine branch. -/
theorem OffsetRawStepAffine (q c d : ℤ) (admissible : 2 ≤ d.natAbs)
    (notDiv : ¬ d ∣ c) :
    RawStep ⟨q, c, d, admissible⟩ c = q * c + c := by
  simp [RawStep, if_neg notDiv]

/-- Every integer seed meets `cℤ` after `k` steps of `n ↦ q * n + c`, before any division. -/
theorem LatticeEntry (q c d : ℤ) (k : ℕ) (hyp : LatticeEntryHypotheses q c d k)
    (n : ℤ) : c ∣ Iterate (AffineBranch q c) k n :=
  AffineBranchPowerDivisible q c n k hyp.power

/-- Parameters `(q, c, D) = (2, 2, 3)`, whose raw orbit at `2` is a two-cycle. -/
def LatticeEntryCycleParameters : Parameters where
  Q := 2
  C := 2
  D := 3
  DAdmissible := by decide

/-- Three does not divide two. -/
theorem ThreeNotDivideTwo : ¬ (3 : ℤ) ∣ 2 := by
  decide

/-- The cycle parameters satisfy the lattice-entry hypotheses at exponent `1`. -/
theorem LatticeEntryCycleHypotheses :
    LatticeEntryHypotheses LatticeEntryCycleParameters.Q LatticeEntryCycleParameters.C
      LatticeEntryCycleParameters.D 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [LatticeEntryCycleParameters]
  · decide
  · {
      refine ⟨1, ?_⟩
      simp [LatticeEntryCycleParameters, pow_one, mul_one]
    }

/-- The state `2` takes the affine branch and lands at `6`. -/
theorem LatticeEntryCycleToSix : RawStep LatticeEntryCycleParameters 2 = 6 := by
  simp only [RawStep, LatticeEntryCycleParameters]
  rw [if_neg ThreeNotDivideTwo]
  norm_num

/-- The state `6` takes the division branch and returns to `2`. -/
theorem LatticeEntryCycleToTwo : RawStep LatticeEntryCycleParameters 6 = 2 := by
  have divides : (3 : ℤ) ∣ 6 := ⟨2, rfl⟩
  simp only [RawStep, LatticeEntryCycleParameters]
  rw [if_pos divides]
  norm_num

/-- Even raw time on the cycle is the state `2`. -/
theorem LatticeEntryCycleEven (j : ℕ) :
    Iterate (RawStep LatticeEntryCycleParameters) (2 * j) 2 = 2 := by
  induction j with
  | zero => {
      simp [Iterate]
    }
  | succ j inductionHypothesis => {
      rw [show 2 * (j + 1) = ((2 * j) + 1) + 1 by omega, Iterate, Iterate]
      rw [inductionHypothesis, LatticeEntryCycleToSix, LatticeEntryCycleToTwo]
    }

/-- Odd raw time on the cycle is the state `6`. -/
theorem LatticeEntryCycleOdd (j : ℕ) :
    Iterate (RawStep LatticeEntryCycleParameters) (2 * j + 1) 2 = 6 := by
  rw [Iterate, LatticeEntryCycleEven j, LatticeEntryCycleToSix]

/-- Every natural number is twice a quotient or one more than twice a quotient. -/
theorem ModTwoSplit (m : ℕ) : ∃ j, m = 2 * j ∨ m = 2 * j + 1 := by
  refine ⟨m / 2, ?_⟩
  have divided : m = 2 * (m / 2) + m % 2 := (Nat.div_add_mod m 2).symm
  have bound : m % 2 < 2 := Nat.mod_lt m (by decide)
  cases residue : m % 2 with
  | zero => {
      left
      rw [divided, residue]
      omega
    }
  | succ r => {
      have small : r + 1 < 2 := by
        simpa [residue] using bound
      have zero : r = 0 := by omega
      right
      rw [divided, residue, zero]
      omega
    }

/-- No raw iterate of `2` under `(q, c, D) = (2, 2, 3)` equals `1`. -/
theorem LatticeEntryCycleAvoidsOne (m : ℕ) :
    Iterate (RawStep LatticeEntryCycleParameters) m 2 ≠ 1 := by
  obtain ⟨j, split⟩ := ModTwoSplit m
  rcases split with even | odd
  · {
      rw [even, LatticeEntryCycleEven]
      decide
    }
  · {
      rw [odd, LatticeEntryCycleOdd]
      decide
    }

/-- Lattice entry is not capture: the cycle meets `cℤ` and never equals `1`. -/
theorem LatticeEntryNotCapture :
    ∃ q c d : ℤ, ∃ k : ℕ, ∃ n : ℤ, ∃ admissible : 2 ≤ d.natAbs,
      LatticeEntryHypotheses q c d k ∧
        c ∣ Iterate (AffineBranch q c) k n ∧
        ∀ m : ℕ,
          Iterate (RawStep ⟨q, c, d, admissible⟩) m n ≠ 1 := by
  refine ⟨2, 2, 3, 1, 2, by decide, ?_, ?_, ?_⟩
  · simpa [LatticeEntryCycleParameters] using LatticeEntryCycleHypotheses
  · exact LatticeEntry 2 2 3 1
      (by simpa [LatticeEntryCycleParameters] using LatticeEntryCycleHypotheses) 2
  · intro m
    simpa [LatticeEntryCycleParameters] using LatticeEntryCycleAvoidsOne m

/-- The classical parameters `(q, c, D) = (3, 1, 2)` meet the lattice hypotheses. -/
theorem ClassicalParametersAreLatticeEntry (k : ℕ) :
    LatticeEntryHypotheses 3 1 2 k := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · exact Int.one_gcd
  · exact one_dvd ((3 : ℤ) ^ k)


end GeneralizedCollatz.LatticeEntryAnalysis
