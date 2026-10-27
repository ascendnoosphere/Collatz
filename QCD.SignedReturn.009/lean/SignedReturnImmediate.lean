-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps

/-!
# Immediate return at exponent zero

At time zero the affine state is the seed, and the bounded quantifier over
earlier times ranges over the empty initial segment of the naturals. Thus a
first hit at time zero is exactly divisibility by the signed divisor. On that
event the raw step is division by `D`, the absolute values multiply back to
the absolute value of the seed, and the core comparison holds with slope `1`
and constant `0`. No positive exponent is treated.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.SignedReturnImmediate

/-- Affine state after `j` undivided steps, with offset sum `TrapSum q j`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- `j` is the first time `p.D` divides the affine state of the seed `n`. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n

/-- At time zero the power is one and the offset sum is the empty sum. -/
theorem AffineStateZero (q c n : ℤ) : AffineState q c 0 n = n := by
  unfold AffineState
  rw [Int.pow_zero]
  have hsum : TrapSum q 0 = 0 := rfl
  rw [hsum]
  rw [Int.one_mul, Int.mul_zero, Int.add_zero]

/-- The bounded quantifier over `i < 0` holds because that range is empty.
By definition, `∀ i < 0, P i` is `∀ i, i < 0 → P i`. No natural number
satisfies `i < 0`. -/
theorem NoEarlierTimeAtZero {P : ℕ → Prop} : ∀ i : ℕ, i < 0 → P i := by
  intro i hi
  have hempty : ¬ i < 0 := Nat.not_lt_zero i
  have hfalse : False := hempty hi
  exact False.elim hfalse

/-- Time zero is a first hit exactly when `D` divides the seed. -/
theorem FirstHitZeroIff (p : Parameters) (n : ℤ) :
    IsFirstHit p n 0 ↔ p.D ∣ n := by
  unfold IsFirstHit
  have hstate : AffineState p.Q p.C 0 n = n :=
    AffineStateZero p.Q p.C n
  -- The earlier-time conjunct is a bounded quantifier over the empty range.
  have hearly :
      ∀ i : ℕ, i < 0 → ¬ p.D ∣ AffineState p.Q p.C i n :=
    NoEarlierTimeAtZero
  constructor
  · {
      intro hhit
      have hdiv : p.D ∣ AffineState p.Q p.C 0 n := hhit.1
      rw [hstate] at hdiv
      exact hdiv
    }
  · {
      intro hdiv
      refine ⟨?_, hearly⟩
      show p.D ∣ AffineState p.Q p.C 0 n
      rw [hstate]
      exact hdiv
    }

/-- If `D` divides `n`, the raw step is the quotient and absolute values cancel. -/
theorem ImmediateQuotient (p : Parameters) (n : ℤ) (hdiv : p.D ∣ n) :
    RawStep p n = n / p.D ∧
      p.D.natAbs * (n / p.D).natAbs = n.natAbs := by
  constructor
  · {
      -- Divisibility selects the division branch of the raw step.
      show RawStep p n = n / p.D
      unfold RawStep
      exact if_pos hdiv
    }
  · {
      -- Absolute value is multiplicative, and `D * (n / D)` is `n`.
      have hcancel : p.D * (n / p.D) = n :=
        Int.mul_ediv_cancel' hdiv
      have hnat : (p.D * (n / p.D)).natAbs = n.natAbs :=
        congrArg Int.natAbs hcancel
      rw [Int.natAbs_mul] at hnat
      exact hnat
    }

/-- Exponent zero meets the core bound with slope `1` and constant `0`. -/
theorem ImmediateCore (p : Parameters) (n : ℤ) (hdiv : p.D ∣ n)
    (A B : ℕ) (hA : A = 1) (hB : B = 0) :
    A < p.D.natAbs ∧
      p.D.natAbs * (n / p.D).natAbs ≤ A * n.natAbs + B := by
  have hstep : (1 : ℕ) < 2 := by decide
  have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
  have hlt : (1 : ℕ) < p.D.natAbs := lt_of_lt_of_le hstep htwo
  constructor
  · {
      show A < p.D.natAbs
      rw [hA]
      exact hlt
    }
  · {
      -- The absolute-value identity is the core inequality at slope 1.
      have heq : p.D.natAbs * (n / p.D).natAbs = n.natAbs :=
        (ImmediateQuotient p n hdiv).2
      have hbound : p.D.natAbs * (n / p.D).natAbs ≤ n.natAbs :=
        le_of_eq heq
      have hrhs : A * n.natAbs + B = n.natAbs := by
        rw [hA, hB, Nat.one_mul, Nat.add_zero]
      show p.D.natAbs * (n / p.D).natAbs ≤ A * n.natAbs + B
      rw [hrhs]
      exact hbound
    }

end GeneralizedCollatz.SignedReturnImmediate
