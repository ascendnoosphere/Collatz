-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Tactic.Ring

/-!
# Returns for a zero multiplier

With multiplier zero, the affine state at time zero is the seed, and the affine
state at every positive time is the offset. The signed divisor therefore meets
the affine itinerary at time zero when it divides the seed, and at time one
when it misses the seed but divides the offset. In the first case the raw
return is `n / D`. In the second case one affine step reaches the offset and
the raw return is `C / D`. If the divisor misses both integers, no time is a
first hit: the constant continuation is a trap, not a return.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.SignedReturnZero

/-- The affine state of multiplier `q`, offset `c`, time `j` and seed `n`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- The affine state meets `D` at time `j` and at no earlier time. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n

/-- At time zero the affine state is the seed. -/
theorem AffineStateAtZero (q c n : ℤ) : AffineState q c 0 n = n := by
  unfold AffineState
  have hpow : q ^ (0 : ℕ) = 1 := pow_zero q
  have hsum : TrapSum q 0 = 0 := rfl
  rw [hpow, hsum]
  ring

/-- With multiplier zero, every positive time equals the offset. -/
theorem ZeroAffine (C n : ℤ) (j : ℕ) (hj : 1 ≤ j) :
    AffineState 0 C j n = C := by
  have hk : j = (j - 1) + 1 := by omega
  rw [hk]
  unfold AffineState
  have hsum : TrapSum 0 ((j - 1) + 1) = 1 := TrapSumZero (j - 1)
  -- The exponent is positive, so the zero power vanishes.
  have hpow : (0 : ℤ) ^ ((j - 1) + 1) = 0 := by
    rw [pow_succ]
    exact Int.mul_zero ((0 : ℤ) ^ (j - 1))
  rw [hsum, hpow]
  ring

/-- The zero multiplier has three return regimes, and a double miss is not one. -/
theorem ZeroHitCases (p : Parameters) (n : ℤ) (hq : p.Q = 0) :
    (p.D ∣ n →
      IsFirstHit p n 0 ∧ RawStep p n = n / p.D ∧
        ∀ j, IsFirstHit p n j → j = 0) ∧
    (¬ p.D ∣ n → p.D ∣ p.C →
      IsFirstHit p n 1 ∧ RawStep p (RawStep p n) = p.C / p.D ∧
        ∀ j, IsFirstHit p n j → j = 1) ∧
    (¬ p.D ∣ n → ¬ p.D ∣ p.C →
      AffineState p.Q p.C 0 n = n ∧
        (∀ j, 1 ≤ j → AffineState p.Q p.C j n = p.C) ∧
        ∀ j, ¬ IsFirstHit p n j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    refine ⟨?_, ?_, ?_⟩
    · unfold IsFirstHit
      refine ⟨?_, ?_⟩
      · rw [AffineStateAtZero]
        exact hd
      · intro i hi
        exact absurd hi (Nat.not_lt_zero i)
    · show RawStep p n = n / p.D
      unfold RawStep
      exact if_pos hd
    · intro j hj
      unfold IsFirstHit at hj
      cases j with
      | zero => {
          rfl
        }
      | succ k => {
          -- Time zero is already a hit, so no later time is first.
          have hseed : AffineState p.Q p.C 0 n = n :=
            AffineStateAtZero p.Q p.C n
          have hd0 : p.D ∣ AffineState p.Q p.C 0 n := by
            rw [hseed]
            exact hd
          exact absurd hd0 (hj.2 0 (Nat.succ_pos k))
        }
  · intro hnd hc
    refine ⟨?_, ?_, ?_⟩
    · unfold IsFirstHit
      refine ⟨?_, ?_⟩
      · have hone : AffineState p.Q p.C 1 n = p.C := by
          rw [hq]
          exact ZeroAffine p.C n 1 (by omega)
        rw [hone]
        exact hc
      · intro i hi
        have hi0 : i = 0 := by omega
        rw [hi0, AffineStateAtZero]
        exact hnd
    · show RawStep p (RawStep p n) = p.C / p.D
      have haff : RawStep p n = p.C := by
        rw [RawStepAffine p n hnd, hq]
        ring
      have hdiv : RawStep p p.C = p.C / p.D := by
        unfold RawStep
        exact if_pos hc
      rw [haff]
      exact hdiv
    · intro j hj
      unfold IsFirstHit at hj
      cases j with
      | zero => {
          rw [AffineStateAtZero] at hj
          exact absurd hj.1 hnd
        }
      | succ k => {
          cases k with
          | zero => {
              rfl
            }
          | succ k => {
              -- Time one is already a hit, so no later time is first.
              have hone : AffineState p.Q p.C 1 n = p.C := by
                rw [hq]
                exact ZeroAffine p.C n 1 (by omega)
              have hd1 : p.D ∣ AffineState p.Q p.C 1 n := by
                rw [hone]
                exact hc
              exact absurd hd1 (hj.2 (1 : ℕ) (by omega))
            }
        }
  · intro hnd hnc
    have hzero : AffineState p.Q p.C 0 n = n :=
      AffineStateAtZero p.Q p.C n
    have hpos : ∀ j, 1 ≤ j → AffineState p.Q p.C j n = p.C := by
      intro j hj
      rw [hq]
      exact ZeroAffine p.C n j hj
    refine ⟨hzero, hpos, ?_⟩
    intro j hhit
    unfold IsFirstHit at hhit
    cases j with
    | zero => {
        rw [hzero] at hhit
        exact absurd hhit.1 hnd
      }
    | succ k => {
        -- A positive time equals the offset, which was assumed indivisible.
        have hj : 1 ≤ k + 1 := by omega
        have hC : AffineState p.Q p.C (k + 1) n = p.C := hpos (k + 1) hj
        rw [hC] at hhit
        exact absurd hhit.1 hnc
      }

end GeneralizedCollatz.SignedReturnZero
