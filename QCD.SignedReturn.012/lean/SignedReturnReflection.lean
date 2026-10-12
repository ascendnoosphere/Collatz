-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

/-!
# Reflection at multiplier `-1`

For the multiplier `-1`, the affine state at an even time is the seed and at an
odd time is the reflection `C - n`. Those two values are also the raw orbit
when neither is divisible by the signed divisor. The first time the divisor
meets the affine state is then `0`, `1`, or nonexistent. A return quotient
exists only in the first two cases. The third case is an undivided two-cycle,
not a cycle of the return map.

Not proved here: any multiplier other than `-1`, a hit time after the first
division, a bound on a return, or any density or classical convergence
statement.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Affine state after `j` undivided steps, with offset sum `TrapSum q j`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- `j` is the first time `p.D` divides the affine state of the seed `n`. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n

/-- `r` is the return of `n` when a first hit has affine state `p.D * r`. -/
def IsReturn (p : Parameters) (n r : ℤ) : Prop :=
  ∃ j : ℕ, IsFirstHit p n j ∧ AffineState p.Q p.C j n = p.D * r

/-- A two-step cycle of the return map, not of the undivided branch. -/
def IsReturnTwoCycle (p : Parameters) (n : ℤ) : Prop :=
  ∃ r : ℤ, IsReturn p n r ∧ IsReturn p r n

/-- Every time is twice an integer or one more than twice an integer. -/
theorem NatParitySplit (j : ℕ) :
    (∃ k : ℕ, j = 2 * k) ∨ (∃ k : ℕ, j = 2 * k + 1) := by
  induction j with
  | zero => {
      left
      exact ⟨0, rfl⟩
    }
  | succ j ih => {
      cases ih with
      | inl h => {
          obtain ⟨k, hk⟩ := h
          right
          exact ⟨k, by omega⟩
        }
      | inr h => {
          obtain ⟨k, hk⟩ := h
          left
          exact ⟨k + 1, by omega⟩
        }
    }

/-- An even power of `-1` equals one. -/
theorem NegOnePowEven (k : ℕ) : (-1 : ℤ) ^ (2 * k) = 1 := by
  rw [Int.pow_mul]
  induction k with
  | zero => {
      rw [Int.pow_zero]
    }
  | succ k ih => {
      rw [Int.pow_succ, ih]
      have hsq : (-1 : ℤ) ^ 2 = 1 := by
        rw [Int.pow_succ, Int.pow_one]
        ring
      rw [hsq]
      ring
    }

/-- An odd power of `-1` equals minus one. -/
theorem NegOnePowOdd (k : ℕ) : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
  rw [Int.pow_succ, NegOnePowEven k]
  ring

/-- Even times reproduce the seed and odd times reproduce `C - n`. -/
theorem ReflectionAffine (C n : ℤ) (j : ℕ) :
    ((∃ k : ℕ, j = 2 * k) → AffineState (-1) C j n = n) ∧
      ((∃ k : ℕ, j = 2 * k + 1) →
        AffineState (-1) C j n = C - n) := by
  constructor
  · {
      intro h
      obtain ⟨k, hk⟩ := h
      rw [hk]
      unfold AffineState
      show (-1 : ℤ) ^ (2 * k) * n + C * TrapSum (-1) (2 * k) = n
      rw [TrapSumNegOneEven k, NegOnePowEven k]
      ring
    }
  · {
      intro h
      obtain ⟨k, hk⟩ := h
      rw [hk]
      unfold AffineState
      show (-1 : ℤ) ^ (2 * k + 1) * n + C * TrapSum (-1) (2 * k + 1) =
        C - n
      rw [TrapSumNegOneOdd k, NegOnePowOdd k]
      ring
    }

/-- Time zero is the even base: the affine state is the seed. -/
theorem ReflectionTimeZero (C n : ℤ) : AffineState (-1) C 0 n = n := by
  unfold AffineState
  show (-1 : ℤ) ^ 0 * n + C * TrapSum (-1) 0 = n
  rw [TrapSumNegOneEven 0, NegOnePowEven 0]
  ring

/-- Time one is the odd base: the affine state is `C - n`. -/
theorem ReflectionTimeOne (C n : ℤ) : AffineState (-1) C 1 n = C - n := by
  unfold AffineState
  show (-1 : ℤ) ^ 1 * n + C * TrapSum (-1) 1 = C - n
  rw [TrapSumNegOneOdd 0, NegOnePowOdd 0]
  ring

/-- Two further steps cancel a consecutive pair of powers of `-1`. -/
theorem ReflectionRepeatTwo (C n : ℤ) (j : ℕ) :
    AffineState (-1) C (j + 2) n = AffineState (-1) C j n := by
  unfold AffineState
  rw [TrapSumAddTwo]
  have hpow : (-1 : ℤ) ^ (j + 2) = (-1) ^ j := by
    rw [show j + 2 = 2 + j by omega, Int.pow_add]
    have hsq : (-1 : ℤ) ^ 2 = 1 := by
      rw [Int.pow_succ, Int.pow_one]
      ring
    rw [hsq]
    ring
  have hnext : (-1 : ℤ) ^ (j + 1) = - (-1) ^ j := by
    rw [Int.pow_succ]
    ring
  rw [hpow, hnext]
  ring

/-- The first repetition steps are the base times `0` and `1`. -/
theorem ReflectionRepeatBases (C n : ℤ) :
    AffineState (-1) C (0 + 2) n = AffineState (-1) C 0 n ∧
      AffineState (-1) C (1 + 2) n = AffineState (-1) C 1 n := by
  exact ⟨ReflectionRepeatTwo C n 0, ReflectionRepeatTwo C n 1⟩

/-- Later even times repeat time zero and later odd times repeat time one. -/
theorem ReflectionFromBases (C n : ℤ) (k : ℕ) :
    AffineState (-1) C (2 * k) n = AffineState (-1) C 0 n ∧
      AffineState (-1) C (2 * k + 1) n = AffineState (-1) C 1 n := by
  induction k with
  | zero => {
      constructor
      · rfl
      · rfl
    }
  | succ k ih => {
      obtain ⟨heven, hodd⟩ := ih
      have hidxe : 2 * (k + 1) = 2 * k + 2 := by omega
      have hidxo : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      constructor
      · {
          rw [hidxe, ReflectionRepeatTwo C n (2 * k), heven]
        }
      · {
          rw [hidxo, ReflectionRepeatTwo C n (2 * k + 1), hodd]
        }
    }

/-- The two-step relation carries the base values to every later time. -/
theorem ReflectionByRepeat (C n : ℤ) (k : ℕ) :
    AffineState (-1) C (2 * k) n = n ∧
      AffineState (-1) C (2 * k + 1) n = C - n := by
  have hrep := ReflectionFromBases C n k
  constructor
  · {
      rw [hrep.1]
      exact ReflectionTimeZero C n
    }
  · {
      rw [hrep.2]
      exact ReflectionTimeOne C n
    }

/-- The first repeated pair equals the seed and the reflection. -/
theorem ReflectionSecondPeriod (C n : ℤ) :
    AffineState (-1) C 2 n = n ∧ AffineState (-1) C 3 n = C - n := by
  have hbases := ReflectionRepeatBases C n
  constructor
  · {
      rw [hbases.1]
      exact ReflectionTimeZero C n
    }
  · {
      rw [hbases.2]
      exact ReflectionTimeOne C n
    }

/-- Because `|D| ≥ 2`, an exact multiple equals `D` times its quotient. -/
theorem ExactQuotient (d m : ℤ) (hd : d ≠ 0) (h : d ∣ m) :
    m = d * (m / d) := by
  obtain ⟨k, hk⟩ := h
  have hq : m / d = k := Int.ediv_eq_of_eq_mul_right hd hk
  rw [hq, hk]

/-- The first hit is time zero exactly when the divisor meets the seed. -/
theorem ReflectionHitAtZero (p : Parameters) (n : ℤ) (hq : p.Q = -1) :
    IsFirstHit p n 0 ↔ p.D ∣ n := by
  constructor
  · {
      intro h
      obtain ⟨hdiv, _⟩ := h
      rw [hq, ReflectionTimeZero] at hdiv
      exact hdiv
    }
  · {
      intro hdiv
      refine ⟨?_, ?_⟩
      · {
          rw [hq, ReflectionTimeZero]
          exact hdiv
        }
      · {
          intro i hi
          omega
        }
    }

/-- A hit at time zero blocks every later time from being first. -/
theorem ReflectionOnlyZero (p : Parameters) (n : ℤ) (hq : p.Q = -1)
    (hd : p.D ∣ n) {j : ℕ} (hj : 0 < j) : ¬ IsFirstHit p n j := by
  intro hbad
  obtain ⟨-, hearly⟩ := hbad
  have h0 : p.D ∣ AffineState p.Q p.C 0 n := by
    rw [hq, ReflectionTimeZero]
    exact hd
  exact hearly 0 hj h0

/-- If the seed misses and `C - n` hits, the first hit is time one. -/
theorem ReflectionHitAtOne (p : Parameters) (n : ℤ) (hq : p.Q = -1)
    (hn : ¬ p.D ∣ n) (hc : p.D ∣ p.C - n) :
    IsFirstHit p n 1 ∧
      AffineState p.Q p.C 1 n = p.C - n ∧
      RawStep p n = p.C - n ∧
      RawStep p (RawStep p n) = (p.C - n) / p.D ∧
      p.C - n = p.D * ((p.C - n) / p.D) ∧
      ∀ j : ℕ, j ≠ 1 → ¬ IsFirstHit p n j := by
  have hstate : AffineState p.Q p.C 1 n = p.C - n := by
    rw [hq]
    exact ReflectionTimeOne p.C n
  have hhit : IsFirstHit p n 1 := by
    refine ⟨?_, ?_⟩
    · {
        rw [hstate]
        exact hc
      }
    · {
        intro i hi
        have hi0 : i = 0 := by omega
        rw [hi0, hq, ReflectionTimeZero]
        exact hn
      }
  have hraw : RawStep p n = p.C - n := by
    rw [RawStep, if_neg hn, hq]
    ring
  have hdiv : RawStep p (p.C - n) = (p.C - n) / p.D := by
    rw [RawStep, if_pos hc]
  have hret : RawStep p (RawStep p n) = (p.C - n) / p.D := by
    rw [hraw, hdiv]
  have hquot : p.C - n = p.D * ((p.C - n) / p.D) :=
    ExactQuotient p.D (p.C - n) p.DNonzero hc
  refine ⟨hhit, hstate, hraw, hret, hquot, ?_⟩
  intro j hj hbad
  cases j with
  | zero => {
      have h0 := (ReflectionHitAtZero p n hq).1 hbad
      exact hn h0
    }
  | succ t => {
      cases t with
      | zero => {
          exact hj rfl
        }
      | succ t => {
          obtain ⟨-, hearly⟩ := hbad
          have hlt : 1 < t + 2 := by omega
          exact hearly 1 hlt hhit.1
        }
    }

/-- Neither residue divisible means no time is a first hit. -/
theorem ReflectionNoFirstHit (p : Parameters) (n : ℤ) (hq : p.Q = -1)
    (hn : ¬ p.D ∣ n) (hc : ¬ p.D ∣ p.C - n) (j : ℕ) :
    ¬ IsFirstHit p n j := by
  intro hbad
  obtain ⟨hdiv, _⟩ := hbad
  cases NatParitySplit j with
  | inl h => {
      obtain ⟨k, hk⟩ := h
      have hval := (ReflectionByRepeat p.C n k).1
      rw [hk, hq] at hdiv
      rw [hval] at hdiv
      exact hn hdiv
    }
  | inr h => {
      obtain ⟨k, hk⟩ := h
      have hval := (ReflectionByRepeat p.C n k).2
      rw [hk, hq] at hdiv
      rw [hval] at hdiv
      exact hc hdiv
    }

/-- The undivided raw orbit alternates between `n` and `C - n`. -/
theorem ReflectionRawAlternates (p : Parameters) (n : ℤ) (hq : p.Q = -1)
    (hn : ¬ p.D ∣ n) (hc : ¬ p.D ∣ p.C - n) (k : ℕ) :
    Iterate (RawStep p) (2 * k) n = n ∧
      Iterate (RawStep p) (2 * k + 1) n = p.C - n := by
  have hevenStep : RawStep p n = p.C - n := by
    rw [RawStep, if_neg hn, hq]
    ring
  have hoddStep : RawStep p (p.C - n) = n := by
    rw [RawStep, if_neg hc, hq]
    ring
  induction k with
  | zero => {
      constructor
      · rfl
      · {
          have hstep : Iterate (RawStep p) 1 n = RawStep p n := rfl
          rw [hstep, hevenStep]
        }
    }
  | succ k ih => {
      obtain ⟨_, hodd⟩ := ih
      have hidxe : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      have htwo : Iterate (RawStep p) (2 * (k + 1)) n =
          RawStep p (Iterate (RawStep p) (2 * k + 1) n) := by
        rw [hidxe]
        rfl
      have hthree : Iterate (RawStep p) (2 * (k + 1) + 1) n =
          RawStep p (Iterate (RawStep p) (2 * (k + 1)) n) := rfl
      constructor
      · {
          rw [htwo, hodd, hoddStep]
        }
      · {
          rw [hthree, htwo, hodd, hoddStep, hevenStep]
        }
    }

/-- No return exists when both residues miss the divisor. -/
theorem ReflectionNoReturn (p : Parameters) (n : ℤ) (hq : p.Q = -1)
    (hn : ¬ p.D ∣ n) (hc : ¬ p.D ∣ p.C - n) :
    ¬ ∃ r : ℤ, IsReturn p n r := by
  intro hex
  obtain ⟨r, hr⟩ := hex
  obtain ⟨j, hhit, _⟩ := hr
  exact ReflectionNoFirstHit p n hq hn hc j hhit

/-- For multiplier `-1`, the hit is at `0`, at `1`, or nowhere. -/
theorem ReflectionHit (p : Parameters) (n : ℤ) (hq : p.Q = -1) :
    (∀ j : ℕ,
      ((∃ k : ℕ, j = 2 * k) → AffineState p.Q p.C j n = n) ∧
        ((∃ k : ℕ, j = 2 * k + 1) →
          AffineState p.Q p.C j n = p.C - n)) ∧
    (IsFirstHit p n 0 ↔ p.D ∣ n) ∧
    (p.D ∣ n →
      n = p.D * (n / p.D) ∧
        RawStep p n = n / p.D ∧
        ∀ j : ℕ, 0 < j → ¬ IsFirstHit p n j) ∧
    (¬ p.D ∣ n → p.D ∣ p.C - n →
      IsFirstHit p n 1 ∧
        AffineState p.Q p.C 1 n = p.C - n ∧
        RawStep p n = p.C - n ∧
        RawStep p (RawStep p n) = (p.C - n) / p.D ∧
        p.C - n = p.D * ((p.C - n) / p.D) ∧
        ∀ j : ℕ, j ≠ 1 → ¬ IsFirstHit p n j) ∧
    (¬ p.D ∣ n → ¬ p.D ∣ p.C - n →
      (∀ j : ℕ, ¬ IsFirstHit p n j) ∧
        (∀ k : ℕ, AffineState p.Q p.C (2 * k) n = n) ∧
        (∀ k : ℕ, AffineState p.Q p.C (2 * k + 1) n = p.C - n) ∧
        (∀ k : ℕ, Iterate (RawStep p) (2 * k) n = n) ∧
        (∀ k : ℕ,
          Iterate (RawStep p) (2 * k + 1) n = p.C - n) ∧
        (¬ ∃ r : ℤ, IsReturn p n r) ∧
        ¬ IsReturnTwoCycle p n) ∧
    ((∃ r : ℤ, IsReturn p n r) ↔ p.D ∣ n ∨ p.D ∣ p.C - n) := by
  refine ⟨?_, ReflectionHitAtZero p n hq, ?_, ?_, ?_, ?_⟩
  · {
      intro j
      constructor
      · {
          intro h
          rw [hq]
          exact (ReflectionAffine p.C n j).1 h
        }
      · {
          intro h
          rw [hq]
          exact (ReflectionAffine p.C n j).2 h
        }
    }
  · {
      intro hd
      refine ⟨ExactQuotient p.D n p.DNonzero hd, ?_, ?_⟩
      · {
          show RawStep p n = n / p.D
          rw [RawStep, if_pos hd]
        }
      · {
          intro j hj
          exact ReflectionOnlyZero p n hq hd hj
        }
    }
  · {
      intro hn hc
      exact ReflectionHitAtOne p n hq hn hc
    }
  · {
      intro hn hc
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · {
          intro j
          exact ReflectionNoFirstHit p n hq hn hc j
        }
      · {
          intro k
          rw [hq]
          exact (ReflectionByRepeat p.C n k).1
        }
      · {
          intro k
          rw [hq]
          exact (ReflectionByRepeat p.C n k).2
        }
      · {
          intro k
          exact (ReflectionRawAlternates p n hq hn hc k).1
        }
      · {
          intro k
          exact (ReflectionRawAlternates p n hq hn hc k).2
        }
      · {
          exact ReflectionNoReturn p n hq hn hc
        }
      · {
          intro hcycle
          obtain ⟨r, hret, _⟩ := hcycle
          exact ReflectionNoReturn p n hq hn hc ⟨r, hret⟩
        }
    }
  · {
      constructor
      · {
          intro hex
          obtain ⟨r, hr⟩ := hex
          obtain ⟨j, hhit, _⟩ := hr
          obtain ⟨hdiv, _⟩ := hhit
          cases NatParitySplit j with
          | inl h => {
              obtain ⟨k, hk⟩ := h
              left
              rw [hk, hq] at hdiv
              have heq := (ReflectionAffine p.C n (2 * k)).1 ⟨k, rfl⟩
              rw [heq] at hdiv
              exact hdiv
            }
          | inr h => {
              obtain ⟨k, hk⟩ := h
              right
              rw [hk, hq] at hdiv
              have heq :=
                (ReflectionAffine p.C n (2 * k + 1)).2 ⟨k, rfl⟩
              rw [heq] at hdiv
              exact hdiv
            }
        }
      · {
          intro h
          cases h with
          | inl hd => {
              refine ⟨n / p.D, 0, (ReflectionHitAtZero p n hq).2 hd, ?_⟩
              rw [hq, ReflectionTimeZero]
              exact ExactQuotient p.D n p.DNonzero hd
            }
          | inr hc => {
              by_cases hd : p.D ∣ n
              · {
                  refine ⟨n / p.D, 0,
                    (ReflectionHitAtZero p n hq).2 hd, ?_⟩
                  rw [hq, ReflectionTimeZero]
                  exact ExactQuotient p.D n p.DNonzero hd
                }
              · {
                  have hone := ReflectionHitAtOne p n hq hd hc
                  refine ⟨(p.C - n) / p.D, 1, hone.1, ?_⟩
                  rw [hone.2.1]
                  exact ExactQuotient p.D (p.C - n) p.DNonzero hc
                }
            }
        }
    }

end GeneralizedCollatz
