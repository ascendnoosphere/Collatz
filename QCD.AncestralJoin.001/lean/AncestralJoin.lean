-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-!
# Saturated inverse-odd-then-even join

For integers `a ≥ 1`, `b ≥ 1` and an odd integer `u`, set
`z = 2^a * 3^b * u - 1` and assume
`z ≡ 2^a - 1` modulo `2^(a+2)`. The inverse odd step
`I(y) = (2y - 1) / 3`, repeated `b` times, is an exact division by `3` at the
first step and ends at `2^(a+b) * u - 1`. One exact division by `2` of the
successor of that value produces `2^(a+b-1) * u - 1`. The congruence forces
`u ≡ (-1)^b` modulo `4`. Oddness of `u` blocks one further factor of `2`.

The congruence is a hypothesis. The statement is not claimed for an arbitrary
odd integer, and it does not assert that the classical map reaches `1`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.Ancestral

/-- One inverse odd step `(2y - 1) / 3` on the integers. -/
def InverseOdd (y : ℤ) : ℤ := (2 * y - 1) / 3

/-- The inverse odd step, repeated `k` times. -/
def InverseOddIterate (k : ℕ) (y : ℤ) : ℤ :=
  Nat.rec y (fun _ acc => InverseOdd acc) k

/-- Divide the successor by two and return to the shifted coordinate. -/
def SuccessorHalf (y : ℤ) : ℤ := (y + 1) / 2 - 1

/-- A positive power of two does not vanish in `ℤ`. -/
theorem AncestralJoinTwoPowNeZero (n : ℕ) : (2 : ℤ) ^ n ≠ 0 := by
  induction n with
  | zero => {
      decide
    }
  | succ n ih => {
      rw [pow_succ]
      intro hzero
      rcases Int.mul_eq_zero.mp hzero with hpow | htwo
      · exact ih hpow
      · exact absurd htwo (by decide)
    }

/-- An odd integer is not divisible by `2`. -/
theorem AncestralJoinOddNotTwoDvd (u : ℤ) (hu : Odd u) : ¬ (2 : ℤ) ∣ u := by
  intro hdvd
  rcases hu with ⟨k, hk⟩
  rcases hdvd with ⟨t, ht⟩
  have hsum : (2 : ℤ) * k + 1 = 2 * t := by
    rw [← hk, ht]
  have hone : (1 : ℤ) = 2 * (t - k) := by
    calc
      (1 : ℤ) = 2 * t - 2 * k := by
        rw [← hsum]
        ring
      _ = 2 * (t - k) := by ring
  have hdiv : (2 : ℤ) ∣ 1 := ⟨t - k, hone⟩
  have hmod : (1 : ℤ) % 2 = 0 :=
    (Int.dvd_iff_emod_eq_zero (a := 2) (b := 1)).mp hdiv
  have honeMod : (1 : ℤ) % 2 = 1 := by decide
  exact absurd hmod (by rw [honeMod]; decide)

/-- `k` inverse odd steps peel `k` factors of `3` from `2^a 3^b u - 1`. -/
theorem AncestralJoinInverseClosed (a b : ℕ) (u : ℤ) :
    ∀ k : ℕ, k ≤ b →
      InverseOddIterate k ((2 : ℤ) ^ a * (3 : ℤ) ^ b * u - 1) =
        (2 : ℤ) ^ (a + k) * (3 : ℤ) ^ (b - k) * u - 1 := by
  intro k
  induction k with
  | zero =>
    {
      intro _
      rfl
    }
  | succ k ih =>
    {
      intro hk
      have hkLe : k ≤ b := Nat.le_of_succ_le hk
      have ihk := ih hkLe
      -- One more inverse odd step removes one factor of `3`.
      have hstep :
          InverseOddIterate (k + 1)
              ((2 : ℤ) ^ a * (3 : ℤ) ^ b * u - 1) =
            InverseOdd
              (InverseOddIterate k
                ((2 : ℤ) ^ a * (3 : ℤ) ^ b * u - 1)) :=
        rfl
      rw [hstep]
      unfold InverseOdd
      rw [ihk]
      have hcancel : b - (k + 1) + (k + 1) = b :=
        Nat.sub_add_cancel hk
      have hExp : b - k = b - (k + 1) + 1 :=
        (Nat.sub_eq_iff_eq_add hkLe).2 <| by
          calc
            b = b - (k + 1) + (k + 1) := hcancel.symm
            _ = b - (k + 1) + (1 + k) := by rw [Nat.add_comm k 1]
            _ = b - (k + 1) + 1 + k := by rw [← Nat.add_assoc]
      have hBin : a + (k + 1) = (a + k) + 1 :=
        (Nat.add_assoc a k 1).symm
      apply Int.ediv_eq_of_eq_mul_left (by decide : (3 : ℤ) ≠ 0)
      rw [hExp, pow_succ (3 : ℤ) (b - (k + 1))]
      rw [hBin, pow_succ (2 : ℤ) (a + k)]
      ring
    }

/-- The first inverse odd step is an exact division by `3` when `b ≥ 1`. -/
theorem AncestralJoinFirstDivisible (a b : ℕ) (u : ℤ) (hb : 1 ≤ b) :
    (3 : ℤ) ∣ 2 * ((2 : ℤ) ^ a * (3 : ℤ) ^ b * u - 1) - 1 := by
  refine ⟨(2 : ℤ) ^ (a + 1) * (3 : ℤ) ^ (b - 1) * u - 1, ?_⟩
  have hs : b = b - 1 + 1 := (Nat.sub_add_cancel hb).symm
  rw [hs, pow_succ (3 : ℤ) (b - 1), pow_succ (2 : ℤ) a]
  have hexp : b - 1 + 1 - 1 = b - 1 := by omega
  rw [hexp]
  ring

/-- One exact division by `2` of a pure binary successor. -/
theorem AncestralJoinHalf (n : ℕ) (u : ℤ) (hn : 1 ≤ n) :
    SuccessorHalf ((2 : ℤ) ^ n * u - 1) = (2 : ℤ) ^ (n - 1) * u - 1 := by
  unfold SuccessorHalf
  have hnum : (2 : ℤ) ^ n * u - 1 + 1 = (2 : ℤ) ^ n * u := by ring
  rw [hnum]
  have hdiv : ((2 : ℤ) ^ n * u) / 2 = (2 : ℤ) ^ (n - 1) * u := by
    apply Int.ediv_eq_of_eq_mul_right (by decide : (2 : ℤ) ≠ 0)
    have hs : n = n - 1 + 1 := (Nat.sub_add_cancel hn).symm
    rw [hs, pow_succ (2 : ℤ) (n - 1)]
    have hexp : n - 1 + 1 - 1 = n - 1 := by omega
    rw [hexp]
    ring
  rw [hdiv]

/-- The binary congruence cancels to a condition modulo `4`. -/
theorem AncestralJoinOddPart (a b : ℕ) (u z : ℤ)
    (hz : z = (2 : ℤ) ^ a * (3 : ℤ) ^ b * u - 1)
    (hcong : z ≡ (2 : ℤ) ^ a - 1 [ZMOD (2 : ℤ) ^ (a + 2)]) :
    (3 : ℤ) ^ b * u ≡ 1 [ZMOD 4] := by
  have hdvd : (2 : ℤ) ^ (a + 2) ∣ (2 : ℤ) ^ a - 1 - z := hcong.dvd
  have hdiff :
      (2 : ℤ) ^ a - 1 - ((2 : ℤ) ^ a * (3 : ℤ) ^ b * u - 1) =
        (2 : ℤ) ^ a * (1 - (3 : ℤ) ^ b * u) := by
    ring
  rw [hz, hdiff] at hdvd
  have hfac : (2 : ℤ) ^ (a + 2) = (2 : ℤ) ^ a * 4 := by
    have hsq : (2 : ℤ) ^ 2 = 4 := by decide
    rw [pow_add, hsq]
  rw [hfac] at hdvd
  have hfour : (4 : ℤ) ∣ 1 - (3 : ℤ) ^ b * u :=
    Int.dvd_of_mul_dvd_mul_left (AncestralJoinTwoPowNeZero a) hdvd
  exact (Int.modEq_iff_dvd).2 hfour

/-- The odd-part congruence is the sign of `u` modulo `4`. -/
theorem AncestralJoinSeedResidue (b : ℕ) (u : ℤ)
    (h : (3 : ℤ) ^ b * u ≡ 1 [ZMOD 4]) :
    u ≡ (-1 : ℤ) ^ b [ZMOD 4] := by
  have hbase : (3 : ℤ) ≡ -1 [ZMOD 4] :=
    (Int.modEq_iff_dvd).2 (by decide : (4 : ℤ) ∣ -1 - 3)
  have hpow : (3 : ℤ) ^ b ≡ (-1 : ℤ) ^ b [ZMOD 4] := hbase.pow b
  have hsigned : (-1 : ℤ) ^ b * u ≡ 1 [ZMOD 4] := by
    exact (hpow.mul_right u).symm.trans h
  -- `(-1)^b` is a unit modulo `4`, so it may be cancelled.
  have hsign : (-1 : ℤ) ^ b * (-1 : ℤ) ^ b = 1 := by
    rw [← pow_add]
    have htwo : b + b = 2 * b := by omega
    rw [htwo, pow_mul]
    have hsq : (-1 : ℤ) ^ 2 = 1 := by decide
    rw [hsq, one_pow]
  have hunit :
      (-1 : ℤ) ^ b * ((-1 : ℤ) ^ b * u) ≡ (-1 : ℤ) ^ b * 1 [ZMOD 4] :=
    hsigned.mul_left ((-1) ^ b)
  have hassoc : (-1 : ℤ) ^ b * ((-1 : ℤ) ^ b * u) = u := by
    rw [← Int.mul_assoc, hsign, one_mul]
  have hright : (-1 : ℤ) ^ b * 1 = (-1 : ℤ) ^ b := mul_one _
  rw [hassoc, hright] at hunit
  exact hunit

/-- An odd factor blocks one further factor of `2` in the parent successor. -/
theorem AncestralJoinPowerExact (a b : ℕ) (u : ℤ) (ha : 1 ≤ a) (hu : Odd u) :
    ¬ (2 : ℤ) ^ (a + b) ∣ (2 : ℤ) ^ (a + b - 1) * u := by
  intro hdvd
  have hsum : 1 ≤ a + b := Nat.le_trans ha (Nat.le_add_right a b)
  have hs : a + b = a + b - 1 + 1 := (Nat.sub_add_cancel hsum).symm
  have hpow : (2 : ℤ) ^ (a + b) = (2 : ℤ) ^ (a + b - 1) * 2 := by
    rw [hs, pow_succ]
    have hexp : a + b - 1 + 1 - 1 = a + b - 1 := by omega
    rw [hexp]
  rw [hpow] at hdvd
  have hu2 : (2 : ℤ) ∣ u :=
    Int.dvd_of_mul_dvd_mul_left (AncestralJoinTwoPowNeZero (a + b - 1)) hdvd
  exact AncestralJoinOddNotTwoDvd u hu hu2

/-- `b` inverse odd steps, then one exact division by `2`.

The congruence is a hypothesis. The statement does not apply to every odd
integer, and it does not assert that the classical map reaches `1`. -/
theorem AncestralJoin (a b : ℕ) (u z : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hu : Odd u) (hz : z = (2 : ℤ) ^ a * (3 : ℤ) ^ b * u - 1)
    (hcong : z ≡ (2 : ℤ) ^ a - 1 [ZMOD (2 : ℤ) ^ (a + 2)]) :
    (3 : ℤ) ∣ 2 * z - 1 ∧
      InverseOddIterate b z = (2 : ℤ) ^ (a + b) * u - 1 ∧
        SuccessorHalf (InverseOddIterate b z) =
          (2 : ℤ) ^ (a + b - 1) * u - 1 ∧
          u ≡ (-1 : ℤ) ^ b [ZMOD 4] ∧
            ¬ (2 : ℤ) ^ (a + b) ∣ (2 : ℤ) ^ (a + b - 1) * u := by
  have hdiv : (3 : ℤ) ∣ 2 * z - 1 := by
    rw [hz]
    exact AncestralJoinFirstDivisible a b u hb
  have hiter0 := AncestralJoinInverseClosed a b u b (Nat.le_refl b)
  have hiter : InverseOddIterate b z = (2 : ℤ) ^ (a + b) * u - 1 := by
    rw [hz, hiter0, Nat.sub_self, pow_zero, mul_one]
  have hsum : 1 ≤ a + b := Nat.le_trans ha (Nat.le_add_right a b)
  have hhalf := AncestralJoinHalf (a + b) u hsum
  have hres :=
    AncestralJoinSeedResidue b u (AncestralJoinOddPart a b u z hz hcong)
  have hexact := AncestralJoinPowerExact a b u ha hu
  refine ⟨hdiv, hiter, ?_, hres, hexact⟩
  rw [hiter]
  exact hhalf

end GeneralizedCollatz.Ancestral
