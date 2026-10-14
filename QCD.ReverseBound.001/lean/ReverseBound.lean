-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# Even division totals and complementary factors

The equations `2 ^ a * y = q * x + 1` and `2 ^ b * x = q * y + 1` cannot
both hold when `a + b = 2 * t` and `x, y ≥ μ ≥ 2`. This algebraic statement
holds for every natural multiplier `q`, including the odd multipliers of the
raw Collatz map. The proof compares the product forced by the equations with
the strict square bound at `q ≤ 2 ^ t - 1`.

Complementary factors recover the multiplier from their sum and product.
For difference `7`, the only even exponent is `4`, with multiplier `3`.
The equations at `x = y = 1` show why the minimum `2` is necessary.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.ReverseBound

/-- `n` is odd when its remainder modulo `2` is `1`. -/
def IsOdd (n : ℕ) : Prop := n % 2 = 1

/-- Squaring commutes with the even exponent `2 t`. -/
theorem TwoPowSquare (t : ℕ) : (2 ^ t) ^ 2 = 2 ^ (2 * t) :=
  (Nat.pow_mul' 2 2 t).symm

/-- A positive power of two is even. -/
theorem TwoPowEven (t : ℕ) (ht : 1 ≤ t) : (2 ^ t) % 2 = 0 := by
  cases t with
  | zero =>
    {
      exact absurd ht (Nat.not_succ_le_zero 0)
    }
  | succ s =>
    {
      rw [Nat.pow_succ]
      exact Nat.mul_mod_left (2 ^ s) 2
    }

/-- The integer immediately below a positive power of two is odd. -/
theorem BoundaryOdd (t : ℕ) (ht : 1 ≤ t) : IsOdd (2 ^ t - 1) := by
  cases t with
  | zero =>
    {
      exact absurd ht (Nat.not_succ_le_zero 0)
    }
  | succ s =>
    {
      have hk : 1 ≤ 2 ^ s := Nat.one_le_of_lt (Nat.two_pow_pos s)
      have hfactor : 2 * (2 ^ s - 1) + 2 = 2 * ((2 ^ s - 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      have hsum : 2 * (2 ^ s - 1) + 2 = 2 * 2 ^ s := by
        rw [hfactor, Nat.sub_add_cancel hk]
      have hpair : (1 : ℕ) + 1 = 2 := rfl
      have hbuild : 2 * (2 ^ s - 1) + (1 + 1) = 2 * 2 ^ s := by
        rw [hpair, hsum]
      have hsum1 : 2 * 2 ^ s = 2 * (2 ^ s - 1) + 1 + 1 := by
        rw [← Nat.add_assoc] at hbuild
        exact hbuild.symm
      have hsub : 2 * 2 ^ s - 1 = 2 * (2 ^ s - 1) + 1 :=
        Nat.sub_eq_of_eq_add hsum1
      have hpow : 2 ^ (s + 1) - 1 = 2 * (2 ^ s - 1) + 1 := by
        calc
          2 ^ (s + 1) - 1 = 2 ^ s * 2 - 1 := by rw [Nat.pow_succ]
          _ = 2 * 2 ^ s - 1 := by rw [Nat.mul_comm]
          _ = 2 * (2 ^ s - 1) + 1 := hsub
      have hmod : (2 * (2 ^ s - 1) + 1) % 2 = 1 := by
        rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
      rw [hpow]
      exact hmod
    }

/-- A positive power of two is not an odd multiplier. -/
theorem PowerNotOdd (t : ℕ) (ht : 1 ≤ t) : ¬ IsOdd (2 ^ t) := by
  intro h
  exact Nat.one_ne_zero (h.symm.trans (TwoPowEven t ht))

/-- A strict square window lies at most one below the integer root. -/
theorem SquareWindowBound (t q : ℕ) (hwindow : q ^ 2 < 2 ^ (2 * t)) :
    q ≤ 2 ^ t - 1 := by
  have hlt : q < 2 ^ t := by
    {
      by_contra hge
      have hle : 2 ^ t ≤ q := Nat.le_of_not_lt hge
      have hsq : (2 ^ t) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hle 2
      have hpow : 2 ^ (2 * t) ≤ q ^ 2 := by
        {
          rw [TwoPowSquare] at hsq
          exact hsq
        }
      exact Nat.not_lt_of_le hpow hwindow
    }
  exact Nat.le_sub_one_of_lt hlt

/-- An odd multiplier inside the strict window is at most `2 ^ t - 1`. -/
theorem OddCandidateBound (t q : ℕ) (ht : 1 ≤ t) (hq : IsOdd q)
    (hwindow : q ^ 2 < 2 ^ (2 * t)) : q ≤ 2 ^ t - 1 := by
  have hbound : q ≤ 2 ^ t - 1 := SquareWindowBound t q hwindow
  have hne : q ≠ 2 ^ t := by
    {
      intro h
      rw [h] at hq
      exact PowerNotOdd t ht hq
    }
  have hle : q ≤ 2 ^ t := Nat.le_trans hbound (Nat.sub_le (2 ^ t) 1)
  cases Nat.lt_or_eq_of_le hle with
  | inl hlt =>
    {
      exact Nat.le_sub_one_of_lt hlt
    }
  | inr heq =>
    {
      exact absurd heq hne
    }

/-- The odd endpoint itself remains inside the strict square window. -/
theorem EndpointInWindow (t : ℕ) (ht : 1 ≤ t) :
    IsOdd (2 ^ t - 1) ∧ (2 ^ t - 1) ^ 2 < 2 ^ (2 * t) := by
  have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
  have hlt : 2 ^ t - 1 < 2 ^ t := Nat.pred_lt_self hpos
  have hsq : (2 ^ t - 1) ^ 2 < (2 ^ t) ^ 2 :=
    Nat.pow_lt_pow_left hlt (by decide : (2 : ℕ) ≠ 0)
  rw [TwoPowSquare] at hsq
  exact And.intro (BoundaryOdd t ht) hsq

/-- The largest admissible product still lies at most one below the root. -/
theorem EndpointCeiling (t μ q : ℕ) (hμ : 2 ≤ μ) (hq : q ≤ 2 ^ t - 1) :
    μ * q + 1 ≤ μ * 2 ^ t - 1 := by
  have hone : 1 ≤ μ := Nat.le_trans (by decide : (1 : ℕ) ≤ 2) hμ
  have hpow : 1 ≤ 2 ^ t := Nat.one_le_of_lt (Nat.two_pow_pos t)
  have hμle : μ ≤ μ * 2 ^ t := by
    {
      have hmul : μ * 1 ≤ μ * 2 ^ t := Nat.mul_le_mul_left μ hpow
      rw [Nat.mul_one] at hmul
      exact hmul
    }
  have hsub : μ * (2 ^ t - 1) = μ * 2 ^ t - μ := by
    rw [Nat.mul_sub, Nat.mul_one]
  have hk : 1 ≤ μ - 1 := (Nat.le_sub_iff_add_le hone).2 hμ
  have hrest : 1 + (μ - 1) = μ := by
    rw [Nat.add_comm]
    exact Nat.sub_add_cancel hone
  have hsum : (μ * 2 ^ t - μ) + 1 + (μ - 1) = μ * 2 ^ t := by
    calc
      (μ * 2 ^ t - μ) + 1 + (μ - 1)
          = (μ * 2 ^ t - μ) + (1 + (μ - 1)) := by rw [Nat.add_assoc]
      _ = (μ * 2 ^ t - μ) + μ := by rw [hrest]
      _ = μ * 2 ^ t := Nat.sub_add_cancel hμle
  have hs : (μ * 2 ^ t - μ) + 1 = μ * 2 ^ t - (μ - 1) :=
    (Nat.sub_eq_of_eq_add hsum.symm).symm
  have hcmp : μ * 2 ^ t - (μ - 1) ≤ μ * 2 ^ t - 1 :=
    Nat.sub_le_sub_left hk (μ * 2 ^ t)
  have hpush : μ * q + 1 ≤ μ * (2 ^ t - 1) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left μ hq) 1
  have hrewrite : μ * (2 ^ t - 1) + 1 = (μ * 2 ^ t - μ) + 1 := by
    rw [hsub]
  exact Nat.le_trans (Nat.le_trans hpush (Nat.le_of_eq hrewrite))
    (Nat.le_trans (Nat.le_of_eq hs) hcmp)

/-- For minimum `μ ≥ 2`, the endpoint square lies strictly under the root. -/
theorem ProductCeiling (t μ q : ℕ) (hμ : 2 ≤ μ) (hq : q ≤ 2 ^ t - 1) :
    (μ * q + 1) ^ 2 < μ ^ 2 * 2 ^ (2 * t) := by
  have htop : μ * q + 1 ≤ μ * 2 ^ t - 1 := EndpointCeiling t μ q hμ hq
  have hμpos : 0 < μ := Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hμ
  have hpow : 1 ≤ 2 ^ t := Nat.one_le_of_lt (Nat.two_pow_pos t)
  have hμle : μ ≤ μ * 2 ^ t := by
    {
      have hmul : μ * 1 ≤ μ * 2 ^ t := Nat.mul_le_mul_left μ hpow
      rw [Nat.mul_one] at hmul
      exact hmul
    }
  have hN : 0 < μ * 2 ^ t := Nat.lt_of_lt_of_le hμpos hμle
  have hpred : μ * 2 ^ t - 1 < μ * 2 ^ t := Nat.pred_lt_self hN
  have hsq : (μ * 2 ^ t - 1) ^ 2 < (μ * 2 ^ t) ^ 2 :=
    Nat.pow_lt_pow_left hpred (by decide : (2 : ℕ) ≠ 0)
  have hle : (μ * q + 1) ^ 2 ≤ (μ * 2 ^ t - 1) ^ 2 :=
    Nat.pow_le_pow_left htop 2
  have hpowsq : (μ * 2 ^ t) ^ 2 = μ ^ 2 * 2 ^ (2 * t) := by
    rw [Nat.mul_pow, TwoPowSquare]
  exact Nat.lt_of_le_of_lt hle (by rw [hpowsq] at hsq; exact hsq)

/-- Even length splits as a difference of squares. -/
theorem DifferenceSplit (m q : ℕ) :
    2 ^ (2 * m) - q ^ 2 = (2 ^ m - q) * (2 ^ m + q) := by
  calc
    2 ^ (2 * m) - q ^ 2 = (2 ^ m) ^ 2 - q ^ 2 := by rw [← TwoPowSquare]
    _ = (2 ^ m + q) * (2 ^ m - q) := Nat.pow_two_sub_pow_two (2 ^ m) q
    _ = (2 ^ m - q) * (2 ^ m + q) := by rw [Nat.mul_comm]

/-- The two factors of an even length sum to the next power of two. -/
theorem FactorSum (m q : ℕ) (hq : q ≤ 2 ^ m) :
    (2 ^ m - q) + (2 ^ m + q) = 2 ^ (m + 1) := by
  calc
    (2 ^ m - q) + (2 ^ m + q) = (2 ^ m - q) + (q + 2 ^ m) := by
      rw [Nat.add_comm (2 ^ m) q]
    _ = (2 ^ m - q) + q + 2 ^ m := by rw [← Nat.add_assoc]
    _ = 2 ^ m + 2 ^ m := by rw [Nat.sub_add_cancel hq]
    _ = 2 * 2 ^ m := by rw [← Nat.two_mul]
    _ = 2 ^ m * 2 := by rw [Nat.mul_comm]
    _ = 2 ^ (m + 1) := by rw [← Nat.pow_succ]

/-- The factor gap is twice the multiplier. -/
theorem FactorGap (m q : ℕ) (hq : q ≤ 2 ^ m) :
    (2 ^ m + q) - (2 ^ m - q) = 2 * q := by
  have hbuild : (2 ^ m - q) + 2 * q = 2 ^ m + q := by
    calc
      (2 ^ m - q) + 2 * q = (2 ^ m - q) + (q + q) := by rw [Nat.two_mul]
      _ = (2 ^ m - q) + q + q := by rw [← Nat.add_assoc]
      _ = 2 ^ m + q := by rw [Nat.sub_add_cancel hq]
  exact Nat.sub_eq_of_eq_add' hbuild.symm

/-- Equal squares have equal roots. -/
theorem SqEq (a b : ℕ) (h : a ^ 2 = b ^ 2) : a = b := by
  cases Nat.le_total a b with
  | inl hab =>
    {
      have hdiff : b ^ 2 - a ^ 2 = 0 := by
        rw [← h, Nat.sub_self]
      rw [Nat.pow_two_sub_pow_two] at hdiff
      cases Nat.mul_eq_zero.mp hdiff with
      | inl hsum =>
        {
          have hboth := Nat.eq_zero_of_add_eq_zero hsum
          exact hboth.2.trans hboth.1.symm
        }
      | inr hsub =>
        {
          have hba : b ≤ a := (Nat.sub_eq_zero_iff_le).mp hsub
          exact Nat.le_antisymm_iff.mpr ⟨hab, hba⟩
        }
    }
  | inr hba =>
    {
      have hdiff : a ^ 2 - b ^ 2 = 0 := by
        rw [h, Nat.sub_self]
      rw [Nat.pow_two_sub_pow_two] at hdiff
      cases Nat.mul_eq_zero.mp hdiff with
      | inl hsum =>
        {
          have hboth := Nat.eq_zero_of_add_eq_zero hsum
          exact hboth.1.trans hboth.2.symm
        }
      | inr hsub =>
        {
          have hab : a ≤ b := (Nat.sub_eq_zero_iff_le).mp hsub
          exact Nat.le_antisymm_iff.mpr ⟨hab, hba⟩
        }
    }

/-- The square of a factor at most `2 ^ m` remains inside the even window. -/
theorem SquareOfFactor (m u : ℕ) (hu : u ≤ 2 ^ m) : u ^ 2 ≤ 2 ^ (2 * m) := by
  have hsq : u ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left hu 2
  rw [TwoPowSquare] at hsq
  exact hsq

/-- A complementary factor pair recovers the multiplier. -/
theorem FactorRecovery (m q u v : ℕ) (hq : q ^ 2 ≤ 2 ^ (2 * m))
    (hsum : u + v = 2 ^ (m + 1)) (hprod : u * v = 2 ^ (2 * m) - q ^ 2)
    (huv : u ≤ v) : v - u = 2 * q := by
  have hs : 2 ^ (m + 1) = 2 * 2 ^ m := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have hdouble : u + v = 2 * 2 ^ m := by
    rw [hsum, hs]
  have hv : 2 ^ m ≤ v := by
    {
      by_contra hlt
      have hvlt : v < 2 ^ m := Nat.lt_of_not_ge hlt
      have hvle : v ≤ 2 ^ m - 1 := Nat.le_sub_one_of_lt hvlt
      have hule : u ≤ 2 ^ m - 1 := Nat.le_trans huv hvle
      have hpair : u + v ≤ (2 ^ m - 1) + (2 ^ m - 1) :=
        Nat.add_le_add hule hvle
      have htwo : (2 ^ m - 1) + (2 ^ m - 1) = 2 * (2 ^ m - 1) := by
        rw [← Nat.two_mul]
      have hcut : 2 * (2 ^ m - 1) = 2 * 2 ^ m - 2 := by
        rw [Nat.mul_sub, Nat.mul_one]
      have hle2 : 2 ≤ 2 * 2 ^ m := by
        {
          have hone : 1 ≤ 2 ^ m := Nat.one_le_of_lt (Nat.two_pow_pos m)
          have hmul : 2 * 1 ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 hone
          rw [Nat.mul_one] at hmul
          exact hmul
        }
      have hstrict : 2 * 2 ^ m - 2 < 2 * 2 ^ m :=
        Nat.sub_lt_of_pos_le (by decide : (0 : ℕ) < 2) hle2
      have hsmall : u + v < 2 * 2 ^ m := by
        {
          have hstep : u + v ≤ 2 * 2 ^ m - 2 := by
            rw [← hcut, ← htwo]
            exact hpair
          exact Nat.lt_of_le_of_lt hstep hstrict
        }
      exact Nat.not_le_of_lt hsmall (Nat.le_of_eq hdouble.symm)
    }
  have hu_le : u ≤ 2 ^ m := by
    {
      have hu_eq : u = 2 * 2 ^ m - v := by
        {
          have hflip : 2 * 2 ^ m = v + u := by
            rw [Nat.add_comm]
            exact hdouble.symm
          exact (Nat.sub_eq_of_eq_add' hflip).symm
        }
      have hsub : 2 * 2 ^ m - v ≤ 2 * 2 ^ m - 2 ^ m :=
        Nat.sub_le_sub_left hv (2 * 2 ^ m)
      have hred : 2 * 2 ^ m - 2 ^ m = 2 ^ m := by
        rw [Nat.two_mul, Nat.add_sub_cancel]
      rw [← hu_eq] at hsub
      rw [hred] at hsub
      exact hsub
    }
  have hqrec_le : 2 ^ m - u ≤ 2 ^ m := Nat.sub_le (2 ^ m) u
  have hv_from : v = 2 * 2 ^ m - u := by
    exact (Nat.sub_eq_of_eq_add' hdouble.symm).symm
  have hv_split : v = 2 ^ m + (2 ^ m - u) := by
    calc
      v = 2 * 2 ^ m - u := hv_from
      _ = 2 ^ m + 2 ^ m - u := by rw [Nat.two_mul]
      _ = 2 ^ m + (2 ^ m - u) := Nat.add_sub_assoc hu_le (2 ^ m)
  have hu_split : u = 2 ^ m - (2 ^ m - u) := (Nat.sub_sub_self hu_le).symm
  have hprodRec : u * v = 2 ^ (2 * m) - (2 ^ m - u) ^ 2 := by
    calc
      u * v = (2 ^ m - (2 ^ m - u)) * (2 ^ m + (2 ^ m - u)) :=
        congrArg₂ Nat.mul hu_split hv_split
      _ = 2 ^ (2 * m) - (2 ^ m - u) ^ 2 :=
        (DifferenceSplit m (2 ^ m - u)).symm
  have hrestore : u * v + q ^ 2 = 2 ^ (2 * m) := by
    rw [hprod]
    exact Nat.sub_add_cancel hq
  have hrestoreRec : u * v + (2 ^ m - u) ^ 2 = 2 ^ (2 * m) := by
    rw [hprodRec]
    exact Nat.sub_add_cancel (SquareOfFactor m (2 ^ m - u) hqrec_le)
  have hqsq : q ^ 2 = (2 ^ m - u) ^ 2 := by
    {
      have hsame : u * v + q ^ 2 = u * v + (2 ^ m - u) ^ 2 := by
        rw [hrestore, hrestoreRec]
      exact Nat.add_left_cancel hsame
    }
  have hqeq : q = 2 ^ m - u := SqEq q (2 ^ m - u) hqsq
  have hgap : (2 ^ m + (2 ^ m - u)) - (2 ^ m - (2 ^ m - u)) = 2 * (2 ^ m - u) :=
    FactorGap m (2 ^ m - u) hqrec_le
  calc
    v - u = (2 ^ m + (2 ^ m - u)) - (2 ^ m - (2 ^ m - u)) :=
      congrArg₂ Nat.sub hv_split hu_split
    _ = 2 * (2 ^ m - u) := hgap
    _ = 2 * q := by rw [← hqeq]

/-- A positive factorisation of `7` with ordered factors is `1 * 7`. -/
theorem SevenFactors (u v : ℕ) (hu : 0 < u) (huv : u ≤ v) (hprod : u * v = 7) :
    u = 1 ∧ v = 7 := by
  have hu2 : u ≤ 2 := by
    {
      by_contra hge
      have hgt : 2 < u := Nat.lt_of_not_ge hge
      have h3 : 3 ≤ u := hgt
      have h9 : 3 * 3 ≤ u * u := Nat.mul_le_mul h3 h3
      have hle : u * u ≤ u * v := Nat.mul_le_mul_left u huv
      rw [hprod] at hle
      have hbad : 3 * 3 ≤ 7 := Nat.le_trans h9 hle
      exact Nat.not_le_of_lt (by decide : (7 : ℕ) < 3 * 3) hbad
    }
  have hcases : u = 1 ∨ u = 2 := by omega
  cases hcases with
  | inl hunit =>
    {
      subst u
      exact ⟨rfl, by simpa using hprod⟩
    }
  | inr htwo =>
    {
      subst u
      omega
    }

/-- A power of two equal to `8` has exponent `3`. -/
theorem PowEqEight (k : ℕ) (h : 2 ^ k = 8) : k = 3 := by
  cases k with
  | zero =>
    {
      exact absurd h (by decide : (2 : ℕ) ^ 0 ≠ 8)
    }
  | succ k1 =>
    {
      cases k1 with
      | zero =>
        {
          exact absurd h (by decide : (2 : ℕ) ^ 1 ≠ 8)
        }
      | succ k2 =>
        {
          cases k2 with
          | zero =>
            {
              exact absurd h (by decide : (2 : ℕ) ^ 2 ≠ 8)
            }
          | succ k3 =>
            {
              cases k3 with
              | zero =>
                {
                  rfl
                }
              | succ k4 =>
                {
                  change 2 ^ (k4 + 1 + 1 + 1 + 1) = 8 at h
                  have h16 : 2 ^ 4 ≤ 2 ^ (k4 + 1 + 1 + 1 + 1) :=
                    Nat.pow_le_pow_right (by decide : (0 : ℕ) < 2) (by omega)
                  rw [h] at h16
                  exact False.elim ((by decide : ¬ ((2 : ℕ) ^ 4 ≤ 8)) h16)
                }
            }
        }
    }

/-- Difference `7` has only the even length `K = 4` and multiplier `3`. -/
theorem DeltaSevenOnly (m q : ℕ) (hq : q ≤ 2 ^ m)
    (hdelta : 2 ^ (2 * m) - q ^ 2 = 7) : m = 2 ∧ q = 3 := by
  have hsplit : (2 ^ m - q) * (2 ^ m + q) = 7 := by
    rw [← DifferenceSplit m q, hdelta]
  have hule : 2 ^ m - q ≤ 2 ^ m + q :=
    Nat.le_trans (Nat.sub_le (2 ^ m) q) (Nat.le_add_right (2 ^ m) q)
  have hpos : 0 < 2 ^ m - q := Nat.pos_of_mul_pos_right (by
    rw [hsplit]
    decide)
  have hpair := SevenFactors (2 ^ m - q) (2 ^ m + q) hpos hule hsplit
  have h8 : 2 ^ (m + 1) = 8 := by
    calc
      2 ^ (m + 1) = (2 ^ m - q) + (2 ^ m + q) := (FactorSum m q hq).symm
      _ = 1 + 7 := by rw [hpair.1, hpair.2]
      _ = 8 := by decide
  have hm1 : m + 1 = 3 := PowEqEight (m + 1) h8
  have hm : m = 2 := by
    {
      have heq : m + 1 = 2 + 1 := by
        rw [hm1]
      exact Nat.add_right_cancel heq
    }
  have h6 : 2 * q = 6 := by
    calc
      2 * q = (2 ^ m + q) - (2 ^ m - q) := (FactorGap m q hq).symm
      _ = 7 - 1 := by rw [hpair.1, hpair.2]
      _ = 6 := by decide
  have hq3 : q = 3 := by
    {
      have heq : 2 * q = 2 * 3 := by
        rw [h6]
      exact Nat.mul_left_cancel (by decide : (0 : ℕ) < 2) heq
    }
  exact ⟨hm, hq3⟩

/-- The checked pair `(q, K) = (3, 4)` has difference `7`. -/
theorem DeltaSeven : 2 ^ 4 - 3 ^ 2 = 7 := by decide

/-- The same pair satisfies `3 ^ 2 + 7 = 2 ^ 4`. -/
theorem ThreeFourCheck : 3 ^ 2 + 7 = 2 ^ 4 := by decide

/-- State `1` realises both letters of `(q, K) = (3, 4)`. -/
theorem UnitCycle : 2 ^ 2 * 1 = 3 * 1 + 1 ∧ 2 ^ 2 * 1 = 3 * 1 + 1 := by
  decide

/-- State `1` lies strictly below the minimum used above. -/
theorem UnitBelowMinimum : ¬ (2 ≤ 1) := by decide

/-- At minimum `1` the endpoint product is equality, not a strict defect. -/
theorem UnitNotStrict : ¬ ((1 * 3 + 1) ^ 2 < 1 ^ 2 * 2 ^ (2 * 2)) := by
  decide

/-- At minimum `1` the endpoint product equals the root. -/
theorem UnitEquality : (1 * 3 + 1) ^ 2 = 1 ^ 2 * 2 ^ (2 * 2) := by decide

/-- Minimum `2` makes the same endpoint product strict. -/
theorem MinimumTwoOpens : (2 * 3 + 1) ^ 2 < 2 ^ 2 * 2 ^ (2 * 2) := by decide

/-- The two comparisons multiply after the state factors are reassociated. -/
theorem PairMul (P Q y x : ℕ) : (P * y) * (Q * x) = P * Q * (y * x) := by
  calc
    (P * y) * (Q * x) = (P * y) * Q * x := by
      rw [← Nat.mul_assoc (P * y) Q x]
    _ = P * (y * Q) * x := by rw [Nat.mul_assoc P y Q]
    _ = P * (Q * y) * x := by rw [Nat.mul_comm y Q]
    _ = P * Q * y * x := by rw [← Nat.mul_assoc P Q y]
    _ = P * Q * (y * x) := by rw [Nat.mul_assoc (P * Q) y x]

/-- The affine step contributes a nonnegative slack `x - m` when `m ≤ x`. -/
theorem AffineSlack (m q x : ℕ) (hmx : m ≤ x) :
    m * (q * x + 1) + (x - m) = (m * q + 1) * x := by
  calc
    m * (q * x + 1) + (x - m) = m * (q * x) + m * 1 + (x - m) := by
      rw [Nat.mul_add]
    _ = m * (q * x) + m + (x - m) := by rw [Nat.mul_one]
    _ = m * q * x + (m + (x - m)) := by
      rw [← Nat.mul_assoc m q x, Nat.add_assoc]
    _ = m * q * x + x := by rw [Nat.add_sub_of_le hmx]
    _ = m * q * x + 1 * x := by rw [Nat.one_mul]
    _ = (m * q + 1) * x := by rw [← Nat.add_mul]

/-- A state at least `m` raises the affine value by at most the enlarged root. -/
theorem AffineCompare (m q x : ℕ) (hmx : m ≤ x) :
    m * (q * x + 1) ≤ (m * q + 1) * x := by
  have hslack : m * (q * x + 1) + (x - m) = (m * q + 1) * x :=
    AffineSlack m q x hmx
  have hle : m * (q * x + 1) ≤ m * (q * x + 1) + (x - m) :=
    Nat.le_add_right (m * (q * x + 1)) (x - m)
  rw [hslack] at hle
  exact hle

/-- The product of the two enlarged steps is the squared root times the states. -/
theorem ProductArrange (m a b x y : ℕ) :
    (m * 2 ^ a * y) * (m * 2 ^ b * x) = m ^ 2 * 2 ^ (a + b) * (y * x) := by
  have h1 : (m * 2 ^ a * y) * (m * 2 ^ b * x) =
      (m * 2 ^ a) * (m * 2 ^ b) * (y * x) :=
    PairMul (m * 2 ^ a) (m * 2 ^ b) y x
  have h2 : (m * 2 ^ a) * (m * 2 ^ b) = m * m * (2 ^ a * 2 ^ b) :=
    PairMul m m (2 ^ a) (2 ^ b)
  have h3 : m * m * (2 ^ a * 2 ^ b) = m ^ 2 * 2 ^ (a + b) := by
    rw [← Nat.pow_two, ← Nat.pow_add]
  have h4 : (m * 2 ^ a) * (m * 2 ^ b) * (y * x) =
      m ^ 2 * 2 ^ (a + b) * (y * x) := by
    rw [h2, h3]
  exact h1.trans h4

/-- Odd states at least `m` force `(m q + 1) ^ 2 ≥ m ^ 2 * 2 ^ (a + b)`. -/
theorem ProductTest (m q x y a b : ℕ) (hmx : m ≤ x) (hmy : m ≤ y)
    (hax : 2 ^ a * y = q * x + 1) (hby : 2 ^ b * x = q * y + 1) :
    m ^ 2 * 2 ^ (a + b) ≤ (m * q + 1) ^ 2 := by
  have hx0 : m * (2 ^ a * y) ≤ (m * q + 1) * x := by
    {
      rw [hax]
      exact AffineCompare m q x hmx
    }
  have hy0 : m * (2 ^ b * x) ≤ (m * q + 1) * y := by
    {
      rw [hby]
      exact AffineCompare m q y hmy
    }
  have hx : m * 2 ^ a * y ≤ (m * q + 1) * x := by
    {
      rw [← Nat.mul_assoc] at hx0
      exact hx0
    }
  have hy : m * 2 ^ b * x ≤ (m * q + 1) * y := by
    {
      rw [← Nat.mul_assoc] at hy0
      exact hy0
    }
  have hmul : (m * 2 ^ a * y) * (m * 2 ^ b * x) ≤
      ((m * q + 1) * x) * ((m * q + 1) * y) := Nat.mul_le_mul hx hy
  have hleft : (m * 2 ^ a * y) * (m * 2 ^ b * x) =
      m ^ 2 * 2 ^ (a + b) * (x * y) := by
    {
      rw [ProductArrange, Nat.mul_comm y x]
    }
  have hright : ((m * q + 1) * x) * ((m * q + 1) * y) =
      (m * q + 1) ^ 2 * (x * y) := by
    {
      rw [PairMul (m * q + 1) (m * q + 1) x y, ← Nat.pow_two]
    }
  have hxpos : 0 < x := by
    {
      have hgt : 0 < 2 ^ b * x := by
        {
          rw [hby]
          exact Nat.zero_lt_succ (q * y)
        }
      exact Nat.pos_of_mul_pos_left hgt
    }
  have hypos : 0 < y := by
    {
      have hgt : 0 < 2 ^ a * y := by
        {
          rw [hax]
          exact Nat.zero_lt_succ (q * x)
        }
      exact Nat.pos_of_mul_pos_left hgt
    }
  have hxy : 0 < x * y := by
    {
      have hy1 : 1 ≤ y := Nat.one_le_of_lt hypos
      have hmul : x * 1 ≤ x * y := Nat.mul_le_mul_left x hy1
      rw [Nat.mul_one] at hmul
      exact Nat.lt_of_lt_of_le hxpos hmul
    }
  have hscaled : m ^ 2 * 2 ^ (a + b) * (x * y) ≤ (m * q + 1) ^ 2 * (x * y) := by
    {
      rw [← hleft, ← hright]
      exact hmul
    }
  exact Nat.le_of_mul_le_mul_right hscaled hxy

/-- The two letters close by `2 ^ (a + b) * x = q ^ 2 * x + (q + 2 ^ a)`. -/
theorem TwoLetterClosure (q x y a b : ℕ) (hax : 2 ^ a * y = q * x + 1)
    (hby : 2 ^ b * x = q * y + 1) :
    2 ^ (a + b) * x = q ^ 2 * x + (q + 2 ^ a) := by
  have hswap : 2 ^ a * (q * y) = q * (2 ^ a * y) := by
    calc
      2 ^ a * (q * y) = 2 ^ a * q * y := by rw [Nat.mul_assoc (2 ^ a) q y]
      _ = q * 2 ^ a * y := by rw [Nat.mul_comm (2 ^ a) q]
      _ = q * (2 ^ a * y) := by rw [← Nat.mul_assoc q (2 ^ a) y]
  calc
    2 ^ (a + b) * x = 2 ^ a * 2 ^ b * x := by rw [Nat.pow_add]
    _ = 2 ^ a * (2 ^ b * x) := by rw [Nat.mul_assoc (2 ^ a) (2 ^ b) x]
    _ = 2 ^ a * (q * y + 1) := by rw [hby]
    _ = 2 ^ a * (q * y) + 2 ^ a * 1 := by rw [Nat.mul_add]
    _ = 2 ^ a * (q * y) + 2 ^ a := by rw [Nat.mul_one]
    _ = q * (2 ^ a * y) + 2 ^ a := by rw [hswap]
    _ = q * (q * x + 1) + 2 ^ a := by rw [hax]
    _ = q * (q * x) + q * 1 + 2 ^ a := by rw [Nat.mul_add]
    _ = q * q * x + q + 2 ^ a := by rw [← Nat.mul_assoc q q x, Nat.mul_one]
    _ = q ^ 2 * x + q + 2 ^ a := by rw [← Nat.pow_two]
    _ = q ^ 2 * x + (q + 2 ^ a) := by rw [Nat.add_assoc]

/-- A positive two-step cycle forces the multiplier square below `2 ^ (a + b)`. -/
theorem WindowFromCycle (q x y a b : ℕ) (hax : 2 ^ a * y = q * x + 1)
    (hby : 2 ^ b * x = q * y + 1) : q ^ 2 < 2 ^ (a + b) := by
  have hclose : 2 ^ (a + b) * x = q ^ 2 * x + (q + 2 ^ a) :=
    TwoLetterClosure q x y a b hax hby
  have hbase : 1 ≤ 2 ^ a := Nat.one_le_of_lt (Nat.two_pow_pos a)
  have hoffset : 1 ≤ q + 2 ^ a := Nat.le_trans hbase (Nat.le_add_left (2 ^ a) q)
  have hle : q ^ 2 * x + 1 ≤ 2 ^ (a + b) * x := by
    {
      have hstep : q ^ 2 * x + 1 ≤ q ^ 2 * x + (q + 2 ^ a) :=
        Nat.add_le_add_left hoffset (q ^ 2 * x)
      exact Nat.le_trans hstep (Nat.le_of_eq hclose.symm)
    }
  have hstrict : q ^ 2 * x < 2 ^ (a + b) * x := Nat.lt_of_add_one_le hle
  by_contra hge
  have hbig : 2 ^ (a + b) ≤ q ^ 2 := Nat.le_of_not_lt hge
  have hmul : 2 ^ (a + b) * x ≤ q ^ 2 * x := Nat.mul_le_mul_right x hbig
  exact Nat.not_lt_of_le hmul hstrict

/-- Even division totals are impossible above state `1`, for every natural multiplier. -/
theorem EvenTotalNoCycle (t μ q x y a b : ℕ) (hμ : 2 ≤ μ)
    (hk : a + b = 2 * t) (hmx : μ ≤ x) (hmy : μ ≤ y)
    (hax : 2 ^ a * y = q * x + 1) (hby : 2 ^ b * x = q * y + 1) : False := by
  have hwindow : q ^ 2 < 2 ^ (a + b) := WindowFromCycle q x y a b hax hby
  have hwindowK : q ^ 2 < 2 ^ (2 * t) := by
    {
      rw [hk] at hwindow
      exact hwindow
    }
  have hodd : q ≤ 2 ^ t - 1 := SquareWindowBound t q hwindowK
  have hceil : (μ * q + 1) ^ 2 < μ ^ 2 * 2 ^ (2 * t) :=
    ProductCeiling t μ q hμ hodd
  have htest : μ ^ 2 * 2 ^ (a + b) ≤ (μ * q + 1) ^ 2 :=
    ProductTest μ q x y a b hmx hmy hax hby
  have htestK : μ ^ 2 * 2 ^ (2 * t) ≤ (μ * q + 1) ^ 2 := by
    {
      rw [hk] at htest
      exact htest
    }
  exact Nat.not_lt_of_le htestK hceil

/-- The even-total obstruction specialises to the raw map with an odd multiplier. -/
theorem EvenLengthNoCycle (t μ q x y a b : ℕ) (_ht : 1 ≤ t) (hμ : 2 ≤ μ)
    (_hq : IsOdd q) (hk : a + b = 2 * t) (hmx : μ ≤ x) (hmy : μ ≤ y)
    (hax : 2 ^ a * y = q * x + 1) (hby : 2 ^ b * x = q * y + 1) : False := by
  exact EvenTotalNoCycle t μ q x y a b hμ hk hmx hmy hax hby

end GeneralizedCollatz.ReverseBound
