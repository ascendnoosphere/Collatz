-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Source weight `ρ(n) = 1/(n(n+1))`.
The denominator vanishes at `n = 0`, so the source law is used for `n ≥ 1`. -/
def Rho (n : ℕ) : ℚ :=
  (1 : ℚ) / ((n * (n + 1) : ℕ) : ℚ)

/-- Source weight `μ(n) = 2/(n(n-1))`.
The denominator vanishes for `n < 2`, so the source law is used for `n ≥ 2`. -/
def Mu (n : ℕ) : ℚ :=
  (2 : ℚ) / ((n * (n - 1) : ℕ) : ℚ)

/-- `ρ(n)` is positive for every positive integer. -/
theorem RhoPos {n : ℕ} (hn : 1 ≤ n) : 0 < Rho n := by
  unfold Rho
  have hn0 : 0 < n := by omega
  have hnp : 0 < n + 1 := by omega
  have hden : (0 : ℚ) < ((n * (n + 1) : ℕ) : ℚ) :=
    Nat.cast_pos.mpr (Nat.mul_pos hn0 hnp)
  exact div_pos one_pos hden

/-- `μ(n)` is positive for every integer `n ≥ 2`. -/
theorem MuPos {n : ℕ} (hn : 2 ≤ n) : 0 < Mu n := by
  unfold Mu
  have hn0 : 0 < n := by omega
  have hp : 0 < n - 1 := by omega
  have hden : (0 : ℚ) < ((n * (n - 1) : ℕ) : ℚ) :=
    Nat.cast_pos.mpr (Nat.mul_pos hn0 hp)
  exact div_pos (by norm_num) hden

/-- Telescoping step `ρ(n) = 1/n - 1/(n+1)` for `n ≥ 1`. -/
theorem RhoTelescope {n : ℕ} (hn : 1 ≤ n) :
    Rho n = (1 : ℚ) / (n : ℚ) - (1 : ℚ) / ((n + 1 : ℕ) : ℚ) := by
  have hn0 : n ≠ 0 := by omega
  have hb : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hd : ((n + 1 : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hsub := div_sub_div (1 : ℚ) (1 : ℚ) hb hd
  have hnum :
      (1 : ℚ) * ((n + 1 : ℕ) : ℚ) - (n : ℚ) * 1 = 1 := by
    rw [one_mul, mul_one, Nat.cast_add, Nat.cast_one]
    ring
  have hden :
      (n : ℚ) * ((n + 1 : ℕ) : ℚ) =
        ((n * (n + 1) : ℕ) : ℚ) := by
    rw [← Nat.cast_mul]
  unfold Rho
  rw [hsub, hnum, hden]

/-- Telescoping step `μ(n) = 2/(n-1) - 2/n` for `n ≥ 2`. -/
theorem MuTelescope {n : ℕ} (hn : 2 ≤ n) :
    Mu n =
      (2 : ℚ) / ((n - 1 : ℕ) : ℚ) - (2 : ℚ) / (n : ℚ) := by
  have h1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hp0 : n - 1 ≠ 0 := by omega
  have hb : ((n - 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp0
  have hd : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hsub := div_sub_div (2 : ℚ) (2 : ℚ) hb hd
  have hnum :
      (2 : ℚ) * (n : ℚ) - ((n - 1 : ℕ) : ℚ) * 2 = 2 := by
    rw [Nat.cast_sub h1]
    ring
  have hden :
      ((n - 1 : ℕ) : ℚ) * (n : ℚ) =
        ((n * (n - 1) : ℕ) : ℚ) := by
    rw [mul_comm, ← Nat.cast_mul]
  unfold Mu
  rw [hsub, hnum, hden]

/-- Closed form `R/(R+1) = 1 - 1/(R+1)`. -/
theorem RhoClosed (R : ℕ) :
    (R : ℚ) / ((R + 1 : ℕ) : ℚ) =
      1 - (1 : ℚ) / ((R + 1 : ℕ) : ℚ) := by
  have hd : ((R + 1 : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero R)
  have hsub :=
    sub_div' (a := (1 : ℚ)) (b := (1 : ℚ))
      (c := ((R + 1 : ℕ) : ℚ)) hd
  have hnum : (1 : ℚ) * ((R + 1 : ℕ) : ℚ) - 1 = (R : ℚ) := by
    rw [one_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [hnum] at hsub
  exact hsub.symm

/-- Partial sum `∑_{n=1}^R ρ(n) = R/(R+1)`. -/
theorem RhoPartialSum (R : ℕ) :
    ∑ k ∈ Finset.range R, Rho (k + 1) =
      (R : ℚ) / ((R + 1 : ℕ) : ℚ) := by
  induction R with
  | zero =>
    {
      rw [Finset.sum_range_zero]
      have hden : ((0 + 1 : ℕ) : ℚ) = 1 := by norm_num
      rw [hden, Nat.cast_zero, zero_div]
    }
  | succ R ih =>
    {
      rw [Finset.sum_range_succ, ih]
      have hstep := RhoTelescope (n := R + 1) (by omega)
      have hidx : (R + 1) + 1 = R + 2 := by omega
      rw [hidx] at hstep
      rw [hstep]
      have hd : ((R + 1 : ℕ) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.succ_ne_zero R)
      have hcast : (R : ℚ) + 1 = ((R + 1 : ℕ) : ℚ) := by
        rw [Nat.cast_add, Nat.cast_one]
      have hjoin :
          (R : ℚ) / ((R + 1 : ℕ) : ℚ) +
              ((1 : ℚ) / ((R + 1 : ℕ) : ℚ) -
                (1 : ℚ) / ((R + 2 : ℕ) : ℚ)) =
            (1 : ℚ) - (1 : ℚ) / ((R + 2 : ℕ) : ℚ) := by
        calc
          (R : ℚ) / ((R + 1 : ℕ) : ℚ) +
                ((1 : ℚ) / ((R + 1 : ℕ) : ℚ) -
                  (1 : ℚ) / ((R + 2 : ℕ) : ℚ))
              = ((R : ℚ) / ((R + 1 : ℕ) : ℚ) +
                  (1 : ℚ) / ((R + 1 : ℕ) : ℚ)) -
                (1 : ℚ) / ((R + 2 : ℕ) : ℚ) := by
                abel
          _ = (((R : ℚ) + 1) / ((R + 1 : ℕ) : ℚ)) -
                (1 : ℚ) / ((R + 2 : ℕ) : ℚ) := by
                rw [← add_div]
          _ = (((R + 1 : ℕ) : ℚ) / ((R + 1 : ℕ) : ℚ)) -
                (1 : ℚ) / ((R + 2 : ℕ) : ℚ) := by
                rw [hcast]
          _ = (1 : ℚ) - (1 : ℚ) / ((R + 2 : ℕ) : ℚ) := by
                rw [div_self hd]
      rw [hjoin]
      have hc := RhoClosed (R + 1)
      rw [hidx] at hc
      exact hc.symm
    }

/-- The complementary mass after `1, …, R` is the tail `1/(R+1)`. -/
theorem RhoComplement (R : ℕ) :
    (1 : ℚ) / ((R + 1 : ℕ) : ℚ) =
      1 - ∑ k ∈ Finset.range R, Rho (k + 1) := by
  rw [RhoPartialSum, RhoClosed]
  abel

/-- Partial sum `∑_{n=3}^R μ(n) = 1 - 2/R` for `R ≥ 2`.
The sum is empty at `R = 2`, and both sides are zero. -/
theorem MuPartialSum {R : ℕ} (hR : 2 ≤ R) :
    ∑ k ∈ Finset.range (R - 2), Mu (k + 3) =
      1 - (2 : ℚ) / (R : ℚ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hR
  induction d with
  | zero =>
    {
      have hlen : (2 + 0) - 2 = 0 := by omega
      rw [hlen, Finset.sum_range_zero]
      have hden : ((2 + 0 : ℕ) : ℚ) = 2 := by norm_num
      rw [hden]
      norm_num
    }
  | succ d ih =>
    {
      have hlenR : (2 + d) - 2 = d := by omega
      rw [hlenR] at ih
      have hlen : (2 + (d + 1)) - 2 = d + 1 := by omega
      have hle : 2 ≤ 2 + d := Nat.le_add_right 2 d
      rw [hlen, Finset.sum_range_succ, ih hle]
      have hmu := MuTelescope (n := d + 3) (by omega)
      have hpred : (d + 3) - 1 = 2 + d := by omega
      rw [hmu, hpred]
      have hthree : d + 3 = 2 + (d + 1) := by omega
      rw [hthree]
      abel
    }

/-- The complementary mass after `3, …, R` is the tail `2/R`. -/
theorem MuComplement {R : ℕ} (hR : 2 ≤ R) :
    (2 : ℚ) / (R : ℚ) =
      1 - ∑ k ∈ Finset.range (R - 2), Mu (k + 3) := by
  rw [MuPartialSum hR]
  abel

/-- Window `∑_{n=R+1}^N ρ(n) = 1/(R+1) - 1/(N+1)` for `R ≤ N`. -/
theorem RhoWindow {R N : ℕ} (hN : R ≤ N) :
    ∑ j ∈ Finset.range (N - R), Rho (j + R + 1) =
      (1 : ℚ) / ((R + 1 : ℕ) : ℚ) -
        (1 : ℚ) / ((N + 1 : ℕ) : ℚ) := by
  have hsplit :=
    Finset.sum_range_add (fun k => Rho (k + 1)) R (N - R)
  have hlen : R + (N - R) = N := by omega
  rw [hlen] at hsplit
  have hfun :
      (fun j => Rho (R + j + 1)) =
        fun j => Rho (j + R + 1) := by
    funext j
    have hcomm : R + j + 1 = j + R + 1 := by omega
    rw [hcomm]
  rw [hfun] at hsplit
  have hW :
      ∑ j ∈ Finset.range (N - R), Rho (j + R + 1) =
        (∑ k ∈ Finset.range N, Rho (k + 1)) -
          ∑ k ∈ Finset.range R, Rho (k + 1) := by
    calc
      ∑ j ∈ Finset.range (N - R), Rho (j + R + 1)
          = (∑ k ∈ Finset.range R, Rho (k + 1)) +
              ∑ j ∈ Finset.range (N - R), Rho (j + R + 1) -
              ∑ k ∈ Finset.range R, Rho (k + 1) := by
            abel
      _ = (∑ k ∈ Finset.range N, Rho (k + 1)) -
            ∑ k ∈ Finset.range R, Rho (k + 1) := by
            rw [← hsplit]
  rw [hW, RhoPartialSum, RhoPartialSum, RhoClosed, RhoClosed]
  abel

/-- Window `∑_{n=R+1}^N μ(n) = 2/R - 2/N` for `2 ≤ R ≤ N`. -/
theorem MuWindow {R N : ℕ} (hR : 2 ≤ R) (hN : R ≤ N) :
    ∑ j ∈ Finset.range (N - R), Mu (j + R + 1) =
      (2 : ℚ) / (R : ℚ) - (2 : ℚ) / (N : ℚ) := by
  have hNge : 2 ≤ N := le_trans hR hN
  have hsplit :=
    Finset.sum_range_add (fun k => Mu (k + 3)) (R - 2) (N - R)
  have hlen : (R - 2) + (N - R) = N - 2 := by omega
  rw [hlen] at hsplit
  have hfun :
      (fun j => Mu ((R - 2) + j + 3)) =
        fun j => Mu (j + R + 1) := by
    funext j
    have hcomm : (R - 2) + j + 3 = j + R + 1 := by omega
    rw [hcomm]
  rw [hfun] at hsplit
  have hW :
      ∑ j ∈ Finset.range (N - R), Mu (j + R + 1) =
        (∑ k ∈ Finset.range (N - 2), Mu (k + 3)) -
          ∑ k ∈ Finset.range (R - 2), Mu (k + 3) := by
    calc
      ∑ j ∈ Finset.range (N - R), Mu (j + R + 1)
          = (∑ k ∈ Finset.range (R - 2), Mu (k + 3)) +
              ∑ j ∈ Finset.range (N - R), Mu (j + R + 1) -
              ∑ k ∈ Finset.range (R - 2), Mu (k + 3) := by
            abel
      _ = (∑ k ∈ Finset.range (N - 2), Mu (k + 3)) -
            ∑ k ∈ Finset.range (R - 2), Mu (k + 3) := by
            rw [← hsplit]
  rw [hW, MuPartialSum hNge, MuPartialSum hR]
  abel

/-- Common-denominator identity `(p x)/(q y) = (p/q)(x/y)`. -/
theorem ScaleDiv {p q x y : ℚ} (hq : q ≠ 0) (hy : y ≠ 0) :
    (p * x) / (q * y) = (p / q) * (x / y) := by
  have hden : q * y ≠ 0 := mul_ne_zero hq hy
  refine (div_eq_iff_mul_eq hden).mpr ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hre :
      (p * q⁻¹) * (x * y⁻¹) * (q * y) =
        p * (q * q⁻¹) * x * (y * y⁻¹) := by
    ring
  rw [hre, mul_inv_cancel₀ hq, mul_inv_cancel₀ hy, mul_one, mul_one]

/-- The factor `4/2` collapses to `2`. -/
theorem FourOverTwo {a b : ℚ} (hb : b ≠ 0) :
    (4 * a) / (2 * b) = 2 * (a / b) := by
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hco : (4 : ℚ) / 2 = 2 := by norm_num
  calc
    (4 * a) / (2 * b) = ((4 : ℚ) / 2) * (a / b) :=
      ScaleDiv h2 hb
    _ = 2 * (a / b) := by rw [hco]

/-- The factor `2/4` collapses to division by `2`. -/
theorem TwoOverFour {a b : ℚ} (hb : b ≠ 0) :
    (2 * a) / (4 * b) = (a / b) / 2 := by
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  have hco : (2 : ℚ) / 4 = 1 / 2 := by norm_num
  have hcomm : (1 : ℚ) / 2 * (a / b) = (a / b) / 2 := by
    rw [mul_comm, one_div, ← div_eq_mul_inv]
  calc
    (2 * a) / (4 * b) = ((2 : ℚ) / 4) * (a / b) :=
      ScaleDiv h4 hb
    _ = ((1 : ℚ) / 2) * (a / b) := by rw [hco]
    _ = (a / b) / 2 := hcomm

/-- Ratio `μ(n)/ρ(n) = 2(n+1)/(n-1)` for every integer `n ≥ 3`. -/
theorem MuDivRho {n : ℕ} (hn : 3 ≤ n) :
    Mu n / Rho n = 2 * ((n : ℚ) + 1) / ((n : ℚ) - 1) := by
  have h1 : 1 ≤ n := by omega
  have hp0 : n - 1 ≠ 0 := by omega
  have hsub : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := Nat.cast_sub h1
  have hpred : (n : ℚ) - 1 ≠ 0 := by
    rw [← hsub]
    exact Nat.cast_ne_zero.mpr hp0
  have hnp : (n : ℚ) + 1 ≠ 0 := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hRho0 : Rho n ≠ 0 := ne_of_gt (RhoPos (by omega))
  have hMuSide : Mu n * ((n : ℚ) - 1) = (2 : ℚ) / (n : ℚ) := by
    unfold Mu
    have hcast :
        ((n * (n - 1) : ℕ) : ℚ) =
          (n : ℚ) * ((n : ℚ) - 1) := by
      rw [Nat.cast_mul, hsub]
    rw [hcast, div_mul_eq_mul_div₀]
    exact mul_div_mul_right (2 : ℚ) (n : ℚ) hpred
  have hRhoSide :
      Rho n * (2 * ((n : ℚ) + 1)) = (2 : ℚ) / (n : ℚ) := by
    unfold Rho
    have hcast :
        ((n * (n + 1) : ℕ) : ℚ) =
          (n : ℚ) * ((n : ℚ) + 1) := by
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [hcast, div_mul_eq_mul_div₀, one_mul]
    exact mul_div_mul_right (2 : ℚ) (n : ℚ) hnp
  have hmul :
      Mu n * ((n : ℚ) - 1) =
        Rho n * (2 * ((n : ℚ) + 1)) := by
    rw [hMuSide, hRhoSide]
  have hquot :
      Mu n =
        Rho n * (2 * ((n : ℚ) + 1) / ((n : ℚ) - 1)) := by
    have hdiv :
        Mu n =
          (Rho n * (2 * ((n : ℚ) + 1))) / ((n : ℚ) - 1) :=
      (eq_div_iff hpred).mpr hmul
    have hassoc :
        (Rho n * (2 * ((n : ℚ) + 1))) / ((n : ℚ) - 1) =
          Rho n * (2 * ((n : ℚ) + 1) / ((n : ℚ) - 1)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    rw [hdiv, hassoc]
  rw [hquot]
  exact mul_div_cancel_left₀ _ hRho0

/-- The scalar ratio lies between `2` and `4` for every integer `n ≥ 3`. -/
theorem RatioBounds {n : ℕ} (hn : 3 ≤ n) :
    (2 : ℚ) ≤ 2 * ((n : ℚ) + 1) / ((n : ℚ) - 1) ∧
      2 * ((n : ℚ) + 1) / ((n : ℚ) - 1) ≤ 4 := by
  have h1 : 1 ≤ n := by omega
  have hpos : 0 < (n : ℚ) - 1 := by
    have hp : 0 < n - 1 := by omega
    have hpQ : (0 : ℚ) < ((n - 1 : ℕ) : ℚ) := Nat.cast_pos.mpr hp
    rwa [Nat.cast_sub h1] at hpQ
  constructor
  · {
      rw [le_div_iff₀ hpos]
      linarith
    }
  · {
      rw [div_le_iff₀ hpos]
      have hnQ : (3 : ℚ) ≤ (n : ℚ) := Nat.cast_le.mpr hn
      linarith
    }

/-- Classical comparison `2ρ(n) ≤ μ(n) ≤ 4ρ(n)` for every integer `n ≥ 3`. -/
theorem TwoRhoLeMuLeFourRho {n : ℕ} (hn : 3 ≤ n) :
    2 * Rho n ≤ Mu n ∧ Mu n ≤ 4 * Rho n := by
  have hrat := MuDivRho hn
  have hbnd := RatioBounds hn
  have hpos := RhoPos (le_trans (by decide : (1 : ℕ) ≤ 3) hn)
  have hle2 : (2 : ℚ) ≤ Mu n / Rho n := by
    rw [hrat]
    exact hbnd.1
  have hle4 : Mu n / Rho n ≤ 4 := by
    rw [hrat]
    exact hbnd.2
  constructor
  · {
      rw [le_div_iff₀ hpos] at hle2
      exact hle2
    }
  · {
      rw [div_le_iff₀ hpos] at hle4
      exact hle4
    }

/-- The upper constant is attained at `n = 3`: `μ(3) = 4ρ(3)`. -/
theorem MuEqFourRhoAtThree : Mu 3 = 4 * Rho 3 := by
  have hρden : (3 * (3 + 1) : ℕ) = 12 := by decide
  have hμden : (3 * (3 - 1) : ℕ) = 6 := by decide
  unfold Rho Mu
  rw [hρden, hμden]
  norm_num

/-- The upper bound fails at `n = 2`: `4ρ(2) < μ(2)`. -/
theorem FourRhoLtMuAtTwo : 4 * Rho 2 < Mu 2 := by
  have hρden : (2 * (2 + 1) : ℕ) = 6 := by decide
  have hμden : (2 * (2 - 1) : ℕ) = 2 := by decide
  unfold Rho Mu
  rw [hρden, hμden]
  norm_num

/-- Summing the pointwise comparison preserves it on any finite set of
integers at least `3`. -/
theorem SameLabelMassComparison (S : Finset ℕ)
    (hS : ∀ n ∈ S, 3 ≤ n) :
    2 * ∑ n ∈ S, Rho n ≤ ∑ n ∈ S, Mu n ∧
      ∑ n ∈ S, Mu n ≤ 4 * ∑ n ∈ S, Rho n := by
  have hlo : ∀ n ∈ S, 2 * Rho n ≤ Mu n := by
    intro n hn
    exact (TwoRhoLeMuLeFourRho (hS n hn)).1
  have hhi : ∀ n ∈ S, Mu n ≤ 4 * Rho n := by
    intro n hn
    exact (TwoRhoLeMuLeFourRho (hS n hn)).2
  have hsumLo := Finset.sum_le_sum hlo
  have hsumHi := Finset.sum_le_sum hhi
  rw [← Finset.mul_sum] at hsumLo
  rw [← Finset.mul_sum] at hsumHi
  exact ⟨hsumLo, hsumHi⟩

/-- Quotient of a captured mass by an unresolved mass.
This is only a quotient of the two masses supplied to it. -/
def CaptureFraction (captured unresolved : ℚ) : ℚ :=
  captured / unresolved

/-- If both masses lie in the factor interval and the unresolved `ρ` mass
is positive, the quotients differ by a factor of at most `2`.
No orbit is asserted to meet a target. -/
theorem CaptureFractionFactor
    {cRho uRho cMu uMu : ℚ}
    (hc0 : 0 ≤ cRho) (hu0 : 0 < uRho)
    (hc : 2 * cRho ≤ cMu ∧ cMu ≤ 4 * cRho)
    (hu : 2 * uRho ≤ uMu ∧ uMu ≤ 4 * uRho) :
    CaptureFraction cRho uRho / 2 ≤ CaptureFraction cMu uMu ∧
      CaptureFraction cMu uMu ≤
        2 * CaptureFraction cRho uRho := by
  have htwo : (0 : ℚ) < 2 := by norm_num
  have huMu : 0 < uMu := lt_of_lt_of_le (mul_pos htwo hu0) hu.1
  have htwoRho : 0 < 2 * uRho := mul_pos htwo hu0
  have hnum2 : 0 ≤ 2 * cRho := mul_nonneg (by norm_num) hc0
  have hnum4 : 0 ≤ 4 * cRho := mul_nonneg (by norm_num) hc0
  unfold CaptureFraction
  constructor
  · {
      have hLowNum : (2 * cRho) / uMu ≤ cMu / uMu :=
        div_le_div_of_nonneg_right hc.1 (le_of_lt huMu)
      have hDen : (2 * cRho) / (4 * uRho) ≤ (2 * cRho) / uMu :=
        div_le_div_of_nonneg_left hnum2 huMu hu.2
      have hScale := TwoOverFour (a := cRho) (b := uRho) (ne_of_gt hu0)
      calc
        (cRho / uRho) / 2 = (2 * cRho) / (4 * uRho) := by
          exact hScale.symm
        _ ≤ (2 * cRho) / uMu := hDen
        _ ≤ cMu / uMu := hLowNum
    }
  · {
      have hUpNum : cMu / uMu ≤ (4 * cRho) / uMu :=
        div_le_div_of_nonneg_right hc.2 (le_of_lt huMu)
      have hDen : (4 * cRho) / uMu ≤ (4 * cRho) / (2 * uRho) :=
        div_le_div_of_nonneg_left hnum4 htwoRho hu.1
      have hScale := FourOverTwo (a := cRho) (b := uRho) (ne_of_gt hu0)
      calc
        cMu / uMu ≤ (4 * cRho) / uMu := hUpNum
        _ ≤ (4 * cRho) / (2 * uRho) := hDen
        _ = 2 * (cRho / uRho) := hScale
    }

/-- The factor-`2` quotient comparison on two finite sets of integers
at least `3`, when the unresolved `ρ` mass is positive.
Disjointness of the sets is not used and is not claimed. -/
theorem CommonLabelFraction (C U : Finset ℕ)
    (hC : ∀ n ∈ C, 3 ≤ n) (hU : ∀ n ∈ U, 3 ≤ n)
    (hpos : 0 < ∑ n ∈ U, Rho n) :
    CaptureFraction (∑ n ∈ C, Rho n) (∑ n ∈ U, Rho n) / 2 ≤
        CaptureFraction (∑ n ∈ C, Mu n) (∑ n ∈ U, Mu n) ∧
      CaptureFraction (∑ n ∈ C, Mu n) (∑ n ∈ U, Mu n) ≤
        2 * CaptureFraction (∑ n ∈ C, Rho n) (∑ n ∈ U, Rho n) := by
  have h13 : (1 : ℕ) ≤ 3 := by decide
  have hc0 : 0 ≤ ∑ n ∈ C, Rho n := by
    refine Finset.sum_nonneg ?_
    intro n hn
    exact le_of_lt (RhoPos (le_trans h13 (hC n hn)))
  exact CaptureFractionFactor hc0 hpos
    (SameLabelMassComparison C hC) (SameLabelMassComparison U hU)

/-- The weight `+1` at `3` and `-1` at `4` breaks the upper comparison:
`4(ρ(3)-ρ(4)) < μ(3)-μ(4)`. -/
theorem SignedUpperBoundFails :
    4 * (Rho 3 - Rho 4) < Mu 3 - Mu 4 := by
  unfold Rho Mu
  norm_num

/-- The swapped signs break the lower comparison:
`μ(4)-μ(3) < 2(ρ(4)-ρ(3))`. -/
theorem SignedLowerBoundFails :
    Mu 4 - Mu 3 < 2 * (Rho 4 - Rho 3) := by
  unfold Rho Mu
  norm_num

end GeneralizedCollatz
