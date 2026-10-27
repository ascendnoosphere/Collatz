-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Forward orbit. The zeroth state is the seed. -/
def Orbit (T : ℤ → ℤ) : ℕ → ℤ → ℤ
  | 0, n => n
  | k + 1, n => Orbit T k (T n)

/-- The zeroth iterate is the seed. -/
@[simp] theorem OrbitZero (T : ℤ → ℤ) (n : ℤ) : Orbit T 0 n = n := rfl

/-- A positive iterate applies the map and then the remaining orbit. -/
@[simp] theorem OrbitSucc (T : ℤ → ℤ) (k : ℕ) (n : ℤ) :
    Orbit T (k + 1) n = Orbit T k (T n) := rfl

/-- Forward orbit of a map on the natural numbers. -/
def OrbitNat (T : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => OrbitNat T k (T n)

/-- The zeroth natural iterate is the seed. -/
@[simp] theorem OrbitNatZero (T : ℕ → ℕ) (n : ℕ) : OrbitNat T 0 n = n := rfl

/-- A positive natural iterate applies the map and then the remaining orbit. -/
@[simp] theorem OrbitNatSucc (T : ℕ → ℕ) (k : ℕ) (n : ℕ) :
    OrbitNat T (k + 1) n = OrbitNat T k (T n) := rfl

/-- Uniform half-contraction outside radius `R`: every integer strictly outside
the radius is sent to an integer of at most half the absolute value. -/
def UniformHalfContraction (R : ℕ) (T : ℤ → ℤ) : Prop :=
  ∀ n : ℤ, R < n.natAbs → 2 * (T n).natAbs ≤ n.natAbs

/-- Absolute value strictly decreases while a half-contraction stays outside
the radius, so every integer orbit enters the radius in at most `|n|` steps. -/
theorem UniformHalfEntry (R : ℕ) (T : ℤ → ℤ)
    (hT : UniformHalfContraction R T) (n : ℤ) :
    ∃ k : ℕ, k ≤ n.natAbs ∧ (Orbit T k n).natAbs ≤ R := by
  suffices ∀ m : ℕ, ∀ x : ℤ, x.natAbs = m →
      ∃ k : ℕ, k ≤ m ∧ (Orbit T k x).natAbs ≤ R from
    this n.natAbs n rfl
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    {
      intro x hx
      cases Nat.lt_or_ge R x.natAbs with
      | inr hin =>
        {
          exact ⟨0, Nat.zero_le m, by simpa [OrbitZero] using hin⟩
        }
      | inl hout =>
        {
          have hhalf : 2 * (T x).natAbs ≤ x.natAbs := hT x hout
          have hpos : 0 < x.natAbs := Nat.lt_of_le_of_lt (Nat.zero_le R) hout
          -- Twice the image is at most the input, and the input is positive,
          -- so the image is a strictly smaller natural number.
          have hlt : (T x).natAbs < x.natAbs := by
            have htwice : x.natAbs < 2 * x.natAbs := by
              rw [Nat.two_mul]
              exact Nat.lt_add_of_pos_right hpos
            have hmul : 2 * (T x).natAbs < 2 * x.natAbs :=
              lt_of_le_of_lt hhalf htwice
            exact Nat.lt_of_mul_lt_mul_left hmul
          have hm : (T x).natAbs < m := by
            rw [← hx]
            exact hlt
          obtain ⟨k, hk, hent⟩ := ih (T x).natAbs hm (T x) rfl
          have hk1 : k + 1 ≤ m := by
            have hsucc : k + 1 ≤ (T x).natAbs + 1 := Nat.succ_le_succ hk
            have hpred : (T x).natAbs + 1 ≤ m := Nat.succ_le_of_lt hm
            exact Nat.le_trans hsucc hpred
          exact ⟨k + 1, hk1, by simpa [OrbitSucc] using hent⟩
        }
    }

/-- If `|n| < 2^h (R+1)`, a half-contraction enters the radius in at most `h`
steps. This is the halving form of a finite entry budget. -/
theorem UniformHalfBudget (R : ℕ) (T : ℤ → ℤ)
    (hT : UniformHalfContraction R T) (h : ℕ) (n : ℤ)
    (hn : n.natAbs < 2 ^ h * (R + 1)) :
    ∃ k : ℕ, k ≤ h ∧ (Orbit T k n).natAbs ≤ R := by
  induction h generalizing n with
  | zero =>
    {
      have hlt : n.natAbs < R + 1 := by simpa using hn
      exact ⟨0, Nat.zero_le 0, by simpa [OrbitZero] using Nat.le_of_lt_succ hlt⟩
    }
  | succ h ih =>
    {
      cases Nat.lt_or_ge R n.natAbs with
      | inr hin =>
        {
          exact ⟨0, Nat.zero_le _, by simpa [OrbitZero] using hin⟩
        }
      | inl hout =>
        {
          have hhalf : 2 * (T n).natAbs ≤ n.natAbs := hT n hout
          have hpow : 2 ^ (h + 1) * (R + 1) = 2 * (2 ^ h * (R + 1)) := by
            rw [Nat.pow_succ, Nat.mul_comm (2 ^ h) 2, Nat.mul_assoc]
          have hbig : n.natAbs < 2 * (2 ^ h * (R + 1)) := by
            rw [← hpow]
            exact hn
          have hmul : 2 * (T n).natAbs < 2 * (2 ^ h * (R + 1)) :=
            lt_of_le_of_lt hhalf hbig
          have hTn : (T n).natAbs < 2 ^ h * (R + 1) :=
            Nat.lt_of_mul_lt_mul_left hmul
          obtain ⟨k, hk, hent⟩ := ih (T n) hTn
          exact ⟨k + 1, Nat.succ_le_succ hk, by simpa [OrbitSucc] using hent⟩
        }
    }

/-- The same statement for a map defined on the natural numbers. -/
theorem NatHalfEntry (R : ℕ) (T : ℕ → ℕ)
    (hT : ∀ n : ℕ, R < n → 2 * T n ≤ n) (n : ℕ) :
    ∃ k : ℕ, k ≤ n ∧ OrbitNat T k n ≤ R := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    {
      cases Nat.lt_or_ge R n with
      | inr hin =>
        {
          exact ⟨0, Nat.zero_le n, by simpa [OrbitNatZero] using hin⟩
        }
      | inl hout =>
        {
          have hhalf : 2 * T n ≤ n := hT n hout
          have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le R) hout
          have hlt : T n < n := by
            have htwice : n < 2 * n := by
              rw [Nat.two_mul]
              exact Nat.lt_add_of_pos_right hpos
            have hmul : 2 * T n < 2 * n := lt_of_le_of_lt hhalf htwice
            exact Nat.lt_of_mul_lt_mul_left hmul
          obtain ⟨k, hk, hent⟩ := ih (T n) hlt
          have hk1 : k + 1 ≤ n := by
            have hsucc : k + 1 ≤ T n + 1 := Nat.succ_le_succ hk
            have hpred : T n + 1 ≤ n := Nat.succ_le_of_lt hlt
            exact Nat.le_trans hsucc hpred
          exact ⟨k + 1, hk1, by simpa [OrbitNatSucc] using hent⟩
        }
    }

/-- Fixed point of the slope-`a/d` majorant with constant term `b`. -/
def MajorantFixedPoint (a d b : ℕ) : ℚ :=
  (b : ℚ) / ((d : ℚ) - (a : ℚ))

/-- Affine majorant `(a x + b) / d`. -/
def AffineMajorant (a d b : ℕ) (x : ℚ) : ℚ :=
  ((a : ℚ) * x + (b : ℚ)) / (d : ℚ)

/-- Cleared form of the fixed-point decomposition. The denominator `d (d - a)`
is nonzero whenever `a < d`. -/
theorem AffineMajorantIdentity (a d : ℕ) (hd : a < d) (b n : ℚ) :
    ((a : ℚ) * n + b) / (d : ℚ) =
      b / ((d : ℚ) - (a : ℚ)) +
        ((a : ℚ) / (d : ℚ)) * (n - b / ((d : ℚ) - (a : ℚ))) := by
  have hdpos : (0 : ℚ) < (d : ℚ) := by
    exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le a) hd
  have hδpos : (0 : ℚ) < (d : ℚ) - (a : ℚ) := by
    have ha : (a : ℚ) < (d : ℚ) := by exact_mod_cast hd
    linarith
  -- Both denominators are positive, so clearing them is an equivalence.
  field_simp (disch := positivity)
  ring

/-- Above the fixed point the majorant is strictly smaller than the input. -/
theorem AffineMajorantStrictDecrease (a d b n : ℕ) (hd : a < d)
    (hn : MajorantFixedPoint a d b < (n : ℚ)) :
    AffineMajorant a d b (n : ℚ) < (n : ℚ) := by
  set K : ℚ := MajorantFixedPoint a d b
  have hdpos : (0 : ℚ) < (d : ℚ) := by
    exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le a) hd
  have hρ : (a : ℚ) / (d : ℚ) < 1 :=
    (div_lt_one hdpos).mpr (by exact_mod_cast hd)
  have hcoef : (0 : ℚ) < 1 - (a : ℚ) / (d : ℚ) := by linarith
  have hgap : (0 : ℚ) < (n : ℚ) - K := by linarith
  have hform :
      AffineMajorant a d b (n : ℚ) =
        K + ((a : ℚ) / (d : ℚ)) * ((n : ℚ) - K) := by
    simpa [AffineMajorant, K, MajorantFixedPoint] using
      AffineMajorantIdentity a d hd (b : ℚ) (n : ℚ)
  have hdiff :
      (n : ℚ) - AffineMajorant a d b (n : ℚ) =
        (1 - (a : ℚ) / (d : ℚ)) * ((n : ℚ) - K) := by
    rw [hform]
    set ρ : ℚ := (a : ℚ) / (d : ℚ)
    ring
  have hpos : (0 : ℚ) < (n : ℚ) - AffineMajorant a d b (n : ℚ) := by
    rw [hdiff]
    exact mul_pos hcoef hgap
  linarith

/-- On the initial segment through the floor of the fixed point, the majorant
stays strictly below that floor plus one. -/
theorem AffineCoreBound (a d b : ℕ) (hd : a < d) (n : ℕ)
    (hn : (n : ℤ) ≤ Int.floor (MajorantFixedPoint a d b)) :
    AffineMajorant a d b (n : ℚ) <
      (Int.floor (MajorantFixedPoint a d b) : ℚ) + 1 := by
  set K : ℚ := MajorantFixedPoint a d b
  set N0 : ℤ := Int.floor K
  have hdpos : (0 : ℚ) < (d : ℚ) := by
    exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le a) hd
  have hρ0 : (0 : ℚ) ≤ (a : ℚ) / (d : ℚ) :=
    div_nonneg (Nat.cast_nonneg a) (le_of_lt hdpos)
  have hN0le : (N0 : ℚ) ≤ K := Int.floor_le K
  have hKlt : K < (N0 : ℚ) + 1 := Int.lt_floor_add_one K
  have hnle : (n : ℚ) ≤ (N0 : ℚ) := by exact_mod_cast hn
  have hgap0 : (0 : ℚ) ≤ K - (N0 : ℚ) := by linarith
  have hgap1 : K - (N0 : ℚ) < 1 := by linarith
  have hcoef : 1 - (a : ℚ) / (d : ℚ) ≤ 1 := by linarith
  have hprod : (1 - (a : ℚ) / (d : ℚ)) * (K - (N0 : ℚ)) < 1 := by
    have hle : (1 - (a : ℚ) / (d : ℚ)) * (K - (N0 : ℚ)) ≤ K - (N0 : ℚ) :=
      mul_le_of_le_one_left hgap0 hcoef
    exact lt_of_le_of_lt hle hgap1
  have hmono :
      ((a : ℚ) / (d : ℚ)) * ((n : ℚ) - K) ≤
        ((a : ℚ) / (d : ℚ)) * ((N0 : ℚ) - K) := by
    have hdiff : (n : ℚ) - K ≤ (N0 : ℚ) - K := by linarith
    exact mul_le_mul_of_nonneg_left hdiff hρ0
  have hform :
      AffineMajorant a d b (n : ℚ) =
        K + ((a : ℚ) / (d : ℚ)) * ((n : ℚ) - K) := by
    simpa [AffineMajorant, K, MajorantFixedPoint] using
      AffineMajorantIdentity a d hd (b : ℚ) (n : ℚ)
  have hmaj :
      AffineMajorant a d b (n : ℚ) ≤
        (N0 : ℚ) + (1 - (a : ℚ) / (d : ℚ)) * (K - (N0 : ℚ)) := by
    calc
      AffineMajorant a d b (n : ℚ)
          = K + ((a : ℚ) / (d : ℚ)) * ((n : ℚ) - K) := hform
      _ ≤ K + ((a : ℚ) / (d : ℚ)) * ((N0 : ℚ) - K) := by
          simpa [add_comm] using add_le_add_left hmono K
      _ = (N0 : ℚ) + (1 - (a : ℚ) / (d : ℚ)) * (K - (N0 : ℚ)) := by
          set ρ : ℚ := (a : ℚ) / (d : ℚ)
          ring
  have htop :
      (N0 : ℚ) + (1 - (a : ℚ) / (d : ℚ)) * (K - (N0 : ℚ)) < (N0 : ℚ) + 1 := by
    linarith
  exact lt_of_le_of_lt hmaj htop

/-- An integer-valued map bounded by the majorant sends the floor segment into
itself. -/
theorem AffineCoreInvariant (a d b : ℕ) (hd : a < d) (T : ℕ → ℕ)
    (hT : ∀ m : ℕ, (T m : ℚ) ≤ AffineMajorant a d b (m : ℚ))
    (n : ℕ) (hn : (n : ℤ) ≤ Int.floor (MajorantFixedPoint a d b)) :
    (T n : ℤ) ≤ Int.floor (MajorantFixedPoint a d b) := by
  have hlt : (T n : ℚ) < (Int.floor (MajorantFixedPoint a d b) : ℚ) + 1 :=
    lt_of_le_of_lt (hT n) (AffineCoreBound a d b hd n hn)
  have hint : (T n : ℤ) < Int.floor (MajorantFixedPoint a d b) + 1 := by
    exact_mod_cast hlt
  exact Int.lt_add_one_iff.mp hint

/-- Under a global majorant bound of slope strictly less than one, every
natural orbit enters the floor of the fixed point. -/
theorem AffineMajorantEntry (a d b : ℕ) (hd : a < d) (T : ℕ → ℕ)
    (hT : ∀ m : ℕ, (T m : ℚ) ≤ AffineMajorant a d b (m : ℚ)) (n : ℕ) :
    ∃ k : ℕ, k ≤ n ∧
      (OrbitNat T k n : ℤ) ≤ Int.floor (MajorantFixedPoint a d b) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    {
      cases le_or_gt (n : ℤ) (Int.floor (MajorantFixedPoint a d b)) with
      | inl hcore =>
        {
          exact ⟨0, Nat.zero_le n, by simpa [OrbitNatZero] using hcore⟩
        }
      | inr hout =>
        {
          have hK : MajorantFixedPoint a d b < (n : ℚ) := (Int.floor_lt).mp hout
          have hmaj : AffineMajorant a d b (n : ℚ) < (n : ℚ) :=
            AffineMajorantStrictDecrease a d b n hd hK
          have hTnq : (T n : ℚ) < (n : ℚ) := lt_of_le_of_lt (hT n) hmaj
          have hTn : T n < n := by exact_mod_cast hTnq
          obtain ⟨k, hk, hent⟩ := ih (T n) hTn
          have hk1 : k + 1 ≤ n := by
            have hsucc : k + 1 ≤ T n + 1 := Nat.succ_le_succ hk
            have hpred : T n + 1 ≤ n := Nat.succ_le_of_lt hTn
            exact Nat.le_trans hsucc hpred
          exact ⟨k + 1, hk1, by simpa [OrbitNatSucc] using hent⟩
        }
    }

/-- Rational iteration of the affine majorant. -/
def IterateMajorant (a d b : ℕ) : ℕ → ℚ → ℚ
  | 0, x => x
  | k + 1, x => IterateMajorant a d b k (AffineMajorant a d b x)

/-- The zeroth majorant iterate is the input. -/
@[simp] theorem IterateMajorantZero (a d b : ℕ) (x : ℚ) :
    IterateMajorant a d b 0 x = x := rfl

/-- A positive majorant iterate applies the affine bound first. -/
@[simp] theorem IterateMajorantSucc (a d b k : ℕ) (x : ℚ) :
    IterateMajorant a d b (k + 1) x =
      IterateMajorant a d b k (AffineMajorant a d b x) := rfl

/-- Closed form: the majorant orbit is the convex combination of the seed and
the fixed point with weight `(a/d)^h`. -/
theorem IterateMajorantFormula (a d b : ℕ) (hd : a < d) (h : ℕ) (n : ℚ) :
    IterateMajorant a d b h n =
      ((a : ℚ) / (d : ℚ)) ^ h * (n - MajorantFixedPoint a d b) +
        MajorantFixedPoint a d b := by
  induction h generalizing n with
  | zero =>
    {
      rw [IterateMajorantZero, pow_zero, one_mul]
      exact (sub_add_cancel n (MajorantFixedPoint a d b)).symm
    }
  | succ h ih =>
    {
      set K : ℚ := MajorantFixedPoint a d b
      set ρ : ℚ := (a : ℚ) / (d : ℚ) with hρ
      have hform : AffineMajorant a d b n = K + ρ * (n - K) := by
        simpa [AffineMajorant, K, MajorantFixedPoint, hρ] using
          AffineMajorantIdentity a d hd (b : ℚ) n
      have hstep : AffineMajorant a d b n - K = ρ * (n - K) := by
        rw [hform]
        ring
      calc
        IterateMajorant a d b (h + 1) n
            = IterateMajorant a d b h (AffineMajorant a d b n) := by
              rw [IterateMajorantSucc]
        _ = ρ ^ h * (AffineMajorant a d b n - K) + K := by
              simpa [K, hρ] using ih (AffineMajorant a d b n)
        _ = ρ ^ h * (ρ * (n - K)) + K := by rw [hstep]
        _ = ρ ^ (h + 1) * (n - K) + K := by
              rw [pow_succ]
              ring
    }

/-- A strict power budget puts the iterated majorant below the floor plus one.
The budget is `d^h ((N_0+1) - K) > a^h (n - K)`. -/
theorem IterateMajorantBelowCore (a d b : ℕ) (hd : a < d) (n : ℚ) (h : ℕ)
    (hbudget :
      ((d : ℚ) ^ h) *
          ((Int.floor (MajorantFixedPoint a d b) : ℚ) + 1 -
            MajorantFixedPoint a d b) >
        ((a : ℚ) ^ h) * (n - MajorantFixedPoint a d b)) :
    IterateMajorant a d b h n <
      (Int.floor (MajorantFixedPoint a d b) : ℚ) + 1 := by
  set K : ℚ := MajorantFixedPoint a d b
  set N0 : ℤ := Int.floor K
  have hdpos : (0 : ℚ) < (d : ℚ) := by
    exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le a) hd
  have hdpow : (0 : ℚ) < (d : ℚ) ^ h := pow_pos hdpos h
  have hdiv :
      ((a : ℚ) / (d : ℚ)) ^ h * (n - K) < (N0 : ℚ) + 1 - K := by
    have hrew :
        ((a : ℚ) ^ h) * (n - K) / ((d : ℚ) ^ h) < (N0 : ℚ) + 1 - K := by
      rw [div_lt_iff₀ hdpow]
      have hcomm :
          ((N0 : ℚ) + 1 - K) * ((d : ℚ) ^ h) =
            ((d : ℚ) ^ h) * ((N0 : ℚ) + 1 - K) := by
        exact mul_comm _ _
      rw [hcomm]
      simpa [K, N0] using hbudget
    have hpow : ((a : ℚ) / (d : ℚ)) ^ h = (a : ℚ) ^ h / (d : ℚ) ^ h := by
      rw [div_pow]
    calc
      ((a : ℚ) / (d : ℚ)) ^ h * (n - K)
          = ((a : ℚ) ^ h / (d : ℚ) ^ h) * (n - K) := by rw [hpow]
      _ = ((a : ℚ) ^ h) * (n - K) / ((d : ℚ) ^ h) := by
          rw [div_mul_eq_mul_div₀]
      _ < (N0 : ℚ) + 1 - K := hrew
  have hformula :
      IterateMajorant a d b h n =
        ((a : ℚ) / (d : ℚ)) ^ h * (n - K) + K := by
    simpa [K] using IterateMajorantFormula a d b hd h n
  rw [hformula]
  linarith

/-- The majorant does not decrease the order of its input. -/
theorem AffineMajorantMonotone (a d b : ℕ) (hd : a < d) {x y : ℚ}
    (hxy : x ≤ y) :
    AffineMajorant a d b x ≤ AffineMajorant a d b y := by
  have hdpos : (0 : ℚ) < (d : ℚ) := by
    exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le a) hd
  have hmul : (a : ℚ) * x ≤ (a : ℚ) * y :=
    mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg a)
  have hadd : (a : ℚ) * x + (b : ℚ) ≤ (a : ℚ) * y + (b : ℚ) := by linarith
  exact (div_le_div_iff_of_pos_right hdpos).mpr hadd

/-- Iteration preserves the inequality between seeds. -/
theorem IterateMajorantMonotone (a d b : ℕ) (hd : a < d) (h : ℕ) {x y : ℚ}
    (hxy : x ≤ y) :
    IterateMajorant a d b h x ≤ IterateMajorant a d b h y := by
  induction h generalizing x y with
  | zero =>
    {
      simpa [IterateMajorantZero] using hxy
    }
  | succ h ih =>
    {
      have hM : AffineMajorant a d b x ≤ AffineMajorant a d b y :=
        AffineMajorantMonotone a d b hd hxy
      have hrec := ih hM
      simpa [IterateMajorantSucc] using hrec
    }

/-- An integer orbit bounded pointwise by the majorant stays below the rational
majorant orbit. -/
theorem OrbitBelowMajorant (a d b : ℕ) (hd : a < d) (T : ℕ → ℕ)
    (hT : ∀ m : ℕ, (T m : ℚ) ≤ AffineMajorant a d b (m : ℚ))
    (k n : ℕ) :
    (OrbitNat T k n : ℚ) ≤ IterateMajorant a d b k (n : ℚ) := by
  induction k generalizing n with
  | zero =>
    {
      simp [OrbitNatZero, IterateMajorantZero]
    }
  | succ k ih =>
    {
      have hTn : (T n : ℚ) ≤ AffineMajorant a d b (n : ℚ) := hT n
      have horb : (OrbitNat T k (T n) : ℚ) ≤
          IterateMajorant a d b k (T n : ℚ) := ih (T n)
      have hmono : IterateMajorant a d b k (T n : ℚ) ≤
          IterateMajorant a d b k (AffineMajorant a d b (n : ℚ)) :=
        IterateMajorantMonotone a d b hd k hTn
      have hle : (OrbitNat T (k + 1) n : ℚ) ≤
          IterateMajorant a d b (k + 1) (n : ℚ) := by
        calc
          (OrbitNat T (k + 1) n : ℚ) = (OrbitNat T k (T n) : ℚ) := by
            simp [OrbitNatSucc]
          _ ≤ IterateMajorant a d b k (T n : ℚ) := horb
          _ ≤ IterateMajorant a d b k (AffineMajorant a d b (n : ℚ)) := hmono
          _ = IterateMajorant a d b (k + 1) (n : ℚ) := by
            simp [IterateMajorantSucc]
      exact hle
    }

/-- If `2 (a n + b) < d n`, the majorant is strictly below half the input. -/
theorem HalfFromAffineMajorant (a d b n : ℕ) (ha : 2 * a < d)
    (hn : 2 * b < n * (d - 2 * a)) :
    AffineMajorant a d b (n : ℚ) < (n : ℚ) / 2 := by
  have hdpos : (0 : ℚ) < (d : ℚ) := by
    exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le (2 * a)) ha
  have h2 : (0 : ℚ) < (2 : ℚ) := by norm_num
  have hle : 2 * a ≤ d := Nat.le_of_lt ha
  have hcast : ((d - 2 * a : ℕ) : ℚ) = (d : ℚ) - 2 * (a : ℚ) := by
    rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat]
  have hhyp : (2 : ℚ) * (b : ℚ) <
      (n : ℚ) * ((d : ℚ) - 2 * (a : ℚ)) := by
    have hnat : (2 * b : ℚ) < (n * (d - 2 * a) : ℕ) := by exact_mod_cast hn
    have hmul : ((n * (d - 2 * a) : ℕ) : ℚ) =
        (n : ℚ) * ((d - 2 * a : ℕ) : ℚ) := by
      rw [Nat.cast_mul]
    have : (2 * b : ℚ) < (n : ℚ) * ((d - 2 * a : ℕ) : ℚ) := by
      simpa [hmul] using hnat
    simpa [hcast] using this
  have hcross : (2 : ℚ) * ((a : ℚ) * (n : ℚ) + (b : ℚ)) < (d : ℚ) * (n : ℚ) := by
    have hdiff : (n : ℚ) * ((d : ℚ) - 2 * (a : ℚ)) =
        (d : ℚ) * (n : ℚ) - 2 * (a : ℚ) * (n : ℚ) := by ring
    have hexpand : (2 : ℚ) * ((a : ℚ) * (n : ℚ) + (b : ℚ)) =
        2 * (a : ℚ) * (n : ℚ) + 2 * (b : ℚ) := by ring
    linarith
  rw [AffineMajorant, div_lt_iff₀ hdpos]
  have hreorder : (n : ℚ) / 2 * (d : ℚ) = (d : ℚ) * (n : ℚ) / 2 := by
    rw [div_mul_eq_mul_div₀, mul_comm (n : ℚ) (d : ℚ)]
  rw [hreorder, lt_div_iff₀ h2]
  linarith

/-- Every integer strictly larger than `2b` clears the half-majorant threshold
once `2a < d`, because the positive denominator `d - 2a` is then at least one. -/
theorem RadiusTwoB (a d b n : ℕ) (ha : 2 * a < d) (hn : 2 * b < n) :
    2 * b < n * (d - 2 * a) := by
  have hδ : 0 < d - 2 * a := Nat.sub_pos_of_lt ha
  have h1 : 1 ≤ d - 2 * a := Nat.succ_le_of_lt hδ
  have hmul : n * 1 ≤ n * (d - 2 * a) := Nat.mul_le_mul_left n h1
  have hnle : n ≤ n * (d - 2 * a) := by
    simpa [Nat.mul_one] using hmul
  exact Nat.lt_of_lt_of_le hn hnle

/-- A natural map bounded by the majorant outside radius `2b` is a natural
half-contraction there, provided the slope satisfies `2a < d`. -/
theorem UniformHalfFromMajorant (a d b : ℕ) (ha : 2 * a < d) (T : ℕ → ℕ)
    (hT : ∀ n : ℕ, 2 * b < n → (T n : ℚ) ≤ AffineMajorant a d b (n : ℚ))
    (n : ℕ) (hn : 2 * b < n) : 2 * T n ≤ n := by
  have hmaj : AffineMajorant a d b (n : ℚ) < (n : ℚ) / 2 :=
    HalfFromAffineMajorant a d b n ha (RadiusTwoB a d b n ha hn)
  have hle : (T n : ℚ) < (n : ℚ) / 2 := lt_of_le_of_lt (hT n hn) hmaj
  have h2 : (0 : ℚ) < (2 : ℚ) := by norm_num
  have hmul : (T n : ℚ) * 2 < (n : ℚ) := (lt_div_iff₀ h2).mp hle
  have hcomm : (2 : ℚ) * (T n : ℚ) < (n : ℚ) := by
    simpa [mul_comm] using hmul
  have hint : 2 * T n < n := by exact_mod_cast hcomm
  exact Nat.le_of_lt hint

end GeneralizedCollatz
