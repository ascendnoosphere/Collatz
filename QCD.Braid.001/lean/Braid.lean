-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-!
# Saturated braid modulo `D ^ 2`

When `q = D + 1`, multiplication by `1 - D` and then by `q` returns every
integer to itself modulo `D ^ 2`. If `D` does not divide the input, it does
not divide the intermediate factor `1 - D` either.

On the family cut out by `q ^ (a + b) * u ≡ c` modulo `D ^ 2`, with `a ≥ 1`
and `D` not dividing `c`, the source word of `a` divided affine steps and two
exact divisions ends at the same integer as the parent word of `a + b - 1`
divided affine steps, one exact division, and one divided affine step.

For a coprime slope, equality of the endpoints of `A ^ a EE` and `A ^ (a - 1) EA`
forces `q ^ a` to divide `c * (D - 1) * (q - D - 1)`. The divisibility alone
does not produce a pair.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Two-step state: multiply by the unit `1 - D`, then by `D + 1`. -/
def TwoStepState (D n : ℤ) : ℤ :=
  (D + 1) * ((1 - D) * n)

/-- Source state after `k` divided affine steps, before the two exact divisions. -/
def BraidSourceState (D u c : ℤ) (a b k : ℕ) : ℤ :=
  D ^ (a - k) * (D + 1) ^ (b + k) * u - c

/-- Parent state after `k` divided affine steps. -/
def BraidParentState (D u c : ℤ) (a b k : ℕ) : ℤ :=
  D ^ (a + b - 1 - k) * (D + 1) ^ k * u - c

/-- Cleared endpoint identity of an unsaturated pair of return length `a`. -/
def UnsaturatedRelation (q c D : ℤ) (a : ℕ) (n p : ℤ) : Prop :=
  q ^ a * ((q - D) * n - (D - 1) * c) - D * q ^ a * (q - D) * p =
    c * (D - 1) * (q - D - 1) * D ^ a

/-- Divided affine branch `(q * x + c) / D`. Exact when `D` divides the numerator. -/
def DividedAffine (q c D x : ℤ) : ℤ :=
  (q * x + c) / D

/-- Exact division branch `x / D`. -/
def ExactHalf (D x : ℤ) : ℤ :=
  x / D

/-- Linear witness `Y(x) = (q - D) * x + c`, constant precisely when `q = D`. -/
def BraidY (q D c x : ℤ) : ℤ :=
  (q - D) * x + c

/-- `a` successive divided affine steps, head first. -/
def AffineRun (q c D : ℤ) : ℕ → ℤ → ℤ
  | 0, x => x
  | k + 1, x => AffineRun q c D k (DividedAffine q c D x)

/-- Each head is an affine letter: `D` misses the input and divides `q * x + c`. -/
def AffineRunLegal (q c D : ℤ) : ℕ → ℤ → Prop
  | 0, _ => True
  | k + 1, x =>
      ¬ D ∣ x ∧ D ∣ q * x + c ∧
        AffineRunLegal q c D k (DividedAffine q c D x)

/-- Source word `A ^ a EE`: `a` affine letters, then two exact divisions. -/
def SourceWordLegal (q c D : ℤ) (a : ℕ) (n : ℤ) : Prop :=
  AffineRunLegal q c D a n ∧
    D ∣ AffineRun q c D a n ∧
    D ∣ ExactHalf D (AffineRun q c D a n)

/-- Parent word `A ^ (a - 1) EA`, using truncated subtraction when `a = 0`. -/
def ParentWordLegal (q c D : ℤ) (a : ℕ) (p : ℤ) : Prop :=
  AffineRunLegal q c D (a - 1) p ∧
    D ∣ AffineRun q c D (a - 1) p ∧
    ¬ D ∣ ExactHalf D (AffineRun q c D (a - 1) p) ∧
    D ∣ q * ExactHalf D (AffineRun q c D (a - 1) p) + c

/-- Endpoint of `A ^ a EE`. -/
def SourceEndpoint (q c D : ℤ) (a : ℕ) (n : ℤ) : ℤ :=
  ExactHalf D (ExactHalf D (AffineRun q c D a n))

/-- Endpoint of `A ^ (a - 1) EA`. -/
def ParentEndpoint (q c D : ℤ) (a : ℕ) (p : ℤ) : ℤ :=
  DividedAffine q c D (ExactHalf D (AffineRun q c D (a - 1) p))

/-- `(D + 1) * (1 - D) = 1 - D ^ 2`, so `D + 1` is a unit modulo `D ^ 2`. -/
theorem BraidInverseProduct (D : ℤ) :
    (D + 1) * (1 - D) = 1 - D ^ 2 := by
  ring

/-- If `D` misses `n`, it misses `(1 - D) * n`, and the two-step state returns `n`. -/
theorem BraidTwoStepCongruence (D n : ℤ) (hD : ¬ D ∣ n) :
    ¬ D ∣ (1 - D) * n ∧ TwoStepState D n ≡ n [ZMOD D ^ 2] := by
  constructor
  · intro hfac
    have hdiff : (1 - D) * n - n = (-D) * n := by ring
    have hDn : D ∣ (1 - D) * n - n := by
      rw [hdiff]
      exact ⟨-n, by ring⟩
    rcases hfac with ⟨s, hs⟩
    rcases hDn with ⟨t, ht⟩
    have hn : n = D * (s - t) := by
      have hsub : n = (1 - D) * n - ((1 - D) * n - n) := by ring
      rw [hsub, ht, hs]
      ring
    exact hD ⟨s - t, hn⟩
  · rw [Int.modEq_iff_dvd]
    refine ⟨n, ?_⟩
    unfold TwoStepState
    have hprod := BraidInverseProduct D
    calc
      n - (D + 1) * ((1 - D) * n) =
          n - ((D + 1) * (1 - D)) * n := by ring
      _ = n - (1 - D ^ 2) * n := by rw [hprod]
      _ = D ^ 2 * n := by ring

/-- An affine source step stays off multiples of `D` and advances the closed form. -/
theorem BraidSourceAffineStep (D u c : ℤ) (a b k : ℕ) (hk : k < a)
    (hc : ¬ D ∣ c) :
    ¬ D ∣ BraidSourceState D u c a b k ∧
      (D + 1) * BraidSourceState D u c a b k + c =
        D * BraidSourceState D u c a b (k + 1) := by
  have hexp : a - k = (a - (k + 1)) + 1 := by omega
  have hbexp : b + (k + 1) = (b + k) + 1 := by omega
  constructor
  · intro hDx
    have hxc :
        (D ^ (a - k) * (D + 1) ^ (b + k) * u - c) + c =
          D * (D ^ (a - (k + 1)) * (D + 1) ^ (b + k) * u) := by
      rw [hexp, pow_succ]
      ring
    rcases hDx with ⟨s, hs⟩
    have hcEq :
        c =
          D * (D ^ (a - (k + 1)) * (D + 1) ^ (b + k) * u - s) := by
      have hsub :
          c =
            ((D ^ (a - k) * (D + 1) ^ (b + k) * u - c) + c) -
              (D ^ (a - k) * (D + 1) ^ (b + k) * u - c) := by
        ring
      unfold BraidSourceState at hs
      rw [hsub, hxc, hs]
      ring
    exact hc ⟨_, hcEq⟩
  · unfold BraidSourceState
    rw [hexp, hbexp, pow_succ]
    ring

/-- After `a` source steps the closed form is the terminal numerator. -/
theorem BraidSourceTerminal (D u c : ℤ) (a b : ℕ) :
    BraidSourceState D u c a b a = (D + 1) ^ (a + b) * u - c := by
  unfold BraidSourceState
  have hzero : a - a = 0 := by omega
  have hsum : b + a = a + b := by omega
  rw [hzero, hsum, pow_zero]
  ring

/-- The selecting congruence is divisibility of the terminal numerator by `D ^ 2`. -/
theorem BraidCongruenceDivides (D c u : ℤ) (a b : ℕ)
    (h : (D + 1) ^ (a + b) * u ≡ c [ZMOD D ^ 2]) :
    D ^ 2 ∣ (D + 1) ^ (a + b) * u - c := by
  rw [Int.modEq_iff_dvd] at h
  rcases h with ⟨t, ht⟩
  refine ⟨-t, ?_⟩
  have hneg :
      (D + 1) ^ (a + b) * u - c =
        -(c - (D + 1) ^ (a + b) * u) := by
    ring
  rw [hneg, ht]
  ring

/-- Two exact divisions by a nonzero integer are one division by its square. -/
theorem BraidDoubleQuotient (D m : ℤ) (hD : D ≠ 0) (hdiv : D ^ 2 ∣ m) :
    (m / D) / D = m / D ^ 2 := by
  rcases hdiv with ⟨j, hj⟩
  have hSq : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have h1 : m / D = D * j := by
    apply Int.ediv_eq_of_eq_mul_right hD
    rw [hj]
    ring
  have h2 : (m / D) / D = j := by
    apply Int.ediv_eq_of_eq_mul_right hD
    exact h1
  have h3 : m / D ^ 2 = j := Int.ediv_eq_of_eq_mul_right hSq hj
  rw [h2, h3]

/-- The saturated source word is legal and its two divisions equal the join. -/
theorem BraidSaturatedSource (D u c : ℤ) (a b : ℕ) (hAdm : 2 ≤ D.natAbs)
    (ha : 1 ≤ a) (hc : ¬ D ∣ c)
    (hcong : (D + 1) ^ (a + b) * u ≡ c [ZMOD D ^ 2]) :
    ¬ D ∣ BraidSourceState D u c a b 0 ∧
      (∀ k, k < a →
        ¬ D ∣ BraidSourceState D u c a b k ∧
          ((D + 1) * BraidSourceState D u c a b k + c) / D =
            BraidSourceState D u c a b (k + 1)) ∧
      BraidSourceState D u c a b a = (D + 1) ^ (a + b) * u - c ∧
      D ^ 2 ∣ BraidSourceState D u c a b a ∧
      (BraidSourceState D u c a b a / D) / D =
        BraidSourceState D u c a b a / D ^ 2 := by
  have hD : D ≠ 0 := (Int.natAbs_eq_zero (a := D)).not.mp (by omega)
  refine ⟨(BraidSourceAffineStep D u c a b 0 ha hc).1, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hstep := BraidSourceAffineStep D u c a b k hk hc
    exact ⟨hstep.1, Int.ediv_eq_of_eq_mul_right hD hstep.2⟩
  · exact BraidSourceTerminal D u c a b
  · rw [BraidSourceTerminal D u c a b]
    exact BraidCongruenceDivides D c u a b hcong
  · have hdiv : D ^ 2 ∣ BraidSourceState D u c a b a := by
      rw [BraidSourceTerminal D u c a b]
      exact BraidCongruenceDivides D c u a b hcong
    exact BraidDoubleQuotient D (BraidSourceState D u c a b a) hD hdiv

/-- An affine parent step stays off multiples of `D` and advances the closed form. -/
theorem BraidParentAffineStep (D u c : ℤ) (a b k : ℕ) (hk : k < a + b - 1)
    (hc : ¬ D ∣ c) :
    ¬ D ∣ BraidParentState D u c a b k ∧
      (D + 1) * BraidParentState D u c a b k + c =
        D * BraidParentState D u c a b (k + 1) := by
  have hexp : a + b - 1 - k = (a + b - 1 - (k + 1)) + 1 := by omega
  constructor
  · intro hDx
    have hxc :
        (D ^ (a + b - 1 - k) * (D + 1) ^ k * u - c) + c =
          D * (D ^ (a + b - 1 - (k + 1)) * (D + 1) ^ k * u) := by
      rw [hexp, pow_succ]
      ring
    rcases hDx with ⟨s, hs⟩
    have hcEq :
        c =
          D *
            (D ^ (a + b - 1 - (k + 1)) * (D + 1) ^ k * u - s) := by
      have hsub :
          c =
            ((D ^ (a + b - 1 - k) * (D + 1) ^ k * u - c) + c) -
              (D ^ (a + b - 1 - k) * (D + 1) ^ k * u - c) := by
        ring
      unfold BraidParentState at hs
      rw [hsub, hxc, hs]
      ring
    exact hc ⟨_, hcEq⟩
  · unfold BraidParentState
    rw [hexp, pow_succ]
    ring

/-- The parent gate is the state with no remaining exact powers of `D`. -/
theorem BraidParentGateState (D u c : ℤ) (a b : ℕ) :
    BraidParentState D u c a b (a + b - 1) =
      (D + 1) ^ (a + b - 1) * u - c := by
  unfold BraidParentState
  have hzero : a + b - 1 - (a + b - 1) = 0 := by omega
  rw [hzero, pow_zero]
  ring

/-- The parent gate divides once, and the following affine letter hits the join. -/
theorem BraidSaturatedParent (D u c : ℤ) (a b : ℕ) (hAdm : 2 ≤ D.natAbs)
    (ha : 1 ≤ a) (hc : ¬ D ∣ c)
    (hcong : (D + 1) ^ (a + b) * u ≡ c [ZMOD D ^ 2]) :
    (∀ k, k < a + b - 1 →
        ¬ D ∣ BraidParentState D u c a b k ∧
          ((D + 1) * BraidParentState D u c a b k + c) / D =
            BraidParentState D u c a b (k + 1)) ∧
      BraidParentState D u c a b (a + b - 1) =
        (D + 1) ^ (a + b - 1) * u - c ∧
      D ∣ BraidParentState D u c a b (a + b - 1) ∧
      ¬ D ∣ BraidParentState D u c a b (a + b - 1) / D ∧
      ((D + 1) * (BraidParentState D u c a b (a + b - 1) / D) + c) / D =
        ((D + 1) ^ (a + b) * u - c) / D ^ 2 := by
  have hD : D ≠ 0 := (Int.natAbs_eq_zero (a := D)).not.mp (by omega)
  have hpow : a + b = (a + b - 1) + 1 := by omega
  refine ⟨?_, BraidParentGateState D u c a b, ?_, ?_, ?_⟩
  · intro k hk
    have hstep := BraidParentAffineStep D u c a b k hk hc
    exact ⟨hstep.1, Int.ediv_eq_of_eq_mul_right hD hstep.2⟩
  · have hunit : (1 - D) * (D + 1) ≡ 1 [ZMOD D ^ 2] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨1, ?_⟩
      have hprod := BraidInverseProduct D
      calc
        1 - (1 - D) * (D + 1) = 1 - (D + 1) * (1 - D) := by ring
        _ = 1 - (1 - D ^ 2) := by rw [hprod]
        _ = D ^ 2 * 1 := by ring
    have hmul := Int.ModEq.mul_left (1 - D) hcong
    have hassoc :
        (1 - D) * ((D + 1) ^ (a + b) * u) =
          ((1 - D) * (D + 1)) * ((D + 1) ^ (a + b - 1) * u) := by
      rw [hpow, pow_succ]
      have hidx : (a + b - 1) + 1 - 1 = a + b - 1 := by omega
      rw [hidx]
      ring
    have hscaled :
        ((1 - D) * (D + 1)) * ((D + 1) ^ (a + b - 1) * u) ≡
          (1 - D) * c [ZMOD D ^ 2] := by
      rw [← hassoc]
      exact hmul
    have hcancel :
        ((1 - D) * (D + 1)) * ((D + 1) ^ (a + b - 1) * u) ≡
          (D + 1) ^ (a + b - 1) * u [ZMOD D ^ 2] := by
      have hmulr :=
        Int.ModEq.mul_right ((D + 1) ^ (a + b - 1) * u) hunit
      rw [one_mul] at hmulr
      exact hmulr
    have hσ :
        (D + 1) ^ (a + b - 1) * u ≡ (1 - D) * c [ZMOD D ^ 2] :=
      hcancel.symm.trans hscaled
    have hgateCong :
        (D + 1) ^ (a + b - 1) * u - c ≡ -D * c [ZMOD D ^ 2] := by
      have hsub := hσ.sub (show c ≡ c [ZMOD D ^ 2] from Int.ModEq.refl c)
      have hrhs : (1 - D) * c - c = -D * c := by ring
      rw [hrhs] at hsub
      exact hsub
    rw [Int.modEq_iff_dvd] at hgateCong
    rcases hgateCong with ⟨t, ht⟩
    have hgateEq :
        (D + 1) ^ (a + b - 1) * u - c = D * (-c - D * t) := by
      have hre :
          (D + 1) ^ (a + b - 1) * u - c =
            -D * c - (-D * c - ((D + 1) ^ (a + b - 1) * u - c)) := by
        ring
      rw [hre, ht]
      ring
    rw [← BraidParentGateState D u c a b] at hgateEq
    exact ⟨_, hgateEq⟩
  · intro hquot
    have hunit : (1 - D) * (D + 1) ≡ 1 [ZMOD D ^ 2] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨1, ?_⟩
      have hprod := BraidInverseProduct D
      calc
        1 - (1 - D) * (D + 1) = 1 - (D + 1) * (1 - D) := by ring
        _ = 1 - (1 - D ^ 2) := by rw [hprod]
        _ = D ^ 2 * 1 := by ring
    have hmul := Int.ModEq.mul_left (1 - D) hcong
    have hassoc :
        (1 - D) * ((D + 1) ^ (a + b) * u) =
          ((1 - D) * (D + 1)) * ((D + 1) ^ (a + b - 1) * u) := by
      rw [hpow, pow_succ]
      have hidx : (a + b - 1) + 1 - 1 = a + b - 1 := by omega
      rw [hidx]
      ring
    have hscaled :
        ((1 - D) * (D + 1)) * ((D + 1) ^ (a + b - 1) * u) ≡
          (1 - D) * c [ZMOD D ^ 2] := by
      rw [← hassoc]
      exact hmul
    have hcancel :
        ((1 - D) * (D + 1)) * ((D + 1) ^ (a + b - 1) * u) ≡
          (D + 1) ^ (a + b - 1) * u [ZMOD D ^ 2] := by
      have hmulr :=
        Int.ModEq.mul_right ((D + 1) ^ (a + b - 1) * u) hunit
      rw [one_mul] at hmulr
      exact hmulr
    have hσ :
        (D + 1) ^ (a + b - 1) * u ≡ (1 - D) * c [ZMOD D ^ 2] :=
      hcancel.symm.trans hscaled
    have hgateCong :
        (D + 1) ^ (a + b - 1) * u - c ≡ -D * c [ZMOD D ^ 2] := by
      have hsub := hσ.sub (show c ≡ c [ZMOD D ^ 2] from Int.ModEq.refl c)
      have hrhs : (1 - D) * c - c = -D * c := by ring
      rw [hrhs] at hsub
      exact hsub
    rw [Int.modEq_iff_dvd] at hgateCong
    rcases hgateCong with ⟨t, ht⟩
    have hr :
        ((D + 1) ^ (a + b - 1) * u - c) / D = -c - D * t := by
      apply Int.ediv_eq_of_eq_mul_right hD
      have hre :
          (D + 1) ^ (a + b - 1) * u - c =
            -D * c - (-D * c - ((D + 1) ^ (a + b - 1) * u - c)) := by
        ring
      rw [hre, ht]
      ring
    rw [← BraidParentGateState D u c a b] at hr
    rcases hquot with ⟨s, hs⟩
    rw [hr] at hs
    have hcEq : c = D * (-t - s) := by
      have hc' : c = -D * t - (-c - D * t) := by ring
      rw [hc', hs]
      ring
    exact hc ⟨_, hcEq⟩
  · have hunit : (1 - D) * (D + 1) ≡ 1 [ZMOD D ^ 2] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨1, ?_⟩
      have hprod := BraidInverseProduct D
      calc
        1 - (1 - D) * (D + 1) = 1 - (D + 1) * (1 - D) := by ring
        _ = 1 - (1 - D ^ 2) := by rw [hprod]
        _ = D ^ 2 * 1 := by ring
    have hmul := Int.ModEq.mul_left (1 - D) hcong
    have hassoc :
        (1 - D) * ((D + 1) ^ (a + b) * u) =
          ((1 - D) * (D + 1)) * ((D + 1) ^ (a + b - 1) * u) := by
      rw [hpow, pow_succ]
      have hidx : (a + b - 1) + 1 - 1 = a + b - 1 := by omega
      rw [hidx]
      ring
    have hscaled :
        ((1 - D) * (D + 1)) * ((D + 1) ^ (a + b - 1) * u) ≡
          (1 - D) * c [ZMOD D ^ 2] := by
      rw [← hassoc]
      exact hmul
    have hcancel :
        ((1 - D) * (D + 1)) * ((D + 1) ^ (a + b - 1) * u) ≡
          (D + 1) ^ (a + b - 1) * u [ZMOD D ^ 2] := by
      have hmulr :=
        Int.ModEq.mul_right ((D + 1) ^ (a + b - 1) * u) hunit
      rw [one_mul] at hmulr
      exact hmulr
    have hσ :
        (D + 1) ^ (a + b - 1) * u ≡ (1 - D) * c [ZMOD D ^ 2] :=
      hcancel.symm.trans hscaled
    have hgateCong :
        (D + 1) ^ (a + b - 1) * u - c ≡ -D * c [ZMOD D ^ 2] := by
      have hsub := hσ.sub (show c ≡ c [ZMOD D ^ 2] from Int.ModEq.refl c)
      have hrhs : (1 - D) * c - c = -D * c := by ring
      rw [hrhs] at hsub
      exact hsub
    rw [Int.modEq_iff_dvd] at hgateCong
    rcases hgateCong with ⟨t, ht⟩
    have hgateEq :
        (D + 1) ^ (a + b - 1) * u - c = D * (-c - D * t) := by
      have hre :
          (D + 1) ^ (a + b - 1) * u - c =
            -D * c - (-D * c - ((D + 1) ^ (a + b - 1) * u - c)) := by
        ring
      rw [hre, ht]
      ring
    have hr :
        ((D + 1) ^ (a + b - 1) * u - c) / D = -c - D * t :=
      Int.ediv_eq_of_eq_mul_right hD hgateEq
    have hnum :
        (D + 1) * ((D + 1) ^ (a + b - 1) * u - c) + c * D =
          (D + 1) ^ (a + b) * u - c := by
      rw [hpow, pow_succ]
      have hidx : (a + b - 1) + 1 - 1 = a + b - 1 := by omega
      rw [hidx]
      ring
    have hfac :
        (D + 1) * ((D + 1) ^ (a + b - 1) * u - c) + c * D =
          D * ((D + 1) * (((D + 1) ^ (a + b - 1) * u - c) / D) + c) := by
      rw [hr, hgateEq]
      ring
    have hdiv1 :
        ((D + 1) ^ (a + b) * u - c) / D =
          (D + 1) * (((D + 1) ^ (a + b - 1) * u - c) / D) + c := by
      apply Int.ediv_eq_of_eq_mul_right hD
      exact hnum.symm.trans hfac
    have hSq : D ^ 2 ∣ (D + 1) ^ (a + b) * u - c :=
      BraidCongruenceDivides D c u a b hcong
    have hdiv2 :=
      BraidDoubleQuotient D ((D + 1) ^ (a + b) * u - c) hD hSq
    rw [BraidParentGateState D u c a b, ← hdiv1]
    exact hdiv2

/-- Source and parent words of a saturated pair end at the same integer. -/
theorem BraidSaturatedSameJoin (D u c : ℤ) (a b : ℕ) (hAdm : 2 ≤ D.natAbs)
    (ha : 1 ≤ a) (hc : ¬ D ∣ c)
    (hcong : (D + 1) ^ (a + b) * u ≡ c [ZMOD D ^ 2]) :
    (BraidSourceState D u c a b a / D) / D =
      ((D + 1) * (BraidParentState D u c a b (a + b - 1) / D) + c) / D := by
  have hsrc := BraidSaturatedSource D u c a b hAdm ha hc hcong
  have hpar := BraidSaturatedParent D u c a b hAdm ha hc hcong
  rcases hsrc with ⟨_, _, hterm, _, hquot⟩
  rcases hpar with ⟨_, _, _, _, hfinal⟩
  rw [hterm] at hquot
  rw [hterm, hquot]
  exact hfinal.symm

/-- The two-step state of a saturated source seed agrees with that seed. -/
theorem BraidSaturatedSeedTwoStep (D u c : ℤ) (a b : ℕ) (hAdm : 2 ≤ D.natAbs)
    (ha : 1 ≤ a) (hc : ¬ D ∣ c)
    (hcong : (D + 1) ^ (a + b) * u ≡ c [ZMOD D ^ 2]) :
    TwoStepState D (BraidSourceState D u c a b 0) ≡
      BraidSourceState D u c a b 0 [ZMOD D ^ 2] := by
  have hsrc := BraidSaturatedSource D u c a b hAdm ha hc hcong
  exact (BraidTwoStepCongruence D (BraidSourceState D u c a b 0) hsrc.1).2

/-- An exact divided affine step multiplies `Y` by `q / D`. -/
theorem BraidAffineY (q c D x : ℤ) (hD : D ≠ 0) (hdiv : D ∣ q * x + c) :
    D * BraidY q D c (DividedAffine q c D x) = q * BraidY q D c x := by
  rcases hdiv with ⟨t, ht⟩
  have hquot : DividedAffine q c D x = t :=
    Int.ediv_eq_of_eq_mul_right hD ht
  rw [hquot]
  unfold BraidY
  calc
    D * ((q - D) * t + c) = (q - D) * (D * t) + c * D := by ring
    _ = (q - D) * (q * x + c) + c * D := by rw [← ht]
    _ = q * ((q - D) * x + c) := by ring

/-- An exact division adds the constant defect `c * (D - 1) / D` to `Y`. -/
theorem BraidExactY (q c D x : ℤ) (hD : D ≠ 0) (hdiv : D ∣ x) :
    D * BraidY q D c (ExactHalf D x) =
      BraidY q D c x + c * (D - 1) := by
  rcases hdiv with ⟨t, ht⟩
  have hquot : ExactHalf D x = t := Int.ediv_eq_of_eq_mul_right hD ht
  rw [hquot]
  unfold BraidY
  calc
    D * ((q - D) * t + c) = (q - D) * (D * t) + c * D := by ring
    _ = (q - D) * x + c * D := by rw [← ht]
    _ = (q - D) * x + c + c * (D - 1) := by ring

/-- Legal affine runs multiply `Y` by `(q / D) ^ a`. -/
theorem BraidAffineRunY (q c D : ℤ) (hD : D ≠ 0) (a : ℕ) (x : ℤ)
    (hleg : AffineRunLegal q c D a x) :
    D ^ a * BraidY q D c (AffineRun q c D a x) =
      q ^ a * BraidY q D c x := by
  induction a generalizing x with
  | zero =>
    {
      unfold AffineRun
      simp [pow_zero, one_mul]
    }
  | succ k ih =>
    {
      rcases hleg with ⟨_, hdiv, htail⟩
      have hstep := BraidAffineY q c D x hD hdiv
      have htailY := ih (DividedAffine q c D x) htail
      calc
        D ^ (k + 1) * BraidY q D c (AffineRun q c D (k + 1) x) =
            (D ^ k * D) * BraidY q D c
              (AffineRun q c D k (DividedAffine q c D x)) := by
          rw [pow_succ, AffineRun]
        _ =
            D * (D ^ k * BraidY q D c
              (AffineRun q c D k (DividedAffine q c D x))) := by
          ring
        _ = D * (q ^ k * BraidY q D c (DividedAffine q c D x)) := by
          rw [htailY]
        _ = q ^ k * (D * BraidY q D c (DividedAffine q c D x)) := by
          ring
        _ = q ^ k * (q * BraidY q D c x) := by rw [hstep]
        _ = q ^ (k + 1) * BraidY q D c x := by
          rw [pow_succ]
          ring
    }

/-- Equal legal endpoints of `A ^ a EE` and `A ^ (a - 1) EA` satisfy the relation. -/
theorem BraidWordRelation (q c D n p : ℤ) (a : ℕ) (hD : D ≠ 0) (ha : 1 ≤ a)
    (hs : SourceWordLegal q c D a n) (hp : ParentWordLegal q c D a p)
    (hend : SourceEndpoint q c D a n = ParentEndpoint q c D a p) :
    UnsaturatedRelation q c D a n p := by
  rcases hs with ⟨hRunS, hdivRun, hdivHalf⟩
  rcases hp with ⟨hRunPleg, hdivZ0, _, hdivA⟩
  let run := AffineRun q c D a n
  let half := ExactHalf D run
  let fin := ExactHalf D half
  let z0 := AffineRun q c D (a - 1) p
  let z1 := ExactHalf D z0
  let z2 := DividedAffine q c D z1
  have hfin : fin = SourceEndpoint q c D a n := rfl
  have hz2 : z2 = ParentEndpoint q c D a p := rfl
  have hYeq : BraidY q D c fin = BraidY q D c z2 := by
    rw [hfin, hz2, hend]
  have hRun := BraidAffineRunY q c D hD a n hRunS
  have hRunP := BraidAffineRunY q c D hD (a - 1) p hRunPleg
  have hEhalf := BraidExactY q c D run hD hdivRun
  have hEfin := BraidExactY q c D half hD hdivHalf
  have hEz1 := BraidExactY q c D z0 hD hdivZ0
  have hAz2 := BraidAffineY q c D z1 hD hdivA
  have hSq :
      D ^ 2 * BraidY q D c fin =
        BraidY q D c run + c * (D - 1) * (D + 1) := by
    calc
      D ^ 2 * BraidY q D c fin = D * (D * BraidY q D c fin) := by ring
      _ = D * (BraidY q D c half + c * (D - 1)) := by rw [hEfin]
      _ = D * BraidY q D c half + D * (c * (D - 1)) := by ring
      _ =
          (BraidY q D c run + c * (D - 1)) + c * (D - 1) * D := by
        rw [hEhalf]
        ring
      _ = BraidY q D c run + c * (D - 1) * (D + 1) := by ring
  have hsrc :
      D ^ (a + 2) * BraidY q D c fin =
        q ^ a * BraidY q D c n + c * (D - 1) * (D + 1) * D ^ a := by
    calc
      D ^ (a + 2) * BraidY q D c fin =
          (D ^ a * D ^ 2) * BraidY q D c fin := by
        rw [pow_add]
      _ = D ^ a * (D ^ 2 * BraidY q D c fin) := by ring
      _ =
          D ^ a * (BraidY q D c run + c * (D - 1) * (D + 1)) := by
        rw [hSq]
      _ =
          D ^ a * BraidY q D c run + c * (D - 1) * (D + 1) * D ^ a := by
        ring
      _ =
          q ^ a * BraidY q D c n + c * (D - 1) * (D + 1) * D ^ a := by
        rw [hRun]
  have hsplit : a = (a - 1) + 1 := (Nat.sub_add_cancel ha).symm
  have hpowD : D ^ a = D ^ (a - 1) * D :=
    (congrArg (fun n : ℕ => D ^ n) hsplit).trans (pow_succ D (a - 1))
  have hqpow : q ^ (a - 1) * q = q ^ a :=
    (pow_succ q (a - 1)).symm.trans
      (congrArg (fun n : ℕ => q ^ n) hsplit.symm)
  have hleft :
      D ^ a * BraidY q D c z0 =
        D * (D ^ (a - 1) * BraidY q D c z0) := by
    rw [hpowD]
    ring
  have hYz1 :
      D ^ (a + 1) * BraidY q D c z1 =
        D * (q ^ (a - 1) * BraidY q D c p) + c * (D - 1) * D ^ a := by
    calc
      D ^ (a + 1) * BraidY q D c z1 =
          (D ^ a * D) * BraidY q D c z1 := by
        rw [pow_succ]
      _ = D ^ a * (D * BraidY q D c z1) := by ring
      _ = D ^ a * (BraidY q D c z0 + c * (D - 1)) := by rw [hEz1]
      _ = D ^ a * BraidY q D c z0 + c * (D - 1) * D ^ a := by ring
      _ =
          D * (D ^ (a - 1) * BraidY q D c z0) + c * (D - 1) * D ^ a := by
        rw [hleft]
      _ =
          D * (q ^ (a - 1) * BraidY q D c p) + c * (D - 1) * D ^ a := by
        rw [hRunP]
  have hpar :
      D ^ (a + 2) * BraidY q D c z2 =
        D * q ^ a * BraidY q D c p + q * c * (D - 1) * D ^ a := by
    calc
      D ^ (a + 2) * BraidY q D c z2 =
          (D ^ (a + 1) * D) * BraidY q D c z2 := by
        rw [pow_succ]
      _ = D ^ (a + 1) * (D * BraidY q D c z2) := by ring
      _ = D ^ (a + 1) * (q * BraidY q D c z1) := by rw [hAz2]
      _ = q * (D ^ (a + 1) * BraidY q D c z1) := by ring
      _ =
          q * (D * (q ^ (a - 1) * BraidY q D c p) +
            c * (D - 1) * D ^ a) := by
        rw [hYz1]
      _ =
          D * (q ^ (a - 1) * q) * BraidY q D c p +
            q * c * (D - 1) * D ^ a := by
        ring
      _ = D * q ^ a * BraidY q D c p + q * c * (D - 1) * D ^ a := by
        rw [hqpow]
  have hSamePow :
      D ^ (a + 2) * BraidY q D c fin =
        D ^ (a + 2) * BraidY q D c z2 := by
    rw [hYeq]
  have hbalance :
      q ^ a * BraidY q D c n + c * (D - 1) * (D + 1) * D ^ a =
        D * q ^ a * BraidY q D c p + q * c * (D - 1) * D ^ a :=
    hsrc.symm.trans (hSamePow.trans hpar)
  unfold UnsaturatedRelation
  have hL :
      q ^ a * ((q - D) * n - (D - 1) * c) - D * q ^ a * (q - D) * p =
        q ^ a * ((q - D) * n + c) -
          D * q ^ a * ((q - D) * p + c) := by
    ring
  have hR :
      c * (D - 1) * (q - D - 1) * D ^ a =
        q * c * (D - 1) * D ^ a - c * (D - 1) * (D + 1) * D ^ a := by
    ring
  have hmove :
      q ^ a * ((q - D) * n + c) - D * q ^ a * ((q - D) * p + c) =
        q * c * (D - 1) * D ^ a - c * (D - 1) * (D + 1) * D ^ a := by
    unfold BraidY at hbalance
    have hlhs :
        q ^ a * ((q - D) * n + c) =
          (q ^ a * ((q - D) * n + c) + c * (D - 1) * (D + 1) * D ^ a) -
            c * (D - 1) * (D + 1) * D ^ a := by
      ring
    have hrhs :
        D * q ^ a * ((q - D) * p + c) + q * c * (D - 1) * D ^ a -
            c * (D - 1) * (D + 1) * D ^ a =
          (D * q ^ a * ((q - D) * p + c) + q * c * (D - 1) * D ^ a) -
            c * (D - 1) * (D + 1) * D ^ a := by
      ring
    have hsub :
        (q ^ a * ((q - D) * n + c) + c * (D - 1) * (D + 1) * D ^ a) -
            c * (D - 1) * (D + 1) * D ^ a =
          (D * q ^ a * ((q - D) * p + c) + q * c * (D - 1) * D ^ a) -
            c * (D - 1) * (D + 1) * D ^ a := by
      rw [hbalance]
    have hA : q ^ a * ((q - D) * n + c) =
        D * q ^ a * ((q - D) * p + c) + q * c * (D - 1) * D ^ a -
          c * (D - 1) * (D + 1) * D ^ a := by
      rw [hlhs, hsub, ← hrhs]
    calc
      q ^ a * ((q - D) * n + c) - D * q ^ a * ((q - D) * p + c) =
          (D * q ^ a * ((q - D) * p + c) + q * c * (D - 1) * D ^ a -
            c * (D - 1) * (D + 1) * D ^ a) -
            D * q ^ a * ((q - D) * p + c) := by
        rw [hA]
      _ = q * c * (D - 1) * D ^ a - c * (D - 1) * (D + 1) * D ^ a := by
        ring
  calc
    q ^ a * ((q - D) * n - (D - 1) * c) - D * q ^ a * (q - D) * p =
        q ^ a * ((q - D) * n + c) - D * q ^ a * ((q - D) * p + c) := hL
    _ = q * c * (D - 1) * D ^ a - c * (D - 1) * (D + 1) * D ^ a := hmove
    _ = c * (D - 1) * (q - D - 1) * D ^ a := hR.symm

/-- A positive-length coprime unsaturated pair forces the coefficient divisibility. -/
theorem BraidUnsaturatedDivisibility (q c D : ℤ) (a : ℕ) (n p : ℤ) (ha : 1 ≤ a)
    (hcop : IsCoprime q D) (hrel : UnsaturatedRelation q c D a n p) :
    q ^ a ∣ c * (D - 1) * (q - D - 1) := by
  have hsplit : a = (a - 1) + 1 := (Nat.sub_add_cancel ha).symm
  have hdiv :
      q ^ ((a - 1) + 1) ∣
        c * (D - 1) * (q - D - 1) * D ^ ((a - 1) + 1) := by
    rw [← hsplit]
    refine ⟨(q - D) * n - (D - 1) * c - D * (q - D) * p, ?_⟩
    unfold UnsaturatedRelation at hrel
    calc
      c * (D - 1) * (q - D - 1) * D ^ a =
          q ^ a * ((q - D) * n - (D - 1) * c) -
            D * q ^ a * (q - D) * p := by
        exact hrel.symm
      _ = q ^ a * ((q - D) * n - (D - 1) * c - D * (q - D) * p) := by
        ring
  have hcopPow : IsCoprime (q ^ ((a - 1) + 1)) (D ^ ((a - 1) + 1)) :=
    hcop.pow
  have hclean := hcopPow.dvd_of_dvd_mul_right hdiv
  rw [hsplit]
  exact hclean

/-- Divisibility of the coefficient does not realize every integer pair. -/
theorem BraidDivisibilityMissesPair :
    IsCoprime (3 : ℤ) 2 ∧
      (3 : ℤ) ^ 1 ∣ (1 : ℤ) * (2 - 1) * (3 - 2 - 1) ∧
      ¬ UnsaturatedRelation 3 1 2 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨1, -1, by ring⟩
  · exact ⟨0, by ring⟩
  · intro h
    unfold UnsaturatedRelation at h
    have hl :
        (3 : ℤ) ^ 1 * ((3 - 2) * 1 - (2 - 1) * 1) -
          2 * (3 : ℤ) ^ 1 * (3 - 2) * 1 = -6 := by
      ring
    have hr : (1 : ℤ) * (2 - 1) * (3 - 2 - 1) * (2 : ℤ) ^ 1 = 0 := by ring
    rw [hl, hr] at h
    omega

/-- No integers realize the unsaturated relation for slope `5`, offset `1`, divisor `2`. -/
theorem BraidFiveObstruction (a : ℕ) (ha : 1 ≤ a) (n p : ℤ) :
    ¬ UnsaturatedRelation 5 1 2 a n p := by
  intro hrel
  have hcop : IsCoprime (5 : ℤ) 2 := ⟨1, -2, by ring⟩
  have hdiv := BraidUnsaturatedDivisibility 5 1 2 a n p ha hcop hrel
  have hprod : (1 : ℤ) * (2 - 1) * (5 - 2 - 1) = 2 := by ring
  rw [hprod] at hdiv
  have hsplit : a = (a - 1) + 1 := by omega
  have hfive : (5 : ℤ) ∣ (5 : ℤ) ^ a := by
    refine ⟨5 ^ (a - 1), ?_⟩
    rw [hsplit, pow_succ]
    have hidx : (a - 1) + 1 - 1 = a - 1 := by omega
    rw [hidx]
    ring
  rcases Int.dvd_trans hfive hdiv with ⟨k, hk⟩
  omega

/-- The undivided second iterate need not return the seed modulo `D ^ 2`. -/
theorem BraidUndividedGap :
    ¬ (2 : ℤ) ∣ 1 ∧
      ((2 : ℤ) + 1) * 1 + 1 = 4 ∧
      (4 : ℤ) / 2 = 2 ∧
      ¬ ((2 : ℤ) ≡ 1 [ZMOD (2 : ℤ) ^ 2]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rcases h with ⟨k, hk⟩
    omega
  · ring
  · exact Int.ediv_eq_of_eq_mul_right (by decide : (2 : ℤ) ≠ 0) (by ring)
  · intro h
    rw [Int.modEq_iff_dvd] at h
    rcases h with ⟨k, hk⟩
    omega

/-- Closed forms for one saturated pair with no extra parent letters, and one with one. -/
theorem BraidSaturatedNumerals :
    ((4 : ℤ) * 7 ≡ 1 [ZMOD 9]) ∧
      (3 : ℤ) * 7 - 1 = 20 ∧
      (3 : ℤ) ^ 0 * 7 - 1 = 6 ∧
      ((4 : ℤ) * 7 - 1) / 9 = 3 ∧
      ¬ (3 : ℤ) ∣ 20 ∧
      ((4 : ℤ) ^ 2 * 4 ≡ 1 [ZMOD 9]) ∧
      (3 : ℤ) * 4 * 4 - 1 = 47 ∧
      (3 : ℤ) * 4 - 1 = 11 ∧
      ((4 : ℤ) ^ 2 * 4 - 1) / 9 = 7 ∧
      ¬ (3 : ℤ) ∣ 47 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Int.modEq_iff_dvd.mpr ⟨-3, by ring⟩
  · ring
  · ring
  · exact Int.ediv_eq_of_eq_mul_right (by decide : (9 : ℤ) ≠ 0) (by ring)
  · intro h
    rcases h with ⟨k, hk⟩
    omega
  · exact Int.modEq_iff_dvd.mpr ⟨-7, by ring⟩
  · ring
  · ring
  · exact Int.ediv_eq_of_eq_mul_right (by decide : (9 : ℤ) ≠ 0) (by ring)
  · intro h
    rcases h with ⟨k, hk⟩
    omega

end GeneralizedCollatz
