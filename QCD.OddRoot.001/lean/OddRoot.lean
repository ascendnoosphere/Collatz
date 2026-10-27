-- SPDX-License-Identifier: CC-BY-4.0
import GeneralizedCollatz
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
The inverse odd root of an integer translate.

For `z + 1 ≠ 0` and `b = v_3(z + 1)`, the cofactor `m = (z + 1) / 3^b` is an
integer not divisible by `3`. Exactly `b` steps of `n ↦ (2n - 1) / 3` are
integral, and the last state is `R = 2^b * m - 1`. Thus `3` does not divide
`R + 1`, so `3` does not divide `2R - 1`. The odd branch `(3n + 1) / 2`
returns from `R` to `z` in `b` integral steps. None of this asserts that a
classical Collatz trajectory reaches `1`, and `R` itself may be divisible by `3`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.OddRootAnalysis

/-- The `3`-adic valuation of the translate `z + 1`. -/
def OddValuation (z : ℤ) : ℕ :=
  padicValInt 3 (z + 1)

/-- The cofactor `(z + 1) / 3^{v_3(z + 1)}`. -/
def OddCofactor (z : ℤ) : ℤ :=
  (z + 1) / (3 : ℤ) ^ OddValuation z

/-- The inverse odd root `2^{v_3(z + 1)} (z + 1) / 3^{v_3(z + 1)} - 1`. -/
def OddRoot (z : ℤ) : ℤ :=
  (2 : ℤ) ^ OddValuation z * OddCofactor z - 1

/-- One inverse odd step `(2 * n - 1) / 3`. -/
def OddInverseStep (n : ℤ) : ℤ :=
  (2 * n - 1) / 3

/-- The plus and minus inverse numerators differ by two. -/
theorem DistinctInverseNumerators (n : ℤ) :
    (2 * n + 1) - (2 * n - 1) = 2 := by
  omega

/-- One odd branch `(3 * n + 1) / 2` of the shortcut. -/
def OddForwardStep (n : ℤ) : ℤ :=
  (3 * n + 1) / 2

/-- Three divides no power of two. -/
theorem ThreeNotDvdTwoPow (k : ℕ) : ¬ (3 : ℤ) ∣ (2 : ℤ) ^ k := by
  intro hdiv
  have hprime : Prime (3 : ℤ) := Int.prime_three
  have htwo : (3 : ℤ) ∣ 2 := hprime.dvd_of_dvd_pow hdiv
  have hzero : (2 : ℤ) % 3 = 0 := Int.emod_eq_zero_of_dvd htwo
  have hrem : (2 : ℤ) % 3 = 2 :=
    Int.emod_eq_of_lt (by decide) (by decide)
  omega

/-- Move the next factor of two across a product. -/
theorem OddRootFactorTwo (s : ℕ) (c : ℤ) :
    (2 : ℤ) ^ (s + 1) * c = 2 * ((2 : ℤ) ^ s * c) := by
  rw [Int.pow_succ']
  exact Int.mul_assoc 2 ((2 : ℤ) ^ s) c

/-- Move one factor of three from the power into the front of the product. -/
theorem OddRootFactorThree (k s : ℕ) (m : ℤ) :
    (2 : ℤ) ^ k * ((3 : ℤ) ^ (s + 1) * m) =
      3 * ((2 : ℤ) ^ k * ((3 : ℤ) ^ s * m)) := by
  have hpow :
      (2 : ℤ) ^ k * ((3 : ℤ) ^ (s + 1) * m) =
        (2 : ℤ) ^ k * ((3 * (3 : ℤ) ^ s) * m) := by
    exact congrArg (fun w : ℤ => (2 : ℤ) ^ k * (w * m))
      (Int.pow_succ' (3 : ℤ) s)
  have hassoc3 :
      (2 : ℤ) ^ k * ((3 * (3 : ℤ) ^ s) * m) =
        (2 : ℤ) ^ k * (3 * ((3 : ℤ) ^ s * m)) := by
    exact congrArg (fun w : ℤ => (2 : ℤ) ^ k * w)
      (Int.mul_assoc 3 ((3 : ℤ) ^ s) m)
  have hpull :
      (2 : ℤ) ^ k * (3 * ((3 : ℤ) ^ s * m)) =
        ((2 : ℤ) ^ k * 3) * ((3 : ℤ) ^ s * m) := by
    exact (Int.mul_assoc ((2 : ℤ) ^ k) 3 ((3 : ℤ) ^ s * m)).symm
  have hcomm :
      ((2 : ℤ) ^ k * 3) * ((3 : ℤ) ^ s * m) =
        (3 * (2 : ℤ) ^ k) * ((3 : ℤ) ^ s * m) := by
    exact congrArg (fun w : ℤ => w * ((3 : ℤ) ^ s * m))
      (Int.mul_comm ((2 : ℤ) ^ k) 3)
  have hfront :
      (3 * (2 : ℤ) ^ k) * ((3 : ℤ) ^ s * m) =
        3 * ((2 : ℤ) ^ k * ((3 : ℤ) ^ s * m)) := by
    exact Int.mul_assoc 3 ((2 : ℤ) ^ k) ((3 : ℤ) ^ s * m)
  exact hpow.trans (hassoc3.trans (hpull.trans (hcomm.trans hfront)))

/-- The translate is the valuation power times the cofactor. -/
theorem OddCofactorSpec (z : ℤ) :
    z + 1 = (3 : ℤ) ^ OddValuation z * OddCofactor z := by
  have hdiv : (3 : ℤ) ^ OddValuation z ∣ z + 1 := padicValInt_dvd (z + 1)
  rcases hdiv with ⟨m, hm⟩
  have hpow : (3 : ℤ) ^ OddValuation z ≠ 0 :=
    Int.pow_ne_zero (by decide)
  have hq : OddCofactor z = m := by
    unfold OddCofactor OddValuation
    exact Int.ediv_eq_of_eq_mul_right hpow hm
  rw [← hq] at hm
  exact hm

/-- A nonzero translate has a cofactor not divisible by three. -/
theorem OddCofactorNotDiv (z : ℤ) (hz : z + 1 ≠ 0) :
    ¬ (3 : ℤ) ∣ OddCofactor z := by
  intro hdiv
  rcases hdiv with ⟨t, ht⟩
  have spec := OddCofactorSpec z
  have hb : (3 : ℤ) ^ (OddValuation z + 1) ∣ z + 1 := by
    refine ⟨t, ?_⟩
    have hmul :
        (3 : ℤ) ^ OddValuation z * (3 * t) =
          (3 : ℤ) ^ (OddValuation z + 1) * t := by
      have hassoc :=
        (Int.mul_assoc ((3 : ℤ) ^ OddValuation z) 3 t).symm
      have hpow :=
        congrArg (fun w : ℤ => w * t)
          ((Int.pow_succ (3 : ℤ) (OddValuation z)).symm)
      exact hassoc.trans hpow
    calc
      z + 1 = (3 : ℤ) ^ OddValuation z * OddCofactor z := spec
      _ = (3 : ℤ) ^ OddValuation z * (3 * t) := by rw [ht]
      _ = (3 : ℤ) ^ (OddValuation z + 1) * t := hmul
  have hle : OddValuation z + 1 ≤ OddValuation z := by
    have hiff :=
      (padicValInt_dvd_iff (p := 3) (OddValuation z + 1) (z + 1)).1 hb
    cases hiff with
    | inl hzero => {
        exact absurd hzero hz
      }
    | inr hle => {
        exact hle
      }
  omega

/-- Adding one to the root recovers the scaled cofactor. -/
theorem OddRootAddOne (z : ℤ) :
    OddRoot z + 1 = (2 : ℤ) ^ OddValuation z * OddCofactor z := by
  unfold OddRoot
  exact Int.sub_add_cancel ((2 : ℤ) ^ OddValuation z * OddCofactor z) 1

/-- Three does not divide the translate of the root. -/
theorem OddRootAddOneNotDiv (z : ℤ) (hz : z + 1 ≠ 0) :
    ¬ (3 : ℤ) ∣ OddRoot z + 1 := by
  intro hdiv
  rw [OddRootAddOne] at hdiv
  have hprime : Prime (3 : ℤ) := Int.prime_three
  cases hprime.dvd_or_dvd hdiv with
  | inl hpow => {
      exact ThreeNotDvdTwoPow (OddValuation z) hpow
    }
  | inr hcof => {
      exact OddCofactorNotDiv z hz hcof
    }

/-- A translate divisible by three has inverse odd step `2t - 1`. -/
theorem OddInverseStepOfTriple (n t : ℤ) (h : n + 1 = 3 * t) :
    3 * OddInverseStep n = 2 * n - 1 ∧ OddInverseStep n = 2 * t - 1 := by
  have hnum : 2 * n - 1 = 3 * (2 * t - 1) := by
    have hshift : 2 * n - 1 = 2 * (n + 1) - 3 := by omega
    have hsub : 2 * (n + 1) - 3 = 2 * (3 * t) - 3 := by rw [h]
    have hfac : 2 * (3 * t) - 3 = 3 * (2 * t - 1) := by omega
    exact hshift.trans (hsub.trans hfac)
  have hdiv : OddInverseStep n = 2 * t - 1 := by
    unfold OddInverseStep
    exact Int.ediv_eq_of_eq_mul_right (by decide) hnum
  refine ⟨?_, hdiv⟩
  rw [hdiv]
  exact hnum.symm

/-- Closed form of `k ≤ v_3(z + 1)` inverse odd steps. -/
theorem OddInverseClosed (z : ℤ) (k : ℕ) (hk : k ≤ OddValuation z) :
    Iterate OddInverseStep k z =
      (2 : ℤ) ^ k * ((3 : ℤ) ^ (OddValuation z - k) * OddCofactor z) - 1 := by
  revert hk
  induction k with
  | zero => {
      intro _hk
      have hiter : Iterate OddInverseStep 0 z = z := rfl
      rw [hiter, Nat.sub_zero, Int.pow_zero, Int.one_mul]
      have spec := OddCofactorSpec z
      have hz' : z = (z + 1) - 1 := by omega
      exact hz'.trans (congrArg (fun w : ℤ => w - 1) spec)
    }
  | succ k ih => {
      intro hk
      have hkLe : k ≤ OddValuation z := Nat.le_of_succ_le hk
      have ihk := ih hkLe
      have hsplit :
          OddValuation z - k = (OddValuation z - (k + 1)) + 1 := by
        omega
      have hx1 :
          Iterate OddInverseStep k z + 1 =
            (2 : ℤ) ^ k *
              ((3 : ℤ) ^ (OddValuation z - k) * OddCofactor z) := by
        rw [ihk]
        exact Int.sub_add_cancel _ 1
      have htriple :
          Iterate OddInverseStep k z + 1 =
            3 * ((2 : ℤ) ^ k *
              ((3 : ℤ) ^ (OddValuation z - (k + 1)) * OddCofactor z)) := by
        rw [hx1, hsplit]
        exact OddRootFactorThree k (OddValuation z - (k + 1)) (OddCofactor z)
      have hstep :=
        OddInverseStepOfTriple (Iterate OddInverseStep k z)
          ((2 : ℤ) ^ k *
            ((3 : ℤ) ^ (OddValuation z - (k + 1)) * OddCofactor z))
          htriple
      have hnext :
          Iterate OddInverseStep (k + 1) z =
            OddInverseStep (Iterate OddInverseStep k z) := by
        rfl
      rw [hnext, hstep.2]
      apply congrArg (fun w : ℤ => w - 1)
      exact (OddRootFactorTwo k
        ((3 : ℤ) ^ (OddValuation z - (k + 1)) * OddCofactor z)).symm
    }

/-- The `b`-th inverse odd step is the root. -/
theorem OddInverseReachesRoot (z : ℤ) :
    Iterate OddInverseStep (OddValuation z) z = OddRoot z := by
  have h := OddInverseClosed z (OddValuation z) (Nat.le_refl _)
  simp only [Nat.sub_self, Int.pow_zero, Int.one_mul] at h
  unfold OddRoot
  exact h

/-- Each of the `b` inverse steps divides an integral numerator by three. -/
theorem OddInverseStepExact (z : ℤ) (k : ℕ) (hk : k < OddValuation z) :
    (3 : ℤ) * Iterate OddInverseStep (k + 1) z =
      2 * Iterate OddInverseStep k z - 1 := by
  have hx := OddInverseClosed z k (Nat.le_of_lt hk)
  have hsplit :
      OddValuation z - k = (OddValuation z - (k + 1)) + 1 := by
    omega
  have htriple :
      Iterate OddInverseStep k z + 1 =
        3 * ((2 : ℤ) ^ k *
          ((3 : ℤ) ^ (OddValuation z - (k + 1)) * OddCofactor z)) := by
    have hx1 :
        Iterate OddInverseStep k z + 1 =
          (2 : ℤ) ^ k *
            ((3 : ℤ) ^ (OddValuation z - k) * OddCofactor z) := by
      rw [hx]
      exact Int.sub_add_cancel _ 1
    rw [hx1, hsplit]
    exact OddRootFactorThree k (OddValuation z - (k + 1)) (OddCofactor z)
  have hstep :=
    OddInverseStepOfTriple (Iterate OddInverseStep k z)
      ((2 : ℤ) ^ k *
        ((3 : ℤ) ^ (OddValuation z - (k + 1)) * OddCofactor z))
      htriple
  have hnext :
      Iterate OddInverseStep (k + 1) z =
        OddInverseStep (Iterate OddInverseStep k z) := by
    rfl
  rw [hnext]
  exact hstep.1

/-- The inverse odd chain stops at the root. -/
theorem OddRootStops (z : ℤ) (hz : z + 1 ≠ 0) :
    ¬ (3 : ℤ) ∣ 2 * OddRoot z - 1 := by
  intro hdiv
  have hshift : 2 * OddRoot z - 1 + 3 = 2 * (OddRoot z + 1) := by omega
  have hthree : (3 : ℤ) ∣ 2 * (OddRoot z + 1) := by
    have hsum : (3 : ℤ) ∣ 2 * OddRoot z - 1 + 3 :=
      Int.dvd_add hdiv (Int.dvd_refl 3)
    rwa [hshift] at hsum
  rw [OddRootAddOne] at hthree
  have hprime : Prime (3 : ℤ) := Int.prime_three
  cases hprime.dvd_or_dvd hthree with
  | inl htwo => {
      have hpow : (3 : ℤ) ∣ (2 : ℤ) ^ 1 := by
        rw [Int.pow_one]
        exact htwo
      exact ThreeNotDvdTwoPow 1 hpow
    }
  | inr hrest => {
      cases hprime.dvd_or_dvd hrest with
      | inl hpow => {
          exact ThreeNotDvdTwoPow (OddValuation z) hpow
        }
      | inr hcof => {
          exact OddCofactorNotDiv z hz hcof
        }
    }

/-- The inverse odd root is the `b`-step integral chain, and it stops there. -/
theorem OddInverseRoot (z : ℤ) (hz : z + 1 ≠ 0) :
    (∀ k, k ≤ OddValuation z →
      Iterate OddInverseStep k z =
        (2 : ℤ) ^ k * ((3 : ℤ) ^ (OddValuation z - k) * OddCofactor z) - 1) ∧
    (∀ k, k < OddValuation z →
      (3 : ℤ) * Iterate OddInverseStep (k + 1) z =
        2 * Iterate OddInverseStep k z - 1) ∧
    Iterate OddInverseStep (OddValuation z) z = OddRoot z ∧
    ¬ (3 : ℤ) ∣ OddCofactor z ∧
    ¬ (3 : ℤ) ∣ OddRoot z + 1 ∧
    ¬ (3 : ℤ) ∣ 2 * OddRoot z - 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact OddInverseClosed z k hk
  · intro k hk
    exact OddInverseStepExact z k hk
  · exact OddInverseReachesRoot z
  · exact OddCofactorNotDiv z hz
  · exact OddRootAddOneNotDiv z hz
  · exact OddRootStops z hz

/-- An odd state one less than twice `t` has odd branch `3t - 1`. -/
theorem OddForwardStepOfDouble (n t : ℤ) (h : n = 2 * t - 1) :
    2 * OddForwardStep n = 3 * n + 1 ∧ OddForwardStep n = 3 * t - 1 := by
  have hnum : 3 * n + 1 = 2 * (3 * t - 1) := by
    have hsub : 3 * n + 1 = 3 * (2 * t - 1) + 1 := by rw [h]
    have hfac : 3 * (2 * t - 1) + 1 = 2 * (3 * t - 1) := by omega
    exact hsub.trans hfac
  have hdiv : OddForwardStep n = 3 * t - 1 := by
    unfold OddForwardStep
    exact Int.ediv_eq_of_eq_mul_right (by decide) hnum
  refine ⟨?_, hdiv⟩
  rw [hdiv]
  exact hnum.symm

/-- Closed form of `k ≤ v_3(z + 1)` odd-branch steps from the root. -/
theorem OddForwardClosed (z : ℤ) (k : ℕ) (hk : k ≤ OddValuation z) :
    Iterate OddForwardStep k (OddRoot z) =
      (2 : ℤ) ^ (OddValuation z - k) *
        ((3 : ℤ) ^ k * OddCofactor z) - 1 := by
  revert hk
  induction k with
  | zero => {
      intro _hk
      have hiter : Iterate OddForwardStep 0 (OddRoot z) = OddRoot z := rfl
      rw [hiter, Nat.sub_zero, Int.pow_zero, Int.one_mul]
      unfold OddRoot
      rfl
    }
  | succ k ih => {
      intro hk
      have hkLe : k ≤ OddValuation z := Nat.le_of_succ_le hk
      have ihk := ih hkLe
      have hsplit :
          OddValuation z - k = (OddValuation z - (k + 1)) + 1 := by
        omega
      have hy :
          Iterate OddForwardStep k (OddRoot z) =
            2 * ((2 : ℤ) ^ (OddValuation z - (k + 1)) *
              ((3 : ℤ) ^ k * OddCofactor z)) - 1 := by
        rw [ihk, hsplit]
        apply congrArg (fun w : ℤ => w - 1)
        exact OddRootFactorTwo (OddValuation z - (k + 1))
          ((3 : ℤ) ^ k * OddCofactor z)
      have hstep := OddForwardStepOfDouble _ _ hy
      have hnext :
          Iterate OddForwardStep (k + 1) (OddRoot z) =
            OddForwardStep (Iterate OddForwardStep k (OddRoot z)) := by
        rfl
      rw [hnext, hstep.2]
      apply congrArg (fun w : ℤ => w - 1)
      exact (OddRootFactorThree (OddValuation z - (k + 1)) k
        (OddCofactor z)).symm
    }

/-- `b` odd-branch steps return from the root to `z`. -/
theorem OddForwardReaches (z : ℤ) :
    Iterate OddForwardStep (OddValuation z) (OddRoot z) = z := by
  have h := OddForwardClosed z (OddValuation z) (Nat.le_refl _)
  simp only [Nat.sub_self, Int.pow_zero, Int.one_mul] at h
  rw [h, ← OddCofactorSpec z]
  omega

/-- Each odd-branch step before the end divides an even numerator by two. -/
theorem OddForwardStepExact (z : ℤ) (k : ℕ) (hk : k < OddValuation z) :
    (2 : ℤ) * Iterate OddForwardStep (k + 1) (OddRoot z) =
      3 * Iterate OddForwardStep k (OddRoot z) + 1 := by
  have hx := OddForwardClosed z k (Nat.le_of_lt hk)
  have hsplit :
      OddValuation z - k = (OddValuation z - (k + 1)) + 1 := by
    omega
  have hy :
      Iterate OddForwardStep k (OddRoot z) =
        2 * ((2 : ℤ) ^ (OddValuation z - (k + 1)) *
          ((3 : ℤ) ^ k * OddCofactor z)) - 1 := by
    rw [hx, hsplit]
    apply congrArg (fun w : ℤ => w - 1)
    exact OddRootFactorTwo (OddValuation z - (k + 1))
      ((3 : ℤ) ^ k * OddCofactor z)
  have hstep := OddForwardStepOfDouble _ _ hy
  have hnext :
      Iterate OddForwardStep (k + 1) (OddRoot z) =
        OddForwardStep (Iterate OddForwardStep k (OddRoot z)) := by
    rfl
  rw [hnext]
  exact hstep.1

/-- Every strict prefix of the odd return is an odd integer. -/
theorem OddForwardOdd (z : ℤ) (k : ℕ) (hk : k < OddValuation z) :
    ¬ (2 : ℤ) ∣ Iterate OddForwardStep k (OddRoot z) := by
  intro hdiv
  have hx := OddForwardClosed z k (Nat.le_of_lt hk)
  have hsplit :
      OddValuation z - k = (OddValuation z - (k + 1)) + 1 := by
    omega
  rw [hx, hsplit] at hdiv
  let s : ℕ := OddValuation z - (k + 1)
  let c : ℤ := (3 : ℤ) ^ k * OddCofactor z
  have heven : (2 : ℤ) ∣ (2 : ℤ) ^ (s + 1) * c := by
    have hpow := OddRootFactorTwo s c
    rw [hpow]
    exact Int.dvd_mul_right 2 ((2 : ℤ) ^ s * c)
  have hone : (2 : ℤ) ∣ 1 := by
    have hsub :
        (2 : ℤ) ∣ (2 : ℤ) ^ (s + 1) * c -
          ((2 : ℤ) ^ (s + 1) * c - 1) :=
      Int.dvd_sub heven hdiv
    have hid :
        (2 : ℤ) ^ (s + 1) * c - ((2 : ℤ) ^ (s + 1) * c - 1) = 1 := by
      omega
    rwa [hid] at hsub
  have hzero : (1 : ℤ) % 2 = 0 := Int.emod_eq_zero_of_dvd hone
  have hrem : (1 : ℤ) % 2 = 1 := Int.emod_eq_of_lt (by decide) (by decide)
  omega

/-- The odd branch returns to `z`, with odd integral steps on the prefix. -/
theorem OddForwardReturn (z : ℤ) (_hz : z + 1 ≠ 0) :
    (∀ k, k ≤ OddValuation z →
      Iterate OddForwardStep k (OddRoot z) =
        (2 : ℤ) ^ (OddValuation z - k) *
          ((3 : ℤ) ^ k * OddCofactor z) - 1) ∧
    Iterate OddForwardStep (OddValuation z) (OddRoot z) = z ∧
    (∀ k, k < OddValuation z →
      (2 : ℤ) * Iterate OddForwardStep (k + 1) (OddRoot z) =
        3 * Iterate OddForwardStep k (OddRoot z) + 1) ∧
    (∀ k, k < OddValuation z →
      ¬ (2 : ℤ) ∣ Iterate OddForwardStep k (OddRoot z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    exact OddForwardClosed z k hk
  · exact OddForwardReaches z
  · intro k hk
    exact OddForwardStepExact z k hk
  · intro k hk
    exact OddForwardOdd z k hk

/-- Every power of two is an integer at least `1`. -/
theorem OneLeTwoPow (k : ℕ) : (1 : ℤ) ≤ (2 : ℤ) ^ k := by
  induction k with
  | zero => {
      simp
    }
  | succ k ih => {
      rw [Int.pow_succ']
      have hmul : (2 : ℤ) * 1 ≤ (2 : ℤ) * (2 : ℤ) ^ k :=
        Int.mul_le_mul_of_nonneg_left ih (by decide)
      rw [Int.mul_one] at hmul
      exact Int.le_trans (by decide : (1 : ℤ) ≤ 2) hmul
    }

/-- Powers of two do not exceed the same powers of three. -/
theorem TwoPowLeThreePow (k : ℕ) : (2 : ℤ) ^ k ≤ (3 : ℤ) ^ k := by
  induction k with
  | zero => {
      simp
    }
  | succ k ih => {
      rw [Int.pow_succ', Int.pow_succ']
      have hleft : (2 : ℤ) * (2 : ℤ) ^ k ≤ (3 : ℤ) * (2 : ℤ) ^ k := by
        exact Int.mul_le_mul_of_nonneg_right (by decide : (2 : ℤ) ≤ 3)
          (Int.le_of_lt (Int.pow_pos (by decide : (0 : ℤ) < 2)))
      have hright : (3 : ℤ) * (2 : ℤ) ^ k ≤ (3 : ℤ) * (3 : ℤ) ^ k := by
        exact Int.mul_le_mul_of_nonneg_left ih (by decide)
      exact Int.le_trans hleft hright
    }

/-- For a nonnegative seed the root lies between `0` and the seed. -/
theorem OddRootBounds (z : ℤ) (_hz : 0 ≤ z) :
    0 ≤ OddRoot z ∧ OddRoot z ≤ z := by
  have hz1 : z + 1 ≠ 0 := by omega
  have spec := OddCofactorSpec z
  have hpow : (0 : ℤ) < (3 : ℤ) ^ OddValuation z :=
    Int.pow_pos (by decide : (0 : ℤ) < 3)
  have hm0 : OddCofactor z ≠ 0 := by
    intro hm
    apply hz1
    rw [spec, hm, Int.mul_zero]
  have hmPos : (0 : ℤ) < OddCofactor z := by
    rcases Int.lt_trichotomy (OddCofactor z) 0 with hlt | heq | hgt
    · have hneg : OddCofactor z < 0 := hlt
      have ht : (0 : ℤ) < -OddCofactor z :=
        Int.neg_pos_of_neg hneg
      have hnonneg :
          (0 : ℤ) ≤ (3 : ℤ) ^ OddValuation z * -OddCofactor z :=
        Int.mul_nonneg (Int.le_of_lt hpow) (Int.le_of_lt ht)
      have hnegProd :
          (3 : ℤ) ^ OddValuation z * OddCofactor z ≤ 0 := by
        have hid :
            (3 : ℤ) ^ OddValuation z * OddCofactor z =
              -((3 : ℤ) ^ OddValuation z * -OddCofactor z) := by
          rw [Int.mul_neg, Int.neg_neg]
        rw [hid]
        exact Int.neg_nonpos_of_nonneg hnonneg
      have hpos :
          (0 : ℤ) < (3 : ℤ) ^ OddValuation z * OddCofactor z := by
        rw [← spec]
        omega
      exact absurd hnegProd (not_le_of_gt hpos)
    · exact absurd heq hm0
    · exact hgt
  have hm1 : (1 : ℤ) ≤ OddCofactor z := by omega
  have htwo : (1 : ℤ) ≤ (2 : ℤ) ^ OddValuation z := OneLeTwoPow _
  have hscale :
      (2 : ℤ) ^ OddValuation z * 1 ≤
        (2 : ℤ) ^ OddValuation z * OddCofactor z :=
    Int.mul_le_mul_of_nonneg_left hm1
      (Int.le_of_lt (Int.pow_pos (by decide : (0 : ℤ) < 2)))
  have hge : (1 : ℤ) ≤ (2 : ℤ) ^ OddValuation z * OddCofactor z := by
    have hone : (1 : ℤ) ≤ (2 : ℤ) ^ OddValuation z * 1 := by
      rw [Int.mul_one]
      exact htwo
    exact Int.le_trans hone hscale
  have hlow : (0 : ℤ) ≤ OddRoot z := by
    unfold OddRoot
    exact Int.sub_nonneg.mpr hge
  have hcmp :
      (2 : ℤ) ^ OddValuation z * OddCofactor z ≤
        (3 : ℤ) ^ OddValuation z * OddCofactor z :=
    Int.mul_le_mul_of_nonneg_right (TwoPowLeThreePow _) (Int.le_of_lt hmPos)
  have hhigh : OddRoot z ≤ z := by
    unfold OddRoot
    have hzEq : z = (3 : ℤ) ^ OddValuation z * OddCofactor z - 1 := by
      have hsub : z = (z + 1) - 1 := by omega
      exact hsub.trans (congrArg (fun w : ℤ => w - 1) spec)
    conv_rhs => rw [hzEq]
    exact Int.sub_le_sub_right hcmp 1
  exact ⟨hlow, hhigh⟩

/-- At `z = 8` the root equals `3`, so three may divide the root. -/
theorem OddRootEight : OddRoot 8 = 3 ∧ (3 : ℤ) ∣ OddRoot 8 := by
  have hsum : (8 : ℤ) + 1 = 9 := by decide
  have hnat : (9 : ℕ) = 3 ^ 2 := by decide
  have hval : OddValuation 8 = 2 := by
    unfold OddValuation
    rw [hsum]
    have hof : padicValInt 3 (9 : ℤ) = padicValNat 3 9 := padicValInt.of_nat
    rw [hof, hnat]
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact padicValNat.prime_pow 2
  have hcof : OddCofactor 8 = 1 := by
    have spec := OddCofactorSpec 8
    rw [hval, hsum] at spec
    have heq : (3 : ℤ) ^ 2 * OddCofactor 8 = (3 : ℤ) ^ 2 * 1 := by
      rw [spec.symm]
      decide
    exact Int.eq_of_mul_eq_mul_left (by decide) heq
  have hroot : OddRoot 8 = 3 := by
    unfold OddRoot
    rw [hval, hcof]
    decide
  exact ⟨hroot, by simp [hroot]⟩

/-- At `z = -4` the root equals `-3`, which is strictly larger than `z`. -/
theorem OddRootNegFour : OddRoot (-4) = -3 ∧ -4 < OddRoot (-4) := by
  have hsum : (-4 : ℤ) + 1 = -3 := by decide
  have hval : OddValuation (-4) = 1 := by
    unfold OddValuation
    rw [hsum]
    unfold padicValInt
    have habs : ((-3 : ℤ).natAbs) = 3 := by decide
    rw [habs]
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hprime : padicValNat 3 (3 ^ 1) = 1 := padicValNat.prime_pow 1
    rw [pow_one] at hprime
    exact hprime
  have hcof : OddCofactor (-4) = -1 := by
    have spec := OddCofactorSpec (-4)
    rw [hval, hsum] at spec
    have heq : (3 : ℤ) ^ 1 * OddCofactor (-4) = (3 : ℤ) ^ 1 * (-1) := by
      rw [spec.symm]
      decide
    exact Int.eq_of_mul_eq_mul_left (by decide) heq
  have hroot : OddRoot (-4) = -3 := by
    unfold OddRoot
    rw [hval, hcof]
    decide
  exact ⟨hroot, by rw [hroot]; decide⟩

end GeneralizedCollatz.OddRootAnalysis
