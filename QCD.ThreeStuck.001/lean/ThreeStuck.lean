-- SPDX-License-Identifier: CC-BY-4.0
import GeneralizedCollatz
import Mathlib.Data.Nat.MaxPowDiv

/-!
Inverse odd steps and the factor of `3` in the successor.

The inverse odd step is `InverseOdd z = (2 * z - 1) / 3`.
It is exact whenever `3` divides `z + 1`.
Each exact step lowers `padicValNat 3 (· + 1)` by
one. A sequence shorter than that valuation therefore still meets a factor of
`3`, and a sequence of that exact length meets none.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Inverse odd step, as a natural-number quotient. -/
def InverseOdd (z : ℕ) : ℕ := (2 * z - 1) / 3

/-- `3` divides the inverse-odd numerator whenever it divides the successor. -/
theorem InverseOddDivides (z : ℕ) (h : 3 ∣ z + 1) : 3 ∣ 2 * z - 1 := by
  obtain ⟨t, ht⟩ := h
  have hz : z = 3 * t - 1 := by
    calc
      z = (z + 1) - 1 := by rw [Nat.add_sub_cancel]
      _ = 3 * t - 1 := by rw [ht]
  -- `2z - 1 = 3(2t - 1)` once `z + 1 = 3t`.
  refine ⟨2 * t - 1, ?_⟩
  calc
    2 * z - 1 = 2 * (3 * t - 1) - 1 := by rw [hz]
    _ = 2 * (3 * t) - 2 * 1 - 1 := by rw [Nat.mul_sub_left_distrib]
    _ = 6 * t - 2 - 1 := by
      rw [show 2 * (3 * t) = 6 * t by rw [← Nat.mul_assoc], Nat.mul_one]
    _ = 6 * t - 3 := by rw [Nat.sub_sub]
    _ = 3 * (2 * t) - 3 := by
      rw [show 6 * t = 3 * (2 * t) by rw [← Nat.mul_assoc]]
    _ = 3 * (2 * t - 1) := by
      have ht1 : 1 ≤ 2 * t := by
        have hpos : 0 < z + 1 := Nat.succ_pos z
        rw [ht] at hpos
        omega
      omega

/-- The inverse odd step divides exactly, rather than truncating. -/
theorem InverseOddMul (z : ℕ) (h : 3 ∣ z + 1) :
    3 * InverseOdd z = 2 * z - 1 := by
  unfold InverseOdd
  exact Nat.mul_div_cancel' (InverseOddDivides z h)

/-- One exact inverse odd step replaces `z + 1` by `2(z + 1) / 3`. -/
theorem InverseOddSucc (z : ℕ) (h : 3 ∣ z + 1) :
    InverseOdd z + 1 = 2 * (z + 1) / 3 := by
  have hmul := InverseOddMul z h
  have hz : 1 ≤ 2 * z := by
    have h3 : 3 ≤ z + 1 := Nat.le_of_dvd (Nat.succ_pos z) h
    omega
  have hsum : 3 * (InverseOdd z + 1) = 2 * (z + 1) := by
    calc
      3 * (InverseOdd z + 1) = 3 * InverseOdd z + 3 * 1 := by
        rw [Nat.left_distrib]
      _ = 3 * InverseOdd z + 3 := by rw [Nat.mul_one]
      _ = 2 * z - 1 + 3 := by rw [hmul]
      _ = 2 * z - 1 + 1 + 2 := by omega
      _ = 2 * z + 2 := by rw [Nat.sub_add_cancel hz]
      _ = 2 * z + 2 * 1 := by rw [Nat.mul_one]
      _ = 2 * (z + 1) := by rw [← Nat.left_distrib]
  have hdiv := congrArg (fun n => n / 3) hsum
  rw [Nat.mul_div_cancel_left (InverseOdd z + 1) (by decide)] at hdiv
  exact hdiv

/-- The opposite numerator `2z + 1` is never divisible by `3` in this case. -/
theorem PlusSignNotIntegral (z : ℕ) (h : 3 ∣ z + 1) : ¬ 3 ∣ 2 * z + 1 := by
  intro hd
  obtain ⟨t, ht⟩ := h
  obtain ⟨s, hs⟩ := hd
  have hthree : 3 * (2 * t) = 3 * s + 1 := by
    calc
      3 * (2 * t) = 2 * (3 * t) := by
        rw [← Nat.mul_assoc, Nat.mul_comm 3 2, Nat.mul_assoc]
      _ = 2 * (z + 1) := by rw [← ht]
      _ = 2 * z + 2 := by rw [Nat.left_distrib, Nat.mul_one]
      _ = 2 * z + 1 + 1 := by omega
      _ = 3 * s + 1 := by rw [hs]
  have hmod := congrArg (fun n => n % 3) hthree
  rw [Nat.mul_mod_right, Nat.mul_add_mod_self_left,
    Nat.mod_eq_of_lt (by decide : 1 < 3)] at hmod
  exact absurd hmod (by decide)

/-- No power of `2` is divisible by `3`. -/
theorem ThreeNotDvdTwoPow (k : ℕ) : ¬ 3 ∣ 2 ^ k := by
  intro hd
  exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 3) hd (Nat.dvd_refl 3)
    (((by decide : Nat.Coprime 3 2).pow_right k).symm)

/-- A factor coprime to `3` cannot create a factor of `3`. -/
theorem ThreeNotDvdTwoPowMul (k u : ℕ) (hu : ¬ 3 ∣ u) : ¬ 3 ∣ 2 ^ k * u := by
  intro hd
  exact hu
    (((by decide : Nat.Coprime 3 2).pow_right k).dvd_of_dvd_mul_left hd)

/-- A positive integer not divisible by `3` has successor valuation zero at `3`. -/
theorem PadicValNatThreeZeroOfNotDvd (n : ℕ) (hn : n ≠ 0) (h : ¬ 3 ∣ n) :
    padicValNat 3 n = 0 := by
  have hiff :=
    Nat.pow_dvd_iff_le_padicValNat (p := 3) (k := 1) (n := n)
      (by decide : (3 : ℕ) ≠ 1) hn
  have hlt : ¬ 1 ≤ padicValNat 3 n := by
    intro hle
    have hdvd : 3 ^ 1 ∣ n := hiff.mpr hle
    rw [pow_one] at hdvd
    exact h hdvd
  omega

/-- Closed form before cancelling the remaining power of `3`. -/
theorem InverseOddIterateForm (z k : ℕ)
    (hk : k ≤ padicValNat 3 (z + 1)) :
    Iterate InverseOdd k z + 1 =
      2 ^ k * Nat.divMaxPow (z + 1) 3 *
        3 ^ (padicValNat 3 (z + 1) - k) := by
  induction k with
  | zero => {
      simp only [Iterate, Nat.pow_zero, Nat.sub_zero, Nat.one_mul]
      exact (Nat.divMaxPow_mul_pow_padicValNat 3 (z + 1)).symm
    }
  | succ k ih => {
      have hkLe : k ≤ padicValNat 3 (z + 1) := Nat.le_of_succ_le hk
      have ihForm := ih hkLe
      have hindex :
          padicValNat 3 (z + 1) - k =
            padicValNat 3 (z + 1) - (k + 1) + 1 := by
        omega
      -- The remaining power is still positive, so the next division is exact.
      have dvdSucc : 3 ∣ Iterate InverseOdd k z + 1 := by
        rw [ihForm, hindex]
        rw [Nat.pow_succ 3 (padicValNat 3 (z + 1) - (k + 1))]
        refine ⟨2 ^ k * Nat.divMaxPow (z + 1) 3 *
          3 ^ (padicValNat 3 (z + 1) - (k + 1)), ?_⟩
        ac_rfl
      have hstep := InverseOddSucc (Iterate InverseOdd k z) dvdSucc
      have hrec :
          Iterate InverseOdd (k + 1) z =
            InverseOdd (Iterate InverseOdd k z) := by
        simp only [Iterate]
      rw [hrec, hstep, ihForm, hindex]
      rw [Nat.pow_succ 3 (padicValNat 3 (z + 1) - (k + 1))]
      rw [Nat.pow_succ 2 k]
      have hprod :
          2 * (2 ^ k * Nat.divMaxPow (z + 1) 3 *
              (3 ^ (padicValNat 3 (z + 1) - (k + 1)) * 3)) =
            3 * ((2 ^ k * 2) * Nat.divMaxPow (z + 1) 3 *
              3 ^ (padicValNat 3 (z + 1) - (k + 1))) := by
        ac_rfl
      rw [hprod]
      exact Nat.mul_div_cancel_left
        ((2 ^ k * 2) * Nat.divMaxPow (z + 1) 3 *
          3 ^ (padicValNat 3 (z + 1) - (k + 1)))
        (by decide)
    }

/-- Each admissible iterate divides the successor by exactly one factor of `3`. -/
theorem InverseOddIterateQuotient (z k : ℕ)
    (hk : k ≤ padicValNat 3 (z + 1)) :
    Iterate InverseOdd k z + 1 = 2 ^ k * (z + 1) / 3 ^ k := by
  have hform := InverseOddIterateForm z k hk
  have hindex :
      k + (padicValNat 3 (z + 1) - k) = padicValNat 3 (z + 1) := by
    omega
  have hpow :
      3 ^ k * 3 ^ (padicValNat 3 (z + 1) - k) =
        3 ^ padicValNat 3 (z + 1) := by
    rw [← pow_add, hindex]
  have recon := Nat.divMaxPow_mul_pow_padicValNat 3 (z + 1)
  have hmul :
      3 ^ k * (Iterate InverseOdd k z + 1) = 2 ^ k * (z + 1) := by
    calc
      3 ^ k * (Iterate InverseOdd k z + 1) =
          3 ^ k * (2 ^ k * Nat.divMaxPow (z + 1) 3 *
            3 ^ (padicValNat 3 (z + 1) - k)) := by
        rw [hform]
      _ =
          2 ^ k * Nat.divMaxPow (z + 1) 3 *
            (3 ^ k * 3 ^ (padicValNat 3 (z + 1) - k)) := by
        ac_rfl
      _ =
          2 ^ k * Nat.divMaxPow (z + 1) 3 *
            3 ^ padicValNat 3 (z + 1) := by
        rw [hpow]
      _ =
          2 ^ k * (Nat.divMaxPow (z + 1) 3 *
            3 ^ padicValNat 3 (z + 1)) := by
        ac_rfl
      _ = 2 ^ k * (z + 1) := by rw [recon]
  have hdiv := congrArg (fun n => n / 3 ^ k) hmul
  rw [Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide : 0 < 3))] at hdiv
  exact hdiv

/-- The successor valuation falls by exactly the number of inverse odd steps. -/
theorem InverseOddIterateValuation (z k : ℕ)
    (hk : k ≤ padicValNat 3 (z + 1)) :
    padicValNat 3 (Iterate InverseOdd k z + 1) =
      padicValNat 3 (z + 1) - k := by
  have hform := InverseOddIterateForm z k hk
  have recon := Nat.divMaxPow_mul_pow_padicValNat 3 (z + 1)
  have uNonzero : Nat.divMaxPow (z + 1) 3 ≠ 0 := by
    intro hu
    rw [hu, Nat.zero_mul] at recon
    exact Nat.succ_ne_zero z recon.symm
  have notDvdU : ¬ 3 ∣ Nat.divMaxPow (z + 1) 3 :=
    Nat.not_dvd_divMaxPow (by decide : 1 < 3) (Nat.succ_ne_zero z)
  have notDvdProd : ¬ 3 ∣ 2 ^ k * Nat.divMaxPow (z + 1) 3 :=
    ThreeNotDvdTwoPowMul k (Nat.divMaxPow (z + 1) 3) notDvdU
  have prodNonzero : 2 ^ k * Nat.divMaxPow (z + 1) 3 ≠ 0 := by
    intro hzero
    rcases Nat.mul_eq_zero.mp hzero with hk0 | hu0
    · exact (Nat.two_pow_pos k).ne' hk0
    · exact uNonzero hu0
  have vzero := PadicValNatThreeZeroOfNotDvd
    (2 ^ k * Nat.divMaxPow (z + 1) 3) prodNonzero notDvdProd
  -- Swap so the power of `3` is the left factor required by the valuation lemma.
  rw [hform, Nat.mul_comm (2 ^ k * Nat.divMaxPow (z + 1) 3)
    (3 ^ (padicValNat 3 (z + 1) - k)),
    padicValNat_base_pow_mul (by decide : 1 < 3) prodNonzero, vzero,
    Nat.zero_add]

/--
For `k` at most the successor valuation, the iterate is the exact quotient
`2^k(z + 1) / 3^k`, the valuation falls by `k`, and a factor of `3` remains
if and only if `k` is strictly smaller.
-/
theorem InverseOddFactorBudget (z k : ℕ)
    (hk : k ≤ padicValNat 3 (z + 1)) :
    Iterate InverseOdd k z + 1 = 2 ^ k * (z + 1) / 3 ^ k ∧
      padicValNat 3 (Iterate InverseOdd k z + 1) =
        padicValNat 3 (z + 1) - k ∧
      (3 ∣ Iterate InverseOdd k z + 1 ↔ k < padicValNat 3 (z + 1)) := by
  refine ⟨InverseOddIterateQuotient z k hk,
    InverseOddIterateValuation z k hk, ?_⟩
  have hv := InverseOddIterateValuation z k hk
  have hne : Iterate InverseOdd k z + 1 ≠ 0 := Nat.succ_ne_zero _
  have hiff :=
    Nat.pow_dvd_iff_le_padicValNat (p := 3) (k := 1)
      (n := Iterate InverseOdd k z + 1)
      (by decide : (3 : ℕ) ≠ 1) hne
  constructor
  · intro hd
    have hd1 : 3 ^ 1 ∣ Iterate InverseOdd k z + 1 := by
      simpa [pow_one] using hd
    have hle : 1 ≤ padicValNat 3 (Iterate InverseOdd k z + 1) :=
      hiff.mp hd1
    rw [hv] at hle
    omega
  · intro hkLt
    have hle : 1 ≤ padicValNat 3 (Iterate InverseOdd k z + 1) := by
      rw [hv]
      omega
    have hd1 : 3 ^ 1 ∣ Iterate InverseOdd k z + 1 := hiff.mpr hle
    simpa [pow_one] using hd1

/-- Fewer than `v_3(z + 1)` inverse odd steps leave a factor of `3`. -/
theorem InverseOddFewerLeavesFactor (z k : ℕ)
    (hk : k < padicValNat 3 (z + 1)) :
    3 ∣ Iterate InverseOdd k z + 1 :=
  (InverseOddFactorBudget z k (Nat.le_of_lt hk)).2.2.mpr hk

/-- Exactly `v_3(z + 1)` inverse odd steps remove every factor of `3`. -/
theorem InverseOddExactRemoves (z : ℕ) :
    ¬ 3 ∣ Iterate InverseOdd (padicValNat 3 (z + 1)) z + 1 := by
  intro hd
  exact Nat.lt_irrefl _
    ((InverseOddFactorBudget z (padicValNat 3 (z + 1))
      (Nat.le_refl _)).2.2.mp hd)

/-- Every step before the valuation is exhausted is exact division by `3`. -/
theorem InverseOddEarlierExact (z k : ℕ)
    (hk : k < padicValNat 3 (z + 1)) :
    3 * InverseOdd (Iterate InverseOdd k z) =
      2 * Iterate InverseOdd k z - 1 :=
  InverseOddMul (Iterate InverseOdd k z)
    (InverseOddFewerLeavesFactor z k hk)

/-- The seed `2` has successor valuation one and inverse image `1`. -/
theorem InverseOddTwo : InverseOdd 2 = 1 := rfl

/-- The successor of `2` is exactly the first power of `3`. -/
theorem SuccessorValuationTwo : padicValNat 3 (2 + 1) = 1 := by
  have h3 : 2 + 1 = 3 := by decide
  rw [h3]
  exact padicValNat_base (by decide : 1 < 3)

/-- One inverse odd step from `2` removes the only factor of `3`. -/
theorem InverseOddTwoRemoves : ¬ 3 ∣ InverseOdd 2 + 1 := by
  have hnot := InverseOddExactRemoves 2
  rw [SuccessorValuationTwo] at hnot
  have hrec : Iterate InverseOdd 1 2 = InverseOdd 2 := by simp [Iterate]
  rw [hrec] at hnot
  exact hnot

/-- The seed `8` has successor `9 = 3^2`. -/
theorem SuccessorValuationEight : padicValNat 3 (8 + 1) = 2 := by
  have h9 : 8 + 1 = 3 ^ 2 := by decide
  rw [h9]
  exact padicValNat_base_pow (by decide : 1 < 3) 2

/-- The first inverse odd image of `8` is `5`. -/
theorem InverseOddEight : InverseOdd 8 = 5 := rfl

/-- One step from `8` leaves a factor of `3` in the successor. -/
theorem InverseOddEightStill : 3 ∣ InverseOdd 8 + 1 := by
  have hlt : 1 < padicValNat 3 (8 + 1) := by
    rw [SuccessorValuationEight]
    decide
  have hdiv := InverseOddFewerLeavesFactor 8 1 hlt
  have hrec : Iterate InverseOdd 1 8 = InverseOdd 8 := by simp [Iterate]
  rw [hrec, InverseOddEight] at hdiv
  exact hdiv

/-- The second inverse odd image of `8` is `3`. -/
theorem InverseOddEightSecond : InverseOdd (InverseOdd 8) = 3 := by
  rw [InverseOddEight]
  rfl

/-- Two steps from `8` remove every factor of `3` from the successor. -/
theorem InverseOddEightRemoves :
    ¬ 3 ∣ InverseOdd (InverseOdd 8) + 1 := by
  have hnot := InverseOddExactRemoves 8
  rw [SuccessorValuationEight] at hnot
  have hrec : Iterate InverseOdd 2 8 = InverseOdd (InverseOdd 8) := by
    simp [Iterate]
  rw [hrec] at hnot
  exact hnot

end GeneralizedCollatz
