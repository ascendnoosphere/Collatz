-- SPDX-License-Identifier: CC-BY-4.0
import Homogeneous
import Mathlib.Data.Nat.MaxPowDiv

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The unit-multiplier exponent update removes one available divisor factor. -/
def UnitExponentStep (k : ℕ) : ℕ := k - 1

/-- One unit-multiplier step preserves the base-free factor and updates its exponent. -/
theorem UnitStepRepresentation (D r k : ℕ) (DLower : 2 ≤ D)
    (baseFree : ¬D ∣ r) :
    PositiveHomogeneousStep 1 D (r * D ^ k) = r * D ^ UnitExponentStep k := by
  cases k with
  | zero => {
      simp [PositiveHomogeneousStep, UnitExponentStep, baseFree]
    }
  | succ k => {
      have DPositive : 0 < D := lt_of_lt_of_le Nat.zero_lt_two DLower
      have divides : D ∣ r * D ^ (k + 1) := by
        simpa [pow_succ, Nat.mul_assoc] using dvd_mul_left D (r * D ^ k)
      rw [PositiveHomogeneousStep, if_pos divides, UnitExponentStep]
      rw [pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ DPositive]
      congr 2
    }

/-- Repeated unit-multiplier exponent updates subtract the elapsed raw time. -/
theorem UnitExponentIterate (j k : ℕ) :
    (UnitExponentStep^[j]) k = k - j := by
  induction j with
  | zero => {
      simp
    }
  | succ j inductionHypothesis => {
      rw [Function.iterate_succ_apply', inductionHypothesis]
      simp [UnitExponentStep, Nat.sub_sub]
    }

/-- Unit-multiplier raw iterates have an exact base-free normal form. -/
theorem UnitIterateRepresentation (D r k j : ℕ) (DLower : 2 ≤ D)
    (baseFree : ¬D ∣ r) :
    Iterate (PositiveHomogeneousStep 1 D) j (r * D ^ k) = r * D ^ (k - j) := by
  induction j with
  | zero => {
      simp [Iterate]
    }
  | succ j inductionHypothesis => {
      rw [Iterate, inductionHypothesis]
      rw [UnitStepRepresentation D r (k - j) DLower baseFree]
      simp [UnitExponentStep, Nat.sub_sub]
    }

/-- Any base-free representation agrees with the canonical whole-base data. -/
theorem UnitNormalFormUnique (D n r k : ℕ) (DLower : 2 ≤ D)
    (nPositive : 0 < n) (representation : r * D ^ k = n) (baseFree : ¬D ∣ r) :
    r = n.divMaxPow D ∧ k = padicValNat D n := by
  have rNonzero : r ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at representation
    omega
  have freeData := Nat.maxPowDvdDiv_of_not_dvd baseFree
  have freeFactor : r.divMaxPow D = r := congrArg Prod.snd freeData
  have freeExponent : padicValNat D r = 0 := congrArg Prod.fst freeData
  constructor
  · rw [← representation, Nat.mul_comm, Nat.divMaxPow_base_pow_mul (by omega)]
    exact freeFactor.symm
  · rw [← representation, Nat.mul_comm, padicValNat_base_pow_mul (by omega) rNonzero]
    simp [freeExponent]

/-- Every positive seed has the canonical exact unit-multiplier iterate formula. -/
theorem UnitSeedIterateRepresentation (D n j : ℕ) (DLower : 2 ≤ D)
    (nPositive : 0 < n) :
    Iterate (PositiveHomogeneousStep 1 D) j n =
      n.divMaxPow D * D ^ (padicValNat D n - j) := by
  have factorFree : ¬D ∣ n.divMaxPow D := by
    exact Nat.not_dvd_divMaxPow (lt_of_lt_of_le Nat.one_lt_two DLower)
      (Nat.ne_of_gt nPositive)
  let r := n.divMaxPow D
  let k := padicValNat D n
  change Iterate (PositiveHomogeneousStep 1 D) j n = r * D ^ (k - j)
  have reconstruction : r * D ^ k = n := Nat.divMaxPow_mul_pow_padicValNat D n
  rw [← reconstruction]
  exact UnitIterateRepresentation D r k j DLower factorFree

/-- Zero is fixed by division precedence. -/
theorem UnitZeroFixed (D : ℕ) : PositiveHomogeneousStep 1 D 0 = 0 := by
  simp [PositiveHomogeneousStep]

/-- The canonical base-free factor is fixed by the unit-multiplier map. -/
theorem UnitBaseFreeFixed (D r : ℕ) (baseFree : ¬D ∣ r) :
    PositiveHomogeneousStep 1 D r = r := by
  simp [PositiveHomogeneousStep, baseFree]

/-- The positive fixed points are exactly the states not divisible by `D`. -/
theorem UnitPositiveFixedIff (D n : ℕ) (DLower : 2 ≤ D) (nPositive : 0 < n) :
    PositiveHomogeneousStep 1 D n = n ↔ ¬D ∣ n := by
  constructor
  · intro fixed divides
    simp only [PositiveHomogeneousStep, if_pos divides] at fixed
    have strict := Nat.div_lt_self nPositive DLower
    omega
  · intro baseFree
    exact UnitBaseFreeFixed D n baseFree

/-- A positive seed does not reach its canonical `D`-free factor before its initial
`D`-adic exponent has elapsed. -/
theorem UnitNoEarlyFixed (D n j : ℕ) (DLower : 2 ≤ D)
    (nPositive : 0 < n) (jBefore : j < padicValNat D n) :
    Iterate (PositiveHomogeneousStep 1 D) j n ≠ n.divMaxPow D := by
  rw [UnitSeedIterateRepresentation D n j DLower nPositive]
  have factorPositive : 0 < n.divMaxPow D := by
    have reconstruction := Nat.divMaxPow_mul_pow_padicValNat D n
    by_contra notPositive
    have factorZero : n.divMaxPow D = 0 := Nat.eq_zero_of_not_pos notPositive
    rw [factorZero, zero_mul] at reconstruction
    omega
  have exponentPositive : 0 < padicValNat D n - j := Nat.sub_pos_of_lt jBefore
  have powerGreater : 1 < D ^ (padicValNat D n - j) :=
    Nat.one_lt_pow (Nat.ne_of_gt exponentPositive) DLower
  exact Nat.ne_of_gt (lt_mul_of_one_lt_right factorPositive powerGreater)

/-- Every positive unit-multiplier orbit reaches its canonical fixed point exactly. -/
theorem UnitEventuallyFixed (D n : ℕ) (DLower : 2 ≤ D) (nPositive : 0 < n) :
    let r := n.divMaxPow D
    let k := padicValNat D n
    Iterate (PositiveHomogeneousStep 1 D) k n = r ∧
      ∀ j, Iterate (PositiveHomogeneousStep 1 D) (k + j) n = r := by
  intro r k
  constructor
  · rw [UnitSeedIterateRepresentation D n k DLower nPositive]
    rw [Nat.sub_self, pow_zero, mul_one]
  · intro j
    rw [UnitSeedIterateRepresentation D n (k + j) DLower nPositive]
    rw [Nat.sub_eq_zero_of_le (Nat.le_add_right k j), pow_zero, mul_one]

/-- One unit-multiplier raw step never increases a natural-number state. -/
theorem UnitStepLe (D n : ℕ) : PositiveHomogeneousStep 1 D n ≤ n := by
  simp only [PositiveHomogeneousStep]
  split
  · exact Nat.div_le_self _ _
  · simp

/-- Every unit-multiplier raw iterate is bounded by its initial state. -/
theorem UnitIterateLe (D n j : ℕ) :
    Iterate (PositiveHomogeneousStep 1 D) j n ≤ n := by
  induction j with
  | zero => {
      simp [Iterate]
    }
  | succ j inductionHypothesis => {
      simp only [Iterate]
      exact le_trans (UnitStepLe D _) inductionHypothesis
    }

/-- Every positive-period return is a positive base-free fixed point. -/
theorem UnitPositivePeriodicIffFixed (D n p : ℕ) (DLower : 2 ≤ D)
    (nPositive : 0 < n) (pPositive : 0 < p) :
    Iterate (PositiveHomogeneousStep 1 D) p n = n ↔ ¬D ∣ n := by
  constructor
  · intro returned divides
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pPositive)
    rw [← IterateFirst] at returned
    have noIncrease := UnitIterateLe D (PositiveHomogeneousStep 1 D n) s
    rw [returned] at noIncrease
    have strict : PositiveHomogeneousStep 1 D n < n := by
      simp only [PositiveHomogeneousStep, if_pos divides]
      exact Nat.div_lt_self nPositive DLower
    exact (Nat.not_le_of_lt strict) noIncrease
  · intro baseFree
    clear pPositive
    induction p with
    | zero => {
        rfl
      }
    | succ p inductionHypothesis => {
        rw [Iterate, inductionHypothesis, UnitBaseFreeFixed D n baseFree]
      }

end GeneralizedCollatz
