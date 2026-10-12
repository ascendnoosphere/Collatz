/-
Copyright (c) 2026 ascendnoosphere
SPDX-License-Identifier: CC-BY-4.0

Repunit divisors of the offset one raw map.

Write `S_k(q) = 1 + q + ... + q^(k-1)` for the partial sums of the geometric
series.  For the raw map that divides by `D` at multiples of `D` and applies
`n ↦ q n + 1` otherwise, the choice `D = S_k(q)` is special in three ways that
are proved here:

* the divisor identity `(q - 1) S_k = q^k - 1`, hence `D ∣ q^k - 1`, and the
  powers `q^j` with `0 < j < k` are never `1` modulo `D`, so `q` has order
  exactly `k` modulo `D`;
* the orbit of `1` is the explicit primitive cycle
  `1 -> S_2 -> ... -> S_k -> 1` of length `k`, whose first `k` states are the
  pairwise distinct residues `S_1, ..., S_k` modulo `D`;
* the residue walk from zero is that same partial-sum walk reduced modulo `D`,
  so it is periodic with period `k` and its first `k` residues are distinct.

The remaining statements (capture density, the general modulus `M` and the
general offset) are not formalized here.
-/

import GeneralizedCollatz
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Monotone.Basic

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The repunit sum `S_k(q) = 1 + q + ... + q^(k-1)`, the sum of the first `k`
powers of `q`. -/
def RepunitSum (q k : ℕ) : ℕ := (Finset.range k).sum fun j => q ^ j

/-- The raw map of the offset one repunit slice: divide by `D` at multiples of
`D`, apply the affine branch `n ↦ q n + 1` otherwise. -/
def RepunitStep (q D n : ℕ) : ℕ := if D ∣ n then n / D else q * n + 1

/-- The residue map of the offset one slice, `r ↦ q r + 1` reduced modulo `D`. -/
def RepunitResidue (q D r : ℕ) : ℕ := (q * r + 1) % D

/-- The state reached from `n` by `ell` affine events and one division, the
first-division return of the slice. -/
def RepunitReturn (q D ell n : ℕ) : ℕ := (q ^ ell * n + RepunitSum q ell) / D

/-! ## The arithmetic of the repunit sum -/

/-- The empty sum is zero. -/
theorem RepunitSum_zero (q : ℕ) : RepunitSum q 0 = 0 := by
  simp [RepunitSum]

/-- The recurrence that appends the highest power. -/
theorem RepunitSum_succ (q k : ℕ) :
    RepunitSum q (k + 1) = RepunitSum q k + q ^ k := by
  simp [RepunitSum, Finset.sum_range_succ]

/-- The first partial sum is one. -/
theorem RepunitSum_one (q : ℕ) : RepunitSum q 1 = 1 := by
  simp [RepunitSum]

/-- The recurrence that appends one leading term, which is the shape of one
affine event at the offset one. -/
theorem RepunitSum_succ_mul (q k : ℕ) :
    q * RepunitSum q k + 1 = RepunitSum q (k + 1) := by
  induction k with
  | zero => simp [RepunitSum]
  | succ k ih =>
      rw [RepunitSum_succ, RepunitSum_succ, ← ih]
      ring

/-- The repunit sum splits by index blocks: `S_{j+k} = S_j + q^j S_k`. -/
theorem RepunitSum_add (q j k : ℕ) :
    RepunitSum q (j + k) = RepunitSum q j + q ^ j * RepunitSum q k := by
  induction k with
  | zero => simp [RepunitSum]
  | succ k ih =>
      rw [Nat.add_succ, RepunitSum_succ, RepunitSum_succ, ih, pow_add]
      ring

/-- The repunit sum satisfies `(q - 1) S_k = q^k - 1`. -/
theorem RepunitSum_mul_pred (q k : ℕ) (hq : 1 ≤ q) :
    (q - 1) * RepunitSum q k = q ^ k - 1 := by
  induction k with
  | zero => simp [RepunitSum]
  | succ k ih =>
      have hpow : (q - 1) * q ^ k + q ^ k = q ^ (k + 1) := by
        calc (q - 1) * q ^ k + q ^ k
            = ((q - 1) + 1) * q ^ k := by rw [Nat.add_mul, one_mul]
          _ = q * q ^ k := by rw [Nat.sub_add_cancel hq]
          _ = q ^ k * q := by rw [mul_comm]
          _ = q ^ (k + 1) := by rw [pow_succ]
      rw [RepunitSum_succ, Nat.mul_add, ih]
      have hkpos : 1 ≤ q ^ k := Nat.one_le_pow k q hq
      omega

/-- The powers of `q` return to one modulo the repunit sum. -/
theorem RepunitSum_modeq (q k : ℕ) (hq : 1 ≤ q) :
    q ^ k ≡ 1 [MOD RepunitSum q k] := by
  have hsplit : (q - 1) * RepunitSum q k + 1 = q ^ k := by
    have := RepunitSum_mul_pred q k hq
    have hpos : 1 ≤ q ^ k := Nat.one_le_pow k q (by omega)
    omega
  have h0 : (q - 1) * RepunitSum q k ≡ 0 [MOD RepunitSum q k] :=
    Nat.modEq_zero_iff_dvd.mpr ⟨q - 1, mul_comm _ _⟩
  have h1 : (q - 1) * RepunitSum q k + 1 ≡ 0 + 1 [MOD RepunitSum q k] :=
    h0.add (Nat.ModEq.refl 1)
  rw [← hsplit]
  simpa only [zero_add] using h1

/-- The repunit sum splits off its highest power. -/
theorem RepunitSum_eq_pow_add (q k : ℕ) (hk : 1 ≤ k) :
    RepunitSum q k = q ^ (k - 1) + RepunitSum q (k - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, RepunitSum_succ]
  ring

/-- A repunit sum with one term is at least one. -/
theorem RepunitSum_one_le (q k : ℕ) (hk : 0 < k) : 1 ≤ RepunitSum q k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  induction j with
  | zero => simp [RepunitSum]
  | succ j ih =>
      rw [RepunitSum_succ]
      exact le_trans (ih (by omega)) (Nat.le_add_right _ _)

/-- A repunit sum with one term is positive. -/
theorem RepunitSum_pos (q k : ℕ) (hk : 0 < k) : 0 < RepunitSum q k :=
  lt_of_lt_of_le Nat.zero_lt_one (RepunitSum_one_le q k hk)

/-- The repunit sum strictly increases with the number of terms once the base
exceeds one. -/
theorem RepunitSum_lt_succ (q k : ℕ) (hq : 2 ≤ q) :
    RepunitSum q k < RepunitSum q (k + 1) := by
  rw [RepunitSum_succ]
  have hpow : 0 < q ^ k := pow_pos (by omega : (0 : ℕ) < q) k
  omega

/-- The repunit sum grows with the number of terms. -/
theorem RepunitSum_strictMono (q : ℕ) (hq : 2 ≤ q) :
    StrictMono (RepunitSum q) :=
  strictMono_nat_of_lt_succ fun k => RepunitSum_lt_succ q k hq

/-- The repunit sum divides `q^k - 1`. -/
theorem RepunitSum_dvd_pred (q k : ℕ) (hq : 1 ≤ q) :
    RepunitSum q k ∣ q ^ k - 1 :=
  ⟨q - 1, by rw [mul_comm (RepunitSum q k) (q - 1), ← RepunitSum_mul_pred q k hq]⟩

/-- The repunit sum stays below the corresponding power: one more than the sum
of `k` terms is at most `q^k`. -/
theorem RepunitSum_succ_le_pow (q k : ℕ) (hq : 2 ≤ q) :
    RepunitSum q k + 1 ≤ q ^ k := by
  induction k with
  | zero => simp [RepunitSum]
  | succ k ih =>
      rw [RepunitSum_succ]
      calc RepunitSum q k + q ^ k + 1 = (RepunitSum q k + 1) + q ^ k := by ring
        _ ≤ q ^ k + q ^ k := Nat.add_le_add_right ih _
        _ = 2 * q ^ k := by ring
        _ ≤ q * q ^ k := Nat.mul_le_mul_right _ hq
        _ = q ^ (k + 1) := by rw [pow_succ, mul_comm]

/-- The repunit sum is strictly below the corresponding power. -/
theorem RepunitSum_lt_pow (q k : ℕ) (hq : 2 ≤ q) :
    RepunitSum q k < q ^ k :=
  Nat.lt_of_succ_le (RepunitSum_succ_le_pow q k hq)

/-! ## The raw map of the offset one slice -/

/-- An iterate may execute its last instruction after the previous ones. -/
theorem RepunitIterateSuccLast {α : Type*} (f : α → α) (k : ℕ) (x : α) :
    Iterate f (k + 1) x = f (Iterate f k x) := rfl

/-- A multiple of `D` is divided immediately. -/
theorem RepunitStepOfDvd (q D n : ℕ) (h : D ∣ n) : RepunitStep q D n = n / D := by
  rw [RepunitStep, if_pos h]

/-- A non-multiple of `D` takes the affine branch. -/
theorem RepunitStepOfNotDvd (q D n : ℕ) (h : ¬ D ∣ n) :
    RepunitStep q D n = q * n + 1 := by
  rw [RepunitStep, if_neg h]

/-- Zero is a fixed point of the slice. -/
theorem RepunitStep_zero (q D : ℕ) : RepunitStep q D 0 = 0 := by
  rw [RepunitStep, if_pos (dvd_zero D), Nat.zero_div]

/-- Zero is absorbing. -/
theorem RepunitStep_iterate_zero (q D j : ℕ) :
    Iterate (RepunitStep q D) j 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [RepunitIterateSuccLast, ih, RepunitStep_zero]

/-- Zero is the only state that maps to zero. -/
theorem RepunitStep_eq_zero {q D n : ℕ} (h : RepunitStep q D n = 0) : n = 0 := by
  by_cases hD : D ∣ n
  · rw [RepunitStepOfDvd q D n hD] at h
    exact Nat.eq_zero_of_dvd_of_div_eq_zero hD h
  · rw [RepunitStepOfNotDvd q D n hD] at h
    omega

/-! ## The residue walk from zero -/

/-- The residue after `j` affine branches applied to zero is the partial sum
`S_j` reduced modulo `D`. -/
theorem RepunitResidue_iterate_zero (q k j : ℕ) :
    Iterate (RepunitResidue q (RepunitSum q k)) j 0
      = RepunitSum q j % RepunitSum q k := by
  induction j with
  | zero => simp [Iterate, RepunitSum]
  | succ j ih =>
      rw [RepunitIterateSuccLast, ih, RepunitResidue, ← RepunitSum_succ_mul]
      simp only [Nat.mul_mod, Nat.add_mod, Nat.mod_mod]

/-- The residue walk from zero is periodic with period `k`. -/
theorem RepunitResidue_iterate_period (q k j : ℕ) :
    Iterate (RepunitResidue q (RepunitSum q k)) (j + k) 0
      = Iterate (RepunitResidue q (RepunitSum q k)) j 0 := by
  rw [RepunitResidue_iterate_zero, RepunitResidue_iterate_zero, RepunitSum_add,
    mul_comm (q ^ j) (RepunitSum q k), Nat.add_mul_mod_self_left]

/-- The first `k` residues of the walk from zero are pairwise distinct. -/
theorem RepunitResidue_iterate_injective (q k j j' : ℕ) (hq : 2 ≤ q)
    (hj : j < k) (hj' : j' < k)
    (h : RepunitSum q j % RepunitSum q k
      = RepunitSum q j' % RepunitSum q k) : j = j' := by
  have hmono := RepunitSum_strictMono q hq
  rw [Nat.mod_eq_of_lt (hmono hj), Nat.mod_eq_of_lt (hmono hj')] at h
  exact hmono.injective h

/-! ## The primitive cycle of the slice -/

/-- The orbit of one under the repunit slice runs through the partial sums:
after `j < k` steps the state is `S_{j+1}`. -/
theorem RepunitStep_iterate_one (q k j : ℕ) (hq : 2 ≤ q) (hj : j < k) :
    Iterate (RepunitStep q (RepunitSum q k)) j 1 = RepunitSum q (j + 1) := by
  induction j with
  | zero => simp [Iterate, RepunitSum]
  | succ j ih =>
      rw [RepunitIterateSuccLast, ih (by omega)]
      have hlt : RepunitSum q (j + 1) < RepunitSum q k :=
        (RepunitSum_strictMono q hq) (by omega)
      have hpos : 0 < RepunitSum q (j + 1) := RepunitSum_pos q (j + 1) (by omega)
      rw [RepunitStepOfNotDvd q (RepunitSum q k) (RepunitSum q (j + 1))
        (Nat.not_dvd_of_pos_of_lt hpos hlt), RepunitSum_succ_mul]

/-- The orbit of one returns to one after exactly `k` steps: the cycle
`1 -> S_2 -> ... -> S_k -> 1`. -/
theorem RepunitStep_iterate_one_cycle (q k : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) :
    Iterate (RepunitStep q (RepunitSum q k)) k 1 = 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [RepunitIterateSuccLast, RepunitStep_iterate_one q (j + 1) j hq (by omega),
    RepunitStepOfDvd q (RepunitSum q (j + 1)) (RepunitSum q (j + 1)) (dvd_refl _),
    Nat.div_self (RepunitSum_pos q (j + 1) (by omega))]

/-- No step of the cycle returns to one before `k` steps: the cycle is
primitive. -/
theorem RepunitStep_iterate_one_ne (q k j : ℕ) (hq : 2 ≤ q) (h0 : 0 < j)
    (hj : j < k) :
    Iterate (RepunitStep q (RepunitSum q k)) j 1 ≠ 1 := by
  rw [RepunitStep_iterate_one q k j hq hj]
  have hle : RepunitSum q 2 ≤ RepunitSum q (j + 1) :=
    (RepunitSum_strictMono q hq).monotone (by omega)
  have htwo : RepunitSum q 2 = 1 + q := by simp [RepunitSum, Finset.sum_range_succ]
  omega

/-- The powers of `q` below the repunit index are not congruent to one: for
`0 < j < k` the order of `q` modulo `S_k` has not come around yet. -/
theorem RepunitSum_modeq_order (q k j : ℕ) (hq : 2 ≤ q) (h0 : 0 < j) (hj : j < k) :
    ¬ (q ^ j ≡ 1 [MOD RepunitSum q k]) := by
  intro h
  have hlt : q ^ j < RepunitSum q k := by
    have hsplit := RepunitSum_eq_pow_add q k (by omega : 1 ≤ k)
    have hpow : q ^ j ≤ q ^ (k - 1) :=
      Nat.pow_le_pow_right (by omega : 0 < q) (by omega : j ≤ k - 1)
    have hpos : 1 ≤ RepunitSum q (k - 1) := RepunitSum_one_le q (k - 1) (by omega)
    omega
  have hone : 1 < RepunitSum q k := by
    have hle : RepunitSum q 2 ≤ RepunitSum q k :=
      (RepunitSum_strictMono q hq).monotone (by omega)
    have htwo : RepunitSum q 2 = 1 + q := by simp [RepunitSum, Finset.sum_range_succ]
    omega
  have hmod : q ^ j % RepunitSum q k = 1 % RepunitSum q k := h
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hone] at hmod
  have hgt : 1 < q ^ j := by
    have := Nat.lt_pow_self (n := j) (by omega : 1 < q)
    omega
  omega

/-- The unit offset return map fixes one: after `k - 1` affine events the state
`1` is at the multiple `S_k` of `D`, and the division returns it to one. -/
theorem RepunitReturn_fixes_one (q k : ℕ) (hk : 2 ≤ k) :
    RepunitReturn q (RepunitSum q k) (k - 1) 1 = 1 := by
  have hD : 0 < RepunitSum q k := RepunitSum_pos q k (by omega)
  rw [RepunitReturn, mul_one, Nat.add_comm, ← RepunitSum_succ q (k - 1),
    Nat.sub_add_cancel (by omega : 1 ≤ k), Nat.div_self hD]

end GeneralizedCollatz
