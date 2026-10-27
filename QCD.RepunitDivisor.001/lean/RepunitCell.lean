/-
Copyright (c) 2026 ascendnoosphere
SPDX-License-Identifier: CC-BY-4.0

Divisibility by the repunit sum on the displayed cells.

For `q ≥ 1` write `G_k(q) = 1 + q + … + q^(k-1)`. The identity proved here is
`q^k = 1 + (q - 1) G_k(q)`, hence `G_k(q)` divides `q^k - 1` and
`q^k ≡ 1` modulo `G_k(q)`. For `k ≥ 1` one also has `G_k(q) ≡ 1` modulo `q`
and `gcd(q, G_k(q)) = 1`. Consequently `k` iterations of `x ↦ q x + c` are
congruent to the input modulo `G_k(q)`.

The five displayed cells are `(q, c, D) = (2, 1, 3), (2, 1, 7), (2, 1, 15),
(3, 1, 4), (3, 1, 13)`, with indices `k = 2, 3, 4, 2, 3`. On each cell `D`
equals `G_k(q)` and the same congruences hold for offset `c = 1`.

This does not prove density of escaping seeds, a contracting core, uniqueness
of a raw cycle, the Hull–Dobell criterion, or the comparison `2 ρ ≤ μ ≤ 4 ρ`.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

namespace GeneralizedCollatz.RepunitCell

/-- The repunit sum `G_k(q) = 1 + q + … + q^(k-1)`. -/
def RepunitSum (q k : ℕ) : ℕ :=
  (Finset.range k).sum fun j => q ^ j

/-- The empty repunit sum is zero. -/
theorem RepunitSumZero (q : ℕ) : RepunitSum q 0 = 0 := by
  rw [RepunitSum, Finset.sum_range_zero]

/-- The repunit sum of one power is `1`. -/
theorem RepunitSumOne (q : ℕ) : RepunitSum q 1 = 1 := by
  rw [RepunitSum, Finset.sum_range_one, Nat.pow_zero]

/-- Appending the next power of the base. -/
theorem RepunitSumSucc (q k : ℕ) :
    RepunitSum q (k + 1) = RepunitSum q k + q ^ k := by
  rw [RepunitSum, RepunitSum, Finset.sum_range_succ]

/-- One affine step sends a repunit sum to the next: `q G_k(q) + 1 = G_{k+1}(q)`. -/
theorem RepunitSumSuccMul (q k : ℕ) :
    q * RepunitSum q k + 1 = RepunitSum q (k + 1) := by
  induction k with
  | zero =>
    {
      { rw [RepunitSumZero, RepunitSumOne, Nat.mul_zero, Nat.zero_add] }
    }
  | succ k ih =>
    {
      { calc
          q * RepunitSum q (k + 1) + 1
              = q * (RepunitSum q k + q ^ k) + 1 := by
                rw [RepunitSumSucc]
          _ = q * RepunitSum q k + q * q ^ k + 1 := by
                rw [Nat.mul_add]
          _ = q * RepunitSum q k + 1 + q * q ^ k := by
                rw [Nat.add_assoc, Nat.add_comm (q * q ^ k) 1, ← Nat.add_assoc]
          _ = RepunitSum q (k + 1) + q * q ^ k := by
                rw [ih]
          _ = RepunitSum q (k + 1) + q ^ (k + 1) := by
                rw [← Nat.pow_succ']
          _ = RepunitSum q (k + 1 + 1) := by
                rw [← RepunitSumSucc] }
    }

/-- The closed geometric identity `q^k = 1 + (q - 1) G_k(q)` for `q ≥ 1`. -/
theorem RepunitSumGeom (q k : ℕ) (hq : 1 ≤ q) :
    q ^ k = 1 + (q - 1) * RepunitSum q k := by
  induction k with
  | zero =>
    {
      { rw [RepunitSumZero, Nat.pow_zero, Nat.mul_zero, Nat.add_zero] }
    }
  | succ k ih =>
    {
      { rw [RepunitSumSucc, Nat.mul_add, ← Nat.add_assoc, ← ih]
        -- Goal: `q^(k+1) = q^k + (q-1) q^k`.
        have factor : q ^ k + (q - 1) * q ^ k = q ^ (k + 1) := by
          { calc
              q ^ k + (q - 1) * q ^ k
                  = 1 * q ^ k + (q - 1) * q ^ k := by
                    rw [Nat.one_mul]
              _ = (q - 1) * q ^ k + 1 * q ^ k := by
                    rw [Nat.add_comm]
              _ = ((q - 1) + 1) * q ^ k := by
                    rw [← Nat.add_mul]
              _ = q * q ^ k := by
                    rw [Nat.sub_add_cancel hq]
              _ = q ^ (k + 1) := by
                    rw [← Nat.pow_succ'] }
        exact factor.symm }
    }

/-- The cofactor form `(q - 1) G_k(q) = q^k - 1`. -/
theorem RepunitSumMulPred (q k : ℕ) (hq : 1 ≤ q) :
    (q - 1) * RepunitSum q k = q ^ k - 1 := by
  rw [← Nat.add_sub_cancel_left 1 ((q - 1) * RepunitSum q k), ← RepunitSumGeom q k hq]

/-- The repunit sum divides `q^k - 1`. -/
theorem RepunitSumDvd (q k : ℕ) (hq : 1 ≤ q) :
    RepunitSum q k ∣ q ^ k - 1 :=
  ⟨q - 1,
    (RepunitSumMulPred q k hq).symm.trans
      (Nat.mul_comm (q - 1) (RepunitSum q k))⟩

/-- The base power returns to one modulo the repunit sum. -/
theorem RepunitSumModeq (q k : ℕ) (hq : 1 ≤ q) :
    q ^ k ≡ 1 [MOD RepunitSum q k] := by
  have geom := RepunitSumGeom q k hq
  rw [geom, Nat.add_comm]
  simp

/-- The repunit sum splits off its constant term: `G_{k+1}(q) = 1 + q G_k(q)`. -/
theorem RepunitSumOneAdd (q k : ℕ) :
    RepunitSum q (k + 1) = 1 + q * RepunitSum q k := by
  rw [← RepunitSumSuccMul q k, Nat.add_comm]

/-- For a positive number of terms, `G_k(q) ≡ 1` modulo `q`. -/
theorem RepunitSumModBase (q k : ℕ) (hk : 0 < k) :
    RepunitSum q k ≡ 1 [MOD q] := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [RepunitSumOneAdd, Nat.add_comm]
  simp

/-- For a positive number of terms, `q` is coprime to `G_k(q)`. -/
theorem RepunitSumCoprime (q k : ℕ) (hk : 0 < k) :
    Nat.Coprime q (RepunitSum q k) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [RepunitSumOneAdd, Nat.add_comm]
  refine (Nat.coprime_mul_left_add_right q 1 (RepunitSum q t)).mpr ?_
  rw [Nat.Coprime, Nat.gcd_one_right]

/-- `k` affine steps have the closed value `q^k r + c G_k(q)`. -/
theorem RepunitAffineClosed (q c k r : ℕ) :
    (fun x => q * x + c)^[k] r = q ^ k * r + c * RepunitSum q k := by
  induction k with
  | zero =>
    {
      { rw [Function.iterate_zero_apply, Nat.pow_zero, Nat.one_mul,
          RepunitSumZero, Nat.mul_zero, Nat.add_zero] }
    }
  | succ k ih =>
    {
      { rw [Function.iterate_succ_apply', ih]
        calc
          q * (q ^ k * r + c * RepunitSum q k) + c
              = q * (q ^ k * r) + q * (c * RepunitSum q k) + c := by
                rw [Nat.mul_add]
          _ = (q * q ^ k) * r + q * (c * RepunitSum q k) + c := by
                conv_lhs =>
                  arg 1
                  arg 1
                  rw [← Nat.mul_assoc]
          _ = q ^ (k + 1) * r + q * (c * RepunitSum q k) + c := by
                rw [← Nat.pow_succ']
          _ = q ^ (k + 1) * r + (q * c) * RepunitSum q k + c := by
                conv_lhs =>
                  arg 1
                  arg 2
                  rw [← Nat.mul_assoc]
          _ = q ^ (k + 1) * r + (c * q) * RepunitSum q k + c := by
                rw [Nat.mul_comm q c]
          _ = q ^ (k + 1) * r + c * (q * RepunitSum q k) + c := by
                rw [Nat.mul_assoc]
          _ = q ^ (k + 1) * r + (c * (q * RepunitSum q k) + c) := by
                rw [Nat.add_assoc]
          _ = q ^ (k + 1) * r + (c * (q * RepunitSum q k) + c * 1) := by
                conv_lhs =>
                  arg 2
                  arg 2
                  rw [← Nat.mul_one c]
          _ = q ^ (k + 1) * r + c * (q * RepunitSum q k + 1) := by
                rw [← Nat.mul_add]
          _ = q ^ (k + 1) * r + c * RepunitSum q (k + 1) := by
                rw [RepunitSumSuccMul] }
    }

/-- The `k`-fold affine map is the identity modulo `G_k(q)`. -/
theorem RepunitAffineModId (q c k r : ℕ) (hq : 1 ≤ q) :
    (fun x => q * x + c)^[k] r ≡ r [MOD RepunitSum q k] := by
  rw [RepunitAffineClosed]
  have power : q ^ k * r ≡ 1 * r [MOD RepunitSum q k] :=
    (RepunitSumModeq q k hq).mul_right r
  have offset : c * RepunitSum q k ≡ 0 [MOD RepunitSum q k] :=
    Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_mul_left (RepunitSum q k) c)
  have sumCong := power.add offset
  simpa [Nat.one_mul, Nat.add_zero] using sumCong

/-- Signed offsets and signed seeds obey the same integral affine closed form. -/
theorem RepunitAffineClosedInt (q k : ℕ) (c r : ℤ) :
    (fun x : ℤ => (q : ℤ) * x + c)^[k] r =
      (q : ℤ) ^ k * r + c * (RepunitSum q k : ℤ) := by
  induction k with
  | zero => {
      simp [RepunitSumZero]
    }
  | succ k ih => {
      rw [Function.iterate_succ_apply', ih, ← RepunitSumSuccMul]
      push_cast
      ring
    }

/-- The integral affine return retains arbitrary signed offset and seed. -/
theorem RepunitAffineModIdInt (q k : ℕ) (c r : ℤ) (hq : 1 ≤ q) :
    (fun x : ℤ => (q : ℤ) * x + c)^[k] r ≡ r [ZMOD (RepunitSum q k : ℤ)] := by
  rw [RepunitAffineClosedInt, Int.modEq_iff_dvd]
  have hgeom := RepunitSumGeom q k hq
  have hcast : (q : ℤ) ^ k = 1 + (q - 1 : ℕ) * (RepunitSum q k : ℤ) := by
    exact_mod_cast hgeom
  refine ⟨-((q - 1 : ℕ) * r + c), ?_⟩
  rw [hcast]
  ring

/-- Two-term repunit sum: `G_2(q) = 1 + q`. -/
theorem RepunitSumTwo (q : ℕ) : RepunitSum q 2 = 1 + q := by
  have h2 : (2 : ℕ) = 1 + 1 := by decide
  rw [h2, RepunitSumSucc, RepunitSumOne, Nat.pow_one]

/-- Three-term repunit sum: `G_3(q) = 1 + q + q^2`. -/
theorem RepunitSumThree (q : ℕ) : RepunitSum q 3 = 1 + q + q ^ 2 := by
  have h3 : (3 : ℕ) = 2 + 1 := by decide
  rw [h3, RepunitSumSucc, RepunitSumTwo]

/-- Four-term repunit sum: `G_4(q) = 1 + q + q^2 + q^3`. -/
theorem RepunitSumFour (q : ℕ) : RepunitSum q 4 = 1 + q + q ^ 2 + q ^ 3 := by
  have h4 : (4 : ℕ) = 3 + 1 := by decide
  rw [h4, RepunitSumSucc, RepunitSumThree]

/-- Divisibility data of one parameter cell with divisor `D`. -/
def CellDivisible (q k D : ℕ) : Prop :=
  RepunitSum q k = D ∧
    q ^ k = 1 + (q - 1) * D ∧
    (q - 1) * D = q ^ k - 1 ∧
    D ∣ q ^ k - 1 ∧
    D ≡ 1 [MOD q] ∧
    Nat.Coprime q D

/-- Every positive-length repunit sum satisfies the divisibility package. -/
theorem CellDivisibleOfRepunit (q k : ℕ) (hq : 1 ≤ q) (hk : 0 < k) :
    CellDivisible q k (RepunitSum q k) := by
  refine ⟨rfl, RepunitSumGeom q k hq, RepunitSumMulPred q k hq,
    RepunitSumDvd q k hq, RepunitSumModBase q k hk,
    RepunitSumCoprime q k hk⟩

/-- The five displayed cells obey the repunit divisibility identity. -/
theorem DisplayedRepunitDivisor :
    CellDivisible 2 2 3 ∧ CellDivisible 2 3 7 ∧ CellDivisible 2 4 15 ∧
      CellDivisible 3 2 4 ∧ CellDivisible 3 3 13 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have sumEq : RepunitSum 2 2 = 3 := by
      rw [RepunitSumTwo]
    exact sumEq ▸ CellDivisibleOfRepunit 2 2 (by decide) (by decide)
  · have sumEq : RepunitSum 2 3 = 7 := by
      rw [RepunitSumThree]
      decide
    exact sumEq ▸ CellDivisibleOfRepunit 2 3 (by decide) (by decide)
  · have sumEq : RepunitSum 2 4 = 15 := by
      rw [RepunitSumFour]
      decide
    exact sumEq ▸ CellDivisibleOfRepunit 2 4 (by decide) (by decide)
  · have sumEq : RepunitSum 3 2 = 4 := by
      rw [RepunitSumTwo]
    exact sumEq ▸ CellDivisibleOfRepunit 3 2 (by decide) (by decide)
  · have sumEq : RepunitSum 3 3 = 13 := by
      rw [RepunitSumThree]
      decide
    exact sumEq ▸ CellDivisibleOfRepunit 3 3 (by decide) (by decide)

/-- On each displayed cell the offset-one affine map returns every residue. -/
theorem DisplayedRepunitAffine (r : ℕ) :
    (fun x => 2 * x + 1)^[2] r ≡ r [MOD 3] ∧
      (fun x => 2 * x + 1)^[3] r ≡ r [MOD 7] ∧
      (fun x => 2 * x + 1)^[4] r ≡ r [MOD 15] ∧
      (fun x => 3 * x + 1)^[2] r ≡ r [MOD 4] ∧
      (fun x => 3 * x + 1)^[3] r ≡ r [MOD 13] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have sumEq : RepunitSum 2 2 = 3 := by
      rw [RepunitSumTwo]
    have h := RepunitAffineModId 2 1 2 r (by decide)
    rw [sumEq] at h
    exact h
  · have sumEq : RepunitSum 2 3 = 7 := by
      rw [RepunitSumThree]
      decide
    have h := RepunitAffineModId 2 1 3 r (by decide)
    rw [sumEq] at h
    exact h
  · have sumEq : RepunitSum 2 4 = 15 := by
      { rw [RepunitSumFour]; decide }
    have h := RepunitAffineModId 2 1 4 r (by decide)
    rw [sumEq] at h
    exact h
  · have sumEq : RepunitSum 3 2 = 4 := by
      rw [RepunitSumTwo]
    have h := RepunitAffineModId 3 1 2 r (by decide)
    rw [sumEq] at h
    exact h
  · have sumEq : RepunitSum 3 3 = 13 := by
      { rw [RepunitSumThree]; decide }
    have h := RepunitAffineModId 3 1 3 r (by decide)
    rw [sumEq] at h
    exact h

end GeneralizedCollatz.RepunitCell
