-- SPDX-License-Identifier: CC-BY-4.0
import CommonBaseHighOffsetClock
import CompressionOutcomes

/-!
Finite initial-division recovery and same-seed raw rays for nonzero signed states.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- A base at least two supplies an elementary effective bound on its whole-base order. -/
theorem WholeBasePowerRank (t k : ℕ) (tLower : 2 ≤ t) : k + 1 ≤ t ^ k := by
  induction k with
  | zero => { simp }
  | succ k ih => {
    calc
      (k + 1) + 1 ≤ (k + 1) * 2 := by omega
      _ ≤ t ^ k * 2 := Nat.mul_le_mul_right 2 ih
      _ ≤ t ^ k * t := Nat.mul_le_mul_left (t ^ k) tLower
      _ = t ^ (k + 1) := (pow_succ t k).symm
  }

/-- The signed residual cannot hide an unbounded initial division count. -/
theorem WholeBaseOrderAtRank (t k : ℕ) (n : ℤ) (tLower : 2 ≤ t)
    (atOrder : WholeBaseOrderAt t n k) : k ≤ n.natAbs := by
  rcases atOrder with ⟨w, state, guard⟩
  have residualNonzero : w ≠ 0 := by
    intro zero
    apply guard
    simp [zero]
  have residualPositive : 0 < w.natAbs := Int.natAbs_pos.mpr residualNonzero
  have magnitude : n.natAbs = t ^ k * w.natAbs := by
    rw [state, Int.natAbs_mul, Int.natAbs_pow]
    simp
  have power := WholeBasePowerRank t k tLower
  have growth : t ^ k ≤ t ^ k * w.natAbs := Nat.le_mul_of_pos_right _ residualPositive
  omega

/-- Legal initial divisions find a below-divisor phase with explicit finite bounds. -/
theorem WholeBaseNormalizeRaw (p : Parameters) (t v : ℕ) (n : ℤ)
    (tLower : 2 ≤ t) (vPositive : 0 < v) (divisor : p.D = (t : ℤ) ^ v)
    (nNonzero : n ≠ 0) :
    ∃ r k : ℕ, ∃ x : ℤ, r ≤ n.natAbs ∧ k < v ∧
      Iterate (RawStep p) r n = x ∧ WholeBaseOrderAt t x k ∧ x.natAbs ≤ n.natAbs := by
  obtain ⟨m, atOrder⟩ := WholeBaseOrderAtExists t n tLower nNonzero
  have rank := WholeBaseOrderAtRank t m n tLower atOrder
  rcases atOrder with ⟨w, state, guard⟩
  have power : (t : ℤ) ^ m = p.D ^ (m / v) * (t : ℤ) ^ (m % v) := by
    rw [divisor, ← pow_mul, ← pow_add, Nat.div_add_mod]
  have input : n = p.D ^ (m / v) * ((t : ℤ) ^ (m % v) * w) := by
    rw [state, power]
    ring
  have travel := PowerDivisionPrefix p (m / v) (m / v)
    ((t : ℤ) ^ (m % v) * w) (Nat.le_refl _)
  rw [← input, Nat.sub_self, pow_zero, one_mul] at travel
  have baseNonzero : (t : ℤ) ≠ 0 := by omega
  have divisorNonzero : p.D ≠ 0 := by
    rw [divisor]
    exact pow_ne_zero _ baseNonzero
  have powerPositive : 0 < (p.D ^ (m / v)).natAbs :=
    Int.natAbs_pos.mpr (pow_ne_zero _ divisorNonzero)
  have magnitude : n.natAbs =
      (p.D ^ (m / v)).natAbs * ((t : ℤ) ^ (m % v) * w).natAbs := by
    conv_lhs => rw [input, Int.natAbs_mul]
  have contraction : ((t : ℤ) ^ (m % v) * w).natAbs ≤ n.natAbs := by
    rw [magnitude]
    exact Nat.le_mul_of_pos_left _ powerPositive
  refine ⟨m / v, m % v, (t : ℤ) ^ (m % v) * w, ?_, Nat.mod_lt _ vPositive,
    travel, ⟨w, rfl, guard⟩, contraction⟩
  exact (Nat.div_le_self m v).trans rank

/-- Every nonzero signed seed reaches the same admissible raw arithmetic progression. -/
theorem WholeBaseHighOffsetNormalizeRawRay (p : Parameters) (t u v a : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uBelow : u < v) (highOffset : u + v ≤ a)
    (coprime : Nat.Coprime u v) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (nNonzero : n ≠ 0) :
    ∃ r k : ℕ, ∃ x : ℤ, r ≤ n.natAbs ∧ k < v ∧
      Iterate (RawStep p) r n = x ∧ WholeBaseOrderAt t x k ∧ x.natAbs ≤ n.natAbs ∧
      ∀ j : ℕ, Iterate (RawStep p) (r + j * (u + v)) n =
        x + (j : ℤ) *
          (s * (t : ℤ) ^ (a - u - v + 1 + k) * WholeBaseGeometricSum t v) := by
  obtain ⟨r, k, x, rBound, kBelow, reached, atOrder, magnitude⟩ :=
    WholeBaseNormalizeRaw p t v n tLower (by omega) divisor nNonzero
  have ray := WholeBaseHighOffsetRawRay p t u v a k s x tLower uBelow kBelow
    highOffset coprime divisor multiplier offset atOrder
  refine ⟨r, k, x, rBound, kBelow, reached, atOrder, magnitude, ?_⟩
  intro j
  rw [IterateAdd, reached]
  exact (ray j).2

end GeneralizedCollatz
