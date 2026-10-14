-- SPDX-License-Identifier: CC-BY-4.0
import ProfileDrop
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Two equal fixed-precision residues can have unequal residues after a raw division. -/
theorem RawPrecisionWitness (q c : ℤ) (d k : ℕ) (hd : 2 ≤ d) :
    let modulus : ℤ := (d : ℤ) ^ (k + 1)
    0 % modulus = modulus % modulus ∧
      RawBranch q c d 0 % modulus ≠ RawBranch q c d modulus % modulus := by
  dsimp
  have hD : 0 < (d : ℤ) := by omega
  have hpow : 0 < (d : ℤ) ^ k := pow_pos hD k
  have hlt : (d : ℤ) ^ k < (d : ℤ) ^ (k + 1) := by
    rw [pow_succ]
    have hdZ : 2 ≤ (d : ℤ) := by exact_mod_cast hd
    exact lt_mul_of_one_lt_right hpow (by omega)
  have hdiv : (d : ℤ) ∣ (d : ℤ) ^ (k + 1) := by
    exact ⟨(d : ℤ) ^ k, by rw [pow_succ]; ring⟩
  have hzero : RawBranch q c d 0 = 0 := by simp [RawBranch]
  have hnext : RawBranch q c d ((d : ℤ) ^ (k + 1)) = (d : ℤ) ^ k := by
    rw [RawBranch, if_pos hdiv, pow_succ]
    exact Int.mul_ediv_cancel _ (ne_of_gt hD)
  constructor
  · simp
  · rw [hzero, hnext, Int.zero_emod, Int.emod_eq_of_lt hpow.le hlt]
    exact ne_of_gt hpow |>.symm

/-- No deterministic map on one fixed d-adic residue precision recovers all raw successors. -/
theorem NoFixedRawPrecision (q c : ℤ) (d k : ℕ) (hd : 2 ≤ d) :
    ¬ ∃ f : ℤ → ℤ, ∀ n : ℤ,
      RawBranch q c d n % (d : ℤ) ^ (k + 1) =
        f (n % (d : ℤ) ^ (k + 1)) := by
  rintro ⟨f, hf⟩
  obtain ⟨heq, hne⟩ := RawPrecisionWitness q c d k hd
  apply hne
  rw [hf, hf, heq]

/-- Integral division consumes one d-adic digit and preserves every lower-precision residue. -/
theorem DivisionPrecisionTransfer (d k : ℕ) (hd : 2 ≤ d) (u v : ℤ)
    (hu : (d : ℤ) ∣ u) (hv : (d : ℤ) ∣ v)
    (heq : Int.ModEq ((d : ℤ) ^ (k + 1)) u v) :
    Int.ModEq ((d : ℤ) ^ k) (u / d) (v / d) := by
  have hD : (d : ℤ) ≠ 0 := by omega
  apply Int.ModEq.mul_left_cancel' hD
  simpa only [Int.mul_ediv_cancel' hu, Int.mul_ediv_cancel' hv,
    pow_succ, mul_comm] using heq

end GeneralizedCollatz
