-- SPDX-License-Identifier: CC-BY-4.0
import AffineEscape
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Signed dyadic affine tails and two exact positive capture families.
The shift `(q - 1) * n + c` removes the affine offset without changing the raw clock.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.DyadicDynamics

/-- Signed dyadic parameters retain division precedence at zero. -/
def DyadicParameters (q c : ℤ) : Parameters where
  Q := q
  C := c
  D := 2
  DAdmissible := by norm_num

/-- The raw dyadic rule uses exact signed halving only on even states. -/
abbrev Step (q c : ℤ) := RawStep (DyadicParameters q c)

/-- An even multiplier and odd offset send every affine input to an odd state. -/
theorem OddAffineOutput (q c n : ℤ) (hq : 2 ∣ q) (hc : ¬2 ∣ c) :
    ¬2 ∣ q * n + c := by
  intro h
  have hqn : 2 ∣ q * n := dvd_mul_of_dvd_left hq n
  have hd := dvd_sub h hqn
  have he : q * n + c - q * n = c := by ring
  rw [he] at hd
  exact hc hd

/-- A dyadic multiple executes its initial halving prefix in the original clock. -/
theorem DivisionPrefix (q c u : ℤ) (k : ℕ) :
    Iterate (Step q c) k (2 ^ k * u) = u := by
  induction k with
  | zero => { simp [Iterate] }
  | succ k ih => {
      rw [IterateSuccFirst, pow_succ', mul_assoc]
      have hd : (2 : ℤ) ∣ 2 * (2 ^ k * u) := dvd_mul_right _ _
      simp only [Step, RawStep, DyadicParameters, if_pos hd]
      rw [Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
      exact ih
    }

/-- Opposite-parity coefficients preserve the odd affine branch. -/
theorem OddBranchInvariant (q c n : ℤ) (hqc : ¬2 ∣ q + c) (hn : ¬2 ∣ n) :
    ¬2 ∣ q * n + c := by
  have hnmod : n % 2 = 1 := by omega
  have hsum : (q + c) % 2 = 1 := by omega
  rw [Int.add_emod] at hsum
  intro hd
  have hmod : (q * n + c) % 2 = 0 := Int.emod_eq_zero_of_dvd hd
  rw [Int.add_emod, Int.mul_emod, hnmod, mul_one] at hmod
  omega

/-- The exact shift identity and the odd guard propagate jointly along an affine tail. -/
theorem TailCertificate (q c u : ℤ) (hqc : ¬2 ∣ q + c)
    (hu : ¬2 ∣ u) (j : ℕ) :
    ¬2 ∣ Iterate (Step q c) j u ∧
      (q - 1) * Iterate (Step q c) j u + c = q ^ j * ((q - 1) * u + c) := by
  induction j with
  | zero => { simp [Iterate, hu] }
  | succ j ih => {
      have hs : Step q c (Iterate (Step q c) j u) =
          q * Iterate (Step q c) j u + c := by
        change (if (2 : ℤ) ∣ Iterate (Step q c) j u then
          Iterate (Step q c) j u / 2 else q * Iterate (Step q c) j u + c) = _
        rw [if_neg ih.1]
      constructor
      · rw [Iterate, hs]
        exact OddBranchInvariant q c _ hqc ih.1
      · rw [Iterate, hs, pow_succ]
        calc
          (q - 1) * (q * Iterate (Step q c) j u + c) + c =
              q * ((q - 1) * Iterate (Step q c) j u + c) := by ring
          _ = q * (q ^ j * ((q - 1) * u + c)) := by rw [ih.2]
          _ = q ^ j * q * ((q - 1) * u + c) := by ring
    }

/-- Exponential growth dominates elapsed time with an integer-only bound. -/
theorem PowerDominatesTime (Q j : ℕ) (hQ : 2 ≤ Q) : j + 1 ≤ Q ^ j := by
  induction j with
  | zero => { simp }
  | succ j ih => {
      rw [pow_succ]
      nlinarith [Nat.mul_le_mul_left (Q ^ j) hQ]
    }

/-- A nonzero shift certificate forces full-sequence magnitude escape, not just unboundedness. -/
theorem TailEscape (q c u : ℤ) (hqc : ¬2 ∣ q + c) (hu : ¬2 ∣ u)
    (hQ : 2 ≤ q.natAbs) (hn : (q - 1) * u + c ≠ 0) :
    ∀ B : ℕ, ∃ J : ℕ, ∀ j ≥ J, B < (Iterate (Step q c) j u).natAbs := by
  intro B
  refine ⟨(q - 1).natAbs * (B + 1) + c.natAbs, ?_⟩
  intro j hj
  have hp := PowerDominatesTime q.natAbs j hQ
  have hcert := congrArg Int.natAbs (TailCertificate q c u hqc hu j).2
  simp only [Int.natAbs_mul, Int.natAbs_pow] at hcert
  have hb : 1 ≤ ((q - 1) * u + c).natAbs := by
    have hnabs : ((q - 1) * u + c).natAbs ≠ 0 := by simpa using hn
    omega
  have htriangle := Int.natAbs_add_le
    ((q - 1) * Iterate (Step q c) j u) c
  simp only [Int.natAbs_mul] at htriangle
  have hl : q.natAbs ^ j ≤
      (q - 1).natAbs * (Iterate (Step q c) j u).natAbs + c.natAbs := by
    nlinarith
  by_contra h
  have hupper : (Iterate (Step q c) j u).natAbs ≤ B := by omega
  have hm : (q - 1).natAbs * (Iterate (Step q c) j u).natAbs ≤
      (q - 1).natAbs * (B + 1) :=
    Nat.mul_le_mul_left _ (le_trans hupper (Nat.le_succ B))
  have hlarge := le_trans hp (le_trans hl (Nat.add_le_add_right hm c.natAbs))
  exact Nat.not_succ_le_self j (le_trans hlarge hj)

/-- A zero shift certificate is exactly a fixed affine anchor when the multiplier is nonunit. -/
theorem TailFixed (q c u : ℤ) (hqc : ¬2 ∣ q + c) (hu : ¬2 ∣ u)
    (hq1 : q ≠ 1) (hz : (q - 1) * u + c = 0) (j : ℕ) :
    Iterate (Step q c) j u = u := by
  have h := (TailCertificate q c u hqc hu j).2
  rw [hz, mul_zero] at h
  have hfactor : (q - 1) * (Iterate (Step q c) j u - u) = 0 := by
    nlinarith
  have hn : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  have hd : Iterate (Step q c) j u - u = 0 := (mul_eq_zero.mp hfactor).resolve_left hn
  omega

/-- A repeated odd anchor with an expanding multiplier has zero shift certificate. -/
theorem TailPeriodicOnlyFixed (q c u : ℤ) (hqc : ¬2 ∣ q + c)
    (hu : ¬2 ∣ u) (hQ : 2 ≤ q.natAbs) (h : ℕ) (hh : 0 < h)
    (hp : Iterate (Step q c) h u = u) : (q - 1) * u + c = 0 := by
  have hcq := (TailCertificate q c u hqc hu h).2
  rw [hp] at hcq
  have hfactor : (q ^ h - 1) * ((q - 1) * u + c) = 0 := by nlinarith
  have hpow : q ^ h ≠ 1 := by
    intro he
    have heabs := congrArg Int.natAbs he
    simp only [Int.natAbs_pow, Int.natAbs_one] at heabs
    have hl := PowerDominatesTime q.natAbs h hQ
    omega
  exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hpow)

/-- Every nonzero signed seed has an odd anchor after finitely many exact halvings. -/
theorem DyadicDecomposition (n : ℤ) (hn : n ≠ 0) :
    ∃ k : ℕ, ∃ u : ℤ, ¬2 ∣ u ∧ n = 2 ^ k * u := by
  have habs : n.natAbs ≠ 0 := by simpa using hn
  obtain ⟨k, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd habs 2 (by decide)
  have hmInt : ¬(2 : ℤ) ∣ (m : ℤ) := by exact_mod_cast hm
  have heInt : |n| = (2 : ℤ) ^ k * (m : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast he
  by_cases hp : 0 ≤ n
  · exact ⟨k, m, hmInt, by simpa [abs_of_nonneg hp] using heInt⟩
  · refine ⟨k, -(m : ℤ), ?_, ?_⟩
    · simpa only [dvd_neg] using hmInt
    · have ha : -n = (2 : ℤ) ^ k * (m : ℤ) := by
        simpa [abs_of_nonpos (by omega : n ≤ 0)] using heInt
      rw [mul_neg]
      omega

/-- Opposite-parity coefficients with an expanding multiplier give a complete signed dichotomy. -/
theorem SeedOutcome (q c n : ℤ) (hqc : ¬2 ∣ q + c) (hQ : 2 ≤ q.natAbs)
    (hn : n ≠ 0) :
    (∃ s : ℕ, ∃ u : ℤ, ¬2 ∣ u ∧ (q - 1) * u + c = 0 ∧
      ∀ j, Iterate (Step q c) (s + j) n = u) ∨
    (∀ B : ℕ, ∃ J : ℕ, ∀ j ≥ J, B < (Iterate (Step q c) j n).natAbs) := by
  obtain ⟨k, u, hu, he⟩ := DyadicDecomposition n hn
  have hr : Iterate (Step q c) k n = u := by
    rw [he]
    exact DivisionPrefix q c u k
  by_cases hz : (q - 1) * u + c = 0
  · refine Or.inl ⟨k, u, hu, hz, ?_⟩
    intro j
    rw [IterateAdd, hr]
    have hq1 : q ≠ 1 := by intro h; subst q; norm_num at hQ
    exact TailFixed q c u hqc hu hq1 hz j
  · right
    intro B
    obtain ⟨J, hJ⟩ := TailEscape q c u hqc hu hQ hz B
    refine ⟨k + J, ?_⟩
    intro j hj
    have hjk : k ≤ j := by omega
    have heq : j = k + (j - k) := by omega
    rw [heq, IterateAdd, hr]
    exact hJ (j - k) (by omega)

/-- Every positive seed reaches one for the unit multiplier and unit offset. -/
theorem UnitCapture (n : ℕ) (hn : 0 < n) :
    ∃ k, Iterate (PositiveRawStep 1 1 2) k n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih => {
      by_cases h1 : n = 1
      · exact ⟨0, by simpa [Iterate] using h1⟩
      by_cases he : 2 ∣ n
      · have hl : n / 2 < n := Nat.div_lt_self hn (by norm_num)
        have hp : 0 < n / 2 := by
          have hm := Nat.le_of_dvd hn he
          omega
        obtain ⟨k, hk⟩ := ih (n / 2) hl hp
        refine ⟨k + 1, ?_⟩
        rw [IterateSuccFirst]
        simpa [PositiveRawStep, he] using hk
      · have hadd : 2 ∣ n + 1 := by omega
        have hl : (n + 1) / 2 < n := by omega
        have hp : 0 < (n + 1) / 2 := by omega
        obtain ⟨k, hk⟩ := ih ((n + 1) / 2) hl hp
        refine ⟨(k + 1) + 1, ?_⟩
        rw [IterateSuccFirst]
        simp only [PositiveRawStep, if_neg he, one_mul]
        rw [IterateSuccFirst]
        simpa [PositiveRawStep, hadd] using hk
    }

/-- The seed one makes the declared power-of-two excursion in one affine instruction. -/
theorem MersenneFirst (k : ℕ) :
    PositiveRawStep (2 ^ k - 1) 1 2 1 = 2 ^ k := by
  have hp : 0 < (2 : ℕ) ^ k := pow_pos (by norm_num) k
  norm_num [PositiveRawStep]
  omega

/-- Every phase of the power-of-two excursion has its exact raw time. -/
theorem MersennePhase (k j : ℕ) (hj : j ≤ k) :
    Iterate (PositiveRawStep (2 ^ k - 1) 1 2) (j + 1) 1 = 2 ^ (k - j) := by
  rw [IterateSuccFirst, MersenneFirst]
  have he : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  rw [he]
  exact PositiveDivisionPrefix _ _ _ _ _ (by norm_num)

/-- The Mersenne excursion closes after its one affine tick and exactly k halvings. -/
theorem MersenneClosure (k : ℕ) :
    Iterate (PositiveRawStep (2 ^ k - 1) 1 2) (k + 1) 1 = 1 := by
  simpa using MersennePhase k k (le_refl k)

/-- No earlier positive raw time closes the Mersenne excursion. -/
theorem MersennePrimitive (k h : ℕ) (hh : 0 < h) (hlt : h < k + 1) :
    Iterate (PositiveRawStep (2 ^ k - 1) 1 2) h 1 ≠ 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  rw [MersennePhase k j (by omega)]
  have he : 0 < k - j := by omega
  have hp : 1 < (2 : ℕ) ^ (k - j) := Nat.one_lt_pow (by omega) (by norm_num)
  omega

end GeneralizedCollatz.DyadicDynamics
