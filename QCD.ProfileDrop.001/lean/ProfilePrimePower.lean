/-
SPDX-License-Identifier: CC-BY-4.0

Signed geometric sums and prime-power lifting for affine residue dynamics.
-/
import ProfileDrop
import SignedTraps
import Mathlib.NumberTheory.Multiplicity

namespace GeneralizedCollatz

/-- The polynomial representation interfaces with the geometric-sum lifting theorem. -/
theorem TrapSumEqSum (q : ℤ) (n : ℕ) :
    TrapSum q n = ∑ i ∈ Finset.range n, q ^ i := by
  induction n with
  | zero => { simp [TrapSum] }
  | succ n ih => { rw [TrapSum, Finset.sum_range_succ, ih] }

/-- Splitting a geometric sum preserves the multiplier of its second block. -/
theorem TrapSumAdd (q : ℤ) (m n : ℕ) :
    TrapSum q (m + n) = TrapSum q m + q ^ m * TrapSum q n := by
  induction n with
  | zero => { simp [TrapSum] }
  | succ n ih => {
      rw [Nat.add_succ, TrapSum, ih, TrapSum, pow_add]
      ring
    }

/-- Factoring an index into equal blocks gives the multiplicative lifting identity. -/
theorem TrapSumMul (q : ℤ) (m n : ℕ) :
    TrapSum q (m * n) = TrapSum q m * TrapSum (q ^ m) n := by
  induction n with
  | zero => { simp [TrapSum] }
  | succ n ih => {
      rw [Nat.mul_succ, TrapSumAdd, ih, TrapSum, ← pow_mul]
      ring
    }

/-- The affine polynomial identity needs neither division avoidance nor `q ≠ 1`. -/
theorem AffineIterPolynomial (q c x : ℤ) (n : ℕ) :
    AffineIter q c x n = q ^ n * x + c * TrapSum q n := by
  induction n with
  | zero => { simp [AffineIter, TrapSum] }
  | succ n ih => {
      -- Replace the last-term recurrence by its equivalent first-term recurrence.
      have hpow : q ^ n = (q - 1) * TrapSum q n + 1 := by
        have h := TrapSumMulSubOne q n
        omega
      have hrec : TrapSum q (n + 1) = q * TrapSum q n + 1 := by
        rw [TrapSum, hpow]
        ring
      rw [AffineIter, ih, hrec, pow_succ]
      simp only [AffineBranch]
      ring
    }

/-- The same displacement controls every return without dividing by `q - 1`. -/
theorem AffineIterDisplacement (q c x : ℤ) (n : ℕ) :
    AffineIter q c x n - x = TrapSum q n * Displacement q c x := by
  rw [AffineIterPolynomial]
  calc
    q ^ n * x + c * TrapSum q n - x = (q ^ n - 1) * x + c * TrapSum q n := by ring
    _ = ((q - 1) * TrapSum q n) * x + c * TrapSum q n := by
      rw [TrapSumMulSubOne]
    _ = TrapSum q n * Displacement q c x := by
      simp only [Displacement]
      ring

/-- A multiplier congruent to one cannot be divisible by the same prime. -/
theorem PrimeUnitOfSuccessorDivisibility (q : ℤ) (p : ℕ) (hp : p.Prime)
    (hdiv : (p : ℤ) ∣ q - 1) : ¬ (p : ℤ) ∣ q := by
  intro hq
  have hone : (p : ℤ) ∣ 1 := by
    have h := Int.dvd_sub hq hdiv
    simpa only [sub_sub_cancel] using h
  have hn : p ∣ 1 := by exact_mod_cast hone
  exact hp.ne_one (Nat.dvd_one.mp hn)

/-- One odd-prime geometric block has exactly one factor of the prime, even at `q = 1`. -/
theorem TrapSumOddPrimeLift (q : ℤ) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hdiv : (p : ℤ) ∣ q - 1) :
    emultiplicity (p : ℤ) (TrapSum q p) = 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnot := PrimeUnitOfSuccessorDivisibility q p hp hdiv
  rw [TrapSumEqSum]
  simpa only [one_pow, mul_one] using
    emultiplicity_geom_sum₂_eq_one (x := q) (y := (1 : ℤ)) hpZ hodd hdiv hnot

/-- The binary geometric block has exactly one factor of two when `q ≡ 1` modulo four. -/
theorem TrapSumTwoLift (q : ℤ) (hdiv : (4 : ℤ) ∣ q - 1) :
    emultiplicity (2 : ℤ) (TrapSum q 2) = 1 := by
  have hsum : TrapSum q 2 = q + 1 := by simp [TrapSum, add_comm]
  rw [hsum]
  apply emultiplicity_eq_coe.2
  obtain ⟨t, ht⟩ := hdiv
  constructor
  · {
      rw [pow_one]
      refine ⟨2 * t + 1, ?_⟩
      omega
    }
  · {
      intro hfour
      obtain ⟨u, hu⟩ := hfour
      norm_num at hu
      omega
    }

/-- Every odd-prime index lifting increases the geometric-sum multiplicity by exactly one. -/
theorem TrapSumOddPrimePower (q : ℤ) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hdiv : (p : ℤ) ∣ q - 1) (a : ℕ) :
    emultiplicity (p : ℤ) (TrapSum q (p ^ a)) = (a : ℕ∞) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  induction a with
  | zero => { simp [TrapSum, emultiplicity_of_one_right hpZ.not_unit] }
  | succ a ih => {
      have hpow : (p : ℤ) ∣ q ^ (p ^ a) - 1 := by
        rw [← TrapSumMulSubOne]
        exact dvd_mul_of_dvd_left hdiv _
      rw [Nat.pow_succ, TrapSumMul, emultiplicity_mul hpZ, ih,
        TrapSumOddPrimeLift (q ^ (p ^ a)) p hp hodd hpow]
      simp only [Nat.cast_add, Nat.cast_one]
    }

/-- Binary lifting preserves the modulo-four hypothesis and gives exact finite multiplicity. -/
theorem TrapSumTwoPower (q : ℤ) (hdiv : (4 : ℤ) ∣ q - 1) (a : ℕ) :
    emultiplicity (2 : ℤ) (TrapSum q (2 ^ a)) = (a : ℕ∞) := by
  have hpZ : Prime (2 : ℤ) := Nat.prime_iff_prime_int.mp Nat.prime_two
  induction a with
  | zero => { simp [TrapSum, emultiplicity_of_one_right hpZ.not_unit] }
  | succ a ih => {
      have hpow : (4 : ℤ) ∣ q ^ (2 ^ a) - 1 := by
        rw [← TrapSumMulSubOne]
        exact dvd_mul_of_dvd_left hdiv _
      rw [Nat.pow_succ, TrapSumMul, emultiplicity_mul hpZ, ih,
        TrapSumTwoLift (q ^ (2 ^ a)) hpow]
      simp only [Nat.cast_add, Nat.cast_one]
    }

/-- Signed odd-prime LTE gives all index multiplicities after a separate `q = 1` branch. -/
theorem TrapSumOddPrimeMultiplicity (q : ℤ) (p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hdiv : (p : ℤ) ∣ q - 1) (n : ℕ) :
    emultiplicity (p : ℤ) (TrapSum q n) = emultiplicity p n := by
  by_cases hq : q = 1
  · { rw [hq, TrapSumOne, Int.natCast_emultiplicity] }
  · {
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hnot := PrimeUnitOfSuccessorDivisibility q p hp hdiv
      have hf : FiniteMultiplicity (p : ℤ) (q - 1) :=
        Int.finiteMultiplicity_iff.2 ⟨by simpa using hp.ne_one, sub_ne_zero.mpr hq⟩
      have hfinite := finiteMultiplicity_iff_emultiplicity_ne_top.1 hf
      have h := Int.emultiplicity_pow_sub_pow hp hodd hdiv hnot n
      simp only [one_pow] at h
      rw [← TrapSumMulSubOne, emultiplicity_mul hpZ] at h
      exact ENat.add_right_injective_of_ne_top hfinite h
    }

/-- Binary LTE is cancelled only when the signed initial difference has finite multiplicity. -/
theorem TrapSumTwoMultiplicity (q : ℤ) (hdiv : (4 : ℤ) ∣ q - 1) (n : ℕ) :
    emultiplicity (2 : ℤ) (TrapSum q n) = emultiplicity (2 : ℕ) n := by
  by_cases hq : q = 1
  · {
      rw [hq, TrapSumOne]
      exact Int.natCast_emultiplicity 2 n
    }
  · {
      have htwo : (2 : ℤ) ∣ q - 1 := (show (2 : ℤ) ∣ 4 by decide).trans hdiv
      have hnot := PrimeUnitOfSuccessorDivisibility q 2 Nat.prime_two htwo
      have hf : FiniteMultiplicity (2 : ℤ) (q - 1) :=
        Int.finiteMultiplicity_iff.2 ⟨by decide, sub_ne_zero.mpr hq⟩
      have hfinite := finiteMultiplicity_iff_emultiplicity_ne_top.1 hf
      have h := Int.two_pow_sub_pow' n hdiv hnot
      simp only [one_pow] at h
      rw [← TrapSumMulSubOne, emultiplicity_mul Int.prime_two] at h
      -- Apply the explicit cast identity after cancelling the finite ENat term.
      have hcancel := ENat.add_right_injective_of_ne_top hfinite h
      exact hcancel.trans (Int.natCast_emultiplicity 2 n)
    }

/-- A unit displacement transfers exact geometric-sum divisibility to every signed start. -/
theorem PrimePowerReturnDivisibility (q c : ℤ) (p a : ℕ) (hp : p.Prime)
    (hdiv : (p : ℤ) ∣ q - 1) (hc : ¬ (p : ℤ) ∣ c)
    (hgeom : ∀ n : ℕ,
      emultiplicity (p : ℤ) (TrapSum q n) = emultiplicity p n) (x : ℤ) (n : ℕ) :
    ((p ^ a : ℕ) : ℤ) ∣ AffineIter q c x n - x ↔ p ^ a ∣ n := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdis : ¬ (p : ℤ) ∣ Displacement q c x := by
    intro hx
    have hprod : (p : ℤ) ∣ (q - 1) * x := dvd_mul_of_dvd_left hdiv _
    apply hc
    simpa only [Displacement, add_sub_cancel_left] using Int.dvd_sub hx hprod
  rw [AffineIterDisplacement, Nat.cast_pow, pow_dvd_iff_le_emultiplicity,
    emultiplicity_mul hpZ, emultiplicity_eq_zero.2 hdis, add_zero, hgeom,
    pow_dvd_iff_le_emultiplicity]

/-- Affine iteration composes on the same chronological clock. -/
theorem AffineIterAdd (q c x : ℤ) (i j : ℕ) :
    AffineIter q c x (i + j) = AffineIter q c (AffineIter q c x i) j := by
  induction j with
  | zero => { simp [AffineIter] }
  | succ j ih => { rw [Nat.add_succ, AffineIter, ih, AffineIter] }

/-- Equal Euclidean residues imply divisibility of the signed difference. -/
theorem ResidueEqualityDivides (m : ℕ) (hm : 0 < m) (x y : ℤ)
    (h : Residue m x = Residue m y) : (m : ℤ) ∣ x - y := by
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hx : (Residue m x : ℤ) = x % (m : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg x (ne_of_gt hmZ))
  have hy : (Residue m y : ℤ) = y % (m : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg y (ne_of_gt hmZ))
  have hmod : x % (m : ℤ) = y % (m : ℤ) := by
    rw [← hx, ← hy, h]
  exact Int.dvd_iff_emod_eq_zero.2 (Int.emod_eq_emod_iff_emod_sub_eq_zero.1 hmod)

/-- Exact return divisibility makes the first `m` iterates exhaust all `m` residues. -/
theorem AffineZeroAccessOfExactReturns (q c : ℤ) (m : ℕ) (hm : 0 < m)
    (hreturn : ∀ x : ℤ, ∀ n : ℕ,
      (m : ℤ) ∣ AffineIter q c x n - x ↔ m ∣ n) (x : ℤ) :
    ∃ j : ℕ, j < m ∧ (m : ℤ) ∣ AffineIter q c x j := by
  let f : Fin m → Fin m := fun i =>
    ⟨Residue m (AffineIter q c x i.val), ResidueLt m hm _⟩
  have hordered : ∀ i j : Fin m, i.val ≤ j.val → f i = f j → i = j := by
    intro i j hij heq
    have hres : Residue m (AffineIter q c x j.val) =
        Residue m (AffineIter q c x i.val) := congrArg Fin.val heq.symm
    have hd := ResidueEqualityDivides m hm _ _ hres
    have hj : j.val = i.val + (j.val - i.val) := by omega
    rw [hj, AffineIterAdd] at hd
    have hindex : m ∣ j.val - i.val := (hreturn _ _).1 hd
    have hlt : j.val - i.val < m := by omega
    have hzero := Nat.eq_zero_of_dvd_of_lt hindex hlt
    apply Fin.ext
    omega
  have hinj : Function.Injective f := by
    intro i j heq
    by_cases hij : i.val ≤ j.val
    · { exact hordered i j hij heq }
    · { exact (hordered j i (by omega) heq.symm).symm }
  obtain ⟨j, hj⟩ := Finite.surjective_of_injective hinj ⟨0, hm⟩
  have hz : Residue m (AffineIter q c x j.val) = 0 := congrArg Fin.val hj
  exact ⟨j.val, j.isLt, (ResidueZeroIff m hm _).1 hz⟩

/-- The odd-prime conditions provide a zero visit before the complete prime-power period. -/
theorem OddPrimePowerZeroAccess (q c : ℤ) (p a : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hdiv : (p : ℤ) ∣ q - 1) (hc : ¬ (p : ℤ) ∣ c) (x : ℤ) :
    ∃ j : ℕ, j < p ^ a ∧ ((p ^ a : ℕ) : ℤ) ∣ AffineIter q c x j := by
  apply AffineZeroAccessOfExactReturns q c (p ^ a) (pow_pos hp.pos a)
  intro y n
  exact PrimePowerReturnDivisibility q c p a hp hdiv hc
    (TrapSumOddPrimeMultiplicity q p hp hodd hdiv) y n

/-- The modulo-four binary condition gives a zero visit on the full power-of-two clock. -/
theorem TwoPowerZeroAccess (q c : ℤ) (a : ℕ) (hdiv : (4 : ℤ) ∣ q - 1)
    (hc : ¬ (2 : ℤ) ∣ c) (x : ℤ) :
    ∃ j : ℕ, j < 2 ^ a ∧ ((2 ^ a : ℕ) : ℤ) ∣ AffineIter q c x j := by
  have htwo : (2 : ℤ) ∣ q - 1 := (show (2 : ℤ) ∣ 4 by decide).trans hdiv
  apply AffineZeroAccessOfExactReturns q c (2 ^ a) (by positivity)
  intro y n
  exact PrimePowerReturnDivisibility q c 2 a Nat.prime_two htwo hc
    (TrapSumTwoMultiplicity q hdiv) y n

end GeneralizedCollatz
