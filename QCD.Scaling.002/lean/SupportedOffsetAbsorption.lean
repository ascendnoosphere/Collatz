/- SPDX-License-Identifier: CC-BY-4.0 -/
import GeneralizedScaling
import CompressionPeriods
import AdditiveCycles
import Mathlib.Data.Nat.Prime.Defs

/-!
Entry into a supplied offset factor, with exact raw-clock recovery on its invariant lattice.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Dividing a supplied offset factor changes neither multiplier nor signed divisor. -/
def RelativeOffsetParameters (p : Parameters) (factor : ℤ) : Parameters where
  Q := p.Q
  C := p.C / factor
  D := p.D
  DAdmissible := p.DAdmissible

/-- Exact offset divisibility reconstructs the original parameters after scaling. -/
theorem RelativeOffsetScale (p : Parameters) (factor : ℤ)
    (offsetDivides : factor ∣ p.C) :
    ScaleParameters (RelativeOffsetParameters p factor) factor = p := by
  have reconstructed : factor * (p.C / factor) = p.C := by
    simpa [mul_comm] using Int.ediv_mul_cancel offsetDivides
  cases p
  simp_all [ScaleParameters, RelativeOffsetParameters]

/-- A supplied factor uses the same lexicographic entry rank as the full offset. -/
theorem RelativeOffsetCaptureBudget (p : Parameters) (factor : ℤ)
    (coprime : Int.gcd factor p.D = 1) (offsetDivides : factor ∣ p.C)
    (r : ℕ) (n : ℤ) (prepared : factor ∣ p.Q ^ r * n) :
    ∃ t : ℕ, factor ∣ Iterate (RawStep p) t n ∧ AffineCount p t n ≤ r := by
  by_cases captured : factor ∣ n
  · exact ⟨0, captured, Nat.zero_le r⟩
  · cases r with
    | zero => {
        have impossible : factor ∣ n := by simpa using prepared
        exact False.elim (captured impossible)
      }
    | succ r => {
        by_cases divisible : p.D ∣ n
        · have nonzero : n ≠ 0 := by
            intro zero
            apply captured
            simp [zero]
          have decrease := DivisionMagnitudeDescent p n divisible nonzero
          have multiplied : factor ∣ (p.Q ^ (r + 1) * (n / p.D)) * p.D := by
            rw [mul_assoc, Int.ediv_mul_cancel divisible]
            exact prepared
          have nextPrepared : factor ∣ p.Q ^ (r + 1) * RawStep p n := by
            have cancelled := Int.dvd_of_dvd_mul_left_of_gcd_one multiplied coprime
            simpa [RawStep, divisible] using cancelled
          obtain ⟨t, entered, budget⟩ := RelativeOffsetCaptureBudget p factor coprime
            offsetDivides (r + 1) (RawStep p n) nextPrepared
          refine ⟨t + 1, ?_, ?_⟩
          · rw [← IterateFirst]
            exact entered
          · simpa [AffineCount, divisible] using budget
        · have extra : factor ∣ p.Q ^ r * p.C :=
            dvd_mul_of_dvd_right offsetDivides (p.Q ^ r)
          have nextPrepared : factor ∣ p.Q ^ r * RawStep p n := by
            simpa [RawStep, divisible, pow_succ, mul_add, mul_assoc] using
              Int.dvd_add prepared extra
          obtain ⟨t, entered, budget⟩ := RelativeOffsetCaptureBudget p factor coprime
            offsetDivides r (RawStep p n) nextPrepared
          refine ⟨t + 1, ?_, ?_⟩
          · rw [← IterateFirst]
            exact entered
          · simpa [AffineCount, divisible] using Nat.succ_le_succ budget
      }
termination_by (r, n.natAbs)
decreasing_by
  all_goals omega

/-- Entry gives one normalized state whose entire future has the original raw clock. -/
theorem RelativeOffsetTail (p : Parameters) (factor : ℤ)
    (coprime : Int.gcd factor p.D = 1) (offsetDivides : factor ∣ p.C)
    (k : ℕ) (power : factor ∣ p.Q ^ k) (n : ℤ) :
    ∃ t : ℕ, ∃ m : ℤ,
      Iterate (RawStep p) t n = factor * m ∧ AffineCount p t n ≤ k ∧
      ∀ s : ℕ, Iterate (RawStep p) (t + s) n =
        factor * Iterate (RawStep (RelativeOffsetParameters p factor)) s m := by
  obtain ⟨t, entered, budget⟩ := RelativeOffsetCaptureBudget p factor coprime
    offsetDivides k n (dvd_mul_of_dvd_left power n)
  obtain ⟨m, endpoint⟩ := entered
  refine ⟨t, m, endpoint, budget, ?_⟩
  intro s
  rw [IterateAdd, endpoint]
  have scaled := ScalingIterates (RelativeOffsetParameters p factor) factor m coprime s
  rw [RelativeOffsetScale p factor offsetDivides] at scaled
  exact scaled

/-- A positive scale and positive raw orbit give a positive common normalized witness. -/
theorem PositiveRelativeOffsetTail (p : Parameters) (factor : ℤ)
    (factorPositive : 0 < factor) (coprime : Int.gcd factor p.D = 1)
    (offsetDivides : factor ∣ p.C) (qNonnegative : 0 ≤ p.Q)
    (cPositive : 0 < p.C) (dPositive : 0 < p.D)
    (k : ℕ) (power : factor ∣ p.Q ^ k) (n : ℤ) (nPositive : 0 < n) :
    ∃ t : ℕ, ∃ m : ℤ, 0 < m ∧
      Iterate (RawStep p) t n = factor * m ∧ AffineCount p t n ≤ k ∧
      ∀ s : ℕ, Iterate (RawStep p) (t + s) n =
        factor * Iterate (RawStep (RelativeOffsetParameters p factor)) s m := by
  obtain ⟨t, m, endpoint, budget, tail⟩ :=
    RelativeOffsetTail p factor coprime offsetDivides k power n
  have enteredPositive := PositiveIterates p qNonnegative cPositive dPositive n nPositive t
  rw [endpoint] at enteredPositive
  have normalizedPositive := pos_of_mul_pos_right enteredPositive (le_of_lt factorPositive)
  exact ⟨t, m, normalizedPositive, endpoint, budget, tail⟩

/-- An arbitrary target pulls back along scaling without an invariance assumption. -/
theorem RelativeOffsetTargetEquivalence (p : Parameters) (factor : ℤ)
    (coprime : Int.gcd factor p.D = 1) (offsetDivides : factor ∣ p.C)
    (k : ℕ) (power : factor ∣ p.Q ^ k) (target : ℤ → Prop) :
    (∀ m : ℤ, ∃ s : ℕ,
      target (factor * Iterate (RawStep (RelativeOffsetParameters p factor)) s m)) ↔
    (∀ n : ℤ, ∃ t : ℕ, target (Iterate (RawStep p) t n)) := by
  constructor
  · intro captured n
    obtain ⟨t, m, _, _, tail⟩ :=
      RelativeOffsetTail p factor coprime offsetDivides k power n
    obtain ⟨s, reached⟩ := captured m
    exact ⟨t + s, (tail s).symm ▸ reached⟩
  · intro captured m
    obtain ⟨t, reached⟩ := captured (factor * m)
    have scaled := ScalingIterates (RelativeOffsetParameters p factor) factor m coprime t
    rw [RelativeOffsetScale p factor offsetDivides] at scaled
    exact ⟨t, scaled ▸ reached⟩

/-- Positive universal capture uses the same common positive tail, not separate witnesses. -/
theorem PositiveRelativeOffsetTargetEquivalence (p : Parameters) (factor : ℤ)
    (factorPositive : 0 < factor) (coprime : Int.gcd factor p.D = 1)
    (offsetDivides : factor ∣ p.C) (qNonnegative : 0 ≤ p.Q)
    (cPositive : 0 < p.C) (dPositive : 0 < p.D)
    (k : ℕ) (power : factor ∣ p.Q ^ k) (target : ℤ → Prop) :
    (∀ m : ℤ, 0 < m → ∃ s : ℕ,
      target (factor * Iterate (RawStep (RelativeOffsetParameters p factor)) s m)) ↔
    (∀ n : ℤ, 0 < n → ∃ t : ℕ, target (Iterate (RawStep p) t n)) := by
  constructor
  · intro captured n nPositive
    obtain ⟨t, m, mPositive, _, _, tail⟩ := PositiveRelativeOffsetTail p factor
      factorPositive coprime offsetDivides qNonnegative cPositive dPositive
      k power n nPositive
    obtain ⟨s, reached⟩ := captured m mPositive
    exact ⟨t + s, (tail s).symm ▸ reached⟩
  · intro captured m mPositive
    obtain ⟨t, reached⟩ := captured (factor * m) (mul_pos factorPositive mPositive)
    have scaled := ScalingIterates (RelativeOffsetParameters p factor) factor m coprime t
    rw [RelativeOffsetScale p factor offsetDivides] at scaled
    exact ⟨t, scaled ▸ reached⟩

/-- Scaling preserves every return time within the invariant factor lattice. -/
theorem RelativeOffsetReturnTimes (p : Parameters) (factor n : ℤ)
    (coprime : Int.gcd factor p.D = 1) (offsetDivides : factor ∣ p.C) (s : ℕ) :
    Iterate (RawStep p) s (factor * n) = factor * n ↔
      Iterate (RawStep (RelativeOffsetParameters p factor)) s n = n := by
  have returned := ScalingReturnTimes (RelativeOffsetParameters p factor) factor n coprime s
  rw [RelativeOffsetScale p factor offsetDivides] at returned
  exact returned

/-- Prime support gives an explicit, nonoptimal power by one strictly smaller factor child. -/
theorem PrimeSupportPower (factor q : ℕ) (factorPositive : 0 < factor)
    (support : ∀ p : ℕ, Nat.Prime p → p ∣ factor → p ∣ q) : factor ∣ q ^ factor := by
  by_cases unit : factor = 1
  · simp [unit]
  · obtain ⟨p, prime, pDivides⟩ := Nat.exists_prime_and_dvd unit
    let remainder := factor / p
    have product : p * remainder = factor := Nat.mul_div_cancel' pDivides
    have remainderPositive : 0 < remainder := by
      by_contra notPositive
      have zero : remainder = 0 := Nat.eq_zero_of_not_pos notPositive
      rw [zero, mul_zero] at product
      exact (Nat.ne_of_gt factorPositive) product.symm
    have remainderDivides : remainder ∣ factor := by
      refine ⟨p, ?_⟩
      simpa [mul_comm] using product.symm
    have remainderSupport : ∀ r : ℕ, Nat.Prime r → r ∣ remainder → r ∣ q := by
      intro r rPrime rDivides
      exact support r rPrime (dvd_trans rDivides remainderDivides)
    have decrease : remainder < factor := Nat.div_lt_self factorPositive prime.one_lt
    have remainderPower := PrimeSupportPower remainder q remainderPositive remainderSupport
    have combined : factor ∣ q ^ (remainder + 1) := by
      have multiplied := Nat.mul_dvd_mul (support p prime pDivides) remainderPower
      simpa [product, pow_succ, mul_comm] using multiplied
    have doubleBound : remainder + remainder ≤ factor := by
      calc
        remainder + remainder = 2 * remainder := by omega
        _ ≤ p * remainder := Nat.mul_le_mul_right remainder prime.two_le
        _ = factor := product
    have exponentBound : remainder + 1 ≤ factor := by omega
    exact dvd_trans combined (pow_dvd_pow q exponentBound)
termination_by factor
decreasing_by
  exact decrease

/-- Absolute-value divisibility transports prime support to signed integer coefficients. -/
theorem IntegerPrimeSupportPower (factor q : ℤ) (nonzero : factor ≠ 0)
    (support : ∀ p : ℕ, Nat.Prime p → p ∣ factor.natAbs → p ∣ q.natAbs) :
    factor ∣ q ^ factor.natAbs := by
  apply Int.natAbs_dvd_natAbs.mp
  rw [Int.natAbs_pow]
  exact PrimeSupportPower factor.natAbs q.natAbs (Int.natAbs_pos.mpr nonzero) support

/-- Supported factors enter with an explicit affine budget while retaining one whole tail. -/
theorem PrimeSupportedOffsetTail (p : Parameters) (factor : ℤ)
    (coprime : Int.gcd factor p.D = 1) (offsetDivides : factor ∣ p.C)
    (support : ∀ r : ℕ, Nat.Prime r → r ∣ factor.natAbs → r ∣ p.Q.natAbs) (n : ℤ) :
    ∃ t : ℕ, ∃ m : ℤ,
      Iterate (RawStep p) t n = factor * m ∧ AffineCount p t n ≤ factor.natAbs ∧
      ∀ s : ℕ, Iterate (RawStep p) (t + s) n =
        factor * Iterate (RawStep (RelativeOffsetParameters p factor)) s m := by
  have power := IntegerPrimeSupportPower factor p.Q (ScalingNonzero p factor coprime) support
  exact RelativeOffsetTail p factor coprime offsetDivides factor.natAbs power n

/-- Removing a proper positive factor strictly lowers the positive offset, not the multiplier. -/
theorem RelativeOffsetStrictDecrease (p : Parameters) (factor : ℤ)
    (factorLarge : 1 < factor) (cPositive : 0 < p.C) (offsetDivides : factor ∣ p.C) :
    (RelativeOffsetParameters p factor).C.natAbs < p.C.natAbs := by
  have factorAbsLarge : 1 < factor.natAbs := by
    have absBound := Int.natAbs_lt_natAbs_of_nonneg_of_lt (by decide : (0 : ℤ) ≤ 1)
      factorLarge
    simpa using absBound
  have cNonzero : p.C ≠ 0 := ne_of_gt cPositive
  rw [RelativeOffsetParameters, Int.natAbs_ediv_of_dvd offsetDivides]
  exact Nat.div_lt_self (Int.natAbs_pos.mpr cNonzero) factorAbsLarge

/-- Exact division by a positive offset factor preserves the positive parameter class. -/
theorem RelativeOffsetPositiveCore (p : Parameters) (factor : ℤ)
    (factorPositive : 0 < factor) (cPositive : 0 < p.C) (offsetDivides : factor ∣ p.C) :
    0 < (RelativeOffsetParameters p factor).C := by
  have product : factor * (p.C / factor) = p.C := by
    simpa [mul_comm] using Int.ediv_mul_cancel offsetDivides
  change 0 < p.C / factor
  by_contra notPositive
  have nonpositive := mul_nonpos_of_nonneg_of_nonpos (le_of_lt factorPositive)
    (le_of_not_gt notPositive)
  rw [product] at nonpositive
  exact (not_le_of_gt cPositive) nonpositive

/-- A periodic orbit cannot merely enter the invariant lattice without already lying in it. -/
theorem RelativeOffsetPeriodicInLattice (p : Parameters) (factor : ℤ)
    (coprime : Int.gcd factor p.D = 1) (offsetDivides : factor ∣ p.C)
    (k : ℕ) (power : factor ∣ p.Q ^ k) (n : ℤ) (h : ℕ)
    (hPositive : 0 < h) (returned : Iterate (RawStep p) h n = n) : factor ∣ n := by
  obtain ⟨t, m, _, _, tail⟩ := RelativeOffsetTail p factor coprime offsetDivides k power n
  have productBound : t + 1 ≤ h * (t + 1) := by
    have bound := Nat.mul_le_mul_right (t + 1) (Nat.succ_le_of_lt hPositive)
    simpa using bound
  have bound : t ≤ h * (t + 1) := le_trans (Nat.le_succ t) productBound
  have clock : t + (h * (t + 1) - t) = h * (t + 1) := by omega
  have repeated := IterateReturnMultiple (RawStep p) n h (t + 1) returned
  have endpoint := tail (h * (t + 1) - t)
  rw [clock, repeated] at endpoint
  exact ⟨Iterate (RawStep (RelativeOffsetParameters p factor)) (h * (t + 1) - t) m,
    endpoint⟩

/-- Primitive periods agree because every positive return clock, not just one, agrees. -/
theorem RelativeOffsetPrimitiveReturnIff (p : Parameters) (factor n : ℤ)
    (coprime : Int.gcd factor p.D = 1) (offsetDivides : factor ∣ p.C) (h : ℕ) :
    PrimitiveReturn (RawStep p) (factor * n) h ↔
      PrimitiveReturn (RawStep (RelativeOffsetParameters p factor)) n h := by
  constructor
  · intro primitive
    obtain ⟨positive, returned, least⟩ := primitive
    refine ⟨positive, (RelativeOffsetReturnTimes p factor n coprime offsetDivides h).mp
      returned, ?_⟩
    intro r rPositive rReturn
    exact least r rPositive
      ((RelativeOffsetReturnTimes p factor n coprime offsetDivides r).mpr rReturn)
  · intro primitive
    obtain ⟨positive, returned, least⟩ := primitive
    refine ⟨positive, (RelativeOffsetReturnTimes p factor n coprime offsetDivides h).mpr
      returned, ?_⟩
    intro r rPositive rReturn
    exact least r rPositive
      ((RelativeOffsetReturnTimes p factor n coprime offsetDivides r).mp rReturn)

/-- Every original cycle recovers one core state, every phase and its primitive raw period. -/
theorem RelativeOffsetCycleRecovery (p : Parameters) (factor : ℤ)
    (coprime : Int.gcd factor p.D = 1) (offsetDivides : factor ∣ p.C)
    (k : ℕ) (power : factor ∣ p.Q ^ k) (n : ℤ) (h : ℕ)
    (hPositive : 0 < h) (returned : Iterate (RawStep p) h n = n) :
    ∃ m : ℤ, n = factor * m ∧
      (∀ r : ℕ, Iterate (RawStep p) r n =
        factor * Iterate (RawStep (RelativeOffsetParameters p factor)) r m) ∧
      (PrimitiveReturn (RawStep p) n h ↔
        PrimitiveReturn (RawStep (RelativeOffsetParameters p factor)) m h) := by
  obtain ⟨m, endpoint⟩ :=
    RelativeOffsetPeriodicInLattice p factor coprime offsetDivides k power n h
      hPositive returned
  refine ⟨m, endpoint, ?_, ?_⟩
  · intro r
    rw [endpoint]
    have scaled := ScalingIterates (RelativeOffsetParameters p factor) factor m coprime r
    rw [RelativeOffsetScale p factor offsetDivides] at scaled
    exact scaled
  · rw [endpoint]
    exact RelativeOffsetPrimitiveReturnIff p factor m coprime offsetDivides h

/-- A positive integer scale converts a starting-state cutoff to its exact ceiling cutoff. -/
theorem RelativeOffsetSearchBound (factor minimum n : ℕ) (factorPositive : 0 < factor) :
    minimum ≤ factor * n ↔ (minimum + factor - 1) / factor ≤ n := by
  have numeratorPositive : 1 ≤ minimum + factor := by omega
  constructor
  · intro lower
    apply Nat.lt_succ_iff.mp
    apply (Nat.div_lt_iff_lt_mul factorPositive).mpr
    rw [Nat.succ_mul, Nat.mul_comm n factor]
    omega
  · intro lower
    have divided : (minimum + factor - 1) / factor < n + 1 :=
      Nat.lt_succ_iff.mpr lower
    have multiplied := (Nat.div_lt_iff_lt_mul factorPositive).mp divided
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm n factor] at multiplied
    omega

end GeneralizedCollatz
