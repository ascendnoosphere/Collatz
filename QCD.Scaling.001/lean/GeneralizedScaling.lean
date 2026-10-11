import GeneralizedCollatz
import Mathlib.Data.Int.GCD

/-!
Coprime signed scaling and entry into an invariant offset lattice.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Scaling changes the offset while retaining the affine multiplier and signed divisor. -/
def ScaleParameters (p : Parameters) (h : ℤ) : Parameters where
  Q := p.Q
  C := h * p.C
  D := p.D
  DAdmissible := p.DAdmissible

/-- A scale coprime to the divisor preserves both complementary raw branch guards. -/
theorem ScalingDivisibility (p : Parameters) (h n : ℤ)
    (coprime : Int.gcd h p.D = 1) : p.D ∣ h * n ↔ p.D ∣ n := by
  constructor
  · intro scaled
    have reversed : Int.gcd p.D h = 1 := by
      simpa [Int.gcd_comm] using coprime
    exact Int.dvd_of_dvd_mul_right_of_gcd_one scaled reversed
  · intro original
    exact dvd_mul_of_dvd_right original h

/-- Coprime scaling intertwines one raw step, not merely its rational relaxation. -/
theorem ScalingStep (p : Parameters) (h n : ℤ)
    (coprime : Int.gcd h p.D = 1) :
    RawStep (ScaleParameters p h) (h * n) = h * RawStep p n := by
  have guards := ScalingDivisibility p h n coprime
  by_cases divisible : p.D ∣ n
  · have scaled : p.D ∣ h * n := guards.mpr divisible
    simp only [RawStep, ScaleParameters, if_pos divisible, if_pos scaled]
    exact Int.mul_ediv_assoc h divisible
  · have scaled : ¬p.D ∣ h * n := fun contradiction => divisible (guards.mp contradiction)
    simp only [RawStep, ScaleParameters, if_neg divisible, if_neg scaled]
    ring

/-- Exact scaling preserves the whole raw clock for every finite iterate. -/
theorem ScalingIterates (p : Parameters) (h n : ℤ)
    (coprime : Int.gcd h p.D = 1) (s : ℕ) :
    Iterate (RawStep (ScaleParameters p h)) s (h * n) = h * Iterate (RawStep p) s n := by
  induction s with
  | zero => { rfl }
  | succ s inductionHypothesis => {
      simp only [Iterate, inductionHypothesis]
      exact ScalingStep p h (Iterate (RawStep p) s n) coprime
    }

/-- A scale coprime to an admissible divisor is nonzero, so multiplication is injective. -/
theorem ScalingNonzero (p : Parameters) (h : ℤ)
    (coprime : Int.gcd h p.D = 1) : h ≠ 0 := by
  intro zero
  have unit : p.D.natAbs = 1 := by simpa [zero] using coprime
  have admissible := p.DAdmissible
  omega

/-- Coprime scaling preserves exactly the set of raw return times, including primitive periods. -/
theorem ScalingReturnTimes (p : Parameters) (h n : ℤ)
    (coprime : Int.gcd h p.D = 1) (s : ℕ) :
    Iterate (RawStep (ScaleParameters p h)) s (h * n) = h * n ↔
      Iterate (RawStep p) s n = n := by
  rw [ScalingIterates p h n coprime s]
  constructor
  · exact mul_left_cancel₀ (ScalingNonzero p h coprime)
  · intro returned
    rw [returned]

/-- A nonzero divisible state strictly decreases in magnitude on the division branch. -/
theorem DivisionMagnitudeDescent (p : Parameters) (n : ℤ)
    (divisible : p.D ∣ n) (nonzero : n ≠ 0) :
    (RawStep p n).natAbs < n.natAbs := by
  rw [RawStep, if_pos divisible, Int.natAbs_ediv_of_dvd divisible]
  have positive : 0 < n.natAbs := Int.natAbs_pos.mpr nonzero
  have divisorLarge : 1 < p.D.natAbs := lt_of_lt_of_le (by decide) p.DAdmissible
  exact Nat.div_lt_self positive divisorLarge

/-- Count affine events along the same first-step recursion as the exact raw trace. -/
def AffineCount (p : Parameters) : ℕ → ℤ → ℕ
  | 0, _ => 0
  | t + 1, n =>
      if p.D ∣ n then AffineCount p t (RawStep p n)
      else AffineCount p t (RawStep p n) + 1

/-- The affine budget and then the current magnitude give a terminating entry rank. -/
theorem OffsetCaptureBudget (p : Parameters) (coprime : Int.gcd p.C p.D = 1)
    (r : ℕ) (n : ℤ) (prepared : p.C ∣ p.Q ^ r * n) :
    ∃ t : ℕ, p.C ∣ Iterate (RawStep p) t n ∧ AffineCount p t n ≤ r := by
  by_cases captured : p.C ∣ n
  · exact ⟨0, captured, Nat.zero_le r⟩
  · cases r with
    | zero => {
        have impossible : p.C ∣ n := by simpa using prepared
        exact False.elim (captured impossible)
      }
    | succ r => {
        by_cases divisible : p.D ∣ n
        · have nonzero : n ≠ 0 := by
            intro zero
            apply captured
            simp [zero]
          have decrease := DivisionMagnitudeDescent p n divisible nonzero
          have multiplied : p.C ∣ (p.Q ^ (r + 1) * (n / p.D)) * p.D := by
            rw [mul_assoc, Int.ediv_mul_cancel divisible]
            exact prepared
          have nextPrepared : p.C ∣ p.Q ^ (r + 1) * RawStep p n := by
            have cancelled := Int.dvd_of_dvd_mul_left_of_gcd_one multiplied coprime
            simpa [RawStep, divisible] using cancelled
          obtain ⟨t, entered, budget⟩ := OffsetCaptureBudget p coprime (r + 1)
            (RawStep p n) nextPrepared
          refine ⟨t + 1, ?_, ?_⟩
          · rw [← IterateFirst]
            exact entered
          · simpa [AffineCount, divisible] using budget
        · have extra : p.C ∣ p.Q ^ r * p.C := ⟨p.Q ^ r, by ring⟩
          have nextPrepared : p.C ∣ p.Q ^ r * RawStep p n := by
            simpa [RawStep, divisible, pow_succ, mul_add, mul_assoc] using
              Int.dvd_add prepared extra
          obtain ⟨t, entered, budget⟩ :=
            OffsetCaptureBudget p coprime r (RawStep p n) nextPrepared
          refine ⟨t + 1, ?_, ?_⟩
          · rw [← IterateFirst]
            exact entered
          · simpa [AffineCount, divisible] using Nat.succ_le_succ budget
      }
termination_by (r, n.natAbs)
decreasing_by
  all_goals omega

/-- Divisibility of one multiplier power gives entry for every signed integer seed. -/
theorem OffsetCapture (p : Parameters) (coprime : Int.gcd p.C p.D = 1)
    (k : ℕ) (power : p.C ∣ p.Q ^ k) (n : ℤ) :
    ∃ t : ℕ, p.C ∣ Iterate (RawStep p) t n := by
  obtain ⟨t, entered, _⟩ :=
    OffsetCaptureBudget p coprime k n (dvd_mul_of_dvd_left power n)
  exact ⟨t, entered⟩

/-- Offset normalization keeps the multiplier, divisor and signed state domain unchanged. -/
def UnitOffsetParameters (p : Parameters) : Parameters where
  Q := p.Q
  C := 1
  D := p.D
  DAdmissible := p.DAdmissible

/-- Scaling the unit-offset parameters by the original offset recovers the original map. -/
theorem UnitOffsetScale (p : Parameters) :
    ScaleParameters (UnitOffsetParameters p) p.C = p := by
  cases p
  simp [ScaleParameters, UnitOffsetParameters]

/-- Coprimality to an admissible divisor rules out a zero offset. -/
theorem OffsetNonzero (p : Parameters) (coprime : Int.gcd p.C p.D = 1) : p.C ≠ 0 := by
  exact ScalingNonzero p p.C coprime

/-- Every orbit enters an exact scaled unit-offset tail after at most k affine events. -/
theorem OffsetOneTail (p : Parameters) (coprime : Int.gcd p.C p.D = 1)
    (k : ℕ) (power : p.C ∣ p.Q ^ k) (n : ℤ) :
    ∃ t : ℕ, ∃ m : ℤ,
      Iterate (RawStep p) t n = p.C * m ∧ AffineCount p t n ≤ k ∧
      ∀ s : ℕ, Iterate (RawStep p) (t + s) n =
        p.C * Iterate (RawStep (UnitOffsetParameters p)) s m := by
  obtain ⟨t, entered, budget⟩ :=
    OffsetCaptureBudget p coprime k n (dvd_mul_of_dvd_left power n)
  obtain ⟨m, endpoint⟩ := entered
  refine ⟨t, m, endpoint, budget, ?_⟩
  intro s
  rw [IterateAdd, endpoint]
  have scaled := ScalingIterates (UnitOffsetParameters p) p.C m coprime s
  rw [UnitOffsetScale] at scaled
  exact scaled

/-- Unit-offset capture lifts to all original seeds through one common tail witness. -/
theorem UnitOffsetCaptureLifts (p : Parameters) (coprime : Int.gcd p.C p.D = 1)
    (k : ℕ) (power : p.C ∣ p.Q ^ k) (target : ℤ → Prop)
    (captured : ∀ m : ℤ, ∃ s : ℕ, target (Iterate
      (RawStep (UnitOffsetParameters p)) s m)) :
    ∀ n : ℤ, ∃ t : ℕ, ∃ m : ℤ, target m ∧ Iterate (RawStep p) t n = p.C * m := by
  intro n
  obtain ⟨t, m, _, _, tail⟩ := OffsetOneTail p coprime k power n
  obtain ⟨s, reached⟩ := captured m
  exact ⟨t + s, Iterate (RawStep (UnitOffsetParameters p)) s m, reached, tail s⟩

/-- Nonzero scaling reflects capture from scaled seeds without a time change. -/
theorem ScaledOffsetCaptureReflects (p : Parameters) (coprime : Int.gcd p.C p.D = 1)
    (target : ℤ → Prop)
    (captured : ∀ n : ℤ, ∃ t : ℕ, ∃ m : ℤ,
      target m ∧ Iterate (RawStep p) t n = p.C * m) :
    ∀ n : ℤ, ∃ t : ℕ, target (Iterate (RawStep (UnitOffsetParameters p)) t n) := by
  intro n
  obtain ⟨t, m, reached, endpoint⟩ := captured (p.C * n)
  have scaled := ScalingIterates (UnitOffsetParameters p) p.C n coprime t
  rw [UnitOffsetScale] at scaled
  rw [scaled] at endpoint
  have equal := mul_left_cancel₀ (OffsetNonzero p coprime) endpoint
  exact ⟨t, equal.symm ▸ reached⟩

/-- Power absorption makes all-seed capture exactly equivalent to unit-offset capture. -/
theorem OffsetCaptureEquivalence (p : Parameters) (coprime : Int.gcd p.C p.D = 1)
    (k : ℕ) (power : p.C ∣ p.Q ^ k) (target : ℤ → Prop) :
    (∀ m : ℤ, ∃ s : ℕ, target (Iterate (RawStep (UnitOffsetParameters p)) s m)) ↔
    (∀ n : ℤ, ∃ t : ℕ, ∃ m : ℤ, target m ∧ Iterate (RawStep p) t n = p.C * m) := by
  constructor
  · exact UnitOffsetCaptureLifts p coprime k power target
  · exact ScaledOffsetCaptureReflects p coprime target

/-- Pulling back an arbitrary target preserves the all-seed obligation without invariance. -/
theorem OffsetTargetEquivalence (p : Parameters) (coprime : Int.gcd p.C p.D = 1)
    (k : ℕ) (power : p.C ∣ p.Q ^ k) (target : ℤ → Prop) :
    (∀ m : ℤ, ∃ s : ℕ,
      target (p.C * Iterate (RawStep (UnitOffsetParameters p)) s m)) ↔
    (∀ n : ℤ, ∃ t : ℕ, target (Iterate (RawStep p) t n)) := by
  constructor
  · intro captured n
    obtain ⟨t, m, reached, endpoint⟩ :=
      UnitOffsetCaptureLifts p coprime k power (fun x => target (p.C * x)) captured n
    refine ⟨t, ?_⟩
    rw [endpoint]
    exact reached
  · intro captured m
    obtain ⟨t, reached⟩ := captured (p.C * m)
    have scaled := ScalingIterates (UnitOffsetParameters p) p.C m coprime t
    rw [UnitOffsetScale] at scaled
    exact ⟨t, scaled ▸ reached⟩

/-- Nonnegative multipliers and positive offsets and divisors preserve positive states. -/
theorem RawStepPositive (p : Parameters) (qNonnegative : 0 ≤ p.Q)
    (cPositive : 0 < p.C) (dPositive : 0 < p.D) (n : ℤ) (nPositive : 0 < n) :
    0 < RawStep p n := by
  by_cases divisible : p.D ∣ n
  · rw [RawStep, if_pos divisible]
    have productPositive : 0 < (n / p.D) * p.D := by
      rw [Int.ediv_mul_cancel divisible]
      exact nPositive
    exact pos_of_mul_pos_left productPositive (le_of_lt dPositive)
  · rw [RawStep, if_neg divisible]
    have multiplied : 0 ≤ p.Q * n := mul_nonneg qNonnegative (le_of_lt nPositive)
    omega

/-- Every raw iterate stays in the positive state domain under the positivity hypotheses. -/
theorem PositiveIterates (p : Parameters) (qNonnegative : 0 ≤ p.Q)
    (cPositive : 0 < p.C) (dPositive : 0 < p.D) (n : ℤ) (nPositive : 0 < n)
    (s : ℕ) : 0 < Iterate (RawStep p) s n := by
  induction s with
  | zero => { exact nPositive }
  | succ s inductionHypothesis => {
      exact RawStepPositive p qNonnegative cPositive dPositive
        (Iterate (RawStep p) s n) inductionHypothesis
    }

/-- The normalized tail of a positive orbit has a positive integer seed, not just a signed one. -/
theorem PositiveOffsetOneTail (p : Parameters) (coprime : Int.gcd p.C p.D = 1)
    (qNonnegative : 0 ≤ p.Q) (cPositive : 0 < p.C) (dPositive : 0 < p.D)
    (k : ℕ) (power : p.C ∣ p.Q ^ k) (n : ℤ) (nPositive : 0 < n) :
    ∃ t : ℕ, ∃ m : ℤ, 0 < m ∧
      Iterate (RawStep p) t n = p.C * m ∧ AffineCount p t n ≤ k ∧
      ∀ s : ℕ, Iterate (RawStep p) (t + s) n =
        p.C * Iterate (RawStep (UnitOffsetParameters p)) s m := by
  obtain ⟨t, m, endpoint, budget, tail⟩ := OffsetOneTail p coprime k power n
  have enteredPositive := PositiveIterates p qNonnegative cPositive dPositive n nPositive t
  rw [endpoint] at enteredPositive
  have normalizedPositive := pos_of_mul_pos_right enteredPositive (le_of_lt cPositive)
  exact ⟨t, m, normalizedPositive, endpoint, budget, tail⟩

/-- Pullback of targets also preserves all-seed capture within the positive invariant domain. -/
theorem PositiveOffsetTargetEquivalence (p : Parameters) (coprime : Int.gcd p.C p.D = 1)
    (qNonnegative : 0 ≤ p.Q) (cPositive : 0 < p.C) (dPositive : 0 < p.D)
    (k : ℕ) (power : p.C ∣ p.Q ^ k) (target : ℤ → Prop) :
    (∀ m : ℤ, 0 < m → ∃ s : ℕ,
      target (p.C * Iterate (RawStep (UnitOffsetParameters p)) s m)) ↔
    (∀ n : ℤ, 0 < n → ∃ t : ℕ, target (Iterate (RawStep p) t n)) := by
  constructor
  · intro captured n nPositive
    obtain ⟨t, m, mPositive, _, _, tail⟩ := PositiveOffsetOneTail p coprime
      qNonnegative cPositive dPositive k power n nPositive
    obtain ⟨s, reached⟩ := captured m mPositive
    exact ⟨t + s, (tail s).symm ▸ reached⟩
  · intro captured m mPositive
    obtain ⟨t, reached⟩ := captured (p.C * m) (mul_pos cPositive mPositive)
    have scaled := ScalingIterates (UnitOffsetParameters p) p.C m coprime t
    rw [UnitOffsetScale] at scaled
    exact ⟨t, scaled ▸ reached⟩

/-- A noncoprime scale can change the branch even for the classical positive parameters. -/
theorem NoncoprimeScalingFailure :
    RawStep (ScaleParameters ClassicalParameters 2) 2 ≠
      2 * RawStep ClassicalParameters 1 := by
  norm_num [RawStep, ScaleParameters, ClassicalParameters]

end GeneralizedCollatz
