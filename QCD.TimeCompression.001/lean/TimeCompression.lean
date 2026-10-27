import GeneralizedCollatz

/-!
Exact removal of a common divisor power from the affine coefficients.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Replace the affine coefficients while retaining the signed divisor. -/
def CompressedParameters (p : Parameters) (q c : ℤ) : Parameters where
  Q := q
  C := c
  D := p.D
  DAdmissible := p.DAdmissible

/-- A division costs one raw step; an affine event includes the forced divisions. -/
def CompressionClock (p : Parameters) (a : ℕ) (n : ℤ) : ℕ :=
  if p.D ∣ n then 1 else a + 1

/-- Every compression block advances the original raw clock. -/
theorem CompressionClockPositive (p : Parameters) (a : ℕ) (n : ℤ) :
    1 ≤ CompressionClock p a n := by
  by_cases divisible : p.D ∣ n
  · simp [CompressionClock, divisible]
  · simp [CompressionClock, divisible]

/-- A state carrying `a` explicit divisor factors loses exactly those factors in `a` steps. -/
theorem PowerDivisionRun (p : Parameters) (a : ℕ) (n : ℤ) :
    Iterate (RawStep p) a (p.D ^ a * n) = n := by
  induction a with
  | zero => {
      simp [Iterate]
    }
  | succ a inductionHypothesis => {
      rw [← IterateFirst]
      have divisible : p.D ∣ p.D ^ (a + 1) * n := by
        refine ⟨p.D ^ a * n, ?_⟩
        ring
      have quotient : p.D ^ (a + 1) * n / p.D = p.D ^ a * n := by
        apply Int.ediv_eq_of_eq_mul_left p.DNonzero
        ring
      rw [RawStep, if_pos divisible, quotient, inductionHypothesis]
    }

/-- One compressed step is one exact original block, with no change of state space. -/
theorem CompressionStep (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (n : ℤ) :
    Iterate (RawStep p) (CompressionClock p a n) n =
      RawStep (CompressedParameters p q c) n := by
  by_cases divisible : p.D ∣ n
  · simp [CompressionClock, RawStep, CompressedParameters, divisible, Iterate]
  · have affine : RawStep p n = p.D ^ a * (q * n + c) := by
      rw [RawStep, if_neg divisible, qFactor, cFactor]
      ring
    rw [CompressionClock, if_neg divisible, ← IterateFirst, affine, PowerDivisionRun]
    simp [RawStep, CompressedParameters, divisible]

/-- Every compressed iterate occurs at its accumulated exact original time. -/
theorem CompressionIterates (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c)
    (k : ℕ) (n : ℤ) :
    Iterate (RawStep (CompressedParameters p q c)) k n =
      Iterate (RawStep p)
        (AccumulatedClock (RawStep (CompressedParameters p q c))
          (CompressionClock p a) k n) n := by
  simpa using VariableClockIterates
    (RawStep (CompressedParameters p q c)) (RawStep p) (fun x : ℤ => x)
    (CompressionClock p a)
    (fun x => (CompressionStep p q c a qFactor cFactor x).symm) k n

/-- Count compressed affine events at the same sampled states used by the raw clock. -/
def CompressionAffineCount (p : Parameters) (q c : ℤ) : ℕ → ℤ → ℕ
  | 0, _ => 0
  | k + 1, n =>
      CompressionAffineCount p q c k n +
        if p.D ∣ Iterate (RawStep (CompressedParameters p q c)) k n then 0 else 1

/-- The expanded raw time is the compressed time plus `a` steps per affine event. -/
theorem CompressionClockTotal (p : Parameters) (q c : ℤ) (a k : ℕ) (n : ℤ) :
    AccumulatedClock (RawStep (CompressedParameters p q c))
        (CompressionClock p a) k n =
      k + a * CompressionAffineCount p q c k n := by
  induction k with
  | zero => {
      simp [AccumulatedClock, CompressionAffineCount]
    }
  | succ k inductionHypothesis => {
      simp only [AccumulatedClock, CompressionAffineCount]
      by_cases divisible :
          p.D ∣ Iterate (RawStep (CompressedParameters p q c)) k n
      · simp [CompressionClock, divisible, inductionHypothesis]
        omega
      · simp [CompressionClock, divisible, inductionHypothesis, Nat.mul_succ]
        omega
    }

/-- The sampled trajectory has the explicit raw time `k + a r`. -/
theorem CompressionIteratesAtExpandedTime (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c)
    (k : ℕ) (n : ℤ) :
    Iterate (RawStep (CompressedParameters p q c)) k n =
      Iterate (RawStep p) (k + a * CompressionAffineCount p q c k n) n := by
  rw [← CompressionClockTotal]
  exact CompressionIterates p q c a qFactor cFactor k n

/-- A compressed return is exactly a raw return at the expanded time. -/
theorem CompressionReturnTimes (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c)
    (k : ℕ) (n : ℤ) :
    Iterate (RawStep p) (k + a * CompressionAffineCount p q c k n) n = n ↔
      Iterate (RawStep (CompressedParameters p q c)) k n = n := by
  rw [CompressionIteratesAtExpandedTime p q c a qFactor cFactor]

/-- Any target reached by the compressed system is reached by the original system. -/
theorem CompressionTargetLifts (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c)
    (target : ℤ → Prop)
    (captured : ∀ n : ℤ, ∃ k : ℕ,
      target (Iterate (RawStep (CompressedParameters p q c)) k n)) :
    ∀ n : ℤ, ∃ t : ℕ, target (Iterate (RawStep p) t n) := by
  intro n
  obtain ⟨k, reached⟩ := captured n
  refine ⟨k + a * CompressionAffineCount p q c k n, ?_⟩
  rw [← CompressionIteratesAtExpandedTime p q c a qFactor cFactor]
  exact reached

/-- The coefficient height is an intrinsic nonnegative resource. -/
def CoefficientHeight (q c : ℤ) : ℕ :=
  max q.natAbs c.natAbs

/-- Removing a declared common power scales the coefficient height exactly. -/
theorem CompressionHeightScale (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) :
    CoefficientHeight p.Q p.C = p.D.natAbs ^ a * CoefficientHeight q c := by
  rw [qFactor, cFactor]
  unfold CoefficientHeight
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]
  exact (mul_max (p.D.natAbs ^ a) q.natAbs c.natAbs).symm

/-- A positive removed power strictly lowers height for a nonzero coefficient pair. -/
theorem CompressionHeightStrict (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c)
    (aPositive : 0 < a) (nonzeroPair : q ≠ 0 ∨ c ≠ 0) :
    CoefficientHeight q c < CoefficientHeight p.Q p.C := by
  have heightPositive : 0 < CoefficientHeight q c := by
    unfold CoefficientHeight
    cases nonzeroPair with
    | inl qNonzero =>
      {
        exact lt_of_lt_of_le (Int.natAbs_pos.mpr qNonzero) (Nat.le_max_left _ _)
      }
    | inr cNonzero =>
      {
        exact lt_of_lt_of_le (Int.natAbs_pos.mpr cNonzero) (Nat.le_max_right _ _)
      }
  have factorLarge : 1 < p.D.natAbs ^ a := by
    exact Nat.one_lt_pow (Nat.ne_of_gt aPositive)
      (lt_of_lt_of_le Nat.one_lt_two p.DAdmissible)
  rw [CompressionHeightScale p q c a qFactor cFactor]
  exact lt_mul_of_one_lt_left heightPositive factorLarge

/-- The identity state correspondence does not intertwine the two sample maps
one step at a time, although compression matches the three-step block. -/
theorem CompressionNotOneStepIdentity :
    RawStep { Q := 4, C := 4, D := 2, DAdmissible := by decide } 1 ≠
      RawStep { Q := 1, C := 1, D := 2, DAdmissible := by decide } 1 ∧
    Iterate (RawStep { Q := 4, C := 4, D := 2, DAdmissible := by decide }) 3 1 =
      RawStep { Q := 1, C := 1, D := 2, DAdmissible := by decide } 1 := by
  norm_num [RawStep, Iterate]

end GeneralizedCollatz
