import GeneralizedCollatz
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.MaxPowDiv

/-!
A greatest-common-divisor obstruction to every future division branch.

For positive natural parameters, if `gcd q d` does not divide `c`, an orbit
has only its finite initial run of divisions.  Its remaining states have an
exact affine formula and tend to infinity.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Positive raw dynamics, kept separate from signed dynamics while proving order facts. -/
def PositiveRawStep (q c d n : ℕ) : ℕ :=
  if d ∣ n then n / d else q * n + c

/-- The geometric sum in the chronological recurrence order. -/
def GeometricSum (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => q * GeometricSum q j + 1

/-- The closed form for `j` successive affine instructions from `x`. -/
def AffineTail (q c x j : ℕ) : ℕ :=
  q ^ j * x + c * GeometricSum q j

/-- Natural parameters embed into the signed foundational parameter space. -/
def NaturalParameters (q c d : ℕ) (dAdmissible : 2 ≤ d) : Parameters where
  Q := q
  C := c
  D := d
  DAdmissible := by simpa using dAdmissible

/-- The positive raw step is the restriction of the signed foundational raw step. -/
theorem PositiveRawStepCast (q c d n : ℕ) (dAdmissible : 2 ≤ d) :
    (PositiveRawStep q c d n : ℤ) =
      RawStep (NaturalParameters q c d dAdmissible) n := by
  by_cases h : d ∣ n
  · obtain ⟨a, rfl⟩ := h
    simp [PositiveRawStep, RawStep, NaturalParameters]
  · have hz : ¬(d : ℤ) ∣ (n : ℤ) := by
      exact fun hd => h (Int.natCast_dvd_natCast.mp hd)
    simp [PositiveRawStep, RawStep, NaturalParameters, h, hz]

/-- A multiple of `d` takes one exact division step when `d` is nonzero. -/
theorem PositiveRawStepMultiple (q c d y : ℕ) (dPositive : 0 < d) :
    PositiveRawStep q c d (d * y) = y := by
  simp [PositiveRawStep, dPositive.ne']

/-- A successor iterate may execute its first instruction before the remaining ones. -/
theorem IterateSuccFirst {α : Type*} (f : α → α) (k : ℕ) (x : α) :
    Iterate f (k + 1) x = Iterate f k (f x) := by
  rw [show k + 1 = 1 + k by omega, IterateAdd]
  rfl

/-- Iterating from `d^k x` performs the selected `k` initial divisions exactly. -/
theorem PositiveDivisionPrefix (q c d x k : ℕ) (dPositive : 0 < d) :
    Iterate (PositiveRawStep q c d) k (d ^ k * x) = x := by
  induction k with
  | zero => {
      simp [Iterate]
    }
  | succ k ih => {
      rw [IterateSuccFirst, pow_succ', Nat.mul_assoc,
        PositiveRawStepMultiple q c d _ dPositive]
      exact ih
    }

/-- The gcd obstruction makes every affine output nondivisible by `d`. -/
theorem GcdBarrierOutput (q c d y : ℕ) (barrier : ¬Nat.gcd q d ∣ c) :
    ¬d ∣ q * y + c := by
  intro hd
  have hgq : Nat.gcd q d ∣ q := Nat.gcd_dvd_left q d
  have hgd : Nat.gcd q d ∣ d := Nat.gcd_dvd_right q d
  have hgqy : Nat.gcd q d ∣ q * y := dvd_mul_of_dvd_left hgq y
  have hgsum : Nat.gcd q d ∣ q * y + c := dvd_trans hgd hd
  exact barrier ((Nat.dvd_add_iff_right hgqy).mpr hgsum)

/-- The affine closed form advances by one instruction. -/
theorem AffineTailSucc (q c x j : ℕ) :
    AffineTail q c x (j + 1) = q * AffineTail q c x j + c := by
  simp only [AffineTail, GeometricSum, pow_succ]
  ring

/-- Formula and nondivisibility propagate together along the affine tail. -/
theorem GcdBarrierTail (q c d x : ℕ) (barrier : ¬Nat.gcd q d ∣ c)
    (anchorNondivisible : ¬d ∣ x) (j : ℕ) :
    Iterate (PositiveRawStep q c d) j x = AffineTail q c x j ∧
      ¬d ∣ Iterate (PositiveRawStep q c d) j x := by
  induction j with
  | zero => {
      exact ⟨by simp [Iterate, AffineTail, GeometricSum],
        by simpa [Iterate] using anchorNondivisible⟩
    }
  | succ j ih => {
      have step : PositiveRawStep q c d (Iterate (PositiveRawStep q c d) j x) =
          q * Iterate (PositiveRawStep q c d) j x + c := by
        simp [PositiveRawStep, ih.2]
      constructor
      · simp only [Iterate]
        rw [step, ih.1]
        exact (AffineTailSucc q c x j).symm
      · simp only [Iterate, step]
        exact GcdBarrierOutput q c d _ barrier
    }

/-- After a nondivisible anchor, every state has the exact affine closed form. -/
theorem GcdBarrierTailFormula (q c d x : ℕ) (barrier : ¬Nat.gcd q d ∣ c)
    (anchorNondivisible : ¬d ∣ x) (j : ℕ) :
    Iterate (PositiveRawStep q c d) j x = AffineTail q c x j := by
  exact (GcdBarrierTail q c d x barrier anchorNondivisible j).1

/-- Every state after the anchor stays outside the division branch. -/
theorem GcdBarrierTailNondivisible (q c d x : ℕ) (barrier : ¬Nat.gcd q d ∣ c)
    (anchorNondivisible : ¬d ∣ x) (j : ℕ) :
    ¬d ∣ Iterate (PositiveRawStep q c d) j x := by
  exact (GcdBarrierTail q c d x barrier anchorNondivisible j).2

/-- Every positive seed has a canonical finite initial division prefix and exact affine tail. -/
theorem GcdBarrierAllSeedFormula (q c d n : ℕ) (dAtLeastTwo : 2 ≤ d)
    (seedPositive : 0 < n)
    (barrier : ¬Nat.gcd q d ∣ c) :
    let k := padicValNat d n
    let x := Nat.divMaxPow n d
    ¬d ∣ x ∧
      ∀ j, Iterate (PositiveRawStep q c d) (k + j) n = AffineTail q c x j := by
  let k := padicValNat d n
  let x := Nat.divMaxPow n d
  have seedNonzero : n ≠ 0 := seedPositive.ne'
  have dGreaterOne : 1 < d := dAtLeastTwo
  have anchorNondivisible : ¬d ∣ x := by
    exact Nat.not_dvd_divMaxPow dGreaterOne seedNonzero
  refine ⟨anchorNondivisible, ?_⟩
  intro j
  rw [IterateAdd]
  have decomposition : d ^ k * x = n := by
    exact Nat.pow_padicValNat_mul_divMaxPow d n
  have prefixResult : Iterate (PositiveRawStep q c d) k n = x := by
    rw [← decomposition]
    exact PositiveDivisionPrefix q c d x k (by omega)
  rw [prefixResult]
  exact GcdBarrierTailFormula q c d x barrier anchorNondivisible j

/-- Under the gcd obstruction, every positive raw orbit tends to infinity. -/
theorem GcdBarrierAllSeedEscape (q c d n : ℕ) (qAtLeastTwo : 2 ≤ q)
    (dAtLeastTwo : 2 ≤ d) (seedPositive : 0 < n)
    (barrier : ¬Nat.gcd q d ∣ c) :
    let k := padicValNat d n
    Filter.Tendsto (fun j => Iterate (PositiveRawStep q c d) (k + j) n)
      Filter.atTop Filter.atTop := by
  let k := padicValNat d n
  let x := Nat.divMaxPow n d
  have formula := GcdBarrierAllSeedFormula q c d n dAtLeastTwo seedPositive barrier
  dsimp only at formula ⊢
  have seedNonzero : n ≠ 0 := seedPositive.ne'
  have decomposition : d ^ padicValNat d n * x = n := by
    exact Nat.pow_padicValNat_mul_divMaxPow d n
  have anchorPositive : 0 < x := by
    by_contra hx
    have xZero : x = 0 := Nat.eq_zero_of_not_pos hx
    rw [xZero, Nat.mul_zero] at decomposition
    exact seedNonzero decomposition.symm
  have powerTends : Filter.Tendsto (fun j : ℕ => q ^ j) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  refine Filter.tendsto_atTop_mono' Filter.atTop
    (Filter.Eventually.of_forall ?_) powerTends
  intro j
  change q ^ j ≤ Iterate (PositiveRawStep q c d) (padicValNat d n + j) n
  rw [formula.2 j]
  exact le_trans (Nat.le_mul_of_pos_right (q ^ j) anchorPositive)
    (Nat.le_add_right (q ^ j * x) _)

end GeneralizedCollatz
