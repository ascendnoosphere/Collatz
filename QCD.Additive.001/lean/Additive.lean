-- SPDX-License-Identifier: CC-BY-4.0
import AffineEscape
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
namespace GeneralizedCollatz

/-- An inaccessible additive seed has no future divisible affine state. -/
theorem AdditiveNoAccess (c D n j : ℕ) (inaccessible : ¬Nat.gcd c D ∣ n) :
    ¬D ∣ n + j * c := by
  intro divisible
  have gcdDivides : Nat.gcd c D ∣ n + j * c :=
    dvd_trans (Nat.gcd_dvd_right c D) divisible
  have gcdDividesOffset : Nat.gcd c D ∣ j * c :=
    dvd_mul_of_dvd_right (Nat.gcd_dvd_left c D) j
  have gcdDividesSeed : Nat.gcd c D ∣ n :=
    (Nat.dvd_add_iff_left gcdDividesOffset).mpr gcdDivides
  exact inaccessible gcdDividesSeed

/-- The normalized residue gate always reaches division from an accessible seed. -/
theorem AdditiveAccessExists (c D n : ℕ) (DPositive : 0 < D)
    (accessible : Nat.gcd c D ∣ n) :
    ∃ ell < D / Nat.gcd c D, D ∣ n + ell * c := by
  let g := Nat.gcd c D
  have gPositive : 0 < g := Nat.gcd_pos_of_pos_right c DPositive
  have gDividesD : g ∣ D := Nat.gcd_dvd_right c D
  have gDividesC : g ∣ c := Nat.gcd_dvd_left c D
  have lengthPositive : 0 < D / g :=
    Nat.div_pos (Nat.le_of_dvd DPositive gDividesD) gPositive
  have coprime : (c / g).Coprime (D / g) := Nat.coprime_div_gcd_div_gcd gPositive
  let r := (n / g) % (D / g)
  have rLess : r < D / g := Nat.mod_lt _ lengthPositive
  obtain ⟨ell, ellLess, ellResidue⟩ := Nat.exists_mul_mod_eq_of_coprime
    (D / g - r) coprime (Nat.ne_of_gt lengthPositive)
  have divisibleNormalized : D / g ∣ n / g + ell * (c / g) := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    rw [Nat.add_mod, Nat.mul_comm ell, ellResidue]
    change (r + (D / g - r) % (D / g)) % (D / g) = 0
    by_cases rZero : r = 0
    · simp [rZero]
    · have subtractionLess : D / g - r < D / g := by omega
      rw [Nat.mod_eq_of_lt subtractionLess]
      have complement : r + (D / g - r) = D / g := by omega
      rw [complement, Nat.mod_self]
  obtain ⟨v, vEquation⟩ := divisibleNormalized
  refine ⟨ell, ellLess, v, ?_⟩
  have cReconstruct : c / g * g = c := Nat.div_mul_cancel gDividesC
  have nReconstruct : n / g * g = n := Nat.div_mul_cancel accessible
  have dReconstruct : D / g * g = D := Nat.div_mul_cancel gDividesD
  calc
    n + ell * c = (n / g + ell * (c / g)) * g := by
      rw [Nat.add_mul, Nat.mul_assoc, nReconstruct, cReconstruct]
    _ = (D / g * v) * g := by rw [vEquation]
    _ = D * v := by
      rw [Nat.mul_assoc, Nat.mul_comm v g, ← Nat.mul_assoc, dReconstruct]

/-- Division-access indices are unique in the normalized residue interval. -/
theorem AdditiveAccessUnique (c D n ell j : ℕ) (DPositive : 0 < D)
    (ellLess : ell < D / Nat.gcd c D) (jLess : j < D / Nat.gcd c D)
    (ellDivides : D ∣ n + ell * c) (jDivides : D ∣ n + j * c) : ell = j := by
  have sums : Nat.ModEq D (n + ell * c) (n + j * c) :=
    ellDivides.modEq_zero_nat.trans jDivides.modEq_zero_nat.symm
  have products : Nat.ModEq D (ell * c) (j * c) :=
    Nat.ModEq.add_left_cancel' n sums
  have indices : Nat.ModEq (D / Nat.gcd c D) ell j := by
    simpa [Nat.gcd_comm] using products.cancel_right_div_gcd DPositive
  exact indices.eq_of_lt_of_lt ellLess jLess

/-- An accessible seed has one first-division index in the normalized interval. -/
theorem AdditiveFirstDivisionExists (c D n : ℕ) (DPositive : 0 < D)
    (accessible : Nat.gcd c D ∣ n) :
    ∃! ell, ell < D / Nat.gcd c D ∧ D ∣ n + ell * c := by
  obtain ⟨ell, ellLess, ellDivides⟩ := AdditiveAccessExists c D n DPositive accessible
  refine ⟨ell, ⟨ellLess, ellDivides⟩, ?_⟩
  intro j jCondition
  exact AdditiveAccessUnique c D n j ell DPositive
    jCondition.1 ellLess jCondition.2 ellDivides

/-- An inaccessible seed has its entire raw orbit given by successive additions. -/
theorem AdditiveTrapIterate (c D n j : ℕ) (inaccessible : ¬Nat.gcd c D ∣ n) :
    Iterate (PositiveRawStep 1 c D) j n = n + j * c := by
  induction j with
  | zero => {
      simp [Iterate]
    }
  | succ j ih => {
      rw [Iterate, ih]
      have notDivisible := AdditiveNoAccess c D n j inaccessible
      simp [PositiveRawStep, notDivisible, Nat.succ_mul, Nat.add_assoc]
    }

/-- A positive additive offset sends every inaccessible seed to infinity. -/
theorem AdditiveTrapEscape (c D n : ℕ) (cPositive : 0 < c)
    (inaccessible : ¬Nat.gcd c D ∣ n) :
    Filter.Tendsto (fun j => Iterate (PositiveRawStep 1 c D) j n)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_mono' Filter.atTop
    (Filter.Eventually.of_forall ?_) Filter.tendsto_id
  intro j
  change j ≤ Iterate (PositiveRawStep 1 c D) j n
  rw [AdditiveTrapIterate c D n j inaccessible]
  have productLower : j ≤ j * c := Nat.le_mul_of_pos_right j cPositive
  exact le_trans productLower (Nat.le_add_left _ _)

/-- All instructions before the selected division are legal affine instructions. -/
theorem AdditiveFirstDivisionGuards (c D n ell j : ℕ) (DPositive : 0 < D)
    (ellLess : ell < D / Nat.gcd c D) (ellDivides : D ∣ n + ell * c)
    (jBefore : j < ell) : ¬D ∣ n + j * c := by
  intro jDivides
  have equal := AdditiveAccessUnique c D n ell j DPositive ellLess
    (lt_trans jBefore ellLess) ellDivides jDivides
  omega

/-- The selected additive affine prefix has its exact raw-clock endpoint. -/
theorem AdditiveFirstDivisionPrefix (c D n ell j : ℕ) (DPositive : 0 < D)
    (ellLess : ell < D / Nat.gcd c D) (ellDivides : D ∣ n + ell * c)
    (jAtMost : j ≤ ell) :
    Iterate (PositiveRawStep 1 c D) j n = n + j * c := by
  induction j with
  | zero => {
      simp [Iterate]
    }
  | succ j ih => {
      rw [Iterate, ih (by omega)]
      have notDivisible := AdditiveFirstDivisionGuards c D n ell j DPositive
        ellLess ellDivides (by omega)
      simp [PositiveRawStep, notDivisible, Nat.succ_mul, Nat.add_assoc]
    }

/-- A first-division edge expands to precisely the selected additions and one division. -/
theorem AdditiveFirstDivisionRaw (c D n ell : ℕ) (DPositive : 0 < D)
    (ellLess : ell < D / Nat.gcd c D) (ellDivides : D ∣ n + ell * c) :
    Iterate (PositiveRawStep 1 c D) (ell + 1) n = (n + ell * c) / D := by
  rw [Iterate, AdditiveFirstDivisionPrefix c D n ell ell DPositive
    ellLess ellDivides (le_refl ell)]
  simp [PositiveRawStep, ellDivides]


/-- The maximum additive displacement before a first-division endpoint. -/
def AdditiveDisplacement (c D : ℕ) : ℕ := c * (D / Nat.gcd c D - 1)

/-- The additive first-division core uses an exact integer threshold. -/
def AdditiveCoreRadius (c D : ℕ) : ℕ := AdditiveDisplacement c D / (D - 1)

/-- The least access index bounds the endpoint before dividing. -/
theorem AdditiveFirstDivisionUpper (c D n ell : ℕ)
    (ellLess : ell < D / Nat.gcd c D) :
    (n + ell * c) / D ≤ (n + AdditiveDisplacement c D) / D := by
  have indexUpper : ell ≤ D / Nat.gcd c D - 1 := by omega
  have productUpper := Nat.mul_le_mul_right c indexUpper
  have sumUpper : n + ell * c ≤ n + AdditiveDisplacement c D := by
    simp only [AdditiveDisplacement]
    nlinarith
  exact Nat.div_le_div_right sumUpper

/-- Above the integer core radius, each accessible endpoint strictly decreases. -/
theorem AdditiveAboveCoreDescent (c D n ell : ℕ) (DLower : 2 ≤ D)
    (ellLess : ell < D / Nat.gcd c D) (aboveCore : AdditiveCoreRadius c D < n) :
    (n + ell * c) / D < n := by
  have DPositive : 0 < D := by omega
  have divisorPositive : 0 < D - 1 := by omega
  have displacementLess : AdditiveDisplacement c D < n * (D - 1) := by
    exact (Nat.div_lt_iff_lt_mul divisorPositive).mp aboveCore
  have decrement : D - 1 + 1 = D := by omega
  have numeratorLess : n + AdditiveDisplacement c D < n * D := by
    nlinarith
  have coarseStrict : (n + AdditiveDisplacement c D) / D < n :=
    (Nat.div_lt_iff_lt_mul DPositive).mpr numeratorLess
  exact lt_of_le_of_lt (AdditiveFirstDivisionUpper c D n ell ellLess) coarseStrict

/-- The positive finite core is preserved at every accessible first-division endpoint. -/
theorem AdditiveCoreInvariant (c D n ell : ℕ) (DLower : 2 ≤ D)
    (ellLess : ell < D / Nat.gcd c D) (inCore : n ≤ AdditiveCoreRadius c D) :
    (n + ell * c) / D ≤ AdditiveCoreRadius c D := by
  have DPositive : 0 < D := by omega
  have divisorPositive : 0 < D - 1 := by omega
  have remainderBound : AdditiveDisplacement c D <
      (AdditiveCoreRadius c D + 1) * (D - 1) := by
    exact (Nat.div_lt_iff_lt_mul divisorPositive).mp (Nat.lt_succ_self _)
  have decrement : D - 1 + 1 = D := by omega
  have numeratorLess : n + AdditiveDisplacement c D <
      (AdditiveCoreRadius c D + 1) * D := by
    nlinarith
  have coarseBound : (n + AdditiveDisplacement c D) / D <
      AdditiveCoreRadius c D + 1 :=
    (Nat.div_lt_iff_lt_mul DPositive).mpr numeratorLess
  exact Nat.lt_succ_iff.mp (lt_of_le_of_lt
    (AdditiveFirstDivisionUpper c D n ell ellLess) coarseBound)

/-- A legal division endpoint of a positive additive seed is positive. -/
theorem AdditiveFirstDivisionPositive (c D n ell : ℕ) (DPositive : 0 < D)
    (nPositive : 0 < n) (divides : D ∣ n + ell * c) :
    0 < (n + ell * c) / D := by
  have numeratorPositive : 0 < n + ell * c :=
    lt_of_lt_of_le nPositive (Nat.le_add_right _ _)
  have denominatorLe : D ≤ n + ell * c := Nat.le_of_dvd numeratorPositive divides
  exact Nat.div_pos denominatorLe DPositive


/-- The shifted endpoint coordinate retains signed cancellation at the core boundary. -/
def AdditiveDefect (c D n : ℕ) : ℤ :=
  ((D : ℤ) - 1) * (n : ℤ) - (AdditiveDisplacement c D : ℤ)

/-- Every legal endpoint has the unshifted contraction bound before normalization. -/
theorem AdditiveEndpointBound (c D n ell : ℕ)
    (ellLess : ell < D / Nat.gcd c D) :
    D * ((n + ell * c) / D) ≤ n + AdditiveDisplacement c D := by
  have indexUpper : ell ≤ D / Nat.gcd c D - 1 := by omega
  have productUpper := Nat.mul_le_mul_right c indexUpper
  have sumUpper : n + ell * c ≤ n + AdditiveDisplacement c D := by
    simpa [AdditiveDisplacement, Nat.mul_comm] using Nat.add_le_add_left productUpper n
  exact le_trans (Nat.mul_div_le (n + ell * c) D) sumUpper

/-- The exact reference subtraction cancels the accumulated affine displacement. -/
theorem AdditiveDefectStep (c D n m : ℕ) (DLower : 2 ≤ D)
    (endpointBound : D * m ≤ n + AdditiveDisplacement c D) :
    (D : ℤ) * AdditiveDefect c D m ≤ AdditiveDefect c D n := by
  have integerBound : (D : ℤ) * (m : ℤ) ≤
      (n : ℤ) + (AdditiveDisplacement c D : ℤ) := by exact_mod_cast endpointBound
  have DIntegerLower : (2 : ℤ) ≤ D := by exact_mod_cast DLower
  simp only [AdditiveDefect]
  nlinarith

/-- The shifted defect contracts over every specified finite first-division path. -/
theorem AdditivePathDefect (c D h : ℕ) (x : ℕ → ℕ) (DLower : 2 ≤ D)
    (steps : ∀ i < h, D * x (i + 1) ≤ x i + AdditiveDisplacement c D) :
    (D : ℤ) ^ h * AdditiveDefect c D (x h) ≤ AdditiveDefect c D (x 0) := by
  induction h with
  | zero => {
      simp
    }
  | succ h ih => {
      have prefixBound := ih (fun i iLess => steps i (by omega))
      have finalStep := AdditiveDefectStep c D (x h) (x (h + 1)) DLower
        (steps h (by omega))
      have powerNonnegative : 0 ≤ (D : ℤ) ^ h := by positivity
      calc
        (D : ℤ) ^ (h + 1) * AdditiveDefect c D (x (h + 1)) =
            (D : ℤ) ^ h * ((D : ℤ) * AdditiveDefect c D (x (h + 1))) := by
          rw [pow_succ, mul_assoc]
        _ ≤ (D : ℤ) ^ h * AdditiveDefect c D (x h) :=
          mul_le_mul_of_nonneg_left finalStep powerNonnegative
        _ ≤ AdditiveDefect c D (x 0) := prefixBound
    }

/-- Each selected first-division block retains its full raw instruction count. -/
def AdditivePathClock (ell : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => AdditivePathClock ell h + (ell h + 1)

/-- A finite first-division path reconstructs its original raw endpoint and clock. -/
theorem AdditivePathRawRecovery (c D h : ℕ) (x ell : ℕ → ℕ) (DPositive : 0 < D)
    (indices : ∀ i < h, ell i < D / Nat.gcd c D)
    (divisions : ∀ i < h, D ∣ x i + ell i * c)
    (endpoints : ∀ i < h, x (i + 1) = (x i + ell i * c) / D) :
    Iterate (PositiveRawStep 1 c D) (AdditivePathClock ell h) (x 0) = x h := by
  induction h with
  | zero => {
      rfl
    }
  | succ h ih => {
      have prefixRecovered := ih (fun i iLess => indices i (by omega))
        (fun i iLess => divisions i (by omega))
        (fun i iLess => endpoints i (by omega))
      rw [AdditivePathClock, IterateAdd, prefixRecovered]
      rw [AdditiveFirstDivisionRaw c D (x h) (ell h) DPositive
        (indices h (by omega)) (divisions h (by omega))]
      exact (endpoints h (by omega)).symm
    }

/-- The exact raw clock is bounded by the number of blocks times the access window. -/
theorem AdditivePathClockUpper (c D h : ℕ) (ell : ℕ → ℕ)
    (indices : ∀ i < h, ell i < D / Nat.gcd c D) :
    AdditivePathClock ell h ≤ h * (D / Nat.gcd c D) := by
  induction h with
  | zero => {
      simp [AdditivePathClock]
    }
  | succ h ih => {
      have prefixUpper := ih (fun i iLess => indices i (by omega))
      have indexUpper : ell h + 1 ≤ D / Nat.gcd c D := by
        have finalIndex := indices h (by omega)
        omega
      simp only [AdditivePathClock, Nat.succ_mul]
      omega
    }

/-- Coprime offsets have the full radius `c`, with no inaccessible residue class. -/
theorem AdditiveCoprimeCore (c D : ℕ) (DLower : 2 ≤ D) (coprime : Nat.Coprime c D) :
    AdditiveCoreRadius c D = c := by
  rw [AdditiveCoreRadius, AdditiveDisplacement, coprime.gcd_eq_one, Nat.div_one]
  exact Nat.mul_div_cancel c (by omega)

/-- The shifted coordinate is increasing in the state under the declared divisor bound. -/
theorem AdditiveDefectMonotone (c D m n : ℕ) (DLower : 2 ≤ D) (stateLe : m ≤ n) :
    AdditiveDefect c D m ≤ AdditiveDefect c D n := by
  have integerLe : (m : ℤ) ≤ n := by exact_mod_cast stateLe
  have integerLower : (2 : ℤ) ≤ D := by exact_mod_cast DLower
  simp only [AdditiveDefect]
  nlinarith

/-- The first integer above the core has shifted defect between one and the divisor minus one. -/
theorem AdditiveCoreDefectBounds (c D : ℕ) (DLower : 2 ≤ D) :
    1 ≤ AdditiveDefect c D (AdditiveCoreRadius c D + 1) ∧
      AdditiveDefect c D (AdditiveCoreRadius c D + 1) ≤ (D : ℤ) - 1 := by
  have divisorPositive : 0 < D - 1 := by omega
  have below : AdditiveCoreRadius c D * (D - 1) ≤ AdditiveDisplacement c D :=
    Nat.div_mul_le_self (AdditiveDisplacement c D) (D - 1)
  have above : AdditiveDisplacement c D < (AdditiveCoreRadius c D + 1) * (D - 1) :=
    (Nat.div_lt_iff_lt_mul divisorPositive).mp (Nat.lt_succ_self _)
  have decrement : ((D - 1 : ℕ) : ℤ) = (D : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_one]
  have belowInteger : (AdditiveCoreRadius c D : ℤ) * ((D : ℤ) - 1) ≤
      (AdditiveDisplacement c D : ℤ) := by
    rw [← decrement]
    exact_mod_cast below
  have aboveInteger : (AdditiveDisplacement c D : ℤ) <
      ((AdditiveCoreRadius c D : ℤ) + 1) * ((D : ℤ) - 1) := by
    rw [← decrement]
    exact_mod_cast above
  simp only [AdditiveDefect, Nat.cast_add, Nat.cast_one]
  constructor <;> nlinarith

/-- The exact power threshold forces core entry at the last endpoint of a finite path. -/
theorem AdditiveGeometricEntry (c D h : ℕ) (x : ℕ → ℕ) (DLower : 2 ≤ D)
    (steps : ∀ i < h, D * x (i + 1) ≤ x i + AdditiveDisplacement c D)
    (budget : AdditiveDefect c D (x 0) <
      (D : ℤ) ^ h * AdditiveDefect c D (AdditiveCoreRadius c D + 1)) :
    x h ≤ AdditiveCoreRadius c D := by
  by_contra notInCore
  have aboveCore : AdditiveCoreRadius c D + 1 ≤ x h := by omega
  have defectLower := AdditiveDefectMonotone c D (AdditiveCoreRadius c D + 1)
    (x h) DLower aboveCore
  have powerNonnegative : 0 ≤ (D : ℤ) ^ h := by positivity
  have thresholdLe := mul_le_mul_of_nonneg_left defectLower powerNonnegative
  have contraction := AdditivePathDefect c D h x DLower steps
  exact not_lt_of_ge (le_trans thresholdLe contraction) budget

/-- The geometric core estimate has a complete recovery at the original raw clock. -/
theorem AdditiveGeometricRawEntry (c D h : ℕ) (x ell : ℕ → ℕ) (DLower : 2 ≤ D)
    (indices : ∀ i < h, ell i < D / Nat.gcd c D)
    (divisions : ∀ i < h, D ∣ x i + ell i * c)
    (endpoints : ∀ i < h, x (i + 1) = (x i + ell i * c) / D)
    (budget : AdditiveDefect c D (x 0) <
      (D : ℤ) ^ h * AdditiveDefect c D (AdditiveCoreRadius c D + 1)) :
    ∃ t ≤ h * (D / Nat.gcd c D),
      Iterate (PositiveRawStep 1 c D) t (x 0) = x h ∧ x h ≤ AdditiveCoreRadius c D := by
  have steps : ∀ i < h, D * x (i + 1) ≤ x i + AdditiveDisplacement c D := by
    intro i iLess
    rw [endpoints i iLess]
    exact AdditiveEndpointBound c D (x i) (ell i) (indices i iLess)
  refine ⟨AdditivePathClock ell h, AdditivePathClockUpper c D h ell indices, ?_, ?_⟩
  · exact AdditivePathRawRecovery c D h x ell (by omega) indices divisions endpoints
  · exact AdditiveGeometricEntry c D h x DLower steps budget

/-- Every seed has a core-or-trap witness within any valid geometric raw-time budget. -/
theorem AdditiveFiniteBudget (c D h n : ℕ) (DLower : 2 ≤ D) (nPositive : 0 < n)
    (budget : AdditiveDefect c D n <
      (D : ℤ) ^ h * AdditiveDefect c D (AdditiveCoreRadius c D + 1)) :
    ∃ t ≤ h * (D / Nat.gcd c D),
      0 < Iterate (PositiveRawStep 1 c D) t n ∧
      (Iterate (PositiveRawStep 1 c D) t n ≤ AdditiveCoreRadius c D ∨
        ¬Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) t n) := by
  induction h generalizing n with
  | zero => {
      have inCore := AdditiveGeometricEntry c D 0 (fun _ => n) DLower
        (fun i iLess => by omega) budget
      exact ⟨0, by simp, nPositive, Or.inl inCore⟩
    }
  | succ h ih => {
      by_cases inCore : n ≤ AdditiveCoreRadius c D
      · exact ⟨0, Nat.zero_le _, nPositive, Or.inl inCore⟩
      · by_cases accessible : Nat.gcd c D ∣ n
        · obtain ⟨ell, indices, uniqueness⟩ :=
            AdditiveFirstDivisionExists c D n (by omega) accessible
          let m := (n + ell * c) / D
          have mPositive : 0 < m :=
            AdditiveFirstDivisionPositive c D n ell (by omega) nPositive indices.2
          have endpointBound := AdditiveEndpointBound c D n ell indices.1
          have defectStep : (D : ℤ) * AdditiveDefect c D m ≤ AdditiveDefect c D n :=
            AdditiveDefectStep c D n m DLower endpointBound
          have scaledBudget : (D : ℤ) * AdditiveDefect c D m <
              (D : ℤ) * ((D : ℤ) ^ h *
                AdditiveDefect c D (AdditiveCoreRadius c D + 1)) := by
            apply lt_of_le_of_lt defectStep
            simpa [pow_succ, mul_comm, mul_assoc] using budget
          have nextBudget : AdditiveDefect c D m < (D : ℤ) ^ h *
              AdditiveDefect c D (AdditiveCoreRadius c D + 1) := by
            exact lt_of_mul_lt_mul_left scaledBudget
              (by exact_mod_cast (Nat.zero_le D))
          obtain ⟨t, timeBound, positive, outcome⟩ := ih m mPositive nextBudget
          have indexBound : ell + 1 ≤ D / Nat.gcd c D := by omega
          have raw : Iterate (PositiveRawStep 1 c D) (ell + 1) n = m :=
            AdditiveFirstDivisionRaw c D n ell (by omega) indices.1 indices.2
          refine ⟨ell + 1 + t, ?_, ?_, ?_⟩
          · rw [Nat.succ_mul]
            omega
          · rw [IterateAdd, raw]
            exact positive
          · rw [IterateAdd, raw]
            exact outcome
        · exact ⟨0, Nat.zero_le _, nPositive, Or.inr accessible⟩
    }

/-- A finite power budget always exists, including seeds already below the threshold. -/
theorem AdditiveGeometricBudgetExists (c D n : ℕ) (DLower : 2 ≤ D) :
    ∃ h, AdditiveDefect c D n <
      (D : ℤ) ^ h * AdditiveDefect c D (AdditiveCoreRadius c D + 1) := by
  have epsilonPositive := (AdditiveCoreDefectBounds c D DLower).1
  by_cases defectNonnegative : 0 ≤ AdditiveDefect c D n
  · let h := (AdditiveDefect c D n).toNat
    have exponentCast : (h : ℤ) = AdditiveDefect c D n :=
      Int.toNat_of_nonneg defectNonnegative
    have powerGreaterNat : h < D ^ h := Nat.lt_pow_self (by omega)
    have powerGreater : (h : ℤ) < (D : ℤ) ^ h := by exact_mod_cast powerGreaterNat
    have powerNonnegative : 0 ≤ (D : ℤ) ^ h := by positivity
    have gain : (D : ℤ) ^ h ≤
        (D : ℤ) ^ h * AdditiveDefect c D (AdditiveCoreRadius c D + 1) := by
      simpa using mul_le_mul_of_nonneg_left epsilonPositive powerNonnegative
    refine ⟨h, ?_⟩
    rw [← exponentCast]
    exact lt_of_lt_of_le powerGreater gain
  · refine ⟨0, ?_⟩
    simp only [pow_zero, one_mul]
    omega

/-- The additive core has at most one positive vertex per unit of offset. -/
theorem AdditiveCoreRadiusLe (c D : ℕ) (DLower : 2 ≤ D) :
    AdditiveCoreRadius c D ≤ c := by
  have divisorPositive : 0 < D - 1 := by omega
  have quotientLe : D / Nat.gcd c D ≤ D := Nat.div_le_self D (Nat.gcd c D)
  have indexLe : D / Nat.gcd c D - 1 ≤ D - 1 :=
    Nat.sub_le_sub_right quotientLe 1
  have numeratorLe : AdditiveDisplacement c D ≤ c * (D - 1) :=
    Nat.mul_le_mul_left c indexLe
  change AdditiveDisplacement c D / (D - 1) ≤ c
  calc
    AdditiveDisplacement c D / (D - 1) ≤ c * (D - 1) / (D - 1) :=
      Nat.div_le_div_right numeratorLe
    _ = c := Nat.mul_div_cancel c divisorPositive

/-- Every positive additive raw orbit reaches the finite core or an affine-only trap. -/
theorem AdditiveFiniteReduction (c D n : ℕ) (DLower : 2 ≤ D) (nPositive : 0 < n) :
    ∃ t, 0 < Iterate (PositiveRawStep 1 c D) t n ∧
      (Iterate (PositiveRawStep 1 c D) t n ≤ AdditiveCoreRadius c D ∨
        ¬Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) t n) := by
  revert nPositive
  induction n using Nat.strong_induction_on with
  | h n ih => {
      intro nPositive
      by_cases inCore : n ≤ AdditiveCoreRadius c D
      · exact ⟨0, nPositive, Or.inl inCore⟩
      · by_cases accessible : Nat.gcd c D ∣ n
        · have DPositive : 0 < D := by omega
          obtain ⟨ell, ellLess, ellDivides⟩ :=
            AdditiveAccessExists c D n DPositive accessible
          let m := (n + ell * c) / D
          have mPositive : 0 < m :=
            AdditiveFirstDivisionPositive c D n ell DPositive nPositive ellDivides
          have mLess : m < n :=
            AdditiveAboveCoreDescent c D n ell DLower ellLess (by omega)
          obtain ⟨t, reached⟩ := ih m mLess mPositive
          refine ⟨ell + 1 + t, ?_⟩
          rw [IterateAdd, AdditiveFirstDivisionRaw c D n ell DPositive ellLess ellDivides]
          exact reached
        · exact ⟨0, nPositive, Or.inr accessible⟩
    }

/-- Every positive seed reaches the finite core of a coprime additive map. -/
theorem AdditiveCoprimeCapture (c D n : ℕ) (DLower : 2 ≤ D) (nPositive : 0 < n)
    (coprime : Nat.Coprime c D) :
    ∃ t, 0 < Iterate (PositiveRawStep 1 c D) t n ∧
      Iterate (PositiveRawStep 1 c D) t n ≤ c := by
  obtain ⟨t, reachedPositive, inCore | trap⟩ :=
    AdditiveFiniteReduction c D n DLower nPositive
  · rw [AdditiveCoprimeCore c D DLower coprime] at inCore
    exact ⟨t, reachedPositive, inCore⟩
  · rw [coprime.gcd_eq_one] at trap
    exact False.elim (trap (one_dvd _))

/-- A raw orbit that reaches an inaccessible state has its exact linear tail. -/
theorem AdditiveReachedTrapTail (c D n t j : ℕ)
    (trap : ¬Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) t n) :
    Iterate (PositiveRawStep 1 c D) (t + j) n =
      Iterate (PositiveRawStep 1 c D) t n + j * c := by
  rw [IterateAdd]
  exact AdditiveTrapIterate c D _ j trap

/-- An inaccessible raw tail gives full-sequence escape, with the finite prefix retained. -/
theorem AdditiveReachedTrapEscape (c D n t : ℕ) (cPositive : 0 < c)
    (trap : ¬Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) t n) :
    Filter.Tendsto (fun j => Iterate (PositiveRawStep 1 c D) j n)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.mpr ?_
  intro b
  filter_upwards [Filter.eventually_ge_atTop (t + b)] with j jLower
  have bLower : b ≤ j - t := by omega
  have clockSplit : j = t + (j - t) := by omega
  rw [clockSplit, AdditiveReachedTrapTail c D n t (j - t) trap]
  exact le_trans bLower (le_trans (Nat.le_mul_of_pos_right _ cPositive)
    (Nat.le_add_left _ _))

/-- An empty positive core forces every positive additive raw seed to escape. -/
theorem AdditiveZeroCoreEscape (c D n : ℕ) (cPositive : 0 < c)
    (DLower : 2 ≤ D) (nPositive : 0 < n) (emptyCore : AdditiveCoreRadius c D = 0) :
    Filter.Tendsto (fun j => Iterate (PositiveRawStep 1 c D) j n)
      Filter.atTop Filter.atTop := by
  obtain ⟨t, reachedPositive, inCore | trap⟩ :=
    AdditiveFiniteReduction c D n DLower nPositive
  · rw [emptyCore] at inCore
    omega
  · exact AdditiveReachedTrapEscape c D n t cPositive trap

end GeneralizedCollatz
