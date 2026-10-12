-- SPDX-License-Identifier: CC-BY-4.0
import Additive
import Mathlib.Data.Nat.GCD.Basic
import DynamicalMorphisms
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Repeated gcd removal separates a divisor-power factor from a divisor-coprime factor. -/
theorem AdditiveOffsetDecomposition (c D : ℕ) (cPositive : 0 < c) :
    ∃ s t k : ℕ, 0 < s ∧ 0 < t ∧ s * t = c ∧ Nat.Coprime t D ∧ s ∣ D ^ k := by
  induction c using Nat.strong_induction_on with
  | h c ih => {
    by_cases coprime : Nat.Coprime c D
    · exact ⟨1, c, 0, by omega, cPositive, by simp, coprime, by simp⟩
    · let g := Nat.gcd c D
      have gPositive : 0 < g := Nat.gcd_pos_of_pos_left D cPositive
      have gLarge : 1 < g := by
        have notOne : g ≠ 1 := by
          intro equal
          apply coprime
          exact equal
        omega
      have gDividesC : g ∣ c := Nat.gcd_dvd_left c D
      have gDividesD : g ∣ D := Nat.gcd_dvd_right c D
      have quotientPositive : 0 < c / g :=
        Nat.div_pos (Nat.le_of_dvd cPositive gDividesC) gPositive
      have quotientLess : c / g < c := Nat.div_lt_self cPositive gLarge
      rcases ih (c / g) quotientLess quotientPositive with
        ⟨s, t, k, sPositive, tPositive, product, tCoprime, sPower⟩
      refine ⟨g * s, t, k + 1, Nat.mul_pos gPositive sPositive,
        tPositive, ?_, tCoprime, ?_⟩
      · calc
          g * s * t = g * (s * t) := Nat.mul_assoc g s t
          _ = g * (c / g) := by rw [product]
          _ = c := Nat.mul_div_cancel' gDividesC
      · have divides : g * s ∣ D * D ^ k := Nat.mul_dvd_mul gDividesD sPower
        simpa [Nat.pow_succ, Nat.mul_comm] using divides
  }

/-- Every divisor of the offset that is coprime to the divisor lies in the extracted factor. -/
theorem AdditiveCoprimeFactorMaximal (c D s t k u : ℕ)
    (product : s * t = c) (sPower : s ∣ D ^ k)
    (uDivides : u ∣ c) (uCoprime : Nat.Coprime u D) : u ∣ t := by
  have uSCoprime : Nat.Coprime u s :=
    (uCoprime.pow_right k).coprime_dvd_right sPower
  apply uSCoprime.dvd_of_dvd_mul_left
  rw [product]
  exact uDivides

/-- The chronological kernel retains the addition count at each division level. -/
def AdditiveReturnKernel (D : ℕ) (ell : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => AdditiveReturnKernel D ell h + D ^ h * ell h

/-- Multiplying the exact first-division equations recovers the path numerator. -/
theorem AdditiveReturnEquation (c D h : ℕ) (ell x : ℕ → ℕ)
    (path : ∀ i < h, D * x (i + 1) = x i + ell i * c) :
    D ^ h * x h = x 0 + c * AdditiveReturnKernel D ell h := by
  induction h with
  | zero => {
    simp [AdditiveReturnKernel]
  }
  | succ h ih => {
    have earlier : ∀ i < h, D * x (i + 1) = x i + ell i * c := by
      intro i iLess
      exact path i (by omega)
    have previous := ih earlier
    have edge := path h (by omega)
    calc
      D ^ (h + 1) * x (h + 1) = D ^ h * (D * x (h + 1)) := by
        ring
      _ = D ^ h * (x h + ell h * c) := by rw [edge]
      _ = (x 0 + c * AdditiveReturnKernel D ell h) + D ^ h * (ell h * c) := by
        rw [Nat.mul_add, previous]
      _ = x 0 + c * AdditiveReturnKernel D ell (h + 1) := by
        simp only [AdditiveReturnKernel]
        ring
  }

/-- A factor supported on the divisor is coprime to every nontrivial return multiplier. -/
theorem AdditiveSupportedCoprimeReturn (D s k h : ℕ) (DLower : 2 ≤ D)
    (hPositive : 0 < h) (sPower : s ∣ D ^ k) : Nat.Coprime s (D ^ h - 1) := by
  have powerPositive : 0 < D ^ h := pow_pos (by omega : 0 < D) h
  have powerCoprime : Nat.Coprime (D ^ h) (D ^ h - 1) :=
    (Nat.coprime_self_sub_right (by omega : 1 ≤ D ^ h)).mpr
      (Nat.coprime_one_right (D ^ h))
  have baseCoprime : Nat.Coprime D (D ^ h - 1) :=
    (Nat.coprime_pow_left_iff hPositive D (D ^ h - 1)).mp powerCoprime
  exact (baseCoprime.pow_left k).coprime_dvd_left sPower

/-- The exact return equation forces the divisor-supported offset factor into every state. -/
theorem AdditiveReturnSupportedFactor (c D s k h n b : ℕ) (DLower : 2 ≤ D)
    (hPositive : 0 < h) (sOffset : s ∣ c) (sPower : s ∣ D ^ k)
    (returned : D ^ h * n = n + c * b) : s ∣ n := by
  have powerPositive : 0 < D ^ h := pow_pos (by omega : 0 < D) h
  have product : (D ^ h - 1) * n = c * b := by
    have restored : D ^ h - 1 + 1 = D ^ h := Nat.sub_add_cancel (by omega)
    have expanded : (D ^ h - 1 + 1) * n = n + c * b := by
      rw [restored]
      exact returned
    nlinarith
  have supported : s ∣ (D ^ h - 1) * n := by
    rw [product]
    exact dvd_mul_of_dvd_left sOffset b
  have coprime := AdditiveSupportedCoprimeReturn D s k h DLower hPositive sPower
  exact coprime.dvd_of_dvd_mul_left supported

/-- Divisor-supported factors propagate backward through every exact division equation. -/
theorem AdditiveSupportedBackward (c D s h : ℕ) (ell x : ℕ → ℕ)
    (sOffset : s ∣ c) (path : ∀ i < h, D * x (i + 1) = x i + ell i * c)
    (finalSupported : s ∣ x h) : ∀ i ≤ h, s ∣ x i := by
  induction h with
  | zero => {
    intro i iLe
    have equal : i = 0 := by omega
    simpa [equal] using finalSupported
  }
  | succ h ih => {
    have edge := path h (by omega)
    have finalProduct : s ∣ D * x (h + 1) :=
      dvd_mul_of_dvd_right finalSupported D
    have offsetProduct : s ∣ ell h * c := dvd_mul_of_dvd_right sOffset (ell h)
    have previousSupported : s ∣ x h := by
      have difference := Nat.dvd_sub finalProduct offsetProduct
      simpa [edge] using difference
    have earlier := ih (fun i iLess => path i (by omega)) previousSupported
    intro i iLe
    by_cases finalIndex : i = h + 1
    · simpa [finalIndex] using finalSupported
    · exact earlier i (by omega)
  }

/-- A closed first-division path has the supported offset factor at all its vertices. -/
theorem AdditiveClosedPathSupported (c D s k h : ℕ) (ell x : ℕ → ℕ)
    (DLower : 2 ≤ D) (hPositive : 0 < h) (sOffset : s ∣ c) (sPower : s ∣ D ^ k)
    (path : ∀ i < h, D * x (i + 1) = x i + ell i * c) (closed : x h = x 0) :
    ∀ i ≤ h, s ∣ x i := by
  have equation := AdditiveReturnEquation c D h ell x path
  rw [closed] at equation
  have firstSupported := AdditiveReturnSupportedFactor c D s k h (x 0)
    (AdditiveReturnKernel D ell h) DLower hPositive sOffset sPower equation
  have finalSupported : s ∣ x h := by rw [closed]; exact firstSupported
  exact AdditiveSupportedBackward c D s h ell x sOffset path finalSupported

/-- A closed contracting endpoint path cannot start above its exact finite core. -/
theorem AdditiveClosedPathCore (c D h : ℕ) (x : ℕ → ℕ) (DLower : 2 ≤ D)
    (hPositive : 0 < h)
    (steps : ∀ i < h, D * x (i + 1) ≤ x i + AdditiveDisplacement c D)
    (closed : x h = x 0) : x 0 ≤ AdditiveCoreRadius c D := by
  have contracted := AdditivePathDefect c D h x DLower steps
  rw [closed] at contracted
  have DIntegerLower : (2 : ℤ) ≤ D := by exact_mod_cast DLower
  have powerLarge : (1 : ℤ) < (D : ℤ) ^ h :=
    one_lt_pow₀ (by omega) (by omega : h ≠ 0)
  have defectNonpositive : AdditiveDefect c D (x 0) ≤ 0 := by
    nlinarith
  by_contra outside
  have above : AdditiveCoreRadius c D < x 0 := by omega
  have displacementLess : AdditiveDisplacement c D < x 0 * (D - 1) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < D - 1)).mp above
  have integerLess : (AdditiveDisplacement c D : ℤ) <
      (x 0 : ℤ) * ((D - 1 : ℕ) : ℤ) := by exact_mod_cast displacementLess
  have decrement : ((D - 1 : ℕ) : ℤ) + 1 = (D : ℤ) := by
    exact_mod_cast (show D - 1 + 1 = D by omega)
  simp only [AdditiveDefect] at defectNonpositive
  nlinarith

/-- The scaled cycle window removes the divisor-supported offset factor. -/
def AdditiveCycleWindow (c D t : ℕ) : ℕ :=
  t * (D / Nat.gcd c D - 1) / (D - 1)

/-- The cycle window lies in one complete set of positive residue representatives. -/
theorem AdditiveCycleWindowUpper (c D t : ℕ) (DLower : 2 ≤ D) :
    AdditiveCycleWindow c D t ≤ t := by
  have decrementPositive : 0 < D - 1 := by omega
  have phaseBound : D / Nat.gcd c D - 1 ≤ D - 1 :=
    Nat.sub_le_sub_right (Nat.div_le_self D (Nat.gcd c D)) 1
  have productBound := Nat.mul_le_mul_left t phaseBound
  have divided := Nat.div_le_div_right (c := D - 1) productBound
  simpa [AdditiveCycleWindow, Nat.mul_div_cancel t decrementPositive] using divided

/-- Positive representatives congruent to a larger multiple admit a nonnegative lift. -/
theorem AdditiveModularNumerator (D t m next : ℕ) (DPositive : 0 < D)
    (nextPositive : 0 < next) (mUpper : m ≤ t)
    (congruence : Nat.ModEq t (D * next) m) : m ≤ D * next := by
  have productPositive : 0 < D * next := Nat.mul_pos DPositive nextPositive
  by_contra below
  have productLess : D * next < m := by omega
  have productLessT : D * next < t := lt_of_lt_of_le productLess mUpper
  by_cases boundary : m = t
  · have remainder := congruence
    change (D * next) % t = m % t at remainder
    rw [boundary, Nat.mod_self, Nat.mod_eq_of_lt productLessT] at remainder
    omega
  · have mLessT : m < t := by omega
    have equal := congruence.eq_of_lt_of_lt productLessT mLessT
    omega

/-- Every modular edge inside the scaled window reconstructs all raw first-division guards. -/
theorem AdditiveModularEdgeLegal (c D s t m next : ℕ) (DLower : 2 ≤ D)
    (sPositive : 0 < s) (tPositive : 0 < t) (product : s * t = c)
    (mPositive : 0 < m) (nextPositive : 0 < next)
    (mWindow : m ≤ AdditiveCycleWindow c D t)
    (nextWindow : next ≤ AdditiveCycleWindow c D t)
    (congruence : Nat.ModEq t (D * next) m) :
    ∃ ell < D / Nat.gcd c D,
      D ∣ s * m + ell * c ∧ (s * m + ell * c) / D = s * next ∧
      (∀ j < ell, ¬D ∣ s * m + j * c) ∧
      Iterate (PositiveRawStep 1 c D) (ell + 1) (s * m) = s * next := by
  have DPositive : 0 < D := by omega
  have cPositive : 0 < c := by rw [← product]; exact Nat.mul_pos sPositive tPositive
  have gcdPositive := Nat.gcd_pos_of_pos_left D cPositive
  have gcdUpper : Nat.gcd c D ≤ D := Nat.le_of_dvd DPositive (Nat.gcd_dvd_right c D)
  have phasePositive : 0 < D / Nat.gcd c D := Nat.div_pos gcdUpper gcdPositive
  have mUpper : m ≤ t := le_trans mWindow (AdditiveCycleWindowUpper c D t DLower)
  have nextUpper : next ≤ t :=
    le_trans nextWindow (AdditiveCycleWindowUpper c D t DLower)
  have numeratorNonnegative :=
    AdditiveModularNumerator D t m next DPositive nextPositive mUpper congruence
  have differenceDivides : t ∣ D * next - m :=
    (Nat.modEq_iff_dvd' numeratorNonnegative).mp congruence.symm
  rcases differenceDivides with ⟨ell, difference⟩
  have restored : D * next - m + m = D * next :=
    Nat.sub_add_cancel numeratorNonnegative
  have edge : D * next = m + ell * t := by nlinarith
  have windowBound : AdditiveCycleWindow c D t * (D - 1) ≤
      t * (D / Nat.gcd c D - 1) := Nat.div_mul_le_self _ _
  have nextBound : next * (D - 1) ≤ t * (D / Nat.gcd c D - 1) :=
    le_trans (Nat.mul_le_mul_right (D - 1) nextWindow) windowBound
  have divisorDecrement : D - 1 + 1 = D := by omega
  have phaseDecrement : D / Nat.gcd c D - 1 + 1 = D / Nat.gcd c D := by omega
  have scaledLess : ell * t < (D / Nat.gcd c D) * t := by nlinarith
  have ellLess : ell < D / Nat.gcd c D := (Nat.mul_lt_mul_right tPositive).mp scaledLess
  have rawEquation : s * m + ell * c = D * (s * next) := by
    calc
      s * m + ell * c = s * (m + ell * t) := by rw [← product]; ring
      _ = s * (D * next) := by rw [← edge]
      _ = D * (s * next) := by ring
  have divides : D ∣ s * m + ell * c := ⟨s * next, rawEquation⟩
  have endpoint : (s * m + ell * c) / D = s * next := by
    rw [rawEquation]
    exact Nat.mul_div_cancel_left _ DPositive
  refine ⟨ell, ellLess, divides, endpoint, ?_, ?_⟩
  · intro j jBefore
    exact AdditiveFirstDivisionGuards c D (s * m) ell j DPositive ellLess divides jBefore
  · rw [← endpoint]
    exact AdditiveFirstDivisionRaw c D (s * m) ell DPositive ellLess divides

/-- Scaling the integer core is equivalent to the smaller modular window. -/
theorem AdditiveScaledCoreIff (c D s t m : ℕ) (DLower : 2 ≤ D)
    (sPositive : 0 < s) (product : s * t = c) :
    s * m ≤ AdditiveCoreRadius c D ↔ m ≤ AdditiveCycleWindow c D t := by
  have decrementPositive : 0 < D - 1 := by omega
  have offsetFactor : c * (D / Nat.gcd c D - 1) =
      s * (t * (D / Nat.gcd c D - 1)) := by rw [← Nat.mul_assoc, product]
  constructor
  · intro inCore
    have rawBound : s * m * (D - 1) ≤ c * (D / Nat.gcd c D - 1) :=
      (Nat.le_div_iff_mul_le decrementPositive).mp inCore
    rw [offsetFactor] at rawBound
    have normalized : s * (m * (D - 1)) ≤ s * (t * (D / Nat.gcd c D - 1)) := by
      simpa [Nat.mul_assoc] using rawBound
    have cancelled : m * (D - 1) ≤ t * (D / Nat.gcd c D - 1) := by
      by_contra larger
      have strict : t * (D / Nat.gcd c D - 1) < m * (D - 1) := by omega
      have scaled := Nat.mul_lt_mul_left sPositive |>.mpr strict
      exact (not_lt_of_ge normalized) scaled
    exact (Nat.le_div_iff_mul_le decrementPositive).mpr cancelled
  · intro inWindow
    have smallerBound : m * (D - 1) ≤ t * (D / Nat.gcd c D - 1) :=
      (Nat.le_div_iff_mul_le decrementPositive).mp inWindow
    have scaled := Nat.mul_le_mul_left s smallerBound
    have rawBound : s * m * (D - 1) ≤ c * (D / Nat.gcd c D - 1) := by
      calc
        s * m * (D - 1) = s * (m * (D - 1)) := Nat.mul_assoc s m (D - 1)
        _ ≤ s * (t * (D / Nat.gcd c D - 1)) := scaled
        _ = c * (D / Nat.gcd c D - 1) := offsetFactor.symm
    exact (Nat.le_div_iff_mul_le decrementPositive).mpr rawBound

/-- Cancelling the supported factor recovers the modular relation of every scaled edge. -/
theorem AdditiveScaledEdgeCongruence (c D s t m next ell : ℕ)
    (sPositive : 0 < s) (product : s * t = c)
    (edge : D * (s * next) = s * m + ell * c) : Nat.ModEq t (D * next) m := by
  have scaled : s * (D * next) = s * (m + ell * t) := by
    calc
      s * (D * next) = D * (s * next) := by ring
      _ = s * m + ell * c := edge
      _ = s * (m + ell * t) := by rw [← product]; ring
  have cancelled : D * next = m + ell * t :=
    mul_left_cancel₀ (by omega : s ≠ 0) scaled
  rw [cancelled]
  exact Nat.add_modEq_left_iff.mpr (dvd_mul_left t ell)

/-- Each first-division block contributes at least one original instruction. -/
theorem AdditivePathClockLower (ell : ℕ → ℕ) (h : ℕ) : h ≤ AdditivePathClock ell h := by
  induction h with
  | zero => {
    simp [AdditivePathClock]
  }
  | succ h ih => {
    simp only [AdditivePathClock]
    omega
  }

/-- A modular closed path in the exact window expands to a positive-time raw return. -/
theorem AdditiveModularClosedLift (c D s t h : ℕ) (m : ℕ → ℕ)
    (DLower : 2 ≤ D) (sPositive : 0 < s) (tPositive : 0 < t) (hPositive : 0 < h)
    (product : s * t = c) (positive : ∀ i ≤ h, 0 < m i)
    (windows : ∀ i ≤ h, m i ≤ AdditiveCycleWindow c D t)
    (modular : ∀ i < h, Nat.ModEq t (D * m (i + 1)) (m i))
    (closed : m h = m 0) :
    ∃ r, 0 < r ∧ r ≤ h * (D / Nat.gcd c D) ∧
      Iterate (PositiveRawStep 1 c D) r (s * m 0) = s * m 0 := by
  classical
  have selected : ∀ i, ∃ ell, i < h → ell < D / Nat.gcd c D ∧
      D ∣ s * m i + ell * c ∧ (s * m i + ell * c) / D = s * m (i + 1) := by
    intro i
    by_cases before : i < h
    · rcases AdditiveModularEdgeLegal c D s t (m i) (m (i + 1)) DLower
        sPositive tPositive product (positive i (by omega))
        (positive (i + 1) (by omega)) (windows i (by omega))
        (windows (i + 1) (by omega)) (modular i before) with
        ⟨ell, ellLess, divides, endpoint, guards, rawEndpoint⟩
      exact ⟨ell, fun _ => ⟨ellLess, divides, endpoint⟩⟩
    · exact ⟨0, fun impossible => False.elim (before impossible)⟩
  choose ell selectedEdge using selected
  have indices : ∀ i < h, ell i < D / Nat.gcd c D := by
    intro i before
    exact (selectedEdge i before).1
  have divisions : ∀ i < h, D ∣ s * m i + ell i * c := by
    intro i before
    exact (selectedEdge i before).2.1
  have endpoints : ∀ i < h, s * m (i + 1) = (s * m i + ell i * c) / D := by
    intro i before
    exact (selectedEdge i before).2.2.symm
  refine ⟨AdditivePathClock ell h, lt_of_lt_of_le hPositive
    (AdditivePathClockLower ell h), AdditivePathClockUpper c D h ell indices, ?_⟩
  have recovered := AdditivePathRawRecovery c D h (fun i => s * m i) ell
    (by omega : 0 < D) indices divisions endpoints
  simpa [closed] using recovered

/-- The unit-offset modular cycle at three is removed by the larger-offset window. -/
theorem AdditiveScalingGhostControl :
    Iterate (PositiveRawStep 1 5 6) 4 3 = 3 ∧
    Iterate (PositiveRawStep 1 10 6) 1 6 = 1 ∧
    AdditiveCycleWindow 10 6 5 = 2 := by
  decide

/-- Every legal closed first-division path factors into a modular path in the exact window. -/
theorem AdditiveClosedPathToModular (c D s t k h : ℕ) (ell x : ℕ → ℕ)
    (DLower : 2 ≤ D) (sPositive : 0 < s) (hPositive : 0 < h)
    (product : s * t = c) (sPower : s ∣ D ^ k)
    (positive : ∀ i ≤ h, 0 < x i)
    (indices : ∀ i < h, ell i < D / Nat.gcd c D)
    (path : ∀ i < h, D * x (i + 1) = x i + ell i * c) (closed : x h = x 0) :
    ∃ m : ℕ → ℕ,
      (∀ i ≤ h, x i = s * m i ∧ 0 < m i ∧ m i ≤ AdditiveCycleWindow c D t) ∧
      (∀ i < h, Nat.ModEq t (D * m (i + 1)) (m i)) ∧ m h = m 0 := by
  have DPositive : 0 < D := by omega
  have sOffset : s ∣ c := ⟨t, product.symm⟩
  have supported := AdditiveClosedPathSupported c D s k h ell x
    DLower hPositive sOffset sPower path closed
  have bounds : ∀ i < h, D * x (i + 1) ≤ x i + AdditiveDisplacement c D := by
    intro i before
    have indexBound : ell i ≤ D / Nat.gcd c D - 1 := by
      have leastBound := indices i before
      omega
    have scaled := Nat.mul_le_mul_right c indexBound
    rw [path i before]
    simpa [AdditiveDisplacement, Nat.mul_comm] using Nat.add_le_add_left scaled (x i)
  have endpoints : ∀ i < h, x (i + 1) = (x i + ell i * c) / D := by
    intro i before
    rw [← path i before]
    exact (Nat.mul_div_cancel_left (x (i + 1)) DPositive).symm
  have firstCore := AdditiveClosedPathCore c D h x DLower hPositive bounds closed
  have cores : ∀ i, i ≤ h → x i ≤ AdditiveCoreRadius c D := by
    intro i
    induction i with
    | zero => {
      intro _
      exact firstCore
    }
    | succ i ih => {
      intro within
      rw [endpoints i (by omega)]
      exact AdditiveCoreInvariant c D (x i) (ell i) DLower
        (indices i (by omega)) (ih (by omega))
    }
  have reconstructed : ∀ i ≤ h, x i = s * (x i / s) := by
    intro i within
    exact (Nat.mul_div_cancel' (supported i within)).symm
  refine ⟨fun i => x i / s, ?_, ?_, ?_⟩
  · intro i within
    have factorization := reconstructed i within
    have quotientPositive : 0 < x i / s :=
      Nat.div_pos (Nat.le_of_dvd (positive i within) (supported i within)) sPositive
    refine ⟨factorization, quotientPositive, ?_⟩
    apply (AdditiveScaledCoreIff c D s t (x i / s) DLower sPositive product).mp
    rw [← factorization]
    exact cores i within
  · intro i before
    apply AdditiveScaledEdgeCongruence c D s t (x i / s) (x (i + 1) / s)
      (ell i) sPositive product
    rw [← reconstructed (i + 1) (by omega), ← reconstructed i (by omega)]
    exact path i before
  · change x h / s = x 0 / s
    rw [closed]

/-- A positive raw predecessor of a state at most the offset must use division. -/
theorem AdditiveSmallEndpointDivision (c D u n : ℕ) (uPositive : 0 < u)
    (small : n ≤ c) (endpoint : PositiveRawStep 1 c D u = n) : D ∣ u := by
  by_contra affine
  simp [PositiveRawStep, affine] at endpoint
  omega

/-- A periodic positive orbit reaches the core; the affine-only alternative is impossible. -/
theorem AdditivePeriodicCore (c D n p : ℕ) (DLower : 2 ≤ D) (cPositive : 0 < c)
    (nPositive : 0 < n) (pPositive : 0 < p)
    (returned : Iterate (PositiveRawStep 1 c D) p n = n) :
    ∃ t, 0 < Iterate (PositiveRawStep 1 c D) t n ∧
      Iterate (PositiveRawStep 1 c D) t n ≤ AdditiveCoreRadius c D := by
  obtain ⟨t, reachedPositive, inCore | trap⟩ :=
    AdditiveFiniteReduction c D n DLower nPositive
  · exact ⟨t, reachedPositive, inCore⟩
  · have shiftedReturn :
        Iterate (PositiveRawStep 1 c D) p (Iterate (PositiveRawStep 1 c D) t n) =
          Iterate (PositiveRawStep 1 c D) t n := by
      calc
        Iterate (PositiveRawStep 1 c D) p (Iterate (PositiveRawStep 1 c D) t n) =
            Iterate (PositiveRawStep 1 c D) (t + p) n := (IterateAdd _ _ _ _).symm
        _ = Iterate (PositiveRawStep 1 c D) (p + t) n := by rw [Nat.add_comm t p]
        _ = Iterate (PositiveRawStep 1 c D) t (Iterate (PositiveRawStep 1 c D) p n) :=
          IterateAdd _ _ _ _
        _ = Iterate (PositiveRawStep 1 c D) t n := by rw [returned]
    have affineTail := AdditiveTrapIterate c D (Iterate (PositiveRawStep 1 c D) t n) p trap
    have incrementPositive : 0 < p * c := Nat.mul_pos pPositive cPositive
    rw [affineTail] at shiftedReturn
    omega

end GeneralizedCollatz

namespace GeneralizedCollatz

/-- Prepending one datum shifts the remaining finite path indices without changing their values. -/
def AdditivePrepend (first : ℕ) (tail : ℕ → ℕ) : ℕ → ℕ
  | 0 => first
  | i + 1 => tail i

/-- Prepending a block adds its exact raw length to the tail clock. -/
theorem AdditivePrependClock (first : ℕ) (ell : ℕ → ℕ) (h : ℕ) :
    AdditivePathClock (AdditivePrepend first ell) (h + 1) =
      first + 1 + AdditivePathClock ell h := by
  induction h with
  | zero => {
    simp [AdditivePathClock, AdditivePrepend]
  }
  | succ h ih => {
    change AdditivePathClock (AdditivePrepend first ell) (h + 1) + (ell h + 1) =
      first + 1 + (AdditivePathClock ell h + (ell h + 1))
    rw [ih]
    omega
  }

/-- A positive raw segment ending in the core splits into legal blocks with its original clock. -/
theorem AdditiveEndingCorePath (c D r : ℕ) (DLower : 2 ≤ D) (cPositive : 0 < c)
    (rPositive : 0 < r) (rCore : r ≤ AdditiveCoreRadius c D) :
    ∀ p n : ℕ, 0 < p → 0 < n → Iterate (PositiveRawStep 1 c D) p n = r →
      ∃ h : ℕ, ∃ ell x : ℕ → ℕ,
        0 < h ∧ h ≤ p ∧ x 0 = n ∧ x h = r ∧
        (∀ i ≤ h, 0 < x i) ∧ (∀ i < h, ell i < D / Nat.gcd c D) ∧
        (∀ i < h, D * x (i + 1) = x i + ell i * c) ∧
        AdditivePathClock ell h = p := by
  have DPositive : 0 < D := by omega
  have rSmall : r ≤ c := le_trans rCore (AdditiveCoreRadiusLe c D DLower)
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih => {
    intro n pPositive nPositive reached
    have offsetLower : c ≤ p * c := by
      have multiplied : c * 1 ≤ c * p :=
        (mul_le_mul_iff_right₀ cPositive).mpr (by omega : 1 ≤ p)
      simpa [Nat.mul_comm] using multiplied
    have accessible : Nat.gcd c D ∣ n := by
      by_contra trap
      have affine := AdditiveTrapIterate c D n p trap
      rw [affine] at reached
      omega
    obtain ⟨ell, ellLess, divides⟩ := AdditiveAccessExists c D n DPositive accessible
    have ellBefore : ell < p := by
      by_contra outside
      have prefixEndpoint := AdditiveFirstDivisionPrefix c D n ell p DPositive
        ellLess divides (by omega)
      rw [prefixEndpoint] at reached
      omega
    let m := (n + ell * c) / D
    have mPositive : 0 < m :=
      AdditiveFirstDivisionPositive c D n ell DPositive nPositive divides
    have firstEquation : D * m = n + ell * c := Nat.mul_div_cancel' divides
    let w := ell + 1
    let remaining := p - w
    have wPositive : 0 < w := by dsimp [w]; omega
    have wUpper : w ≤ p := by dsimp [w]; omega
    have total : w + remaining = p := by dsimp [remaining]; omega
    have remainingLess : remaining < p := by omega
    have tailEndpoint : Iterate (PositiveRawStep 1 c D) remaining m = r := by
      have longer : Iterate (PositiveRawStep 1 c D) (w + remaining) n = r := by
        rw [total]
        exact reached
      change Iterate (PositiveRawStep 1 c D) (ell + 1 + remaining) n = r at longer
      rw [IterateAdd, AdditiveFirstDivisionRaw c D n ell DPositive ellLess divides] at longer
      exact longer
    by_cases empty : remaining = 0
    · have mEquals : m = r := by simpa [empty, Iterate] using tailEndpoint
      refine ⟨1, fun _ => ell, AdditivePrepend n (fun _ => r), by omega,
        by omega, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · intro i within
        cases i with
        | zero => {
          exact nPositive
        }
        | succ i => {
          exact rPositive
        }
      · intro i before
        exact ellLess
      · intro i before
        have equal : i = 0 := by omega
        subst i
        simpa [AdditivePrepend, mEquals] using firstEquation
      · have firstLength : ell + 1 = p := by dsimp [w] at total; omega
        simpa [AdditivePathClock] using firstLength
    · have remainingPositive : 0 < remaining := by omega
      obtain ⟨h, eta, y, hPositive, hUpper, first, last, vertices, indices, edges, clock⟩ :=
        ih remaining remainingLess m remainingPositive mPositive tailEndpoint
      refine ⟨h + 1, AdditivePrepend ell eta, AdditivePrepend n y,
        by omega, by omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [AdditivePrepend] using last
      · intro i within
        cases i with
        | zero => {
          exact nPositive
        }
        | succ i => {
          exact vertices i (by omega)
        }
      · intro i before
        cases i with
        | zero => {
          exact ellLess
        }
        | succ i => {
          exact indices i (by omega)
        }
      · intro i before
        cases i with
        | zero => {
          simpa [AdditivePrepend, first] using firstEquation
        }
        | succ i => {
          exact edges i (by omega)
        }
      · rw [AdditivePrependClock, clock]
        exact total
  }

end GeneralizedCollatz

namespace GeneralizedCollatz

/-- Repeating a known return produces a return at every nonnegative multiple of its clock. -/
theorem IterateReturnMultiple {α : Type*} (f : α → α) (n : α) (p k : ℕ)
    (returned : Iterate f p n = n) : Iterate f (p * k) n = n := by
  induction k with
  | zero => {
    simp [Iterate]
  }
  | succ k ih => {
    rw [Nat.mul_succ, IterateAdd, ih, returned]
  }

/-- Powers of a single map commute even when the map itself is not invertible. -/
theorem IteratePowersCommute {α : Type*} (f : α → α) (a b : ℕ) (n : α) :
    Iterate f a (Iterate f b n) = Iterate f b (Iterate f a n) := by
  calc
    _ = Iterate f (b + a) n := (IterateAdd f b a n).symm
    _ = Iterate f (a + b) n := by rw [Nat.add_comm b a]
    _ = _ := IterateAdd f a b n

/-- A positive periodic orbit has identical return clocks at every forward phase. -/
theorem IterateReturnAlongCycle {α : Type*} (f : α → α) (n : α) (p u v : ℕ)
    (pPositive : 0 < p) (returned : Iterate f p n = n) :
    Iterate f v (Iterate f u n) = Iterate f u n ↔ Iterate f v n = n := by
  constructor
  · intro phaseReturn
    have productBound : u + 1 ≤ p * (u + 1) := by
      have multiplied := Nat.mul_le_mul_right (u + 1) (Nat.succ_le_of_lt pPositive)
      simpa using multiplied
    have bound : u ≤ p * (u + 1) := le_trans (Nat.le_succ u) productBound
    let a := p * (u + 1) - u
    have total : u + a = p * (u + 1) := by dsimp [a]; omega
    -- A multiple of the known period supplies an inverse along this orbit only.
    have recovered : Iterate f a (Iterate f u n) = n := by
      calc
        _ = Iterate f (u + a) n := (IterateAdd f u a n).symm
        _ = Iterate f (p * (u + 1)) n := by rw [total]
        _ = n := IterateReturnMultiple f n p (u + 1) returned
    calc
      Iterate f v n = Iterate f v (Iterate f a (Iterate f u n)) := by rw [recovered]
      _ = Iterate f a (Iterate f v (Iterate f u n)) := IteratePowersCommute _ _ _ _
      _ = Iterate f a (Iterate f u n) := by rw [phaseReturn]
      _ = n := recovered
  · intro initialReturn
    calc
      _ = Iterate f u (Iterate f v n) := IteratePowersCommute _ _ _ _
      _ = Iterate f u n := by rw [initialReturn]

end GeneralizedCollatz

namespace GeneralizedCollatz

/-- Extending a first-division path cannot decrease its raw clock. -/
theorem AdditivePathClockMonotone (ell : ℕ → ℕ) (i j : ℕ) (within : i ≤ j) :
    AdditivePathClock ell i ≤ AdditivePathClock ell j := by
  induction j with
  | zero => {
    have equal : i = 0 := by omega
    simp [equal]
  }
  | succ j ih => {
    by_cases earlier : i ≤ j
    · have previous := ih earlier
      simp only [AdditivePathClock]
      omega
    · have equal : i = j + 1 := by omega
      rw [equal]
  }

/-- Uniqueness of the least division index fixes both states and clocks of a common prefix. -/
theorem AdditivePathPrefixUnique (c D h k : ℕ) (ell eta x y : ℕ → ℕ)
    (DPositive : 0 < D)
    (xIndices : ∀ i < h, ell i < D / Nat.gcd c D)
    (yIndices : ∀ i < k, eta i < D / Nat.gcd c D)
    (xEdges : ∀ i < h, D * x (i + 1) = x i + ell i * c)
    (yEdges : ∀ i < k, D * y (i + 1) = y i + eta i * c) (first : y 0 = x 0) :
    ∀ i ≤ h, i ≤ k → y i = x i ∧ AdditivePathClock eta i = AdditivePathClock ell i := by
  intro i
  induction i with
  | zero => {
    intro _ _
    exact ⟨first, by simp [AdditivePathClock]⟩
  }
  | succ i ih => {
    intro xWithin yWithin
    obtain ⟨previous, previousClock⟩ := ih (by omega) (by omega)
    have xDivides : D ∣ x i + ell i * c := ⟨x (i + 1), (xEdges i (by omega)).symm⟩
    have yDivides : D ∣ x i + eta i * c := by
      rw [← previous]
      exact ⟨y (i + 1), (yEdges i (by omega)).symm⟩
    have indexEquals := AdditiveAccessUnique c D (x i) (eta i) (ell i) DPositive
      (yIndices i (by omega)) (xIndices i (by omega)) yDivides xDivides
    have scaled : D * y (i + 1) = D * x (i + 1) := by
      calc
        _ = y i + eta i * c := yEdges i (by omega)
        _ = x i + ell i * c := by rw [previous, indexEquals]
        _ = _ := (xEdges i (by omega)).symm
    refine ⟨mul_left_cancel₀ (by omega : D ≠ 0) scaled, ?_⟩
    simp only [AdditivePathClock]
    rw [previousClock, indexEquals]
  }

/-- A least positive first-division return expands to the least positive raw return. -/
theorem AdditivePrimitiveRawReturn (c D h : ℕ) (ell x : ℕ → ℕ)
    (DLower : 2 ≤ D) (cPositive : 0 < c) (hPositive : 0 < h)
    (firstPositive : 0 < x 0) (firstCore : x 0 ≤ AdditiveCoreRadius c D)
    (indices : ∀ i < h, ell i < D / Nat.gcd c D)
    (edges : ∀ i < h, D * x (i + 1) = x i + ell i * c) (closed : x h = x 0)
    (noEarlier : ∀ i, 0 < i → i < h → x i ≠ x 0) :
    0 < AdditivePathClock ell h ∧
      Iterate (PositiveRawStep 1 c D) (AdditivePathClock ell h) (x 0) = x 0 ∧
      ∀ p, 0 < p → p < AdditivePathClock ell h →
        Iterate (PositiveRawStep 1 c D) p (x 0) ≠ x 0 := by
  have DPositive : 0 < D := by omega
  have divisions : ∀ i < h, D ∣ x i + ell i * c := by
    intro i before
    exact ⟨x (i + 1), (edges i before).symm⟩
  have endpoints : ∀ i < h, x (i + 1) = (x i + ell i * c) / D := by
    intro i before
    rw [← edges i before]
    exact (Nat.mul_div_cancel_left _ DPositive).symm
  have raw := AdditivePathRawRecovery c D h x ell DPositive indices divisions endpoints
  refine ⟨lt_of_lt_of_le hPositive (AdditivePathClockLower ell h),
    by simpa [closed] using raw, ?_⟩
  intro p pPositive pLess shorterReturn
  obtain ⟨k, eta, y, kPositive, kUpper, first, last, vertices, yIndices, yEdges, yClock⟩ :=
    AdditiveEndingCorePath c D (x 0) DLower cPositive firstPositive firstCore
      p (x 0) pPositive firstPositive shorterReturn
  have comparison := AdditivePathPrefixUnique c D h k ell eta x y DPositive
    indices yIndices edges yEdges first
  by_cases kLess : k < h
  · have endEquals := (comparison k (by omega) (by omega)).1
    exact noEarlier k kPositive kLess (endEquals.symm.trans last)
  · have hWithin : h ≤ k := by omega
    have clockEquals := (comparison h (by omega) hWithin).2
    have clockBound := AdditivePathClockMonotone eta h k hWithin
    rw [clockEquals, yClock] at clockBound
    omega

end GeneralizedCollatz

namespace GeneralizedCollatz

/-- Counting each selected block once separates its divisions from its additions. -/
theorem AdditiveClockSum (ell : ℕ → ℕ) (h : ℕ) :
    AdditivePathClock ell h = h + ∑ i ∈ Finset.range h, ell i := by
  induction h with
  | zero => {
    simp [AdditivePathClock]
  }
  | succ h ih => {
    rw [AdditivePathClock, ih, Finset.sum_range_succ]
    omega
  }

/-- Summing the exact division equations retains their joint addition budget. -/
theorem AdditivePathSumEquation (c D h : ℕ) (ell x : ℕ → ℕ)
    (path : ∀ i < h, D * x (i + 1) = x i + ell i * c) :
    D * (∑ i ∈ Finset.range h, x (i + 1)) =
      (∑ i ∈ Finset.range h, x i) + c * (∑ i ∈ Finset.range h, ell i) := by
  induction h with
  | zero => {
    simp
  }
  | succ h ih => {
    have previous := ih (fun i before => path i (by omega))
    have edge := path h (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Nat.mul_add, previous, edge]
    ring
  }

/-- Shifting the vertex sum exposes only the two path endpoints. -/
theorem AdditiveVertexSumShift (x : ℕ → ℕ) (h : ℕ) :
    (∑ i ∈ Finset.range h, x (i + 1)) + x 0 =
      (∑ i ∈ Finset.range h, x i) + x h := by
  induction h with
  | zero => {
    simp
  }
  | succ h ih => {
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    omega
  }

/-- A closed path has an exact integral raw-clock formula, without termwise rounding. -/
theorem AdditiveClosedClockFormula (c D h : ℕ) (ell x : ℕ → ℕ)
    (cPositive : 0 < c) (DLower : 2 ≤ D)
    (path : ∀ i < h, D * x (i + 1) = x i + ell i * c) (closed : x h = x 0) :
    AdditivePathClock ell h = h +
      ((D - 1) * (∑ i ∈ Finset.range h, x i)) / c := by
  have shifted := AdditiveVertexSumShift x h
  rw [closed] at shifted
  have sumsEqual : (∑ i ∈ Finset.range h, x (i + 1)) =
      (∑ i ∈ Finset.range h, x i) := by omega
  have summed := AdditivePathSumEquation c D h ell x path
  rw [sumsEqual] at summed
  have decrement : D - 1 + 1 = D := by omega
  have expanded : (D - 1) * (∑ i ∈ Finset.range h, x i) +
      (∑ i ∈ Finset.range h, x i) = D * (∑ i ∈ Finset.range h, x i) := by
    calc
      _ = (D - 1 + 1) * (∑ i ∈ Finset.range h, x i) := by ring
      _ = _ := by rw [decrement]
  have cancelled : (∑ i ∈ Finset.range h, x i) +
      c * (∑ i ∈ Finset.range h, ell i) = (∑ i ∈ Finset.range h, x i) +
      (D - 1) * (∑ i ∈ Finset.range h, x i) := by
    rw [← summed, ← expanded]
    exact Nat.add_comm _ _
  have scaled : c * (∑ i ∈ Finset.range h, ell i) =
      (D - 1) * (∑ i ∈ Finset.range h, x i) := Nat.add_left_cancel cancelled
  have quotient : ((D - 1) * (∑ i ∈ Finset.range h, x i)) / c =
      ∑ i ∈ Finset.range h, ell i := by
    rw [← scaled]
    exact Nat.mul_div_cancel_left _ cPositive
  rw [AdditiveClockSum, quotient]

end GeneralizedCollatz

namespace GeneralizedCollatz

/-- Every raw return supplies a modular closed path on the same cycle with the same raw clock. -/
theorem AdditiveRawPeriodicToModular (c D s t k n p : ℕ) (DLower : 2 ≤ D)
    (cPositive : 0 < c) (sPositive : 0 < s) (product : s * t = c) (sPower : s ∣ D ^ k)
    (nPositive : 0 < n) (pPositive : 0 < p)
    (returned : Iterate (PositiveRawStep 1 c D) p n = n) :
    ∃ u h : ℕ, ∃ m : ℕ → ℕ,
      0 < h ∧ h ≤ p ∧ Iterate (PositiveRawStep 1 c D) u n = s * m 0 ∧
      (∀ i ≤ h, 0 < m i ∧ m i ≤ AdditiveCycleWindow c D t) ∧
      (∀ i < h, Nat.ModEq t (D * m (i + 1)) (m i)) ∧ m h = m 0 ∧
      ∃ ell : ℕ → ℕ,
        (∀ i < h, ell i < D / Nat.gcd c D) ∧
        (∀ i < h, D * (s * m (i + 1)) = s * m i + ell i * c) ∧
        AdditivePathClock ell h = p := by
  obtain ⟨u, rPositive, rCore⟩ :=
    AdditivePeriodicCore c D n p DLower cPositive nPositive pPositive returned
  let r := Iterate (PositiveRawStep 1 c D) u n
  have rReturned : Iterate (PositiveRawStep 1 c D) p r = r := by
    calc
      Iterate (PositiveRawStep 1 c D) p r =
          Iterate (PositiveRawStep 1 c D) (u + p) n := (IterateAdd _ _ _ _).symm
      _ = Iterate (PositiveRawStep 1 c D) (p + u) n := by rw [Nat.add_comm u p]
      _ = Iterate (PositiveRawStep 1 c D) u (Iterate (PositiveRawStep 1 c D) p n) :=
        IterateAdd _ _ _ _
      _ = r := by rw [returned]
  obtain ⟨h, ell, x, hPositive, hUpper, first, last, vertices, indices, edges, clock⟩ :=
    AdditiveEndingCorePath c D r DLower cPositive rPositive rCore
      p r pPositive rPositive rReturned
  have closedPath : x h = x 0 := by rw [last, first]
  obtain ⟨m, factorization, modular, closed⟩ := AdditiveClosedPathToModular
    c D s t k h ell x DLower sPositive hPositive product sPower
    vertices indices edges closedPath
  refine ⟨u, h, m, hPositive, hUpper, ?_, ?_, modular, closed, ell, indices, ?_, clock⟩
  · calc
      Iterate (PositiveRawStep 1 c D) u n = r := rfl
      _ = x 0 := first.symm
      _ = s * m 0 := (factorization 0 (by omega)).1
  · intro i within
    exact (factorization i within).2
  · intro i before
    rw [← (factorization (i + 1) (by omega)).1, ← (factorization i (by omega)).1]
    exact edges i before

/-- A least raw return yields a least modular return, with no loss of the original period. -/
theorem AdditiveRawPrimitiveToModular (c D s t k n p : ℕ) (DLower : 2 ≤ D)
    (cPositive : 0 < c) (sPositive : 0 < s) (product : s * t = c) (sPower : s ∣ D ^ k)
    (nPositive : 0 < n) (pPositive : 0 < p)
    (returned : Iterate (PositiveRawStep 1 c D) p n = n)
    (noEarlierRaw : ∀ v, 0 < v → v < p → Iterate (PositiveRawStep 1 c D) v n ≠ n) :
    ∃ u h : ℕ, ∃ m : ℕ → ℕ,
      0 < h ∧ h ≤ p ∧ Iterate (PositiveRawStep 1 c D) u n = s * m 0 ∧
      (∀ i ≤ h, 0 < m i ∧ m i ≤ AdditiveCycleWindow c D t) ∧
      (∀ i < h, Nat.ModEq t (D * m (i + 1)) (m i)) ∧ m h = m 0 ∧
      (∀ i, 0 < i → i < h → m i ≠ m 0) ∧
      ∃ ell : ℕ → ℕ,
        (∀ i < h, ell i < D / Nat.gcd c D) ∧
        (∀ i < h, D * (s * m (i + 1)) = s * m i + ell i * c) ∧
        AdditivePathClock ell h = p := by
  obtain ⟨u, h, m, hPositive, hUpper, phase, windows, modular, closed,
    ell, indices, edges, clock⟩ := AdditiveRawPeriodicToModular
      c D s t k n p DLower cPositive sPositive product sPower nPositive pPositive returned
  refine ⟨u, h, m, hPositive, hUpper, phase, windows, modular, closed, ?_,
    ell, indices, edges, clock⟩
  intro i iPositive iLess repeated
  have DPositive : 0 < D := by omega
  have divisions : ∀ j < i, D ∣ s * m j + ell j * c := by
    intro j before
    exact ⟨s * m (j + 1), (edges j (by omega)).symm⟩
  have endpoints : ∀ j < i, s * m (j + 1) = (s * m j + ell j * c) / D := by
    intro j before
    rw [← edges j (by omega)]
    exact (Nat.mul_div_cancel_left _ DPositive).symm
  have raw := AdditivePathRawRecovery c D i (fun j => s * m j) ell DPositive
    (fun j before => indices j (by omega)) divisions endpoints
  have phaseReturned : Iterate (PositiveRawStep 1 c D) (AdditivePathClock ell i)
      (Iterate (PositiveRawStep 1 c D) u n) = Iterate (PositiveRawStep 1 c D) u n := by
    rw [phase]
    simpa [repeated] using raw
  have atInitial := (IterateReturnAlongCycle (PositiveRawStep 1 c D) n p u
    (AdditivePathClock ell i) pPositive returned).mp phaseReturned
  have timePositive : 0 < AdditivePathClock ell i :=
    lt_of_lt_of_le iPositive (AdditivePathClockLower ell i)
  have increment : AdditivePathClock ell i < AdditivePathClock ell (i + 1) := by
    rw [AdditivePathClock]
    omega
  have prefixBound := AdditivePathClockMonotone ell (i + 1) h (by omega)
  have timeLess : AdditivePathClock ell i < p := by
    rw [← clock]
    exact lt_of_lt_of_le increment prefixBound
  exact noEarlierRaw (AdditivePathClock ell i) timePositive timeLess atInitial

end GeneralizedCollatz

namespace GeneralizedCollatz

/-- Inside the window, the Euclidean edge index is the actual first-division index. -/
theorem AdditiveModularEdgeIndex (c D s t m next : ℕ) (DLower : 2 ≤ D)
    (sPositive : 0 < s) (tPositive : 0 < t) (product : s * t = c)
    (mPositive : 0 < m) (nextPositive : 0 < next)
    (mWindow : m ≤ AdditiveCycleWindow c D t)
    (nextWindow : next ≤ AdditiveCycleWindow c D t)
    (congruence : Nat.ModEq t (D * next) m) :
    let ell := (D * next - m) / t
    ell < D / Nat.gcd c D ∧ D * (s * next) = s * m + ell * c := by
  obtain ⟨ell, ellLess, divides, endpoint, guards, raw⟩ :=
    AdditiveModularEdgeLegal c D s t m next DLower sPositive tPositive product
      mPositive nextPositive mWindow nextWindow congruence
  have scaled : D * (s * next) = s * m + ell * c := by
    rw [← endpoint]
    exact Nat.mul_div_cancel' divides
  have cancelled : D * next = m + ell * t := by
    apply mul_left_cancel₀ (by omega : s ≠ 0)
    calc
      s * (D * next) = D * (s * next) := by ring
      _ = s * m + ell * c := scaled
      _ = s * (m + ell * t) := by rw [← product]; ring
  have difference : D * next - m = t * ell := by
    rw [cancelled, Nat.add_sub_cancel_left, Nat.mul_comm]
  have index : (D * next - m) / t = ell := by
    rw [difference]
    exact Nat.mul_div_cancel_left _ tPositive
  change (D * next - m) / t < D / Nat.gcd c D ∧
    D * (s * next) = s * m + ((D * next - m) / t) * c
  rw [index]
  exact ⟨ellLess, scaled⟩

/-- A modular path admits computable indices, with no independent per-edge choices to reconcile. -/
theorem AdditiveModularPathEquations (c D s t h : ℕ) (m : ℕ → ℕ)
    (DLower : 2 ≤ D) (sPositive : 0 < s) (tPositive : 0 < t) (product : s * t = c)
    (windows : ∀ i ≤ h, 0 < m i ∧ m i ≤ AdditiveCycleWindow c D t)
    (modular : ∀ i < h, Nat.ModEq t (D * m (i + 1)) (m i)) :
    let ell := fun i => (D * m (i + 1) - m i) / t
    (∀ i < h, ell i < D / Nat.gcd c D) ∧
      (∀ i < h, D * (s * m (i + 1)) = s * m i + ell i * c) := by
  constructor
  · intro i before
    exact (AdditiveModularEdgeIndex c D s t (m i) (m (i + 1)) DLower
      sPositive tPositive product (windows i (by omega)).1
      (windows (i + 1) (by omega)).1 (windows i (by omega)).2
      (windows (i + 1) (by omega)).2 (modular i before)).1
  · intro i before
    exact (AdditiveModularEdgeIndex c D s t (m i) (m (i + 1)) DLower
      sPositive tPositive product (windows i (by omega)).1
      (windows (i + 1) (by omega)).1 (windows i (by omega)).2
      (windows (i + 1) (by omega)).2 (modular i before)).2

/-- Scaling cancels from the grouped raw-clock formula, leaving the coprime-factor denominator. -/
theorem AdditiveScaledClosedClock (c D s t h : ℕ) (ell m : ℕ → ℕ)
    (DLower : 2 ≤ D) (sPositive : 0 < s) (tPositive : 0 < t) (product : s * t = c)
    (edges : ∀ i < h, D * (s * m (i + 1)) = s * m i + ell i * c)
    (closed : m h = m 0) :
    AdditivePathClock ell h = h + ((D - 1) * (∑ i ∈ Finset.range h, m i)) / t := by
  have cPositive : 0 < c := by rw [← product]; exact Nat.mul_pos sPositive tPositive
  have clock := AdditiveClosedClockFormula c D h ell (fun i => s * m i)
    cPositive DLower edges (by rw [closed])
  have grouped : (∑ i ∈ Finset.range h, s * m i) =
      s * (∑ i ∈ Finset.range h, m i) := by rw [Finset.mul_sum]
  have factored : (D - 1) * (s * (∑ i ∈ Finset.range h, m i)) =
      s * ((D - 1) * (∑ i ∈ Finset.range h, m i)) := by ring
  rw [grouped, factored, ← product] at clock
  simpa only [Nat.mul_div_mul_left _ _ sPositive] using clock

/-- A least modular return reconstructs a least raw return and its exact grouped period. -/
theorem AdditiveModularPrimitiveRaw (c D s t h : ℕ) (m : ℕ → ℕ)
    (DLower : 2 ≤ D) (sPositive : 0 < s) (tPositive : 0 < t) (hPositive : 0 < h)
    (product : s * t = c)
    (windows : ∀ i ≤ h, 0 < m i ∧ m i ≤ AdditiveCycleWindow c D t)
    (modular : ∀ i < h, Nat.ModEq t (D * m (i + 1)) (m i))
    (closed : m h = m 0) (noEarlier : ∀ i, 0 < i → i < h → m i ≠ m 0) :
    let p := h + ((D - 1) * (∑ i ∈ Finset.range h, m i)) / t
    0 < p ∧ Iterate (PositiveRawStep 1 c D) p (s * m 0) = s * m 0 ∧
      ∀ v, 0 < v → v < p → Iterate (PositiveRawStep 1 c D) v (s * m 0) ≠ s * m 0 := by
  let ell := fun i => (D * m (i + 1) - m i) / t
  obtain ⟨indices, edges⟩ := AdditiveModularPathEquations
    c D s t h m DLower sPositive tPositive product windows modular
  have cPositive : 0 < c := by rw [← product]; exact Nat.mul_pos sPositive tPositive
  have firstPositive := Nat.mul_pos sPositive (windows 0 (by omega)).1
  have firstCore := (AdditiveScaledCoreIff c D s t (m 0) DLower sPositive product).mpr
    (windows 0 (by omega)).2
  have noEarlierScaled : ∀ i, 0 < i → i < h → s * m i ≠ s * m 0 := by
    intro i iPositive iLess equal
    exact noEarlier i iPositive iLess (mul_left_cancel₀ (by omega : s ≠ 0) equal)
  have least := AdditivePrimitiveRawReturn c D h ell (fun i => s * m i)
    DLower cPositive hPositive firstPositive firstCore indices edges
    (by rw [closed]) noEarlierScaled
  have clock := AdditiveScaledClosedClock c D s t h ell m
    DLower sPositive tPositive product edges closed
  rw [clock] at least
  exact least

end GeneralizedCollatz

namespace GeneralizedCollatz

/-- Inverse unit multiplication realizes the modular successor as a permutation. -/
def AdditiveResiduePermutation (D t : ℕ) (coprime : Nat.Coprime D t) : ZMod t ≃ ZMod t :=
  let u : (ZMod t)ˣ := ZMod.unitOfCoprime D coprime
  {
    toFun := fun z => (↑(u⁻¹) : ZMod t) * z
    invFun := fun z => (↑u : ZMod t) * z
    left_inv := by
      intro z
      simp only [← mul_assoc, ← Units.val_mul]
      simp
    right_inv := by
      intro z
      simp only [← mul_assoc, ← Units.val_mul]
      simp
  }

/-- The permutation edge is precisely the guarded classifier's residue equation. -/
theorem AdditiveResiduePermutationEdge (D t m next : ℕ) (coprime : Nat.Coprime D t) :
    AdditiveResiduePermutation D t coprime (m : ZMod t) = (next : ZMod t) ↔
      Nat.ModEq t (D * next) m := by
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  change (m : ZMod t) = (D : ZMod t) * (next : ZMod t) ↔ Nat.ModEq t (D * next) m
  rw [← Nat.cast_mul]
  exact eq_comm.trans (ZMod.natCast_eq_natCast_iff (D * next) m t)

/-- Positive representatives up to the modulus retain the zero class at the upper endpoint. -/
theorem AdditivePositiveResidueUnique (t m n : ℕ) (_tPositive : 0 < t)
    (mPositive : 0 < m) (nPositive : 0 < n) (mUpper : m ≤ t) (nUpper : n ≤ t)
    (congruence : Nat.ModEq t m n) : m = n := by
  change m % t = n % t at congruence
  by_cases mBoundary : m = t
  · rw [mBoundary, Nat.mod_self] at congruence
    by_cases nBoundary : n = t
    · omega
    · have nLess : n < t := by omega
      rw [Nat.mod_eq_of_lt nLess] at congruence
      omega
  · have mLess : m < t := by omega
    rw [Nat.mod_eq_of_lt mLess] at congruence
    by_cases nBoundary : n = t
    · rw [nBoundary, Nat.mod_self] at congruence
      omega
    · have nLess : n < t := by omega
      rw [Nat.mod_eq_of_lt nLess] at congruence
      exact congruence

/-- Cancelling the marked residue yields the exact effective modulus in both directions. -/
theorem AdditiveEffectiveModulus (t m a b : ℕ) (tPositive : 0 < t) :
    Nat.ModEq t (a * m) (b * m) ↔ Nat.ModEq (t / Nat.gcd m t) a b := by
  constructor
  · intro congruence
    simpa [Nat.gcd_comm] using congruence.cancel_right_div_gcd tPositive
  · intro reduced
    let g := Nat.gcd m t
    have mFactor : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m t)
    have tFactor : g * (t / g) = t := Nat.mul_div_cancel' (Nat.gcd_dvd_right m t)
    have scaled := reduced.mul_left' g
    change Nat.ModEq (g * (t / g)) (g * a) (g * b) at scaled
    rw [tFactor] at scaled
    have lifted := scaled.mul_right (m / g)
    have factored (v : ℕ) : g * v * (m / g) = v * m := by
      calc
        _ = v * (g * (m / g)) := by ring
        _ = _ := by rw [mFactor]
    rw [factored a, factored b] at lifted
    exact lifted

/-- Successive modular edges retain their exact power relation to the initial phase. -/
theorem AdditiveModularPowerTransport (D t h : ℕ) (m : ℕ → ℕ)
    (modular : ∀ i < h, Nat.ModEq t (D * m (i + 1)) (m i)) :
    ∀ i ≤ h, Nat.ModEq t (D ^ i * m i) (m 0) := by
  intro i
  induction i with
  | zero => {
    intro _
    simpa only [Nat.pow_zero, Nat.one_mul] using
      (show Nat.ModEq t (m 0) (m 0) from rfl)
  }
  | succ i ih => {
    intro within
    have multiplied := (modular i (by omega)).mul_left (D ^ i)
    have previous := ih (by omega)
    simpa [Nat.pow_succ, Nat.mul_assoc] using multiplied.trans previous
  }

/-- A least modular return has the usual multiplicative order at its effective modulus. -/
theorem AdditivePrimitiveOrder (D t h : ℕ) (m : ℕ → ℕ)
    (tPositive : 0 < t) (coprime : Nat.Coprime D t) (hPositive : 0 < h)
    (representatives : ∀ i ≤ h, 0 < m i ∧ m i ≤ t)
    (modular : ∀ i < h, Nat.ModEq t (D * m (i + 1)) (m i))
    (closed : m h = m 0) (noEarlier : ∀ i, 0 < i → i < h → m i ≠ m 0) :
    orderOf (ZMod.unitOfCoprime D (coprime.coprime_dvd_right
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right (m 0) t)))) = h := by
  let modulus := t / Nat.gcd (m 0) t
  have reducedCoprime : Nat.Coprime D modulus := coprime.coprime_dvd_right
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right (m 0) t))
  let u : (ZMod modulus)ˣ := ZMod.unitOfCoprime D reducedCoprime
  have powerCriterion (i : ℕ) : u ^ i = 1 ↔ Nat.ModEq modulus (D ^ i) 1 := by
    constructor
    · intro equal
      have casted := congrArg (fun v : (ZMod modulus)ˣ => (v : ZMod modulus)) equal
      apply (ZMod.natCast_eq_natCast_iff (D ^ i) 1 modulus).mp
      simpa [u] using casted
    · intro congruence
      apply Units.ext
      have casted := (ZMod.natCast_eq_natCast_iff (D ^ i) 1 modulus).mpr congruence
      simpa [u] using casted
  have phaseCriterion (i : ℕ) (within : i ≤ h) :
      m i = m 0 ↔ Nat.ModEq modulus (D ^ i) 1 := by
    have transported := AdditiveModularPowerTransport D t h m modular i within
    constructor
    · intro equal
      rw [equal] at transported
      exact (AdditiveEffectiveModulus t (m 0) (D ^ i) 1 tPositive).mp
        (by simpa using transported)
    · intro reduced
      have atInitial := (AdditiveEffectiveModulus t (m 0) (D ^ i) 1 tPositive).mpr reduced
      have products : Nat.ModEq t (D ^ i * m i) (D ^ i * m 0) :=
        transported.trans (by simpa using atInitial.symm)
      have phases := products.cancel_left_of_coprime (coprime.pow_left i).symm
      exact AdditivePositiveResidueUnique t (m i) (m 0) tPositive
        (representatives i within).1 (representatives 0 (by omega)).1
        (representatives i within).2 (representatives 0 (by omega)).2 phases
  change orderOf u = h
  apply (orderOf_eq_iff hPositive).mpr
  constructor
  · exact (powerCriterion h).mpr ((phaseCriterion h (by omega)).mp closed)
  · intro i iLess iPositive equal
    exact noEarlier i iPositive iLess
      ((phaseCriterion i (by omega)).mpr ((powerCriterion i).mp equal))

/-- Every primitive modular cycle has length at most its effective modulus. -/
theorem AdditivePrimitiveLengthBoundModulus (D t h : ℕ) (m : ℕ → ℕ)
    (tPositive : 0 < t) (coprime : Nat.Coprime D t) (hPositive : 0 < h)
    (representatives : ∀ i ≤ h, 0 < m i ∧ m i ≤ t)
    (modular : ∀ i < h, Nat.ModEq t (D * m (i + 1)) (m i))
    (closed : m h = m 0) (noEarlier : ∀ i, 0 < i → i < h → m i ≠ m 0) :
    h ≤ t / Nat.gcd (m 0) t := by
  classical
  let modulus := t / Nat.gcd (m 0) t
  have gcdPositive := Nat.gcd_pos_of_pos_right (m 0) tPositive
  have gcdUpper := Nat.le_of_dvd tPositive (Nat.gcd_dvd_right (m 0) t)
  have modulusPositive : 0 < modulus := Nat.div_pos gcdUpper gcdPositive
  letI : NeZero modulus := ⟨by omega⟩
  let u : (ZMod modulus)ˣ := ZMod.unitOfCoprime D
    (coprime.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right (m 0) t)))
  have exactOrder : orderOf u = h := AdditivePrimitiveOrder
    D t h m tPositive coprime hPositive representatives modular closed noEarlier
  have unitCard : Fintype.card ((ZMod modulus)ˣ) ≤ Fintype.card (ZMod modulus) :=
    Fintype.card_le_of_injective (fun v : (ZMod modulus)ˣ => (v : ZMod modulus))
      (fun a b equal => Units.ext equal)
  have orderBound : orderOf u ≤ modulus := by
    have bound := le_trans (orderOf_le_card_univ (x := u)) unitCard
    simpa only [ZMod.card] using bound
  rw [exactOrder] at orderBound
  exact orderBound

/-- Every primitive modular cycle fits within the finite residue catalogue. -/
theorem AdditivePrimitiveLengthBound (D t h : ℕ) (m : ℕ → ℕ)
    (tPositive : 0 < t) (coprime : Nat.Coprime D t) (hPositive : 0 < h)
    (representatives : ∀ i ≤ h, 0 < m i ∧ m i ≤ t)
    (modular : ∀ i < h, Nat.ModEq t (D * m (i + 1)) (m i))
    (closed : m h = m 0) (noEarlier : ∀ i, 0 < i → i < h → m i ≠ m 0) : h ≤ t := by
  exact le_trans
    (AdditivePrimitiveLengthBoundModulus D t h m tPositive coprime hPositive
      representatives modular closed noEarlier)
    (Nat.div_le_self t (Nat.gcd (m 0) t))

/-- Every primitive raw cycle has one modular witness carrying its clock, order, and bounds. -/
theorem AdditiveRawPrimitiveClassification (c D s t k n p : ℕ) (DLower : 2 ≤ D)
    (cPositive : 0 < c) (sPositive : 0 < s) (tPositive : 0 < t)
    (product : s * t = c) (sPower : s ∣ D ^ k) (coprime : Nat.Coprime D t)
    (nPositive : 0 < n) (pPositive : 0 < p)
    (returned : Iterate (PositiveRawStep 1 c D) p n = n)
    (noEarlierRaw : ∀ v, 0 < v → v < p → Iterate (PositiveRawStep 1 c D) v n ≠ n) :
    ∃ u h : ℕ, ∃ m : ℕ → ℕ,
      0 < h ∧ Iterate (PositiveRawStep 1 c D) u n = s * m 0 ∧
      (∀ i ≤ h, 0 < m i ∧ m i ≤ AdditiveCycleWindow c D t) ∧
      (∀ i < h, Nat.ModEq t (D * m (i + 1)) (m i)) ∧ m h = m 0 ∧
      (∀ i, 0 < i → i < h → m i ≠ m 0) ∧
      p = h + ((D - 1) * (∑ i ∈ Finset.range h, m i)) / t ∧
      orderOf (ZMod.unitOfCoprime D (coprime.coprime_dvd_right
        (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right (m 0) t)))) = h ∧ h ≤ t := by
  obtain ⟨u, h, m, hPositive, _hUpper, phase, windows, modular, closed, noEarlier,
    ell, indices, edges, clock⟩ := AdditiveRawPrimitiveToModular
      c D s t k n p DLower cPositive sPositive product sPower
        nPositive pPositive returned noEarlierRaw
  have representatives : ∀ i ≤ h, 0 < m i ∧ m i ≤ t := by
    intro i within
    exact ⟨(windows i within).1, le_trans (windows i within).2
      (AdditiveCycleWindowUpper c D t DLower)⟩
  have grouped : p = h + ((D - 1) * (∑ i ∈ Finset.range h, m i)) / t := by
    rw [← clock]
    exact AdditiveScaledClosedClock c D s t h ell m
      DLower sPositive tPositive product edges closed
  have exactOrder := AdditivePrimitiveOrder
    D t h m tPositive coprime hPositive representatives modular closed noEarlier
  have lengthBound := AdditivePrimitiveLengthBound
    D t h m tPositive coprime hPositive representatives modular closed noEarlier
  exact ⟨u, h, m, hPositive, phase, windows, modular, closed, noEarlier,
    grouped, exactOrder, lengthBound⟩

end GeneralizedCollatz
