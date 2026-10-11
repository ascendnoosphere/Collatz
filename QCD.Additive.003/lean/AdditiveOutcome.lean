-- SPDX-License-Identifier: CC-BY-4.0
import AdditiveCycles
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Pigeonhole

set_option autoImplicit false
namespace GeneralizedCollatz

/-- Choose the unique legal access index, reserving zero for inaccessible states. -/
noncomputable def AdditiveEventIndex (c D n : ℕ) (DLower : 2 ≤ D) : ℕ :=
  if accessible : Nat.gcd c D ∣ n then
    Classical.choose (AdditiveAccessExists c D n (by omega) accessible)
  else 0

/-- The chosen accessible index retains its bound and division certificate. -/
theorem AdditiveEventIndexSpec (c D n : ℕ) (DLower : 2 ≤ D)
    (accessible : Nat.gcd c D ∣ n) :
    AdditiveEventIndex c D n DLower < D / Nat.gcd c D ∧
      D ∣ n + AdditiveEventIndex c D n DLower * c := by
  rw [AdditiveEventIndex, dif_pos accessible]
  exact Classical.choose_spec (AdditiveAccessExists c D n (by omega) accessible)

/-- An event is one first division, or a stopped trap rather than a fictitious raw step. -/
noncomputable def AdditiveEventStep (c D n : ℕ) (DLower : 2 ≤ D) : ℕ :=
  if Nat.gcd c D ∣ n then (n + AdditiveEventIndex c D n DLower * c) / D else n

/-- Stopped traps have clock zero; accessible events have their full positive raw clock. -/
noncomputable def AdditiveEventWeight (c D n : ℕ) (DLower : 2 ≤ D) : ℕ :=
  if Nat.gcd c D ∣ n then AdditiveEventIndex c D n DLower + 1 else 0

/-- The stopped event model preserves exact raw endpoints without claiming positive trap clocks. -/
theorem AdditiveEventRaw (c D n : ℕ) (DLower : 2 ≤ D) :
    AdditiveEventStep c D n DLower =
      Iterate (PositiveRawStep 1 c D) (AdditiveEventWeight c D n DLower) n := by
  by_cases accessible : Nat.gcd c D ∣ n
  · have index := AdditiveEventIndexSpec c D n DLower accessible
    simp only [AdditiveEventStep, AdditiveEventWeight, if_pos accessible]
    exact (AdditiveFirstDivisionRaw c D n _ (by omega) index.1 index.2).symm
  · simp [AdditiveEventStep, AdditiveEventWeight, accessible, Iterate]

/-- Every finite event path is recovered at its accumulated, possibly stopped, raw clock. -/
theorem AdditiveEventRecovery (c D n k : ℕ) (DLower : 2 ≤ D) :
    Iterate (fun x => AdditiveEventStep c D x DLower) k n =
      Iterate (PositiveRawStep 1 c D)
        (AccumulatedClock (fun x => AdditiveEventStep c D x DLower)
          (fun x => AdditiveEventWeight c D x DLower) k n) n := by
  exact VariableClockIterates (fun x => AdditiveEventStep c D x DLower)
    (PositiveRawStep 1 c D) id (fun x => AdditiveEventWeight c D x DLower)
    (fun x => AdditiveEventRaw c D x DLower) k n

/-- Both accessible events and stopped traps preserve the positive finite core. -/
theorem AdditiveEventCore (c D n : ℕ) (DLower : 2 ≤ D)
    (nPositive : 0 < n) (nCore : n ≤ AdditiveCoreRadius c D) :
    0 < AdditiveEventStep c D n DLower ∧
      AdditiveEventStep c D n DLower ≤ AdditiveCoreRadius c D := by
  by_cases accessible : Nat.gcd c D ∣ n
  · have index := AdditiveEventIndexSpec c D n DLower accessible
    rw [AdditiveEventStep, if_pos accessible]
    exact ⟨AdditiveFirstDivisionPositive c D n _ (by omega) nPositive index.2,
      AdditiveCoreInvariant c D n _ DLower index.1 nCore⟩
  · simpa [AdditiveEventStep, accessible] using And.intro nPositive nCore

/-- Core invariance holds at every event index, including a stopped tail. -/
theorem AdditiveEventCoreTrace (c D n : ℕ) (DLower : 2 ≤ D)
    (nPositive : 0 < n) (nCore : n ≤ AdditiveCoreRadius c D) (k : ℕ) :
    0 < Iterate (fun x => AdditiveEventStep c D x DLower) k n ∧
      Iterate (fun x => AdditiveEventStep c D x DLower) k n ≤ AdditiveCoreRadius c D := by
  induction k with
  | zero => {
      exact ⟨nPositive, nCore⟩
    }
  | succ k ih => {
      exact AdditiveEventCore c D _ DLower ih.1 ih.2
    }

/-- No event consumes more raw instructions than the normalized access length. -/
theorem AdditiveEventWeightUpper (c D n : ℕ) (DLower : 2 ≤ D) :
    AdditiveEventWeight c D n DLower ≤ D / Nat.gcd c D := by
  by_cases accessible : Nat.gcd c D ∣ n
  · have index := (AdditiveEventIndexSpec c D n DLower accessible).1
    simp only [AdditiveEventWeight, if_pos accessible]
    omega
  · simp [AdditiveEventWeight, accessible]

/-- Event budgets bound the complete raw clock, not just the division count. -/
theorem AdditiveEventClockUpper (c D n k : ℕ) (DLower : 2 ≤ D) :
    AccumulatedClock (fun x => AdditiveEventStep c D x DLower)
      (fun x => AdditiveEventWeight c D x DLower) k n ≤ k * (D / Nat.gcd c D) := by
  induction k with
  | zero => {
      simp [AccumulatedClock]
    }
  | succ k ih => {
      rw [AccumulatedClock, Nat.succ_mul]
      exact Nat.add_le_add ih (AdditiveEventWeightUpper c D _ DLower)
    }

/-- Nonnegative event clocks never decrease, even after stopping at a trap. -/
theorem AdditiveEventClockMonotone (c D n i j : ℕ) (DLower : 2 ≤ D) (ij : i ≤ j) :
    AccumulatedClock (fun x => AdditiveEventStep c D x DLower)
        (fun x => AdditiveEventWeight c D x DLower) i n ≤
      AccumulatedClock (fun x => AdditiveEventStep c D x DLower)
        (fun x => AdditiveEventWeight c D x DLower) j n := by
  induction j with
  | zero => {
      have iZero : i = 0 := by omega
      subst i
      rfl
    }
  | succ j ih => {
      by_cases before : i ≤ j
      · exact le_trans (ih before) (by rw [AccumulatedClock]; omega)
      · have atEnd : i = j + 1 := by omega
        subst i
        rfl
    }

/-- Among the first N+1 positive core states, two have equal event endpoints. -/
theorem AdditiveEventCoreRepeat (c D n : ℕ) (DLower : 2 ≤ D)
    (nPositive : 0 < n) (nCore : n ≤ AdditiveCoreRadius c D) :
    ∃ i j : ℕ, i < j ∧ j ≤ AdditiveCoreRadius c D ∧
      Iterate (fun x => AdditiveEventStep c D x DLower) i n =
        Iterate (fun x => AdditiveEventStep c D x DLower) j n := by
  let N := AdditiveCoreRadius c D
  let labels : Fin (N + 1) → Fin N := fun i =>
    ⟨Iterate (fun x => AdditiveEventStep c D x DLower) i.val n - 1, by
      have bounds := AdditiveEventCoreTrace c D n DLower nPositive nCore i.val
      change _ < AdditiveCoreRadius c D
      omega⟩
  have cardinal : Fintype.card (Fin N) < Fintype.card (Fin (N + 1)) := by simp
  obtain ⟨i, j, distinct, same⟩ := Fintype.exists_ne_map_eq_of_card_lt labels cardinal
  have different : i.val ≠ j.val := by
    intro equal
    exact distinct (Fin.ext equal)
  have points : Iterate (fun x => AdditiveEventStep c D x DLower) i.val n =
      Iterate (fun x => AdditiveEventStep c D x DLower) j.val n := by
    have equal := congrArg Fin.val same
    change Iterate (fun x => AdditiveEventStep c D x DLower) i.val n - 1 =
      Iterate (fun x => AdditiveEventStep c D x DLower) j.val n - 1 at equal
    have positiveI := (AdditiveEventCoreTrace c D n DLower nPositive nCore i.val).1
    have positiveJ := (AdditiveEventCoreTrace c D n DLower nPositive nCore j.val).1
    omega
  rcases lt_or_gt_of_ne different with before | after
  · exact ⟨i.val, j.val, before, by have bound := j.isLt; dsimp [N] at bound; omega,
      points⟩
  · exact ⟨j.val, i.val, after, by have bound := i.isLt; dsimp [N] at bound; omega,
      points.symm⟩

/-- A finite core path stops at a true trap or returns with a strictly positive raw period. -/
theorem AdditiveCoreOutcome (c D n : ℕ) (DLower : 2 ≤ D)
    (nPositive : 0 < n) (nCore : n ≤ AdditiveCoreRadius c D) :
    ∃ a : ℕ, a ≤ AdditiveCoreRadius c D * (D / Nat.gcd c D) ∧
      (¬Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) a n ∨
        ∃ p : ℕ, 0 < p ∧ p ≤ AdditiveCoreRadius c D * (D / Nat.gcd c D) ∧
          Iterate (PositiveRawStep 1 c D) (a + p) n =
            Iterate (PositiveRawStep 1 c D) a n) := by
  classical
  let e := fun x => AdditiveEventStep c D x DLower
  let w := fun x => AdditiveEventWeight c D x DLower
  let K := fun i => AccumulatedClock e w i n
  by_cases stopped : ∃ i ≤ AdditiveCoreRadius c D, ¬Nat.gcd c D ∣ Iterate e i n
  · obtain ⟨i, iUpper, trap⟩ := stopped
    refine ⟨K i, le_trans (AdditiveEventClockUpper c D n i DLower)
      (Nat.mul_le_mul_right _ iUpper), Or.inl ?_⟩
    rwa [AdditiveEventRecovery c D n i DLower] at trap
  · obtain ⟨i, j, before, jUpper, repeated⟩ :=
      AdditiveEventCoreRepeat c D n DLower nPositive nCore
    have accessible : Nat.gcd c D ∣ Iterate e i n := by
      by_contra trap
      exact stopped ⟨i, by omega, trap⟩
    have positiveWeight : 0 < w (Iterate e i n) := by
      dsimp [w]
      rw [AdditiveEventWeight, if_pos accessible]
      omega
    have firstIncrease : K i < K (i + 1) := by
      dsimp [K]
      rw [AccumulatedClock]
      omega
    have subsequent : K (i + 1) ≤ K j :=
      AdditiveEventClockMonotone c D n (i + 1) j DLower (by omega)
    have strictClock : K i < K j := lt_of_lt_of_le firstIncrease subsequent
    have finalUpper : K j ≤ AdditiveCoreRadius c D * (D / Nat.gcd c D) :=
      le_trans (AdditiveEventClockUpper c D n j DLower) (Nat.mul_le_mul_right _ jUpper)
    refine ⟨K i, by omega, Or.inr ⟨K j - K i, by omega, by omega, ?_⟩⟩
    have split : K i + (K j - K i) = K j := by omega
    rw [split, ← AdditiveEventRecovery c D n j DLower,
      ← AdditiveEventRecovery c D n i DLower]
    exact repeated.symm

/-- Every positive additive seed reaches either an inaccessible state or a raw periodic phase. -/
theorem AdditiveAllSeedReturnOrTrap (c D n : ℕ) (DLower : 2 ≤ D) (nPositive : 0 < n) :
    ∃ u : ℕ, ¬Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) u n ∨
      ∃ p : ℕ, 0 < p ∧ Iterate (PositiveRawStep 1 c D) (u + p) n =
        Iterate (PositiveRawStep 1 c D) u n := by
  obtain ⟨v, phasePositive, inCore | trap⟩ := AdditiveFiniteReduction c D n DLower nPositive
  · obtain ⟨a, _bound, trapped | periodic⟩ :=
      AdditiveCoreOutcome c D _ DLower phasePositive inCore
    · refine ⟨v + a, Or.inl ?_⟩
      rwa [IterateAdd]
    · obtain ⟨p, pPositive, _pBound, returned⟩ := periodic
      refine ⟨v + a, Or.inr ⟨p, pPositive, ?_⟩⟩
      rw [Nat.add_assoc, IterateAdd (PositiveRawStep 1 c D) v (a + p) n,
        IterateAdd (PositiveRawStep 1 c D) v a n]
      exact returned
  · exact ⟨v, Or.inl trap⟩

/-- Positive offsets yield either eventual periodicity or an exact escaping affine tail. -/
theorem AdditiveAllSeedOutcome (c D n : ℕ) (DLower : 2 ≤ D)
    (cPositive : 0 < c) (nPositive : 0 < n) :
    (∃ u p : ℕ, 0 < p ∧ Iterate (PositiveRawStep 1 c D) (u + p) n =
      Iterate (PositiveRawStep 1 c D) u n) ∨
    (∃ u : ℕ, ¬Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) u n ∧
      (∀ j : ℕ, Iterate (PositiveRawStep 1 c D) (u + j) n =
        Iterate (PositiveRawStep 1 c D) u n + j * c) ∧
      Filter.Tendsto (fun j => Iterate (PositiveRawStep 1 c D) j n)
        Filter.atTop Filter.atTop) := by
  obtain ⟨u, trap | periodic⟩ := AdditiveAllSeedReturnOrTrap c D n DLower nPositive
  · exact Or.inr ⟨u, trap, (fun j => AdditiveReachedTrapTail c D n u j trap),
      AdditiveReachedTrapEscape c D n u cPositive trap⟩
  · obtain ⟨p, pPositive, returned⟩ := periodic
    exact Or.inl ⟨u, p, pPositive, returned⟩

/-- After core entry, one common witness needs at most N access-length raw steps. -/
theorem AdditiveAllSeedFiniteBudget (c D n : ℕ) (DLower : 2 ≤ D) (nPositive : 0 < n) :
    ∃ v a : ℕ, 0 < Iterate (PositiveRawStep 1 c D) v n ∧
      (Iterate (PositiveRawStep 1 c D) v n ≤ AdditiveCoreRadius c D ∨
        ¬Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) v n) ∧
      a ≤ AdditiveCoreRadius c D * (D / Nat.gcd c D) ∧
      (¬Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) (v + a) n ∨
        ∃ p : ℕ, 0 < p ∧ p ≤ AdditiveCoreRadius c D * (D / Nat.gcd c D) ∧
          Iterate (PositiveRawStep 1 c D) (v + a + p) n =
            Iterate (PositiveRawStep 1 c D) (v + a) n) := by
  obtain ⟨v, positive, inCore | trap⟩ := AdditiveFiniteReduction c D n DLower nPositive
  · obtain ⟨a, bound, trapped | periodic⟩ :=
      AdditiveCoreOutcome c D _ DLower positive inCore
    · refine ⟨v, a, positive, Or.inl inCore, bound, Or.inl ?_⟩
      rwa [IterateAdd]
    · obtain ⟨p, pPositive, pBound, returned⟩ := periodic
      refine ⟨v, a, positive, Or.inl inCore, bound, Or.inr ⟨p, pPositive, pBound, ?_⟩⟩
      rw [Nat.add_assoc, IterateAdd (PositiveRawStep 1 c D) v (a + p) n,
        IterateAdd (PositiveRawStep 1 c D) v a n]
      exact returned
  · exact ⟨v, 0, positive, Or.inr trap, by simp, Or.inl (by simpa using trap)⟩

/-- A positive-offset raw periodic tail can never reach an inaccessible state. -/
theorem AdditivePeriodicNoTrap (c D n u p : ℕ) (cPositive : 0 < c) (pPositive : 0 < p)
    (returned : Iterate (PositiveRawStep 1 c D) (u + p) n =
      Iterate (PositiveRawStep 1 c D) u n) :
    ∀ t : ℕ, Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) t n := by
  intro t
  by_contra trap
  have laterReturn : Iterate (PositiveRawStep 1 c D) ((u + p) + t) n =
      Iterate (PositiveRawStep 1 c D) (u + t) n := by
    rw [IterateAdd (PositiveRawStep 1 c D) (u + p) t n, returned,
      IterateAdd (PositiveRawStep 1 c D) u t n]
  have highClock : (u + p) + t = t + (u + p) := by omega
  have lowClock : u + t = t + u := by omega
  rw [highClock, lowClock, AdditiveReachedTrapTail c D n t (u + p) trap,
    AdditiveReachedTrapTail c D n t u trap, Nat.add_mul] at laterReturn
  have strictGrowth : 0 < p * c := Nat.mul_pos pPositive cPositive
  omega

/-- Eventual raw periodicity is equivalent to never encountering a true trap. -/
theorem AdditivePeriodicIffNoTrap (c D n : ℕ) (DLower : 2 ≤ D)
    (cPositive : 0 < c) (nPositive : 0 < n) :
    (∃ u p : ℕ, 0 < p ∧ Iterate (PositiveRawStep 1 c D) (u + p) n =
      Iterate (PositiveRawStep 1 c D) u n) ↔
    (∀ t : ℕ, Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) t n) := by
  constructor
  · rintro ⟨u, p, pPositive, returned⟩
    exact AdditivePeriodicNoTrap c D n u p cPositive pPositive returned
  · intro accessible
    obtain ⟨u, trap | periodic⟩ := AdditiveAllSeedReturnOrTrap c D n DLower nPositive
    · exact False.elim (trap (accessible u))
    · obtain ⟨p, pPositive, returned⟩ := periodic
      exact ⟨u, p, pPositive, returned⟩

/-- Coprimality exactly characterizes eventual periodicity of every positive additive seed. -/
theorem AdditiveAllPeriodicIffCoprime (c D : ℕ) (DLower : 2 ≤ D) (cPositive : 0 < c) :
    (∀ n : ℕ, 0 < n → ∃ u p : ℕ, 0 < p ∧
      Iterate (PositiveRawStep 1 c D) (u + p) n =
        Iterate (PositiveRawStep 1 c D) u n) ↔ Nat.Coprime c D := by
  constructor
  · intro everySeed
    obtain ⟨u, p, pPositive, returned⟩ := everySeed 1 (by omega)
    have access := AdditivePeriodicNoTrap c D 1 u p cPositive pPositive returned 0
    change Nat.gcd c D ∣ 1 at access
    change Nat.gcd c D = 1
    exact Nat.dvd_one.mp access
  · intro coprime n nPositive
    apply (AdditivePeriodicIffNoTrap c D n DLower cPositive nPositive).mpr
    intro t
    rw [coprime.gcd_eq_one]
    exact one_dvd _

/-- A returned raw phase cannot have full-sequence escape to infinity. -/
theorem AdditivePeriodicNotEscape (c D n u p : ℕ) (pPositive : 0 < p)
    (returned : Iterate (PositiveRawStep 1 c D) (u + p) n =
      Iterate (PositiveRawStep 1 c D) u n) :
    ¬Filter.Tendsto (fun j => Iterate (PositiveRawStep 1 c D) j n)
      Filter.atTop Filter.atTop := by
  intro escapes
  obtain ⟨B, above⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.mp escapes) (Iterate (PositiveRawStep 1 c D) u n + 1))
  have clockBound : B ≤ u + p * B := by
    have multiplied := Nat.le_mul_of_pos_left B pPositive
    omega
  have phaseReturn : Iterate (PositiveRawStep 1 c D) p
      (Iterate (PositiveRawStep 1 c D) u n) = Iterate (PositiveRawStep 1 c D) u n := by
    rw [← IterateAdd]
    exact returned
  have repeated : Iterate (PositiveRawStep 1 c D) (u + p * B) n =
      Iterate (PositiveRawStep 1 c D) u n := by
    rw [IterateAdd]
    exact IterateReturnMultiple (PositiveRawStep 1 c D) _ p B phaseReturn
  have contradicted := above (u + p * B) clockBound
  rw [repeated] at contradicted
  omega

/-- For positive offsets, divergence occurs exactly when a finite trap witness is reached. -/
theorem AdditiveEscapeIffTrap (c D n : ℕ) (DLower : 2 ≤ D)
    (cPositive : 0 < c) (nPositive : 0 < n) :
    Filter.Tendsto (fun j => Iterate (PositiveRawStep 1 c D) j n)
      Filter.atTop Filter.atTop ↔
    ∃ t : ℕ, ¬Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) t n := by
  constructor
  · intro escapes
    obtain ⟨u, trap | periodic⟩ := AdditiveAllSeedReturnOrTrap c D n DLower nPositive
    · exact ⟨u, trap⟩
    · obtain ⟨p, pPositive, returned⟩ := periodic
      exact False.elim (AdditivePeriodicNotEscape c D n u p pPositive returned escapes)
  · rintro ⟨t, trap⟩
    exact AdditiveReachedTrapEscape c D n t cPositive trap

/-- Positive additive raw states remain positive at division as well as addition. -/
theorem AdditiveRawPositive (c D n : ℕ) (DLower : 2 ≤ D) (nPositive : 0 < n) :
    0 < PositiveRawStep 1 c D n := by
  by_cases divides : D ∣ n
  · rw [PositiveRawStep, if_pos divides]
    exact Nat.div_pos (Nat.le_of_dvd nPositive divides) (by omega)
  · simp only [PositiveRawStep, if_neg divides, one_mul]
    omega

/-- The entire positive raw trajectory stays in the domain of the cycle classification. -/
theorem AdditiveRawIteratePositive (c D n k : ℕ) (DLower : 2 ≤ D)
    (nPositive : 0 < n) : 0 < Iterate (PositiveRawStep 1 c D) k n := by
  induction k with
  | zero => {
      exact nPositive
    }
  | succ k ih => {
      exact AdditiveRawPositive c D _ DLower ih
    }

/-- An empty modular window excludes every periodic tail, even when the raw core is nonempty. -/
theorem AdditiveEmptyWindowEscape (c D s t k n : ℕ) (DLower : 2 ≤ D)
    (cPositive : 0 < c) (sPositive : 0 < s) (product : s * t = c) (sPower : s ∣ D ^ k)
    (nPositive : 0 < n) (empty : AdditiveCycleWindow c D t = 0) :
    Filter.Tendsto (fun j => Iterate (PositiveRawStep 1 c D) j n)
      Filter.atTop Filter.atTop := by
  obtain ⟨u, trap | periodic⟩ := AdditiveAllSeedReturnOrTrap c D n DLower nPositive
  · exact AdditiveReachedTrapEscape c D n u cPositive trap
  · obtain ⟨p, pPositive, returned⟩ := periodic
    have phasePositive := AdditiveRawIteratePositive c D n u DLower nPositive
    have phaseReturned : Iterate (PositiveRawStep 1 c D) p
        (Iterate (PositiveRawStep 1 c D) u n) = Iterate (PositiveRawStep 1 c D) u n := by
      rw [← IterateAdd]
      exact returned
    obtain ⟨v, h, m, _hPositive, _hBound, _phase, windows, _modular, _closed, _edges⟩ :=
      AdditiveRawPeriodicToModular c D s t k _ p DLower cPositive sPositive product sPower
        phasePositive pPositive phaseReturned
    have impossible := windows 0 (Nat.zero_le h)
    rw [empty] at impossible
    omega

/-- Every positive seed escapes exactly when no positive raw periodic state exists. -/
theorem AdditiveEverySeedEscapesIffNoCycle (c D : ℕ) (DLower : 2 ≤ D)
    (cPositive : 0 < c) :
    (∀ n : ℕ, 0 < n → Filter.Tendsto (fun j => Iterate (PositiveRawStep 1 c D) j n)
      Filter.atTop Filter.atTop) ↔
    ¬∃ n p : ℕ, 0 < n ∧ 0 < p ∧ Iterate (PositiveRawStep 1 c D) p n = n := by
  constructor
  · intro allEscape
    rintro ⟨n, p, nPositive, pPositive, returned⟩
    apply AdditivePeriodicNotEscape c D n 0 p pPositive (by simpa [Iterate] using returned)
    exact allEscape n nPositive
  · intro noCycle n nPositive
    obtain ⟨u, trap | periodic⟩ := AdditiveAllSeedReturnOrTrap c D n DLower nPositive
    · exact AdditiveReachedTrapEscape c D n u cPositive trap
    · obtain ⟨p, pPositive, returned⟩ := periodic
      have phasePositive := AdditiveRawIteratePositive c D n u DLower nPositive
      have phaseReturn : Iterate (PositiveRawStep 1 c D) p
          (Iterate (PositiveRawStep 1 c D) u n) = Iterate (PositiveRawStep 1 c D) u n := by
        rw [← IterateAdd]
        exact returned
      exact False.elim (noCycle ⟨_, p, phasePositive, pPositive, phaseReturn⟩)

/-- Nonempty raw cores need not contain a cycle: the offset-nine divisor-six window is empty. -/
theorem AdditiveNonemptyCoreEscapeControl (n : ℕ) (nPositive : 0 < n) :
    AdditiveCoreRadius 9 6 = 1 ∧
      Filter.Tendsto (fun j => Iterate (PositiveRawStep 1 9 6) j n)
        Filter.atTop Filter.atTop := by
  refine ⟨by decide, ?_⟩
  exact AdditiveEmptyWindowEscape 9 6 9 1 2 n (by omega) (by omega) (by omega)
    (by decide) (by decide) nPositive (by decide)

/-- Initial division access does not determine a seed's basin for noncoprime parameters. -/
theorem AdditiveMixedBasinControl :
    Iterate (PositiveRawStep 1 6 4) 2 2 = 2 ∧ Nat.gcd 6 4 ∣ 4 ∧
      Filter.Tendsto (fun j => Iterate (PositiveRawStep 1 6 4) j 4)
        Filter.atTop Filter.atTop := by
  refine ⟨by decide, by decide, ?_⟩
  exact AdditiveReachedTrapEscape 6 4 4 1 (by omega) (by decide)

/-- A positive window can reject every whole modular orbit and force all seeds to escape. -/
theorem AdditivePositiveWindowEscapeControl (n : ℕ) (nPositive : 0 < n) :
    AdditiveCycleWindow 10 4 5 = 1 ∧
      Filter.Tendsto (fun j => Iterate (PositiveRawStep 1 10 4) j n)
        Filter.atTop Filter.atTop := by
  refine ⟨by decide, ?_⟩
  obtain ⟨u, trap | periodic⟩ := AdditiveAllSeedReturnOrTrap 10 4 n (by omega) nPositive
  · exact AdditiveReachedTrapEscape 10 4 n u (by omega) trap
  · obtain ⟨p, pPositive, returned⟩ := periodic
    have phasePositive := AdditiveRawIteratePositive 10 4 n u (by omega) nPositive
    have phaseReturn : Iterate (PositiveRawStep 1 10 4) p
        (Iterate (PositiveRawStep 1 10 4) u n) = Iterate (PositiveRawStep 1 10 4) u n := by
      rw [← IterateAdd]
      exact returned
    obtain ⟨v, h, m, hPositive, _hBound, _phase, windows, modular, _closed, _edges⟩ :=
      AdditiveRawPeriodicToModular 10 4 2 5 1 _ p (by omega) (by omega) (by omega)
        (by decide) (by decide) phasePositive pPositive phaseReturn
    have windowValue : AdditiveCycleWindow 10 4 5 = 1 := by decide
    have first := windows 0 (Nat.zero_le h)
    have second := windows 1 (by omega)
    rw [windowValue] at first second
    have firstValue : m 0 = 1 := by omega
    have secondValue : m 1 = 1 := by omega
    have edge := modular 0 hPositive
    rw [firstValue, secondValue] at edge
    exact False.elim ((by decide : ¬Nat.ModEq 5 (4 * 1) 1) edge)

/-- A geometric entry budget and the finite core budget compose at the same raw witness. -/
theorem AdditiveAllSeedTotalBudget (c D n h : ℕ) (DLower : 2 ≤ D) (nPositive : 0 < n)
    (budget : AdditiveDefect c D n <
      (D : ℤ) ^ h * AdditiveDefect c D (AdditiveCoreRadius c D + 1)) :
    ∃ u ≤ (h + AdditiveCoreRadius c D) * (D / Nat.gcd c D),
      ¬Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) u n ∨
        ∃ p : ℕ, 0 < p ∧ p ≤ AdditiveCoreRadius c D * (D / Nat.gcd c D) ∧
          Iterate (PositiveRawStep 1 c D) (u + p) n =
            Iterate (PositiveRawStep 1 c D) u n := by
  obtain ⟨v, vBound, positive, inCore | trap⟩ :=
    AdditiveFiniteBudget c D h n DLower nPositive budget
  · obtain ⟨a, aBound, trapped | periodic⟩ :=
      AdditiveCoreOutcome c D _ DLower positive inCore
    · refine ⟨v + a, ?_, Or.inl ?_⟩
      · rw [Nat.add_mul]
        exact Nat.add_le_add vBound aBound
      · rwa [IterateAdd]
    · obtain ⟨p, pPositive, pBound, returned⟩ := periodic
      refine ⟨v + a, ?_, Or.inr ⟨p, pPositive, pBound, ?_⟩⟩
      · rw [Nat.add_mul]
        exact Nat.add_le_add vBound aBound
      · rw [Nat.add_assoc, IterateAdd (PositiveRawStep 1 c D) v (a + p) n,
          IterateAdd (PositiveRawStep 1 c D) v a n]
        exact returned
  · refine ⟨v, ?_, Or.inl trap⟩
    exact le_trans vBound (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))

/-- Bernoulli's inequality supplies a uniform, nonoptimal geometric budget h=n. -/
theorem AdditiveSeedGeometricBudget (c D n : ℕ) (DLower : 2 ≤ D) :
    AdditiveDefect c D n <
      (D : ℤ) ^ n * AdditiveDefect c D (AdditiveCoreRadius c D + 1) := by
  have baseline : AdditiveDefect c D n < 1 + (n : ℤ) * ((D : ℤ) - 1) := by
    have displacementNonnegative : 0 ≤ (AdditiveDisplacement c D : ℤ) := Nat.cast_nonneg _
    dsimp [AdditiveDefect]
    nlinarith
  have bernoulli : 1 + (n : ℤ) * ((D : ℤ) - 1) ≤ (D : ℤ) ^ n := by
    have bound := one_add_mul_le_pow (a := (D : ℤ) - 1) (by omega) n
    have base : 1 + ((D : ℤ) - 1) = (D : ℤ) := by ring
    rw [base] at bound
    exact bound
  have epsilon := (AdditiveCoreDefectBounds c D DLower).1
  have powerNonnegative : 0 ≤ (D : ℤ) ^ n := pow_nonneg (by omega) n
  have amplification : (D : ℤ) ^ n ≤
      (D : ℤ) ^ n * AdditiveDefect c D (AdditiveCoreRadius c D + 1) := by
    simpa using mul_le_mul_of_nonneg_left epsilon powerNonnegative
  exact lt_of_lt_of_le (lt_of_lt_of_le baseline bernoulli) amplification

/-- A closed raw-time bound exists for every positive seed without an unbounded clock oracle. -/
theorem AdditiveAllSeedExplicitBudget (c D n : ℕ) (DLower : 2 ≤ D) (nPositive : 0 < n) :
    ∃ u ≤ (n + AdditiveCoreRadius c D) * (D / Nat.gcd c D),
      ¬Nat.gcd c D ∣ Iterate (PositiveRawStep 1 c D) u n ∨
        ∃ p : ℕ, 0 < p ∧ p ≤ AdditiveCoreRadius c D * (D / Nat.gcd c D) ∧
          Iterate (PositiveRawStep 1 c D) (u + p) n =
            Iterate (PositiveRawStep 1 c D) u n := by
  exact AdditiveAllSeedTotalBudget c D n n DLower nPositive
    (AdditiveSeedGeometricBudget c D n DLower)

end GeneralizedCollatz
