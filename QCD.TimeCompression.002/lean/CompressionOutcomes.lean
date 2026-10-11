-- SPDX-License-Identifier: CC-BY-4.0
import TimeCompression
import Mathlib.Data.Fintype.Pigeonhole

/-!
Full-time orbit recovery for common-divisor-power compression.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Every prefix of a forced division run retains the unspent divisor factors. -/
theorem PowerDivisionPrefix (p : Parameters) (a s : ℕ) (n : ℤ) (sBound : s ≤ a) :
    Iterate (RawStep p) s (p.D ^ a * n) = p.D ^ (a - s) * n := by
  have split : p.D ^ a * n = p.D ^ s * (p.D ^ (a - s) * n) := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le sBound]
  rw [split, PowerDivisionRun]

/-- Intermediate affine-block states are explicit, including the final endpoint. -/
theorem CompressionAffineIntermediate (p : Parameters) (q c : ℤ) (a s : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c)
    (n : ℤ) (affineGuard : ¬p.D ∣ n) (sPositive : 0 < s) (sBound : s ≤ a + 1) :
    Iterate (RawStep p) s n =
      p.D ^ (a + 1 - s) * RawStep (CompressedParameters p q c) n := by
  have first : RawStep p n = p.D ^ a * (q * n + c) := by
    rw [RawStep, if_neg affineGuard, qFactor, cFactor]
    ring
  have remainingBound : s - 1 ≤ a := by omega
  have time : s - 1 + 1 = s := by omega
  have exponent : a - (s - 1) = a + 1 - s := by omega
  calc
    Iterate (RawStep p) s n = Iterate (RawStep p) (s - 1 + 1) n := by rw [time]
    _ = Iterate (RawStep p) (s - 1) (RawStep p n) := by rw [IterateFirst]
    _ = p.D ^ (a - (s - 1)) * (q * n + c) := by
      rw [first, PowerDivisionPrefix p a (s - 1) _ remainingBound]
    _ = p.D ^ (a + 1 - s) * RawStep (CompressedParameters p q c) n := by
      rw [exponent]
      simp only [RawStep, CompressedParameters, if_neg affineGuard]

/-- Positive block lengths make accumulated times strictly increasing. -/
theorem PositiveClockStrictMono {α : Type*} (g : α → α) (clock : α → ℕ)
    (positive : ∀ x, 1 ≤ clock x) (n : α) :
    StrictMono (fun k => AccumulatedClock g clock k n) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have advances := positive (Iterate g k n)
  simp only [AccumulatedClock]
  omega

/-- Positive blocks cover every raw time, including times between sampled states. -/
theorem PositiveClockCover {α : Type*} (g : α → α) (clock : α → ℕ)
    (positive : ∀ x, 1 ≤ clock x) (n : α) (r : ℕ) :
    ∃ k s : ℕ, k ≤ r ∧ s < clock (Iterate g k n) ∧
      r = AccumulatedClock g clock k n + s := by
  induction r with
  | zero => {
      refine ⟨0, 0, by omega, ?_, rfl⟩
      have advances := positive n
      simp only [Iterate]
      omega
    }
  | succ r inductionHypothesis => {
      obtain ⟨k, s, kBound, sBound, time⟩ := inductionHypothesis
      by_cases inside : s + 1 < clock (Iterate g k n)
      · refine ⟨k, s + 1, by omega, inside, ?_⟩
        omega
      · have boundary : s + 1 = clock (Iterate g k n) := by omega
        refine ⟨k + 1, 0, by omega, ?_, ?_⟩
        · have advances := positive (Iterate g (k + 1) n)
          omega
        · simp only [AccumulatedClock]
          omega
    }

/-- A block containing a time beyond a chosen accumulated cutoff has a later index. -/
theorem PositiveClockCoverAfter {α : Type*} (g : α → α) (clock : α → ℕ)
    (positive : ∀ x, 1 ≤ clock x) (n : α) (r k s K : ℕ)
    (inside : s < clock (Iterate g k n))
    (time : r = AccumulatedClock g clock k n + s)
    (after : AccumulatedClock g clock K n ≤ r) : K ≤ k := by
  have monotone := (PositiveClockStrictMono g clock positive n).monotone
  by_contra earlier
  have nextBefore : k + 1 ≤ K := by omega
  have nextBound : AccumulatedClock g clock (k + 1) n ≤
      AccumulatedClock g clock K n := monotone nextBefore
  have endTime : r < AccumulatedClock g clock (k + 1) n := by
    simp only [AccumulatedClock]
    omega
  omega

/-- Uniform block bounds give a quantitative bound for every accumulated time. -/
theorem BoundedClockTotal {α : Type*} (g : α → α) (clock : α → ℕ) (B : ℕ)
    (bounded : ∀ x, clock x ≤ B) (n : α) (k : ℕ) :
    AccumulatedClock g clock k n ≤ k * B := by
  induction k with
  | zero => {
      simp [AccumulatedClock]
    }
  | succ k inductionHypothesis => {
      have cap := bounded (Iterate g k n)
      simp only [AccumulatedClock, Nat.succ_mul]
      omega
    }

/-- Compression has a seed-independent upper bound on each exact block length. -/
theorem CompressionClockUpper (p : Parameters) (a : ℕ) (n : ℤ) :
    CompressionClock p a n ≤ a + 1 := by
  by_cases divisible : p.D ∣ n
  · simp [CompressionClock, divisible]
  · simp [CompressionClock, divisible]

/-- Intermediate raw magnitudes are controlled by the two adjacent compressed states. -/
theorem CompressionBlockMagnitudeBounds (p : Parameters) (q c : ℤ) (a s : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c)
    (n : ℤ) (inside : s < CompressionClock p a n) :
    min n.natAbs (RawStep (CompressedParameters p q c) n).natAbs ≤
        (Iterate (RawStep p) s n).natAbs ∧
      (Iterate (RawStep p) s n).natAbs ≤ p.D.natAbs ^ a *
        max n.natAbs (RawStep (CompressedParameters p q c) n).natAbs := by
  have divisorPositive : 0 < p.D.natAbs := by have h := p.DAdmissible; omega
  have factorOne : 1 ≤ p.D.natAbs ^ a := Nat.one_le_pow a _ divisorPositive
  by_cases zeroTime : s = 0
  · subst s
    simp only [Iterate]
    refine ⟨Nat.min_le_left _ _, ?_⟩
    calc
      n.natAbs ≤ max n.natAbs (RawStep (CompressedParameters p q c) n).natAbs :=
        Nat.le_max_left _ _
      _ = 1 * max n.natAbs (RawStep (CompressedParameters p q c) n).natAbs := by
        simp
      _ ≤ p.D.natAbs ^ a *
          max n.natAbs (RawStep (CompressedParameters p q c) n).natAbs :=
        Nat.mul_le_mul_right _ factorOne
  · have sPositive : 0 < s := by omega
    have affineGuard : ¬p.D ∣ n := by
      intro divisible
      simp only [CompressionClock, if_pos divisible] at inside
      omega
    have clockValue : CompressionClock p a n = a + 1 := by
      simp [CompressionClock, affineGuard]
    have sBound : s ≤ a + 1 := by omega
    have exponentBound : a + 1 - s ≤ a := by omega
    have intermediate :=
      CompressionAffineIntermediate p q c a s qFactor cFactor n affineGuard sPositive sBound
    rw [intermediate, Int.natAbs_mul, Int.natAbs_pow]
    have factorPositive : 1 ≤ p.D.natAbs ^ (a + 1 - s) :=
      Nat.one_le_pow _ _ divisorPositive
    have factorBound : p.D.natAbs ^ (a + 1 - s) ≤ p.D.natAbs ^ a :=
      Nat.pow_le_pow_right divisorPositive exponentBound
    constructor
    · calc
        min n.natAbs (RawStep (CompressedParameters p q c) n).natAbs ≤
            (RawStep (CompressedParameters p q c) n).natAbs := Nat.min_le_right _ _
        _ = 1 * (RawStep (CompressedParameters p q c) n).natAbs := by simp
        _ ≤ p.D.natAbs ^ (a + 1 - s) *
            (RawStep (CompressedParameters p q c) n).natAbs :=
          Nat.mul_le_mul_right _ factorPositive
    · exact Nat.mul_le_mul factorBound (Nat.le_max_right _ _)

/-- Boundedness here refers to the full signed orbit, including every raw time. -/
def MagnitudeBounded (f : ℤ → ℤ) (n : ℤ) : Prop :=
  ∃ M : ℕ, ∀ r : ℕ, (Iterate f r n).natAbs ≤ M

/-- Magnitude escape is a full-sequence assertion, not subsequence unboundedness. -/
def MagnitudeEscapes (f : ℤ → ℤ) (n : ℤ) : Prop :=
  ∀ M : ℕ, ∃ R : ℕ, ∀ r : ℕ, R ≤ r → M < (Iterate f r n).natAbs

/-- Bounded sampled states control every raw state, with an explicit magnitude factor. -/
theorem CompressionMagnitudeBounded (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (n : ℤ) :
    MagnitudeBounded (RawStep p) n ↔
      MagnitudeBounded (RawStep (CompressedParameters p q c)) n := by
  let g := RawStep (CompressedParameters p q c)
  let clock := CompressionClock p a
  have positive : ∀ x, 1 ≤ clock x := CompressionClockPositive p a
  have sampled : ∀ k, Iterate g k n =
      Iterate (RawStep p) (AccumulatedClock g clock k n) n :=
    fun k => CompressionIterates p q c a qFactor cFactor k n
  constructor
  · rintro ⟨M, bounded⟩
    refine ⟨M, ?_⟩
    intro k
    rw [sampled k]
    exact bounded _
  · rintro ⟨M, bounded⟩
    refine ⟨p.D.natAbs ^ a * M, ?_⟩
    intro r
    obtain ⟨k, s, _, inside, time⟩ := PositiveClockCover g clock positive n r
    have state : Iterate (RawStep p) r n =
        Iterate (RawStep p) s (Iterate g k n) := by
      rw [time, IterateAdd, ← sampled k]
    rw [state]
    have bounds := CompressionBlockMagnitudeBounds p q c a s qFactor cFactor
      (Iterate g k n) inside
    have nextBound : (RawStep (CompressedParameters p q c) (Iterate g k n)).natAbs ≤ M :=
      bounded (k + 1)
    have maxBound := max_le (bounded k) nextBound
    exact bounds.2.trans (Nat.mul_le_mul_left _ maxBound)

/-- Full-sequence magnitude escape transfers in both directions, not only at sample times. -/
theorem CompressionMagnitudeEscapes (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (n : ℤ) :
    MagnitudeEscapes (RawStep p) n ↔
      MagnitudeEscapes (RawStep (CompressedParameters p q c)) n := by
  let g := RawStep (CompressedParameters p q c)
  let clock := CompressionClock p a
  have positive : ∀ x, 1 ≤ clock x := CompressionClockPositive p a
  have sampled : ∀ k, Iterate g k n =
      Iterate (RawStep p) (AccumulatedClock g clock k n) n :=
    fun k => CompressionIterates p q c a qFactor cFactor k n
  constructor
  · intro escaped M
    obtain ⟨R, beyond⟩ := escaped M
    refine ⟨R, ?_⟩
    intro k kAfter
    rw [sampled k]
    have clockLower := AccumulatedClockLower g clock positive k n
    exact beyond _ (by omega)
  · intro escaped M
    obtain ⟨K, beyond⟩ := escaped M
    refine ⟨AccumulatedClock g clock K n, ?_⟩
    intro r rAfter
    obtain ⟨k, s, _, inside, time⟩ := PositiveClockCover g clock positive n r
    have kAfter := PositiveClockCoverAfter g clock positive n r k s K inside time rAfter
    have state : Iterate (RawStep p) r n =
        Iterate (RawStep p) s (Iterate g k n) := by
      rw [time, IterateAdd, ← sampled k]
    rw [state]
    have bounds := CompressionBlockMagnitudeBounds p q c a s qFactor cFactor
      (Iterate g k n) inside
    have nextBeyond : M <
        (RawStep (CompressedParameters p q c) (Iterate g k n)).natAbs :=
      beyond (k + 1) (by omega)
    have adjacentBeyond := lt_min (beyond k kAfter) nextBeyond
    exact lt_of_lt_of_le adjacentBeyond bounds.1

/-- Eventual periodicity means one positive-length return after a finite prefix. -/
def EventuallyPeriodic {α : Type*} (f : α → α) (n : α) : Prop :=
  ∃ u p : ℕ, 0 < p ∧ Iterate f (u + p) n = Iterate f u n

/-- A finite initial list of natural values has a common bound, without an orbit assumption. -/
theorem FinitePrefixBound (values : ℕ → ℕ) (length : ℕ) :
    ∃ M : ℕ, ∀ i : ℕ, i < length → values i ≤ M := by
  induction length with
  | zero => {
      exact ⟨0, fun i impossible => by omega⟩
    }
  | succ length inductionHypothesis => {
      obtain ⟨M, bounded⟩ := inductionHypothesis
      refine ⟨max M (values length), ?_⟩
      intro i iBound
      by_cases earlier : i < length
      · exact (bounded i earlier).trans (Nat.le_max_left _ _)
      · have last : i = length := by omega
        rw [last]
        exact Nat.le_max_right _ _
    }

/-- A repeated state makes a signed orbit bounded; strong induction decreases by its period. -/
theorem EventuallyPeriodicMagnitudeBounded (f : ℤ → ℤ) (n : ℤ)
    (periodic : EventuallyPeriodic f n) : MagnitudeBounded f n := by
  obtain ⟨u, p, pPositive, returned⟩ := periodic
  obtain ⟨M, bounded⟩ := FinitePrefixBound (fun i => (Iterate f i n).natAbs) (u + p)
  refine ⟨M, ?_⟩
  intro t
  induction t using Nat.strong_induction_on with
  | h t inductionHypothesis => {
      by_cases initial : t < u + p
      · exact bounded t initial
      · have tailBound : u + p ≤ t := by omega
        have decrease : t - p < t := by omega
        have totalTime : u + p + (t - (u + p)) = t := by omega
        have earlierTime : u + (t - (u + p)) = t - p := by omega
        have earlierState : Iterate f t n = Iterate f (t - p) n := by
          calc
            Iterate f t n = Iterate f (t - (u + p)) (Iterate f (u + p) n) := by
              rw [← IterateAdd, totalTime]
            _ = Iterate f (t - (u + p)) (Iterate f u n) := by rw [returned]
            _ = Iterate f (t - p) n := by rw [← IterateAdd, earlierTime]
        rw [earlierState]
        exact inductionHypothesis (t - p) decrease
    }

/-- The finite integer interval in a magnitude bound forces two equal orbit states. -/
theorem MagnitudeBoundedEventuallyPeriodic (f : ℤ → ℤ) (n : ℤ)
    (boundedOrbit : MagnitudeBounded f n) : EventuallyPeriodic f n := by
  classical
  obtain ⟨M, bounded⟩ := boundedOrbit
  let points : Fin (2 * M + 2) → Fin (2 * M + 1) := fun i =>
    ⟨(Iterate f i.val n + (M : ℤ)).toNat, by
      have cap := bounded i.val
      omega⟩
  have cardBound : Fintype.card (Fin (2 * M + 1)) < Fintype.card (Fin (2 * M + 2)) := by
    simp
  obtain ⟨i, j, different, same⟩ := Fintype.exists_ne_map_eq_of_card_lt points cardBound
  have differentTimes : i.val ≠ j.val := fun equal => different (Fin.ext equal)
  have sameCodes := congrArg Fin.val same
  change (Iterate f i.val n + (M : ℤ)).toNat =
    (Iterate f j.val n + (M : ℤ)).toNat at sameCodes
  have iBound := bounded i.val
  have jBound := bounded j.val
  have sameStates : Iterate f i.val n = Iterate f j.val n := by omega
  rcases lt_or_gt_of_ne differentTimes with earlier | earlier
  · refine ⟨i.val, j.val - i.val, by omega, ?_⟩
    have time : i.val + (j.val - i.val) = j.val := by omega
    rw [time]
    exact sameStates.symm
  · refine ⟨j.val, i.val - j.val, by omega, ?_⟩
    have time : j.val + (i.val - j.val) = i.val := by omega
    rw [time]
    exact sameStates

/-- On the integer state space, boundedness and eventual periodicity are equivalent. -/
theorem MagnitudeBoundedIffEventuallyPeriodic (f : ℤ → ℤ) (n : ℤ) :
    MagnitudeBounded f n ↔ EventuallyPeriodic f n :=
  ⟨MagnitudeBoundedEventuallyPeriodic f n, EventuallyPeriodicMagnitudeBounded f n⟩

/-- Common-power compression preserves eventual periodicity for the same signed seed. -/
theorem CompressionEventuallyPeriodic (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (n : ℤ) :
    EventuallyPeriodic (RawStep p) n ↔
      EventuallyPeriodic (RawStep (CompressedParameters p q c)) n := by
  rw [← MagnitudeBoundedIffEventuallyPeriodic, ← MagnitudeBoundedIffEventuallyPeriodic]
  exact CompressionMagnitudeBounded p q c a qFactor cFactor n

/-- Division-closed targets survive every forced division, including signed divisors. -/
theorem DivisionClosedPowerTarget (p : Parameters) (target : ℤ → Prop)
    (divisionClosed : ∀ x : ℤ, p.D ∣ x → target x → target (x / p.D))
    (a : ℕ) (n : ℤ) (atTop : target (p.D ^ a * n)) : target n := by
  revert atTop
  induction a with
  | zero => {
      intro atTop
      simpa using atTop
    }
  | succ a inductionHypothesis => {
      intro atTop
      have divisible : p.D ∣ p.D ^ (a + 1) * n := by
        refine ⟨p.D ^ a * n, ?_⟩
        ring
      have quotient : p.D ^ (a + 1) * n / p.D = p.D ^ a * n := by
        apply Int.ediv_eq_of_eq_mul_left p.DNonzero
        ring
      apply inductionHypothesis
      have descended := divisionClosed _ divisible atTop
      rwa [quotient] at descended
    }

/-- A raw target hit reflects to a compressed hit when the target retains forced divisions. -/
theorem CompressionTargetReflects (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c)
    (target : ℤ → Prop)
    (divisionClosed : ∀ x : ℤ, p.D ∣ x → target x → target (x / p.D)) (n : ℤ)
    (captured : ∃ r : ℕ, target (Iterate (RawStep p) r n)) :
    ∃ k : ℕ, target (Iterate (RawStep (CompressedParameters p q c)) k n) := by
  let g := RawStep (CompressedParameters p q c)
  let clock := CompressionClock p a
  have positive : ∀ x, 1 ≤ clock x := CompressionClockPositive p a
  obtain ⟨r, reached⟩ := captured
  obtain ⟨k, s, _, inside, time⟩ := PositiveClockCover g clock positive n r
  have state : Iterate (RawStep p) r n = Iterate (RawStep p) s (Iterate g k n) := by
    rw [time, IterateAdd, ← CompressionIterates p q c a qFactor cFactor k n]
  rw [state] at reached
  by_cases zeroTime : s = 0
  · refine ⟨k, ?_⟩
    simpa only [zeroTime, Iterate] using reached
  · have sPositive : 0 < s := by omega
    have affineGuard : ¬p.D ∣ Iterate g k n := by
      intro divisible
      change s < CompressionClock p a (Iterate g k n) at inside
      simp only [CompressionClock, if_pos divisible] at inside
      omega
    have clockValue : clock (Iterate g k n) = a + 1 := by
      simp [clock, CompressionClock, affineGuard]
    have sBound : s ≤ a + 1 := by omega
    have intermediate := CompressionAffineIntermediate p q c a s qFactor cFactor
      (Iterate g k n) affineGuard sPositive sBound
    rw [intermediate] at reached
    refine ⟨k + 1, ?_⟩
    exact DivisionClosedPowerTarget p target divisionClosed (a + 1 - s) _ reached

/-- Division-closed targets give equivalent same-seed capture.
Arbitrary targets need not reflect. -/
theorem CompressionCaptureIff (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c)
    (target : ℤ → Prop)
    (divisionClosed : ∀ x : ℤ, p.D ∣ x → target x → target (x / p.D)) (n : ℤ) :
    (∃ r : ℕ, target (Iterate (RawStep p) r n)) ↔
      ∃ k : ℕ, target (Iterate (RawStep (CompressedParameters p q c)) k n) := by
  constructor
  · exact CompressionTargetReflects p q c a qFactor cFactor target divisionClosed n
  · rintro ⟨k, reached⟩
    refine ⟨AccumulatedClock (RawStep (CompressedParameters p q c))
      (CompressionClock p a) k n, ?_⟩
    rwa [← CompressionIterates p q c a qFactor cFactor k n]

/-- The classical target is division-closed, so the scaled family has the same capture problem. -/
theorem CompressionClassicalCaptureIff (p : Parameters) (a : ℕ)
    (divisor : p.D = 2) (qFactor : p.Q = p.D ^ a * 3)
    (cFactor : p.C = p.D ^ a * 1) (n : ℤ) :
    (∃ r : ℕ, Iterate (RawStep p) r n = 1 ∨ Iterate (RawStep p) r n = 2) ↔
      ∃ k : ℕ, Iterate (RawStep (CompressedParameters p 3 1)) k n = 1 ∨
        Iterate (RawStep (CompressedParameters p 3 1)) k n = 2 := by
  apply CompressionCaptureIff p 3 1 a qFactor cFactor (fun x => x = 1 ∨ x = 2)
  intro x divisible reached
  rcases reached with one | two
  · subst x
    norm_num [divisor] at divisible
  · subst x
    left
    norm_num [divisor]

/-- Reaching one is equivalent without changing the classical target to a two-point set. -/
theorem CompressionClassicalCaptureOneIff (p : Parameters) (a : ℕ)
    (divisor : p.D = 2) (qFactor : p.Q = p.D ^ a * 3)
    (cFactor : p.C = p.D ^ a * 1) (n : ℤ) :
    (∃ r : ℕ, Iterate (RawStep p) r n = 1) ↔
      ∃ k : ℕ, Iterate (RawStep (CompressedParameters p 3 1)) k n = 1 := by
  apply CompressionCaptureIff p 3 1 a qFactor cFactor (fun x => x = 1)
  intro x divisible reached
  subst x
  norm_num [divisor] at divisible

/-- A negative-divisor control retains the three-step cycle and its two-step compression. -/
theorem CompressionNegativeDivisorControl :
    Iterate (RawStep { Q := 2, C := 2, D := -2, DAdmissible := by decide }) 3 1 = 1 ∧
      Iterate (RawStep { Q := -1, C := -1, D := -2, DAdmissible := by decide }) 2 1 = 1 ∧
      CompressionAffineCount { Q := 2, C := 2, D := -2, DAdmissible := by decide }
        (-1) (-1) 2 1 = 1 := by
  norm_num [Iterate, RawStep, CompressionAffineCount, CompressedParameters]

/-- An intermediate target need not be visited by the compressed orbit of the same seed. -/
theorem CompressionTargetReflectionNotAutomatic :
    (∃ r : ℕ,
      Iterate (RawStep { Q := 4, C := 4, D := 2, DAdmissible := by decide }) r 1 = 8) ∧
      ¬∃ k : ℕ,
        Iterate (RawStep { Q := 1, C := 1, D := 2, DAdmissible := by decide }) k 1 = 8 := by
  constructor
  · refine ⟨1, ?_⟩
    norm_num [Iterate, RawStep]
  · have stays : ∀ k : ℕ,
        Iterate (RawStep { Q := 1, C := 1, D := 2, DAdmissible := by decide }) k 1 = 1 ∨
          Iterate (RawStep { Q := 1, C := 1, D := 2, DAdmissible := by decide }) k 1 = 2 := by
      intro k
      induction k with
      | zero => {
          exact Or.inl rfl
        }
      | succ k inductionHypothesis => {
          simp only [Iterate]
          rcases inductionHypothesis with one | two
          · rw [one]
            right
            norm_num [RawStep]
          · rw [two]
            left
            norm_num [RawStep]
        }
    rintro ⟨k, reached⟩
    rcases stays k with one | two
    · omega
    · omega


end GeneralizedCollatz
