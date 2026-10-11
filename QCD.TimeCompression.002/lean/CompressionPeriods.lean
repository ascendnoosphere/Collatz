-- SPDX-License-Identifier: CC-BY-4.0
import CompressionOutcomes

/-!
Primitive periods and affine-phase recovery for time compression.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- One return witness propagates to every phase of the same orbit. -/
theorem ReturnPeriodPropagates {α : Type*} (f : α → α) (h k : ℕ) (n : α)
    (returned : Iterate f h n = n) : Iterate f h (Iterate f k n) = Iterate f k n := by
  calc
    Iterate f h (Iterate f k n) = Iterate f (k + h) n := (IterateAdd f k h n).symm
    _ = Iterate f (h + k) n := by rw [Nat.add_comm]
    _ = Iterate f k (Iterate f h n) := IterateAdd f h k n
    _ = Iterate f k n := by rw [returned]

/-- Two points with a common positive return period have unique predecessors. -/
theorem CommonReturnStepInjective {α : Type*} (f : α → α) (h : ℕ) (x y : α)
    (hPositive : 0 < h) (xReturn : Iterate f h x = x) (yReturn : Iterate f h y = y)
    (sameNext : f x = f y) : x = y := by
  have time : h - 1 + 1 = h := by omega
  have continued := congrArg (Iterate f (h - 1)) sameNext
  rw [IterateFirst, IterateFirst, time, xReturn, yReturn] at continued
  exact continued

/-- An affine image cannot have a divisor-power predecessor on the same periodic orbit. -/
theorem PeriodicAffineImageHasNoPeriodicPower (p : Parameters) (r h k : ℕ) (n : ℤ)
    (rPositive : 0 < r) (hPositive : 0 < h)
    (returned : Iterate (RawStep p) h n = n)
    (affineGuard : ¬p.D ∣ Iterate (RawStep p) k n) :
    n ≠ p.D ^ r * RawStep p (Iterate (RawStep p) k n) := by
  intro atPower
  have exponent : r - (r - 1) = 1 := by omega
  have stage : Iterate (RawStep p) (r - 1) n =
      p.D * RawStep p (Iterate (RawStep p) k n) := by
    calc
      Iterate (RawStep p) (r - 1) n = Iterate (RawStep p) (r - 1)
          (p.D ^ r * RawStep p (Iterate (RawStep p) k n)) :=
        congrArg (Iterate (RawStep p) (r - 1)) atPower
      _ = p.D ^ (r - (r - 1)) * RawStep p (Iterate (RawStep p) k n) :=
        PowerDivisionPrefix p r (r - 1) _ (by omega)
      _ = p.D * RawStep p (Iterate (RawStep p) k n) := by rw [exponent, pow_one]
  have stageDivisible : p.D ∣ Iterate (RawStep p) (r - 1) n := by
    exact ⟨RawStep p (Iterate (RawStep p) k n), stage⟩
  have sameNext : RawStep p (Iterate (RawStep p) (r - 1) n) =
      RawStep p (Iterate (RawStep p) k n) := by
    calc
      RawStep p (Iterate (RawStep p) (r - 1) n) =
          Iterate (RawStep p) (r - 1) n / p.D := by
        simp only [RawStep, if_pos stageDivisible]
      _ = RawStep p (Iterate (RawStep p) k n) := by
        apply Int.ediv_eq_of_eq_mul_left p.DNonzero
        rw [stage]
        ring
  have samePoints := CommonReturnStepInjective (RawStep p) h
    (Iterate (RawStep p) (r - 1) n) (Iterate (RawStep p) k n) hPositive
    (ReturnPeriodPropagates (RawStep p) h (r - 1) n returned)
    (ReturnPeriodPropagates (RawStep p) h k n returned) sameNext
  exact affineGuard (samePoints ▸ stageDivisible)

/-- A periodic compressed seed is never an interior point of any of its affine blocks. -/
theorem CompressionPeriodicSeedNoInterior (p : Parameters) (q c : ℤ) (a h k s : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (n : ℤ)
    (hPositive : 0 < h)
    (returned : Iterate (RawStep (CompressedParameters p q c)) h n = n)
    (sPositive : 0 < s)
    (inside : s < CompressionClock p a
      (Iterate (RawStep (CompressedParameters p q c)) k n)) :
    Iterate (RawStep p) s (Iterate (RawStep (CompressedParameters p q c)) k n) ≠ n := by
  intro interiorReturn
  have affineGuard : ¬p.D ∣ Iterate (RawStep (CompressedParameters p q c)) k n := by
    intro divisible
    simp only [CompressionClock, if_pos divisible] at inside
    omega
  have clockValue : CompressionClock p a
      (Iterate (RawStep (CompressedParameters p q c)) k n) = a + 1 := by
    simp [CompressionClock, affineGuard]
  have sBound : s ≤ a + 1 := by omega
  have exponentPositive : 0 < a + 1 - s := by omega
  have intermediate := CompressionAffineIntermediate p q c a s qFactor cFactor
    (Iterate (RawStep (CompressedParameters p q c)) k n) affineGuard sPositive sBound
  have atPower : n = p.D ^ (a + 1 - s) * RawStep (CompressedParameters p q c)
      (Iterate (RawStep (CompressedParameters p q c)) k n) :=
    interiorReturn.symm.trans intermediate
  exact PeriodicAffineImageHasNoPeriodicPower (CompressedParameters p q c)
    (a + 1 - s) h k n exponentPositive hPositive returned affineGuard atPower

/-- Every raw return of a periodic compressed seed is an exact clock boundary. -/
theorem CompressionRawReturnBoundary (p : Parameters) (q c : ℤ) (a h r : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (n : ℤ)
    (hPositive : 0 < h)
    (compressedReturn : Iterate (RawStep (CompressedParameters p q c)) h n = n)
    (rawReturn : Iterate (RawStep p) r n = n) :
    ∃ k : ℕ, k ≤ r ∧ AccumulatedClock (RawStep (CompressedParameters p q c))
      (CompressionClock p a) k n = r ∧
      Iterate (RawStep (CompressedParameters p q c)) k n = n := by
  let g := RawStep (CompressedParameters p q c)
  let clock := CompressionClock p a
  obtain ⟨k, s, kBound, inside, time⟩ :=
    PositiveClockCover g clock (CompressionClockPositive p a) n r
  have state : Iterate (RawStep p) r n = Iterate (RawStep p) s (Iterate g k n) := by
    rw [time, IterateAdd, ← CompressionIterates p q c a qFactor cFactor k n]
  have interiorReturn := state.symm.trans rawReturn
  by_cases zeroTime : s = 0
  · refine ⟨k, kBound, ?_, ?_⟩
    · change AccumulatedClock g clock k n = r
      omega
    · simpa only [zeroTime, Iterate] using interiorReturn
  · have sPositive : 0 < s := by omega
    exact False.elim (CompressionPeriodicSeedNoInterior p q c a h k s qFactor cFactor n
      hPositive compressedReturn sPositive inside interiorReturn)

/-- A primitive return is the least positive return of the stated seed. -/
def PrimitiveReturn {α : Type*} (f : α → α) (n : α) (h : ℕ) : Prop :=
  0 < h ∧ Iterate f h n = n ∧
    ∀ r : ℕ, 0 < r → Iterate f r n = n → h ≤ r

/-- Expansion preserves primitiveness, since every shorter raw return is a clock boundary. -/
theorem CompressionPrimitiveReturn (p : Parameters) (q c : ℤ) (a h : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (n : ℤ)
    (primitive : PrimitiveReturn (RawStep (CompressedParameters p q c)) n h) :
    PrimitiveReturn (RawStep p) n
      (AccumulatedClock (RawStep (CompressedParameters p q c)) (CompressionClock p a) h n) := by
  obtain ⟨hPositive, returned, least⟩ := primitive
  let g := RawStep (CompressedParameters p q c)
  let clock := CompressionClock p a
  have positive : ∀ x, 1 ≤ clock x := CompressionClockPositive p a
  have clockLower := AccumulatedClockLower g clock positive h n
  refine ⟨lt_of_lt_of_le hPositive clockLower, ?_, ?_⟩
  · rwa [← CompressionIterates p q c a qFactor cFactor h n]
  · intro r rPositive rawReturn
    obtain ⟨k, _, time, compressedReturn⟩ :=
      CompressionRawReturnBoundary p q c a h r qFactor cFactor n hPositive returned rawReturn
    have kPositive : 0 < k := by
      by_contra zeroIndex
      have zeroTime : k = 0 := by omega
      simp only [zeroTime, AccumulatedClock] at time
      omega
    have hBefore : h ≤ k := least k kPositive compressedReturn
    have clocksBefore := (PositiveClockStrictMono g clock positive n).monotone hBefore
    exact time ▸ clocksBefore

/-- A primitive expanded return cannot come from a nonprimitive compressed return. -/
theorem CompressionPrimitiveReflects (p : Parameters) (q c : ℤ) (a h : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (n : ℤ)
    (primitive : PrimitiveReturn (RawStep p) n
      (AccumulatedClock (RawStep (CompressedParameters p q c)) (CompressionClock p a) h n)) :
    PrimitiveReturn (RawStep (CompressedParameters p q c)) n h := by
  obtain ⟨clockPositive, rawReturn, least⟩ := primitive
  let g := RawStep (CompressedParameters p q c)
  let clock := CompressionClock p a
  have positive : ∀ x, 1 ≤ clock x := CompressionClockPositive p a
  have hPositive : 0 < h := by
    by_contra zeroIndex
    have zeroTime : h = 0 := by omega
    simp only [zeroTime, AccumulatedClock] at clockPositive
    omega
  refine ⟨hPositive, ?_, ?_⟩
  · rwa [CompressionIterates p q c a qFactor cFactor h n]
  · intro r rPositive returned
    have clockLower := AccumulatedClockLower g clock positive r n
    have rClockPositive : 0 < AccumulatedClock g clock r n := by omega
    have expandedReturn : Iterate (RawStep p) (AccumulatedClock g clock r n) n = n := by
      rwa [← CompressionIterates p q c a qFactor cFactor r n]
    have clocksBefore : AccumulatedClock g clock h n ≤ AccumulatedClock g clock r n :=
      least _ rClockPositive expandedReturn
    by_contra earlier
    have rBefore : r < h := by omega
    have strict : AccumulatedClock g clock r n < AccumulatedClock g clock h n :=
      PositiveClockStrictMono g clock positive n rBefore
    omega

/-- The primitive raw period is the primitive compressed period plus the forced divisions. -/
theorem CompressionPrimitivePeriodFormula (p : Parameters) (q c : ℤ) (a h : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (n : ℤ) :
    PrimitiveReturn (RawStep (CompressedParameters p q c)) n h ↔
      PrimitiveReturn (RawStep p) n (h + a * CompressionAffineCount p q c h n) := by
  rw [← CompressionClockTotal]
  exact ⟨CompressionPrimitiveReturn p q c a h qFactor cFactor n,
    CompressionPrimitiveReflects p q c a h qFactor cFactor n⟩

/-- Every positive-time interior state of an affine block still carries a divisor factor. -/
theorem CompressionInteriorDivisible (p : Parameters) (q c : ℤ) (a s : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (n : ℤ)
    (sPositive : 0 < s) (inside : s < CompressionClock p a n) :
    p.D ∣ Iterate (RawStep p) s n := by
  have affineGuard : ¬p.D ∣ n := by
    intro divisible
    simp only [CompressionClock, if_pos divisible] at inside
    omega
  have clockValue : CompressionClock p a n = a + 1 := by
    simp [CompressionClock, affineGuard]
  have sBound : s ≤ a + 1 := by omega
  have exponent : a + 1 - s = a - s + 1 := by omega
  refine ⟨p.D ^ (a - s) * RawStep (CompressedParameters p q c) n, ?_⟩
  rw [CompressionAffineIntermediate p q c a s qFactor cFactor n affineGuard sPositive sBound,
    exponent, pow_succ]
  ring

/-- A nondivisible raw cycle phase necessarily returns at a compressed clock boundary. -/
theorem CompressionAffineRawReturnBoundary (p : Parameters) (q c : ℤ) (a r : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (n : ℤ)
    (affineGuard : ¬p.D ∣ n) (rawReturn : Iterate (RawStep p) r n = n) :
    ∃ k : ℕ, k ≤ r ∧ AccumulatedClock (RawStep (CompressedParameters p q c))
      (CompressionClock p a) k n = r ∧
      Iterate (RawStep (CompressedParameters p q c)) k n = n := by
  let g := RawStep (CompressedParameters p q c)
  let clock := CompressionClock p a
  obtain ⟨k, s, kBound, inside, time⟩ :=
    PositiveClockCover g clock (CompressionClockPositive p a) n r
  have state : Iterate (RawStep p) r n = Iterate (RawStep p) s (Iterate g k n) := by
    rw [time, IterateAdd, ← CompressionIterates p q c a qFactor cFactor k n]
  have interiorReturn := state.symm.trans rawReturn
  by_cases zeroTime : s = 0
  · refine ⟨k, kBound, ?_, ?_⟩
    · change AccumulatedClock g clock k n = r
      omega
    · simpa only [zeroTime, Iterate] using interiorReturn
  · have sPositive : 0 < s := by omega
    have divided := CompressionInteriorDivisible p q c a s qFactor cFactor
      (Iterate g k n) sPositive inside
    exact False.elim (affineGuard (interiorReturn ▸ divided))

/-- A closed orbit consisting entirely of divisions has only the zero state. -/
theorem RawAllDivisionReturnZero (p : Parameters) (h : ℕ) (n : ℤ)
    (hPositive : 0 < h) (returned : Iterate (RawStep p) h n = n)
    (divisions : ∀ k : ℕ, k < h → p.D ∣ Iterate (RawStep p) k n) : n = 0 := by
  have balance : ∀ k : ℕ, k ≤ h → p.D ^ k * Iterate (RawStep p) k n = n := by
    intro k
    induction k with
    | zero => {
        intro kBound
        simp [Iterate]
      }
    | succ k inductionHypothesis => {
        intro kBound
        have kEarlier : k < h := by omega
        have divisible := divisions k kEarlier
        have cancellation : p.D * Iterate (RawStep p) (k + 1) n =
            Iterate (RawStep p) k n := by
          simp only [Iterate, RawStep, if_pos divisible]
          exact Int.mul_ediv_cancel' divisible
        calc
          p.D ^ (k + 1) * Iterate (RawStep p) (k + 1) n =
              p.D ^ k * (p.D * Iterate (RawStep p) (k + 1) n) := by ring
          _ = p.D ^ k * Iterate (RawStep p) k n := by rw [cancellation]
          _ = n := inductionHypothesis (by omega)
      }
  have fixed : p.D ^ h * n = n := by
    simpa only [returned] using balance h (Nat.le_refl h)
  have productZero : (p.D ^ h - 1) * n = 0 := by
    calc
      (p.D ^ h - 1) * n = p.D ^ h * n - n := by ring
      _ = 0 := by rw [fixed]; simp
  rcases mul_eq_zero.mp productZero with factorZero | seedZero
  · have powerOne : p.D ^ h = 1 := by omega
    have absOne : p.D.natAbs ^ h = 1 := by
      have sameMagnitude := congrArg Int.natAbs powerOne
      simpa only [Int.natAbs_pow, Int.natAbs_one] using sameMagnitude
    have powerLarge := Nat.one_lt_pow (Nat.ne_of_gt hPositive)
      (lt_of_lt_of_le Nat.one_lt_two p.DAdmissible)
    omega
  · exact seedZero

/-- Every nonzero raw cycle has a legal affine phase, without a coprimality assumption. -/
theorem RawNonzeroReturnHasAffinePhase (p : Parameters) (h : ℕ) (n : ℤ)
    (hPositive : 0 < h) (returned : Iterate (RawStep p) h n = n) (nNonzero : n ≠ 0) :
    ∃ k : ℕ, k < h ∧ ¬p.D ∣ Iterate (RawStep p) k n := by
  by_contra noAffine
  have divisions : ∀ k : ℕ, k < h → p.D ∣ Iterate (RawStep p) k n := by
    intro k kBound
    by_contra affine
    exact noAffine ⟨k, kBound, affine⟩
  exact nNonzero (RawAllDivisionReturnZero p h n hPositive returned divisions)

/-- Primitive period is preserved by a phase shift within one complete raw cycle. -/
theorem PrimitiveReturnShift {α : Type*} (f : α → α) (n : α) (h k : ℕ)
    (kBound : k ≤ h) (primitive : PrimitiveReturn f n h) :
    PrimitiveReturn f (Iterate f k n) h := by
  obtain ⟨hPositive, returned, least⟩ := primitive
  have recovered : Iterate f (h - k) (Iterate f k n) = n := by
    rw [← IterateAdd, Nat.add_sub_of_le kBound, returned]
  refine ⟨hPositive, ReturnPeriodPropagates f h k n returned, ?_⟩
  intro r rPositive phaseReturn
  have originalReturn := ReturnPeriodPropagates f r (h - k) (Iterate f k n) phaseReturn
  rw [recovered] at originalReturn
  exact least r rPositive originalReturn

/-- Every nonzero primitive raw cycle recovers a primitive compressed cycle at an affine phase. -/
theorem CompressionNonzeroPrimitiveCycleRecovery (p : Parameters) (q c : ℤ) (a h : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (n : ℤ)
    (nNonzero : n ≠ 0) (primitive : PrimitiveReturn (RawStep p) n h) :
    ∃ k : ℕ, k < h ∧ ¬p.D ∣ Iterate (RawStep p) k n ∧ ∃ r : ℕ,
      PrimitiveReturn (RawStep (CompressedParameters p q c)) (Iterate (RawStep p) k n) r ∧
      h = r + a * CompressionAffineCount p q c r (Iterate (RawStep p) k n) := by
  obtain ⟨k, kBound, affineGuard⟩ :=
    RawNonzeroReturnHasAffinePhase p h n primitive.1 primitive.2.1 nNonzero
  have phasePrimitive := PrimitiveReturnShift (RawStep p) n h k (Nat.le_of_lt kBound) primitive
  obtain ⟨r, _, time, returned⟩ := CompressionAffineRawReturnBoundary p q c a h
    qFactor cFactor (Iterate (RawStep p) k n) affineGuard phasePrimitive.2.1
  have expandedPrimitive : PrimitiveReturn (RawStep p) (Iterate (RawStep p) k n)
      (AccumulatedClock (RawStep (CompressedParameters p q c)) (CompressionClock p a) r
        (Iterate (RawStep p) k n)) := by
    rw [time]
    exact phasePrimitive
  refine ⟨k, kBound, affineGuard,
    r, CompressionPrimitiveReflects p q c a r qFactor cFactor _ expandedPrimitive, ?_⟩
  exact time.symm.trans (CompressionClockTotal p q c a r (Iterate (RawStep p) k n))

/-- The zero boundary has primitive raw period one for every admissible parameter triple. -/
theorem RawZeroPrimitivePeriod (p : Parameters) : PrimitiveReturn (RawStep p) 0 1 := by
  refine ⟨by decide, ?_, ?_⟩
  · simp [RawStep, Iterate]
  · intro r rPositive _
    omega


end GeneralizedCollatz
