-- SPDX-License-Identifier: CC-BY-4.0
import CommonBaseRebasing
import AdditiveDivisibleOffset

/-!
Whole-divisor compression removes the multiplier-exponent ordering restriction.
The recovery uses full-time compression, not a one-step state conjugacy.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Euclidean exponent division leaves an admissible high offset for the remainder. -/
theorem WholeBaseRemainderAdmissible (u v a : ℕ) (vPositive : 0 < v)
    (highOffset : u + v ≤ a) :
    u % v < v ∧ u % v + v ≤ a - v * (u / v) ∧ v * (u / v) ≤ a := by
  have reconstruction := Nat.div_add_mod u v
  exact ⟨Nat.mod_lt u vPositive, by omega, by omega⟩

/-- The exact removed divisor power reconstructs both affine coefficients. -/
theorem WholeBaseRemainderCoefficients (t u v a : ℕ) (s : ℤ)
    (highOffset : u + v ≤ a) :
    (t : ℤ) ^ u = ((t : ℤ) ^ v) ^ (u / v) * (t : ℤ) ^ (u % v) ∧
      (t : ℤ) ^ a * s = ((t : ℤ) ^ v) ^ (u / v) *
        ((t : ℤ) ^ (a - v * (u / v)) * s) := by
  have input := Nat.div_add_mod u v
  have capacity : v * (u / v) ≤ a := by omega
  have split : v * (u / v) + (a - v * (u / v)) = a := Nat.add_sub_of_le capacity
  constructor
  · simp only [← pow_mul, ← pow_add, input]
  · simp only [← pow_mul, ← mul_assoc, ← pow_add, split]

/-- Every compressed remainder case escapes, including the signed additive case. -/
theorem WholeBaseRemainderMagnitudeEscapes (p : Parameters) (t u v a : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (vPositive : 0 < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) :
    MagnitudeEscapes
      (RawStep (CompressedParameters p ((t : ℤ) ^ (u % v))
        ((t : ℤ) ^ (a - v * (u / v)) * s))) n := by
  let b := u % v
  let A := a - v * (u / v)
  let g := CompressedParameters p ((t : ℤ) ^ b) ((t : ℤ) ^ A * s)
  have admissible := WholeBaseRemainderAdmissible u v a vPositive highOffset
  have below : b < v := admissible.1
  have high : b + v ≤ A := admissible.2.1
  have gDivisor : g.D = (t : ℤ) ^ v := divisor
  have gOffset : g.C = (t : ℤ) ^ A * s := rfl
  -- A zero remainder leaves q=1 and a divisor-multiple nonzero offset.
  by_cases zero : b = 0
  · have dLower : 2 ≤ t ^ v := by
      have powers := WholeBasePowerRank t v tLower
      omega
    have gDivisorNat : g.D = ((t ^ v : ℕ) : ℤ) := by
      simpa only [Nat.cast_pow] using gDivisor
    have gMultiplier : g.Q = 1 := by simp [g, CompressedParameters, zero]
    have vBelow : v ≤ A := by omega
    have split : v + (A - v) = A := Nat.add_sub_of_le vBelow
    have offsetDivides : g.D ∣ g.C := by
      refine ⟨(t : ℤ) ^ (A - v) * s, ?_⟩
      rw [gOffset, gDivisor]
      simp only [← mul_assoc, ← pow_add, split]
    have offsetNonzero : g.C ≠ 0 := by
      rw [gOffset]
      exact mul_ne_zero (pow_ne_zero _ (by omega : (t : ℤ) ≠ 0)) sNonzero
    exact AdditiveDivisibleOffsetMagnitudeEscapes g (t ^ v) n dLower gDivisorNat
      gMultiplier offsetDivides offsetNonzero nNonzero
  · have positive : 0 < b := Nat.pos_of_ne_zero zero
    exact WholeBaseHighOffsetMagnitudeEscapesRebased g t b v A s n
      tLower positive below high gDivisor rfl gOffset sNonzero nNonzero

/-- Full-time recovery gives escape without any ordering or coprimality of exponents. -/
theorem WholeBaseGeneralHighOffsetMagnitudeEscapes (p : Parameters) (t u v a : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (_uPositive : 0 < u) (vPositive : 0 < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) : MagnitudeEscapes (RawStep p) n := by
  rcases WholeBaseRemainderCoefficients t u v a s highOffset with ⟨left, right⟩
  have qFactor : p.Q = p.D ^ (u / v) * (t : ℤ) ^ (u % v) := by
    rw [divisor, multiplier]
    exact left
  have cFactor : p.C = p.D ^ (u / v) * ((t : ℤ) ^ (a - v * (u / v)) * s) := by
    rw [divisor, offset]
    exact right
  apply (CompressionMagnitudeEscapes p ((t : ℤ) ^ (u % v))
    ((t : ℤ) ^ (a - v * (u / v)) * s) (u / v) qFactor cFactor n).2
  exact WholeBaseRemainderMagnitudeEscapes p t u v a s n tLower vPositive highOffset
    divisor sNonzero nNonzero

/-- This finite threshold covers the additive and positive remainder cases separately. -/
def WholeBaseRemainderBudget (p : Parameters) (u v : ℕ) (n : ℤ) (M : ℕ) : ℕ :=
  if u % v = 0 then 2 * n.natAbs + M + 1
  else n.natAbs +
    (n.natAbs + 1 + M * (p.D ^ ((u % v) / Nat.gcd (u % v) v)).natAbs) *
      ((u % v) / Nat.gcd (u % v) v + v / Nat.gcd (u % v) v)

/-- The compressed raw threshold controls both magnitude and the original offset sign. -/
theorem WholeBaseRemainderRawBudget (p : Parameters) (t u v a : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (vPositive : 0 < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) :
    ∀ M r : ℕ, WholeBaseRemainderBudget p u v n M ≤ r →
      0 < s * Iterate
        (RawStep (CompressedParameters p ((t : ℤ) ^ (u % v))
          ((t : ℤ) ^ (a - v * (u / v)) * s))) r n ∧
      M < (Iterate
        (RawStep (CompressedParameters p ((t : ℤ) ^ (u % v))
          ((t : ℤ) ^ (a - v * (u / v)) * s))) r n).natAbs := by
  let b := u % v
  let A := a - v * (u / v)
  let g := CompressedParameters p ((t : ℤ) ^ b) ((t : ℤ) ^ A * s)
  have admissible := WholeBaseRemainderAdmissible u v a vPositive highOffset
  have below : b < v := admissible.1
  have high : b + v ≤ A := admissible.2.1
  have gDivisor : g.D = (t : ℤ) ^ v := divisor
  have gOffset : g.C = (t : ℤ) ^ A * s := rfl
  intro M r after
  change (if b = 0 then 2 * n.natAbs + M + 1 else n.natAbs +
    (n.natAbs + 1 + M * (p.D ^ (b / Nat.gcd b v)).natAbs) *
      (b / Nat.gcd b v + v / Nat.gcd b v)) ≤ r at after
  by_cases zero : b = 0
  · rw [if_pos zero] at after
    have dLower : 2 ≤ t ^ v := by
      have powers := WholeBasePowerRank t v tLower
      omega
    have gDivisorNat : g.D = ((t ^ v : ℕ) : ℤ) := by
      simpa only [Nat.cast_pow] using gDivisor
    have gMultiplier : g.Q = 1 := by simp [g, CompressedParameters, zero]
    have vBelow : v ≤ A := by omega
    have split : v + (A - v) = A := Nat.add_sub_of_le vBelow
    have offsetDivides : g.D ∣ g.C := by
      refine ⟨(t : ℤ) ^ (A - v) * s, ?_⟩
      rw [gOffset, gDivisor]
      simp only [← mul_assoc, ← pow_add, split]
    have factorPositive : 0 < (t : ℤ) ^ A := pow_pos (by omega) _
    have offsetNonzero : g.C ≠ 0 := by
      rw [gOffset]
      exact mul_ne_zero (ne_of_gt factorPositive) sNonzero
    have result := AdditiveDivisibleOffsetRawBudget g (t ^ v) n dLower gDivisorNat
      gMultiplier offsetDivides offsetNonzero nNonzero M r after
    have product : 0 < (t : ℤ) ^ A * (s * Iterate (RawStep g) r n) := by
      simpa only [gOffset, mul_assoc] using result.1
    exact ⟨pos_of_mul_pos_right product (le_of_lt factorPositive), result.2⟩
  · rw [if_neg zero] at after
    have positive : 0 < b := Nat.pos_of_ne_zero zero
    have magnitude := WholeBaseHighOffsetRawEscapeRebased g t b v A s n
      tLower positive below high gDivisor rfl gOffset sNonzero nNonzero M r after
    obtain ⟨cutoff, cutoffBound, aligned⟩ :=
      WholeBaseHighOffsetEventuallyAlignedRebased g t b v A s n
        tLower positive below high gDivisor rfl gOffset sNonzero nNonzero
    have budgetComparison := Nat.mul_le_mul_right
      (b / Nat.gcd b v + v / Nat.gcd b v)
      (show n.natAbs + 1 ≤ n.natAbs + 1 +
        M * (p.D ^ (b / Nat.gcd b v)).natAbs by omega)
    exact ⟨aligned r (by omega), magnitude⟩

/-- Uniform compression-clock bounds turn the compressed threshold into an all-raw bound. -/
theorem WholeBaseGeneralHighOffsetRawBudget (p : Parameters) (t u v a : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (_uPositive : 0 < u) (vPositive : 0 < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) :
    ∀ M r : ℕ, WholeBaseRemainderBudget p u v n M * (u / v + 1) ≤ r →
      M < (Iterate (RawStep p) r n).natAbs := by
  let q := (t : ℤ) ^ (u % v)
  let c := (t : ℤ) ^ (a - v * (u / v)) * s
  let g := RawStep (CompressedParameters p q c)
  let clock := CompressionClock p (u / v)
  rcases WholeBaseRemainderCoefficients t u v a s highOffset with ⟨left, right⟩
  have qFactor : p.Q = p.D ^ (u / v) * q := by rw [divisor, multiplier]; exact left
  have cFactor : p.C = p.D ^ (u / v) * c := by rw [divisor, offset]; exact right
  have positive : ∀ x, 1 ≤ clock x := CompressionClockPositive p (u / v)
  intro M r after
  let K := WholeBaseRemainderBudget p u v n M
  have clockBound := BoundedClockTotal g clock (u / v + 1)
    (CompressionClockUpper p (u / v)) n K
  have rAfter : AccumulatedClock g clock K n ≤ r := clockBound.trans after
  obtain ⟨k, j, _, inside, time⟩ := PositiveClockCover g clock positive n r
  have kAfter := PositiveClockCoverAfter g clock positive n r k j K inside time rAfter
  have sampled := CompressionIterates p q c (u / v) qFactor cFactor k n
  have state : Iterate (RawStep p) r n = Iterate (RawStep p) j (Iterate g k n) := by
    rw [time, IterateAdd, ← sampled]
  rw [state]
  have bounds := CompressionBlockMagnitudeBounds p q c (u / v) j qFactor cFactor
    (Iterate g k n) inside
  have leftBeyond := (WholeBaseRemainderRawBudget p t u v a s n tLower vPositive
    highOffset divisor sNonzero nNonzero M k kAfter).2
  have rightBeyond : M < (RawStep (CompressedParameters p q c) (Iterate g k n)).natAbs :=
    (WholeBaseRemainderRawBudget p t u v a s n tLower vPositive
      highOffset divisor sNonzero nNonzero M (k + 1) (by omega)).2
  exact lt_of_lt_of_le (lt_min leftBeyond rightBeyond) bounds.1

/-- A sampled aligned state and the positive raw sign invariant give an effective sign cutoff. -/
theorem WholeBaseGeneralHighOffsetEventuallyAligned (p : Parameters) (t u v a : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (_uPositive : 0 < u) (vPositive : 0 < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) :
    ∃ cutoff : ℕ, cutoff ≤ WholeBaseRemainderBudget p u v n 0 * (u / v + 1) ∧
      ∀ r : ℕ, cutoff ≤ r → 0 < s * Iterate (RawStep p) r n := by
  let q := (t : ℤ) ^ (u % v)
  let c := (t : ℤ) ^ (a - v * (u / v)) * s
  let g := RawStep (CompressedParameters p q c)
  let clock := CompressionClock p (u / v)
  let K := WholeBaseRemainderBudget p u v n 0
  let cutoff := AccumulatedClock g clock K n
  rcases WholeBaseRemainderCoefficients t u v a s highOffset with ⟨left, right⟩
  have qFactor : p.Q = p.D ^ (u / v) * q := by rw [divisor, multiplier]; exact left
  have cFactor : p.C = p.D ^ (u / v) * c := by rw [divisor, offset]; exact right
  have clockBound := BoundedClockTotal g clock (u / v + 1)
    (CompressionClockUpper p (u / v)) n K
  have sampled := CompressionIterates p q c (u / v) qFactor cFactor K n
  have aligned : 0 < s * Iterate (RawStep p) cutoff n := by
    rw [← sampled]
    exact (WholeBaseRemainderRawBudget p t u v a s n tLower vPositive highOffset
      divisor sNonzero nNonzero 0 K (Nat.le_refl _)).1
  refine ⟨cutoff, clockBound, ?_⟩
  intro r after
  have invariant := WholeBaseHighOffsetSignInvariant p t u v a s
    (Iterate (RawStep p) cutoff n) tLower divisor multiplier offset aligned (r - cutoff)
  rw [← IterateAdd, Nat.add_sub_of_le after] at invariant
  exact invariant

/-- Full-sequence escape excludes every nonzero return in the unrestricted exponent family. -/
theorem WholeBaseGeneralHighOffsetNoNonzeroReturn (p : Parameters) (t u v a : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (uPositive : 0 < u) (vPositive : 0 < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) (h : ℕ) (hPositive : 0 < h) :
    Iterate (RawStep p) h n ≠ n := by
  intro returned
  have escaped := WholeBaseGeneralHighOffsetMagnitudeEscapes p t u v a s n tLower
    uPositive vPositive highOffset divisor multiplier offset sNonzero nNonzero
  obtain ⟨R, late⟩ := escaped n.natAbs
  have repeated := IterateReturnMultiple (RawStep p) n h (R + 1) returned
  have after : R ≤ h * (R + 1) := by
    have growth := Nat.le_mul_of_pos_left (R + 1) hPositive
    omega
  have contradiction := late (h * (R + 1)) after
  rw [repeated] at contradiction
  exact (Nat.lt_irrefl _ contradiction)

/-- Zero remains fixed and is the only periodic point for arbitrary positive exponents. -/
theorem WholeBaseGeneralHighOffsetPeriodicIffZero (p : Parameters) (t u v a : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (uPositive : 0 < u) (vPositive : 0 < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) : PeriodicPoint (RawStep p) n ↔ n = 0 := by
  constructor
  · rintro ⟨h, positive, returned⟩
    by_contra nonzero
    exact WholeBaseGeneralHighOffsetNoNonzeroReturn p t u v a s n tLower uPositive
      vPositive highOffset divisor multiplier offset sNonzero nonzero h positive returned
  · intro zero
    subst n
    refine ⟨1, by decide, ?_⟩
    simp [Iterate, RawStep]

/-- Removing a positive whole-divisor power strictly lowers the actual coefficient height. -/
theorem WholeBaseGeneralCompressionHeightDecrease (p : Parameters) (t u v a : ℕ)
    (s : ℤ) (tLower : 2 ≤ t) (vPositive : 0 < v) (uAbove : v ≤ u)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s) :
    CoefficientHeight ((t : ℤ) ^ (u % v)) ((t : ℤ) ^ (a - v * (u / v)) * s) <
      CoefficientHeight p.Q p.C := by
  rcases WholeBaseRemainderCoefficients t u v a s highOffset with ⟨left, right⟩
  have qFactor : p.Q = p.D ^ (u / v) * (t : ℤ) ^ (u % v) := by
    rw [divisor, multiplier]
    exact left
  have cFactor : p.C = p.D ^ (u / v) * ((t : ℤ) ^ (a - v * (u / v)) * s) := by
    rw [divisor, offset]
    exact right
  have removedPositive : 0 < u / v := Nat.div_pos uAbove vPositive
  have qNonzero : (t : ℤ) ^ (u % v) ≠ 0 := pow_ne_zero _ (by omega)
  exact CompressionHeightStrict p _ _ (u / v) qFactor cFactor removedPositive
    (Or.inl qNonzero)

end GeneralizedCollatz
