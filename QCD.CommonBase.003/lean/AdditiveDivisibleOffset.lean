-- SPDX-License-Identifier: CC-BY-4.0
import CommonBaseHighOffsetNormalization

/-!
Signed affine tails for q = 1 and offsets divisible by the positive divisor.
These results supply the zero-remainder child of whole-divisor compression.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Divisor-free states remain divisor-free under every integral offset translate. -/
theorem AdditiveDivisibleOffsetRawRay (p : Parameters) (x : ℤ)
    (multiplier : p.Q = 1) (offsetDivides : p.D ∣ p.C) (guard : ¬p.D ∣ x) :
    ∀ r : ℕ, Iterate (RawStep p) r x = x + (r : ℤ) * p.C := by
  rcases offsetDivides with ⟨z, offset⟩
  -- A divisible translate would reconstruct a divisor of the original state.
  have invisible : ∀ r : ℕ, ¬p.D ∣ x + (r : ℤ) * p.C := by
    intro r collision
    rcases collision with ⟨y, equation⟩
    apply guard
    refine ⟨y - (r : ℤ) * z, ?_⟩
    calc
      x = p.D * y - (r : ℤ) * p.C := by linarith [equation]
      _ = p.D * (y - (r : ℤ) * z) := by rw [offset]; ring
  intro r
  induction r with
  | zero => { simp [Iterate] }
  | succ r ih => {
      rw [Iterate, ih, RawStep, if_neg (invisible r), multiplier]
      push_cast
      ring
    }

/-- Legal initial divisions recover a permanent affine tail with explicit bounds. -/
theorem AdditiveDivisibleOffsetNormalForm (p : Parameters) (d : ℕ) (n : ℤ)
    (dLower : 2 ≤ d) (divisor : p.D = (d : ℤ)) (multiplier : p.Q = 1)
    (offsetDivides : p.D ∣ p.C) (nonzero : n ≠ 0) :
    ∃ start : ℕ, ∃ x : ℤ, start ≤ n.natAbs ∧ x.natAbs ≤ n.natAbs ∧
      ¬p.D ∣ x ∧ ∀ r : ℕ, Iterate (RawStep p) (start + r) n = x + (r : ℤ) * p.C := by
  have divisorPower : p.D = (d : ℤ) ^ 1 := by simpa using divisor
  obtain ⟨start, k, x, startBound, phase, reached, atOrder, magnitude⟩ :=
    WholeBaseNormalizeRaw p d 1 n dLower (by decide) divisorPower nonzero
  have phaseZero : k = 0 := by omega
  rcases atOrder with ⟨w, state, guard⟩
  have residual : x = w := by simpa [phaseZero] using state
  have invisible : ¬p.D ∣ x := by rw [divisor, residual]; exact guard
  refine ⟨start, x, startBound, magnitude, invisible, ?_⟩
  intro r
  rw [IterateAdd, reached]
  exact AdditiveDivisibleOffsetRawRay p x multiplier offsetDivides invisible r

/-- An integral nonzero translation crosses the origin with a uniform late bound. -/
theorem IntegralAffineTailLateBound (x c : ℤ) (M r : ℕ) (cNonzero : c ≠ 0)
    (after : x.natAbs + 1 + M ≤ r) :
    0 < c * (x + (r : ℤ) * c) ∧ M < (x + (r : ℤ) * c).natAbs := by
  have indexNonnegative : (0 : ℤ) ≤ r := by omega
  have indexBound : (x.natAbs : ℤ) + 1 + (M : ℤ) ≤ r := by exact_mod_cast after
  -- Integrality makes a nonzero positive or negative increment at least one in magnitude.
  by_cases positive : 0 < c
  · have coefficient : (1 : ℤ) ≤ c := by omega
    have scaled : (r : ℤ) ≤ (r : ℤ) * c := by
      simpa using mul_le_mul_of_nonneg_left coefficient indexNonnegative
    have initial : -(x.natAbs : ℤ) ≤ x := by
      simpa [Int.natCast_natAbs] using neg_abs_le x
    have late : (M : ℤ) < x + (r : ℤ) * c := by omega
    have statePositive : 0 < x + (r : ℤ) * c := by omega
    refine ⟨mul_pos positive statePositive, ?_⟩
    have magnitude : (M : ℤ) < ((x + (r : ℤ) * c).natAbs : ℤ) := by
      rw [Int.natAbs_of_nonneg (le_of_lt statePositive)]
      exact late
    exact_mod_cast magnitude
  · have negative : c < 0 := by omega
    have coefficient : c ≤ (-1 : ℤ) := by omega
    have scaled : (r : ℤ) * c ≤ -(r : ℤ) := by
      simpa using mul_le_mul_of_nonneg_left coefficient indexNonnegative
    have initial : x ≤ (x.natAbs : ℤ) := Int.le_natAbs
    have late : x + (r : ℤ) * c < -(M : ℤ) := by omega
    have stateNegative : x + (r : ℤ) * c < 0 := by omega
    refine ⟨mul_pos_of_neg_of_neg negative stateNegative, ?_⟩
    have magnitude : (M : ℤ) < ((x + (r : ℤ) * c).natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonpos (le_of_lt stateNegative)]
      omega
    exact_mod_cast magnitude

/-- Every sufficiently late raw state has large magnitude and the offset sign. -/
theorem AdditiveDivisibleOffsetRawBudget (p : Parameters) (d : ℕ) (n : ℤ)
    (dLower : 2 ≤ d) (divisor : p.D = (d : ℤ)) (multiplier : p.Q = 1)
    (offsetDivides : p.D ∣ p.C) (offsetNonzero : p.C ≠ 0) (nonzero : n ≠ 0) :
    ∀ M r : ℕ, 2 * n.natAbs + M + 1 ≤ r →
      0 < p.C * Iterate (RawStep p) r n ∧ M < (Iterate (RawStep p) r n).natAbs := by
  obtain ⟨start, x, startBound, magnitude, invisible, tail⟩ :=
    AdditiveDivisibleOffsetNormalForm p d n dLower divisor multiplier offsetDivides nonzero
  intro M r after
  have startBefore : start ≤ r := by omega
  have late : x.natAbs + 1 + M ≤ r - start := by omega
  have formula := tail (r - start)
  rw [Nat.add_sub_of_le startBefore] at formula
  rw [formula]
  exact IntegralAffineTailLateBound x p.C M (r - start) offsetNonzero late

/-- The effective affine-tail bound gives full-sequence magnitude escape. -/
theorem AdditiveDivisibleOffsetMagnitudeEscapes (p : Parameters) (d : ℕ) (n : ℤ)
    (dLower : 2 ≤ d) (divisor : p.D = (d : ℤ)) (multiplier : p.Q = 1)
    (offsetDivides : p.D ∣ p.C) (offsetNonzero : p.C ≠ 0) (nonzero : n ≠ 0) :
    MagnitudeEscapes (RawStep p) n := by
  intro M
  refine ⟨2 * n.natAbs + M + 1, ?_⟩
  intro r after
  exact (AdditiveDivisibleOffsetRawBudget p d n dLower divisor multiplier
    offsetDivides offsetNonzero nonzero M r after).2

/-- An original nonzero seed return would force a positive affine-tail return. -/
theorem AdditiveDivisibleOffsetNoNonzeroReturn (p : Parameters) (d : ℕ) (n : ℤ)
    (dLower : 2 ≤ d) (divisor : p.D = (d : ℤ)) (multiplier : p.Q = 1)
    (offsetDivides : p.D ∣ p.C) (offsetNonzero : p.C ≠ 0) (nonzero : n ≠ 0) :
    ∀ h : ℕ, 0 < h → Iterate (RawStep p) h n ≠ n := by
  intro h positive returned
  obtain ⟨start, x, startBound, magnitude, invisible, tail⟩ :=
    AdditiveDivisibleOffsetNormalForm p d n dLower divisor multiplier offsetDivides nonzero
  have zeroTail := tail 0
  have returnedTail := tail h
  -- Chronological iteration transports a hypothetical return to the same normalized state.
  have commute : Iterate (RawStep p) (start + h) n = Iterate (RawStep p) start n := by
    calc
      Iterate (RawStep p) (start + h) n = Iterate (RawStep p) (h + start) n := by
        rw [Nat.add_comm]
      _ = Iterate (RawStep p) start (Iterate (RawStep p) h n) := by rw [IterateAdd]
      _ = Iterate (RawStep p) start n := by rw [returned]
  rw [commute] at returnedTail
  simp only [Nat.cast_zero, zero_mul, add_zero] at zeroTail
  rw [zeroTail] at returnedTail
  have product : (h : ℤ) * p.C = 0 := by linarith [returnedTail]
  have indexNonzero : (h : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt positive)
  exact (mul_ne_zero indexNonzero offsetNonzero) product

end GeneralizedCollatz
