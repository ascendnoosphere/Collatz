-- SPDX-License-Identifier: CC-BY-4.0
import CommonBaseHighOffsetOutcomes
import Mathlib.Data.Nat.GCD.Basic

/-!
Exact rebasing of pure common-base parameters. The raw map and seed are unchanged.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Division by the exponent gcd gives a coprime pair and preserves the high-offset bound. -/
theorem WholeBaseRebasedAdmissible (t u v a : ℕ)
    (tLower : 2 ≤ t) (uPositive : 0 < u) (uBelow : u < v)
    (highOffset : u + v ≤ a) :
    2 ≤ t ^ Nat.gcd u v ∧ 0 < u / Nat.gcd u v ∧
      u / Nat.gcd u v < v / Nat.gcd u v ∧
      u / Nat.gcd u v + v / Nat.gcd u v ≤ a / Nat.gcd u v ∧
      Nat.Coprime (u / Nat.gcd u v) (v / Nat.gcd u v) := by
  let g := Nat.gcd u v
  have gPositive : 0 < g := Nat.gcd_pos_of_pos_left v uPositive
  have gLeft : g ∣ u := Nat.gcd_dvd_left u v
  have gRight : g ∣ v := Nat.gcd_dvd_right u v
  have base : 2 ≤ t ^ g := by
    have powers := Nat.pow_le_pow_right (by omega : 0 < t) (show 1 ≤ g by omega)
    have baseBelow : t ≤ t ^ g := by simpa using powers
    exact tLower.trans baseBelow
  have positive : 0 < u / g := Nat.div_pos (Nat.le_of_dvd uPositive gLeft) gPositive
  have below : u / g < v / g := Nat.div_lt_div_of_lt_of_dvd gRight uBelow
  have high : u / g + v / g ≤ a / g := by
    apply (Nat.le_div_iff_mul_le gPositive).2
    rw [Nat.add_mul, Nat.div_mul_cancel gLeft, Nat.div_mul_cancel gRight]
    exact highOffset
  exact ⟨base, positive, below, high, Nat.coprime_div_gcd_div_gcd gPositive⟩

/-- The quotient and remainder of the offset exponent reconstruct all three coefficients. -/
theorem WholeBaseRebasedCoefficients (t u v a : ℕ) (s : ℤ) :
    (t : ℤ) ^ u = ((t ^ Nat.gcd u v : ℕ) : ℤ) ^ (u / Nat.gcd u v) ∧
      (t : ℤ) ^ v = ((t ^ Nat.gcd u v : ℕ) : ℤ) ^ (v / Nat.gcd u v) ∧
      (t : ℤ) ^ a * s =
        ((t ^ Nat.gcd u v : ℕ) : ℤ) ^ (a / Nat.gcd u v) *
          ((t : ℤ) ^ (a % Nat.gcd u v) * s) := by
  have left : Nat.gcd u v * (u / Nat.gcd u v) = u := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left u v)
  have right : Nat.gcd u v * (v / Nat.gcd u v) = v := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right u v)
  constructor
  · simp only [Nat.cast_pow, ← pow_mul, left]
  constructor
  · simp only [Nat.cast_pow, ← pow_mul, right]
  · have offset : Nat.gcd u v * (a / Nat.gcd u v) + a % Nat.gcd u v = a :=
      Nat.div_add_mod a (Nat.gcd u v)
    simp only [Nat.cast_pow, ← pow_mul, ← mul_assoc, ← pow_add, offset]

/-- The carried exponent remainder is a positive factor, even when the residual is not a unit. -/
theorem WholeBaseRebasedResidualNonzero (t u v a : ℕ) (s : ℤ)
    (tLower : 2 ≤ t) (sNonzero : s ≠ 0) :
    (t : ℤ) ^ (a % Nat.gcd u v) * s ≠ 0 := by
  exact mul_ne_zero (ne_of_gt (pow_pos (by omega : (0 : ℤ) < t) _)) sNonzero

/-- The raw sweep ray retains every rebased phase and the same legal raw map. -/
theorem WholeBaseHighOffsetRawRayRebased (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uPositive : 0 < u) (uBelow : u < v) (highOffset : u + v ≤ a)
    (kBelow : k < v / Nat.gcd u v) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt (t ^ Nat.gcd u v) n k) (j : ℕ) :
    WholeBaseOrderAt (t ^ Nat.gcd u v)
        (Iterate (RawStep p) (j * (u / Nat.gcd u v + v / Nat.gcd u v)) n) k ∧
      Iterate (RawStep p) (j * (u / Nat.gcd u v + v / Nat.gcd u v)) n =
        n + (j : ℤ) * ((t : ℤ) ^ (a % Nat.gcd u v) * s *
          ((t ^ Nat.gcd u v : ℕ) : ℤ) ^
            (a / Nat.gcd u v - u / Nat.gcd u v - v / Nat.gcd u v + 1 + k) *
          WholeBaseGeometricSum (t ^ Nat.gcd u v) (v / Nat.gcd u v)) := by
  have admissible := WholeBaseRebasedAdmissible t u v a tLower uPositive uBelow highOffset
  rcases admissible with ⟨base, positive, below, high, coprime⟩
  rcases WholeBaseRebasedCoefficients t u v a s with ⟨left, right, coefficients⟩
  exact WholeBaseHighOffsetRawRay p (t ^ Nat.gcd u v) (u / Nat.gcd u v)
    (v / Nat.gcd u v) (a / Nat.gcd u v) k ((t : ℤ) ^ (a % Nat.gcd u v) * s) n
    base below kBelow high coprime (divisor.trans right) (multiplier.trans left)
    (offset.trans coefficients) atOrder j

/-- The published full-raw estimate applies to exactly the same parameters after rebasing. -/
theorem WholeBaseHighOffsetRawEscapeRebased (p : Parameters) (t u v a : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uPositive : 0 < u) (uBelow : u < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s) (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) :
    ∀ M r : ℕ,
      n.natAbs + (n.natAbs + 1 + M * (p.D ^ (u / Nat.gcd u v)).natAbs) *
        (u / Nat.gcd u v + v / Nat.gcd u v) ≤ r →
      M < (Iterate (RawStep p) r n).natAbs := by
  let g := Nat.gcd u v
  let T := t ^ g
  let S := (t : ℤ) ^ (a % g) * s
  have admissible := WholeBaseRebasedAdmissible t u v a tLower uPositive uBelow highOffset
  rcases admissible with ⟨base, positive, below, high, coprime⟩
  rcases WholeBaseRebasedCoefficients t u v a s with ⟨left, right, coefficients⟩
  have residual : S ≠ 0 := WholeBaseRebasedResidualNonzero t u v a s tLower sNonzero
  exact WholeBaseHighOffsetRawEscape p T (u / g) (v / g) (a / g) S n
    base positive below high coprime (divisor.trans right) (multiplier.trans left)
    (offset.trans coefficients) residual nNonzero

/-- The rebased raw budget supplies full-sequence escape without original coprimality. -/
theorem WholeBaseHighOffsetMagnitudeEscapesRebased (p : Parameters) (t u v a : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (uPositive : 0 < u) (uBelow : u < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) : MagnitudeEscapes (RawStep p) n := by
  intro M
  refine ⟨n.natAbs + (n.natAbs + 1 + M * (p.D ^ (u / Nat.gcd u v)).natAbs) *
    (u / Nat.gcd u v + v / Nat.gcd u v), ?_⟩
  exact WholeBaseHighOffsetRawEscapeRebased p t u v a s n tLower uPositive uBelow
    highOffset divisor multiplier offset sNonzero nNonzero M

/-- The carried residual has the original offset's sign, so all late raw signs transfer. -/
theorem WholeBaseHighOffsetEventuallyAlignedRebased (p : Parameters) (t u v a : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (uPositive : 0 < u) (uBelow : u < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) :
    ∃ T : ℕ, T ≤ n.natAbs + (n.natAbs + 1) * (u / Nat.gcd u v + v / Nat.gcd u v) ∧
      ∀ r : ℕ, T ≤ r → 0 < s * Iterate (RawStep p) r n := by
  let g := Nat.gcd u v
  let factor := (t : ℤ) ^ (a % g)
  let S := factor * s
  have admissible := WholeBaseRebasedAdmissible t u v a tLower uPositive uBelow highOffset
  rcases admissible with ⟨base, positive, below, high, coprime⟩
  rcases WholeBaseRebasedCoefficients t u v a s with ⟨left, right, coefficients⟩
  have residual : S ≠ 0 := WholeBaseRebasedResidualNonzero t u v a s tLower sNonzero
  obtain ⟨T, bound, aligned⟩ := WholeBaseHighOffsetEventuallyAligned p (t ^ g)
    (u / g) (v / g) (a / g) S n base positive below high coprime (divisor.trans right)
    (multiplier.trans left) (offset.trans coefficients) residual nNonzero
  refine ⟨T, bound, ?_⟩
  intro r after
  have product : 0 < factor * (s * Iterate (RawStep p) r n) := by
    simpa [S, mul_assoc] using aligned r after
  exact pos_of_mul_pos_right product (le_of_lt (pow_pos (by omega : (0 : ℤ) < t) _))

/-- Periodic-point classification is transferred without changing any seed or raw iterate. -/
theorem WholeBaseHighOffsetPeriodicIffZeroRebased (p : Parameters) (t u v a : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (uPositive : 0 < u) (uBelow : u < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) : PeriodicPoint (RawStep p) n ↔ n = 0 := by
  have admissible := WholeBaseRebasedAdmissible t u v a tLower uPositive uBelow highOffset
  rcases admissible with ⟨base, positive, below, high, coprime⟩
  rcases WholeBaseRebasedCoefficients t u v a s with ⟨left, right, coefficients⟩
  exact WholeBaseHighOffsetPeriodicIffZero p (t ^ Nat.gcd u v)
    (u / Nat.gcd u v) (v / Nat.gcd u v) (a / Nat.gcd u v)
    ((t : ℤ) ^ (a % Nat.gcd u v) * s) n base positive below high coprime
    (divisor.trans right) (multiplier.trans left) (offset.trans coefficients)
    (WholeBaseRebasedResidualNonzero t u v a s tLower sNonzero)

/-- Nontrivial exponent gcd rebasing strictly decreases the number of phases. -/
theorem WholeBaseRebasedPhaseDecrease (u v : ℕ) (uPositive : 0 < u) (uBelow : u < v)
    (gLarge : 1 < Nat.gcd u v) : v / Nat.gcd u v < v := by
  exact Nat.div_lt_self (lt_trans uPositive uBelow) gLarge

/-- The new base and carried residual do not exceed the existing coefficient magnitudes. -/
theorem WholeBaseRebasedParameterBounds (t u v a : ℕ) (s : ℤ)
    (tLower : 2 ≤ t) (uPositive : 0 < u) :
    t ^ Nat.gcd u v ≤ t ^ u ∧
      ((t : ℤ) ^ (a % Nat.gcd u v) * s).natAbs ≤ ((t : ℤ) ^ a * s).natAbs := by
  constructor
  · exact Nat.pow_le_pow_right (by omega : 0 < t)
      (Nat.le_of_dvd uPositive (Nat.gcd_dvd_left u v))
  · have powers := Nat.pow_le_pow_right (by omega : 0 < t) (Nat.mod_le a (Nat.gcd u v))
    simpa [Int.natAbs_mul, Int.natAbs_pow] using Nat.mul_le_mul_right s.natAbs powers

end GeneralizedCollatz
