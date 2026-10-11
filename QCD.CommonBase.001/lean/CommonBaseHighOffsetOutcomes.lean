-- SPDX-License-Identifier: CC-BY-4.0
import CommonBaseHighOffsetEscape
import CompressionCycleClasses

/-!
Full-sequence escape, the zero periodic class, and the sharp threshold control.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The explicit raw budget supplies full-sequence escape, not only a growing subsequence. -/
theorem WholeBaseHighOffsetMagnitudeEscapes (p : Parameters) (t u v a : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uPositive : 0 < u) (uBelow : u < v) (highOffset : u + v ≤ a)
    (coprime : Nat.Coprime u v) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) : MagnitudeEscapes (RawStep p) n := by
  intro M
  refine ⟨n.natAbs + (n.natAbs + 1 + M * (p.D ^ u).natAbs) * (u + v), ?_⟩
  intro r after
  exact WholeBaseHighOffsetRawEscape p t u v a s n tLower uPositive uBelow highOffset
    coprime divisor multiplier offset sNonzero nNonzero M r after

/-- A hypothetical return repeats beyond the escape budget and contradicts its own magnitude. -/
theorem WholeBaseHighOffsetNoNonzeroReturn (p : Parameters) (t u v a : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uPositive : 0 < u) (uBelow : u < v) (highOffset : u + v ≤ a)
    (coprime : Nat.Coprime u v) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) (h : ℕ) (hPositive : 0 < h) :
    Iterate (RawStep p) h n ≠ n := by
  intro returned
  have escapes := WholeBaseHighOffsetMagnitudeEscapes p t u v a s n tLower
    uPositive uBelow highOffset coprime divisor multiplier offset sNonzero nNonzero
  obtain ⟨R, late⟩ := escapes n.natAbs
  have repeated := IterateReturnMultiple (RawStep p) n h (R + 1) returned
  have growth : R + 1 ≤ h * (R + 1) := Nat.le_mul_of_pos_left _ hPositive
  have contradiction := late (h * (R + 1)) (by omega)
  rw [repeated] at contradiction
  exact (Nat.lt_irrefl _ contradiction)

/-- Zero is the only periodic point; nonzero offsets do not affect its division branch. -/
theorem WholeBaseHighOffsetPeriodicIffZero (p : Parameters) (t u v a : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uPositive : 0 < u) (uBelow : u < v) (highOffset : u + v ≤ a)
    (coprime : Nat.Coprime u v) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) : PeriodicPoint (RawStep p) n ↔ n = 0 := by
  constructor
  · intro periodic
    rcases periodic with ⟨h, hPositive, returned⟩
    by_contra nNonzero
    exact WholeBaseHighOffsetNoNonzeroReturn p t u v a s n tLower uPositive uBelow
      highOffset coprime divisor multiplier offset sNonzero nNonzero h hPositive returned
  · intro zero
    subst n
    refine ⟨1, by decide, ?_⟩
    simp [Iterate, RawStep]

/-- The level a=u+v-1 admits a primitive four-step positive cycle at t=2,u=1,v=2. -/
theorem WholeBaseHighOffsetBoundaryPrimitive (p : Parameters)
    (multiplier : p.Q = 2) (offset : p.C = 4) (divisor : p.D = 4) :
    PrimitiveReturn (RawStep p) 1 4 := by
  refine ⟨by decide, ?_, ?_⟩
  · norm_num [Iterate, RawStep, multiplier, offset, divisor]
  · intro r rPositive returned
    by_contra notBound
    have small : r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases small with one | two | three
    · subst r
      norm_num [Iterate, RawStep, multiplier, offset, divisor] at returned
    · subst r
      norm_num [Iterate, RawStep, multiplier, offset, divisor] at returned
    · subst r
      norm_num [Iterate, RawStep, multiplier, offset, divisor] at returned

end GeneralizedCollatz
