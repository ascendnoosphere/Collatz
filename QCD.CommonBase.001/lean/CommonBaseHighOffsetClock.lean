-- SPDX-License-Identifier: CC-BY-4.0
import CommonBaseHighOffsetKernel

/-!
Division counts and exact raw clocks for common-base high-offset sweeps.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Each legal event clock adds precisely the wrap count of its current phase. -/
theorem WholeBaseHighOffsetEventClockPhase (p : Parameters) (t u v a k : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt t n k) :
    WholeBaseHighOffsetEventClock p n = 1 + (k + u) / v := by
  have law := WholeBaseHighOffsetRawEvent p t u v a k s n tLower uBelow kBelow
    highOffset divisor multiplier offset atOrder
  by_cases noDivision : k + u < v
  · have branch := law.2.1 noDivision
    simp [WholeBaseHighOffsetEventClock, branch.2, Nat.div_eq_of_lt noDivision]
  · have oneDivision : v ≤ k + u := by omega
    have branch := law.2.2 oneDivision
    have quotient : (k + u) / v = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [WholeBaseHighOffsetEventClock, branch.2.2, quotient]

/-- Euclidean division turns the sum of successive phase wraps into a prefix count. -/
theorem WholeBaseHighOffsetDivisionRecurrence (u v k i : ℕ) (vPositive : 0 < v) :
    (k + (i + 1) * u) / v =
      (k + i * u) / v + ((k + i * u) % v + u) / v := by
  have split : k + (i + 1) * u = v * ((k + i * u) / v) + ((k + i * u) % v + u) := by
    calc
      k + (i + 1) * u = k + i * u + u := by ring
      _ = (v * ((k + i * u) / v) + (k + i * u) % v) + u := by
        rw [Nat.div_add_mod]
      _ = v * ((k + i * u) / v) + ((k + i * u) % v + u) := by ring
  rw [split, Nat.mul_add_div vPositive]

/-- The accumulated clock retains every affine step and every actual division. -/
theorem WholeBaseHighOffsetPrefixClock (p : Parameters) (t u v a k : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt t n k) :
    ∀ i : ℕ, AccumulatedClock (WholeBaseHighOffsetEvent p)
      (WholeBaseHighOffsetEventClock p) i n = i + (k + i * u) / v := by
  intro i
  induction i with
  | zero => { simp [AccumulatedClock, Nat.div_eq_of_lt kBelow] }
  | succ i ih => {
    have vPositive : 0 < v := by omega
    have trace := WholeBaseHighOffsetEventTrace p t u v a k s n tLower uBelow
      kBelow highOffset divisor multiplier offset atOrder i
    have clock := WholeBaseHighOffsetEventClockPhase p t u v a ((k + i * u) % v) s
      (Iterate (WholeBaseHighOffsetEvent p) i n) tLower uBelow
      (Nat.mod_lt _ vPositive) highOffset divisor multiplier offset trace.1
    have counts := WholeBaseHighOffsetDivisionRecurrence u v k i vPositive
    rw [AccumulatedClock, ih, clock, counts]
    omega
  }

/-- Exactly v affine events and u divisions make the same-seed physical sweep. -/
theorem WholeBaseHighOffsetSweepClock (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s) (atOrder : WholeBaseOrderAt t n k) :
    AccumulatedClock (WholeBaseHighOffsetEvent p) (WholeBaseHighOffsetEventClock p) v n =
      u + v := by
  have vPositive : 0 < v := by omega
  have clock := WholeBaseHighOffsetPrefixClock p t u v a k s n tLower uBelow kBelow
    highOffset divisor multiplier offset atOrder v
  rw [Nat.add_mul_div_left k u vPositive, Nat.div_eq_of_lt kBelow] at clock
  omega

/-- The computed event translation occurs at the exact raw, not normalized, sweep clock. -/
theorem WholeBaseHighOffsetRawSweep (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v) (highOffset : u + v ≤ a)
    (coprime : Nat.Coprime u v) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt t n k) :
    Iterate (RawStep p) (u + v) n =
      n + s * (t : ℤ) ^ (a - u - v + 1 + k) * WholeBaseGeometricSum t v := by
  have sweep := WholeBaseHighOffsetEventSweep p t u v a k s n tLower uBelow kBelow
    highOffset coprime divisor multiplier offset atOrder
  rw [WholeBaseHighOffsetEventRawIterates,
    WholeBaseHighOffsetSweepClock p t u v a k s n tLower uBelow kBelow
      highOffset divisor multiplier offset atOrder] at sweep
  exact sweep

/-- The sweep translation preserves the actual whole-base phase of the same state. -/
theorem WholeBaseHighOffsetRawSweepOrder (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s) (atOrder : WholeBaseOrderAt t n k) :
    WholeBaseOrderAt t (Iterate (RawStep p) (u + v) n) k := by
  have trace := WholeBaseHighOffsetEventTrace p t u v a k s n tLower uBelow kBelow
    highOffset divisor multiplier offset atOrder v
  have phase : (k + v * u) % v = k := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt kBelow]
  rw [WholeBaseHighOffsetEventRawIterates,
    WholeBaseHighOffsetSweepClock p t u v a k s n tLower uBelow kBelow
      highOffset divisor multiplier offset atOrder, phase] at trace
  exact trace.1

/-- Iterating the same admissible raw sweep produces an exact arithmetic progression. -/
theorem WholeBaseHighOffsetRawRay (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v) (highOffset : u + v ≤ a)
    (coprime : Nat.Coprime u v) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt t n k) :
    ∀ j : ℕ, WholeBaseOrderAt t (Iterate (RawStep p) (j * (u + v)) n) k ∧
      Iterate (RawStep p) (j * (u + v)) n =
        n + (j : ℤ) *
          (s * (t : ℤ) ^ (a - u - v + 1 + k) * WholeBaseGeometricSum t v) := by
  intro j
  induction j with
  | zero => { simpa [Iterate] using atOrder }
  | succ j ih => {
    have order := WholeBaseHighOffsetRawSweepOrder p t u v a k s
      (Iterate (RawStep p) (j * (u + v)) n) tLower uBelow kBelow highOffset
      divisor multiplier offset ih.1
    have sweep := WholeBaseHighOffsetRawSweep p t u v a k s
      (Iterate (RawStep p) (j * (u + v)) n) tLower uBelow kBelow highOffset coprime
      divisor multiplier offset ih.1
    have composition : Iterate (RawStep p) ((j + 1) * (u + v)) n =
        Iterate (RawStep p) (u + v) (Iterate (RawStep p) (j * (u + v)) n) := by
      rw [Nat.succ_mul, IterateAdd]
    refine ⟨composition ▸ order, ?_⟩
    rw [composition, sweep, ih.2]
    push_cast
    ring
  }

end GeneralizedCollatz
