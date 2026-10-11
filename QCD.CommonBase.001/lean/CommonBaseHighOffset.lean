-- SPDX-License-Identifier: CC-BY-4.0
import GuardedDynamics
import DynamicalMorphisms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Whole-base order witnesses for the common-base high-offset event schedule.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Exact whole-base order keeps the signed residual rather than assuming a prime base. -/
def WholeBaseOrderAt (t : ℕ) (n : ℤ) (k : ℕ) : Prop :=
  ∃ w : ℤ, n = (t : ℤ) ^ k * w ∧ ¬(t : ℤ) ∣ w

/-- A genuine order witness over a base at least two cannot represent zero. -/
theorem WholeBaseOrderAtNonzero (t k : ℕ) (n : ℤ) (tLower : 2 ≤ t)
    (atOrder : WholeBaseOrderAt t n k) : n ≠ 0 := by
  rcases atOrder with ⟨w, state, notDivisible⟩
  have baseNonzero : (t : ℤ) ≠ 0 := by omega
  have residualNonzero : w ≠ 0 := by
    intro zero
    apply notDivisible
    simp [zero]
  rw [state]
  exact mul_ne_zero (pow_ne_zero _ baseNonzero) residualNonzero

/-- Every nonzero signed state has a whole-base witness by strict magnitude descent. -/
theorem WholeBaseOrderAtExists (t : ℕ) (n : ℤ) (tLower : 2 ≤ t)
    (nNonzero : n ≠ 0) : ∃ k : ℕ, WholeBaseOrderAt t n k := by
  have auxiliary : ∀ b : ℕ, ∀ n : ℤ, n.natAbs = b → n ≠ 0 →
      ∃ k : ℕ, WholeBaseOrderAt t n k := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih => {
        intro n magnitude nonzero
        by_cases divisible : (t : ℤ) ∣ n
        · rcases divisible with ⟨m, state⟩
          have mNonzero : m ≠ 0 := by
            intro zero
            apply nonzero
            simp [state, zero]
          have mPositive : 0 < m.natAbs := Int.natAbs_pos.mpr mNonzero
          have rank : b = t * m.natAbs := by
            rw [← magnitude, state, Int.natAbs_mul]
            simp
          have decrease : m.natAbs < b := by nlinarith
          rcases ih m.natAbs decrease m rfl mNonzero with ⟨k, w, factor, guard⟩
          refine ⟨k + 1, w, ?_, guard⟩
          calc
            n = (t : ℤ) * m := state
            _ = (t : ℤ) * ((t : ℤ) ^ k * w) := by rw [factor]
            _ = (t : ℤ) ^ (k + 1) * w := by rw [pow_succ]; ring
        · exact ⟨0, n, by simp, divisible⟩
      }
  exact auxiliary n.natAbs n rfl nNonzero

/-- All lower base powers divide a state carrying an exact higher-order witness. -/
theorem WholeBaseOrderAtPowerDivides (t k h : ℕ) (n : ℤ) (hBound : h ≤ k)
    (atOrder : WholeBaseOrderAt t n k) : (t : ℤ) ^ h ∣ n := by
  rcases atOrder with ⟨w, state, _⟩
  refine ⟨(t : ℤ) ^ (k - h) * w, ?_⟩
  rw [state, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hBound]

/-- A larger base power cannot divide a state of lower exact whole-base order. -/
theorem WholeBaseOrderAtPowerNotDivides (t k h : ℕ) (n : ℤ) (tLower : 2 ≤ t)
    (hAbove : k < h) (atOrder : WholeBaseOrderAt t n k) : ¬(t : ℤ) ^ h ∣ n := by
  intro divisible
  rcases atOrder with ⟨w, state, guard⟩
  have baseNonzero : (t : ℤ) ≠ 0 := by omega
  have lowerDivides : (t : ℤ) ^ (k + 1) ∣ (t : ℤ) ^ h := by
    refine ⟨(t : ℤ) ^ (h - (k + 1)), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  rcases dvd_trans lowerDivides divisible with ⟨z, equation⟩
  have product : (t : ℤ) ^ k * w = (t : ℤ) ^ k * ((t : ℤ) * z) := by
    rw [← state, equation, pow_succ]
    ring
  have residual : w = (t : ℤ) * z :=
    mul_left_cancel₀ (pow_ne_zero _ baseNonzero) product
  exact guard ⟨z, residual⟩

/-- Exact division removes precisely the specified number of whole-base factors. -/
theorem WholeBaseOrderAtPowerQuotient (t k h : ℕ) (n : ℤ) (tLower : 2 ≤ t)
    (hBound : h ≤ k) (atOrder : WholeBaseOrderAt t n k) :
    WholeBaseOrderAt t (n / (t : ℤ) ^ h) (k - h) := by
  rcases atOrder with ⟨w, state, guard⟩
  have baseNonzero : (t : ℤ) ≠ 0 := by omega
  refine ⟨w, ?_, guard⟩
  apply Int.ediv_eq_of_eq_mul_left (pow_ne_zero _ baseNonzero)
  calc
    n = (t : ℤ) ^ k * w := state
    _ = (t : ℤ) ^ h * ((t : ℤ) ^ (k - h) * w) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hBound]
    _ = (t : ℤ) ^ (k - h) * w * (t : ℤ) ^ h := by ring

/-- The high offset cannot cancel the lower-order affine multiplier term. -/
theorem WholeBaseHighOffsetAffineOrder (t u v a k : ℕ) (s n : ℤ)
    (kBelow : k < v) (highOffset : u + v ≤ a)
    (atOrder : WholeBaseOrderAt t n k) :
    WholeBaseOrderAt t ((t : ℤ) ^ u * n + (t : ℤ) ^ a * s) (k + u) := by
  rcases atOrder with ⟨w, state, guard⟩
  let b := a - (k + u)
  have bPositive : 0 < b := by dsimp [b]; omega
  have exponent : k + u + b = a := by dsimp [b]; omega
  have offsetDivisible : (t : ℤ) ∣ (t : ℤ) ^ b * s := by
    refine ⟨(t : ℤ) ^ (b - 1) * s, ?_⟩
    have split : b = 1 + (b - 1) := by omega
    have splitPower : (t : ℤ) ^ b = (t : ℤ) * (t : ℤ) ^ (b - 1) := by
      calc
        (t : ℤ) ^ b = (t : ℤ) ^ (1 + (b - 1)) := congrArg ((t : ℤ) ^ ·) split
        _ = (t : ℤ) * (t : ℤ) ^ (b - 1) := by rw [pow_add, pow_one]
    rw [splitPower]
    ring
  refine ⟨w + (t : ℤ) ^ b * s, ?_, ?_⟩
  · rw [state, ← exponent, pow_add, pow_add]
    ring
  · intro divisible
    apply guard
    rcases divisible with ⟨z, total⟩
    rcases offsetDivisible with ⟨y, offset⟩
    refine ⟨z - y, ?_⟩
    calc
      w = (w + (t : ℤ) ^ b * s) - (t : ℤ) ^ b * s := by ring
      _ = (t : ℤ) * z - (t : ℤ) * y := by rw [total, offset]
      _ = (t : ℤ) * (z - y) := by ring

/-- A normalized nonzero state has an admissible phase below the division exponent. -/
theorem WholeBaseOrderBelowDivisor (t v : ℕ) (n : ℤ) (tLower : 2 ≤ t)
    (nNonzero : n ≠ 0) (notDivisible : ¬(t : ℤ) ^ v ∣ n) :
    ∃ k : ℕ, k < v ∧ WholeBaseOrderAt t n k := by
  rcases WholeBaseOrderAtExists t n tLower nNonzero with ⟨k, atOrder⟩
  refine ⟨k, ?_, atOrder⟩
  by_contra notBelow
  apply notDivisible
  exact WholeBaseOrderAtPowerDivides t k v n (by omega) atOrder

/-- One normalized event realizes the forced affine and optional single division. -/
theorem WholeBaseHighOffsetRawEvent (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s) (atOrder : WholeBaseOrderAt t n k) :
    (¬p.D ∣ n) ∧
      ((k + u < v → WholeBaseOrderAt t (RawStep p n) (k + u) ∧
          ¬p.D ∣ RawStep p n) ∧
        (v ≤ k + u → WholeBaseOrderAt t (RawStep p (RawStep p n)) (k + u - v) ∧
          ¬p.D ∣ RawStep p (RawStep p n) ∧ p.D ∣ RawStep p n)) := by
  have inputGuard : ¬p.D ∣ n := by
    rw [divisor]
    exact WholeBaseOrderAtPowerNotDivides t k v n tLower kBelow atOrder
  have firstStep : RawStep p n = (t : ℤ) ^ u * n + (t : ℤ) ^ a * s := by
    simp only [RawStep, if_neg inputGuard, multiplier, offset]
  have affineOrder : WholeBaseOrderAt t (RawStep p n) (k + u) := by
    rw [firstStep]
    exact WholeBaseHighOffsetAffineOrder t u v a k s n kBelow highOffset atOrder
  refine ⟨inputGuard, ?_, ?_⟩
  · intro noDivision
    refine ⟨affineOrder, ?_⟩
    rw [divisor]
    exact WholeBaseOrderAtPowerNotDivides t (k + u) v (RawStep p n)
      tLower noDivision affineOrder
  · intro oneDivision
    have nextDivisible : p.D ∣ RawStep p n := by
      rw [divisor]
      exact WholeBaseOrderAtPowerDivides t (k + u) v (RawStep p n)
        oneDivision affineOrder
    have quotientOrder :
        WholeBaseOrderAt t (RawStep p (RawStep p n)) (k + u - v) := by
      rw [RawStep, if_pos nextDivisible, divisor]
      exact WholeBaseOrderAtPowerQuotient t (k + u) v (RawStep p n)
        tLower oneDivision affineOrder
    refine ⟨quotientOrder, ?_, nextDivisible⟩
    rw [divisor]
    exact WholeBaseOrderAtPowerNotDivides t (k + u - v) v (RawStep p (RawStep p n))
      tLower (by omega) quotientOrder

/-- A normalized event takes one raw step and, if needed, one extra division. -/
def WholeBaseHighOffsetEvent (p : Parameters) (n : ℤ) : ℤ :=
  if p.D ∣ RawStep p n then RawStep p (RawStep p n) else RawStep p n

/-- The event clock counts exactly the raw steps selected by the same guard. -/
def WholeBaseHighOffsetEventClock (p : Parameters) (n : ℤ) : ℕ :=
  if p.D ∣ RawStep p n then 2 else 1

/-- The event and its clock use the same branch and realize the physical raw trajectory. -/
theorem WholeBaseHighOffsetEventRawClock (p : Parameters) (n : ℤ) :
    WholeBaseHighOffsetEvent p n =
      Iterate (RawStep p) (WholeBaseHighOffsetEventClock p n) n := by
  by_cases divisible : p.D ∣ RawStep p n <;>
    simp [WholeBaseHighOffsetEvent, WholeBaseHighOffsetEventClock, divisible, Iterate]

/-- A legal normalized event has the deterministic next phase and remains normalized. -/
theorem WholeBaseHighOffsetEventOrder (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s) (atOrder : WholeBaseOrderAt t n k) :
    WholeBaseOrderAt t (WholeBaseHighOffsetEvent p n) ((k + u) % v) ∧
      ¬p.D ∣ WholeBaseHighOffsetEvent p n := by
  have law := WholeBaseHighOffsetRawEvent p t u v a k s n tLower uBelow kBelow
    highOffset divisor multiplier offset atOrder
  by_cases noDivision : k + u < v
  · have branch := law.2.1 noDivision
    simpa [WholeBaseHighOffsetEvent, branch.2, Nat.mod_eq_of_lt noDivision] using branch
  · have oneDivision : v ≤ k + u := by omega
    have branch := law.2.2 oneDivision
    have phase : (k + u) % v = k + u - v := by
      have split : k + u = (k + u - v) + v := by omega
      have remainingBelow : k + u - v < v := by omega
      calc
        (k + u) % v = ((k + u - v) + v) % v := congrArg (· % v) split
        _ = (k + u - v) % v := Nat.add_mod_right _ _
        _ = k + u - v := Nat.mod_eq_of_lt remainingBelow
    simpa [WholeBaseHighOffsetEvent, branch.2.2, phase] using
      And.intro branch.1 branch.2.1

/-- Every event phase is fixed by its index rather than by the signed seed size. -/
theorem WholeBaseHighOffsetEventTrace (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s) (atOrder : WholeBaseOrderAt t n k) :
    ∀ i : ℕ, WholeBaseOrderAt t (Iterate (WholeBaseHighOffsetEvent p) i n)
        ((k + i * u) % v) ∧ ¬p.D ∣ Iterate (WholeBaseHighOffsetEvent p) i n := by
  intro i
  induction i with
  | zero => {
      have guard : ¬p.D ∣ n := by
        rw [divisor]
        exact WholeBaseOrderAtPowerNotDivides t k v n tLower kBelow atOrder
      simpa [Iterate, Nat.mod_eq_of_lt kBelow] using And.intro atOrder guard
    }
  | succ i ih => {
      have vPositive : 0 < v := by omega
      have law := WholeBaseHighOffsetEventOrder p t u v a ((k + i * u) % v) s
        (Iterate (WholeBaseHighOffsetEvent p) i n) tLower uBelow
        (Nat.mod_lt _ vPositive) highOffset divisor multiplier offset ih.1
      have exponent : k + (i + 1) * u = (k + i * u) + u := by ring
      have phase : (((k + i * u) % v) + u) % v = (k + (i + 1) * u) % v := by
        rw [exponent]
        simp [Nat.add_mod]
      simpa [Iterate, phase] using law
    }

/-- Accumulated event clocks recover every event sample on the same raw orbit. -/
theorem WholeBaseHighOffsetEventRawIterates (p : Parameters) (i : ℕ) (n : ℤ) :
    Iterate (WholeBaseHighOffsetEvent p) i n = Iterate (RawStep p)
      (AccumulatedClock (WholeBaseHighOffsetEvent p) (WholeBaseHighOffsetEventClock p) i n)
      n := by
  exact VariableClockIterates (WholeBaseHighOffsetEvent p) (RawStep p) id
    (WholeBaseHighOffsetEventClock p) (WholeBaseHighOffsetEventRawClock p) i n

end GeneralizedCollatz
