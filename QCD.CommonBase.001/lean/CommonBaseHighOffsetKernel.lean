-- SPDX-License-Identifier: CC-BY-4.0
import CommonBaseHighOffset
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev

/-!
Phase permutation and finite kernel for the common-base high-offset branch.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The phase map records the actual rotation without presupposing its invertibility. -/
def WholeBasePhaseIndex (u v k : ℕ) (vPositive : 0 < v) (i : Fin v) : Fin v :=
  ⟨(k + i.val * u) % v, Nat.mod_lt _ vPositive⟩

/-- Coprimality prevents two indices of one sweep from sharing a phase. -/
theorem WholeBasePhaseIndexInjective (u v k : ℕ) (vPositive : 0 < v)
    (coprime : Nat.Coprime u v) :
    Function.Injective (WholeBasePhaseIndex u v k vPositive) := by
  intro i j samePhase
  have congruent : Nat.ModEq v (k + i.val * u) (k + j.val * u) :=
    congrArg Fin.val samePhase
  have sameProduct : Nat.ModEq v (i.val * u) (j.val * u) :=
    Nat.ModEq.add_left_cancel' k congruent
  have modulusCoprime : Nat.gcd v u = 1 := by
    simpa [Nat.gcd_comm] using coprime.gcd_eq_one
  have sameIndex := Nat.ModEq.cancel_right_of_coprime modulusCoprime sameProduct
  apply Fin.ext
  simpa [Nat.ModEq, Nat.mod_eq_of_lt i.is_lt, Nat.mod_eq_of_lt j.is_lt] using sameIndex

/-- Injectivity on the finite phase set supplies the full, not merely partial, sweep. -/
theorem WholeBasePhaseIndexBijective (u v k : ℕ) (vPositive : 0 < v)
    (coprime : Nat.Coprime u v) :
    Function.Bijective (WholeBasePhaseIndex u v k vPositive) := by
  have injective := WholeBasePhaseIndexInjective u v k vPositive coprime
  exact ⟨injective, Finite.surjective_of_injective injective⟩

/-- The integer geometric sum is finite for every natural base and length. -/
def WholeBaseGeometricSum (t v : ℕ) : ℤ := ∑ i : Fin v, (t : ℤ) ^ i.val

/-- Reversing all phases preserves every exponent of the geometric sum exactly once. -/
theorem WholeBaseReverseGeometricSum (t v : ℕ) :
    (∑ i : Fin v, (t : ℤ) ^ (v - 1 - i.val)) = WholeBaseGeometricSum t v := by
  have reversed : Function.Bijective (Fin.rev : Fin v → Fin v) :=
    Fin.rev_involutive.bijective
  have reverseValue : ∀ i : Fin v, i.rev.val = v - 1 - i.val := by
    intro i
    simp only [Fin.val_rev]
    omega
  calc
    (∑ i : Fin v, (t : ℤ) ^ (v - 1 - i.val)) =
        ∑ i : Fin v, (t : ℤ) ^ i.rev.val := by
      apply Finset.sum_congr rfl
      intro i _
      rw [reverseValue]
    _ = WholeBaseGeometricSum t v := by
      exact reversed.sum_comp (fun i : Fin v => (t : ℤ) ^ i.val)

/-- The whole sweep removes the phase ordering from the residual affine correction. -/
theorem WholeBaseHighOffsetPhaseKernel (t u v a k : ℕ) (vPositive : 0 < v)
    (coprime : Nat.Coprime u v) (highOffset : u + v ≤ a) :
    (∑ i : Fin v, (t : ℤ) ^ (a - u - (k + i.val * u) % v)) =
      (t : ℤ) ^ (a - u - (v - 1)) * WholeBaseGeometricSum t v := by
  have permutation := WholeBasePhaseIndexBijective u v k vPositive coprime
  calc
    (∑ i : Fin v, (t : ℤ) ^ (a - u - (k + i.val * u) % v)) =
        ∑ i : Fin v, (t : ℤ) ^ (a - u - i.val) := by
      exact permutation.sum_comp (fun i : Fin v => (t : ℤ) ^ (a - u - i.val))
    _ = ∑ i : Fin v,
        (t : ℤ) ^ (a - u - (v - 1)) * (t : ℤ) ^ (v - 1 - i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      have exponent : a - u - i.val = (a - u - (v - 1)) + (v - 1 - i.val) := by
        have bound := i.is_lt
        omega
      rw [exponent, pow_add]
    _ = (t : ℤ) ^ (a - u - (v - 1)) * WholeBaseGeometricSum t v := by
      rw [← Finset.mul_sum, WholeBaseReverseGeometricSum]

/-- The residual coefficient has the same affine update in either legal raw branch. -/
theorem WholeBaseHighOffsetEventValue (p : Parameters) (t u v a k : ℕ)
    (s n w : ℤ) (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt t n k) (state : n = (t : ℤ) ^ k * w) :
    WholeBaseHighOffsetEvent p n =
      (t : ℤ) ^ ((k + u) % v) * (w + (t : ℤ) ^ (a - u - k) * s) := by
  have law := WholeBaseHighOffsetRawEvent p t u v a k s n tLower uBelow kBelow
    highOffset divisor multiplier offset atOrder
  have exponent : k + u + (a - u - k) = a := by omega
  have splitPower : (t : ℤ) ^ a = (t : ℤ) ^ (k + u) * (t : ℤ) ^ (a - u - k) := by
    rw [← pow_add, exponent]
  have factored : RawStep p n =
      (t : ℤ) ^ (k + u) * (w + (t : ℤ) ^ (a - u - k) * s) := by
    rw [RawStep, if_neg law.1, multiplier, offset, state, splitPower]
    simp only [pow_add]
    ring
  by_cases noDivision : k + u < v
  · have branch := law.2.1 noDivision
    rw [WholeBaseHighOffsetEvent, if_neg branch.2, factored,
      Nat.mod_eq_of_lt noDivision]
  · have oneDivision : v ≤ k + u := by omega
    have branch := law.2.2 oneDivision
    have remainingBelow : k + u - v < v := by omega
    have phase : (k + u) % v = k + u - v := by
      have split : k + u = (k + u - v) + v := by omega
      conv_lhs => rw [split, Nat.add_mod_right, Nat.mod_eq_of_lt remainingBelow]
    rw [WholeBaseHighOffsetEvent, if_pos branch.2.2, RawStep, if_pos branch.2.2,
      divisor, factored, phase]
    apply Int.ediv_eq_of_eq_mul_left (pow_ne_zero _ (by omega : (t : ℤ) ≠ 0))
    have split : k + u = (k + u - v) + v := by omega
    conv_lhs => rw [split, pow_add]
    ring

/-- The actual event orbit equals an explicit residual sum at every phase. -/
theorem WholeBaseHighOffsetResidualTrace (p : Parameters) (t u v a k : ℕ)
    (s n w : ℤ) (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt t n k) (state : n = (t : ℤ) ^ k * w) :
    ∀ i : ℕ, Iterate (WholeBaseHighOffsetEvent p) i n =
      (t : ℤ) ^ ((k + i * u) % v) *
        (w + s * ∑ j ∈ Finset.range i, (t : ℤ) ^ (a - u - (k + j * u) % v)) := by
  intro i
  induction i with
  | zero => { simp [Iterate, Nat.mod_eq_of_lt kBelow, state] }
  | succ i ih => {
    have vPositive : 0 < v := by omega
    have trace := WholeBaseHighOffsetEventTrace p t u v a k s n tLower uBelow
      kBelow highOffset divisor multiplier offset atOrder i
    have value := WholeBaseHighOffsetEventValue p t u v a ((k + i * u) % v) s
      (Iterate (WholeBaseHighOffsetEvent p) i n)
      (w + s * ∑ j ∈ Finset.range i, (t : ℤ) ^ (a - u - (k + j * u) % v))
      tLower uBelow (Nat.mod_lt _ vPositive) highOffset divisor multiplier offset
      trace.1 ih
    have phase : ((k + i * u) % v + u) % v = (k + (i + 1) * u) % v := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      congr 1
      ring
    rw [Iterate, value, phase, Finset.sum_range_succ]
    ring
  }

/-- A complete coprime sweep is an exact translation on every admissible phase. -/
theorem WholeBaseHighOffsetEventSweep (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v) (highOffset : u + v ≤ a)
    (coprime : Nat.Coprime u v) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt t n k) :
    Iterate (WholeBaseHighOffsetEvent p) v n =
      n + s * (t : ℤ) ^ (a - u - v + 1 + k) * WholeBaseGeometricSum t v := by
  rcases atOrder with ⟨w, state, guard⟩
  have trace := WholeBaseHighOffsetResidualTrace p t u v a k s n w tLower uBelow
    kBelow highOffset divisor multiplier offset ⟨w, state, guard⟩ state v
  have phase : (k + v * u) % v = k := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt kBelow]
  have kernel : (∑ j ∈ Finset.range v, (t : ℤ) ^ (a - u - (k + j * u) % v)) =
      (t : ℤ) ^ (a - u - (v - 1)) * WholeBaseGeometricSum t v := by
    rw [Finset.sum_range]
    exact WholeBaseHighOffsetPhaseKernel t u v a k (by omega) coprime highOffset
  have exponent : k + (a - u - (v - 1)) = a - u - v + 1 + k := by omega
  rw [phase, kernel] at trace
  calc
    Iterate (WholeBaseHighOffsetEvent p) v n =
        (t : ℤ) ^ k *
          (w + s * ((t : ℤ) ^ (a - u - (v - 1)) * WholeBaseGeometricSum t v)) := trace
    _ = n + s * (t : ℤ) ^ (a - u - v + 1 + k) * WholeBaseGeometricSum t v := by
      rw [state, ← exponent, pow_add]
      ring

end GeneralizedCollatz
