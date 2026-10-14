-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import ThreeAffineClosure
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace GeneralizedCollatz.ClassicalThreeReturn

/-- An odd positive quotient of `4` by a positive power of two is `1`. -/
theorem UnitEdge (a : ℕ) (y : ℤ) (ha : 0 < a) (hy : 0 < y) (ho : Odd y)
    (he : (2 : ℤ) ^ a * y = 4) : a = 2 ∧ y = 1 := by
  have hp : (0 : ℤ) < 2 ^ a := by positivity
  have hbound : (2 : ℤ) ^ a ≤ 4 := by nlinarith
  have ha3 : a < 3 := by
    by_contra h
    have hm := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega : 3 ≤ a)
    norm_num at hm
    omega
  have ha12 : a = 1 ∨ a = 2 := by omega
  rcases ha12 with rfl | rfl
  · norm_num at he
    have hy2 : y = 2 := by omega
    rw [hy2] at ho
    exact (show ¬ Odd (2 : ℤ) by decide) ho |>.elim
  · norm_num at he
    exact ⟨rfl, by omega⟩

/-- The product window forces total exponent five if all three states exceed one. -/
theorem ExponentWindow (a b c : ℕ) (x y z : ℤ)
    (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (he : (2 : ℤ) ^ a * y = 3 * x + 1)
    (hf : (2 : ℤ) ^ b * z = 3 * y + 1)
    (hg : (2 : ℤ) ^ c * x = 3 * z + 1) : a + b + c = 5 := by
  have hprod : (2 : ℤ) ^ (a + b + c) * (x * y * z) =
      (3 * x + 1) * (3 * y + 1) * (3 * z + 1) := by
    rw [← he, ← hf, ← hg, pow_add, pow_add]
    ring
  have hxyz : (0 : ℤ) < x * y * z := by positivity
  -- Multiply the three individual ratio bounds without dividing by a state.
  have hl1 : (3 * x) * (3 * y) < (3 * x + 1) * (3 * y + 1) := by
    nlinarith
  have hl2 := mul_lt_mul_of_pos_right hl1 (by positivity : (0 : ℤ) < 3 * z)
  have hl3 := mul_lt_mul_of_pos_left (by omega : 3 * z < 3 * z + 1)
    (by positivity : (0 : ℤ) < (3 * x + 1) * (3 * y + 1))
  have hlow : (27 : ℤ) < 2 ^ (a + b + c) := by
    nlinarith [hprod]
  have hu1 : (9 * x + 3) * (9 * y + 3) ≤ (10 * x) * (10 * y) :=
    mul_le_mul (by omega) (by omega) (by positivity) (by positivity)
  have hu2 := mul_le_mul hu1 (by omega : 9 * z + 3 ≤ 10 * z)
    (by positivity : (0 : ℤ) ≤ 9 * z + 3)
    (by positivity : (0 : ℤ) ≤ (10 * x) * (10 * y))
  have hupp : (27 : ℤ) * 2 ^ (a + b + c) ≤ 1000 := by
    nlinarith [hprod]
  have hslo : 5 ≤ a + b + c := by
    by_contra h
    have hm := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (by omega : a + b + c ≤ 4)
    norm_num at hm
    omega
  have hshi : a + b + c < 6 := by
    by_contra h
    have hm := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (by omega : 6 ≤ a + b + c)
    norm_num at hm
    omega
  omega

/-- Six positive compositions of five fail the necessary closure divisibility. -/
theorem NoExponentFive (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hs : a + b + c = 5) : ¬ Delta a b c 3 ∣ ClosureNumerator a b 3 := by
  have ha4 : a ≤ 3 := by omega
  have hb4 : b ≤ 3 := by omega
  have hc4 : c ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    norm_num [Delta, ClosureNumerator] at *

/-- Every positive odd classical closure with three return edges repeats the unit state. -/
theorem Classification (a b c : ℕ) (x y z : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hox : Odd x) (hoy : Odd y) (hoz : Odd z)
    (he : (2 : ℤ) ^ a * y = 3 * x + 1)
    (hf : (2 : ℤ) ^ b * z = 3 * y + 1)
    (hg : (2 : ℤ) ^ c * x = 3 * z + 1) :
    x = 1 ∧ y = 1 ∧ z = 1 ∧ a = 2 ∧ b = 2 ∧ c = 2 := by
  have hunit : x = 1 ∨ y = 1 ∨ z = 1 := by
    by_contra h
    have hx1 : x ≠ 1 := fun heq => h (Or.inl heq)
    have hy1 : y ≠ 1 := fun heq => h (Or.inr (Or.inl heq))
    have hz1 : z ≠ 1 := fun heq => h (Or.inr (Or.inr heq))
    have hx3 : 3 ≤ x := by
      obtain ⟨k, hk⟩ := hox
      omega
    have hy3 : 3 ≤ y := by
      obtain ⟨k, hk⟩ := hoy
      omega
    have hz3 : 3 ≤ z := by
      obtain ⟨k, hk⟩ := hoz
      omega
    have hs := ExponentWindow a b c x y z hx3 hy3 hz3 he hf hg
    have hd := (ThreeAffineClosure a b c 3 x y z ha hb hc (by decide) he hf hg).2.1
    exact NoExponentFive a b c ha hb hc hs hd
  rcases hunit with hx1 | hy1 | hz1
  · have ha2 := UnitEdge a y ha hy hoy (by simpa [hx1] using he)
    have hb2 := UnitEdge b z hb hz hoz (by simpa [ha2.2] using hf)
    have hc2 := UnitEdge c x hc hx hox (by simpa [hb2.2] using hg)
    exact ⟨hx1, ha2.2, hb2.2, ha2.1, hb2.1, hc2.1⟩
  · have hb2 := UnitEdge b z hb hz hoz (by simpa [hy1] using hf)
    have hc2 := UnitEdge c x hc hx hox (by simpa [hb2.2] using hg)
    have ha2 := UnitEdge a y ha hy hoy (by simpa [hc2.2] using he)
    exact ⟨hc2.2, hy1, hb2.2, ha2.1, hb2.1, hc2.1⟩
  · have hc2 := UnitEdge c x hc hx hox (by simpa [hz1] using hg)
    have ha2 := UnitEdge a y ha hy hoy (by simpa [hc2.2] using he)
    have hb2 := UnitEdge b z hb hz hoz (by simpa [ha2.2] using hf)
    exact ⟨hc2.2, ha2.2, hz1, ha2.1, hb2.1, hc2.1⟩

/-- Ordered closure numerator for five classical odd-return edges. -/
def FiveNumerator (a b c d : ℕ) : ℤ :=
  81 + 27 * 2 ^ a + 9 * 2 ^ (a + b) + 3 * 2 ^ (a + b + c) +
    2 ^ (a + b + c + d)

/-- Five legal edge equations imply the ordered elimination identity. -/
theorem FiveElimination (a b c d e : ℕ) (v w x y z : ℤ)
    (h0 : (2 : ℤ) ^ a * w = 3 * v + 1)
    (h1 : (2 : ℤ) ^ b * x = 3 * w + 1)
    (h2 : (2 : ℤ) ^ c * y = 3 * x + 1)
    (h3 : (2 : ℤ) ^ d * z = 3 * y + 1)
    (h4 : (2 : ℤ) ^ e * v = 3 * z + 1) :
    ((2 : ℤ) ^ (a + b + c + d + e) - 243) * v = FiveNumerator a b c d := by
  unfold FiveNumerator
  simp only [pow_add]
  linear_combination 81 * h0 + 27 * 2 ^ a * h1 +
    9 * 2 ^ (a + b) * h2 + 3 * 2 ^ (a + b + c) * h3 +
    2 ^ (a + b + c + d) * h4

/-- All 35 positive compositions of eight fail five-edge closure divisibility. -/
theorem NoFiveExponentEight (a b c d e : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hs : a + b + c + d + e = 8) : ¬ (13 : ℤ) ∣ FiveNumerator a b c d := by
  have ha4 : a ≤ 4 := by omega
  have hb4 : b ≤ 4 := by omega
  have hc4 : c ≤ 4 := by omega
  have hd4 : d ≤ 4 := by omega
  have heq : e = 8 - a - b - c - d := by omega
  subst e
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    norm_num [FiveNumerator] at *

end GeneralizedCollatz.ClassicalThreeReturn
