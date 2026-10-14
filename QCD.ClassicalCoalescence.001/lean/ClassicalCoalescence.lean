-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace GeneralizedCollatz.ClassicalCoalescence

/-- The classical shortcut, with one affine branch and its forced division in one tick. -/
def Shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Exact halving of a displayed even state. -/
theorem EvenStep (k : ℕ) : Shortcut (2 * k) = k := by
  simp [Shortcut]

/-- Exact evaluation of a displayed odd state. -/
theorem OddStep (k : ℕ) : Shortcut (2 * k + 1) = 3 * k + 2 := by
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  simp only [Shortcut, hmod, if_neg (by decide : ¬ (1 : ℕ) = 0)]
  omega

/-- Each state on the six-tick source cylinder is fixed by its affine coefficients. -/
theorem SourceStates (t : ℕ) :
    Shortcut (79 + 128 * t) = 119 + 192 * t ∧
    Shortcut (119 + 192 * t) = 179 + 288 * t ∧
    Shortcut (179 + 288 * t) = 269 + 432 * t ∧
    Shortcut (269 + 432 * t) = 404 + 648 * t ∧
    Shortcut (404 + 648 * t) = 202 + 324 * t ∧
    Shortcut (202 + 324 * t) = 101 + 162 * t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 79 + 128 * t = 2 * (39 + 64 * t) + 1 by ring, OddStep]
    ring
  · rw [show 119 + 192 * t = 2 * (59 + 96 * t) + 1 by ring, OddStep]
    ring
  · rw [show 179 + 288 * t = 2 * (89 + 144 * t) + 1 by ring, OddStep]
    ring
  · rw [show 269 + 432 * t = 2 * (134 + 216 * t) + 1 by ring, OddStep]
    ring
  · rw [show 404 + 648 * t = 2 * (202 + 324 * t) by ring, EvenStep]
  · rw [show 202 + 324 * t = 2 * (101 + 162 * t) by ring, EvenStep]

/-- The source word `111100` and the parent word `1` have the same endpoint. -/
theorem CylinderJoin (t : ℕ) :
    Shortcut^[6] (79 + 128 * t) = Shortcut (67 + 108 * t) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := SourceStates t
  have hp : Shortcut (67 + 108 * t) = 101 + 162 * t := by
    rw [show 67 + 108 * t = 2 * (33 + 54 * t) + 1 by ring, OddStep]
    ring
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    h0, h1, h2, h3, h4, h5, hp]

/-- The shared endpoint lies above the source, but the parent is strictly smaller. -/
theorem CylinderOrder (t : ℕ) :
    1 ≤ 67 + 108 * t ∧ 67 + 108 * t < 79 + 128 * t ∧
      79 + 128 * t < 101 + 162 * t := by
  omega

/-- No positive source tick up to the join is a forward descent. -/
theorem CylinderNoDescent (t j : ℕ) (hj : 1 ≤ j) (hmax : j ≤ 6) :
    79 + 128 * t < Shortcut^[j] (79 + 128 * t) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := SourceStates t
  have hs : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      h0, h1, h2, h3, h4, h5] <;> omega

/-- The residual class retains the exact odd-burst length and both congruence guards. -/
def Residual (n : ℕ) : Prop :=
  ∃ a u : ℕ, 2 ≤ a ∧ 0 < u ∧ Odd u ∧ ¬ 3 ∣ u ∧
    (3 ^ a * u) % 4 = 3 ∧ n + 1 = 2 ^ a * u

/-- The legal parent word `110` ends at every integer congruent to four modulo nine. -/
theorem Inverse110 (t : ℕ) : Shortcut^[3] (3 + 8 * t) = 4 + 9 * t := by
  have h0 : Shortcut (3 + 8 * t) = 5 + 12 * t := by
    rw [show 3 + 8 * t = 2 * (1 + 4 * t) + 1 by ring, OddStep]
    ring
  have h1 : Shortcut (5 + 12 * t) = 8 + 18 * t := by
    rw [show 5 + 12 * t = 2 * (2 + 6 * t) + 1 by ring, OddStep]
    ring
  have h2 : Shortcut (8 + 18 * t) = 4 + 9 * t := by
    rw [show 8 + 18 * t = 2 * (4 + 9 * t) by ring, EvenStep]
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply, h0, h1, h2]

/-- This inverse certificate gives a smaller parent with a uniform eight-ninths bound. -/
theorem Inverse110Order (t : ℕ) :
    0 < 3 + 8 * t ∧ 3 + 8 * t < 4 + 9 * t ∧
      9 * (3 + 8 * t) < 8 * (4 + 9 * t) := by
  omega

/-- The five-letter cylinder `11010` has a strictly smaller endpoint. -/
theorem FiveLetterDescent (t : ℕ) :
    Shortcut^[5] (11 + 32 * t) = 10 + 27 * t ∧
      10 + 27 * t < 11 + 32 * t := by
  have h0 : Shortcut (11 + 32 * t) = 17 + 48 * t := by
    rw [show 11 + 32 * t = 2 * (5 + 16 * t) + 1 by ring, OddStep]
    ring
  have h1 : Shortcut (17 + 48 * t) = 26 + 72 * t := by
    rw [show 17 + 48 * t = 2 * (8 + 24 * t) + 1 by ring, OddStep]
    ring
  have h2 : Shortcut (26 + 72 * t) = 13 + 36 * t := by
    rw [show 26 + 72 * t = 2 * (13 + 36 * t) by ring, EvenStep]
  have h3 : Shortcut (13 + 36 * t) = 20 + 54 * t := by
    rw [show 13 + 36 * t = 2 * (6 + 18 * t) + 1 by ring, OddStep]
    ring
  have h4 : Shortcut (20 + 54 * t) = 10 + 27 * t := by
    rw [show 20 + 54 * t = 2 * (10 + 27 * t) by ring, EvenStep]
  constructor
  · norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      h0, h1, h2, h3, h4]
  · omega

/-- These source seeds are genuinely residual, with odd-burst length five. -/
theorem ResidualCylinder (t : ℕ) : Residual (31 + 1152 * t) := by
  refine ⟨5, 1 + 36 * t, by decide, by omega, ?_, ?_, ?_, by ring⟩
  · exact ⟨18 * t, by ring⟩
  · intro hd
    have hz := Nat.mod_eq_zero_of_dvd hd
    norm_num [Nat.add_mod, Nat.mul_mod] at hz
  · norm_num [Nat.add_mod, Nat.mul_mod]

/-- A growing residual source joins the smaller parent before taking any source step. -/
theorem ResidualCylinderJoin (t : ℕ) :
    Shortcut^[3] (27 + 1024 * t) = 31 + 1152 * t ∧
      0 < 27 + 1024 * t ∧ 27 + 1024 * t < 31 + 1152 * t := by
  have hj := Inverse110 (3 + 128 * t)
  have hp : 3 + 8 * (3 + 128 * t) = 27 + 1024 * t := by ring
  have hn : 4 + 9 * (3 + 128 * t) = 31 + 1152 * t := by ring
  rw [hp, hn] at hj
  exact ⟨hj, by omega, by omega⟩

/-- The expanding parent word `111010` removes the residue class ten modulo eighty-one. -/
theorem Inverse111010 (t : ℕ) :
    Shortcut^[6] (7 + 64 * t) = 10 + 81 * t ∧
      0 < 7 + 64 * t ∧ 7 + 64 * t < 10 + 81 * t ∧
        9 * (7 + 64 * t) < 8 * (10 + 81 * t) := by
  have h0 : Shortcut (7 + 64 * t) = 11 + 96 * t := by
    rw [show 7 + 64 * t = 2 * (3 + 32 * t) + 1 by ring, OddStep]
    ring
  have h1 : Shortcut (11 + 96 * t) = 17 + 144 * t := by
    rw [show 11 + 96 * t = 2 * (5 + 48 * t) + 1 by ring, OddStep]
    ring
  have h2 : Shortcut (17 + 144 * t) = 26 + 216 * t := by
    rw [show 17 + 144 * t = 2 * (8 + 72 * t) + 1 by ring, OddStep]
    ring
  have h3 : Shortcut (26 + 216 * t) = 13 + 108 * t := by
    rw [show 26 + 216 * t = 2 * (13 + 108 * t) by ring, EvenStep]
  have h4 : Shortcut (13 + 108 * t) = 20 + 162 * t := by
    rw [show 13 + 108 * t = 2 * (6 + 54 * t) + 1 by ring, OddStep]
    ring
  have h5 : Shortcut (20 + 162 * t) = 10 + 81 * t := by
    rw [show 20 + 162 * t = 2 * (10 + 81 * t) by ring, EvenStep]
  refine ⟨?_, by omega, by omega, by omega⟩
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    h0, h1, h2, h3, h4, h5]

end GeneralizedCollatz.ClassicalCoalescence
