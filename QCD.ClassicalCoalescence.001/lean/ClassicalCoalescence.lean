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

/-- The word `11011010` sends an entire cylinder to a uniformly smaller state. -/
theorem EightLetterDescent (t : ℕ) :
    Shortcut^[8] (123 + 256 * t) = 118 + 243 * t ∧
      0 < 118 + 243 * t ∧ 118 + 243 * t < 123 + 256 * t ∧
        123 * (118 + 243 * t) ≤ 118 * (123 + 256 * t) := by
  have h0 : Shortcut (123 + 256 * t) = 185 + 384 * t := by
    rw [show 123 + 256 * t = 2 * (61 + 128 * t) + 1 by ring, OddStep]
    ring
  have h1 : Shortcut (185 + 384 * t) = 278 + 576 * t := by
    rw [show 185 + 384 * t = 2 * (92 + 192 * t) + 1 by ring, OddStep]
    ring
  have h2 : Shortcut (278 + 576 * t) = 139 + 288 * t := by
    rw [show 278 + 576 * t = 2 * (139 + 288 * t) by ring, EvenStep]
  have h3 : Shortcut (139 + 288 * t) = 209 + 432 * t := by
    rw [show 139 + 288 * t = 2 * (69 + 144 * t) + 1 by ring, OddStep]
    ring
  have h4 : Shortcut (209 + 432 * t) = 314 + 648 * t := by
    rw [show 209 + 432 * t = 2 * (104 + 216 * t) + 1 by ring, OddStep]
    ring
  have h5 : Shortcut (314 + 648 * t) = 157 + 324 * t := by
    rw [show 314 + 648 * t = 2 * (157 + 324 * t) by ring, EvenStep]
  have h6 : Shortcut (157 + 324 * t) = 236 + 486 * t := by
    rw [show 157 + 324 * t = 2 * (78 + 162 * t) + 1 by ring, OddStep]
    ring
  have h7 : Shortcut (236 + 486 * t) = 118 + 243 * t := by
    rw [show 236 + 486 * t = 2 * (118 + 243 * t) by ring, EvenStep]
  refine ⟨?_, by omega, by omega, by omega⟩
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    h0, h1, h2, h3, h4, h5, h6, h7]

/-- The word `11110100` directly contracts the cylinder `175` modulo `256`. -/
theorem Direct175Descent (t : ℕ) :
    Shortcut^[8] (175 + 256 * t) = 167 + 243 * t ∧
      0 < 167 + 243 * t ∧ 167 + 243 * t < 175 + 256 * t ∧
        24 * (167 + 243 * t) ≤ 23 * (175 + 256 * t) := by
  have h0 : Shortcut (175 + 256 * t) = 263 + 384 * t := by
    rw [show 175 + 256 * t = 2 * (87 + 128 * t) + 1 by ring, OddStep]
    ring
  have h1 : Shortcut (263 + 384 * t) = 395 + 576 * t := by
    rw [show 263 + 384 * t = 2 * (131 + 192 * t) + 1 by ring, OddStep]
    ring
  have h2 : Shortcut (395 + 576 * t) = 593 + 864 * t := by
    rw [show 395 + 576 * t = 2 * (197 + 288 * t) + 1 by ring, OddStep]
    ring
  have h3 : Shortcut (593 + 864 * t) = 890 + 1296 * t := by
    rw [show 593 + 864 * t = 2 * (296 + 432 * t) + 1 by ring, OddStep]
    ring
  have h4 : Shortcut (890 + 1296 * t) = 445 + 648 * t := by
    rw [show 890 + 1296 * t = 2 * (445 + 648 * t) by ring, EvenStep]
  have h5 : Shortcut (445 + 648 * t) = 668 + 972 * t := by
    rw [show 445 + 648 * t = 2 * (222 + 324 * t) + 1 by ring, OddStep]
    ring
  have h6 : Shortcut (668 + 972 * t) = 334 + 486 * t := by
    rw [show 668 + 972 * t = 2 * (334 + 486 * t) by ring, EvenStep]
  have h7 : Shortcut (334 + 486 * t) = 167 + 243 * t := by
    rw [show 334 + 486 * t = 2 * (167 + 243 * t) by ring, EvenStep]
  refine ⟨?_, by omega, by omega, by omega⟩
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    h0, h1, h2, h3, h4, h5, h6, h7]

/-- The word `11101010` directly contracts the cylinder `199` modulo `256`. -/
theorem Direct199Descent (t : ℕ) :
    Shortcut^[8] (199 + 256 * t) = 190 + 243 * t ∧
      0 < 190 + 243 * t ∧ 190 + 243 * t < 199 + 256 * t ∧
        24 * (190 + 243 * t) ≤ 23 * (199 + 256 * t) := by
  have h0 : Shortcut (199 + 256 * t) = 299 + 384 * t := by
    rw [show 199 + 256 * t = 2 * (99 + 128 * t) + 1 by ring, OddStep]
    ring
  have h1 : Shortcut (299 + 384 * t) = 449 + 576 * t := by
    rw [show 299 + 384 * t = 2 * (149 + 192 * t) + 1 by ring, OddStep]
    ring
  have h2 : Shortcut (449 + 576 * t) = 674 + 864 * t := by
    rw [show 449 + 576 * t = 2 * (224 + 288 * t) + 1 by ring, OddStep]
    ring
  have h3 : Shortcut (674 + 864 * t) = 337 + 432 * t := by
    rw [show 674 + 864 * t = 2 * (337 + 432 * t) by ring, EvenStep]
  have h4 : Shortcut (337 + 432 * t) = 506 + 648 * t := by
    rw [show 337 + 432 * t = 2 * (168 + 216 * t) + 1 by ring, OddStep]
    ring
  have h5 : Shortcut (506 + 648 * t) = 253 + 324 * t := by
    rw [show 506 + 648 * t = 2 * (253 + 324 * t) by ring, EvenStep]
  have h6 : Shortcut (253 + 324 * t) = 380 + 486 * t := by
    rw [show 253 + 324 * t = 2 * (126 + 162 * t) + 1 by ring, OddStep]
    ring
  have h7 : Shortcut (380 + 486 * t) = 190 + 243 * t := by
    rw [show 380 + 486 * t = 2 * (190 + 243 * t) by ring, EvenStep]
  refine ⟨?_, by omega, by omega, by omega⟩
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    h0, h1, h2, h3, h4, h5, h6, h7]

/-- The word `1111101000` directly contracts the cylinder `287` modulo `1024`. -/
theorem Direct287Descent (t : ℕ) :
    Shortcut^[10] (287 + 1024 * t) = 205 + 729 * t ∧
      0 < 205 + 729 * t ∧ 205 + 729 * t < 287 + 1024 * t ∧
        24 * (205 + 729 * t) ≤ 23 * (287 + 1024 * t) := by
  have h0 : Shortcut (287 + 1024 * t) = 431 + 1536 * t := by
    rw [show 287 + 1024 * t = 2 * (143 + 512 * t) + 1 by ring, OddStep]
    ring
  have h1 : Shortcut (431 + 1536 * t) = 647 + 2304 * t := by
    rw [show 431 + 1536 * t = 2 * (215 + 768 * t) + 1 by ring, OddStep]
    ring
  have h2 : Shortcut (647 + 2304 * t) = 971 + 3456 * t := by
    rw [show 647 + 2304 * t = 2 * (323 + 1152 * t) + 1 by ring, OddStep]
    ring
  have h3 : Shortcut (971 + 3456 * t) = 1457 + 5184 * t := by
    rw [show 971 + 3456 * t = 2 * (485 + 1728 * t) + 1 by ring, OddStep]
    ring
  have h4 : Shortcut (1457 + 5184 * t) = 2186 + 7776 * t := by
    rw [show 1457 + 5184 * t = 2 * (728 + 2592 * t) + 1 by ring, OddStep]
    ring
  have h5 : Shortcut (2186 + 7776 * t) = 1093 + 3888 * t := by
    rw [show 2186 + 7776 * t = 2 * (1093 + 3888 * t) by ring, EvenStep]
  have h6 : Shortcut (1093 + 3888 * t) = 1640 + 5832 * t := by
    rw [show 1093 + 3888 * t = 2 * (546 + 1944 * t) + 1 by ring, OddStep]
    ring
  have h7 : Shortcut (1640 + 5832 * t) = 820 + 2916 * t := by
    rw [show 1640 + 5832 * t = 2 * (820 + 2916 * t) by ring, EvenStep]
  have h8 : Shortcut (820 + 2916 * t) = 410 + 1458 * t := by
    rw [show 820 + 2916 * t = 2 * (410 + 1458 * t) by ring, EvenStep]
  have h9 : Shortcut (410 + 1458 * t) = 205 + 729 * t := by
    rw [show 410 + 1458 * t = 2 * (205 + 729 * t) by ring, EvenStep]
  refine ⟨?_, by omega, by omega, by omega⟩
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- The word `1111011000` directly contracts the cylinder `367` modulo `1024`. -/
theorem Direct367Descent (t : ℕ) :
    Shortcut^[10] (367 + 1024 * t) = 262 + 729 * t ∧
      0 < 262 + 729 * t ∧ 262 + 729 * t < 367 + 1024 * t ∧
        24 * (262 + 729 * t) ≤ 23 * (367 + 1024 * t) := by
  have h0 : Shortcut (367 + 1024 * t) = 551 + 1536 * t := by
    rw [show 367 + 1024 * t = 2 * (183 + 512 * t) + 1 by ring, OddStep]
    ring
  have h1 : Shortcut (551 + 1536 * t) = 827 + 2304 * t := by
    rw [show 551 + 1536 * t = 2 * (275 + 768 * t) + 1 by ring, OddStep]
    ring
  have h2 : Shortcut (827 + 2304 * t) = 1241 + 3456 * t := by
    rw [show 827 + 2304 * t = 2 * (413 + 1152 * t) + 1 by ring, OddStep]
    ring
  have h3 : Shortcut (1241 + 3456 * t) = 1862 + 5184 * t := by
    rw [show 1241 + 3456 * t = 2 * (620 + 1728 * t) + 1 by ring, OddStep]
    ring
  have h4 : Shortcut (1862 + 5184 * t) = 931 + 2592 * t := by
    rw [show 1862 + 5184 * t = 2 * (931 + 2592 * t) by ring, EvenStep]
  have h5 : Shortcut (931 + 2592 * t) = 1397 + 3888 * t := by
    rw [show 931 + 2592 * t = 2 * (465 + 1296 * t) + 1 by ring, OddStep]
    ring
  have h6 : Shortcut (1397 + 3888 * t) = 2096 + 5832 * t := by
    rw [show 1397 + 3888 * t = 2 * (698 + 1944 * t) + 1 by ring, OddStep]
    ring
  have h7 : Shortcut (2096 + 5832 * t) = 1048 + 2916 * t := by
    rw [show 2096 + 5832 * t = 2 * (1048 + 2916 * t) by ring, EvenStep]
  have h8 : Shortcut (1048 + 2916 * t) = 524 + 1458 * t := by
    rw [show 1048 + 2916 * t = 2 * (524 + 1458 * t) by ring, EvenStep]
  have h9 : Shortcut (524 + 1458 * t) = 262 + 729 * t := by
    rw [show 524 + 1458 * t = 2 * (262 + 729 * t) by ring, EvenStep]
  refine ⟨?_, by omega, by omega, by omega⟩
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- The word `1101101100` directly contracts the cylinder `507` modulo `1024`. -/
theorem Direct507Descent (t : ℕ) :
    Shortcut^[10] (507 + 1024 * t) = 362 + 729 * t ∧
      0 < 362 + 729 * t ∧ 362 + 729 * t < 507 + 1024 * t ∧
        24 * (362 + 729 * t) ≤ 23 * (507 + 1024 * t) := by
  have h0 : Shortcut (507 + 1024 * t) = 761 + 1536 * t := by
    rw [show 507 + 1024 * t = 2 * (253 + 512 * t) + 1 by ring, OddStep]
    ring
  have h1 : Shortcut (761 + 1536 * t) = 1142 + 2304 * t := by
    rw [show 761 + 1536 * t = 2 * (380 + 768 * t) + 1 by ring, OddStep]
    ring
  have h2 : Shortcut (1142 + 2304 * t) = 571 + 1152 * t := by
    rw [show 1142 + 2304 * t = 2 * (571 + 1152 * t) by ring, EvenStep]
  have h3 : Shortcut (571 + 1152 * t) = 857 + 1728 * t := by
    rw [show 571 + 1152 * t = 2 * (285 + 576 * t) + 1 by ring, OddStep]
    ring
  have h4 : Shortcut (857 + 1728 * t) = 1286 + 2592 * t := by
    rw [show 857 + 1728 * t = 2 * (428 + 864 * t) + 1 by ring, OddStep]
    ring
  have h5 : Shortcut (1286 + 2592 * t) = 643 + 1296 * t := by
    rw [show 1286 + 2592 * t = 2 * (643 + 1296 * t) by ring, EvenStep]
  have h6 : Shortcut (643 + 1296 * t) = 965 + 1944 * t := by
    rw [show 643 + 1296 * t = 2 * (321 + 648 * t) + 1 by ring, OddStep]
    ring
  have h7 : Shortcut (965 + 1944 * t) = 1448 + 2916 * t := by
    rw [show 965 + 1944 * t = 2 * (482 + 972 * t) + 1 by ring, OddStep]
    ring
  have h8 : Shortcut (1448 + 2916 * t) = 724 + 1458 * t := by
    rw [show 1448 + 2916 * t = 2 * (724 + 1458 * t) by ring, EvenStep]
  have h9 : Shortcut (724 + 1458 * t) = 362 + 729 * t := by
    rw [show 724 + 1458 * t = 2 * (362 + 729 * t) by ring, EvenStep]
  refine ⟨?_, by omega, by omega, by omega⟩
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- The word `1110101100` directly contracts the cylinder `583` modulo `1024`. -/
theorem Direct583Descent (t : ℕ) :
    Shortcut^[10] (583 + 1024 * t) = 416 + 729 * t ∧
      0 < 416 + 729 * t ∧ 416 + 729 * t < 583 + 1024 * t ∧
        24 * (416 + 729 * t) ≤ 23 * (583 + 1024 * t) := by
  have h0 : Shortcut (583 + 1024 * t) = 875 + 1536 * t := by
    rw [show 583 + 1024 * t = 2 * (291 + 512 * t) + 1 by ring, OddStep]
    ring
  have h1 : Shortcut (875 + 1536 * t) = 1313 + 2304 * t := by
    rw [show 875 + 1536 * t = 2 * (437 + 768 * t) + 1 by ring, OddStep]
    ring
  have h2 : Shortcut (1313 + 2304 * t) = 1970 + 3456 * t := by
    rw [show 1313 + 2304 * t = 2 * (656 + 1152 * t) + 1 by ring, OddStep]
    ring
  have h3 : Shortcut (1970 + 3456 * t) = 985 + 1728 * t := by
    rw [show 1970 + 3456 * t = 2 * (985 + 1728 * t) by ring, EvenStep]
  have h4 : Shortcut (985 + 1728 * t) = 1478 + 2592 * t := by
    rw [show 985 + 1728 * t = 2 * (492 + 864 * t) + 1 by ring, OddStep]
    ring
  have h5 : Shortcut (1478 + 2592 * t) = 739 + 1296 * t := by
    rw [show 1478 + 2592 * t = 2 * (739 + 1296 * t) by ring, EvenStep]
  have h6 : Shortcut (739 + 1296 * t) = 1109 + 1944 * t := by
    rw [show 739 + 1296 * t = 2 * (369 + 648 * t) + 1 by ring, OddStep]
    ring
  have h7 : Shortcut (1109 + 1944 * t) = 1664 + 2916 * t := by
    rw [show 1109 + 1944 * t = 2 * (554 + 972 * t) + 1 by ring, OddStep]
    ring
  have h8 : Shortcut (1664 + 2916 * t) = 832 + 1458 * t := by
    rw [show 1664 + 2916 * t = 2 * (832 + 1458 * t) by ring, EvenStep]
  have h9 : Shortcut (832 + 1458 * t) = 416 + 729 * t := by
    rw [show 832 + 1458 * t = 2 * (416 + 729 * t) by ring, EvenStep]
  refine ⟨?_, by omega, by omega, by omega⟩
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- The word `1111010100` directly contracts the cylinder `815` modulo `1024`. -/
theorem Direct815Descent (t : ℕ) :
    Shortcut^[10] (815 + 1024 * t) = 581 + 729 * t ∧
      0 < 581 + 729 * t ∧ 581 + 729 * t < 815 + 1024 * t ∧
        24 * (581 + 729 * t) ≤ 23 * (815 + 1024 * t) := by
  have h0 : Shortcut (815 + 1024 * t) = 1223 + 1536 * t := by
    rw [show 815 + 1024 * t = 2 * (407 + 512 * t) + 1 by ring, OddStep]
    ring
  have h1 : Shortcut (1223 + 1536 * t) = 1835 + 2304 * t := by
    rw [show 1223 + 1536 * t = 2 * (611 + 768 * t) + 1 by ring, OddStep]
    ring
  have h2 : Shortcut (1835 + 2304 * t) = 2753 + 3456 * t := by
    rw [show 1835 + 2304 * t = 2 * (917 + 1152 * t) + 1 by ring, OddStep]
    ring
  have h3 : Shortcut (2753 + 3456 * t) = 4130 + 5184 * t := by
    rw [show 2753 + 3456 * t = 2 * (1376 + 1728 * t) + 1 by ring, OddStep]
    ring
  have h4 : Shortcut (4130 + 5184 * t) = 2065 + 2592 * t := by
    rw [show 4130 + 5184 * t = 2 * (2065 + 2592 * t) by ring, EvenStep]
  have h5 : Shortcut (2065 + 2592 * t) = 3098 + 3888 * t := by
    rw [show 2065 + 2592 * t = 2 * (1032 + 1296 * t) + 1 by ring, OddStep]
    ring
  have h6 : Shortcut (3098 + 3888 * t) = 1549 + 1944 * t := by
    rw [show 3098 + 3888 * t = 2 * (1549 + 1944 * t) by ring, EvenStep]
  have h7 : Shortcut (1549 + 1944 * t) = 2324 + 2916 * t := by
    rw [show 1549 + 1944 * t = 2 * (774 + 972 * t) + 1 by ring, OddStep]
    ring
  have h8 : Shortcut (2324 + 2916 * t) = 1162 + 1458 * t := by
    rw [show 2324 + 2916 * t = 2 * (1162 + 1458 * t) by ring, EvenStep]
  have h9 : Shortcut (1162 + 1458 * t) = 581 + 729 * t := by
    rw [show 1162 + 1458 * t = 2 * (581 + 729 * t) by ring, EvenStep]
  refine ⟨?_, by omega, by omega, by omega⟩
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

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

/-- Counts odd shortcut inputs in a finite prefix. -/
def PrefixOddCount (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => (if n % 2 = 0 then 0 else 1) + PrefixOddCount (Shortcut n) h

/-- One even base step transports an arbitrary even perturbation. -/
theorem ShortcutEvenLift (k m : ℕ) :
    Shortcut (2 * k + 2 * m) = Shortcut (2 * k) + m := by
  rw [show 2 * k + 2 * m = 2 * (k + m) by ring, EvenStep, EvenStep]

/-- One odd base step triples an arbitrary even perturbation. -/
theorem ShortcutOddLift (k m : ℕ) :
    Shortcut ((2 * k + 1) + 2 * m) = Shortcut (2 * k + 1) + 3 * m := by
  rw [show (2 * k + 1) + 2 * m = 2 * (k + m) + 1 by ring, OddStep, OddStep]
  ring

/-- A dyadic perturbation retains the base word and gains a three per odd input. -/
theorem DyadicLift (n h t : ℕ) :
    Shortcut^[h] (n + 2 ^ h * t) =
      Shortcut^[h] n + 3 ^ (PrefixOddCount n h) * t := by
  induction h generalizing n t with
  | zero => simp [PrefixOddCount]
  | succ h ih =>
      simp only [Function.iterate_succ_apply]
      rcases Nat.even_or_odd n with he | ho
      · obtain ⟨k, hk⟩ := he
        have hn : n = 2 * k := by omega
        have hpow : 2 ^ (h + 1) * t = 2 * (2 ^ h * t) := by ring
        rw [hn, hpow, ShortcutEvenLift]
        rw [ih]
        have hmod : (2 * k) % 2 = 0 := by omega
        simp only [PrefixOddCount, hmod, if_pos, zero_add]
      · obtain ⟨k, hk⟩ := ho
        have hn : n = 2 * k + 1 := by omega
        have hpow : 2 ^ (h + 1) * t = 2 * (2 ^ h * t) := by ring
        rw [hn, hpow, ShortcutOddLift]
        rw [show 3 * (2 ^ h * t) = 2 ^ h * (3 * t) by ring, ih]
        have hmod : (2 * k + 1) % 2 = 1 := by omega
        simp only [PrefixOddCount, hmod, if_neg (by decide : ¬ (1 : ℕ) = 0)]
        ring

/-- The first depth-ten cylinder has its exact affine descendant. -/
theorem FurtherDirect347 (t : ℕ) :
    Shortcut^[10] (347 + 1024 * t) = 248 + 729 * t ∧
      4 * (248 + 729 * t) < 3 * (347 + 1024 * t) := by
  have hb : Shortcut^[10] 347 = 248 := by decide
  have hc : PrefixOddCount 347 10 = 6 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 347 10 t
  · omega

/-- The second depth-ten cylinder has its exact affine descendant. -/
theorem FurtherDirect423 (t : ℕ) :
    Shortcut^[10] (423 + 1024 * t) = 302 + 729 * t ∧
      4 * (302 + 729 * t) < 3 * (423 + 1024 * t) := by
  have hb : Shortcut^[10] 423 = 302 := by decide
  have hc : PrefixOddCount 423 10 = 6 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 423 10 t
  · omega

/-- The 2203 cylinder has its exact affine descendant. -/
theorem FurtherDirect2203 (t : ℕ) :
    Shortcut^[12] (2203 + 4096 * t) = 1177 + 2187 * t ∧
      4 * (1177 + 2187 * t) < 3 * (2203 + 4096 * t) := by
  have hb : Shortcut^[12] 2203 = 1177 := by decide
  have hc : PrefixOddCount 2203 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 2203 12 t
  · omega

/-- The 3675 cylinder has its exact affine descendant. -/
theorem FurtherDirect3675 (t : ℕ) :
    Shortcut^[12] (3675 + 4096 * t) = 1963 + 2187 * t ∧
      4 * (1963 + 2187 * t) < 3 * (3675 + 4096 * t) := by
  have hb : Shortcut^[12] 3675 = 1963 := by decide
  have hc : PrefixOddCount 3675 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 3675 12 t
  · omega

/-- The 2907 cylinder has its exact affine descendant. -/
theorem FurtherDirect2907 (t : ℕ) :
    Shortcut^[12] (2907 + 4096 * t) = 1553 + 2187 * t ∧
      4 * (1553 + 2187 * t) < 3 * (2907 + 4096 * t) := by
  have hb : Shortcut^[12] 2907 = 1553 := by decide
  have hc : PrefixOddCount 2907 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 2907 12 t
  · omega

/-- The 1787 cylinder has its exact affine descendant. -/
theorem FurtherDirect1787 (t : ℕ) :
    Shortcut^[12] (1787 + 4096 * t) = 955 + 2187 * t ∧
      4 * (955 + 2187 * t) < 3 * (1787 + 4096 * t) := by
  have hb : Shortcut^[12] 1787 = 955 := by decide
  have hc : PrefixOddCount 1787 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 1787 12 t
  · omega

/-- The 1019 cylinder has its exact affine descendant. -/
theorem FurtherDirect1019 (t : ℕ) :
    Shortcut^[12] (1019 + 4096 * t) = 545 + 2187 * t ∧
      4 * (545 + 2187 * t) < 3 * (1019 + 4096 * t) := by
  have hb : Shortcut^[12] 1019 = 545 := by decide
  have hc : PrefixOddCount 1019 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 1019 12 t
  · omega

/-- The 3143 cylinder has its exact affine descendant. -/
theorem FurtherDirect3143 (t : ℕ) :
    Shortcut^[12] (3143 + 4096 * t) = 1679 + 2187 * t ∧
      4 * (1679 + 2187 * t) < 3 * (3143 + 4096 * t) := by
  have hb : Shortcut^[12] 3143 = 1679 := by decide
  have hc : PrefixOddCount 3143 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 3143 12 t
  · omega

/-- The 3911 cylinder has its exact affine descendant. -/
theorem FurtherDirect3911 (t : ℕ) :
    Shortcut^[12] (3911 + 4096 * t) = 2089 + 2187 * t ∧
      4 * (2089 + 2187 * t) < 3 * (3911 + 4096 * t) := by
  have hb : Shortcut^[12] 3911 = 2089 := by decide
  have hc : PrefixOddCount 3911 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 3911 12 t
  · omega

/-- The 1703 cylinder has its exact affine descendant. -/
theorem FurtherDirect1703 (t : ℕ) :
    Shortcut^[12] (1703 + 4096 * t) = 910 + 2187 * t ∧
      4 * (910 + 2187 * t) < 3 * (1703 + 4096 * t) := by
  have hb : Shortcut^[12] 1703 = 910 := by decide
  have hc : PrefixOddCount 1703 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 1703 12 t
  · omega

/-- The 935 cylinder has its exact affine descendant. -/
theorem FurtherDirect935 (t : ℕ) :
    Shortcut^[12] (935 + 4096 * t) = 500 + 2187 * t ∧
      4 * (500 + 2187 * t) < 3 * (935 + 4096 * t) := by
  have hb : Shortcut^[12] 935 = 500 := by decide
  have hc : PrefixOddCount 935 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 935 12 t
  · omega

/-- The 231 cylinder has its exact affine descendant. -/
theorem FurtherDirect231 (t : ℕ) :
    Shortcut^[12] (231 + 4096 * t) = 124 + 2187 * t ∧
      4 * (124 + 2187 * t) < 3 * (231 + 4096 * t) := by
  have hb : Shortcut^[12] 231 = 124 := by decide
  have hc : PrefixOddCount 231 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 231 12 t
  · omega

/-- The 3119 cylinder has its exact affine descendant. -/
theorem FurtherDirect3119 (t : ℕ) :
    Shortcut^[12] (3119 + 4096 * t) = 1666 + 2187 * t ∧
      4 * (1666 + 2187 * t) < 3 * (3119 + 4096 * t) := by
  have hb : Shortcut^[12] 3119 = 1666 := by decide
  have hc : PrefixOddCount 3119 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 3119 12 t
  · omega

/-- The 2351 cylinder has its exact affine descendant. -/
theorem FurtherDirect2351 (t : ℕ) :
    Shortcut^[12] (2351 + 4096 * t) = 1256 + 2187 * t ∧
      4 * (1256 + 2187 * t) < 3 * (2351 + 4096 * t) := by
  have hb : Shortcut^[12] 2351 = 1256 := by decide
  have hc : PrefixOddCount 2351 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 2351 12 t
  · omega

/-- The 1647 cylinder has its exact affine descendant. -/
theorem FurtherDirect1647 (t : ℕ) :
    Shortcut^[12] (1647 + 4096 * t) = 880 + 2187 * t ∧
      4 * (880 + 2187 * t) < 3 * (1647 + 4096 * t) := by
  have hb : Shortcut^[12] 1647 = 880 := by decide
  have hc : PrefixOddCount 1647 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 1647 12 t
  · omega

/-- The 879 cylinder has its exact affine descendant. -/
theorem FurtherDirect879 (t : ℕ) :
    Shortcut^[12] (879 + 4096 * t) = 470 + 2187 * t ∧
      4 * (470 + 2187 * t) < 3 * (879 + 4096 * t) := by
  have hb : Shortcut^[12] 879 = 470 := by decide
  have hc : PrefixOddCount 879 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 879 12 t
  · omega

/-- The 2031 cylinder has its exact affine descendant. -/
theorem FurtherDirect2031 (t : ℕ) :
    Shortcut^[12] (2031 + 4096 * t) = 1085 + 2187 * t ∧
      4 * (1085 + 2187 * t) < 3 * (2031 + 4096 * t) := by
  have hb : Shortcut^[12] 2031 = 1085 := by decide
  have hc : PrefixOddCount 2031 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 2031 12 t
  · omega

/-- The 2591 cylinder has its exact affine descendant. -/
theorem FurtherDirect2591 (t : ℕ) :
    Shortcut^[12] (2591 + 4096 * t) = 1384 + 2187 * t ∧
      4 * (1384 + 2187 * t) < 3 * (2591 + 4096 * t) := by
  have hb : Shortcut^[12] 2591 = 1384 := by decide
  have hc : PrefixOddCount 2591 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 2591 12 t
  · omega

/-- The 1823 cylinder has its exact affine descendant. -/
theorem FurtherDirect1823 (t : ℕ) :
    Shortcut^[12] (1823 + 4096 * t) = 974 + 2187 * t ∧
      4 * (974 + 2187 * t) < 3 * (1823 + 4096 * t) := by
  have hb : Shortcut^[12] 1823 = 974 := by decide
  have hc : PrefixOddCount 1823 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 1823 12 t
  · omega

/-- The 2975 cylinder has its exact affine descendant. -/
theorem FurtherDirect2975 (t : ℕ) :
    Shortcut^[12] (2975 + 4096 * t) = 1589 + 2187 * t ∧
      4 * (1589 + 2187 * t) < 3 * (2975 + 4096 * t) := by
  have hb : Shortcut^[12] 2975 = 1589 := by decide
  have hc : PrefixOddCount 2975 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 2975 12 t
  · omega

/-- The 2239 cylinder has its exact affine descendant. -/
theorem FurtherDirect2239 (t : ℕ) :
    Shortcut^[12] (2239 + 4096 * t) = 1196 + 2187 * t ∧
      4 * (1196 + 2187 * t) < 3 * (2239 + 4096 * t) := by
  have hb : Shortcut^[12] 2239 = 1196 := by decide
  have hc : PrefixOddCount 2239 12 = 7 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 2239 12 t
  · omega

/-- The depth-thirteen 2075 cylinder contracts by at least one sixth. -/
theorem DeepDirect2075 (t : ℕ) :
    Shortcut^[13] (2075 + 8192 * t) = 1663 + 6561 * t ∧
      6 * (1663 + 6561 * t) ≤ 5 * (2075 + 8192 * t) := by
  have hb : Shortcut^[13] 2075 = 1663 := by decide
  have hc : PrefixOddCount 2075 13 = 8 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 2075 13 t
  · omega

-- Kernel evaluation of the fifty-nine-step base trajectory needs deeper recursion.
set_option maxRecDepth 4096 in
/-- The first residual trajectory gives a uniform depth-fifty-nine cylinder. -/
theorem DeepDirect27 (t : ℕ) :
    Shortcut^[59] (27 + 2 ^ 59 * t) = 23 + 3 ^ 37 * t ∧
      7 * (23 + 3 ^ 37 * t) ≤ 6 * (27 + 2 ^ 59 * t) := by
  have hb : Shortcut^[59] 27 = 23 := by decide
  have hc : PrefixOddCount 27 59 = 37 := by decide
  constructor
  · simpa [hb, hc] using DyadicLift 27 59 t
  · norm_num
    omega

/-- The 111 cylinder joins a smaller parent with the global contraction factor. -/
theorem FurtherJoin111 (t : ℕ) :
    Shortcut (111 + 2 ^ 15 * 3 ^ 7 * t) =
      Shortcut^[12] (103 + 2 ^ 26 * t) ∧
    103 + 2 ^ 26 * t < 111 + 2 ^ 15 * 3 ^ 7 * t ∧
      123 * (103 + 2 ^ 26 * t) ≤
        118 * (111 + 2 ^ 15 * 3 ^ 7 * t) := by
  have hs :
      Shortcut (111 + 2 ^ 15 * 3 ^ 7 * t) =
        167 + 2 ^ 14 * 3 ^ 8 * t := by
    rw [show 111 + 2 ^ 15 * 3 ^ 7 * t =
      2 * (55 + 2 ^ 14 * 3 ^ 7 * t) + 1 by ring, OddStep]
    ring
  have hb : Shortcut^[12] 103 = 167 := by decide
  have hc : PrefixOddCount 103 12 = 8 := by decide
  have hp :
      Shortcut^[12] (103 + 2 ^ 26 * t) =
        167 + 2 ^ 14 * 3 ^ 8 * t := by
    calc
      Shortcut^[12] (103 + 2 ^ 26 * t) =
          Shortcut^[12] (103 + 2 ^ 12 * (2 ^ 14 * t)) := by
        congr 2
        ring
      _ = Shortcut^[12] 103 + 3 ^ (PrefixOddCount 103 12) * (2 ^ 14 * t) :=
        DyadicLift 103 12 (2 ^ 14 * t)
      _ = 167 + 2 ^ 14 * 3 ^ 8 * t := by rw [hb, hc]; norm_num; ring
  exact ⟨hs.trans hp.symm, by omega, by norm_num; omega⟩

end GeneralizedCollatz.ClassicalCoalescence
