-- SPDX-License-Identifier: CC-BY-4.0

import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Iterate

/-!
Raw Collatz successor chains on the cylinder `11003 + 1048576 * t`.
The smaller cylinder `9915 + 944784 * t` meets it at
`33466 + 3188646 * t`, and the next raw value is
`16733 + 1594323 * t`.

The argument does not claim that either orbit reaches `1`, that every
positive integer reaches `1`, or that any general capture statement holds.
-/

namespace GeneralizedCollatz

/-- Classical raw Collatz step: divide evens by `2`, and send odds by `3n+1`. -/
def LocalJoinStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- An even constant and an even slope force division by `2`. -/
theorem LocalJoinEvenStep (a b t : ℕ) (ha : 2 ∣ a) (hb : 2 ∣ b) :
    (a + b * t) % 2 = 0 ∧
      LocalJoinStep (a + b * t) = a / 2 + (b / 2) * t := by
  obtain ⟨ka, hka⟩ := ha
  obtain ⟨kb, hkb⟩ := hb
  -- Factor `2` out of both coefficients.
  have hmul : a + b * t = 2 * (ka + kb * t) := by
    rw [hka, hkb]
    calc
      2 * ka + (2 * kb) * t
          = 2 * ka + 2 * (kb * t) := by rw [Nat.mul_assoc]
      _ = 2 * (ka + kb * t) := by rw [← Nat.mul_add]
  have hmod : (a + b * t) % 2 = 0 := by
    rw [hmul]
    exact Nat.mul_mod_right 2 (ka + kb * t)
  -- The raw step on an even value is division by `2`.
  have hstep : LocalJoinStep (a + b * t) = (a + b * t) / 2 := by
    unfold LocalJoinStep
    rw [if_pos hmod]
  have hdiv : (a + b * t) / 2 = ka + kb * t := by
    rw [hmul]
    exact Nat.mul_div_cancel_left (ka + kb * t) (by decide : 0 < 2)
  have hkaDiv : a / 2 = ka := by
    rw [hka]
    exact Nat.mul_div_cancel_left ka (by decide : 0 < 2)
  have hkbDiv : b / 2 = kb := by
    rw [hkb]
    exact Nat.mul_div_cancel_left kb (by decide : 0 < 2)
  refine ⟨hmod, ?_⟩
  rw [hstep, hdiv, ← hkaDiv, ← hkbDiv]

/-- An odd constant and an even slope force the affine step `3n+1`. -/
theorem LocalJoinOddStep (a b t : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 0) :
    (a + b * t) % 2 = 1 ∧
      LocalJoinStep (a + b * t) = (3 * a + 1) + (3 * b) * t := by
  -- The even slope does not change the odd constant's parity.
  have hmod : (a + b * t) % 2 = 1 := by
    calc
      (a + b * t) % 2
          = ((a % 2) + ((b * t) % 2)) % 2 := by rw [Nat.add_mod]
      _ = ((a % 2) + ((b % 2) * (t % 2) % 2)) % 2 := by
          rw [Nat.mul_mod]
      _ = (1 + (0 * (t % 2) % 2)) % 2 := by rw [ha, hb]
      _ = (1 + (0 % 2)) % 2 := by rw [Nat.zero_mul]
      _ = (1 + 0) % 2 := by rw [Nat.zero_mod]
      _ = 1 := by decide
  have hne : (a + b * t) % 2 ≠ 0 := by
    intro hzero
    rw [hmod] at hzero
    exact Nat.one_ne_zero hzero
  have hstep :
      LocalJoinStep (a + b * t) = 3 * (a + b * t) + 1 := by
    unfold LocalJoinStep
    rw [if_neg hne]
  -- Expand `3(a + bt) + 1` and collect the constant term.
  have hlin :
      3 * (a + b * t) + 1 = (3 * a + 1) + (3 * b) * t := by
    calc
      3 * (a + b * t) + 1
          = 3 * a + 3 * (b * t) + 1 := by rw [Nat.mul_add]
      _ = 3 * a + (3 * b) * t + 1 := by rw [← Nat.mul_assoc]
      _ = 3 * a + ((3 * b) * t + 1) := by rw [Nat.add_assoc]
      _ = 3 * a + (1 + (3 * b) * t) := by
          rw [Nat.add_comm ((3 * b) * t) 1]
      _ = 3 * a + 1 + (3 * b) * t := by rw [← Nat.add_assoc]
  refine ⟨hmod, ?_⟩
  rw [hstep, hlin]

/-- Evaluate one odd step after checking the concrete coefficients. -/
theorem LocalJoinOddAt (a b u v t : ℕ)
    (ha : a % 2 = 1) (hb : b % 2 = 0)
    (hu : 3 * a + 1 = u) (hv : 3 * b = v) :
    LocalJoinStep (a + b * t) = u + v * t := by
  have hstep := And.right (LocalJoinOddStep a b t ha hb)
  rw [hstep, hu, hv]

/-- Evaluate one division by `2` after checking the concrete coefficients. -/
theorem LocalJoinEvenAt (a b u v t : ℕ)
    (ha : 2 ∣ a) (hb : 2 ∣ b)
    (hu : a / 2 = u) (hv : b / 2 = v) :
    LocalJoinStep (a + b * t) = u + v * t := by
  have hstep := And.right (LocalJoinEvenStep a b t ha hb)
  rw [hstep, hu, hv]

/-- Sum of two affine forms, with no cross term. -/
theorem LocalJoinAddForms (a b c d t : ℕ) :
    a + b * t + (c + d * t) = a + c + (b + d) * t := by
  calc
    a + b * t + (c + d * t)
        = a + b * t + c + d * t := by rw [← Nat.add_assoc]
    _ = a + (b * t + c) + d * t := by rw [Nat.add_assoc a (b * t) c]
    _ = a + (c + b * t) + d * t := by rw [Nat.add_comm (b * t) c]
    _ = a + c + b * t + d * t := by rw [← Nat.add_assoc]
    _ = a + c + (b * t + d * t) := by rw [Nat.add_assoc]
    _ = a + c + (b + d) * t := by rw [← Nat.add_mul]

/-- A larger constant and a slope at least as large give a strict inequality. -/
theorem LocalJoinDominates (a b c d t : ℕ)
    (hconst : c < a) (hslope : d ≤ b) :
    c + d * t < a + b * t := by
  have hs : d * t ≤ b * t := Nat.mul_le_mul_right t hslope
  have hleft : c + d * t ≤ c + b * t := Nat.add_le_add_left hs c
  have hright : c + b * t < a + b * t :=
    Nat.add_lt_add_right hconst (b * t)
  exact Nat.lt_of_le_of_lt hleft hright

/-- Raw successor chain from `11003 + 1048576 * t` through the join. -/
theorem LocalJoinSourceChain (t : ℕ) :
    LocalJoinStep (11003 + 1048576 * t) = 33010 + 3145728 * t ∧
    LocalJoinStep (33010 + 3145728 * t) = 16505 + 1572864 * t ∧
    LocalJoinStep (16505 + 1572864 * t) = 49516 + 4718592 * t ∧
    LocalJoinStep (49516 + 4718592 * t) = 24758 + 2359296 * t ∧
    LocalJoinStep (24758 + 2359296 * t) = 12379 + 1179648 * t ∧
    LocalJoinStep (12379 + 1179648 * t) = 37138 + 3538944 * t ∧
    LocalJoinStep (37138 + 3538944 * t) = 18569 + 1769472 * t ∧
    LocalJoinStep (18569 + 1769472 * t) = 55708 + 5308416 * t ∧
    LocalJoinStep (55708 + 5308416 * t) = 27854 + 2654208 * t ∧
    LocalJoinStep (27854 + 2654208 * t) = 13927 + 1327104 * t ∧
    LocalJoinStep (13927 + 1327104 * t) = 41782 + 3981312 * t ∧
    LocalJoinStep (41782 + 3981312 * t) = 20891 + 1990656 * t ∧
    LocalJoinStep (20891 + 1990656 * t) = 62674 + 5971968 * t ∧
    LocalJoinStep (62674 + 5971968 * t) = 31337 + 2985984 * t ∧
    LocalJoinStep (31337 + 2985984 * t) = 94012 + 8957952 * t ∧
    LocalJoinStep (94012 + 8957952 * t) = 47006 + 4478976 * t ∧
    LocalJoinStep (47006 + 4478976 * t) = 23503 + 2239488 * t ∧
    LocalJoinStep (23503 + 2239488 * t) = 70510 + 6718464 * t ∧
    LocalJoinStep (70510 + 6718464 * t) = 35255 + 3359232 * t ∧
    LocalJoinStep (35255 + 3359232 * t) = 105766 + 10077696 * t ∧
    LocalJoinStep (105766 + 10077696 * t) = 52883 + 5038848 * t ∧
    LocalJoinStep (52883 + 5038848 * t) = 158650 + 15116544 * t ∧
    LocalJoinStep (158650 + 15116544 * t) = 79325 + 7558272 * t ∧
    LocalJoinStep (79325 + 7558272 * t) = 237976 + 22674816 * t ∧
    LocalJoinStep (237976 + 22674816 * t) = 118988 + 11337408 * t ∧
    LocalJoinStep (118988 + 11337408 * t) = 59494 + 5668704 * t ∧
    LocalJoinStep (59494 + 5668704 * t) = 29747 + 2834352 * t ∧
    LocalJoinStep (29747 + 2834352 * t) = 89242 + 8503056 * t ∧
    LocalJoinStep (89242 + 8503056 * t) = 44621 + 4251528 * t ∧
    LocalJoinStep (44621 + 4251528 * t) = 133864 + 12754584 * t ∧
    LocalJoinStep (133864 + 12754584 * t) = 66932 + 6377292 * t ∧
    LocalJoinStep (66932 + 6377292 * t) = 33466 + 3188646 * t ∧
    LocalJoinStep (33466 + 3188646 * t) = 16733 + 1594323 * t := by
  -- Each even step is division by 2; each odd step is `3n+1`.
  have h0 :
      LocalJoinStep (11003 + 1048576 * t) = 33010 + 3145728 * t :=
    LocalJoinOddAt 11003 1048576 33010 3145728 t
      (by decide) (by decide) (by decide) (by decide)
  have h1 :
      LocalJoinStep (33010 + 3145728 * t) = 16505 + 1572864 * t :=
    LocalJoinEvenAt 33010 3145728 16505 1572864 t
      (by decide) (by decide) (by decide) (by decide)
  have h2 :
      LocalJoinStep (16505 + 1572864 * t) = 49516 + 4718592 * t :=
    LocalJoinOddAt 16505 1572864 49516 4718592 t
      (by decide) (by decide) (by decide) (by decide)
  have h3 :
      LocalJoinStep (49516 + 4718592 * t) = 24758 + 2359296 * t :=
    LocalJoinEvenAt 49516 4718592 24758 2359296 t
      (by decide) (by decide) (by decide) (by decide)
  have h4 :
      LocalJoinStep (24758 + 2359296 * t) = 12379 + 1179648 * t :=
    LocalJoinEvenAt 24758 2359296 12379 1179648 t
      (by decide) (by decide) (by decide) (by decide)
  have h5 :
      LocalJoinStep (12379 + 1179648 * t) = 37138 + 3538944 * t :=
    LocalJoinOddAt 12379 1179648 37138 3538944 t
      (by decide) (by decide) (by decide) (by decide)
  have h6 :
      LocalJoinStep (37138 + 3538944 * t) = 18569 + 1769472 * t :=
    LocalJoinEvenAt 37138 3538944 18569 1769472 t
      (by decide) (by decide) (by decide) (by decide)
  have h7 :
      LocalJoinStep (18569 + 1769472 * t) = 55708 + 5308416 * t :=
    LocalJoinOddAt 18569 1769472 55708 5308416 t
      (by decide) (by decide) (by decide) (by decide)
  have h8 :
      LocalJoinStep (55708 + 5308416 * t) = 27854 + 2654208 * t :=
    LocalJoinEvenAt 55708 5308416 27854 2654208 t
      (by decide) (by decide) (by decide) (by decide)
  have h9 :
      LocalJoinStep (27854 + 2654208 * t) = 13927 + 1327104 * t :=
    LocalJoinEvenAt 27854 2654208 13927 1327104 t
      (by decide) (by decide) (by decide) (by decide)
  have h10 :
      LocalJoinStep (13927 + 1327104 * t) = 41782 + 3981312 * t :=
    LocalJoinOddAt 13927 1327104 41782 3981312 t
      (by decide) (by decide) (by decide) (by decide)
  have h11 :
      LocalJoinStep (41782 + 3981312 * t) = 20891 + 1990656 * t :=
    LocalJoinEvenAt 41782 3981312 20891 1990656 t
      (by decide) (by decide) (by decide) (by decide)
  have h12 :
      LocalJoinStep (20891 + 1990656 * t) = 62674 + 5971968 * t :=
    LocalJoinOddAt 20891 1990656 62674 5971968 t
      (by decide) (by decide) (by decide) (by decide)
  have h13 :
      LocalJoinStep (62674 + 5971968 * t) = 31337 + 2985984 * t :=
    LocalJoinEvenAt 62674 5971968 31337 2985984 t
      (by decide) (by decide) (by decide) (by decide)
  have h14 :
      LocalJoinStep (31337 + 2985984 * t) = 94012 + 8957952 * t :=
    LocalJoinOddAt 31337 2985984 94012 8957952 t
      (by decide) (by decide) (by decide) (by decide)
  have h15 :
      LocalJoinStep (94012 + 8957952 * t) = 47006 + 4478976 * t :=
    LocalJoinEvenAt 94012 8957952 47006 4478976 t
      (by decide) (by decide) (by decide) (by decide)
  have h16 :
      LocalJoinStep (47006 + 4478976 * t) = 23503 + 2239488 * t :=
    LocalJoinEvenAt 47006 4478976 23503 2239488 t
      (by decide) (by decide) (by decide) (by decide)
  have h17 :
      LocalJoinStep (23503 + 2239488 * t) = 70510 + 6718464 * t :=
    LocalJoinOddAt 23503 2239488 70510 6718464 t
      (by decide) (by decide) (by decide) (by decide)
  have h18 :
      LocalJoinStep (70510 + 6718464 * t) = 35255 + 3359232 * t :=
    LocalJoinEvenAt 70510 6718464 35255 3359232 t
      (by decide) (by decide) (by decide) (by decide)
  have h19 :
      LocalJoinStep (35255 + 3359232 * t) = 105766 + 10077696 * t :=
    LocalJoinOddAt 35255 3359232 105766 10077696 t
      (by decide) (by decide) (by decide) (by decide)
  have h20 :
      LocalJoinStep (105766 + 10077696 * t) = 52883 + 5038848 * t :=
    LocalJoinEvenAt 105766 10077696 52883 5038848 t
      (by decide) (by decide) (by decide) (by decide)
  have h21 :
      LocalJoinStep (52883 + 5038848 * t) = 158650 + 15116544 * t :=
    LocalJoinOddAt 52883 5038848 158650 15116544 t
      (by decide) (by decide) (by decide) (by decide)
  have h22 :
      LocalJoinStep (158650 + 15116544 * t) = 79325 + 7558272 * t :=
    LocalJoinEvenAt 158650 15116544 79325 7558272 t
      (by decide) (by decide) (by decide) (by decide)
  have h23 :
      LocalJoinStep (79325 + 7558272 * t) = 237976 + 22674816 * t :=
    LocalJoinOddAt 79325 7558272 237976 22674816 t
      (by decide) (by decide) (by decide) (by decide)
  have h24 :
      LocalJoinStep (237976 + 22674816 * t) = 118988 + 11337408 * t :=
    LocalJoinEvenAt 237976 22674816 118988 11337408 t
      (by decide) (by decide) (by decide) (by decide)
  have h25 :
      LocalJoinStep (118988 + 11337408 * t) = 59494 + 5668704 * t :=
    LocalJoinEvenAt 118988 11337408 59494 5668704 t
      (by decide) (by decide) (by decide) (by decide)
  have h26 :
      LocalJoinStep (59494 + 5668704 * t) = 29747 + 2834352 * t :=
    LocalJoinEvenAt 59494 5668704 29747 2834352 t
      (by decide) (by decide) (by decide) (by decide)
  have h27 :
      LocalJoinStep (29747 + 2834352 * t) = 89242 + 8503056 * t :=
    LocalJoinOddAt 29747 2834352 89242 8503056 t
      (by decide) (by decide) (by decide) (by decide)
  have h28 :
      LocalJoinStep (89242 + 8503056 * t) = 44621 + 4251528 * t :=
    LocalJoinEvenAt 89242 8503056 44621 4251528 t
      (by decide) (by decide) (by decide) (by decide)
  have h29 :
      LocalJoinStep (44621 + 4251528 * t) = 133864 + 12754584 * t :=
    LocalJoinOddAt 44621 4251528 133864 12754584 t
      (by decide) (by decide) (by decide) (by decide)
  have h30 :
      LocalJoinStep (133864 + 12754584 * t) = 66932 + 6377292 * t :=
    LocalJoinEvenAt 133864 12754584 66932 6377292 t
      (by decide) (by decide) (by decide) (by decide)
  have h31 :
      LocalJoinStep (66932 + 6377292 * t) = 33466 + 3188646 * t :=
    LocalJoinEvenAt 66932 6377292 33466 3188646 t
      (by decide) (by decide) (by decide) (by decide)
  have h32 :
      LocalJoinStep (33466 + 3188646 * t) = 16733 + 1594323 * t :=
    LocalJoinEvenAt 33466 3188646 16733 1594323 t
      (by decide) (by decide) (by decide) (by decide)
  exact ⟨h0,
   h1,
   h2,
   h3,
   h4,
   h5,
   h6,
   h7,
   h8,
   h9,
   h10,
   h11,
   h12,
   h13,
   h14,
   h15,
   h16,
   h17,
   h18,
   h19,
   h20,
   h21,
   h22,
   h23,
   h24,
   h25,
   h26,
   h27,
   h28,
   h29,
   h30,
   h31,
   h32⟩

/-- Raw successor chain from `9915 + 944784 * t` through the same join. -/
theorem LocalJoinParentChain (t : ℕ) :
    LocalJoinStep (9915 + 944784 * t) = 29746 + 2834352 * t ∧
    LocalJoinStep (29746 + 2834352 * t) = 14873 + 1417176 * t ∧
    LocalJoinStep (14873 + 1417176 * t) = 44620 + 4251528 * t ∧
    LocalJoinStep (44620 + 4251528 * t) = 22310 + 2125764 * t ∧
    LocalJoinStep (22310 + 2125764 * t) = 11155 + 1062882 * t ∧
    LocalJoinStep (11155 + 1062882 * t) = 33466 + 3188646 * t ∧
    LocalJoinStep (33466 + 3188646 * t) = 16733 + 1594323 * t := by
  -- Each even step is division by 2; each odd step is `3n+1`.
  have h0 :
      LocalJoinStep (9915 + 944784 * t) = 29746 + 2834352 * t :=
    LocalJoinOddAt 9915 944784 29746 2834352 t
      (by decide) (by decide) (by decide) (by decide)
  have h1 :
      LocalJoinStep (29746 + 2834352 * t) = 14873 + 1417176 * t :=
    LocalJoinEvenAt 29746 2834352 14873 1417176 t
      (by decide) (by decide) (by decide) (by decide)
  have h2 :
      LocalJoinStep (14873 + 1417176 * t) = 44620 + 4251528 * t :=
    LocalJoinOddAt 14873 1417176 44620 4251528 t
      (by decide) (by decide) (by decide) (by decide)
  have h3 :
      LocalJoinStep (44620 + 4251528 * t) = 22310 + 2125764 * t :=
    LocalJoinEvenAt 44620 4251528 22310 2125764 t
      (by decide) (by decide) (by decide) (by decide)
  have h4 :
      LocalJoinStep (22310 + 2125764 * t) = 11155 + 1062882 * t :=
    LocalJoinEvenAt 22310 2125764 11155 1062882 t
      (by decide) (by decide) (by decide) (by decide)
  have h5 :
      LocalJoinStep (11155 + 1062882 * t) = 33466 + 3188646 * t :=
    LocalJoinOddAt 11155 1062882 33466 3188646 t
      (by decide) (by decide) (by decide) (by decide)
  have h6 :
      LocalJoinStep (33466 + 3188646 * t) = 16733 + 1594323 * t :=
    LocalJoinEvenAt 33466 3188646 16733 1594323 t
      (by decide) (by decide) (by decide) (by decide)
  exact ⟨h0,
   h1,
   h2,
   h3,
   h4,
   h5,
   h6⟩

/-- Exact gaps `p < n < j`, and the join's parity is the parity of `t + 1`. -/
theorem LocalJoinOrder (t : ℕ) :
    9915 + 944784 * t + (1088 + 103792 * t) =
      11003 + 1048576 * t ∧
    11003 + 1048576 * t + (5730 + 545747 * t) =
      16733 + 1594323 * t ∧
    9915 + 944784 * t < 11003 + 1048576 * t ∧
    11003 + 1048576 * t < 16733 + 1594323 * t ∧
    (16733 + 1594323 * t) % 2 = (1 + t) % 2 := by
  have hsum1 :
      9915 + 944784 * t + (1088 + 103792 * t) =
        (9915 + 1088) + (944784 + 103792) * t :=
    LocalJoinAddForms 9915 944784 1088 103792 t
  have hconst1 : 9915 + 1088 = 11003 := by decide
  have hslope1 : 944784 + 103792 = 1048576 := by decide
  rw [hconst1, hslope1] at hsum1
  have hpos1 : 0 < 1088 + 103792 * t :=
    Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 1088)
      (Nat.le_add_right 1088 (103792 * t))
  have hlt1 :
      9915 + 944784 * t <
        9915 + 944784 * t + (1088 + 103792 * t) :=
    Nat.lt_add_of_pos_right hpos1
  rw [hsum1] at hlt1
  have hsum2 :
      11003 + 1048576 * t + (5730 + 545747 * t) =
        (11003 + 5730) + (1048576 + 545747) * t :=
    LocalJoinAddForms 11003 1048576 5730 545747 t
  have hconst2 : 11003 + 5730 = 16733 := by decide
  have hslope2 : 1048576 + 545747 = 1594323 := by decide
  rw [hconst2, hslope2] at hsum2
  have hpos2 : 0 < 5730 + 545747 * t :=
    Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 5730)
      (Nat.le_add_right 5730 (545747 * t))
  have hlt2 :
      11003 + 1048576 * t <
        11003 + 1048576 * t + (5730 + 545747 * t) :=
    Nat.lt_add_of_pos_right hpos2
  rw [hsum2] at hlt2
  -- Both coefficients of the join are odd, so the parity is `1 + t`.
  have hpar : (16733 + 1594323 * t) % 2 = (1 + t) % 2 := by
    have h1 : 16733 % 2 = 1 := by decide
    have hone : (1 : ℕ) % 2 = 1 := by decide
    calc
      (16733 + 1594323 * t) % 2
          = ((16733 % 2) + ((1594323 * t) % 2)) % 2 := by
            rw [Nat.add_mod]
      _ = ((16733 % 2) + ((1594323 % 2) * (t % 2) % 2)) % 2 := by
          rw [Nat.mul_mod]
      _ = (1 + (1 * (t % 2) % 2)) % 2 := by simp only [h1]
      _ = (1 + ((t % 2) % 2)) % 2 := by rw [Nat.one_mul]
      _ = (1 + t % 2) % 2 := by rw [Nat.mod_mod]
      _ = ((1 % 2) + (t % 2)) % 2 := by rw [← hone]
      _ = (1 + t) % 2 := by rw [← Nat.add_mod]
  exact ⟨hsum1, hsum2, hlt1, hlt2, hpar⟩

-- The explicit cross-comparison conjunction has 268 components.
set_option maxRecDepth 4096 in
/-- The two chains meet only at the shared tail `33466 + 3188646 * t` and `16733 + 1594323 * t`. -/
theorem LocalJoinDistinctPrefixes (t : ℕ) :
    9915 + 944784 * t < 11003 + 1048576 * t ∧
    11003 + 1048576 * t < 29746 + 2834352 * t ∧
    11003 + 1048576 * t < 14873 + 1417176 * t ∧
    11003 + 1048576 * t < 44620 + 4251528 * t ∧
    11003 + 1048576 * t < 22310 + 2125764 * t ∧
    11003 + 1048576 * t < 11155 + 1062882 * t ∧
    11003 + 1048576 * t < 33466 + 3188646 * t ∧
    11003 + 1048576 * t < 16733 + 1594323 * t ∧
    9915 + 944784 * t < 33010 + 3145728 * t ∧
    29746 + 2834352 * t < 33010 + 3145728 * t ∧
    14873 + 1417176 * t < 33010 + 3145728 * t ∧
    33010 + 3145728 * t < 44620 + 4251528 * t ∧
    22310 + 2125764 * t < 33010 + 3145728 * t ∧
    11155 + 1062882 * t < 33010 + 3145728 * t ∧
    33010 + 3145728 * t < 33466 + 3188646 * t ∧
    16733 + 1594323 * t < 33010 + 3145728 * t ∧
    9915 + 944784 * t < 16505 + 1572864 * t ∧
    16505 + 1572864 * t < 29746 + 2834352 * t ∧
    14873 + 1417176 * t < 16505 + 1572864 * t ∧
    16505 + 1572864 * t < 44620 + 4251528 * t ∧
    16505 + 1572864 * t < 22310 + 2125764 * t ∧
    11155 + 1062882 * t < 16505 + 1572864 * t ∧
    16505 + 1572864 * t < 33466 + 3188646 * t ∧
    16505 + 1572864 * t < 16733 + 1594323 * t ∧
    9915 + 944784 * t < 49516 + 4718592 * t ∧
    29746 + 2834352 * t < 49516 + 4718592 * t ∧
    14873 + 1417176 * t < 49516 + 4718592 * t ∧
    44620 + 4251528 * t < 49516 + 4718592 * t ∧
    22310 + 2125764 * t < 49516 + 4718592 * t ∧
    11155 + 1062882 * t < 49516 + 4718592 * t ∧
    33466 + 3188646 * t < 49516 + 4718592 * t ∧
    16733 + 1594323 * t < 49516 + 4718592 * t ∧
    9915 + 944784 * t < 24758 + 2359296 * t ∧
    24758 + 2359296 * t < 29746 + 2834352 * t ∧
    14873 + 1417176 * t < 24758 + 2359296 * t ∧
    24758 + 2359296 * t < 44620 + 4251528 * t ∧
    22310 + 2125764 * t < 24758 + 2359296 * t ∧
    11155 + 1062882 * t < 24758 + 2359296 * t ∧
    24758 + 2359296 * t < 33466 + 3188646 * t ∧
    16733 + 1594323 * t < 24758 + 2359296 * t ∧
    9915 + 944784 * t < 12379 + 1179648 * t ∧
    12379 + 1179648 * t < 29746 + 2834352 * t ∧
    12379 + 1179648 * t < 14873 + 1417176 * t ∧
    12379 + 1179648 * t < 44620 + 4251528 * t ∧
    12379 + 1179648 * t < 22310 + 2125764 * t ∧
    11155 + 1062882 * t < 12379 + 1179648 * t ∧
    12379 + 1179648 * t < 33466 + 3188646 * t ∧
    12379 + 1179648 * t < 16733 + 1594323 * t ∧
    9915 + 944784 * t < 37138 + 3538944 * t ∧
    29746 + 2834352 * t < 37138 + 3538944 * t ∧
    14873 + 1417176 * t < 37138 + 3538944 * t ∧
    37138 + 3538944 * t < 44620 + 4251528 * t ∧
    22310 + 2125764 * t < 37138 + 3538944 * t ∧
    11155 + 1062882 * t < 37138 + 3538944 * t ∧
    33466 + 3188646 * t < 37138 + 3538944 * t ∧
    16733 + 1594323 * t < 37138 + 3538944 * t ∧
    9915 + 944784 * t < 18569 + 1769472 * t ∧
    18569 + 1769472 * t < 29746 + 2834352 * t ∧
    14873 + 1417176 * t < 18569 + 1769472 * t ∧
    18569 + 1769472 * t < 44620 + 4251528 * t ∧
    18569 + 1769472 * t < 22310 + 2125764 * t ∧
    11155 + 1062882 * t < 18569 + 1769472 * t ∧
    18569 + 1769472 * t < 33466 + 3188646 * t ∧
    16733 + 1594323 * t < 18569 + 1769472 * t ∧
    9915 + 944784 * t < 55708 + 5308416 * t ∧
    29746 + 2834352 * t < 55708 + 5308416 * t ∧
    14873 + 1417176 * t < 55708 + 5308416 * t ∧
    44620 + 4251528 * t < 55708 + 5308416 * t ∧
    22310 + 2125764 * t < 55708 + 5308416 * t ∧
    11155 + 1062882 * t < 55708 + 5308416 * t ∧
    33466 + 3188646 * t < 55708 + 5308416 * t ∧
    16733 + 1594323 * t < 55708 + 5308416 * t ∧
    9915 + 944784 * t < 27854 + 2654208 * t ∧
    27854 + 2654208 * t < 29746 + 2834352 * t ∧
    14873 + 1417176 * t < 27854 + 2654208 * t ∧
    27854 + 2654208 * t < 44620 + 4251528 * t ∧
    22310 + 2125764 * t < 27854 + 2654208 * t ∧
    11155 + 1062882 * t < 27854 + 2654208 * t ∧
    27854 + 2654208 * t < 33466 + 3188646 * t ∧
    16733 + 1594323 * t < 27854 + 2654208 * t ∧
    9915 + 944784 * t < 13927 + 1327104 * t ∧
    13927 + 1327104 * t < 29746 + 2834352 * t ∧
    13927 + 1327104 * t < 14873 + 1417176 * t ∧
    13927 + 1327104 * t < 44620 + 4251528 * t ∧
    13927 + 1327104 * t < 22310 + 2125764 * t ∧
    11155 + 1062882 * t < 13927 + 1327104 * t ∧
    13927 + 1327104 * t < 33466 + 3188646 * t ∧
    13927 + 1327104 * t < 16733 + 1594323 * t ∧
    9915 + 944784 * t < 41782 + 3981312 * t ∧
    29746 + 2834352 * t < 41782 + 3981312 * t ∧
    14873 + 1417176 * t < 41782 + 3981312 * t ∧
    41782 + 3981312 * t < 44620 + 4251528 * t ∧
    22310 + 2125764 * t < 41782 + 3981312 * t ∧
    11155 + 1062882 * t < 41782 + 3981312 * t ∧
    33466 + 3188646 * t < 41782 + 3981312 * t ∧
    16733 + 1594323 * t < 41782 + 3981312 * t ∧
    9915 + 944784 * t < 20891 + 1990656 * t ∧
    20891 + 1990656 * t < 29746 + 2834352 * t ∧
    14873 + 1417176 * t < 20891 + 1990656 * t ∧
    20891 + 1990656 * t < 44620 + 4251528 * t ∧
    20891 + 1990656 * t < 22310 + 2125764 * t ∧
    11155 + 1062882 * t < 20891 + 1990656 * t ∧
    20891 + 1990656 * t < 33466 + 3188646 * t ∧
    16733 + 1594323 * t < 20891 + 1990656 * t ∧
    9915 + 944784 * t < 62674 + 5971968 * t ∧
    29746 + 2834352 * t < 62674 + 5971968 * t ∧
    14873 + 1417176 * t < 62674 + 5971968 * t ∧
    44620 + 4251528 * t < 62674 + 5971968 * t ∧
    22310 + 2125764 * t < 62674 + 5971968 * t ∧
    11155 + 1062882 * t < 62674 + 5971968 * t ∧
    33466 + 3188646 * t < 62674 + 5971968 * t ∧
    16733 + 1594323 * t < 62674 + 5971968 * t ∧
    9915 + 944784 * t < 31337 + 2985984 * t ∧
    29746 + 2834352 * t < 31337 + 2985984 * t ∧
    14873 + 1417176 * t < 31337 + 2985984 * t ∧
    31337 + 2985984 * t < 44620 + 4251528 * t ∧
    22310 + 2125764 * t < 31337 + 2985984 * t ∧
    11155 + 1062882 * t < 31337 + 2985984 * t ∧
    31337 + 2985984 * t < 33466 + 3188646 * t ∧
    16733 + 1594323 * t < 31337 + 2985984 * t ∧
    9915 + 944784 * t < 94012 + 8957952 * t ∧
    29746 + 2834352 * t < 94012 + 8957952 * t ∧
    14873 + 1417176 * t < 94012 + 8957952 * t ∧
    44620 + 4251528 * t < 94012 + 8957952 * t ∧
    22310 + 2125764 * t < 94012 + 8957952 * t ∧
    11155 + 1062882 * t < 94012 + 8957952 * t ∧
    33466 + 3188646 * t < 94012 + 8957952 * t ∧
    16733 + 1594323 * t < 94012 + 8957952 * t ∧
    9915 + 944784 * t < 47006 + 4478976 * t ∧
    29746 + 2834352 * t < 47006 + 4478976 * t ∧
    14873 + 1417176 * t < 47006 + 4478976 * t ∧
    44620 + 4251528 * t < 47006 + 4478976 * t ∧
    22310 + 2125764 * t < 47006 + 4478976 * t ∧
    11155 + 1062882 * t < 47006 + 4478976 * t ∧
    33466 + 3188646 * t < 47006 + 4478976 * t ∧
    16733 + 1594323 * t < 47006 + 4478976 * t ∧
    9915 + 944784 * t < 23503 + 2239488 * t ∧
    23503 + 2239488 * t < 29746 + 2834352 * t ∧
    14873 + 1417176 * t < 23503 + 2239488 * t ∧
    23503 + 2239488 * t < 44620 + 4251528 * t ∧
    22310 + 2125764 * t < 23503 + 2239488 * t ∧
    11155 + 1062882 * t < 23503 + 2239488 * t ∧
    23503 + 2239488 * t < 33466 + 3188646 * t ∧
    16733 + 1594323 * t < 23503 + 2239488 * t ∧
    9915 + 944784 * t < 70510 + 6718464 * t ∧
    29746 + 2834352 * t < 70510 + 6718464 * t ∧
    14873 + 1417176 * t < 70510 + 6718464 * t ∧
    44620 + 4251528 * t < 70510 + 6718464 * t ∧
    22310 + 2125764 * t < 70510 + 6718464 * t ∧
    11155 + 1062882 * t < 70510 + 6718464 * t ∧
    33466 + 3188646 * t < 70510 + 6718464 * t ∧
    16733 + 1594323 * t < 70510 + 6718464 * t ∧
    9915 + 944784 * t < 35255 + 3359232 * t ∧
    29746 + 2834352 * t < 35255 + 3359232 * t ∧
    14873 + 1417176 * t < 35255 + 3359232 * t ∧
    35255 + 3359232 * t < 44620 + 4251528 * t ∧
    22310 + 2125764 * t < 35255 + 3359232 * t ∧
    11155 + 1062882 * t < 35255 + 3359232 * t ∧
    33466 + 3188646 * t < 35255 + 3359232 * t ∧
    16733 + 1594323 * t < 35255 + 3359232 * t ∧
    9915 + 944784 * t < 105766 + 10077696 * t ∧
    29746 + 2834352 * t < 105766 + 10077696 * t ∧
    14873 + 1417176 * t < 105766 + 10077696 * t ∧
    44620 + 4251528 * t < 105766 + 10077696 * t ∧
    22310 + 2125764 * t < 105766 + 10077696 * t ∧
    11155 + 1062882 * t < 105766 + 10077696 * t ∧
    33466 + 3188646 * t < 105766 + 10077696 * t ∧
    16733 + 1594323 * t < 105766 + 10077696 * t ∧
    9915 + 944784 * t < 52883 + 5038848 * t ∧
    29746 + 2834352 * t < 52883 + 5038848 * t ∧
    14873 + 1417176 * t < 52883 + 5038848 * t ∧
    44620 + 4251528 * t < 52883 + 5038848 * t ∧
    22310 + 2125764 * t < 52883 + 5038848 * t ∧
    11155 + 1062882 * t < 52883 + 5038848 * t ∧
    33466 + 3188646 * t < 52883 + 5038848 * t ∧
    16733 + 1594323 * t < 52883 + 5038848 * t ∧
    9915 + 944784 * t < 158650 + 15116544 * t ∧
    29746 + 2834352 * t < 158650 + 15116544 * t ∧
    14873 + 1417176 * t < 158650 + 15116544 * t ∧
    44620 + 4251528 * t < 158650 + 15116544 * t ∧
    22310 + 2125764 * t < 158650 + 15116544 * t ∧
    11155 + 1062882 * t < 158650 + 15116544 * t ∧
    33466 + 3188646 * t < 158650 + 15116544 * t ∧
    16733 + 1594323 * t < 158650 + 15116544 * t ∧
    9915 + 944784 * t < 79325 + 7558272 * t ∧
    29746 + 2834352 * t < 79325 + 7558272 * t ∧
    14873 + 1417176 * t < 79325 + 7558272 * t ∧
    44620 + 4251528 * t < 79325 + 7558272 * t ∧
    22310 + 2125764 * t < 79325 + 7558272 * t ∧
    11155 + 1062882 * t < 79325 + 7558272 * t ∧
    33466 + 3188646 * t < 79325 + 7558272 * t ∧
    16733 + 1594323 * t < 79325 + 7558272 * t ∧
    9915 + 944784 * t < 237976 + 22674816 * t ∧
    29746 + 2834352 * t < 237976 + 22674816 * t ∧
    14873 + 1417176 * t < 237976 + 22674816 * t ∧
    44620 + 4251528 * t < 237976 + 22674816 * t ∧
    22310 + 2125764 * t < 237976 + 22674816 * t ∧
    11155 + 1062882 * t < 237976 + 22674816 * t ∧
    33466 + 3188646 * t < 237976 + 22674816 * t ∧
    16733 + 1594323 * t < 237976 + 22674816 * t ∧
    9915 + 944784 * t < 118988 + 11337408 * t ∧
    29746 + 2834352 * t < 118988 + 11337408 * t ∧
    14873 + 1417176 * t < 118988 + 11337408 * t ∧
    44620 + 4251528 * t < 118988 + 11337408 * t ∧
    22310 + 2125764 * t < 118988 + 11337408 * t ∧
    11155 + 1062882 * t < 118988 + 11337408 * t ∧
    33466 + 3188646 * t < 118988 + 11337408 * t ∧
    16733 + 1594323 * t < 118988 + 11337408 * t ∧
    9915 + 944784 * t < 59494 + 5668704 * t ∧
    29746 + 2834352 * t < 59494 + 5668704 * t ∧
    14873 + 1417176 * t < 59494 + 5668704 * t ∧
    44620 + 4251528 * t < 59494 + 5668704 * t ∧
    22310 + 2125764 * t < 59494 + 5668704 * t ∧
    11155 + 1062882 * t < 59494 + 5668704 * t ∧
    33466 + 3188646 * t < 59494 + 5668704 * t ∧
    16733 + 1594323 * t < 59494 + 5668704 * t ∧
    9915 + 944784 * t < 29747 + 2834352 * t ∧
    29746 + 2834352 * t < 29747 + 2834352 * t ∧
    14873 + 1417176 * t < 29747 + 2834352 * t ∧
    29747 + 2834352 * t < 44620 + 4251528 * t ∧
    22310 + 2125764 * t < 29747 + 2834352 * t ∧
    11155 + 1062882 * t < 29747 + 2834352 * t ∧
    29747 + 2834352 * t < 33466 + 3188646 * t ∧
    16733 + 1594323 * t < 29747 + 2834352 * t ∧
    9915 + 944784 * t < 89242 + 8503056 * t ∧
    29746 + 2834352 * t < 89242 + 8503056 * t ∧
    14873 + 1417176 * t < 89242 + 8503056 * t ∧
    44620 + 4251528 * t < 89242 + 8503056 * t ∧
    22310 + 2125764 * t < 89242 + 8503056 * t ∧
    11155 + 1062882 * t < 89242 + 8503056 * t ∧
    33466 + 3188646 * t < 89242 + 8503056 * t ∧
    16733 + 1594323 * t < 89242 + 8503056 * t ∧
    9915 + 944784 * t < 44621 + 4251528 * t ∧
    29746 + 2834352 * t < 44621 + 4251528 * t ∧
    14873 + 1417176 * t < 44621 + 4251528 * t ∧
    44620 + 4251528 * t < 44621 + 4251528 * t ∧
    22310 + 2125764 * t < 44621 + 4251528 * t ∧
    11155 + 1062882 * t < 44621 + 4251528 * t ∧
    33466 + 3188646 * t < 44621 + 4251528 * t ∧
    16733 + 1594323 * t < 44621 + 4251528 * t ∧
    9915 + 944784 * t < 133864 + 12754584 * t ∧
    29746 + 2834352 * t < 133864 + 12754584 * t ∧
    14873 + 1417176 * t < 133864 + 12754584 * t ∧
    44620 + 4251528 * t < 133864 + 12754584 * t ∧
    22310 + 2125764 * t < 133864 + 12754584 * t ∧
    11155 + 1062882 * t < 133864 + 12754584 * t ∧
    33466 + 3188646 * t < 133864 + 12754584 * t ∧
    16733 + 1594323 * t < 133864 + 12754584 * t ∧
    9915 + 944784 * t < 66932 + 6377292 * t ∧
    29746 + 2834352 * t < 66932 + 6377292 * t ∧
    14873 + 1417176 * t < 66932 + 6377292 * t ∧
    44620 + 4251528 * t < 66932 + 6377292 * t ∧
    22310 + 2125764 * t < 66932 + 6377292 * t ∧
    11155 + 1062882 * t < 66932 + 6377292 * t ∧
    33466 + 3188646 * t < 66932 + 6377292 * t ∧
    16733 + 1594323 * t < 66932 + 6377292 * t ∧
    9915 + 944784 * t < 33466 + 3188646 * t ∧
    9915 + 944784 * t < 16733 + 1594323 * t ∧
    29746 + 2834352 * t < 33466 + 3188646 * t ∧
    16733 + 1594323 * t < 29746 + 2834352 * t ∧
    14873 + 1417176 * t < 33466 + 3188646 * t ∧
    14873 + 1417176 * t < 16733 + 1594323 * t ∧
    33466 + 3188646 * t < 44620 + 4251528 * t ∧
    16733 + 1594323 * t < 44620 + 4251528 * t ∧
    22310 + 2125764 * t < 33466 + 3188646 * t ∧
    16733 + 1594323 * t < 22310 + 2125764 * t ∧
    11155 + 1062882 * t < 33466 + 3188646 * t ∧
    11155 + 1062882 * t < 16733 + 1594323 * t := by
  -- Each displayed comparison follows from its two coefficient inequalities.
  repeat' apply And.intro
  all_goals exact LocalJoinDominates _ _ _ _ t (by decide) (by decide)

/-- Every listed chain state misses `8251 + 786432 * t` and `24754 + 2359296 * t`. -/
theorem LocalJoinExcludesForms (t : ℕ) :
    8251 + 786432 * t < 11003 + 1048576 * t ∧
    11003 + 1048576 * t < 24754 + 2359296 * t ∧
    8251 + 786432 * t < 33010 + 3145728 * t ∧
    24754 + 2359296 * t < 33010 + 3145728 * t ∧
    8251 + 786432 * t < 16505 + 1572864 * t ∧
    16505 + 1572864 * t < 24754 + 2359296 * t ∧
    8251 + 786432 * t < 49516 + 4718592 * t ∧
    24754 + 2359296 * t < 49516 + 4718592 * t ∧
    8251 + 786432 * t < 24758 + 2359296 * t ∧
    24754 + 2359296 * t < 24758 + 2359296 * t ∧
    8251 + 786432 * t < 12379 + 1179648 * t ∧
    12379 + 1179648 * t < 24754 + 2359296 * t ∧
    8251 + 786432 * t < 37138 + 3538944 * t ∧
    24754 + 2359296 * t < 37138 + 3538944 * t ∧
    8251 + 786432 * t < 18569 + 1769472 * t ∧
    18569 + 1769472 * t < 24754 + 2359296 * t ∧
    8251 + 786432 * t < 55708 + 5308416 * t ∧
    24754 + 2359296 * t < 55708 + 5308416 * t ∧
    8251 + 786432 * t < 27854 + 2654208 * t ∧
    24754 + 2359296 * t < 27854 + 2654208 * t ∧
    8251 + 786432 * t < 13927 + 1327104 * t ∧
    13927 + 1327104 * t < 24754 + 2359296 * t ∧
    8251 + 786432 * t < 41782 + 3981312 * t ∧
    24754 + 2359296 * t < 41782 + 3981312 * t ∧
    8251 + 786432 * t < 20891 + 1990656 * t ∧
    20891 + 1990656 * t < 24754 + 2359296 * t ∧
    8251 + 786432 * t < 62674 + 5971968 * t ∧
    24754 + 2359296 * t < 62674 + 5971968 * t ∧
    8251 + 786432 * t < 31337 + 2985984 * t ∧
    24754 + 2359296 * t < 31337 + 2985984 * t ∧
    8251 + 786432 * t < 94012 + 8957952 * t ∧
    24754 + 2359296 * t < 94012 + 8957952 * t ∧
    8251 + 786432 * t < 47006 + 4478976 * t ∧
    24754 + 2359296 * t < 47006 + 4478976 * t ∧
    8251 + 786432 * t < 23503 + 2239488 * t ∧
    23503 + 2239488 * t < 24754 + 2359296 * t ∧
    8251 + 786432 * t < 70510 + 6718464 * t ∧
    24754 + 2359296 * t < 70510 + 6718464 * t ∧
    8251 + 786432 * t < 35255 + 3359232 * t ∧
    24754 + 2359296 * t < 35255 + 3359232 * t ∧
    8251 + 786432 * t < 105766 + 10077696 * t ∧
    24754 + 2359296 * t < 105766 + 10077696 * t ∧
    8251 + 786432 * t < 52883 + 5038848 * t ∧
    24754 + 2359296 * t < 52883 + 5038848 * t ∧
    8251 + 786432 * t < 158650 + 15116544 * t ∧
    24754 + 2359296 * t < 158650 + 15116544 * t ∧
    8251 + 786432 * t < 79325 + 7558272 * t ∧
    24754 + 2359296 * t < 79325 + 7558272 * t ∧
    8251 + 786432 * t < 237976 + 22674816 * t ∧
    24754 + 2359296 * t < 237976 + 22674816 * t ∧
    8251 + 786432 * t < 118988 + 11337408 * t ∧
    24754 + 2359296 * t < 118988 + 11337408 * t ∧
    8251 + 786432 * t < 59494 + 5668704 * t ∧
    24754 + 2359296 * t < 59494 + 5668704 * t ∧
    8251 + 786432 * t < 29747 + 2834352 * t ∧
    24754 + 2359296 * t < 29747 + 2834352 * t ∧
    8251 + 786432 * t < 89242 + 8503056 * t ∧
    24754 + 2359296 * t < 89242 + 8503056 * t ∧
    8251 + 786432 * t < 44621 + 4251528 * t ∧
    24754 + 2359296 * t < 44621 + 4251528 * t ∧
    8251 + 786432 * t < 133864 + 12754584 * t ∧
    24754 + 2359296 * t < 133864 + 12754584 * t ∧
    8251 + 786432 * t < 66932 + 6377292 * t ∧
    24754 + 2359296 * t < 66932 + 6377292 * t ∧
    8251 + 786432 * t < 33466 + 3188646 * t ∧
    24754 + 2359296 * t < 33466 + 3188646 * t ∧
    8251 + 786432 * t < 16733 + 1594323 * t ∧
    16733 + 1594323 * t < 24754 + 2359296 * t ∧
    8251 + 786432 * t < 9915 + 944784 * t ∧
    9915 + 944784 * t < 24754 + 2359296 * t ∧
    8251 + 786432 * t < 29746 + 2834352 * t ∧
    24754 + 2359296 * t < 29746 + 2834352 * t ∧
    8251 + 786432 * t < 14873 + 1417176 * t ∧
    14873 + 1417176 * t < 24754 + 2359296 * t ∧
    8251 + 786432 * t < 44620 + 4251528 * t ∧
    24754 + 2359296 * t < 44620 + 4251528 * t ∧
    8251 + 786432 * t < 22310 + 2125764 * t ∧
    22310 + 2125764 * t < 24754 + 2359296 * t ∧
    8251 + 786432 * t < 11155 + 1062882 * t ∧
    11155 + 1062882 * t < 24754 + 2359296 * t := by
  -- The same dominance test excludes both foreign forms at every listed state.
  repeat' apply And.intro
  all_goals exact LocalJoinDominates _ _ _ _ t (by decide) (by decide)

/-- The literal successor chains recover both shared raw iterate values. -/
theorem LocalJoinIterates (t : ℕ) :
    LocalJoinStep^[32] (11003 + 1048576 * t) = 33466 + 3188646 * t ∧
    LocalJoinStep^[6] (9915 + 944784 * t) = 33466 + 3188646 * t ∧
    LocalJoinStep^[33] (11003 + 1048576 * t) = 16733 + 1594323 * t ∧
    LocalJoinStep^[7] (9915 + 944784 * t) = 16733 + 1594323 * t := by
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15,
      s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31,
      s32⟩ := LocalJoinSourceChain t
  obtain ⟨p0, p1, p2, p3, p4, p5, _⟩ := LocalJoinParentChain t
  -- Unroll exactly the two certified prefixes, without continuing past the join.
  repeat' apply And.intro
  all_goals simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16,
    s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31,
    s32, p0, p1, p2, p3, p4, p5]

/-- A fixed contraction bound for this cylinder's positive smaller parent. -/
theorem LocalJoinParentBound (t : ℕ) :
    0 < 9915 + 944784 * t ∧
    100 * (9915 + 944784 * t) ≤ 91 * (11003 + 1048576 * t) := by
  have hpos : 0 < 9915 + 944784 * t :=
    Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 9915)
      (Nat.le_add_right 9915 (944784 * t))
  refine ⟨hpos, ?_⟩
  calc
    100 * (9915 + 944784 * t) = 991500 + 94478400 * t := by
      simp only [Nat.mul_add, ← Nat.mul_assoc]
    _ ≤ 1001273 + 95420416 * t :=
      Nat.add_le_add (by decide) (Nat.mul_le_mul_right t (by decide))
    _ = 91 * (11003 + 1048576 * t) := by
      simp only [Nat.mul_add, ← Nat.mul_assoc]

end GeneralizedCollatz
