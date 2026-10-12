-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Logic.Function.Iterate

/-!
The classical shortcut sends an even natural number to its half and an odd
natural number to `(3x+1)/2`. The states `1` and `2` form a 2-cycle. If a
parent reaches `1` at time `t` and a source meets that parent orbit at times
`a` and `b`, the source reaches `1` at an explicit time built from `a`, `b`,
and `t`. The time need not be the first arrival, and the identity assumes the
parent rather than producing one.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Classical shortcut: halve an even input, and send an odd input through
    `(3x+1)/2`. -/
def Shortcut (x : ℕ) : ℕ :=
  if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

/-- The shortcut fixes zero. -/
theorem ShortcutZero : Shortcut 0 = 0 := by
  unfold Shortcut
  rw [if_pos (Nat.zero_mod 2)]

/-- One is odd, so the shortcut applies the odd branch. -/
theorem OneModTwo : (1 : ℕ) % 2 = 1 :=
  Nat.mod_eq_of_lt Nat.one_lt_two

/-- The odd branch at `1` is the other point of the terminal cycle. -/
theorem ShortcutOne : Shortcut 1 = 2 := by
  unfold Shortcut
  have hodd : ¬ (1 : ℕ) % 2 = 0 := by
    rw [OneModTwo]
    exact Nat.one_ne_zero
  rw [if_neg hodd]

/-- The even branch at `2` returns to `1`. -/
theorem ShortcutTwo : Shortcut 2 = 1 := by
  unfold Shortcut
  rw [if_pos (Nat.mod_self 2)]

/-- A positive input has a positive shortcut image. -/
theorem ShortcutPositive {x : ℕ} (hx : 0 < x) : 0 < Shortcut x := by
  unfold Shortcut
  by_cases heven : x % 2 = 0
  · {
      rw [if_pos heven]
      have hnot : x ≠ 1 := by
        intro h
        rw [h] at heven
        rw [OneModTwo] at heven
        exact Nat.one_ne_zero heven
      have htwo : 2 ≤ x := by
        omega
      exact (Nat.div_pos_iff).2 ⟨Nat.two_pos, htwo⟩
    }
  · {
      rw [if_neg heven]
      have hden : 2 ≤ 3 * x + 1 := by
        omega
      exact (Nat.div_pos_iff).2 ⟨Nat.two_pos, hden⟩
    }

/-- Every iterate of zero remains zero. -/
theorem IterateAtZero (n : ℕ) : Shortcut^[n] 0 = 0 := by
  induction n with
  | zero => {
      rw [Function.iterate_zero_apply]
    }
  | succ n inductionHypothesis => {
      rw [Function.iterate_succ_apply', inductionHypothesis, ShortcutZero]
    }

/-- Reaching `1` forces the starting state to be positive. -/
theorem ReachesOnePositive (x n : ℕ) (h : Shortcut^[n] x = 1) : 0 < x := by
  apply Nat.pos_of_ne_zero
  intro hx
  have hzero : Shortcut^[n] x = 0 := by
    rw [hx]
    exact IterateAtZero n
  rw [hzero] at h
  exact Nat.one_ne_zero h.symm

/-- Positive inputs stay positive under every iterate. -/
theorem IteratePositive (n x : ℕ) (hx : 0 < x) : 0 < Shortcut^[n] x := by
  induction n with
  | zero => {
      rw [Function.iterate_zero_apply]
      exact hx
    }
  | succ n inductionHypothesis => {
      rw [Function.iterate_succ_apply']
      exact ShortcutPositive inductionHypothesis
    }

/-- The successor flips the remainder modulo `2`. -/
theorem SuccModTwo (m : ℕ) :
    (m + 1) % 2 = if m % 2 = 0 then 1 else 0 := by
  cases Nat.mod_two_eq_zero_or_one m with
  | inl heven => {
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero heven
      have hmod : (2 * k + 1) % 2 = 1 := by
        have hraw : (2 * k + 1) % 2 = 1 % 2 := Nat.mul_add_mod 2 k 1
        rw [Nat.mod_eq_of_lt Nat.one_lt_two] at hraw
        exact hraw
      rw [hk]
      have hmul : (2 * k) % 2 = 0 := Nat.mul_mod_right 2 k
      rw [hmul, if_pos rfl]
      exact hmod
    }
  | inr hodd => {
      have hsplit : 2 * (m / 2) + m % 2 = m := Nat.div_add_mod m 2
      rw [hodd] at hsplit
      have hm : m + 1 = 2 * (m / 2 + 1) := by
        calc
          m + 1 = (2 * (m / 2) + 1) + 1 := by
            rw [hsplit]
          _ = 2 * (m / 2) + (1 + 1) := by
            rw [Nat.add_assoc]
          _ = 2 * (m / 2) + 2 * 1 := by rfl
          _ = 2 * (m / 2 + 1) := by
            rw [← Nat.mul_add]
      have hmod : (m + 1) % 2 = 0 := by
        rw [hm]
        exact Nat.mul_mod_right 2 (m / 2 + 1)
      rw [hodd, if_neg Nat.one_ne_zero]
      exact hmod
    }

/-- Even iterates of `1` are `1`, and odd iterates are `2`. -/
theorem TerminalPhase (m : ℕ) :
    Shortcut^[m] 1 = if m % 2 = 0 then 1 else 2 := by
  induction m with
  | zero => {
      rw [Function.iterate_zero_apply, Nat.zero_mod, if_pos rfl]
    }
  | succ m inductionHypothesis => {
      rw [Function.iterate_succ_apply', inductionHypothesis]
      have hflip := SuccModTwo m
      by_cases heven : m % 2 = 0
      · {
          rw [if_pos heven, ShortcutOne]
          have hodd : (m + 1) % 2 ≠ 0 := by
            rw [hflip, if_pos heven]
            exact Nat.one_ne_zero
          rw [if_neg hodd]
        }
      · {
          have hodd : m % 2 = 1 := by
            cases Nat.mod_two_eq_zero_or_one m with
            | inl hzero => {
                exact (heven hzero).elim
              }
            | inr hone => {
                exact hone
              }
          rw [if_neg heven, ShortcutTwo]
          have hevenSucc : (m + 1) % 2 = 0 := by
            rw [hflip, if_neg heven]
          rw [if_pos hevenSucc]
        }
    }

/-- Applying `m` steps after `n` steps is one block of `m + n` steps. -/
theorem ShortcutIterateAdd (m n x : ℕ) :
    Shortcut^[m + n] x = Shortcut^[m] (Shortcut^[n] x) := by
  induction m with
  | zero => {
      rw [Nat.zero_add, Function.iterate_zero_apply]
    }
  | succ m inductionHypothesis => {
      rw [Nat.succ_add, Function.iterate_succ_apply', inductionHypothesis]
      rw [← Function.iterate_succ_apply' Shortcut m (Shortcut^[n] x)]
    }

/-- Certified shortcut time of a source joined to a parent that reaches `1`.
    `a` is the source time of the join, `b` is the parent time of the join,
    and `t` is a parent time with image `1`. -/
def ParentCertifiedTime (a b t : ℕ) : ℕ :=
  if b ≤ t then a + (t - b) else a + ((b - t) % 2)

/-- Before the parent's arrival at `1`, the remaining parent time is enough. -/
theorem ParentTimeBefore
    (source parent a b t : ℕ)
    (hle : b ≤ t)
    (hParent : Shortcut^[t] parent = 1)
    (hJoin : Shortcut^[a] source = Shortcut^[b] parent) :
    Shortcut^[a + (t - b)] source = 1 := by
  have hcomm : (t - b) + a = a + (t - b) := Nat.add_comm (t - b) a
  have htail := ShortcutIterateAdd (t - b) a source
  have hparentTail := ShortcutIterateAdd (t - b) b parent
  have hsum : (t - b) + b = t := Nat.sub_add_cancel hle
  rw [← hcomm, htail, hJoin, ← hparentTail, hsum, hParent]

/-- After the parent's arrival at `1`, the cycle phase is one parity bit. -/
theorem ParentTimeAfter
    (source parent a b t : ℕ)
    (hgt : t < b)
    (hParent : Shortcut^[t] parent = 1)
    (hJoin : Shortcut^[a] source = Shortcut^[b] parent) :
    Shortcut^[a + ((b - t) % 2)] source = 1 := by
  have hle : t ≤ b := Nat.le_of_lt hgt
  have hsum : (b - t) + t = b := Nat.sub_add_cancel hle
  have hsplit := ShortcutIterateAdd (b - t) t parent
  have hback : Shortcut^[b] parent = Shortcut^[b - t] 1 := by
    calc
      Shortcut^[b] parent = Shortcut^[(b - t) + t] parent := by
        rw [hsum]
      _ = Shortcut^[b - t] (Shortcut^[t] parent) := hsplit
      _ = Shortcut^[b - t] 1 := by
        rw [hParent]
  have hjoined : Shortcut^[a] source = Shortcut^[b - t] 1 := by
    rw [hJoin, hback]
  have hterm := TerminalPhase (b - t)
  cases Nat.mod_two_eq_zero_or_one (b - t) with
  | inl heven => {
      have hone : Shortcut^[b - t] 1 = 1 := by
        rw [hterm, if_pos heven]
      have htime : a + ((b - t) % 2) = a := by
        rw [heven, Nat.add_zero]
      rw [htime, hjoined, hone]
    }
  | inr hodd => {
      have htwo : Shortcut^[b - t] 1 = 2 := by
        have hne : (b - t) % 2 ≠ 0 := by
          rw [hodd]
          exact Nat.one_ne_zero
        rw [hterm, if_neg hne]
      have htime : a + ((b - t) % 2) = a + 1 := by
        rw [hodd]
      have hstep :
          Shortcut^[a + 1] source = Shortcut (Shortcut^[a] source) :=
        Function.iterate_succ_apply' Shortcut a source
      rw [htime, hstep, hjoined, htwo, ShortcutTwo]
    }

/-- A join to a parent that reaches `1` gives an explicit source time at `1`.
    The parent is a hypothesis. The time is not asserted to be minimal. -/
theorem ParentCertifiedTimeAtOne
    (source parent a b t : ℕ)
    (hParent : Shortcut^[t] parent = 1)
    (hJoin : Shortcut^[a] source = Shortcut^[b] parent) :
    Shortcut^[ParentCertifiedTime a b t] source = 1 := by
  unfold ParentCertifiedTime
  by_cases hle : b ≤ t
  · {
      rw [if_pos hle]
      show Shortcut^[a + (t - b)] source = 1
      exact ParentTimeBefore source parent a b t hle hParent hJoin
    }
  · {
      have hgt : t < b := (Nat.not_le).1 hle
      rw [if_neg hle]
      show Shortcut^[a + ((b - t) % 2)] source = 1
      exact ParentTimeAfter source parent a b t hgt hParent hJoin
    }

/-- The certified time can be strictly later than another time at `1`. -/
theorem ParentCertifiedTimeNotAlwaysLeast :
    Shortcut^[ParentCertifiedTime 2 0 0] 1 = 1 ∧
      Shortcut^[0] 1 = 1 ∧
      ParentCertifiedTime 2 0 0 = 2 := by
  have htime : ParentCertifiedTime 2 0 0 = 2 := by
    unfold ParentCertifiedTime
    rw [if_pos (Nat.le_refl 0), Nat.sub_zero, Nat.add_zero]
  refine ⟨?_, ?_, htime⟩
  · rw [htime, TerminalPhase, if_pos (Nat.mod_self 2)]
  · rw [Function.iterate_zero_apply]

/-- An odd phase past time `0` at parent `1` needs one further step from `2`. -/
theorem ParentPhaseNeedsOneStep :
    ParentCertifiedTime 0 1 0 = 1 ∧
      Shortcut^[1] 1 = 2 ∧
      Shortcut^[ParentCertifiedTime 0 1 0] 2 = 1 := by
  have htime : ParentCertifiedTime 0 1 0 = 1 := by
    unfold ParentCertifiedTime
    have hgt : ¬ (1 : ℕ) ≤ 0 := by
      intro h
      exact Nat.not_succ_le_zero 0 h
    rw [if_neg hgt, Nat.sub_zero, OneModTwo, Nat.zero_add]
  refine ⟨htime, ?_, ?_⟩
  · rw [Function.iterate_succ_apply' Shortcut 0 1,
      Function.iterate_zero_apply, ShortcutOne]
  · rw [htime, Function.iterate_succ_apply' Shortcut 0 2,
      Function.iterate_zero_apply, ShortcutTwo]

end GeneralizedCollatz
