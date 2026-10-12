-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Tactic.Ring

/-!
# Unit return

With multiplier `1`, the affine state is the translation `n + j * C`. At a first
hit the raw state equals that translation, so the next raw step is exact
division by `D`. The absolute value of the quotient satisfies the core
inequality at that seed with expansion `1` and additive term `j * |C|`. The
hitting time is left inside that term: no uniform substitute for `j` is proved.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Affine state after `j` undivided steps, with offset sum `TrapSum q j`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- `j` is the first time `p.D` divides the affine state of the seed `n`. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n

/-- With multiplier one, the offset sum is the time, so the state is a translation. -/
theorem UnitAffine (C n : ℤ) (j : ℕ) :
    AffineState 1 C j n = n + (j : ℤ) * C := by
  unfold AffineState
  rw [TrapSumOne j]
  have hpow : (1 : ℤ) ^ j = 1 := one_pow j
  rw [hpow]
  show (1 : ℤ) * n + C * (j : ℤ) = n + (j : ℤ) * C
  ring

/-- A division-free prefix with multiplier one is translation by the offset. -/
theorem UnitPrefix (p : Parameters) (n : ℤ) (j : ℕ) (hQ : p.Q = 1)
    (h : ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n) :
    Iterate (RawStep p) j n = n + (j : ℤ) * p.C := by
  revert h
  induction j with
  | zero => {
      intro _h
      change n = n + (0 : ℤ) * p.C
      ring
    }
  | succ j ih => {
      intro h
      have hlt : ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self j))
      have ihj : Iterate (RawStep p) j n = n + (j : ℤ) * p.C := ih hlt
      have haff : AffineState p.Q p.C j n = n + (j : ℤ) * p.C := by
        rw [hQ]
        exact UnitAffine p.C n j
      have hj : ¬ p.D ∣ AffineState p.Q p.C j n :=
        h j (Nat.lt_succ_self j)
      have hnd : ¬ p.D ∣ Iterate (RawStep p) j n := by
        rw [ihj, ← haff]
        exact hj
      have hstep : Iterate (RawStep p) (j + 1) n =
          RawStep p (Iterate (RawStep p) j n) := rfl
      have haffine : RawStep p (Iterate (RawStep p) j n) =
          p.Q * Iterate (RawStep p) j n + p.C :=
        RawStepAffine p _ hnd
      rw [hstep, haffine, hQ, ihj]
      have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := Nat.cast_succ j
      rw [hcast]
      show (1 : ℤ) * (n + (j : ℤ) * p.C) + p.C = n + ((j : ℤ) + 1) * p.C
      ring
    }

/-- At a first hit with multiplier one, the next raw step divides `n + j * C`. -/
theorem UnitReturn (p : Parameters) (n : ℤ) (j : ℕ)
    (hQ : p.Q = 1) (h : IsFirstHit p n j) :
    RawStep p (Iterate (RawStep p) j n) = (n + (j : ℤ) * p.C) / p.D := by
  obtain ⟨hdvd, hfree⟩ := h
  have hstate : Iterate (RawStep p) j n = n + (j : ℤ) * p.C :=
    UnitPrefix p n j hQ hfree
  have haff : AffineState p.Q p.C j n = n + (j : ℤ) * p.C := by
    rw [hQ]
    exact UnitAffine p.C n j
  have hnum : p.D ∣ n + (j : ℤ) * p.C := by
    rw [← haff]
    exact hdvd
  have hdiv : p.D ∣ Iterate (RawStep p) j n := by
    rw [hstate]
    exact hnum
  rw [RawStep, if_pos hdiv, hstate]

/-- The divided return is at most `|n| + j * |C|` after cancelling `|D|`. -/
theorem UnitMagnitude (p : Parameters) (n : ℤ) (j : ℕ)
    (hQ : p.Q = 1) (h : IsFirstHit p n j) :
    p.D.natAbs * (RawStep p (Iterate (RawStep p) j n)).natAbs ≤
      n.natAbs + j * p.C.natAbs := by
  have hret : RawStep p (Iterate (RawStep p) j n) =
      (n + (j : ℤ) * p.C) / p.D :=
    UnitReturn p n j hQ h
  rw [hret]
  have haff : AffineState p.Q p.C j n = n + (j : ℤ) * p.C := by
    rw [hQ]
    exact UnitAffine p.C n j
  have hdvd : p.D ∣ n + (j : ℤ) * p.C := by
    rw [← haff]
    exact h.1
  have hquot : ((n + (j : ℤ) * p.C) / p.D).natAbs =
      (n + (j : ℤ) * p.C).natAbs / p.D.natAbs :=
    Int.natAbs_ediv_of_dvd hdvd
  rw [hquot]
  have hdiv : p.D.natAbs ∣ (n + (j : ℤ) * p.C).natAbs :=
    Int.natAbs_dvd_natAbs.mpr hdvd
  have hcancel : p.D.natAbs * ((n + (j : ℤ) * p.C).natAbs / p.D.natAbs) =
      (n + (j : ℤ) * p.C).natAbs :=
    Nat.mul_div_cancel' hdiv
  rw [hcancel]
  have htri : (n + (j : ℤ) * p.C).natAbs ≤
      n.natAbs + ((j : ℤ) * p.C).natAbs :=
    Int.natAbs_add_le _ _
  have hscale : ((j : ℤ) * p.C).natAbs = (j : ℤ).natAbs * p.C.natAbs :=
    Int.natAbs_mul _ _
  have hj : (j : ℤ).natAbs = j := Int.natAbs_natCast j
  rw [hscale, hj] at htri
  exact htri

/-- The same return is a core inequality at that seed, with `A = 1` and `B = j * |C|`. -/
theorem UnitCoreAtSeed (p : Parameters) (n : ℤ) (j : ℕ)
    (hQ : p.Q = 1) (h : IsFirstHit p n j) :
    p.Q.natAbs < p.D.natAbs ∧
      p.D.natAbs * (RawStep p (Iterate (RawStep p) j n)).natAbs ≤
        p.Q.natAbs * n.natAbs + j * p.C.natAbs := by
  have hA : p.Q.natAbs = 1 := by
    rw [hQ]
    exact Int.natAbs_one
  refine ⟨?_, ?_⟩
  · {
      rw [hA]
      have hd : 2 ≤ p.D.natAbs := p.DAdmissible
      omega
    }
  · {
      rw [hA, Nat.one_mul]
      exact UnitMagnitude p n j hQ h
    }

end GeneralizedCollatz
