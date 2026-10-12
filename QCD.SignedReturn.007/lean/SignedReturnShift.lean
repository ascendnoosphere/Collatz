-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

/-!
# Congruence transport of the affine class

The affine state `q ^ j * n + c * TrapSum q j` changes by `q ^ j * t * d` when
the seed is replaced by `n + t * d`. The difference is a multiple of `d` at
every time, so divisibility by `d` is unchanged at every time. Specializing
`d` to the signed divisor of a parameter record, the first time of
divisibility is the same for `n` and for `n + t * p.D`, in both directions.

Not proved here: existence of a first hit, any lower bound on the absolute
value of a hitting state, equality between the affine state and a raw orbit,
and every construction that produces a large state.
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

/-- Moving the seed by `t * d` adds exactly `q ^ j * t * d` at time `j`. -/
theorem AffineClassShift (q c n t d : ℤ) (j : ℕ) :
    AffineState q c j (n + t * d) =
      AffineState q c j n + q ^ j * t * d := by
  unfold AffineState
  ring

/-- At every time, the seed shift changes the affine state by a multiple of `d`. -/
theorem AffineDifferenceMultiple (q c n t d : ℤ) (j : ℕ) :
    d ∣ AffineState q c j (n + t * d) - AffineState q c j n := by
  have hdiff :
      AffineState q c j (n + t * d) - AffineState q c j n =
        q ^ j * t * d := by
    rw [AffineClassShift]
    ring
  rw [hdiff]
  refine ⟨q ^ j * t, ?_⟩
  ring

/-- Divisibility by `p.D` agrees at every time after a multiple seed shift. -/
theorem AffineDivisibilityShift (p : Parameters) (n t : ℤ) (i : ℕ) :
    p.D ∣ AffineState p.Q p.C i n ↔
      p.D ∣ AffineState p.Q p.C i (n + t * p.D) := by
  -- Substitute the shift before either witness, so the difference stays visible.
  have hshift := AffineClassShift p.Q p.C n t p.D i
  constructor
  · {
      intro h
      obtain ⟨m, hm⟩ := h
      refine ⟨m + p.Q ^ i * t, ?_⟩
      rw [hshift, hm]
      ring
    }
  · {
      intro h
      obtain ⟨m, hm⟩ := h
      refine ⟨m - p.Q ^ i * t, ?_⟩
      have hback :
          AffineState p.Q p.C i n =
            AffineState p.Q p.C i (n + t * p.D) - p.Q ^ i * t * p.D := by
        rw [hshift]
        ring
      rw [hback, hm]
      ring
    }

/-- A multiple of the divisor does not move the first affine divisibility time. -/
theorem FirstHitShift (p : Parameters) (n t : ℤ) (j : ℕ) :
    IsFirstHit p n j ↔ IsFirstHit p (n + t * p.D) j := by
  unfold IsFirstHit
  constructor
  · {
      intro h
      obtain ⟨hj, hearly⟩ := h
      refine ⟨(AffineDivisibilityShift p n t j).mp hj, ?_⟩
      -- Every earlier time differs by a multiple of `p.D`, so failure transports.
      intro i hi hdiv
      exact hearly i hi ((AffineDivisibilityShift p n t i).mpr hdiv)
    }
  · {
      intro h
      obtain ⟨hj, hearly⟩ := h
      refine ⟨(AffineDivisibilityShift p n t j).mpr hj, ?_⟩
      -- The same equivalence at each earlier time gives the opposite direction.
      intro i hi hdiv
      exact hearly i hi ((AffineDivisibilityShift p n t i).mp hdiv)
    }

end GeneralizedCollatz
