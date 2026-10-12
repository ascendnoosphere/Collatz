-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps

/-!
# Magnitude of one affine return

The absolute value of an affine state is at most the sum of the absolute
values of its two terms. At a first hit the divisor divides that state, so
the absolute value of the exact quotient, multiplied by the absolute value of
the divisor, equals the absolute value of the state and inherits the same
majorant. The comparison is one seed and one hitting time. It is not a
uniform core.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The affine state of multiplier `q`, offset `c`, time `j` and seed `n`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- The affine state meets `D` at time `j` and at no earlier time. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n

/-- Exact division preserves absolute value: `|d| * |a / d| = |a|`. -/
theorem NatAbsExactDiv (d a : ℤ) (h : d ∣ a) :
    d.natAbs * (a / d).natAbs = a.natAbs := by
  have hcancel : d * (a / d) = a := Int.mul_ediv_cancel_of_dvd h
  have habs : (d * (a / d)).natAbs = a.natAbs := by
    rw [hcancel]
  rw [Int.natAbs_mul] at habs
  exact habs

/-- The triangle inequality, then absolute values of a product and of a power. -/
theorem AffineTriangle (q c n : ℤ) (j : ℕ) :
    (q ^ j * n + c * TrapSum q j).natAbs ≤
      q.natAbs ^ j * n.natAbs + c.natAbs * (TrapSum q j).natAbs := by
  have htri :
      (q ^ j * n + c * TrapSum q j).natAbs ≤
        (q ^ j * n).natAbs + (c * TrapSum q j).natAbs :=
    Int.natAbs_add_le (q ^ j * n) (c * TrapSum q j)
  have hprod : (q ^ j * n).natAbs = (q ^ j).natAbs * n.natAbs :=
    Int.natAbs_mul (q ^ j) n
  have hpow : (q ^ j).natAbs = q.natAbs ^ j := Int.natAbs_pow q j
  have hoff : (c * TrapSum q j).natAbs =
      c.natAbs * (TrapSum q j).natAbs :=
    Int.natAbs_mul c (TrapSum q j)
  have hright :
      (q ^ j * n).natAbs + (c * TrapSum q j).natAbs =
        q.natAbs ^ j * n.natAbs +
          c.natAbs * (TrapSum q j).natAbs := by
    rw [hprod, hpow, hoff]
  calc
    (q ^ j * n + c * TrapSum q j).natAbs
        ≤ (q ^ j * n).natAbs + (c * TrapSum q j).natAbs := htri
    _ = q.natAbs ^ j * n.natAbs + c.natAbs * (TrapSum q j).natAbs := hright

/-- One seed and one hitting time, not a uniform core. -/
theorem ReturnMagnitude (p : Parameters) (n : ℤ) (j : ℕ)
    (h : IsFirstHit p n j) :
    p.D.natAbs * (AffineState p.Q p.C j n / p.D).natAbs ≤
      p.Q.natAbs ^ j * n.natAbs +
        p.C.natAbs * (TrapSum p.Q j).natAbs := by
  unfold IsFirstHit at h
  have hdvd : p.D ∣ AffineState p.Q p.C j n := h.left
  have hid :
      p.D.natAbs * (AffineState p.Q p.C j n / p.D).natAbs =
        (AffineState p.Q p.C j n).natAbs :=
    NatAbsExactDiv p.D (AffineState p.Q p.C j n) hdvd
  rw [hid]
  show (AffineState p.Q p.C j n).natAbs ≤
    p.Q.natAbs ^ j * n.natAbs + p.C.natAbs * (TrapSum p.Q j).natAbs
  unfold AffineState
  exact AffineTriangle p.Q p.C n j

end GeneralizedCollatz
