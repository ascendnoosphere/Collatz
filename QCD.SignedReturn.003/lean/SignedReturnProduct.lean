-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Data.Int.Basic

/-!
# Exact product of a signed division

If `D ≠ 0` and `D` divides `a`, the truncating quotient is the divisibility
witness, so `D * (a / D) = a`. Absolute values multiply:
`D.natAbs * (a / D).natAbs = a.natAbs`, whether or not `D` is negative. Both
identities specialize to the affine state at a first hit. The identity is a
product, not a triangle bound, and no nonnegative remainder is discarded.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The affine state of multiplier `q`, offset `c`, time `j` and seed `n`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- `D` divides the affine state at time `j` and at no earlier time. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n

/-- A nonzero divisor multiplies the truncating quotient back to the dividend. -/
theorem ReturnProduct (D a : ℤ) (hD : D ≠ 0) (h : D ∣ a) :
    D * (a / D) = a := by
  obtain ⟨k, hk⟩ := h
  have hquot : a / D = k := by
    rw [hk]
    exact Int.mul_ediv_cancel_left k hD
  rw [hquot]
  show D * k = a
  exact hk.symm

/-- At a first hit the divisor multiplies the affine quotient back to the state. -/
theorem ReturnProductFirstHit (p : Parameters) (n : ℤ) (j : ℕ)
    (h : IsFirstHit p n j) :
    p.D * (AffineState p.Q p.C j n / p.D) =
      AffineState p.Q p.C j n := by
  have hD : p.D ≠ 0 := Parameters.DNonzero p
  have hdvd : p.D ∣ AffineState p.Q p.C j n := h.left
  show p.D * (AffineState p.Q p.C j n / p.D) =
    AffineState p.Q p.C j n
  exact ReturnProduct p.D (AffineState p.Q p.C j n) hD hdvd

/-- Absolute values of an exact quotient multiply, for either sign of `D`. -/
theorem ReturnAbsProduct (D a : ℤ) (hD : D ≠ 0) (h : D ∣ a) :
    D.natAbs * (a / D).natAbs = a.natAbs := by
  obtain ⟨k, hk⟩ := h
  have hquot : a / D = k := by
    rw [hk]
    exact Int.mul_ediv_cancel_left k hD
  rw [hquot, hk]
  show D.natAbs * k.natAbs = (D * k).natAbs
  exact (Int.natAbs_mul D k).symm

/-- At a first hit the absolute values of the divisor and the quotient multiply. -/
theorem ReturnAbsProductFirstHit (p : Parameters) (n : ℤ) (j : ℕ)
    (h : IsFirstHit p n j) :
    p.D.natAbs * (AffineState p.Q p.C j n / p.D).natAbs =
      (AffineState p.Q p.C j n).natAbs := by
  have hD : p.D ≠ 0 := Parameters.DNonzero p
  have hdvd : p.D ∣ AffineState p.Q p.C j n := h.left
  show p.D.natAbs * (AffineState p.Q p.C j n / p.D).natAbs =
    (AffineState p.Q p.C j n).natAbs
  exact ReturnAbsProduct p.D (AffineState p.Q p.C j n) hD hdvd

end GeneralizedCollatz
