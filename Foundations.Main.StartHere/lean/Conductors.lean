import Mathlib.Data.Int.GCD
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The conductor of an integer scalar closure equation.

For nonzero `delta`, this is the positive divisibility obstruction to solving
`delta * n = c * b`. It is not the ambient lattice index, and it does not
supply the intermediate guards of a raw or accelerated itinerary.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The conductor uses the determinant magnitude divided by the common divisor. -/
def Conductor (delta b : ℤ) : ℕ := delta.natAbs / Int.gcd delta b

/-- The conductor exactly detects the additive parameters satisfying scalar divisibility. -/
theorem ConductorCriterion (delta b c : ℤ) (nonzero : delta ≠ 0) :
    Conductor delta b ∣ c.natAbs ↔ delta ∣ b * c := by
  have positive : 0 < Int.gcd delta b := Int.gcd_pos_of_ne_zero_left b nonzero
  have hg : (Int.gcd delta b : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt positive
  have quotient := Int.ediv_dvd_iff_dvd_mul (c := c) (Int.gcd_dvd_left delta b) hg
  have reduced : delta / (Int.gcd delta b : ℤ) ∣ c ↔ delta ∣ b * c := by
    constructor
    · intro hc
      have hd := quotient.mp hc
      obtain ⟨k, hk⟩ := Int.gcd_dvd_right delta b
      have hmul := dvd_mul_of_dvd_left hd k
      have heq : (Int.gcd delta b : ℤ) * c * k = b * c := by
        calc
          (Int.gcd delta b : ℤ) * c * k = (Int.gcd delta b : ℤ) * k * c := by ring
          _ = b * c := congrArg (fun x : ℤ => x * c) hk.symm
      rw [heq] at hmul
      exact hmul
    · intro hc
      apply quotient.mpr
      rw [Int.gcd_eq_gcd_ab, add_mul]
      apply Int.dvd_add
      · exact ⟨Int.gcdA delta b * c, by ring⟩
      · have hmul := dvd_mul_of_dvd_left hc (Int.gcdB delta b)
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_ediv_of_dvd (Int.gcd_dvd_left delta b),
    Int.natAbs_natCast] at reduced
  exact reduced

/-- Scalar divisibility is equivalent to integral closure, with either determinant sign. -/
theorem ConductorIntegralWitness (delta b c : ℤ) (nonzero : delta ≠ 0) :
    Conductor delta b ∣ c.natAbs ↔ ∃ n : ℤ, delta * n = c * b := by
  rw [ConductorCriterion delta b c nonzero]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa [mul_comm] using hn.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa [mul_comm] using hn.symm⟩

end GeneralizedCollatz
