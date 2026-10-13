/-
SPDX-License-Identifier: CC-BY-4.0
Coordinate division certificates for imaginary quadratic orders.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace GeneralizedCollatz.QuadraticArithmetic

/-- The norm form records the squared absolute value in the chosen integral basis. -/
def NormForm (tau nu x y : ℤ) : ℤ := x ^ 2 + tau * x * y + nu * y ^ 2

/-- Exact divisibility is the integral image of the multiplication matrix. -/
def CoefficientDivides (tau nu s t x y : ℤ) : Prop :=
  ∃ u v : ℤ, x = s * u - nu * t * v ∧ y = t * u + (s + tau * t) * v

/-- A negative discriminant makes the integral norm positive away from the origin. -/
theorem ImaginaryNormPos (tau nu x y : ℤ) (hd : tau ^ 2 < 4 * nu)
    (hz : ¬(x = 0 ∧ y = 0)) : 0 < NormForm tau nu x y := by
  by_cases hy : y = 0
  · have hx : x ≠ 0 := fun h => hz ⟨h, hy⟩
    simpa [NormForm, hy] using sq_pos_of_ne_zero hx
  · have hdelta : 0 < 4 * nu - tau ^ 2 := by omega
    have hprod : 0 < (4 * nu - tau ^ 2) * y ^ 2 :=
      mul_pos hdelta (sq_pos_of_ne_zero hy)
    have hidentity :
        4 * NormForm tau nu x y =
          (2 * x + tau * y) ^ 2 + (4 * nu - tau ^ 2) * y ^ 2 := by
      unfold NormForm
      ring
    nlinarith [sq_nonneg (2 * x + tau * y)]

/-- Multiplication has an exact norm product without any factorization hypothesis. -/
theorem NormFormMultiplicative (tau nu x y s t : ℤ) :
    NormForm tau nu (x * s - nu * y * t) (x * t + y * s + tau * y * t) =
      NormForm tau nu x y * NormForm tau nu s t := by
  unfold NormForm
  ring

/-- The adjugate supplies a complete, constructive integral division certificate. -/
theorem DividesCoordinates (tau nu s t x y : ℤ)
    (hn : NormForm tau nu s t ≠ 0) :
    CoefficientDivides tau nu s t x y ↔
      NormForm tau nu s t ∣ (s + tau * t) * x + nu * t * y ∧
      NormForm tau nu s t ∣ -t * x + s * y := by
  unfold CoefficientDivides
  constructor
  · rintro ⟨u, v, hx, hy⟩
    constructor
    · refine ⟨u, ?_⟩
      rw [hx, hy]
      unfold NormForm
      ring
    · refine ⟨v, ?_⟩
      rw [hx, hy]
      unfold NormForm
      ring
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    have hx :
        NormForm tau nu s t * x =
          NormForm tau nu s t * (s * u - nu * t * v) := by
      calc
        _ = s * ((s + tau * t) * x + nu * t * y) -
            nu * t * (-t * x + s * y) := by unfold NormForm; ring
        _ = _ := by rw [hu, hv]; ring
    have hy :
        NormForm tau nu s t * y =
          NormForm tau nu s t * (t * u + (s + tau * t) * v) := by
      calc
        _ = t * ((s + tau * t) * x + nu * t * y) +
            (s + tau * t) * (-t * x + s * y) := by unfold NormForm; ring
        _ = _ := by rw [hu, hv]; ring
    exact ⟨u, v, mul_left_cancel₀ hn hx, mul_left_cancel₀ hn hy⟩

/-- A nonzero determinant makes the exact quotient unique in integral coordinates. -/
theorem QuotientUnique (tau nu s t u v a b : ℤ)
    (hn : NormForm tau nu s t ≠ 0)
    (hx : s * u - nu * t * v = s * a - nu * t * b)
    (hy : t * u + (s + tau * t) * v = t * a + (s + tau * t) * b) :
    u = a ∧ v = b := by
  have hu : NormForm tau nu s t * u = NormForm tau nu s t * a := by
    calc
      _ = (s + tau * t) * (s * u - nu * t * v) +
          nu * t * (t * u + (s + tau * t) * v) := by unfold NormForm; ring
      _ = _ := by rw [hx, hy]; unfold NormForm; ring
  have hv : NormForm tau nu s t * v = NormForm tau nu s t * b := by
    calc
      _ = -t * (s * u - nu * t * v) +
          s * (t * u + (s + tau * t) * v) := by unfold NormForm; ring
      _ = _ := by rw [hx, hy]; unfold NormForm; ring
  exact ⟨mul_left_cancel₀ hn hu, mul_left_cancel₀ hn hv⟩

/-- The order with discriminant -20 has no element of norm two. -/
theorem QuadraticFiveNoNormTwo (x y : ℤ) : NormForm 0 5 x y ≠ 2 := by
  intro h
  unfold NormForm at h
  have hy : y = 0 := by
    by_contra hne
    have hsq : 1 ≤ y ^ 2 := by have hp := sq_pos_of_ne_zero hne; omega
    nlinarith [sq_nonneg x]
  subst y
  simp only [mul_zero, add_zero] at h
  have hlo : -3 ≤ 2 * x := by nlinarith [sq_nonneg (x + 2)]
  have hhi : 2 * x ≤ 3 := by nlinarith [sq_nonneg (x - 2)]
  have hcases : x = -1 ∨ x = 0 ∨ x = 1 := by omega
  rcases hcases with hneg | hzero | hpos
  · norm_num [hneg] at h
  · norm_num [hzero] at h
  · norm_num [hpos] at h

/-- The product (1+w)(1-w)=6 enters the division ideal after multiplication by two. -/
theorem QuadraticFiveDividesSix : CoefficientDivides 0 5 1 1 6 0 := by
  exact ⟨1, -1, by norm_num, by norm_num⟩

/-- The same divisor does not divide three, so element-gcd guard cancellation fails. -/
theorem QuadraticFiveNotDividesThree : ¬CoefficientDivides 0 5 1 1 3 0 := by
  rw [DividesCoordinates 0 5 1 1 3 0 (by norm_num [NormForm])]
  norm_num [NormForm]

/-- The unimodular change of basis exposes a triangular ideal, including nonmaximal orders. -/
theorem TriangleMembershipIff (tau nu a b g u v x y : ℤ)
    (hbez : a * u + b * v = 1) :
    CoefficientDivides tau nu (g * a) (g * b) x y ↔
      ∃ k l : ℤ,
        x = (g * NormForm tau nu a b) * k +
          (g * (a * v - (tau * a + nu * b) * u)) * l ∧ y = g * l := by
  constructor
  · rintro ⟨r, s, hx, hy⟩
    refine ⟨u * r + (tau * u - v) * s, b * r + (a + tau * b) * s, ?_, ?_⟩
    · have hre :
          (g * NormForm tau nu a b) * (u * r + (tau * u - v) * s) +
              (g * (a * v - (tau * a + nu * b) * u)) *
                (b * r + (a + tau * b) * s) =
            (g * a * r - nu * (g * b) * s) * (a * u + b * v) := by
        unfold NormForm
        ring
      rw [hre, hbez, mul_one]
      exact hx
    · rw [hy]
      ring
  · rintro ⟨k, l, hx, hy⟩
    refine ⟨(a + tau * b) * k + (v - tau * u) * l, -b * k + u * l, ?_, ?_⟩
    · have hre :
          g * a * ((a + tau * b) * k + (v - tau * u) * l) -
              nu * (g * b) * (-b * k + u * l) =
            (g * NormForm tau nu a b) * k +
              (g * (a * v - (tau * a + nu * b) * u)) * l := by
        unfold NormForm
        ring
      rw [hre]
      exact hx
    · have hre :
          g * b * ((a + tau * b) * k + (v - tau * u) * l) +
              (g * a + tau * (g * b)) * (-b * k + u * l) =
            (g * l) * (a * u + b * v) := by ring
      rw [hre, hbez, mul_one]
      exact hy

/-- The primitive-coordinate norm gives the quotient's diagonal product exactly. -/
theorem TriangleNormProduct (tau nu a b g : ℤ) :
    (g * NormForm tau nu a b) * g = NormForm tau nu (g * a) (g * b) := by
  unfold NormForm
  ring

end GeneralizedCollatz.QuadraticArithmetic
