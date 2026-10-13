/-
SPDX-License-Identifier: CC-BY-4.0
Integral guard and block certificates for dyadic quadratic dynamics.
-/
import QuadraticArithmetic
import Mathlib.Algebra.GroupWithZero.Divisibility

namespace GeneralizedCollatz.QuadraticArithmetic

/-- The stable class has odd coefficients and coordinate difference twice an odd integer. -/
def DyadicStableClass (x y : ℤ) : Prop :=
  ∃ a b : ℤ, y = 2 * a + 1 ∧ x - y = 2 * (2 * b + 1)

/-- The quadratic division guard reduces to one power-of-two difference test. -/
theorem DyadicDividesDifference (D x y : ℤ) (e : ℕ)
    (hD : 1 + D = (2 : ℤ) ^ e) :
    CoefficientDivides 0 D 1 1 x y ↔ (2 : ℤ) ^ e ∣ x - y := by
  have hn : NormForm 0 D 1 1 = (2 : ℤ) ^ e := by
    simpa [NormForm] using hD
  have hne : NormForm 0 D 1 1 ≠ 0 := by
    rw [hn]
    exact pow_ne_zero e (by norm_num)
  rw [DividesCoordinates 0 D 1 1 x y hne, hn]
  constructor
  · rintro ⟨_, k, hk⟩
    refine ⟨-k, ?_⟩
    linarith
  · rintro ⟨k, hk⟩
    constructor
    · refine ⟨k + y, ?_⟩
      calc
        _ = (x - y) + (1 + D) * y := by ring
        _ = _ := by rw [hk, hD]; ring
    · refine ⟨-k, ?_⟩
      linarith

/-- An odd factor cannot supply any additional power of two. -/
theorem PowerTwoOddDvdIff (e k : ℕ) (b : ℤ) :
    (2 : ℤ) ^ e ∣ (2 : ℤ) ^ k * (2 * b + 1) ↔ e ≤ k := by
  constructor
  · intro h
    by_contra hle
    have hke : k + 1 ≤ e := by omega
    have hd : (2 : ℤ) ^ (k + 1) ∣ (2 : ℤ) ^ k * (2 * b + 1) :=
      dvd_trans (pow_dvd_pow (2 : ℤ) hke) h
    rw [pow_succ] at hd
    have hodd : (2 : ℤ) ∣ 2 * b + 1 :=
      (mul_dvd_mul_iff_left (pow_ne_zero k (by norm_num : (2 : ℤ) ≠ 0))).mp hd
    rcases hodd with ⟨t, ht⟩
    omega
  · intro hle
    exact dvd_trans (pow_dvd_pow (2 : ℤ) hle) ⟨2 * b + 1, rfl⟩

/-- Stable seeds have their first legal division after exactly e-1 doublings. -/
theorem DyadicStableGuard (D x y : ℤ) (e k : ℕ)
    (hD : 1 + D = (2 : ℤ) ^ e) (hc : DyadicStableClass x y) :
    CoefficientDivides 0 D 1 1 ((2 : ℤ) ^ k * x) ((2 : ℤ) ^ k * y) ↔
      e ≤ k + 1 := by
  rcases hc with ⟨a, b, _, hd⟩
  rw [DyadicDividesDifference D _ _ e hD]
  have hre :
      (2 : ℤ) ^ k * x - (2 : ℤ) ^ k * y =
        (2 : ℤ) ^ (k + 1) * (2 * b + 1) := by
    calc
      _ = (2 : ℤ) ^ k * (x - y) := by ring
      _ = (2 : ℤ) ^ k * (2 * (2 * b + 1)) := by rw [hd]
      _ = _ := by rw [pow_succ]; ring
  rw [hre, PowerTwoOddDvdIff]

/-- One complete legal block preserves the same integral class and has exact norm gain. -/
theorem DyadicStableBlock (D x y : ℤ) (e : ℕ) (he : 3 ≤ e)
    (hD : 1 + D = (2 : ℤ) ^ e) (hc : DyadicStableClass x y) :
    ∃ u v : ℤ,
      (2 : ℤ) ^ (e - 1) * x = u - D * v ∧
      (2 : ℤ) ^ (e - 1) * y = u + v ∧
      DyadicStableClass u v ∧
      NormForm 0 D u v = (2 : ℤ) ^ (e - 2) * NormForm 0 D x y := by
  rcases hc with ⟨a, b, hy, hd⟩
  have hx : x = y + 2 * (2 * b + 1) := by linarith
  have hp1 : (2 : ℤ) ^ e = 2 * (2 : ℤ) ^ (e - 1) := by
    calc
      _ = (2 : ℤ) ^ ((e - 1) + 1) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = _ := by rw [pow_succ]; ring
  have hp2 : (2 : ℤ) ^ e = 4 * (2 : ℤ) ^ (e - 2) := by
    calc
      _ = (2 : ℤ) ^ ((e - 2) + 2) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = _ := by rw [pow_add]; ring
  have hp3 : (2 : ℤ) ^ (e - 1) = 4 * (2 : ℤ) ^ (e - 3) := by
    calc
      _ = (2 : ℤ) ^ ((e - 3) + 2) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = _ := by rw [pow_add]; ring
  have hp4 : (2 : ℤ) ^ (e - 1) = 2 * (2 : ℤ) ^ (e - 2) := by
    calc
      _ = (2 : ℤ) ^ ((e - 2) + 1) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = _ := by rw [pow_succ]; ring
  refine ⟨(2 : ℤ) ^ (e - 1) * y + (2 * b + 1), -(2 * b + 1), ?_, ?_, ?_, ?_⟩
  · calc
      _ = (2 : ℤ) ^ (e - 1) * (y + 2 * (2 * b + 1)) := by rw [hx]
      _ = (2 : ℤ) ^ (e - 1) * y + (1 + D) * (2 * b + 1) := by
        rw [hD, hp1]
        ring
      _ = _ := by ring
  · ring
  · refine ⟨-b - 1, (2 : ℤ) ^ (e - 3) * y + b, ?_, ?_⟩
    · ring
    · rw [hp3]
      ring
  · have hde : D = 4 * (2 : ℤ) ^ (e - 2) - 1 := by rw [hp2] at hD; omega
    rw [hx, hp4, hde]
    unfold NormForm
    ring

/-- The exceptional primitive block contracts its positive integer norm. -/
theorem DyadicExceptionalNormIdentity (D b t : ℤ) (e : ℕ) (he : 1 ≤ e)
    (hD : 1 + D = (2 : ℤ) ^ e) :
    (2 : ℤ) ^ e * NormForm 0 D (2 * b + t) (-t) =
      4 * NormForm 0 D (b + (2 : ℤ) ^ (e - 1) * t) b := by
  have hp : (2 : ℤ) ^ e = 2 * (2 : ℤ) ^ (e - 1) := by
    calc
      _ = (2 : ℤ) ^ ((e - 1) + 1) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = _ := by rw [pow_succ]; ring
  have hd : D = 2 * (2 : ℤ) ^ (e - 1) - 1 := by rw [hp] at hD; omega
  rw [hp, hd]
  unfold NormForm
  ring

/-- Strict norm decrease proves termination of repeated exceptional primitive blocks. -/
theorem DyadicExceptionalNormDrop (D b t : ℤ) (e : ℕ) (he : 3 ≤ e)
    (hD : 1 + D = (2 : ℤ) ^ e)
    (hn : 0 < NormForm 0 D (b + (2 : ℤ) ^ (e - 1) * t) b) :
    NormForm 0 D (2 * b + t) (-t) <
      NormForm 0 D (b + (2 : ℤ) ^ (e - 1) * t) b := by
  have hidentity := DyadicExceptionalNormIdentity D b t e (by omega) hD
  have hp : (2 : ℤ) ^ e = 8 * (2 : ℤ) ^ (e - 3) := by
    calc
      _ = (2 : ℤ) ^ ((e - 3) + 3) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = _ := by rw [pow_add]; ring
  have hpos : 0 < (2 : ℤ) ^ (e - 3) := pow_pos (by norm_num) _
  have hlarge : 8 ≤ (2 : ℤ) ^ e := by rw [hp]; omega
  by_contra hlt
  have hle :
      NormForm 0 D (b + (2 : ℤ) ^ (e - 1) * t) b ≤ NormForm 0 D (2 * b + t) (-t) :=
    le_of_not_gt hlt
  have hnew : 0 < NormForm 0 D (2 * b + t) (-t) := lt_of_lt_of_le hn hle
  have hproduct :
      0 < ((2 : ℤ) ^ e - 4) * NormForm 0 D (2 * b + t) (-t) :=
    mul_pos (by omega) hnew
  nlinarith

end GeneralizedCollatz.QuadraticArithmetic
