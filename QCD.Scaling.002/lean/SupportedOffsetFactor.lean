/- SPDX-License-Identifier: CC-BY-4.0 -/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs

/-! A terminating gcd-only extraction of the multiplier-supported part of an offset. -/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Repeated gcd removal is defined at zero, but its positive-offset certificate is separate. -/
def SupportedOffsetPeel (q c : ℕ) : ℕ × ℕ :=
  if c = 0 then (1, 0)
  else if Nat.gcd c q = 1 then (1, c)
  else
    let g := Nat.gcd c q
    let next := SupportedOffsetPeel q (c / g)
    (g * next.1, next.2)
termination_by c
decreasing_by
  have cPositive : 0 < c := by omega
  have gPositive : 0 < Nat.gcd c q := Nat.gcd_pos_of_pos_left q cPositive
  have gLarge : 1 < Nat.gcd c q := by omega
  exact Nat.div_lt_self cPositive gLarge

/-- The actual executable result reconstructs the offset and has a divisor-power certificate. -/
theorem SupportedOffsetPeelCertificate (q c : ℕ) (cPositive : 0 < c) :
    let factors := SupportedOffsetPeel q c
    0 < factors.1 ∧ 0 < factors.2 ∧ factors.1 * factors.2 = c ∧
      Nat.Coprime factors.2 q ∧ ∃ k : ℕ, k ≤ c ∧ factors.1 ∣ q ^ k := by
  have cNonzero : c ≠ 0 := Nat.ne_of_gt cPositive
  by_cases unit : Nat.gcd c q = 1
  · rw [SupportedOffsetPeel, if_neg cNonzero, if_pos unit]
    exact ⟨by simp, cPositive, by simp, unit, 0, by omega, by simp⟩
  · let g := Nat.gcd c q
    have gPositive : 0 < g := Nat.gcd_pos_of_pos_left q cPositive
    have gLarge : 1 < g := by omega
    have gDivides : g ∣ c := Nat.gcd_dvd_left c q
    have gQDivides : g ∣ q := Nat.gcd_dvd_right c q
    have quotientPositive : 0 < c / g :=
      Nat.div_pos (Nat.le_of_dvd cPositive gDivides) gPositive
    have quotientLess : c / g < c := Nat.div_lt_self cPositive gLarge
    obtain ⟨sPositive, corePositive, product, coreCoprime, k, kBound, power⟩ :=
      SupportedOffsetPeelCertificate q (c / g) quotientPositive
    rw [SupportedOffsetPeel, if_neg cNonzero, if_neg unit]
    refine ⟨Nat.mul_pos gPositive sPositive, corePositive, ?_, coreCoprime,
      k + 1, ?_, ?_⟩
    · calc
        g * (SupportedOffsetPeel q (c / g)).1 * (SupportedOffsetPeel q (c / g)).2 =
            g * ((SupportedOffsetPeel q (c / g)).1 *
              (SupportedOffsetPeel q (c / g)).2) := by rw [Nat.mul_assoc]
        _ = g * (c / g) := by rw [product]
        _ = c := Nat.mul_div_cancel' gDivides
    · omega
    · have multiplied := Nat.mul_dvd_mul gQDivides power
      simpa [Nat.pow_succ, Nat.mul_comm] using multiplied
termination_by c
decreasing_by
  exact quotientLess

/-- Every prime divisor of a positive power divides its base, including the zero-base case. -/
theorem PrimeDivisorOfPower (p q k : ℕ) (prime : Nat.Prime p) (divides : p ∣ q ^ k) :
    p ∣ q := by
  induction k with
  | zero => {
      have impossible : p ∣ 1 := by simpa using divides
      exact False.elim (prime.not_dvd_one impossible)
    }
  | succ k ih => {
      rw [Nat.pow_succ] at divides
      obtain lower | direct := prime.dvd_mul.mp divides
      · exact ih lower
      · exact direct
    }

/-- The gcd-only result has exactly the required multiplier prime support. -/
theorem SupportedOffsetPeelPrimeSupport (q c : ℕ) (cPositive : 0 < c) :
    ∀ p : ℕ, Nat.Prime p → p ∣ (SupportedOffsetPeel q c).1 → p ∣ q := by
  obtain ⟨_, _, _, _, k, _, power⟩ := SupportedOffsetPeelCertificate q c cPositive
  intro p prime divides
  exact PrimeDivisorOfPower p q k prime (dvd_trans divides power)

/-- Both coefficients remain bounded by the original positive offset during recovery. -/
theorem SupportedOffsetPeelBounds (q c : ℕ) (cPositive : 0 < c) :
    (SupportedOffsetPeel q c).1 ≤ c ∧ (SupportedOffsetPeel q c).2 ≤ c := by
  obtain ⟨_, _, product, _, _, _, _⟩ := SupportedOffsetPeelCertificate q c cPositive
  have sDivides : (SupportedOffsetPeel q c).1 ∣ c := ⟨_, product.symm⟩
  have coreDivides : (SupportedOffsetPeel q c).2 ∣ c := by
    refine ⟨(SupportedOffsetPeel q c).1, ?_⟩
    simpa [Nat.mul_comm] using product.symm
  exact ⟨Nat.le_of_dvd cPositive sDivides, Nat.le_of_dvd cPositive coreDivides⟩

/-- A supported divisor of the offset lies in the extracted factor, not the coprime core. -/
theorem SupportedOffsetPeelMaximalPower (q c divisor k : ℕ) (cPositive : 0 < c)
    (divides : divisor ∣ c) (power : divisor ∣ q ^ k) :
    divisor ∣ (SupportedOffsetPeel q c).1 := by
  obtain ⟨_, _, product, coreCoprime, _, _, _⟩ :=
    SupportedOffsetPeelCertificate q c cPositive
  have divisorCoreCoprime : Nat.Coprime divisor (SupportedOffsetPeel q c).2 :=
    ((coreCoprime.pow_right k).coprime_dvd_right power).symm
  apply divisorCoreCoprime.dvd_of_dvd_mul_right
  rw [product]
  exact divides

/-- Coprimality of the full offset with the raw divisor passes to the extracted factor. -/
theorem SupportedOffsetPeelCoprime (q c D : ℕ) (cPositive : 0 < c)
    (coprime : Nat.Coprime c D) : Nat.Coprime (SupportedOffsetPeel q c).1 D := by
  obtain ⟨_, _, product, _, _, _, _⟩ := SupportedOffsetPeelCertificate q c cPositive
  exact coprime.coprime_dvd_left ⟨_, product.symm⟩

end GeneralizedCollatz
