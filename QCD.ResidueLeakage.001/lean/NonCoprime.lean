-- SPDX-License-Identifier: CC-BY-4.0
import ResidueCylinders

set_option autoImplicit false

namespace GeneralizedCollatz.ResidueLeakage

/-- An offset outside a common-divisor stratum prevents every affine image from dividing. -/
theorem CommonDivisorAffineMiss (q c D s n : ℕ)
    (hsq : s ∣ q) (hsD : s ∣ D) (hsc : ¬s ∣ c) :
    ¬D ∣ q * n + c := by
  intro h
  have hsum : s ∣ q * n + c := dvd_trans hsD h
  have hprod : s ∣ q * n := dvd_mul_of_dvd_left hsq n
  exact hsc ((Nat.dvd_add_iff_right hprod).mpr hsum)

/-- Once the first affine event occurs, the simultaneous arithmetic obstruction persists. -/
theorem CommonDivisorAffineTail (q c D s u : ℕ)
    (hsq : s ∣ q) (hsD : s ∣ D) (hsc : ¬s ∣ c) (hu : ¬D ∣ u) :
    ∀ j, ¬D ∣ Iterate (Raw q c D) j u := by
  intro j
  induction j with
  | zero => { exact hu }
  | succ j ih => {
      change ¬D ∣ Raw q c D (Iterate (Raw q c D) j u)
      rw [Raw, if_neg ih]
      exact CommonDivisorAffineMiss q c D s _ hsq hsD hsc
    }

/-- A positive seed loses only finitely many initial division factors, with exact raw recovery. -/
theorem InitialDivisionStrip (q c D n : ℕ) (hD : 2 ≤ D) (hn : 0 < n) :
    ∃ k u : ℕ, 0 < u ∧ ¬D ∣ u ∧ n = D ^ k * u ∧
      Iterate (Raw q c D) k n = u := by
  induction n using Nat.strong_induction_on with
  | h n ih => {
      by_cases hdiv : D ∣ n
      · have hDpos : 0 < D := by omega
        have hsmall : n / D < n := Nat.div_lt_self hn hD
        have hu : 0 < n / D := Nat.div_pos (Nat.le_of_dvd hn hdiv) hDpos
        obtain ⟨k, u, hupos, huD, he, hit⟩ := ih (n / D) hsmall hu
        refine ⟨k + 1, u, hupos, huD, ?_, ?_⟩
        · calc
            n = D * (n / D) := (Nat.mul_div_cancel' hdiv).symm
            _ = D * (D ^ k * u) := by rw [he]
            _ = D ^ (k + 1) * u := by rw [pow_succ]; ring
        · rw [← IterateFirst]
          simpa only [Raw, if_pos hdiv] using hit
      · exact ⟨0, n, hn, hdiv, by simp, rfl⟩
    }

/-- Non-coprime obstruction gives an exact affine tail for every positive seed. -/
theorem CommonDivisorTailClassification (q c D s n : ℕ) (hD : 2 ≤ D)
    (hsq : s ∣ q) (hsD : s ∣ D) (hsc : ¬s ∣ c) (hn : 0 < n) :
    ∃ k u : ℕ, 0 < u ∧ ¬D ∣ u ∧ n = D ^ k * u ∧
      ∀ j, Iterate (Raw q c D) (k + j) n = q ^ j * u + c * RepunitSum q j := by
  obtain ⟨k, u, hupos, huD, he, hit⟩ := InitialDivisionStrip q c D n hD hn
  refine ⟨k, u, hupos, huD, he, ?_⟩
  intro j
  rw [IterateAdd, hit]
  have htail := CommonDivisorAffineTail q c D s u hsq hsD hsc huD
  have hformula := DivisionFreeAffine q c D u 0 (fun t _ => htail t) j
  simpa only [zero_add, Iterate, AffineFormula] using hformula

/-- Under positive affine growth, the common-divisor family escapes along the full raw clock. -/
theorem CommonDivisorEscape (q c D s n : ℕ) (hq : 1 ≤ q) (hc : 1 ≤ c)
    (hD : 2 ≤ D) (hsq : s ∣ q) (hsD : s ∣ D) (hsc : ¬s ∣ c) (hn : 0 < n) :
    ∀ B, ∃ K, ∀ j, K ≤ j → B < Iterate (Raw q c D) j n := by
  obtain ⟨k, u, _, huD, _, hit⟩ := InitialDivisionStrip q c D n hD hn
  apply DivisionFreeEscape q c D n k hq hc
  intro j hj
  have he : j = k + (j - k) := (Nat.add_sub_of_le hj).symm
  rw [he, IterateAdd, hit]
  exact CommonDivisorAffineTail q c D s u hsq hsD hsc huD (j - k)

/-- The gcd criterion supplies the same explicit obstruction without a coprimeness assumption. -/
theorem GcdOffsetEscape (q c D n : ℕ) (hq : 1 ≤ q) (hc : 1 ≤ c)
    (hD : 2 ≤ D) (hmiss : ¬q.gcd D ∣ c) (hn : 0 < n) :
    ∀ B, ∃ K, ∀ j, K ≤ j → B < Iterate (Raw q c D) j n := by
  exact CommonDivisorEscape q c D (q.gcd D) n hq hc hD
    (Nat.gcd_dvd_left q D) (Nat.gcd_dvd_right q D) hmiss hn

/-- The first nonunit layer is invariant even when the common divisor divides the offset. -/
theorem SquareLayerImageMiss (p Q C n : ℕ) (hp : 0 < p)
    (hc : ¬p ∣ C) (hn : p ∣ n) : ¬p ^ 2 ∣ p * (Q * n + C) := by
  intro h
  have hmul : p * p ∣ p * (Q * n + C) := by simpa [pow_two] using h
  have hsum : p ∣ Q * n + C := (Nat.mul_dvd_mul_iff_left hp).mp hmul
  have hprod : p ∣ Q * n := dvd_mul_of_dvd_right hn Q
  exact hc ((Nat.dvd_add_iff_right hprod).mpr hsum)

/-- A layer-one state takes the affine branch and remains in that same exact layer. -/
theorem SquareLayerInvariant (p Q C n : ℕ) (hp : 0 < p) (hc : ¬p ∣ C)
    (hn : p ∣ n) (hmiss : ¬p ^ 2 ∣ n) :
    Raw (p * Q) (p * C) (p ^ 2) n = p * (Q * n + C) ∧
      p ∣ Raw (p * Q) (p * C) (p ^ 2) n ∧
      ¬p ^ 2 ∣ Raw (p * Q) (p * C) (p ^ 2) n := by
  have he : Raw (p * Q) (p * C) (p ^ 2) n = p * (Q * n + C) := by
    rw [Raw, if_neg hmiss]
    ring
  refine ⟨he, ?_, ?_⟩
  · rw [he]
    exact dvd_mul_right p _
  · rw [he]
    exact SquareLayerImageMiss p Q C n hp hc hn

/-- The invariant layer has an exact division-free future in the original raw clock. -/
theorem SquareLayerTail (p Q C n : ℕ) (hp : 0 < p) (hc : ¬p ∣ C)
    (hn : p ∣ n) (hmiss : ¬p ^ 2 ∣ n) :
    ∀ j, p ∣ Iterate (Raw (p * Q) (p * C) (p ^ 2)) j n ∧
      ¬p ^ 2 ∣ Iterate (Raw (p * Q) (p * C) (p ^ 2)) j n := by
  intro j
  induction j with
  | zero => { exact ⟨hn, hmiss⟩ }
  | succ j ih => {
      exact (SquareLayerInvariant p Q C _ hp hc ih.1 ih.2).2
    }

/-- Positive affine coefficients make every layer-one state escape along the full sequence. -/
theorem SquareLayerEscape (p Q C n : ℕ) (hp : 2 ≤ p) (hQ : 1 ≤ Q) (hC : 1 ≤ C)
    (hc : ¬p ∣ C) (hn : p ∣ n) (hmiss : ¬p ^ 2 ∣ n) :
    ∀ B, ∃ K, ∀ j, K ≤ j →
      B < Iterate (Raw (p * Q) (p * C) (p ^ 2)) j n := by
  apply DivisionFreeEscape (p * Q) (p * C) (p ^ 2) n 0
    (by nlinarith) (by nlinarith)
  intro j _
  exact (SquareLayerTail p Q C n (by omega) hc hn hmiss j).2

/-- Prescribed whole-divisor powers recover all forced division ticks exactly. -/
theorem DivisionPowerRecover (q c D k u : ℕ) (hD : 0 < D) :
    Iterate (Raw q c D) k (D ^ k * u) = u := by
  induction k with
  | zero => { simp [Iterate] }
  | succ k ih => {
      have he : D ^ (k + 1) * u = D * (D ^ k * u) := by rw [pow_succ]; ring
      rw [← IterateFirst, he, Raw, if_pos (dvd_mul_right D _)]
      rw [Nat.mul_div_cancel_left _ hD]
      exact ih
    }

/-- A prescribed odd power factor recovers its quotient at an exact raw time. -/
theorem SquareOddReturn (p Q C n k u : ℕ) (hp : 0 < p) (hn : ¬p ∣ n)
    (he : Q * n + C = p ^ (2 * k + 1) * u) :
    Iterate (Raw (p * Q) (p * C) (p ^ 2)) (k + 2) n = u := by
  have hmiss : ¬p ^ 2 ∣ n := by
    intro h
    exact hn (dvd_trans (by exact ⟨p, by simp [pow_two]⟩) h)
  have ha : Raw (p * Q) (p * C) (p ^ 2) n = (p ^ 2) ^ (k + 1) * u := by
    rw [Raw, if_neg hmiss]
    calc
      p * Q * n + p * C = p * (Q * n + C) := by ring
      _ = p * (p ^ (2 * k + 1) * u) := by rw [he]
      _ = p ^ ((2 * k + 1) + 1) * u := by simp only [pow_succ]; ring
      _ = (p ^ 2) ^ (k + 1) * u := by rw [← pow_mul]; congr 2
  have htime : k + 2 = (k + 1) + 1 := by omega
  rw [htime, ← IterateFirst, ha]
  exact DivisionPowerRecover _ _ _ _ _ (pow_pos hp 2)

/-- Requiring a unit endpoint gives the exact unit-return block used by the density argument. -/
theorem SquareUnitReturn (p Q C n k u : ℕ) (hp : 0 < p) (hn : ¬p ∣ n)
    (hu : ¬p ∣ u) (he : Q * n + C = p ^ (2 * k + 1) * u) :
    Iterate (Raw (p * Q) (p * C) (p ^ 2)) (k + 2) n = u ∧
      ¬p ∣ Iterate (Raw (p * Q) (p * C) (p ^ 2)) (k + 2) n := by
  have hit := SquareOddReturn p Q C n k u hp hn he
  exact ⟨hit, by rw [hit]; exact hu⟩

end GeneralizedCollatz.ResidueLeakage
