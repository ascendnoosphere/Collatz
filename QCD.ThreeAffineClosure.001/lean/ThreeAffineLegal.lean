/-
SPDX-License-Identifier: CC-BY-4.0
Positive odd reconstruction from the three-affine divisibility criterion.
-/
import ThreeAffineClosure
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace GeneralizedCollatz.ThreeAffineLegal

/-- A cyclic rotation leaves the determinant unchanged. -/
theorem DeltaRotate (a b c q : ℕ) : Delta b c a q = Delta a b c q := by
  have he : b + c + a = a + b + c := by omega
  simp only [Delta, he]

/-- Transport of the closure numerator through one affine letter. -/
theorem Transport (a b c q : ℕ) :
    (q : ℤ) * ClosureNumerator a b q + Delta a b c q =
      (2 : ℤ) ^ a * ClosureNumerator b c q := by
  simp only [ClosureNumerator, Delta, pow_add]
  ring

/-- Every odd integer is coprime to every power of two. -/
theorem OddCoprimePower (delta : ℤ) (a : ℕ) (ho : Odd delta) :
    IsCoprime delta ((2 : ℤ) ^ a) := by
  have h : IsCoprime delta (2 : ℤ) := by
    rcases ho with ⟨k, hk⟩
    refine ⟨1, -k, ?_⟩
    rw [hk]
    ring
  exact h.pow_right

/-- Positive letters and an odd multiplier give an odd determinant. -/
theorem DeltaOdd (a b c q : ℕ) (ha : 0 < a) (ho : Odd q) :
    Odd (Delta a b c q) := by
  have hq : Odd (q : ℤ) := by exact_mod_cast ho
  have hE : Even ((2 : ℤ) ^ (a + b + c)) :=
    Even.pow_of_ne_zero even_two (by omega)
  rcases hE with ⟨s, hs⟩
  rcases hq.pow (n := 3) with ⟨r, hr⟩
  refine ⟨s - r - 1, ?_⟩
  simp only [Delta, hs, hr]
  ring

/-- The numerator of a positive-letter word is odd when the multiplier is odd. -/
theorem NumeratorOdd (a b q : ℕ) (ha : 0 < a) (ho : Odd q) :
    Odd (ClosureNumerator a b q) := by
  have hq : Odd (q : ℤ) := by exact_mod_cast ho
  have hA : Even ((2 : ℤ) ^ a) := Even.pow_of_ne_zero even_two (by omega)
  have hAB : Even ((2 : ℤ) ^ (a + b)) := Even.pow_of_ne_zero even_two (by omega)
  exact ((hq.pow (n := 2)).add_even (hA.mul_left (q : ℤ))).add_even hAB

/-- Coprime cancellation propagates integrality to the next chronological phase. -/
theorem DividesRotate (a b c q : ℕ) (ha : 0 < a) (ho : Odd q)
    (hdiv : Delta a b c q ∣ ClosureNumerator a b q) :
    Delta a b c q ∣ ClosureNumerator b c q := by
  apply (OddCoprimePower _ a (DeltaOdd a b c q ha ho)).dvd_of_dvd_mul_left
  rw [← Transport]
  exact dvd_add (dvd_mul_of_dvd_right hdiv _) (dvd_refl _)

/-- Cancellation of the nonzero determinant reconstructs an actual affine equation. -/
theorem RecoverEdge (delta q P B U x y : ℤ) (hd : delta ≠ 0)
    (hx : B = delta * x) (hy : U = delta * y) (ht : q * B + delta = P * U) :
    P * y = q * x + 1 := by
  have hm : (q * x + 1) * delta = (P * y) * delta := by
    calc
      (q * x + 1) * delta = q * (delta * x) + delta := by ring
      _ = q * B + delta := by rw [← hx]
      _ = P * U := ht
      _ = P * (delta * y) := by rw [hy]
      _ = (P * y) * delta := by ring
  exact (mul_right_cancel₀ hd hm).symm

/-- Positivity and parity of an integral phase follow from its numerator and determinant. -/
theorem RecoverPhase (delta B x : ℤ) (hd : 0 < delta) (hB : 0 < B)
    (ho : Odd B) (hx : B = delta * x) : 0 < x ∧ Odd x := by
  constructor
  · nlinarith
  · rw [hx] at ho
    exact (Int.odd_mul.mp ho).2

/-- An odd positive multiplier and one divisibility test recover all three positive odd phases. -/
theorem PositiveOddRecovery (a b c q : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : 0 < q) (ho : Odd q)
    (hd : 0 < Delta a b c q) (hdiv : Delta a b c q ∣ ClosureNumerator a b q) :
    ∃ x y z : ℤ, 0 < x ∧ 0 < y ∧ 0 < z ∧ Odd x ∧ Odd y ∧ Odd z ∧
      (2 : ℤ) ^ a * y = (q : ℤ) * x + 1 ∧
      (2 : ℤ) ^ b * z = (q : ℤ) * y + 1 ∧
      (2 : ℤ) ^ c * x = (q : ℤ) * z + 1 := by
  have hydiv := DividesRotate a b c q ha ho hdiv
  have hzdiv := DividesRotate b c a q hb ho (by simpa only [DeltaRotate] using hydiv)
  rw [DeltaRotate] at hzdiv
  obtain ⟨x, hx⟩ := hdiv
  obtain ⟨y, hy⟩ := hydiv
  obtain ⟨z, hz⟩ := hzdiv
  have hBx : 0 < ClosureNumerator a b q := by
    have h := NumeratorAtLeastSeven a b q ha hb hq
    change (7 : ℤ) ≤ ClosureNumerator a b q at h
    omega
  have hBy : 0 < ClosureNumerator b c q := by
    have h := NumeratorAtLeastSeven b c q hb hc hq
    change (7 : ℤ) ≤ ClosureNumerator b c q at h
    omega
  have hBz : 0 < ClosureNumerator c a q := by
    have h := NumeratorAtLeastSeven c a q hc ha hq
    change (7 : ℤ) ≤ ClosureNumerator c a q at h
    omega
  obtain ⟨hxpos, hxodd⟩ := RecoverPhase _ _ x hd hBx (NumeratorOdd a b q ha ho) hx
  obtain ⟨hypos, hyodd⟩ := RecoverPhase _ _ y hd hBy (NumeratorOdd b c q hb ho) hy
  obtain ⟨hzpos, hzodd⟩ := RecoverPhase _ _ z hd hBz (NumeratorOdd c a q hc ho) hz
  refine ⟨x, y, z, hxpos, hypos, hzpos, hxodd, hyodd, hzodd, ?_, ?_, ?_⟩
  · exact RecoverEdge _ _ _ _ _ _ _ (ne_of_gt hd) hx hy (Transport a b c q)
  · apply RecoverEdge _ _ _ _ _ _ _ (ne_of_gt hd) hy hz
    simpa only [DeltaRotate] using Transport b c a q
  · apply RecoverEdge _ _ _ _ _ _ _ (ne_of_gt hd) hz hx
    simpa only [DeltaRotate, DeltaRotate b c a q] using Transport c a b q

/-- Any affine edge ending in a positive power-of-two multiple has an odd multiplier. -/
theorem MultiplierOdd (a q : ℕ) (x y : ℤ) (ha : 0 < a)
    (he : (2 : ℤ) ^ a * y = (q : ℤ) * x + 1) : Odd q := by
  apply Nat.not_even_iff_odd.mp
  intro hq
  have hqi : Even (q : ℤ) := by exact_mod_cast hq
  have hodd : Odd ((q : ℤ) * x + 1) :=
    (hqi.mul_right x).add_odd (by decide : Odd (1 : ℤ))
  have heven : Even ((q : ℤ) * x + 1) := by
    rw [← he]
    exact (Even.pow_of_ne_zero even_two (by omega : a ≠ 0)).mul_right y
  exact (Int.not_even_iff_odd.mpr hodd) heven

/-- For positive letters, positivity and one divisibility test characterize legal odd closure. -/
theorem PositiveOddCriterion (a b c q : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : 0 < q) :
    (∃ x y z : ℤ, 0 < x ∧ 0 < y ∧ 0 < z ∧ Odd x ∧ Odd y ∧ Odd z ∧
      (2 : ℤ) ^ a * y = (q : ℤ) * x + 1 ∧
      (2 : ℤ) ^ b * z = (q : ℤ) * y + 1 ∧
      (2 : ℤ) ^ c * x = (q : ℤ) * z + 1) ↔
    Odd q ∧ 0 < Delta a b c q ∧ Delta a b c q ∣ ClosureNumerator a b q := by
  constructor
  · rintro ⟨x, y, z, hx, _hy, _hz, _hox, _hoy, _hoz, he, hf, hg⟩
    have ht := ThreeAffineClosure a b c q x y z ha hb hc hq he hf hg
    refine ⟨MultiplierOdd a q x y ha he, ?_, ht.2.1⟩
    nlinarith [ht.1, ht.2.2.2.2.2.1]
  · rintro ⟨ho, hd, hv⟩
    exact PositiveOddRecovery a b c q ha hb hc hq ho hd hv

end GeneralizedCollatz.ThreeAffineLegal
