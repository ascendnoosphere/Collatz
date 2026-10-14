/-
SPDX-License-Identifier: CC-BY-4.0
Positive two-affine closures of even total division length.
-/
import TwoAffineEven
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace GeneralizedCollatz.TwoAffineClassification

/-- Ordering the exponents makes the smaller numerator no larger than the determinant. -/
theorem OrderedEvenClosure (q a b n y t : ℕ) (hq : 0 < q)
    (hn : 0 < n) (_ha : 0 < a) (_hb : 0 < b) (hab : a ≤ b)
    (hlen : a + b = t + t) (h : TwoAffine q a b n y) :
    a = t ∧ b = t ∧ q = 2 ^ t - 1 ∧ n = 1 ∧ y = 1 := by
  let A : ℤ := (2 : ℤ) ^ a
  let B : ℤ := (2 : ℤ) ^ b
  let H : ℤ := (2 : ℤ) ^ t
  let Q : ℤ := q
  let N : ℤ := n
  let Y : ℤ := y
  have hfirst : Q * N + 1 = A * Y := by
    dsimp [Q, N, A, Y]
    exact_mod_cast h.1
  have hsecond : Q * Y + 1 = B * N := by
    dsimp [Q, Y, B, N]
    exact_mod_cast h.2
  have hproduct : A * B = H ^ 2 := by
    dsimp [A, B, H]
    rw [← pow_add, hlen, pow_add, pow_two]
  have hclosure : (H ^ 2 - Q ^ 2) * N = Q + A := by
    nlinarith [congrArg (fun s : ℤ => Q * s) hfirst,
      congrArg (fun s : ℤ => A * s) hsecond]
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast hq
  have hN : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast Nat.succ_le_of_lt hn
  have hH : 0 < H := pow_pos (by norm_num) _
  have hA : 0 < A := pow_pos (by norm_num) _
  have hat : a ≤ t := by omega
  have hAH : A ≤ H := by
    dsimp [A, H]
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) hat
  have hdelta : 0 < H ^ 2 - Q ^ 2 := by
    nlinarith
  have hQH : Q < H := by nlinarith
  have hgap : 1 ≤ H - Q := by omega
  have hsum : 0 < H + Q := by omega
  have hfactor : H ^ 2 - Q ^ 2 = (H - Q) * (H + Q) := by ring
  have hlower : H + Q ≤ H ^ 2 - Q ^ 2 := by
    rw [hfactor]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hgap hsum.le
  have hupper : H ^ 2 - Q ^ 2 ≤ Q + A := by
    calc
      H ^ 2 - Q ^ 2 ≤ (H ^ 2 - Q ^ 2) * N := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hN hdelta.le
      _ = Q + A := hclosure
  have hAHsame : A = H := by omega
  have hdeltaSame : H ^ 2 - Q ^ 2 = H + Q := by omega
  have hunitGap : H - Q = 1 := by
    apply mul_right_cancel₀ (ne_of_gt hsum)
    simpa only [one_mul, ← hfactor] using hdeltaSame
  have hNsame : N = 1 := by nlinarith [hclosure]
  have hatSame : a = t := by
    apply TwoPowInjective
    have he : (2 : ℤ) ^ a = (2 : ℤ) ^ t := hAHsame
    exact_mod_cast he
  have hbtSame : b = t := by omega
  have hqNat : q + 1 = 2 ^ t := by
    have he : Q + 1 = H := by omega
    change (q : ℤ) + 1 = (2 : ℤ) ^ t at he
    exact_mod_cast he
  have hnNat : n = 1 := by
    have he : (n : ℤ) = 1 := hNsame
    exact_mod_cast he
  have hYsame : Y = 1 := by
    have hBsame : B = H := by simp [B, H, hbtSame]
    rw [hNsame, hBsame] at hsecond
    nlinarith [hfirst]
  refine ⟨hatSame, hbtSame, by omega, hnNat, ?_⟩
  have he : (y : ℤ) = 1 := hYsame
  exact_mod_cast he

/-- Every positive even-length two-affine closure has equal exponents and the unit states. -/
theorem EvenClosureClassification (q a b n y t : ℕ) (hq : 0 < q)
    (hn : 0 < n) (hy : 0 < y) (ha : 0 < a) (hb : 0 < b)
    (hlen : a + b = t + t) (h : TwoAffine q a b n y) :
    a = t ∧ b = t ∧ q = 2 ^ t - 1 ∧ n = 1 ∧ y = 1 := by
  rcases le_total a b with hab | hba
  · exact OrderedEvenClosure q a b n y t hq hn ha hb hab hlen h
  · have hswap : TwoAffine q b a y n := ⟨h.2, h.1⟩
    have hsum : b + a = t + t := by omega
    obtain ⟨hbt, hat, hqt, hyt, hnt⟩ :=
      OrderedEvenClosure q b a y n t hq hy hb ha hba hsum hswap
    exact ⟨hat, hbt, hqt, hnt, hyt⟩

/-- Unit states close for every exponent; a positive exponent gives a positive multiplier. -/
theorem UnitClosure (t : ℕ) :
    TwoAffine (2 ^ t - 1) t t 1 1 := by
  have hpow : 1 ≤ 2 ^ t := Nat.one_le_pow _ _ (by decide)
  simp only [TwoAffine, mul_one]
  omega

end GeneralizedCollatz.TwoAffineClassification
