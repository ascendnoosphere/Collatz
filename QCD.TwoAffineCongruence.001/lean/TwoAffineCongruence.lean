-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

/-
Elementary arithmetic of the two-affine denominator `2 ^ K - q ^ 2`.

Integrality of `(q + 2 ^ a) / Δ` is the congruence `2 ^ a ≡ -q` modulo `Δ`.
Oddness of `Δ` makes `Δ` coprime to `q`, so the same congruence at exponent
`K - a` is integral as well. The partner quotient is odd when `a < K`.
When `Δ > 0`, the two quotients agree only for the unit seed `K = 2a`, `q = 2 ^ a - 1`,
and value `1`. In particular they disagree whenever `K` is odd.
-/

import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The two-affine denominator `2 ^ K - q ^ 2`. -/
def TwoAffineDelta (K : ℕ) (q : ℤ) : ℤ :=
  (2 : ℤ) ^ K - q ^ 2

/-- Every natural power of two is positive. -/
theorem TwoAffineNatPowPositive (k : ℕ) : 0 < 2 ^ k := by
  induction k with
  | zero =>
    {
      decide
    }
  | succ k ih =>
    {
      rw [Nat.pow_succ, Nat.mul_two]
      exact Nat.add_pos_left ih (2 ^ k)
    }

/-- Casting a natural power of two into `ℤ` agrees with the integer power. -/
theorem TwoAffineNatCastPow (k : ℕ) : ((2 : ℕ) ^ k : ℤ) = (2 : ℤ) ^ k := by
  induction k with
  | zero =>
    {
      simp
    }
  | succ k ih =>
    {
      simp
    }

/-- An integer power of two is positive. -/
theorem TwoAffinePowPositive (k : ℕ) : (0 : ℤ) < (2 : ℤ) ^ k := by
  rw [← TwoAffineNatCastPow]
  exact (Int.ofNat_lt).mpr (TwoAffineNatPowPositive k)

/-- An odd natural divisor of a power of two equals `1`. -/
theorem OddNatDvdTwoPow (d : ℕ) (hodd : Odd d) :
    ∀ K : ℕ, d ∣ 2 ^ K → d = 1 := by
  intro K
  induction K with
  | zero =>
    {
      intro hd
      have h1 : d ∣ 1 := by
        simpa [Nat.pow_zero] using hd
      exact (Nat.dvd_one).mp h1
    }
  | succ K ih =>
    {
      intro hd
      have hnot : ¬ 2 ∣ d := Odd.not_two_dvd_nat hodd
      have hcop : Nat.Coprime d 2 :=
        (Nat.coprime_comm).mp
          ((Nat.prime_two.coprime_iff_not_dvd).mpr hnot)
      have hdMul : d ∣ 2 ^ K * 2 := by
        simpa [Nat.pow_succ] using hd
      exact ih ((Nat.Coprime.dvd_mul_right hcop).mp hdMul)
    }

/-- `Δ` divides `q + 2 ^ a` if and only if `2 ^ a ≡ -q` modulo `Δ`. -/
theorem TwoAffineCongruenceIff (K : ℕ) (q : ℤ) (a : ℕ) :
    TwoAffineDelta K q ∣ q + (2 : ℤ) ^ a ↔
      (2 : ℤ) ^ a ≡ -q [ZMOD TwoAffineDelta K q] := by
  rw [Int.modEq_iff_dvd]
  constructor
  · intro h
    have hneg : -q - (2 : ℤ) ^ a = -(q + (2 : ℤ) ^ a) := by
      ring
    rw [hneg]
    exact Int.dvd_neg.mpr h
  · intro h
    have hneg : -q - (2 : ℤ) ^ a = -(q + (2 : ℤ) ^ a) := by
      ring
    rw [hneg] at h
    exact Int.dvd_neg.mp h

/-- An odd denominator `2 ^ K - q ^ 2` is coprime to `q`. -/
theorem TwoAffineCoprime (K : ℕ) (q : ℤ)
    (hodd : Odd (TwoAffineDelta K q)) :
    Int.gcd (TwoAffineDelta K q) q = 1 := by
  set Δ := TwoAffineDelta K q
  set g := Int.gcd Δ q
  have hgΔ : (g : ℤ) ∣ Δ := Int.gcd_dvd_left Δ q
  have hgq : (g : ℤ) ∣ q := Int.gcd_dvd_right Δ q
  have hgq2 : (g : ℤ) ∣ q ^ 2 := by
    have hmul : (g : ℤ) ∣ q * q := dvd_mul_of_dvd_left hgq q
    simpa [pow_two] using hmul
  have hsum : Δ + q ^ 2 = (2 : ℤ) ^ K := by
    unfold Δ TwoAffineDelta
    ring
  have hgpow : (g : ℤ) ∣ (2 : ℤ) ^ K := by
    rw [← hsum]
    exact dvd_add hgΔ hgq2
  have hgnat : g ∣ 2 ^ K := by
    have hcoe : (g : ℤ) ∣ ((2 : ℕ) ^ K : ℤ) := by
      rw [TwoAffineNatCastPow]
      exact hgpow
    exact (Int.natCast_dvd_natCast).mp hcoe
  have hgodd : Odd g := by
    have hnot : ¬ Even g := by
      intro he
      have h2 : (2 : ℤ) ∣ Δ := by
        exact dvd_trans (Int.natCast_dvd_natCast.mpr (even_iff_two_dvd.mp he)) hgΔ
      exact (Int.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    exact (Nat.not_even_iff_odd).mp hnot
  exact OddNatDvdTwoPow g hgodd K hgnat

/-- Oddness of `Δ` carries divisibility from exponent `a` to exponent `K - a`. -/
theorem TwoAffinePartnerDivides (K a : ℕ) (q : ℤ)
    (hodd : Odd (TwoAffineDelta K q)) (ha : a ≤ K)
    (hdiv : TwoAffineDelta K q ∣ q + (2 : ℤ) ^ a) :
    TwoAffineDelta K q ∣ q + (2 : ℤ) ^ (K - a) := by
  set Δ := TwoAffineDelta K q
  have hsplit : (2 : ℤ) ^ K = (2 : ℤ) ^ (K - a) * (2 : ℤ) ^ a := by
    have hexp : (K - a) + a = K := by
      omega
    have hpow := pow_add (2 : ℤ) (K - a) a
    rw [hexp] at hpow
    exact hpow
  have hprod : Δ ∣ q * (q + (2 : ℤ) ^ (K - a)) := by
    have hq2 : q ^ 2 = (2 : ℤ) ^ K - Δ := by
      unfold Δ TwoAffineDelta
      ring
    have hrewrite :
        q * (q + (2 : ℤ) ^ (K - a)) =
          (2 : ℤ) ^ (K - a) * (q + (2 : ℤ) ^ a) - Δ := by
      calc
        q * (q + (2 : ℤ) ^ (K - a))
          = q ^ 2 + (2 : ℤ) ^ (K - a) * q := by
          ring
        _ = ((2 : ℤ) ^ K - Δ) + (2 : ℤ) ^ (K - a) * q := by
          rw [hq2]
        _ = (2 : ℤ) ^ (K - a) * (2 : ℤ) ^ a + (2 : ℤ) ^ (K - a) * q - Δ := by
          rw [hsplit]
          ring
        _ = (2 : ℤ) ^ (K - a) * (q + (2 : ℤ) ^ a) - Δ := by
          ring
    rw [hrewrite]
    exact dvd_sub (dvd_mul_of_dvd_right hdiv _) (dvd_refl Δ)
  exact Int.dvd_of_dvd_mul_right_of_gcd_one hprod (TwoAffineCoprime K q hodd)

/-- The partner quotient is odd when the remaining exponent is positive. -/
theorem TwoAffinePartnerOdd (K a : ℕ) (q y : ℤ)
    (hodd : Odd (TwoAffineDelta K q)) (ha : a < K)
    (hy : q + (2 : ℤ) ^ (K - a) = y * TwoAffineDelta K q) :
    Odd y := by
  have hK : K ≠ 0 := by
    omega
  have hq : Odd q := by
    have h2K : Even ((2 : ℤ) ^ K) :=
      Even.pow_of_ne_zero even_two hK
    have hnot : ¬ Even q := by
      intro hqE
      have hq2 : Even (q ^ 2) :=
        Even.pow_of_ne_zero hqE (by decide : (2 : ℕ) ≠ 0)
      have hΔE : Even (TwoAffineDelta K q) := by
        rcases h2K with ⟨r, hr⟩
        rcases hq2 with ⟨s, hs⟩
        refine ⟨r - s, ?_⟩
        unfold TwoAffineDelta
        rw [hr, hs]
        ring
      exact (Int.not_even_iff_odd.mpr hodd) hΔE
    exact (Int.not_even_iff_odd).mp hnot
  have hExp : K - a ≠ 0 := by
    omega
  have hEvenPow : Even ((2 : ℤ) ^ (K - a)) :=
    Even.pow_of_ne_zero even_two hExp
  have hNum : Odd (q + (2 : ℤ) ^ (K - a)) :=
    hq.add_even hEvenPow
  have hNy : Odd (y * TwoAffineDelta K q) := by
    rw [← hy]
    exact hNum
  exact (Int.odd_mul.mp hNy).1

/-- Both affine numerators factor as a power of two times the other quotient. -/
theorem TwoAffineProduct (K a : ℕ) (q n y : ℤ)
    (hpos : 0 < TwoAffineDelta K q) (ha : a ≤ K)
    (hn : q + (2 : ℤ) ^ a = n * TwoAffineDelta K q)
    (hy : q + (2 : ℤ) ^ (K - a) = y * TwoAffineDelta K q) :
    q * n + 1 = (2 : ℤ) ^ a * y ∧
      q * y + 1 = (2 : ℤ) ^ (K - a) * n := by
  set Δ := TwoAffineDelta K q
  have hΔne : Δ ≠ 0 := ne_of_gt hpos
  have hsplit : (2 : ℤ) ^ K = (2 : ℤ) ^ a * (2 : ℤ) ^ (K - a) := by
    have hexp : a + (K - a) = K := by
      omega
    have hpow := pow_add (2 : ℤ) a (K - a)
    rw [hexp] at hpow
    exact hpow
  have hsplit' : (2 : ℤ) ^ K = (2 : ℤ) ^ (K - a) * (2 : ℤ) ^ a := by
    have hexp : (K - a) + a = K := by
      omega
    have hpow := pow_add (2 : ℤ) (K - a) a
    rw [hexp] at hpow
    exact hpow
  have hmulN : (q * n + 1) * Δ = ((2 : ℤ) ^ a * y) * Δ := by
    calc
      (q * n + 1) * Δ = q * (n * Δ) + Δ := by
        ring
      _ = q * (q + (2 : ℤ) ^ a) + Δ := by
        rw [hn]
      _ = q * (q + (2 : ℤ) ^ a) + ((2 : ℤ) ^ K - q ^ 2) := by
        rfl
      _ = (2 : ℤ) ^ a * q + (2 : ℤ) ^ K := by
        ring
      _ = (2 : ℤ) ^ a * q + (2 : ℤ) ^ a * (2 : ℤ) ^ (K - a) := by
        rw [hsplit]
      _ = (2 : ℤ) ^ a * (q + (2 : ℤ) ^ (K - a)) := by
        ring
      _ = (2 : ℤ) ^ a * (y * Δ) := by
        rw [hy]
      _ = ((2 : ℤ) ^ a * y) * Δ := by
        ring
  have hdiffN : ((q * n + 1) - ((2 : ℤ) ^ a * y)) * Δ = 0 := by
    have hsub :
        (q * n + 1) * Δ - ((2 : ℤ) ^ a * y) * Δ = 0 := by
      rw [hmulN, sub_self]
    have hfactor :
        (q * n + 1) * Δ - ((2 : ℤ) ^ a * y) * Δ =
          ((q * n + 1) - ((2 : ℤ) ^ a * y)) * Δ := by
      ring
    rw [← hfactor]
    exact hsub
  have hN : q * n + 1 = (2 : ℤ) ^ a * y := by
    have hzero :
        (q * n + 1) - ((2 : ℤ) ^ a * y) = 0 :=
      Or.resolve_right (Int.mul_eq_zero.mp hdiffN) hΔne
    exact sub_eq_zero.mp hzero
  have hmulY : (q * y + 1) * Δ = ((2 : ℤ) ^ (K - a) * n) * Δ := by
    calc
      (q * y + 1) * Δ = q * (y * Δ) + Δ := by
        ring
      _ = q * (q + (2 : ℤ) ^ (K - a)) + Δ := by
        rw [hy]
      _ = q * (q + (2 : ℤ) ^ (K - a)) + ((2 : ℤ) ^ K - q ^ 2) := by
        rfl
      _ = (2 : ℤ) ^ (K - a) * q + (2 : ℤ) ^ K := by
        ring
      _ = (2 : ℤ) ^ (K - a) * q + (2 : ℤ) ^ (K - a) * (2 : ℤ) ^ a := by
        rw [hsplit']
      _ = (2 : ℤ) ^ (K - a) * (q + (2 : ℤ) ^ a) := by
        ring
      _ = (2 : ℤ) ^ (K - a) * (n * Δ) := by
        rw [hn]
      _ = ((2 : ℤ) ^ (K - a) * n) * Δ := by
        ring
  have hdiffY :
      ((q * y + 1) - ((2 : ℤ) ^ (K - a) * n)) * Δ = 0 := by
    have hsub :
        (q * y + 1) * Δ - ((2 : ℤ) ^ (K - a) * n) * Δ = 0 := by
      rw [hmulY, sub_self]
    have hfactor :
        (q * y + 1) * Δ - ((2 : ℤ) ^ (K - a) * n) * Δ =
          ((q * y + 1) - ((2 : ℤ) ^ (K - a) * n)) * Δ := by
      ring
    rw [← hfactor]
    exact hsub
  have hY : q * y + 1 = (2 : ℤ) ^ (K - a) * n := by
    have hzero :
        (q * y + 1) - ((2 : ℤ) ^ (K - a) * n) = 0 :=
      Or.resolve_right (Int.mul_eq_zero.mp hdiffY) hΔne
    exact sub_eq_zero.mp hzero
  exact ⟨hN, hY⟩

/-- With odd cofactors, both seeds are even exactly on the open exponent range. -/
theorem TwoAffineExactPowers (K a : ℕ) (q n y : ℤ)
    (ha : a ≤ K)
    (hN : q * n + 1 = (2 : ℤ) ^ a * y)
    (hY : q * y + 1 = (2 : ℤ) ^ (K - a) * n)
    (hn : Odd n) (hy : Odd y) :
    (Even (q * n + 1) ∧ Even (q * y + 1)) ↔ (1 ≤ a ∧ a < K) := by
  constructor
  · intro hE
    refine ⟨?_, ?_⟩
    · by_contra h0
      have ha0 : a = 0 := by
        omega
      have hseed : q * n + 1 = y := by
        simpa [ha0, pow_zero] using hN
      exact (Int.not_even_iff_odd.mpr hy) (hseed ▸ hE.1)
    · by_contra hK
      have haK : a = K := by
        omega
      have hExp : K - a = 0 := by
        omega
      have hseed : q * y + 1 = n := by
        simpa [hExp, pow_zero] using hY
      exact (Int.not_even_iff_odd.mpr hn) (hseed ▸ hE.2)
  · intro hrange
    have ha1 : a ≠ 0 := by
      omega
    have haK : K - a ≠ 0 := by
      omega
    have hEvenA : Even ((2 : ℤ) ^ a) :=
      Even.pow_of_ne_zero even_two ha1
    have hEvenB : Even ((2 : ℤ) ^ (K - a)) :=
      Even.pow_of_ne_zero even_two haK
    refine ⟨?_, ?_⟩
    · rw [hN]
      rcases hEvenA with ⟨r, hr⟩
      refine ⟨r * y, ?_⟩
      rw [hr]
      ring
    · rw [hY]
      rcases hEvenB with ⟨r, hr⟩
      refine ⟨r * n, ?_⟩
      rw [hr]
      ring

/-- Equal quotients occur only for the unit seed of even length. -/
theorem TwoAffineEqualSeed (K a : ℕ) (q n y : ℤ)
    (hpos : 0 < TwoAffineDelta K q) (ha : a ≤ K)
    (hn : q + (2 : ℤ) ^ a = n * TwoAffineDelta K q)
    (hy : q + (2 : ℤ) ^ (K - a) = y * TwoAffineDelta K q)
    (heq : n = y) :
    K = 2 * a ∧ q = (2 : ℤ) ^ a - 1 ∧ n = 1 ∧ y = 1 := by
  set Δ := TwoAffineDelta K q
  have hΔne : Δ ≠ 0 := ne_of_gt hpos
  have hpow : (2 : ℤ) ^ a = (2 : ℤ) ^ (K - a) := by
    have hsum : q + (2 : ℤ) ^ a = q + (2 : ℤ) ^ (K - a) := by
      rw [hn, hy, heq]
    exact add_left_cancel hsum
  have haeq : a = K - a := by
    have hnat : (2 : ℕ) ^ a = (2 : ℕ) ^ (K - a) := by
      apply Int.natCast_inj.mp
      calc
        ((2 : ℕ) ^ a : ℤ) = (2 : ℤ) ^ a := by
          rw [TwoAffineNatCastPow]
        _ = (2 : ℤ) ^ (K - a) := hpow
        _ = ((2 : ℕ) ^ (K - a) : ℤ) := by
          rw [TwoAffineNatCastPow]
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hnat
  have hsum : K = a + a := by
    calc
      K = a + (K - a) := (Nat.add_sub_of_le ha).symm
      _ = a + a := by
        rw [haeq.symm]
  have hK : K = 2 * a := by
    rw [two_mul]
    exact hsum
  let d : ℤ := (2 : ℤ) ^ a - q
  let s : ℤ := (2 : ℤ) ^ a + q
  have hfac : d * s = Δ := by
    calc
      d * s = ((2 : ℤ) ^ a - q) * ((2 : ℤ) ^ a + q) := by
        rfl
      _ = (2 : ℤ) ^ a * (2 : ℤ) ^ a - q ^ 2 := by
        ring
      _ = (2 : ℤ) ^ (a + a) - q ^ 2 := by
        rw [← pow_add]
      _ = (2 : ℤ) ^ K - q ^ 2 := by
        rw [hsum]
      _ = Δ := by
        rfl
  have hs : s = n * Δ := by
    rw [← hn]
    change (2 : ℤ) ^ a + q = q + (2 : ℤ) ^ a
    ring
  have hs0 : s ≠ 0 := by
    intro hs0
    have hΔ0 : Δ = 0 := by
      rw [← hfac, hs0, mul_zero]
    exact hΔne hΔ0
  have hdn : d * n = 1 := by
    have hs1 : s = (d * n) * s := by
      calc
        s = n * Δ := hs
        _ = n * (d * s) := by
          rw [← hfac]
        _ = (d * n) * s := by
          ring
    have hcancel : s * (d * n - 1) = 0 := by
      calc
        s * (d * n - 1) = (d * n) * s - s := by
          ring
        _ = s - s := by
          rw [← hs1]
        _ = 0 := by
          ring
    have hzero : d * n - 1 = 0 :=
      Or.resolve_left (Int.mul_eq_zero.mp hcancel) hs0
    exact sub_eq_zero.mp hzero
  have habs : d.natAbs * n.natAbs = 1 := by
    have h := congrArg Int.natAbs hdn
    rwa [Int.natAbs_mul, Int.natAbs_one] at h
  have hdAbs : d.natAbs = 1 :=
    (Nat.dvd_one).mp ⟨n.natAbs, habs.symm⟩
  cases (Int.natAbs_eq_iff).mp hdAbs with
  | inl hdPos =>
    {
      have hd1 : d = 1 := hdPos
      have hq : q = (2 : ℤ) ^ a - 1 := by
        have hdEq : (2 : ℤ) ^ a - q = 1 := by
          dsimp [d] at hd1
          exact hd1
        linarith
      have hn1 : n = 1 := by
        have hmul : (1 : ℤ) * n = 1 := by
          simpa [hd1] using hdn
        simpa using hmul
      exact ⟨hK, hq, hn1, heq.symm.trans hn1⟩
    }
  | inr hdNeg =>
    {
      have hd1 : d = -((1 : ℕ) : ℤ) := hdNeg
      have hqNeg : q = (2 : ℤ) ^ a + 1 := by
        have hdEq : (2 : ℤ) ^ a - q = -1 := by
          dsimp [d] at hd1
          simpa using hd1
        linarith
      have hspos : (0 : ℤ) < s := by
        have hpow : (0 : ℤ) < (2 : ℤ) ^ a := TwoAffinePowPositive a
        dsimp [s]
        linarith [hqNeg, hpow]
      have hnegΔ : Δ = -s := by
        have hdmul : d * s = -s := by
          rw [hd1]
          ring
        rw [← hfac, hdmul]
      have hΔlt : Δ < 0 := by
        rw [hnegΔ]
        linarith
      exact (lt_asymm hpos hΔlt).elim
    }

/-- Odd length forbids equal two-affine quotients. -/
theorem TwoAffineOddKUnequal (K a : ℕ) (q n y : ℤ)
    (hpos : 0 < TwoAffineDelta K q) (ha : a ≤ K)
    (hn : q + (2 : ℤ) ^ a = n * TwoAffineDelta K q)
    (hy : q + (2 : ℤ) ^ (K - a) = y * TwoAffineDelta K q)
    (hK : Odd K) (heq : n = y) : False := by
  have hseed := TwoAffineEqualSeed K a q n y hpos ha hn hy heq
  have heven : Even K := by
    rw [hseed.1]
    exact even_two_mul a
  exact (Nat.not_even_iff_odd.mpr hK) heven

/-- A positive odd denominator and a positive remaining exponent give an odd partner. -/
theorem TwoAffineLane (K a : ℕ) (q : ℤ)
    (hpos : 0 < TwoAffineDelta K q) (hodd : Odd (TwoAffineDelta K q))
    (ha : a < K)
    (hcong : (2 : ℤ) ^ a ≡ -q [ZMOD TwoAffineDelta K q]) :
    ∃ n y : ℤ,
      q + (2 : ℤ) ^ a = n * TwoAffineDelta K q ∧
        q + (2 : ℤ) ^ (K - a) = y * TwoAffineDelta K q ∧
          Odd y ∧ (Odd K → n ≠ y) := by
  set Δ := TwoAffineDelta K q
  have haLe : a ≤ K := Nat.le_of_lt ha
  have hdivN : Δ ∣ q + (2 : ℤ) ^ a :=
    (TwoAffineCongruenceIff K q a).mpr hcong
  have hdivY : Δ ∣ q + (2 : ℤ) ^ (K - a) :=
    TwoAffinePartnerDivides K a q hodd haLe hdivN
  let n : ℤ := (q + (2 : ℤ) ^ a) / Δ
  let y : ℤ := (q + (2 : ℤ) ^ (K - a)) / Δ
  have hnEq : q + (2 : ℤ) ^ a = n * Δ := by
    rw [show n = (q + (2 : ℤ) ^ a) / Δ from rfl]
    exact (Int.ediv_mul_cancel hdivN).symm
  have hyEq : q + (2 : ℤ) ^ (K - a) = y * Δ := by
    rw [show y = (q + (2 : ℤ) ^ (K - a)) / Δ from rfl]
    exact (Int.ediv_mul_cancel hdivY).symm
  have hyOdd : Odd y := TwoAffinePartnerOdd K a q y hodd ha hyEq
  have hneq : Odd K → n ≠ y := by
    intro hK heq
    exact TwoAffineOddKUnequal K a q n y hpos haLe hnEq hyEq hK heq
  exact ⟨n, y, hnEq, hyEq, hyOdd, hneq⟩

end GeneralizedCollatz
