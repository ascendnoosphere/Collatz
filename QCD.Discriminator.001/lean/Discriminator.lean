/-
Copyright (c) 2026 ascendnoosphere
SPDX-License-Identifier: CC-BY-4.0

Separation of one neutral family.

For integers `q ≥ 2`, `k ≥ 1` and `t ≥ 1`, set `D = q ^ k` and `c = t * D`.
On a positive seed not divisible by `q`, divisibility by `gcd(q, t)` splits the raw
orbit. If the gcd misses the seed, every block is the neutral translation by
`t * (1 + q + … + q ^ (k - 1))` and the orbit is unbounded. If the gcd hits the
seed, the first later multiple of `q` has a one-division return `J` with
`J * q ≤ n + A`. That return lies strictly below `n` once `n` exceeds the
floor of `A / (q - 1)`, and otherwise does not exceed the floor.

The argument does not classify seeds divisible by `q`, does not identify
periods, and does not apply to a map outside this family.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false

namespace GeneralizedCollatz.Discriminator

/-- Partial geometric sum `1 + q + … + q ^ (j - 1)`, with the empty sum `0`. -/
def Geom (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => q * Geom q j + 1

/-- The empty sum supplies the time-zero term in the affine formulas. -/
theorem GeomZero (q : ℕ) : Geom q 0 = 0 := by
  rfl

/-- One affine increment appends the constant term. -/
theorem GeomStep (q j : ℕ) : Geom q (j + 1) = q * Geom q j + 1 := by
  rfl

/-- The first nonempty sum is `1`. -/
theorem GeomOne (q : ℕ) : Geom q 1 = 1 := by
  simp [Geom]

/-- Appending the next power agrees with the closed recurrence. -/
theorem GeomSuccPow (q j : ℕ) : Geom q (j + 1) = Geom q j + q ^ j := by
  induction j with
  | zero => {
      simp [Geom]
    }
  | succ j ih => {
      calc
        Geom q (j + 2) = q * Geom q (j + 1) + 1 := by rfl
        _ = q * (Geom q j + q ^ j) + 1 := by rw [ih]
        _ = q * Geom q j + q * q ^ j + 1 := by rw [Nat.mul_add]
        _ = q * Geom q j + q ^ (j + 1) + 1 := by rw [← Nat.pow_succ']
        _ = q * Geom q j + 1 + q ^ (j + 1) := by omega
        _ = Geom q (j + 1) + q ^ (j + 1) := by rfl
    }

/-- Extending the upper index does not decrease the sum. -/
theorem GeomMono (q a b : ℕ) (h : a ≤ b) : Geom q a ≤ Geom q b := by
  induction h with
  | refl => {
      exact le_rfl
    }
  | step _ ih => {
      exact le_trans ih (by
        rw [GeomSuccPow]
        exact Nat.le_add_right _ _)
    }

/-- Every positive length has sum at least `1`. -/
theorem GeomAtLeastOne (q k : ℕ) (hk : 1 ≤ k) : 1 ≤ Geom q k := by
  have hmono : Geom q 1 ≤ Geom q k := GeomMono q 1 k hk
  simpa [GeomOne] using hmono

/-- Raw step: divide by `D` on the nose, otherwise apply `n ↦ q * n + c`. -/
def RawStep (q c D n : ℕ) : ℕ :=
  if D ∣ n then n / D else q * n + c

/-- Iteration of the raw step, with time increasing on the outside. -/
def RawIterate (q c D j n : ℕ) : ℕ :=
  match j with
  | 0 => n
  | j + 1 => RawStep q c D (RawIterate q c D j n)

/-- The successor time executes exactly one raw step. -/
theorem RawIterateSucc (q c D j n : ℕ) :
    RawIterate q c D (j + 1) n = RawStep q c D (RawIterate q c D j n) := by
  rfl

/-- A block of iterations splits at an intermediate time. -/
theorem RawIterateAdd (q c D j i n : ℕ) :
    RawIterate q c D (j + i) n = RawIterate q c D i (RawIterate q c D j n) := by
  induction i with
  | zero => {
      rw [Nat.add_zero]
      rfl
    }
  | succ i ih => {
      rw [Nat.add_succ, RawIterateSucc, ih, RawIterateSucc]
    }

/-- Largest `j ≤ k` such that `q ^ j` divides `n`. -/
def ClipVal (q k n : ℕ) : ℕ :=
  Nat.findGreatest (fun j => q ^ j ∣ n) k

/-- The clipped valuation still divides the state. -/
theorem ClipValDvd (q k n : ℕ) : q ^ ClipVal q k n ∣ n := by
  simpa [ClipVal] using
    (Nat.findGreatest_spec (P := fun j => q ^ j ∣ n) (m := 0) (n := k)
      (Nat.zero_le k) (by simp))

/-- No admissible exponent exceeds the clip. -/
theorem ClipValLe (q k n : ℕ) : ClipVal q k n ≤ k := by
  simpa [ClipVal] using
    (Nat.findGreatest_le (P := fun j => q ^ j ∣ n) k)

/-- Every admissible dividing exponent is at most the clip. -/
theorem ClipValMax (q k n j : ℕ) (hj : j ≤ k) (hd : q ^ j ∣ n) :
    j ≤ ClipVal q k n := by
  simpa [ClipVal] using
    (Nat.le_findGreatest (P := fun i => q ^ i ∣ n) hj hd)

/-- The next exponent past a non-maximal clip does not divide. -/
theorem ClipValSuccNot (q k n : ℕ) (h : ClipVal q k n < k) :
    ¬ q ^ (ClipVal q k n + 1) ∣ n := by
  have hle : ClipVal q k n + 1 ≤ k := Nat.succ_le_of_lt h
  have hiff :=
    (Nat.findGreatest_eq_iff (P := fun j => q ^ j ∣ n) (k := k)
      (m := ClipVal q k n)).mp (by rfl)
  exact hiff.2.2 (Nat.lt_succ_self _) hle

/-- A clip equal to the cap means the cap itself divides. -/
theorem ClipValFull (q k n : ℕ) (hk : 1 ≤ k) (h : ClipVal q k n = k) :
    q ^ k ∣ n := by
  have hfold : Nat.findGreatest (fun j => q ^ j ∣ n) k = k := by
    simpa [ClipVal] using h
  have hiff :=
    (Nat.findGreatest_eq_iff (P := fun j => q ^ j ∣ n) (k := k) (m := k)).mp hfold
  exact hiff.2.1 (by omega)

/-- Divisor of the neutral family. -/
def FamilyDivisor (q k : ℕ) : ℕ :=
  q ^ k

/-- Offset of the neutral family, a multiple of the divisor. -/
def FamilyOffset (q k t : ℕ) : ℕ :=
  t * q ^ k

/-- Neutral translation length `t * (1 + q + … + q ^ (k - 1))`. -/
def FamilyShift (q k t : ℕ) : ℕ :=
  t * Geom q k

/-- Numerator `A = (q / gcd(q, t)) * b - t` of the return threshold. -/
def FamilyExcess (q k t : ℕ) : ℕ :=
  (q / Nat.gcd q t) * FamilyShift q k t - t

/-- One-division return after clipping the incoming power of `q`. -/
def FamilyReturn (q k t m : ℕ) : ℕ :=
  m / q ^ ClipVal q k m + t * Geom q (k - ClipVal q k m)

/-- The shift splits off one multiple of `q` and leaves the summand `t`. -/
theorem TranslationSplit (q k t : ℕ) (hk : 1 ≤ k) :
    t * Geom q k = t + q * (t * Geom q (k - 1)) := by
  have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel hk
  calc
    t * Geom q k = t * Geom q (k - 1 + 1) := by rw [hsucc]
    _ = t * (q * Geom q (k - 1) + 1) := by rfl
    _ = t * (q * Geom q (k - 1)) + t := by rw [Nat.mul_add, Nat.mul_one]
    _ = q * (t * Geom q (k - 1)) + t := by rw [Nat.mul_left_comm]
    _ = t + q * (t * Geom q (k - 1)) := by rw [Nat.add_comm]

/-- Cancelling `t` leaves the multiple of `q` in the shift. -/
theorem TranslationExcess (q k t : ℕ) (hk : 1 ≤ k) :
    t * Geom q k - t = q * (t * Geom q (k - 1)) := by
  rw [TranslationSplit q k t hk]
  exact Nat.add_sub_cancel_left t (q * (t * Geom q (k - 1)))

/-- Adding neutral copies does not change divisibility by `q`. -/
theorem SumDivisibleIff (q k t n s : ℕ) (hk : 1 ≤ k) :
    q ∣ n + s * (t * Geom q k) ↔ q ∣ n + s * t := by
  have hexcess : t * Geom q k = t + q * (t * Geom q (k - 1)) :=
    TranslationSplit q k t hk
  have hsum :
      n + s * (t * Geom q k) =
        n + s * t + q * (s * (t * Geom q (k - 1))) := by
    calc
      n + s * (t * Geom q k)
          = n + s * (t + q * (t * Geom q (k - 1))) := by rw [hexcess]
      _ = n + (s * t + s * (q * (t * Geom q (k - 1)))) := by rw [Nat.mul_add]
      _ = n + s * t + s * (q * (t * Geom q (k - 1))) := by rw [Nat.add_assoc]
      _ = n + s * t + q * (s * (t * Geom q (k - 1))) := by rw [Nat.mul_left_comm]
  rw [hsum]
  have hd : q ∣ q * (s * (t * Geom q (k - 1))) := Nat.dvd_mul_right q _
  exact (Nat.dvd_add_iff_left hd).symm

/-- A hit of `q` forces the gcd to divide the seed. -/
theorem GcdDividesSeed (q t n s : ℕ) (h : q ∣ n + s * t) :
    Nat.gcd q t ∣ n := by
  have hgq : Nat.gcd q t ∣ q := Nat.gcd_dvd_left q t
  have hgt : Nat.gcd q t ∣ t := Nat.gcd_dvd_right q t
  have hgst : Nat.gcd q t ∣ s * t := Nat.dvd_mul_left_of_dvd hgt s
  have hsum : Nat.gcd q t ∣ s * t + n := by
    rw [Nat.add_comm]
    exact Nat.dvd_trans hgq h
  exact (Nat.dvd_add_iff_right hgst).mpr hsum

/-- Missing the gcd blocks every later multiple of `q` on the translation. -/
theorem AnchorFree (q k t n s : ℕ) (hk : 1 ≤ k)
    (hng : ¬ Nat.gcd q t ∣ n) : ¬ q ∣ n + s * (t * Geom q k) := by
  intro hd
  have ht : q ∣ n + s * t := (SumDivisibleIff q k t n s hk).mp hd
  exact hng (GcdDividesSeed q t n s ht)

/-- A high power of `q` dividing a shifted copy forces a lower power to divide. -/
theorem HighPowDividesBase (q i k m : ℕ) (hq : 0 < q) (hik : i ≤ k)
    (h : q ^ k ∣ q ^ i * m) : q ^ (k - i) ∣ m := by
  obtain ⟨r, hr⟩ := h
  have hpow : q ^ k = q ^ i * q ^ (k - i) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hik]
  have hmul : q ^ i * m = q ^ i * (q ^ (k - i) * r) := by
    rw [hpow, Nat.mul_assoc] at hr
    exact hr
  have hm : m = q ^ (k - i) * r :=
    Nat.mul_left_cancel ((Nat.pow_pos_iff.mpr) (Or.inl hq)) hmul
  exact ⟨r, hm⟩

/-- Before `k` affine steps a `q`-free state is not yet divisible by `q ^ k`. -/
theorem AffineNotDiv (q k t anchor i : ℕ) (hq : 2 ≤ q) (hi : i < k)
    (hfree : ¬ q ∣ anchor) :
    ¬ q ^ k ∣ q ^ i * anchor + (t * q ^ k) * Geom q i := by
  intro hd
  have hq0 : 0 < q := by omega
  have hsecond : q ^ k ∣ (t * q ^ k) * Geom q i := by
    refine ⟨t * Geom q i, ?_⟩
    rw [Nat.mul_comm t (q ^ k), Nat.mul_assoc]
  have hfirst : q ^ k ∣ q ^ i * anchor :=
    (Nat.dvd_add_iff_left hsecond).mpr hd
  have hlow : q ^ (k - i) ∣ anchor :=
    HighPowDividesBase q i k anchor hq0 (Nat.le_of_lt hi) hfirst
  have hspan : 1 ≤ k - i := by omega
  have hqdiv : q ∣ q ^ (k - i) := by
    have : q ^ 1 ∣ q ^ (k - i) := Nat.pow_dvd_pow q hspan
    simpa using this
  exact hfree (Nat.dvd_trans hqdiv hlow)

/-- One affine step matches the closed geometric recurrence. -/
theorem AffineFormulaStep (q c x i : ℕ) :
    q * (q ^ i * x + c * Geom q i) + c =
      q ^ (i + 1) * x + c * Geom q (i + 1) := by
  calc
    q * (q ^ i * x + c * Geom q i) + c
        = q * (q ^ i * x) + q * (c * Geom q i) + c := by rw [Nat.mul_add]
    _ = q ^ (i + 1) * x + q * (c * Geom q i) + c := by
      simp only [Nat.pow_succ', Nat.mul_assoc]
    _ = q ^ (i + 1) * x + (c * (q * Geom q i) + c) := by
      simp only [Nat.mul_left_comm q c (Geom q i), Nat.add_assoc]
    _ = q ^ (i + 1) * x + c * (q * Geom q i + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    _ = q ^ (i + 1) * x + c * Geom q (i + 1) := by rfl

/-- From a `q`-free anchor, `i ≤ k` raw steps stay on the affine formula. -/
theorem AnchorSegment (q k t anchor i : ℕ) (hq : 2 ≤ q) (_hk : 1 ≤ k)
    (hfree : ¬ q ∣ anchor) (hi : i ≤ k) :
    RawIterate q (t * q ^ k) (q ^ k) i anchor =
      q ^ i * anchor + (t * q ^ k) * Geom q i := by
  induction i with
  | zero => {
      simp [RawIterate, Geom]
    }
  | succ i ih => {
      have ile : i ≤ k := Nat.le_of_succ_le hi
      have ilt : i < k := Nat.lt_of_succ_le hi
      have ihv := ih ile
      have hnd := AffineNotDiv q k t anchor i hq ilt hfree
      have hstep :
          RawStep q (t * q ^ k) (q ^ k)
            (q ^ i * anchor + (t * q ^ k) * Geom q i) =
            q * (q ^ i * anchor + (t * q ^ k) * Geom q i) + t * q ^ k := by
        unfold RawStep
        rw [if_neg hnd]
      calc
        RawIterate q (t * q ^ k) (q ^ k) (i + 1) anchor
            = RawStep q (t * q ^ k) (q ^ k)
                (RawIterate q (t * q ^ k) (q ^ k) i anchor) := by
              rfl
        _ = RawStep q (t * q ^ k) (q ^ k)
              (q ^ i * anchor + (t * q ^ k) * Geom q i) := by rw [ihv]
        _ = q * (q ^ i * anchor + (t * q ^ k) * Geom q i) + t * q ^ k := hstep
        _ = q ^ (i + 1) * anchor + (t * q ^ k) * Geom q (i + 1) :=
          AffineFormulaStep q (t * q ^ k) anchor i
    }

/-- The state after `k` affine steps is exactly one division above the shift. -/
theorem LandingProduct (q k t anchor : ℕ) :
    q ^ k * anchor + (t * q ^ k) * Geom q k =
      q ^ k * (anchor + t * Geom q k) := by
  calc
    q ^ k * anchor + (t * q ^ k) * Geom q k
        = q ^ k * anchor + t * (q ^ k * Geom q k) := by rw [Nat.mul_assoc]
    _ = q ^ k * anchor + q ^ k * (t * Geom q k) := by rw [Nat.mul_left_comm]
    _ = q ^ k * (anchor + t * Geom q k) := by rw [← Nat.mul_add]

/-- A `q`-free anchor returns, after `k` affine steps and one division, at `anchor + b`. -/
theorem BlockLanding (q k t anchor : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (hfree : ¬ q ∣ anchor) :
    RawIterate q (t * q ^ k) (q ^ k) (k + 1) anchor =
      anchor + t * Geom q k := by
  have hseg := AnchorSegment q k t anchor k hq hk hfree le_rfl
  have hprod := LandingProduct q k t anchor
  have hq0 : 0 < q ^ k := (Nat.pow_pos_iff.mpr) (Or.inl (by omega : 0 < q))
  have hdvd : q ^ k ∣ q ^ k * anchor + (t * q ^ k) * Geom q k := by
    refine ⟨anchor + t * Geom q k, ?_⟩
    exact hprod
  have hdiv :
      RawStep q (t * q ^ k) (q ^ k)
        (q ^ k * anchor + (t * q ^ k) * Geom q k) =
        anchor + t * Geom q k := by
    unfold RawStep
    rw [if_pos hdvd]
    exact Nat.div_eq_of_eq_mul_right hq0 hprod
  calc
    RawIterate q (t * q ^ k) (q ^ k) (k + 1) anchor
        = RawStep q (t * q ^ k) (q ^ k)
            (RawIterate q (t * q ^ k) (q ^ k) k anchor) := by rfl
    _ = RawStep q (t * q ^ k) (q ^ k)
          (q ^ k * anchor + (t * q ^ k) * Geom q k) := by rw [hseg]
    _ = anchor + t * Geom q k := hdiv

/-- While every earlier anchor misses `q`, the block landings are the translations. -/
theorem PrefixAnchor (q k t n s r : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k)
    (hfree : ∀ r', r' < s → ¬ q ∣ n + r' * (t * Geom q k)) (hr : r ≤ s) :
    RawIterate q (t * q ^ k) (q ^ k) (r * (k + 1)) n =
      n + r * (t * Geom q k) := by
  induction r with
  | zero => {
      simp [RawIterate]
    }
  | succ r ih => {
      have hrle : r ≤ s := Nat.le_of_succ_le hr
      have hrlt : r < s := Nat.lt_of_succ_le hr
      have ihv := ih hrle
      have hanchor : ¬ q ∣ n + r * (t * Geom q k) := hfree r hrlt
      have hblock := BlockLanding q k t (n + r * (t * Geom q k)) hq hk hanchor
      have hadd :=
        RawIterateAdd q (t * q ^ k) (q ^ k) (r * (k + 1)) (k + 1) n
      have hidx : r * (k + 1) + (k + 1) = (r + 1) * (k + 1) := by
        rw [Nat.succ_mul]
      calc
        RawIterate q (t * q ^ k) (q ^ k) ((r + 1) * (k + 1)) n
            = RawIterate q (t * q ^ k) (q ^ k) (r * (k + 1) + (k + 1)) n := by
              rw [hidx]
        _ = RawIterate q (t * q ^ k) (q ^ k) (k + 1)
              (RawIterate q (t * q ^ k) (q ^ k) (r * (k + 1)) n) := hadd
        _ = RawIterate q (t * q ^ k) (q ^ k) (k + 1)
              (n + r * (t * Geom q k)) := by rw [ihv]
        _ = n + r * (t * Geom q k) + t * Geom q k := hblock
        _ = n + (r + 1) * (t * Geom q k) := by
          rw [Nat.succ_mul, Nat.add_assoc]
    }

/-- Every residue modulo a positive integer is hit by a coprime step. -/
theorem ResidueCover (q' t' r : ℕ) (hq : 0 < q') (hcop : Nat.Coprime q' t') :
    ∃ s, s < q' ∧ (t' * s) % q' = r % q' := by
  classical
  let f : Fin q' → Fin q' := fun s => ⟨(t' * s.val) % q', Nat.mod_lt _ hq⟩
  have key :
      ∀ u v : Fin q',
        (t' * u.val) % q' = (t' * v.val) % q' → u.val ≤ v.val → u = v := by
    intro u v hmod huv
    have hmul : t' * u.val ≤ t' * v.val := Nat.mul_le_mul_left t' huv
    have hcong : t' * u.val ≡ t' * v.val [MOD q'] := by
      calc
        t' * u.val ≡ (t' * u.val) % q' [MOD q'] := (Nat.mod_modEq _ _).symm
        _ ≡ (t' * v.val) % q' [MOD q'] := by rw [hmod]
        _ ≡ t' * v.val [MOD q'] := Nat.mod_modEq _ _
    have hdvd : q' ∣ t' * v.val - t' * u.val := (Nat.modEq_iff_dvd' hmul).mp hcong
    have hsub : t' * v.val - t' * u.val = t' * (v.val - u.val) := by
      rw [← Nat.mul_sub_left_distrib]
    have hdvd' : q' ∣ v.val - u.val := by
      rw [hsub, Nat.mul_comm] at hdvd
      exact hcop.dvd_of_dvd_mul_right hdvd
    have hlt : v.val - u.val < q' :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) v.isLt
    have hz : v.val - u.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' hlt
    exact Fin.ext (Nat.le_antisymm huv ((Nat.sub_eq_zero_iff_le).mp hz))
  have hinj : Function.Injective f := by
    intro s1 s2 hfs
    have hmod : (t' * s1.val) % q' = (t' * s2.val) % q' := congrArg Fin.val hfs
    rcases Nat.le_total s1.val s2.val with huv | huv
    · {
        exact key s1 s2 hmod huv
      }
    · {
        exact (key s2 s1 hmod.symm huv).symm
      }
  haveI : Finite (Fin q') := ⟨Equiv.refl (Fin q')⟩
  have hsurj : Function.Surjective f := (Finite.injective_iff_surjective).mp hinj
  obtain ⟨s, hs⟩ := hsurj ⟨r % q', Nat.mod_lt _ hq⟩
  refine ⟨s.val, s.isLt, ?_⟩
  exact congrArg Fin.val hs

/-- The first translation making `q` divide the state exists and is the least one. -/
theorem DelayExists (q k t n : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hfree : ¬ q ∣ n) (hg : Nat.gcd q t ∣ n) :
    ∃ s, 1 ≤ s ∧ s ≤ q / Nat.gcd q t - 1 ∧ q ∣ n + s * (t * Geom q k) ∧
      ∀ s', s' < s → ¬ q ∣ n + s' * (t * Geom q k) := by
  have hgpos : 0 < Nat.gcd q t := Nat.gcd_pos_of_pos_right q ht
  have hqg : Nat.gcd q t ∣ q := Nat.gcd_dvd_left q t
  have htg : Nat.gcd q t ∣ t := Nat.gcd_dvd_right q t
  set g := Nat.gcd q t
  set q' := q / g
  set t' := t / g
  set n' := n / g
  have hq'pos : 0 < q' := Nat.div_pos (Nat.le_of_dvd (by omega) hqg) hgpos
  have hq'ge : 2 ≤ q' := by
    by_contra hlt
    have hq'one : q' = 1 := by omega
    have hqeq : q = g := by
      rw [show q = g * q' from (Nat.mul_div_cancel' hqg).symm, hq'one, Nat.mul_one]
    exact hfree (by simpa [hqeq] using hg)
  have hcop : Nat.Coprime q' t' := Nat.coprime_div_gcd_div_gcd hgpos
  have hhit :=
    ResidueCover q' t' ((q' - n' % q') % q') hq'pos hcop
  obtain ⟨s0, hs0lt, hs0mod⟩ := hhit
  have hmod0 : (n' + t' * s0) % q' = 0 := by
    have hsum := Nat.add_mod n' (t' * s0) q'
    rw [hsum, hs0mod, Nat.mod_mod]
    set a := n' % q' with ha
    have halt : a < q' := Nat.mod_lt _ hq'pos
    by_cases hz : a = 0
    · {
        simp [hz, Nat.mod_self, Nat.zero_mod]
      }
    · {
        have hpos : 0 < a := Nat.pos_of_ne_zero hz
        have hsublt : q' - a < q' := Nat.sub_lt hq'pos hpos
        have hsubmod : (q' - a) % q' = q' - a := Nat.mod_eq_of_lt hsublt
        rw [hsubmod, Nat.add_sub_of_le (Nat.le_of_lt halt), Nat.mod_self]
      }
  have hq'dvd : q' ∣ n' + t' * s0 := (Nat.dvd_iff_mod_eq_zero).mpr hmod0
  have hscale : g * (n' + s0 * t') = n + s0 * t := by
    calc
      g * (n' + s0 * t') = g * n' + g * (s0 * t') := by rw [Nat.mul_add]
      _ = n + s0 * (g * t') := by
        rw [Nat.mul_div_cancel' hg, Nat.mul_left_comm]
      _ = n + s0 * t := by rw [Nat.mul_div_cancel' htg]
  have hqdvdt : q ∣ n + s0 * t := by
    have hmul : g * q' ∣ g * (n' + s0 * t') :=
      (Nat.mul_dvd_mul_iff_left hgpos).mpr (by simpa [Nat.mul_comm] using hq'dvd)
    have hqg' : g * q' = q := Nat.mul_div_cancel' hqg
    rw [hqg', hscale] at hmul
    simpa [Nat.mul_comm] using hmul
  have hqdvdb : q ∣ n + s0 * (t * Geom q k) :=
    (SumDivisibleIff q k t n s0 hk).mpr hqdvdt
  let p : ℕ → Prop := fun s => q ∣ n + s * (t * Geom q k)
  have hex : ∃ s, p s := ⟨s0, hqdvdb⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex, ?_⟩
  · {
      have hnot : ¬ p 0 := by
        intro hd
        exact hfree (by simpa [p] using hd)
      have : 0 < Nat.find hex := by
        by_contra h0
        have hzero : Nat.find hex = 0 := by omega
        exact hnot (hzero ▸ Nat.find_spec hex)
      omega
    }
  · {
      have hle : Nat.find hex ≤ s0 := Nat.find_min' hex hqdvdb
      have hlt : Nat.find hex < q' := Nat.lt_of_le_of_lt hle hs0lt
      exact Nat.le_sub_one_of_lt hlt
    }
  · {
      intro s' hs'
      exact Nat.find_min hex hs'
    }

/-- Below the clip, the affine state is still not divisible by `q ^ k`. -/
theorem ClipAffineNotDiv (q k t m i : ℕ) (hq : 2 ≤ q)
    (hi : i < k - ClipVal q k m) :
    ¬ q ^ k ∣ q ^ i * m + (t * q ^ k) * Geom q i := by
  intro hd
  set j := ClipVal q k m
  have hq0 : 0 < q := by omega
  have hsecond : q ^ k ∣ (t * q ^ k) * Geom q i := by
    refine ⟨t * Geom q i, ?_⟩
    rw [Nat.mul_comm t (q ^ k), Nat.mul_assoc]
  have hfirst : q ^ k ∣ q ^ i * m := (Nat.dvd_add_iff_left hsecond).mpr hd
  have hik : i ≤ k := by
    have hle : i < k - j := hi
    have hjle : j ≤ k := ClipValLe q k m
    omega
  have hlow : q ^ (k - i) ∣ m := HighPowDividesBase q i k m hq0 hik hfirst
  have hgap : j + 1 ≤ k - i := by omega
  have hdiv : q ^ (j + 1) ∣ m := by
    have hp : q ^ (j + 1) ∣ q ^ (k - i) := Nat.pow_dvd_pow q hgap
    exact Nat.dvd_trans hp hlow
  have hjlt : j < k := by omega
  exact ClipValSuccNot q k m hjlt hdiv

/-- Affine steps before the clipped division stay on the closed formula. -/
theorem ClipSegment (q k t m i : ℕ) (hq : 2 ≤ q) (_hk : 1 ≤ k)
    (hi : i ≤ k - ClipVal q k m) :
    RawIterate q (t * q ^ k) (q ^ k) i m =
      q ^ i * m + (t * q ^ k) * Geom q i := by
  induction i with
  | zero => {
      simp [RawIterate, Geom]
    }
  | succ i ih => {
      have ile : i ≤ k - ClipVal q k m := Nat.le_of_succ_le hi
      have ilt : i < k - ClipVal q k m := Nat.lt_of_succ_le hi
      have ihv := ih ile
      have hnd := ClipAffineNotDiv q k t m i hq ilt
      have hstep :
          RawStep q (t * q ^ k) (q ^ k)
            (q ^ i * m + (t * q ^ k) * Geom q i) =
            q * (q ^ i * m + (t * q ^ k) * Geom q i) + t * q ^ k := by
        unfold RawStep
        rw [if_neg hnd]
      calc
        RawIterate q (t * q ^ k) (q ^ k) (i + 1) m
            = RawStep q (t * q ^ k) (q ^ k)
                (RawIterate q (t * q ^ k) (q ^ k) i m) := by rfl
        _ = RawStep q (t * q ^ k) (q ^ k)
              (q ^ i * m + (t * q ^ k) * Geom q i) := by rw [ihv]
        _ = q * (q ^ i * m + (t * q ^ k) * Geom q i) + t * q ^ k := hstep
        _ = q ^ (i + 1) * m + (t * q ^ k) * Geom q (i + 1) :=
          AffineFormulaStep q (t * q ^ k) m i
    }

/-- The clipped division state is `q ^ k` times the return value. -/
theorem ClipProduct (q k t m : ℕ) :
    q ^ (k - ClipVal q k m) * m +
        (t * q ^ k) * Geom q (k - ClipVal q k m) =
      q ^ k * FamilyReturn q k t m := by
  set j := ClipVal q k m
  have hj : q ^ j ∣ m := ClipValDvd q k m
  have hpow : q ^ k = q ^ (k - j) * q ^ j := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (ClipValLe q k m)]
  calc
    q ^ (k - j) * m + (t * q ^ k) * Geom q (k - j)
        = q ^ (k - j) * (q ^ j * (m / q ^ j)) +
            (t * q ^ k) * Geom q (k - j) := by
          exact congrArg
            (fun z => q ^ (k - j) * z + (t * q ^ k) * Geom q (k - j))
            (Nat.mul_div_cancel' hj).symm
    _ = q ^ (k - j) * q ^ j * (m / q ^ j) +
          (t * q ^ k) * Geom q (k - j) := by
          rw [← Nat.mul_assoc]
    _ = q ^ k * (m / q ^ j) + (t * q ^ k) * Geom q (k - j) := by
          rw [← hpow]
    _ = q ^ k * (m / q ^ j) + t * (q ^ k * Geom q (k - j)) := by
          rw [Nat.mul_assoc]
    _ = q ^ k * (m / q ^ j) + q ^ k * (t * Geom q (k - j)) := by
          rw [Nat.mul_left_comm t (q ^ k) (Geom q (k - j))]
    _ = q ^ k * (m / q ^ j + t * Geom q (k - j)) := by rw [← Nat.mul_add]
    _ = q ^ k * FamilyReturn q k t m := by rfl

/-- The return is the raw state after the clipped affine run and one division. -/
theorem HClosedForm (q k t m : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) :
    RawIterate q (t * q ^ k) (q ^ k) (k - ClipVal q k m + 1) m =
      FamilyReturn q k t m := by
  set j := ClipVal q k m
  have hseg := ClipSegment q k t m (k - j) hq hk le_rfl
  have hprod := ClipProduct q k t m
  have hq0 : 0 < q ^ k := (Nat.pow_pos_iff.mpr) (Or.inl (by omega : 0 < q))
  have hdvd :
      q ^ k ∣
        q ^ (k - j) * m + (t * q ^ k) * Geom q (k - j) := by
    refine ⟨FamilyReturn q k t m, ?_⟩
    simpa [j] using hprod
  have hdiv :
      RawStep q (t * q ^ k) (q ^ k)
        (q ^ (k - j) * m + (t * q ^ k) * Geom q (k - j)) =
        FamilyReturn q k t m := by
    unfold RawStep
    rw [if_pos hdvd]
    exact Nat.div_eq_of_eq_mul_right hq0 (by simpa [j] using hprod)
  calc
    RawIterate q (t * q ^ k) (q ^ k) (k - j + 1) m
        = RawStep q (t * q ^ k) (q ^ k)
            (RawIterate q (t * q ^ k) (q ^ k) (k - j) m) := by rfl
    _ = RawStep q (t * q ^ k) (q ^ k)
          (q ^ (k - j) * m + (t * q ^ k) * Geom q (k - j)) := by
          exact congrArg (RawStep q (t * q ^ k) (q ^ k))
            (by simpa [j] using hseg)
    _ = FamilyReturn q k t m := hdiv

/-- Exact division of a positive state leaves a positive return. -/
theorem FamilyReturnPositive (q k t m : ℕ) (hq : 2 ≤ q) (hm : 1 ≤ m) :
    1 ≤ FamilyReturn q k t m := by
  have hp : 0 < q ^ ClipVal q k m :=
    Nat.pow_pos_iff.mpr (Or.inl (by omega : 0 < q))
  have hle : q ^ ClipVal q k m ≤ m :=
    Nat.le_of_dvd (by omega : 0 < m) (ClipValDvd q k m)
  have hquot : 1 ≤ m / q ^ ClipVal q k m :=
    Nat.succ_le_of_lt (Nat.div_pos hle hp)
  exact le_trans hquot (Nat.le_add_right _ _)

/-- Quotients by higher powers of `q` are at most the quotient by `q`. -/
theorem QuotientPowLe (q j m : ℕ) (_hq : 0 < q) (hj : 1 ≤ j) (_hd : q ^ j ∣ m) :
    m / q ^ j ≤ m / q := by
  have hpow : q ^ j = q * q ^ (j - 1) := by
    calc
      q ^ j = q ^ (j - 1 + 1) :=
        congrArg (fun e : ℕ => q ^ e) (Nat.sub_add_cancel hj).symm
      _ = q * q ^ (j - 1) := Nat.pow_succ'
  have hdiv : m / q ^ j = (m / q) / q ^ (j - 1) := by
    rw [hpow, ← Nat.div_div_eq_div_mul]
  rw [hdiv]
  exact Nat.div_le_self _ _

/-- The return numerator is at most the explicit linear excess. -/
theorem ReturnProductBound (q k t n s : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (_hs1 : 1 ≤ s) (hsu : s ≤ q / Nat.gcd q t - 1) (hqm : q ∣ n + s * FamilyShift q k t) :
    FamilyReturn q k t (n + s * FamilyShift q k t) * q ≤
      n + FamilyExcess q k t := by
  set g := Nat.gcd q t
  set b := FamilyShift q k t
  set m := n + s * b
  set j := ClipVal q k m
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right q ht
  have hgle : g ≤ q := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left q t)
  have hu : 1 ≤ q / g := Nat.succ_le_of_lt (Nat.div_pos hgle hgpos)
  have hj1 : 1 ≤ j := by
    have hqd : q ^ 1 ∣ m := by simpa using hqm
    have hjle : 1 ≤ k := hk
    exact ClipValMax q k m 1 hjle hqd
  have hqu : m / q ^ j ≤ m / q :=
    QuotientPowLe q j m (by omega) hj1 (ClipValDvd q k m)
  have hgeom : Geom q (k - j) ≤ Geom q (k - 1) := by
    have hle : k - j ≤ k - 1 := by omega
    exact GeomMono q (k - j) (k - 1) hle
  have hexcess : q * (t * Geom q (k - 1)) = b - t := by
    simpa [b, FamilyShift] using (TranslationExcess q k t hk).symm
  have hmulJ :
      FamilyReturn q k t m * q ≤ m + (b - t) := by
    have hJ :
        FamilyReturn q k t m * q =
          q * (m / q ^ j) + q * (t * Geom q (k - j)) := by
      calc
        FamilyReturn q k t m * q
            = (m / q ^ ClipVal q k m +
                t * Geom q (k - ClipVal q k m)) * q := by
              rfl
        _ = (m / q ^ j + t * Geom q (k - j)) * q := by
              simp [j]
        _ = m / q ^ j * q + (t * Geom q (k - j)) * q := by
              rw [Nat.add_mul]
        _ = q * (m / q ^ j) + q * (t * Geom q (k - j)) := by
              rw [Nat.mul_comm (m / q ^ j) q,
                Nat.mul_comm (t * Geom q (k - j)) q]
    have hleft : q * (m / q ^ j) ≤ m := by
      exact le_trans (Nat.mul_le_mul_left q hqu) (Nat.mul_div_le m q)
    have hright : q * (t * Geom q (k - j)) ≤ b - t := by
      have hcmp : q * (t * Geom q (k - j)) ≤ q * (t * Geom q (k - 1)) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hgeom)
      rw [hexcess] at hcmp
      exact hcmp
    have : q * (m / q ^ j) + q * (t * Geom q (k - j)) ≤ m + (b - t) :=
      Nat.add_le_add hleft hright
    simpa [hJ] using this
  have hbt : t ≤ b := by
    have hone : 1 ≤ Geom q k := GeomAtLeastOne q k hk
    have : t * 1 ≤ t * Geom q k := Nat.mul_le_mul_left t hone
    simpa [b, FamilyShift, Nat.mul_one] using this
  have hsb : s * b ≤ (q / g - 1) * b := Nat.mul_le_mul_right b hsu
  have hmle : m ≤ n + (q / g - 1) * b := by
    simpa [m] using Nat.add_le_add_left hsb n
  have hrest : (q / g - 1) * b + (b - t) = (q / g) * b - t := by
    have hassoc :
        (q / g - 1) * b + (b - t) = (q / g - 1) * b + b - t :=
      (Nat.add_sub_assoc hbt ((q / g - 1) * b)).symm
    have hsum : (q / g - 1) * b + b = (q / g) * b := by
      calc
        (q / g - 1) * b + b = (q / g - 1) * b + 1 * b := by rw [Nat.one_mul]
        _ = ((q / g - 1) + 1) * b := by rw [← Nat.add_mul]
        _ = (q / g) * b := by rw [Nat.sub_add_cancel hu]
    calc
      (q / g - 1) * b + (b - t) = (q / g - 1) * b + b - t := hassoc
      _ = (q / g) * b - t := by rw [hsum]
  have hjoin : m + (b - t) ≤ n + ((q / g) * b - t) := by
    have hstep : m + (b - t) ≤ n + (q / g - 1) * b + (b - t) :=
      Nat.add_le_add_right hmle _
    have hident :
        n + (q / g - 1) * b + (b - t) = n + ((q / g) * b - t) := by
      calc
        n + (q / g - 1) * b + (b - t)
            = n + ((q / g - 1) * b + (b - t)) := by rw [Nat.add_assoc]
        _ = n + ((q / g) * b - t) := by rw [hrest]
    exact le_trans hstep (by rw [hident])
  have hA : (q / g) * b - t = FamilyExcess q k t := by
    simp [FamilyExcess, b, FamilyShift, g]
  calc
    FamilyReturn q k t m * q ≤ m + (b - t) := hmulJ
    _ ≤ n + ((q / g) * b - t) := hjoin
    _ = n + FamilyExcess q k t := by rw [hA]

/-- Above the floor threshold the return is strictly smaller. -/
theorem ReturnStrictDescent (q n A J : ℕ) (hq : 2 ≤ q) (hJ : J * q ≤ n + A)
    (hN : A / (q - 1) < n) : J < n := by
  have hd : 0 < q - 1 := by omega
  have hA : A < n * (q - 1) := (Nat.div_lt_iff_lt_mul hd).mp hN
  have hsum : n + A < n * q := by
    have hstrict : n + A < n + n * (q - 1) := Nat.add_lt_add_left hA n
    have hident : n + n * (q - 1) = n * q := by
      calc
        n + n * (q - 1) = n * 1 + n * (q - 1) := by rw [Nat.mul_one]
        _ = n * (1 + (q - 1)) := by rw [← Nat.mul_add]
        _ = n * ((q - 1) + 1) := by rw [Nat.add_comm]
        _ = n * q := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
    exact lt_of_lt_of_le hstrict (by rw [hident])
  have hmul : J * q < n * q := lt_of_le_of_lt hJ hsum
  have hcomm : q * J < q * n := by simpa [Nat.mul_comm] using hmul
  exact (Nat.mul_lt_mul_left (by omega : 0 < q)).mp hcomm

/-- At or below the floor threshold the return does not exceed it. -/
theorem ReturnCoreBound (q n A J : ℕ) (hq : 2 ≤ q) (hJ : J * q ≤ n + A)
    (hn : n ≤ A / (q - 1)) : J ≤ A / (q - 1) := by
  set N0 := A / (q - 1)
  have hd : 0 < q - 1 := by omega
  have hA : A < (N0 + 1) * (q - 1) :=
    (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self N0)
  have hsplit : (N0 + 1) * q = (N0 + 1) * (q - 1) + (N0 + 1) := by
    calc
      (N0 + 1) * q = (N0 + 1) * (q - 1 + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = (N0 + 1) * (q - 1) + (N0 + 1) := by rw [Nat.mul_add, Nat.mul_one]
  have hsum : N0 + A < (N0 + 1) * q := by
    rw [hsplit]
    omega
  have hlt : J * q < (N0 + 1) * q :=
    lt_of_le_of_lt hJ (lt_of_le_of_lt (Nat.add_le_add_right hn A) hsum)
  have hJsucc : J < N0 + 1 :=
    (Nat.mul_lt_mul_right (by omega : 0 < q)).mp hlt
  exact Nat.le_of_lt_succ hJsucc

/-- A missed gcd makes every block the neutral translation, hence unbounded. -/
theorem NeutralEscape (q k t n : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (_hn : 1 ≤ n) (_hfree : ¬ q ∣ n) (hng : ¬ Nat.gcd q t ∣ n) :
    (∀ s i, i ≤ k →
      RawIterate q (FamilyOffset q k t) (FamilyDivisor q k) (s * (k + 1) + i) n =
        q ^ i * (n + s * FamilyShift q k t) +
          FamilyOffset q k t * Geom q i) ∧
    (∀ N, ∃ m, N < RawIterate q (FamilyOffset q k t) (FamilyDivisor q k) m n) := by
  have hanchor : ∀ s, ¬ q ∣ n + s * FamilyShift q k t := by
    intro s
    simpa [FamilyShift] using AnchorFree q k t n s hk hng
  refine ⟨?_, ?_⟩
  · {
      intro s i hi
      have hland :=
        PrefixAnchor q k t n (s + 1) s hq hk
          (by
            intro r' _hr'
            exact hanchor r')
          (Nat.le_succ s)
      have hseg :=
        AnchorSegment q k t (n + s * FamilyShift q k t) i hq hk (hanchor s) hi
      calc
        RawIterate q (FamilyOffset q k t) (FamilyDivisor q k) (s * (k + 1) + i) n
            = RawIterate q (t * q ^ k) (q ^ k) i
                (RawIterate q (t * q ^ k) (q ^ k) (s * (k + 1)) n) := by
              simpa [FamilyOffset, FamilyDivisor] using
                RawIterateAdd q (t * q ^ k) (q ^ k) (s * (k + 1)) i n
        _ = RawIterate q (t * q ^ k) (q ^ k) i (n + s * FamilyShift q k t) := by
          simpa [FamilyShift, FamilyOffset, FamilyDivisor] using congrArg _ hland
        _ = q ^ i * (n + s * FamilyShift q k t) +
              (t * q ^ k) * Geom q i := hseg
        _ = q ^ i * (n + s * FamilyShift q k t) +
              FamilyOffset q k t * Geom q i := by rfl
    }
  · {
      intro N
      have hb : 1 ≤ FamilyShift q k t := by
        have hone : 1 ≤ Geom q k := GeomAtLeastOne q k hk
        have hmul : t * 1 ≤ t * Geom q k := Nat.mul_le_mul_left t hone
        have ht1 : 1 ≤ t := ht
        have : 1 ≤ t * Geom q k := by
          exact le_trans ht1 (by simpa [Nat.mul_one] using hmul)
        simpa [FamilyShift] using this
      refine ⟨(N + 1) * (k + 1), ?_⟩
      have hland :=
        PrefixAnchor q k t n (N + 1) (N + 1) hq hk
          (by
            intro r' _
            exact hanchor r')
          le_rfl
      have hgt : N < n + (N + 1) * FamilyShift q k t := by
        calc
          N < N + 1 := Nat.lt_succ_self N
          _ ≤ (N + 1) * FamilyShift q k t :=
            Nat.le_mul_of_pos_right (N + 1) (by omega)
          _ ≤ n + (N + 1) * FamilyShift q k t := Nat.le_add_left _ n
      simpa [FamilyOffset, FamilyDivisor, FamilyShift] using lt_of_lt_of_eq hgt hland.symm
    }

/-- Every raw time, not only the block landings, obeys a growing lower bound. -/
theorem NeutralEscapeLowerBound (q k t n clock : ℕ)
    (hq : 2 ≤ q) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hn : 1 ≤ n) (hfree : ¬ q ∣ n) (hng : ¬ Nat.gcd q t ∣ n) :
    n + (clock / (k + 1)) * FamilyShift q k t ≤
      RawIterate q (FamilyOffset q k t) (FamilyDivisor q k) clock n := by
  have hi : clock % (k + 1) ≤ k :=
    Nat.le_of_lt_succ (Nat.mod_lt clock (by omega : 0 < k + 1))
  have hclock : clock / (k + 1) * (k + 1) + clock % (k + 1) = clock := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod clock (k + 1)
  have hformula := (NeutralEscape q k t n hq hk ht hn hfree hng).1
    (clock / (k + 1)) (clock % (k + 1)) hi
  rw [hclock] at hformula
  rw [hformula]
  have hpower : 1 ≤ q ^ (clock % (k + 1)) :=
    Nat.succ_le_of_lt (Nat.pow_pos_iff.mpr (Or.inl (by omega : 0 < q)))
  have hmul := Nat.mul_le_mul_right
    (n + (clock / (k + 1)) * FamilyShift q k t) hpower
  exact le_trans (by simpa only [Nat.one_mul] using hmul) (Nat.le_add_right _ _)

/-- A hit of the gcd produces a strictly contracting return above the floor. -/
theorem NeutralReturn (q k t n : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hfree : ¬ q ∣ n) (hg : Nat.gcd q t ∣ n) :
    ∃ s, 1 ≤ s ∧ s ≤ q / Nat.gcd q t - 1 ∧
      q ∣ n + s * FamilyShift q k t ∧
      (∀ s', s' < s → ¬ q ∣ n + s' * FamilyShift q k t) ∧
      RawIterate q (FamilyOffset q k t) (FamilyDivisor q k)
        (s * (k + 1)) n = n + s * FamilyShift q k t ∧
      RawIterate q (FamilyOffset q k t) (FamilyDivisor q k)
        (s * (k + 1) + (k - ClipVal q k (n + s * FamilyShift q k t) + 1)) n =
          FamilyReturn q k t (n + s * FamilyShift q k t) ∧
      FamilyReturn q k t (n + s * FamilyShift q k t) * q ≤
        n + FamilyExcess q k t ∧
      (FamilyExcess q k t / (q - 1) < n →
        FamilyReturn q k t (n + s * FamilyShift q k t) < n) ∧
      (n ≤ FamilyExcess q k t / (q - 1) →
        FamilyReturn q k t (n + s * FamilyShift q k t) ≤
          FamilyExcess q k t / (q - 1)) := by
  obtain ⟨s, hs1, hsu, hqd, hmin⟩ := DelayExists q k t n hq hk ht hfree hg
  have hprefix :=
    PrefixAnchor q k t n s s hq hk
      (by
        intro r' hr'
        simpa [FamilyShift] using hmin r' hr')
      le_rfl
  set m := n + s * FamilyShift q k t
  have hH := HClosedForm q k t m hq hk
  have hprod := ReturnProductBound q k t n s hq hk ht hs1 hsu
    (by simpa [FamilyShift] using hqd)
  refine ⟨s, hs1, hsu, hqd, ?_, ?_, ?_, hprod, ?_, ?_⟩
  · {
      intro s' hs'
      simpa [FamilyShift] using hmin s' hs'
    }
  · {
      simpa [FamilyOffset, FamilyDivisor, FamilyShift, m] using hprefix
    }
  · {
      have hadd :=
        RawIterateAdd q (t * q ^ k) (q ^ k) (s * (k + 1))
          (k - ClipVal q k m + 1) n
      calc
        RawIterate q (FamilyOffset q k t) (FamilyDivisor q k)
            (s * (k + 1) + (k - ClipVal q k m + 1)) n
            = RawIterate q (t * q ^ k) (q ^ k) (k - ClipVal q k m + 1)
                (RawIterate q (t * q ^ k) (q ^ k) (s * (k + 1)) n) := by
              simpa [FamilyOffset, FamilyDivisor] using hadd
        _ = RawIterate q (t * q ^ k) (q ^ k) (k - ClipVal q k m + 1) m := by
          simpa [FamilyOffset, FamilyDivisor, FamilyShift, m] using congrArg _ hprefix
        _ = FamilyReturn q k t m := hH
    }
  · {
      intro hN
      exact ReturnStrictDescent q n (FamilyExcess q k t)
        (FamilyReturn q k t m) hq hprod hN
    }
  · {
      intro hn
      exact ReturnCoreBound q n (FamilyExcess q k t)
        (FamilyReturn q k t m) hq hprod hn
    }

/-- Separation of a `q`-free seed on the neutral family `D = q ^ k`, `c = t * D`. -/
theorem NeutralReturnSeparation (q k t n : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hn : 1 ≤ n) (hfree : ¬ q ∣ n) :
    (¬ Nat.gcd q t ∣ n →
      (∀ s i, i ≤ k →
        RawIterate q (FamilyOffset q k t) (FamilyDivisor q k) (s * (k + 1) + i) n =
          q ^ i * (n + s * FamilyShift q k t) + FamilyOffset q k t * Geom q i) ∧
      (∀ N, ∃ m, N <
        RawIterate q (FamilyOffset q k t) (FamilyDivisor q k) m n)) ∧
    (Nat.gcd q t ∣ n →
      ∃ s, 1 ≤ s ∧ s ≤ q / Nat.gcd q t - 1 ∧
        q ∣ n + s * FamilyShift q k t ∧
        (∀ s', s' < s → ¬ q ∣ n + s' * FamilyShift q k t) ∧
        RawIterate q (FamilyOffset q k t) (FamilyDivisor q k) (s * (k + 1)) n =
          n + s * FamilyShift q k t ∧
        RawIterate q (FamilyOffset q k t) (FamilyDivisor q k)
          (s * (k + 1) +
            (k - ClipVal q k (n + s * FamilyShift q k t) + 1)) n =
            FamilyReturn q k t (n + s * FamilyShift q k t) ∧
        FamilyReturn q k t (n + s * FamilyShift q k t) * q ≤
          n + FamilyExcess q k t ∧
        (FamilyExcess q k t / (q - 1) < n →
          FamilyReturn q k t (n + s * FamilyShift q k t) < n) ∧
        (n ≤ FamilyExcess q k t / (q - 1) →
          FamilyReturn q k t (n + s * FamilyShift q k t) ≤
            FamilyExcess q k t / (q - 1))) := by
  refine ⟨?_, ?_⟩
  · {
      intro hng
      exact NeutralEscape q k t n hq hk ht hn hfree hng
    }
  · {
      intro hg
      exact NeutralReturn q k t n hq hk ht hfree hg
    }

/-- A return below the floor can change from the gcd class to the escape class. -/
theorem SmallReturnEscapeData :
    FamilyShift 4 2 2 = 10 ∧ FamilyExcess 4 2 2 = 18 ∧
    FamilyExcess 4 2 2 / (4 - 1) = 6 ∧ FamilyReturn 4 2 2 12 = 5 ∧
    RawIterate 4 32 16 5 2 = 5 ∧ ¬ Nat.gcd 4 2 ∣ 5 := by
  decide

/-- The seed `2`, below the floor `6`, subsequently follows an escaping neutral orbit. -/
theorem SmallReturnEscape (s i : ℕ) (hi : i ≤ 2) :
    RawIterate 4 32 16 (5 + (s * 3 + i)) 2 =
      4 ^ i * (5 + s * 10) + 32 * Geom 4 i := by
  have hland : RawIterate 4 32 16 5 2 = 5 := by decide
  have hformula := (NeutralEscape 4 2 2 5 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).1 s i hi
  change RawIterate 4 32 16 (s * 3 + i) 5 =
    4 ^ i * (5 + s * 10) + 32 * Geom 4 i at hformula
  rw [RawIterateAdd, hland]
  exact hformula

end GeneralizedCollatz.Discriminator
