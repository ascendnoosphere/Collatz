-- SPDX-License-Identifier: CC-BY-4.0
import GeneralizedCollatz
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic

/-!
Explicit positive cycles of the raw map

  `NatRawStep d q c n = n / d` for `d ∣ n`, and `NatRawStep d q c n = q * n + c` otherwise,

for `q ≥ 1`, `c ≥ 0` and `d ≥ 2`.  The family records four parameter slices of the raw
map and proves, on each of them, statements about positive cycles and their periods:

* `q = 2 c + 1`, `d = 2`, `c` even: every positive seed reaches an odd state and then
  increases strictly at every step, so every seed diverges.
* `q = 2 c + 1`, `d = 2`, `c` odd: `gcd (NatRawStep … n) c = gcd n c`, so the divisor strata
  of `c` are forward invariant; if no seed diverges then every divisor of `c` carries a
  cycle.  For `c = 3 (8 ^ h - 1) / 7` the seed `3` lies on a primitive cycle of length
  `3 h + 1` that avoids `1`.
* `q = d + c` with `c = (d - 1) (d ^ (k - 1) - 1)`: the residues are a full translation
  cycle, and `d - 1` lies on a primitive cycle of length `k + 1` that avoids `1` for
  `d ≥ 3`; `d = k = 2` is the classical cycle `1 ↦ 4 ↦ 2 ↦ 1`.
* `q = d + 1`, `c = d - 1`, `d ≥ 3`: an affine step can never be followed by divisions
  down to `1`, so the seeds that reach `1` are exactly the powers of `d`, and `1` is on no
  positive cycle.

Every statement is about the raw clock: divisions are single steps and no compressed
event clock is used.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The raw map: divide a multiple of `d`, otherwise apply the affine branch. -/
def NatRawStep (d q c n : ℕ) : ℕ := if d ∣ n then n / d else q * n + c

/-- A multiple of `d` is divided immediately. -/
theorem RawStepOfDvd (d q c n : ℕ) (h : d ∣ n) : NatRawStep d q c n = n / d := by
  rw [NatRawStep, if_pos h]

/-- A non-multiple of `d` takes the affine branch. -/
theorem RawStepOfNotDvd (d q c n : ℕ) (h : ¬ d ∣ n) : NatRawStep d q c n = q * n + c := by
  rw [NatRawStep, if_neg h]

/-- An iterate may execute its first instruction before the remaining ones. -/
theorem RawStepIterateSucc {α : Type*} (f : α → α) (k : ℕ) (x : α) :
    Iterate f (k + 1) x = Iterate f k (f x) := by
  rw [show k + 1 = 1 + k by omega, IterateAdd]
  rfl

/-- An iterate may execute its last instruction after the previous ones. -/
theorem RawStepIterateSuccLast {α : Type*} (f : α → α) (k : ℕ) (x : α) :
    Iterate f (k + 1) x = f (Iterate f k x) := rfl

/-- `j` divisions send `d ^ j * m` to `m`. -/
theorem RawStepDivMulIterate (d q c m j : ℕ) (hd : 2 ≤ d) :
    Iterate (NatRawStep d q c) j (d ^ j * m) = m := by
  induction j with
  | zero => simp [Iterate]
  | succ j ih =>
      rw [RawStepIterateSucc]
      have hdvd : d ∣ d ^ (j + 1) * m := by
        refine dvd_mul_of_dvd_left ?_ m
        exact ⟨d ^ j, by rw [pow_succ']⟩
      rw [RawStepOfDvd d q c _ hdvd]
      rw [show d ^ (j + 1) * m = d * (d ^ j * m) by rw [pow_succ']; ring,
        Nat.mul_div_cancel_left _ (by omega : 0 < d)]
      exact ih

/-- `j` divisions send `d ^ j` to `1`. -/
theorem RawStepPowIterate (d q c j : ℕ) (hd : 2 ≤ d) :
    Iterate (NatRawStep d q c) j (d ^ j) = 1 := by
  have h := RawStepDivMulIterate d q c 1 j hd
  simpa using h

/-- A bounded positive orbit repeats two of its early states. -/
theorem RawStepBoundedEventuallyPeriodic (d q c n M : ℕ)
    (hM : ∀ k, Iterate (NatRawStep d q c) k n ≤ M) :
    ∃ k p, 0 < p ∧ Iterate (NatRawStep d q c) (k + p) n = Iterate (NatRawStep d q c) k n := by
  obtain ⟨i, _, j, _, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (M + 2)) (t := Finset.range (M + 1))
      (by simp) (f := fun k => Iterate (NatRawStep d q c) k n) (by
        intro k _
        have hk := hM k
        simpa [Finset.mem_range] using Nat.lt_succ_of_le hk)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · refine ⟨i, j - i, by omega, ?_⟩
    rw [Nat.add_sub_of_le (le_of_lt hlt)]
    exact heq.symm
  · refine ⟨j, i - j, by omega, ?_⟩
    rw [Nat.add_sub_of_le (le_of_lt hgt)]
    exact heq

/-- An odd state takes the affine branch when `d = 2`. -/
theorem RawStepTwoOfOdd (q c n : ℕ) (hn : Odd n) : NatRawStep 2 q c n = q * n + c := by
  refine RawStepOfNotDvd 2 q c n ?_
  exact fun h => Nat.not_even_iff_odd.mpr hn (even_iff_two_dvd.mpr h)

/-- With `q = 2 c + 1` an odd state maps to `(2 c + 1) n + c`. -/
theorem RawStepTwoEvenOffsetAffine (c n : ℕ) (hn : Odd n) :
    NatRawStep 2 (2 * c + 1) c n = (2 * c + 1) * n + c :=
  RawStepTwoOfOdd (2 * c + 1) c n hn

/-- For even `c` the affine step of an odd state is odd again. -/
theorem RawStepTwoEvenOffsetOddOfOdd (c n : ℕ) (hc : Even c) (hn : Odd n) :
    Odd (NatRawStep 2 (2 * c + 1) c n) := by
  rw [RawStepTwoEvenOffsetAffine c n hn]
  exact (odd_two_mul_add_one c).mul hn |>.add_even hc

/-- For even `c` and `1 ≤ c` the affine step of an odd positive state increases it. -/
theorem RawStepTwoEvenOffsetIncreaseOdd (c n : ℕ) (hc1 : 1 ≤ c) (hn : Odd n) :
    n < NatRawStep 2 (2 * c + 1) c n := by
  rw [RawStepTwoEvenOffsetAffine c n hn]
  have hle : n ≤ (2 * c + 1) * n :=
    Nat.le_mul_of_pos_left n (by omega)
  omega

/-- Every positive seed of the even-offset slice reaches an odd state. -/
theorem RawStepTwoEvenOffsetReachesOdd (c n : ℕ) (hn : 1 ≤ n) :
    ∃ j, Odd (Iterate (NatRawStep 2 (2 * c + 1) c) j n) := by
  revert hn
  refine Nat.strong_induction_on n ?_
  intro n ih hn
  rcases Nat.even_or_odd n with hev | hod
  · have h2 : 2 ∣ n := even_iff_two_dvd.mp hev
    have hdiv : NatRawStep 2 (2 * c + 1) c n = n / 2 := RawStepOfDvd 2 (2 * c + 1) c n h2
    have hpos : 1 ≤ n / 2 := by
      have := Nat.div_mul_cancel h2
      omega
    have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
    obtain ⟨j, hj⟩ := ih (n / 2) hlt hpos
    exact ⟨j + 1, by rw [RawStepIterateSucc, hdiv]; exact hj⟩
  · exact ⟨0, hod⟩

/-- Every positive seed of the even-offset slice eventually increases forever. -/
theorem RawStepTwoEvenOffsetUnbounded (c n : ℕ) (hc : Even c) (hc1 : 1 ≤ c)
    (hn : 1 ≤ n) : ∀ M, ∃ k, M < Iterate (NatRawStep 2 (2 * c + 1) c) k n := by
  obtain ⟨j, hj⟩ := RawStepTwoEvenOffsetReachesOdd c n hn
  have hstep : ∀ x, Odd x → x + 1 ≤ NatRawStep 2 (2 * c + 1) c x := by
    intro x hx
    have hlt := RawStepTwoEvenOffsetIncreaseOdd c x hc1 hx
    omega
  have hodd : ∀ t, Odd (Iterate (NatRawStep 2 (2 * c + 1) c) t
      (Iterate (NatRawStep 2 (2 * c + 1) c) j n)) := by
    intro t
    induction t with
    | zero => simpa [Iterate] using hj
    | succ t ih =>
        have h := RawStepTwoEvenOffsetOddOfOdd c _ hc ih
        simpa [Iterate] using h
  have hmono : ∀ t, Iterate (NatRawStep 2 (2 * c + 1) c) j n + t
      ≤ Iterate (NatRawStep 2 (2 * c + 1) c) t (Iterate (NatRawStep 2 (2 * c + 1) c) j n) := by
    intro t
    induction t with
    | zero => simp [Iterate]
    | succ t ih =>
        have h := hstep _ (hodd t)
        have hlast : NatRawStep 2 (2 * c + 1) c
            (Iterate (NatRawStep 2 (2 * c + 1) c) t (Iterate (NatRawStep 2 (2 * c + 1) c) j n))
            = Iterate (NatRawStep 2 (2 * c + 1) c) (t + 1)
              (Iterate (NatRawStep 2 (2 * c + 1) c) j n) := rfl
        omega
  intro M
  refine ⟨j + M, ?_⟩
  rw [IterateAdd]
  have hM := hmono M
  have hpos : 1 ≤ Iterate (NatRawStep 2 (2 * c + 1) c) j n := hj.pos
  omega

/-- For odd `c` the divisor gcd with `c` is invariant under one step. -/
theorem RawStepTwoOddOffsetGcd (c n : ℕ) (hc : Odd c) :
    Nat.gcd (NatRawStep 2 (2 * c + 1) c n) c = Nat.gcd n c := by
  by_cases h2 : 2 ∣ n
  · rw [RawStepOfDvd 2 (2 * c + 1) c n h2]
    refine Nat.dvd_antisymm ?_ ?_
    · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
      exact Nat.dvd_trans (Nat.gcd_dvd_left _ _) ⟨2, (Nat.div_mul_cancel h2).symm⟩
    · have hn_eq : n = 2 * (n / 2) := by
        have := Nat.div_mul_cancel h2
        omega
      have hodd : Odd (Nat.gcd n c) := hc.of_dvd_nat (Nat.gcd_dvd_right n c)
      have hcop : Nat.Coprime (Nat.gcd n c) 2 := Nat.coprime_two_right.mpr hodd
      have hdvd : Nat.gcd n c ∣ 2 * (n / 2) := by
        rw [← hn_eq]
        exact Nat.gcd_dvd_left n c
      exact Nat.dvd_gcd (hcop.dvd_of_dvd_mul_left hdvd) (Nat.gcd_dvd_right n c)
  · rw [RawStepOfNotDvd 2 (2 * c + 1) c n h2]
    rw [show (2 * c + 1) * n + c = n + (2 * n + 1) * c by ring]
    exact Nat.gcd_add_mul_right_left c n (2 * n + 1)

/-- For odd `c` the divisor gcd with `c` is invariant under every iterate. -/
theorem RawStepTwoOddOffsetGcdIterate (c n k : ℕ) (hc : Odd c) :
    Nat.gcd (Iterate (NatRawStep 2 (2 * c + 1) c) k n) c = Nat.gcd n c := by
  induction k with
  | zero => simp [Iterate]
  | succ k ih =>
      rw [RawStepIterateSuccLast, RawStepTwoOddOffsetGcd c _ hc, ih]

/-- For odd `c > 1` the seed `c` never reaches `1`. -/
theorem RawStepTwoOddOffsetSeedNoCapture (c k : ℕ) (hc : Odd c) (hc1 : 1 < c) :
    Iterate (NatRawStep 2 (2 * c + 1) c) k c ≠ 1 := by
  intro h
  have hgcd := RawStepTwoOddOffsetGcdIterate c c k hc
  rw [h, Nat.gcd_one_left, Nat.gcd_self] at hgcd
  omega

/-- A bounded orbit of the odd-offset slice is eventually periodic in its own stratum. -/
theorem RawStepTwoOddOffsetStratumCycle (c n : ℕ) (hc : Odd c)
    (hb : ∃ M, ∀ k, Iterate (NatRawStep 2 (2 * c + 1) c) k n ≤ M) :
    ∃ y p, 0 < p ∧ Nat.gcd y c = Nat.gcd n c
      ∧ Iterate (NatRawStep 2 (2 * c + 1) c) p y = y := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨k, p, hp, hper⟩ := RawStepBoundedEventuallyPeriodic 2 (2 * c + 1) c n M hM
  refine ⟨Iterate (NatRawStep 2 (2 * c + 1) c) k n, p, hp, ?_, ?_⟩
  · exact RawStepTwoOddOffsetGcdIterate c n k hc
  · rw [← IterateAdd]
    exact hper

/-- If no positive seed of the odd-offset slice diverges, every divisor of `c` carries a
cycle. -/
theorem RawStepTwoOddOffsetManyCycles (c : ℕ) (hc : Odd c) (hc1 : 1 ≤ c)
    (hb : ∀ n, 1 ≤ n → ∃ M, ∀ k, Iterate (NatRawStep 2 (2 * c + 1) c) k n ≤ M) :
    ∀ g, g ∣ c → ∃ y p, 0 < p ∧ Nat.gcd y c = g
      ∧ Iterate (NatRawStep 2 (2 * c + 1) c) p y = y := by
  intro g hgc
  have hg1 : 1 ≤ g := Nat.pos_of_dvd_of_pos hgc (by omega)
  have hgcd : Nat.gcd g c = g := Nat.gcd_eq_left hgc
  obtain ⟨y, p, hp, hystratum, hper⟩ :=
    RawStepTwoOddOffsetStratumCycle c g hc (hb g hg1)
  exact ⟨y, p, hp, by rw [hystratum, hgcd], hper⟩

/-- Seven divides `8 ^ h - 1`. -/
theorem SevenDvdEightPowSubOne (h : ℕ) : 7 ∣ 8 ^ h - 1 := by
  induction h with
  | zero => simp
  | succ h ih =>
      have hpow : 8 ^ (h + 1) - 1 = 8 * (8 ^ h - 1) + 7 := by
        have : 1 ≤ 8 ^ h := Nat.one_le_pow h 8 (by norm_num)
        rw [pow_succ]
        omega
      rw [hpow]
      exact Nat.dvd_add (dvd_mul_of_dvd_right ih 8) (by norm_num)

/-- The offset `3 (8 ^ h - 1) / 7` of the second slice. -/
def CycleC (h : ℕ) : ℕ := 3 * (8 ^ h - 1) / 7

/-- The multiplier `2 c + 1` of the second slice. -/
def CycleQ (h : ℕ) : ℕ := 2 * CycleC h + 1

/-- The defining equation `7 c = 3 (8 ^ h - 1)` of the second slice. -/
theorem CycleCMulSeven (h : ℕ) : 7 * CycleC h = 3 * (8 ^ h - 1) := by
  rw [CycleC]
  exact Nat.mul_div_cancel' (dvd_mul_of_dvd_right (SevenDvdEightPowSubOne h) 3)

/-- The affine step of the seed `3` lands on `3 * 2 ^ (3 h)`. -/
theorem CycleQIdentity (h : ℕ) : 3 * CycleQ h + CycleC h = 3 * 2 ^ (3 * h) := by
  have h7 := CycleCMulSeven h
  have h8 : (8 : ℕ) ^ h = 2 ^ (3 * h) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, pow_mul]
  have hle : 1 ≤ 2 ^ (3 * h) := Nat.one_le_pow _ 2 (by norm_num)
  rw [h8] at h7
  simp only [CycleQ]
  omega

/-- The seed `3` takes the affine branch of the second slice. -/
theorem CycleAffineStep (h : ℕ) :
    NatRawStep 2 (CycleQ h) (CycleC h) 3 = 3 * 2 ^ (3 * h) := by
  rw [RawStepTwoOfOdd (CycleQ h) (CycleC h) 3 ⟨1, rfl⟩]
  have h := CycleQIdentity h
  omega

/-- The orbit of `3` under the second slice: `j + 1` steps give `3 * 2 ^ (3 h - j)`. -/
theorem CycleIterateFormula (h j : ℕ) (hj : j ≤ 3 * h) :
    Iterate (NatRawStep 2 (CycleQ h) (CycleC h)) (j + 1) 3 = 3 * 2 ^ (3 * h - j) := by
  induction j with
  | zero => simpa [Iterate] using CycleAffineStep h
  | succ j ih =>
      have hj' : j ≤ 3 * h := by omega
      have hprev := ih hj'
      have hexp : 1 ≤ 3 * h - j := by omega
      rw [RawStepIterateSuccLast, hprev]
      have hfact : 3 * 2 ^ (3 * h - j) = 2 * (3 * 2 ^ (3 * h - j - 1)) := by
        conv_lhs => rw [← Nat.sub_add_cancel hexp]
        rw [pow_succ]
        ring
      have h2 : 2 ∣ 3 * 2 ^ (3 * h - j) := ⟨3 * 2 ^ (3 * h - j - 1), hfact⟩
      rw [RawStepOfDvd 2 (CycleQ h) (CycleC h) _ h2, hfact,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      rw [show 3 * h - (j + 1) = 3 * h - j - 1 by omega]

/-- The seed `3` returns to itself after `3 h + 1` steps. -/
theorem CycleReturns (h : ℕ) :
    Iterate (NatRawStep 2 (CycleQ h) (CycleC h)) (3 * h + 1) 3 = 3 := by
  have h := CycleIterateFormula h (3 * h) (le_refl _)
  rw [Nat.sub_self, pow_zero, mul_one] at h
  exact h

/-- The return of the seed `3` is minimal. -/
theorem CyclePrimitive (h : ℕ) :
    ∀ j, 0 < j → j < 3 * h + 1 → Iterate (NatRawStep 2 (CycleQ h) (CycleC h)) j 3 ≠ 3 := by
  intro j hj hjlt
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i ≤ 3 * h := by omega
  have hiter := CycleIterateFormula h i hi
  have hpos : 1 ≤ 3 * h - i := by omega
  rw [hiter]
  have : 2 ≤ 2 ^ (3 * h - i) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (3 * h - i) := Nat.pow_le_pow_right (by norm_num) hpos
  omega

/-- The cycle of the seed `3` avoids `1`. -/
theorem CycleAvoidsOne (h : ℕ) :
    ∀ j, Iterate (NatRawStep 2 (CycleQ h) (CycleC h)) j 3 ≠ 1 := by
  intro j
  have hper := CycleReturns h
  have hp : 0 < 3 * h + 1 := by omega
  have hred : Iterate (NatRawStep 2 (CycleQ h) (CycleC h)) ((3 * h + 1) * (j / (3 * h + 1))) 3
      = 3 := by
    induction j / (3 * h + 1) with
    | zero => simp [Iterate]
    | succ a ih =>
        rw [show (3 * h + 1) * (a + 1) = (3 * h + 1) * a + (3 * h + 1) by ring]
        rw [IterateAdd, ih, hper]
  have hsplit : (3 * h + 1) * (j / (3 * h + 1)) + j % (3 * h + 1) = j := by
    have := Nat.div_add_mod j (3 * h + 1)
    omega
  have hmod : j % (3 * h + 1) < 3 * h + 1 := Nat.mod_lt _ hp
  rw [← hsplit, IterateAdd, hred]
  rcases eq_zero_or_pos (j % (3 * h + 1)) with hz | hpos
  · rw [hz]
    simp [Iterate]
  · obtain ⟨i, hi⟩ : ∃ i, j % (3 * h + 1) = i + 1 := ⟨j % (3 * h + 1) - 1, by omega⟩
    have hib : i ≤ 3 * h := by omega
    have hiter := CycleIterateFormula h i hib
    rw [hi, hiter]
    have hexp : 1 ≤ 3 * h - i := by omega
    have : 2 ≤ 2 ^ (3 * h - i) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (3 * h - i) := Nat.pow_le_pow_right (by norm_num) hexp
    omega

/-- The offset `(d - 1) (d ^ (k - 1) - 1)` of the full-residue-access slice. -/
def FullAccessC (d k : ℕ) : ℕ := (d - 1) * (d ^ (k - 1) - 1)

/-- The multiplier `(d - 1) d ^ (k - 1) + 1` of the full-residue-access slice. -/
def FullAccessQ (d k : ℕ) : ℕ := (d - 1) * d ^ (k - 1) + 1

/-- On the full-residue-access slice the multiplier exceeds `d` exactly by the offset. -/
theorem FullAccessQeq (d k : ℕ) (hd : 2 ≤ d) :
    FullAccessQ d k = d + FullAccessC d k := by
  have hsub : (d - 1) * d ^ (k - 1) = (d - 1) * (d ^ (k - 1) - 1) + (d - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    exact (Nat.sub_add_cancel
      (Nat.le_mul_of_pos_right (d - 1) (pow_pos (by omega : 0 < d) _))).symm
  simp only [FullAccessQ, FullAccessC]
  omega

/-- The affine step of `d - 1` lands on `(d - 1) d ^ k` on the full-residue slice. -/
theorem FullAccessIdentity (d k : ℕ) (hd : 2 ≤ d) (hk : 2 ≤ k) :
    FullAccessQ d k * (d - 1) + FullAccessC d k = (d - 1) * d ^ k := by
  have h1 : 1 ≤ d ^ (k - 1) := Nat.one_le_pow _ d (by omega)
  have hBX : d - 1 ≤ (d - 1) * d ^ (k - 1) :=
    Nat.le_mul_of_pos_right (d - 1) (by omega : 0 < d ^ (k - 1))
  have hB1 : d - 1 + 1 = d := Nat.sub_add_cancel (by omega)
  have hpow : d ^ k = d ^ (k - 1) * d := by
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk_eq]
    rw [pow_succ]
  have hExpand : ((d - 1) * d ^ (k - 1) + 1) * (d - 1)
      = (d - 1) * d ^ (k - 1) * (d - 1) + (d - 1) := by ring
  have hSub : (d - 1) * (d ^ (k - 1) - 1) = (d - 1) * d ^ (k - 1) - (d - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  calc FullAccessQ d k * (d - 1) + FullAccessC d k
      = ((d - 1) * d ^ (k - 1) * (d - 1) + (d - 1))
          + ((d - 1) * d ^ (k - 1) - (d - 1)) := by rw [FullAccessQ, FullAccessC, hExpand, hSub]
    _ = (d - 1) * d ^ (k - 1) * (d - 1) + (d - 1) * d ^ (k - 1) := by omega
    _ = (d - 1) * d ^ (k - 1) * ((d - 1) + 1) := by ring
    _ = (d - 1) * d ^ (k - 1) * d := by rw [hB1]
    _ = (d - 1) * (d ^ (k - 1) * d) := by ring
    _ = (d - 1) * d ^ k := by rw [← hpow]

/-- `d` does not divide `d - 1`. -/
theorem FullAccessNotDvd (d : ℕ) (hd : 2 ≤ d) : ¬ d ∣ d - 1 := by
  intro h
  have hle : d ≤ d - 1 := Nat.le_of_dvd (by omega) h
  omega

/-- A positive power of `d` is divisible by `d`. -/
theorem NatPowDvdSelfPow (d n : ℕ) (h : 1 ≤ n) : d ∣ d ^ n := by
  obtain ⟨e, he⟩ : ∃ e, n = e + 1 := ⟨n - 1, by omega⟩
  exact ⟨d ^ e, by rw [he, pow_succ']⟩

/-- The orbit of `d - 1`: `j + 1` steps give `(d - 1) d ^ (k - j)`. -/
theorem FullAccessIterateFormula (d k j : ℕ) (hd : 2 ≤ d) (hk : 2 ≤ k) (hj : j ≤ k) :
    Iterate (NatRawStep d (FullAccessQ d k) (FullAccessC d k)) (j + 1) (d - 1)
      = (d - 1) * d ^ (k - j) := by
  induction j with
  | zero =>
      change NatRawStep d (FullAccessQ d k) (FullAccessC d k) (d - 1)
        = (d - 1) * d ^ k
      rw [RawStepOfNotDvd d _ _ _ (FullAccessNotDvd d hd)]
      exact FullAccessIdentity d k hd hk
  | succ j ih =>
      have hj' : j ≤ k := by omega
      have hprev := ih hj'
      have hexp : 1 ≤ k - j := by omega
      rw [RawStepIterateSuccLast, hprev]
      have hdvd : d ∣ (d - 1) * d ^ (k - j) :=
        dvd_mul_of_dvd_right (NatPowDvdSelfPow d (k - j) hexp) (d - 1)
      rw [RawStepOfDvd d _ _ _ hdvd]
      have hfact : (d - 1) * d ^ (k - j) = d * ((d - 1) * d ^ (k - j - 1)) := by
        conv_lhs => rw [← Nat.sub_add_cancel hexp]
        rw [pow_succ']
        ring
      rw [hfact, Nat.mul_div_cancel_left _ (by omega : 0 < d)]
      rw [show k - (j + 1) = k - j - 1 by omega]

/-- The seed `d - 1` returns to itself after `k + 1` steps. -/
theorem FullAccessReturns (d k : ℕ) (hd : 2 ≤ d) (hk : 2 ≤ k) :
    Iterate (NatRawStep d (FullAccessQ d k) (FullAccessC d k)) (k + 1) (d - 1) = d - 1 := by
  have h := FullAccessIterateFormula d k k hd hk (le_refl k)
  rw [h]
  simp

/-- The return of the seed `d - 1` is minimal. -/
theorem FullAccessPrimitive (d k : ℕ) (hd : 2 ≤ d) (hk : 2 ≤ k) :
    ∀ j, 0 < j → j < k + 1
      → Iterate (NatRawStep d (FullAccessQ d k) (FullAccessC d k)) j (d - 1) ≠ d - 1 := by
  intro j hj hjlt
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i ≤ k := by omega
  have h := FullAccessIterateFormula d k i hd hk hi
  have hexp : 1 ≤ k - i := by omega
  rw [h]
  have hdvd : d ∣ (d - 1) * d ^ (k - i) :=
    dvd_mul_of_dvd_right (NatPowDvdSelfPow d (k - i) hexp) (d - 1)
  intro heq
  exact FullAccessNotDvd d hd (heq ▸ hdvd)

/-- The cycle of the seed `d - 1` avoids `1` when `d ≥ 3`. -/
theorem FullAccessAvoidsOne (d k : ℕ) (hd : 3 ≤ d) (hk : 2 ≤ k) :
    ∀ j, Iterate (NatRawStep d (FullAccessQ d k) (FullAccessC d k)) j (d - 1) ≠ 1 := by
  intro j
  have hper := FullAccessReturns d k (by omega) hk
  have hp : 0 < k + 1 := by omega
  have hred : Iterate (NatRawStep d (FullAccessQ d k) (FullAccessC d k))
      ((k + 1) * (j / (k + 1))) (d - 1) = d - 1 := by
    induction j / (k + 1) with
    | zero => simp [Iterate]
    | succ a ih =>
        rw [show (k + 1) * (a + 1) = (k + 1) * a + (k + 1) by ring]
        rw [IterateAdd, ih, hper]
  have hsplit : (k + 1) * (j / (k + 1)) + j % (k + 1) = j := by
    have := Nat.div_add_mod j (k + 1)
    omega
  have hmod : j % (k + 1) < k + 1 := Nat.mod_lt _ hp
  rw [← hsplit, IterateAdd, hred]
  rcases eq_zero_or_pos (j % (k + 1)) with hz | hpos
  · rw [hz]
    simp [Iterate]
    omega
  · obtain ⟨i, hi⟩ : ∃ i, j % (k + 1) = i + 1 := ⟨j % (k + 1) - 1, by omega⟩
    have hib : i ≤ k := by omega
    have hiter := FullAccessIterateFormula d k i (by omega) hk hib
    rw [hi, hiter]
    have hle : 1 ≤ d - 1 := by omega
    have hexp : 1 ≤ k - i := by omega
    have hpow : 1 < d ^ (k - i) := by
      calc 1 < d ^ 1 := by
            rw [pow_one]
            omega
        _ ≤ d ^ (k - i) := Nat.pow_le_pow_right (by omega) hexp
    have hprod : 1 < (d - 1) * d ^ (k - i) := by
      have hle1 : 1 * d ^ (k - i) ≤ (d - 1) * d ^ (k - i) :=
        Nat.mul_le_mul hle (le_refl _)
      have hlt1 : 1 < 1 * d ^ (k - i) := by simpa using hpow
      exact lt_of_lt_of_le hlt1 hle1
    exact ne_of_gt hprod

/-- The classical cycle `1 ↦ 4 ↦ 2 ↦ 1` is the case `d = k = 2` of the slice. -/
theorem FullAccessClassicalInstance :
    Iterate (NatRawStep 2 (FullAccessQ 2 2) (FullAccessC 2 2)) 3 1 = 1
      ∧ NatRawStep 2 (FullAccessQ 2 2) (FullAccessC 2 2) 1 = 4 := by
  constructor <;> decide

/-- Zero is fixed by every raw map. -/
theorem RawStepZero (d q c : ℕ) : NatRawStep d q c 0 = 0 := by
  rw [RawStepOfDvd d q c 0 (dvd_zero d), Nat.zero_div]

/-- On the intersection slice an affine step cannot be followed by divisions down to a
power of `d`. -/
theorem RawStepIntersectionPredecessor (d x m : ℕ) (hd : 3 ≤ d)
    (h : NatRawStep d (d + 1) (d - 1) x = d ^ m) : x = d ^ (m + 1) := by
  by_cases hdvd : d ∣ x
  · rw [RawStepOfDvd d (d + 1) (d - 1) x hdvd] at h
    have hx_eq : x = d * (x / d) := by
      rw [Nat.mul_comm]
      exact (Nat.div_mul_cancel hdvd).symm
    rw [hx_eq, h, pow_succ']
  · rw [RawStepOfNotDvd d (d + 1) (d - 1) x hdvd] at h
    have hd1 : (((d + 1 : ℕ)) : ZMod (d + 1)) = 0 := ZMod.natCast_self (d + 1)
    have hdneg : ((d : ZMod (d + 1))) = -1 := by
      have h1 : ((d : ZMod (d + 1)) + 1) = 0 := by
        have h2 := hd1
        rw [Nat.cast_add, Nat.cast_one] at h2
        exact h2
      exact eq_neg_of_add_eq_zero_left h1
    have hcast : (((d ^ m : ℕ)) : ZMod (d + 1)) = (-1 : ZMod (d + 1)) ^ m := by
      rw [Nat.cast_pow, hdneg]
    have hleft : ((((d + 1) * x + (d - 1) : ℕ)) : ZMod (d + 1)) = -2 := by
      have hsub : (((d - 1 : ℕ)) : ZMod (d + 1)) = ((d : ZMod (d + 1)) - 1) :=
        Nat.cast_sub (by omega)
      rw [Nat.cast_add, Nat.cast_mul, hsub, hdneg, hd1]
      ring
    have heq : (-2 : ZMod (d + 1)) = (-1 : ZMod (d + 1)) ^ m := by
      rw [← hcast, ← hleft, h]
    rcases Nat.even_or_odd m with hev | hod
    · have hone : (-1 : ZMod (d + 1)) ^ m = 1 := Even.neg_one_pow hev
      rw [hone] at heq
      have h2 : (((2 : ℕ)) : ZMod (d + 1)) = ((d : ℕ) : ZMod (d + 1)) := by
        have hneg := congrArg (fun t : ZMod (d + 1) => -t) heq
        rw [hdneg]
        simpa using hneg
      have hmod := (ZMod.natCast_eq_natCast_iff' 2 d (d + 1)).mp h2
      have h2' : 2 % (d + 1) = 2 := Nat.mod_eq_of_lt (by omega)
      have hd' : d % (d + 1) = d := Nat.mod_eq_of_lt (by omega)
      omega
    · have hone : (-1 : ZMod (d + 1)) ^ m = -1 := Odd.neg_one_pow hod
      rw [hone] at heq
      have h2 : (((2 : ℕ)) : ZMod (d + 1)) = ((1 : ℕ) : ZMod (d + 1)) := by
        have hneg := congrArg (fun t : ZMod (d + 1) => -t) heq
        simpa using hneg
      have hmod := (ZMod.natCast_eq_natCast_iff' 2 1 (d + 1)).mp h2
      have h2' : 2 % (d + 1) = 2 := Nat.mod_eq_of_lt (by omega)
      have h1' : 1 % (d + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      omega

/-- On the intersection slice, `k` steps from `x` land on `d ^ t` only from `d ^ (k + t)`. -/
theorem RawStepIntersectionIteratePow (d k t x : ℕ) (hd : 3 ≤ d) (hx : 1 ≤ x)
    (h : Iterate (NatRawStep d (d + 1) (d - 1)) k x = d ^ t) : x = d ^ (k + t) := by
  induction k generalizing x t with
  | zero => simpa [Iterate] using h
  | succ k ih =>
      have hstep : NatRawStep d (d + 1) (d - 1)
          (Iterate (NatRawStep d (d + 1) (d - 1)) k x) = d ^ t := h
      have hkey : Iterate (NatRawStep d (d + 1) (d - 1)) k x = d ^ (t + 1) :=
        RawStepIntersectionPredecessor d _ t hd hstep
      have hxpow := ih (t + 1) x hx hkey
      rw [hxpow]
      congr 1
      omega

/-- On the intersection slice, `x` reaches `1` only from a power of `d`. -/
theorem RawStepIntersectionReachesOne (d k x : ℕ) (hd : 3 ≤ d) (hx : 1 ≤ x)
    (h : Iterate (NatRawStep d (d + 1) (d - 1)) k x = 1) : x = d ^ k := by
  have h := RawStepIntersectionIteratePow d k 0 x hd hx (by simpa using h)
  simpa using h

/-- On the intersection slice the seeds that reach `1` are exactly the powers of `d`. -/
theorem RawStepIntersectionReachesOneIff (d x : ℕ) (hd : 3 ≤ d) (hx : 1 ≤ x) :
    (∃ k, Iterate (NatRawStep d (d + 1) (d - 1)) k x = 1) ↔ ∃ j, x = d ^ j := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, RawStepIntersectionReachesOne d k x hd hx hk⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, RawStepPowIterate d (d + 1) (d - 1) j (by omega)⟩

/-- On the intersection slice no positive power of the clock returns to `1`. -/
theorem RawStepIntersectionNoReturnToOne (d : ℕ) (hd : 3 ≤ d) :
    ∀ k, 0 < k → Iterate (NatRawStep d (d + 1) (d - 1)) k 1 ≠ 1 := by
  intro k hk hcon
  have hp := RawStepIntersectionReachesOne d k 1 hd (by norm_num) hcon
  have hpow : d ^ k = d ^ 0 := by
    rw [pow_zero]
    exact hp.symm
  have := Nat.pow_right_injective (by omega : 2 ≤ d) hpow
  omega

end GeneralizedCollatz
