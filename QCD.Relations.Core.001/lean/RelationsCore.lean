-- SPDX-License-Identifier: CC-BY-4.0
import GeneralizedCollatz
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat

/-!
Return-core dynamics of the offset map with multiplier `d - 1`

  `CoreMap d c n = n / d` for `d ∣ n`, and `CoreMap d c n = (d - 1) * n + c` otherwise,

the case `q = d - 1` of the generalized Collatz map.  States divisible by `d` and
states congruent to `c` modulo `d` are exactly the states from which one original
instruction divides by `d`; the state after that division is the return map
`CoreReturn`.  The return map strictly decreases above the core `{1, ..., c}` and
maps the core into itself, so every positive orbit either leaves the domain
(and then grows strictly at every instruction forever) or returns to a periodic
orbit inside the core.  Every return step is realized by one or two original
instructions, so a return cycle in the domain expands to a raw cycle.  For the
corner case `c = d + 1` the only return cycle in the domain core is the fixed
point `d + 1`, whose expansion is the raw cycle `d + 1 ↦ d * (d + 1) ↦ d + 1`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The offset map with multiplier `d - 1`: divide a multiple of `d`, otherwise apply
the affine branch. -/
def CoreMap (d c n : ℕ) : ℕ := if d ∣ n then n / d else (d - 1) * n + c

/-- The states from which one original instruction divides by `d`. -/
def CoreDomain (d c n : ℕ) : Prop := d ∣ n ∨ n % d = c % d

/-- The state reached after the pending division by `d`. -/
def CoreReturn (d c n : ℕ) : ℕ := if d ∣ n then n / d else ((d - 1) * n + c) / d

/-- A successor iterate may execute its first instruction before the remaining ones. -/
theorem CoreIterateSucc {α : Type*} (f : α → α) (k : ℕ) (x : α) :
    Iterate f (k + 1) x = Iterate f k (f x) := by
  rw [show k + 1 = 1 + k by omega, IterateAdd]
  rfl

/-- A multiple of `d` is divided immediately. -/
theorem CoreMapOfDvd (d c n : ℕ) (h : d ∣ n) : CoreMap d c n = n / d := by
  rw [CoreMap, if_pos h]

/-- A non-multiple of `d` takes the affine branch. -/
theorem CoreMapOfNotDvd (d c n : ℕ) (h : ¬ d ∣ n) : CoreMap d c n = (d - 1) * n + c := by
  rw [CoreMap, if_neg h]

/-- A free affine step strictly increases a positive state. -/
theorem CoreMapFreeIncrease (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c) (h : ¬ d ∣ n) :
    n < CoreMap d c n := by
  rw [CoreMapOfNotDvd d c n h]
  have hone : 1 ≤ d - 1 := by omega
  have hmul : n ≤ (d - 1) * n := by
    calc n = 1 * n := (one_mul n).symm
      _ ≤ (d - 1) * n := Nat.mul_le_mul_right n hone
  omega

/-- A divisible state strictly decreases after division. -/
theorem CoreMapDivisibleDecrease (d c n : ℕ) (hd : 2 ≤ d) (hpos : 0 < n) (h : d ∣ n) :
    CoreMap d c n < n := by
  rw [CoreMapOfDvd d c n h]
  exact Nat.div_lt_self hpos (by omega)

/-- The residue condition of the domain makes the affine step land on a multiple of `d`. -/
theorem CoreDomainDivisible (d c n : ℕ) (hd : 0 < d) (h : n % d = c % d) :
    d ∣ (d - 1) * n + c := by
  rw [← ZMod.natCast_eq_zero_iff ((d - 1) * n + c) d]
  push_cast
  have hnc : ((n : ℕ) : ZMod d) = ((c : ℕ) : ZMod d) :=
    (ZMod.natCast_eq_natCast_iff' n c d).mpr h
  have hpred : ((d - 1 : ℕ) : ZMod d) = -1 := by
    rw [Nat.cast_pred hd, ZMod.natCast_self]
    ring
  rw [hpred, hnc]
  ring

/-- The affine branch in the ring `ZMod d` is the reflection `n ↦ c - n`. -/
theorem CoreMapCast (d c n : ℕ) (hd : 0 < d) (h : ¬ d ∣ n) :
    ((CoreMap d c n : ℕ) : ZMod d) = -((n : ℕ) : ZMod d) + ((c : ℕ) : ZMod d) := by
  rw [CoreMapOfNotDvd d c n h]
  push_cast
  have hpred : ((d - 1 : ℕ) : ZMod d) = -1 := by
    rw [Nat.cast_pred hd, ZMod.natCast_self]
    ring
  rw [hpred]
  ring

/-- For a state that is not a multiple of `d`, the affine step is divisible exactly when the
state is congruent to `c`. -/
theorem CoreMapDivisibleIff (d c n : ℕ) (hd : 0 < d) (h : ¬ d ∣ n) :
    d ∣ CoreMap d c n ↔ n % d = c % d := by
  rw [← ZMod.natCast_eq_zero_iff (CoreMap d c n) d, CoreMapCast d c n hd h, neg_add_eq_zero,
    ZMod.natCast_eq_natCast_iff' n c d]

/-- For a state that is not a multiple of `d`, the affine step is again congruent to `c`
exactly when the state is a multiple of `d`. -/
theorem CoreMapResidueIff (d c n : ℕ) (hd : 0 < d) (h : ¬ d ∣ n) :
    CoreMap d c n % d = c % d ↔ d ∣ n := by
  rw [← ZMod.natCast_eq_natCast_iff' (CoreMap d c n) c d, CoreMapCast d c n hd h]
  have hiff : (-((n : ℕ) : ZMod d) + ((c : ℕ) : ZMod d) = ((c : ℕ) : ZMod d)) ↔
      ((n : ℕ) : ZMod d) = 0 := by
    constructor
    · intro hh
      have hzero : -((n : ℕ) : ZMod d) = 0 :=
        add_right_cancel (by simpa using hh : -((n : ℕ) : ZMod d) + ((c : ℕ) : ZMod d) =
          (0 : ZMod d) + ((c : ℕ) : ZMod d))
      exact neg_eq_zero.mp hzero
    · intro hh
      rw [hh]
      simp
  rw [hiff, ZMod.natCast_eq_zero_iff n d]

/-- A state outside the domain never enters the domain. -/
theorem CoreMapNotDomain (d c n : ℕ) (hd : 0 < d) (h : ¬ CoreDomain d c n) :
    ¬ CoreDomain d c (CoreMap d c n) := by
  have hn : ¬ d ∣ n := fun hdvd => h (Or.inl hdvd)
  have hres : ¬ n % d = c % d := fun hmod => h (Or.inr hmod)
  intro hdom
  rcases hdom with hdvd | hmod
  · exact hres ((CoreMapDivisibleIff d c n hd hn).mp hdvd)
  · exact hn ((CoreMapResidueIff d c n hd hn).mp hmod)

/-- Every iterate of a state outside the domain is outside the domain. -/
theorem CoreTrapNotDomain (d c n : ℕ) (hd : 0 < d) (h : ¬ CoreDomain d c n) (k : ℕ) :
    ¬ CoreDomain d c (Iterate (CoreMap d c) k n) := by
  induction k with
  | zero => { simpa [Iterate] using h }
  | succ k ih =>
    {
      rw [show Iterate (CoreMap d c) (k + 1) n = CoreMap d c (Iterate (CoreMap d c) k n) from rfl]
      exact CoreMapNotDomain d c _ hd ih
    }

/-- A trapped state strictly increases at every instruction. -/
theorem CoreTrapStrictMono (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c) (h : ¬ CoreDomain d c n)
    (k : ℕ) :
    Iterate (CoreMap d c) k n < Iterate (CoreMap d c) (k + 1) n := by
  rw [show Iterate (CoreMap d c) (k + 1) n = CoreMap d c (Iterate (CoreMap d c) k n) from rfl]
  exact CoreMapFreeIncrease d c _ hd hc
    (fun hdvd => CoreTrapNotDomain d c n (by omega) h k (Or.inl hdvd))

/-- A trapped orbit grows by at least one at every instruction. -/
theorem CoreTrapGrowth (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c) (h : ¬ CoreDomain d c n) :
    ∀ k, n + k ≤ Iterate (CoreMap d c) k n := by
  intro k
  induction k with
  | zero => { simp [Iterate] }
  | succ k ih =>
    {
      have hstep := CoreTrapStrictMono d c n hd hc h k
      omega
    }

/-- A trapped orbit is unbounded. -/
theorem CoreTrapUnbounded (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c) (h : ¬ CoreDomain d c n)
    (bound : ℕ) :
    ∃ k, bound < Iterate (CoreMap d c) k n :=
  ⟨bound + 1,
    lt_of_lt_of_le (by omega) (CoreTrapGrowth d c n hd hc h (bound + 1))⟩

/-- A multiple of `d` returns by dividing. -/
theorem CoreReturnOfDvd (d c n : ℕ) (h : d ∣ n) : CoreReturn d c n = n / d := by
  rw [CoreReturn, if_pos h]

/-- A non-multiple of `d` returns by the affine step followed by the division. -/
theorem CoreReturnOfNotDvd (d c n : ℕ) (h : ¬ d ∣ n) :
    CoreReturn d c n = ((d - 1) * n + c) / d := by
  rw [CoreReturn, if_neg h]

/-- At a multiple of `d` the return is realized by one instruction. -/
theorem CoreReturnRealizeDvd (d c n : ℕ) (h : d ∣ n) :
    Iterate (CoreMap d c) 1 n = CoreReturn d c n := by
  rw [show Iterate (CoreMap d c) 1 n = CoreMap d c n from rfl, CoreMapOfDvd d c n h,
    CoreReturnOfDvd d c n h]

/-- At a residue-`c` state the return is realized by two instructions. -/
theorem CoreReturnRealizeMod (d c n : ℕ) (hd : 0 < d) (h : ¬ d ∣ n) (hres : n % d = c % d) :
    Iterate (CoreMap d c) 2 n = CoreReturn d c n := by
  have hdiv : d ∣ (d - 1) * n + c := CoreDomainDivisible d c n hd hres
  rw [show Iterate (CoreMap d c) 2 n = CoreMap d c (CoreMap d c n) from rfl,
    CoreMapOfNotDvd d c n h, CoreMapOfDvd d c _ hdiv, CoreReturnOfNotDvd d c n h]

/-- The two instructions at a residue-`c` state compose to the return map. -/
theorem CoreReturnRealizeModCompose (d c n : ℕ) (hd : 0 < d) (h : ¬ d ∣ n)
    (hres : n % d = c % d) :
    CoreMap d c (CoreMap d c n) = CoreReturn d c n := by
  have hdiv : d ∣ (d - 1) * n + c := CoreDomainDivisible d c n hd hres
  rw [CoreMapOfNotDvd d c n h, CoreMapOfDvd d c _ hdiv, CoreReturnOfNotDvd d c n h]

/-- Above the core the return map strictly decreases. -/
theorem CoreReturnDecrease (d c n : ℕ) (hd : 2 ≤ d) (hn : c < n) : CoreReturn d c n < n := by
  by_cases h : d ∣ n
  · rw [CoreReturnOfDvd d c n h]
    exact Nat.div_lt_self (by omega) (by omega)
  · rw [CoreReturnOfNotDvd d c n h, Nat.div_lt_iff_lt_mul (by omega : 0 < d)]
    have hsub : (d - 1) * n = d * n - n := by rw [Nat.sub_mul, one_mul]
    rw [hsub, Nat.mul_comm n d]
    have hle : n ≤ d * n := Nat.le_mul_of_pos_left n (by omega)
    omega

/-- Positive states have positive returns. -/
theorem CoreReturnPositive (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c) (h1 : 1 ≤ n) :
    1 ≤ CoreReturn d c n := by
  by_cases h : d ∣ n
  · rw [CoreReturnOfDvd d c n h, Nat.le_div_iff_mul_le (by omega : 0 < d)]
    simpa using Nat.le_of_dvd (by omega) h
  · rw [CoreReturnOfNotDvd d c n h, Nat.le_div_iff_mul_le (by omega : 0 < d)]
    have hone : 1 ≤ d - 1 := by omega
    have hmul : d - 1 ≤ (d - 1) * n := by
      calc d - 1 = (d - 1) * 1 := (mul_one _).symm
        _ ≤ (d - 1) * n := Nat.mul_le_mul_left _ h1
    omega

/-- Every iterate of a positive state is positive. -/
theorem CoreReturnIteratePositive (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c) (h1 : 1 ≤ n) :
    ∀ k, 1 ≤ Iterate (CoreReturn d c) k n := by
  intro k
  induction k with
  | zero => { simpa [Iterate] using h1 }
  | succ k ih =>
    {
      rw [show Iterate (CoreReturn d c) (k + 1) n =
        CoreReturn d c (Iterate (CoreReturn d c) k n) from rfl]
      exact CoreReturnPositive d c _ hd hc ih
    }

/-- The return map maps the core into itself. -/
theorem CoreReturnCore (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c) (h1 : 1 ≤ n) (h2 : n ≤ c) :
    1 ≤ CoreReturn d c n ∧ CoreReturn d c n ≤ c := by
  refine ⟨CoreReturnPositive d c n hd hc h1, ?_⟩
  by_cases h : d ∣ n
  · rw [CoreReturnOfDvd d c n h]
    exact le_trans (Nat.div_le_self n d) h2
  · rw [CoreReturnOfNotDvd d c n h]
    have hmul : (d - 1) * n ≤ (d - 1) * c := Nat.mul_le_mul_left _ h2
    have hsum : (d - 1) * n + c ≤ d * c := by
      have hsub : (d - 1) * c + c = d * c := by
        rw [Nat.sub_mul, one_mul]
        exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left c (by omega : 0 < d))
      omega
    calc ((d - 1) * n + c) / d ≤ (d * c) / d := Nat.div_le_div_right hsum
      _ = c := Nat.mul_div_cancel_left c (by omega : 0 < d)

/-- Once inside the core the return map stays inside it. -/
theorem CoreReturnIterateCore (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c) (h1 : 1 ≤ n)
    (h2 : n ≤ c) :
    ∀ k, 1 ≤ Iterate (CoreReturn d c) k n ∧ Iterate (CoreReturn d c) k n ≤ c := by
  intro k
  induction k with
  | zero => { simpa [Iterate] using ⟨h1, h2⟩ }
  | succ k ih =>
    {
      rw [show Iterate (CoreReturn d c) (k + 1) n =
        CoreReturn d c (Iterate (CoreReturn d c) k n) from rfl]
      exact CoreReturnCore d c _ hd hc ih.1 ih.2
    }

/-- Every positive state reaches the core. -/
theorem CoreReturnReachesCore (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c) (h1 : 1 ≤ n) :
    ∃ k, Iterate (CoreReturn d c) k n ≤ c := by
  revert h1
  refine Nat.strong_induction_on n ?_
  intro n ih h1
  by_cases hn : n ≤ c
  · exact ⟨0, by simpa [Iterate] using hn⟩
  · have hlt : c < n := by omega
    have hdec := CoreReturnDecrease d c n hd hlt
    have hpos := CoreReturnPositive d c n hd hc h1
    obtain ⟨k, hk⟩ := ih (CoreReturn d c n) hdec hpos
    refine ⟨k + 1, ?_⟩
    rw [CoreIterateSucc (CoreReturn d c) k n]
    exact hk

/-- Every positive return orbit is eventually periodic, with the period exhibited in the core. -/
theorem CoreReturnEventuallyPeriodic (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c) (h1 : 1 ≤ n) :
    ∃ k p, 0 < p ∧ Iterate (CoreReturn d c) k n ∈ Finset.Icc 1 c ∧
      ∀ s, Iterate (CoreReturn d c) (k + s + p) n =
        Iterate (CoreReturn d c) (k + s) n := by
  obtain ⟨k, hk⟩ := CoreReturnReachesCore d c n hd hc h1
  have hkpos : 1 ≤ Iterate (CoreReturn d c) k n := CoreReturnIteratePositive d c n hd hc h1 k
  have hcore := CoreReturnIterateCore d c (Iterate (CoreReturn d c) k n) hd hc hkpos hk
  have hmem : ∀ j ∈ Finset.range (c + 1),
      Iterate (CoreReturn d c) j (Iterate (CoreReturn d c) k n) ∈ Finset.Icc 1 c :=
    fun j _ => Finset.mem_Icc.mpr (hcore j)
  have hcard : (Finset.Icc 1 c).card < (Finset.range (c + 1)).card := by
    rw [Nat.card_Icc, Finset.card_range]
    omega
  obtain ⟨i, -, j, -, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmem
  have hshift : ∀ t, Iterate (CoreReturn d c) (j + t) (Iterate (CoreReturn d c) k n) =
      Iterate (CoreReturn d c) (i + t) (Iterate (CoreReturn d c) k n) := by
    intro t
    calc Iterate (CoreReturn d c) (j + t) (Iterate (CoreReturn d c) k n)
        = Iterate (CoreReturn d c) t
            (Iterate (CoreReturn d c) j (Iterate (CoreReturn d c) k n)) :=
          IterateAdd (CoreReturn d c) j t _
      _ = Iterate (CoreReturn d c) t
            (Iterate (CoreReturn d c) i (Iterate (CoreReturn d c) k n)) := by rw [heq]
      _ = Iterate (CoreReturn d c) (i + t) (Iterate (CoreReturn d c) k n) :=
          (IterateAdd (CoreReturn d c) i t _).symm
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · refine ⟨k + i, j - i, by omega, ?_, fun s => ?_⟩
    · rw [IterateAdd (CoreReturn d c) k i n]
      exact Finset.mem_Icc.mpr (hcore i)
    have h1' : k + i + s + (j - i) = k + (i + s + (j - i)) := by omega
    have h2' : k + i + s = k + (i + s) := by omega
    have hsj : i + s + (j - i) = j + s := by omega
    rw [h1', h2', IterateAdd (CoreReturn d c) k (i + s + (j - i)) n,
      IterateAdd (CoreReturn d c) k (i + s) n, hsj, hshift s]
  · refine ⟨k + j, i - j, by omega, ?_, fun s => ?_⟩
    · rw [IterateAdd (CoreReturn d c) k j n]
      exact Finset.mem_Icc.mpr (hcore j)
    have h1' : k + j + s + (i - j) = k + (j + s + (i - j)) := by omega
    have h2' : k + j + s = k + (j + s) := by omega
    have hsj : j + s + (i - j) = i + s := by omega
    rw [h1', h2', IterateAdd (CoreReturn d c) k (j + s + (i - j)) n,
      IterateAdd (CoreReturn d c) k (j + s) n, hsj, hshift s]

/-- A domain return orbit of length `p` is realized by the original map within `2 * p`
instructions. -/
theorem CoreReturnRawRealization (d c p x : ℕ) (hd : 2 ≤ d) (_hx : 1 ≤ x)
    (hdom : ∀ k, k < p → CoreDomain d c (Iterate (CoreReturn d c) k x)) :
    ∃ j, p ≤ j ∧ j ≤ 2 * p ∧ Iterate (CoreMap d c) j x = Iterate (CoreReturn d c) p x := by
  induction p with
  | zero => { exact ⟨0, le_rfl, by simp, by simp [Iterate]⟩ }
  | succ p ih =>
    {
      obtain ⟨j, hj1, hj2, hjx⟩ := ih (fun k hk => hdom k (by omega))
      have hdomp := hdom p (by omega)
      rcases hdomp with hdvd | hres
      · refine ⟨j + 1, by omega, by omega, ?_⟩
        calc Iterate (CoreMap d c) (j + 1) x
            = CoreMap d c (Iterate (CoreMap d c) j x) := rfl
          _ = CoreMap d c (Iterate (CoreReturn d c) p x) := by rw [hjx]
          _ = CoreReturn d c (Iterate (CoreReturn d c) p x) := by
                rw [CoreMapOfDvd d c _ hdvd, CoreReturnOfDvd d c _ hdvd]
          _ = Iterate (CoreReturn d c) (p + 1) x := rfl
      · by_cases hdy : d ∣ Iterate (CoreReturn d c) p x
        · refine ⟨j + 1, by omega, by omega, ?_⟩
          calc Iterate (CoreMap d c) (j + 1) x
              = CoreMap d c (Iterate (CoreMap d c) j x) := rfl
            _ = CoreMap d c (Iterate (CoreReturn d c) p x) := by rw [hjx]
            _ = CoreReturn d c (Iterate (CoreReturn d c) p x) := by
                  rw [CoreMapOfDvd d c _ hdy, CoreReturnOfDvd d c _ hdy]
            _ = Iterate (CoreReturn d c) (p + 1) x := rfl
        · refine ⟨j + 2, by omega, by omega, ?_⟩
          calc Iterate (CoreMap d c) (j + 2) x
              = CoreMap d c (CoreMap d c (Iterate (CoreMap d c) j x)) := rfl
            _ = CoreMap d c (CoreMap d c (Iterate (CoreReturn d c) p x)) := by rw [hjx]
            _ = CoreReturn d c (Iterate (CoreReturn d c) p x) :=
                  CoreReturnRealizeModCompose d c _ (by omega) hdy hres
            _ = Iterate (CoreReturn d c) (p + 1) x := rfl
    }

/-- A return cycle whose values lie in the domain expands to a raw cycle within twice as
many instructions. -/
theorem CoreReturnCycleRaw (d c p x : ℕ) (hd : 2 ≤ d) (hp : 0 < p) (hx : 1 ≤ x)
    (hdom : ∀ k, k < p → CoreDomain d c (Iterate (CoreReturn d c) k x))
    (hcycle : Iterate (CoreReturn d c) p x = x) :
    ∃ j, 0 < j ∧ j ≤ 2 * p ∧ Iterate (CoreMap d c) j x = x := by
  obtain ⟨j, hj1, hj2, hjx⟩ := CoreReturnRawRealization d c p x hd hx hdom
  exact ⟨j, by omega, hj2, by rw [hjx, hcycle]⟩

/-- Either some iterate leaves the domain, and from there the orbit grows without bound, or
every iterate stays in the domain. -/
theorem CoreMapDichotomy (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c) (_h1 : 1 ≤ n) :
    (∃ k, ¬ CoreDomain d c (Iterate (CoreMap d c) k n) ∧
      ∀ bound, ∃ j, bound < Iterate (CoreMap d c) (k + j) n) ∨
    (∀ k, CoreDomain d c (Iterate (CoreMap d c) k n)) := by
  by_cases h : ∀ k, CoreDomain d c (Iterate (CoreMap d c) k n)
  · exact Or.inr h
  · obtain ⟨k, hk⟩ := not_forall.mp h
    refine Or.inl ⟨k, hk, fun bound => ?_⟩
    obtain ⟨j, hj⟩ := CoreTrapUnbounded d c (Iterate (CoreMap d c) k n) hd hc hk bound
    exact ⟨j, by rw [IterateAdd (CoreMap d c) k j n]; exact hj⟩

/-- For `d ≥ 2` the successor of `d` is not divisible by `d`. -/
theorem CoreCornerNotDvd (d : ℕ) (hd : 2 ≤ d) : ¬ d ∣ d + 1 := by
  intro h
  have h1 : d ∣ 1 := by
    simpa using Nat.dvd_sub h (dvd_refl d)
  have := Nat.le_of_dvd Nat.one_pos h1
  omega

/-- The corner state `d + 1` is fixed by the corner return map. -/
theorem CoreReturnCornerSelf (d : ℕ) (hd : 2 ≤ d) : CoreReturn d (d + 1) (d + 1) = d + 1 := by
  have hnd := CoreCornerNotDvd d hd
  rw [CoreReturnOfNotDvd d (d + 1) (d + 1) hnd]
  have hsum : (d - 1) * (d + 1) + (d + 1) = d * (d + 1) := by
    rw [Nat.sub_mul, one_mul]
    exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left (d + 1) (by omega : 0 < d))
  rw [hsum, Nat.mul_div_cancel_left (d + 1) (by omega : 0 < d)]

/-- The corner return of `1` is the trap state `2`. -/
theorem CoreReturnCornerOne (d : ℕ) (hd : 2 ≤ d) : CoreReturn d (d + 1) 1 = 2 := by
  have hnd : ¬ d ∣ 1 := by
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  rw [CoreReturnOfNotDvd d (d + 1) 1 hnd]
  have hsum : (d - 1) * 1 + (d + 1) = 2 * d := by omega
  rw [hsum, Nat.mul_div_cancel 2 (by omega : 0 < d)]

/-- The corner return of `d` is `1`. -/
theorem CoreReturnCornerD (d : ℕ) (hd : 1 ≤ d) : CoreReturn d (d + 1) d = 1 := by
  rw [CoreReturnOfDvd d (d + 1) d (dvd_refl d), Nat.div_self (by omega : 0 < d)]

/-- The corner two-cycle is realized by the original map. -/
theorem CoreMapCornerCycle (d : ℕ) (hd : 3 ≤ d) :
    Iterate (CoreMap d (d + 1)) 2 (d + 1) = d + 1 := by
  have hnd := CoreCornerNotDvd d (by omega)
  have hsum : (d - 1) * (d + 1) + (d + 1) = d * (d + 1) := by
    rw [Nat.sub_mul, one_mul]
    exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left (d + 1) (by omega : 0 < d))
  rw [show Iterate (CoreMap d (d + 1)) 2 (d + 1) =
      CoreMap d (d + 1) (CoreMap d (d + 1) (d + 1)) from rfl,
    CoreMapOfNotDvd d (d + 1) (d + 1) hnd, hsum,
    CoreMapOfDvd d (d + 1) (d * (d + 1)) ⟨d + 1, rfl⟩,
    Nat.mul_div_cancel_left (d + 1) (by omega : 0 < d)]

/-- At the corner, the residues other than `0` and `c` are exactly `2, ..., d - 1`, and they
are all trapped. -/
theorem CoreMapCornerTrap (d x : ℕ) (hd : 3 ≤ d) (hx2 : 2 ≤ x) (hxd : x < d) :
    ¬ CoreDomain d (d + 1) x := by
  have hcd : (d + 1) % d = 1 := by
    have h1 : (d + 1) % d = (1 + d) % d := by rw [show d + 1 = 1 + d by omega]
    rw [h1, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt (by omega : 1 < d),
      Nat.mod_eq_of_lt (by omega : 1 < d)]
  intro hdom
  rcases hdom with hdvd | hmod
  · have := Nat.le_of_dvd (by omega) hdvd
    omega
  · have hxmod : x % d = x := Nat.mod_eq_of_lt (by omega)
    omega

/-- The only fixed point of the corner return map inside the domain core is `d + 1`. -/
theorem CoreReturnCornerFixedUnique (d x : ℕ) (hd : 2 ≤ d) (h1 : 1 ≤ x) (h2 : x ≤ d + 1)
    (hdom : CoreDomain d (d + 1) x) (hfix : CoreReturn d (d + 1) x = x) :
    x = d + 1 := by
  have hcd : (d + 1) % d = 1 := by
    have h1 : (d + 1) % d = (1 + d) % d := by rw [show d + 1 = 1 + d by omega]
    rw [h1, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt (by omega : 1 < d),
      Nat.mod_eq_of_lt (by omega : 1 < d)]
  rcases hdom with hdvd | hmod
  · have hle := Nat.le_of_dvd (by omega) hdvd
    have hne : x ≠ d + 1 := by
      intro hx
      rw [hx] at hdvd
      exact CoreCornerNotDvd d (by omega) hdvd
    have hx : x = d := by omega
    rw [hx, CoreReturnCornerD d (by omega : 1 ≤ d)] at hfix
    omega
  · have hx1 : x % d = 1 := by omega
    have hcases : x = 1 ∨ x = d + 1 := by
      by_cases hle : x ≤ d
      · rcases eq_or_lt_of_le hle with hxd | hxlt
        · rw [← hxd, Nat.mod_self] at hx1
          omega
        · have hxx : x % d = x := Nat.mod_eq_of_lt hxlt
          omega
      · omega
    rcases hcases with hx | hx
    · rw [hx, CoreReturnCornerOne d hd] at hfix
      omega
    · exact hx


/-- Every positive state reaches the core within at most its own number of return steps. -/
theorem CoreReturnReachesCoreBounded (d c n : ℕ) (hd : 2 ≤ d) (hc : 1 ≤ c) (h1 : 1 ≤ n) :
    ∃ k, k ≤ n ∧ Iterate (CoreReturn d c) k n ≤ c := by
  revert h1
  refine Nat.strong_induction_on n ?_
  intro n ih h1
  by_cases hn : n ≤ c
  · exact ⟨0, by omega, by simpa [Iterate] using hn⟩
  · have hlt : CoreReturn d c n < n := CoreReturnDecrease d c n hd (by omega)
    have hpos : 1 ≤ CoreReturn d c n := CoreReturnPositive d c n hd hc h1
    obtain ⟨k, hk1, hk2⟩ := ih (CoreReturn d c n) hlt hpos
    exact ⟨k + 1, by omega, by rw [CoreIterateSucc]; exact hk2⟩

/-- One more than `d` is congruent to one modulo `d`. -/
theorem CoreCornerModSelf (d : ℕ) (hd : 1 < d) : (d + 1) % d = 1 := by
  rw [show d + 1 = 1 + d by omega, Nat.add_mod, Nat.mod_self, Nat.add_zero]
  rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd]

/-- The positive states of the corner core are exactly `1`, `d` and `d + 1`. -/
theorem CoreCornerCoreStates (d x : ℕ) (hd : 3 ≤ d) (h1 : 1 ≤ x) (h2 : x ≤ d + 1)
    (hdom : CoreDomain d (d + 1) x) : x = 1 ∨ x = d ∨ x = d + 1 := by
  have hcd : (d + 1) % d = 1 := CoreCornerModSelf d (by omega)
  rcases hdom with hdvd | hmod
  · have hle : d ≤ x := Nat.le_of_dvd (by omega) hdvd
    have hne : x ≠ d + 1 := by
      intro hx
      exact CoreCornerNotDvd d (by omega) (hx ▸ hdvd)
    have hle2 : x ≤ d := by omega
    exact Or.inr (Or.inl (by omega))
  · have hx1 : x % d = 1 := by omega
    by_cases hle : x ≤ d
    · rcases eq_or_lt_of_le hle with hxd | hxlt
      · exact Or.inr (Or.inl hxd)
      · have hxx : x % d = x := Nat.mod_eq_of_lt hxlt
        exact Or.inl (by omega)
    · exact Or.inr (Or.inr (by omega))

/-- The positive states of the corner core are exactly `1`, `d` and `d + 1`; conversely each of
the three belongs to the corner domain. -/
theorem CoreCornerCoreStatesIff (d x : ℕ) (hd : 3 ≤ d) (h1 : 1 ≤ x) (h2 : x ≤ d + 1) :
    CoreDomain d (d + 1) x ↔ x = 1 ∨ x = d ∨ x = d + 1 := by
  refine ⟨CoreCornerCoreStates d x hd h1 h2, ?_⟩
  have hmod : (d + 1) % d = 1 := CoreCornerModSelf d (by omega)
  rintro (hx | hx | hx)
  · exact Or.inr (by rw [hx, hmod, Nat.mod_eq_of_lt (by omega : 1 < d)])
  · exact Or.inl (by rw [hx])
  · exact Or.inr (by rw [hx])

/-- One corner instruction sends `d + 1` to `d * (d + 1)` and one sends `d * (d + 1)` back. -/
theorem CoreMapCornerCycleSteps (d : ℕ) (hd : 3 ≤ d) :
    CoreMap d (d + 1) (d + 1) = d * (d + 1) ∧
      CoreMap d (d + 1) (d * (d + 1)) = d + 1 := by
  have hnd := CoreCornerNotDvd d (by omega)
  have hsum : (d - 1) * (d + 1) + (d + 1) = d * (d + 1) := by
    rw [Nat.sub_mul, one_mul]
    exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left (d + 1) (by omega : 0 < d))
  exact ⟨by rw [CoreMapOfNotDvd d (d + 1) (d + 1) hnd, hsum],
    by rw [CoreMapOfDvd d (d + 1) (d * (d + 1)) ⟨d + 1, rfl⟩,
      Nat.mul_div_cancel_left (d + 1) (by omega : 0 < d)]⟩

/-- Two corner instructions return `d * (d + 1)` to itself. -/
theorem CoreMapCornerCycleBack (d : ℕ) (hd : 3 ≤ d) :
    Iterate (CoreMap d (d + 1)) 2 (d * (d + 1)) = d * (d + 1) := by
  rw [show Iterate (CoreMap d (d + 1)) 2 (d * (d + 1)) =
      CoreMap d (d + 1) (CoreMap d (d + 1) (d * (d + 1))) from rfl,
    (CoreMapCornerCycleSteps d hd).2, (CoreMapCornerCycleSteps d hd).1]

/-- The corner cycle returns to `d + 1` after an even number of instructions. -/
theorem CoreCornerCycleIterateEven (d m : ℕ) (hd : 3 ≤ d) :
    Iterate (CoreMap d (d + 1)) (2 * m) (d + 1) = d + 1 := by
  induction m with
  | zero => { simp [Iterate] }
  | succ m ih =>
    {
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, IterateAdd, ih]
      exact CoreMapCornerCycle d hd
    }

/-- A backward corner state returns to itself after an even number of instructions. -/
theorem CoreCornerCycleIterateBack (d m : ℕ) (hd : 3 ≤ d) :
    Iterate (CoreMap d (d + 1)) (2 * m) (d * (d + 1)) = d * (d + 1) := by
  induction m with
  | zero => { simp [Iterate] }
  | succ m ih =>
    {
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, IterateAdd, ih]
      exact CoreMapCornerCycleBack d hd
    }

/-- The corner cycle reaches `d * (d + 1)` after an odd number of instructions. -/
theorem CoreCornerCycleIterateOdd (d m : ℕ) (hd : 3 ≤ d) :
    Iterate (CoreMap d (d + 1)) (2 * m + 1) (d + 1) = d * (d + 1) := by
  rw [IterateAdd, CoreCornerCycleIterateEven d m hd]
  exact (CoreMapCornerCycleSteps d hd).1

/-- A backward corner state reaches `d + 1` after an odd number of instructions. -/
theorem CoreCornerCycleIterateBackOdd (d m : ℕ) (hd : 3 ≤ d) :
    Iterate (CoreMap d (d + 1)) (2 * m + 1) (d * (d + 1)) = d + 1 := by
  rw [IterateAdd, CoreCornerCycleIterateBack d m hd]
  exact (CoreMapCornerCycleSteps d hd).2

/-- Every iterate of a corner cycle state stays on the corner cycle. -/
theorem CoreCornerCycleInvariant (d y m : ℕ) (hd : 3 ≤ d)
    (hy : y = d + 1 ∨ y = d * (d + 1)) :
    Iterate (CoreMap d (d + 1)) m y = d + 1 ∨
      Iterate (CoreMap d (d + 1)) m y = d * (d + 1) := by
  induction m with
  | zero => { simpa [Iterate] using hy }
  | succ m ih =>
    {
      rw [show Iterate (CoreMap d (d + 1)) (m + 1) y =
          CoreMap d (d + 1) (Iterate (CoreMap d (d + 1)) m y) from rfl]
      rcases ih with h | h
      · rw [h]
        exact Or.inr (CoreMapCornerCycleSteps d hd).1
      · rw [h]
        exact Or.inl (CoreMapCornerCycleSteps d hd).2
    }

/-- A return iterate of a seed in the domain is a raw iterate of that seed. -/
theorem CoreCornerIterateRealized (d x : ℕ) (hd : 3 ≤ d)
    (hdom : ∀ k, CoreDomain d (d + 1) (Iterate (CoreMap d (d + 1)) k x)) (p : ℕ) :
    CoreDomain d (d + 1) (Iterate (CoreReturn d (d + 1)) p x) ∧
      ∃ j, Iterate (CoreMap d (d + 1)) j x = Iterate (CoreReturn d (d + 1)) p x := by
  induction p with
  | zero => { exact ⟨by simpa [Iterate] using hdom 0, 0, by simp [Iterate]⟩ }
  | succ p ih =>
    {
      obtain ⟨hdomP, j, hj⟩ := ih
      have hstep : ∃ j', Iterate (CoreMap d (d + 1)) j' (Iterate (CoreReturn d (d + 1)) p x) =
          CoreReturn d (d + 1) (Iterate (CoreReturn d (d + 1)) p x) := by
        rcases hdomP with hdvd | hmod
        · exact ⟨1, by
            rw [CoreReturnOfDvd d (d + 1) _ hdvd]
            exact CoreMapOfDvd d (d + 1) _ hdvd⟩
        · have hnd : ¬ d ∣ Iterate (CoreReturn d (d + 1)) p x := by
            intro hdvd
            rw [Nat.dvd_iff_mod_eq_zero] at hdvd
            have hcd : (d + 1) % d = 1 := CoreCornerModSelf d (by omega)
            omega
          exact ⟨2, CoreReturnRealizeMod d (d + 1) _ (by omega) hnd hmod⟩
      obtain ⟨j', hj'⟩ := hstep
      have hreal : ∃ j'', Iterate (CoreMap d (d + 1)) j'' x =
          Iterate (CoreReturn d (d + 1)) (p + 1) x := by
        refine ⟨j + j', ?_⟩
        rw [show Iterate (CoreReturn d (d + 1)) (p + 1) x =
            CoreReturn d (d + 1) (Iterate (CoreReturn d (d + 1)) p x) from rfl,
          IterateAdd, hj]
        exact hj'
      refine ⟨?_, hreal⟩
      obtain ⟨j'', hj''⟩ := hreal
      rw [← hj'']
      exact hdom j''
    }

/-- A corner orbit that never leaves the domain reaches the corner two-cycle. -/
theorem CoreCornerDomainForeverHitsCycle (d x : ℕ) (hd : 3 ≤ d) (hx1 : 1 ≤ x)
    (hdom : ∀ k, CoreDomain d (d + 1) (Iterate (CoreMap d (d + 1)) k x)) :
    ∃ k, Iterate (CoreMap d (d + 1)) k x = d + 1 ∨
      Iterate (CoreMap d (d + 1)) k x = d * (d + 1) := by
  have hc : 1 ≤ d + 1 := by omega
  obtain ⟨k, hk⟩ := CoreReturnReachesCore d (d + 1) x (by omega) hc hx1
  have hkpos : 1 ≤ Iterate (CoreReturn d (d + 1)) k x :=
    CoreReturnIteratePositive d (d + 1) x (by omega) hc hx1 k
  have hcore : ∀ t, 1 ≤ Iterate (CoreReturn d (d + 1)) t (Iterate (CoreReturn d (d + 1)) k x) ∧
      Iterate (CoreReturn d (d + 1)) t (Iterate (CoreReturn d (d + 1)) k x) ≤ d + 1 :=
    CoreReturnIterateCore d (d + 1) (Iterate (CoreReturn d (d + 1)) k x) (by omega) hc hkpos hk
  obtain ⟨K, P, hP, hper⟩ :=
    CoreReturnEventuallyPeriodic d (d + 1) (Iterate (CoreReturn d (d + 1)) k x) (by omega) hc hkpos
  have hdomS : ∀ s, CoreDomain d (d + 1)
      (Iterate (CoreReturn d (d + 1)) (K + s) (Iterate (CoreReturn d (d + 1)) k x)) := by
    intro s
    have h1 := (CoreCornerIterateRealized d x hd hdom (k + (K + s))).1
    rwa [IterateAdd] at h1
  have hcases : ∀ s, Iterate (CoreReturn d (d + 1)) (K + s)
      (Iterate (CoreReturn d (d + 1)) k x) = 1 ∨
      Iterate (CoreReturn d (d + 1)) (K + s) (Iterate (CoreReturn d (d + 1)) k x) = d ∨
      Iterate (CoreReturn d (d + 1)) (K + s) (Iterate (CoreReturn d (d + 1)) k x) = d + 1 := by
    intro s
    exact CoreCornerCoreStates d _ hd (hcore (K + s)).1 (hcore (K + s)).2 (hdomS s)
  have hnotOne : ∀ s, Iterate (CoreReturn d (d + 1)) (K + s)
      (Iterate (CoreReturn d (d + 1)) k x) ≠ 1 := by
    intro s h1
    have hnext : Iterate (CoreReturn d (d + 1)) (K + (s + 1))
        (Iterate (CoreReturn d (d + 1)) k x) = 2 := by
      rw [show K + (s + 1) = (K + s) + 1 by omega,
        show Iterate (CoreReturn d (d + 1)) ((K + s) + 1)
            (Iterate (CoreReturn d (d + 1)) k x) =
          CoreReturn d (d + 1) (Iterate (CoreReturn d (d + 1)) (K + s)
            (Iterate (CoreReturn d (d + 1)) k x)) from rfl,
        h1, CoreReturnCornerOne d (by omega : 2 ≤ d)]
    have hbad := hdomS (s + 1)
    rw [hnext] at hbad
    exact CoreMapCornerTrap d 2 hd (by omega) (by omega) hbad
  have hnotD : ∀ s, Iterate (CoreReturn d (d + 1)) (K + s)
      (Iterate (CoreReturn d (d + 1)) k x) ≠ d := by
    intro s hd_
    have hnext : Iterate (CoreReturn d (d + 1)) (K + (s + 1))
        (Iterate (CoreReturn d (d + 1)) k x) = 1 := by
      rw [show K + (s + 1) = (K + s) + 1 by omega,
        show Iterate (CoreReturn d (d + 1)) ((K + s) + 1)
            (Iterate (CoreReturn d (d + 1)) k x) =
          CoreReturn d (d + 1) (Iterate (CoreReturn d (d + 1)) (K + s)
            (Iterate (CoreReturn d (d + 1)) k x)) from rfl,
        hd_, CoreReturnCornerD d (by omega : 1 ≤ d)]
    have hnext2 : Iterate (CoreReturn d (d + 1)) (K + (s + 2))
        (Iterate (CoreReturn d (d + 1)) k x) = 2 := by
      rw [show K + (s + 2) = (K + (s + 1)) + 1 by omega,
        show Iterate (CoreReturn d (d + 1)) ((K + (s + 1)) + 1)
            (Iterate (CoreReturn d (d + 1)) k x) =
          CoreReturn d (d + 1) (Iterate (CoreReturn d (d + 1)) (K + (s + 1))
            (Iterate (CoreReturn d (d + 1)) k x)) from rfl,
        hnext, CoreReturnCornerOne d (by omega : 2 ≤ d)]
    have hbad := hdomS (s + 2)
    rw [hnext2] at hbad
    exact CoreMapCornerTrap d 2 hd (by omega) (by omega) hbad
  have hcycle : Iterate (CoreReturn d (d + 1)) K
      (Iterate (CoreReturn d (d + 1)) k x) = d + 1 := by
    rcases hcases 0 with h | h | h
    · exact absurd h (hnotOne 0)
    · exact absurd h (hnotD 0)
    · simpa using h
  obtain ⟨j, hj⟩ := (CoreCornerIterateRealized d x hd hdom (k + K)).2
  rw [IterateAdd] at hj
  exact ⟨j, Or.inl (by rw [hj, hcycle])⟩

/-- Every positive corner orbit either leaves the domain and then grows without bound, or
reaches the corner two-cycle. -/
theorem CoreCornerClassification (d x : ℕ) (hd : 3 ≤ d) (hx1 : 1 ≤ x) :
    (∃ k, ¬ CoreDomain d (d + 1) (Iterate (CoreMap d (d + 1)) k x) ∧
      ∀ bound, ∃ j, bound < Iterate (CoreMap d (d + 1)) (k + j) x) ∨
    (∃ k, Iterate (CoreMap d (d + 1)) k x = d + 1 ∨
      Iterate (CoreMap d (d + 1)) k x = d * (d + 1)) := by
  by_cases h : ∀ k, CoreDomain d (d + 1) (Iterate (CoreMap d (d + 1)) k x)
  · exact Or.inr (CoreCornerDomainForeverHitsCycle d x hd hx1 h)
  · obtain ⟨k, hk⟩ := not_forall.mp h
    refine Or.inl ⟨k, hk, fun bound => ?_⟩
    obtain ⟨j, hj⟩ := CoreTrapUnbounded d (d + 1) (Iterate (CoreMap d (d + 1)) k x)
      (by omega) (by omega) hk bound
    exact ⟨j, by rw [IterateAdd (CoreMap d (d + 1)) k j x]; exact hj⟩

/-- A positive periodic point of the corner map lies on the corner two-cycle. -/
theorem CoreCornerPeriodicPointCycle (d x k : ℕ) (hd : 3 ≤ d) (hx1 : 1 ≤ x) (hk : 0 < k)
    (hper : Iterate (CoreMap d (d + 1)) k x = x) : x = d + 1 ∨ x = d * (d + 1) := by
  have hc : 1 ≤ d + 1 := by omega
  by_cases h : ∀ j, CoreDomain d (d + 1) (Iterate (CoreMap d (d + 1)) j x)
  · obtain ⟨j, hj⟩ := CoreCornerDomainForeverHitsCycle d x hd hx1 h
    have hperiod : ∀ t, Iterate (CoreMap d (d + 1)) (k * t) x = x := by
      intro t
      induction t with
      | zero => { simp [Iterate] }
      | succ t ih =>
        {
          rw [Nat.mul_succ k t, IterateAdd, ih, hper]
        }
    obtain ⟨t, ht⟩ : ∃ t, j ≤ k * t :=
      ⟨j + 1, by
        calc j ≤ k * j := Nat.le_mul_of_pos_left j hk
          _ ≤ k * (j + 1) := Nat.mul_le_mul_left k (by omega)⟩
    have hkey : Iterate (CoreMap d (d + 1)) (k * t - j) (Iterate (CoreMap d (d + 1)) j x) = x := by
      rw [← IterateAdd (CoreMap d (d + 1)) j (k * t - j) x, Nat.add_sub_cancel' ht, hperiod t]
    rcases hj with hj | hj
    · rw [hj] at hkey
      rcases CoreCornerCycleInvariant d (d + 1) (k * t - j) hd (Or.inl rfl) with h1 | h1
      · exact Or.inl (by rw [← hkey, h1])
      · exact Or.inr (by rw [← hkey, h1])
    · rw [hj] at hkey
      rcases CoreCornerCycleInvariant d (d * (d + 1)) (k * t - j) hd (Or.inr rfl) with h1 | h1
      · exact Or.inl (by rw [← hkey, h1])
      · exact Or.inr (by rw [← hkey, h1])
  · obtain ⟨j, hj⟩ := not_forall.mp h
    have hgrow := CoreTrapGrowth d (d + 1) (Iterate (CoreMap d (d + 1)) j x)
      (by omega) hc hj k
    rw [← IterateAdd (CoreMap d (d + 1)) j k x] at hgrow
    have hshift : Iterate (CoreMap d (d + 1)) (j + k) x = Iterate (CoreMap d (d + 1)) j x := by
      rw [show j + k = k + j by omega, IterateAdd, hper]
    rw [hshift] at hgrow
    omega

/-- The positive fixed points of the `k`-th corner iterate, for positive `k`, are exactly the
corner two-cycle at even times. -/
theorem CoreCornerPeriodicIff (d x k : ℕ) (hd : 3 ≤ d) (hx1 : 1 ≤ x) (hk : 0 < k) :
    Iterate (CoreMap d (d + 1)) k x = x ↔
      (x = d + 1 ∨ x = d * (d + 1)) ∧ 2 ∣ k := by
  have hlt : d + 1 < d * (d + 1) := by
    have hpos : 0 < (d - 1) * (d + 1) := Nat.mul_pos (by omega) (by omega)
    have hsum : (d - 1) * (d + 1) + (d + 1) = d * (d + 1) := by
      rw [Nat.sub_mul, one_mul]
      exact Nat.sub_add_cancel (Nat.le_mul_of_pos_left (d + 1) (by omega : 0 < d))
    omega
  constructor
  · intro hper
    obtain hx | hx := CoreCornerPeriodicPointCycle d x k hd hx1 hk hper
    · refine ⟨Or.inl hx, ?_⟩
      by_contra h2
      obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := by
        have hmod : k % 2 = 1 := by omega
        exact ⟨k / 2, by omega⟩
      rw [hx, hm, CoreCornerCycleIterateOdd d m hd] at hper
      omega
    · refine ⟨Or.inr hx, ?_⟩
      by_contra h2
      obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := by
        have hmod : k % 2 = 1 := by omega
        exact ⟨k / 2, by omega⟩
      rw [hx, hm, CoreCornerCycleIterateBackOdd d m hd] at hper
      omega
  · rintro ⟨hx | hx, h2⟩
    · obtain ⟨m, hm⟩ := h2
      rw [hx, hm, CoreCornerCycleIterateEven d m hd]
    · obtain ⟨m, hm⟩ := h2
      rw [hx, hm, CoreCornerCycleIterateBack d m hd]
end GeneralizedCollatz
