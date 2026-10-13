-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import ResidueCylinders
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

/-!
# Interval counts and density-zero raw division survivors

The counting estimate uses the jointly legal cylinders proved in `ResidueCylinders`.
No distribution on a single integer orbit and no independence of successive guards
is imposed. Counting starts at zero; this stronger convention also bounds positive
seeds. Infinite-event counts below a finite threshold are mathematical quantities,
not a claim that the infinite predicate is decidable by a bounded computation.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.ResidueLeakage

/-- Count finite-depth legal seeds in a half-open initial interval. -/
def PrefixBelow (q c D m h X : ℕ) : Finset ℕ :=
  (Finset.range X).filter (fun n => (Run q c D m h n).isSome)

/-- Count the length-`L` blocks meeting a half-open interval, including the empty boundary. -/
def CeilingBlocks (X L : ℕ) : ℕ := if X = 0 then 0 else (X - 1) / L + 1

/-- The elementary boundary estimate is uniform in the finite source threshold. -/
theorem CeilingBlocksBound (X L : ℕ) : CeilingBlocks X L ≤ X / L + 1 := by
  unfold CeilingBlocks
  split_ifs with hz
  · exact Nat.zero_le _
  · have hb : (X - 1) / L ≤ X / L := Nat.div_le_div_right (Nat.sub_le X 1)
    omega

/-- Packing each legal seed by its residue and quotient gives the exact ceiling bound. -/
theorem PrefixBelowCeilingBound (q c D m h X : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    (PrefixBelow q c D m h X).card ≤ m ^ h * CeilingBlocks X (D ^ h) := by
  by_cases hz : X = 0
  · subst X
    simp [PrefixBelow, CeilingBlocks]
  let s := (Classes q c D m h) ×ˢ (Finset.range (CeilingBlocks X (D ^ h)))
  suffices hb : (PrefixBelow q c D m h X).card ≤ s.card by
    simpa only [s, Finset.card_product, Finset.card_range,
      ClassesCard q c D m h hq hD hcop hm] using hb
  apply Finset.card_le_card_of_injOn (fun n => (n % D ^ h, n / D ^ h))
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hlt := Finset.mem_range.mp hn'.1
    apply Finset.mem_product.mpr
    constructor
    · apply (ClassesMember q c D m h (n % D ^ h)).mpr
      exact ⟨Nat.mod_lt n (pow_pos hD h),
        (SurvivesMod q c D m h n hD).mp hn'.2⟩
    · apply Finset.mem_range.mpr
      have hnX : n ≤ X - 1 := by omega
      have hb : n / D ^ h ≤ (X - 1) / D ^ h := Nat.div_le_div_right hnX
      simpa only [CeilingBlocks, if_neg hz] using Nat.lt_succ_of_le hb
  · intro n _ u _ he
    have hr : n % D ^ h = u % D ^ h := congrArg Prod.fst he
    have ht : n / D ^ h = u / D ^ h := congrArg Prod.snd he
    calc
      n = n % D ^ h + D ^ h * (n / D ^ h) := (Nat.mod_add_div n (D ^ h)).symm
      _ = u % D ^ h + D ^ h * (u / D ^ h) := by rw [hr, ht]
      _ = u := Nat.mod_add_div u (D ^ h)

/-- The explicit floor-plus-boundary form follows without losing the stronger count. -/
theorem PrefixBelowBound (q c D m h X : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    (PrefixBelow q c D m h X).card ≤ m ^ h * (X / D ^ h + 1) := by
  exact (PrefixBelowCeilingBound q c D m h X hq hD hcop hm).trans
    (Nat.mul_le_mul_left (m ^ h) (CeilingBlocksBound X (D ^ h)))

noncomputable section

/-- Count actual infinite-division seeds below a threshold, retaining the raw predicate. -/
def InfiniteBelow (q c D X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter (InfiniteDivisions q c D)

/-- Every infinite raw witness lies in the same finite-depth legal seed set. -/
theorem InfiniteBelowSubset (q c D m h X : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    InfiniteBelow q c D X ⊆ PrefixBelow q c D m h X := by
  classical
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  exact ⟨hn'.1, (InfiniteSurvives q c D m n hq hD hcop hm).mp hn'.2 h⟩

/-- The source's ceiling survivor estimate holds for the actual infinite raw predicate. -/
theorem InfiniteBelowCeilingBound (q c D m h X : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    (InfiniteBelow q c D X).card ≤ m ^ h * CeilingBlocks X (D ^ h) := by
  exact (Finset.card_le_card (InfiniteBelowSubset q c D m h X hq hD hcop hm)).trans
    (PrefixBelowCeilingBound q c D m h X hq hD hcop hm)

/-- At a geometric scale a single source block recovers the integer power threshold. -/
theorem InfiniteBelowScaleBound (q c D m h X : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) (hX : X ≤ D ^ h) :
    (InfiniteBelow q c D X).card ≤ m ^ h := by
  have hc : CeilingBlocks X (D ^ h) ≤ 1 := by
    by_cases hz : X = 0
    · simp [CeilingBlocks, hz]
    · have hl : X - 1 < D ^ h := by omega
      simp [CeilingBlocks, hz, Nat.div_eq_of_lt hl]
  exact (InfiniteBelowCeilingBound q c D m h X hq hD hcop hm).trans
    (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (m ^ h) hc)

/-- All finite depth bounds apply to the same infinite-event seed set. -/
theorem InfiniteBelowBound (q c D m h X : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    (InfiniteBelow q c D X).card ≤ m ^ h * (X / D ^ h + 1) := by
  exact (Finset.card_le_card (InfiniteBelowSubset q c D m h X hq hD hcop hm)).trans
    (PrefixBelowBound q c D m h X hq hD hcop hm)

/-- Dividing the interval count keeps the explicit finite-interval boundary term. -/
theorem InfiniteDensityBound (q c D m h X : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) (hX : 0 < X) :
    ((InfiniteBelow q c D X).card : ℝ) / (X : ℝ) ≤
      ((m : ℝ) / (D : ℝ)) ^ h + (m ^ h : ℝ) / (X : ℝ) := by
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  have hL : 0 < (D ^ h : ℝ) := by
    exact_mod_cast pow_pos hD h
  have hd := Nat.div_mul_le_self X (D ^ h)
  have hf : ((X / D ^ h : ℕ) : ℝ) ≤ (X : ℝ) / (D ^ h : ℝ) := by
    apply (le_div_iff₀ hL).mpr
    exact_mod_cast hd
  have hc' : ((InfiniteBelow q c D X).card : ℝ) ≤
      (m ^ h : ℝ) * (((X / D ^ h : ℕ) : ℝ) + 1) := by
    exact_mod_cast InfiniteBelowBound q c D m h X hq hD hcop hm
  apply (div_le_iff₀ hx).mpr
  calc
    ((InfiniteBelow q c D X).card : ℝ) ≤
        (m ^ h : ℝ) * (((X / D ^ h : ℕ) : ℝ) + 1) := hc'
    _ ≤ (m ^ h : ℝ) * ((X : ℝ) / (D ^ h : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (((m : ℝ) / (D : ℝ)) ^ h + (m ^ h : ℝ) / (X : ℝ)) * (X : ℝ) := by
      rw [div_pow]
      field_simp

/-- This is the ordinary initial-interval density limit, with an explicit epsilon contract. -/
def NaturalDensityZero (q c D : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
    ∀ X : ℕ, N ≤ X → ((InfiniteBelow q c D X).card : ℝ) / (X : ℝ) < ε

/-- A strict residue shortfall closes the full-sequence natural-density limit. -/
theorem ResidueDensityZero (q c D m : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) (hshort : m < D) :
    NaturalDensityZero q c D := by
  intro ε hε
  have hρ : (m : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one (by exact_mod_cast hD)).mpr
    exact_mod_cast hshort
  obtain ⟨h, hh⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by linarith) hρ
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (m ^ h : ℝ) / ε + 1)
  have hA : 0 ≤ 2 * (m ^ h : ℝ) / ε := by positivity
  have hNpos : 0 < N := by
    exact_mod_cast (show 0 < (N : ℝ) by linarith)
  refine ⟨N, hNpos, ?_⟩
  intro X hNX
  have hXpos : 0 < X := hNpos.trans_le hNX
  have hx : 0 < (X : ℝ) := by exact_mod_cast hXpos
  have hnX : (N : ℝ) ≤ (X : ℝ) := by exact_mod_cast hNX
  have ht : 2 * (m ^ h : ℝ) / ε < (X : ℝ) := by linarith
  have hb : (m ^ h : ℝ) / (X : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hx).mpr
    have ht' := (div_lt_iff₀ hε).mp ht
    nlinarith
  have hu := InfiniteDensityBound q c D m h X hq hD hcop hm hXpos
  linarith

/-- The complement consists of seeds whose actual number of division events is finite. -/
def FiniteBelow (q c D X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter (fun n => ¬InfiniteDivisions q c D n)

/-- Finite and infinite division-event seeds form an exact partition, including zero. -/
theorem FinitePartition (q c D X : ℕ) :
    (InfiniteBelow q c D X).card + (FiniteBelow q c D X).card = X := by
  classical
  simpa only [InfiniteBelow, FiniteBelow, Finset.card_range] using
    Finset.card_filter_add_card_filter_not (s := Finset.range X) (InfiniteDivisions q c D)

/-- The same full-sequence ordinary density is one for finite-division seeds. -/
theorem FiniteDensityOne (q c D m : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) (hshort : m < D) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ X : ℕ, N ≤ X →
      1 - ε < ((FiniteBelow q c D X).card : ℝ) / (X : ℝ) ∧
        ((FiniteBelow q c D X).card : ℝ) / (X : ℝ) ≤ 1 := by
  intro ε hε
  obtain ⟨N, hNpos, hN⟩ := ResidueDensityZero q c D m hq hD hcop hm hshort ε hε
  refine ⟨N, hNpos, ?_⟩
  intro X hNX
  have hx : 0 < (X : ℝ) := by exact_mod_cast hNpos.trans_le hNX
  have hp : ((InfiniteBelow q c D X).card : ℝ) +
      ((FiniteBelow q c D X).card : ℝ) = (X : ℝ) := by
    exact_mod_cast FinitePartition q c D X
  constructor
  · apply (lt_div_iff₀ hx).mpr
    have hz := (div_lt_iff₀ hx).mp (hN X hNX)
    nlinarith
  · apply (div_le_one hx).mpr
    have hI : 0 ≤ ((InfiniteBelow q c D X).card : ℝ) := by positivity
    linarith

/-- Retain the finite guard test in the source's positive initial interval. -/
def PositivePrefixBelow (q c D m h X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter (fun n => (Run q c D m h n).isSome)

/-- Count the source's positive initial interval `[1,X]` without a zero-seed convention. -/
def PositiveInfiniteBelow (q c D X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter (InfiniteDivisions q c D)

/-- Count finitely-dividing seeds in the same positive initial interval. -/
def PositiveFiniteBelow (q c D X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter (fun n => ¬InfiniteDivisions q c D n)

/-- Translating interval conventions costs at most the explicitly retained endpoint. -/
theorem PositiveInfiniteBelowSubset (q c D X : ℕ) :
    PositiveInfiniteBelow q c D X ⊆ InfiniteBelow q c D (X + 1) := by
  classical
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  have hb := Finset.mem_Icc.mp hn'.1
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (by omega), hn'.2⟩

/-- The positive interval has the exact source-scale bound, including `X = D^h`. -/
theorem PositivePrefixBelowScaleBound (q c D m h X : ℕ) (hq : 2 ≤ q)
    (hD : 0 < D) (hcop : D.Coprime q) (hm : AccessLeast q c D m) (hX : X ≤ D ^ h) :
    (PositivePrefixBelow q c D m h X).card ≤ m ^ h := by
  classical
  rw [← ClassesCard q c D m h hq hD hcop hm]
  apply Finset.card_le_card_of_injOn (fun n => n % D ^ h)
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    apply (ClassesMember q c D m h (n % D ^ h)).mpr
    exact ⟨Nat.mod_lt n (pow_pos hD h), (SurvivesMod q c D m h n hD).mp hn'.2⟩
  · intro n hn u hu he
    have hn' := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hu' := Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1
    have hnL : n ≤ D ^ h := hn'.2.trans hX
    have huL : u ≤ D ^ h := hu'.2.trans hX
    change n % D ^ h = u % D ^ h at he
    -- The endpoint `D^h` alone represents zero in the positive source block.
    by_cases hnEq : n = D ^ h
    · rw [hnEq, Nat.mod_self] at he
      by_cases huEq : u = D ^ h
      · omega
      · have huLt : u < D ^ h := by omega
        rw [Nat.mod_eq_of_lt huLt] at he
        omega
    · have hnLt : n < D ^ h := by omega
      rw [Nat.mod_eq_of_lt hnLt] at he
      have huLt : u < D ^ h := by
        by_contra huNot
        have huEq : u = D ^ h := by omega
        rw [huEq, Nat.mod_self] at he
        omega
      rwa [Nat.mod_eq_of_lt huLt] at he

/-- The same positive infinite witnesses lie in every complete finite guard test. -/
theorem PositiveInfinitePrefixSubset (q c D m h X : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    PositiveInfiniteBelow q c D X ⊆ PositivePrefixBelow q c D m h X := by
  classical
  intro n hn
  have hn' := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr
    ⟨hn'.1, (InfiniteSurvives q c D m n hq hD hcop hm).mp hn'.2 h⟩

/-- Positive source packing retains the exact ceiling boundary in every partial block. -/
theorem PositivePrefixBelowCeilingBound (q c D m h X : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    (PositivePrefixBelow q c D m h X).card ≤ m ^ h * CeilingBlocks X (D ^ h) := by
  classical
  by_cases hz : X = 0
  · subst X
    simp [PositivePrefixBelow, CeilingBlocks]
  let L := D ^ h
  have hL : 0 < L := pow_pos hD h
  let s := (PositivePrefixBelow q c D m h L) ×ˢ (Finset.range (CeilingBlocks X L))
  suffices hb : (PositivePrefixBelow q c D m h X).card ≤ s.card by
    calc
      (PositivePrefixBelow q c D m h X).card ≤ s.card := hb
      _ = (PositivePrefixBelow q c D m h L).card * CeilingBlocks X L := by
        simp only [s, Finset.card_product, Finset.card_range]
      _ ≤ m ^ h * CeilingBlocks X L := Nat.mul_le_mul_right _
        (PositivePrefixBelowScaleBound q c D m h L hq hD hcop hm (Nat.le_refl L))
  apply Finset.card_le_card_of_injOn (fun n => ((n - 1) % L + 1, (n - 1) / L))
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hbounds := Finset.mem_Icc.mp hn'.1
    let r := (n - 1) % L + 1
    have he : n = r + L * ((n - 1) / L) := by
      have hd := Nat.mod_add_div (n - 1) L
      dsimp only [r]
      omega
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        have hr := Nat.mod_lt (n - 1) hL
        dsimp only [r]
        omega
      · have hs : Survives q c D m h n := hn'.2
        rw [he] at hs
        exact (SurvivesShift q c D m h r ((n - 1) / L) hD).mp hs
    · apply Finset.mem_range.mpr
      have hb : (n - 1) / L ≤ (X - 1) / L :=
        Nat.div_le_div_right (Nat.sub_le_sub_right hbounds.2 1)
      simpa only [CeilingBlocks, if_neg hz] using Nat.lt_succ_of_le hb
  · intro n hn u hu he
    have hn' := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hu' := Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1
    have hr := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    change (n - 1) % L + 1 = (u - 1) % L + 1 at hr
    change (n - 1) / L = (u - 1) / L at ht
    have hr' : (n - 1) % L = (u - 1) % L := Nat.add_right_cancel hr
    have hnEq := Nat.mod_add_div (n - 1) L
    have huEq := Nat.mod_add_div (u - 1) L
    rw [hr', ht] at hnEq
    omega

/-- The original survivor ceiling applies to `[1,X]`, not a shifted surrogate interval. -/
theorem PositiveInfiniteBelowCeilingBound (q c D m h X : ℕ) (hq : 2 ≤ q)
    (hD : 0 < D) (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    (PositiveInfiniteBelow q c D X).card ≤ m ^ h * CeilingBlocks X (D ^ h) := by
  exact (Finset.card_le_card (PositiveInfinitePrefixSubset q c D m h X hq hD hcop hm)).trans
    (PositivePrefixBelowCeilingBound q c D m h X hq hD hcop hm)

/-- The exact original minimum retains both interval size and legal-cylinder budgets. -/
theorem PositiveInfiniteBelowMinBound (q c D m h X : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    (PositiveInfiniteBelow q c D X).card ≤ min X (m ^ h * CeilingBlocks X (D ^ h)) := by
  classical
  have hs : PositiveInfiniteBelow q c D X ⊆ Finset.Icc 1 X := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hc : (PositiveInfiniteBelow q c D X).card ≤ X := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hs
  exact le_min hc (PositiveInfiniteBelowCeilingBound q c D m h X hq hD hcop hm)

/-- The same infinite-event set retains the one-block bound at the closed positive boundary. -/
theorem PositiveInfiniteBelowScaleBound (q c D m h X : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) (hX : X ≤ D ^ h) :
    (PositiveInfiniteBelow q c D X).card ≤ m ^ h := by
  exact (Finset.card_le_card (PositiveInfinitePrefixSubset q c D m h X hq hD hcop hm)).trans
    (PositivePrefixBelowScaleBound q c D m h X hq hD hcop hm hX)

/-- The positive source interval has the same full-sequence density-zero contract. -/
theorem PositiveResidueDensityZero (q c D m : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) (hshort : m < D) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ X : ℕ, N ≤ X →
      ((PositiveInfiniteBelow q c D X).card : ℝ) / (X : ℝ) < ε := by
  intro ε hε
  obtain ⟨N, hNpos, hN⟩ :=
    ResidueDensityZero q c D m hq hD hcop hm hshort (ε / 2) (by linarith)
  refine ⟨N, hNpos, ?_⟩
  intro X hNX
  have hX : 0 < X := hNpos.trans_le hNX
  have hx : 0 < (X : ℝ) := by exact_mod_cast hX
  have hxOne : 1 ≤ (X : ℝ) := by exact_mod_cast hX
  have hc : ((PositiveInfiniteBelow q c D X).card : ℝ) ≤
      ((InfiniteBelow q c D (X + 1)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (PositiveInfiniteBelowSubset q c D X)
  have hxSucc : 0 < ((X + 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < X + 1 by omega)
  have hz := (div_lt_iff₀ hxSucc).mp (hN (X + 1) (by omega))
  push_cast at hz
  apply (div_lt_iff₀ hx).mpr
  nlinarith

/-- Positive finite and infinite division counts partition exactly the original `X` seeds. -/
theorem PositivePartition (q c D X : ℕ) :
    (PositiveInfiniteBelow q c D X).card + (PositiveFiniteBelow q c D X).card = X := by
  classical
  simpa only [PositiveInfiniteBelow, PositiveFiniteBelow, Nat.card_Icc,
    Nat.add_sub_cancel] using
    Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 X) (InfiniteDivisions q c D)

/-- Density one is recovered with the source's exact positive-interval normalization. -/
theorem PositiveFiniteDensityOne (q c D m : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) (hshort : m < D) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ ∀ X : ℕ, N ≤ X →
      1 - ε < ((PositiveFiniteBelow q c D X).card : ℝ) / (X : ℝ) ∧
        ((PositiveFiniteBelow q c D X).card : ℝ) / (X : ℝ) ≤ 1 := by
  intro ε hε
  obtain ⟨N, hNpos, hN⟩ :=
    PositiveResidueDensityZero q c D m hq hD hcop hm hshort ε hε
  refine ⟨N, hNpos, ?_⟩
  intro X hNX
  have hx : 0 < (X : ℝ) := by exact_mod_cast hNpos.trans_le hNX
  have hp : ((PositiveInfiniteBelow q c D X).card : ℝ) +
      ((PositiveFiniteBelow q c D X).card : ℝ) = (X : ℝ) := by
    exact_mod_cast PositivePartition q c D X
  constructor
  · apply (lt_div_iff₀ hx).mpr
    have hz := (div_lt_iff₀ hx).mp (hN X hNX)
    nlinarith
  · apply (div_le_one hx).mpr
    have hI : 0 ≤ ((PositiveInfiniteBelow q c D X).card : ℝ) := by positivity
    linarith

/-- The logarithmic exponent exactly converts integral residue scales to powers of `m`. -/
theorem ResiduePowerIdentity (m D k : ℕ) (hm : 1 ≤ m) (hD : 2 ≤ D) :
    ((D : ℝ) ^ k) ^ (Real.log (m : ℝ) / Real.log (D : ℝ)) = (m : ℝ) ^ k := by
  have hd : 0 < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hlog : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  calc
    ((D : ℝ) ^ k) ^ (Real.log (m : ℝ) / Real.log (D : ℝ)) =
        Real.exp (Real.log ((D : ℝ) ^ k) *
          (Real.log (m : ℝ) / Real.log (D : ℝ))) :=
      Real.rpow_def_of_pos (pow_pos hd k) _
    _ = Real.exp (Real.log (m : ℝ) * (k : ℝ)) := by
      congr 1
      rw [Real.log_pow]
      field_simp
    _ = (m : ℝ) ^ (k : ℝ) := (Real.rpow_def_of_pos hmpos _).symm
    _ = (m : ℝ) ^ k := Real.rpow_natCast _ _

/-- A finite scale exists by a proved elementary exponential bound, not an oracle. -/
theorem PositiveScaleExists (D X : ℕ) (hD : 2 ≤ D) : ∃ h, X ≤ D ^ h := by
  have hb : ∀ k, k + 1 ≤ D ^ k := by
    intro k
    induction k with
    | zero => {
        simp
      }
    | succ k ih => {
        rw [pow_succ]
        nlinarith
      }
  exact ⟨X, by have hh := hb X; omega⟩

/-- The source's real-power positive survivor bound follows from an exact minimal scale. -/
theorem PositiveInfinitePowerBound (q c D m X : ℕ) (hq : 2 ≤ q) (hD : 2 ≤ D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) (hX : 0 < X) :
    ((PositiveInfiniteBelow q c D X).card : ℝ) ≤
      (m : ℝ) * (X : ℝ) ^ (Real.log (m : ℝ) / Real.log (D : ℝ)) := by
  classical
  have hmOne : 1 ≤ m := hm.1
  have hdPos : 0 < D := by omega
  have he := PositiveScaleExists D X hD
  have hs := Nat.find_spec he
  cases hh : Nat.find he with
  | zero => {
      rw [hh, pow_zero] at hs
      have hxEq : X = 1 := by omega
      have hc := PositiveInfiniteBelowScaleBound q c D m 0 X hq hdPos hcop hm
        (by simpa only [pow_zero] using hs)
      have hc' : ((PositiveInfiniteBelow q c D X).card : ℝ) ≤ 1 := by
        exact_mod_cast hc
      rw [hxEq] at hc' ⊢
      simp only [Nat.cast_one, Real.one_rpow, mul_one]
      exact hc'.trans (show 1 ≤ (m : ℝ) by exact_mod_cast hmOne)
    }
  | succ k => {
      rw [hh] at hs
      have hp : D ^ k < X := by
        have hh' := Nat.find_min he (show k < Nat.find he by omega)
        omega
      have hc := PositiveInfiniteBelowScaleBound q c D m (k + 1) X hq hdPos hcop hm hs
      have hc' : ((PositiveInfiniteBelow q c D X).card : ℝ) ≤ (m : ℝ) ^ (k + 1) := by
        exact_mod_cast hc
      have ha : 0 ≤ Real.log (m : ℝ) / Real.log (D : ℝ) := by
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hmOne))
          (Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega)))
      have hr := Real.rpow_le_rpow (show 0 ≤ (D : ℝ) ^ k by positivity)
        (show (D : ℝ) ^ k ≤ (X : ℝ) by exact_mod_cast hp.le) ha
      rw [ResiduePowerIdentity m D k hmOne hD] at hr
      calc
        ((PositiveInfiniteBelow q c D X).card : ℝ) ≤ (m : ℝ) ^ (k + 1) := hc'
        _ = (m : ℝ) * (m : ℝ) ^ k := by rw [pow_succ, mul_comm]
        _ ≤ (m : ℝ) * (X : ℝ) ^ (Real.log (m : ℝ) / Real.log (D : ℝ)) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
    }

/-- Residue leakage gives raw-clock escape for every seed outside the zero-density set. -/
theorem ResidueEscape (q c D m n : ℕ) (hq : 2 ≤ q) (hc : 1 ≤ c) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m)
    (hi : ¬InfiniteDivisions q c D n) :
    ∀ B, ∃ K, ∀ j, K ≤ j → B < Iterate (Raw q c D) j n := by
  obtain ⟨t, ht⟩ := FiniteDivisionsTail q c D m n hq hD hcop hm hi
  exact DivisionFreeEscape q c D n t (by omega) hc ht

/-- Every bounded raw orbit lies in the same infinitely-dividing exceptional set. -/
theorem BoundedInfinite (q c D m n : ℕ) (hq : 2 ≤ q) (hc : 1 ≤ c) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m)
    (hb : ∃ B, ∀ j, Iterate (Raw q c D) j n ≤ B) : InfiniteDivisions q c D n := by
  by_contra hi
  obtain ⟨B, hB⟩ := hb
  obtain ⟨K, hK⟩ := ResidueEscape q c D m n hq hc hD hcop hm hi B
  have hu := hK K (Nat.le_refl K)
  have hl := hB K
  omega

/-- Repetition on a genuine positive raw clock forces infinitely many division events. -/
theorem PeriodicInfinite (q c D m n t L : ℕ) (hq : 2 ≤ q) (hc : 1 ≤ c) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) (hL : 0 < L)
    (hp : ∀ j, t ≤ j → Iterate (Raw q c D) (j + L) n = Iterate (Raw q c D) j n) :
    InfiniteDivisions q c D n := by
  by_contra hi
  have hr : ∀ k, Iterate (Raw q c D) (t + L * k) n = Iterate (Raw q c D) t n := by
    intro k
    induction k with
    | zero => {
        simp
      }
    | succ k ih => {
        rw [show t + L * (k + 1) = (t + L * k) + L by ring,
          hp (t + L * k) (Nat.le_add_right t (L * k)), ih]
      }
  obtain ⟨K, hK⟩ :=
    ResidueEscape q c D m n hq hc hD hcop hm hi (Iterate (Raw q c D) t n)
  have htime : K ≤ t + L * K := by nlinarith
  have hu := hK (t + L * K) htime
  rw [hr K] at hu
  exact (Nat.lt_irrefl _) hu

end

end GeneralizedCollatz.ResidueLeakage
