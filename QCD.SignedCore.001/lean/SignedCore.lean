-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Signed core bound

The first-division return of a signed raw map is not constructed here. What is
proved is the integer estimate that makes a finite core possible. If a map
`H : ℤ → ℤ` obeys `m * |H(n)| ≤ A * |n| + B` with `A < m`, and
`N = ⌊B / (m - A)⌋`, then `|n| ≥ N + 1` forces `|H(n)| < |n|`, while
`|n| ≤ N` forces `|H(n)| ≤ N`. Every orbit therefore enters the finite
invariant interval of radius `N` and is eventually periodic there.

Not formalized here: the first hitting time of the zero residue, the
identification of `H` with one exact division of an affine block, the values
of `A` and `B` as maxima over residues, traps, and every classical
convergence statement.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Radius `⌊B / (m - A)⌋` of a core whose expansion is strictly below `m`. -/
def CoreRadius (A B m : ℕ) : ℕ := B / (m - A)

/-- The remainder of `B` leaves room for one more copy of the contraction gap. -/
theorem CoreBoundRoom (A B m : ℕ) (hA : A < m) :
    B < (m - A) * (CoreRadius A B m + 1) := by
  have hd : 0 < m - A := Nat.sub_pos_of_lt hA
  have hmod : B % (m - A) < m - A := Nat.mod_lt B hd
  have hle : B % (m - A) ≤ m - A - 1 := Nat.le_pred_of_lt hmod
  have hgap : m - A - 1 < m - A := Nat.sub_lt hd Nat.one_pos
  calc
    B = (m - A) * CoreRadius A B m + B % (m - A) :=
      (Nat.div_add_mod B (m - A)).symm
    _ ≤ (m - A) * CoreRadius A B m + (m - A - 1) :=
      Nat.add_le_add_left hle _
    _ < (m - A) * CoreRadius A B m + (m - A) := Nat.add_lt_add_left hgap _
    _ = (m - A) * (CoreRadius A B m + 1) := by rw [Nat.mul_add, Nat.mul_one]

/-- Outside the radius the linear bound is a strict contraction. -/
theorem CoreDescentNat (A B m n : ℕ) (hA : A < m)
    (hn : CoreRadius A B m + 1 ≤ n) : A * n + B < m * n := by
  have hB : B < (m - A) * (CoreRadius A B m + 1) := CoreBoundRoom A B m hA
  have hstep : (m - A) * (CoreRadius A B m + 1) ≤ (m - A) * n :=
    Nat.mul_le_mul_left (m - A) hn
  have hlt : B < (m - A) * n := Nat.lt_of_lt_of_le hB hstep
  have hdist : (m - A) * n = m * n - A * n := Nat.sub_mul m A n
  have hle : A * n ≤ m * n := Nat.mul_le_mul_right n (Nat.le_of_lt hA)
  calc
    A * n + B < A * n + (m - A) * n := Nat.add_lt_add_left hlt (A * n)
    _ = A * n + (m * n - A * n) := by rw [hdist]
    _ = m * n := Nat.add_sub_of_le hle

/-- Inside the radius the same bound stays strictly below the next shell. -/
theorem CoreInvariantNat (A B m n : ℕ) (hA : A < m) (hn : n ≤ CoreRadius A B m) :
    A * n + B < m * (CoreRadius A B m + 1) := by
  set N := CoreRadius A B m
  have hB : B < (m - A) * (N + 1) := CoreBoundRoom A B m hA
  have hAn : A * n ≤ A * N := Nat.mul_le_mul_left A hn
  have hsum : A * N + (m - A) * (N + 1) = m * N + (m - A) := by
    calc
      A * N + (m - A) * (N + 1) = A * N + ((m - A) * N + (m - A)) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = A * N + (m - A) * N + (m - A) := by rw [Nat.add_assoc]
      _ = (A + (m - A)) * N + (m - A) := by rw [Nat.add_mul]
      _ = m * N + (m - A) := by rw [Nat.add_sub_of_le (Nat.le_of_lt hA)]
  have hshell : m * N + (m - A) ≤ m * (N + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_left (Nat.sub_le m A) (m * N)
  have hstrict : A * n + B < m * N + (m - A) := by
    calc
      A * n + B ≤ A * N + B := Nat.add_le_add_right hAn B
      _ < A * N + (m - A) * (N + 1) := Nat.add_lt_add_left hB (A * N)
      _ = m * N + (m - A) := hsum
  exact Nat.lt_of_lt_of_le hstrict hshell

/-- A map obeying the core bound contracts every state outside the radius. -/
theorem CoreMapDescent (A B m : ℕ) (H : ℤ → ℤ) (n : ℤ) (hA : A < m)
    (hbound : m * (H n).natAbs ≤ A * n.natAbs + B)
    (hn : CoreRadius A B m + 1 ≤ n.natAbs) : (H n).natAbs < n.natAbs := by
  have hlt : m * (H n).natAbs < m * n.natAbs :=
    Nat.lt_of_le_of_lt hbound (CoreDescentNat A B m n.natAbs hA hn)
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le A) hA
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- A map obeying the core bound sends the closed radius into itself. -/
theorem CoreMapInvariant (A B m : ℕ) (H : ℤ → ℤ) (n : ℤ) (hA : A < m)
    (hbound : m * (H n).natAbs ≤ A * n.natAbs + B) (hn : n.natAbs ≤ CoreRadius A B m) :
    (H n).natAbs ≤ CoreRadius A B m := by
  have hlt : m * (H n).natAbs < m * (CoreRadius A B m + 1) :=
    Nat.lt_of_le_of_lt hbound (CoreInvariantNat A B m n.natAbs hA hn)
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le A) hA
  have hdiv : (H n).natAbs < CoreRadius A B m + 1 := Nat.lt_of_mul_lt_mul_left hlt
  exact Nat.le_of_lt_succ hdiv

/-- Every state obeying the bound at every point reaches the radius. -/
theorem CoreEntry (A B m : ℕ) (H : ℤ → ℤ) (hA : A < m)
    (hbound : ∀ k : ℤ, m * (H k).natAbs ≤ A * k.natAbs + B) (n : ℤ) :
    ∃ j : ℕ, (Iterate H j n).natAbs ≤ CoreRadius A B m := by
  suffices ∀ k n, n.natAbs = k → ∃ j, (Iterate H j n).natAbs ≤ CoreRadius A B m by
    exact this n.natAbs n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro n hk
    by_cases hcore : n.natAbs ≤ CoreRadius A B m
    · exact ⟨0, by simpa [Iterate, hk] using hcore⟩
    · have hn : CoreRadius A B m + 1 ≤ n.natAbs := by
        have hnot : ¬ n.natAbs ≤ CoreRadius A B m := hcore
        omega
      have hlt : (H n).natAbs < n.natAbs :=
        CoreMapDescent A B m H n hA (hbound n) hn
      have hkey : (H n).natAbs < k := by rw [← hk]; exact hlt
      obtain ⟨j, hj⟩ := ih (H n).natAbs hkey (H n) rfl
      refine ⟨j + 1, ?_⟩
      rw [show j + 1 = 1 + j by omega, IterateAdd]
      simpa [Iterate] using hj

/-- The radius stays closed under every iterate of a bound-preserving map. -/
theorem CoreStays (A B m : ℕ) (H : ℤ → ℤ) (hA : A < m)
    (hbound : ∀ k : ℤ, m * (H k).natAbs ≤ A * k.natAbs + B) (n : ℤ)
    (hn : n.natAbs ≤ CoreRadius A B m) (j : ℕ) :
    (Iterate H j n).natAbs ≤ CoreRadius A B m := by
  induction j with
  | zero => {
      simpa [Iterate] using hn
    }
  | succ j ih => {
      have hstep : Iterate H (j + 1) n = H (Iterate H j n) := rfl
      rw [hstep]
      exact CoreMapInvariant A B m H (Iterate H j n) hA (hbound _) ih
    }

/-- A repeat of two iterates propagates to every later time with that gap. -/
theorem CoreRepeatPropagates (H : ℤ → ℤ) (n : ℤ) (i j : ℕ)
    (heq : Iterate H i n = Iterate H j n) (k : ℕ) :
    Iterate H (i + k) n = Iterate H (j + k) n := by
  rw [IterateAdd, IterateAdd, heq]

/-- Code of an integer in the closed interval of radius `N`, as an index. -/
def CoreCode (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) : Fin (2 * N + 1) :=
  ⟨(k + (N : ℤ)).toNat, by
    have hhi : k ≤ (k.natAbs : ℤ) := Int.le_natAbs (a := k)
    have hneg : -k ≤ ((-k).natAbs : ℤ) := Int.le_natAbs (a := -k)
    have hlo : -(k.natAbs : ℤ) ≤ k := by
      rw [Int.natAbs_neg] at hneg
      omega
    have habs : (k.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hk
    have hnonneg : 0 ≤ k + (N : ℤ) := by omega
    have htop : k + (N : ℤ) ≤ (2 * N : ℤ) := by omega
    have hcast : ((k + (N : ℤ)).toNat : ℤ) = k + (N : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    have hnat : (k + (N : ℤ)).toNat ≤ 2 * N := by
      have : ((k + (N : ℤ)).toNat : ℤ) ≤ (2 * N : ℤ) := by
        rw [hcast]
        exact htop
      exact_mod_cast this
    omega⟩

/-- The code determines the integer. -/
theorem CoreCodeInjective (N : ℕ) (k₁ k₂ : ℤ) (hk₁ : k₁.natAbs ≤ N)
    (hk₂ : k₂.natAbs ≤ N) (h : CoreCode N k₁ hk₁ = CoreCode N k₂ hk₂) : k₁ = k₂ := by
  have hlo₁ : 0 ≤ k₁ + (N : ℤ) := by
    have hneg : -k₁ ≤ ((-k₁).natAbs : ℤ) := Int.le_natAbs (a := -k₁)
    have habs : (k₁.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hk₁
    rw [Int.natAbs_neg] at hneg
    omega
  have hlo₂ : 0 ≤ k₂ + (N : ℤ) := by
    have hneg : -k₂ ≤ ((-k₂).natAbs : ℤ) := Int.le_natAbs (a := -k₂)
    have habs : (k₂.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hk₂
    rw [Int.natAbs_neg] at hneg
    omega
  have hidx : (k₁ + (N : ℤ)).toNat = (k₂ + (N : ℤ)).toNat := by
    simpa [CoreCode] using congrArg Fin.val h
  have hcast₁ : ((k₁ + (N : ℤ)).toNat : ℤ) = k₁ + (N : ℤ) := Int.toNat_of_nonneg hlo₁
  have hcast₂ : ((k₂ + (N : ℤ)).toNat : ℤ) = k₂ + (N : ℤ) := Int.toNat_of_nonneg hlo₂
  have : k₁ + (N : ℤ) = k₂ + (N : ℤ) := by
    rw [← hcast₁, ← hcast₂]
    exact_mod_cast hidx
  omega

/-- Inside the radius, two of the first `2N + 2` states agree. -/
theorem CorePigeon (A B m : ℕ) (H : ℤ → ℤ) (hA : A < m)
    (hbound : ∀ k : ℤ, m * (H k).natAbs ≤ A * k.natAbs + B) (n : ℤ)
    (hn : n.natAbs ≤ CoreRadius A B m) :
    ∃ i j, i < j ∧ j ≤ 2 * CoreRadius A B m + 1 ∧
      Iterate H i n = Iterate H j n := by
  let N := CoreRadius A B m
  let f : Fin (2 * N + 2) → Fin (2 * N + 1) := fun t =>
    CoreCode N (Iterate H t.val n) (CoreStays A B m H hA hbound n hn t.val)
  have hcard : Fintype.card (Fin (2 * N + 1)) < Fintype.card (Fin (2 * N + 2)) := by
    simp [Fintype.card_fin]
  obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hval : Iterate H a.val n = Iterate H b.val n :=
    CoreCodeInjective N _ _ (CoreStays A B m H hA hbound n hn a.val)
      (CoreStays A B m H hA hbound n hn b.val) heq
  rcases Nat.lt_trichotomy a.val b.val with hlt | heqv | hgt
  · exact ⟨a.val, b.val, hlt, Nat.le_of_lt_succ b.isLt, hval⟩
  · exact False.elim (hne (Fin.ext heqv))
  · exact ⟨b.val, a.val, hgt, Nat.le_of_lt_succ a.isLt, hval.symm⟩

/-- An orbit that has entered the radius is eventually periodic. -/
theorem CoreEventuallyPeriodic (A B m : ℕ) (H : ℤ → ℤ) (hA : A < m)
    (hbound : ∀ k : ℤ, m * (H k).natAbs ≤ A * k.natAbs + B) (n : ℤ) :
    ∃ t p, 0 < p ∧ ∀ k, Iterate H (t + k) n = Iterate H (t + k + p) n := by
  obtain ⟨t, ht⟩ := CoreEntry A B m H hA hbound n
  obtain ⟨i, j, hij, _, heq⟩ :=
    CorePigeon A B m H hA hbound (Iterate H t n) ht
  refine ⟨t + i, j - i, Nat.sub_pos_of_lt hij, ?_⟩
  intro k
  have hshift : Iterate H (i + k) (Iterate H t n) =
      Iterate H (j + k) (Iterate H t n) :=
    CoreRepeatPropagates H (Iterate H t n) i j heq k
  have hleft : Iterate H (t + i + k) n =
      Iterate H (i + k) (Iterate H t n) := by
    rw [show t + i + k = t + (i + k) by omega, IterateAdd]
  have hright : Iterate H (j + k) (Iterate H t n) =
      Iterate H (t + (j + k)) n := by
    rw [← IterateAdd]
  have hidx : t + (j + k) = t + i + k + (j - i) := by omega
  rw [hleft, hshift, hright, hidx]

end GeneralizedCollatz
