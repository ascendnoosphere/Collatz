/-
Copyright (c) 2026 ascendnoosphere
SPDX-License-Identifier: CC-BY-4.0

No-crossing supports of symmetric difference two.

For a finite set `S` of indices, the shortcut numerator is
`SupportA S = ∑_{j ∈ S} 3^{#(k ∈ S : k > j)} 2^j`.
Take `lo < hi` and a common set `C` containing neither index and no index
strictly between them. The supports `insert lo C` and `insert hi C` are
distinct, have equal cardinality `r`, and have symmetric difference
`{lo, hi}`. Their numerator difference is exactly
`3^s 2^lo (2^(hi - lo) - 1)`, where `s` is the number of elements of `C`
strictly above `hi`. The equal-halves modulus `M = 2^h + 3^r` is coprime to
`6`, and the third factor `2^(hi - lo) - 1` is strictly between `0` and `M`.
Thus `M` cannot divide the numerator difference: the difference condition
would force `M` to divide that third factor.

Indices lying strictly between `lo` and `hi`, symmetric differences larger
than two, divisibility by `2^h - 3^r`, and convergence of the classical
Collatz map are not treated.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

namespace GeneralizedCollatz

open Finset

/-- Number of indices of `S` strictly above `j`. -/
def OddsAfter (S : Finset ℕ) (j : ℕ) : ℕ :=
  (S.filter (fun k => j < k)).card

/-- Shortcut numerator `∑ 3^{#(k ∈ S : k > j)} 2^j` over `j ∈ S`. -/
def SupportA (S : Finset ℕ) : ℕ :=
  S.sum fun j => 3 ^ OddsAfter S j * 2 ^ j

/-- Split `2^hi` across a positive gap as `2^lo` plus the third factor. -/
theorem TwoPowSplit (lo hi : ℕ) (hlt : lo < hi) :
    2 ^ hi = 2 ^ lo + 2 ^ lo * (2 ^ (hi - lo) - 1) := by
  have hle : lo ≤ hi := Nat.le_of_lt hlt
  -- `hi = lo + (hi - lo)`, so the pure power factors.
  have hpow : 2 ^ hi = 2 ^ lo * 2 ^ (hi - lo) := by
    conv_lhs => rw [← Nat.add_sub_of_le hle]
    rw [Nat.pow_add]
  have hsplit : 2 ^ (hi - lo) = 2 ^ (hi - lo) - 1 + 1 :=
    (Nat.sub_add_cancel Nat.one_le_two_pow).symm
  rw [hpow]
  conv_lhs => rw [hsplit]
  rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- With nothing strictly between `lo` and `hi`, the two moved indices have
the same numerator exponent. -/
theorem OddsAfterEndpoints (lo hi : ℕ) (C : Finset ℕ) (hlo : lo < hi)
    (hgap : ∀ x ∈ C, x < lo ∨ hi < x) :
    OddsAfter (insert lo C) lo = OddsAfter (insert hi C) hi := by
  -- Above `lo` and above `hi`, the common set contributes the same indices.
  have hF : C.filter (fun k => lo < k) = C.filter (fun k => hi < k) := by
    refine filter_congr ?_
    intro x hx
    rcases hgap x hx with hxl | hxh
    · exact ⟨fun hlt => (Nat.lt_asymm hxl hlt).elim,
        fun hlt => (Nat.lt_asymm (Nat.lt_trans hxl hlo) hlt).elim⟩
    · exact ⟨fun _ => hxh, fun _ => Nat.lt_trans hlo hxh⟩
  have hL : OddsAfter (insert lo C) lo =
      (C.filter (fun k => lo < k)).card := by
    unfold OddsAfter
    rw [filter_insert, if_neg (Nat.lt_irrefl lo)]
  have hR : OddsAfter (insert hi C) hi =
      (C.filter (fun k => hi < k)).card := by
    unfold OddsAfter
    rw [filter_insert, if_neg (Nat.lt_irrefl hi)]
  rw [hL, hR]
  exact congrArg Finset.card hF

/-- Every common index has the same numerator exponent in both supports. -/
theorem OddsAfterCommon (lo hi : ℕ) (C : Finset ℕ) (x : ℕ) (hlo : lo < hi)
    (hloC : lo ∉ C) (hhiC : hi ∉ C) (hx : x ∈ C)
    (hgap : ∀ y ∈ C, y < lo ∨ hi < y) :
    OddsAfter (insert lo C) x = OddsAfter (insert hi C) x := by
  rcases hgap x hx with hxl | hxh
  · -- `x` lies below both moved indices, so each contributes one.
    have hxhi : x < hi := Nat.lt_trans hxl hlo
    have hloF : lo ∉ C.filter (fun k => x < k) := by
      intro hmem
      exact hloC (mem_filter.mp hmem).1
    have hhiF : hi ∉ C.filter (fun k => x < k) := by
      intro hmem
      exact hhiC (mem_filter.mp hmem).1
    have hL : OddsAfter (insert lo C) x =
        (C.filter (fun k => x < k)).card + 1 := by
      unfold OddsAfter
      rw [filter_insert, if_pos hxl, card_insert_of_notMem hloF]
    have hR : OddsAfter (insert hi C) x =
        (C.filter (fun k => x < k)).card + 1 := by
      unfold OddsAfter
      rw [filter_insert, if_pos hxhi, card_insert_of_notMem hhiF]
    rw [hL, hR]
  · -- `x` lies above both moved indices, so neither contributes.
    have hltlo : lo < x := Nat.lt_trans hlo hxh
    unfold OddsAfter
    rw [filter_insert, if_neg (Nat.lt_asymm hltlo)]
    rw [filter_insert, if_neg (Nat.lt_asymm hxh)]

/-- Moving one index across an empty gap changes the support by exactly those
two indices. -/
theorem NoCrossingSymmDiff (lo hi : ℕ) (C : Finset ℕ) (hlo : lo < hi)
    (hloC : lo ∉ C) (hhiC : hi ∉ C) :
    symmDiff (insert lo C) (insert hi C) = {lo, hi} := by
  ext x
  constructor
  · intro hx
    rw [mem_symmDiff] at hx
    rcases hx with ⟨hxU, hxNotV⟩ | ⟨hxV, hxNotU⟩
    · rw [mem_insert] at hxU
      rcases hxU with hEq | hxC
      · rw [hEq]
        exact mem_insert_self lo {hi}
      · exact (hxNotV (mem_insert_of_mem hxC)).elim
    · rw [mem_insert] at hxV
      rcases hxV with hEq | hxC
      · rw [hEq]
        exact mem_insert_of_mem (mem_singleton_self hi)
      · exact (hxNotU (mem_insert_of_mem hxC)).elim
  · intro hx
    rw [mem_insert, mem_singleton] at hx
    rw [mem_symmDiff]
    rcases hx with hEq | hEq
    · rw [hEq]
      refine Or.inl ⟨mem_insert_self lo C, ?_⟩
      intro hV
      rw [mem_insert] at hV
      rcases hV with hEq | hC
      · exact Nat.ne_of_lt hlo hEq
      · exact hloC hC
    · rw [hEq]
      refine Or.inr ⟨mem_insert_self hi C, ?_⟩
      intro hU
      rw [mem_insert] at hU
      rcases hU with hEq | hC
      · exact Nat.ne_of_gt hlo hEq
      · exact hhiC hC

/-- For `h > 0` and `r > 0`, `2^h + 3^r` is coprime to `2` and to `3`. -/
theorem ModulusCoprimeTwoThree (h r : ℕ) (hh : 0 < h) (hr : 0 < r) :
    Nat.Coprime (2 ^ h + 3 ^ r) 2 ∧ Nat.Coprime (2 ^ h + 3 ^ r) 3 := by
  refine ⟨?_, ?_⟩
  · -- Even power of two plus odd power of three.
    have heven : Even (2 ^ h) :=
      Nat.even_pow.mpr ⟨⟨1, rfl⟩, Nat.ne_of_gt hh⟩
    have hodd : Odd (3 ^ r) := Odd.pow ⟨1, rfl⟩
    exact Odd.coprime_two_right (Even.add_odd heven hodd)
  · rw [Nat.coprime_comm, Nat.prime_three.coprime_iff_not_dvd]
    intro hd
    -- `r > 0`, so removing `3^r` leaves the pure power of two.
    have hpow3 : 3 ∣ 3 ^ r := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
      rw [Nat.pow_succ]
      exact Nat.dvd_mul_left 3 (3 ^ k)
    have hsub : 3 ∣ 2 ^ h + 3 ^ r - 3 ^ r := Nat.dvd_sub hd hpow3
    rw [Nat.add_sub_cancel] at hsub
    have hcop : Nat.Coprime 3 (2 ^ h) :=
      Nat.Coprime.pow_right h (Odd.coprime_two_right (⟨1, rfl⟩ : Odd 3))
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop hsub) (by decide : (3 : ℕ) ≠ 1)

/-- The equal-halves modulus is coprime to six. -/
theorem ModulusCoprimeSix (h r : ℕ) (hh : 0 < h) (hr : 0 < r) :
    Nat.Coprime (2 ^ h + 3 ^ r) 6 := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right]
  exact ModulusCoprimeTwoThree h r hh hr

/-- The numerator gap across an empty interval is the third factor
`2^(hi - lo) - 1`, multiplied by the common power of three and by `2^lo`. -/
theorem NoCrossingDifference (lo hi : ℕ) (C : Finset ℕ) (hlo : lo < hi)
    (hloC : lo ∉ C) (hhiC : hi ∉ C)
    (hgap : ∀ x ∈ C, x < lo ∨ hi < x) :
    SupportA (insert hi C) =
      SupportA (insert lo C) +
        3 ^ (C.filter (fun k => hi < k)).card *
          2 ^ lo * (2 ^ (hi - lo) - 1) := by
  let s : ℕ := (C.filter (fun k => hi < k)).card
  let third : ℕ := 2 ^ (hi - lo) - 1
  have hsV : OddsAfter (insert hi C) hi = s := by
    unfold OddsAfter
    rw [filter_insert, if_neg (Nat.lt_irrefl hi)]
  have hsU : OddsAfter (insert lo C) lo = s := by
    rw [OddsAfterEndpoints lo hi C hlo hgap, hsV]
  -- Common indices contribute the same sum to both numerators.
  have hcommon :
      C.sum (fun j => 3 ^ OddsAfter (insert hi C) j * 2 ^ j) =
        C.sum (fun j => 3 ^ OddsAfter (insert lo C) j * 2 ^ j) := by
    refine sum_congr rfl ?_
    intro j hj
    have hodds :=
      OddsAfterCommon lo hi C j hlo hloC hhiC hj hgap
    rw [← hodds]
  have hAU : SupportA (insert lo C) =
      3 ^ s * 2 ^ lo +
        C.sum fun j => 3 ^ OddsAfter (insert lo C) j * 2 ^ j := by
    unfold SupportA
    rw [sum_insert hloC, hsU]
  have hAV : SupportA (insert hi C) =
      3 ^ s * 2 ^ hi +
        C.sum fun j => 3 ^ OddsAfter (insert hi C) j * 2 ^ j := by
    unfold SupportA
    rw [sum_insert hhiC, hsV]
  have hterm : 3 ^ s * 2 ^ hi =
      3 ^ s * 2 ^ lo + 3 ^ s * 2 ^ lo * third := by
    rw [TwoPowSplit lo hi hlo, Nat.mul_add, ← Nat.mul_assoc]
  rw [hAV, hterm, hcommon, Nat.add_right_comm, ← hAU]

/-- Two supports that differ by one index move across an empty gap have
symmetric difference of size two, and the equal-halves modulus cannot divide
their numerator difference. The two indices determine the third factor
`2^(hi - lo) - 1`; coprimality of the modulus to six passes the divisibility
onto that factor, which is strictly smaller than the modulus. -/
theorem NoCrossingObstruction (h lo hi : ℕ) (C U V : Finset ℕ)
    (hU : U = insert lo C) (hV : V = insert hi C) (hlo : lo < hi)
    (hhi : hi < h) (hloC : lo ∉ C) (hhiC : hi ∉ C)
    (hwindow : ∀ x ∈ C, x < h) (hgap : ∀ x ∈ C, x < lo ∨ hi < x) :
    U ≠ V ∧
      symmDiff U V = {lo, hi} ∧
        (symmDiff U V).card = 2 ∧
          U.card = V.card ∧
            (∀ x ∈ U, x < h) ∧
              (∀ x ∈ V, x < h) ∧
                SupportA V =
                  SupportA U +
                    3 ^ (C.filter (fun k => hi < k)).card *
                      2 ^ lo * (2 ^ (hi - lo) - 1) ∧
                  Nat.Coprime (2 ^ h + 3 ^ U.card) 6 ∧
                    0 < 2 ^ (hi - lo) - 1 ∧
                      2 ^ (hi - lo) - 1 < 2 ^ h ∧
                        2 ^ h < 2 ^ h + 3 ^ U.card ∧
                          ((2 ^ h + 3 ^ U.card) ∣
                              3 ^ (C.filter (fun k => hi < k)).card *
                                2 ^ lo * (2 ^ (hi - lo) - 1) →
                            (2 ^ h + 3 ^ U.card) ∣ 2 ^ (hi - lo) - 1) ∧
                            ¬ (2 ^ h + 3 ^ U.card) ∣ 2 ^ (hi - lo) - 1 ∧
                              ¬ (2 ^ h + 3 ^ U.card) ∣
                                SupportA V - SupportA U := by
  subst hU
  subst hV
  let s : ℕ := (C.filter (fun k => hi < k)).card
  let third : ℕ := 2 ^ (hi - lo) - 1
  let M : ℕ := 2 ^ h + 3 ^ (insert lo C).card
  have hsym := NoCrossingSymmDiff lo hi C hlo hloC hhiC
  have hcard : (symmDiff (insert lo C) (insert hi C)).card = 2 := by
    rw [hsym]
    exact card_pair (Nat.ne_of_lt hlo)
  have hdistinct : insert lo C ≠ insert hi C := by
    intro hEq
    have hzero : ({lo, hi} : Finset ℕ).card = 0 := by
      rw [← hsym, (symmDiff_eq_empty).mpr hEq, card_empty]
    have htwo : ({lo, hi} : Finset ℕ).card = 2 :=
      card_pair (Nat.ne_of_lt hlo)
    exact absurd (htwo.symm.trans hzero) (by decide : (2 : ℕ) ≠ 0)
  have hcards : (insert lo C).card = (insert hi C).card := by
    rw [card_insert_of_notMem hloC, card_insert_of_notMem hhiC]
  have hUwin : ∀ x ∈ insert lo C, x < h := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hxC
    · exact Nat.lt_trans hlo hhi
    · exact hwindow x hxC
  have hVwin : ∀ x ∈ insert hi C, x < h := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hxC
    · exact hhi
    · exact hwindow x hxC
  have hdiff := NoCrossingDifference lo hi C hlo hloC hhiC hgap
  -- `h > 0` and `r > 0`, so the modulus is coprime to six and to the unit.
  have hh : 0 < h :=
    Nat.lt_of_le_of_lt (Nat.zero_le lo) (Nat.lt_trans hlo hhi)
  have hr : 0 < (insert lo C).card := by
    rw [card_insert_of_notMem hloC]
    exact Nat.zero_lt_succ C.card
  have hcop : Nat.Coprime M 6 := ModulusCoprimeSix h (insert lo C).card hh hr
  obtain ⟨hM2, hM3⟩ :=
    ModulusCoprimeTwoThree h (insert lo C).card hh hr
  have hunit : Nat.Coprime M (3 ^ s * 2 ^ lo) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow_right s hM3)
      (Nat.Coprime.pow_right lo hM2)
  have hforce : M ∣ 3 ^ s * 2 ^ lo * third → M ∣ third :=
    fun hd => Nat.Coprime.dvd_of_dvd_mul_left hunit hd
  have hδpos : 0 < hi - lo := Nat.sub_pos_of_lt hlo
  have hpos : 0 < third :=
    Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt hδpos))
  have hδlt : hi - lo < h := Nat.lt_of_le_of_lt (Nat.sub_le hi lo) hhi
  have hpowlt : 2 ^ (hi - lo) < 2 ^ h :=
    Nat.pow_lt_pow_of_lt (by decide) hδlt
  have hthirdPow : third < 2 ^ (hi - lo) :=
    Nat.sub_lt_of_pos_le Nat.zero_lt_one (Nat.one_le_two_pow (n := hi - lo))
  have hthirdH : third < 2 ^ h := Nat.lt_trans hthirdPow hpowlt
  have hMgt : 2 ^ h < M :=
    Nat.lt_add_of_pos_right ((Nat.pow_pos_iff).mpr (Or.inl (by decide)))
  have hthirdM : third < M := Nat.lt_trans hthirdH hMgt
  have hnot : ¬ M ∣ third := by
    intro hd
    exact Nat.ne_of_gt hpos (Nat.eq_zero_of_dvd_of_lt hd hthirdM)
  have hsub : SupportA (insert hi C) - SupportA (insert lo C) =
      3 ^ s * 2 ^ lo * third := by
    rw [hdiff, Nat.add_sub_cancel_left]
  have hnotDiff : ¬ M ∣ SupportA (insert hi C) - SupportA (insert lo C) := by
    intro hd
    exact hnot (hforce (by rwa [hsub] at hd))
  exact ⟨hdistinct, hsym, hcard, hcards, hUwin, hVwin, hdiff, hcop, hpos,
    hthirdH, hMgt, hforce, hnot, hnotDiff⟩

end GeneralizedCollatz
