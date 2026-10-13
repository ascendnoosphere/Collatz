-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import RhoComparison
import Mathlib.Data.Rat.BigOperators
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The rho weight on the classical label `j + 3`, read as a real number. -/
def LabelRho (j : ℕ) : ℝ := (Rho (j + 3) : ℝ)

/-- The mu weight on the same classical label `j + 3`. -/
def LabelMu (j : ℕ) : ℝ := (Mu (j + 3) : ℝ)

/-- The positive rho weights on all positive labels form a summable series. -/
theorem PositiveRhoSummable : Summable (fun j : ℕ => (Rho (j + 1) : ℝ)) := by
  refine summable_of_sum_range_le (c := 1) ?_ ?_
  · {
      intro j
      exact_mod_cast (le_of_lt (RhoPos (n := j + 1) (by omega)))
    }
  · {
      intro N
      have hsum := RhoPartialSum N
      have hbound : (N : ℚ) / ((N + 1 : ℕ) : ℚ) ≤ 1 := by
        have hd : (0 : ℚ) < ((N + 1 : ℕ) : ℚ) := by positivity
        apply (div_le_one hd).2
        exact_mod_cast (Nat.le_succ N)
      have hQ : ∑ j ∈ Finset.range N, Rho (j + 1) ≤ 1 := by
        rw [hsum]
        exact hbound
      exact_mod_cast hQ
    }

/-- Restricting rho to labels at least three preserves summability. -/
theorem LabelRhoSummable : Summable LabelRho := by
  have hi : Function.Injective (fun j : ℕ => j + 2) := by
    intro a b h
    change a + 2 = b + 2 at h
    omega
  have h := PositiveRhoSummable.comp_injective hi
  refine h.congr ?_
  intro j
  change (Rho ((j + 2) + 1) : ℝ) = (Rho (j + 3) : ℝ)
  congr 2

/-- The mu weights on labels at least three are summable, without a set hypothesis. -/
theorem LabelMuSummable : Summable LabelMu := by
  refine summable_of_sum_range_le (c := 1) ?_ ?_
  · {
      intro j
      unfold LabelMu
      exact_mod_cast (le_of_lt (MuPos (n := j + 3) (by omega)))
    }
  · {
      intro N
      have hsum := MuPartialSum (R := N + 2) (by omega)
      have hlen : N + 2 - 2 = N := by omega
      rw [hlen] at hsum
      have hQ : ∑ j ∈ Finset.range N, Mu (j + 3) ≤ 1 := by
        rw [hsum]
        have hnonneg : (0 : ℚ) ≤ 2 / ((N + 2 : ℕ) : ℚ) := by positivity
        linarith
      unfold LabelMu
      exact_mod_cast hQ
    }

/-- The rho source on all positive labels has total mass one. -/
theorem PositiveRhoTotal : (∑' j : ℕ, (Rho (j + 1) : ℝ)) = 1 := by
  open Filter Topology in
  have htail : Tendsto (fun N : ℕ => (1 : ℝ) / ((N + 1 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hpart (N : ℕ) : ∑ j ∈ Finset.range N, (Rho (j + 1) : ℝ) =
      1 - (1 : ℝ) / ((N + 1 : ℕ) : ℝ) := by
    have hQ := (RhoPartialSum N).trans (RhoClosed N)
    have hcast := congrArg (fun x : ℚ => (x : ℝ)) hQ
    simpa only [Rat.cast_sum, Rat.cast_sub, Rat.cast_div,
      Rat.cast_one, Rat.cast_natCast] using hcast
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub htail
  have hlimSum := hlim.congr' (Filter.Eventually.of_forall (fun N => (hpart N).symm))
  have htotal := PositiveRhoSummable.hasSum.tendsto_sum_nat
  simpa only [sub_zero] using tendsto_nhds_unique htotal hlimSum

/-- The unnormalized rho mass on the classical domain is one third. -/
theorem LabelRhoTotal : (∑' j : ℕ, LabelRho j) = (1 : ℝ) / 3 := by
  open Filter Topology in
  have htail : Tendsto (fun N : ℕ => (1 : ℝ) / ((N + 3 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 3).2 (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hpart (N : ℕ) : ∑ j ∈ Finset.range N, LabelRho j =
      (1 : ℝ) / 3 - (1 : ℝ) / ((N + 3 : ℕ) : ℝ) := by
    have hQ := RhoWindow (R := 2) (N := N + 2) (by omega)
    have hlen : N + 2 - 2 = N := by omega
    rw [hlen] at hQ
    simp only [Nat.add_assoc, Nat.reduceAdd] at hQ
    unfold LabelRho
    have hcast := congrArg (fun x : ℚ => (x : ℝ)) hQ
    simpa only [Rat.cast_sum, Rat.cast_sub, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast, Nat.cast_ofNat] using hcast
  have hlim := (tendsto_const_nhds (x := (1 : ℝ) / 3)).sub htail
  have hlimSum := hlim.congr' (Filter.Eventually.of_forall (fun N => (hpart N).symm))
  have htotal := LabelRhoSummable.hasSum.tendsto_sum_nat
  simpa only [sub_zero] using tendsto_nhds_unique htotal hlimSum

/-- The mu source on labels at least three has total mass one. -/
theorem LabelMuTotal : (∑' j : ℕ, LabelMu j) = 1 := by
  open Filter Topology in
  have htail : Tendsto (fun N : ℕ => (2 : ℝ) / ((N + 2 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  have hpart (N : ℕ) : ∑ j ∈ Finset.range N, LabelMu j =
      1 - (2 : ℝ) / ((N + 2 : ℕ) : ℝ) := by
    have hQ := MuPartialSum (R := N + 2) (by omega)
    have hlen : N + 2 - 2 = N := by omega
    rw [hlen] at hQ
    unfold LabelMu
    have hcast := congrArg (fun x : ℚ => (x : ℝ)) hQ
    simpa only [Rat.cast_sum, Rat.cast_sub, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast] using hcast
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub htail
  have hlimSum := hlim.congr' (Filter.Eventually.of_forall (fun N => (hpart N).symm))
  have htotal := LabelMuSummable.hasSum.tendsto_sum_nat
  simpa only [sub_zero] using tendsto_nhds_unique htotal hlimSum

/-- An arbitrary label set retains only its rho terms at labels at least three. -/
noncomputable def RhoSetTerm (S : Set ℕ) (j : ℕ) : ℝ := by
  classical
  exact if j + 3 ∈ S then LabelRho j else 0

/-- The same set restriction applied to the mu weights. -/
noncomputable def MuSetTerm (S : Set ℕ) (j : ℕ) : ℝ := by
  classical
  exact if j + 3 ∈ S then LabelMu j else 0

/-- Rho mass of a possibly infinite set, restricted to labels at least three. -/
noncomputable def RhoMass (S : Set ℕ) : ℝ := ∑' j, RhoSetTerm S j

/-- Mu mass of the identical set of labels. -/
noncomputable def MuMass (S : Set ℕ) : ℝ := ∑' j, MuSetTerm S j

/-- Both restricted terms are nonnegative and retain the pointwise comparison. -/
theorem LabelSetTermBounds (S : Set ℕ) (j : ℕ) :
    0 ≤ RhoSetTerm S j ∧ 0 ≤ MuSetTerm S j ∧
      2 * RhoSetTerm S j ≤ MuSetTerm S j ∧
      MuSetTerm S j ≤ 4 * RhoSetTerm S j := by
  classical
  by_cases h : j + 3 ∈ S
  · {
      simp only [RhoSetTerm, MuSetTerm, if_pos h, LabelRho, LabelMu]
      have hr := RhoPos (n := j + 3) (by omega)
      have hm := MuPos (n := j + 3) (by omega)
      have hb := TwoRhoLeMuLeFourRho (n := j + 3) (by omega)
      exact_mod_cast And.intro (le_of_lt hr) (And.intro (le_of_lt hm) hb)
    }
  · {
      simp [RhoSetTerm, MuSetTerm, h]
    }

/-- Every set restriction of rho is summable by domination by the full series. -/
theorem RhoSetSummable (S : Set ℕ) : Summable (RhoSetTerm S) := by
  classical
  refine Summable.of_nonneg_of_le (fun j => (LabelSetTermBounds S j).1) ?_
    LabelRhoSummable
  intro j
  by_cases h : j + 3 ∈ S
  · {
      simp [RhoSetTerm, h]
    }
  · {
      simp only [RhoSetTerm, if_neg h, LabelRho]
      exact_mod_cast (le_of_lt (RhoPos (n := j + 3) (by omega)))
    }

/-- Every set restriction of mu is summable by domination by its full series. -/
theorem MuSetSummable (S : Set ℕ) : Summable (MuSetTerm S) := by
  classical
  refine Summable.of_nonneg_of_le (fun j => (LabelSetTermBounds S j).2.1) ?_
    LabelMuSummable
  intro j
  by_cases h : j + 3 ∈ S
  · {
      simp [MuSetTerm, h]
    }
  · {
      simp only [MuSetTerm, if_neg h, LabelMu]
      exact_mod_cast (le_of_lt (MuPos (n := j + 3) (by omega)))
    }

/-- Infinite positive masses retain the factor interval for every label set. -/
theorem InfiniteLabelMassComparison (S : Set ℕ) :
    2 * RhoMass S ≤ MuMass S ∧ MuMass S ≤ 4 * RhoMass S := by
  have hlo := (RhoSetSummable S).mul_left (2 : ℝ)
  have hhi := (RhoSetSummable S).mul_left (4 : ℝ)
  have hmu := MuSetSummable S
  have hL := hlo.tsum_le_tsum (fun j => (LabelSetTermBounds S j).2.2.1) hmu
  have hH := hmu.tsum_le_tsum (fun j => (LabelSetTermBounds S j).2.2.2) hhi
  rw [(RhoSetSummable S).tsum_mul_left] at hL hH
  exact ⟨hL, hH⟩

/-- A rho mass is nonnegative, including for the empty label set. -/
theorem RhoMassNonneg (S : Set ℕ) : 0 ≤ RhoMass S := by
  exact tsum_nonneg (fun j => (LabelSetTermBounds S j).1)

/-- One member at least three forces strictly positive rho mass. -/
theorem RhoMassPosOfMember (S : Set ℕ) (n : ℕ) (hn : 3 ≤ n) (hmem : n ∈ S) :
    0 < RhoMass S := by
  classical
  let j := n - 3
  have hj : j + 3 = n := by dsimp [j]; omega
  have hp : 0 < RhoSetTerm S j := by
    simp only [RhoSetTerm, hj, if_pos hmem, LabelRho]
    exact_mod_cast (RhoPos (n := n) (by omega))
  have hle := (RhoSetSummable S).sum_le_tsum {j}
    (fun k _ => (LabelSetTermBounds S k).1)
  have hterm : RhoSetTerm S j ≤ RhoMass S := by
    simpa only [Finset.sum_singleton, RhoMass] using hle
  exact lt_of_lt_of_le hp hterm

/-- Any two possibly infinite label sets obey the quotient bound when rho(U)>0. -/
theorem InfiniteLabelFraction (C U : Set ℕ) (hu : 0 < RhoMass U) :
    (RhoMass C / RhoMass U) / 2 ≤ MuMass C / MuMass U ∧
      MuMass C / MuMass U ≤ 2 * (RhoMass C / RhoMass U) := by
  have hc0 := RhoMassNonneg C
  have hc := InfiniteLabelMassComparison C
  have hU := InfiniteLabelMassComparison U
  have hum : 0 < MuMass U := by linarith
  constructor
  · {
      rw [div_div, div_le_div_iff₀ (by positivity) hum]
      have h1 := mul_le_mul_of_nonneg_left hU.2 hc0
      have h2 := mul_le_mul_of_nonneg_right hc.1
        (show 0 ≤ RhoMass U * 2 by positivity)
      nlinarith
    }
  · {
      rw [← mul_div_assoc, div_le_div_iff₀ hum hu]
      have h1 := mul_le_mul_of_nonneg_right hc.2 (le_of_lt hu)
      have h2 := mul_le_mul_of_nonneg_left hU.1
        (show 0 ≤ 2 * RhoMass C by positivity)
      nlinarith
    }

end GeneralizedCollatz
