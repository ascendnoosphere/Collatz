-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import TerminalConverse

set_option autoImplicit false

namespace GeneralizedCollatz.ClassicalCoalescence

/-- Two legal halving letters are detected by divisibility by four. -/
theorem TwoHalvingRelation (x : ℕ) (hx : x % 4 = 0) :
    4 * Shortcut^[2] x = x := by
  have h0 := EvenRelation x (by omega : x % 2 = 0)
  have h1 := EvenRelation (Shortcut x) (by omega : Shortcut x % 2 = 0)
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  omega

/-- One halving and one odd letter are detected by the residue two modulo four. -/
theorem HalvingOddRelation (x : ℕ) (hx : x % 4 = 2) :
    4 * Shortcut^[2] x = 3 * x + 2 := by
  have h0 := EvenRelation x (by omega : x % 2 = 0)
  have h1 := OddRelation (Shortcut x) (by omega : Shortcut x % 2 = 1)
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  omega

/-- The entrance equation locates the second odd run after one halving. -/
theorem BurstEntrance (a k u v : ℕ) (hu : 0 < u)
    (he : 3 ^ a * u + 1 = 2 ^ (k + 2) * v) :
    Shortcut^[a + 1] (2 ^ a * u - 1) = 2 ^ (k + 1) * v - 1 := by
  have hrun := OddRunShift a u a hu (le_refl a)
  simp only [Nat.sub_self, pow_zero, mul_one] at hrun
  have hp : 2 ^ (k + 2) * v = 2 * (2 ^ (k + 1) * v) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring
  rw [hp] at he
  have hhalf := EvenRelation (Shortcut^[a] (2 ^ a * u - 1)) (by omega)
  rw [← Function.iterate_succ_apply' Shortcut a (2 ^ a * u - 1)] at hhalf
  simp only [Nat.succ_eq_add_one] at hhalf
  omega

/-- Removing one odd letter from the parent run produces the same guarded endpoint. -/
theorem BurstJoin (a k u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (he : 3 ^ a * u + 1 = 2 ^ (k + 2) * v)
    (hguard : (3 ^ (k + 1) * v) % 4 = 1) :
    Shortcut^[a + k + 4] (2 ^ a * u - 1) = Shortcut^[k + 2] (2 ^ k * v - 1) := by
  have hentry := BurstEntrance a k u v hu he
  have hsource := OddRunShift (k + 1) v (k + 1) hv (le_refl _)
  simp only [Nat.sub_self, pow_zero, mul_one] at hsource
  have hparent := OddRunShift k v k hv (le_refl _)
  simp only [Nat.sub_self, pow_zero, mul_one] at hparent
  have hpow : 3 ^ (k + 1) * v = 3 * (3 ^ k * v) := by
    rw [pow_succ]
    ring
  have hpmod : (3 ^ k * v) % 4 = 3 := by
    rw [hpow] at hguard
    omega
  have hs := TwoHalvingRelation (Shortcut^[k + 1] (2 ^ (k + 1) * v - 1))
    (by omega)
  have hp := HalvingOddRelation (Shortcut^[k] (2 ^ k * v - 1)) (by omega)
  have hjoin : Shortcut^[2] (Shortcut^[k + 1] (2 ^ (k + 1) * v - 1)) =
      Shortcut^[2] (Shortcut^[k] (2 ^ k * v - 1)) := by omega
  have hsfull : Shortcut^[a + k + 4] (2 ^ a * u - 1) =
      Shortcut^[2] (Shortcut^[k + 1] (2 ^ (k + 1) * v - 1)) := by
    rw [show a + k + 4 = 2 + ((k + 1) + (a + 1)) by omega,
      Function.iterate_add_apply, Function.iterate_add_apply, hentry]
  have hpfull : Shortcut^[k + 2] (2 ^ k * v - 1) =
      Shortcut^[2] (Shortcut^[k] (2 ^ k * v - 1)) := by
    rw [show k + 2 = 2 + k by omega, Function.iterate_add_apply]
  exact hsfull.trans (hjoin.trans hpfull.symm)

/-- The two-letter initial burst yields a parent below nine sixteenths of the source. -/
theorem TwoBurstOrder (k u v : ℕ) (hu : 0 < u)
    (he : 9 * u + 1 = 2 ^ (k + 2) * v) :
    0 < 2 ^ k * v - 1 ∧ 16 * (2 ^ k * v - 1) + 3 = 9 * (4 * u - 1) ∧
      2 ^ k * v - 1 < 4 * u - 1 ∧ 7 * (2 ^ k * v - 1) ≤ 6 * (4 * u - 1) := by
  have hp : 2 ^ (k + 2) * v = 4 * (2 ^ k * v) := by
    rw [pow_add]
    ring
  rw [hp] at he
  omega

/-- The three-letter initial burst has a uniform six-sevenths original-source bound. -/
theorem ThreeBurstOrder (k u v : ℕ) (hu : 0 < u)
    (he : 27 * u + 1 = 2 ^ (k + 2) * v) :
    0 < 2 ^ k * v - 1 ∧ 32 * (2 ^ k * v - 1) = 27 * (8 * u - 1) + 3 ∧
      2 ^ k * v - 1 < 8 * u - 1 ∧ 7 * (2 ^ k * v - 1) ≤ 6 * (8 * u - 1) := by
  have hp : 2 ^ (k + 2) * v = 4 * (2 ^ k * v) := by
    rw [pow_add]
    ring
  rw [hp] at he
  omega

/-- Membership records arithmetic guards independently of any proposed join. -/
def BurstSource (a n : ℕ) : Prop :=
  ∃ k u v : ℕ, 0 < u ∧ Odd u ∧ 0 < v ∧
    3 ^ a * u + 1 = 2 ^ (k + 2) * v ∧
    (3 ^ (k + 1) * v) % 4 = 1 ∧ n + 1 = 2 ^ a * u

/-- Either short initial burst supplies one contracted parent for every legal second length. -/
theorem TwoThreeBurstParent (a n : ℕ) (ha : a = 2 ∨ a = 3) (h : BurstSource a n) :
    ∃ p k : ℕ, 0 < p ∧ p < n ∧ 7 * p ≤ 6 * n ∧
      Shortcut^[a + k + 4] n = Shortcut^[k + 2] p := by
  obtain ⟨k, u, v, hu, ho, hv, he, hg, hn⟩ := h
  have hnseed : n = 2 ^ a * u - 1 := by omega
  have hjoin := BurstJoin a k u v hu hv he hg
  rw [← hnseed] at hjoin
  rcases ha with htwo | hthree
  {
    subst a
    norm_num only [Nat.reducePow] at he hnseed
    obtain ⟨hpos, heq, hlt, hbound⟩ := TwoBurstOrder k u v hu he
    refine ⟨2 ^ k * v - 1, k, hpos, ?_, ?_, hjoin⟩
    · rwa [hnseed]
    · rwa [hnseed]
  }
  {
    subst a
    norm_num only [Nat.reducePow] at he hnseed
    obtain ⟨hpos, heq, hlt, hbound⟩ := ThreeBurstOrder k u v hu he
    refine ⟨2 ^ k * v - 1, k, hpos, ?_, ?_, hjoin⟩
    · rwa [hnseed]
    · rwa [hnseed]
  }

/-- The two-burst residual cylinder joins an entire contracted parent cylinder. -/
theorem BurstTwoCylinderJoin (t : ℕ) :
    Shortcut^[9] (411 + 1536 * t) = Shortcut^[5] (231 + 864 * t) := by
  have h := BurstJoin 2 3 (103 + 384 * t) (29 + 108 * t) (by omega) (by omega)
    (by norm_num; ring) (by norm_num [Nat.add_mod, Nat.mul_mod])
  norm_num only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMul] at h
  have hn : 4 * (103 + 384 * t) - 1 = 411 + 1536 * t := by omega
  have hp : 8 * (29 + 108 * t) - 1 = 231 + 864 * t := by omega
  simpa only [hn, hp] using h

/-- Every source of the two-burst cylinder belongs to the earlier residual. -/
theorem BurstTwoCylinderResidual (t : ℕ) :
    Residual (411 + 1536 * t) ∧ (411 + 1536 * t) % 9 ≠ 4 ∧
      (411 + 1536 * t) % 32 ≠ 11 ∧ (411 + 1536 * t) % 81 ≠ 10 := by
  have hr : Residual (411 + 1536 * t) := by
    refine ⟨2, 103 + 384 * t, by decide, by omega, ?_, ?_, ?_, by ring⟩
    · exact ⟨51 + 192 * t, by ring⟩
    · intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      norm_num [Nat.add_mod, Nat.mul_mod] at hz
    · norm_num [Nat.add_mod, Nat.mul_mod]
  exact ⟨hr, by omega, by omega, by omega⟩

/-- The three-burst residual cylinder has a join before any source descent. -/
theorem BurstThreeCylinderJoin (t : ℕ) :
    Shortcut^[10] (615 + 3072 * t) = Shortcut^[5] (519 + 2592 * t) := by
  have h := BurstJoin 3 3 (77 + 384 * t) (65 + 324 * t) (by omega) (by omega)
    (by norm_num; ring) (by norm_num [Nat.add_mod, Nat.mul_mod])
  norm_num only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMul] at h
  have hn : 8 * (77 + 384 * t) - 1 = 615 + 3072 * t := by omega
  have hp : 8 * (65 + 324 * t) - 1 = 519 + 2592 * t := by omega
  simpa only [hn, hp] using h

/-- The new cylinder is outside every earlier removal and has a different initial burst. -/
theorem BurstThreeCylinderResidual (t : ℕ) :
    Residual (615 + 3072 * t) ∧ (615 + 3072 * t) % 9 ≠ 4 ∧
      (615 + 3072 * t) % 32 ≠ 11 ∧ (615 + 3072 * t) % 81 ≠ 10 := by
  have hr : Residual (615 + 3072 * t) := by
    refine ⟨3, 77 + 384 * t, by decide, by omega, ?_, ?_, ?_, by ring⟩
    · exact ⟨38 + 192 * t, by ring⟩
    · intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      norm_num [Nat.add_mod, Nat.mul_mod] at hz
    · norm_num [Nat.add_mod, Nat.mul_mod]
  exact ⟨hr, by omega, by omega, by omega⟩

end GeneralizedCollatz.ClassicalCoalescence
