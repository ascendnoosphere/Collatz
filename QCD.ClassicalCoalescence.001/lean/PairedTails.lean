-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import SecondBurst

set_option autoImplicit false

namespace GeneralizedCollatz.ClassicalCoalescence

/-- Seven halvings followed by an odd letter evaluate the first eight-letter tail. -/
theorem TailOneRelation (x : ℕ) (hx : x % 256 = 128) :
    256 * Shortcut^[8] x = 3 * x + 128 := by
  have h0 := EvenRelation x (by omega)
  have h1 := EvenRelation (Shortcut x) (by omega)
  have h2 := EvenRelation (Shortcut^[2] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply]; omega)
  have h3 := EvenRelation (Shortcut^[3] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  have h4 := EvenRelation (Shortcut^[4] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  have h5 := EvenRelation (Shortcut^[5] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  have h6 := EvenRelation (Shortcut^[6] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  have h7 := OddRelation (Shortcut^[7] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *
  omega

/-- The tail `01000001` has two odd letters and the same centered offset. -/
theorem TailTwoRelation (x : ℕ) (hx : x % 256 = 42) :
    256 * Shortcut^[8] x = 9 * x + 134 := by
  have h0 := EvenRelation x (by omega)
  have h1 := OddRelation (Shortcut x) (by omega)
  have h2 := EvenRelation (Shortcut^[2] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply]; omega)
  have h3 := EvenRelation (Shortcut^[3] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  have h4 := EvenRelation (Shortcut^[4] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  have h5 := EvenRelation (Shortcut^[5] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  have h6 := EvenRelation (Shortcut^[6] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  have h7 := OddRelation (Shortcut^[7] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *
  omega

/-- The parent tail `01011100` removes three or two odd letters from the earlier run. -/
theorem TailFourRelation (x : ℕ) (hx : x % 256 = 146) :
    256 * Shortcut^[8] x = 81 * x + 206 := by
  have h0 := EvenRelation x (by omega)
  have h1 := OddRelation (Shortcut x) (by omega)
  have h2 := EvenRelation (Shortcut^[2] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply]; omega)
  have h3 := OddRelation (Shortcut^[3] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  have h4 := OddRelation (Shortcut^[4] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  have h5 := OddRelation (Shortcut^[5] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  have h6 := EvenRelation (Shortcut^[6] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  have h7 := EvenRelation (Shortcut^[7] x) (by
    norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *; omega)
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply] at *
  omega

/-- Equal centered offsets give a join after shortening the parent odd run by three. -/
theorem PairedThreeJoin (a k u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (he : 3 ^ a * u + 1 = 2 ^ (k + 4) * v)
    (hg : (3 ^ (k + 3) * v) % 256 = 129) :
    Shortcut^[a + k + 12] (2 ^ a * u - 1) = Shortcut^[k + 8] (2 ^ k * v - 1) := by
  have hentry := BurstEntrance a (k + 2) u v hu he
  have hs := OddRunShift (k + 3) v (k + 3) hv (le_refl _)
  have hp := OddRunShift k v k hv (le_refl _)
  simp only [Nat.sub_self, pow_zero, mul_one] at hs hp
  have hpow : 3 ^ (k + 3) * v = 27 * (3 ^ k * v) := by
    rw [pow_add]; ring
  have ht := TailOneRelation (Shortcut^[k + 3] (2 ^ (k + 3) * v - 1)) (by omega)
  have huword := TailFourRelation (Shortcut^[k] (2 ^ k * v - 1)) (by
    rw [hpow] at hg hs; omega)
  have hj : Shortcut^[8] (Shortcut^[k + 3] (2 ^ (k + 3) * v - 1)) =
      Shortcut^[8] (Shortcut^[k] (2 ^ k * v - 1)) := by
    rw [hpow] at hs
    omega
  have hfull : Shortcut^[a + k + 12] (2 ^ a * u - 1) =
      Shortcut^[8] (Shortcut^[k + 3] (2 ^ (k + 3) * v - 1)) := by
    rw [show a + k + 12 = 8 + ((k + 3) + (a + 1)) by omega,
      Function.iterate_add_apply, Function.iterate_add_apply]
    simpa only [show k + 2 + 1 = k + 3 by omega] using congrArg
      (fun z => Shortcut^[8] (Shortcut^[k + 3] z)) hentry
  have hpfull : Shortcut^[k + 8] (2 ^ k * v - 1) =
      Shortcut^[8] (Shortcut^[k] (2 ^ k * v - 1)) := by
    rw [show k + 8 = 8 + k by omega, Function.iterate_add_apply]
  exact hfull.trans (hj.trans hpfull.symm)

/-- A two-letter shortening reaches the opposite residue-three terminal guard. -/
theorem PairedTwoJoin (a k u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (he : 3 ^ a * u + 1 = 2 ^ (k + 3) * v)
    (hg : (3 ^ (k + 2) * v) % 256 = 43) :
    Shortcut^[a + k + 11] (2 ^ a * u - 1) = Shortcut^[k + 8] (2 ^ k * v - 1) := by
  have hentry := BurstEntrance a (k + 1) u v hu he
  have hs := OddRunShift (k + 2) v (k + 2) hv (le_refl _)
  have hp := OddRunShift k v k hv (le_refl _)
  simp only [Nat.sub_self, pow_zero, mul_one] at hs hp
  have hpow : 3 ^ (k + 2) * v = 9 * (3 ^ k * v) := by
    rw [pow_add]; ring
  have ht := TailTwoRelation (Shortcut^[k + 2] (2 ^ (k + 2) * v - 1)) (by omega)
  have huword := TailFourRelation (Shortcut^[k] (2 ^ k * v - 1)) (by
    rw [hpow] at hg hs; omega)
  have hj : Shortcut^[8] (Shortcut^[k + 2] (2 ^ (k + 2) * v - 1)) =
      Shortcut^[8] (Shortcut^[k] (2 ^ k * v - 1)) := by
    rw [hpow] at hs
    omega
  have hfull : Shortcut^[a + k + 11] (2 ^ a * u - 1) =
      Shortcut^[8] (Shortcut^[k + 2] (2 ^ (k + 2) * v - 1)) := by
    rw [show a + k + 11 = 8 + ((k + 2) + (a + 1)) by omega,
      Function.iterate_add_apply, Function.iterate_add_apply]
    simpa only [show k + 1 + 1 = k + 2 by omega] using congrArg
      (fun z => Shortcut^[8] (Shortcut^[k + 2] z)) hentry
  have hpfull : Shortcut^[k + 8] (2 ^ k * v - 1) =
      Shortcut^[8] (Shortcut^[k] (2 ^ k * v - 1)) := by
    rw [show k + 8 = 8 + k by omega, Function.iterate_add_apply]
  exact hfull.trans (hj.trans hpfull.symm)

/-- Three shortened letters contract each initial rank four through six. -/
theorem PairedThreeOrder (a k u v : ℕ) (ha : a = 4 ∨ a = 5 ∨ a = 6)
    (hu : 0 < u) (he : 3 ^ a * u + 1 = 2 ^ (k + 4) * v) :
    0 < 2 ^ k * v - 1 ∧ 2 ^ k * v - 1 < 2 ^ a * u - 1 ∧
      1024 * (2 ^ k * v - 1) ≤ 729 * (2 ^ a * u - 1) := by
  have hp : 2 ^ (k + 4) * v = 16 * (2 ^ k * v) := by
    rw [pow_add]; ring
  rw [hp] at he
  rcases ha with rfl | rfl | rfl <;> norm_num only [Nat.reducePow] at he ⊢ <;> omega

/-- Two shortened letters contract initial ranks two through four. -/
theorem PairedTwoOrder (a k u v : ℕ) (ha : a = 2 ∨ a = 3 ∨ a = 4)
    (hu : 0 < u) (he : 3 ^ a * u + 1 = 2 ^ (k + 3) * v) :
    0 < 2 ^ k * v - 1 ∧ 2 ^ k * v - 1 < 2 ^ a * u - 1 ∧
      128 * (2 ^ k * v - 1) ≤ 81 * (2 ^ a * u - 1) := by
  have hp : 2 ^ (k + 3) * v = 8 * (2 ^ k * v) := by
    rw [pow_add]; ring
  rw [hp] at he
  rcases ha with rfl | rfl | rfl <;> norm_num only [Nat.reducePow] at he ⊢ <;> omega

/-- The three-letter family is specified by arithmetic data rather than a desired parent. -/
def PairedThreeSource (a n : ℕ) : Prop :=
  ∃ k u v : ℕ, 0 < u ∧ Odd u ∧ 0 < v ∧ Odd v ∧
    3 ^ a * u + 1 = 2 ^ (k + 4) * v ∧
    (3 ^ (k + 3) * v) % 256 = 129 ∧ n + 1 = 2 ^ a * u

/-- The opposite-guard family retains its entrance equation and exact second length. -/
def PairedTwoSource (a n : ℕ) : Prop :=
  ∃ k u v : ℕ, 0 < u ∧ Odd u ∧ 0 < v ∧ Odd v ∧
    3 ^ a * u + 1 = 2 ^ (k + 3) * v ∧
    (3 ^ (k + 2) * v) % 256 = 43 ∧ n + 1 = 2 ^ a * u

/-- Every member at initial rank four through six has an original-source contracted parent. -/
theorem PairedThreeParent (a n : ℕ) (ha : a = 4 ∨ a = 5 ∨ a = 6)
    (h : PairedThreeSource a n) :
    ∃ p k : ℕ, 0 < p ∧ p < n ∧ 1024 * p ≤ 729 * n ∧ 9 * p ≤ 8 * n ∧
      Shortcut^[a + k + 12] n = Shortcut^[k + 8] p := by
  obtain ⟨k, u, v, hu, ho, hv, hvo, he, hg, hn⟩ := h
  have hseed : n = 2 ^ a * u - 1 := by omega
  obtain ⟨hpos, hlt, hbound⟩ := PairedThreeOrder a k u v ha hu he
  have hj := PairedThreeJoin a k u v hu hv he hg
  rw [← hseed] at hlt hbound hj
  exact ⟨2 ^ k * v - 1, k, hpos, hlt, hbound, by omega, hj⟩

/-- The residue-three family provides parents at initial rank two through four. -/
theorem PairedTwoParent (a n : ℕ) (ha : a = 2 ∨ a = 3 ∨ a = 4)
    (h : PairedTwoSource a n) :
    ∃ p k : ℕ, 0 < p ∧ p < n ∧ 128 * p ≤ 81 * n ∧ 9 * p ≤ 8 * n ∧
      Shortcut^[a + k + 11] n = Shortcut^[k + 8] p := by
  obtain ⟨k, u, v, hu, ho, hv, hvo, he, hg, hn⟩ := h
  have hseed : n = 2 ^ a * u - 1 := by omega
  obtain ⟨hpos, hlt, hbound⟩ := PairedTwoOrder a k u v ha hu he
  have hj := PairedTwoJoin a k u v hu hv he hg
  rw [← hseed] at hlt hbound hj
  exact ⟨2 ^ k * v - 1, k, hpos, hlt, hbound, by omega, hj⟩

/-- A whole multiple-of-three source cylinder joins the three-shortening parent cylinder. -/
theorem PairedThreeCylinderJoin (t : ℕ) :
    Shortcut^[16] (137199 + 5308416 * t) =
      Shortcut^[8] (43410 + 1679616 * t) := by
  have h := PairedThreeJoin 4 0 (8575 + 331776 * t) (43411 + 1679616 * t)
    (by omega) (by omega) (by norm_num; ring)
    (by norm_num [Nat.add_mod, Nat.mul_mod])
  norm_num only [Nat.reduceAdd, Nat.reducePow, one_mul] at h
  have hn : 16 * (8575 + 331776 * t) - 1 = 137199 + 5308416 * t := by omega
  have hp : 43411 + 1679616 * t - 1 = 43410 + 1679616 * t := by omega
  simpa only [hn, hp] using h

/-- The common endpoint of that cylinder is determined without an orbit search. -/
theorem PairedThreeCylinderEndpoint (t : ℕ) :
    Shortcut^[8] (43410 + 1679616 * t) = 13736 + 531441 * t := by
  have h := TailFourRelation (43410 + 1679616 * t) (by omega)
  omega

/-- Every three-shortening source cylinder member survives the earlier residue exclusions. -/
theorem PairedThreeCylinderResidual (t : ℕ) :
    Residual (137199 + 5308416 * t) ∧ (137199 + 5308416 * t) % 3 = 0 ∧
      (137199 + 5308416 * t) % 9 ≠ 4 ∧
      (137199 + 5308416 * t) % 32 ≠ 11 ∧
      (137199 + 5308416 * t) % 81 ≠ 10 := by
  have hr : Residual (137199 + 5308416 * t) := by
    refine ⟨4, 8575 + 331776 * t, by decide, by omega, ?_, ?_, ?_, by ring⟩
    · exact ⟨4287 + 165888 * t, by ring⟩
    · intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      norm_num [Nat.add_mod, Nat.mul_mod] at hz
    · norm_num [Nat.add_mod, Nat.mul_mod]
  exact ⟨hr, by omega, by omega, by omega, by omega⟩

/-- The opposite-guard cylinder joins a parent with an empty initial odd run. -/
theorem PairedTwoCylinderJoin (t : ℕ) :
    Shortcut^[13] (7803 + 663552 * t) = Shortcut^[8] (2194 + 186624 * t) := by
  have h := PairedTwoJoin 2 0 (1951 + 165888 * t) (2195 + 186624 * t)
    (by omega) (by omega) (by norm_num; ring)
    (by norm_num [Nat.add_mod, Nat.mul_mod])
  norm_num only [Nat.reduceAdd, Nat.reducePow, one_mul] at h
  have hn : 4 * (1951 + 165888 * t) - 1 = 7803 + 663552 * t := by omega
  have hp : 2195 + 186624 * t - 1 = 2194 + 186624 * t := by omega
  simpa only [hn, hp] using h

/-- The opposite-guard common endpoint is a linear cylinder as well. -/
theorem PairedTwoCylinderEndpoint (t : ℕ) :
    Shortcut^[8] (2194 + 186624 * t) = 695 + 59049 * t := by
  have h := TailFourRelation (2194 + 186624 * t) (by omega)
  omega

/-- The opposite-guard cylinder is residual and consists entirely of multiples of three. -/
theorem PairedTwoCylinderResidual (t : ℕ) :
    Residual (7803 + 663552 * t) ∧ (7803 + 663552 * t) % 3 = 0 ∧
      (7803 + 663552 * t) % 9 ≠ 4 ∧ (7803 + 663552 * t) % 32 ≠ 11 ∧
      (7803 + 663552 * t) % 81 ≠ 10 := by
  have hr : Residual (7803 + 663552 * t) := by
    refine ⟨2, 1951 + 165888 * t, by decide, by omega, ?_, ?_, ?_, by ring⟩
    · exact ⟨975 + 82944 * t, by ring⟩
    · intro hd
      have hz := Nat.mod_eq_zero_of_dvd hd
      norm_num [Nat.add_mod, Nat.mul_mod] at hz
    · norm_num [Nat.add_mod, Nat.mul_mod]
  exact ⟨hr, by omega, by omega, by omega, by omega⟩

end GeneralizedCollatz.ClassicalCoalescence
