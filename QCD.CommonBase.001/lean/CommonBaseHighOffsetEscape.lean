-- SPDX-License-Identifier: CC-BY-4.0
import CommonBaseHighOffsetNormalization
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Signed interstitial magnitude recovery and effective full-sequence high-offset escape.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The complete phase kernel has a positive coefficient, including its constant term. -/
theorem WholeBaseGeometricSumPositive (t v : ℕ) (vPositive : 0 < v) :
    0 < WholeBaseGeometricSum t v := by
  have single : (t : ℤ) ^ (⟨0, vPositive⟩ : Fin v).val ≤
      ∑ i : Fin v, (t : ℤ) ^ i.val :=
    Finset.single_le_sum (f := fun i : Fin v => (t : ℤ) ^ i.val)
      (fun i _ => pow_nonneg (Nat.cast_nonneg t) i.val)
      (Finset.mem_univ (⟨0, vPositive⟩ : Fin v))
  have lower : (1 : ℤ) ≤ WholeBaseGeometricSum t v := by
    simpa [WholeBaseGeometricSum] using single
  omega

/-- Same-sign corrections cannot diminish the signed residual's magnitude. -/
theorem WholeBaseSignedResidualBound (w s b : ℤ) (aligned : 0 ≤ s * w)
    (bNonnegative : 0 ≤ b) : w.natAbs ≤ (w + s * b).natAbs := by
  by_cases zero : w = 0
  · simp [zero]
  · have comparison : (w.natAbs : ℤ) ≤ ((w + s * b).natAbs : ℤ) := by
      by_cases positive : 0 < w
      · have sNonnegative := nonneg_of_mul_nonneg_left aligned positive
        have correction := mul_nonneg sNonnegative bNonnegative
        have total : 0 ≤ w + s * b := by omega
        rw [Int.natCast_natAbs, Int.natCast_natAbs,
          abs_of_nonneg (le_of_lt positive), abs_of_nonneg total]
        omega
      · have negative : w < 0 := by omega
        have sNonpositive := nonpos_of_mul_nonneg_left aligned negative
        have correction := mul_nonpos_of_nonpos_of_nonneg sNonpositive bNonnegative
        have total : w + s * b ≤ 0 := by omega
        rw [Int.natCast_natAbs, Int.natCast_natAbs,
          abs_of_nonpos (le_of_lt negative), abs_of_nonpos total]
        omega
    exact_mod_cast comparison

/-- Actual event clocks are positive and have at most one raw interior state. -/
theorem WholeBaseHighOffsetClockBounds (p : Parameters) (n : ℤ) :
    1 ≤ WholeBaseHighOffsetEventClock p n ∧ WholeBaseHighOffsetEventClock p n ≤ 2 := by
  unfold WholeBaseHighOffsetEventClock
  split <;> omega

/-- After sign alignment, every raw time retains the initial residual magnitude. -/
theorem WholeBaseHighOffsetAlignedMagnitude (p : Parameters) (t u v a k : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (uBelow : u < v) (kBelow : k < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt t n k) (aligned : 0 ≤ s * n) :
    ∀ r : ℕ, n.natAbs ≤ ((t : ℤ) ^ k).natAbs * (Iterate (RawStep p) r n).natAbs := by
  rcases atOrder with ⟨w, state, guard⟩
  have basePositive : (0 : ℤ) < t := by omega
  have powerPositive : (0 : ℤ) < (t : ℤ) ^ k := pow_pos basePositive _
  have residualAligned : 0 ≤ s * w := by
    have product : 0 ≤ (s * w) * (t : ℤ) ^ k := by
      have rearranged : (s * w) * (t : ℤ) ^ k = s * n := by rw [state]; ring
      rw [rearranged]
      exact aligned
    exact nonneg_of_mul_nonneg_left product powerPositive
  intro r
  obtain ⟨i, inside, _, insideBound, time⟩ := PositiveClockCover
    (WholeBaseHighOffsetEvent p) (WholeBaseHighOffsetEventClock p)
    (fun x => (WholeBaseHighOffsetClockBounds p x).1) n r
  let x := Iterate (WholeBaseHighOffsetEvent p) i n
  let b : ℤ := ∑ j ∈ Finset.range i, (t : ℤ) ^ (a - u - (k + j * u) % v)
  have bNonnegative : 0 ≤ b :=
    Finset.sum_nonneg (fun j _ => pow_nonneg (le_of_lt basePositive) _)
  have value : x = (t : ℤ) ^ ((k + i * u) % v) * (w + s * b) :=
    WholeBaseHighOffsetResidualTrace p t u v a k s n w tLower uBelow kBelow
      highOffset divisor multiplier offset ⟨w, state, guard⟩ state i
  have residualBound := WholeBaseSignedResidualBound w s b residualAligned bNonnegative
  have phasePositive : (0 : ℤ) < (t : ℤ) ^ ((k + i * u) % v) :=
    pow_pos basePositive _
  have phaseMagnitude : 0 < ((t : ℤ) ^ ((k + i * u) % v)).natAbs :=
    Int.natAbs_pos.mpr (ne_of_gt phasePositive)
  have sampledBound : w.natAbs ≤ x.natAbs := by
    rw [value, Int.natAbs_mul]
    exact residualBound.trans (Nat.le_mul_of_pos_left _ phaseMagnitude)
  have sampledAligned : 0 ≤ s * x := by
    have correction : 0 ≤ s ^ 2 * b := mul_nonneg (sq_nonneg s) bNonnegative
    have residual : 0 ≤ s * (w + s * b) := by nlinarith [residualAligned]
    have product := mul_nonneg (le_of_lt phasePositive) residual
    rw [value]
    nlinarith only [product]
  have trace := WholeBaseHighOffsetEventTrace p t u v a k s n tLower uBelow kBelow
    highOffset divisor multiplier offset ⟨w, state, guard⟩ i
  have affineAligned : 0 ≤ s * ((t : ℤ) ^ u * x) := by
    have product := mul_nonneg (pow_nonneg (le_of_lt basePositive) u) sampledAligned
    nlinarith only [product]
  have affineBound : x.natAbs ≤ (RawStep p x).natAbs := by
    have positiveMultiplier : 0 < ((t : ℤ) ^ u).natAbs :=
      Int.natAbs_pos.mpr (ne_of_gt (pow_pos basePositive u))
    have scaled : x.natAbs ≤ ((t : ℤ) ^ u * x).natAbs := by
      rw [Int.natAbs_mul]
      exact Nat.le_mul_of_pos_left _ positiveMultiplier
    have correction := WholeBaseSignedResidualBound ((t : ℤ) ^ u * x) s
      ((t : ℤ) ^ a) affineAligned (pow_nonneg (le_of_lt basePositive) a)
    have step : RawStep p x = (t : ℤ) ^ u * x + s * (t : ℤ) ^ a := by
      rw [RawStep, if_neg trace.2, multiplier, offset]
      ring
    rw [step]
    exact scaled.trans correction
  have raw : Iterate (RawStep p) r n = Iterate (RawStep p) inside x := by
    rw [time, IterateAdd, ← WholeBaseHighOffsetEventRawIterates]
  have small : inside = 0 ∨ inside = 1 := by
    have upper := (WholeBaseHighOffsetClockBounds p x).2
    change inside < WholeBaseHighOffsetEventClock p x at insideBound
    omega
  have rawBound : w.natAbs ≤ (Iterate (RawStep p) r n).natAbs := by
    rw [raw]
    rcases small with zero | one
    · simpa [zero, Iterate] using sampledBound
    · simpa [one, Iterate] using sampledBound.trans affineBound
  conv_lhs => rw [state, Int.natAbs_mul]
  exact Nat.mul_le_mul_left _ rawBound

/-- Divisor-power form of the aligned magnitude bound, under positive multiplier order. -/
theorem WholeBaseHighOffsetAlignedDivisorMagnitude (p : Parameters) (t u v a k : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (uPositive : 0 < u) (uBelow : u < v)
    (kBelow : k < v) (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt t n k) (aligned : 0 ≤ s * n) :
    ∀ r : ℕ, n.natAbs ≤ (p.D ^ u).natAbs * (Iterate (RawStep p) r n).natAbs := by
  have powerIdentity : (p.D ^ u).natAbs = t ^ (v * u) := by
    rw [divisor, ← pow_mul, Int.natAbs_pow, Int.natAbs_natCast]
  have exponentLe : k ≤ v * u := by
    have oneLe : 1 ≤ u := Nat.succ_le_of_lt uPositive
    have step : v ≤ v * u := by
      simpa using Nat.mul_le_mul_left v oneLe
    omega
  have baseLe : t ^ k ≤ t ^ (v * u) := Nat.pow_le_pow_right (by omega) exponentLe
  intro r
  have alignedBound := WholeBaseHighOffsetAlignedMagnitude p t u v a k s n tLower
    uBelow kBelow highOffset divisor multiplier offset atOrder aligned r
  have natBound : n.natAbs ≤ t ^ k * (Iterate (RawStep p) r n).natAbs := by
    simpa [Int.natAbs_pow, Int.natAbs_natCast] using alignedBound
  calc n.natAbs ≤ t ^ k * (Iterate (RawStep p) r n).natAbs := natBound
    _ ≤ t ^ (v * u) * (Iterate (RawStep p) r n).natAbs :=
        Nat.mul_le_mul_right _ baseLe
    _ = (p.D ^ u).natAbs * (Iterate (RawStep p) r n).natAbs := by rw [powerIdentity]

/-- A nonzero integer translation crosses into its own sign at an explicit finite index. -/
theorem WholeBaseSignedRayCrossing (x beta : ℤ) (M K : ℕ) (betaNonzero : beta ≠ 0) :
    let j := x.natAbs + 1 + M * K
    0 < beta * (x + (j : ℤ) * beta) ∧ M * K < (x + (j : ℤ) * beta).natAbs := by
  let j := x.natAbs + 1 + M * K
  have index : (j : ℤ) = (x.natAbs : ℤ) + 1 + (M * K : ℕ) := by simp [j]
  have indexNonnegative : (0 : ℤ) ≤ j := Nat.cast_nonneg j
  have thresholdNonnegative : (0 : ℤ) ≤ (M * K : ℕ) := Nat.cast_nonneg _
  by_cases betaPositive : 0 < beta
  · have scaled : (j : ℤ) ≤ (j : ℤ) * beta := by
      have coefficient : (1 : ℤ) ≤ beta := by omega
      simpa using mul_le_mul_of_nonneg_left coefficient indexNonnegative
    have initial : -(x.natAbs : ℤ) ≤ x := by
      simpa [Int.natCast_natAbs] using neg_abs_le x
    have late : (M * K : ℕ) < x + (j : ℤ) * beta := by omega
    have positive : 0 < x + (j : ℤ) * beta := by omega
    refine ⟨mul_pos betaPositive positive, ?_⟩
    have magnitude : (M * K : ℕ) < ((x + (j : ℤ) * beta).natAbs : ℤ) := by
      rw [Int.natAbs_of_nonneg (le_of_lt positive)]
      exact late
    exact_mod_cast magnitude
  · have betaNegative : beta < 0 := by omega
    have scaled : (j : ℤ) * beta ≤ -(j : ℤ) := by
      have coefficient : beta ≤ (-1 : ℤ) := by omega
      simpa using mul_le_mul_of_nonneg_left coefficient indexNonnegative
    have initial : x ≤ (x.natAbs : ℤ) := Int.le_natAbs
    have late : x + (j : ℤ) * beta < -(M * K : ℕ) := by omega
    have negative : x + (j : ℤ) * beta < 0 := by omega
    refine ⟨mul_pos_of_neg_of_neg betaNegative negative, ?_⟩
    have magnitude : (M * K : ℕ) < ((x + (j : ℤ) * beta).natAbs : ℤ) := by
      rw [Int.natCast_natAbs, abs_of_nonpos (le_of_lt negative)]
      omega
    exact_mod_cast magnitude

/-- Every nonzero signed seed escapes at all sufficiently late raw times with a finite budget. -/
theorem WholeBaseHighOffsetRawEscape (p : Parameters) (t u v a : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uPositive : 0 < u) (uBelow : u < v) (highOffset : u + v ≤ a)
    (coprime : Nat.Coprime u v) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) :
    ∀ M r : ℕ, n.natAbs + (n.natAbs + 1 + M * (p.D ^ u).natAbs) * (u + v) ≤ r →
      M < (Iterate (RawStep p) r n).natAbs := by
  obtain ⟨start, k, x, startBound, kBelow, reached, atOrder, initialMagnitude⟩ :=
    WholeBaseNormalizeRaw p t v n tLower (by omega) divisor nNonzero
  let K := ((t : ℤ) ^ k).natAbs
  let gamma := (t : ℤ) ^ (a - u - v + 1 + k) * WholeBaseGeometricSum t v
  let beta := s * gamma
  have gammaPositive : 0 < gamma := mul_pos (pow_pos (by omega : (0 : ℤ) < t) _)
    (WholeBaseGeometricSumPositive t v (by omega))
  have betaNonzero : beta ≠ 0 := mul_ne_zero sNonzero (ne_of_gt gammaPositive)
  have denominator : K ≤ (p.D ^ u).natAbs := by
    have exponent : k ≤ v * u :=
      (Nat.le_of_lt kBelow).trans (Nat.le_mul_of_pos_right _ uPositive)
    have powers := Nat.pow_le_pow_right (by omega : 0 < t) exponent
    simpa [K, divisor, Int.natAbs_pow, ← pow_mul] using powers
  intro M r after
  let j := x.natAbs + 1 + M * K
  let y := x + (j : ℤ) * beta
  have crossing := WholeBaseSignedRayCrossing x beta M K betaNonzero
  change 0 < beta * y ∧ M * K < y.natAbs at crossing
  have endpoint : Iterate (RawStep p) (start + j * (u + v)) n = y := by
    rw [IterateAdd, reached]
    simpa [y, beta, gamma, mul_assoc] using
      (WholeBaseHighOffsetRawRay p t u v a k s x tLower uBelow kBelow
        highOffset coprime divisor multiplier offset atOrder j).2
  have lateOrder : WholeBaseOrderAt t y k := by
    have ray := WholeBaseHighOffsetRawRay p t u v a k s x tLower uBelow kBelow
      highOffset coprime divisor multiplier offset atOrder j
    have ordered := ray.1
    rw [ray.2] at ordered
    simpa [y, beta, gamma, mul_assoc] using ordered
  have aligned : 0 ≤ s * y := by
    have product : 0 < (s * y) * gamma := by
      have rearranged : (s * y) * gamma = beta * y := by dsimp [beta]; ring
      rw [rearranged]
      exact crossing.1
    exact le_of_lt (pos_of_mul_pos_left product (le_of_lt gammaPositive))
  have indexBound : j ≤ n.natAbs + 1 + M * (p.D ^ u).natAbs := by
    have magnitudes := Nat.mul_le_mul_left M denominator
    dsimp [j]
    omega
  have cutoff : start + j * (u + v) ≤ r :=
    (Nat.add_le_add startBound (Nat.mul_le_mul_right (u + v) indexBound)).trans after
  have time : r = (start + j * (u + v)) + (r - (start + j * (u + v))) := by omega
  have tail : Iterate (RawStep p) r n =
      Iterate (RawStep p) (r - (start + j * (u + v))) y := by
    conv_lhs => rw [time, IterateAdd, endpoint]
  have recovery := WholeBaseHighOffsetAlignedMagnitude p t u v a k s y tLower
    uBelow kBelow highOffset divisor multiplier offset lateOrder aligned
    (r - (start + j * (u + v)))
  change y.natAbs ≤ K *
    (Iterate (RawStep p) (r - (start + j * (u + v))) y).natAbs at recovery
  have growth := crossing.2.trans_le recovery
  rw [Nat.mul_comm M K] at growth
  rw [tail]
  exact Nat.lt_of_mul_lt_mul_left growth

/-- Positive multiplier and divisor preserve a strict offset-aligned sign at every raw step. -/
theorem WholeBaseHighOffsetSignInvariant (p : Parameters) (t u v a : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (aligned : 0 < s * n) : ∀ r : ℕ, 0 < s * Iterate (RawStep p) r n := by
  have basePositive : (0 : ℤ) < t := by omega
  have divisorPositive : 0 < p.D := by rw [divisor]; exact pow_pos basePositive _
  have multiplierPositive : 0 < p.Q := by rw [multiplier]; exact pow_pos basePositive _
  have offsetAligned : 0 ≤ s * p.C := by
    have product := mul_nonneg (pow_nonneg (le_of_lt basePositive) a) (sq_nonneg s)
    rw [offset]
    nlinarith only [product]
  intro r
  induction r with
  | zero => { simpa [Iterate] using aligned }
  | succ r ih => {
      let x := Iterate (RawStep p) r n
      change 0 < s * RawStep p x
      by_cases division : p.D ∣ x
      · have quotient : RawStep p x * p.D = x := by
          rw [RawStep, if_pos division]
          exact Int.ediv_mul_cancel division
        have positive : 0 < (s * RawStep p x) * p.D := by
          rw [mul_assoc, quotient]
          exact ih
        exact pos_of_mul_pos_left positive (le_of_lt divisorPositive)
      · have product := mul_pos multiplierPositive ih
        rw [RawStep, if_neg division]
        nlinarith only [product, offsetAligned]
    }

/-- Every nonzero signed seed enters the offset's sign within the zero-threshold budget. -/
theorem WholeBaseHighOffsetEventuallyAligned (p : Parameters) (t u v a : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (uPositive : 0 < u) (uBelow : u < v) (highOffset : u + v ≤ a)
    (coprime : Nat.Coprime u v) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (sNonzero : s ≠ 0) (nNonzero : n ≠ 0) :
    ∃ T : ℕ, T ≤ n.natAbs + (n.natAbs + 1) * (u + v) ∧
      ∀ r : ℕ, T ≤ r → 0 < s * Iterate (RawStep p) r n := by
  have vPositive : 0 < v := lt_trans uPositive uBelow
  obtain ⟨start, k, x, startBound, kBelow, reached, atOrder, initialMagnitude⟩ :=
    WholeBaseNormalizeRaw p t v n tLower vPositive divisor nNonzero
  let gamma := (t : ℤ) ^ (a - u - v + 1 + k) * WholeBaseGeometricSum t v
  let beta := s * gamma
  let j := x.natAbs + 1
  let y := x + (j : ℤ) * beta
  have gammaPositive : 0 < gamma := mul_pos (pow_pos (by omega : (0 : ℤ) < t) _)
    (WholeBaseGeometricSumPositive t v vPositive)
  have betaNonzero : beta ≠ 0 := mul_ne_zero sNonzero (ne_of_gt gammaPositive)
  have crossing : 0 < beta * y := by
    simpa [j, y] using (WholeBaseSignedRayCrossing x beta 0 0 betaNonzero).1
  have aligned : 0 < s * y := by
    have product : 0 < (s * y) * gamma := by
      have rearranged : (s * y) * gamma = beta * y := by dsimp [beta]; ring
      rw [rearranged]
      exact crossing
    exact pos_of_mul_pos_left product (le_of_lt gammaPositive)
  have endpoint : Iterate (RawStep p) (start + j * (u + v)) n = y := by
    rw [IterateAdd, reached]
    simpa [y, beta, gamma, mul_assoc] using
      (WholeBaseHighOffsetRawRay p t u v a k s x tLower uBelow kBelow
        highOffset coprime divisor multiplier offset atOrder j).2
  have indexBound : j ≤ n.natAbs + 1 := by dsimp [j]; omega
  refine ⟨start + j * (u + v),
    Nat.add_le_add startBound (Nat.mul_le_mul_right (u + v) indexBound), ?_⟩
  intro r after
  have time : r = (start + j * (u + v)) + (r - (start + j * (u + v))) := by omega
  have tail : Iterate (RawStep p) r n =
      Iterate (RawStep p) (r - (start + j * (u + v))) y := by
    conv_lhs => rw [time, IterateAdd, endpoint]
  rw [tail]
  exact WholeBaseHighOffsetSignInvariant p t u v a s y tLower divisor multiplier offset
    aligned (r - (start + j * (u + v)))

end GeneralizedCollatz
