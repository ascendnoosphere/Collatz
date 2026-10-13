/-
SPDX-License-Identifier: CC-BY-4.0
Gaussian divisibility, exact raw iteration, and homogeneous escape.
-/
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace GeneralizedCollatz.GaussianDynamics

/-- The integral squared Euclidean height supplies a well-founded division rank. -/
def Norm (z : GaussianInt) : ℕ := z.norm.natAbs

/-- Multiplication changes squared height by the exact product of heights. -/
theorem NormMul (z w : GaussianInt) : Norm (z * w) = Norm z * Norm w := by
  simp [Norm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- A Gaussian integer has zero height precisely when it is zero. -/
theorem NormZeroIff (z : GaussianInt) : Norm z = 0 ↔ z = 0 := by
  simp [Norm, GaussianInt.norm_eq_zero]

/-- A nonzero lattice point has positive integral squared height. -/
theorem NormPos (z : GaussianInt) (hz : z ≠ 0) : 0 < Norm z := by
  exact Nat.pos_of_ne_zero (fun h => hz ((NormZeroIff z).mp h))

/-- Powers have the corresponding exact power of squared height. -/
theorem NormPow (z : GaussianInt) (j : ℕ) : Norm (z ^ j) = Norm z ^ j := by
  induction j with
  | zero => simp [Norm, Zsqrtd.norm]
  | succ j ih => rw [pow_succ, NormMul, ih, pow_succ]

/-- Both coordinates of the complex quotient must be integral. -/
theorem DvdCoordinates (d z : GaussianInt) (hd : d ≠ 0) :
    d ∣ z ↔
      (d.re ^ 2 + d.im ^ 2) ∣ d.re * z.re + d.im * z.im ∧
      (d.re ^ 2 + d.im ^ 2) ∣ d.re * z.im - d.im * z.re := by
  constructor
  · intro h
    obtain ⟨w, rfl⟩ := h
    constructor
    · refine ⟨w.re, ?_⟩
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
      ring
    · refine ⟨w.im, ?_⟩
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
      ring
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    have hn : d.re ^ 2 + d.im ^ 2 ≠ 0 := by
      intro h
      have hre : d.re = 0 := by nlinarith [sq_nonneg d.im]
      have him : d.im = 0 := by nlinarith [sq_nonneg d.re]
      apply hd
      exact Zsqrtd.ext hre him
    have hx :
        (d.re ^ 2 + d.im ^ 2) * z.re =
          (d.re ^ 2 + d.im ^ 2) * (d.re * u - d.im * v) := by
      calc
        _ = d.re * (d.re * z.re + d.im * z.im) -
            d.im * (d.re * z.im - d.im * z.re) := by ring
        _ = _ := by rw [hu, hv]; ring
    have hy :
        (d.re ^ 2 + d.im ^ 2) * z.im =
          (d.re ^ 2 + d.im ^ 2) * (d.im * u + d.re * v) := by
      calc
        _ = d.im * (d.re * z.re + d.im * z.im) +
            d.re * (d.re * z.im - d.im * z.re) := by ring
        _ = _ := by rw [hu, hv]; ring
    refine ⟨⟨u, v⟩, ?_⟩
    apply Zsqrtd.ext
    · simpa [Zsqrtd.re_mul, sub_eq_add_neg] using mul_left_cancel₀ hn hx
    · simpa [Zsqrtd.im_mul, add_comm] using mul_left_cancel₀ hn hy

/-- The division branch is selected in the Gaussian ring, not in the complex field. -/
noncomputable def RawBranch (q c d z : GaussianInt) : GaussianInt := by
  classical
  exact if d ∣ z then z / d else q * z + c

/-- One raw tick retains the exact Gaussian branch guard. -/
noncomputable def RawIter (q c d z : GaussianInt) : ℕ → GaussianInt
  | 0 => z
  | j + 1 => RawBranch q c d (RawIter q c d z j)

/-- Splitting the first tick allows reconstruction of a division prefix. -/
theorem RawIterSuccStart (q c d z : GaussianInt) (j : ℕ) :
    RawIter q c d z (j + 1) = RawIter q c d (RawBranch q c d z) j := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [RawIter] using congrArg (RawBranch q c d) ih

/-- Concatenated clocks recover the original raw trajectory exactly. -/
theorem RawIterAdd (q c d z : GaussianInt) (r j : ℕ) :
    RawIter q c d z (r + j) = RawIter q c d (RawIter q c d z r) j := by
  induction r generalizing z with
  | zero => { simp only [Nat.zero_add, RawIter] }
  | succ r ih => {
      simpa only [Nat.succ_add, RawIterSuccStart] using ih (RawBranch q c d z)
    }

/-- Exact division by a nonunit strictly decreases the height of a nonzero point. -/
theorem DivisionNormDrop (d z : GaussianInt) (hd : 2 ≤ Norm d)
    (hz : z ≠ 0) (hdiv : d ∣ z) : Norm (z / d) < Norm z := by
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    norm_num [Norm, Zsqrtd.norm] at hd
  have hprod : d * (z / d) = z := EuclideanDomain.mul_div_cancel' hd0 hdiv
  have hw0 : z / d ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact hz hprod.symm
  have hw : 0 < Norm (z / d) := NormPos _ hw0
  have hn : Norm z = Norm d * Norm (z / d) := by
    calc
      Norm z = Norm (d * (z / d)) := congrArg Norm hprod.symm
      _ = Norm d * Norm (z / d) := NormMul d (z / d)
  rw [hn]
  nlinarith

/-- A finite division prefix ends at a nondivisible point; height proves termination. -/
theorem DivisionPrefix (q c d z : GaussianInt) (hd : 2 ≤ Norm d) (hz : z ≠ 0) :
    ∃ r : ℕ, ∃ t : GaussianInt,
      ¬d ∣ t ∧ RawIter q c d z r = t ∧ z = d ^ r * t := by
  have aux : ∀ n : ℕ, ∀ w : GaussianInt, Norm w = n → w ≠ 0 →
      ∃ r : ℕ, ∃ t : GaussianInt,
        ¬d ∣ t ∧ RawIter q c d w r = t ∧ w = d ^ r * t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn hw
      by_cases hdiv : d ∣ w
      · have hlt : Norm (w / d) < n := by
          rw [← hn]
          exact DivisionNormDrop d w hd hw hdiv
        have hd0 : d ≠ 0 := by
          intro h
          subst d
          norm_num [Norm, Zsqrtd.norm] at hd
        have hprod : d * (w / d) = w := EuclideanDomain.mul_div_cancel' hd0 hdiv
        have hw0 : w / d ≠ 0 := by
          intro h
          rw [h, mul_zero] at hprod
          exact hw hprod.symm
        obtain ⟨r, t, ht, hiter, hfactor⟩ := ih (Norm (w / d)) hlt (w / d) rfl hw0
        refine ⟨r + 1, t, ht, ?_, ?_⟩
        · rw [RawIterSuccStart]
          simpa [RawBranch, hdiv] using hiter
        · calc
            w = d * (w / d) := hprod.symm
            _ = d * (d ^ r * t) := by rw [hfactor]
            _ = d ^ (r + 1) * t := by rw [pow_succ]; ring
      · exact ⟨0, w, hdiv, rfl, by simp⟩
  exact aux (Norm z) z rfl hz

/-- The finite division prefix has an explicit integral height budget. -/
theorem DivisionPrefixBudget (q c d z : GaussianInt) (hd : 2 ≤ Norm d) (hz : z ≠ 0) :
    ∃ r : ℕ, ∃ t : GaussianInt,
      ¬d ∣ t ∧ RawIter q c d z r = t ∧ z = d ^ r * t ∧ 2 ^ r ≤ Norm z := by
  obtain ⟨r, t, ht, hiter, hfactor⟩ := DivisionPrefix q c d z hd hz
  have ht0 : t ≠ 0 := by
    intro h
    apply ht
    rw [h]
    exact dvd_zero d
  have hpos : 1 ≤ Norm t := NormPos t ht0
  have hpow : 2 ^ r ≤ Norm d ^ r := by gcongr
  refine ⟨r, t, ht, hiter, hfactor, ?_⟩
  rw [hfactor, NormMul, NormPow]
  nlinarith [Nat.mul_le_mul_left (Norm d ^ r) hpos]

/-- A Bezout identity prevents multiplication by q from entering the division ideal. -/
theorem CoprimePreservesAvoidance (q d a b z : GaussianInt)
    (hab : a * q + b * d = 1) (hz : ¬d ∣ z) : ¬d ∣ q * z := by
  intro h
  obtain ⟨t, ht⟩ := h
  apply hz
  refine ⟨a * t + b * z, ?_⟩
  calc
    z = (a * q + b * d) * z := by rw [hab]; simp
    _ = a * (q * z) + b * (d * z) := by ring
    _ = d * (a * t + b * z) := by rw [ht]; ring

/-- Every affine power remains outside the division ideal under the same Bezout identity. -/
theorem CoprimePowerAvoidance (q d a b z : GaussianInt)
    (hab : a * q + b * d = 1) (hz : ¬d ∣ z) (j : ℕ) : ¬d ∣ q ^ j * z := by
  induction j with
  | zero => simpa using hz
  | succ j ih =>
      have hmul : q ^ (j + 1) * z = q * (q ^ j * z) := by rw [pow_succ]; ring
      rw [hmul]
      exact CoprimePreservesAvoidance q d a b (q ^ j * z) hab ih

/-- The entire tail, not a subsequence, is the expanding homogeneous affine orbit. -/
theorem CoprimeRawPower (q d a b z : GaussianInt)
    (hab : a * q + b * d = 1) (hz : ¬d ∣ z) (j : ℕ) :
    RawIter q 0 d z j = q ^ j * z := by
  induction j with
  | zero => simp [RawIter]
  | succ j ih =>
      rw [RawIter, ih, RawBranch, if_neg (CoprimePowerAvoidance q d a b z hab hz j)]
      rw [pow_succ]
      ring

/-- The exact squared height of each tail iterate dominates the explicit rate 2^j. -/
theorem CoprimeHeightBound (q d a b z : GaussianInt) (hq : 2 ≤ Norm q)
    (hab : a * q + b * d = 1) (hz : ¬d ∣ z) (j : ℕ) :
    2 ^ j ≤ Norm (RawIter q 0 d z j) := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact hz (dvd_zero d)
  have hn : 1 ≤ Norm z := NormPos z hz0
  have hp : 2 ^ j ≤ Norm q ^ j := by gcongr
  rw [CoprimeRawPower q d a b z hab hz j, NormMul, NormPow]
  nlinarith [Nat.mul_le_mul_left (Norm q ^ j) hn]

/-- Nonzero homogeneous trajectories escape in full sequence when q and d are coprime. -/
theorem CoprimeHomogeneousEscape (q d a b z : GaussianInt)
    (hq : 2 ≤ Norm q) (hd : 2 ≤ Norm d) (hab : a * q + b * d = 1) (hz : z ≠ 0) :
    ∀ B : ℕ, ∃ K : ℕ, ∀ j : ℕ, K ≤ j → B < Norm (RawIter q 0 d z j) := by
  obtain ⟨r, t, ht, hiter, _⟩ := DivisionPrefix q 0 d z hd hz
  have hp : ∀ k : ℕ, k < 2 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        have hpos : 0 < 2 ^ k := by positivity
        nlinarith
  intro B
  refine ⟨r + B + 1, ?_⟩
  intro j hj
  have hr : r ≤ j := by omega
  have hlarge : B < j - r := by omega
  have hclock : j = r + (j - r) := by omega
  rw [hclock, RawIterAdd, hiter]
  exact lt_of_lt_of_le (lt_trans hlarge (hp (j - r)))
    (CoprimeHeightBound q d a b t hq hab ht (j - r))

/-- The split Gaussian prime in the upper half-plane. -/
def QPlus : GaussianInt := ⟨2, 1⟩

/-- Its conjugate is a genuinely different division ideal. -/
def DMinus : GaussianInt := ⟨2, -1⟩

/-- Equal parameter norms permit every nonzero seed to escape, not only neutral cycles. -/
theorem EqualNormSplitEscape (z : GaussianInt) (hz : z ≠ 0) :
    Norm QPlus = 5 ∧ Norm DMinus = 5 ∧
      ∀ B : ℕ, ∃ K : ℕ, ∀ j : ℕ,
        K ≤ j → B < Norm (RawIter QPlus 0 DMinus z j) := by
  refine ⟨by decide, by decide, ?_⟩
  apply CoprimeHomogeneousEscape QPlus DMinus (-1) (⟨1, 1⟩ : GaussianInt) z
  · decide
  · decide
  · decide
  · exact hz

/-- Reduction modulo 2-i sends i to 2 in the five-element field. -/
def SplitResidue : GaussianInt →+* ZMod 5 := Zsqrtd.lift ⟨2, by decide⟩

/-- Equal norms do not supply any common positive power, even with unequal exponents. -/
theorem EqualNormNoCommonPower (a b : ℕ) (_ha : 1 ≤ a) (hb : 1 ≤ b) :
    QPlus ^ a ≠ DMinus ^ b := by
  have hq : SplitResidue QPlus = 4 := by decide
  have hd : SplitResidue DMinus = 0 := by decide
  have hunit : IsUnit (4 : ZMod 5) := by
    exact ⟨⟨4, 4, by decide, by decide⟩, rfl⟩
  intro h
  have heq := congrArg SplitResidue h
  have hb0 : b ≠ 0 := by omega
  have hzero : (4 : ZMod 5) ^ a = 0 := by
    simpa only [map_pow, hq, hd, zero_pow hb0] using heq
  haveI : Fact (1 < 5) := ⟨by decide⟩
  exact (hunit.pow a).ne_zero hzero

end GeneralizedCollatz.GaussianDynamics
