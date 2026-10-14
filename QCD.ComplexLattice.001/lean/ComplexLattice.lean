/-
SPDX-License-Identifier: CC-BY-4.0
Off-axis escape for raw (3,c,2) on every integral quadratic coordinate lattice.
-/
import QuadraticArithmetic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace GeneralizedCollatz.ComplexLattice

open scoped QuadraticAlgebra

/-- These are integral basis coordinates, not the real and imaginary parts of omega. -/
abbrev Point := ℤ × ℤ

/-- A real scalar divisor two divides precisely when both basis coefficients are even. -/
theorem TwoGuard (tau nu x y : ℤ) :
    QuadraticArithmetic.CoefficientDivides tau nu 2 0 x y ↔ 2 ∣ x ∧ 2 ∣ y := by
  constructor
  · rintro ⟨u, v, hx, hy⟩
    exact ⟨⟨u, by simpa using hx⟩, ⟨v, by simpa using hy⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    exact ⟨u, v, by simpa using hu, by simpa using hv⟩

/-- Raw ticks retain the simultaneous divisibility guard on the two coordinates. -/
def Raw (c : ℤ) (p : Point) : Point :=
  if 2 ∣ p.1 ∧ 2 ∣ p.2 then (p.1 / 2, p.2 / 2) else (3 * p.1 + c, 3 * p.2)

/-- All clocks in this file count raw ticks, not shortcut or accelerated ticks. -/
def Iter (c : ℤ) (p : Point) : ℕ → Point
  | 0 => p
  | j + 1 => Raw c (Iter c p j)

/-- A clock split reconstructs the same trajectory after its first raw tick. -/
theorem IterSuccStart (c : ℤ) (p : Point) (j : ℕ) :
    Iter c p (j + 1) = Iter c (Raw c p) j := by
  induction j with
  | zero => { rfl }
  | succ j ih => { simpa only [Iter] using congrArg (Raw c) ih }

/-- Concatenation keeps both coordinates and the raw clock exactly. -/
theorem IterAdd (c : ℤ) (p : Point) (r j : ℕ) :
    Iter c p (r + j) = Iter c (Iter c p r) j := by
  induction r generalizing p with
  | zero => { simp [Iter] }
  | succ r ih => { simpa only [Nat.succ_add, IterSuccStart] using ih (Raw c p) }

/-- An affine step cannot restore a factor of two to an odd transverse coefficient. -/
theorem ThreePreservesOdd (u : ℤ) (hu : ¬2 ∣ u) : ¬2 ∣ 3 * u := by
  simp only [Int.dvd_iff_emod_eq_zero] at hu ⊢
  omega

/-- With odd c, an odd real coefficient becomes even on the next affine tick. -/
theorem OddRealFlip (x c : ℤ) (hx : ¬2 ∣ x) (hc : ¬2 ∣ c) : 2 ∣ 3 * x + c := by
  simp only [Int.dvd_iff_emod_eq_zero] at hx hc ⊢
  omega

/-- Odd transverse parity forbids every subsequent division, regardless of x or c. -/
theorem OddTailImag (c : ℤ) (p : Point) (hp : ¬2 ∣ p.2) (j : ℕ) :
    (Iter c p j).2 = 3 ^ j * p.2 ∧ ¬2 ∣ (Iter c p j).2 := by
  induction j with
  | zero => { simp [Iter, hp] }
  | succ j ih => {
      have hguard : ¬(2 ∣ (Iter c p j).1 ∧ 2 ∣ (Iter c p j).2) :=
        fun h => ih.2 h.2
      simp only [Iter, Raw, if_neg hguard]
      constructor
      · rw [ih.1, pow_succ]
        ring
      · exact ThreePreservesOdd _ ih.2
    }

/-- The solved odd transverse tail reconstructs the real coordinate at every raw tick. -/
theorem OddTailReal (c : ℤ) (p : Point) (hp : ¬2 ∣ p.2) (j : ℕ) :
    (Iter c p j).1 = 3 ^ j * p.1 + c * ∑ k ∈ Finset.range j, (3 : ℤ) ^ k := by
  induction j with
  | zero => { simp [Iter] }
  | succ j ih => {
      have hguard : ¬(2 ∣ (Iter c p j).1 ∧ 2 ∣ (Iter c p j).2) :=
        fun h => (OddTailImag c p hp j).2 h.2
      simp only [Iter, Raw, if_neg hguard]
      rw [ih, Finset.sum_range_succ']
      simp only [pow_succ, pow_zero, ← Finset.sum_mul]
      ring
    }

/-- Each block of at most two raw ticks removes one transverse factor of two. -/
theorem FiniteOddEntry (r : ℕ) (x u c : ℤ) (hu : ¬2 ∣ u) (hc : ¬2 ∣ c) :
    ∃ t : ℕ, t ≤ 2 * r ∧ ¬2 ∣ (Iter c (x, 2 ^ r * u) t).2 := by
  induction r generalizing x u with
  | zero => {
      refine ⟨0, by omega, ?_⟩
      simpa [Iter] using hu
    }
  | succ r ih => {
      have hy : 2 ∣ (2 : ℤ) ^ (r + 1) * u := by
        refine ⟨2 ^ r * u, ?_⟩
        rw [pow_succ]
        ring
      by_cases hx : 2 ∣ x
      · have hstep : Raw c (x, 2 ^ (r + 1) * u) = (x / 2, 2 ^ r * u) := by
          have hg : 2 ∣ x ∧ 2 ∣ (2 : ℤ) ^ (r + 1) * u := ⟨hx, hy⟩
          simp only [Raw, if_pos hg]
          congr 1
          have heq : (2 : ℤ) ^ (r + 1) * u = 2 * (2 ^ r * u) := by
            rw [pow_succ]
            ring
          rw [heq, Int.mul_ediv_cancel_left _ (by decide : (2 : ℤ) ≠ 0)]
        obtain ⟨t, ht, ho⟩ := ih (x / 2) u hu
        refine ⟨1 + t, by omega, ?_⟩
        simpa only [Nat.add_comm 1 t, IterSuccStart, hstep] using ho
      · have hflip := OddRealFlip x c hx hc
        have hy3 : 2 ∣ 3 * ((2 : ℤ) ^ (r + 1) * u) := dvd_mul_of_dvd_right hy 3
        have hstep : Raw c (Raw c (x, 2 ^ (r + 1) * u)) =
            ((3 * x + c) / 2, 2 ^ r * (3 * u)) := by
          have hg : ¬(2 ∣ x ∧ 2 ∣ (2 : ℤ) ^ (r + 1) * u) := fun h => hx h.1
          have hg2 : 2 ∣ 3 * x + c ∧ 2 ∣ 3 * ((2 : ℤ) ^ (r + 1) * u) :=
            ⟨hflip, hy3⟩
          simp only [Raw, if_neg hg, if_pos hg2]
          congr 1
          have heq : 3 * ((2 : ℤ) ^ (r + 1) * u) = 2 * (2 ^ r * (3 * u)) := by
            rw [pow_succ]
            ring
          rw [heq, Int.mul_ediv_cancel_left _ (by decide : (2 : ℤ) ≠ 0)]
        obtain ⟨t, ht, ho⟩ := ih ((3 * x + c) / 2) (3 * u) (ThreePreservesOdd u hu)
        refine ⟨2 + t, by omega, ?_⟩
        rw [IterAdd]
        simpa only [Iter, hstep] using ho
    }

/-- Every nonzero transverse integer has a finite dyadic rank and an odd residual. -/
theorem DyadicDecomposition (y : ℤ) (hy : y ≠ 0) :
    ∃ r : ℕ, ∃ u : ℤ, ¬2 ∣ u ∧ y = 2 ^ r * u := by
  have habs : y.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy
  obtain ⟨r, m, hm, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd habs 2 (by decide)
  have hmInt : ¬(2 : ℤ) ∣ (m : ℤ) := by exact_mod_cast hm
  have heqInt : |y| = (2 : ℤ) ^ r * (m : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast heq
  by_cases hpos : 0 ≤ y
  · exact ⟨r, m, hmInt, by simpa [abs_of_nonneg hpos] using heqInt⟩
  · refine ⟨r, -(m : ℤ), ?_, ?_⟩
    · simpa only [dvd_neg] using hmInt
    · have hn : y ≤ 0 := by omega
      have ha : -y = (2 : ℤ) ^ r * (m : ℤ) := by
        simpa [abs_of_nonpos hn] using heqInt
      rw [mul_neg]
      omega

/-- An odd transverse coordinate gives an exact exponentially expanding height bound. -/
theorem OddTailHeight (c : ℤ) (p : Point) (hp : ¬2 ∣ p.2) (j : ℕ) :
    3 ^ j ≤ (Iter c p j).2.natAbs := by
  have hnonzero : p.2 ≠ 0 := fun h => hp (h ▸ dvd_zero 2)
  have hpos : 0 < p.2.natAbs := Int.natAbs_pos.mpr hnonzero
  rw [(OddTailImag c p hp j).1, Int.natAbs_mul, Int.natAbs_pow]
  simpa using Nat.le_mul_of_pos_right (3 ^ j) hpos

/-- Every off-axis trajectory escapes in full sequence for each odd real offset c. -/
theorem OffAxisEscape (c : ℤ) (p : Point) (hc : ¬2 ∣ c) (hp : p.2 ≠ 0) :
    ∀ B : ℕ, ∃ K : ℕ, ∀ j : ℕ, K ≤ j → B < (Iter c p j).2.natAbs := by
  obtain ⟨r, u, hu, heq⟩ := DyadicDecomposition p.2 hp
  have hpEq : p = (p.1, 2 ^ r * u) := by exact Prod.ext rfl heq
  obtain ⟨t, _, ht⟩ := FiniteOddEntry r p.1 u c hu hc
  have ho : ¬2 ∣ (Iter c p t).2 := by simpa only [← hpEq] using ht
  have hpow : ∀ j : ℕ, j < 3 ^ j := by
    intro j
    induction j with
    | zero => { norm_num }
    | succ j ih => { rw [pow_succ]; omega }
  intro B
  refine ⟨t + B + 1, ?_⟩
  intro j hj
  have hclock : j = t + (j - t) := by omega
  have hlarge : B < j - t := by omega
  rw [hclock, IterAdd]
  exact lt_of_lt_of_le (lt_trans hlarge (hpow (j - t)))
    (OddTailHeight c (Iter c p t) ho (j - t))

/-- The actual free integral algebra retains the basis relation theta² = tau*theta - nu. -/
abbrev LatticeRing (tau nu : ℤ) := QuadraticAlgebra ℤ (-nu) tau

/-- Integral basis coordinates identify ring elements without changing their state space. -/
def Coordinates (tau nu : ℤ) (z : LatticeRing tau nu) : Point := (z.re, z.im)

/-- Actual ring divisibility by the scalar two is exactly the simultaneous parity guard. -/
theorem ScalarTwoDivides (tau nu : ℤ) (z : LatticeRing tau nu) :
    (2 : LatticeRing tau nu) ∣ z ↔ 2 ∣ z.re ∧ 2 ∣ z.im := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨⟨w.re, by simpa using congrArg (fun v => v.re) hw⟩,
      ⟨w.im, by simpa using congrArg (fun v => v.im) hw⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨x, y⟩, ?_⟩
    apply QuadraticAlgebra.ext
    · simpa using hx
    · simpa using hy

/-- On the legal guard, coefficient halving reconstructs an actual integral ring quotient. -/
theorem ScalarTwoQuotient (tau nu : ℤ) (z : LatticeRing tau nu)
    (hz : (2 : LatticeRing tau nu) ∣ z) :
    (2 : LatticeRing tau nu) * ⟨z.re / 2, z.im / 2⟩ = z := by
  have h := (ScalarTwoDivides tau nu z).mp hz
  simp only [Int.dvd_iff_emod_eq_zero] at h
  apply QuadraticAlgebra.ext <;> simp <;> omega

/-- Scalar-two exact division is unique even when the quadratic algebra has other zero divisors. -/
theorem ScalarTwoUnique (tau nu : ℤ) (z u v : LatticeRing tau nu)
    (hu : (2 : LatticeRing tau nu) * u = z)
    (hv : (2 : LatticeRing tau nu) * v = z) : u = v := by
  have hr := congrArg (fun w => w.re) (hu.trans hv.symm)
  have hi := congrArg (fun w => w.im) (hu.trans hv.symm)
  simp at hr hi
  apply QuadraticAlgebra.ext <;> omega

/-- The ring raw map uses element divisibility, an exact integral quotient, and the same clock. -/
noncomputable def QuadraticRaw (tau nu c : ℤ) (z : LatticeRing tau nu) :
    LatticeRing tau nu := by
  classical
  exact if (2 : LatticeRing tau nu) ∣ z then ⟨z.re / 2, z.im / 2⟩
    else (3 : LatticeRing tau nu) * z + (c : LatticeRing tau nu)

/-- One actual ring tick and one coordinate tick agree with all branch guards preserved. -/
theorem RawCoordinates (tau nu c : ℤ) (z : LatticeRing tau nu) :
    Coordinates tau nu (QuadraticRaw tau nu c z) = Raw c (Coordinates tau nu z) := by
  classical
  by_cases h : 2 ∣ z.re ∧ 2 ∣ z.im
  · simp [Coordinates, QuadraticRaw, Raw, ScalarTwoDivides, h]
  · simp [Coordinates, QuadraticRaw, Raw, ScalarTwoDivides, h]

/-- Iteration of the actual ring map counts its original raw ticks. -/
noncomputable def QuadraticIter (tau nu c : ℤ) (z : LatticeRing tau nu) :
    ℕ → LatticeRing tau nu
  | 0 => z
  | j + 1 => QuadraticRaw tau nu c (QuadraticIter tau nu c z j)

/-- The coordinate recovery is exact for every raw time, not only at a selected endpoint. -/
theorem CoordinatesIter (tau nu c : ℤ) (z : LatticeRing tau nu) (j : ℕ) :
    Coordinates tau nu (QuadraticIter tau nu c z j) = Iter c (Coordinates tau nu z) j := by
  induction j with
  | zero => { rfl }
  | succ j ih => { rw [QuadraticIter, RawCoordinates, ih]; rfl }

/-- All odd-offset off-axis escape statements apply to actual integral quadratic ring elements. -/
theorem QuadraticOffAxisEscape (tau nu c : ℤ) (z : LatticeRing tau nu)
    (hc : ¬2 ∣ c) (hz : z.im ≠ 0) :
    ∀ B : ℕ, ∃ K : ℕ, ∀ j : ℕ, K ≤ j →
      B < (QuadraticIter tau nu c z j).im.natAbs := by
  intro B
  obtain ⟨K, hK⟩ := OffAxisEscape c (Coordinates tau nu z) hc hz B
  refine ⟨K, ?_⟩
  intro j hj
  have hcoord := congrArg (fun p : Point => p.2) (CoordinatesIter tau nu c z j)
  change (QuadraticIter tau nu c z j).im = (Iter c (Coordinates tau nu z) j).2 at hcoord
  rw [hcoord]
  exact hK j hj

/-- The positive-imaginary root embeds each admissible quadratic coordinate order in C. -/
noncomputable def ImaginaryGenerator (tau nu : ℤ) : ℂ :=
  ⟨(tau : ℝ) / 2, Real.sqrt (4 * (nu : ℝ) - (tau : ℝ) ^ 2) / 2⟩

/-- The explicit generator satisfies the original quadratic relation, with no changed order. -/
theorem ImaginaryGeneratorRoot (tau nu : ℤ) (h : tau ^ 2 < 4 * nu) :
    ImaginaryGenerator tau nu * ImaginaryGenerator tau nu =
      -(nu : ℂ) + (tau : ℂ) * ImaginaryGenerator tau nu := by
  have hr : (tau : ℝ) ^ 2 < 4 * (nu : ℝ) := by exact_mod_cast h
  have hs := Real.sq_sqrt (le_of_lt (sub_pos.mpr hr))
  apply Complex.ext <;> simp [ImaginaryGenerator, Complex.mul_re, Complex.mul_im]
  · nlinarith
  · ring

/-- The admissibility inequality supplies a fixed strictly positive transverse scale. -/
theorem ImaginaryGeneratorPositive (tau nu : ℤ) (h : tau ^ 2 < 4 * nu) :
    0 < (ImaginaryGenerator tau nu).im := by
  have hr : (tau : ℝ) ^ 2 < 4 * (nu : ℝ) := by exact_mod_cast h
  exact div_pos (Real.sqrt_pos.mpr (sub_pos.mpr hr)) (by norm_num)

/-- The universal quadratic lift is an actual algebra map into the complex plane. -/
noncomputable def ImaginaryEmbedding (tau nu : ℤ) (h : tau ^ 2 < 4 * nu) :
    LatticeRing tau nu →ₐ[ℤ] ℂ :=
  QuadraticAlgebra.lift ⟨ImaginaryGenerator tau nu, by
    simpa only [zsmul_eq_mul, Int.cast_neg, mul_one] using ImaginaryGeneratorRoot tau nu h⟩

/-- The algebra embedding uses the same complex coordinates as the visual survey. -/
theorem ImaginaryEmbeddingApply (tau nu : ℤ) (h : tau ^ 2 < 4 * nu)
    (z : LatticeRing tau nu) :
    ImaginaryEmbedding tau nu h z = (z.re : ℂ) + (z.im : ℂ) * ImaginaryGenerator tau nu := by
  simp [ImaginaryEmbedding, QuadraticAlgebra.lift, zsmul_eq_mul]

/-- The transverse integer coordinate is recovered from the actual imaginary part. -/
theorem ImaginaryEmbeddingImag (tau nu : ℤ) (h : tau ^ 2 < 4 * nu)
    (z : LatticeRing tau nu) :
    (ImaginaryEmbedding tau nu h z).im = (z.im : ℝ) * (ImaginaryGenerator tau nu).im := by
  simp [ImaginaryEmbeddingApply, Complex.mul_im]

/-- The fixed nonzero imaginary scale proves the coordinate embedding forgets no state. -/
theorem ImaginaryEmbeddingInjective (tau nu : ℤ) (h : tau ^ 2 < 4 * nu) :
    Function.Injective (ImaginaryEmbedding tau nu h) := by
  intro z w he
  have hi := congrArg Complex.im he
  rw [ImaginaryEmbeddingImag, ImaginaryEmbeddingImag] at hi
  have hiReal := mul_right_cancel₀ (ne_of_gt (ImaginaryGeneratorPositive tau nu h)) hi
  have hiInt : z.im = w.im := by exact_mod_cast hiReal
  rw [ImaginaryEmbeddingApply, ImaginaryEmbeddingApply, hiInt] at he
  have hrInt : z.re = w.re := by exact_mod_cast add_right_cancel he
  exact QuadraticAlgebra.ext hrInt hiInt

/-- A lower bound on the original complex norm controls the transverse coefficient height. -/
theorem ImaginaryEmbeddingNorm (tau nu : ℤ) (h : tau ^ 2 < 4 * nu)
    (z : LatticeRing tau nu) :
    (z.im.natAbs : ℝ) * (ImaginaryGenerator tau nu).im ≤ ‖ImaginaryEmbedding tau nu h z‖ := by
  have ha : (z.im.natAbs : ℝ) = |(z.im : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun k : ℤ => (k : ℝ)) (Int.natCast_natAbs z.im)
  have hn := Complex.abs_im_le_norm (ImaginaryEmbedding tau nu h z)
  rw [ImaginaryEmbeddingImag, abs_mul, abs_of_pos (ImaginaryGeneratorPositive tau nu h),
    ← ha] at hn
  exact hn

/-- Coordinate escape reconstructs full-sequence escape in the actual complex norm. -/
theorem ComplexOffAxisEscape (tau nu c : ℤ) (z : LatticeRing tau nu)
    (h : tau ^ 2 < 4 * nu) (hc : ¬2 ∣ c) (hz : z.im ≠ 0) :
    ∀ B : ℝ, ∃ K : ℕ, ∀ j : ℕ, K ≤ j →
      B < ‖ImaginaryEmbedding tau nu h (QuadraticIter tau nu c z j)‖ := by
  intro B
  have hp := ImaginaryGeneratorPositive tau nu h
  obtain ⟨N, hN⟩ := exists_nat_gt (B / (ImaginaryGenerator tau nu).im)
  have hb : B < (N : ℝ) * (ImaginaryGenerator tau nu).im := (div_lt_iff₀ hp).mp hN
  obtain ⟨K, hK⟩ := QuadraticOffAxisEscape tau nu c z hc hz N
  refine ⟨K, ?_⟩
  intro j hj
  have ht : (N : ℝ) < ((QuadraticIter tau nu c z j).im.natAbs : ℝ) := by
    exact_mod_cast hK j hj
  exact lt_of_lt_of_le (hb.trans (mul_lt_mul_of_pos_right ht hp))
    (ImaginaryEmbeddingNorm tau nu h (QuadraticIter tau nu c z j))

/-- Fixed-modulus raw reduction already fails on the even real states zero and two. -/
theorem ResidueNonDescent :
    (0 : ℤ) % 2 = 2 % 2 ∧
      (Raw (-1) (0, 0)).1 % 2 ≠ (Raw (-1) (2, 0)).1 % 2 := by
  decide

/-- Joseph's plus convention uses a different offset on each nonzero residue modulo two. -/
def ResiduePlus (p : Point) : Point :=
  if 2 ∣ p.1 ∧ 2 ∣ p.2 then (p.1 / 2, p.2 / 2)
    else ((3 * p.1 + p.1 % 2) / 2, (3 * p.2 + p.2 % 2) / 2)

/-- The minus variant is likewise a residue-wise quotient, not the raw minus map. -/
def ResidueMinus (p : Point) : Point :=
  if 2 ∣ p.1 ∧ 2 ∣ p.2 then (p.1 / 2, p.2 / 2)
    else ((3 * p.1 - p.1 % 2) / 2, (3 * p.2 - p.2 % 2) / 2)

/-- Both residue offsets make each coordinate numerator exactly divisible by two. -/
theorem ResidueNumerators (x : ℤ) :
    2 ∣ 3 * x + x % 2 ∧ 2 ∣ 3 * x - x % 2 := by
  simp only [Int.dvd_iff_emod_eq_zero]
  omega

/-- Unlike the raw map, the plus residue convention has a nonreal two-cycle. -/
theorem NonrealResidueCycle :
    ResiduePlus (1, 1) = (2, 2) ∧ ResiduePlus (2, 2) = (1, 1) := by
  decide

/-- Both signs also admit explicit nonreal fixed points in the quotient convention. -/
theorem NonrealResidueFixed :
    ResiduePlus (-1, -1) = (-1, -1) ∧ ResidueMinus (1, 1) = (1, 1) := by
  decide

end GeneralizedCollatz.ComplexLattice
