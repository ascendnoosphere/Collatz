/-
SPDX-License-Identifier: CC-BY-4.0
Zero-offset scalar dynamics on integral quadratic lattices.
-/
import ScalarEscape
import DependentHomogeneous
import Mathlib.Data.Int.GCD
import Mathlib.Data.Fintype.Pigeonhole

set_option autoImplicit false

namespace GeneralizedCollatz.HomogeneousLattice

open ComplexLattice

/-- The common coordinate factor controls the simultaneous scalar division guard. -/
def Content (p : Point) : ℕ := p.1.gcd p.2

/-- Scalar divisibility is equivalent to divisibility of the common coordinate factor. -/
theorem ContentGuard (d : ℤ) (p : Point) :
    d ∣ p.1 ∧ d ∣ p.2 ↔ d.natAbs ∣ Content p := by
  simp only [Content, Int.gcd_def, ← Int.natAbs_dvd_natAbs]
  exact ⟨fun h => Nat.dvd_gcd h.1 h.2,
    fun h => ⟨dvd_trans h (Nat.gcd_dvd_left _ _),
      dvd_trans h (Nat.gcd_dvd_right _ _)⟩⟩

/-- Content follows the positive homogeneous map even when the original scalars are signed. -/
theorem ContentStep (q d : ℤ) (p : Point) :
    Content (ScalarEscape.Raw q 0 d p) =
      PositiveHomogeneousStep q.natAbs d.natAbs (Content p) := by
  by_cases h : d ∣ p.1 ∧ d ∣ p.2
  · rw [ScalarEscape.Raw, if_pos h, PositiveHomogeneousStep,
      if_pos ((ContentGuard d p).mp h)]
    exact Int.gcd_ediv h.1 h.2
  · rw [ScalarEscape.Raw, if_neg h, PositiveHomogeneousStep,
      if_neg (fun hc => h ((ContentGuard d p).mpr hc))]
    simp only [Content, add_zero]
    exact Int.gcd_mul_left q p.1 p.2

/-- Content commutes with every raw iterate, not only with one division-free segment. -/
theorem ContentIterate (q d : ℤ) (p : Point) (n : ℕ) :
    Content (Iterate (ScalarEscape.Raw q 0 d) n p) =
      Iterate (PositiveHomogeneousStep q.natAbs d.natAbs) n (Content p) := by
  exact SemiconjugacyIterates _ _ Content (ContentStep q d) n p

/-- The two conventional recursion definitions of iteration agree. -/
theorem IterateFunction {α : Type*} (f : α → α) (n : ℕ) (p : α) :
    Iterate f n p = f^[n] p := by
  induction n with
  | zero => { rfl }
  | succ n ih => { simp only [Iterate, Function.iterate_succ_apply', ih] }

/-- Each coordinate keeps its initial absolute proportion to the common factor. -/
theorem CoordinateProportions (q d : ℤ) (hd0 : d ≠ 0) (p : Point) (n : ℕ) :
    Content p * (Iterate (ScalarEscape.Raw q 0 d) n p).1.natAbs =
      Content (Iterate (ScalarEscape.Raw q 0 d) n p) * p.1.natAbs ∧
    Content p * (Iterate (ScalarEscape.Raw q 0 d) n p).2.natAbs =
      Content (Iterate (ScalarEscape.Raw q 0 d) n p) * p.2.natAbs := by
  induction n with
  | zero => { exact ⟨rfl, rfl⟩ }
  | succ n ih => {
      let r := Iterate (ScalarEscape.Raw q 0 d) n p
      change Content p * (ScalarEscape.Raw q 0 d r).1.natAbs =
          Content (ScalarEscape.Raw q 0 d r) * p.1.natAbs ∧
        Content p * (ScalarEscape.Raw q 0 d r).2.natAbs =
          Content (ScalarEscape.Raw q 0 d r) * p.2.natAbs
      by_cases h : d ∣ r.1 ∧ d ∣ r.2
      · have hx := Int.natAbs_dvd_natAbs.mpr h.1
        have hy := Int.natAbs_dvd_natAbs.mpr h.2
        have hg := (ContentGuard d r).mp h
        have hd : 0 < d.natAbs := Int.natAbs_pos.mpr hd0
        have hqx := Nat.mul_div_cancel' hx
        have hqy := Nat.mul_div_cancel' hy
        have hqg := Nat.mul_div_cancel' hg
        rw [ContentStep, PositiveHomogeneousStep, if_pos hg]
        simp only [ScalarEscape.Raw, if_pos h, Int.natAbs_ediv_of_dvd h.1,
          Int.natAbs_ediv_of_dvd h.2]
        constructor
        · apply Nat.mul_left_cancel hd
          calc
            d.natAbs * (Content p * (r.1.natAbs / d.natAbs)) =
                Content p * r.1.natAbs := by nlinarith [hqx]
            _ = Content r * p.1.natAbs := ih.1
            _ = d.natAbs * ((Content r / d.natAbs) * p.1.natAbs) := by
              rw [← mul_assoc, hqg]
        · apply Nat.mul_left_cancel hd
          calc
            d.natAbs * (Content p * (r.2.natAbs / d.natAbs)) =
                Content p * r.2.natAbs := by nlinarith [hqy]
            _ = Content r * p.2.natAbs := ih.2
            _ = d.natAbs * ((Content r / d.natAbs) * p.2.natAbs) := by
              rw [← mul_assoc, hqg]
      · rw [ContentStep, PositiveHomogeneousStep,
          if_neg (fun hc => h ((ContentGuard d r).mpr hc))]
        simp only [ScalarEscape.Raw, if_neg h, add_zero, Int.natAbs_mul]
        constructor
        · calc
            Content p * (q.natAbs * r.1.natAbs) =
                q.natAbs * (Content p * r.1.natAbs) := by ring
            _ = q.natAbs * (Content r * p.1.natAbs) := by rw [ih.1]
            _ = q.natAbs * Content r * p.1.natAbs := by ring
        · calc
            Content p * (q.natAbs * r.2.natAbs) =
                q.natAbs * (Content p * r.2.natAbs) := by ring
            _ = q.natAbs * (Content r * p.2.natAbs) := by rw [ih.2]
            _ = q.natAbs * Content r * p.2.natAbs := by ring
    }

/-- A nonzero coordinate pair has positive content. -/
theorem ContentPositive (p : Point) (hp : p ≠ (0, 0)) : 0 < Content p := by
  have hn : Content p ≠ 0 := by
    intro h
    have hz := Int.gcd_eq_zero_iff.mp h
    exact hp (Prod.ext hz.1 hz.2)
  omega

/-- Coordinate height bounds content without assuming that either chosen coordinate is nonzero. -/
def Height (p : Point) : ℕ := max p.1.natAbs p.2.natAbs

/-- The common coordinate factor never exceeds coordinate height. -/
theorem ContentLeHeight (p : Point) : Content p ≤ Height p := by
  by_cases hx : p.1 = 0
  · simp [Content, Height, hx]
  · exact (Nat.gcd_le_left _ (Int.natAbs_pos.mpr hx)).trans (Nat.le_max_left _ _)

/-- Every nonzero zero-offset lattice seed escapes when the scalar magnitudes are independent. -/
theorem IndependentHeightEscape (q d : ℤ) (hq : 2 ≤ q.natAbs) (hd : 2 ≤ d.natAbs)
    (hi : MultiplicativelyIndependent q.natAbs d.natAbs)
    (p : Point) (hp : p ≠ (0, 0)) :
    Filter.Tendsto (fun n => Height (Iterate (ScalarEscape.Raw q 0 d) n p))
      Filter.atTop Filter.atTop := by
  have hg := PositiveHomogeneousIndependentEscape q.natAbs d.natAbs (Content p)
    hq hd hi (ContentPositive p hp)
  have hc : Filter.Tendsto (fun n => Content (Iterate (ScalarEscape.Raw q 0 d) n p))
      Filter.atTop Filter.atTop := by
    simpa only [ContentIterate] using hg
  exact Filter.tendsto_atTop_mono (fun n => ContentLeHeight _) hc

/-- Dependence gives a source-relative bound for both coordinates, including signed scalar maps. -/
theorem DependentCoordinateBound (q d : ℤ) (hq : 2 ≤ q.natAbs) (hd : 2 ≤ d.natAbs)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (he : q.natAbs ^ a = d.natAbs ^ b)
    (p : Point) (hp : p ≠ (0, 0)) (n : ℕ) :
    (Iterate (ScalarEscape.Raw q 0 d) n p).1.natAbs ≤
        q.natAbs * d.natAbs * p.1.natAbs ∧
      (Iterate (ScalarEscape.Raw q 0 d) n p).2.natAbs ≤
        q.natAbs * d.natAbs * p.2.natAbs := by
  obtain ⟨params, hqeq, hdeq⟩ :=
    MultiplicativeDependenceNormalForm hq hd ha hb he
  have hcontent : Content (Iterate (ScalarEscape.Raw q 0 d) n p) ≤
      q.natAbs * d.natAbs * Content p := by
    rw [ContentIterate, IterateFunction, ← hqeq, ← hdeq,
      ← params.NatStepEqPositiveHomogeneous]
    exact params.NatIterateHeightBound (ContentPositive p hp)
  have hd0 : d ≠ 0 := by
    intro hzero
    simp [hzero] at hd
  obtain ⟨hx, hy⟩ := CoordinateProportions q d hd0 p n
  have hg := ContentPositive p hp
  constructor
  · apply Nat.le_of_mul_le_mul_left _ hg
    calc
      Content p * (Iterate (ScalarEscape.Raw q 0 d) n p).1.natAbs =
          Content (Iterate (ScalarEscape.Raw q 0 d) n p) * p.1.natAbs := hx
      _ ≤ (q.natAbs * d.natAbs * Content p) * p.1.natAbs :=
        Nat.mul_le_mul_right _ hcontent
      _ = Content p * (q.natAbs * d.natAbs * p.1.natAbs) := by ring
  · apply Nat.le_of_mul_le_mul_left _ hg
    calc
      Content p * (Iterate (ScalarEscape.Raw q 0 d) n p).2.natAbs =
          Content (Iterate (ScalarEscape.Raw q 0 d) n p) * p.2.natAbs := hy
      _ ≤ (q.natAbs * d.natAbs * Content p) * p.2.natAbs :=
        Nat.mul_le_mul_right _ hcontent
      _ = Content p * (q.natAbs * d.natAbs * p.2.natAbs) := by ring

/-- A bounded integral pair trajectory has a repeated state and a genuinely periodic tail. -/
theorem BoundedPointPeriodic (f : Point → Point) (p : Point) (bound : ℕ)
    (hbound : ∀ n, Height (Iterate f n p) ≤ bound) :
    ∃ s period : ℕ, 0 < period ∧
      ∀ n, Iterate f (s + n + period) p = Iterate f (s + n) p := by
  let interval := Set.Icc (-(bound : ℤ)) (bound : ℤ)
  have hfinite : interval.Finite := Set.finite_Icc _ _
  letI := hfinite.fintype
  have hmem : ∀ n, (Iterate f n p).1 ∈ interval ∧ (Iterate f n p).2 ∈ interval := by
    intro n
    have hx : (Iterate f n p).1.natAbs ≤ bound :=
      (Nat.le_max_left _ _).trans (hbound n)
    have hy : (Iterate f n p).2.natAbs ≤ bound :=
      (Nat.le_max_right _ _).trans (hbound n)
    have hxcast : ((Iterate f n p).1.natAbs : ℤ) ≤ bound := by exact_mod_cast hx
    have hycast : ((Iterate f n p).2.natAbs : ℤ) ≤ bound := by exact_mod_cast hy
    have hxpos := Int.le_natAbs (a := (Iterate f n p).1)
    have hxneg := Int.le_natAbs (a := -(Iterate f n p).1)
    have hypos := Int.le_natAbs (a := (Iterate f n p).2)
    have hyneg := Int.le_natAbs (a := -(Iterate f n p).2)
    simp only [Int.natAbs_neg] at hxneg hyneg
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  let encoded (n : ℕ) : interval × interval :=
    (⟨(Iterate f n p).1, (hmem n).1⟩, ⟨(Iterate f n p).2, (hmem n).2⟩)
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite encoded
  have hcollision : Iterate f i p = Iterate f j p := by
    have hx := congrArg (fun z : interval × interval => (z.1 : ℤ)) heq
    have hy := congrArg (fun z : interval × interval => (z.2 : ℤ)) heq
    exact Prod.ext hx hy
  have ordered : ∀ i j, i < j → Iterate f i p = Iterate f j p →
      ∃ s period : ℕ, 0 < period ∧
        ∀ n, Iterate f (s + n + period) p = Iterate f (s + n) p := by
    intro i j hij he
    refine ⟨i, j - i, by omega, ?_⟩
    intro n
    rw [show i + n + (j - i) = j + n by omega,
      IterateAdd, IterateAdd, ← he]
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact ordered i j hij hcollision
  · exact ordered j i hji hcollision.symm

/-- Every nonzero dependent zero-offset lattice orbit is eventually periodic. -/
theorem DependentEventuallyPeriodic (q d : ℤ) (hq : 2 ≤ q.natAbs)
    (hd : 2 ≤ d.natAbs) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (he : q.natAbs ^ a = d.natAbs ^ b) (p : Point) (hp : p ≠ (0, 0)) :
    ∃ s period : ℕ, 0 < period ∧
      ∀ n, Iterate (ScalarEscape.Raw q 0 d) (s + n + period) p =
        Iterate (ScalarEscape.Raw q 0 d) (s + n) p := by
  apply BoundedPointPeriodic _ p (q.natAbs * d.natAbs * Height p)
  intro n
  obtain ⟨hx, hy⟩ := DependentCoordinateBound q d hq hd a b ha hb he p hp n
  apply max_le
  · exact hx.trans (Nat.mul_le_mul_left _ (Nat.le_max_left _ _))
  · exact hy.trans (Nat.mul_le_mul_left _ (Nat.le_max_right _ _))

/-- Zero transverse coordinate remains zero under every homogeneous raw tick. -/
theorem AxisInvariant (q d : ℤ) (p : Point) (hp : p.2 = 0) (n : ℕ) :
    (Iterate (ScalarEscape.Raw q 0 d) n p).2 = 0 := by
  induction n with
  | zero => { exact hp }
  | succ n ih => {
      simp only [Iterate, ScalarEscape.Raw]
      split_ifs <;> simp [ih]
    }

/-- Coordinate periodicity reconstructs the actual ring trajectory at the same raw times. -/
theorem RingDependentEventuallyPeriodic (tau nu q d : ℤ)
    (hq : 2 ≤ q.natAbs) (hd : 2 ≤ d.natAbs) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (he : q.natAbs ^ a = d.natAbs ^ b)
    (z : LatticeRing tau nu) (hz : z ≠ 0) :
    ∃ s period : ℕ, 0 < period ∧
      ∀ n, Iterate (ScalarEscape.RingRaw tau nu q 0 d) (s + n + period) z =
        Iterate (ScalarEscape.RingRaw tau nu q 0 d) (s + n) z := by
  have hp : Coordinates tau nu z ≠ (0, 0) := by
    intro heq
    apply hz
    apply QuadraticAlgebra.ext
    · exact congrArg Prod.fst heq
    · exact congrArg Prod.snd heq
  obtain ⟨s, period, hpos, hperiod⟩ :=
    DependentEventuallyPeriodic q d hq hd a b ha hb he (Coordinates tau nu z) hp
  refine ⟨s, period, hpos, ?_⟩
  intro n
  have hc : Coordinates tau nu
      (Iterate (ScalarEscape.RingRaw tau nu q 0 d) (s + n + period) z) =
      Coordinates tau nu (Iterate (ScalarEscape.RingRaw tau nu q 0 d) (s + n) z) := by
    rw [ScalarEscape.RingCoordinatesIter, ScalarEscape.RingCoordinatesIter]
    exact hperiod n
  exact QuadraticAlgebra.ext (congrArg Prod.fst hc) (congrArg Prod.snd hc)

/-- Independent homogeneous scalars force complex-norm escape for every nonzero lattice seed. -/
theorem RingIndependentEscape (tau nu q d : ℤ) (h : tau ^ 2 < 4 * nu)
    (hq : 2 ≤ q.natAbs) (hd : 2 ≤ d.natAbs)
    (hi : MultiplicativelyIndependent q.natAbs d.natAbs)
    (z : LatticeRing tau nu) (hz : z ≠ 0) :
    ∀ B : ℝ, ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      B < ‖ImaginaryEmbedding tau nu h
        (Iterate (ScalarEscape.RingRaw tau nu q 0 d) n z)‖ := by
  by_cases hy : z.im = 0
  · have hp : Coordinates tau nu z ≠ (0, 0) := by
      intro heq
      apply hz
      exact QuadraticAlgebra.ext (congrArg Prod.fst heq) (congrArg Prod.snd heq)
    have ht := IndependentHeightEscape q d hq hd hi (Coordinates tau nu z) hp
    intro B
    obtain ⟨N, hN⟩ := exists_nat_gt B
    have hevent := (Filter.tendsto_atTop.mp ht) N
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hevent
    refine ⟨K, ?_⟩
    intro n hn
    let r := Iterate (ScalarEscape.RingRaw tau nu q 0 d) n z
    have hcoords := ScalarEscape.RingCoordinatesIter tau nu q 0 d z n
    have hrim : r.im = 0 := by
      have hc := congrArg Prod.snd hcoords
      change r.im = (Iterate (ScalarEscape.Raw q 0 d) n (Coordinates tau nu z)).2 at hc
      rw [hc]
      exact AxisInvariant q d _ hy n
    have hlarge : N ≤ r.re.natAbs := by
      have hc := hK n hn
      rw [← hcoords] at hc
      change N ≤ Height (Coordinates tau nu r) at hc
      simpa [Height, Coordinates, hrim] using hc
    have hnorm : ‖ImaginaryEmbedding tau nu h r‖ = (r.re.natAbs : ℝ) := by
      rw [ImaginaryEmbeddingApply]
      simp [hrim]
    rw [hnorm]
    exact hN.trans_le (by exact_mod_cast hlarge)
  · exact ScalarEscape.ComplexOffAxisEscape tau nu q 0 d z h hq hd hi hy

end GeneralizedCollatz.HomogeneousLattice
