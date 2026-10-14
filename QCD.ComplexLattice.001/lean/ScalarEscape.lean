/-
SPDX-License-Identifier: CC-BY-4.0
Scalar off-axis escape on quadratic orders by multiplicative independence.
-/
import ComplexLattice
import Homogeneous

set_option autoImplicit false

namespace GeneralizedCollatz.ScalarEscape

open ComplexLattice

/-- Scalar division tests both integral coordinates and retains the signed divisor. -/
def Raw (q c d : ℤ) (p : Point) : Point :=
  if d ∣ p.1 ∧ d ∣ p.2 then (p.1 / d, p.2 / d) else (q * p.1 + c, q * p.2)

/-- Every prefix has an exact transverse monomial identity on its original raw clock. -/
theorem TransverseProduct (q c d : ℤ) (p : Point) (n : ℕ) :
    ∃ a b : ℕ, a + b = n ∧
      d ^ b * (Iterate (Raw q c d) n p).2 = q ^ a * p.2 := by
  induction n with
  | zero => {
      exact ⟨0, 0, rfl, by simp [Iterate]⟩
    }
  | succ n ih => {
      obtain ⟨a, b, hcount, hproduct⟩ := ih
      by_cases hg : d ∣ (Iterate (Raw q c d) n p).1 ∧
          d ∣ (Iterate (Raw q c d) n p).2
      · refine ⟨a, b + 1, by omega, ?_⟩
        simp only [Iterate, Raw, if_pos hg]
        calc
          d ^ (b + 1) * ((Iterate (Raw q c d) n p).2 / d) =
              d ^ b * (d * ((Iterate (Raw q c d) n p).2 / d)) := by ring
          _ = d ^ b * (Iterate (Raw q c d) n p).2 := by
            rw [Int.mul_ediv_cancel' hg.2]
          _ = q ^ a * p.2 := hproduct
      · refine ⟨a + 1, b, by omega, ?_⟩
        simp only [Iterate, Raw, if_neg hg]
        calc
          d ^ b * (q * (Iterate (Raw q c d) n p).2) =
              q * (d ^ b * (Iterate (Raw q c d) n p).2) := by ring
          _ = q * (q ^ a * p.2) := by rw [hproduct]
          _ = q ^ (a + 1) * p.2 := by ring
    }

/-- A nonzero transverse seed stays nonzero when the affine multiplier is nonzero. -/
theorem TransverseNonzero (q c d : ℤ) (p : Point) (n : ℕ)
    (hq : q ≠ 0) (hp : p.2 ≠ 0) :
    (Iterate (Raw q c d) n p).2 ≠ 0 := by
  obtain ⟨a, b, _, he⟩ := TransverseProduct q c d p n
  intro hz
  rw [hz, mul_zero] at he
  exact (mul_ne_zero (pow_ne_zero a hq) hp) he.symm

/-- Any repeated transverse magnitude would force a nontrivial coefficient resonance. -/
theorem NoMagnitudeReturn (q c d : ℤ) (p : Point) (n : ℕ)
    (hq : 2 ≤ q.natAbs) (hd : 2 ≤ d.natAbs)
    (hi : MultiplicativelyIndependent q.natAbs d.natAbs)
    (hp : p.2 ≠ 0) (hn : 0 < n) :
    (Iterate (Raw q c d) n p).2.natAbs ≠ p.2.natAbs := by
  intro returns
  obtain ⟨a, b, hcount, he⟩ := TransverseProduct q c d p n
  have habs := congrArg Int.natAbs he
  simp only [Int.natAbs_mul, Int.natAbs_pow, returns] at habs
  have hpositive : 0 < p.2.natAbs := Int.natAbs_pos.mpr hp
  have heq : d.natAbs ^ b = q.natAbs ^ a :=
    Nat.eq_of_mul_eq_mul_right hpositive habs
  have ha : 0 < a := by
    by_contra h
    have hz : a = 0 := by omega
    have hb : 0 < b := by omega
    have hlarge := Nat.one_lt_pow hb.ne' (by omega : 1 < d.natAbs)
    simp [hz] at heq
    omega
  have hb : 0 < b := by
    by_contra h
    have hz : b = 0 := by omega
    have hlarge := Nat.one_lt_pow ha.ne' (by omega : 1 < q.natAbs)
    simp [hz] at heq
    omega
  exact hi a b ha hb heq.symm

/-- Independence separates magnitudes even when branch choices depend on both coordinates. -/
theorem MagnitudeInjective (q c d : ℤ) (p : Point)
    (hq : 2 ≤ q.natAbs) (hd : 2 ≤ d.natAbs)
    (hi : MultiplicativelyIndependent q.natAbs d.natAbs) (hp : p.2 ≠ 0) :
    Function.Injective (fun n => (Iterate (Raw q c d) n p).2.natAbs) := by
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hq
  have collision : ∀ {i j : ℕ}, i < j →
      (Iterate (Raw q c d) i p).2.natAbs =
        (Iterate (Raw q c d) j p).2.natAbs → False := by
    intro i j hij he
    have hsplit : Iterate (Raw q c d) j p =
        Iterate (Raw q c d) (j - i) (Iterate (Raw q c d) i p) := by
      calc
        Iterate (Raw q c d) j p = Iterate (Raw q c d) (i + (j - i)) p := by
          congr 1
          omega
        _ = Iterate (Raw q c d) (j - i) (Iterate (Raw q c d) i p) :=
          GeneralizedCollatz.IterateAdd _ _ _ _
    have hreturn :
        (Iterate (Raw q c d) (j - i) (Iterate (Raw q c d) i p)).2.natAbs =
          (Iterate (Raw q c d) i p).2.natAbs := by
      rw [← hsplit]
      exact he.symm
    exact NoMagnitudeReturn q c d (Iterate (Raw q c d) i p) (j - i)
      hq hd hi (TransverseNonzero q c d p i hq0 hp) (by omega) hreturn
  intro i j he
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact collision hij he
  · exact collision hji he.symm

/-- Integer discreteness converts no repeated magnitude into full-sequence escape. -/
theorem OffAxisEscape (q c d : ℤ) (p : Point)
    (hq : 2 ≤ q.natAbs) (hd : 2 ≤ d.natAbs)
    (hi : MultiplicativelyIndependent q.natAbs d.natAbs) (hp : p.2 ≠ 0) :
    Filter.Tendsto (fun n => (Iterate (Raw q c d) n p).2.natAbs)
      Filter.atTop Filter.atTop := by
  exact Function.Injective.nat_tendsto_atTop (MagnitudeInjective q c d p hq hd hi hp)

/-- Coprimality excludes positive-power resonance when the divisor magnitude exceeds one. -/
theorem CoprimeIndependent (q d : ℕ) (hd : 2 ≤ d)
    (hc : q.Coprime d) : MultiplicativelyIndependent q d := by
  intro a b ha hb he
  have hcop := hc.pow a b
  rw [he] at hcop
  have hone : d ^ b = 1 := by simpa using hcop
  have hlarge := Nat.one_lt_pow hb.ne' (by omega : 1 < d)
  omega

/-- Two nonproportional prime-exponent rows exclude every positive-power resonance. -/
theorem ExponentIndependent (q d p r : ℕ)
    (hdet : q.factorization p * d.factorization r ≠
      q.factorization r * d.factorization p) : MultiplicativelyIndependent q d := by
  intro a b ha _ he
  have hp := congrArg (fun n : ℕ => n.factorization p) he
  have hr := congrArg (fun n : ℕ => n.factorization r) he
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hp hr
  have hcross : a * (q.factorization p * d.factorization r) =
      a * (q.factorization r * d.factorization p) := by
    calc
      a * (q.factorization p * d.factorization r) =
          (a * q.factorization p) * d.factorization r := by ring
      _ = (b * d.factorization p) * d.factorization r := by rw [hp]
      _ = (b * d.factorization r) * d.factorization p := by ring
      _ = (a * q.factorization r) * d.factorization p := by rw [hr]
      _ = a * (q.factorization r * d.factorization p) := by ring
  exact hdet (Nat.eq_of_mul_eq_mul_left ha hcross)

/-- Independence can hold with identical prime supports and a nontrivial gcd. -/
theorem TwelveEighteenIndependent : MultiplicativelyIndependent 12 18 := by
  apply ExponentIndependent 12 18 2 3
  have h2 : Nat.Prime 2 := by decide
  have h3 : Nat.Prime 3 := by decide
  have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  have h18 : (18 : ℕ) = 2 * 3 ^ 2 := by norm_num
  rw [h12, h18]
  rw [Nat.factorization_mul (by norm_num : 2 ^ 2 ≠ 0) (by norm_num : 3 ≠ 0),
    Nat.factorization_mul (by norm_num : 2 ≠ 0) (by norm_num : 3 ^ 2 ≠ 0)]
  simp only [Nat.factorization_pow, h2.factorization, h3.factorization,
    Finsupp.add_apply, Finsupp.smul_apply]
  norm_num

/-- A shared-support family keeps dividing forever; independence does not imply an affine tail. -/
theorem CommonSupportBlock (j : ℕ) :
    Raw 12 0 18 (0, (8 : ℤ) ^ j) = (0, 12 * 8 ^ j) ∧
      Raw 12 0 18 (0, 12 * (8 : ℤ) ^ j) = (0, 144 * 8 ^ j) ∧
      Raw 12 0 18 (0, 144 * (8 : ℤ) ^ j) = (0, 8 ^ (j + 1)) := by
  have hnNat : ¬3 ∣ (8 : ℕ) ^ j := by
    intro h
    have hbad := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h
    norm_num at hbad
  have hn : ¬(3 : ℤ) ∣ (8 : ℤ) ^ j := by exact_mod_cast hnNat
  have hfirst : ¬(18 : ℤ) ∣ (8 : ℤ) ^ j :=
    fun h => hn (dvd_trans (by norm_num : (3 : ℤ) ∣ 18) h)
  have hsecond : ¬(18 : ℤ) ∣ 12 * (8 : ℤ) ^ j := by
    simp only [Int.dvd_iff_emod_eq_zero] at hn ⊢
    omega
  have hthird : (18 : ℤ) ∣ 144 * (8 : ℤ) ^ j :=
    dvd_mul_of_dvd_left (by norm_num : (18 : ℤ) ∣ 144) _
  have hquot : 144 * (8 : ℤ) ^ j / 18 = 8 ^ (j + 1) := by
    have he : 144 * (8 : ℤ) ^ j = 18 * (8 ^ (j + 1)) := by ring
    rw [he, Int.mul_ediv_cancel_left _ (by norm_num : (18 : ℤ) ≠ 0)]
  simp [Raw, hfirst, hsecond, hthird, hquot]
  ring

/-- The shared-support seed has a three-tick repeated itinerary and grows by eight per block. -/
theorem CommonSupportIterate (j : ℕ) :
    Iterate (Raw 12 0 18) (3 * j) (0, 1) = (0, (8 : ℤ) ^ j) := by
  induction j with
  | zero => { simp [Iterate] }
  | succ j ih => {
      rw [show 3 * (j + 1) = 3 * j + 3 by omega, GeneralizedCollatz.IterateAdd, ih]
      obtain ⟨h0, h1, h2⟩ := CommonSupportBlock j
      simp only [Iterate, h0, h1, h2]
    }

/-- A dependent family has a genuine nonreal raw five-cycle, so independence is essential. -/
theorem DependentFiveCycle :
    Iterate (Raw 4 0 8) 5 (0, 1) = (0, 1) ∧
      ∀ n : Fin 4, Iterate (Raw 4 0 8) (n.val + 1) (0, 1) ≠ (0, 1) := by
  decide

/-- An actual quadratic ring scalar divides exactly when it divides both coordinates. -/
theorem ScalarDivides (tau nu d : ℤ) (z : LatticeRing tau nu) :
    (d : LatticeRing tau nu) ∣ z ↔ d ∣ z.re ∧ d ∣ z.im := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨⟨w.re, by simpa using congrArg (fun v => v.re) hw⟩,
      ⟨w.im, by simpa using congrArg (fun v => v.im) hw⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨x, y⟩, ?_⟩
    apply QuadraticAlgebra.ext
    · simpa using hx
    · simpa using hy

/-- Coordinate division reconstructs the legal quotient of the original ring element. -/
theorem ScalarQuotient (tau nu d : ℤ) (z : LatticeRing tau nu)
    (hz : (d : LatticeRing tau nu) ∣ z) :
    (d : LatticeRing tau nu) * ⟨z.re / d, z.im / d⟩ = z := by
  have hg := (ScalarDivides tau nu d z).mp hz
  apply QuadraticAlgebra.ext <;> simp [Int.mul_ediv_cancel' hg.1,
    Int.mul_ediv_cancel' hg.2]

/-- A nonzero scalar quotient is unique; no integral-domain hypothesis is hidden here. -/
theorem ScalarUnique (tau nu d : ℤ) (z u v : LatticeRing tau nu) (hd : d ≠ 0)
    (hu : (d : LatticeRing tau nu) * u = z)
    (hv : (d : LatticeRing tau nu) * v = z) : u = v := by
  have hr := congrArg (fun w => w.re) (hu.trans hv.symm)
  have hi := congrArg (fun w => w.im) (hu.trans hv.symm)
  simp at hr hi
  apply QuadraticAlgebra.ext
  · exact mul_left_cancel₀ hd (by simpa using hr)
  · exact mul_left_cancel₀ hd (by simpa using hi)

/-- The ring map uses actual element divisibility, not division in its fraction field. -/
noncomputable def RingRaw (tau nu q c d : ℤ) (z : LatticeRing tau nu) :
    LatticeRing tau nu := by
  classical
  exact if (d : LatticeRing tau nu) ∣ z then ⟨z.re / d, z.im / d⟩
    else (q : LatticeRing tau nu) * z + (c : LatticeRing tau nu)

/-- The branch-aware coordinate map intertwines each original ring tick exactly. -/
theorem RingCoordinates (tau nu q c d : ℤ) (z : LatticeRing tau nu) :
    Coordinates tau nu (RingRaw tau nu q c d z) = Raw q c d (Coordinates tau nu z) := by
  classical
  by_cases h : d ∣ z.re ∧ d ∣ z.im <;>
    simp [Coordinates, RingRaw, Raw, ScalarDivides, h]

/-- All-time coordinate recovery preserves the same state, guards and raw clock. -/
theorem RingCoordinatesIter (tau nu q c d : ℤ) (z : LatticeRing tau nu) (n : ℕ) :
    Coordinates tau nu (Iterate (RingRaw tau nu q c d) n z) =
      Iterate (Raw q c d) n (Coordinates tau nu z) := by
  exact SemiconjugacyIterates _ _ _ (RingCoordinates tau nu q c d) n z

/-- Coefficient matching transfers scalar dynamics between different quadratic orders. -/
def OrderTransfer (tau nu tau' nu' : ℤ) (z : LatticeRing tau nu) :
    LatticeRing tau' nu' := ⟨z.re, z.im⟩

/-- The inverse coefficient matching loses neither states nor phases. -/
theorem OrderTransferInverse (tau nu tau' nu' : ℤ) (z : LatticeRing tau nu) :
    OrderTransfer tau' nu' tau nu (OrderTransfer tau nu tau' nu' z) = z := by
  apply QuadraticAlgebra.ext <;> rfl

/-- Scalar raw ticks intertwine even though the transfer need not preserve multiplication. -/
theorem OrderTransferRaw (tau nu tau' nu' q c d : ℤ) (z : LatticeRing tau nu) :
    OrderTransfer tau nu tau' nu' (RingRaw tau nu q c d z) =
      RingRaw tau' nu' q c d (OrderTransfer tau nu tau' nu' z) := by
  classical
  by_cases hg : d ∣ z.re ∧ d ∣ z.im
  · simp [RingRaw, ScalarDivides, OrderTransfer, hg]
  · simp [RingRaw, ScalarDivides, OrderTransfer, hg]
    apply QuadraticAlgebra.ext <;> simp

/-- The order change retains every raw time, not merely a return subsequence. -/
theorem OrderTransferIterate (tau nu tau' nu' q c d : ℤ)
    (z : LatticeRing tau nu) (n : ℕ) :
    OrderTransfer tau nu tau' nu' (Iterate (RingRaw tau nu q c d) n z) =
      Iterate (RingRaw tau' nu' q c d) n (OrderTransfer tau nu tau' nu' z) := by
  exact SemiconjugacyIterates _ _ _ (OrderTransferRaw tau nu tau' nu' q c d) n z

/-- Dynamical conjugacy between Gaussian and Eisenstein orders is not a ring homomorphism. -/
theorem OrderTransferNotMultiplicative :
    OrderTransfer 0 1 (-1) 1 ((⟨0, 1⟩ : LatticeRing 0 1) * ⟨0, 1⟩) ≠
      OrderTransfer 0 1 (-1) 1 ⟨0, 1⟩ * OrderTransfer 0 1 (-1) 1 ⟨0, 1⟩ := by
  intro he
  have hi := congrArg (fun z => z.im) he
  norm_num [OrderTransfer] at hi

/-- The same independent scalar family escapes in the original complex embedding norm. -/
theorem ComplexOffAxisEscape (tau nu q c d : ℤ) (z : LatticeRing tau nu)
    (h : tau ^ 2 < 4 * nu) (hq : 2 ≤ q.natAbs) (hd : 2 ≤ d.natAbs)
    (hi : MultiplicativelyIndependent q.natAbs d.natAbs) (hz : z.im ≠ 0) :
    ∀ B : ℝ, ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      B < ‖ImaginaryEmbedding tau nu h (Iterate (RingRaw tau nu q c d) n z)‖ := by
  intro B
  have hp := ImaginaryGeneratorPositive tau nu h
  obtain ⟨N, hN⟩ := exists_nat_gt (B / (ImaginaryGenerator tau nu).im)
  have hb : B < (N : ℝ) * (ImaginaryGenerator tau nu).im := (div_lt_iff₀ hp).mp hN
  have ht := OffAxisEscape q c d (Coordinates tau nu z) hq hd hi hz
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      N + 1 ≤ (Iterate (Raw q c d) n (Coordinates tau nu z)).2.natAbs :=
    (Filter.tendsto_atTop.mp ht) (N + 1)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨K, ?_⟩
  intro n hn
  have hc := congrArg (fun p : Point => p.2) (RingCoordinatesIter tau nu q c d z n)
  change (Iterate (RingRaw tau nu q c d) n z).im =
    (Iterate (Raw q c d) n (Coordinates tau nu z)).2 at hc
  have hlarge : N < (Iterate (RingRaw tau nu q c d) n z).im.natAbs := by
    rw [hc]
    have hbound := hK n hn
    omega
  have hreal : (N : ℝ) < ((Iterate (RingRaw tau nu q c d) n z).im.natAbs : ℝ) := by
    exact_mod_cast hlarge
  exact lt_of_lt_of_le (hb.trans (mul_lt_mul_of_pos_right hreal hp))
    (ImaginaryEmbeddingNorm tau nu h (Iterate (RingRaw tau nu q c d) n z))

end GeneralizedCollatz.ScalarEscape
