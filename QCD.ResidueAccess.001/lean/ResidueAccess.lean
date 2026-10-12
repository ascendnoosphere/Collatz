-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import RepunitDivisor
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Accessible residues of the offset slice `q n + c`

For `q ≥ 2`, `c ≥ 1` and `D ≥ 2` the residue map of the offset slice is
`AccessStep q c D r = (q r + c) % D`.  This family studies the orbit of the
residue `0` under that map, the return time of the orbit, and the modulus
`AccessModulus q c D = D (q - 1) / gcd (c (D (q - 1)))` whose multiplicative
order governs the returns.  Coprimality of `q` and `D` is not needed for the
orbit formula and the criterion; it is used for injectivity of the residue map
and for the prime case.

The results formalize Section 2.1 of the residue-criticality source: the orbit
formula `F^j(0) = c G_j(q) mod D`, the criterion that the orbit returns to `0`
exactly at the exponents `j` with `AccessModulus q c D ∣ q^j - 1`, pure
periodicity of the orbit, distinctness of the residues below the least positive
return time `m`, the counting bound `m ≤ D`, and the prime case, where the
criterion reduces to `ord_p(q)` or to `p ∣ j`.
-/

namespace GeneralizedCollatz

set_option autoImplicit false

/-- The residue map of the offset slice: one affine event `r ↦ q r + c`
reduced modulo `D`. -/
def AccessStep (q c D r : ℕ) : ℕ := (q * r + c) % D

/-- The modulus whose multiplicative order gives the return times of the
orbit of `0`: `D (q - 1) / gcd (c (D (q - 1)))`. -/
def AccessModulus (q c D : ℕ) : ℕ := D * (q - 1) / Nat.gcd c (D * (q - 1))

/-- The `j`-th residue of the orbit of `0` under the offset residue map. -/
def AccessOrbit (q c D j : ℕ) : ℕ := Iterate (AccessStep q c D) j 0

/-- `m` is the least positive exponent with `AccessModulus q c D ∣ q^m - 1`.
Equivalently `m` is the length of the cycle of `0`. -/
def AccessLeast (q c D m : ℕ) : Prop :=
  0 < m ∧ AccessModulus q c D ∣ q ^ m - 1 ∧
    ∀ s, 0 < s → s < m → ¬ AccessModulus q c D ∣ q ^ s - 1

/-! ## The orbit formula -/

/-- The first residue is the offset reduced modulo `D`. -/
theorem AccessStepZero (q c D : ℕ) : AccessStep q c D 0 = c % D := by
  simp [AccessStep]

/-- The orbit starts at the accessible residue `0`. -/
theorem AccessOrbitZero (q c D : ℕ) : AccessOrbit q c D 0 = 0 := by
  simp [AccessOrbit, Iterate]

/-- One step of the orbit. -/
theorem AccessOrbitSucc (q c D j : ℕ) :
    AccessOrbit q c D (j + 1) = AccessStep q c D (AccessOrbit q c D j) := by
  simp [AccessOrbit, Iterate]

/-- The orbit splits at a block boundary. -/
theorem AccessOrbitAdd (q c D j k : ℕ) :
    AccessOrbit q c D (j + k) = Iterate (AccessStep q c D) k (AccessOrbit q c D j) := by
  simp only [AccessOrbit]
  exact IterateAdd (AccessStep q c D) j k 0

/-- **Orbit formula.** The `j`-th residue of the orbit is `c G_j(q)` modulo
`D`, where `G_j` is the repunit sum. -/
theorem AccessOrbitEqOffsetMulRepunit (q c D j : ℕ) :
    AccessOrbit q c D j = (c * RepunitSum q j) % D := by
  induction j with
  | zero => simp [AccessOrbit, Iterate, RepunitSum]
  | succ j ih =>
      rw [AccessOrbitSucc, ih, AccessStep]
      have hmod : (q * ((c * RepunitSum q j) % D) + c) % D
          = (q * (c * RepunitSum q j) + c) % D :=
        (Nat.ModEq.mul_left q (Nat.mod_modEq (c * RepunitSum q j) D)).add_right c
      rw [hmod, show q * (c * RepunitSum q j) + c
          = c * (q * RepunitSum q j + 1) by ring, RepunitSumSuccMul]
/-- The orbit returns to `0` exactly when `D` divides `c G_j(q)`. -/
theorem AccessOrbitEqZeroIff (q c D j : ℕ) :
    AccessOrbit q c D j = 0 ↔ D ∣ c * RepunitSum q j := by
  rw [AccessOrbitEqOffsetMulRepunit]
  exact Nat.dvd_iff_mod_eq_zero.symm

/-! ## The modulus criterion -/

/-- Cleared form of the criterion: multiplying the dividend by `D (q - 1)`
replaces the modulus `D (q - 1)` by its quotient by `gcd (c (D (q - 1)))`. -/
theorem AccessModulusDvdIffMul (q c D X : ℕ) (hq : 2 ≤ q) (hD : 0 < D) :
    D * (q - 1) ∣ c * X ↔ AccessModulus q c D ∣ X := by
  have hA : 0 < D * (q - 1) := Nat.mul_pos hD (by omega)
  have hg : 0 < Nat.gcd c (D * (q - 1)) := Nat.gcd_pos_of_pos_right c hA
  have hgM : Nat.gcd c (D * (q - 1)) * AccessModulus q c D = D * (q - 1) := by
    show Nat.gcd c (D * (q - 1)) * (D * (q - 1) / Nat.gcd c (D * (q - 1)))
        = D * (q - 1)
    exact (mul_comm _ _).trans (Nat.div_mul_cancel (Nat.gcd_dvd_right c (D * (q - 1))))
  constructor
  · intro h
    have h2 : D * (q - 1) ∣ D * (q - 1) * X := dvd_mul_right _ _
    have hgXd : D * (q - 1) ∣ Nat.gcd c (D * (q - 1)) * X := by
      have h3 : Nat.gcd (c * X) (D * (q - 1) * X)
          = Nat.gcd c (D * (q - 1)) * X := Nat.gcd_mul_right c X (D * (q - 1))
      rw [← h3]
      exact Nat.dvd_gcd h h2
    have hgX : Nat.gcd c (D * (q - 1)) * AccessModulus q c D
        ∣ Nat.gcd c (D * (q - 1)) * X := by
      rw [hgM]
      exact hgXd
    exact Nat.dvd_of_mul_dvd_mul_left hg hgX
  · intro h
    have h1 : Nat.gcd c (D * (q - 1)) * AccessModulus q c D
        ∣ Nat.gcd c (D * (q - 1)) * X := Nat.mul_dvd_mul_left _ h
    have h2 : Nat.gcd c (D * (q - 1)) * X ∣ c * X :=
      Nat.mul_dvd_mul_right (Nat.gcd_dvd_left c (D * (q - 1))) X
    show D * (q - 1) ∣ c * X
    rw [← hgM]
    exact h1.trans h2

/-- **Modulus criterion.** The orbit returns to `0` at time `j` exactly when
`AccessModulus q c D` divides `q^j - 1`. -/
theorem AccessOrbitEqZeroIffModulus (q c D j : ℕ) (hq : 2 ≤ q) (hD : 0 < D) :
    AccessOrbit q c D j = 0 ↔ AccessModulus q c D ∣ q ^ j - 1 := by
  have hq1 : 1 ≤ q := by omega
  have hpos : 0 < q - 1 := by omega
  have hpred : c * RepunitSum q j * (q - 1) = c * (q ^ j - 1) := by
    calc c * RepunitSum q j * (q - 1) = c * ((q - 1) * RepunitSum q j) := by ring
      _ = c * (q ^ j - 1) := by rw [RepunitSumMulPred q j hq1]
  rw [AccessOrbitEqZeroIff]
  have h1 : D ∣ c * RepunitSum q j ↔ D * (q - 1) ∣ c * (q ^ j - 1) := by
    constructor
    · intro h
      have h' : D * (q - 1) ∣ c * RepunitSum q j * (q - 1) :=
        Nat.mul_dvd_mul_right h (q - 1)
      rwa [hpred] at h'
    · intro h
      rw [← hpred] at h
      rw [mul_comm D (q - 1), mul_comm (c * RepunitSum q j) (q - 1)] at h
      exact (Nat.mul_dvd_mul_iff_left hpos).mp h
  exact h1.trans (AccessModulusDvdIffMul q c D (q ^ j - 1) hq hD)

/-- The modulus divides the cleared modulus `D (q - 1)`. -/
theorem AccessModulusDvdMulPred (q c D : ℕ) (hq : 2 ≤ q) (hD : 0 < D) :
    AccessModulus q c D ∣ D * (q - 1) := by
  have hA : 0 < D * (q - 1) := Nat.mul_pos hD (by omega)
  rw [AccessModulus]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_right c (D * (q - 1)))

/-- The modulus is coprime to the multiplier `q` once `q` is coprime to `D`. -/
theorem AccessModulusCoprimeQ (q c D : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) : (AccessModulus q c D).Coprime q := by
  have hA : 0 < D * (q - 1) := Nat.mul_pos hD (by omega)
  have hq1 : (q - 1).Coprime q := by
    have := Nat.coprime_self_sub_left (show 1 ≤ q by omega)
    simpa using this.mpr (Nat.coprime_one_left q)
  have hcopA : q.Coprime (D * (q - 1)) := hcop.symm.mul_right hq1.symm
  exact (Nat.Coprime.coprime_dvd_right (AccessModulusDvdMulPred q c D hq hD) hcopA).symm

/-- The residue map remembers the residue class modulo `D` when `q` is
coprime to `D`: it is injective on residue classes. -/
theorem AccessStepEqIff (q c D r r' : ℕ) (hD : 0 < D) (hcop : D.Coprime q) :
    AccessStep q c D r = AccessStep q c D r' ↔ r % D = r' % D := by
  have hgcd : D.gcd q = 1 := hcop.gcd_eq_one
  constructor
  · intro h
    have hm : q * r + c ≡ q * r' + c [MOD D] := h
    have hm' : q * r ≡ q * r' [MOD D] :=
      Nat.ModEq.add_right_cancel' c hm
    have hq : q * r = r * q := mul_comm q r
    have hq' : q * r' = r' * q := mul_comm q r'
    rw [hq, hq'] at hm'
    have hm'' : r ≡ r' [MOD D / D.gcd q] := Nat.ModEq.cancel_right_div_gcd hD hm'
    rw [hgcd, Nat.div_one] at hm''
    exact hm''
  · intro h
    show (q * r + c) % D = (q * r' + c) % D
    have hm : r ≡ r' [MOD D] := h
    exact (Nat.ModEq.mul_left q hm).add_right c


/-! ## Periodicity of the accessible orbit -/

/-- A divisibility `q^k - 1` is the same statement as the congruence
`q^k ≡ 1`. -/
theorem AccessModulusModEqOne {M q k : ℕ} (hq : 1 ≤ q) (h : M ∣ q ^ k - 1) :
    q ^ k ≡ 1 [MOD M] := by
  have hzero : q ^ k - 1 ≡ 0 [MOD M] := Nat.modEq_zero_iff_dvd.mpr h
  have h1 : (q ^ k - 1) + 1 ≡ 0 + 1 [MOD M] := hzero.add (Nat.ModEq.refl 1)
  rwa [Nat.sub_add_cancel (Nat.one_le_pow k q hq), zero_add] at h1

/-- A congruence `q^k ≡ 1` is the same statement as the divisibility
`M ∣ q^k - 1`. -/
theorem AccessModulusDvdPredOfModEq {M q k : ℕ} (h1 : 1 ≤ q ^ k)
    (h : q ^ k ≡ 1 [MOD M]) : M ∣ q ^ k - 1 := by
  have hsub : q ^ k - 1 ≡ 1 - 1 [MOD M] :=
    Nat.ModEq.sub h1 le_rfl h (Nat.ModEq.refl 1)
  simpa using Nat.modEq_zero_iff_dvd.mp hsub

/-- Iterates at block boundaries commute. -/
theorem AccessIterateComm (q c D m j : ℕ) (x : ℕ) :
    Iterate (AccessStep q c D) m (Iterate (AccessStep q c D) j x)
      = Iterate (AccessStep q c D) j (Iterate (AccessStep q c D) m x) := by
  rw [← IterateAdd (AccessStep q c D) j m x,
    ← IterateAdd (AccessStep q c D) m j x, Nat.add_comm]

/-- The orbit returns to `0` at the least positive exponent. -/
theorem AccessOrbitEqZeroOfLeast (q c D m : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hm : AccessLeast q c D m) : AccessOrbit q c D m = 0 :=
  (AccessOrbitEqZeroIffModulus q c D m hq hD).mpr hm.2.1

/-- **Purity of the period.** The orbit of `0` is periodic with period `m`,
not merely eventually periodic. -/
theorem AccessOrbitPeriod (q c D m j : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hm : AccessLeast q c D m) :
    AccessOrbit q c D (j + m) = AccessOrbit q c D j := by
  have hm0 : AccessOrbit q c D m = 0 := AccessOrbitEqZeroOfLeast q c D m hq hD hm
  calc AccessOrbit q c D (j + m)
      = Iterate (AccessStep q c D) m (AccessOrbit q c D j) :=
        AccessOrbitAdd q c D j m
    _ = Iterate (AccessStep q c D) j (AccessOrbit q c D m) :=
        AccessIterateComm q c D m j 0
    _ = AccessOrbit q c D j := by rw [hm0]; rfl

/-- The period propagates to multiples of the least positive exponent. -/
theorem AccessOrbitPeriodMul (q c D m j t : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hm : AccessLeast q c D m) :
    AccessOrbit q c D (j + m * t) = AccessOrbit q c D j := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hstep : j + m * (t + 1) = (j + m * t) + m := by ring
      rw [hstep, AccessOrbitPeriod q c D m (j + m * t) hq hD hm, ih]

/-- **Return times.** The orbit visits `0` exactly at the multiples of the
least positive exponent. -/
theorem AccessOrbitEqZeroIffDvd (q c D m j : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hm : AccessLeast q c D m) : AccessOrbit q c D j = 0 ↔ m ∣ j := by
  constructor
  · intro h
    have hmod : AccessModulus q c D ∣ q ^ j - 1 :=
      (AccessOrbitEqZeroIffModulus q c D j hq hD).mp h
    have hqm : q ^ m ≡ 1 [MOD AccessModulus q c D] :=
      AccessModulusModEqOne (by omega) hm.2.1
    have hqj : q ^ j ≡ 1 [MOD AccessModulus q c D] :=
      AccessModulusModEqOne (by omega) hmod
    have hpow : q ^ (m * (j / m)) ≡ 1 [MOD AccessModulus q c D] := by
      have h1 := Nat.ModEq.pow (j / m) hqm
      rwa [← Nat.pow_mul, one_pow] at h1
    have hsplit : q ^ (m * (j / m) + j % m) ≡ q ^ (j % m) [MOD AccessModulus q c D] := by
      have h1 := hpow.mul (Nat.ModEq.refl (q ^ (j % m)))
      rwa [← Nat.pow_add, one_mul] at h1
    have hjr : q ^ (j % m) ≡ 1 [MOD AccessModulus q c D] := by
      rw [← Nat.div_add_mod j m] at hqj
      exact hsplit.symm.trans hqj
    have hdiv : AccessModulus q c D ∣ q ^ (j % m) - 1 :=
      AccessModulusDvdPredOfModEq (Nat.one_le_pow _ q (by omega)) hjr
    by_cases hr0 : j % m = 0
    · have hj : j = m * (j / m) := by
        calc j = m * (j / m) + j % m := (Nat.div_add_mod j m).symm
          _ = m * (j / m) := by rw [hr0, add_zero]
      exact ⟨j / m, hj⟩
    · exact absurd hdiv (hm.2.2 (j % m) (Nat.pos_of_ne_zero hr0) (Nat.mod_lt j hm.1))
  · rintro ⟨t, rfl⟩
    have := AccessOrbitPeriodMul q c D m 0 t hq hD hm
    simpa [AccessOrbitZero] using this

/-- No two distinct indices below `m` carry the same residue. -/
private theorem AccessOrbitLtEqFalse (q c D m i j : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hm : AccessLeast q c D m) (hj : j < m) (hij : AccessOrbit q c D i = AccessOrbit q c D j)
    (hlt : i < j) : False := by
  have hm0 : AccessOrbit q c D m = 0 := AccessOrbitEqZeroOfLeast q c D m hq hD hm
  have hstep : AccessOrbit q c D (i + (m - j))
      = Iterate (AccessStep q c D) (m - j) (AccessOrbit q c D i) :=
    AccessOrbitAdd q c D i (m - j)
  rw [hij] at hstep
  have hback : Iterate (AccessStep q c D) (m - j) (AccessOrbit q c D j)
      = AccessOrbit q c D (j + (m - j)) :=
    (AccessOrbitAdd q c D j (m - j)).symm
  rw [hback, show j + (m - j) = m by omega, hm0] at hstep
  have hmod' : AccessModulus q c D ∣ q ^ (i + (m - j)) - 1 :=
    (AccessOrbitEqZeroIffModulus q c D (i + (m - j)) hq hD).mp hstep
  exact absurd hmod'
    (hm.2.2 (i + (m - j)) (by omega) (by omega))

/-- **Distinctness.** The first `m` residues of the orbit are pairwise
distinct. -/
theorem AccessOrbitDistinct (q c D m i j : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hm : AccessLeast q c D m) (hi : i < m) (hj : j < m)
    (hij : AccessOrbit q c D i = AccessOrbit q c D j) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact (AccessOrbitLtEqFalse q c D m i j hq hD hm hj hij hlt).elim
  · exact heq
  · exact (AccessOrbitLtEqFalse q c D m j i hq hD hm hi hij.symm hgt).elim

/-- **Counting bound.** The least positive return time is at most `D`. -/
theorem AccessOrbitCardLe (q c D m : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hm : AccessLeast q c D m) : m ≤ D := by
  have hinj : Set.InjOn (AccessOrbit q c D) (↑(Finset.range m) : Set ℕ) := by
    intro i hi j hj hij
    exact AccessOrbitDistinct q c D m i j hq hD hm (Finset.mem_range.mp hi)
      (Finset.mem_range.mp hj) hij
  have hcard : (Finset.image (AccessOrbit q c D) (Finset.range m)).card = m := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : Finset.image (AccessOrbit q c D) (Finset.range m) ⊆ Finset.range D := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    rw [AccessOrbitEqOffsetMulRepunit]
    exact Finset.mem_range.mpr (Nat.mod_lt _ hD)
  have hle := Finset.card_le_card hsub
  rw [hcard, Finset.card_range] at hle
  exact hle

/-- Every accessible residue has a unique representative index below `m`. -/
theorem AccessOrbitRepresentative (q c D m j : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hm : AccessLeast q c D m) :
    ∃! i, i < m ∧ AccessOrbit q c D j = AccessOrbit q c D i := by
  have hsplit : j % m + m * (j / m) = j := by
    have := Nat.div_add_mod j m
    omega
  refine ⟨j % m, ⟨Nat.mod_lt j hm.1, ?_⟩, ?_⟩
  · have := AccessOrbitPeriodMul q c D m (j % m) (j / m) hq hD hm
    rwa [hsplit] at this
  · intro i hi
    have hthis : AccessOrbit q c D j = AccessOrbit q c D (j % m) := by
      have := AccessOrbitPeriodMul q c D m (j % m) (j / m) hq hD hm
      rwa [hsplit] at this
    exact (AccessOrbitDistinct q c D m (j % m) i hq hD hm
      (Nat.mod_lt j hm.1) hi.1 (hthis.symm.trans hi.2)).symm


/-! ## The prime case -/

/-- Modulo a prime where the multiplier is one, the repunit sum counts its
terms. -/
theorem AccessRepunitSumModeqIndex (q p j : ℕ) (h : q ≡ 1 [MOD p]) :
    RepunitSum q j ≡ j [MOD p] := by
  induction j with
  | zero => exact Nat.ModEq.refl 0
  | succ j ih =>
      rw [RepunitSumSucc]
      have hpow : q ^ j ≡ 1 [MOD p] := by
        have := Nat.ModEq.pow j h
        simpa using this
      simpa using ih.add hpow

/-- **Prime case, multiplier not one.** If `p` is prime, `p` does not divide
`c`, and `q` is not one modulo `p`, the accessible exponents are the
multiples of the order of `q` modulo `p`. -/
theorem AccessPrimeOrbitIff (q c p j : ℕ) (hq : 2 ≤ q) (hp : p.Prime)
    (hc : ¬ p ∣ c) (hq1 : ¬ p ∣ q - 1) :
    AccessOrbit q c p j = 0 ↔ p ∣ q ^ j - 1 := by
  have hpred : (q - 1) * RepunitSum q j = q ^ j - 1 := RepunitSumMulPred q j (by omega)
  have hpc : p.Coprime c := (hp.coprime_iff_not_dvd).mpr hc
  have hpq1 : p.Coprime (q - 1) := (hp.coprime_iff_not_dvd).mpr hq1
  constructor
  · intro h
    have hdiv : p ∣ c * RepunitSum q j := (AccessOrbitEqZeroIff q c p j).mp h
    have hG : p ∣ RepunitSum q j := hpc.dvd_of_dvd_mul_left hdiv
    rw [← hpred]
    exact Dvd.dvd.mul_left hG (q - 1)
  · intro h
    rw [← hpred] at h
    have hG : p ∣ RepunitSum q j := hpq1.dvd_of_dvd_mul_left h
    exact (AccessOrbitEqZeroIff q c p j).mpr (Dvd.dvd.mul_left hG c)

/-- **Prime case, multiplier one.** If `p` is prime, `p` does not divide `c`,
and `p` divides `q - 1`, the accessible exponents are exactly the multiples
of `p`. -/
theorem AccessPrimeOrbitIffIndex (q c p j : ℕ) (hq : 2 ≤ q) (hp : p.Prime)
    (hc : ¬ p ∣ c) (hq1 : p ∣ q - 1) :
    AccessOrbit q c p j = 0 ↔ p ∣ j := by
  have hqmod : q ≡ 1 [MOD p] := by
    have hzero : q - 1 ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hq1
    have h1 : (q - 1) + 1 ≡ 0 + 1 [MOD p] := hzero.add (Nat.ModEq.refl 1)
    rwa [Nat.sub_add_cancel (show 1 ≤ q by omega), zero_add] at h1
  have hcount : RepunitSum q j ≡ j [MOD p] := AccessRepunitSumModeqIndex q p j hqmod
  have hpc : p.Coprime c := (hp.coprime_iff_not_dvd).mpr hc
  constructor
  · intro h
    have hdiv : p ∣ c * RepunitSum q j := (AccessOrbitEqZeroIff q c p j).mp h
    have hG : p ∣ RepunitSum q j := hpc.dvd_of_dvd_mul_left hdiv
    have hzero : RepunitSum q j ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hG
    exact Nat.modEq_zero_iff_dvd.mp (hcount.symm.trans hzero)
  · intro h
    have hzero : j ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h
    have hG : p ∣ RepunitSum q j := Nat.modEq_zero_iff_dvd.mp (hcount.trans hzero)
    exact (AccessOrbitEqZeroIff q c p j).mpr (Dvd.dvd.mul_left hG c)

/-- **Full access at a prime.** If `p` is prime, `p` does not divide `c`, and
`p` divides `q - 1`, then the least positive return time is `p` itself. -/
theorem AccessPrimeFullAccess (q c p : ℕ) (hq : 2 ≤ q) (hp : p.Prime)
    (hc : ¬ p ∣ c) (hq1 : p ∣ q - 1) : AccessLeast q c p p := by
  refine ⟨hp.pos, ?_, ?_⟩
  · exact (AccessOrbitEqZeroIffModulus q c p p hq hp.pos).mp
      ((AccessPrimeOrbitIffIndex q c p p hq hp hc hq1).mpr (dvd_refl p))
  · intro s hs hsp
    exact fun hdiv => Nat.not_dvd_of_pos_of_lt hs hsp
      ((AccessPrimeOrbitIffIndex q c p s hq hp hc hq1).mp
        ((AccessOrbitEqZeroIffModulus q c p s hq hp.pos).mpr hdiv))

/-- **Exhaustion at a prime.** If `p` is prime, `p` does not divide `c`, and
`p` divides `q - 1`, the orbit of `0` visits every residue modulo `p`. -/
theorem AccessPrimeOrbitSurjective (q c p : ℕ) (hq : 2 ≤ q) (hp : p.Prime)
    (hc : ¬ p ∣ c) (hq1 : p ∣ q - 1) (r : ℕ) (hr : r < p) :
    ∃ j < p, AccessOrbit q c p j = r := by
  have hm : AccessLeast q c p p := AccessPrimeFullAccess q c p hq hp hc hq1
  have hinj : Set.InjOn (AccessOrbit q c p) (↑(Finset.range p) : Set ℕ) := by
    intro i hi j hj hij
    exact AccessOrbitDistinct q c p p i j hq hp.pos hm (Finset.mem_range.mp hi)
      (Finset.mem_range.mp hj) hij
  have hcard : (Finset.image (AccessOrbit q c p) (Finset.range p)).card = p := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : Finset.image (AccessOrbit q c p) (Finset.range p) ⊆ Finset.range p := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    rw [AccessOrbitEqOffsetMulRepunit]
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)
  have heq : Finset.image (AccessOrbit q c p) (Finset.range p) = Finset.range p :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq (by rw [hcard, Finset.card_range]))
  have : r ∈ Finset.image (AccessOrbit q c p) (Finset.range p) := by
    rw [heq]
    exact Finset.mem_range.mpr hr
  obtain ⟨j, hj, hj'⟩ := Finset.mem_image.mp this
  exact ⟨j, Finset.mem_range.mp hj, hj'⟩

/-- **Necessity of the prime criterion.** If `p` is prime, `p` does not divide
`c`, and `q` is coprime to `p` but not one modulo `p`, the least positive
return time is smaller than `p`, so the orbit cannot exhaust the residues. -/
theorem AccessPrimeNotFullAccess (q c p m : ℕ) (hq : 2 ≤ q) (hp : p.Prime)
    (hc : ¬ p ∣ c) (hcop : p.Coprime q) (hq1 : ¬ p ∣ q - 1)
    (hm : AccessLeast q c p m) : m < p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hnotdvd : ¬ p ∣ q := (hp.coprime_iff_not_dvd).mp hcop
  have hne : (q : ZMod p) ≠ 0 := by
    intro h
    exact hnotdvd ((ZMod.natCast_eq_zero_iff q p).mp h)
  have hfermat : (q : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have hcast : ((q ^ (p - 1) - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub (Nat.one_le_pow (p - 1) q (by omega)), Nat.cast_pow, hfermat,
      Nat.cast_one, sub_self]
  have hF : p ∣ q ^ (p - 1) - 1 := (ZMod.natCast_eq_zero_iff (q ^ (p - 1) - 1) p).mp hcast
  have hdiv : AccessModulus q c p ∣ q ^ (p - 1) - 1 :=
    (AccessOrbitEqZeroIffModulus q c p (p - 1) hq hp.pos).mp
      ((AccessPrimeOrbitIff q c p (p - 1) hq hp hc hq1).mpr hF)
  have hmle : m ≤ p - 1 := by
    by_contra h
    exact absurd hdiv (hm.2.2 (p - 1) (by omega) (Nat.lt_of_not_le h))
  omega

end GeneralizedCollatz
