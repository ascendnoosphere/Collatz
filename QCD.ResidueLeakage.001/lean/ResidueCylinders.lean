-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import ResidueAccess
import GuardedRecovery
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Legal first-division cylinders

A bounded search executes affine events only until the first divisible state,
then divides once. The search records its affine-event count. Composing these
blocks retains the numerator multiplier needed to lift a source cylinder.
The divisor is positive; signed division is not being replaced by its absolute
value. The search is complete and its cylinders match actual raw division counts.
Natural-density estimates are derived separately from these finite counts.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.ResidueLeakage

/-- Search for the first legal division, retaining its affine-event count. -/
def Hit (q c D : ℕ) : ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _ => none
  | fuel + 1, n =>
      if D ∣ n then some (0, n / D)
      else (Hit q c D fuel (q * n + c)).map (fun z => (z.1 + 1, z.2))

/-- Iterate division blocks, retaining the accumulated numerator multiplier. -/
def Run (q c D m : ℕ) : ℕ → ℕ → Option (ℕ × ℕ)
  | 0, n => some (n, 1)
  | h + 1, n =>
      (Run q c D m h n).bind fun z =>
        (Hit q c D m z.1).map (fun w => (w.2, z.2 * q ^ w.1))

/-- A source is legal to depth `h` exactly when all `h` division blocks exist. -/
def Survives (q c D m h n : ℕ) : Prop := (Run q c D m h n).isSome = true

/-- Canonical representatives of legal source cylinders modulo `D^h`. -/
def Classes (q c D m h : ℕ) : Finset ℕ :=
  (Finset.range (D ^ h)).filter (fun n => (Run q c D m h n).isSome)

/-- Adding a multiple of the divisor preserves the actual division guard. -/
theorem DvdShift (D n t : ℕ) : D ∣ n + D * t ↔ D ∣ n := by
  simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]

/-- A legal quotient changes by exactly the added source digit. -/
theorem DivideShift (D n t : ℕ) (hD : 0 < D) :
    (n + D * t) / D = n / D + t := by
  exact Nat.add_mul_div_left n t hD

/-- A first-division block has one common delay on a complete residue class. -/
theorem HitShift (q c D fuel n t : ℕ) (hD : 0 < D) :
    Hit q c D fuel (n + D * t) =
      (Hit q c D fuel n).map (fun z => (z.1, z.2 + q ^ z.1 * t)) := by
  induction fuel generalizing n t with
  | zero => {
      rfl
    }
  | succ fuel ih => {
      by_cases hn : D ∣ n
      · have hs : D ∣ n + D * t := (DvdShift D n t).mpr hn
        simp [Hit, hn, hs, DivideShift D n t hD]
      · have hs : ¬D ∣ n + D * t := by
          intro hd
          exact hn ((DvdShift D n t).mp hd)
        have ha : q * (n + D * t) + c = (q * n + c) + D * (q * t) := by
          ring
        simp only [Hit, if_neg hn, if_neg hs, ha, ih]
        cases hx : Hit q c D fuel (q * n + c) with
        | none => {
            rfl
          }
        | some z => {
            simp only [Option.map_some]
            congr 2
            rw [pow_succ]
            ring
          }
    }

/-- Source shifts by `D^h` preserve every guard and retain the endpoint multiplier. -/
theorem RunShift (q c D m h n t : ℕ) (hD : 0 < D) :
    Run q c D m h (n + D ^ h * t) =
      (Run q c D m h n).map (fun z => (z.1 + z.2 * t, z.2)) := by
  induction h generalizing n t with
  | zero => {
      simp [Run]
    }
  | succ h ih => {
      have he : n + D ^ (h + 1) * t = n + D ^ h * (D * t) := by
        rw [pow_succ]
        ring
      rw [he]
      simp only [Run, ih]
      cases hz : Run q c D m h n with
      | none => {
          rfl
        }
      | some z => {
          simp only [Option.map_some, Option.bind_some]
          have hy : z.1 + z.2 * (D * t) = z.1 + D * (z.2 * t) := by
            ring
          rw [hy, HitShift q c D m z.1 (z.2 * t) hD]
          cases hw : Hit q c D m z.1 with
          | none => {
              rfl
            }
          | some w => {
              simp only [Option.map_some]
              congr 2
              ring
            }
        }
    }

/-- Every multiplier of a successful prefix is coprime to the divisor. -/
theorem RunCoprime (q c D m h n E P : ℕ) (hcop : q.Coprime D)
    (hr : Run q c D m h n = some (E, P)) : P.Coprime D := by
  induction h generalizing n E P with
  | zero => {
      simp only [Run, Option.some.injEq, Prod.mk.injEq] at hr
      rcases hr with ⟨_, rfl⟩
      exact Nat.coprime_one_left D
    }
  | succ h ih => {
      simp only [Run] at hr
      cases hz : Run q c D m h n with
      | none => {
          simp [hz] at hr
        }
      | some z => {
          simp only [hz, Option.bind_some] at hr
          cases hw : Hit q c D m z.1 with
          | none => {
              simp [hw] at hr
            }
          | some w => {
              simp only [hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
              rcases hr with ⟨_, rfl⟩
              exact (ih n z.1 z.2 hz).mul_left (hcop.pow_left w.1)
            }
        }
    }

/-- Legality is periodic on the complete modulus, including unsuccessful prefixes. -/
theorem SurvivesShift (q c D m h n t : ℕ) (hD : 0 < D) :
    Survives q c D m h (n + D ^ h * t) ↔ Survives q c D m h n := by
  rw [Survives, RunShift q c D m h n t hD]
  cases hx : Run q c D m h n <;> simp [Survives, hx]

/-- The canonical source representative has precisely the original legality. -/
theorem SurvivesMod (q c D m h n : ℕ) (hD : 0 < D) :
    Survives q c D m h n ↔ Survives q c D m h (n % D ^ h) := by
  have hs := SurvivesShift q c D m h (n % D ^ h) (n / D ^ h) hD
  rw [Nat.mod_add_div] at hs
  exact hs

/-- Class membership is a bounded, executable legality test with no orbit cap inference. -/
theorem ClassesMember (q c D m h n : ℕ) :
    n ∈ Classes q c D m h ↔ n < D ^ h ∧ Survives q c D m h n := by
  simp [Classes, Survives]

/-- The depth-zero cylinder is the unique residue modulo one. -/
theorem ClassesZero (q c D m : ℕ) : Classes q c D m 0 = {0} := by
  ext n
  simp [Classes, Run]

/-- Affine iteration is distinct from iteration of the guarded raw map. -/
def Affine (q c k n : ℕ) : ℕ := Iterate (fun x => q * x + c) k n

/-- Residue iteration starts at the canonical representative, even at time zero. -/
def Residue (q c D k n : ℕ) : ℕ := Iterate (AccessStep q c D) k (n % D)

/-- The affine iterate has exactly the residue predicted by the residue dynamics. -/
theorem AffineResidue (q c D k n : ℕ) :
    Affine q c k n % D = Residue q c D k n := by
  induction k with
  | zero => {
      rfl
    }
  | succ k ih => {
      change (q * Affine q c k n + c) % D =
        (q * Residue q c D k n + c) % D
      rw [← ih]
      exact ((Nat.ModEq.mul_left q (Nat.mod_modEq (Affine q c k n) D)).add_right c).symm
    }

/-- Every residue iterate remains inside the finite residue interval. -/
theorem ResidueLt (q c D k n : ℕ) (hD : 0 < D) : Residue q c D k n < D := by
  cases k with
  | zero => {
      exact Nat.mod_lt n hD
    }
  | succ k => {
      exact Nat.mod_lt _ hD
    }

/-- Unit multipliers permit cancellation through every residue event. -/
theorem ResidueCancel (q c D k n n' : ℕ) (hD : 0 < D) (hcop : D.Coprime q) :
    Residue q c D k n = Residue q c D k n' ↔ n % D = n' % D := by
  induction k with
  | zero => {
      rfl
    }
  | succ k ih => {
      change AccessStep q c D (Residue q c D k n) =
        AccessStep q c D (Residue q c D k n') ↔ _
      rw [AccessStepEqIff q c D _ _ hD hcop,
        Nat.mod_eq_of_lt (ResidueLt q c D k n hD),
        Nat.mod_eq_of_lt (ResidueLt q c D k n' hD)]
      exact ih
    }

/-- The bounded search succeeds exactly when one of its affine states divides. -/
theorem HitSuccess (q c D fuel n : ℕ) :
    (Hit q c D fuel n).isSome = true ↔ ∃ k, k < fuel ∧ D ∣ Affine q c k n := by
  induction fuel generalizing n with
  | zero => {
      simp [Hit]
    }
  | succ fuel ih => {
      by_cases hn : D ∣ n
      · simp only [Hit, if_pos hn, Option.isSome_some]
        exact ⟨fun _ => ⟨0, by omega, hn⟩, fun _ => trivial⟩
      · have hmap : ((Hit q c D fuel (q * n + c)).map
            (fun z => (z.1 + 1, z.2))).isSome =
            (Hit q c D fuel (q * n + c)).isSome := by
          cases Hit q c D fuel (q * n + c) <;> rfl
        simp only [Hit, if_neg hn, hmap, ih]
        constructor
        · rintro ⟨k, hk, hd⟩
          refine ⟨k + 1, by omega, ?_⟩
          have he := IterateFirst (fun x => q * x + c) k n
          simpa only [Affine] using he ▸ hd
        · rintro ⟨k, hk, hd⟩
          cases k with
          | zero => {
              exact (hn hd).elim
            }
          | succ k => {
              refine ⟨k, by omega, ?_⟩
              have he := IterateFirst (fun x => q * x + c) k n
              simpa only [Affine] using he.symm ▸ hd
            }
    }

/-- A complete orbit of zero lists each residue that can eventually divide. -/
def Accessible (q c D m : ℕ) : Finset ℕ :=
  (Finset.range m).image (AccessOrbit q c D)

/-- Accessible residues have exactly `m` distinct representatives. -/
theorem AccessibleCard (q c D m : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hm : AccessLeast q c D m) : (Accessible q c D m).card = m := by
  have hi : Set.InjOn (AccessOrbit q c D) (↑(Finset.range m) : Set ℕ) := by
    intro i hi j hj he
    exact AccessOrbitDistinct q c D m i j hq hD hm
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) he
  rw [Accessible, Finset.card_image_of_injOn hi, Finset.card_range]

/-- The accessible set contains only genuine residue representatives. -/
theorem AccessibleLt (q c D m r : ℕ) (hD : 0 < D)
    (hr : r ∈ Accessible q c D m) : r < D := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
  rw [AccessOrbitEqOffsetMulRepunit]
  exact Nat.mod_lt _ hD

/-- Starting on the orbit of zero keeps the original chronological residue clock. -/
theorem ResidueOrbit (q c D i k : ℕ) (hD : 0 < D) :
    Residue q c D k (AccessOrbit q c D i) = AccessOrbit q c D (i + k) := by
  have hi : AccessOrbit q c D i < D := by
    rw [AccessOrbitEqOffsetMulRepunit]
    exact Nat.mod_lt _ hD
  rw [Residue, Nat.mod_eq_of_lt hi, AccessOrbitAdd]

/-- Eventual access to zero is precisely membership in its finite cycle. -/
theorem HitAccessible (q c D m n : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    (Hit q c D m n).isSome = true ↔ n % D ∈ Accessible q c D m := by
  rw [HitSuccess]
  have hm0 := AccessOrbitEqZeroOfLeast q c D m hq hD hm
  constructor
  · rintro ⟨k, hk, hd⟩
    have hz : Residue q c D k n = 0 := by
      rw [← AffineResidue, Nat.mod_eq_zero_of_dvd hd]
    by_cases hk0 : k = 0
    · subst k
      refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hm.1, ?_⟩
      exact (AccessOrbitZero q c D).trans hz.symm
    · have hi : m - k < m := by omega
      have hj : (m - k) + k = m := by omega
      have hs : Residue q c D k (AccessOrbit q c D (m - k)) = 0 := by
        rw [ResidueOrbit q c D (m - k) k hD, hj, hm0]
      have he := (ResidueCancel q c D k n (AccessOrbit q c D (m - k))
        hD hcop).mp (hz.trans hs.symm)
      have hl : AccessOrbit q c D (m - k) < D := by
        rw [AccessOrbitEqOffsetMulRepunit]
        exact Nat.mod_lt _ hD
      rw [Nat.mod_eq_of_lt hl] at he
      exact Finset.mem_image.mpr ⟨m - k, Finset.mem_range.mpr hi, he.symm⟩
  · intro hn
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hn
    have him : i < m := Finset.mem_range.mp hi
    have hl : AccessOrbit q c D i < D := by
      rw [AccessOrbitEqOffsetMulRepunit]
      exact Nat.mod_lt _ hD
    have hs : ∀ k, Residue q c D k n = Residue q c D k (AccessOrbit q c D i) := by
      intro k
      simp only [Residue, Nat.mod_eq_of_lt hl, ← he]
    by_cases hi0 : i = 0
    · subst i
      refine ⟨0, hm.1, ?_⟩
      have hz := he.symm.trans (AccessOrbitZero q c D)
      exact Nat.dvd_of_mod_eq_zero hz
    · refine ⟨m - i, by omega, ?_⟩
      have hj : i + (m - i) = m := by omega
      have hz : Residue q c D (m - i) n = 0 := by
        rw [hs, ResidueOrbit q c D i (m - i) hD, hj, hm0]
      exact Nat.dvd_of_mod_eq_zero ((AffineResidue q c D (m - i) n).trans hz)

/-- One complete legal division occupies exactly the accessible residue classes. -/
theorem ClassesOne (q c D m : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    Classes q c D m 1 = Accessible q c D m := by
  ext n
  rw [ClassesMember]
  simp only [pow_one]
  have hs : Survives q c D m 1 n ↔ (Hit q c D m n).isSome = true := by
    unfold Survives
    simp only [Run, Option.bind_some, one_mul]
    cases Hit q c D m n <;> rfl
  rw [hs, HitAccessible q c D m n hq hD hcop hm]
  constructor
  · rintro ⟨hn, he⟩
    rwa [Nat.mod_eq_of_lt hn] at he
  · intro hn
    have hl := AccessibleLt q c D m n hD hn
    exact ⟨hl, by simpa only [Nat.mod_eq_of_lt hl] using hn⟩

/-- The depth-one cardinality is exact; the boundary `m = D` remains admissible. -/
theorem ClassesOneCard (q c D m : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    (Classes q c D m 1).card = m := by
  rw [ClassesOne q c D m hq hD hcop hm, AccessibleCard q c D m hq hD hm]

/-- The endpoint digit map permutes all residues when its multiplier is a unit. -/
def Digit (D E P : ℕ) (hD : 0 < D) (t : Fin D) : Fin D :=
  ⟨(E + P * t.val) % D, Nat.mod_lt _ hD⟩

/-- Digit lifting is bijective, not merely a family of separate congruence witnesses. -/
theorem DigitBijective (D E P : ℕ) (hD : 0 < D) (hcop : P.Coprime D) :
    Function.Bijective (Digit D E P hD) := by
  apply (Fintype.bijective_iff_injective_and_card (Digit D E P hD)).mpr
  refine ⟨?_, rfl⟩
  intro t u he
  have hv := congrArg Fin.val he
  have ha : AccessStep P E D t.val = AccessStep P E D u.val := by
    simpa only [Digit, AccessStep, Nat.add_comm] using hv
  have hh := (AccessStepEqIff P E D t.val u.val hD hcop.symm).mp ha
  rw [Nat.mod_eq_of_lt t.isLt, Nat.mod_eq_of_lt u.isLt] at hh
  exact Fin.ext hh

/-- Legal lifts are source digits, not endpoint residues with independent choices. -/
def Digits (q c D m E P : ℕ) : Finset ℕ :=
  (Finset.range D).filter (fun t => (Hit q c D m (E + P * t)).isSome)

/-- Each legal prefix has exactly `m` legal high-digit lifts. -/
theorem DigitsCard (q c D m E P : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hP : P.Coprime D) (hm : AccessLeast q c D m) :
    (Digits q c D m E P).card = m := by
  suffices hc : (Digits q c D m E P).card = (Accessible q c D m).card by
    exact hc.trans (AccessibleCard q c D m hq hD hm)
  apply Finset.card_bij (fun t _ => (E + P * t) % D)
  · intro t ht
    have hh := (Finset.mem_filter.mp ht).2
    exact (HitAccessible q c D m (E + P * t) hq hD hcop hm).mp hh
  · intro t ht u hu he
    have htD := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    have huD := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
    have ha : AccessStep P E D t = AccessStep P E D u := by
      simpa only [AccessStep, Nat.add_comm] using he
    have hh := (AccessStepEqIff P E D t u hD hP.symm).mp ha
    rwa [Nat.mod_eq_of_lt htD, Nat.mod_eq_of_lt huD] at hh
  · intro r hr
    have hrD := AccessibleLt q c D m r hD hr
    obtain ⟨t, ht⟩ := (DigitBijective D E P hD hP).surjective ⟨r, hrD⟩
    have he : (E + P * t.val) % D = r := congrArg Fin.val ht
    refine ⟨t.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr t.isLt, ?_⟩, he⟩
    apply (HitAccessible q c D m (E + P * t.val) hq hD hcop hm).mpr
    rwa [he]

/-- A child's source representative retains its parent's low `h` digits. -/
def Children (q c D m h r : ℕ) : Finset ℕ :=
  match Run q c D m h r with
  | none => ∅
  | some z => (Digits q c D m z.1 z.2).image (fun t => r + D ^ h * t)

/-- Successful depth `h+1` retains the same successful depth-`h` prefix. -/
theorem SurvivesPred (q c D m h n : ℕ)
    (hs : Survives q c D m (h + 1) n) : Survives q c D m h n := by
  cases hz : Run q c D m h n with
  | none => {
      simp [Survives, Run, hz] at hs
    }
  | some z => {
      simp [Survives, hz]
    }

/-- Legal children share their parent's endpoint and their own exact high digit. -/
theorem ChildrenMember (q c D m h r n E P : ℕ)
    (hr : Run q c D m h r = some (E, P)) :
    n ∈ Children q c D m h r ↔
      ∃ t, t < D ∧ (Hit q c D m (E + P * t)).isSome = true ∧ r + D ^ h * t = n := by
  simp only [Children, hr, Digits, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range, and_assoc]

/-- The next guard is tested on the actual endpoint of the shifted legal prefix. -/
theorem SurvivesSuccShift (q c D m h r t E P : ℕ) (hD : 0 < D)
    (hr : Run q c D m h r = some (E, P)) :
    Survives q c D m (h + 1) (r + D ^ h * t) ↔
      (Hit q c D m (E + P * t)).isSome = true := by
  simp only [Survives, Run, RunShift q c D m h r t hD, hr,
    Option.map_some, Option.bind_some, Option.isSome_map]

/-- The unit multiplier gives exactly `m` children of every legal parent. -/
theorem ChildrenCard (q c D m h r : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m)
    (hr : r ∈ Classes q c D m h) : (Children q c D m h r).card = m := by
  have hs := (ClassesMember q c D m h r).mp hr
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hs.2
  have hP := RunCoprime q c D m h r z.1 z.2 hcop.symm hz
  have hL : 0 < D ^ h := pow_pos hD h
  have hi : Set.InjOn (fun t => r + D ^ h * t)
      (↑(Digits q c D m z.1 z.2) : Set ℕ) := by
    intro t _ u _ he
    nlinarith
  simp only [Children, hz]
  rw [Finset.card_image_of_injOn hi]
  exact DigitsCard q c D m z.1 z.2 hq hD hcop hP hm

/-- Distinct parents have disjoint children because low source digits are preserved. -/
theorem ChildrenDisjoint (q c D m h r s : ℕ)
    (hr : r ∈ Classes q c D m h) (hs : s ∈ Classes q c D m h)
    (hne : r ≠ s) : Disjoint (Children q c D m h r) (Children q c D m h s) := by
  have hr' := (ClassesMember q c D m h r).mp hr
  have hs' := (ClassesMember q c D m h s).mp hs
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hr'.2
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs'.2
  apply Finset.disjoint_left.mpr
  intro n hn hn'
  obtain ⟨t, _, _, ht⟩ := (ChildrenMember q c D m h r n z.1 z.2 hz).mp hn
  obtain ⟨u, _, _, hu⟩ := (ChildrenMember q c D m h s n w.1 w.2 hw).mp hn'
  have he := congrArg (fun x => x % D ^ h) (ht.trans hu.symm)
  have hrs : r = s := by
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul,
      Nat.zero_mod, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hr'.1,
      Nat.mod_eq_of_lt hs'.1] using he
  exact hne hrs

/-- Canonical parent and digit extraction exhaust every legal depth-`h+1` source. -/
theorem ClassesSucc (q c D m h : ℕ) (hD : 0 < D) :
    Classes q c D m (h + 1) =
      (Classes q c D m h).biUnion (Children q c D m h) := by
  ext n
  rw [Finset.mem_biUnion]
  have hL : 0 < D ^ h := pow_pos hD h
  constructor
  · intro hn
    have hn' := (ClassesMember q c D m (h + 1) n).mp hn
    let r := n % D ^ h
    let t := n / D ^ h
    have he : r + D ^ h * t = n := Nat.mod_add_div n (D ^ h)
    have hrL : r < D ^ h := Nat.mod_lt n hL
    have htD : t < D := by
      apply Nat.div_lt_of_lt_mul
      simpa only [pow_succ] using hn'.1
    have hrS : Survives q c D m h r :=
      (SurvivesMod q c D m h n hD).mp (SurvivesPred q c D m h n hn'.2)
    have hr := (ClassesMember q c D m h r).mpr ⟨hrL, hrS⟩
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hrS
    have hshift : Survives q c D m (h + 1) (r + D ^ h * t) := by
      rw [he]
      exact hn'.2
    have hhit := (SurvivesSuccShift q c D m h r t z.1 z.2 hD hz).mp hshift
    refine ⟨r, hr, ?_⟩
    exact (ChildrenMember q c D m h r n z.1 z.2 hz).mpr ⟨t, htD, hhit, he⟩
  · rintro ⟨r, hr, hn⟩
    have hr' := (ClassesMember q c D m h r).mp hr
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hr'.2
    obtain ⟨t, htD, hhit, he⟩ := (ChildrenMember q c D m h r n z.1 z.2 hz).mp hn
    have hbound : r + D ^ h * t < D ^ (h + 1) := by
      rw [pow_succ]
      have ht : t + 1 ≤ D := by omega
      have hb := Nat.mul_le_mul_left (D ^ h) ht
      nlinarith [hr'.1]
    have hshift := (SurvivesSuccShift q c D m h r t z.1 z.2 hD hz).mpr hhit
    rw [he] at hbound hshift
    exact (ClassesMember q c D m (h + 1) n).mpr ⟨hbound, hshift⟩

/-- Summing disjoint lift families gives a global decrease, not separate local witnesses. -/
theorem ClassesSuccCard (q c D m h : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    (Classes q c D m (h + 1)).card = (Classes q c D m h).card * m := by
  have hd : (↑(Classes q c D m h) : Set ℕ).PairwiseDisjoint (Children q c D m h) := by
    intro r hr s hs hne
    exact ChildrenDisjoint q c D m h r s hr hs hne
  rw [ClassesSucc q c D m h hD, Finset.card_biUnion hd]
  exact Finset.sum_const_nat (fun r hr => ChildrenCard q c D m h r hq hD hcop hm hr)

/-- Exactly `m^h` legal source classes exist modulo `D^h` at every finite depth. -/
theorem ClassesCard (q c D m h : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    (Classes q c D m h).card = m ^ h := by
  induction h with
  | zero => {
      simp [ClassesZero]
    }
  | succ h ih => {
      rw [ClassesSuccCard q c D m h hq hD hcop hm, ih, pow_succ]
    }

/-- A zero reached at any affine time must belong to zero's accessible cycle. -/
theorem EventualAccessible (q c D m j n : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m)
    (hz : Residue q c D j n = 0) : n % D ∈ Accessible q c D m := by
  have hm0 := AccessOrbitEqZeroOfLeast q c D m hq hD hm
  have hr : j % m < m := Nat.mod_lt j hm.1
  have hj : m * (j / m) + j % m = j := Nat.div_add_mod j m
  by_cases hr0 : j % m = 0
  · have hs : Residue q c D j (AccessOrbit q c D 0) = 0 := by
      rw [ResidueOrbit q c D 0 j hD, zero_add]
      have he : j = 0 + m * (j / m) := by omega
      rw [he, AccessOrbitPeriodMul q c D m 0 (j / m) hq hD hm,
        AccessOrbitZero]
    have he := (ResidueCancel q c D j n (AccessOrbit q c D 0) hD hcop).mp
      (hz.trans hs.symm)
    rw [AccessOrbitZero, Nat.zero_mod] at he
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hm.1,
      (AccessOrbitZero q c D).trans he.symm⟩
  · let i := m - j % m
    have hi : i < m := by dsimp [i]; omega
    have he : i + j = 0 + m * (j / m + 1) := by
      dsimp [i]
      rw [Nat.mul_add, mul_one]
      omega
    have hs : Residue q c D j (AccessOrbit q c D i) = 0 := by
      rw [ResidueOrbit q c D i j hD, he,
        AccessOrbitPeriodMul q c D m 0 (j / m + 1) hq hD hm, AccessOrbitZero]
    have hn := (ResidueCancel q c D j n (AccessOrbit q c D i) hD hcop).mp
      (hz.trans hs.symm)
    have hl : AccessOrbit q c D i < D := by
      rw [AccessOrbitEqOffsetMulRepunit]
      exact Nat.mod_lt _ hD
    rw [Nat.mod_eq_of_lt hl] at hn
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, hn.symm⟩

/-- The finite first-division search is complete for arbitrarily long affine excursions. -/
theorem HitEventual (q c D m n : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    (Hit q c D m n).isSome = true ↔ ∃ j, D ∣ Affine q c j n := by
  constructor
  · intro hh
    obtain ⟨j, _, hd⟩ := (HitSuccess q c D m n).mp hh
    exact ⟨j, hd⟩
  · rintro ⟨j, hd⟩
    have hz : Residue q c D j n = 0 := by
      rw [← AffineResidue, Nat.mod_eq_zero_of_dvd hd]
    exact (HitAccessible q c D m n hq hD hcop hm).mpr
      (EventualAccessible q c D m j n hq hD hcop hm hz)

/-- The positive-divisor raw map keeps exact division and its original branch priority. -/
def Raw (q c D n : ℕ) : ℕ := if D ∣ n then n / D else q * n + c

/-- A returned first delay consumes at most the supplied finite raw-event budget. -/
theorem HitDelayBound (q c D fuel n k y : ℕ)
    (hh : Hit q c D fuel n = some (k, y)) : k < fuel := by
  induction fuel generalizing n k y with
  | zero => {
      simp [Hit] at hh
    }
  | succ fuel ih => {
      by_cases hd : D ∣ n
      · simp only [Hit, if_pos hd, Option.some.injEq, Prod.mk.injEq] at hh
        omega
      · cases hz : Hit q c D fuel (q * n + c) with
        | none => {
            simp [Hit, hd, hz] at hh
          }
        | some z => {
            simp only [Hit, if_neg hd, hz, Option.map_some,
              Option.some.injEq, Prod.mk.injEq] at hh
            have hb := ih (q * n + c) z.1 z.2 hz
            omega
          }
    }

/-- A computed block recovers every raw guard, its first division and its raw clock. -/
theorem HitRawWitness (q c D fuel n k y : ℕ)
    (hh : Hit q c D fuel n = some (k, y)) :
    (∀ i, i < k → ¬D ∣ Iterate (Raw q c D) i n) ∧
      D ∣ Iterate (Raw q c D) k n ∧ Iterate (Raw q c D) (k + 1) n = y := by
  induction fuel generalizing n k y with
  | zero => {
      simp [Hit] at hh
    }
  | succ fuel ih => {
      by_cases hn : D ∣ n
      · simp only [Hit, if_pos hn, Option.some.injEq, Prod.mk.injEq] at hh
        rcases hh with ⟨rfl, rfl⟩
        refine ⟨by intro i hi; omega, hn, ?_⟩
        simp [Iterate, Raw, hn]
      · simp only [Hit, if_neg hn] at hh
        cases hz : Hit q c D fuel (q * n + c) with
        | none => {
            simp [hz] at hh
          }
        | some z => {
            simp only [hz, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hh
            rcases hh with ⟨rfl, rfl⟩
            have hw := ih (q * n + c) z.1 z.2 hz
            refine ⟨?_, ?_, ?_⟩
            · intro i hi
              cases i with
              | zero => {
                  exact hn
                }
              | succ i => {
                  rw [← IterateFirst (Raw q c D) i n, Raw, if_neg hn]
                  exact hw.1 i (by omega)
                }
            · rw [← IterateFirst (Raw q c D) z.1 n, Raw, if_neg hn]
              exact hw.2.1
            · rw [← IterateFirst (Raw q c D) (z.1 + 1) n, Raw, if_neg hn]
              exact hw.2.2
          }
    }

/-- Division events are counted on the raw clock, including an immediate division. -/
def DivisionCount (q c D : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t + 1, n =>
      DivisionCount q c D t n + if D ∣ Iterate (Raw q c D) t n then 1 else 0

/-- Appending raw-clock intervals adds their actual division-event counts. -/
theorem DivisionCountAdd (q c D a b n : ℕ) :
    DivisionCount q c D (a + b) n =
      DivisionCount q c D a n + DivisionCount q c D b (Iterate (Raw q c D) a n) := by
  induction b with
  | zero => {
      simp [DivisionCount]
    }
  | succ b ih => {
      calc
        DivisionCount q c D (a + (b + 1)) n =
            DivisionCount q c D (a + b) n +
              if D ∣ Iterate (Raw q c D) (a + b) n then 1 else 0 := rfl
        _ = (DivisionCount q c D a n +
              DivisionCount q c D b (Iterate (Raw q c D) a n)) +
              if D ∣ Iterate (Raw q c D) b (Iterate (Raw q c D) a n)
                then 1 else 0 := by rw [ih, IterateAdd]
        _ = DivisionCount q c D a n +
              DivisionCount q c D (b + 1) (Iterate (Raw q c D) a n) := by
          simp only [DivisionCount, Nat.add_assoc]
    }

/-- Extending the actual raw clock cannot remove previously counted division events. -/
theorem DivisionCountMono (q c D n a b : ℕ) (hab : a ≤ b) :
    DivisionCount q c D a n ≤ DivisionCount q c D b n := by
  have he := DivisionCountAdd q c D a (b - a) n
  rw [Nat.add_sub_of_le hab] at he
  omega

/-- A guarded division-free prefix contributes zero, not an estimated drift. -/
theorem DivisionCountZero (q c D t n : ℕ)
    (hn : ∀ i, i < t → ¬D ∣ Iterate (Raw q c D) i n) : DivisionCount q c D t n = 0 := by
  induction t with
  | zero => {
      rfl
    }
  | succ t ih => {
      have hp : ∀ i, i < t → ¬D ∣ Iterate (Raw q c D) i n := by
        intro i hi
        exact hn i (by omega)
      rw [DivisionCount, ih hp, if_neg (hn t (by omega)), Nat.add_zero]
    }

/-- Each complete first-division block contains exactly one raw division event. -/
theorem HitRawCount (q c D fuel n k y : ℕ)
    (hh : Hit q c D fuel n = some (k, y)) : DivisionCount q c D (k + 1) n = 1 := by
  have hw := HitRawWitness q c D fuel n k y hh
  rw [DivisionCount, DivisionCountZero q c D k n hw.1, if_pos hw.2.1]

/-- Every computed depth-`h` endpoint is attained after exactly `h` raw divisions. -/
theorem RunRaw (q c D m h n E P : ℕ) (hr : Run q c D m h n = some (E, P)) :
    ∃ t, h ≤ t ∧ DivisionCount q c D t n = h ∧ Iterate (Raw q c D) t n = E := by
  induction h generalizing E P with
  | zero => {
      simp only [Run, Option.some.injEq, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, _⟩
      exact ⟨0, by omega, rfl, rfl⟩
    }
  | succ h ih => {
      simp only [Run] at hr
      cases hz : Run q c D m h n with
      | none => {
          simp [hz] at hr
        }
      | some z => {
          simp only [hz, Option.bind_some] at hr
          cases hw : Hit q c D m z.1 with
          | none => {
              simp [hw] at hr
            }
          | some w => {
              simp only [hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
              rcases hr with ⟨rfl, _⟩
              obtain ⟨t, ht, hc, he⟩ := ih z.1 z.2 hz
              have hb := HitRawWitness q c D m z.1 w.1 w.2 hw
              refine ⟨t + (w.1 + 1), by omega, ?_, ?_⟩
              · rw [DivisionCountAdd, he, hc, HitRawCount q c D m z.1 w.1 w.2 hw]
              · rw [IterateAdd, he]
                exact hb.2.2
            }
        }
    }

/-- A legal prefix has a full raw witness inside the uniform `m*h` search window. -/
theorem RunRawBudget (q c D m h n E P : ℕ) (hr : Run q c D m h n = some (E, P)) :
    ∃ t, h ≤ t ∧ t ≤ m * h ∧ DivisionCount q c D t n = h ∧
      Iterate (Raw q c D) t n = E := by
  induction h generalizing E P with
  | zero => {
      simp only [Run, Option.some.injEq, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, _⟩
      exact ⟨0, by omega, by omega, rfl, rfl⟩
    }
  | succ h ih => {
      simp only [Run] at hr
      cases hz : Run q c D m h n with
      | none => {
          simp [hz] at hr
        }
      | some z => {
          simp only [hz, Option.bind_some] at hr
          cases hw : Hit q c D m z.1 with
          | none => {
              simp [hw] at hr
            }
          | some w => {
              simp only [hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
              rcases hr with ⟨rfl, _⟩
              obtain ⟨t, ht, htMax, hc, he⟩ := ih z.1 z.2 hz
              have hb := HitRawWitness q c D m z.1 w.1 w.2 hw
              have hk := HitDelayBound q c D m z.1 w.1 w.2 hw
              refine ⟨t + (w.1 + 1), by omega, ?_, ?_, ?_⟩
              · rw [Nat.mul_succ]
                omega
              · rw [DivisionCountAdd, he, hc, HitRawCount q c D m z.1 w.1 w.2 hw]
              · rw [IterateAdd, he]
                exact hb.2.2
            }
        }
    }

/-- Composing blocks from the first division or from the last gives the same computation. -/
theorem RunFirst (q c D m h n : ℕ) :
    Run q c D m (h + 1) n =
      (Hit q c D m n).bind fun w =>
        (Run q c D m h w.2).map (fun z => (z.1, q ^ w.1 * z.2)) := by
  induction h with
  | zero => {
      cases hw : Hit q c D m n <;> simp [Run, hw]
    }
  | succ h ih => {
      rw [Run, ih]
      cases hw : Hit q c D m n with
      | none => {
          simp
        }
      | some w => {
          simp only [Option.bind_some]
          cases hz : Run q c D m h w.2 with
          | none => {
              simp [Run, hz]
            }
          | some z => {
              simp only [Run, hz, Option.map_some, Option.bind_some]
              cases hu : Hit q c D m z.1 <;> simp [Nat.mul_assoc]
            }
        }
    }

/-- A failed complete search certifies that the raw orbit never divides again. -/
theorem HitNoneNoDivisions (q c D m n : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m)
    (hh : Hit q c D m n = none) : ∀ j, ¬D ∣ Iterate (Raw q c D) j n := by
  have ha : ∀ j, ¬D ∣ Affine q c j n := by
    intro j hd
    have hs := (HitEventual q c D m n hq hD hcop hm).mpr ⟨j, hd⟩
    simp [hh] at hs
  have he : ∀ j, Iterate (Raw q c D) j n = Affine q c j n := by
    intro j
    induction j with
    | zero => {
        rfl
      }
    | succ j ih => {
        change Raw q c D (Iterate (Raw q c D) j n) = q * Affine q c j n + c
        rw [ih, Raw, if_neg (ha j)]
      }
  intro j
  rw [he j]
  exact ha j

/-- Every finite raw division-event witness is recognized by the bounded block search. -/
theorem RawCountSurvives (q c D m h n t : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m)
    (hc : h ≤ DivisionCount q c D t n) : Survives q c D m h n := by
  induction h generalizing n t with
  | zero => {
      simp [Survives, Run]
    }
  | succ h ih => {
      cases hw : Hit q c D m n with
      | none => {
          have hz := DivisionCountZero q c D t n
            (fun i _ => HitNoneNoDivisions q c D m n hq hD hcop hm hw i)
          omega
        }
      | some w => {
          have hb := HitRawWitness q c D m n w.1 w.2 hw
          have ht : w.1 + 1 ≤ t := by
            by_contra hn
            have hz := DivisionCountZero q c D t n (by
              intro i hi
              exact hb.1 i (by omega))
            omega
          have he : w.1 + 1 + (t - (w.1 + 1)) = t := Nat.add_sub_of_le ht
          have ha := DivisionCountAdd q c D (w.1 + 1) (t - (w.1 + 1)) n
          rw [he, HitRawCount q c D m n w.1 w.2 hw, hb.2.2] at ha
          have hc' : h ≤ DivisionCount q c D (t - (w.1 + 1)) w.2 := by omega
          have hs := ih w.2 (t - (w.1 + 1)) hc'
          unfold Survives at hs ⊢
          rw [RunFirst, hw]
          simp only [Option.bind_some, Option.isSome_map]
          exact hs
        }
    }

/-- The cylinder test is equivalent to having at least `h` actual raw division events. -/
theorem SurvivesRawCount (q c D m h n : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    Survives q c D m h n ↔ ∃ t, h ≤ DivisionCount q c D t n := by
  constructor
  · intro hs
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨t, _, hc, _⟩ := RunRaw q c D m h n z.1 z.2 hz
    exact ⟨t, hc.ge⟩
  · rintro ⟨t, hc⟩
    exact RawCountSurvives q c D m h n t hq hD hcop hm hc

/-- Accepted and rejected cylinders are certified by one complete finite raw-event window. -/
theorem SurvivesRawWindow (q c D m h n : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    Survives q c D m h n ↔ h ≤ DivisionCount q c D (m * h) n := by
  constructor
  · intro hs
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨t, _, ht, hc, _⟩ := RunRawBudget q c D m h n z.1 z.2 hz
    have hb := DivisionCountMono q c D n t (m * h) ht
    omega
  · intro hc
    exact RawCountSurvives q c D m h n (m * h) hq hD hcop hm hc

/-- Infinitely many divisions means that their actual raw-clock count is unbounded. -/
def InfiniteDivisions (q c D n : ℕ) : Prop :=
  ∀ h, ∃ t, h ≤ DivisionCount q c D t n

/-- The infinite raw event condition is exactly survival of all finite cylinders. -/
theorem InfiniteSurvives (q c D m n : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) :
    InfiniteDivisions q c D n ↔ ∀ h, Survives q c D m h n := by
  constructor
  · intro hi h
    exact (SurvivesRawCount q c D m h n hq hD hcop hm).mpr (hi h)
  · intro hi h
    exact (SurvivesRawCount q c D m h n hq hD hcop hm).mp (hi h)

/-- A finite failed depth recovers one common raw time after which division never occurs. -/
theorem RunNoneTail (q c D m h n : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m)
    (hh : Run q c D m h n = none) :
    ∃ t, ∀ j, t ≤ j → ¬D ∣ Iterate (Raw q c D) j n := by
  induction h with
  | zero => {
      simp [Run] at hh
    }
  | succ h ih => {
      cases hz : Run q c D m h n with
      | none => {
          exact ih hz
        }
      | some z => {
          cases hw : Hit q c D m z.1 with
          | none => {
              obtain ⟨t, _, _, he⟩ := RunRaw q c D m h n z.1 z.2 hz
              refine ⟨t, ?_⟩
              intro j hj
              have hj' : t + (j - t) = j := Nat.add_sub_of_le hj
              have htail := HitNoneNoDivisions q c D m z.1 hq hD hcop hm hw (j - t)
              rw [← he, ← IterateAdd, hj'] at htail
              exact htail
            }
          | some w => {
              simp [Run, hz, hw] at hh
            }
        }
    }

/-- Every orbit outside the infinitely-dividing set has a legal division-free raw tail. -/
theorem FiniteDivisionsTail (q c D m n : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m)
    (hi : ¬InfiniteDivisions q c D n) :
    ∃ t, ∀ j, t ≤ j → ¬D ∣ Iterate (Raw q c D) j n := by
  classical
  have hf : ∃ h, Run q c D m h n = none := by
    by_contra hn
    apply hi
    apply (InfiniteSurvives q c D m n hq hD hcop hm).mpr
    intro h
    cases hz : Run q c D m h n with
    | none => {
        exact (hn ⟨h, hz⟩).elim
      }
    | some z => {
        simp [Survives, hz]
      }
  obtain ⟨h, hh⟩ := hf
  exact RunNoneTail q c D m h n hq hD hcop hm hh

/-- A division-free raw tail is the same affine orbit on every later raw clock. -/
theorem DivisionFreeAffine (q c D n t : ℕ)
    (ht : ∀ j, t ≤ j → ¬D ∣ Iterate (Raw q c D) j n) (j : ℕ) :
    Iterate (Raw q c D) (t + j) n = Affine q c j (Iterate (Raw q c D) t n) := by
  induction j with
  | zero => {
      simp [Affine, Iterate]
    }
  | succ j ih => {
      change Raw q c D (Iterate (Raw q c D) (t + j) n) =
        q * Affine q c j (Iterate (Raw q c D) t n) + c
      rw [Raw, if_neg (ht (t + j) (by omega)), ih]
    }

/-- The recovered affine tail has the exact geometric-sum offset. -/
theorem AffineFormula (q c j n : ℕ) :
    Affine q c j n = q ^ j * n + c * RepunitSum q j := by
  induction j with
  | zero => {
      simp [Affine, Iterate, RepunitSum]
    }
  | succ j ih => {
      change q * Affine q c j n + c = _
      rw [ih, pow_succ, ← RepunitSumSuccMul]
      ring
    }

/-- Positive offset gives a uniform increasing tail without any probabilistic drift claim. -/
theorem AffineGrowth (q c j n : ℕ) (hq : 1 ≤ q) (hc : 1 ≤ c) :
    n + j ≤ Affine q c j n := by
  induction j with
  | zero => {
      simp [Affine, Iterate]
    }
  | succ j ih => {
      change n + (j + 1) ≤ q * Affine q c j n + c
      have hh : Affine q c j n ≤ q * Affine q c j n :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    }

/-- The same raw orbit eventually exceeds every threshold once division stops. -/
theorem DivisionFreeEscape (q c D n t : ℕ) (hq : 1 ≤ q) (hc : 1 ≤ c)
    (ht : ∀ j, t ≤ j → ¬D ∣ Iterate (Raw q c D) j n) :
    ∀ B, ∃ K, ∀ j, K ≤ j → B < Iterate (Raw q c D) j n := by
  intro B
  refine ⟨t + B + 1, ?_⟩
  intro j hj
  have hjt : t ≤ j := by omega
  have he : t + (j - t) = j := Nat.add_sub_of_le hjt
  have hg := AffineGrowth q c (j - t) (Iterate (Raw q c D) t n) hq hc
  rw [← DivisionFreeAffine q c D n t ht (j - t), he] at hg
  omega

/-- A finite raw-event orbit has one affine tail with an exact geometric-sum offset. -/
theorem FiniteDivisionsFormula (q c D m n : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m)
    (hi : ¬InfiniteDivisions q c D n) :
    ∃ t, (∀ j, t ≤ j → ¬D ∣ Iterate (Raw q c D) j n) ∧
      ∀ j, Iterate (Raw q c D) (t + j) n =
        q ^ j * Iterate (Raw q c D) t n + c * RepunitSum q j := by
  obtain ⟨t, ht⟩ := FiniteDivisionsTail q c D m n hq hD hcop hm hi
  refine ⟨t, ht, ?_⟩
  intro j
  rw [DivisionFreeAffine q c D n t ht j, AffineFormula]

/-- Positive scalar data embed in the library's signed parameter class without a new map. -/
def PositiveParameters (q c D : ℕ) (hD : 2 ≤ D) : Parameters where
  Q := q
  C := c
  D := D
  DAdmissible := by simpa using hD

/-- The natural raw branch is the signed library branch on nonnegative inputs. -/
theorem RawCast (q c D n : ℕ) (hD : 2 ≤ D) :
    (Raw q c D n : ℤ) = RawStep (PositiveParameters q c D hD) (n : ℤ) := by
  have hi : (D : ℤ) ∣ (n : ℤ) ↔ D ∣ n := Int.natCast_dvd_natCast
  by_cases hd : D ∣ n
  · simp [Raw, RawStep, PositiveParameters, hi, hd, Int.natCast_ediv]
  · simp [Raw, RawStep, PositiveParameters, hi, hd]

/-- Casting preserves every raw clock, not only the selected compressed endpoints. -/
theorem IterateCast (q c D n t : ℕ) (hD : 2 ≤ D) :
    ((Iterate (Raw q c D) t n : ℕ) : ℤ) =
      Iterate (RawStep (PositiveParameters q c D hD)) t (n : ℤ) := by
  induction t with
  | zero => {
      rfl
    }
  | succ t ih => {
      change (Raw q c D (Iterate (Raw q c D) t n) : ℤ) =
        RawStep (PositiveParameters q c D hD)
          (Iterate (RawStep (PositiveParameters q c D hD)) t (n : ℤ))
      rw [RawCast, ih]
    }

/-- The positive source domain is preserved under both division-first branches. -/
theorem RawPositive (q c D n : ℕ) (hq : 2 ≤ q) (hD : 0 < D) (hn : 0 < n) :
    0 < Raw q c D n := by
  unfold Raw
  split_ifs with hd
  · exact Nat.div_pos (Nat.le_of_dvd hn hd) hD
  · nlinarith

/-- Every recovered endpoint remains in the source's positive seed class. -/
theorem IteratePositive (q c D n t : ℕ) (hq : 2 ≤ q) (hD : 0 < D) (hn : 0 < n) :
    0 < Iterate (Raw q c D) t n := by
  induction t with
  | zero => {
      exact hn
    }
  | succ t ih => {
      exact RawPositive q c D (Iterate (Raw q c D) t n) hq hD ih
    }

/-- Every unit residue map has a least positive zero return, within `D` steps. -/
theorem AccessExists (q c D : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) : ∃ m, AccessLeast q c D m ∧ m ≤ D := by
  classical
  let p : Equiv.Perm (Fin D) :=
    Equiv.ofBijective (Digit D c q hD) (DigitBijective D c q hD hcop.symm)
  have he : ∀ k, ((p ^ k) ⟨0, hD⟩).val = AccessOrbit q c D k := by
    intro k
    induction k with
    | zero => {
        simp [AccessOrbit, Iterate]
      }
    | succ k ih => {
        rw [pow_succ', Equiv.Perm.mul_apply]
        change (c + q * ((p ^ k) ⟨0, hD⟩).val) % D = AccessOrbit q c D (k + 1)
        rw [ih, AccessOrbitSucc]
        simp only [AccessStep, Nat.add_comm]
      }
  have hz : AccessOrbit q c D (orderOf p) = 0 := by
    rw [← he (orderOf p), pow_orderOf_eq_one]
    rfl
  have hx : ∃ k, 0 < k ∧ AccessOrbit q c D k = 0 := ⟨orderOf p, orderOf_pos p, hz⟩
  let m := Nat.find hx
  have hmpos : 0 < m := (Nat.find_spec hx).1
  have hmzero : AccessOrbit q c D m = 0 := (Nat.find_spec hx).2
  have hm : AccessLeast q c D m := by
    refine ⟨hmpos, (AccessOrbitEqZeroIffModulus q c D m hq hD).mp hmzero, ?_⟩
    intro s hpos hs hdiv
    have hs0 := (AccessOrbitEqZeroIffModulus q c D s hq hD).mpr hdiv
    exact (Nat.find_min hx hs) ⟨hpos, hs0⟩
  exact ⟨m, hm, AccessOrbitCardLe q c D m hq hD hm⟩

/-- At full access the complete finite cylinder is the whole residue range. -/
theorem FullAccessClasses (q c D m h : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) (hfull : m = D) :
    Classes q c D m h = Finset.range (D ^ h) := by
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.filter_subset _ _
  · rw [Finset.card_range, ClassesCard q c D m h hq hD hcop hm, hfull]

/-- Full access forces infinitely many actual raw divisions for every seed. -/
theorem FullAccessInfinite (q c D m n : ℕ) (hq : 2 ≤ q) (hD : 0 < D)
    (hcop : D.Coprime q) (hm : AccessLeast q c D m) (hfull : m = D) :
    InfiniteDivisions q c D n := by
  apply (InfiniteSurvives q c D m n hq hD hcop hm).mpr
  intro h
  apply (SurvivesMod q c D m h n hD).mpr
  have hr : n % D ^ h ∈ Classes q c D m h := by
    rw [FullAccessClasses q c D m h hq hD hcop hm hfull]
    exact Finset.mem_range.mpr (Nat.mod_lt n (pow_pos hD h))
  exact ((ClassesMember q c D m h (n % D ^ h)).mp hr).2

/-- The ternary control has a genuine strict shortfall and a least period of two. -/
theorem TernaryPeriod : AccessLeast 2 1 3 2 := by
  refine ⟨by decide, by decide, ?_⟩
  intro s hpos hs
  have he : s = 1 := by omega
  subst s
  decide

/-- The ordinary classical parameters are the critical full-access control. -/
theorem ClassicalPeriod : AccessLeast 3 1 2 2 := by
  refine ⟨by decide, by decide, ?_⟩
  intro s hpos hs
  have he : s = 1 := by omega
  subst s
  decide

/-- The positive ternary raw cycle recovers every prefix and its actual multiplier. -/
theorem TernaryCycleRun (h : ℕ) : Run 2 1 3 2 h 1 = some (1, 2 ^ h) := by
  induction h with
  | zero => {
      simp [Run]
    }
  | succ h ih => {
      simp [Run, ih, Hit, pow_succ]
    }

/-- A density-zero exceptional set can still contain a nonzero raw cycle. -/
theorem TernaryCycleInfinite : InfiniteDivisions 2 1 3 1 := by
  apply (InfiniteSurvives 2 1 3 2 1 (by decide) (by decide) (by decide) TernaryPeriod).mpr
  intro h
  simp [Survives, TernaryCycleRun]

/-- The source's stronger claim that the return order divides `D` is false. -/
theorem PeriodNeedNotDivideModulus :
    ∃ q c D m : ℕ, 2 ≤ q ∧ 1 ≤ c ∧ 2 ≤ D ∧ D.Coprime q ∧
      AccessLeast q c D m ∧ ¬m ∣ D := by
  exact ⟨2, 1, 3, 2, by decide, by decide, by decide, by decide, TernaryPeriod, by decide⟩

end GeneralizedCollatz.ResidueLeakage
