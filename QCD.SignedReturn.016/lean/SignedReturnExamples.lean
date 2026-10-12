-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Algebra.Ring.Int.Defs

/-!
# One parameter triple, with a trapped residue

For multiplier `2`, offset `1` and divisor `3`, every integer falls into one
of three residue classes. Class `0` divides at time zero. Class `1` divides
at time one, with numerator `2n+1`. Class `2` is fixed by the residue step, so
it never divides. Its raw orbit is `2 ^ j * (n + 1) - 1`. That orbit
is the fixed point `-1` when `n = -1`, and it is unbounded otherwise.
Every remaining seed reaches `0`, `1`, or `-1`, or else becomes
unbounded after a later return lands in class `2`. The only periodic
points are `0`, `-1`, `1`, and `3`. An orbit is eventually periodic
exactly when it meets one of `0`, `1`, and `-1`. The absolute values
are unbounded exactly when some term is congruent to `2` and different
from `-1`. These four outcomes are mutually exclusive. The two hitting
classes obey
`3 * |return| ≤ 2 * |seed| + 1`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Affine state after `j` undivided steps, with offset sum `TrapSum q j`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- `j` is the first time `p.D` divides the affine state of the seed `n`. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n

/-- At time zero the power is one and the offset sum is empty. -/
theorem AffineStateZero (q c n : ℤ) : AffineState q c 0 n = n := by
  unfold AffineState
  rw [pow_zero]
  have hsum : TrapSum q 0 = 0 := rfl
  rw [hsum, Int.one_mul, Int.mul_zero, Int.add_zero]

/-- One further undivided step multiplies the previous state and adds `c`. -/
theorem AffineStateSucc (q c : ℤ) (j : ℕ) (n : ℤ) :
    AffineState q c (j + 1) n = q * AffineState q c j n + c := by
  unfold AffineState
  rw [pow_succ, TrapSumRec]
  ring

/-- With multiplier two and offset one, time one is the numerator `2n+1`. -/
theorem AffineStateOne (n : ℤ) : AffineState 2 1 1 n = 2 * n + 1 := by
  rw [AffineStateSucc, AffineStateZero]

/-- The remainder of an integer modulo `3` is `0`, `1`, or `2`. -/
theorem EmodThreeCases (n : ℤ) :
    n % (3 : ℤ) = 0 ∨ n % (3 : ℤ) = 1 ∨ n % (3 : ℤ) = 2 := by
  have hnz : (3 : ℤ) ≠ 0 := by omega
  have hpos : (0 : ℤ) < 3 := by omega
  have hlow : 0 ≤ n % (3 : ℤ) := Int.emod_nonneg n hnz
  have hhigh : n % (3 : ℤ) < 3 := Int.emod_lt_of_pos n hpos
  have hle : n % (3 : ℤ) ≤ 2 := by omega
  by_cases h0 : n % (3 : ℤ) = 0
  · {
      exact Or.inl h0
    }
  · {
      by_cases h1 : n % (3 : ℤ) = 1
      · {
          exact Or.inr (Or.inl h1)
        }
      · {
          have h2 : n % (3 : ℤ) = 2 := by omega
          exact Or.inr (Or.inr h2)
        }
    }

/-- After cancelling the factor three, time zero contributes `|n|`. -/
theorem HitBoundZeroNumerator (n : ℤ) : n.natAbs ≤ 2 * n.natAbs + 1 := by
  have hle : n.natAbs ≤ n.natAbs + (n.natAbs + 1) :=
    Nat.le_add_right n.natAbs (n.natAbs + 1)
  have heq : n.natAbs + (n.natAbs + 1) = 2 * n.natAbs + 1 := by
    rw [← Nat.add_assoc, ← Nat.two_mul]
  exact heq ▸ hle

/-- Casting `2k+1` from `ℕ` to `ℤ` is the same integer expression. -/
theorem CastDoubleSucc (k : ℕ) :
    ((2 * k + 1 : ℕ) : ℤ) = 2 * (k : ℤ) + 1 := by
  have hsum : ((2 * k + 1 : ℕ) : ℤ) =
      ((2 * k : ℕ) : ℤ) + ((1 : ℕ) : ℤ) := by
    rw [Nat.cast_add]
  have hmul : ((2 * k : ℕ) : ℤ) =
      ((2 : ℕ) : ℤ) * ((k : ℕ) : ℤ) := by
    rw [Nat.cast_mul]
  rw [hsum, hmul, Nat.cast_one]
  rfl

/-- After cancelling the factor three, time one contributes `|2n+1|`. -/
theorem HitBoundOneNumerator (n : ℤ) :
    (2 * n + 1).natAbs ≤ 2 * n.natAbs + 1 := by
  by_cases hn : 0 ≤ n
  · {
      have hpos : 0 ≤ 2 * n + 1 := by omega
      have hleft : ((2 * n + 1).natAbs : ℤ) = 2 * n + 1 :=
        Int.natAbs_of_nonneg hpos
      have hseed : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hn
      have hle : ((2 * n + 1).natAbs : ℤ) ≤
          ((2 * n.natAbs + 1 : ℕ) : ℤ) := by
        rw [hleft, CastDoubleSucc n.natAbs, hseed]
      exact Int.ofNat_le.mp hle
    }
  · {
      have hneg : n < 0 := not_le.mp hn
      have hlt : 2 * n + 1 < 0 := by omega
      have hleft : ((2 * n + 1).natAbs : ℤ) = -(2 * n + 1) :=
        Int.ofNat_natAbs_of_nonpos (le_of_lt hlt)
      have hseed : (n.natAbs : ℤ) = -n :=
        Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)
      have hle : ((2 * n + 1).natAbs : ℤ) ≤
          ((2 * n.natAbs + 1 : ℕ) : ℤ) := by
        rw [hleft, CastDoubleSucc n.natAbs, hseed]
        omega
      exact Int.ofNat_le.mp hle
    }

/-- A prefix with no earlier affine hit equals the affine state. -/
theorem PrefixEqualsAffine (p : Parameters) (n : ℤ) (j : ℕ)
    (h : ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n) :
    Iterate (RawStep p) j n = AffineState p.Q p.C j n := by
  revert h
  induction j with
  | zero => {
      intro _h
      have hiter : Iterate (RawStep p) 0 n = n := rfl
      rw [hiter]
      exact (AffineStateZero p.Q p.C n).symm
    }
  | succ j ih => {
      intro h
      have hlt : ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self j))
      have ihj : Iterate (RawStep p) j n = AffineState p.Q p.C j n := ih hlt
      have hmiss : ¬ p.D ∣ AffineState p.Q p.C j n :=
        h j (Nat.lt_succ_self j)
      have hraw : ¬ p.D ∣ Iterate (RawStep p) j n := by
        rw [ihj]
        exact hmiss
      have hstep : Iterate (RawStep p) (j + 1) n =
          RawStep p (Iterate (RawStep p) j n) := rfl
      rw [hstep, RawStepAffine p (Iterate (RawStep p) j n) hraw, ihj]
      exact (AffineStateSucc p.Q p.C j n).symm
    }

/-- A seed has at most one first-hit time. -/
theorem FirstHitUnique (p : Parameters) (n : ℤ) (j k : ℕ)
    (hj : IsFirstHit p n j) (hk : IsFirstHit p n k) : j = k := by
  rcases Nat.le_total j k with hle | hle
  · {
      by_cases heq : j = k
      · {
          exact heq
        }
      · {
          have hlt : j < k := lt_of_le_of_ne hle heq
          exact False.elim (hk.2 j hlt hj.1)
        }
    }
  · {
      by_cases heq : j = k
      · {
          exact heq
        }
      · {
          have hlt : k < j := lt_of_le_of_ne hle (Ne.symm heq)
          exact False.elim (hj.2 k hlt hk.1)
        }
    }

/-- Remainder `1` makes `3` divide the time-one numerator `2n+1`. -/
theorem TwoMulSuccDiv (n : ℤ) (hmod : n % (3 : ℤ) = 1) :
    (3 : ℤ) ∣ 2 * n + 1 := by
  have hsplit : (3 : ℤ) * (n / 3) + n % (3 : ℤ) = n :=
    Int.mul_ediv_add_emod n (3 : ℤ)
  have hn : n = (3 : ℤ) * (n / 3) + 1 := by
    calc
      n = (3 : ℤ) * (n / 3) + n % (3 : ℤ) := hsplit.symm
      _ = (3 : ℤ) * (n / 3) + 1 := by rw [hmod]
  have hid : 2 * n + 1 = (3 : ℤ) * (2 * (n / 3) + 1) := by
    conv_lhs => rw [hn]
    ring
  exact ⟨2 * (n / 3) + 1, hid⟩

/-- Division by the positive integer three cancels a factor of three. -/
theorem QuotientCancelThree (k : ℤ) : ((3 : ℤ) * k) / 3 = k := by
  have hne : (3 : ℤ) ≠ 0 := by omega
  exact Int.mul_ediv_cancel_left k hne

/-- Exact division by three restores the absolute value of the numerator. -/
theorem CancelNatAbsThree (a : ℤ) (h : (3 : ℤ) ∣ a) :
    3 * (a / 3).natAbs = a.natAbs := by
  have hquot : (a / 3).natAbs = a.natAbs / (3 : ℤ).natAbs :=
    Int.natAbs_ediv_of_dvd h
  have hthree : (3 : ℤ).natAbs = 3 := Int.natAbs_natCast 3
  rw [hthree] at hquot
  have hdiv : (3 : ℤ).natAbs ∣ a.natAbs := Int.natAbs_dvd_natAbs.mpr h
  rw [hthree] at hdiv
  have hcancel : 3 * (a.natAbs / 3) = a.natAbs := Nat.mul_div_cancel' hdiv
  rw [hquot, hcancel]

/-- Remainder `0` is a first hit at time zero, with return `n/3`. -/
theorem HitAtZero (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (hmod : n % (3 : ℤ) = 0) :
    IsFirstHit p n 0 ∧
      AffineState p.Q p.C 0 n = n ∧
      RawStep p (Iterate (RawStep p) 0 n) = n / 3 := by
  have hdvd3 : (3 : ℤ) ∣ n := (Int.dvd_iff_emod_eq_zero).mpr hmod
  have hdvd : p.D ∣ n := by
    rw [hD]
    exact hdvd3
  have hstate : AffineState p.Q p.C 0 n = n := by
    rw [hQ, hC]
    exact AffineStateZero 2 1 n
  have hearly :
      ∀ i : ℕ, i < 0 → ¬ p.D ∣ AffineState p.Q p.C i n := by
    intro i hi
    exact False.elim (Nat.not_lt_zero i hi)
  have hhit : IsFirstHit p n 0 := by
    refine ⟨?_, hearly⟩
    rw [hstate]
    exact hdvd
  have hret : RawStep p (Iterate (RawStep p) 0 n) = n / 3 := by
    have hiter : Iterate (RawStep p) 0 n = n := rfl
    rw [hiter, RawStep, if_pos hdvd, hD]
  exact ⟨hhit, hstate, hret⟩

/-- Remainder `1` is a first hit at time one, with return `(2n+1)/3`. -/
theorem HitAtOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (hmod : n % (3 : ℤ) = 1) :
    IsFirstHit p n 1 ∧
      AffineState p.Q p.C 1 n = 2 * n + 1 ∧
      RawStep p (Iterate (RawStep p) 1 n) = (2 * n + 1) / 3 := by
  have hnd : ¬ p.D ∣ n := by
    rw [hD]
    intro hdvd
    have hzero : n % (3 : ℤ) = 0 := (Int.dvd_iff_emod_eq_zero).mp hdvd
    omega
  have haff : AffineState p.Q p.C 1 n = 2 * n + 1 := by
    rw [hQ, hC]
    exact AffineStateOne n
  have hdvd3 : (3 : ℤ) ∣ 2 * n + 1 := TwoMulSuccDiv n hmod
  have hdvdA : p.D ∣ AffineState p.Q p.C 1 n := by
    rw [haff, hD]
    exact hdvd3
  have hearly :
      ∀ i : ℕ, i < 1 → ¬ p.D ∣ AffineState p.Q p.C i n := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [AffineStateZero]
    exact hnd
  have hhit : IsFirstHit p n 1 := ⟨hdvdA, hearly⟩
  have hret : RawStep p (Iterate (RawStep p) 1 n) = (2 * n + 1) / 3 := by
    have hstate : Iterate (RawStep p) 1 n = AffineState p.Q p.C 1 n :=
      PrefixEqualsAffine p n 1 hearly
    have hdvdI : p.D ∣ Iterate (RawStep p) 1 n := by
      rw [hstate]
      exact hdvdA
    rw [RawStep, if_pos hdvdI, hstate, haff, hD]
  exact ⟨hhit, haff, hret⟩

/-- The absolute value of the divisor `3` is `3`. -/
theorem ModulusThree (p : Parameters) (hD : p.D = 3) : p.D.natAbs = 3 := by
  rw [hD]
  exact Int.natAbs_natCast 3

/-- In `ℤ/3ℤ`, the class `2` satisfies `2 * 2 + 1 = 2`. -/
theorem ZModThreeFixesTwo :
    ((2 : ℤ) : ZMod 3) * (2 : ZMod 3) + ((1 : ℤ) : ZMod 3) =
      (2 : ZMod 3) := by
  have harg : (2 : ZMod 3) = ((2 : ℤ) : ZMod 3) := Int.cast_two.symm
  have hsum :
      ((2 : ℤ) : ZMod 3) * ((2 : ℤ) : ZMod 3) + ((1 : ℤ) : ZMod 3) =
        (((2 : ℤ) * 2 + 1 : ℤ) : ZMod 3) := by
    rw [← Int.cast_mul, ← Int.cast_add]
  have hfive : (2 : ℤ) * 2 + 1 = 5 := by omega
  have hleft :
      ((2 : ℤ) : ZMod 3) * (2 : ZMod 3) + ((1 : ℤ) : ZMod 3) =
        ((5 : ℤ) : ZMod 3) := by
    rw [harg, hsum, hfive]
  rw [hleft, harg, ← sub_eq_zero, ← Int.cast_sub]
  have hsub : (5 : ℤ) - 2 = 3 := by omega
  rw [hsub, Int.cast_ofNat]
  exact ZMod.natCast_self 3

/-- The class `2` is not the zero class of `ℤ/3ℤ`. -/
theorem ZModThreeTwoNeZero : (2 : ZMod 3) ≠ 0 := by
  intro h
  have hcast : ((2 : ℤ) : ZMod 3) = 0 := by
    rw [Int.cast_two]
    exact h
  have hdvd : (3 : ℤ) ∣ 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) 3).mp hcast
  have hmod : (2 : ℤ) % (3 : ℤ) = 0 := (Int.dvd_iff_emod_eq_zero).mp hdvd
  have htwo : (2 : ℤ) % (3 : ℤ) = 2 :=
    Int.emod_eq_of_lt (by omega) (by omega)
  omega

/-- The residue step of these parameters fixes the class `2`. -/
theorem ResidueStepFixesTwo (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    ResidueStepZ p (2 : ZMod p.D.natAbs) = (2 : ZMod p.D.natAbs) := by
  have hm : p.D.natAbs = 3 := ModulusThree p hD
  unfold ResidueStepZ
  rw [hQ, hC, hm]
  exact ZModThreeFixesTwo

/-- Every iterate of the residue step remains at the class `2`. -/
theorem ResidueTwoConstant (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (j : ℕ) :
    Iterate (ResidueStepZ p) j (2 : ZMod p.D.natAbs) =
      (2 : ZMod p.D.natAbs) := by
  induction j with
  | zero => {
      rfl
    }
  | succ j ih => {
      have hstep :
          Iterate (ResidueStepZ p) (j + 1) (2 : ZMod p.D.natAbs) =
            ResidueStepZ p
              (Iterate (ResidueStepZ p) j (2 : ZMod p.D.natAbs)) := rfl
      rw [hstep, ih]
      exact ResidueStepFixesTwo p hQ hC hD
    }

/-- Remainder `2` is the class `2` in `ℤ/3ℤ`. -/
theorem CastOfRemainderTwo (n : ℤ) (hmod : n % (3 : ℤ) = 2) :
    ((n : ℤ) : ZMod 3) = ((2 : ℤ) : ZMod 3) := by
  have hsplit : (3 : ℤ) * (n / 3) + n % (3 : ℤ) = n :=
    Int.mul_ediv_add_emod n (3 : ℤ)
  have hn : n = (3 : ℤ) * (n / 3) + 2 := by
    calc
      n = (3 : ℤ) * (n / 3) + n % (3 : ℤ) := hsplit.symm
      _ = (3 : ℤ) * (n / 3) + 2 := by rw [hmod]
  have hdiff : n - 2 = (3 : ℤ) * (n / 3) := by
    conv_lhs => rw [hn]
    ring
  have hcast : ((n : ℤ) : ZMod 3) - ((2 : ℤ) : ZMod 3) =
      (((3 : ℤ) * (n / 3) : ℤ) : ZMod 3) := by
    rw [← Int.cast_sub, hdiff]
  have hzero : (((3 : ℤ) * (n / 3) : ℤ) : ZMod 3) = 0 := by
    rw [Int.cast_mul]
    have h3 : ((3 : ℤ) : ZMod 3) = 0 := by
      decide
    rw [h3, zero_mul]
  rw [hzero] at hcast
  exact sub_eq_zero.mp hcast

/-- The same class computation, written in the modulus `|D|`. -/
theorem CastRemainderTwo (p : Parameters) (hD : p.D = 3) (n : ℤ)
    (hmod : n % (3 : ℤ) = 2) :
    ((n : ℤ) : ZMod p.D.natAbs) = (2 : ZMod p.D.natAbs) := by
  have hm : p.D.natAbs = 3 := ModulusThree p hD
  rw [hm, ← Int.cast_two]
  exact CastOfRemainderTwo n hmod

/-- A division-free raw orbit has no first hit at any time. -/
theorem NeverDividesNoHit (p : Parameters) (n : ℤ) (h : NeverDivides p n)
    (j : ℕ) : ¬ IsFirstHit p n j := by
  intro hhit
  have hstate : Iterate (RawStep p) j n = AffineState p.Q p.C j n :=
    PrefixEqualsAffine p n j hhit.2
  have hdvd : p.D ∣ Iterate (RawStep p) j n := by
    rw [hstate]
    exact hhit.1
  exact h j hdvd

/-- Remainder `2` never meets the divisor, because its residue stays `2`. -/
theorem RemainderTwoNeverDivides (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (hmod : n % (3 : ℤ) = 2) : NeverDivides p n := by
  rw [ResidueAvoidsZeroIffNeverDivides]
  intro j hzero
  have hcast : ((n : ℤ) : ZMod p.D.natAbs) = (2 : ZMod p.D.natAbs) :=
    CastRemainderTwo p hD n hmod
  have hiter := ResidueTwoConstant p hQ hC hD j
  have hconst :
      Iterate (ResidueStepZ p) j ((n : ℤ) : ZMod p.D.natAbs) =
        (2 : ZMod p.D.natAbs) := by
    rw [hcast]
    exact hiter
  rw [hconst] at hzero
  have hm : p.D.natAbs = 3 := ModulusThree p hD
  rw [hm] at hzero
  exact ZModThreeTwoNeZero hzero

/-- Remainder `2` is excluded from every first-hit statement. -/
theorem RemainderTwoNoHit (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (hmod : n % (3 : ℤ) = 2) (j : ℕ) : ¬ IsFirstHit p n j :=
  NeverDividesNoHit p n (RemainderTwoNeverDivides p hQ hC hD n hmod) j

/-- The three residues determine the hit, or the absence of a hit. -/
theorem ResidueTrichotomy (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    (n % (3 : ℤ) = 0 ∧ IsFirstHit p n 0 ∧
        RawStep p (Iterate (RawStep p) 0 n) = n / 3) ∨
      (n % (3 : ℤ) = 1 ∧ IsFirstHit p n 1 ∧
          AffineState p.Q p.C 1 n = 2 * n + 1 ∧
          RawStep p (Iterate (RawStep p) 1 n) = (2 * n + 1) / 3) ∨
      (n % (3 : ℤ) = 2 ∧ ∀ j : ℕ, ¬ IsFirstHit p n j) := by
  rcases EmodThreeCases n with h0 | h1 | h2
  · {
      obtain ⟨hhit, _hstate, hret⟩ := HitAtZero p hQ hC hD n h0
      exact Or.inl ⟨h0, hhit, hret⟩
    }
  · {
      obtain ⟨hhit, haff, hret⟩ := HitAtOne p hQ hC hD n h1
      exact Or.inr (Or.inl ⟨h1, hhit, haff, hret⟩)
    }
  · {
      refine Or.inr (Or.inr ⟨h2, ?_⟩)
      intro j
      exact RemainderTwoNoHit p hQ hC hD n h2 j
    }

/-- Seed `1` has first hit `1`, affine state `3` and return `1`. -/
theorem ExampleSeedOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    IsFirstHit p (1 : ℤ) 1 ∧
      AffineState p.Q p.C 1 (1 : ℤ) = 3 ∧
      RawStep p (Iterate (RawStep p) 1 (1 : ℤ)) = 1 := by
  have hmod : (1 : ℤ) % (3 : ℤ) = 1 :=
    Int.emod_eq_of_lt (by omega) (by omega)
  obtain ⟨hhit, haff, hret⟩ := HitAtOne p hQ hC hD 1 hmod
  have hnum : 2 * (1 : ℤ) + 1 = 3 := by omega
  have hquot : (3 : ℤ) / 3 = 1 := by
    have hone : (3 : ℤ) = (3 : ℤ) * 1 := by omega
    rw [hone]
    exact QuotientCancelThree 1
  refine ⟨hhit, ?_, ?_⟩
  · {
      rw [haff, hnum]
    }
  · {
      rw [hret, hnum, hquot]
    }

/-- Seed `4` has first hit `1`, affine state `9` and return `3`. -/
theorem ExampleSeedFour (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    IsFirstHit p (4 : ℤ) 1 ∧
      AffineState p.Q p.C 1 (4 : ℤ) = 9 ∧
      RawStep p (Iterate (RawStep p) 1 (4 : ℤ)) = 3 := by
  have h4 : (4 : ℤ) = (3 : ℤ) * 1 + 1 := by omega
  have hmod : (4 : ℤ) % (3 : ℤ) = 1 := by
    rw [h4]
    have hcancel := Int.mul_add_emod_self_left (3 : ℤ) (1 : ℤ) (1 : ℤ)
    have h1 : (1 : ℤ) % (3 : ℤ) = 1 :=
      Int.emod_eq_of_lt (by omega) (by omega)
    rw [hcancel, h1]
  obtain ⟨hhit, haff, hret⟩ := HitAtOne p hQ hC hD 4 hmod
  have hnum : 2 * (4 : ℤ) + 1 = 9 := by omega
  have hquot : (9 : ℤ) / 3 = 3 := by
    have hnine : (9 : ℤ) = (3 : ℤ) * 3 := by omega
    rw [hnine]
    exact QuotientCancelThree 3
  refine ⟨hhit, ?_, ?_⟩
  · {
      rw [haff, hnum]
    }
  · {
      rw [hret, hnum, hquot]
    }

/-- Seed `2` stays in residue `2`, so it has no first hit and never divides. -/
theorem ExampleSeedTwo (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    ResidueStepZ p (2 : ZMod p.D.natAbs) = (2 : ZMod p.D.natAbs) ∧
      (∀ j : ℕ, Iterate (ResidueStepZ p) j ((2 : ℤ) : ZMod p.D.natAbs) =
          (2 : ZMod p.D.natAbs)) ∧
      (∀ j : ℕ, ¬ IsFirstHit p (2 : ℤ) j) ∧
      NeverDivides p (2 : ℤ) := by
  have hmod : (2 : ℤ) % (3 : ℤ) = 2 :=
    Int.emod_eq_of_lt (by omega) (by omega)
  refine ⟨ResidueStepFixesTwo p hQ hC hD, ?_, ?_, ?_⟩
  · {
      intro j
      have hcast := CastRemainderTwo p hD (2 : ℤ) hmod
      rw [hcast]
      exact ResidueTwoConstant p hQ hC hD j
    }
  · {
      intro j
      exact RemainderTwoNoHit p hQ hC hD (2 : ℤ) hmod j
    }
  · {
      exact RemainderTwoNeverDivides p hQ hC hD (2 : ℤ) hmod
    }

/-- These parameters do not give every integer a first hit. -/
theorem ExampleNoTotalCore (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    ¬ ∀ n : ℤ, ∃ j : ℕ, IsFirstHit p n j := by
  intro hall
  obtain ⟨j, hj⟩ := hall (2 : ℤ)
  rcases ExampleSeedTwo p hQ hC hD with ⟨_hfix, _hiter, hmiss, _hnever⟩
  exact hmiss j hj

/-- Every seed that does hit obeys `3|return| ≤ 2|seed| + 1`. -/
theorem ExampleHitBound (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (j : ℕ) (h : IsFirstHit p n j) :
    3 * (RawStep p (Iterate (RawStep p) j n)).natAbs ≤ 2 * n.natAbs + 1 := by
  rcases ResidueTrichotomy p hQ hC hD n with hzero | hone | htwo
  · {
      rcases hzero with ⟨hmod, hhit, hret⟩
      have hj : j = 0 := FirstHitUnique p n j 0 h hhit
      subst hj
      rw [hret]
      have hdvd : (3 : ℤ) ∣ n := (Int.dvd_iff_emod_eq_zero).mpr hmod
      rw [CancelNatAbsThree n hdvd]
      exact HitBoundZeroNumerator n
    }
  · {
      rcases hone with ⟨hmod, hhit, _haff, hret⟩
      have hj : j = 1 := FirstHitUnique p n j 1 h hhit
      subst hj
      rw [hret]
      have hdvd : (3 : ℤ) ∣ 2 * n + 1 := TwoMulSuccDiv n hmod
      rw [CancelNatAbsThree (2 * n + 1) hdvd]
      exact HitBoundOneNumerator n
    }
  · {
      rcases htwo with ⟨_hmod, hmiss⟩
      exact False.elim (hmiss j h)
    }

/-- A natural number is at most a power of two with the same exponent. -/
theorem NatLeTwoPow (t : ℕ) : t ≤ 2 ^ t := by
  induction t with
  | zero => {
      exact Nat.zero_le 1
    }
  | succ t ih => {
      have hone : 1 ≤ 2 ^ t := Nat.succ_le_of_lt (Nat.two_pow_pos t)
      calc
        t + 1 ≤ 2 ^ t + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ t + 2 ^ t := Nat.add_le_add_left hone (2 ^ t)
        _ = 2 * 2 ^ t := by ring
        _ = 2 ^ (t + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    }

/-- The absolute value of a product with a power of two splits. -/
theorem AbsMulPowTwo (j : ℕ) (m : ℤ) :
    ((2 : ℤ) ^ j * m).natAbs = 2 ^ j * m.natAbs := by
  rw [Int.natAbs_mul, Int.natAbs_pow]
  rfl

/-- Removing one does not drop the absolute value by more than one. -/
theorem AbsSubOneLower (a : ℤ) : a.natAbs ≤ (a - 1).natAbs + 1 := by
  have h := Int.natAbs_add_le (a - 1) (1 : ℤ)
  have hsum : (a - 1) + 1 = a := by omega
  rw [hsum] at h
  simpa using h

/-- For `n ≠ -1`, the integers `2 ^ j * (n + 1) - 1` are unbounded. -/
theorem AffineAbsUnbounded (n : ℤ) (hn : n ≠ -1) (B : ℕ) :
    ∃ j : ℕ, B < ((2 : ℤ) ^ j * (n + 1) - 1).natAbs := by
  refine ⟨B + 2, ?_⟩
  have hunit : 1 ≤ (n + 1).natAbs := by
    have hne : n + 1 ≠ 0 := by
      intro hzero
      apply hn
      omega
    have hpos :
        0 < (n + 1).natAbs :=
      Nat.pos_of_ne_zero ((Int.natAbs_eq_zero).not.mpr hne)
    exact Nat.succ_le_of_lt hpos
  have hmul :
      2 ^ (B + 2) ≤ ((2 : ℤ) ^ (B + 2) * (n + 1)).natAbs := by
    rw [AbsMulPowTwo]
    calc
      2 ^ (B + 2) = 2 ^ (B + 2) * 1 := by omega
      _ ≤ 2 ^ (B + 2) * (n + 1).natAbs :=
        Nat.mul_le_mul_left (2 ^ (B + 2)) hunit
  have hsub :=
    AbsSubOneLower ((2 : ℤ) ^ (B + 2) * (n + 1))
  have hpow : B + 2 ≤ 2 ^ (B + 2) := NatLeTwoPow (B + 2)
  omega

/-- On a division-free orbit the raw states are the affine closed form. -/
theorem AffineOrbit (p : Parameters) (hQ : p.Q = 2) (hC : p.C = 1)
    (n : ℤ) (hfree : NeverDivides p n) (j : ℕ) :
    Iterate (RawStep p) j n = (2 : ℤ) ^ j * (n + 1) - 1 := by
  induction j with
  | zero => {
      simp [Iterate]
    }
  | succ j ih => {
      have hstep :
          Iterate (RawStep p) (j + 1) n =
            RawStep p (Iterate (RawStep p) j n) := rfl
      rw [hstep]
      have hmiss : ¬ p.D ∣ Iterate (RawStep p) j n := hfree j
      rw [RawStepAffine p (Iterate (RawStep p) j n) hmiss, hQ, hC, ih]
      ring
    }

/-- Reaching `0` after a delay is reaching `0` from the original seed. -/
theorem ReachZeroDelay (p : Parameters) (n : ℤ) (t j : ℕ)
    (h : Iterate (RawStep p) j (Iterate (RawStep p) t n) = 0) :
    Iterate (RawStep p) (t + j) n = 0 := by
  rw [IterateAdd]
  exact h

/-- Reaching `1` after a delay is reaching `1` from the original seed. -/
theorem ReachOneDelay (p : Parameters) (n : ℤ) (t j : ℕ)
    (h : Iterate (RawStep p) j (Iterate (RawStep p) t n) = 1) :
    Iterate (RawStep p) (t + j) n = 1 := by
  rw [IterateAdd]
  exact h

/-- Reaching `-1` after a delay is reaching `-1` from the original seed. -/
theorem ReachNegOneDelay (p : Parameters) (n : ℤ) (t j : ℕ)
    (h : Iterate (RawStep p) j (Iterate (RawStep p) t n) = -1) :
    Iterate (RawStep p) (t + j) n = -1 := by
  rw [IterateAdd]
  exact h

/-- An unbounded tail makes the original raw orbit unbounded. -/
theorem UnboundedDelay (p : Parameters) (n : ℤ) (t : ℕ)
    (h : ∀ B : ℕ, ∃ j : ℕ,
      B < (Iterate (RawStep p) j (Iterate (RawStep p) t n)).natAbs) :
    ∀ B : ℕ, ∃ j : ℕ, B < (Iterate (RawStep p) j n).natAbs := by
  intro B
  obtain ⟨j, hj⟩ := h B
  refine ⟨t + j, ?_⟩
  rw [IterateAdd]
  exact hj

/-- A nonzero multiple of three has a strictly smaller quotient. -/
theorem QuotientAbsSmaller (n : ℤ) (hdiv : (3 : ℤ) ∣ n) (hn : n ≠ 0) :
    (n / 3).natAbs < n.natAbs := by
  have hcancel := CancelNatAbsThree n hdiv
  have hpos :
      0 < n.natAbs :=
    Nat.pos_of_ne_zero ((Int.natAbs_eq_zero).not.mpr hn)
  omega

/-- Absolute value one means the integer is `1` or `-1`. -/
theorem NatAbsOneCases (n : ℤ) (h : n.natAbs = 1) : n = 1 ∨ n = -1 := by
  cases n with
  | ofNat m => {
      have hm : m = 1 := by simpa using h
      exact Or.inl (by simp [hm])
    }
  | negSucc m => {
      have hm : m = 0 := by simpa using h
      exact Or.inr (by simp [hm])
    }

/-- A residue-one seed of absolute value at least two has a smaller return. -/
theorem ResidueOneReturnSmaller (n : ℤ) (hmod : n % (3 : ℤ) = 1)
    (hk : 2 ≤ n.natAbs) :
    ((2 * n + 1) / 3).natAbs < n.natAbs := by
  have hdvd := TwoMulSuccDiv n hmod
  have _hcancel := CancelNatAbsThree (2 * n + 1) hdvd
  have htri := HitBoundOneNumerator n
  have hcmp : 2 * n.natAbs + 1 < 3 * n.natAbs := by omega
  omega

/-- Every raw orbit reaches `0`, `1`, or `-1`, or is unbounded. -/
theorem OrbitFate (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    (∃ j : ℕ, Iterate (RawStep p) j n = 0) ∨
      (∃ j : ℕ, Iterate (RawStep p) j n = 1) ∨
        (∃ j : ℕ, Iterate (RawStep p) j n = -1) ∨
          (∀ B : ℕ, ∃ j : ℕ, B < (Iterate (RawStep p) j n).natAbs) := by
  have main :
      ∀ k : ℕ, ∀ n : ℤ, n.natAbs ≤ k →
        (∃ j : ℕ, Iterate (RawStep p) j n = 0) ∨
          (∃ j : ℕ, Iterate (RawStep p) j n = 1) ∨
            (∃ j : ℕ, Iterate (RawStep p) j n = -1) ∨
              (∀ B : ℕ, ∃ j : ℕ,
                B < (Iterate (RawStep p) j n).natAbs) := by
    intro k
    induction k with
    | zero => {
        intro n hk
        have hz : n = 0 :=
          Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
        refine Or.inl ⟨0, ?_⟩
        simp [Iterate, hz]
      }
    | succ k ih => {
        intro n hk
        by_cases hsmall : n.natAbs ≤ k
        · {
            exact ih n hsmall
          }
        · {
            have heq : n.natAbs = k + 1 := by omega
            rcases ResidueTrichotomy p hQ hC hD n with
              hzero | hone | htwo
            · {
                rcases hzero with ⟨hmod, _hhit, hret⟩
                have hn : n ≠ 0 := by
                  intro hz
                  rw [hz] at heq
                  omega
                have hdvd : (3 : ℤ) ∣ n :=
                  (Int.dvd_iff_emod_eq_zero).mpr hmod
                have hlt := QuotientAbsSmaller n hdvd hn
                have hle : (n / 3).natAbs ≤ k := by omega
                have htail := ih (n / 3) hle
                have hstep : Iterate (RawStep p) 1 n = n / 3 := hret
                rw [← hstep] at htail
                rcases htail with h0 | h1 | hm | hu
                · {
                    obtain ⟨j, hj⟩ := h0
                    exact Or.inl ⟨1 + j, ReachZeroDelay p n 1 j hj⟩
                  }
                · {
                    obtain ⟨j, hj⟩ := h1
                    exact Or.inr (Or.inl ⟨1 + j, ReachOneDelay p n 1 j hj⟩)
                  }
                · {
                    obtain ⟨j, hj⟩ := hm
                    exact Or.inr (Or.inr
                      (Or.inl ⟨1 + j, ReachNegOneDelay p n 1 j hj⟩))
                  }
                · {
                    exact Or.inr
                      (Or.inr (Or.inr (UnboundedDelay p n 1 hu)))
                  }
              }
            · {
                rcases hone with ⟨hmod, _hhit, _haff, hret⟩
                by_cases hseed : n = 1
                · {
                    refine Or.inr (Or.inl ⟨0, ?_⟩)
                    simp [Iterate, hseed]
                  }
                · {
                    have hk2 : 2 ≤ n.natAbs := by
                      have hpos : 1 ≤ n.natAbs := by omega
                      have hne1 : n.natAbs ≠ 1 := by
                        intro habs
                        rcases NatAbsOneCases n habs with hn1 | hnm
                        · {
                            exact hseed hn1
                          }
                        · {
                            have hm2 : (-1 : ℤ) % (3 : ℤ) = 2 := by
                              have hsum :
                                  (-1 : ℤ) = 2 + (3 : ℤ) * (-1) := by
                                omega
                              rw [hsum, Int.add_mul_emod_self_left]
                              exact Int.emod_eq_of_lt (by omega) (by omega)
                            rw [hnm] at hmod
                            omega
                          }
                      omega
                    have hlt := ResidueOneReturnSmaller n hmod hk2
                    have hle :
                        ((2 * n + 1) / 3).natAbs ≤ k := by omega
                    have htail := ih ((2 * n + 1) / 3) hle
                    have hstep :
                        Iterate (RawStep p) 2 n = (2 * n + 1) / 3 := hret
                    rw [← hstep] at htail
                    rcases htail with h0 | h1 | hm | hu
                    · {
                        obtain ⟨j, hj⟩ := h0
                        exact Or.inl ⟨2 + j, ReachZeroDelay p n 2 j hj⟩
                      }
                    · {
                        obtain ⟨j, hj⟩ := h1
                        exact Or.inr
                          (Or.inl ⟨2 + j, ReachOneDelay p n 2 j hj⟩)
                      }
                    · {
                        obtain ⟨j, hj⟩ := hm
                        exact Or.inr (Or.inr (Or.inl
                          ⟨2 + j, ReachNegOneDelay p n 2 j hj⟩))
                      }
                    · {
                        exact Or.inr (Or.inr
                          (Or.inr (UnboundedDelay p n 2 hu)))
                      }
                  }
              }
            · {
                rcases htwo with ⟨hmod, _hmiss⟩
                by_cases hneg : n = -1
                · {
                    refine Or.inr (Or.inr (Or.inl ⟨0, ?_⟩))
                    simp [Iterate, hneg]
                  }
                · {
                    refine Or.inr (Or.inr (Or.inr ?_))
                    intro B
                    obtain ⟨j, hj⟩ := AffineAbsUnbounded n hneg B
                    refine ⟨j, ?_⟩
                    have hfree :=
                      RemainderTwoNeverDivides p hQ hC hD n hmod
                    rw [AffineOrbit p hQ hC n hfree j]
                    exact hj
                  }
              }
          }
      }
  exact main n.natAbs n (Nat.le_refl n.natAbs)

/-- The residue of `-1` modulo `3` is `2`. -/
theorem NegOneModThree : (-1 : ℤ) % (3 : ℤ) = 2 := by
  have hsum : (-1 : ℤ) = 2 + (3 : ℤ) * (-1) := by omega
  rw [hsum, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- Zero is fixed by exact division. -/
theorem RawStepZero (p : Parameters) (hD : p.D = 3) : RawStep p 0 = 0 := by
  have hd : p.D ∣ (0 : ℤ) := dvd_zero p.D
  rw [RawStep, if_pos hd, hD]
  rfl

/-- The seed `-1` is fixed by the affine step. -/
theorem RawStepNegOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    RawStep p (-1) = -1 := by
  have hnd : ¬ p.D ∣ (-1 : ℤ) := by
    rw [hD]
    intro hd
    have hzero : (-1 : ℤ) % (3 : ℤ) = 0 :=
      (Int.dvd_iff_emod_eq_zero).mp hd
    rw [NegOneModThree] at hzero
    omega
  rw [RawStep, if_neg hnd, hQ, hC]
  omega

/-- The seed `1` steps to `3`. -/
theorem RawStepOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    RawStep p 1 = 3 := by
  have hnd : ¬ p.D ∣ (1 : ℤ) := by
    rw [hD]
    intro hd
    have hzero : (1 : ℤ) % (3 : ℤ) = 0 :=
      (Int.dvd_iff_emod_eq_zero).mp hd
    have hone : (1 : ℤ) % (3 : ℤ) = 1 :=
      Int.emod_eq_of_lt (by omega) (by omega)
    omega
  rw [RawStep, if_neg hnd, hQ, hC]
  omega

/-- The seed `3` steps to `1`. -/
theorem RawStepThree (p : Parameters) (hD : p.D = 3) :
    RawStep p 3 = 1 := by
  have hd : p.D ∣ (3 : ℤ) := by
    rw [hD]
  have hnum : (3 : ℤ) = (3 : ℤ) * 1 := by omega
  have hthree : (3 : ℤ) / 3 = ((3 : ℤ) * 1) / 3 := by
    rw [← hnum]
  rw [RawStep, if_pos hd, hD, hthree]
  exact QuotientCancelThree 1

/-- Every forward image of zero is zero. -/
theorem OrbitZero (p : Parameters) (hD : p.D = 3) (j : ℕ) :
    Iterate (RawStep p) j 0 = 0 := by
  induction j with
  | zero => {
      rfl
    }
  | succ j ih => {
      have hstep :
          Iterate (RawStep p) (j + 1) 0 =
            RawStep p (Iterate (RawStep p) j 0) := rfl
      rw [hstep, ih, RawStepZero p hD]
    }

/-- Every forward image of `-1` is `-1`. -/
theorem OrbitNegOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (j : ℕ) :
    Iterate (RawStep p) j (-1) = -1 := by
  induction j with
  | zero => {
      rfl
    }
  | succ j ih => {
      have hstep :
          Iterate (RawStep p) (j + 1) (-1) =
            RawStep p (Iterate (RawStep p) j (-1)) := rfl
      rw [hstep, ih, RawStepNegOne p hQ hC hD]
    }

/-- Every forward image of `1` is `1` or `3`. -/
theorem ImageOfOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (j : ℕ) :
    Iterate (RawStep p) j 1 = 1 ∨ Iterate (RawStep p) j 1 = 3 := by
  induction j with
  | zero => {
      exact Or.inl rfl
    }
  | succ j ih => {
      have hstep :
          Iterate (RawStep p) (j + 1) 1 =
            RawStep p (Iterate (RawStep p) j 1) := rfl
      rcases ih with hone | hthree
      · {
          rw [hstep, hone, RawStepOne p hQ hC hD]
          exact Or.inr rfl
        }
      · {
          rw [hstep, hthree, RawStepThree p hD]
          exact Or.inl rfl
        }
    }

/-- A positive period repeats at every multiple. -/
theorem PeriodMultiple (p : Parameters) (n : ℤ) (k t : ℕ)
    (hper : Iterate (RawStep p) k n = n) :
    Iterate (RawStep p) (t * k) n = n := by
  induction t with
  | zero => {
      rw [Nat.zero_mul]
      rfl
    }
  | succ t ih => {
      rw [Nat.succ_mul, IterateAdd, ih, hper]
    }

/-- Adding one period does not change a residue class on the cycle. -/
theorem CongruentIterate (p : Parameters) (n : ℤ) (k r t : ℕ)
    (hper : Iterate (RawStep p) k n = n) :
    Iterate (RawStep p) (t * k + r) n = Iterate (RawStep p) r n := by
  induction t with
  | zero => {
      rw [Nat.zero_mul, Nat.zero_add]
    }
  | succ t ih => {
      have hsum : (t + 1) * k + r = t * k + r + k := by
        rw [Nat.succ_mul]
        exact Nat.add_right_comm (t * k) k r
      rw [hsum, IterateAdd, ih]
      have hcomm : r + k = k + r := Nat.add_comm r k
      rw [← IterateAdd (RawStep p) r k n, hcomm, IterateAdd, hper]
    }

/-- Every iterate on a cycle equals the corresponding initial residue. -/
theorem ReduceByPeriod (p : Parameters) (n : ℤ) (k j : ℕ)
    (hk : 0 < k) (hper : Iterate (RawStep p) k n = n) :
    Iterate (RawStep p) j n = Iterate (RawStep p) (j % k) n := by
  have hsplit : k * (j / k) + j % k = j := Nat.div_add_mod j k
  have hr : j % k < k := Nat.mod_lt j hk
  have hcong :=
    CongruentIterate p n k (j % k) (j / k) hper
  have hcomm : (j / k) * k = k * (j / k) := Nat.mul_comm _ _
  rw [hcomm, hsplit] at hcong
  exact hcong

/-- The largest absolute value among the first `t` iterates. -/
def PrefixMaxAbs (p : Parameters) (n : ℤ) : ℕ → ℕ
  | 0 => 0
  | i + 1 =>
      max (PrefixMaxAbs p n i) (Iterate (RawStep p) i n).natAbs

/-- Extending the prefix cannot decrease the recorded maximum. -/
theorem PrefixMaxAbsSuccLe (p : Parameters) (n : ℤ) (i : ℕ) :
    PrefixMaxAbs p n i ≤ PrefixMaxAbs p n (i + 1) := by
  rw [PrefixMaxAbs]
  exact Nat.le_max_left _ _

/-- The prefix maximum is monotone in the length. -/
theorem PrefixMaxAbsMono (p : Parameters) (n : ℤ) (s t : ℕ)
    (h : s ≤ t) : PrefixMaxAbs p n s ≤ PrefixMaxAbs p n t := by
  induction t with
  | zero => {
      have hs : s = 0 := Nat.eq_zero_of_le_zero h
      rw [hs]
    }
  | succ t ih => {
      by_cases hst : s ≤ t
      · {
          exact Nat.le_trans (ih hst) (PrefixMaxAbsSuccLe p n t)
        }
      · {
          have hs : s = t + 1 := by omega
          rw [hs]
        }
    }

/-- Each listed iterate is at most the maximum of the prefix. -/
theorem PrefixMaxAbsGe (p : Parameters) (n : ℤ) (i : ℕ) :
    (Iterate (RawStep p) i n).natAbs ≤ PrefixMaxAbs p n (i + 1) := by
  rw [PrefixMaxAbs]
  exact Nat.le_max_right _ _

/-- A hit point reaches back to the periodic seed. -/
theorem PullFromHit (p : Parameters) (n a : ℤ) (k j : ℕ)
    (hk : 0 < k) (hper : Iterate (RawStep p) k n = n)
    (hj : Iterate (RawStep p) j n = a) :
    ∃ m : ℕ, Iterate (RawStep p) m a = n := by
  have hone : 1 ≤ k := Nat.succ_le_of_lt hk
  have hmulLe : 1 * j ≤ k * j := Nat.mul_le_mul_right j hone
  have hle : j ≤ k * j := by
    rw [Nat.one_mul] at hmulLe
    exact hmulLe
  refine ⟨k * j - j, ?_⟩
  have hmul := PeriodMultiple p n k j hper
  have hsum : j + (k * j - j) = k * j := Nat.add_sub_of_le hle
  have hback :
      Iterate (RawStep p) (j + (k * j - j)) n =
        Iterate (RawStep p) (k * j - j) a := by
    rw [IterateAdd, hj]
  rw [hsum] at hback
  have hcomm : j * k = k * j := Nat.mul_comm j k
  rw [hcomm] at hmul
  rw [hmul] at hback
  exact hback.symm

/-- The periodic points are exactly `0`, `-1`, `1`, and `3`. -/
theorem PeriodicPoints (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    (∃ k : ℕ, 0 < k ∧ Iterate (RawStep p) k n = n) ↔
      n = 0 ∨ n = -1 ∨ n = 1 ∨ n = 3 := by
  constructor
  · {
      intro hper
      obtain ⟨k, hk, hloop⟩ := hper
      rcases OrbitFate p hQ hC hD n with h0 | h1 | hm | hu
      · {
          obtain ⟨j, hj⟩ := h0
          obtain ⟨m, hm⟩ := PullFromHit p n 0 k j hk hloop hj
          have hzero := OrbitZero p hD m
          rw [hzero] at hm
          exact Or.inl hm.symm
        }
      · {
          obtain ⟨j, hj⟩ := h1
          obtain ⟨m, hm⟩ := PullFromHit p n 1 k j hk hloop hj
          rcases ImageOfOne p hQ hC hD m with hone | hthree
          · {
              rw [hone] at hm
              exact Or.inr (Or.inr (Or.inl hm.symm))
            }
          · {
              rw [hthree] at hm
              exact Or.inr (Or.inr (Or.inr hm.symm))
            }
        }
      · {
          obtain ⟨j, hj⟩ := hm
          obtain ⟨m, hback⟩ := PullFromHit p n (-1) k j hk hloop hj
          have hfix := OrbitNegOne p hQ hC hD m
          rw [hfix] at hback
          exact Or.inr (Or.inl hback.symm)
        }
      · {
          have hle : ∀ j : ℕ,
              (Iterate (RawStep p) j n).natAbs ≤ PrefixMaxAbs p n k := by
            intro j
            rw [ReduceByPeriod p n k j hk hloop]
            have hr : j % k < k := Nat.mod_lt j hk
            exact Nat.le_trans (PrefixMaxAbsGe p n (j % k))
              (PrefixMaxAbsMono p n ((j % k) + 1) k
                (Nat.succ_le_of_lt hr))
          obtain ⟨j, hj⟩ := hu (PrefixMaxAbs p n k)
          exact absurd hj (Nat.not_lt_of_ge (hle j))
        }
    }
  · {
      intro h
      rcases h with h0 | hneg | hone | hthree
      · {
          refine ⟨1, Nat.one_pos, ?_⟩
          rw [h0]
          have hstep : Iterate (RawStep p) 1 0 = RawStep p 0 := rfl
          rw [hstep, RawStepZero p hD]
        }
      · {
          refine ⟨1, Nat.one_pos, ?_⟩
          rw [hneg]
          have hstep : Iterate (RawStep p) 1 (-1) = RawStep p (-1) := rfl
          rw [hstep, RawStepNegOne p hQ hC hD]
        }
      · {
          refine ⟨2, by omega, ?_⟩
          rw [hone]
          have hstep :
              Iterate (RawStep p) 2 1 =
                RawStep p (Iterate (RawStep p) 1 1) := rfl
          have hfirst : Iterate (RawStep p) 1 1 = RawStep p 1 := rfl
          rw [hstep, hfirst, RawStepOne p hQ hC hD, RawStepThree p hD]
        }
      · {
          refine ⟨2, by omega, ?_⟩
          rw [hthree]
          have hstep :
              Iterate (RawStep p) 2 3 =
                RawStep p (Iterate (RawStep p) 1 3) := rfl
          have hfirst : Iterate (RawStep p) 1 3 = RawStep p 3 := rfl
          rw [hstep, hfirst, RawStepThree p hD, RawStepOne p hQ hC hD]
        }
    }

/-- Some forward image is a periodic point. -/
def EventuallyPeriodic (p : Parameters) (n : ℤ) : Prop :=
  ∃ j k : ℕ, 0 < k ∧
    Iterate (RawStep p) k (Iterate (RawStep p) j n) =
      Iterate (RawStep p) j n

/-- Eventual periodicity is reaching `0`, `1`, or `-1`. -/
theorem EventuallyPeriodicIffHit (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    EventuallyPeriodic p n ↔
      (∃ j : ℕ, Iterate (RawStep p) j n = 0) ∨
        (∃ j : ℕ, Iterate (RawStep p) j n = 1) ∨
          (∃ j : ℕ, Iterate (RawStep p) j n = -1) := by
  constructor
  · {
      intro h
      obtain ⟨j, k, hk, hloop⟩ := h
      have hpt :=
        (PeriodicPoints p hQ hC hD (Iterate (RawStep p) j n)).mp
          ⟨k, hk, hloop⟩
      rcases hpt with h0 | hneg | hone | hthree
      · {
          exact Or.inl ⟨j, h0⟩
        }
      · {
          exact Or.inr (Or.inr ⟨j, hneg⟩)
        }
      · {
          exact Or.inr (Or.inl ⟨j, hone⟩)
        }
      · {
          have hnext : Iterate (RawStep p) (j + 1) n = 1 := by
            have hstep :
                Iterate (RawStep p) (j + 1) n =
                  RawStep p (Iterate (RawStep p) j n) := rfl
            rw [hstep, hthree, RawStepThree p hD]
          exact Or.inr (Or.inl ⟨j + 1, hnext⟩)
        }
    }
  · {
      intro h
      rcases h with h0 | h1 | hm
      · {
          obtain ⟨j, hj⟩ := h0
          have hper :=
            (PeriodicPoints p hQ hC hD (Iterate (RawStep p) j n)).mpr
              (Or.inl hj)
          obtain ⟨k, hk, hloop⟩ := hper
          exact ⟨j, k, hk, hloop⟩
        }
      · {
          obtain ⟨j, hj⟩ := h1
          have hper :=
            (PeriodicPoints p hQ hC hD (Iterate (RawStep p) j n)).mpr
              (Or.inr (Or.inr (Or.inl hj)))
          obtain ⟨k, hk, hloop⟩ := hper
          exact ⟨j, k, hk, hloop⟩
        }
      · {
          obtain ⟨j, hj⟩ := hm
          have hper :=
            (PeriodicPoints p hQ hC hD (Iterate (RawStep p) j n)).mpr
              (Or.inr (Or.inl hj))
          obtain ⟨k, hk, hloop⟩ := hper
          exact ⟨j, k, hk, hloop⟩
        }
    }

/-- After `0`, every later term is `0`. -/
theorem TailAtZero (p : Parameters) (hD : p.D = 3) (n : ℤ)
    (j t : ℕ) (hj : Iterate (RawStep p) j n = 0) :
    Iterate (RawStep p) (j + t) n = 0 := by
  rw [IterateAdd, hj, OrbitZero p hD t]

/-- After `-1`, every later term is `-1`. -/
theorem TailAtNegOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (j t : ℕ) (hj : Iterate (RawStep p) j n = -1) :
    Iterate (RawStep p) (j + t) n = -1 := by
  rw [IterateAdd, hj, OrbitNegOne p hQ hC hD t]

/-- After `1`, every later term is `1` or `3`. -/
theorem TailAtOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (j t : ℕ) (hj : Iterate (RawStep p) j n = 1) :
    Iterate (RawStep p) (j + t) n = 1 ∨
      Iterate (RawStep p) (j + t) n = 3 := by
  rw [IterateAdd, hj]
  exact ImageOfOne p hQ hC hD t

/-- A periodic point has absolute value at most `3` at every time. -/
theorem PeriodicValueAbs (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (a : ℤ)
    (ha : a = 0 ∨ a = -1 ∨ a = 1 ∨ a = 3) (t : ℕ) :
    (Iterate (RawStep p) t a).natAbs ≤ 3 := by
  rcases ha with h0 | hneg | hone | hthree
  · {
      rw [h0, OrbitZero p hD t]
      omega
    }
  · {
      rw [hneg, OrbitNegOne p hQ hC hD t]
      have honeAbs : (-1 : ℤ).natAbs = 1 := rfl
      omega
    }
  · {
      rw [hone]
      rcases ImageOfOne p hQ hC hD t with h1 | h3
      · {
          rw [h1]
          omega
        }
      · {
          rw [h3]
          omega
        }
    }
  · {
      rw [hthree]
      cases t with
      | zero => {
          have hzero : Iterate (RawStep p) 0 (3 : ℤ) = 3 := rfl
          rw [hzero]
          omega
        }
      | succ s => {
          have hfirst : Iterate (RawStep p) 1 (3 : ℤ) = 1 := by
            have hraw : Iterate (RawStep p) 1 (3 : ℤ) = RawStep p 3 := rfl
            rw [hraw, RawStepThree p hD]
          have htail := TailAtOne p hQ hC hD (3 : ℤ) 1 s hfirst
          have hsum : 1 + s = s + 1 := Nat.add_comm 1 s
          rw [hsum] at htail
          rcases htail with h1 | h3
          · {
              rw [h1]
              omega
            }
          · {
              rw [h3]
              omega
            }
        }
    }

/-- An eventually periodic orbit is bounded. -/
theorem EventuallyPeriodicBounded (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : EventuallyPeriodic p n) :
    ∃ M : ℕ, ∀ t : ℕ, (Iterate (RawStep p) t n).natAbs ≤ M := by
  obtain ⟨j, k, hk, hloop⟩ := h
  have hpt :=
    (PeriodicPoints p hQ hC hD (Iterate (RawStep p) j n)).mp
      ⟨k, hk, hloop⟩
  refine ⟨max (PrefixMaxAbs p n (j + 1)) 3, ?_⟩
  intro t
  by_cases ht : t ≤ j
  · {
      have hge := PrefixMaxAbsGe p n t
      have hmono :=
        PrefixMaxAbsMono p n (t + 1) (j + 1) (Nat.succ_le_succ ht)
      exact Nat.le_trans (Nat.le_trans hge hmono) (Nat.le_max_left _ _)
    }
  · {
      have hge : j ≤ t := by omega
      have hsum : j + (t - j) = t := Nat.add_sub_of_le hge
      have htail :
          Iterate (RawStep p) t n =
            Iterate (RawStep p) (t - j) (Iterate (RawStep p) j n) := by
        conv_lhs => rw [← hsum]
        rw [IterateAdd]
      rw [htail]
      have habs :=
        PeriodicValueAbs p hQ hC hD _ hpt (t - j)
      exact Nat.le_trans habs (Nat.le_max_right _ _)
    }

/-- Every orbit is eventually periodic or unbounded in absolute value. -/
theorem OrbitSplit (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    EventuallyPeriodic p n ∨
      (∀ B : ℕ, ∃ j : ℕ, B < (Iterate (RawStep p) j n).natAbs) := by
  rcases OrbitFate p hQ hC hD n with h0 | h1 | hm | hu
  · {
      exact Or.inl
        ((EventuallyPeriodicIffHit p hQ hC hD n).mpr (Or.inl h0))
    }
  · {
      exact Or.inl
        ((EventuallyPeriodicIffHit p hQ hC hD n).mpr
          (Or.inr (Or.inl h1)))
    }
  · {
      exact Or.inl
        ((EventuallyPeriodicIffHit p hQ hC hD n).mpr
          (Or.inr (Or.inr hm)))
    }
  · {
      exact Or.inr hu
    }

/-- An eventually periodic orbit is not absolutely unbounded. -/
theorem EventuallyPeriodicNotUnbounded (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : EventuallyPeriodic p n) :
    ¬ (∀ B : ℕ, ∃ j : ℕ,
      B < (Iterate (RawStep p) j n).natAbs) := by
  obtain ⟨M, hM⟩ := EventuallyPeriodicBounded p hQ hC hD n h
  intro hu
  obtain ⟨j, hj⟩ := hu M
  exact Nat.not_lt_of_ge (hM j) hj

/-- Dropping a finite prefix preserves absolute unboundedness. -/
theorem TailOfUnbounded (p : Parameters) (n : ℤ) (t : ℕ)
    (h : ∀ B : ℕ, ∃ j : ℕ, B < (Iterate (RawStep p) j n).natAbs) :
    ∀ B : ℕ, ∃ j : ℕ,
      B < (Iterate (RawStep p) j (Iterate (RawStep p) t n)).natAbs := by
  intro B
  obtain ⟨j, hj⟩ := h (max B (PrefixMaxAbs p n t))
  have hge : t ≤ j := by
    by_contra hlt
    have hltj : j < t := Nat.lt_of_not_le hlt
    have habs := PrefixMaxAbsGe p n j
    have hmono :=
      PrefixMaxAbsMono p n (j + 1) t (Nat.succ_le_of_lt hltj)
    have hbound := Nat.le_trans habs hmono
    have hcap : PrefixMaxAbs p n t ≤ max B (PrefixMaxAbs p n t) :=
      Nat.le_max_right _ _
    omega
  have hsum : t + (j - t) = j := Nat.add_sub_of_le hge
  refine ⟨j - t, ?_⟩
  have heq :
      Iterate (RawStep p) j n =
        Iterate (RawStep p) (j - t) (Iterate (RawStep p) t n) := by
    conv_lhs => rw [← hsum]
    rw [IterateAdd]
  rw [heq] at hj
  exact Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hj

/-- A residue witness survives when it is read on the original orbit. -/
theorem BadResidueDelay (p : Parameters) (n : ℤ) (t j : ℕ)
    (hmod :
      (Iterate (RawStep p) j (Iterate (RawStep p) t n)) % (3 : ℤ) = 2)
    (hne : Iterate (RawStep p) j (Iterate (RawStep p) t n) ≠ -1) :
    (Iterate (RawStep p) (t + j) n) % (3 : ℤ) = 2 ∧
      Iterate (RawStep p) (t + j) n ≠ -1 := by
  have heq :
      Iterate (RawStep p) (t + j) n =
        Iterate (RawStep p) j (Iterate (RawStep p) t n) := by
    rw [IterateAdd]
  rw [heq]
  exact ⟨hmod, hne⟩

/-- Landing on residue `2`, away from `-1`, makes the orbit unbounded. -/
theorem BadResidueUnbounded (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ j : ℕ, (Iterate (RawStep p) j n) % (3 : ℤ) = 2 ∧
      Iterate (RawStep p) j n ≠ -1) :
    ∀ B : ℕ, ∃ i : ℕ, B < (Iterate (RawStep p) i n).natAbs := by
  obtain ⟨j, hmod, hne⟩ := h
  have hfree := RemainderTwoNeverDivides p hQ hC hD
    (Iterate (RawStep p) j n) hmod
  have htail : ∀ B : ℕ, ∃ k : ℕ,
      B < (Iterate (RawStep p) k (Iterate (RawStep p) j n)).natAbs := by
    intro B
    obtain ⟨k, hk⟩ :=
      AffineAbsUnbounded (Iterate (RawStep p) j n) hne B
    rw [← AffineOrbit p hQ hC (Iterate (RawStep p) j n) hfree k] at hk
    exact ⟨k, hk⟩
  exact UnboundedDelay p n j htail

/-- Absolute unboundedness is reaching residue `2` away from `-1`. -/
theorem UnboundedIffBadResidue (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    (∀ B : ℕ, ∃ j : ℕ, B < (Iterate (RawStep p) j n).natAbs) ↔
      ∃ j : ℕ, (Iterate (RawStep p) j n) % (3 : ℤ) = 2 ∧
        Iterate (RawStep p) j n ≠ -1 := by
  constructor
  · {
      intro hu
      have main : ∀ k : ℕ, ∀ n : ℤ, n.natAbs ≤ k →
          (∀ B : ℕ, ∃ j : ℕ,
            B < (Iterate (RawStep p) j n).natAbs) →
            ∃ j : ℕ, (Iterate (RawStep p) j n) % (3 : ℤ) = 2 ∧
              Iterate (RawStep p) j n ≠ -1 := by
        intro k
        induction k with
        | zero => {
            intro n hk hu0
            have hz : n = 0 :=
              Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
            obtain ⟨j, hj⟩ := hu0 0
            rw [hz, OrbitZero p hD j] at hj
            omega
          }
        | succ k ih => {
            intro n hk hu0
            by_cases hsmall : n.natAbs ≤ k
            · {
                exact ih n hsmall hu0
              }
            · {
                have heq : n.natAbs = k + 1 := by omega
                rcases ResidueTrichotomy p hQ hC hD n with
                  hzero | hone | htwo
                · {
                    rcases hzero with ⟨hmod, _hhit, hret⟩
                    have hnz : n ≠ 0 := by
                      intro hz
                      obtain ⟨j, hj⟩ := hu0 0
                      rw [hz, OrbitZero p hD j] at hj
                      omega
                    have hdvd : (3 : ℤ) ∣ n :=
                      (Int.dvd_iff_emod_eq_zero).mpr hmod
                    have hlt := QuotientAbsSmaller n hdvd hnz
                    have hstep : Iterate (RawStep p) 1 n = n / 3 := by
                      have hraw :
                          Iterate (RawStep p) 1 n = RawStep p n := rfl
                      have hbase : Iterate (RawStep p) 0 n = n := rfl
                      rw [hbase] at hret
                      rw [hraw, hret]
                    have htail := TailOfUnbounded p n 1 hu0
                    rw [hstep] at htail
                    have hle : (n / 3).natAbs ≤ k := by omega
                    obtain ⟨j, hmodj, hnej⟩ := ih (n / 3) hle htail
                    rw [← hstep] at hmodj hnej
                    exact ⟨1 + j, BadResidueDelay p n 1 j hmodj hnej⟩
                  }
                · {
                    rcases hone with ⟨hmod, _hhit, _haff, hret⟩
                    by_cases hbig : 2 ≤ n.natAbs
                    · {
                        have hlt :=
                          ResidueOneReturnSmaller n hmod hbig
                        have hstep :
                            Iterate (RawStep p) 2 n =
                              (2 * n + 1) / 3 := by
                          have hraw :
                              Iterate (RawStep p) 2 n =
                                RawStep p (Iterate (RawStep p) 1 n) :=
                            rfl
                          rw [hraw, hret]
                        have htail := TailOfUnbounded p n 2 hu0
                        rw [hstep] at htail
                        have hle :
                            ((2 * n + 1) / 3).natAbs ≤ k := by omega
                        obtain ⟨j, hmodj, hnej⟩ :=
                          ih ((2 * n + 1) / 3) hle htail
                        rw [← hstep] at hmodj hnej
                        exact ⟨2 + j, BadResidueDelay p n 2 j hmodj hnej⟩
                      }
                    · {
                        have honeAbs : n.natAbs = 1 := by omega
                        rcases NatAbsOneCases n honeAbs with hn1 | hnneg
                        · {
                            obtain ⟨j, hj⟩ := hu0 3
                            rcases ImageOfOne p hQ hC hD j with h1 | h3
                            · {
                                rw [hn1, h1] at hj
                                omega
                              }
                            · {
                                rw [hn1, h3] at hj
                                omega
                              }
                          }
                        · {
                            rw [hnneg] at hmod
                            have hclass := NegOneModThree
                            omega
                          }
                      }
                  }
                · {
                    rcases htwo with ⟨hmod, _hmiss⟩
                    refine ⟨0, ?_⟩
                    have hbase : Iterate (RawStep p) 0 n = n := rfl
                    rw [hbase]
                    refine ⟨hmod, ?_⟩
                    intro hneg
                    obtain ⟨j, hj⟩ := hu0 1
                    rw [hneg, OrbitNegOne p hQ hC hD j] at hj
                    omega
                  }
              }
          }
      exact main n.natAbs n (Nat.le_refl _) hu
    }
  · {
      intro h
      exact BadResidueUnbounded p hQ hC hD n h
    }

/-- An orbit cannot meet both `0` and `1`. -/
theorem NotBothZeroAndOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h0 : ∃ j : ℕ, Iterate (RawStep p) j n = 0)
    (h1 : ∃ i : ℕ, Iterate (RawStep p) i n = 1) : False := by
  obtain ⟨j, hj⟩ := h0
  obtain ⟨i, hi⟩ := h1
  rcases Nat.le_total j i with hji | hij
  · {
      have hsum : j + (i - j) = i := Nat.add_sub_of_le hji
      have htail := TailAtZero p hD n j (i - j) hj
      rw [hsum] at htail
      rw [htail] at hi
      omega
    }
  · {
      have hsum : i + (j - i) = j := Nat.add_sub_of_le hij
      have htail := TailAtOne p hQ hC hD n i (j - i) hi
      rw [hsum] at htail
      rw [hj] at htail
      rcases htail with hz | hthree
      · {
          omega
        }
      · {
          omega
        }
    }

/-- An orbit cannot meet both `0` and `-1`. -/
theorem NotBothZeroAndNegOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h0 : ∃ j : ℕ, Iterate (RawStep p) j n = 0)
    (hm : ∃ i : ℕ, Iterate (RawStep p) i n = -1) : False := by
  obtain ⟨j, hj⟩ := h0
  obtain ⟨i, hi⟩ := hm
  rcases Nat.le_total j i with hji | hij
  · {
      have hsum : j + (i - j) = i := Nat.add_sub_of_le hji
      have htail := TailAtZero p hD n j (i - j) hj
      rw [hsum] at htail
      rw [htail] at hi
      omega
    }
  · {
      have hsum : i + (j - i) = j := Nat.add_sub_of_le hij
      have htail := TailAtNegOne p hQ hC hD n i (j - i) hi
      rw [hsum] at htail
      rw [hj] at htail
      omega
    }

/-- An orbit cannot meet both `1` and `-1`. -/
theorem NotBothOneAndNegOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h1 : ∃ i : ℕ, Iterate (RawStep p) i n = 1)
    (hm : ∃ j : ℕ, Iterate (RawStep p) j n = -1) : False := by
  obtain ⟨i, hi⟩ := h1
  obtain ⟨j, hj⟩ := hm
  rcases Nat.le_total i j with hij | hji
  · {
      have hsum : i + (j - i) = j := Nat.add_sub_of_le hij
      have htail := TailAtOne p hQ hC hD n i (j - i) hi
      rw [hsum] at htail
      rw [hj] at htail
      rcases htail with hone | hthree
      · {
          omega
        }
      · {
          omega
        }
    }
  · {
      have hsum : j + (i - j) = i := Nat.add_sub_of_le hji
      have htail := TailAtNegOne p hQ hC hD n j (i - j) hj
      rw [hsum] at htail
      rw [htail] at hi
      omega
    }

/-- Reaching `0`, `1`, or `-1` excludes absolute unboundedness. -/
theorem HitNotUnbounded (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : (∃ j : ℕ, Iterate (RawStep p) j n = 0) ∨
      (∃ j : ℕ, Iterate (RawStep p) j n = 1) ∨
        (∃ j : ℕ, Iterate (RawStep p) j n = -1)) :
    ¬ (∀ B : ℕ, ∃ j : ℕ, B < (Iterate (RawStep p) j n).natAbs) := by
  have hep := (EventuallyPeriodicIffHit p hQ hC hD n).mpr h
  exact EventuallyPeriodicNotUnbounded p hQ hC hD n hep

/-- Every orbit has exactly one of the four outcomes. -/
theorem OrbitExactlyOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    ((∃ j : ℕ, Iterate (RawStep p) j n = 0) ∨
      (∃ j : ℕ, Iterate (RawStep p) j n = 1) ∨
        (∃ j : ℕ, Iterate (RawStep p) j n = -1) ∨
          (∀ B : ℕ, ∃ j : ℕ,
            B < (Iterate (RawStep p) j n).natAbs)) ∧
      (¬ ((∃ j : ℕ, Iterate (RawStep p) j n = 0) ∧
        (∃ i : ℕ, Iterate (RawStep p) i n = 1))) ∧
      (¬ ((∃ j : ℕ, Iterate (RawStep p) j n = 0) ∧
        (∃ i : ℕ, Iterate (RawStep p) i n = -1))) ∧
      (¬ ((∃ i : ℕ, Iterate (RawStep p) i n = 1) ∧
        (∃ j : ℕ, Iterate (RawStep p) j n = -1))) ∧
      (¬ (((∃ j : ℕ, Iterate (RawStep p) j n = 0) ∨
          (∃ j : ℕ, Iterate (RawStep p) j n = 1) ∨
            (∃ j : ℕ, Iterate (RawStep p) j n = -1)) ∧
        (∀ B : ℕ, ∃ j : ℕ,
          B < (Iterate (RawStep p) j n).natAbs))) := by
  refine ⟨OrbitFate p hQ hC hD n, ?_, ?_, ?_, ?_⟩
  · {
      intro h
      exact NotBothZeroAndOne p hQ hC hD n h.1 h.2
    }
  · {
      intro h
      exact NotBothZeroAndNegOne p hQ hC hD n h.1 h.2
    }
  · {
      intro h
      exact NotBothOneAndNegOne p hQ hC hD n h.1 h.2
    }
  · {
      intro h
      exact HitNotUnbounded p hQ hC hD n h.1 h.2
    }

/-- The raw step equals zero only at the seed zero. -/
theorem RawStepZeroIff (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    RawStep p n = 0 ↔ n = 0 := by
  constructor
  · {
      intro h
      by_cases hd : p.D ∣ n
      · {
          have hquot : n / p.D = 0 := by
            rw [RawStep, if_pos hd] at h
            exact h
          have hrec := Int.emod_add_mul_ediv n p.D
          have hmod : n % p.D = 0 := (Int.dvd_iff_emod_eq_zero).mp hd
          rw [hmod, hquot, hD] at hrec
          omega
        }
      · {
          rw [RawStep, if_neg hd, hQ, hC] at h
          omega
        }
    }
  · {
      intro hn
      have hd : p.D ∣ (0 : ℤ) := dvd_zero p.D
      rw [hn, RawStep, if_pos hd, hD]
      rfl
    }

/-- The orbit meets zero if and only if the seed is zero. -/
theorem OnlyZeroReachesZero (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    (∃ j : ℕ, Iterate (RawStep p) j n = 0) ↔ n = 0 := by
  constructor
  · {
      intro h
      obtain ⟨j, hj⟩ := h
      induction j generalizing n with
      | zero => {
          have h0 : Iterate (RawStep p) 0 n = n := rfl
          rw [h0] at hj
          exact hj
        }
      | succ j ih => {
          have hraw :
              Iterate (RawStep p) (j + 1) n =
                RawStep p (Iterate (RawStep p) j n) := rfl
          rw [hraw] at hj
          have hprev :=
            (RawStepZeroIff p hQ hC hD
              (Iterate (RawStep p) j n)).mp hj
          exact ih n hprev
        }
    }
  · {
      intro hn
      refine ⟨0, ?_⟩
      rw [hn]
      rfl
    }

/-- The one-step preimage of `-1` is `{-1,-3}`. -/
theorem RawStepNegOneIff (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    RawStep p n = -1 ↔ n = -1 ∨ n = -3 := by
  constructor
  · {
      intro h
      by_cases hd : p.D ∣ n
      · {
          have hquot : n / p.D = -1 := by
            rw [RawStep, if_pos hd] at h
            exact h
          have hrec := Int.emod_add_mul_ediv n p.D
          have hmod : n % p.D = 0 := (Int.dvd_iff_emod_eq_zero).mp hd
          rw [hmod, hquot, hD] at hrec
          omega
        }
      · {
          rw [RawStep, if_neg hd, hQ, hC] at h
          omega
        }
    }
  · {
      intro h
      rcases h with hn | hn
      · {
          have hnd : ¬ p.D ∣ (-1 : ℤ) := by
            rw [hD]
            intro hd
            have hrec := Int.emod_add_mul_ediv (-1 : ℤ) (3 : ℤ)
            have hmod : (-1 : ℤ) % 3 = 0 :=
              (Int.dvd_iff_emod_eq_zero).mp hd
            rw [hmod] at hrec
            omega
          rw [hn, RawStep, if_neg hnd, hQ, hC]
          ring
        }
      · {
          have hd : p.D ∣ (-3 : ℤ) := by
            rw [hD]
            refine ⟨-1, ?_⟩
            ring
          rw [hn, RawStep, if_pos hd, hD]
          have hrec := Int.emod_add_mul_ediv (-3 : ℤ) (3 : ℤ)
          have hmod : (-3 : ℤ) % 3 = 0 := by decide
          rw [hmod, zero_add] at hrec
          apply mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0)
          rw [hrec]
          ring
        }
    }

/-- Every value has the division preimage `3a`, and an affine preimage
only when `a` is odd and that candidate is not divisible by `3`. -/
theorem RawStepPreimage (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n a : ℤ) :
    RawStep p n = a ↔
      n = 3 * a ∨
        (¬ (3 : ℤ) ∣ n ∧ (2 : ℤ) ∣ (a - 1) ∧ n = (a - 1) / 2) := by
  constructor
  · {
      intro h
      by_cases hd : p.D ∣ n
      · {
          have hquot : n / p.D = a := by
            rw [RawStep, if_pos hd] at h
            exact h
          have hrec := Int.emod_add_mul_ediv n p.D
          have hmod : n % p.D = 0 := (Int.dvd_iff_emod_eq_zero).mp hd
          rw [hmod, hquot, hD, zero_add] at hrec
          left
          apply mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0)
          rw [hrec]
        }
      · {
          have haff : (2 : ℤ) * n + 1 = a := by
            rw [RawStep, if_neg hd, hQ, hC] at h
            exact h
          have hnd : ¬ (3 : ℤ) ∣ n := by
            rw [hD] at hd
            exact hd
          right
          refine ⟨hnd, ?_, ?_⟩
          · {
              refine ⟨n, ?_⟩
              omega
            }
          · {
              have hrec := Int.emod_add_mul_ediv (a - 1) (2 : ℤ)
              have hdiv : (2 : ℤ) ∣ (a - 1) := ⟨n, by omega⟩
              have hmod : (a - 1) % 2 = 0 :=
                (Int.dvd_iff_emod_eq_zero).mp hdiv
              rw [hmod, zero_add] at hrec
              apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
              rw [hrec]
              omega
            }
        }
    }
  · {
      intro h
      rcases h with hn | ⟨hnd, hdv, hn⟩
      · {
          have hd : p.D ∣ n := by
            rw [hn, hD]
            refine ⟨a, ?_⟩
            ring
          rw [RawStep, if_pos hd, hn, hD]
          have hrec := Int.emod_add_mul_ediv (3 * a) (3 : ℤ)
          have hmod : (3 * a) % 3 = 0 := by
            have hd3 : (3 : ℤ) ∣ 3 * a := ⟨a, by ring⟩
            exact (Int.dvd_iff_emod_eq_zero).mp hd3
          rw [hmod, zero_add] at hrec
          apply mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0)
          rw [hrec]
        }
      · {
          have hd : ¬ p.D ∣ n := by
            rw [hD]
            exact hnd
          rw [RawStep, if_neg hd, hQ, hC]
          have hrec := Int.emod_add_mul_ediv (a - 1) (2 : ℤ)
          have hmod : (a - 1) % 2 = 0 :=
            (Int.dvd_iff_emod_eq_zero).mp hdv
          rw [hmod, zero_add] at hrec
          rw [hn]
          omega
        }
    }

/-- The only input sent to `1` is `3`. -/
theorem RawStepEqOneIff (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    RawStep p n = 1 ↔ n = 3 := by
  constructor
  · {
      intro h
      rcases (RawStepPreimage p hQ hC hD n 1).mp h with hn | haff
      · {
          omega
        }
      · {
          rcases haff with ⟨hnd, _hdv, hn⟩
          have hz : n = 0 := by
            rw [hn]
            decide
          rw [hz] at hnd
          exact False.elim (hnd (dvd_zero _))
        }
    }
  · {
      intro hn
      exact (RawStepPreimage p hQ hC hD n 1).mpr (Or.inl (by omega))
    }

/-- The inputs sent to `3` are `1` and `9`. -/
theorem RawStepEqThreeIff (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    RawStep p n = 3 ↔ n = 1 ∨ n = 9 := by
  constructor
  · {
      intro h
      rcases (RawStepPreimage p hQ hC hD n 3).mp h with hn | haff
      · {
          right
          omega
        }
      · {
          rcases haff with ⟨_hnd, _hdv, hn⟩
          left
          rw [hn]
          decide
        }
    }
  · {
      intro h
      rcases h with hn | hn
      · {
          apply (RawStepPreimage p hQ hC hD n 3).mpr
          right
          refine ⟨?_, ?_, ?_⟩
          · {
              rw [hn]
              decide
            }
          · {
              decide
            }
          · {
              rw [hn]
              decide
            }
        }
      · {
          exact (RawStepPreimage p hQ hC hD n 3).mpr
            (Or.inl (by omega))
        }
    }

/-- A first visit to `1` at time at least `2` passes through `9`, then `3`. -/
theorem EntryThroughNine (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (j : ℕ) (hj : 2 ≤ j)
    (hhit : Iterate (RawStep p) j n = 1)
    (hmin : ∀ i : ℕ, i < j → Iterate (RawStep p) i n ≠ 1) :
    Iterate (RawStep p) (j - 1) n = 3 ∧
      Iterate (RawStep p) (j - 2) n = 9 := by
  have hpos : 1 ≤ j := by omega
  have hsum : (j - 1) + 1 = j := Nat.sub_add_cancel hpos
  have hstep :
      Iterate (RawStep p) j n =
        RawStep p (Iterate (RawStep p) (j - 1) n) := by
    conv_lhs => rw [← hsum]
    rfl
  rw [hstep] at hhit
  have hprev :=
    (RawStepEqOneIff p hQ hC hD _).mp hhit
  refine ⟨hprev, ?_⟩
  have htwo : 1 ≤ j - 1 := by omega
  have hsum2 : (j - 2) + 1 = j - 1 := Nat.sub_add_cancel htwo
  have hstep2 :
      Iterate (RawStep p) (j - 1) n =
        RawStep p (Iterate (RawStep p) (j - 2) n) := by
    conv_lhs => rw [← hsum2]
    rfl
  rw [hprev] at hstep2
  have hgate :=
    (RawStepEqThreeIff p hQ hC hD _).mp hstep2.symm
  rcases hgate with hone | hnine
  · {
      have hlt : j - 2 < j := by omega
      exact False.elim (hmin (j - 2) hlt hone)
    }
  · {
      exact hnine
    }

/-- A first visit to `-1` at a positive time passes through `-3`. -/
theorem EntryThroughNegThree (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (j : ℕ) (hj : 1 ≤ j)
    (hhit : Iterate (RawStep p) j n = -1)
    (hmin : ∀ i : ℕ, i < j → Iterate (RawStep p) i n ≠ -1) :
    Iterate (RawStep p) (j - 1) n = -3 := by
  have hsum : (j - 1) + 1 = j := Nat.sub_add_cancel hj
  have hstep :
      Iterate (RawStep p) j n =
        RawStep p (Iterate (RawStep p) (j - 1) n) := by
    conv_lhs => rw [← hsum]
    rfl
  rw [hstep] at hhit
  rcases (RawStepNegOneIff p hQ hC hD _).mp hhit with hfix | hgate
  · {
      have hlt : j - 1 < j := by omega
      exact False.elim (hmin (j - 1) hlt hfix)
    }
  · {
      exact hgate
    }

/-- If the affine test fails, the only preimage is the division branch. -/
theorem OnlyDivisionPreimage (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n a : ℤ)
    (hmiss : ¬ ((2 : ℤ) ∣ (a - 1) ∧ ¬ (3 : ℤ) ∣ ((a - 1) / 2))) :
    RawStep p n = a ↔ n = 3 * a := by
  constructor
  · {
      intro h
      rcases (RawStepPreimage p hQ hC hD n a).mp h with hn | haff
      · {
          exact hn
        }
      · {
          rcases haff with ⟨hnd, hdv, hn⟩
          exfalso
          apply hmiss
          refine ⟨hdv, ?_⟩
          rw [← hn]
          exact hnd
        }
    }
  · {
      intro hn
      exact (RawStepPreimage p hQ hC hD n a).mpr (Or.inl hn)
    }

/-- The affine test produces a second preimage, unequal to `3a`. -/
theorem AffinePreimageIff (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (a : ℤ) :
    ((2 : ℤ) ∣ (a - 1) ∧ ¬ (3 : ℤ) ∣ ((a - 1) / 2)) ↔
      RawStep p ((a - 1) / 2) = a ∧ (a - 1) / 2 ≠ 3 * a := by
  constructor
  · {
      intro h
      rcases h with ⟨hdv, hnd⟩
      refine ⟨?_, ?_⟩
      · {
          exact (RawStepPreimage p hQ hC hD ((a - 1) / 2) a).mpr
            (Or.inr ⟨hnd, hdv, rfl⟩)
        }
      · {
          intro heq
          apply hnd
          rw [heq]
          refine ⟨a, ?_⟩
          ring
        }
    }
  · {
      intro h
      rcases h with ⟨hstep, hne⟩
      rcases (RawStepPreimage p hQ hC hD ((a - 1) / 2) a).mp hstep with
        hn | haff
      · {
          exact False.elim (hne hn)
        }
      · {
          rcases haff with ⟨hnd, hdv, _hn⟩
          exact ⟨hdv, hnd⟩
        }
    }

/-- The affine branch is open exactly for residues `3` and `5` modulo `6`. -/
theorem BranchModSix (a : ℤ) :
    ((2 : ℤ) ∣ (a - 1) ∧ ¬ (3 : ℤ) ∣ ((a - 1) / 2)) ↔
      a % 6 = 3 ∨ a % 6 = 5 := by
  set q : ℤ := a / 6
  set r : ℤ := a % 6
  have hrec : r + 6 * q = a := by
    simpa [q, r] using Int.emod_add_mul_ediv a (6 : ℤ)
  have hnonneg : 0 ≤ r := by
    simpa [r] using Int.emod_nonneg a (by decide)
  have hlt : r < 6 := by
    simpa [r] using Int.emod_lt_of_pos a (by decide : (0 : ℤ) < 6)
  have hsplit : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by
    omega
  have hback : a = r + 6 * q := hrec.symm
  constructor
  · {
      intro h
      rcases h with ⟨hdv, hnd⟩
      rcases hsplit with h0 | h1 | h2 | h3 | h4 | h5
      · {
          exfalso
          have hodd : ¬ (2 : ℤ) ∣ (a - 1) := by
            intro hd
            have heven : (2 : ℤ) ∣ (6 * q) := ⟨3 * q, by ring⟩
            have hsum : a - 1 = (r - 1) + 6 * q := by
              rw [hback]
              ring
            rw [hsum] at hd
            have hrest : (2 : ℤ) ∣ (r - 1) :=
              (dvd_add_left heven).mp hd
            rw [h0] at hrest
            exact absurd hrest (by decide)
          exact hodd hdv
        }
      · {
          exfalso
          have heq : a - 1 = 2 * (3 * q) := by
            rw [hback, h1]
            ring
          have hmul :=
            Int.mul_ediv_cancel_left (3 * q) (by decide : (2 : ℤ) ≠ 0)
          rw [← heq] at hmul
          exact hnd ⟨q, hmul⟩
        }
      · {
          exfalso
          have hodd : ¬ (2 : ℤ) ∣ (a - 1) := by
            intro hd
            have heven : (2 : ℤ) ∣ (6 * q) := ⟨3 * q, by ring⟩
            have hsum : a - 1 = (r - 1) + 6 * q := by
              rw [hback]
              ring
            rw [hsum] at hd
            have hrest : (2 : ℤ) ∣ (r - 1) :=
              (dvd_add_left heven).mp hd
            rw [h2] at hrest
            exact absurd hrest (by decide)
          exact hodd hdv
        }
      · {
          left
          exact h3
        }
      · {
          exfalso
          have hodd : ¬ (2 : ℤ) ∣ (a - 1) := by
            intro hd
            have heven : (2 : ℤ) ∣ (6 * q) := ⟨3 * q, by ring⟩
            have hsum : a - 1 = (r - 1) + 6 * q := by
              rw [hback]
              ring
            rw [hsum] at hd
            have hrest : (2 : ℤ) ∣ (r - 1) :=
              (dvd_add_left heven).mp hd
            rw [h4] at hrest
            exact absurd hrest (by decide)
          exact hodd hdv
        }
      · {
          right
          exact h5
        }
    }
  · {
      intro h
      rcases h with h3 | h5
      · {
          refine ⟨?_, ?_⟩
          · {
              refine ⟨3 * q + 1, ?_⟩
              rw [hback, h3]
              ring
            }
          · {
              intro hd
              have heq : a - 1 = 2 * (3 * q + 1) := by
                rw [hback, h3]
                ring
              have hmul :=
                Int.mul_ediv_cancel_left (3 * q + 1)
                  (by decide : (2 : ℤ) ≠ 0)
              rw [← heq] at hmul
              rw [hmul] at hd
              have hthree : (3 : ℤ) ∣ (3 * q) := ⟨q, by ring⟩
              have hd' : (3 : ℤ) ∣ 1 + 3 * q := by
                rw [add_comm]
                exact hd
              exact absurd ((dvd_add_left hthree).mp hd') (by decide)
            }
        }
      · {
          refine ⟨?_, ?_⟩
          · {
              refine ⟨3 * q + 2, ?_⟩
              rw [hback, h5]
              ring
            }
          · {
              intro hd
              have heq : a - 1 = 2 * (3 * q + 2) := by
                rw [hback, h5]
                ring
              have hmul :=
                Int.mul_ediv_cancel_left (3 * q + 2)
                  (by decide : (2 : ℤ) ≠ 0)
              rw [← heq] at hmul
              rw [hmul] at hd
              have hthree : (3 : ℤ) ∣ (3 * q) := ⟨q, by ring⟩
              have hd' : (3 : ℤ) ∣ 2 + 3 * q := by
                rw [add_comm]
                exact hd
              exact absurd ((dvd_add_left hthree).mp hd') (by decide)
            }
        }
    }

/-- Every preimage is `3a`, plus the affine candidate on residues `3` and `5`. -/
theorem PreimageByResidue (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n a : ℤ) :
    RawStep p n = a ↔
      n = 3 * a ∨
        ((a % 6 = 3 ∨ a % 6 = 5) ∧ n = (a - 1) / 2) := by
  constructor
  · {
      intro h
      rcases (RawStepPreimage p hQ hC hD n a).mp h with hn | haff
      · {
          exact Or.inl hn
        }
      · {
          rcases haff with ⟨hnd, hdv, hn⟩
          have hnot : ¬ (3 : ℤ) ∣ ((a - 1) / 2) := by
            rw [← hn]
            exact hnd
          exact Or.inr ⟨(BranchModSix a).mp ⟨hdv, hnot⟩, hn⟩
        }
    }
  · {
      intro h
      rcases h with hn | ⟨hres, hn⟩
      · {
          exact (RawStepPreimage p hQ hC hD n a).mpr (Or.inl hn)
        }
      · {
          have htest := (BranchModSix a).mpr hres
          have hstep := (AffinePreimageIff p hQ hC hD a).mp htest
          rw [hn]
          exact hstep.1
        }
    }

/-- A nonnegative remainder below `6` is unchanged by reduction modulo `6`. -/
theorem EmodOfSix (k r : ℤ) (h0 : 0 ≤ r) (h6 : r < 6) :
    (6 * k + r) % 6 = r := by
  have hself : (r + 6 * k) % 6 = r % 6 :=
    Int.add_mul_emod_self_left r 6 k
  have hr : r % 6 = r := Int.emod_eq_of_lt h0 h6
  have hcomm : 6 * k + r = r + 6 * k := by ring
  rw [hcomm, hself, hr]

/-- Tripling a residue `3` or `5` returns residue `3`. -/
theorem DivisionChildResidue (q : ℤ) :
    (3 * (6 * q + 3)) % 6 = 3 ∧ (3 * (6 * q + 5)) % 6 = 3 := by
  constructor
  · {
      have h : 3 * (6 * q + 3) = 6 * (3 * q + 1) + 3 := by ring
      rw [h]
      exact EmodOfSix (3 * q + 1) 3 (by decide) (by decide)
    }
  · {
      have h : 3 * (6 * q + 5) = 6 * (3 * q + 2) + 3 := by ring
      rw [h]
      exact EmodOfSix (3 * q + 2) 3 (by decide) (by decide)
    }

/-- The affine child of residue `3` is residue `1` or `4`, hence does not branch. -/
theorem AffineChildOfThree (q : ℤ) :
    ((2 : ℤ) ∣ q → ((6 * q + 3 - 1) / 2) % 6 = 1) ∧
      ((2 : ℤ) ∣ (q - 1) → ((6 * q + 3 - 1) / 2) % 6 = 4) := by
  constructor
  · {
      intro hq
      obtain ⟨k, hk⟩ := hq
      have hshift : 6 * q + 3 - 1 = 6 * q + 2 := by ring
      have heq : 6 * q + 2 = 2 * (6 * k + 1) := by
        rw [hk]
        ring
      have hdiv :=
        Int.mul_ediv_cancel_left (6 * k + 1) (by decide : (2 : ℤ) ≠ 0)
      rw [← heq, ← hshift] at hdiv
      rw [hdiv]
      exact EmodOfSix k 1 (by decide) (by decide)
    }
  · {
      intro hq
      obtain ⟨k, hk⟩ := hq
      have hshift : 6 * q + 3 - 1 = 6 * q + 2 := by ring
      have hq1 : q = (q - 1) + 1 := by ring
      have heq : 6 * q + 2 = 2 * (6 * k + 4) := by
        rw [hq1, hk]
        ring
      have hdiv :=
        Int.mul_ediv_cancel_left (6 * k + 4) (by decide : (2 : ℤ) ≠ 0)
      rw [← heq, ← hshift] at hdiv
      rw [hdiv]
      exact EmodOfSix k 4 (by decide) (by decide)
    }

/-- The affine child of residue `5` is residue `2` or `5`. -/
theorem AffineChildOfFive (q : ℤ) :
    ((2 : ℤ) ∣ q → ((6 * q + 5 - 1) / 2) % 6 = 2) ∧
      ((2 : ℤ) ∣ (q - 1) → ((6 * q + 5 - 1) / 2) % 6 = 5) := by
  constructor
  · {
      intro hq
      obtain ⟨k, hk⟩ := hq
      have hshift : 6 * q + 5 - 1 = 6 * q + 4 := by ring
      have heq : 6 * q + 4 = 2 * (6 * k + 2) := by
        rw [hk]
        ring
      have hdiv :=
        Int.mul_ediv_cancel_left (6 * k + 2) (by decide : (2 : ℤ) ≠ 0)
      rw [← heq, ← hshift] at hdiv
      rw [hdiv]
      exact EmodOfSix k 2 (by decide) (by decide)
    }
  · {
      intro hq
      obtain ⟨k, hk⟩ := hq
      have hshift : 6 * q + 5 - 1 = 6 * q + 4 := by ring
      have hq1 : q = (q - 1) + 1 := by ring
      have heq : 6 * q + 4 = 2 * (6 * k + 5) := by
        rw [hq1, hk]
        ring
      have hdiv :=
        Int.mul_ediv_cancel_left (6 * k + 5) (by decide : (2 : ℤ) ≠ 0)
      rw [← heq, ← hshift] at hdiv
      rw [hdiv]
      exact EmodOfSix k 5 (by decide) (by decide)
    }

/-- Tripling and then dividing once recovers the original integer. -/
theorem StepOfTriple (p : Parameters) (hD : p.D = 3) (m : ℤ) :
    RawStep p (3 * m) = m := by
  have hd : p.D ∣ 3 * m := by
    rw [hD]
    refine ⟨m, ?_⟩
    ring
  rw [RawStep, if_pos hd, hD]
  exact Int.mul_ediv_cancel_left m (by decide : (3 : ℤ) ≠ 0)

/-- `k` divisions send `3 ^ k * a` back to `a`. -/
theorem TriplePowerReturns (p : Parameters) (hD : p.D = 3)
    (a : ℤ) (k : ℕ) :
    Iterate (RawStep p) k ((3 : ℤ) ^ k * a) = a := by
  induction k with
  | zero => {
      have h0 : (3 : ℤ) ^ 0 * a = a := by simp [pow_zero]
      rw [h0]
      rfl
    }
  | succ k ih => {
      have hpow :
          (3 : ℤ) ^ (k + 1) * a = 3 * ((3 : ℤ) ^ k * a) := by
        ring
      rw [hpow]
      have hstep := StepOfTriple p hD ((3 : ℤ) ^ k * a)
      have hone :
          Iterate (RawStep p) 1 (3 * ((3 : ℤ) ^ k * a)) =
            RawStep p (3 * ((3 : ℤ) ^ k * a)) := rfl
      have hiter :
          Iterate (RawStep p) (k + 1) (3 * ((3 : ℤ) ^ k * a)) =
            Iterate (RawStep p) k
              (RawStep p (3 * ((3 : ℤ) ^ k * a))) := by
        conv_lhs => rw [← Nat.add_comm]
        rw [IterateAdd, hone]
      rw [hiter, hstep]
      exact ih
    }

/-- `3 ^ n` is strictly larger than `n`. -/
theorem NatLtThreePow (n : ℕ) : n < 3 ^ n := by
  induction n with
  | zero => {
      decide
    }
  | succ n ih => {
      have hle : n + 1 ≤ 3 ^ n := by omega
      have hpos : 0 < 3 ^ n :=
        Nat.pos_of_ne_zero (pow_ne_zero n (by decide))
      have hmul : 3 ^ n * 1 < 3 ^ n * 3 :=
        (Nat.mul_lt_mul_left hpos).mpr (by decide)
      have hsucc : 3 ^ (n + 1) = 3 ^ n * 3 := Nat.pow_succ 3 n
      omega
    }

/-- Every nonzero value is reached by seeds of arbitrarily large size. -/
theorem InfinitePreimages (p : Parameters) (hD : p.D = 3)
    (a : ℤ) (ha : a ≠ 0) (N : ℕ) :
    ∃ n : ℤ, N < n.natAbs ∧
      ∃ k : ℕ, Iterate (RawStep p) k n = a := by
  refine ⟨(3 : ℤ) ^ N * a, ?_, N, ?_⟩
  · {
      rw [Int.natAbs_mul, Int.natAbs_pow]
      rw [show (3 : ℤ).natAbs = 3 by decide]
      have hpos : 0 < a.natAbs := Int.natAbs_pos.mpr ha
      have hge : 3 ^ N ≤ 3 ^ N * a.natAbs :=
        Nat.le_mul_of_pos_right (3 ^ N) hpos
      have hlt : N < 3 ^ N := NatLtThreePow N
      omega
    }
  · {
      exact TriplePowerReturns p hD a N
    }

/-- Two steps send `9` to `1`. -/
theorem NineToOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    Iterate (RawStep p) 2 (9 : ℤ) = 1 := by
  have hnine : RawStep p 9 = 3 :=
    (RawStepEqThreeIff p hQ hC hD 9).mpr (Or.inr rfl)
  have hthree : RawStep p 3 = 1 :=
    (RawStepEqOneIff p hQ hC hD 3).mpr rfl
  have hone : Iterate (RawStep p) 1 (9 : ℤ) = RawStep p 9 := rfl
  have htwo :
      Iterate (RawStep p) 2 (9 : ℤ) =
        RawStep p (Iterate (RawStep p) 1 (9 : ℤ)) := rfl
  rw [htwo, hone, hnine, hthree]

/-- One step sends `-3` to `-1`. -/
theorem NegThreeToNegOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    Iterate (RawStep p) 1 (-3 : ℤ) = -1 := by
  have hgate : RawStep p (-3) = -1 :=
    (RawStepNegOneIff p hQ hC hD (-3)).mpr (Or.inr rfl)
  have hone : Iterate (RawStep p) 1 (-3 : ℤ) = RawStep p (-3) := rfl
  rw [hone, hgate]

/-- Outside the cycle, meeting `1` is the same as meeting `9`. -/
theorem ExternalCycleIffNine (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    ((∃ j : ℕ, Iterate (RawStep p) j n = 1) ∧ n ≠ 1 ∧ n ≠ 3) ↔
      ∃ j : ℕ, Iterate (RawStep p) j n = 9 := by
  classical
  constructor
  · {
      intro h
      rcases h with ⟨hex, hn1, hn3⟩
      let j := Nat.find hex
      have hj : Iterate (RawStep p) j n = 1 := Nat.find_spec hex
      have hmin : ∀ i : ℕ, i < j → Iterate (RawStep p) i n ≠ 1 := by
        intro i hi
        exact Nat.find_min hex hi
      have hpos : 0 < j := by
        by_contra hzero
        have hj0 : j = 0 := by omega
        have hbase : Iterate (RawStep p) 0 n = n := rfl
        rw [hj0, hbase] at hj
        exact hn1 hj
      have hnot : j ≠ 1 := by
        intro hj1
        have hstep : Iterate (RawStep p) 1 n = RawStep p n := rfl
        rw [hj1, hstep] at hj
        exact hn3 ((RawStepEqOneIff p hQ hC hD n).mp hj)
      have hge : 2 ≤ j := by omega
      exact ⟨j - 2, (EntryThroughNine p hQ hC hD n j hge hj hmin).2⟩
    }
  · {
      intro h
      obtain ⟨j, hj⟩ := h
      have hreach :
          Iterate (RawStep p) (j + 2) n =
            Iterate (RawStep p) 2 (Iterate (RawStep p) j n) := by
        rw [IterateAdd]
      rw [hj, NineToOne p hQ hC hD] at hreach
      refine ⟨⟨j + 2, hreach⟩, ?_, ?_⟩
      · {
          intro hn
          rw [hn] at hj
          rcases ImageOfOne p hQ hC hD j with hone | hthree
          · {
              omega
            }
          · {
              omega
            }
        }
      · {
          intro hn
          have hthree : RawStep p 3 = 1 :=
            (RawStepEqOneIff p hQ hC hD 3).mpr rfl
          rw [hn] at hj
          cases j with
          | zero => {
              have hbase : Iterate (RawStep p) 0 (3 : ℤ) = 3 := rfl
              rw [hbase] at hj
              omega
            }
          | succ k => {
              have hone :
                  Iterate (RawStep p) 1 (3 : ℤ) = RawStep p 3 := rfl
              have hiter :
                  Iterate (RawStep p) (k + 1) (3 : ℤ) =
                    Iterate (RawStep p) k (RawStep p 3) := by
                conv_lhs => rw [← Nat.add_comm]
                rw [IterateAdd, hone]
              rw [hiter, hthree] at hj
              rcases ImageOfOne p hQ hC hD k with hone | hthree'
              · {
                  omega
                }
              · {
                  omega
                }
            }
        }
    }

/-- Outside the fixed point, meeting `-1` is the same as meeting `-3`. -/
theorem ExternalFixedIffNegThree (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    ((∃ j : ℕ, Iterate (RawStep p) j n = -1) ∧ n ≠ -1) ↔
      ∃ j : ℕ, Iterate (RawStep p) j n = -3 := by
  classical
  constructor
  · {
      intro h
      rcases h with ⟨hex, hne⟩
      let j := Nat.find hex
      have hj : Iterate (RawStep p) j n = -1 := Nat.find_spec hex
      have hmin : ∀ i : ℕ, i < j → Iterate (RawStep p) i n ≠ -1 := by
        intro i hi
        exact Nat.find_min hex hi
      have hpos : 1 ≤ j := by
        by_contra hzero
        have hj0 : j = 0 := by omega
        have hbase : Iterate (RawStep p) 0 n = n := rfl
        rw [hj0, hbase] at hj
        exact hne hj
      exact ⟨j - 1, EntryThroughNegThree p hQ hC hD n j hpos hj hmin⟩
    }
  · {
      intro h
      obtain ⟨j, hj⟩ := h
      have hreach :
          Iterate (RawStep p) (j + 1) n =
            Iterate (RawStep p) 1 (Iterate (RawStep p) j n) := by
        rw [IterateAdd]
      rw [hj, NegThreeToNegOne p hQ hC hD] at hreach
      refine ⟨⟨j + 1, hreach⟩, ?_⟩
      intro hn
      rw [hn] at hj
      have hfix := OrbitNegOne p hQ hC hD j
      rw [hj] at hfix
      omega
    }

/-- The orbit of `9` returns to `9` only at time zero. -/
theorem NineNotRevisited (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (k : ℕ)
    (h : Iterate (RawStep p) k (9 : ℤ) = 9) : k = 0 := by
  cases k with
  | zero => {
      rfl
    }
  | succ t => {
      cases t with
      | zero => {
          have hone : Iterate (RawStep p) 1 (9 : ℤ) = RawStep p 9 := rfl
          have hnine : RawStep p 9 = 3 :=
            (RawStepEqThreeIff p hQ hC hD 9).mpr (Or.inr rfl)
          rw [hone, hnine] at h
          omega
        }
      | succ m => {
          have hsum : 2 + m = m + 2 := Nat.add_comm 2 m
          have hreach :
              Iterate (RawStep p) (m + 2) (9 : ℤ) =
                Iterate (RawStep p) m (Iterate (RawStep p) 2 (9 : ℤ)) := by
            conv_lhs => rw [← hsum]
            rw [IterateAdd]
          rw [hreach, NineToOne p hQ hC hD] at h
          rcases ImageOfOne p hQ hC hD m with hone | hthree
          · {
              omega
            }
          · {
              omega
            }
        }
    }

/-- The value `9` occurs at most once on an orbit. -/
theorem NineAppearsAtMostOnce (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (i j : ℕ) (hi : Iterate (RawStep p) i n = 9)
    (hj : Iterate (RawStep p) j n = 9) : i = j := by
  rcases Nat.le_total i j with hij | hji
  · {
      have hsum : i + (j - i) = j := Nat.add_sub_of_le hij
      have hreach :
          Iterate (RawStep p) j n =
            Iterate (RawStep p) (j - i) (Iterate (RawStep p) i n) := by
        conv_lhs => rw [← hsum]
        rw [IterateAdd]
      rw [hreach, hi] at hj
      have hzero := NineNotRevisited p hQ hC hD (j - i) hj
      omega
    }
  · {
      have hsum : j + (i - j) = i := Nat.add_sub_of_le hji
      have hreach :
          Iterate (RawStep p) i n =
            Iterate (RawStep p) (i - j) (Iterate (RawStep p) j n) := by
        conv_lhs => rw [← hsum]
        rw [IterateAdd]
      rw [hreach, hj] at hi
      have hzero := NineNotRevisited p hQ hC hD (i - j) hi
      omega
    }

/-- The orbit of `-3` returns to `-3` only at time zero. -/
theorem NegThreeNotRevisited (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (k : ℕ)
    (h : Iterate (RawStep p) k (-3 : ℤ) = -3) : k = 0 := by
  cases k with
  | zero => {
      rfl
    }
  | succ m => {
      have hreach :
          Iterate (RawStep p) (m + 1) (-3 : ℤ) =
            Iterate (RawStep p) m (Iterate (RawStep p) 1 (-3 : ℤ)) := by
        conv_lhs => rw [← Nat.add_comm]
        rw [IterateAdd]
      rw [hreach, NegThreeToNegOne p hQ hC hD,
        OrbitNegOne p hQ hC hD m] at h
      omega
    }

/-- The value `-3` occurs at most once on an orbit. -/
theorem NegThreeAppearsAtMostOnce (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (i j : ℕ) (hi : Iterate (RawStep p) i n = -3)
    (hj : Iterate (RawStep p) j n = -3) : i = j := by
  rcases Nat.le_total i j with hij | hji
  · {
      have hsum : i + (j - i) = j := Nat.add_sub_of_le hij
      have hreach :
          Iterate (RawStep p) j n =
            Iterate (RawStep p) (j - i) (Iterate (RawStep p) i n) := by
        conv_lhs => rw [← hsum]
        rw [IterateAdd]
      rw [hreach, hi] at hj
      have hzero := NegThreeNotRevisited p hQ hC hD (j - i) hj
      omega
    }
  · {
      have hsum : j + (i - j) = i := Nat.add_sub_of_le hji
      have hreach :
          Iterate (RawStep p) i n =
            Iterate (RawStep p) (i - j) (Iterate (RawStep p) j n) := by
        conv_lhs => rw [← hsum]
        rw [IterateAdd]
      rw [hreach, hj] at hi
      have hzero := NegThreeNotRevisited p hQ hC hD (i - j) hi
      omega
    }

/-- Every seed reaching `g` lies in each inverse-closed set containing `g`. -/
theorem BasinGenerated (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (g : ℤ) (X : ℤ → Prop) (hgate : X g)
    (hdiv : ∀ a : ℤ, X a → X (3 * a))
    (haff : ∀ a : ℤ, X a → (a % 6 = 3 ∨ a % 6 = 5) →
      X ((a - 1) / 2))
    (n : ℤ) (h : ∃ j : ℕ, Iterate (RawStep p) j n = g) : X n := by
  classical
  have main : ∀ k : ℕ, ∀ n : ℤ,
      Iterate (RawStep p) k n = g →
        (∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ g) → X n := by
    intro k
    induction k with
    | zero => {
        intro n h0 _hmin
        have hbase : Iterate (RawStep p) 0 n = n := rfl
        rw [hbase] at h0
        rw [h0]
        exact hgate
      }
    | succ k ih => {
        intro n hhit hmin
        have hstep :
            Iterate (RawStep p) (k + 1) n =
              Iterate (RawStep p) k (RawStep p n) := by
          conv_lhs => rw [← Nat.add_comm]
          rw [IterateAdd]
          rfl
        rw [hstep] at hhit
        have hmin' : ∀ i : ℕ, i < k →
            Iterate (RawStep p) i (RawStep p n) ≠ g := by
          intro i hi hbad
          have hback :
              Iterate (RawStep p) (i + 1) n =
                Iterate (RawStep p) i (RawStep p n) := by
            conv_lhs => rw [← Nat.add_comm]
            rw [IterateAdd]
            rfl
          rw [← hback] at hbad
          exact hmin (i + 1) (Nat.succ_lt_succ hi) hbad
        have hX := ih (RawStep p n) hhit hmin'
        have hpre :=
          (PreimageByResidue p hQ hC hD n (RawStep p n)).mp rfl
        rcases hpre with hn | ⟨hres, hn⟩
        · {
            rw [hn]
            exact hdiv (RawStep p n) hX
          }
        · {
            rw [hn]
            exact haff (RawStep p n) hX hres
          }
      }
  let j := Nat.find h
  exact main j n (Nat.find_spec h) (fun i hi => Nat.find_min h hi)

/-- Tripling a seed delays a hit of `g` by one exact division. -/
theorem ReachesClosedDivision (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (g a : ℤ) (h : ∃ j : ℕ, Iterate (RawStep p) j a = g) :
    ∃ j : ℕ, Iterate (RawStep p) j (3 * a) = g := by
  obtain ⟨j, hj⟩ := h
  have hstep : RawStep p (3 * a) = a :=
    (PreimageByResidue p hQ hC hD (3 * a) a).mpr (Or.inl rfl)
  refine ⟨j + 1, ?_⟩
  have hsum : j + 1 = 1 + j := Nat.add_comm j 1
  have hreach :
      Iterate (RawStep p) (j + 1) (3 * a) =
        Iterate (RawStep p) j (RawStep p (3 * a)) := by
    rw [hsum, IterateAdd]
    rfl
  rw [hreach, hstep, hj]

/-- A legal affine child delays a hit of `g` by one affine step. -/
theorem ReachesClosedAffine (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (g a : ℤ) (hres : a % 6 = 3 ∨ a % 6 = 5)
    (h : ∃ j : ℕ, Iterate (RawStep p) j a = g) :
    ∃ j : ℕ, Iterate (RawStep p) j ((a - 1) / 2) = g := by
  obtain ⟨j, hj⟩ := h
  have hstep : RawStep p ((a - 1) / 2) = a :=
    (PreimageByResidue p hQ hC hD ((a - 1) / 2) a).mpr
      (Or.inr ⟨hres, rfl⟩)
  refine ⟨j + 1, ?_⟩
  have hsum : j + 1 = 1 + j := Nat.add_comm j 1
  have hreach :
      Iterate (RawStep p) (j + 1) ((a - 1) / 2) =
        Iterate (RawStep p) j (RawStep p ((a - 1) / 2)) := by
    rw [hsum, IterateAdd]
    rfl
  rw [hreach, hstep, hj]

/-- Reaching `g` is exactly membership in every inverse-closed set. -/
theorem ReachesIffGenerated (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (g n : ℤ) :
    (∃ j : ℕ, Iterate (RawStep p) j n = g) ↔
      ∀ X : ℤ → Prop, X g →
        (∀ a : ℤ, X a → X (3 * a)) →
          (∀ a : ℤ, X a → (a % 6 = 3 ∨ a % 6 = 5) →
            X ((a - 1) / 2)) →
            X n := by
  constructor
  · {
      intro h X hgate hdiv haff
      exact BasinGenerated p hQ hC hD g X hgate hdiv haff n h
    }
  · {
      intro h
      exact h (fun m => ∃ j : ℕ, Iterate (RawStep p) j m = g)
        ⟨0, rfl⟩
        (fun a ha => ReachesClosedDivision p hQ hC hD g a ha)
        (fun a ha hres =>
          ReachesClosedAffine p hQ hC hD g a hres ha)
    }

/-- A later hit is a hit on the tail of the earlier one. -/
theorem LaterHitOnTail (p : Parameters) (n g₁ g₂ : ℤ)
    (j k : ℕ) (hle : j ≤ k)
    (hj : Iterate (RawStep p) j n = g₁)
    (hk : Iterate (RawStep p) k n = g₂) :
    Iterate (RawStep p) (k - j) g₁ = g₂ := by
  have hsum : j + (k - j) = k := Nat.add_sub_of_le hle
  have heq :
      Iterate (RawStep p) (k - j) (Iterate (RawStep p) j n) =
        Iterate (RawStep p) k n := by
    conv_rhs => rw [← hsum]
    rw [IterateAdd]
  rw [hj, hk] at heq
  exact heq

/-- No orbit meets more than one of `0`, `1`, and `-1`. -/
theorem HitsAtMostOneTarget (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    ¬ ((∃ j : ℕ, Iterate (RawStep p) j n = 0) ∧
        (∃ k : ℕ, Iterate (RawStep p) k n = 1)) ∧
      ¬ ((∃ j : ℕ, Iterate (RawStep p) j n = 0) ∧
        (∃ k : ℕ, Iterate (RawStep p) k n = -1)) ∧
        ¬ ((∃ j : ℕ, Iterate (RawStep p) j n = 1) ∧
          (∃ k : ℕ, Iterate (RawStep p) k n = -1)) := by
  refine ⟨?_, ?_, ?_⟩
  · {
      intro h
      rcases h with ⟨⟨j, hj⟩, ⟨k, hk⟩⟩
      by_cases hle : j ≤ k
      · {
          have htail := LaterHitOnTail p n 0 1 j k hle hj hk
          rw [OrbitZero p hD (k - j)] at htail
          omega
        }
      · {
          have hlt : k < j := Nat.lt_of_not_ge hle
          have htail :=
            LaterHitOnTail p n 1 0 k j (Nat.le_of_lt hlt) hk hj
          rcases ImageOfOne p hQ hC hD (j - k) with h1 | h3
          · {
              rw [h1] at htail
              omega
            }
          · {
              rw [h3] at htail
              omega
            }
        }
    }
  · {
      intro h
      rcases h with ⟨⟨j, hj⟩, ⟨k, hk⟩⟩
      by_cases hle : j ≤ k
      · {
          have htail := LaterHitOnTail p n 0 (-1) j k hle hj hk
          rw [OrbitZero p hD (k - j)] at htail
          omega
        }
      · {
          have hlt : k < j := Nat.lt_of_not_ge hle
          have htail :=
            LaterHitOnTail p n (-1) 0 k j (Nat.le_of_lt hlt) hk hj
          rw [OrbitNegOne p hQ hC hD (j - k)] at htail
          omega
        }
    }
  · {
      intro h
      rcases h with ⟨⟨j, hj⟩, ⟨k, hk⟩⟩
      by_cases hle : j ≤ k
      · {
          have htail := LaterHitOnTail p n 1 (-1) j k hle hj hk
          rcases ImageOfOne p hQ hC hD (k - j) with h1 | h3
          · {
              rw [h1] at htail
              omega
            }
          · {
              rw [h3] at htail
              omega
            }
        }
      · {
          have hlt : k < j := Nat.lt_of_not_ge hle
          have htail :=
            LaterHitOnTail p n (-1) 1 k j (Nat.le_of_lt hlt) hk hj
          rw [OrbitNegOne p hQ hC hD (j - k)] at htail
          omega
        }
    }

/-- One exact return fixes the seed only at `0` and `1`. -/
theorem ReturnEqSeed (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (j : ℕ) (hhit : IsFirstHit p n j)
    (heq : RawStep p (Iterate (RawStep p) j n) = n) :
    n = 0 ∨ n = 1 := by
  have hper : ∃ k : ℕ, 0 < k ∧ Iterate (RawStep p) k n = n := by
    refine ⟨j + 1, Nat.succ_pos j, ?_⟩
    have hstep :
        Iterate (RawStep p) (j + 1) n =
          RawStep p (Iterate (RawStep p) j n) := rfl
    rw [hstep, heq]
  rcases (PeriodicPoints p hQ hC hD n).mp hper with
    h0 | hneg | h1 | h3
  · {
      exact Or.inl h0
    }
  · {
      rw [hneg] at hhit
      exact False.elim
        (RemainderTwoNoHit p hQ hC hD (-1) NegOneModThree j hhit)
    }
  · {
      exact Or.inr h1
    }
  · {
      have hzero :=
        HitAtZero p hQ hC hD 3 (Int.emod_self (a := (3 : ℤ)))
      cases j with
      | zero => {
          rw [h3] at heq
          have hret := hzero.2.2
          rw [hret, Int.ediv_self (by decide : (3 : ℤ) ≠ 0)] at heq
          omega
        }
      | succ t => {
          rw [h3] at hhit
          have hearly := hhit.2 0 (Nat.succ_pos t)
          exact False.elim (hearly hzero.1.1)
        }
    }

/-- Every first return of `3` is the quotient `1`. -/
theorem ReturnAtThree (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (j : ℕ) (h : IsFirstHit p (3 : ℤ) j) :
    RawStep p (Iterate (RawStep p) j (3 : ℤ)) = 1 := by
  have hzero :=
    HitAtZero p hQ hC hD 3 (Int.emod_self (a := (3 : ℤ)))
  have hj : j = 0 := FirstHitUnique p 3 j 0 h hzero.1
  subst hj
  rw [hzero.2.2, Int.ediv_self (by decide : (3 : ℤ) ≠ 0)]

/-- Every first return of `1` is `1`. -/
theorem ReturnAtOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (j : ℕ) (h : IsFirstHit p (1 : ℤ) j) :
    RawStep p (Iterate (RawStep p) j (1 : ℤ)) = 1 := by
  have hmod : (1 : ℤ) % 3 = 1 := by decide
  have hone := HitAtOne p hQ hC hD 1 hmod
  have hj : j = 1 := FirstHitUnique p 1 j 1 h hone.1
  subst hj
  rw [hone.2.2]
  decide

/-- A positive chain of returns closes only at `0` or `1`. -/
theorem ReturnChainAtFixedPoint (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (hm : 0 < m) (s : ℕ → ℤ)
    (h0 : s 0 = n) (hlast : s m = n)
    (hstep : ∀ i : ℕ, i < m → ∃ j : ℕ,
      IsFirstHit p (s i) j ∧
        RawStep p (Iterate (RawStep p) j (s i)) = s (i + 1)) :
    n = 0 ∨ n = 1 := by
  have onOrbit : ∀ i : ℕ, i ≤ m → ∃ t : ℕ,
      Iterate (RawStep p) t n = s i ∧ (0 < i → 0 < t) := by
    intro i hi
    induction i with
    | zero => {
        refine ⟨0, ?_, ?_⟩
        · {
            rw [h0]
            rfl
          }
        · {
            intro hlt
            omega
          }
      }
    | succ i ih => {
        have hlt : i < m := Nat.lt_of_succ_le hi
        obtain ⟨t, ht, _hpos⟩ := ih (Nat.le_of_lt hlt)
        obtain ⟨j, hhit, hret⟩ := hstep i hlt
        refine ⟨t + (j + 1), ?_, ?_⟩
        · {
            have hreach :
                Iterate (RawStep p) (t + (j + 1)) n =
                  RawStep p
                    (Iterate (RawStep p) j
                      (Iterate (RawStep p) t n)) := by
              rw [IterateAdd]
              rfl
            rw [hreach, ht, hret]
          }
        · {
            intro _
            exact Nat.succ_pos (t + j)
          }
      }
  obtain ⟨t, ht, hpos⟩ := onOrbit m (Nat.le_refl m)
  have hper : ∃ k : ℕ, 0 < k ∧ Iterate (RawStep p) k n = n := by
    refine ⟨t, hpos hm, ?_⟩
    rw [ht, hlast]
  rcases (PeriodicPoints p hQ hC hD n).mp hper with
    hzero | hneg | hone | hthree
  · {
      exact Or.inl hzero
    }
  · {
      have hbad := hstep 0 hm
      rcases hbad with ⟨j, hhit, _hret⟩
      rw [h0, hneg] at hhit
      exact False.elim
        (RemainderTwoNoHit p hQ hC hD (-1) NegOneModThree j hhit)
    }
  · {
      exact Or.inr hone
    }
  · {
      have tail : ∀ i : ℕ, 0 < i → i ≤ m → s i = 1 := by
        intro i hi hle
        induction i with
        | zero => {
            omega
          }
        | succ i ih => {
            have hlt : i < m := Nat.lt_of_succ_le hle
            obtain ⟨j, hhit, hret⟩ := hstep i hlt
            by_cases hiz : i = 0
            · {
                rw [hiz, h0, hthree] at hhit
                rw [hiz, h0, hthree] at hret
                rw [ReturnAtThree p hQ hC hD j hhit] at hret
                rw [hiz]
                exact hret.symm
              }
            · {
                have hipos : 0 < i := Nat.pos_of_ne_zero hiz
                have hprev := ih hipos (Nat.le_of_lt hlt)
                rw [hprev] at hhit
                rw [hprev] at hret
                rw [ReturnAtOne p hQ hC hD j hhit] at hret
                exact hret.symm
              }
          }
      have hsm := tail m hm (Nat.le_refl m)
      rw [hlast, hthree] at hsm
      omega
    }

/-- A raw division produces a first hit at or before that time. -/
theorem ExistsHitFromRawDivision (p : Parameters) (n : ℤ) (k : ℕ)
    (h : p.D ∣ Iterate (RawStep p) k n) :
    ∃ j : ℕ, j ≤ k ∧ IsFirstHit p n j := by
  classical
  have hex : ∃ t : ℕ, p.D ∣ Iterate (RawStep p) t n := ⟨k, h⟩
  let t := Nat.find hex
  have ht : p.D ∣ Iterate (RawStep p) t n := Nat.find_spec hex
  have hmin : ∀ i : ℕ, i < Nat.find hex →
      ¬ p.D ∣ Iterate (RawStep p) i n :=
    fun i hi => Nat.find_min hex hi
  have hle : t ≤ k := Nat.find_le h
  have hclean : ∀ i : ℕ, i < t →
      ¬ p.D ∣ AffineState p.Q p.C i n := by
    intro i hi hdiv
    have hexA : ∃ r : ℕ, r < t ∧ p.D ∣ AffineState p.Q p.C r n :=
      ⟨i, hi, hdiv⟩
    let r := Nat.find hexA
    have hr := Nat.find_spec hexA
    have hbefore : ∀ u : ℕ, u < r →
        ¬ p.D ∣ AffineState p.Q p.C u n := by
      intro u hu hbad
      exact Nat.find_min hexA hu ⟨Nat.lt_trans hu hr.1, hbad⟩
    have heq := PrefixEqualsAffine p n r hbefore
    have hraw : p.D ∣ Iterate (RawStep p) r n := by
      rw [heq]
      exact hr.2
    exact hmin r hr.1 hraw
  have heqt := PrefixEqualsAffine p n t hclean
  refine ⟨t, hle, ?_⟩
  refine ⟨?_, ?_⟩
  · {
      rw [← heqt]
      exact ht
    }
  · {
      intro i hi
      exact hclean i hi
    }

/-- The only raw preimage of `1` is `3`. -/
theorem OnlyPreimageOfOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (h : RawStep p n = 1) : n = 3 := by
  rcases (PreimageByResidue p hQ hC hD n 1).mp h with hn | ⟨hres, _hn⟩
  · {
      have hthree : (3 : ℤ) * 1 = 3 := by decide
      rw [← hthree]
      exact hn
    }
  · {
      have hbad : ¬ ((1 : ℤ) % 6 = 3 ∨ (1 : ℤ) % 6 = 5) := by
        decide
      exact False.elim (hbad hres)
    }

/-- The term immediately before a first visit to `1` is `3`. -/
theorem BeforeOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (k : ℕ) (hk : 0 < k)
    (h : Iterate (RawStep p) k n = 1) :
    Iterate (RawStep p) (k - 1) n = 3 := by
  have hsum : (k - 1) + 1 = k := Nat.sub_add_cancel hk
  have hstep :
      Iterate (RawStep p) k n =
        RawStep p (Iterate (RawStep p) (k - 1) n) := by
    conv_lhs => rw [← hsum]
    rw [IterateAdd]
    rfl
  rw [hstep] at h
  exact OnlyPreimageOfOne p hQ hC hD
    (Iterate (RawStep p) (k - 1) n) h

/-- Reaching `1` yields a finite chain of exact returns ending at `1`. -/
theorem ReturnChainToOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ k : ℕ, Iterate (RawStep p) k n = 1) :
    ∃ m : ℕ, ∃ s : ℕ → ℤ,
      s 0 = n ∧ s m = 1 ∧
        (∀ i : ℕ, i < m → s i ≠ 1) ∧
        ∀ i : ℕ, i < m → ∃ j : ℕ,
          IsFirstHit p (s i) j ∧
            RawStep p (Iterate (RawStep p) j (s i)) = s (i + 1) := by
  classical
  obtain ⟨k0, hk0⟩ := h
  let k := Nat.find (⟨k0, hk0⟩ : ∃ k, Iterate (RawStep p) k n = 1)
  have hk : Iterate (RawStep p) k n = 1 :=
    Nat.find_spec (⟨k0, hk0⟩ : ∃ k, Iterate (RawStep p) k n = 1)
  have hmin0 : ∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ 1 :=
    fun i hi =>
      Nat.find_min (⟨k0, hk0⟩ : ∃ k, Iterate (RawStep p) k n = 1) hi
  have main : ∀ k : ℕ, ∀ n : ℤ,
      Iterate (RawStep p) k n = 1 →
        (∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ 1) →
          ∃ m : ℕ, ∃ s : ℕ → ℤ,
            s 0 = n ∧ s m = 1 ∧
              (∀ i : ℕ, i < m → s i ≠ 1) ∧
              ∀ i : ℕ, i < m → ∃ j : ℕ,
                IsFirstHit p (s i) j ∧
                  RawStep p (Iterate (RawStep p) j (s i)) =
                    s (i + 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih => {
        intro n hk hmin
        cases k with
        | zero => {
            have hn : n = 1 := by
              have hbase : Iterate (RawStep p) 0 n = n := rfl
              rw [hbase] at hk
              exact hk
            refine ⟨0, fun _ => n, rfl, ?_, ?_, ?_⟩
            · {
                rw [hn]
              }
            · {
                intro i hi
                omega
              }
            · {
                intro i hi
                omega
              }
          }
        | succ kpred => {
            have hkpos : 0 < kpred + 1 := Nat.succ_pos kpred
            have hpred :=
              BeforeOne p hQ hC hD n (kpred + 1) hkpos hk
            have hdvd3 : (3 : ℤ) ∣ Iterate (RawStep p) kpred n := by
              have hidx : (kpred + 1) - 1 = kpred := by omega
              rw [hidx] at hpred
              rw [hpred]
            have hdvd : p.D ∣ Iterate (RawStep p) kpred n := by
              rw [hD]
              exact hdvd3
            obtain ⟨j, hjle, hhit⟩ :=
              ExistsHitFromRawDivision p n kpred hdvd
            have hret :
                Iterate (RawStep p) (j + 1) n =
                  RawStep p (Iterate (RawStep p) j n) := rfl
            have hrestle : j + 1 ≤ kpred + 1 := by omega
            let r := RawStep p (Iterate (RawStep p) j n)
            have hreach :
                Iterate (RawStep p) ((kpred + 1) - (j + 1)) r = 1 := by
              have hsum :
                  (j + 1) + ((kpred + 1) - (j + 1)) = kpred + 1 :=
                Nat.add_sub_of_le hrestle
              have hsplit :
                  Iterate (RawStep p) (kpred + 1) n =
                    Iterate (RawStep p) ((kpred + 1) - (j + 1))
                      (Iterate (RawStep p) (j + 1) n) := by
                conv_lhs => rw [← hsum]
                rw [IterateAdd]
              unfold r
              rw [← hret, ← hsplit]
              exact hk
            have hrestlt : (kpred + 1) - (j + 1) < kpred + 1 := by
              omega
            have hminr : ∀ i : ℕ, i < (kpred + 1) - (j + 1) →
                Iterate (RawStep p) i r ≠ 1 := by
              intro i hi hbad
              have hback :
                  Iterate (RawStep p) ((j + 1) + i) n =
                    Iterate (RawStep p) i r := by
                rw [IterateAdd, hret]
              have htime : (j + 1) + i < kpred + 1 := by omega
              rw [← hback] at hbad
              exact hmin ((j + 1) + i) htime hbad
            obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
              ih ((kpred + 1) - (j + 1)) hrestlt r hreach hminr
            let s' : ℕ → ℤ := fun i =>
              if i = 0 then n else s (i - 1)
            refine ⟨m + 1, s', ?_, ?_, ?_, ?_⟩
            · {
                rfl
              }
            · {
                have hpos : m + 1 ≠ 0 := by omega
                have hidx : (m + 1) - 1 = m := by omega
                simp [s', hidx, hsm]
              }
            · {
                intro i hi
                by_cases hiz : i = 0
                · {
                    intro hn
                    have hs' : s' i = n := by simp [s', hiz]
                    rw [hs'] at hn
                    have hbase : Iterate (RawStep p) 0 n = n := rfl
                    exact hmin 0 (Nat.succ_pos kpred)
                      (by rw [hbase, hn])
                  }
                · {
                    have hipos : 0 < i := Nat.pos_of_ne_zero hiz
                    have hpredlt : i - 1 < m := by omega
                    have hs' : s' i = s (i - 1) := by
                      simp [s', hiz]
                    rw [hs']
                    exact hsmin (i - 1) hpredlt
                  }
              }
            · {
                intro i hi
                by_cases hiz : i = 0
                · {
                    refine ⟨j, ?_, ?_⟩
                    · {
                        simpa [s', hiz] using hhit
                      }
                    · {
                        have hnext : i + 1 ≠ 0 := by omega
                        have hidx : (i + 1) - 1 = 0 := by omega
                        simp [s', hiz, hs0, r]
                      }
                  }
                · {
                    have hipos : 0 < i := Nat.pos_of_ne_zero hiz
                    have hpredlt : i - 1 < m := by omega
                    obtain ⟨j', hhit', hret'⟩ := hstep (i - 1) hpredlt
                    refine ⟨j', ?_, ?_⟩
                    · {
                        have hidx : i - 1 + 1 = i :=
                          Nat.sub_add_cancel hipos
                        simpa [s', hiz, hidx] using hhit'
                      }
                    · {
                        have hnext : i + 1 ≠ 0 := by omega
                        have hleft : i - 1 + 1 = i :=
                          Nat.sub_add_cancel hipos
                        have hidx : (i + 1) - 1 = i := by omega
                        simpa [s', hiz, hnext, hidx, hleft] using hret'
                      }
                  }
              }
          }
      }
  exact main k n hk hmin0

/-- Reaching `-1` yields a finite chain of exact returns ending at `-1`. -/
theorem ReturnChainToNegOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ k : ℕ, Iterate (RawStep p) k n = -1) :
    ∃ m : ℕ, ∃ s : ℕ → ℤ,
      s 0 = n ∧ s m = -1 ∧
        (∀ i : ℕ, i < m → s i ≠ -1) ∧
        ∀ i : ℕ, i < m → ∃ j : ℕ,
          IsFirstHit p (s i) j ∧
            RawStep p (Iterate (RawStep p) j (s i)) = s (i + 1) := by
  classical
  obtain ⟨k0, hk0⟩ := h
  let k := Nat.find ((⟨k0, hk0⟩ : ∃ k, Iterate (RawStep p) k n = -1))
  have hk : Iterate (RawStep p) k n = -1 :=
    Nat.find_spec ((⟨k0, hk0⟩ : ∃ k, Iterate (RawStep p) k n = -1))
  have hmin0 : ∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ -1 :=
    fun i hi =>
      Nat.find_min
        ((⟨k0, hk0⟩ : ∃ k, Iterate (RawStep p) k n = -1)) hi
  have main : ∀ k : ℕ, ∀ n : ℤ,
      Iterate (RawStep p) k n = -1 →
        (∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ -1) →
          ∃ m : ℕ, ∃ s : ℕ → ℤ,
            s 0 = n ∧ s m = -1 ∧
              (∀ i : ℕ, i < m → s i ≠ -1) ∧
              ∀ i : ℕ, i < m → ∃ j : ℕ,
                IsFirstHit p (s i) j ∧
                  RawStep p (Iterate (RawStep p) j (s i)) =
                    s (i + 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih => {
        intro n hk hmin
        cases k with
        | zero => {
            have hn : n = -1 := by
              have hbase : Iterate (RawStep p) 0 n = n := rfl
              rw [hbase] at hk
              exact hk
            refine ⟨0, fun _ => n, rfl, ?_, ?_, ?_⟩
            · {
                rw [hn]
              }
            · {
                intro i hi
                omega
              }
            · {
                intro i hi
                omega
              }
          }
        | succ kpred => {
            have hj : 1 ≤ kpred + 1 := by omega
            have hpred :=
              EntryThroughNegThree p hQ hC hD n (kpred + 1) hj hk hmin
            have hdvd3 : (3 : ℤ) ∣ Iterate (RawStep p) kpred n := by
              have hidx : (kpred + 1) - 1 = kpred := by omega
              rw [hidx] at hpred
              rw [hpred]
              exact ⟨-1, by ring⟩
            have hdvd : p.D ∣ Iterate (RawStep p) kpred n := by
              rw [hD]
              exact hdvd3
            obtain ⟨j, hjle, hhit⟩ :=
              ExistsHitFromRawDivision p n kpred hdvd
            have hret :
                Iterate (RawStep p) (j + 1) n =
                  RawStep p (Iterate (RawStep p) j n) := rfl
            have hrestle : j + 1 ≤ kpred + 1 := by omega
            let r := RawStep p (Iterate (RawStep p) j n)
            have hreach :
                Iterate (RawStep p) ((kpred + 1) - (j + 1)) r = -1 := by
              have hsum :
                  (j + 1) + ((kpred + 1) - (j + 1)) = kpred + 1 :=
                Nat.add_sub_of_le hrestle
              have hsplit :
                  Iterate (RawStep p) (kpred + 1) n =
                    Iterate (RawStep p) ((kpred + 1) - (j + 1))
                      (Iterate (RawStep p) (j + 1) n) := by
                conv_lhs => rw [← hsum]
                rw [IterateAdd]
              unfold r
              rw [← hret, ← hsplit]
              exact hk
            have hrestlt : (kpred + 1) - (j + 1) < kpred + 1 := by
              omega
            have hminr : ∀ i : ℕ, i < (kpred + 1) - (j + 1) →
                Iterate (RawStep p) i r ≠ -1 := by
              intro i hi hbad
              have hback :
                  Iterate (RawStep p) ((j + 1) + i) n =
                    Iterate (RawStep p) i r := by
                rw [IterateAdd, hret]
              have htime : (j + 1) + i < kpred + 1 := by omega
              rw [← hback] at hbad
              exact hmin ((j + 1) + i) htime hbad
            obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
              ih ((kpred + 1) - (j + 1)) hrestlt r hreach hminr
            let s' : ℕ → ℤ := fun i =>
              if i = 0 then n else s (i - 1)
            refine ⟨m + 1, s', ?_, ?_, ?_, ?_⟩
            · {
                rfl
              }
            · {
                have hidx : (m + 1) - 1 = m := by omega
                simp [s', hidx, hsm]
              }
            · {
                intro i hi
                by_cases hiz : i = 0
                · {
                    intro hn
                    have hs' : s' i = n := by simp [s', hiz]
                    rw [hs'] at hn
                    have hbase : Iterate (RawStep p) 0 n = n := rfl
                    exact hmin 0 (Nat.succ_pos kpred)
                      (by rw [hbase, hn])
                  }
                · {
                    have hipos : 0 < i := Nat.pos_of_ne_zero hiz
                    have hpredlt : i - 1 < m := by omega
                    have hs' : s' i = s (i - 1) := by
                      simp [s', hiz]
                    rw [hs']
                    exact hsmin (i - 1) hpredlt
                  }
              }
            · {
                intro i hi
                by_cases hiz : i = 0
                · {
                    refine ⟨j, ?_, ?_⟩
                    · {
                        simpa [s', hiz] using hhit
                      }
                    · {
                        have hidx : (i + 1) - 1 = 0 := by omega
                        simp [s', hiz, hs0, r]
                      }
                  }
                · {
                    have hipos : 0 < i := Nat.pos_of_ne_zero hiz
                    have hpredlt : i - 1 < m := by omega
                    obtain ⟨j', hhit', hret'⟩ := hstep (i - 1) hpredlt
                    refine ⟨j', ?_, ?_⟩
                    · {
                        have hidx : i - 1 + 1 = i :=
                          Nat.sub_add_cancel hipos
                        simpa [s', hiz, hidx] using hhit'
                      }
                    · {
                        have hleft : i - 1 + 1 = i :=
                          Nat.sub_add_cancel hipos
                        have hidx : (i + 1) - 1 = i := by omega
                        simpa [s', hiz, hidx, hleft] using hret'
                      }
                  }
              }
          }
      }
  exact main k n hk hmin0

/-- A minimal return chain is determined by its start and its target. -/
theorem ReturnChainUnique (p : Parameters) (n g : ℤ)
    (m m' : ℕ) (s t : ℕ → ℤ)
    (hs0 : s 0 = n) (ht0 : t 0 = n)
    (hsm : s m = g) (htm : t m' = g)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ g)
    (htmin : ∀ i : ℕ, i < m' → t i ≠ g)
    (hsstep : ∀ i : ℕ, i < m → ∃ j : ℕ,
      IsFirstHit p (s i) j ∧
        RawStep p (Iterate (RawStep p) j (s i)) = s (i + 1))
    (htstep : ∀ i : ℕ, i < m' → ∃ j : ℕ,
      IsFirstHit p (t i) j ∧
        RawStep p (Iterate (RawStep p) j (t i)) = t (i + 1)) :
    m = m' ∧ ∀ i : ℕ, i ≤ m → s i = t i := by
  have hagree : ∀ i : ℕ, i ≤ m → i ≤ m' → s i = t i := by
    intro i
    induction i with
    | zero => {
        intro _hi _hi'
        rw [hs0, ht0]
      }
    | succ i ih => {
        intro hi hm'
        have hilt : i < m := Nat.lt_of_succ_le hi
        have hilt' : i < m' := Nat.lt_of_succ_le hm'
        have hsi : s i = t i :=
          ih (Nat.le_of_lt hilt) (Nat.le_of_lt hilt')
        obtain ⟨j, hj, hret⟩ := hsstep i hilt
        obtain ⟨j', hj', hret'⟩ := htstep i hilt'
        have hjshift : IsFirstHit p (t i) j := by
          rw [hsi] at hj
          exact hj
        have hjeq : j = j' :=
          FirstHitUnique p (t i) j j' hjshift hj'
        rw [← hret, ← hret', hsi, hjeq]
      }
  rcases Nat.lt_trichotomy m m' with hlt | heq | hgt
  · {
      have hs : s m = t m :=
        hagree m (Nat.le_refl m) (Nat.le_of_lt hlt)
      rw [hsm] at hs
      exact False.elim (htmin m hlt hs.symm)
    }
  · {
      refine ⟨heq, ?_⟩
      intro i hi
      have hi' : i ≤ m' := by
        rw [← heq]
        exact hi
      exact hagree i hi hi'
    }
  · {
      have ht : s m' = t m' :=
        hagree m' (Nat.le_of_lt hgt) (Nat.le_refl m')
      rw [htm] at ht
      exact False.elim (hsmin m' hgt ht)
    }

/-- Sum of the raw lengths `L i + 1` along the first `m` return steps. -/
def RawLengthSum (L : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | Nat.succ m => RawLengthSum L m + (L m + 1)

/-- The first return length plus the tail sum is the full sum. -/
theorem RawLengthSumShift (L : ℕ → ℕ) (t : ℕ) :
    RawLengthSum L (t + 1) =
      (L 0 + 1) + RawLengthSum (fun i => L (i + 1)) t := by
  induction t with
  | zero => {
      simp [RawLengthSum]
    }
  | succ t ih => {
      have htail :
          RawLengthSum (fun i => L (i + 1)) (t + 1) =
            RawLengthSum (fun i => L (i + 1)) t +
              (L (t + 1) + 1) := rfl
      rw [htail, ← Nat.add_assoc, ← ih]
      rfl
    }

/-- A minimal return chain to `1` consumes exactly the first raw hitting time. -/
theorem ReturnChainAddsToHit (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m k : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n) (hsm : s m = 1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ 1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hk : Iterate (RawStep p) k n = 1)
    (hkmin : ∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ 1) :
    RawLengthSum L m = k := by
  revert n k s L hs0 hsm hsmin hL hk hkmin
  induction m with
  | zero => {
      intro n k s L hs0 hsm _hsmin _hL hk hkmin
      have hn : n = 1 := by
        rw [← hs0]
        exact hsm
      cases k with
      | zero => {
          rfl
        }
      | succ kpred => {
          have hbase : Iterate (RawStep p) 0 n = n := rfl
          exact False.elim
            (hkmin 0 (Nat.succ_pos kpred) (by rw [hbase, hn]))
        }
    }
  | succ mpred ih => {
      intro n k s L hs0 hsm hsmin hL hk hkmin
      have hn1 : n ≠ 1 := by
        intro hn
        exact hsmin 0 (Nat.succ_pos mpred) (by rw [hs0, hn])
      have hkpos : 0 < k := by
        cases k with
        | zero => {
            have hbase : Iterate (RawStep p) 0 n = n := rfl
            rw [hbase] at hk
            exact False.elim (hn1 hk)
          }
        | succ _ => {
            exact Nat.succ_pos _
          }
      have hpred := BeforeOne p hQ hC hD n k hkpos hk
      have hdvd : p.D ∣ Iterate (RawStep p) (k - 1) n := by
        rw [hD, hpred]
      obtain ⟨j0, hjle, hhit0⟩ :=
        ExistsHitFromRawDivision p n (k - 1) hdvd
      have hL0 : IsFirstHit p n (L 0) := by
        rw [← hs0]
        exact (hL 0 (Nat.succ_pos mpred)).1
      have heqj : L 0 = j0 :=
        FirstHitUnique p n (L 0) j0 hL0 hhit0
      have hrestle : L 0 + 1 ≤ k := by
        have hle : L 0 ≤ k - 1 := by
          rw [heqj]
          exact hjle
        omega
      have hquot :
          Iterate (RawStep p) (L 0 + 1) n = s 1 := by
        have hrfl :
            Iterate (RawStep p) (L 0 + 1) n =
              RawStep p (Iterate (RawStep p) (L 0) n) := rfl
        rw [hrfl, ← hs0]
        exact (hL 0 (Nat.succ_pos mpred)).2
      let r : ℤ := s 1
      let k' : ℕ := k - (L 0 + 1)
      have hreach : Iterate (RawStep p) k' r = 1 := by
        have hsum : (L 0 + 1) + k' = k := Nat.add_sub_of_le hrestle
        have hsplit :
            Iterate (RawStep p) k n =
              Iterate (RawStep p) k'
                (Iterate (RawStep p) (L 0 + 1) n) := by
          conv_lhs => rw [← hsum]
          rw [IterateAdd]
        rw [hquot] at hsplit
        rw [← hsplit]
        exact hk
      have hkmin' : ∀ i : ℕ, i < k' →
          Iterate (RawStep p) i r ≠ 1 := by
        intro i hi hbad
        have hback :
            Iterate (RawStep p) ((L 0 + 1) + i) n =
              Iterate (RawStep p) i r := by
          rw [IterateAdd, hquot]
        have htime : (L 0 + 1) + i < k := by omega
        rw [← hback] at hbad
        exact hkmin ((L 0 + 1) + i) htime hbad
      let s' : ℕ → ℤ := fun i => s (i + 1)
      let L' : ℕ → ℕ := fun i => L (i + 1)
      have hs0' : s' 0 = r := rfl
      have hsm' : s' mpred = 1 := by
        simpa [s'] using hsm
      have hsmin' : ∀ i : ℕ, i < mpred → s' i ≠ 1 := by
        intro i hi
        exact hsmin (i + 1) (Nat.succ_lt_succ hi)
      have hL' : ∀ i : ℕ, i < mpred →
          IsFirstHit p (s' i) (L' i) ∧
            RawStep p (Iterate (RawStep p) (L' i) (s' i)) =
              s' (i + 1) := by
        intro i hi
        simpa [s', L'] using hL (i + 1) (Nat.succ_lt_succ hi)
      have htail :=
        ih r k' s' L' hs0' hsm' hsmin' hL' hreach hkmin'
      have hshift := RawLengthSumShift L mpred
      have hsumk : (L 0 + 1) + k' = k := Nat.add_sub_of_le hrestle
      rw [hshift, htail, hsumk]
    }

/-- A minimal return chain to `-1` consumes exactly the first raw hitting time. -/
theorem ReturnChainAddsToNegOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m k : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n) (hsm : s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ -1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hk : Iterate (RawStep p) k n = -1)
    (hkmin : ∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ -1) :
    RawLengthSum L m = k := by
  revert n k s L hs0 hsm hsmin hL hk hkmin
  induction m with
  | zero => {
      intro n k s L hs0 hsm _hsmin _hL hk hkmin
      have hn : n = -1 := by
        rw [← hs0]
        exact hsm
      cases k with
      | zero => {
          rfl
        }
      | succ kpred => {
          have hbase : Iterate (RawStep p) 0 n = n := rfl
          exact False.elim
            (hkmin 0 (Nat.succ_pos kpred) (by rw [hbase, hn]))
        }
    }
  | succ mpred ih => {
      intro n k s L hs0 hsm hsmin hL hk hkmin
      have hn1 : n ≠ -1 := by
        intro hn
        exact hsmin 0 (Nat.succ_pos mpred) (by rw [hs0, hn])
      have hkpos : 0 < k := by
        cases k with
        | zero => {
            have hbase : Iterate (RawStep p) 0 n = n := rfl
            rw [hbase] at hk
            exact False.elim (hn1 hk)
          }
        | succ _ => {
            exact Nat.succ_pos _
          }
      have hj : 1 ≤ k := by omega
      have hpred :=
        EntryThroughNegThree p hQ hC hD n k hj hk hkmin
      have hdvd : p.D ∣ Iterate (RawStep p) (k - 1) n := by
        rw [hD, hpred]
        exact ⟨-1, by ring⟩
      obtain ⟨j0, hjle, hhit0⟩ :=
        ExistsHitFromRawDivision p n (k - 1) hdvd
      have hL0 : IsFirstHit p n (L 0) := by
        rw [← hs0]
        exact (hL 0 (Nat.succ_pos mpred)).1
      have heqj : L 0 = j0 :=
        FirstHitUnique p n (L 0) j0 hL0 hhit0
      have hrestle : L 0 + 1 ≤ k := by
        have hle : L 0 ≤ k - 1 := by
          rw [heqj]
          exact hjle
        omega
      have hquot :
          Iterate (RawStep p) (L 0 + 1) n = s 1 := by
        have hrfl :
            Iterate (RawStep p) (L 0 + 1) n =
              RawStep p (Iterate (RawStep p) (L 0) n) := rfl
        rw [hrfl, ← hs0]
        exact (hL 0 (Nat.succ_pos mpred)).2
      let r : ℤ := s 1
      let k' : ℕ := k - (L 0 + 1)
      have hreach : Iterate (RawStep p) k' r = -1 := by
        have hsum : (L 0 + 1) + k' = k := Nat.add_sub_of_le hrestle
        have hsplit :
            Iterate (RawStep p) k n =
              Iterate (RawStep p) k'
                (Iterate (RawStep p) (L 0 + 1) n) := by
          conv_lhs => rw [← hsum]
          rw [IterateAdd]
        rw [hquot] at hsplit
        rw [← hsplit]
        exact hk
      have hkmin' : ∀ i : ℕ, i < k' →
          Iterate (RawStep p) i r ≠ -1 := by
        intro i hi hbad
        have hback :
            Iterate (RawStep p) ((L 0 + 1) + i) n =
              Iterate (RawStep p) i r := by
          rw [IterateAdd, hquot]
        have htime : (L 0 + 1) + i < k := by omega
        rw [← hback] at hbad
        exact hkmin ((L 0 + 1) + i) htime hbad
      let s' : ℕ → ℤ := fun i => s (i + 1)
      let L' : ℕ → ℕ := fun i => L (i + 1)
      have hs0' : s' 0 = r := rfl
      have hsm' : s' mpred = -1 := by
        simpa [s'] using hsm
      have hsmin' : ∀ i : ℕ, i < mpred → s' i ≠ -1 := by
        intro i hi
        exact hsmin (i + 1) (Nat.succ_lt_succ hi)
      have hL' : ∀ i : ℕ, i < mpred →
          IsFirstHit p (s' i) (L' i) ∧
            RawStep p (Iterate (RawStep p) (L' i) (s' i)) =
              s' (i + 1) := by
        intro i hi
        simpa [s', L'] using hL (i + 1) (Nat.succ_lt_succ hi)
      have htail :=
        ih r k' s' L' hs0' hsm' hsmin' hL' hreach hkmin'
      have hshift := RawLengthSumShift L mpred
      have hsumk : (L 0 + 1) + k' = k := Nat.add_sub_of_le hrestle
      rw [hshift, htail, hsumk]
    }

/-- Each return-chain term is the raw orbit at the accumulated length. -/
theorem ReturnChainIsOrbit (p : Parameters)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) :
    ∀ i : ℕ, i ≤ m →
      s i = Iterate (RawStep p) (RawLengthSum L i) n := by
  intro i hi
  induction i with
  | zero => {
      rw [hs0]
      rfl
    }
  | succ t ih => {
      have hlt : t < m := Nat.lt_of_succ_le hi
      have iht := ih (Nat.le_of_lt hlt)
      have hstep := (hL t hlt).2
      have hsum :
          RawLengthSum L (t + 1) =
            RawLengthSum L t + (L t + 1) := rfl
      have hsplit :
          Iterate (RawStep p) (RawLengthSum L (t + 1)) n =
            Iterate (RawStep p) (L t + 1)
              (Iterate (RawStep p) (RawLengthSum L t) n) := by
        rw [hsum, IterateAdd]
      rw [hsplit, ← iht]
      have hrfl :
          Iterate (RawStep p) (L t + 1) (s t) =
            RawStep p (Iterate (RawStep p) (L t) (s t)) := rfl
      rw [hrfl]
      exact hstep.symm
    }

/-- A time before the end of the chain lies in one return block. -/
theorem BlockIndex (L : ℕ → ℕ) (m j : ℕ)
    (hj : j < RawLengthSum L m) :
    ∃ i : ℕ, i < m ∧ RawLengthSum L i ≤ j ∧
      j < RawLengthSum L (i + 1) := by
  induction m with
  | zero => {
      have hzero : RawLengthSum L 0 = 0 := rfl
      rw [hzero] at hj
      omega
    }
  | succ mpred ih => {
      by_cases hlt : j < RawLengthSum L mpred
      · {
          obtain ⟨i, hi, hle, hhi⟩ := ih hlt
          exact ⟨i, Nat.lt_succ_of_lt hi, hle, hhi⟩
        }
      · {
          have hle : RawLengthSum L mpred ≤ j := Nat.le_of_not_lt hlt
          exact ⟨mpred, Nat.lt_succ_self mpred, hle, hj⟩
        }
    }

/-- Shifting a block by its start recovers the orbit of that chain term. -/
theorem BlockShift (p : Parameters) (n s0 : ℤ) (start r : ℕ)
    (horbit : s0 = Iterate (RawStep p) start n) :
    Iterate (RawStep p) (start + r) n =
      Iterate (RawStep p) r s0 := by
  rw [IterateAdd, horbit]

/-- Before the chain ends, the raw divisions are exactly the block ends. -/
theorem DivisionTimesAreBlockEnds (p : Parameters)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (j : ℕ) (hj : j < RawLengthSum L m) :
    p.D ∣ Iterate (RawStep p) j n ↔
      ∃ i : ℕ, i < m ∧ j = RawLengthSum L i + L i := by
  have horbit := ReturnChainIsOrbit p n m s L hs0 hL
  constructor
  · {
      intro hdiv
      obtain ⟨i, hi, hle, hhi⟩ := BlockIndex L m j hj
      have hsum :
          RawLengthSum L (i + 1) =
            RawLengthSum L i + (L i + 1) := rfl
      have hrle : j - RawLengthSum L i ≤ L i := by
        have hlt : j < RawLengthSum L i + (L i + 1) := by
          rw [← hsum]
          exact hhi
        omega
      have hstate :
          Iterate (RawStep p) j n =
            Iterate (RawStep p) (j - RawLengthSum L i) (s i) := by
        have hback :=
          BlockShift p n (s i) (RawLengthSum L i)
            (j - RawLengthSum L i) (horbit i (Nat.le_of_lt hi))
        have hsumj :
            RawLengthSum L i + (j - RawLengthSum L i) = j :=
          Nat.add_sub_of_le hle
        rw [hsumj] at hback
        exact hback
      by_cases hbefore : j - RawLengthSum L i < L i
      · {
          have hclean : ∀ u : ℕ, u < j - RawLengthSum L i →
              ¬ p.D ∣ AffineState p.Q p.C u (s i) := by
            intro u hu
            exact (hL i hi).1.2 u (Nat.lt_trans hu hbefore)
          have heq :=
            PrefixEqualsAffine p (s i) (j - RawLengthSum L i) hclean
          have hmiss :
              ¬ p.D ∣ Iterate (RawStep p)
                (j - RawLengthSum L i) (s i) := by
            rw [heq]
            exact (hL i hi).1.2 (j - RawLengthSum L i) hbefore
          exact False.elim (hmiss (by rw [← hstate]; exact hdiv))
        }
      · {
          have heq : j - RawLengthSum L i = L i := by omega
          exact ⟨i, hi, by omega⟩
        }
    }
  · {
      intro h
      obtain ⟨i, hi, heqj⟩ := h
      have hclean : ∀ u : ℕ, u < L i →
          ¬ p.D ∣ AffineState p.Q p.C u (s i) :=
        (hL i hi).1.2
      have heqaff := PrefixEqualsAffine p (s i) (L i) hclean
      have hhit : p.D ∣ AffineState p.Q p.C (L i) (s i) :=
        (hL i hi).1.1
      have hraw :
          p.D ∣ Iterate (RawStep p) (L i) (s i) := by
        rw [heqaff]
        exact hhit
      have hback :=
        BlockShift p n (s i) (RawLengthSum L i) (L i)
          (horbit i (Nat.le_of_lt hi))
      rw [heqj, hback]
      exact hraw
    }

/-- Accumulated lengths do not decrease. -/
theorem RawLengthSumMono (L : ℕ → ℕ) (i i' : ℕ) (h : i ≤ i') :
    RawLengthSum L i ≤ RawLengthSum L i' := by
  induction i' with
  | zero => {
      have hzero : i = 0 := Nat.eq_zero_of_le_zero h
      rw [hzero]
    }
  | succ i' ih => {
      cases Nat.eq_or_lt_of_le h with
      | inl heq => {
          rw [heq]
        }
      | inr hlt => {
          have hle : i ≤ i' := Nat.le_of_lt_succ hlt
          have hstep :
              RawLengthSum L i' ≤ RawLengthSum L (i' + 1) := by
            have hsum :
                RawLengthSum L (i' + 1) =
                  RawLengthSum L i' + (L i' + 1) := rfl
            omega
          exact Nat.le_trans (ih hle) hstep
        }
    }

/-- Later return blocks end later. -/
theorem BlockEndInjective (L : ℕ → ℕ) (i i' : ℕ) (h : i < i') :
    RawLengthSum L i + L i < RawLengthSum L i' + L i' := by
  have hmono :
      RawLengthSum L (i + 1) ≤ RawLengthSum L i' :=
    RawLengthSumMono L (i + 1) i' h
  have hsum :
      RawLengthSum L (i + 1) =
        RawLengthSum L i + (L i + 1) := rfl
  omega

/-- Equal block-end times come from the same step. -/
theorem BlockEndUnique (L : ℕ → ℕ) (i i' : ℕ)
    (h : RawLengthSum L i + L i = RawLengthSum L i' + L i') :
    i = i' := by
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · {
      have hlt' := BlockEndInjective L i i' hlt
      rw [h] at hlt'
      exact False.elim (Nat.lt_irrefl _ hlt')
    }
  · {
      exact heq
    }
  · {
      have hgt' := BlockEndInjective L i' i hgt
      rw [← h] at hgt'
      exact False.elim (Nat.lt_irrefl _ hgt')
    }

/-- The block ends are all the divisions before the chain ends, without repetition. -/
theorem DivisionCount (p : Parameters)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) :
    (∀ i : ℕ, i < m →
      RawLengthSum L i + L i < RawLengthSum L m ∧
        p.D ∣ Iterate (RawStep p) (RawLengthSum L i + L i) n) ∧
      (∀ j : ℕ, j < RawLengthSum L m →
        p.D ∣ Iterate (RawStep p) j n →
          ∃ i : ℕ, i < m ∧ j = RawLengthSum L i + L i) ∧
        (∀ i i' : ℕ, i < m → i' < m →
          RawLengthSum L i + L i = RawLengthSum L i' + L i' →
            i = i') := by
  refine ⟨?_, ?_, ?_⟩
  · {
      intro i hi
      have hend :
          RawLengthSum L i + L i < RawLengthSum L m := by
        have hlt : RawLengthSum L (i + 1) ≤ RawLengthSum L m :=
          RawLengthSumMono L (i + 1) m hi
        have hsum :
            RawLengthSum L (i + 1) =
              RawLengthSum L i + (L i + 1) := rfl
        omega
      exact ⟨hend,
        (DivisionTimesAreBlockEnds p n m s L hs0 hL
          (RawLengthSum L i + L i) hend).mpr ⟨i, hi, rfl⟩⟩
    }
  · {
      intro j hj hdiv
      exact
        (DivisionTimesAreBlockEnds p n m s L hs0 hL j hj).mp hdiv
    }
  · {
      intro i i' _hi _hi' heq
      exact BlockEndUnique L i i' heq
    }

/-- A block end before step `i` lies before the accumulated time `T(i)`. -/
theorem DivisionsBeforeStart (L : ℕ → ℕ) (i u : ℕ) (hu : u < i) :
    RawLengthSum L u + L u < RawLengthSum L i := by
  have hmono :
      RawLengthSum L (u + 1) ≤ RawLengthSum L i :=
    RawLengthSumMono L (u + 1) i hu
  have hsum :
      RawLengthSum L (u + 1) =
        RawLengthSum L u + (L u + 1) := rfl
  omega

/-- A block end at or after step `i` is at least `T(i)`. -/
theorem DivisionsFromStart (L : ℕ → ℕ) (i u : ℕ) (h : i ≤ u) :
    RawLengthSum L i ≤ RawLengthSum L u + L u := by
  exact Nat.le_trans (RawLengthSumMono L i u h) (Nat.le_add_right _ _)

/-- After `i` returns, the remaining divisions are the later block ends. -/
theorem RemainingDivisions (p : Parameters)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (i : ℕ) (_hi : i ≤ m) :
    (∀ u : ℕ, i ≤ u → u < m →
      RawLengthSum L i ≤ RawLengthSum L u + L u ∧
        RawLengthSum L u + L u < RawLengthSum L m ∧
          p.D ∣
            Iterate (RawStep p) (RawLengthSum L u + L u) n) ∧
      (∀ j : ℕ, RawLengthSum L i ≤ j → j < RawLengthSum L m →
        p.D ∣ Iterate (RawStep p) j n →
          ∃ u : ℕ, i ≤ u ∧ u < m ∧
            j = RawLengthSum L u + L u) ∧
        (∀ u u' : ℕ, i ≤ u → u < m → i ≤ u' → u' < m →
          RawLengthSum L u + L u = RawLengthSum L u' + L u' →
            u = u') := by
  refine ⟨?_, ?_, ?_⟩
  · {
      intro u hiu hum
      have hge := DivisionsFromStart L i u hiu
      have hlt : RawLengthSum L u + L u < RawLengthSum L m := by
        have hmono :
            RawLengthSum L (u + 1) ≤ RawLengthSum L m :=
          RawLengthSumMono L (u + 1) m hum
        have hsum :
            RawLengthSum L (u + 1) =
              RawLengthSum L u + (L u + 1) := rfl
        omega
      exact ⟨hge, hlt,
        (DivisionTimesAreBlockEnds p n m s L hs0 hL
          (RawLengthSum L u + L u) hlt).mpr ⟨u, hum, rfl⟩⟩
    }
  · {
      intro j hge hlt hdiv
      obtain ⟨u, hum, heq⟩ :=
        (DivisionTimesAreBlockEnds p n m s L hs0 hL j hlt).mp hdiv
      have hiu : i ≤ u := by
        by_contra hlt_u
        have hbefore :
            RawLengthSum L u + L u < RawLengthSum L i :=
          DivisionsBeforeStart L i u (Nat.lt_of_not_ge hlt_u)
        have hcontra : j < RawLengthSum L i := by
          rw [heq]
          exact hbefore
        omega
      exact ⟨u, hiu, hum, heq⟩
    }
  · {
      intro u u' _hiu _hum _hiu' _hum' heq
      exact BlockEndUnique L u u' heq
    }

/-- A first hit of absolute value at least two has a strictly smaller quotient. -/
theorem ChainStepDescent (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (j : ℕ) (hhit : IsFirstHit p n j)
    (hk : 2 ≤ n.natAbs) :
    (RawStep p (Iterate (RawStep p) j n)).natAbs < n.natAbs := by
  rcases ResidueTrichotomy p hQ hC hD n with h0 | h1 | h2
  · {
      obtain ⟨_hmod, hhit0, hquot⟩ := h0
      have heq : j = 0 := FirstHitUnique p n j 0 hhit hhit0
      have hdvd : (3 : ℤ) ∣ n := by
        have hz : AffineState p.Q p.C 0 n = n := AffineStateZero p.Q p.C n
        rw [← hD, ← hz]
        exact hhit0.1
      have hn : n ≠ 0 := by
        intro hz
        rw [hz] at hk
        omega
      rw [heq, hquot]
      exact QuotientAbsSmaller n hdvd hn
    }
  · {
      obtain ⟨hmod, hhit1, _haff, hquot⟩ := h1
      have heq : j = 1 := FirstHitUnique p n j 1 hhit hhit1
      rw [heq, hquot]
      exact ResidueOneReturnSmaller n hmod hk
    }
  · {
      exact False.elim (h2.2 j hhit)
    }

/-- One return step of a chain term drops the absolute value. -/
theorem ChainStepFromChain (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (i : ℕ) (hi : i < m) (hk : 2 ≤ (s i).natAbs) :
    (s (i + 1)).natAbs < (s i).natAbs := by
  have hdrop :=
    ChainStepDescent p hQ hC hD (s i) (L i) (hL i hi).1 hk
  rw [(hL i hi).2] at hdrop
  exact hdrop

/-- Absolute values along the chain fall at least as fast as the step count. -/
theorem ChainAbsBound (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hbig : ∀ t : ℕ, t < m → 2 ≤ (s t).natAbs)
    (i : ℕ) (hi : i ≤ m) :
    (s i).natAbs + i ≤ n.natAbs := by
  induction i with
  | zero => {
      rw [hs0]
      omega
    }
  | succ t ih => {
      have ht : t < m := Nat.lt_of_succ_le hi
      have hdrop :=
        ChainStepFromChain p hQ hC hD m s L hL t ht (hbig t ht)
      have iht := ih (Nat.le_of_lt ht)
      omega
    }

/-- An integer of absolute value at most one is `0`, `1`, or `-1`. -/
theorem SmallAbsThree (n : ℤ) (h : n.natAbs ≤ 1) :
    n = 0 ∨ n = 1 ∨ n = -1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with hz | hone
  · {
      exact Or.inl (Int.natAbs_eq_zero.mp hz)
    }
  · {
      rcases NatAbsOneCases n hone with h1 | hm
      · {
          exact Or.inr (Or.inl h1)
        }
      · {
          exact Or.inr (Or.inr hm)
        }
    }

/-- A minimal chain to `1` has at most `|n| - 1` returns. -/
theorem ReturnCountAtMostAbs (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n) (hsm : s m = 1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ 1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) :
    m + 1 ≤ n.natAbs := by
  have horbit := ReturnChainIsOrbit p n m s L hs0 hL
  have hbig : ∀ t : ℕ, t < m → 2 ≤ (s t).natAbs := by
    intro t ht
    by_contra hsmall
    have hle : (s t).natAbs ≤ 1 := by omega
    rcases SmallAbsThree (s t) hle with hz | hone | hneg
    · {
        have h0 : ∃ j : ℕ, Iterate (RawStep p) j n = 0 :=
          ⟨RawLengthSum L t, by rw [← horbit t (Nat.le_of_lt ht)]; exact hz⟩
        have h1 : ∃ j : ℕ, Iterate (RawStep p) j n = 1 :=
          ⟨RawLengthSum L m, by rw [← horbit m (Nat.le_refl m)]; exact hsm⟩
        exact NotBothZeroAndOne p hQ hC hD n h0 h1
      }
    · {
        exact hsmin t ht hone
      }
    · {
        have hm : ∃ j : ℕ, Iterate (RawStep p) j n = -1 :=
          ⟨RawLengthSum L t, by rw [← horbit t (Nat.le_of_lt ht)]; exact hneg⟩
        have h1 : ∃ j : ℕ, Iterate (RawStep p) j n = 1 :=
          ⟨RawLengthSum L m, by rw [← horbit m (Nat.le_refl m)]; exact hsm⟩
        exact NotBothOneAndNegOne p hQ hC hD n h1 hm
      }
  have hbound :=
    ChainAbsBound p hQ hC hD n m s L hs0 hL hbig m (Nat.le_refl m)
  rw [hsm] at hbound
  omega

/-- A minimal chain to `-1` has at most `|n| - 1` returns. -/
theorem ReturnCountAtMostAbsNeg (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n) (hsm : s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ -1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) :
    m + 1 ≤ n.natAbs := by
  have horbit := ReturnChainIsOrbit p n m s L hs0 hL
  have hbig : ∀ t : ℕ, t < m → 2 ≤ (s t).natAbs := by
    intro t ht
    by_contra hsmall
    have hle : (s t).natAbs ≤ 1 := by omega
    rcases SmallAbsThree (s t) hle with hz | hone | hneg
    · {
        have h0 : ∃ j : ℕ, Iterate (RawStep p) j n = 0 :=
          ⟨RawLengthSum L t, by rw [← horbit t (Nat.le_of_lt ht)]; exact hz⟩
        have hm : ∃ j : ℕ, Iterate (RawStep p) j n = -1 :=
          ⟨RawLengthSum L m, by rw [← horbit m (Nat.le_refl m)]; exact hsm⟩
        exact NotBothZeroAndNegOne p hQ hC hD n h0 hm
      }
    · {
        have h1 : ∃ j : ℕ, Iterate (RawStep p) j n = 1 :=
          ⟨RawLengthSum L t, by rw [← horbit t (Nat.le_of_lt ht)]; exact hone⟩
        have hm : ∃ j : ℕ, Iterate (RawStep p) j n = -1 :=
          ⟨RawLengthSum L m, by rw [← horbit m (Nat.le_refl m)]; exact hsm⟩
        exact NotBothOneAndNegOne p hQ hC hD n h1 hm
      }
    · {
        exact hsmin t ht hneg
      }
  have hbound :=
    ChainAbsBound p hQ hC hD n m s L hs0 hL hbig m (Nat.le_refl m)
  rw [hsm] at hbound
  omega

/-- Division by three loses at least the factor `5/6` once `|n| \ge 2`. -/
theorem SixFiveDiv (n : ℤ) (hdiv : (3 : ℤ) ∣ n) (_hk : 2 ≤ n.natAbs) :
    6 * (n / 3).natAbs ≤ 5 * n.natAbs := by
  have hcancel := CancelNatAbsThree n hdiv
  have htwo : 6 * (n / 3).natAbs = 2 * n.natAbs := by
    calc
      6 * (n / 3).natAbs = 2 * (3 * (n / 3).natAbs) := by omega
      _ = 2 * n.natAbs := by rw [hcancel]
  rw [htwo]
  omega

/-- The residue-one numerator loses at least the factor `5/6`. -/
theorem TwoAbsFactor (n : ℤ) (hk : 2 ≤ n.natAbs) :
    2 * (2 * n + 1).natAbs ≤ 5 * n.natAbs := by
  cases n with
  | ofNat k => {
      have hk' : 2 ≤ k := by simpa using hk
      have hnat : (Int.ofNat k).natAbs = k := Int.natAbs_natCast k
      have hcast : ((2 * k + 1 : ℕ) : ℤ) = 2 * (Int.ofNat k) + 1 := by
        simp
      have habs : (2 * (Int.ofNat k) + 1).natAbs = 2 * k + 1 := by
        rw [← hcast]
        exact Int.natAbs_natCast (2 * k + 1)
      rw [habs, hnat]
      omega
    }
  | negSucc k => {
      have hk' : 2 ≤ k + 1 := by simpa using hk
      have hneg : 2 * (Int.negSucc k) + 1 =
          -((2 * (k + 1) - 1 : ℕ) : ℤ) := by
        simp [Int.negSucc_eq]
        omega
      have habs : (2 * (Int.negSucc k) + 1).natAbs = 2 * (k + 1) - 1 := by
        rw [hneg, Int.natAbs_neg]
        exact Int.natAbs_natCast (2 * (k + 1) - 1)
      have hnat : (Int.negSucc k).natAbs = k + 1 := by simp
      rw [habs, hnat]
      omega
    }

/-- A residue-one return loses at least the factor `5/6`. -/
theorem SixFiveOne (n : ℤ) (hmod : n % (3 : ℤ) = 1) (hk : 2 ≤ n.natAbs) :
    6 * ((2 * n + 1) / 3).natAbs ≤ 5 * n.natAbs := by
  have hdvd := TwoMulSuccDiv n hmod
  have hcancel := CancelNatAbsThree (2 * n + 1) hdvd
  have htwo : 6 * ((2 * n + 1) / 3).natAbs =
      2 * (2 * n + 1).natAbs := by
    calc
      6 * ((2 * n + 1) / 3).natAbs =
          2 * (3 * ((2 * n + 1) / 3).natAbs) := by omega
      _ = 2 * (2 * n + 1).natAbs := by rw [hcancel]
  rw [htwo]
  exact TwoAbsFactor n hk

/-- One exact return multiplies the absolute value by at most `5/6`. -/
theorem ChainStepFactor (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (j : ℕ) (hhit : IsFirstHit p n j)
    (hk : 2 ≤ n.natAbs) :
    6 * (RawStep p (Iterate (RawStep p) j n)).natAbs ≤ 5 * n.natAbs := by
  rcases ResidueTrichotomy p hQ hC hD n with h0 | h1 | h2
  · {
      obtain ⟨_hmod, hhit0, hquot⟩ := h0
      have heq : j = 0 := FirstHitUnique p n j 0 hhit hhit0
      have hdvd : (3 : ℤ) ∣ n := by
        have hz : AffineState p.Q p.C 0 n = n := AffineStateZero p.Q p.C n
        rw [← hD, ← hz]
        exact hhit0.1
      rw [heq, hquot]
      exact SixFiveDiv n hdvd hk
    }
  · {
      obtain ⟨hmod, hhit1, _haff, hquot⟩ := h1
      have heq : j = 1 := FirstHitUnique p n j 1 hhit hhit1
      rw [heq, hquot]
      exact SixFiveOne n hmod hk
    }
  · {
      exact False.elim (h2.2 j hhit)
    }

/-- Absolute values along a chain obey the factor `5/6` at every step. -/
theorem ChainSixFive (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hbig : ∀ t : ℕ, t < m → 2 ≤ (s t).natAbs)
    (i : ℕ) (hi : i ≤ m) :
    6 ^ i * (s i).natAbs ≤ 5 ^ i * n.natAbs := by
  induction i with
  | zero => {
      rw [hs0]
      simp
    }
  | succ t ih => {
      have ht : t < m := Nat.lt_of_succ_le hi
      have hdrop0 :=
        ChainStepFactor p hQ hC hD (s t) (L t) (hL t ht).1 (hbig t ht)
      have hdrop :
          6 * (s (t + 1)).natAbs ≤ 5 * (s t).natAbs := by
        rw [(hL t ht).2] at hdrop0
        exact hdrop0
      have iht := ih (Nat.le_of_lt ht)
      have hleft :
          6 ^ (t + 1) * (s (t + 1)).natAbs =
            6 ^ t * (6 * (s (t + 1)).natAbs) := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      have hmid :
          6 ^ t * (6 * (s (t + 1)).natAbs) ≤
            6 ^ t * (5 * (s t).natAbs) :=
        Nat.mul_le_mul_left _ hdrop
      have hcomm :
          6 ^ t * (5 * (s t).natAbs) =
            5 * (6 ^ t * (s t).natAbs) := by
        rw [Nat.mul_left_comm]
      have hend :
          5 * (6 ^ t * (s t).natAbs) ≤
            5 * (5 ^ t * n.natAbs) :=
        Nat.mul_le_mul_left _ iht
      have hpow :
          5 * (5 ^ t * n.natAbs) = 5 ^ (t + 1) * n.natAbs := by
        calc
          5 * (5 ^ t * n.natAbs) = (5 * 5 ^ t) * n.natAbs := by
            rw [Nat.mul_assoc]
          _ = (5 ^ t * 5) * n.natAbs := by
            rw [Nat.mul_comm 5 (5 ^ t)]
          _ = 5 ^ (t + 1) * n.natAbs := by
            rw [← Nat.pow_succ]
      calc
        6 ^ (t + 1) * (s (t + 1)).natAbs
            = 6 ^ t * (6 * (s (t + 1)).natAbs) := hleft
        _ ≤ 6 ^ t * (5 * (s t).natAbs) := hmid
        _ = 5 * (6 ^ t * (s t).natAbs) := hcomm
        _ ≤ 5 * (5 ^ t * n.natAbs) := hend
        _ = 5 ^ (t + 1) * n.natAbs := hpow
    }

/-- A proper term of a chain to `1` or `-1` has absolute value at least `2`. -/
theorem ProperTermsLarge (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hsm : s m = 1 ∨ s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ s m)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) :
    ∀ t : ℕ, t < m → 2 ≤ (s t).natAbs := by
  intro t ht
  by_contra hsmall
  have hle : (s t).natAbs ≤ 1 := by omega
  have horbit := ReturnChainIsOrbit p n m s L hs0 hL
  rcases SmallAbsThree (s t) hle with hz | hone | hneg
  · {
      rcases hsm with hpos | hnegm
      · {
          exact NotBothZeroAndOne p hQ hC hD n
            ⟨RawLengthSum L t, by
              rw [← horbit t (Nat.le_of_lt ht)]; exact hz⟩
            ⟨RawLengthSum L m, by
              rw [← horbit m (Nat.le_refl m), hpos]⟩
        }
      · {
          exact NotBothZeroAndNegOne p hQ hC hD n
            ⟨RawLengthSum L t, by
              rw [← horbit t (Nat.le_of_lt ht)]; exact hz⟩
            ⟨RawLengthSum L m, by
              rw [← horbit m (Nat.le_refl m), hnegm]⟩
        }
    }
  · {
      rcases hsm with hpos | hnegm
      · {
          exact hsmin t ht (hone.trans hpos.symm)
        }
      · {
          exact NotBothOneAndNegOne p hQ hC hD n
            ⟨RawLengthSum L t, by
              rw [← horbit t (Nat.le_of_lt ht), hone]⟩
            ⟨RawLengthSum L m, by
              rw [← horbit m (Nat.le_refl m), hnegm]⟩
        }
    }
  · {
      rcases hsm with hpos | hnegm
      · {
          exact NotBothOneAndNegOne p hQ hC hD n
            ⟨RawLengthSum L m, by
              rw [← horbit m (Nat.le_refl m), hpos]⟩
            ⟨RawLengthSum L t, by
              rw [← horbit t (Nat.le_of_lt ht), hneg]⟩
        }
      · {
          exact hsmin t ht (hneg.trans hnegm.symm)
        }
    }

/-- A minimal chain to `1` or `-1` satisfies `6 ^ m ≤ 5 ^ m * |n|`. -/
theorem ReturnSixFive (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hsm : s m = 1 ∨ s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ s m)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) :
    6 ^ m ≤ 5 ^ m * n.natAbs := by
  have hbig :=
    ProperTermsLarge p hQ hC hD n m s L hs0 hsm hsmin hL
  have hfac :=
    ChainSixFive p hQ hC hD n m s L hs0 hL hbig m (Nat.le_refl m)
  rcases hsm with hpos | hneg
  · {
      rw [hpos] at hfac
      simpa using hfac
    }
  · {
      rw [hneg] at hfac
      simpa using hfac
    }

/-- An orbit that meets `1` has return count `m` with `6 ^ m ≤ 5 ^ m * |n|`. -/
theorem HitOneSixFive (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ k : ℕ, Iterate (RawStep p) k n = 1) :
    ∃ m : ℕ, 6 ^ m ≤ 5 ^ m * n.natAbs := by
  classical
  obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
    ReturnChainToOne p hQ hC hD n h
  let L : ℕ → ℕ := fun i =>
    if hi : i < m then Classical.choose (hstep i hi) else 0
  have hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1) := by
    intro i hi
    have hspec := Classical.choose_spec (hstep i hi)
    have hLi : L i = Classical.choose (hstep i hi) := by
      simp [L, hi]
    rw [hLi]
    exact hspec
  have hsm' : s m = 1 ∨ s m = -1 := Or.inl hsm
  have hsmin' : ∀ i : ℕ, i < m → s i ≠ s m := by
    intro i hi
    rw [hsm]
    exact hsmin i hi
  exact ⟨m, ReturnSixFive p hQ hC hD n m s L hs0 hsm' hsmin' hL⟩

/-- An orbit that meets `-1` has return count `m` with `6 ^ m ≤ 5 ^ m * |n|`. -/
theorem HitNegOneSixFive (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ k : ℕ, Iterate (RawStep p) k n = -1) :
    ∃ m : ℕ, 6 ^ m ≤ 5 ^ m * n.natAbs := by
  classical
  obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
    ReturnChainToNegOne p hQ hC hD n h
  let L : ℕ → ℕ := fun i =>
    if hi : i < m then Classical.choose (hstep i hi) else 0
  have hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1) := by
    intro i hi
    have hspec := Classical.choose_spec (hstep i hi)
    have hLi : L i = Classical.choose (hstep i hi) := by
      simp [L, hi]
    rw [hLi]
    exact hspec
  have hsm' : s m = 1 ∨ s m = -1 := Or.inr hsm
  have hsmin' : ∀ i : ℕ, i < m → s i ≠ s m := by
    intro i hi
    rw [hsm]
    exact hsmin i hi
  exact ⟨m, ReturnSixFive p hQ hC hD n m s L hs0 hsm' hsmin' hL⟩

/-- Division by three loses at least the factor `3/4`. -/
theorem FourThreeDiv (n : ℤ) (hdiv : (3 : ℤ) ∣ n) :
    4 * (n / 3).natAbs ≤ 3 * n.natAbs := by
  have hcancel := CancelNatAbsThree n hdiv
  have hmul : 3 * n.natAbs = 9 * (n / 3).natAbs := by
    calc
      3 * n.natAbs = 3 * (3 * (n / 3).natAbs) := by rw [hcancel]
      _ = 9 * (n / 3).natAbs := by omega
  rw [hmul]
  omega

/-- A residue-one numerator satisfies `4|2n+1| ≤ 9|n|` once `|n| ≥ 2`. -/
theorem FourAbsNine (n : ℤ) (hmod : n % (3 : ℤ) = 1)
    (hk : 2 ≤ n.natAbs) :
    4 * (2 * n + 1).natAbs ≤ 9 * n.natAbs := by
  cases n with
  | ofNat k => {
      have hk' : 2 ≤ k := by simpa using hk
      have hmodk : k % 3 = 1 := by
        have hnat : k = 3 * (k / 3) + k % 3 :=
          (Nat.div_add_mod k 3).symm
        have hsplit : (k : ℤ) =
            ((k % 3 : ℕ) : ℤ) + ((3 : ℕ) : ℤ) * ((k / 3 : ℕ) : ℤ) := by
          calc
            (k : ℤ) = ((3 * (k / 3) + k % 3 : ℕ) : ℤ) :=
              congrArg Nat.cast hnat
            _ = ((3 * (k / 3) : ℕ) : ℤ) + ((k % 3 : ℕ) : ℤ) :=
              Nat.cast_add _ _
            _ = ((3 : ℕ) : ℤ) * ((k / 3 : ℕ) : ℤ) +
                ((k % 3 : ℕ) : ℤ) := by
              rw [Nat.cast_mul]
            _ = ((k % 3 : ℕ) : ℤ) +
                ((3 : ℕ) : ℤ) * ((k / 3 : ℕ) : ℤ) := by
              rw [add_comm]
        have hrem : (k : ℤ) % 3 = ((k % 3 : ℕ) : ℤ) % 3 := by
          rw [hsplit]
          exact Int.add_mul_emod_self_left
            ((k % 3 : ℕ) : ℤ) 3 ((k / 3 : ℕ) : ℤ)
        have hrlt : ((k % 3 : ℕ) : ℤ) < 3 :=
          (Nat.cast_lt).2 (Nat.mod_lt k (by decide : 0 < 3))
        have hr : ((k % 3 : ℕ) : ℤ) % 3 = ((k % 3 : ℕ) : ℤ) := by
          apply Int.emod_eq_of_lt
          · exact Int.natCast_nonneg (k % 3)
          · exact hrlt
        have hmod' : (k : ℤ) % 3 = 1 := by
          simpa using hmod
        rw [hrem, hr] at hmod'
        exact Nat.cast_injective hmod'
      have hk4 : 4 ≤ k := by omega
      have hnat : (Int.ofNat k).natAbs = k := Int.natAbs_natCast k
      have hcast : ((2 * k + 1 : ℕ) : ℤ) = 2 * (Int.ofNat k) + 1 := by
        simp
      have habs : (2 * (Int.ofNat k) + 1).natAbs = 2 * k + 1 := by
        rw [← hcast]
        exact Int.natAbs_natCast (2 * k + 1)
      rw [habs, hnat]
      omega
    }
  | negSucc k => {
      have hneg : 2 * (Int.negSucc k) + 1 =
          -((2 * (k + 1) - 1 : ℕ) : ℤ) := by
        simp [Int.negSucc_eq]
        omega
      have habs : (2 * (Int.negSucc k) + 1).natAbs =
          2 * (k + 1) - 1 := by
        rw [hneg, Int.natAbs_neg]
        exact Int.natAbs_natCast (2 * (k + 1) - 1)
      have hnat : (Int.negSucc k).natAbs = k + 1 := by simp
      rw [habs, hnat]
      omega
    }

/-- A residue-one return loses at least the factor `3/4`. -/
theorem FourThreeOne (n : ℤ) (hmod : n % (3 : ℤ) = 1)
    (hk : 2 ≤ n.natAbs) :
    4 * ((2 * n + 1) / 3).natAbs ≤ 3 * n.natAbs := by
  have hdvd := TwoMulSuccDiv n hmod
  have hcancel := CancelNatAbsThree (2 * n + 1) hdvd
  have hnum := FourAbsNine n hmod hk
  rw [← hcancel] at hnum
  have hleft : 4 * (3 * ((2 * n + 1) / 3).natAbs) =
      3 * (4 * ((2 * n + 1) / 3).natAbs) := by
    omega
  have hright : 9 * n.natAbs = 3 * (3 * n.natAbs) := by omega
  rw [hleft, hright] at hnum
  exact Nat.le_of_mul_le_mul_left hnum (by omega : 0 < 3)

/-- Equality in the residue-one factor holds only at `4`. -/
theorem ResidueOneEquality (n : ℤ) (hmod : n % (3 : ℤ) = 1)
    (hk : 2 ≤ n.natAbs)
    (heq : 4 * ((2 * n + 1) / 3).natAbs = 3 * n.natAbs) : n = 4 := by
  have hdvd := TwoMulSuccDiv n hmod
  have hcancel := CancelNatAbsThree (2 * n + 1) hdvd
  have hmul : 4 * (2 * n + 1).natAbs = 9 * n.natAbs := by
    calc
      4 * (2 * n + 1).natAbs
          = 4 * (3 * ((2 * n + 1) / 3).natAbs) := by rw [hcancel]
      _ = 3 * (4 * ((2 * n + 1) / 3).natAbs) := by omega
      _ = 3 * (3 * n.natAbs) := by rw [heq]
      _ = 9 * n.natAbs := by omega
  cases n with
  | ofNat k => {
      have hnat : (Int.ofNat k).natAbs = k := Int.natAbs_natCast k
      have hcast : ((2 * k + 1 : ℕ) : ℤ) = 2 * (Int.ofNat k) + 1 := by
        simp
      have habs : (2 * (Int.ofNat k) + 1).natAbs = 2 * k + 1 := by
        rw [← hcast]
        exact Int.natAbs_natCast (2 * k + 1)
      rw [habs, hnat] at hmul
      have hk4 : k = 4 := by omega
      simp [hk4]
    }
  | negSucc k => {
      have hneg : 2 * (Int.negSucc k) + 1 =
          -((2 * (k + 1) - 1 : ℕ) : ℤ) := by
        simp [Int.negSucc_eq]
        omega
      have habs : (2 * (Int.negSucc k) + 1).natAbs =
          2 * (k + 1) - 1 := by
        rw [hneg, Int.natAbs_neg]
        exact Int.natAbs_natCast (2 * (k + 1) - 1)
      have hnat : (Int.negSucc k).natAbs = k + 1 := by simp
      rw [habs, hnat] at hmul
      omega
    }

/-- A time-one hit meets the factor `3/4` with equality only at `4`. -/
theorem LengthTwoEqualitySeed (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (hk : 2 ≤ n.natAbs) (hhit : IsFirstHit p n 1)
    (heq : 4 * (RawStep p (Iterate (RawStep p) 1 n)).natAbs =
      3 * n.natAbs) : n = 4 := by
  rcases ResidueTrichotomy p hQ hC hD n with h0 | h1 | h2
  · {
      obtain ⟨_hmod, hhit0, _hquot⟩ := h0
      have hcontra : (1 : ℕ) = 0 :=
        FirstHitUnique p n 1 0 hhit hhit0
      omega
    }
  · {
      obtain ⟨hmod, _hhit1, _haff, hquot⟩ := h1
      rw [hquot] at heq
      exact ResidueOneEquality n hmod hk heq
    }
  · {
      exact False.elim (h2.2 1 hhit)
    }

/-- One exact return multiplies the absolute value by at most `3/4`. -/
theorem ChainStepFour (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (j : ℕ) (hhit : IsFirstHit p n j)
    (hk : 2 ≤ n.natAbs) :
    4 * (RawStep p (Iterate (RawStep p) j n)).natAbs ≤ 3 * n.natAbs := by
  rcases ResidueTrichotomy p hQ hC hD n with h0 | h1 | h2
  · {
      obtain ⟨_hmod, hhit0, hquot⟩ := h0
      have heq : j = 0 := FirstHitUnique p n j 0 hhit hhit0
      have hdvd : (3 : ℤ) ∣ n := by
        have hz : AffineState p.Q p.C 0 n = n := AffineStateZero p.Q p.C n
        rw [← hD, ← hz]
        exact hhit0.1
      rw [heq, hquot]
      exact FourThreeDiv n hdvd
    }
  · {
      obtain ⟨hmod, hhit1, _haff, hquot⟩ := h1
      have heq : j = 1 := FirstHitUnique p n j 1 hhit hhit1
      rw [heq, hquot]
      exact FourThreeOne n hmod hk
    }
  · {
      exact False.elim (h2.2 j hhit)
    }

/-- Absolute values along a chain obey the factor `3/4` at every step. -/
theorem ChainFourThree (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hbig : ∀ t : ℕ, t < m → 2 ≤ (s t).natAbs)
    (i : ℕ) (hi : i ≤ m) :
    4 ^ i * (s i).natAbs ≤ 3 ^ i * n.natAbs := by
  induction i with
  | zero => {
      rw [hs0]
      simp
    }
  | succ t ih => {
      have ht : t < m := Nat.lt_of_succ_le hi
      have hdrop0 :=
        ChainStepFour p hQ hC hD (s t) (L t) (hL t ht).1 (hbig t ht)
      have hdrop :
          4 * (s (t + 1)).natAbs ≤ 3 * (s t).natAbs := by
        rw [(hL t ht).2] at hdrop0
        exact hdrop0
      have iht := ih (Nat.le_of_lt ht)
      have hleft :
          4 ^ (t + 1) * (s (t + 1)).natAbs =
            4 ^ t * (4 * (s (t + 1)).natAbs) := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      have hmid :
          4 ^ t * (4 * (s (t + 1)).natAbs) ≤
            4 ^ t * (3 * (s t).natAbs) :=
        Nat.mul_le_mul_left _ hdrop
      have hcomm :
          4 ^ t * (3 * (s t).natAbs) =
            3 * (4 ^ t * (s t).natAbs) := by
        rw [Nat.mul_left_comm]
      have hend :
          3 * (4 ^ t * (s t).natAbs) ≤
            3 * (3 ^ t * n.natAbs) :=
        Nat.mul_le_mul_left _ iht
      have hpow :
          3 * (3 ^ t * n.natAbs) = 3 ^ (t + 1) * n.natAbs := by
        calc
          3 * (3 ^ t * n.natAbs) = (3 * 3 ^ t) * n.natAbs := by
            rw [Nat.mul_assoc]
          _ = (3 ^ t * 3) * n.natAbs := by
            rw [Nat.mul_comm 3 (3 ^ t)]
          _ = 3 ^ (t + 1) * n.natAbs := by
            rw [← Nat.pow_succ]
      calc
        4 ^ (t + 1) * (s (t + 1)).natAbs
            = 4 ^ t * (4 * (s (t + 1)).natAbs) := hleft
        _ ≤ 4 ^ t * (3 * (s t).natAbs) := hmid
        _ = 3 * (4 ^ t * (s t).natAbs) := hcomm
        _ ≤ 3 * (3 ^ t * n.natAbs) := hend
        _ = 3 ^ (t + 1) * n.natAbs := hpow
    }

/-- A minimal chain to `1` or `-1` satisfies `4 ^ m ≤ 3 ^ m * |n|`. -/
theorem ReturnFourThree (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hsm : s m = 1 ∨ s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ s m)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) :
    4 ^ m ≤ 3 ^ m * n.natAbs := by
  have hbig := ProperTermsLarge p hQ hC hD n m s L hs0 hsm hsmin hL
  have hfac :=
    ChainFourThree p hQ hC hD n m s L hs0 hL hbig m (Nat.le_refl m)
  rcases hsm with hpos | hneg
  · {
      rw [hpos] at hfac
      simpa using hfac
    }
  · {
      rw [hneg] at hfac
      simpa using hfac
    }

/-- An orbit that meets `1` has return count `m` with `4 ^ m ≤ 3 ^ m * |n|`. -/
theorem HitOneFourThree (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ k : ℕ, Iterate (RawStep p) k n = 1) :
    ∃ m : ℕ, 4 ^ m ≤ 3 ^ m * n.natAbs := by
  classical
  obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
    ReturnChainToOne p hQ hC hD n h
  let L : ℕ → ℕ := fun i =>
    if hi : i < m then Classical.choose (hstep i hi) else 0
  have hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1) := by
    intro i hi
    have hspec := Classical.choose_spec (hstep i hi)
    have hLi : L i = Classical.choose (hstep i hi) := by
      simp [L, hi]
    rw [hLi]
    exact hspec
  have hsm' : s m = 1 ∨ s m = -1 := Or.inl hsm
  have hsmin' : ∀ i : ℕ, i < m → s i ≠ s m := by
    intro i hi
    rw [hsm]
    exact hsmin i hi
  exact ⟨m, ReturnFourThree p hQ hC hD n m s L hs0 hsm' hsmin' hL⟩

/-- An orbit that meets `-1` has return count `m` with `4 ^ m ≤ 3 ^ m * |n|`. -/
theorem HitNegOneFourThree (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ k : ℕ, Iterate (RawStep p) k n = -1) :
    ∃ m : ℕ, 4 ^ m ≤ 3 ^ m * n.natAbs := by
  classical
  obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
    ReturnChainToNegOne p hQ hC hD n h
  let L : ℕ → ℕ := fun i =>
    if hi : i < m then Classical.choose (hstep i hi) else 0
  have hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1) := by
    intro i hi
    have hspec := Classical.choose_spec (hstep i hi)
    have hLi : L i = Classical.choose (hstep i hi) := by
      simp [L, hi]
    rw [hLi]
    exact hspec
  have hsm' : s m = 1 ∨ s m = -1 := Or.inr hsm
  have hsmin' : ∀ i : ℕ, i < m → s i ≠ s m := by
    intro i hi
    rw [hsm]
    exact hsmin i hi
  exact ⟨m, ReturnFourThree p hQ hC hD n m s L hs0 hsm' hsmin' hL⟩

/-- A first hit under `(2,1,3)` occurs at time `0` or time `1`. -/
theorem FirstHitIsZeroOrOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (j : ℕ) (hhit : IsFirstHit p n j) :
    j = 0 ∨ j = 1 := by
  rcases ResidueTrichotomy p hQ hC hD n with h0 | h1 | h2
  · {
      exact Or.inl (FirstHitUnique p n j 0 hhit h0.2.1)
    }
  · {
      exact Or.inr (FirstHitUnique p n j 1 hhit h1.2.1)
    }
  · {
      exact False.elim (h2.2 j hhit)
    }

/-- `3 ^ d ≤ 4 ^ d`. -/
theorem ThreeLeFourPow (d : ℕ) : 3 ^ d ≤ 4 ^ d := by
  induction d with
  | zero => {
      simp
    }
  | succ t ih => {
      calc
        3 ^ (t + 1) = 3 ^ t * 3 := by rw [Nat.pow_succ]
        _ ≤ 4 ^ t * 3 := Nat.mul_le_mul_right _ ih
        _ ≤ 4 ^ t * 4 := Nat.mul_le_mul_left _ (by omega)
        _ = 4 ^ (t + 1) := by rw [← Nat.pow_succ]
    }

/-- A smaller exponent preserves `4 ^ m ≤ 3 ^ m * N`. -/
theorem FourThreeDown (t m N : ℕ) (ht : t ≤ m)
    (h : 4 ^ m ≤ 3 ^ m * N) :
    4 ^ t ≤ 3 ^ t * N := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
  rw [hd] at h
  have h3 : 3 ^ d ≤ 4 ^ d := ThreeLeFourPow d
  have hleft : 4 ^ t * 3 ^ d ≤ 4 ^ t * 4 ^ d :=
    Nat.mul_le_mul_left _ h3
  have hpow4 : 4 ^ t * 4 ^ d = 4 ^ (t + d) := by
    rw [← Nat.pow_add]
  have hpow3 : 3 ^ (t + d) = 3 ^ t * 3 ^ d := by
    rw [Nat.pow_add]
  have hmid : 4 ^ t * 3 ^ d ≤ 3 ^ t * 3 ^ d * N := by
    calc
      4 ^ t * 3 ^ d ≤ 4 ^ t * 4 ^ d := hleft
      _ = 4 ^ (t + d) := hpow4
      _ ≤ 3 ^ (t + d) * N := h
      _ = 3 ^ t * 3 ^ d * N := by
        rw [hpow3, Nat.mul_assoc]
  have hpos : 0 < 3 ^ d := Nat.pow_pos (by omega : 0 < 3)
  have hcomm : 3 ^ t * 3 ^ d * N = 3 ^ d * (3 ^ t * N) := by
    calc
      3 ^ t * 3 ^ d * N = 3 ^ d * 3 ^ t * N := by
        rw [Nat.mul_comm (3 ^ t) (3 ^ d)]
      _ = 3 ^ d * (3 ^ t * N) := by
        rw [Nat.mul_assoc]
  rw [hcomm] at hmid
  have hswap : 4 ^ t * 3 ^ d = 3 ^ d * 4 ^ t := Nat.mul_comm _ _
  rw [hswap] at hmid
  exact Nat.le_of_mul_le_mul_left hmid hpos

/-- If every block length is `0` or `1`, the raw sum lies between `m` and `2m`. -/
theorem LengthBetween (m : ℕ) (L : ℕ → ℕ)
    (hL : ∀ i : ℕ, i < m → L i ≤ 1) :
    m ≤ RawLengthSum L m ∧ RawLengthSum L m ≤ 2 * m := by
  induction m with
  | zero => {
      simp [RawLengthSum]
    }
  | succ t ih => {
      have ht : L t ≤ 1 := hL t (Nat.lt_succ_self t)
      have ih' := ih (fun i hi => hL i (Nat.lt_succ_of_lt hi))
      have hrec : RawLengthSum L (t + 1) =
          RawLengthSum L t + (L t + 1) := rfl
      constructor
      · {
          rw [hrec]
          omega
        }
      · {
          rw [hrec]
          omega
        }
    }

/-- The first visit to `1` satisfies the factor bound at half the raw time. -/
theorem HitOneTimeFourThree (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ k : ℕ, Iterate (RawStep p) k n = 1) :
    ∃ k : ℕ, Iterate (RawStep p) k n = 1 ∧
      (∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ 1) ∧
      4 ^ ((k + 1) / 2) ≤ 3 ^ ((k + 1) / 2) * n.natAbs := by
  classical
  obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
    ReturnChainToOne p hQ hC hD n h
  let L : ℕ → ℕ := fun i =>
    if hi : i < m then Classical.choose (hstep i hi) else 0
  have hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1) := by
    intro i hi
    have hspec := Classical.choose_spec (hstep i hi)
    have hLi : L i = Classical.choose (hstep i hi) := by
      simp [L, hi]
    rw [hLi]
    exact hspec
  let pred : ℕ → Prop := fun i => Iterate (RawStep p) i n = 1
  have hex : ∃ i : ℕ, pred i := h
  let k := Nat.find hex
  have hk : pred k := Nat.find_spec hex
  have hkmin : ∀ i : ℕ, i < k → ¬ pred i :=
    fun i hi => Nat.find_min hex hi
  have hsum : RawLengthSum L m = k :=
    ReturnChainAddsToHit p hQ hC hD n m k s L hs0 hsm hsmin hL hk
      (fun i hi => hkmin i hi)
  have hlen : ∀ i : ℕ, i < m → L i ≤ 1 := by
    intro i hi
    rcases FirstHitIsZeroOrOne p hQ hC hD (s i) (L i) (hL i hi).1
      with h0 | h1
    · {
        rw [h0]
        exact Nat.zero_le 1
      }
    · {
        exact Nat.le_of_eq h1
      }
  have hbounds := LengthBetween m L hlen
  have hk2 : k ≤ 2 * m := by
    rw [← hsum]
    exact hbounds.2
  have ht : (k + 1) / 2 ≤ m := by
    have hden : (2 * m + 1) / 2 = m := by omega
    have hle : k + 1 ≤ 2 * m + 1 := by omega
    have hdiv : (k + 1) / 2 ≤ (2 * m + 1) / 2 :=
      Nat.div_le_div_right hle
    rw [hden] at hdiv
    exact hdiv
  have hfac : 4 ^ m ≤ 3 ^ m * n.natAbs := by
    have hsm' : s m = 1 ∨ s m = -1 := Or.inl hsm
    have hsmin' : ∀ i : ℕ, i < m → s i ≠ s m := by
      intro i hi
      rw [hsm]
      exact hsmin i hi
    exact ReturnFourThree p hQ hC hD n m s L hs0 hsm' hsmin' hL
  exact ⟨k, hk, fun i hi => hkmin i hi,
    FourThreeDown ((k + 1) / 2) m n.natAbs ht hfac⟩

/-- The first visit to `-1` satisfies the factor bound at half the raw time. -/
theorem HitNegOneTimeFourThree (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ k : ℕ, Iterate (RawStep p) k n = -1) :
    ∃ k : ℕ, Iterate (RawStep p) k n = -1 ∧
      (∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ -1) ∧
      4 ^ ((k + 1) / 2) ≤ 3 ^ ((k + 1) / 2) * n.natAbs := by
  classical
  obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
    ReturnChainToNegOne p hQ hC hD n h
  let L : ℕ → ℕ := fun i =>
    if hi : i < m then Classical.choose (hstep i hi) else 0
  have hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1) := by
    intro i hi
    have hspec := Classical.choose_spec (hstep i hi)
    have hLi : L i = Classical.choose (hstep i hi) := by
      simp [L, hi]
    rw [hLi]
    exact hspec
  let pred : ℕ → Prop := fun i => Iterate (RawStep p) i n = -1
  have hex : ∃ i : ℕ, pred i := h
  let k := Nat.find hex
  have hk : pred k := Nat.find_spec hex
  have hkmin : ∀ i : ℕ, i < k → ¬ pred i :=
    fun i hi => Nat.find_min hex hi
  have hsum : RawLengthSum L m = k :=
    ReturnChainAddsToNegOne p hQ hC hD n m k s L hs0 hsm hsmin hL hk
      (fun i hi => hkmin i hi)
  have hlen : ∀ i : ℕ, i < m → L i ≤ 1 := by
    intro i hi
    rcases FirstHitIsZeroOrOne p hQ hC hD (s i) (L i) (hL i hi).1
      with h0 | h1
    · {
        rw [h0]
        exact Nat.zero_le 1
      }
    · {
        exact Nat.le_of_eq h1
      }
  have hbounds := LengthBetween m L hlen
  have hk2 : k ≤ 2 * m := by
    rw [← hsum]
    exact hbounds.2
  have ht : (k + 1) / 2 ≤ m := by
    have hden : (2 * m + 1) / 2 = m := by omega
    have hle : k + 1 ≤ 2 * m + 1 := by omega
    have hdiv : (k + 1) / 2 ≤ (2 * m + 1) / 2 :=
      Nat.div_le_div_right hle
    rw [hden] at hdiv
    exact hdiv
  have hfac : 4 ^ m ≤ 3 ^ m * n.natAbs := by
    have hsm' : s m = 1 ∨ s m = -1 := Or.inr hsm
    have hsmin' : ∀ i : ℕ, i < m → s i ≠ s m := by
      intro i hi
      rw [hsm]
      exact hsmin i hi
    exact ReturnFourThree p hQ hC hD n m s L hs0 hsm' hsmin' hL
  exact ⟨k, hk, fun i hi => hkmin i hi,
    FourThreeDown ((k + 1) / 2) m n.natAbs ht hfac⟩

/-- A hit at time zero divides the absolute value by exactly three. -/
theorem ExactTriple (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (hhit : IsFirstHit p n 0) :
    3 * (RawStep p (Iterate (RawStep p) 0 n)).natAbs = n.natAbs := by
  rcases ResidueTrichotomy p hQ hC hD n with h0 | h1 | h2
  · {
      have hdvd : (3 : ℤ) ∣ n := by
        have hz : AffineState p.Q p.C 0 n = n :=
          AffineStateZero p.Q p.C n
        rw [← hD, ← hz]
        exact h0.2.1.1
      rw [h0.2.2]
      exact CancelNatAbsThree n hdvd
    }
  · {
      have heq := FirstHitUnique p n 0 1 hhit h1.2.1
      omega
    }
  · {
      exact False.elim (h2.2 0 hhit)
    }

/-- Number of length-one blocks among the first `i` steps. -/
def ZeroSteps (L : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | Nat.succ t => ZeroSteps L t + if L t = 0 then 1 else 0

/-- Number of length-two blocks among the first `i` steps. -/
def OneSteps (L : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | Nat.succ t => OneSteps L t + if L t = 1 then 1 else 0

/-- Equal block lengths give equal counts. -/
theorem StepsAgree (m : ℕ) (L M : ℕ → ℕ)
    (h : ∀ i : ℕ, i < m → L i = M i) :
    ZeroSteps L m = ZeroSteps M m ∧ OneSteps L m = OneSteps M m := by
  induction m with
  | zero => {
      simp [ZeroSteps, OneSteps]
    }
  | succ t ih => {
      have ih' := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
      have ht : L t = M t := h t (Nat.lt_succ_self t)
      constructor
      · {
          simp [ZeroSteps, ih'.1, ht]
        }
      · {
          simp [OneSteps, ih'.2, ht]
        }
    }

/-- The two block counts recover the return count and the raw time. -/
theorem StepsPartition (m : ℕ) (L : ℕ → ℕ)
    (hL : ∀ i : ℕ, i < m → L i = 0 ∨ L i = 1) :
    ZeroSteps L m + OneSteps L m = m ∧
      ZeroSteps L m + 2 * OneSteps L m = RawLengthSum L m := by
  induction m with
  | zero => {
      simp [ZeroSteps, OneSteps, RawLengthSum]
    }
  | succ t ih => {
      have ht := hL t (Nat.lt_succ_self t)
      have ih' := ih (fun i hi => hL i (Nat.lt_succ_of_lt hi))
      have hz : ZeroSteps L (t + 1) =
          ZeroSteps L t + if L t = 0 then 1 else 0 := rfl
      have ho : OneSteps L (t + 1) =
          OneSteps L t + if L t = 1 then 1 else 0 := rfl
      have hr : RawLengthSum L (t + 1) =
          RawLengthSum L t + (L t + 1) := rfl
      rcases ht with h0 | h1
      · {
          rw [hz, ho, hr, h0]
          simp
          constructor
          · omega
          · omega
        }
      · {
          rw [hz, ho, hr, h1]
          simp
          constructor
          · omega
          · omega
        }
    }

/-- Each block contributes its own factor, not a uniform `3/4`. -/
theorem MixedChain (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hbig : ∀ t : ℕ, t < m → 2 ≤ (s t).natAbs)
    (i : ℕ) (hi : i ≤ m) :
    3 ^ ZeroSteps L i * 4 ^ OneSteps L i * (s i).natAbs ≤
      3 ^ OneSteps L i * n.natAbs := by
  induction i with
  | zero => {
      rw [hs0]
      simp [ZeroSteps, OneSteps]
    }
  | succ t ih => {
      have ht : t < m := Nat.lt_of_succ_le hi
      have iht := ih (Nat.le_of_lt ht)
      have hkind :=
        FirstHitIsZeroOrOne p hQ hC hD (s t) (L t) (hL t ht).1
      have hz : ZeroSteps L (t + 1) =
          ZeroSteps L t + if L t = 0 then 1 else 0 := rfl
      have ho : OneSteps L (t + 1) =
          OneSteps L t + if L t = 1 then 1 else 0 := rfl
      rcases hkind with h0 | h1
      · {
          have hhit0 : IsFirstHit p (s t) 0 := by
            simpa [h0] using (hL t ht).1
          have htri :
              3 * (s (t + 1)).natAbs = (s t).natAbs := by
            have hraw := ExactTriple p hQ hC hD (s t) hhit0
            have hstep :
                RawStep p (Iterate (RawStep p) 0 (s t)) =
                  s (t + 1) := by
              simpa [h0] using (hL t ht).2
            rw [hstep] at hraw
            exact hraw
          rw [hz, ho, h0]
          simp
          have hleft :
              3 ^ (ZeroSteps L t + 1) * 4 ^ OneSteps L t *
                  (s (t + 1)).natAbs =
                3 ^ ZeroSteps L t * 4 ^ OneSteps L t *
                  (s t).natAbs := by
            let a := 3 ^ ZeroSteps L t
            let b := 4 ^ OneSteps L t
            let c := (s (t + 1)).natAbs
            have hmove : a * 3 * b * c = a * b * (3 * c) := by
              calc
                a * 3 * b * c = a * (3 * b) * c := by
                  rw [Nat.mul_assoc a 3 b]
                _ = a * (b * 3) * c := by
                  rw [Nat.mul_comm 3 b]
                _ = a * b * 3 * c := by
                  rw [← Nat.mul_assoc a b 3]
                _ = a * b * (3 * c) := by
                  rw [Nat.mul_assoc (a * b) 3 c]
            calc
              3 ^ (ZeroSteps L t + 1) * 4 ^ OneSteps L t *
                    (s (t + 1)).natAbs
                  = a * 3 * b * c := by
                    rw [Nat.pow_succ]
              _ = a * b * (3 * c) := hmove
              _ = 3 ^ ZeroSteps L t * 4 ^ OneSteps L t *
                    (s t).natAbs := by
                    rw [htri]
          rw [hleft]
          exact iht
        }
      · {
          have hdrop :
              4 * (s (t + 1)).natAbs ≤ 3 * (s t).natAbs := by
            have hraw :=
              ChainStepFour p hQ hC hD (s t) (L t) (hL t ht).1
                (hbig t ht)
            rw [(hL t ht).2] at hraw
            exact hraw
          rw [hz, ho, h1]
          simp
          have hleft :
              3 ^ ZeroSteps L t * 4 ^ (OneSteps L t + 1) *
                  (s (t + 1)).natAbs ≤
                3 ^ (OneSteps L t + 1) * n.natAbs := by
            let a := 3 ^ ZeroSteps L t
            let b := 4 ^ OneSteps L t
            let c := (s (t + 1)).natAbs
            let u := (s t).natAbs
            have hsplit :
                a * 4 ^ (OneSteps L t + 1) * c =
                  a * b * (4 * c) := by
              calc
                a * 4 ^ (OneSteps L t + 1) * c =
                    a * (b * 4) * c := by
                      rw [Nat.pow_succ]
                _ = a * b * 4 * c := by
                  rw [← Nat.mul_assoc a b 4]
                _ = a * b * (4 * c) := by
                  rw [Nat.mul_assoc (a * b) 4 c]
            have hdrop' : a * b * (4 * c) ≤ a * b * (3 * u) := by
              rw [hsplit] at *
              exact Nat.mul_le_mul_left (a * b) hdrop
            have hmove : a * b * (3 * u) = 3 * (a * b * u) := by
              calc
                a * b * (3 * u) = a * b * 3 * u := by
                  rw [← Nat.mul_assoc (a * b) 3 u]
                _ = 3 * (a * b) * u := by
                  rw [Nat.mul_comm (a * b) 3]
                _ = 3 * (a * b * u) := by
                  rw [Nat.mul_assoc 3 (a * b) u]
            have hpow :
                3 * (3 ^ OneSteps L t * n.natAbs) =
                  3 ^ (OneSteps L t + 1) * n.natAbs := by
              calc
                3 * (3 ^ OneSteps L t * n.natAbs) =
                    (3 * 3 ^ OneSteps L t) * n.natAbs := by
                      rw [← Nat.mul_assoc]
                _ = (3 ^ OneSteps L t * 3) * n.natAbs := by
                  rw [Nat.mul_comm 3 (3 ^ OneSteps L t)]
                _ = 3 ^ (OneSteps L t + 1) * n.natAbs := by
                  rw [← Nat.pow_succ]
            have hmul := Nat.mul_le_mul_left 3 iht
            calc
              3 ^ ZeroSteps L t * 4 ^ (OneSteps L t + 1) *
                    (s (t + 1)).natAbs
                  = a * b * (4 * c) := hsplit
              _ ≤ a * b * (3 * u) := hdrop'
              _ = 3 * (a * b * u) := hmove
              _ ≤ 3 * (3 ^ OneSteps L t * n.natAbs) := hmul
              _ = 3 ^ (OneSteps L t + 1) * n.natAbs := hpow
          exact hleft
        }
    }

/-- Product equality puts the seed `4` at every length-two block. -/
theorem MixedEqualityForcesFour (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hbig : ∀ t : ℕ, t < m → 2 ≤ (s t).natAbs)
    (i : ℕ) (hi : i ≤ m)
    (heq : 3 ^ ZeroSteps L i * 4 ^ OneSteps L i * (s i).natAbs =
      3 ^ OneSteps L i * n.natAbs) :
    ∀ t : ℕ, t < i → L t = 1 → s t = 4 := by
  induction i with
  | zero => {
      intro t ht
      omega
    }
  | succ r ih => {
      intro t ht hLt
      have hr : r < m := Nat.lt_of_succ_le hi
      have hkind :=
        FirstHitIsZeroOrOne p hQ hC hD (s r) (L r) (hL r hr).1
      have hprev :
          3 ^ ZeroSteps L r * 4 ^ OneSteps L r * (s r).natAbs =
            3 ^ OneSteps L r * n.natAbs := by
        rcases hkind with h0 | h1
        · {
            have hhit0 : IsFirstHit p (s r) 0 := by
              simpa [h0] using (hL r hr).1
            have htri : 3 * (s (r + 1)).natAbs = (s r).natAbs := by
              have hraw := ExactTriple p hQ hC hD (s r) hhit0
              have hstep :
                  RawStep p (Iterate (RawStep p) 0 (s r)) =
                    s (r + 1) := by
                simpa [h0] using (hL r hr).2
              rw [hstep] at hraw
              exact hraw
            have hleft :
                3 ^ ZeroSteps L (r + 1) * 4 ^ OneSteps L (r + 1) *
                    (s (r + 1)).natAbs =
                  3 ^ ZeroSteps L r * 4 ^ OneSteps L r *
                    (s r).natAbs := by
              have hz : ZeroSteps L (r + 1) =
                  ZeroSteps L r + if L r = 0 then 1 else 0 := rfl
              have ho : OneSteps L (r + 1) =
                  OneSteps L r + if L r = 1 then 1 else 0 := rfl
              rw [hz, ho, h0]
              simp
              calc
                3 ^ (ZeroSteps L r + 1) * 4 ^ OneSteps L r *
                      (s (r + 1)).natAbs
                    = 3 ^ ZeroSteps L r * 3 * 4 ^ OneSteps L r *
                        (s (r + 1)).natAbs := by
                      rw [Nat.pow_succ]
                _ = 3 ^ ZeroSteps L r * 4 ^ OneSteps L r *
                      (3 * (s (r + 1)).natAbs) := by
                      ring
                _ = 3 ^ ZeroSteps L r * 4 ^ OneSteps L r *
                      (s r).natAbs := by
                      rw [htri]
            have ho0 : OneSteps L (r + 1) = OneSteps L r := by
              have hdef : OneSteps L (r + 1) =
                  OneSteps L r + if L r = 1 then 1 else 0 := rfl
              rw [hdef, h0]
              simp
            rw [hleft] at heq
            rw [ho0] at heq
            exact heq
          }
        · {
            have hdrop :
                4 * (s (r + 1)).natAbs ≤ 3 * (s r).natAbs := by
              have hraw :=
                ChainStepFour p hQ hC hD (s r) (L r) (hL r hr).1
                  (hbig r hr)
              rw [(hL r hr).2] at hraw
              exact hraw
            let a := 3 ^ ZeroSteps L r
            let b := 4 ^ OneSteps L r
            let c := (s (r + 1)).natAbs
            let u := (s r).natAbs
            have hsplit :
                a * 4 ^ (OneSteps L r + 1) * c = a * b * (4 * c) := by
              calc
                a * 4 ^ (OneSteps L r + 1) * c = a * (b * 4) * c := by
                  rw [Nat.pow_succ]
                _ = a * b * (4 * c) := by ring
            have hmove : a * b * (3 * u) = 3 * (a * b * u) := by ring
            have hnew :
                3 ^ ZeroSteps L (r + 1) * 4 ^ OneSteps L (r + 1) *
                    (s (r + 1)).natAbs =
                  a * b * (4 * c) := by
              have hz : ZeroSteps L (r + 1) =
                  ZeroSteps L r + if L r = 0 then 1 else 0 := rfl
              have ho : OneSteps L (r + 1) =
                  OneSteps L r + if L r = 1 then 1 else 0 := rfl
              rw [hz, ho, h1]
              simp
              exact hsplit
            have hab : 0 < a * b :=
              Nat.mul_pos (Nat.pow_pos (by decide))
                (Nat.pow_pos (by decide))
            have hle1 : a * b * (4 * c) ≤ a * b * (3 * u) :=
              Nat.mul_le_mul_left (a * b) hdrop
            have hprevle :=
              MixedChain p hQ hC hD n m s L hs0 hL hbig r
                (Nat.le_of_lt hr)
            have hle2 : 3 * (a * b * u) ≤
                3 * (3 ^ OneSteps L r * n.natAbs) :=
              Nat.mul_le_mul_left 3 hprevle
            have hends : a * b * (4 * c) =
                3 * (3 ^ OneSteps L r * n.natAbs) := by
              calc
                a * b * (4 * c) =
                    3 ^ ZeroSteps L (r + 1) *
                      4 ^ OneSteps L (r + 1) *
                      (s (r + 1)).natAbs := by
                    exact hnew.symm
                _ = 3 ^ OneSteps L (r + 1) * n.natAbs := heq
                _ = 3 * (3 ^ OneSteps L r * n.natAbs) := by
                    have ho : OneSteps L (r + 1) =
                        OneSteps L r + 1 := by
                      have hdef : OneSteps L (r + 1) =
                          OneSteps L r +
                            if L r = 1 then 1 else 0 := rfl
                      rw [hdef, h1]
                      simp
                    rw [ho, Nat.pow_succ]
                    ring
            have hmid : a * b * (4 * c) = a * b * (3 * u) := by
              apply Nat.le_antisymm hle1
              calc
                a * b * (3 * u) = 3 * (a * b * u) := hmove
                _ ≤ 3 * (3 ^ OneSteps L r * n.natAbs) := hle2
                _ = a * b * (4 * c) := hends.symm
            have hdrop_eq : 4 * c = 3 * u :=
              Nat.eq_of_mul_eq_mul_left hab hmid
            have hprev_eq : a * b * u =
                3 ^ OneSteps L r * n.natAbs := by
              have h3 : a * b * (3 * u) =
                  3 * (3 ^ OneSteps L r * n.natAbs) := by
                rw [← hmid, hends]
              have hmove' : 3 * (a * b * u) =
                  3 * (3 ^ OneSteps L r * n.natAbs) := by
                rw [← hmove, h3]
              exact Nat.eq_of_mul_eq_mul_left (by decide) hmove'
            exact hprev_eq
          }
      have ht' : t < r ∨ t = r := Nat.lt_succ_iff_lt_or_eq.mp ht
      rcases ht' with htr | heqr
      · {
          exact ih (Nat.le_of_lt hr) hprev t htr hLt
        }
      · {
          have hLr : L r = 1 := by rw [← heqr]; exact hLt
          have hhit : IsFirstHit p (s r) 1 := by
            simpa [hLr] using (hL r hr).1
          have hnew :
              3 ^ ZeroSteps L (r + 1) * 4 ^ OneSteps L (r + 1) *
                  (s (r + 1)).natAbs =
                3 ^ ZeroSteps L r * 4 ^ OneSteps L r *
                  (4 * (s (r + 1)).natAbs) := by
            have hz : ZeroSteps L (r + 1) =
                ZeroSteps L r + if L r = 0 then 1 else 0 := rfl
            have ho : OneSteps L (r + 1) =
                OneSteps L r + if L r = 1 then 1 else 0 := rfl
            rw [hz, ho, hLr]
            simp
            calc
              3 ^ ZeroSteps L r * 4 ^ (OneSteps L r + 1) *
                    (s (r + 1)).natAbs
                  = 3 ^ ZeroSteps L r *
                      (4 ^ OneSteps L r * 4) *
                      (s (r + 1)).natAbs := by
                    rw [Nat.pow_succ]
              _ = 3 ^ ZeroSteps L r * 4 ^ OneSteps L r *
                    (4 * (s (r + 1)).natAbs) := by
                    ring
          have hright :
              3 ^ OneSteps L (r + 1) * n.natAbs =
                3 ^ ZeroSteps L r * 4 ^ OneSteps L r *
                  (3 * (s r).natAbs) := by
            have ho : OneSteps L (r + 1) = OneSteps L r + 1 := by
              have hdef : OneSteps L (r + 1) =
                  OneSteps L r + if L r = 1 then 1 else 0 := rfl
              rw [hdef, hLr]
              simp
            calc
              3 ^ OneSteps L (r + 1) * n.natAbs
                  = 3 ^ (OneSteps L r + 1) * n.natAbs := by rw [ho]
              _ = 3 ^ OneSteps L r * 3 * n.natAbs := by
                  rw [Nat.pow_succ]
              _ = 3 * (3 ^ OneSteps L r * n.natAbs) := by ring
              _ = 3 * (3 ^ ZeroSteps L r * 4 ^ OneSteps L r *
                    (s r).natAbs) := by
                  rw [← hprev]
              _ = 3 ^ ZeroSteps L r * 4 ^ OneSteps L r *
                    (3 * (s r).natAbs) := by ring
          have hab : 0 < 3 ^ ZeroSteps L r * 4 ^ OneSteps L r :=
            Nat.mul_pos (Nat.pow_pos (by decide))
              (Nat.pow_pos (by decide))
          have hdrop :
              4 * (s (r + 1)).natAbs = 3 * (s r).natAbs := by
            have hmul :
                3 ^ ZeroSteps L r * 4 ^ OneSteps L r *
                    (4 * (s (r + 1)).natAbs) =
                  3 ^ ZeroSteps L r * 4 ^ OneSteps L r *
                    (3 * (s r).natAbs) := by
              calc
                3 ^ ZeroSteps L r * 4 ^ OneSteps L r *
                      (4 * (s (r + 1)).natAbs)
                    = 3 ^ ZeroSteps L (r + 1) *
                        4 ^ OneSteps L (r + 1) *
                        (s (r + 1)).natAbs := hnew.symm
                _ = 3 ^ OneSteps L (r + 1) * n.natAbs := heq
                _ = 3 ^ ZeroSteps L r * 4 ^ OneSteps L r *
                      (3 * (s r).natAbs) := hright
            exact Nat.eq_of_mul_eq_mul_left hab hmul
          have hraw' :
              RawStep p (Iterate (RawStep p) 1 (s r)) =
                s (r + 1) := by
            simpa [hLr] using (hL r hr).2
          have hstep :
              4 * (RawStep p (Iterate (RawStep p) 1 (s r))).natAbs =
                3 * (s r).natAbs := by
            rw [hraw']
            exact hdrop
          have hseed : s r = 4 :=
            LengthTwoEqualitySeed p hQ hC hD (s r)
              (hbig r hr) hhit hstep
          rw [heqr]
          exact hseed
        }
    }

/-- A minimal chain multiplies the exact block factors. -/
theorem MixedReturn (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hsm : s m = 1 ∨ s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ s m)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) :
    3 ^ ZeroSteps L m * 4 ^ OneSteps L m ≤
      3 ^ OneSteps L m * n.natAbs := by
  have hbig :=
    ProperTermsLarge p hQ hC hD n m s L hs0 hsm hsmin hL
  have hchain :=
    MixedChain p hQ hC hD n m s L hs0 hL hbig m (Nat.le_refl m)
  have habs : (s m).natAbs = 1 := by
    rcases hsm with h1 | hm1
    · {
        rw [h1]
        rfl
      }
    · {
        rw [hm1]
        rfl
      }
  rw [habs] at hchain
  simpa using hchain

/-- The first visit to `1` obeys the mixed block bound. -/
theorem HitOneMixed (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ k : ℕ, Iterate (RawStep p) k n = 1) :
    ∃ a0 a1 k : ℕ,
      Iterate (RawStep p) k n = 1 ∧
        (∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ 1) ∧
        a0 + a1 + a1 = k ∧
        3 ^ a0 * 4 ^ a1 ≤ 3 ^ a1 * n.natAbs := by
  classical
  obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
    ReturnChainToOne p hQ hC hD n h
  let L : ℕ → ℕ := fun i =>
    if hi : i < m then Classical.choose (hstep i hi) else 0
  have hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1) := by
    intro i hi
    have hspec := Classical.choose_spec (hstep i hi)
    have hLi : L i = Classical.choose (hstep i hi) := by
      simp [L, hi]
    rw [hLi]
    exact hspec
  let pred : ℕ → Prop := fun i => Iterate (RawStep p) i n = 1
  have hex : ∃ i : ℕ, pred i := h
  let k := Nat.find hex
  have hk : pred k := Nat.find_spec hex
  have hkmin : ∀ i : ℕ, i < k → ¬ pred i :=
    fun i hi => Nat.find_min hex hi
  have hsum : RawLengthSum L m = k :=
    ReturnChainAddsToHit p hQ hC hD n m k s L hs0 hsm hsmin hL hk
      (fun i hi => hkmin i hi)
  have hkind : ∀ i : ℕ, i < m → L i = 0 ∨ L i = 1 := by
    intro i hi
    exact FirstHitIsZeroOrOne p hQ hC hD (s i) (L i) (hL i hi).1
  have hpart := StepsPartition m L hkind
  have hfac :=
    MixedReturn p hQ hC hD n m s L hs0 (Or.inl hsm)
      (by intro i hi; rw [hsm]; exact hsmin i hi) hL
  refine ⟨ZeroSteps L m, OneSteps L m, k, hk, ?_, ?_, hfac⟩
  · intro i hi
    exact hkmin i hi
  · rw [← hsum, ← hpart.2]
    omega

/-- The first visit to `-1` obeys the mixed block bound. -/
theorem HitNegOneMixed (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ k : ℕ, Iterate (RawStep p) k n = -1) :
    ∃ a0 a1 k : ℕ,
      Iterate (RawStep p) k n = -1 ∧
        (∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ -1) ∧
        a0 + a1 + a1 = k ∧
        3 ^ a0 * 4 ^ a1 ≤ 3 ^ a1 * n.natAbs := by
  classical
  obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
    ReturnChainToNegOne p hQ hC hD n h
  let L : ℕ → ℕ := fun i =>
    if hi : i < m then Classical.choose (hstep i hi) else 0
  have hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1) := by
    intro i hi
    have hspec := Classical.choose_spec (hstep i hi)
    have hLi : L i = Classical.choose (hstep i hi) := by
      simp [L, hi]
    rw [hLi]
    exact hspec
  let pred : ℕ → Prop := fun i => Iterate (RawStep p) i n = -1
  have hex : ∃ i : ℕ, pred i := h
  let k := Nat.find hex
  have hk : pred k := Nat.find_spec hex
  have hkmin : ∀ i : ℕ, i < k → ¬ pred i :=
    fun i hi => Nat.find_min hex hi
  have hsum : RawLengthSum L m = k :=
    ReturnChainAddsToNegOne p hQ hC hD n m k s L hs0 hsm hsmin hL hk
      (fun i hi => hkmin i hi)
  have hkind : ∀ i : ℕ, i < m → L i = 0 ∨ L i = 1 := by
    intro i hi
    exact FirstHitIsZeroOrOne p hQ hC hD (s i) (L i) (hL i hi).1
  have hpart := StepsPartition m L hkind
  have hfac :=
    MixedReturn p hQ hC hD n m s L hs0 (Or.inr hsm)
      (by intro i hi; rw [hsm]; exact hsmin i hi) hL
  refine ⟨ZeroSteps L m, OneSteps L m, k, hk, ?_, ?_, hfac⟩
  · intro i hi
    exact hkmin i hi
  · rw [← hsum, ← hpart.2]
    omega

/-- A minimal chain determines the two block counts. -/
theorem MixedCountsUnique (p : Parameters) (n g : ℤ)
    (m r : ℕ) (s t : ℕ → ℤ) (L M : ℕ → ℕ)
    (hs0 : s 0 = n) (ht0 : t 0 = n)
    (hsm : s m = g) (htm : t r = g)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ g)
    (htmin : ∀ i : ℕ, i < r → t i ≠ g)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hM : ∀ i : ℕ, i < r →
      IsFirstHit p (t i) (M i) ∧
        RawStep p (Iterate (RawStep p) (M i) (t i)) = t (i + 1)) :
    m = r ∧ ZeroSteps L m = ZeroSteps M r ∧
      OneSteps L m = OneSteps M r := by
  have hsstep : ∀ i : ℕ, i < m → ∃ j : ℕ,
      IsFirstHit p (s i) j ∧
        RawStep p (Iterate (RawStep p) j (s i)) = s (i + 1) := by
    intro i hi
    exact ⟨L i, (hL i hi).1, (hL i hi).2⟩
  have htstep : ∀ i : ℕ, i < r → ∃ j : ℕ,
      IsFirstHit p (t i) j ∧
        RawStep p (Iterate (RawStep p) j (t i)) = t (i + 1) := by
    intro i hi
    exact ⟨M i, (hM i hi).1, (hM i hi).2⟩
  obtain ⟨hmr, hst⟩ :=
    ReturnChainUnique p n g m r s t hs0 ht0 hsm htm hsmin htmin
      hsstep htstep
  have hlen : ∀ i : ℕ, i < m → L i = M i := by
    intro i hi
    have hir : i < r := by
      rw [← hmr]
      exact hi
    have hsi : s i = t i := hst i (Nat.le_of_lt hi)
    have hhitM : IsFirstHit p (s i) (M i) := by
      have hMt := (hM i hir).1
      rw [← hsi] at hMt
      exact hMt
    exact FirstHitUnique p (s i) (L i) (M i) (hL i hi).1 hhitM
  have hcounts := StepsAgree m L M hlen
  refine ⟨hmr, ?_, ?_⟩
  · {
      rw [← hmr]
      exact hcounts.1
    }
  · {
      rw [← hmr]
      exact hcounts.2
    }

/-- The mixed bound, written with the return count and the raw time. -/
theorem MixedTimeForm (m k a0 a1 N : ℕ)
    (hsum : a0 + a1 = m) (htime : a0 + 2 * a1 = k)
    (hfac : 3 ^ a0 * 4 ^ a1 ≤ 3 ^ a1 * N) :
    3 ^ (2 * m - k) * 4 ^ (k - m) ≤ 3 ^ (k - m) * N := by
  have ha1 : a1 = k - m := by omega
  have ha0 : a0 = 2 * m - k := by omega
  rw [ha0, ha1] at hfac
  exact hfac

/-- Clearing the common power of three. -/
theorem MixedCleared (m k N : ℕ)
    (hm : m ≤ k) (hk : k ≤ 2 * m)
    (hfac : 3 ^ (2 * m - k) * 4 ^ (k - m) ≤ 3 ^ (k - m) * N) :
    (2 * k ≤ 3 * m →
      3 ^ (3 * m - 2 * k) * 4 ^ (k - m) ≤ N) ∧
    (3 * m ≤ 2 * k →
      4 ^ (k - m) ≤ 3 ^ (2 * k - 3 * m) * N) := by
  constructor
  · {
      intro hfew
      have hsplit :
          3 ^ (2 * m - k) =
            3 ^ (k - m) * 3 ^ (3 * m - 2 * k) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      rw [hsplit] at hfac
      let a : ℕ := 3 ^ (k - m)
      let b : ℕ := 3 ^ (3 * m - 2 * k)
      let c : ℕ := 4 ^ (k - m)
      have ha : a = 3 ^ (k - m) := rfl
      have hb : b = 3 ^ (3 * m - 2 * k) := rfl
      have hc : c = 4 ^ (k - m) := rfl
      rw [← ha, ← hb, ← hc] at hfac
      have hassoc : (a * b) * c = a * (b * c) := by
        ring
      rw [hassoc] at hfac
      have hpos : 0 < a := by
        rw [ha]
        exact Nat.pow_pos (by decide : 0 < 3)
      exact Nat.le_of_mul_le_mul_left hfac hpos
    }
  · {
      intro hmany
      have hsplit :
          3 ^ (k - m) =
            3 ^ (2 * m - k) * 3 ^ (2 * k - 3 * m) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      rw [hsplit] at hfac
      let a : ℕ := 3 ^ (2 * m - k)
      let b : ℕ := 3 ^ (2 * k - 3 * m)
      have ha : a = 3 ^ (2 * m - k) := rfl
      have hb : b = 3 ^ (2 * k - 3 * m) := rfl
      rw [← ha, ← hb] at hfac
      have hassoc : (a * b) * N = a * (b * N) := by
        ring
      rw [hassoc] at hfac
      have hpos : 0 < a := by
        rw [ha]
        exact Nat.pow_pos (by decide : 0 < 3)
      exact Nat.le_of_mul_le_mul_left hfac hpos
    }

/-- The same cancellation, stated only in the two block counts. -/
theorem MixedCountForm (a0 a1 N : ℕ)
    (hfac : 3 ^ a0 * 4 ^ a1 ≤ 3 ^ a1 * N) :
    (a1 ≤ a0 → 3 ^ (a0 - a1) * 4 ^ a1 ≤ N) ∧
    (a0 ≤ a1 → 4 ^ a1 ≤ 3 ^ (a1 - a0) * N) := by
  have hm : a0 + a1 ≤ a0 + 2 * a1 := by omega
  have hk : a0 + 2 * a1 ≤ 2 * (a0 + a1) := by omega
  have h0 : 2 * (a0 + a1) - (a0 + 2 * a1) = a0 := by omega
  have h1 : (a0 + 2 * a1) - (a0 + a1) = a1 := by omega
  have hfac' :
      3 ^ (2 * (a0 + a1) - (a0 + 2 * a1)) *
          4 ^ ((a0 + 2 * a1) - (a0 + a1)) ≤
        3 ^ ((a0 + 2 * a1) - (a0 + a1)) * N := by
    rw [h0, h1]
    exact hfac
  have hclear :=
    MixedCleared (a0 + a1) (a0 + 2 * a1) N hm hk hfac'
  constructor
  · {
      intro hfew
      have hfew' : 2 * (a0 + 2 * a1) ≤ 3 * (a0 + a1) := by omega
      have hleft := hclear.1 hfew'
      have hexp :
          3 * (a0 + a1) - 2 * (a0 + 2 * a1) = a0 - a1 := by omega
      rw [h1, hexp] at hleft
      exact hleft
    }
  · {
      intro hmany
      have hmany' : 3 * (a0 + a1) ≤ 2 * (a0 + 2 * a1) := by omega
      have hright := hclear.2 hmany'
      have hexp :
          2 * (a0 + 2 * a1) - 3 * (a0 + a1) = a1 - a0 := by omega
      rw [h1, hexp] at hright
      exact hright
    }

/-- Every block of the zero-length function is a length-one block. -/
theorem ZeroLengthCounts (t : ℕ) :
    ZeroSteps (fun _ : ℕ => 0) t = t ∧
      OneSteps (fun _ : ℕ => 0) t = 0 := by
  induction t with
  | zero => {
      constructor
      · {
          rfl
        }
      · {
          rfl
        }
    }
  | succ t ih => {
      constructor
      · {
          have hrec :
              ZeroSteps (fun _ : ℕ => 0) (t + 1) =
                ZeroSteps (fun _ : ℕ => 0) t + 1 := by
            simp [ZeroSteps]
          rw [hrec, ih.1]
        }
      · {
          have hrec :
              OneSteps (fun _ : ℕ => 0) (t + 1) =
                OneSteps (fun _ : ℕ => 0) t := by
            simp [OneSteps]
          rw [hrec, ih.2]
        }
    }

/-- A positive power of three is not `1`. -/
theorem ThreePowNeOne (k : ℕ) (hk : 0 < k) : (3 : ℤ) ^ k ≠ 1 := by
  intro heq
  have habs : ((3 : ℤ) ^ k).natAbs = 3 ^ k := by
    rw [Int.natAbs_pow]
    simp
  have hone : ((3 : ℤ) ^ k).natAbs = 1 := by
    rw [heq]
    decide
  have hbase : 3 ^ 1 ≤ 3 ^ k :=
    Nat.pow_le_pow_right (by decide) hk
  have hge : 3 ≤ 3 ^ k := by
    simpa using hbase
  omega

/-- The first `j` steps from `3 ^ t` are the later powers of three. -/
theorem PowerAt (p : Parameters) (hD : p.D = 3) (t j : ℕ)
    (hj : j ≤ t) :
    Iterate (RawStep p) j ((3 : ℤ) ^ t) = (3 : ℤ) ^ (t - j) := by
  induction j with
  | zero => {
      rfl
    }
  | succ j ih => {
      have hjle : j ≤ t := Nat.le_of_succ_le hj
      have hpred := ih hjle
      have hstep :
          Iterate (RawStep p) (j + 1) ((3 : ℤ) ^ t) =
            RawStep p (Iterate (RawStep p) j ((3 : ℤ) ^ t)) := rfl
      rw [hstep, hpred]
      have hsplit :
          (3 : ℤ) ^ (t - j) = 3 * (3 : ℤ) ^ (t - (j + 1)) := by
        have hsub : t - j = (t - (j + 1)) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      rw [hsplit]
      exact StepOfTriple p hD ((3 : ℤ) ^ (t - (j + 1)))
    }

/-- `3 ^ t` reaches `1` by `t` immediate divisions, with equality. -/
theorem PureDivisionEquality (p : Parameters) (hD : p.D = 3)
    (t : ℕ) :
    let n : ℤ := (3 : ℤ) ^ t
    let s : ℕ → ℤ := fun i => (3 : ℤ) ^ (t - i)
    let L : ℕ → ℕ := fun _ => 0
    Iterate (RawStep p) t n = 1 ∧
      (∀ j : ℕ, j < t → Iterate (RawStep p) j n ≠ 1) ∧
      s 0 = n ∧ s t = 1 ∧
      (∀ i : ℕ, i < t → s i ≠ 1) ∧
      (∀ i : ℕ, i < t →
        IsFirstHit p (s i) (L i) ∧
          RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) ∧
      ZeroSteps L t = t ∧ OneSteps L t = 0 ∧
      3 ^ ZeroSteps L t * 4 ^ OneSteps L t =
        3 ^ OneSteps L t * n.natAbs := by
  intro n s L
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · {
      have hpow := PowerAt p hD t t (le_refl t)
      simpa using hpow
    }
  · {
      intro j hj
      have hpow := PowerAt p hD t j (Nat.le_of_lt hj)
      rw [hpow]
      exact ThreePowNeOne (t - j) (Nat.sub_pos_of_lt hj)
    }
  · {
      show (3 : ℤ) ^ (t - t) = 1
      have hsub : t - t = 0 := Nat.sub_self t
      rw [hsub]
      simp
    }
  · {
      intro i hi
      exact ThreePowNeOne (t - i) (Nat.sub_pos_of_lt hi)
    }
  · {
      intro i hi
      refine ⟨?_, ?_⟩
      · {
          refine ⟨?_, ?_⟩
          · {
              rw [AffineStateZero, hD]
              have hs : s i = (3 : ℤ) ^ (t - i) := rfl
              rw [hs]
              refine ⟨(3 : ℤ) ^ (t - i - 1), ?_⟩
              have hexp :
                  (3 : ℤ) ^ (t - i) =
                    (3 : ℤ) ^ ((t - i - 1) + 1) := by
                have hsub : t - i = (t - i - 1) + 1 := by
                  omega
                conv_lhs => rw [hsub]
              rw [hexp, pow_succ]
              ring
            }
          · {
              intro u hu
              exact False.elim (Nat.not_lt_zero u hu)
            }
        }
      · {
          have hzero :
              Iterate (RawStep p) (L i) (s i) = s i := by
            have hL : L i = 0 := rfl
            rw [hL]
            rfl
          have hsplit :
              s i = 3 * (3 : ℤ) ^ (t - (i + 1)) := by
            have hsub : t - i = (t - (i + 1)) + 1 := by omega
            have hs : s i = (3 : ℤ) ^ (t - i) := rfl
            rw [hs, hsub, pow_succ]
            ring
          rw [hzero, hsplit]
          have hnext : s (i + 1) = (3 : ℤ) ^ (t - (i + 1)) := rfl
          rw [hnext]
          exact StepOfTriple p hD ((3 : ℤ) ^ (t - (i + 1)))
        }
    }
  · {
      exact (ZeroLengthCounts t).1
    }
  · {
      exact (ZeroLengthCounts t).2
    }
  · {
      have hcounts := ZeroLengthCounts t
      have habs : n.natAbs = 3 ^ t := by
        simp [n, Int.natAbs_pow]
      rw [hcounts.1, hcounts.2, habs]
      simp
    }

/-- The first `j` steps from `-3 ^ t` are the later negative powers. -/
theorem NegPowerAt (p : Parameters) (hD : p.D = 3) (t j : ℕ)
    (hj : j ≤ t) :
    Iterate (RawStep p) j (-(3 : ℤ) ^ t) = -(3 : ℤ) ^ (t - j) := by
  induction j with
  | zero => {
      rfl
    }
  | succ j ih => {
      have hjle : j ≤ t := Nat.le_of_succ_le hj
      have hpred := ih hjle
      have hstep :
          Iterate (RawStep p) (j + 1) (-(3 : ℤ) ^ t) =
            RawStep p (Iterate (RawStep p) j (-(3 : ℤ) ^ t)) := rfl
      rw [hstep, hpred]
      have hsplit :
          -(3 : ℤ) ^ (t - j) =
            3 * (-(3 : ℤ) ^ (t - (j + 1))) := by
        have hsub : t - j = (t - (j + 1)) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      rw [hsplit]
      exact StepOfTriple p hD (-(3 : ℤ) ^ (t - (j + 1)))
    }

/-- `-3 ^ t` reaches `-1` by `t` immediate divisions, with equality. -/
theorem NegPureDivisionEquality (p : Parameters) (hD : p.D = 3)
    (t : ℕ) :
    let n : ℤ := -(3 : ℤ) ^ t
    let s : ℕ → ℤ := fun i => -(3 : ℤ) ^ (t - i)
    let L : ℕ → ℕ := fun _ => 0
    Iterate (RawStep p) t n = -1 ∧
      (∀ j : ℕ, j < t → Iterate (RawStep p) j n ≠ -1) ∧
      s 0 = n ∧ s t = -1 ∧
      (∀ i : ℕ, i < t → s i ≠ -1) ∧
      (∀ i : ℕ, i < t →
        IsFirstHit p (s i) (L i) ∧
          RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) ∧
      ZeroSteps L t = t ∧ OneSteps L t = 0 ∧
      3 ^ ZeroSteps L t * 4 ^ OneSteps L t =
        3 ^ OneSteps L t * n.natAbs := by
  intro n s L
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · {
      have hpow := NegPowerAt p hD t t (le_refl t)
      simpa using hpow
    }
  · {
      intro j hj
      have hpow := NegPowerAt p hD t j (Nat.le_of_lt hj)
      rw [hpow]
      intro heq
      have hneg : (3 : ℤ) ^ (t - j) = 1 := by
        have hmul :
            -(3 : ℤ) ^ (t - j) = -((3 : ℤ) ^ (t - j)) := by
          ring
        rw [hmul] at heq
        exact neg_inj.mp heq
      exact ThreePowNeOne (t - j) (Nat.sub_pos_of_lt hj) hneg
    }
  · {
      show -(3 : ℤ) ^ (t - t) = -1
      have hsub : t - t = 0 := Nat.sub_self t
      rw [hsub]
      simp
    }
  · {
      intro i hi
      intro heq
      have hs : s i = -(3 : ℤ) ^ (t - i) := rfl
      rw [hs] at heq
      have hneg : (3 : ℤ) ^ (t - i) = 1 := by
        have hmul :
            -(3 : ℤ) ^ (t - i) = -((3 : ℤ) ^ (t - i)) := by
          ring
        rw [hmul] at heq
        exact neg_inj.mp heq
      exact ThreePowNeOne (t - i) (Nat.sub_pos_of_lt hi) hneg
    }
  · {
      intro i hi
      refine ⟨?_, ?_⟩
      · {
          refine ⟨?_, ?_⟩
          · {
              rw [AffineStateZero, hD]
              have hs : s i = -(3 : ℤ) ^ (t - i) := rfl
              rw [hs]
              refine ⟨-(3 : ℤ) ^ (t - i - 1), ?_⟩
              have hexp :
                  -(3 : ℤ) ^ (t - i) =
                    -((3 : ℤ) ^ ((t - i - 1) + 1)) := by
                have hsub : t - i = (t - i - 1) + 1 := by
                  omega
                conv_lhs => rw [hsub]
              rw [hexp, pow_succ]
              ring
            }
          · {
              intro u hu
              exact False.elim (Nat.not_lt_zero u hu)
            }
        }
      · {
          have hzero :
              Iterate (RawStep p) (L i) (s i) = s i := by
            have hL : L i = 0 := rfl
            rw [hL]
            rfl
          have hsplit :
              s i = 3 * (-(3 : ℤ) ^ (t - (i + 1))) := by
            have hsub : t - i = (t - (i + 1)) + 1 := by omega
            have hs : s i = -(3 : ℤ) ^ (t - i) := rfl
            rw [hs, hsub, pow_succ]
            ring
          rw [hzero, hsplit]
          have hnext : s (i + 1) = -(3 : ℤ) ^ (t - (i + 1)) := rfl
          rw [hnext]
          exact StepOfTriple p hD (-(3 : ℤ) ^ (t - (i + 1)))
        }
    }
  · {
      exact (ZeroLengthCounts t).1
    }
  · {
      exact (ZeroLengthCounts t).2
    }
  · {
      have hcounts := ZeroLengthCounts t
      have habs : n.natAbs = 3 ^ t := by
        simp [n, Int.natAbs_neg, Int.natAbs_pow]
      rw [hcounts.1, hcounts.2, habs]
      simp
    }

/-- The seed `4` reaches `1` by one block of each length, with equality. -/
theorem MixedEqualityFour (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    ∃ s : ℕ → ℤ, ∃ L : ℕ → ℕ,
      Iterate (RawStep p) 3 (4 : ℤ) = 1 ∧
        (∀ j : ℕ, j < 3 → Iterate (RawStep p) j (4 : ℤ) ≠ 1) ∧
        s 0 = 4 ∧ s 2 = 1 ∧
        (∀ i : ℕ, i < 2 → s i ≠ 1) ∧
        (∀ i : ℕ, i < 2 →
          IsFirstHit p (s i) (L i) ∧
            RawStep p (Iterate (RawStep p) (L i) (s i)) =
              s (i + 1)) ∧
        ZeroSteps L 2 = 1 ∧ OneSteps L 2 = 1 ∧
        3 ^ ZeroSteps L 2 * 4 ^ OneSteps L 2 =
          3 ^ OneSteps L 2 * (4 : ℤ).natAbs := by
  let s : ℕ → ℤ := fun i =>
    if i = 0 then 4 else if i = 1 then 3 else 1
  let L : ℕ → ℕ := fun i => if i = 0 then 1 else 0
  have hnd4 : ¬ p.D ∣ (4 : ℤ) := by
    rw [hD]
    intro hdvd
    have hzero : (4 : ℤ) % 3 = 0 :=
      (Int.dvd_iff_emod_eq_zero).mp hdvd
    have hone : (4 : ℤ) % 3 = 1 := by decide
    omega
  have hstep0 : RawStep p (4 : ℤ) = 9 := by
    rw [RawStep, if_neg hnd4, hQ, hC]
    omega
  have hiter1 : Iterate (RawStep p) 1 (4 : ℤ) = 9 := by
    have hrec :
        Iterate (RawStep p) 1 (4 : ℤ) = RawStep p (4 : ℤ) := rfl
    rw [hrec]
    exact hstep0
  have hd9 : p.D ∣ (9 : ℤ) := by
    rw [hD]
    refine ⟨3, by omega⟩
  have hstep1 : RawStep p (9 : ℤ) = 3 := by
    rw [RawStep, if_pos hd9, hD]
    decide
  have hiter2 : Iterate (RawStep p) 2 (4 : ℤ) = 3 := by
    have hrec :
        Iterate (RawStep p) 2 (4 : ℤ) =
          RawStep p (Iterate (RawStep p) 1 (4 : ℤ)) := rfl
    rw [hrec, hiter1, hstep1]
  have hd3 : p.D ∣ (3 : ℤ) := by
    rw [hD]
  have hstep2 : RawStep p (3 : ℤ) = 1 := by
    rw [RawStep, if_pos hd3, hD]
    have hthree : (3 : ℤ) = 3 * 1 := by omega
    rw [hthree]
    exact Int.mul_ediv_cancel_left 1 (by decide)
  have hiter3 : Iterate (RawStep p) 3 (4 : ℤ) = 1 := by
    have hrec :
        Iterate (RawStep p) 3 (4 : ℤ) =
          RawStep p (Iterate (RawStep p) 2 (4 : ℤ)) := rfl
    rw [hrec, hiter2, hstep2]
  refine ⟨s, L, hiter3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · {
      intro j hj
      have hsplit : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hsplit with hj0 | hj1 | hj2
      · {
          subst hj0
          have h0 : Iterate (RawStep p) 0 (4 : ℤ) = 4 := rfl
          rw [h0]
          decide
        }
      · {
          subst hj1
          rw [hiter1]
          decide
        }
      · {
          subst hj2
          rw [hiter2]
          decide
        }
    }
  · {
      simp [s]
    }
  · {
      simp [s]
    }
  · {
      intro i hi
      have hsplit : i = 0 ∨ i = 1 := by omega
      rcases hsplit with hi0 | hi1
      · {
          subst hi0
          simp [s]
        }
      · {
          subst hi1
          simp [s]
        }
    }
  · {
      intro i hi
      have hsplit : i = 0 ∨ i = 1 := by omega
      rcases hsplit with hi0 | hi1
      · {
          subst hi0
          have hfour := ExampleSeedFour p hQ hC hD
          have hs0 : s 0 = 4 := by simp [s]
          have hs1 : s 1 = 3 := by simp [s]
          have hL0 : L 0 = 1 := by simp [L]
          rw [hs0, hs1, hL0]
          exact ⟨hfour.1, hfour.2.2⟩
        }
      · {
          subst hi1
          have hmod : (3 : ℤ) % 3 = 0 := by decide
          have hthree := HitAtZero p hQ hC hD 3 hmod
          have hs1 : s 1 = 3 := by simp [s]
          have hs2 : s 2 = 1 := by simp [s]
          have hL1 : L 1 = 0 := by simp [L]
          have hquot : (3 : ℤ) / 3 = 1 := QuotientCancelThree 1
          rw [hs1, hs2, hL1]
          refine ⟨hthree.1, ?_⟩
          rw [hthree.2.2, hquot]
        }
    }
  · {
      simp [ZeroSteps, L]
    }
  · {
      simp [OneSteps, L]
    }
  · {
      simp [ZeroSteps, OneSteps, L]
    }

/-- Equal block counts cancel the powers of three. -/
theorem EqualCountsForcePower (a N : ℕ)
    (h : 3 ^ a * 4 ^ a = 3 ^ a * N) : N = 4 ^ a := by
  have h3 : 0 < 3 ^ a := Nat.pow_pos (by decide)
  exact (Nat.eq_of_mul_eq_mul_left h3 h).symm

/-- Absolute value `4` can hit only at the seed `4`. -/
theorem OnlyAbsFourHits (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (habs : n.natAbs = 4) (j : ℕ) (hj : IsFirstHit p n j) :
    n = 4 := by
  have hsign : n = (n.natAbs : ℤ) ∨ n = -((n.natAbs : ℤ)) := by
    cases n with
    | ofNat _ => {
        left
        rfl
      }
    | negSucc _ => {
        right
        rfl
      }
  rw [habs] at hsign
  rcases hsign with hpos | hneg
  · {
      exact hpos
    }
  · {
      have hmod : n % (3 : ℤ) = 2 := by
        rw [hneg]
        decide
      exact False.elim
        (RemainderTwoNoHit p hQ hC hD n hmod j hj)
    }

/-- A positive power of four is not a positive power of three times an integer. -/
theorem NoPureTwoEquality (a N : ℕ) (ha : 0 < a)
    (h : 4 ^ a = 3 ^ a * N) : False := by
  have hdvd : 3 ∣ 4 ^ a := by
    rw [h]
    have hpow : 3 ∣ 3 ^ a := by
      have hsplit : a = (a - 1) + 1 := by omega
      rw [hsplit, pow_succ]
      refine ⟨3 ^ (a - 1), ?_⟩
      ring
    exact dvd_mul_of_dvd_left hpow N
  have h4 : 3 ∣ 4 :=
    Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  exact (by decide : ¬ 3 ∣ 4) h4

/-- With no length-one block, the count bound is strict. -/
theorem PureTwoCountStrict (a N : ℕ) (ha : 0 < a)
    (h : 4 ^ a ≤ 3 ^ a * N) : 4 ^ a < 3 ^ a * N := by
  have hne : 4 ^ a ≠ 3 ^ a * N := by
    intro heq
    exact NoPureTwoEquality a N ha heq
  omega

/-- A positive power of three cannot divide a power of four. -/
theorem ThreePowerNotFourPower (b c N : ℕ) (hb : 0 < b)
    (h : 4 ^ c = 3 ^ b * N) : False := by
  have hdvd : 3 ∣ 4 ^ c := by
    rw [h]
    have hpow : 3 ∣ 3 ^ b := by
      have hsplit : b = (b - 1) + 1 := by omega
      rw [hsplit, pow_succ]
      refine ⟨3 ^ (b - 1), ?_⟩
      ring
    exact dvd_mul_of_dvd_left hpow N
  have h4 : 3 ∣ 4 :=
    Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  exact (by decide : ¬ 3 ∣ 4) h4

/-- More length-two blocks than length-one blocks forbids equality. -/
theorem MoreTwosCountStrict (a0 a1 N : ℕ) (hlt : a0 < a1)
    (h : 4 ^ a1 ≤ 3 ^ (a1 - a0) * N) :
    4 ^ a1 < 3 ^ (a1 - a0) * N := by
  have hpos : 0 < a1 - a0 := Nat.sub_pos_of_lt hlt
  have hne : 4 ^ a1 ≠ 3 ^ (a1 - a0) * N := by
    intro heq
    exact ThreePowerNotFourPower (a1 - a0) a1 N hpos heq
  omega

/-- Equality forces at least as many length-one blocks, and names the absolute value. -/
theorem EqualityCriterion (a0 a1 N : ℕ)
    (h : 3 ^ a0 * 4 ^ a1 = 3 ^ a1 * N) :
    a1 ≤ a0 ∧ N = 3 ^ (a0 - a1) * 4 ^ a1 := by
  have hle : a1 ≤ a0 := by
    by_contra hgt
    have hlt : a0 < a1 := Nat.lt_of_not_ge hgt
    have hpos : 0 < a1 - a0 := Nat.sub_pos_of_lt hlt
    have h3 : 0 < 3 ^ a0 := Nat.pow_pos (by decide)
    have hsplit : a1 = (a1 - a0) + a0 := by omega
    have hrew : 3 ^ a1 = 3 ^ (a1 - a0) * 3 ^ a0 := by
      conv_lhs => rw [hsplit]
      rw [pow_add]
    rw [hrew] at h
    have hcomm :
        3 ^ (a1 - a0) * 3 ^ a0 * N =
          3 ^ a0 * (3 ^ (a1 - a0) * N) := by
      ring
    rw [hcomm] at h
    have heq : 4 ^ a1 = 3 ^ (a1 - a0) * N :=
      Nat.eq_of_mul_eq_mul_left h3 h
    exact ThreePowerNotFourPower (a1 - a0) a1 N hpos heq
  refine ⟨hle, ?_⟩
  have h3 : 0 < 3 ^ a1 := Nat.pow_pos (by decide)
  have hsplit : a0 = (a0 - a1) + a1 := by omega
  have hrew : 3 ^ a0 = 3 ^ (a0 - a1) * 3 ^ a1 := by
    conv_lhs => rw [hsplit]
    rw [pow_add]
  rw [hrew] at h
  have hcomm :
      3 ^ (a0 - a1) * 3 ^ a1 * 4 ^ a1 =
        3 ^ a1 * (3 ^ (a0 - a1) * 4 ^ a1) := by
    ring
  rw [hcomm] at h
  exact (Nat.eq_of_mul_eq_mul_left h3 h).symm

/-- The numerical count equality is exactly the block comparison and the absolute value. -/
theorem EqualityCriterionIff (a0 a1 N : ℕ) :
    3 ^ a0 * 4 ^ a1 = 3 ^ a1 * N ↔
      a1 ≤ a0 ∧ N = 3 ^ (a0 - a1) * 4 ^ a1 := by
  constructor
  · {
      exact EqualityCriterion a0 a1 N
    }
  · {
      intro hpair
      obtain ⟨hle, hN⟩ := hpair
      rw [hN]
      have hsplit : a0 = (a0 - a1) + a1 := by omega
      have hpow : 3 ^ a0 = 3 ^ (a0 - a1) * 3 ^ a1 := by
        conv_lhs => rw [hsplit]
        rw [pow_add]
      rw [hpow]
      ring
    }

/-- Equality for a first visit to `1` is the block criterion. -/
theorem HitOneEquality (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ k : ℕ, Iterate (RawStep p) k n = 1) :
    ∃ a0 a1 k : ℕ,
      Iterate (RawStep p) k n = 1 ∧
        (∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ 1) ∧
        a0 + a1 + a1 = k ∧
        (3 ^ a0 * 4 ^ a1 = 3 ^ a1 * n.natAbs ↔
          a1 ≤ a0 ∧ n.natAbs = 3 ^ (a0 - a1) * 4 ^ a1) := by
  obtain ⟨a0, a1, k, hk, hmin, htime, _hfac⟩ :=
    HitOneMixed p hQ hC hD n h
  exact ⟨a0, a1, k, hk, hmin, htime,
    EqualityCriterionIff a0 a1 n.natAbs⟩

/-- Equality for a first visit to `-1` is the block criterion. -/
theorem HitNegOneEquality (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : ∃ k : ℕ, Iterate (RawStep p) k n = -1) :
    ∃ a0 a1 k : ℕ,
      Iterate (RawStep p) k n = -1 ∧
        (∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ -1) ∧
        a0 + a1 + a1 = k ∧
        (3 ^ a0 * 4 ^ a1 = 3 ^ a1 * n.natAbs ↔
          a1 ≤ a0 ∧ n.natAbs = 3 ^ (a0 - a1) * 4 ^ a1) := by
  obtain ⟨a0, a1, k, hk, hmin, htime, _hfac⟩ :=
    HitNegOneMixed p hQ hC hD n h
  exact ⟨a0, a1, k, hk, hmin, htime,
    EqualityCriterionIff a0 a1 n.natAbs⟩

/-- Equality on a chain to `1` puts `4` at every length-two block. -/
theorem HitOneChainForcesFour (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n) (hsm : s m = 1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ 1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (heq : 3 ^ ZeroSteps L m * 4 ^ OneSteps L m =
      3 ^ OneSteps L m * n.natAbs) :
    ∀ t : ℕ, t < m → L t = 1 → s t = 4 := by
  have hsmin' : ∀ i : ℕ, i < m → s i ≠ s m := by
    intro i hi hbad
    exact hsmin i hi (by rw [← hsm]; exact hbad)
  have hbig :=
    ProperTermsLarge p hQ hC hD n m s L hs0 (Or.inl hsm) hsmin' hL
  have hone : (s m).natAbs = 1 := by rw [hsm]; rfl
  have heq' :
      3 ^ ZeroSteps L m * 4 ^ OneSteps L m * (s m).natAbs =
        3 ^ OneSteps L m * n.natAbs := by
    rw [hone]
    simpa using heq
  exact MixedEqualityForcesFour p hQ hC hD n m s L hs0 hL hbig m
    (Nat.le_refl m) heq'

/-- Equality on a chain to `-1` puts `4` at every length-two block. -/
theorem HitNegOneChainForcesFour (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n) (hsm : s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ -1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (heq : 3 ^ ZeroSteps L m * 4 ^ OneSteps L m =
      3 ^ OneSteps L m * n.natAbs) :
    ∀ t : ℕ, t < m → L t = 1 → s t = 4 := by
  have hsmin' : ∀ i : ℕ, i < m → s i ≠ s m := by
    intro i hi hbad
    exact hsmin i hi (by rw [← hsm]; exact hbad)
  have hbig :=
    ProperTermsLarge p hQ hC hD n m s L hs0 (Or.inr hsm) hsmin' hL
  have hone : (s m).natAbs = 1 := by rw [hsm]; rfl
  have heq' :
      3 ^ ZeroSteps L m * 4 ^ OneSteps L m * (s m).natAbs =
        3 ^ OneSteps L m * n.natAbs := by
    rw [hone]
    simpa using heq
  exact MixedEqualityForcesFour p hQ hC hD n m s L hs0 hL hbig m
    (Nat.le_refl m) heq'

/-- The raw step sends `4` to `9`. -/
theorem RawStepFour (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) : RawStep p 4 = 9 := by
  unfold RawStep
  rw [hQ, hC, hD]
  decide

/-- The raw step sends `9` to `3`. -/
theorem RawStepNine (p : Parameters) (hD : p.D = 3) : RawStep p 9 = 3 := by
  have hd : p.D ∣ (9 : ℤ) := by
    rw [hD]
    decide
  have hnum : (9 : ℤ) = (3 : ℤ) * 3 := by omega
  have hdiv : (9 : ℤ) / 3 = 3 := by
    rw [hnum]
    exact QuotientCancelThree 3
  rw [RawStep, if_pos hd, hD, hdiv]

/-- After three steps, the orbit of `4` alternates between `1` and `3`. -/
theorem FourTail (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (k : ℕ) :
    Iterate (RawStep p) (k + 3) (4 : ℤ) =
      if k % 2 = 0 then 1 else 3 := by
  induction k with
  | zero => {
      have h1 : Iterate (RawStep p) 1 (4 : ℤ) = 9 := by
        simp [Iterate, RawStepFour p hQ hC hD]
      have h2 : Iterate (RawStep p) 2 (4 : ℤ) = 3 := by
        have hstep : Iterate (RawStep p) 2 (4 : ℤ) =
            RawStep p (Iterate (RawStep p) 1 4) := by
          simp [Iterate]
        rw [hstep, h1, RawStepNine p hD]
      have h3 : Iterate (RawStep p) 3 (4 : ℤ) =
          RawStep p (Iterate (RawStep p) 2 4) := by
        simp [Iterate]
      rw [h3, h2, RawStepThree p hD]
      simp
    }
  | succ j ih => {
      have hnext : Iterate (RawStep p) (j + 1 + 3) (4 : ℤ) =
          RawStep p (Iterate (RawStep p) (j + 3) 4) := by
        simp [Iterate]
      rw [hnext, ih]
      have hmod : j % 2 = 0 ∨ j % 2 = 1 := by omega
      rcases hmod with h0 | h1
      · {
          have hnextmod : (j + 1) % 2 = 1 := by omega
          simp [h0, hnextmod, RawStepOne p hQ hC hD]
        }
      · {
          have hnextmod : (j + 1) % 2 = 0 := by omega
          simp [h1, hnextmod, RawStepThree p hD]
        }
    }

/-- No raw iterate of `4` equals `-1`. -/
theorem FourNeverNegOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (k : ℕ) :
    Iterate (RawStep p) k (4 : ℤ) ≠ -1 := by
  cases k with
  | zero => {
      simp [Iterate]
    }
  | succ k => {
      cases k with
      | zero => {
          simp [Iterate, RawStepFour p hQ hC hD]
        }
      | succ k => {
          cases k with
          | zero => {
              have h2 : Iterate (RawStep p) 2 (4 : ℤ) = 3 := by
                have h1 : Iterate (RawStep p) 1 (4 : ℤ) = 9 := by
                  simp [Iterate, RawStepFour p hQ hC hD]
                have hstep : Iterate (RawStep p) 2 (4 : ℤ) =
                    RawStep p (Iterate (RawStep p) 1 4) := by
                  simp [Iterate]
                rw [hstep, h1, RawStepNine p hD]
              simp [h2]
            }
          | succ j => {
              have htail := FourTail p hQ hC hD j
              have htime : Iterate (RawStep p) (j + 3) (4 : ℤ) ≠ -1 := by
                rw [htail]
                by_cases hj : j % 2 = 0
                · {
                    simp [hj]
                  }
                · {
                    simp [hj]
                  }
              simpa using htime
            }
        }
    }

/-- A positive count of length-two blocks names one such block. -/
theorem OneStepWitness (L : ℕ → ℕ) (m : ℕ) (h : 0 < OneSteps L m) :
    ∃ t : ℕ, t < m ∧ L t = 1 := by
  induction m with
  | zero => {
      simp [OneSteps] at h
    }
  | succ m ih => {
      have hdef : OneSteps L (m + 1) =
          OneSteps L m + if L m = 1 then 1 else 0 := by
        simp [OneSteps]
      rw [hdef] at h
      by_cases hLm : L m = 1
      · {
          exact ⟨m, Nat.lt_succ_self m, hLm⟩
        }
      · {
          have htail : 0 < OneSteps L m := by
            simp [hLm] at h
            omega
          obtain ⟨t, ht, hLt⟩ := ih htail
          exact ⟨t, Nat.lt_succ_of_lt ht, hLt⟩
        }
    }

/-- Block sums do not decrease. -/
theorem RawLengthSumLe (L : ℕ → ℕ) {t m : ℕ} (ht : t ≤ m) :
    RawLengthSum L t ≤ RawLengthSum L m := by
  induction m with
  | zero => {
      have hz : t = 0 := by omega
      simp [hz]
    }
  | succ m ih => {
      rcases Nat.eq_or_lt_of_le ht with heq | hlt
      · {
          simp [heq]
        }
      · {
          have hle : t ≤ m := Nat.le_of_lt_succ hlt
          calc
            RawLengthSum L t ≤ RawLengthSum L m := ih hle
            _ ≤ RawLengthSum L m + (L m + 1) := by omega
            _ = RawLengthSum L (m + 1) := by simp [RawLengthSum]
        }
    }

/-- Equality on a chain to `-1` excludes every length-two block. -/
theorem NegOneEqualityNoLengthTwo (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n) (hsm : s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ -1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (heq : 3 ^ ZeroSteps L m * 4 ^ OneSteps L m =
      3 ^ OneSteps L m * n.natAbs) :
    OneSteps L m = 0 := by
  by_contra hne
  have hpos : 0 < OneSteps L m := Nat.pos_of_ne_zero hne
  obtain ⟨t, ht, hLt⟩ := OneStepWitness L m hpos
  have hfour : s t = 4 :=
    HitNegOneChainForcesFour p hQ hC hD n m s L hs0 hsm hsmin hL
      heq t ht hLt
  have horbit := ReturnChainIsOrbit p n m s L hs0 hL
  have hstart : Iterate (RawStep p) (RawLengthSum L t) n = 4 := by
    rw [← horbit t (Nat.le_of_lt ht)]
    exact hfour
  have hend : Iterate (RawStep p) (RawLengthSum L m) n = -1 := by
    rw [← horbit m (Nat.le_refl m)]
    exact hsm
  have hle := RawLengthSumLe L (Nat.le_of_lt ht)
  have hrest : Iterate (RawStep p)
      (RawLengthSum L m - RawLengthSum L t) 4 = -1 := by
    have hsplit := IterateAdd (RawStep p) (RawLengthSum L t)
      (RawLengthSum L m - RawLengthSum L t) n
    have hsum : RawLengthSum L t +
        (RawLengthSum L m - RawLengthSum L t) = RawLengthSum L m :=
      Nat.add_sub_of_le hle
    rw [hsum] at hsplit
    rw [hstart] at hsplit
    rw [← hsplit]
    exact hend
  exact FourNeverNegOne p hQ hC hD
    (RawLengthSum L m - RawLengthSum L t) hrest

/-- Equality on a chain to `-1` makes the absolute value a power of three. -/
theorem NegOneEqualityIsPower (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n) (hsm : s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ -1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (heq : 3 ^ ZeroSteps L m * 4 ^ OneSteps L m =
      3 ^ OneSteps L m * n.natAbs) :
    n.natAbs = 3 ^ ZeroSteps L m := by
  have hzero :=
    NegOneEqualityNoLengthTwo p hQ hC hD n m s L hs0 hsm hsmin hL heq
  rw [hzero] at heq
  simp at heq
  exact heq.symm

/-- A length-two block at `4` returns to `3`. -/
theorem ReturnFromFour (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (t : ℕ) (ht : t < m) (hLt : L t = 1) (hfour : s t = 4) :
    s (t + 1) = 3 := by
  have hstep := (hL t ht).2
  rw [hLt, hfour] at hstep
  have hiter : Iterate (RawStep p) 1 (4 : ℤ) = 9 := by
    simp [Iterate, RawStepFour p hQ hC hD]
  rw [hiter, RawStepNine p hD] at hstep
  exact hstep.symm

/-- The seed `3` returns immediately to `1`. -/
theorem ReturnFromThree (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (u : ℕ) (hu : u < m) (hthree : s u = 3) :
    L u = 0 ∧ s (u + 1) = 1 := by
  have hmod : s u % (3 : ℤ) = 0 := by
    rw [hthree]
    decide
  have hhit := HitAtZero p hQ hC hD (s u) hmod
  have hL0 : L u = 0 :=
    FirstHitUnique p (s u) (L u) 0 (hL u hu).1 hhit.1
  have hret := (hL u hu).2
  rw [hL0] at hret
  have hquot : s (u + 1) = s u / 3 := hret.symm.trans hhit.2.2
  rw [hthree] at hquot
  have hone : (3 : ℤ) / 3 = 1 := by
    have hnum : (3 : ℤ) = (3 : ℤ) * 1 := by omega
    rw [hnum]
    exact QuotientCancelThree 1
  rw [hone] at hquot
  exact ⟨hL0, hquot⟩

/-- A length-two block on a chain to `1` is the second-to-last block. -/
theorem LengthTwoEndsAtOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n) (hsm : s m = 1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ 1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (heq : 3 ^ ZeroSteps L m * 4 ^ OneSteps L m =
      3 ^ OneSteps L m * n.natAbs)
    (t : ℕ) (ht : t < m) (hLt : L t = 1) :
    t + 2 = m ∧ s t = 4 ∧ s (t + 1) = 3 := by
  have hfour : s t = 4 :=
    HitOneChainForcesFour p hQ hC hD n m s L hs0 hsm hsmin hL
      heq t ht hLt
  have hthree : s (t + 1) = 3 :=
    ReturnFromFour p hQ hC hD m s L hL t ht hLt hfour
  have hnot : t + 1 ≠ m := by
    intro heqm
    have hbad : s m = 3 := by
      rw [← heqm]
      exact hthree
    rw [hsm] at hbad
    omega
  have hlt : t + 1 < m := by omega
  have hlast := ReturnFromThree p hQ hC hD m s L hL (t + 1) hlt hthree
  have hone : s (t + 2) = 1 := hlast.2
  have hge : m ≤ t + 2 := by
    by_contra hlt2
    have hvisit : t + 2 < m := by omega
    exact hsmin (t + 2) hvisit hone
  have hle : t + 2 ≤ m := by omega
  exact ⟨Nat.le_antisymm hle hge, hfour, hthree⟩

/-- A length-two block increases the count. -/
theorem OneStepsSuccOne (L : ℕ → ℕ) (t : ℕ) (h : L t = 1) :
    OneSteps L t + 1 ≤ OneSteps L (t + 1) := by
  simp [OneSteps, h]

/-- Later prefixes have at least as many length-two blocks. -/
theorem OneStepsLe (L : ℕ → ℕ) {t m : ℕ} (ht : t ≤ m) :
    OneSteps L t ≤ OneSteps L m := by
  induction m with
  | zero => {
      have hz : t = 0 := by omega
      simp [hz]
    }
  | succ m ih => {
      rcases Nat.eq_or_lt_of_le ht with heq | hlt
      · {
          simp [heq]
        }
      · {
          have hle : t ≤ m := Nat.le_of_lt_succ hlt
          have hstep : OneSteps L m ≤ OneSteps L (m + 1) := by
            simp [OneSteps]
          exact Nat.le_trans (ih hle) hstep
        }
    }

/-- No length-two block means every hit is immediate. -/
theorem AllHitsImmediate (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hnone : OneSteps L m = 0) (i : ℕ) (hi : i < m) : L i = 0 := by
  have hhit := (hL i hi).1
  rcases FirstHitIsZeroOrOne p hQ hC hD (s i) (L i) hhit with h0 | h1
  · {
      exact h0
    }
  · {
      have hge : OneSteps L i + 1 ≤ OneSteps L (i + 1) :=
        OneStepsSuccOne L i h1
      have hmono : OneSteps L (i + 1) ≤ OneSteps L m :=
        OneStepsLe L (Nat.succ_le_of_lt hi)
      have hbase : 1 ≤ OneSteps L i + 1 := Nat.le_add_left 1 (OneSteps L i)
      have hchain : 1 ≤ OneSteps L m :=
        Nat.le_trans (Nat.le_trans hbase hge) hmono
      rw [hnone] at hchain
      omega
    }

/-- An immediate hit returns the exact quotient by three. -/
theorem ImmediateQuotient (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (i : ℕ) (hi : i < m) (hL0 : L i = 0) :
    (3 : ℤ) ∣ s i ∧ s (i + 1) = s i / 3 := by
  have hhit0 := (hL i hi).1
  have hhit : IsFirstHit p (s i) 0 := by
    simpa [hL0] using hhit0
  have hstate : AffineState p.Q p.C 0 (s i) = s i :=
    AffineStateZero p.Q p.C (s i)
  have hdvd3 : (3 : ℤ) ∣ s i := by
    rw [← hD, ← hstate]
    exact hhit.1
  have hmod : s i % (3 : ℤ) = 0 :=
    (Int.dvd_iff_emod_eq_zero).mp hdvd3
  have hzero := HitAtZero p hQ hC hD (s i) hmod
  have hret := (hL i hi).2
  rw [hL0] at hret
  exact ⟨hdvd3, hret.symm.trans hzero.2.2⟩

/-- Dividing by three and multiplying by three are inverse. -/
theorem ThreeMulQuotient (a : ℤ) (h : (3 : ℤ) ∣ a) : a = 3 * (a / 3) :=
  (Int.mul_ediv_cancel' h).symm

/-- With only immediate hits, the chain to `1` is the powers of three. -/
theorem PureDivisionPowers (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hsm : s m = 1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hzero : ∀ i : ℕ, i < m → L i = 0) :
    ∀ k : ℕ, k ≤ m → s (m - k) = (3 : ℤ) ^ k := by
  intro k hk
  induction k with
  | zero => {
      simp [hsm]
    }
  | succ k ih => {
      have hk' : k ≤ m := Nat.le_of_succ_le hk
      have hprev := ih hk'
      have hi : m - (k + 1) < m := by omega
      have hpair :=
        ImmediateQuotient p hQ hC hD m s L hL (m - (k + 1)) hi
          (hzero _ hi)
      have hidx : (m - (k + 1)) + 1 = m - k := by omega
      rw [hidx] at hpair
      have hmul := ThreeMulQuotient (s (m - (k + 1))) hpair.1
      rw [← hpair.2, hprev] at hmul
      have hpow : (3 : ℤ) ^ (k + 1) = 3 * (3 : ℤ) ^ k := by
        rw [pow_succ]
        ring
      rw [← hpow] at hmul
      exact hmul
    }

/-- Every immediate hit is counted. -/
theorem AllZeroSteps (L : ℕ → ℕ) (m : ℕ)
    (h : ∀ i : ℕ, i < m → L i = 0) : ZeroSteps L m = m := by
  induction m with
  | zero => {
      rfl
    }
  | succ m ih => {
      have htail : ∀ i : ℕ, i < m → L i = 0 := by
        intro i hi
        exact h i (Nat.lt_succ_of_lt hi)
      simp [ZeroSteps, h m (Nat.lt_succ_self m), ih htail]
    }

/-- All but one block are immediate, so the length-one count is `m - 1`. -/
theorem ZeroStepsExceptOne (L : ℕ → ℕ) (m t : ℕ)
    (ht : t < m) (hLt : L t ≠ 0)
    (h : ∀ i : ℕ, i < m → i ≠ t → L i = 0) :
    ZeroSteps L m = m - 1 := by
  induction m with
  | zero => {
      omega
    }
  | succ m ih => {
      by_cases htlast : t = m
      · {
          have htail : ∀ i : ℕ, i < m → L i = 0 := by
            intro i hi
            exact h i (Nat.lt_succ_of_lt hi) (by omega)
          have hcount : ZeroSteps L m = m := AllZeroSteps L m htail
          have hnot : ¬ L m = 0 := by
            rw [← htlast]
            exact hLt
          simp [ZeroSteps, hnot, hcount]
        }
      · {
          have ht' : t < m := by omega
          have htail : ∀ i : ℕ, i < m → i ≠ t → L i = 0 := by
            intro i hi hne
            exact h i (Nat.lt_succ_of_lt hi) hne
          have hcount : ZeroSteps L m = m - 1 := ih ht' htail
          have hlast : L m = 0 :=
            h m (Nat.lt_succ_self m) (Ne.symm htlast)
          simp [ZeroSteps, hlast, hcount]
          omega
        }
    }

/-- No length-two block on a prefix leaves the count at zero. -/
theorem OneStepsZeroBefore (L : ℕ → ℕ) (t : ℕ)
    (h : ∀ i : ℕ, i < t → L i ≠ 1) : OneSteps L t = 0 := by
  induction t with
  | zero => {
      rfl
    }
  | succ t ih => {
      have htail : ∀ i : ℕ, i < t → L i ≠ 1 := by
        intro i hi
        exact h i (Nat.lt_succ_of_lt hi)
      have hne : L t ≠ 1 := h t (Nat.lt_succ_self t)
      simp [OneSteps, ih htail, hne]
    }

/-- Skipping later blocks that are not length two does not change the count. -/
theorem OneStepsStable (L : ℕ → ℕ) (a b : ℕ) (hab : a ≤ b)
    (h : ∀ i : ℕ, a ≤ i → i < b → L i ≠ 1) :
    OneSteps L b = OneSteps L a := by
  induction b with
  | zero => {
      have hz : a = 0 := by omega
      simp [hz]
    }
  | succ b ih => {
      rcases Nat.eq_or_lt_of_le hab with heq | hlt
      · {
          simp [heq]
        }
      · {
          have hle : a ≤ b := Nat.le_of_lt_succ hlt
          have htail : ∀ i : ℕ, a ≤ i → i < b → L i ≠ 1 := by
            intro i hi hib
            exact h i hi (Nat.lt_succ_of_lt hib)
          have hne : L b ≠ 1 := h b hle (Nat.lt_succ_self b)
          simp [OneSteps, ih hle htail, hne]
        }
    }

/-- One length-two block, and no other, gives count one. -/
theorem CountUniqueOne (L : ℕ → ℕ) (m t : ℕ)
    (ht : t < m) (hLt : L t = 1)
    (honly : ∀ i : ℕ, i < m → L i = 1 → i = t) :
    OneSteps L m = 1 := by
  have hbefore : ∀ i : ℕ, i < t → L i ≠ 1 := by
    intro i hi hLi
    have heqi : i = t := honly i (Nat.lt_trans hi ht) hLi
    omega
  have hzero : OneSteps L t = 0 := OneStepsZeroBefore L t hbefore
  have hstep : OneSteps L (t + 1) = 1 := by
    simp [OneSteps, hLt, hzero]
  have hafter : ∀ i : ℕ, t + 1 ≤ i → i < m → L i ≠ 1 := by
    intro i hi him hLi
    have heqi : i = t := honly i him hLi
    omega
  have hrest : OneSteps L m = OneSteps L (t + 1) :=
    OneStepsStable L (t + 1) m (Nat.succ_le_of_lt ht) hafter
  rw [hrest, hstep]

/-- The terms before `4` are immediate divisions. -/
theorem PowersBeforeFour (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (m t : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (ht : t ≤ m)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hfour : s t = 4)
    (hzero : ∀ i : ℕ, i < t → L i = 0) :
    ∀ j : ℕ, j ≤ t → s (t - j) = 4 * (3 : ℤ) ^ j := by
  intro j hj
  induction j with
  | zero => {
      simp [hfour]
    }
  | succ j ih => {
      have hj' : j ≤ t := Nat.le_of_succ_le hj
      have hprev := ih hj'
      have hi : t - (j + 1) < m := by omega
      have hpair :=
        ImmediateQuotient p hQ hC hD m s L hL (t - (j + 1)) hi
          (hzero _ (by omega))
      have hidx : (t - (j + 1)) + 1 = t - j := by omega
      rw [hidx] at hpair
      have hmul := ThreeMulQuotient (s (t - (j + 1))) hpair.1
      rw [← hpair.2, hprev] at hmul
      have hpow : 4 * (3 : ℤ) ^ (j + 1) = 3 * (4 * (3 : ℤ) ^ j) := by
        rw [pow_succ]
        ring
      rw [← hpow] at hmul
      exact hmul
    }

/-- Equality on a chain to `1` forces a pure power of three or four times one. -/
theorem OneEqualityShape (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n) (hsm : s m = 1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ 1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (heq : 3 ^ ZeroSteps L m * 4 ^ OneSteps L m =
      3 ^ OneSteps L m * n.natAbs) :
    (OneSteps L m = 0 ∧ n = (3 : ℤ) ^ ZeroSteps L m) ∨
      (OneSteps L m = 1 ∧ 1 ≤ ZeroSteps L m ∧
        n = 4 * (3 : ℤ) ^ (ZeroSteps L m - 1)) := by
  by_cases hnone : OneSteps L m = 0
  · {
      have hzero : ∀ i : ℕ, i < m → L i = 0 :=
        fun i hi => AllHitsImmediate p hQ hC hD m s L hL hnone i hi
      have hcount : ZeroSteps L m = m := AllZeroSteps L m hzero
      have hpow :=
        PureDivisionPowers p hQ hC hD m s L hsm hL hzero m (Nat.le_refl m)
      have hn : n = (3 : ℤ) ^ m := by
        rw [← hs0]
        simpa using hpow
      left
      refine ⟨hnone, ?_⟩
      rw [hcount]
      exact hn
    }
  · {
      have hpos : 0 < OneSteps L m := Nat.pos_of_ne_zero hnone
      obtain ⟨t, ht, hLt⟩ := OneStepWitness L m hpos
      have hend :=
        LengthTwoEndsAtOne p hQ hC hD n m s L hs0 hsm hsmin hL heq t ht hLt
      have honly : ∀ i : ℕ, i < m → L i = 1 → i = t := by
        intro i hi hLi
        have hend' :=
          LengthTwoEndsAtOne p hQ hC hD n m s L hs0 hsm hsmin hL heq i hi hLi
        omega
      have hone : OneSteps L m = 1 := CountUniqueOne L m t ht hLt honly
      have himm : ∀ i : ℕ, i < t → L i = 0 := by
        intro i hi
        have hhit := (hL i (Nat.lt_trans hi ht)).1
        rcases FirstHitIsZeroOrOne p hQ hC hD (s i) (L i) hhit with h0 | h1
        · {
            exact h0
          }
        · {
            exact False.elim ((by omega : i ≠ t) (honly i (Nat.lt_trans hi ht) h1))
          }
      have hpref :=
        PowersBeforeFour p hQ hC hD m t s L (Nat.le_of_lt ht) hL hend.2.1
          himm t (Nat.le_refl t)
      have hn : n = 4 * (3 : ℤ) ^ t := by
        rw [← hs0]
        simpa using hpref
      have hlast0 : L (t + 1) = 0 := by
        have hthree : s (t + 1) = 3 := hend.2.2
        have hlt : t + 1 < m := by omega
        exact (ReturnFromThree p hQ hC hD m s L hL (t + 1) hlt hthree).1
      have hzeros : ∀ i : ℕ, i < m → i ≠ t → L i = 0 := by
        intro i hi hne
        have hhit := (hL i hi).1
        rcases FirstHitIsZeroOrOne p hQ hC hD (s i) (L i) hhit with h0 | h1
        · {
            exact h0
          }
        · {
            exact False.elim (hne (honly i hi h1))
          }
      have hcount : ZeroSteps L m = m - 1 :=
        ZeroStepsExceptOne L m t ht (by rw [hLt]; decide) hzeros
      right
      refine ⟨hone, ?_, ?_⟩
      · {
          have hm : 2 ≤ m := by omega
          omega
        }
      · {
          have htpow : t = ZeroSteps L m - 1 := by
            rw [hcount]
            omega
          rw [htpow] at hn
          exact hn
        }
    }

/-- The seed `4` has its first hit at time one. -/
theorem FourIsTimeOneHit (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    IsFirstHit p 4 1 := by
  unfold IsFirstHit AffineState
  rw [hQ, hC, hD]
  refine ⟨?_, ?_⟩
  · {
      decide
    }
  · {
      intro i hi
      have hz : i = 0 := by omega
      subst hz
      decide
    }

/-- A positive power of three makes `4 * 3^k` divisible by three. -/
theorem MixedPowerDivisible (k : ℕ) (hk : 0 < k) :
    (3 : ℤ) ∣ 4 * (3 : ℤ) ^ k := by
  have hsplit : k = (k - 1) + 1 := by omega
  have hpow : (3 : ℤ) ^ k = 3 * (3 : ℤ) ^ (k - 1) := by
    conv_lhs => rw [hsplit]
    rw [pow_succ]
    ring
  refine ⟨4 * (3 : ℤ) ^ (k - 1), ?_⟩
  rw [hpow]
  ring

/-- Dividing `4 * 3^k` by three lowers the exponent by one. -/
theorem MixedPowerQuotient (k : ℕ) (hk : 0 < k) :
    (4 * (3 : ℤ) ^ k) / 3 = 4 * (3 : ℤ) ^ (k - 1) := by
  have hsplit : k = (k - 1) + 1 := by omega
  have hfac : 4 * (3 : ℤ) ^ k = 3 * (4 * (3 : ℤ) ^ (k - 1)) := by
    conv_lhs => rw [hsplit]
    rw [pow_succ]
    ring
  rw [hfac]
  exact QuotientCancelThree (4 * (3 : ℤ) ^ (k - 1))

/-- Chain term of the seed `4 * 3^t`: divide down to `4`, then `3`, then `1`. -/
def MixedSeed (t i : ℕ) : ℤ :=
  if i ≤ t then 4 * (3 : ℤ) ^ (t - i)
  else if i = t + 1 then 3 else 1

/-- Block length of that chain: only the term `4` has length two. -/
def MixedBlock (t i : ℕ) : ℕ :=
  if i = t then 1 else 0

/-- The seed `4 * 3^t` reaches `1` by the mixed chain, with count equality. -/
theorem MixedPowerEquality (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (t : ℕ) :
    let n : ℤ := 4 * (3 : ℤ) ^ t
    let m : ℕ := t + 2
    let s : ℕ → ℤ := MixedSeed t
    let L : ℕ → ℕ := MixedBlock t
    s 0 = n ∧ s m = 1 ∧ (∀ i : ℕ, i < m → s i ≠ 1) ∧
      (∀ i : ℕ, i < m →
        IsFirstHit p (s i) (L i) ∧
          RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) ∧
      ZeroSteps L m = t + 1 ∧ OneSteps L m = 1 ∧
      3 ^ ZeroSteps L m * 4 ^ OneSteps L m =
        3 ^ OneSteps L m * n.natAbs := by
  intro n m s L
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · {
      simp [n, s, MixedSeed]
    }
  · {
      simp [m, s, MixedSeed]
    }
  · {
      intro i hi
      by_cases hle : i ≤ t
      · {
          have hval : s i = 4 * (3 : ℤ) ^ (t - i) := by
            simp [s, MixedSeed, hle]
          rw [hval]
          have hpos : (0 : ℤ) < 4 * (3 : ℤ) ^ (t - i) := by
            positivity
          omega
        }
      · {
          have heq : i = t + 1 := by omega
          simp [s, MixedSeed, heq]
        }
    }
  · {
      intro i hi
      by_cases hlt : i < t
      · {
          have hle : i ≤ t := Nat.le_of_lt hlt
          have hval : s i = 4 * (3 : ℤ) ^ (t - i) := by
            simp [s, MixedSeed, hle]
          have hnext : s (i + 1) = 4 * (3 : ℤ) ^ (t - (i + 1)) := by
            have hle' : i + 1 ≤ t := by omega
            simp [s, MixedSeed, hle']
          have hk : 0 < t - i := by omega
          have hdvd : p.D ∣ s i := by
            rw [hD, hval]
            exact MixedPowerDivisible (t - i) hk
          have hhit : IsFirstHit p (s i) 0 := by
            unfold IsFirstHit
            refine ⟨?_, ?_⟩
            · {
                have hstate : AffineState p.Q p.C 0 (s i) = s i := by
                  unfold AffineState
                  simp [TrapSum]
                rw [hstate]
                exact hdvd
              }
            · {
                intro j hj
                omega
              }
          have hne : i ≠ t := by omega
          have hL : L i = 0 := by
            simp [L, MixedBlock, hne]
          refine ⟨by simpa [hL] using hhit, ?_⟩
          have hstep : RawStep p (s i) = s (i + 1) := by
            have hdiv : (s i) / p.D = s (i + 1) := by
              rw [hD, hval, hnext]
              have hidx : t - i - 1 = t - (i + 1) := by omega
              rw [MixedPowerQuotient (t - i) hk, hidx]
            rw [RawStep, if_pos hdvd, hdiv]
          simpa [hL, Iterate] using hstep
        }
      · {
          have hge : t ≤ i := by omega
          have heq : i = t ∨ i = t + 1 := by omega
          rcases heq with ht | ht1
          · {
              have hfour : s i = 4 := by
                simp [s, MixedSeed, ht]
              have hL : L i = 1 := by
                simp [L, MixedBlock, ht]
              have hhit : IsFirstHit p (s i) 1 := by
                rw [hfour]
                exact FourIsTimeOneHit p hQ hC hD
              refine ⟨by simpa [hL] using hhit, ?_⟩
              have hnext : s (i + 1) = 3 := by
                have hidx : i + 1 = t + 1 := by omega
                simp [s, MixedSeed, hidx]
              have hnine : Iterate (RawStep p) 1 (s i) = 9 := by
                rw [hfour]
                simp [Iterate, RawStepFour p hQ hC hD]
              have hret : RawStep p (Iterate (RawStep p) 1 (s i)) = 3 := by
                rw [hnine]
                exact RawStepNine p hD
              rw [hL, hret, hnext]
            }
          · {
              have hthree : s i = 3 := by
                simp [s, MixedSeed, ht1]
              have hne : i ≠ t := by omega
              have hL : L i = 0 := by
                simp [L, MixedBlock, hne]
              have hdvd : p.D ∣ s i := by
                rw [hD, hthree]
              have hhit : IsFirstHit p (s i) 0 := by
                unfold IsFirstHit
                refine ⟨?_, ?_⟩
                · {
                    have hstate : AffineState p.Q p.C 0 (s i) = s i := by
                      unfold AffineState
                      simp [TrapSum]
                    rw [hstate]
                    exact hdvd
                  }
                · {
                    intro j hj
                    omega
                  }
              refine ⟨by simpa [hL] using hhit, ?_⟩
              have hnext : s (i + 1) = 1 := by
                have hidx : i + 1 = t + 2 := by omega
                simp [s, MixedSeed, hidx]
              have hstep : RawStep p (s i) = 1 := by
                rw [hthree]
                exact RawStepThree p hD
              simpa [hL, Iterate, hnext] using hstep
            }
        }
    }
  · {
      have honly : ∀ i : ℕ, i < m → i ≠ t → L i = 0 := by
        intro i _ hi
        simp [L, MixedBlock, hi]
      exact ZeroStepsExceptOne L m t (by omega : t < m) (by
        simp [L, MixedBlock]) honly
    }
  · {
      have hLt : L t = 1 := by
        simp [L, MixedBlock]
      have honly : ∀ i : ℕ, i < m → L i = 1 → i = t := by
        intro i _ hLi
        by_contra hne
        have hzero : L i = 0 := by
          simp [L, MixedBlock, hne]
        omega
      exact CountUniqueOne L m t (by omega : t < m) hLt honly
    }
  · {
      have hzero : ZeroSteps L m = t + 1 := by
        have honly : ∀ i : ℕ, i < m → i ≠ t → L i = 0 := by
          intro i _ hi
          simp [L, MixedBlock, hi]
        exact ZeroStepsExceptOne L m t (by omega : t < m) (by
          simp [L, MixedBlock]) honly
      have hone : OneSteps L m = 1 := by
        have hLt : L t = 1 := by
          simp [L, MixedBlock]
        have honly : ∀ i : ℕ, i < m → L i = 1 → i = t := by
          intro i _ hLi
          by_contra hne
          have hL0 : L i = 0 := by
            simp [L, MixedBlock, hne]
          omega
        exact CountUniqueOne L m t (by omega : t < m) hLt honly
      rw [hzero, hone]
      have habs : n.natAbs = 4 * 3 ^ t := by
        simp [n, Int.natAbs_mul, Int.natAbs_pow]
      rw [habs]
      have hprod : 3 ^ (t + 1) * 4 = 3 * (4 * 3 ^ t) := by
        rw [pow_succ]
        ring
      simpa [pow_one] using hprod
    }

/-- A seed has a minimal equality chain to `1` exactly in the two shapes. -/
theorem OneEqualityClassification (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    (∃ m : ℕ, ∃ s : ℕ → ℤ, ∃ L : ℕ → ℕ,
      s 0 = n ∧ s m = 1 ∧ (∀ i : ℕ, i < m → s i ≠ 1) ∧
        (∀ i : ℕ, i < m →
          IsFirstHit p (s i) (L i) ∧
            RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) ∧
        3 ^ ZeroSteps L m * 4 ^ OneSteps L m =
          3 ^ OneSteps L m * n.natAbs) ↔
      (∃ t : ℕ, n = (3 : ℤ) ^ t ∨ n = 4 * (3 : ℤ) ^ t) := by
  constructor
  · {
      intro hchain
      obtain ⟨m, s, L, hs0, hsm, hsmin, hL, heq⟩ := hchain
      rcases OneEqualityShape p hQ hC hD n m s L hs0 hsm hsmin hL heq with
        ⟨_, hn⟩ | ⟨_, _, hn⟩
      · {
          exact ⟨ZeroSteps L m, Or.inl hn⟩
        }
      · {
          exact ⟨ZeroSteps L m - 1, Or.inr hn⟩
        }
    }
  · {
      intro ht
      obtain ⟨t, hn⟩ := ht
      rcases hn with hpure | hmixed
      · {
          let s : ℕ → ℤ := fun i => (3 : ℤ) ^ (t - i)
          let L : ℕ → ℕ := fun _ => 0
          have h := PureDivisionEquality p hD t
          refine ⟨t, s, L, ?_, ?_, ?_, ?_, ?_⟩
          · {
              rw [hpure]
              exact h.2.2.1
            }
          · {
              exact h.2.2.2.1
            }
          · {
              exact h.2.2.2.2.1
            }
          · {
              exact h.2.2.2.2.2.1
            }
          · {
              rw [hpure]
              exact h.2.2.2.2.2.2.2.2
            }
        }
      · {
          let s : ℕ → ℤ := MixedSeed t
          let L : ℕ → ℕ := MixedBlock t
          have h := MixedPowerEquality p hQ hC hD t
          refine ⟨t + 2, s, L, ?_, ?_, ?_, ?_, ?_⟩
          · {
              rw [hmixed]
              exact h.1
            }
          · {
              exact h.2.1
            }
          · {
              exact h.2.2.1
            }
          · {
              exact h.2.2.2.1
            }
          · {
              rw [hmixed]
              exact h.2.2.2.2.2.2
            }
        }
    }

/-- With only immediate hits, the chain to `-1` is the negative powers of three. -/
theorem NegDivisionPowers (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hsm : s m = -1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hzero : ∀ i : ℕ, i < m → L i = 0) :
    ∀ k : ℕ, k ≤ m → s (m - k) = -(3 : ℤ) ^ k := by
  intro k hk
  induction k with
  | zero => {
      simp [hsm]
    }
  | succ k ih => {
      have hk' : k ≤ m := Nat.le_of_succ_le hk
      have hprev := ih hk'
      have hi : m - (k + 1) < m := by omega
      have hpair :=
        ImmediateQuotient p hQ hC hD m s L hL (m - (k + 1)) hi
          (hzero _ hi)
      have hidx : (m - (k + 1)) + 1 = m - k := by omega
      rw [hidx] at hpair
      have hmul := ThreeMulQuotient (s (m - (k + 1))) hpair.1
      rw [← hpair.2, hprev] at hmul
      have hpow : -(3 : ℤ) ^ (k + 1) = 3 * (-(3 : ℤ) ^ k) := by
        rw [pow_succ]
        ring
      rw [← hpow] at hmul
      exact hmul
    }

/-- A seed has a minimal equality chain to `-1` exactly for negative powers of three. -/
theorem NegOneEqualityClassification (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    (∃ m : ℕ, ∃ s : ℕ → ℤ, ∃ L : ℕ → ℕ,
      s 0 = n ∧ s m = -1 ∧ (∀ i : ℕ, i < m → s i ≠ -1) ∧
        (∀ i : ℕ, i < m →
          IsFirstHit p (s i) (L i) ∧
            RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) ∧
        3 ^ ZeroSteps L m * 4 ^ OneSteps L m =
          3 ^ OneSteps L m * n.natAbs) ↔
      (∃ t : ℕ, n = -(3 : ℤ) ^ t) := by
  constructor
  · {
      intro hchain
      obtain ⟨m, s, L, hs0, hsm, hsmin, hL, heq⟩ := hchain
      have hnone :=
        NegOneEqualityNoLengthTwo p hQ hC hD n m s L hs0 hsm hsmin hL heq
      have himm : ∀ i : ℕ, i < m → L i = 0 :=
        fun i hi =>
          AllHitsImmediate p hQ hC hD m s L hL hnone i hi
      have hpow :=
        NegDivisionPowers p hQ hC hD m s L hsm hL himm m (Nat.le_refl m)
      have hcount : ZeroSteps L m = m := AllZeroSteps L m himm
      refine ⟨ZeroSteps L m, ?_⟩
      rw [← hs0, hcount]
      simpa using hpow
    }
  · {
      intro ht
      obtain ⟨t, hn⟩ := ht
      let s : ℕ → ℤ := fun i => -(3 : ℤ) ^ (t - i)
      let L : ℕ → ℕ := fun _ => 0
      have h := NegPureDivisionEquality p hD t
      refine ⟨t, s, L, ?_, ?_, ?_, ?_, ?_⟩
      · {
          rw [hn]
          exact h.2.2.1
        }
      · {
          exact h.2.2.2.1
        }
      · {
          exact h.2.2.2.2.1
        }
      · {
          exact h.2.2.2.2.2.1
        }
      · {
          rw [hn]
          exact h.2.2.2.2.2.2.2.2
        }
    }

/-- A power of three is not four times a power of three. -/
theorem ThreeNotFourTimes (a b : ℕ) :
    (3 : ℤ) ^ a ≠ 4 * (3 : ℤ) ^ b := by
  intro h
  have hnat : 3 ^ a = 4 * 3 ^ b := by
    have habs := congrArg Int.natAbs h
    simpa [Int.natAbs_pow, Int.natAbs_mul] using habs
  by_cases hab : b ≤ a
  · {
      have hsplit : a = (a - b) + b := by omega
      have hpow : 3 ^ a = 3 ^ (a - b) * 3 ^ b := by
        conv_lhs => rw [hsplit]
        rw [Nat.pow_add]
      rw [hpow] at hnat
      have h3 : 0 < 3 ^ b := Nat.pow_pos (by decide)
      have hquot : 3 ^ (a - b) = 4 := Nat.eq_of_mul_eq_mul_right h3 hnat
      by_cases hz : a - b = 0
      · {
          simp [hz] at hquot
        }
      · {
          have hpos : 0 < a - b := by omega
          have hfac : 3 ^ (a - b) = 3 * 3 ^ (a - b - 1) := by
            have hsplit' : a - b = (a - b - 1) + 1 := by omega
            conv_lhs => rw [hsplit']
            rw [Nat.pow_succ]
            ring
          have hdiv : 3 ∣ 4 := by
            rw [← hquot, hfac]
            exact Nat.dvd_mul_right 3 (3 ^ (a - b - 1))
          omega
        }
    }
  · {
      have hlt : a < b := by omega
      have hsplit : b = (b - a) + a := by omega
      have hpow : 3 ^ b = 3 ^ (b - a) * 3 ^ a := by
        conv_lhs => rw [hsplit]
        rw [Nat.pow_add]
      rw [hpow] at hnat
      have h3 : 0 < 3 ^ a := Nat.pow_pos (by decide)
      have hcomm : 4 * (3 ^ (b - a) * 3 ^ a) =
          (4 * 3 ^ (b - a)) * 3 ^ a := by ring
      rw [hcomm] at hnat
      have hquot : 1 = 4 * 3 ^ (b - a) := by
        have hflip : (4 * 3 ^ (b - a)) * 3 ^ a = 1 * 3 ^ a := by
          rw [Nat.one_mul]
          exact hnat.symm
        exact (Nat.eq_of_mul_eq_mul_right h3 hflip).symm
      have hbig : 4 ≤ 4 * 3 ^ (b - a) := by
        have hexp : 1 ≤ b - a := by omega
        have hone : 1 ≤ 3 ^ (b - a) := Nat.pow_pos (by decide)
        exact Nat.mul_le_mul_left 4 hone
      omega
    }

/-- A positive power of three is not a negative one. -/
theorem ThreeNotNegThree (a b : ℕ) : (3 : ℤ) ^ a ≠ -(3 : ℤ) ^ b := by
  intro h
  have hpos : (0 : ℤ) < (3 : ℤ) ^ a := by positivity
  have hneg : -(3 : ℤ) ^ b < 0 := by
    have hb : (0 : ℤ) < (3 : ℤ) ^ b := by positivity
    omega
  omega

/-- Four times a power of three is positive, so it is not a negative power. -/
theorem FourThreeNotNeg (a b : ℕ) :
    4 * (3 : ℤ) ^ a ≠ -(3 : ℤ) ^ b := by
  intro h
  have hpos : (0 : ℤ) < 4 * (3 : ℤ) ^ a := by positivity
  have hneg : -(3 : ℤ) ^ b < 0 := by
    have hb : (0 : ℤ) < (3 : ℤ) ^ b := by positivity
    omega
  omega

/-- Equality chains to `1` or `-1` occur exactly on the three disjoint families. -/
theorem EqualityBasins (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    ((∃ m : ℕ, ∃ s : ℕ → ℤ, ∃ L : ℕ → ℕ,
        s 0 = n ∧ s m = 1 ∧ (∀ i : ℕ, i < m → s i ≠ 1) ∧
          (∀ i : ℕ, i < m →
            IsFirstHit p (s i) (L i) ∧
              RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) ∧
          3 ^ ZeroSteps L m * 4 ^ OneSteps L m =
            3 ^ OneSteps L m * n.natAbs) ∨
      (∃ m : ℕ, ∃ s : ℕ → ℤ, ∃ L : ℕ → ℕ,
        s 0 = n ∧ s m = -1 ∧ (∀ i : ℕ, i < m → s i ≠ -1) ∧
          (∀ i : ℕ, i < m →
            IsFirstHit p (s i) (L i) ∧
              RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) ∧
          3 ^ ZeroSteps L m * 4 ^ OneSteps L m =
            3 ^ OneSteps L m * n.natAbs)) ↔
      (∃ t : ℕ, n = (3 : ℤ) ^ t ∨ n = 4 * (3 : ℤ) ^ t ∨ n = -(3 : ℤ) ^ t) := by
  constructor
  · {
      intro h
      rcases h with hone | hneg
      · {
          have hiff := (OneEqualityClassification p hQ hC hD n).1 hone
          obtain ⟨t, ht⟩ := hiff
          rcases ht with h3 | h4
          · {
              exact ⟨t, Or.inl h3⟩
            }
          · {
              exact ⟨t, Or.inr (Or.inl h4)⟩
            }
        }
      · {
          have hiff := (NegOneEqualityClassification p hQ hC hD n).1 hneg
          obtain ⟨t, ht⟩ := hiff
          exact ⟨t, Or.inr (Or.inr ht)⟩
        }
    }
  · {
      intro ht
      obtain ⟨t, hn⟩ := ht
      rcases hn with h3 | hrest
      · {
          left
          exact (OneEqualityClassification p hQ hC hD n).2 ⟨t, Or.inl h3⟩
        }
      · {
          rcases hrest with h4 | hneg
          · {
              left
              exact (OneEqualityClassification p hQ hC hD n).2 ⟨t, Or.inr h4⟩
            }
          · {
              right
              exact (NegOneEqualityClassification p hQ hC hD n).2 ⟨t, hneg⟩
            }
        }
    }

/-- A seed outside the three families has a strict count inequality. -/
theorem StrictOutsideFamilies (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (hnot : ¬ ∃ t : ℕ,
      n = (3 : ℤ) ^ t ∨ n = 4 * (3 : ℤ) ^ t ∨ n = -(3 : ℤ) ^ t)
    (hhit : (∃ k : ℕ, Iterate (RawStep p) k n = 1) ∨
      (∃ k : ℕ, Iterate (RawStep p) k n = -1)) :
    ∃ a0 a1 : ℕ, 3 ^ a0 * 4 ^ a1 < 3 ^ a1 * n.natAbs := by
  classical
  rcases hhit with hone | hneg
  · {
      obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
        ReturnChainToOne p hQ hC hD n hone
      let L : ℕ → ℕ := fun i =>
        if hi : i < m then Classical.choose (hstep i hi) else 0
      have hL : ∀ i : ℕ, i < m →
          IsFirstHit p (s i) (L i) ∧
            RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1) := by
        intro i hi
        have hspec := Classical.choose_spec (hstep i hi)
        have hLi : L i = Classical.choose (hstep i hi) := by
          simp [L, hi]
        rw [hLi]
        exact hspec
      have hmin : ∀ i : ℕ, i < m → s i ≠ s m := by
        intro i hi
        rw [hsm]
        exact hsmin i hi
      have hfac :=
        MixedReturn p hQ hC hD n m s L hs0 (Or.inl hsm) hmin hL
      rcases Nat.lt_or_eq_of_le hfac with hlt | heq
      · {
          exact ⟨ZeroSteps L m, OneSteps L m, hlt⟩
        }
      · {
          have hmem :=
            (OneEqualityClassification p hQ hC hD n).1
              ⟨m, s, L, hs0, hsm, hsmin, hL, heq⟩
          obtain ⟨t, ht⟩ := hmem
          rcases ht with h3 | h4
          · {
              exact False.elim (hnot ⟨t, Or.inl h3⟩)
            }
          · {
              exact False.elim (hnot ⟨t, Or.inr (Or.inl h4)⟩)
            }
        }
    }
  · {
      obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
        ReturnChainToNegOne p hQ hC hD n hneg
      let L : ℕ → ℕ := fun i =>
        if hi : i < m then Classical.choose (hstep i hi) else 0
      have hL : ∀ i : ℕ, i < m →
          IsFirstHit p (s i) (L i) ∧
            RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1) := by
        intro i hi
        have hspec := Classical.choose_spec (hstep i hi)
        have hLi : L i = Classical.choose (hstep i hi) := by
          simp [L, hi]
        rw [hLi]
        exact hspec
      have hmin : ∀ i : ℕ, i < m → s i ≠ s m := by
        intro i hi
        rw [hsm]
        exact hsmin i hi
      have hfac :=
        MixedReturn p hQ hC hD n m s L hs0 (Or.inr hsm) hmin hL
      rcases Nat.lt_or_eq_of_le hfac with hlt | heq
      · {
          exact ⟨ZeroSteps L m, OneSteps L m, hlt⟩
        }
      · {
          have hmem :=
            (NegOneEqualityClassification p hQ hC hD n).1
              ⟨m, s, L, hs0, hsm, hsmin, hL, heq⟩
          obtain ⟨t, ht⟩ := hmem
          exact False.elim (hnot ⟨t, Or.inr (Or.inr ht)⟩)
        }
    }

/-- The count bound holds, and equality occurs exactly on the three families. -/
theorem CountSharp (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (hhit : (∃ k : ℕ, Iterate (RawStep p) k n = 1) ∨
      (∃ k : ℕ, Iterate (RawStep p) k n = -1)) :
    ∃ a0 a1 : ℕ,
      3 ^ a0 * 4 ^ a1 ≤ 3 ^ a1 * n.natAbs ∧
        (3 ^ a0 * 4 ^ a1 = 3 ^ a1 * n.natAbs ↔
          ∃ t : ℕ,
            n = (3 : ℤ) ^ t ∨ n = 4 * (3 : ℤ) ^ t ∨ n = -(3 : ℤ) ^ t) := by
  classical
  by_cases hmem : ∃ t : ℕ,
      n = (3 : ℤ) ^ t ∨ n = 4 * (3 : ℤ) ^ t ∨ n = -(3 : ℤ) ^ t
  · {
      rcases (EqualityBasins p hQ hC hD n).2 hmem with hone | hneg
      · {
          obtain ⟨m, s, L, hs0, hsm, hsmin, hL, heq⟩ := hone
          refine ⟨ZeroSteps L m, OneSteps L m, Nat.le_of_eq heq, ?_⟩
          constructor
          · {
              intro _
              exact hmem
            }
          · {
              intro _
              exact heq
            }
        }
      · {
          obtain ⟨m, s, L, hs0, hsm, hsmin, hL, heq⟩ := hneg
          refine ⟨ZeroSteps L m, OneSteps L m, Nat.le_of_eq heq, ?_⟩
          constructor
          · {
              intro _
              exact hmem
            }
          · {
              intro _
              exact heq
            }
        }
    }
  · {
      obtain ⟨a0, a1, hlt⟩ :=
        StrictOutsideFamilies p hQ hC hD n hmem hhit
      refine ⟨a0, a1, Nat.le_of_lt hlt, ?_⟩
      constructor
      · {
          intro heq
          exact False.elim (Nat.ne_of_lt hlt heq)
        }
      · {
          intro hfam
          exact False.elim (hmem hfam)
        }
    }

/-- Two minimal chains to the same target have the same block counts. -/
theorem BlockCountsUnique (p : Parameters) (n g : ℤ)
    (m m' : ℕ) (s t : ℕ → ℤ) (L M : ℕ → ℕ)
    (hs0 : s 0 = n) (ht0 : t 0 = n)
    (hsm : s m = g) (htm : t m' = g)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ g)
    (htmin : ∀ i : ℕ, i < m' → t i ≠ g)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hM : ∀ i : ℕ, i < m' →
      IsFirstHit p (t i) (M i) ∧
        RawStep p (Iterate (RawStep p) (M i) (t i)) = t (i + 1)) :
    m = m' ∧ ZeroSteps L m = ZeroSteps M m' ∧
      OneSteps L m = OneSteps M m' := by
  have hchain :=
    ReturnChainUnique p n g m m' s t hs0 ht0 hsm htm hsmin htmin
      (fun i hi => ⟨L i, (hL i hi).1, (hL i hi).2⟩)
      (fun i hi => ⟨M i, (hM i hi).1, (hM i hi).2⟩)
  obtain ⟨hm, hst⟩ := hchain
  have hlen : ∀ i : ℕ, i < m → L i = M i := by
    intro i hi
    have hsi : s i = t i := hst i (Nat.le_of_lt hi)
    have hhit : IsFirstHit p (t i) (L i) := by
      rw [← hsi]
      exact (hL i hi).1
    have hi' : i < m' := by
      rw [← hm]
      exact hi
    exact FirstHitUnique p (t i) (L i) (M i) hhit (hM i hi').1
  have hcounts := StepsAgree m L M hlen
  refine ⟨hm, ?_, ?_⟩
  · {
      rw [hcounts.1, hm]
    }
  · {
      rw [hcounts.2, hm]
    }

/-- A power of three that reaches `1` has only immediate divisions. -/
theorem FamilyCountsPower (p : Parameters) (hD : p.D = 3)
    (n : ℤ) (t m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hn : n = (3 : ℤ) ^ t) (hs0 : s 0 = n) (hsm : s m = 1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ 1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) :
    m = t ∧ ZeroSteps L m = t ∧ OneSteps L m = 0 := by
  have hpure := PureDivisionEquality p hD t
  have huniq :=
    BlockCountsUnique p n 1 m t s (fun i => (3 : ℤ) ^ (t - i)) L
      (fun _ => 0) hs0 (by rw [hn]; exact hpure.2.2.1) hsm
      hpure.2.2.2.1 hsmin hpure.2.2.2.2.1 hL hpure.2.2.2.2.2.1
  refine ⟨huniq.1, ?_, ?_⟩
  · {
      rw [huniq.2.1, hpure.2.2.2.2.2.2.1]
    }
  · {
      rw [huniq.2.2, hpure.2.2.2.2.2.2.2.1]
    }

/-- A mixed power that reaches `1` has one length-two block. -/
theorem FamilyCountsMixed (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (t m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hn : n = 4 * (3 : ℤ) ^ t) (hs0 : s 0 = n) (hsm : s m = 1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ 1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) :
    m = t + 2 ∧ ZeroSteps L m = t + 1 ∧ OneSteps L m = 1 := by
  have hmixed := MixedPowerEquality p hQ hC hD t
  have huniq :=
    BlockCountsUnique p n 1 m (t + 2) s (MixedSeed t) L (MixedBlock t)
      hs0 (by rw [hn]; exact hmixed.1) hsm hmixed.2.1 hsmin
      hmixed.2.2.1 hL hmixed.2.2.2.1
  refine ⟨huniq.1, ?_, ?_⟩
  · {
      rw [huniq.2.1, hmixed.2.2.2.2.1]
    }
  · {
      rw [huniq.2.2, hmixed.2.2.2.2.2.1]
    }

/-- A negative power of three that reaches `-1` has only immediate divisions. -/
theorem FamilyCountsNeg (p : Parameters) (hD : p.D = 3)
    (n : ℤ) (t m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hn : n = -(3 : ℤ) ^ t) (hs0 : s 0 = n) (hsm : s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ -1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) :
    m = t ∧ ZeroSteps L m = t ∧ OneSteps L m = 0 := by
  have hpure := NegPureDivisionEquality p hD t
  have huniq :=
    BlockCountsUnique p n (-1) m t s (fun i => -(3 : ℤ) ^ (t - i)) L
      (fun _ => 0) hs0 (by rw [hn]; exact hpure.2.2.1) hsm
      hpure.2.2.2.1 hsmin hpure.2.2.2.2.1 hL hpure.2.2.2.2.2.1
  refine ⟨huniq.1, ?_, ?_⟩
  · {
      rw [huniq.2.1, hpure.2.2.2.2.2.2.1]
    }
  · {
      rw [huniq.2.2, hpure.2.2.2.2.2.2.2.1]
    }

/-- Every first hit has length one or two, so the raw time is `a0+2*a1`. -/
theorem RawTimeFromCounts (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m k : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n) (hsm : s m = 1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ 1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hk : Iterate (RawStep p) k n = 1)
    (hkmin : ∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ 1) :
    k = ZeroSteps L m + 2 * OneSteps L m := by
  have hlen : ∀ i : ℕ, i < m → L i = 0 ∨ L i = 1 := by
    intro i hi
    exact FirstHitIsZeroOrOne p hQ hC hD (s i) (L i) (hL i hi).1
  have hsum := (StepsPartition m L hlen).2
  have hadd :=
    ReturnChainAddsToHit p hQ hC hD n m k s L hs0 hsm hsmin hL hk
      hkmin
  rw [← hsum] at hadd
  exact hadd.symm

/-- The seed `4*3^t` meets `1` first at time `t+3`. -/
theorem FamilyRawTimeMixed (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (t : ℕ) (hn : n = 4 * (3 : ℤ) ^ t) :
    Iterate (RawStep p) (t + 3) n = 1 ∧
      ∀ j : ℕ, j < t + 3 → Iterate (RawStep p) j n ≠ 1 := by
  classical
  have hmixed := MixedPowerEquality p hQ hC hD t
  have hs0 : MixedSeed t 0 = n := by
    rw [hn]
    exact hmixed.1
  have hlen : ∀ i : ℕ, i < t + 2 →
      MixedBlock t i = 0 ∨ MixedBlock t i = 1 := by
    intro i hi
    exact FirstHitIsZeroOrOne p hQ hC hD (MixedSeed t i)
      (MixedBlock t i) (hmixed.2.2.2.1 i hi).1
  have hsum := (StepsPartition (t + 2) (MixedBlock t) hlen).2
  have hcount :
      ZeroSteps (MixedBlock t) (t + 2) +
          2 * OneSteps (MixedBlock t) (t + 2) =
        t + 3 := by
    rw [hmixed.2.2.2.2.1, hmixed.2.2.2.2.2.1] at hsum
    omega
  rw [hcount] at hsum
  have horbit :=
    ReturnChainIsOrbit p n (t + 2) (MixedSeed t) (MixedBlock t) hs0
      hmixed.2.2.2.1 (t + 2) (Nat.le_refl (t + 2))
  rw [← hsum] at horbit
  have hhit : Iterate (RawStep p) (t + 3) n = 1 := by
    rw [← horbit]
    exact hmixed.2.1
  have hex : ∃ j : ℕ, Iterate (RawStep p) j n = 1 := ⟨t + 3, hhit⟩
  let k := Nat.find hex
  have hk : Iterate (RawStep p) k n = 1 := Nat.find_spec hex
  have hkmin : ∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ 1 :=
    fun i hi => Nat.find_min hex hi
  have hkval :=
    RawTimeFromCounts p hQ hC hD n (t + 2) k (MixedSeed t)
      (MixedBlock t) hs0 hmixed.2.1 hmixed.2.2.1 hmixed.2.2.2.1 hk
      hkmin
  have hkt : k = t + 3 := by
    rw [hkval, hmixed.2.2.2.2.1, hmixed.2.2.2.2.2.1]
  refine ⟨?_, ?_⟩
  · {
      rw [← hkt]
      exact hk
    }
  · {
      intro j hj
      rw [← hkt] at hj
      exact hkmin j hj
    }

/-- Every first hit has length one or two, so a chain to `-1` has raw time `a0+2*a1`. -/
theorem RawTimeFromCountsNeg (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m k : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n) (hsm : s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ -1)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hk : Iterate (RawStep p) k n = -1)
    (hkmin : ∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ -1) :
    k = ZeroSteps L m + 2 * OneSteps L m := by
  have hlen : ∀ i : ℕ, i < m → L i = 0 ∨ L i = 1 := by
    intro i hi
    exact FirstHitIsZeroOrOne p hQ hC hD (s i) (L i) (hL i hi).1
  have hsum := (StepsPartition m L hlen).2
  have hadd :=
    ReturnChainAddsToNegOne p hQ hC hD n m k s L hs0 hsm hsmin hL
      hk hkmin
  rw [← hsum] at hadd
  exact hadd.symm

/-- The seed `3^t` meets `1` first at time `t`. -/
theorem FamilyRawTimePower (p : Parameters) (hD : p.D = 3)
    (n : ℤ) (t : ℕ) (hn : n = (3 : ℤ) ^ t) :
    Iterate (RawStep p) t n = 1 ∧
      ∀ j : ℕ, j < t → Iterate (RawStep p) j n ≠ 1 := by
  have hpure := PureDivisionEquality p hD t
  refine ⟨?_, ?_⟩
  · {
      rw [hn]
      exact hpure.1
    }
  · {
      intro j hj
      rw [hn]
      exact hpure.2.1 j hj
    }

/-- The seed `-3^t` meets `-1` first at time `t`. -/
theorem FamilyRawTimeNeg (p : Parameters) (hD : p.D = 3)
    (n : ℤ) (t : ℕ) (hn : n = -(3 : ℤ) ^ t) :
    Iterate (RawStep p) t n = -1 ∧
      ∀ j : ℕ, j < t → Iterate (RawStep p) j n ≠ -1 := by
  have hpure := NegPureDivisionEquality p hD t
  refine ⟨?_, ?_⟩
  · {
      rw [hn]
      exact hpure.1
    }
  · {
      intro j hj
      rw [hn]
      exact hpure.2.1 j hj
    }

/-- The orbit of `4 * 3^t` is `4 * 3^{t-j}` through time `t`, then `9`, `3`, and `1`. -/
theorem FamilyOrbitMixed (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (t : ℕ) :
    let n : ℤ := 4 * (3 : ℤ) ^ t
    (∀ j : ℕ, j ≤ t →
        Iterate (RawStep p) j n = 4 * (3 : ℤ) ^ (t - j)) ∧
      Iterate (RawStep p) (t + 1) n = 9 ∧
      Iterate (RawStep p) (t + 2) n = 3 ∧
      Iterate (RawStep p) (t + 3) n = 1 := by
  intro n
  have hpref : ∀ j : ℕ, j ≤ t →
      Iterate (RawStep p) j n = 4 * (3 : ℤ) ^ (t - j) := by
    intro j hj
    have hpow : (3 : ℤ) ^ t = (3 : ℤ) ^ j * (3 : ℤ) ^ (t - j) := by
      rw [← pow_add]
      congr 1
      omega
    have hmul : n = (3 : ℤ) ^ j * (4 * (3 : ℤ) ^ (t - j)) := by
      simp only [n]
      rw [hpow]
      ring
    rw [hmul]
    exact TriplePowerReturns p hD (4 * (3 : ℤ) ^ (t - j)) j
  have hfour : Iterate (RawStep p) t n = 4 := by
    rw [hpref t (Nat.le_refl t)]
    simp
  have hnine : Iterate (RawStep p) (t + 1) n = 9 := by
    have hstep : Iterate (RawStep p) (t + 1) n =
        RawStep p (Iterate (RawStep p) t n) := rfl
    rw [hstep, hfour]
    exact RawStepFour p hQ hC hD
  have hthree : Iterate (RawStep p) (t + 2) n = 3 := by
    have hstep : Iterate (RawStep p) (t + 2) n =
        RawStep p (Iterate (RawStep p) (t + 1) n) := by
      have hidx : t + 2 = (t + 1) + 1 := by omega
      rw [hidx]
      rfl
    rw [hstep, hnine]
    exact RawStepNine p hD
  have hone : Iterate (RawStep p) (t + 3) n = 1 := by
    have hstep : Iterate (RawStep p) (t + 3) n =
        RawStep p (Iterate (RawStep p) (t + 2) n) := by
      have hidx : t + 3 = (t + 2) + 1 := by omega
      rw [hidx]
      rfl
    rw [hstep, hthree]
    exact RawStepThree p hD
  exact ⟨hpref, hnine, hthree, hone⟩

/-- The only raw predecessors of `9` are `27` and `4`. -/
theorem NinePreimages (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    RawStep p n = 9 ↔ n = 27 ∨ n = 4 := by
  constructor
  · {
      intro hstep
      rcases (RawStepPreimage p hQ hC hD n 9).mp hstep with hdiv | haff
      · {
          left
          have hnum : n = 27 := by
            rw [hdiv]
            ring
          exact hnum
        }
      · {
          right
          have hn : n = (9 - 1) / 2 := haff.2.2
          have hfour : (9 - 1) / (2 : ℤ) = 4 := by decide
          rw [hfour] at hn
          exact hn
        }
    }
  · {
      intro h
      rcases h with h27 | h4
      · {
          rw [h27]
          exact StepOfTriple p hD 9
        }
      · {
          rw [h4]
          exact RawStepFour p hQ hC hD
        }
    }

/-- After `1`, the raw orbit alternates between `1` and `3`. -/
theorem OneAlternates (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (m : ℕ) :
    Iterate (RawStep p) (2 * m) (1 : ℤ) = 1 ∧
      Iterate (RawStep p) (2 * m + 1) (1 : ℤ) = 3 := by
  induction m with
  | zero => {
      constructor
      · {
          rfl
        }
      · {
          exact RawStepOne p hQ hC hD
        }
    }
  | succ m ih => {
      obtain ⟨heven, hodd⟩ := ih
      have htwo : 2 * (m + 1) = 2 * m + 2 := by omega
      have hthree : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
      constructor
      · {
          rw [htwo]
          have hmid : Iterate (RawStep p) (2 * m + 1) (1 : ℤ) =
              RawStep p (Iterate (RawStep p) (2 * m) 1) := rfl
          have hstep : Iterate (RawStep p) (2 * m + 2) (1 : ℤ) =
              RawStep p (Iterate (RawStep p) (2 * m + 1) (1 : ℤ)) := by
            have hidx : 2 * m + 2 = (2 * m + 1) + 1 := by omega
            rw [hidx]
            rfl
          rw [hstep, hmid, heven, RawStepOne p hQ hC hD, RawStepThree p hD]
        }
      · {
          rw [hthree]
          have hstep : Iterate (RawStep p) (2 * m + 3) (1 : ℤ) =
              RawStep p (Iterate (RawStep p) (2 * m + 2) (1 : ℤ)) := by
            have hidx : 2 * m + 3 = (2 * m + 2) + 1 := by omega
            rw [hidx]
            rfl
          have hback : Iterate (RawStep p) (2 * m + 2) (1 : ℤ) = 1 := by
            have hmid : Iterate (RawStep p) (2 * m + 1) (1 : ℤ) =
                RawStep p (Iterate (RawStep p) (2 * m) 1) := rfl
            have hstep' : Iterate (RawStep p) (2 * m + 2) (1 : ℤ) =
                RawStep p (Iterate (RawStep p) (2 * m + 1) (1 : ℤ)) := by
              have hidx : 2 * m + 2 = (2 * m + 1) + 1 := by omega
              rw [hidx]
              rfl
            rw [hstep', hmid, heven, RawStepOne p hQ hC hD, RawStepThree p hD]
          rw [hstep, hback, RawStepOne p hQ hC hD]
        }
    }

/-- The fixed point `-1` stays at `-1`. -/
theorem NegOneStays (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (m : ℕ) :
    Iterate (RawStep p) m (-1 : ℤ) = -1 := by
  induction m with
  | zero => {
      rfl
    }
  | succ m ih => {
      rw [Iterate, ih, RawStepNegOne p hQ hC hD]
    }

/-- On `3^t`, the state `9` occurs only at time `t-2`, and its predecessor is `27`. -/
theorem NineOnPower (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (t k : ℕ)
    (hk : Iterate (RawStep p) k ((3 : ℤ) ^ t) = 9) :
    k + 2 = t ∧
      (0 < k → Iterate (RawStep p) (k - 1) ((3 : ℤ) ^ t) = 27) := by
  have hkLe : k ≤ t := by
    by_contra hgt
    have hlt : t < k := Nat.lt_of_not_ge hgt
    have htail : Iterate (RawStep p) k ((3 : ℤ) ^ t) =
        Iterate (RawStep p) (k - t) (1 : ℤ) := by
      have hsplit := IterateAdd (RawStep p) t (k - t) ((3 : ℤ) ^ t)
      have htime : t + (k - t) = k := by omega
      rw [htime] at hsplit
      have hone : Iterate (RawStep p) t ((3 : ℤ) ^ t) = 1 := by
        rw [PowerAt p hD t t (Nat.le_refl t)]
        simp
      rw [hone] at hsplit
      exact hsplit
    rw [htail] at hk
    rcases Nat.even_or_odd (k - t) with ⟨m, hm⟩ | ⟨m, hm⟩
    · {
        have htwo' : k - t = 2 * m := by
          rw [hm]
          omega
        have halt := (OneAlternates p hQ hC hD m).1
        rw [htwo', halt] at hk
        omega
      }
    · {
        have halt := (OneAlternates p hQ hC hD m).2
        rw [hm, halt] at hk
        omega
      }
  have hpow := PowerAt p hD t k hkLe
  rw [hpow] at hk
  have hnine : (9 : ℤ) = (3 : ℤ) ^ 2 := by decide
  rw [hnine] at hk
  have hnat : (3 : ℕ) ^ (t - k) = 3 ^ 2 := by
    apply Nat.cast_injective (R := ℤ)
    simpa [Nat.cast_pow] using hk
  have hexp : t - k = 2 :=
    Nat.pow_right_injective (by decide : 2 ≤ 3) hnat
  refine ⟨by omega, ?_⟩
  intro hkpos
  have hprev := PowerAt p hD t (k - 1) (by omega)
  have hexp' : t - (k - 1) = 3 := by omega
  rw [hprev, hexp']
  decide

/-- On `4 * 3^t`, the state `9` occurs only at time `t+1`, and its predecessor is `4`. -/
theorem NineOnMixed (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (t k : ℕ)
    (hk : Iterate (RawStep p) k (4 * (3 : ℤ) ^ t) = 9) :
    k = t + 1 ∧
      Iterate (RawStep p) (k - 1) (4 * (3 : ℤ) ^ t) = 4 := by
  have horbit := FamilyOrbitMixed p hQ hC hD t
  have hpref := horbit.1
  have hnine := horbit.2.1
  have hthree := horbit.2.2.1
  have hone := horbit.2.2.2
  by_cases hle : k ≤ t
  · {
      have hstate := hpref k hle
      rw [hstate] at hk
      have hdvd : (4 : ℤ) ∣ 4 * (3 : ℤ) ^ (t - k) :=
        ⟨(3 : ℤ) ^ (t - k), by ring⟩
      have hdvd9 : (4 : ℤ) ∣ 9 := by
        rw [← hk]
        exact hdvd
      exact False.elim ((by decide : ¬ (4 : ℤ) ∣ 9) hdvd9)
    }
  · {
      have hgt : t < k := Nat.lt_of_not_ge hle
      have hk1 : k = t + 1 ∨ t + 1 < k := by omega
      rcases hk1 with hk1 | hgt1
      · {
          refine ⟨hk1, ?_⟩
          have hprev := hpref t (Nat.le_refl t)
          have hidx : k - 1 = t := by omega
          rw [hidx, hprev]
          simp
        }
      · {
          have hk2 : k = t + 2 ∨ t + 2 < k := by omega
          rcases hk2 with hk2 | hgt2
          · {
              rw [hk2] at hk
              rw [hthree] at hk
              omega
            }
          · {
              have htail : Iterate (RawStep p) k (4 * (3 : ℤ) ^ t) =
                  Iterate (RawStep p) (k - (t + 3)) (1 : ℤ) := by
                have hsplit :=
                  IterateAdd (RawStep p) (t + 3) (k - (t + 3))
                    (4 * (3 : ℤ) ^ t)
                have htime : t + 3 + (k - (t + 3)) = k := by omega
                rw [htime] at hsplit
                rw [hone] at hsplit
                exact hsplit
              rw [htail] at hk
              rcases Nat.even_or_odd (k - (t + 3)) with ⟨m, hm⟩ | ⟨m, hm⟩
              · {
                  have htwo' : k - (t + 3) = 2 * m := by
                    rw [hm]
                    omega
                  rw [htwo', (OneAlternates p hQ hC hD m).1] at hk
                  omega
                }
              · {
                  rw [hm, (OneAlternates p hQ hC hD m).2] at hk
                  omega
                }
            }
        }
    }

/-- The orbit of `-3^t` never meets `9`. -/
theorem NineOnNeg (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (t k : ℕ)
    (hk : Iterate (RawStep p) k (-(3 : ℤ) ^ t) = 9) : False := by
  by_cases hle : k ≤ t
  · {
      have hstate := NegPowerAt p hD t k hle
      rw [hstate] at hk
      have hneg : -(3 : ℤ) ^ (t - k) < 0 := by
        have hpos : (0 : ℤ) < (3 : ℤ) ^ (t - k) := by
          exact pow_pos (by decide) _
        omega
      omega
    }
  · {
      have hgt : t < k := Nat.lt_of_not_ge hle
      have htail : Iterate (RawStep p) k (-(3 : ℤ) ^ t) =
          Iterate (RawStep p) (k - t) (-1 : ℤ) := by
        have hsplit :=
          IterateAdd (RawStep p) t (k - t) (-(3 : ℤ) ^ t)
        have htime : t + (k - t) = k := by omega
        rw [htime] at hsplit
        have hneg1 : Iterate (RawStep p) t (-(3 : ℤ) ^ t) = -1 := by
          rw [NegPowerAt p hD t t (Nat.le_refl t)]
          simp
        rw [hneg1] at hsplit
        exact hsplit
      rw [htail, NegOneStays p hQ hC hD] at hk
      omega
    }

/-- After the first visit to `1`, the orbit alternates between `1` and `3`. -/
theorem AfterOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (k m : ℕ)
    (hk : Iterate (RawStep p) k n = 1) :
    Iterate (RawStep p) (k + 2 * m) n = 1 ∧
      Iterate (RawStep p) (k + 2 * m + 1) n = 3 := by
  have halt := OneAlternates p hQ hC hD m
  constructor
  · {
      have hsplit := IterateAdd (RawStep p) k (2 * m) n
      rw [hsplit, hk]
      exact halt.1
    }
  · {
      have hidx : k + 2 * m + 1 = k + (2 * m + 1) := by omega
      rw [hidx]
      have hsplit := IterateAdd (RawStep p) k (2 * m + 1) n
      rw [hsplit, hk]
      exact halt.2
    }

/-- After the first visit to `-1`, the orbit stays at `-1`. -/
theorem AfterNegOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (k m : ℕ)
    (hk : Iterate (RawStep p) k n = -1) :
    Iterate (RawStep p) (k + m) n = -1 := by
  have hsplit := IterateAdd (RawStep p) k m n
  rw [hsplit, hk, NegOneStays p hQ hC hD]

/-- The raw step fixes `n` if and only if `n` is `0` or `-1`. -/
theorem FixedPoints (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    RawStep p n = n ↔ n = 0 ∨ n = -1 := by
  constructor
  · {
      intro h
      by_cases hd : p.D ∣ n
      · {
          have hd' := hd
          obtain ⟨m, hm⟩ := hd'
          rw [hD] at hm
          rw [RawStep, if_pos hd, hD] at h
          have hdiv : n / 3 = m := by
            rw [hm]
            exact Int.mul_ediv_cancel_left m (by decide : (3 : ℤ) ≠ 0)
          rw [hdiv] at h
          have hzero : n = 0 := by
            rw [hm] at h
            omega
          left
          exact hzero
        }
      · {
          rw [RawStep, if_neg hd, hQ, hC] at h
          right
          omega
        }
    }
  · {
      intro h
      rcases h with h0 | hneg
      · {
          rw [h0]
          exact RawStepZero p hD
        }
      · {
          rw [hneg]
          exact RawStepNegOne p hQ hC hD
        }
    }

/-- The second raw step returns to `n` exactly on `0`, `-1`, `1`, and `3`. -/
theorem SquareFixed (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    RawStep p (RawStep p n) = n ↔
      n = 0 ∨ n = -1 ∨ n = 1 ∨ n = 3 := by
  constructor
  · {
      intro hsq
      by_cases hd : p.D ∣ n
      · {
          obtain ⟨a, ha⟩ := id hd
          rw [hD] at ha
          have hstep : RawStep p n = a := by
            rw [RawStep, if_pos hd, hD, ha]
            exact Int.mul_ediv_cancel_left a (by decide : (3 : ℤ) ≠ 0)
          rw [hstep] at hsq
          by_cases hd2 : p.D ∣ a
          · {
              obtain ⟨b, hb⟩ := id hd2
              rw [hD] at hb
              have hstep2 : RawStep p a = b := by
                rw [RawStep, if_pos hd2, hD, hb]
                exact Int.mul_ediv_cancel_left b (by decide : (3 : ℤ) ≠ 0)
              rw [hstep2] at hsq
              have hzero : n = 0 := by
                rw [ha, hb] at hsq
                omega
              left
              exact hzero
            }
          · {
              rw [RawStep, if_neg hd2, hQ, hC] at hsq
              have ha1 : a = 1 := by
                rw [ha] at hsq
                omega
              have hn : n = 3 := by
                rw [ha, ha1]
                ring
              right
              right
              right
              exact hn
            }
        }
      · {
          have hstep : RawStep p n = 2 * n + 1 := by
            rw [RawStep, if_neg hd, hQ, hC]
          rw [hstep] at hsq
          by_cases hd2 : p.D ∣ (2 * n + 1)
          · {
              have hstep2 : RawStep p (2 * n + 1) = (2 * n + 1) / 3 := by
                rw [RawStep, if_pos hd2, hD]
              rw [hstep2] at hsq
              have hd3 : (3 : ℤ) ∣ (2 * n + 1) := by
                rwa [hD] at hd2
              have hback : 3 * ((2 * n + 1) / 3) = 2 * n + 1 :=
                Int.mul_ediv_cancel_of_dvd hd3
              rw [hsq] at hback
              right
              right
              left
              omega
            }
          · {
              rw [RawStep, if_neg hd2, hQ, hC] at hsq
              right
              left
              omega
            }
        }
    }
  · {
      intro h
      rcases h with h0 | hneg | h1 | h3
      · {
          rw [h0, RawStepZero p hD, RawStepZero p hD]
        }
      · {
          rw [hneg, RawStepNegOne p hQ hC hD, RawStepNegOne p hQ hC hD]
        }
      · {
          rw [h1, RawStepOne p hQ hC hD, RawStepThree p hD]
        }
      · {
          rw [h3, RawStepThree p hD, RawStepOne p hQ hC hD]
        }
    }

/-- The raw orbit has exact period two exactly at `1` and `3`. -/
theorem ExactPeriodTwo (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    (RawStep p (RawStep p n) = n ∧ RawStep p n ≠ n) ↔
      n = 1 ∨ n = 3 := by
  constructor
  · {
      intro h
      obtain ⟨hsq, hne⟩ := h
      rcases (SquareFixed p hQ hC hD n).mp hsq with h0 | hneg | h1 | h3
      · {
          exact False.elim (hne (by rw [h0]; exact RawStepZero p hD))
        }
      · {
          exact False.elim
            (hne (by rw [hneg]; exact RawStepNegOne p hQ hC hD))
        }
      · {
          left
          exact h1
        }
      · {
          right
          exact h3
        }
    }
  · {
      intro h
      rcases h with h1 | h3
      · {
          refine ⟨?_, ?_⟩
          · {
              rw [h1, RawStepOne p hQ hC hD, RawStepThree p hD]
            }
          · {
              rw [h1, RawStepOne p hQ hC hD]
              decide
            }
        }
      · {
          refine ⟨?_, ?_⟩
          · {
              rw [h3, RawStepThree p hD, RawStepOne p hQ hC hD]
            }
          · {
              rw [h3, RawStepThree p hD]
              decide
            }
        }
    }

/-- A seed cannot meet both `1` and `-1`. -/
theorem TerminalDisjoint (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (k j : ℕ)
    (h1 : Iterate (RawStep p) k n = 1)
    (hneg : Iterate (RawStep p) j n = -1) : False := by
  by_cases hle : k ≤ j
  · {
      rcases Nat.even_or_odd (j - k) with ⟨m, hm⟩ | ⟨m, hm⟩
      · {
          have hidx : j = k + 2 * m := by omega
          have htail := (AfterOne p hQ hC hD n k m h1).1
          rw [← hidx] at htail
          rw [hneg] at htail
          omega
        }
      · {
          have hidx : j = k + 2 * m + 1 := by omega
          have htail := (AfterOne p hQ hC hD n k m h1).2
          rw [← hidx] at htail
          rw [hneg] at htail
          omega
        }
    }
  · {
      have hgt : j < k := Nat.lt_of_not_ge hle
      have hidx : k = j + (k - j) := by omega
      have htail := AfterNegOne p hQ hC hD n j (k - j) hneg
      rw [← hidx] at htail
      rw [h1] at htail
      omega
    }

/-- The raw step sends `n` to `0` exactly when `n` is `0`. -/
theorem OnlyZeroToZero (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    RawStep p n = 0 ↔ n = 0 := by
  constructor
  · {
      intro h
      by_cases hd : p.D ∣ n
      · {
          obtain ⟨a, ha⟩ := id hd
          rw [hD] at ha
          have hstep : RawStep p n = a := by
            rw [RawStep, if_pos hd, hD, ha]
            exact Int.mul_ediv_cancel_left a (by decide : (3 : ℤ) ≠ 0)
          rw [hstep] at h
          rw [ha, h]
          ring
        }
      · {
          rw [RawStep, if_neg hd, hQ, hC] at h
          omega
        }
    }
  · {
      intro h
      rw [h]
      exact RawStepZero p hD
    }

/-- The raw orbit meets `0` if and only if the seed is `0`. -/
theorem MeetsZeroIffZero (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (k : ℕ) (hk : Iterate (RawStep p) k n = 0) : n = 0 := by
  induction k with
  | zero => {
      simp only [Iterate] at hk
      exact hk
    }
  | succ k ih => {
      have hstep : RawStep p (Iterate (RawStep p) k n) = 0 := by
        simp only [Iterate] at hk
        exact hk
      have hprev := (OnlyZeroToZero p hQ hC hD _).mp hstep
      exact ih hprev
    }

/-- A fixed point has a constant orbit. -/
theorem IterateFixed (p : Parameters) (n : ℤ) (hn : RawStep p n = n)
    (k : ℕ) : Iterate (RawStep p) k n = n := by
  induction k with
  | zero => {
      simp [Iterate]
    }
  | succ k ih => {
      simp only [Iterate]
      rw [ih, hn]
    }

/-- The orbit of a seed cannot meet both `0` and `1`. -/
theorem ZeroMissesOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (k j : ℕ)
    (h0 : Iterate (RawStep p) k n = 0)
    (h1 : Iterate (RawStep p) j n = 1) : False := by
  have hn := MeetsZeroIffZero p hQ hC hD n k h0
  rw [hn] at h1
  have hstay :=
    IterateFixed p (0 : ℤ) (RawStepZero p hD) j
  rw [hstay] at h1
  omega

/-- The orbit of a seed cannot meet both `0` and `-1`. -/
theorem ZeroMissesNegOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (k j : ℕ)
    (h0 : Iterate (RawStep p) k n = 0)
    (hneg : Iterate (RawStep p) j n = -1) : False := by
  have hn := MeetsZeroIffZero p hQ hC hD n k h0
  rw [hn] at hneg
  have hstay :=
    IterateFixed p (0 : ℤ) (RawStepZero p hD) j
  rw [hstay] at hneg
  omega

/-- The third raw step returns to `n` exactly at the fixed points `0` and `-1`. -/
theorem CubeFixed (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    RawStep p (RawStep p (RawStep p n)) = n ↔ n = 0 ∨ n = -1 := by
  constructor
  · {
      intro hcube
      by_cases h1 : p.D ∣ n
      · {
          obtain ⟨a, ha⟩ := id h1
          rw [hD] at ha
          have hstep1 : RawStep p n = a := by
            rw [RawStep, if_pos h1, hD, ha]
            exact Int.mul_ediv_cancel_left a (by decide : (3 : ℤ) ≠ 0)
          rw [hstep1] at hcube
          by_cases h2 : p.D ∣ a
          · {
              obtain ⟨b, hb⟩ := id h2
              rw [hD] at hb
              have hstep2 : RawStep p a = b := by
                rw [RawStep, if_pos h2, hD, hb]
                exact Int.mul_ediv_cancel_left b (by decide : (3 : ℤ) ≠ 0)
              rw [hstep2] at hcube
              by_cases h3 : p.D ∣ b
              · {
                  obtain ⟨c, hc⟩ := id h3
                  rw [hD] at hc
                  have hstep3 : RawStep p b = c := by
                    rw [RawStep, if_pos h3, hD, hc]
                    exact Int.mul_ediv_cancel_left c
                      (by decide : (3 : ℤ) ≠ 0)
                  rw [hstep3] at hcube
                  have hzero : n = 0 := by
                    rw [ha, hb, hc] at hcube
                    omega
                  left
                  exact hzero
                }
              · {
                  rw [RawStep, if_neg h3, hQ, hC] at hcube
                  have hfalse : False := by
                    rw [ha, hb] at hcube
                    omega
                  exact False.elim hfalse
                }
            }
          · {
              have hstep2 : RawStep p a = 2 * a + 1 := by
                rw [RawStep, if_neg h2, hQ, hC]
              rw [hstep2] at hcube
              by_cases h3 : p.D ∣ (2 * a + 1)
              · {
                  have hstep3 : RawStep p (2 * a + 1) =
                      (2 * a + 1) / 3 := by
                    rw [RawStep, if_pos h3, hD]
                  rw [hstep3] at hcube
                  have hd3 : (3 : ℤ) ∣ (2 * a + 1) := by
                    rwa [hD] at h3
                  have hback : 3 * ((2 * a + 1) / 3) = 2 * a + 1 :=
                    Int.mul_ediv_cancel_of_dvd hd3
                  rw [hcube] at hback
                  have hfalse : False := by
                    rw [ha] at hback
                    omega
                  exact False.elim hfalse
                }
              · {
                  rw [RawStep, if_neg h3, hQ, hC] at hcube
                  have ha3 : a = -3 := by
                    rw [ha] at hcube
                    omega
                  have hdiv : p.D ∣ a := by
                    rw [ha3, hD]
                    decide
                  exact False.elim (h2 hdiv)
                }
            }
        }
      · {
          have hstep1 : RawStep p n = 2 * n + 1 := by
            rw [RawStep, if_neg h1, hQ, hC]
          rw [hstep1] at hcube
          by_cases h2 : p.D ∣ (2 * n + 1)
          · {
              have hstep2 : RawStep p (2 * n + 1) = (2 * n + 1) / 3 := by
                rw [RawStep, if_pos h2, hD]
              rw [hstep2] at hcube
              have hd3 : (3 : ℤ) ∣ (2 * n + 1) := by
                rwa [hD] at h2
              set q : ℤ := (2 * n + 1) / 3
              have hback : 3 * q = 2 * n + 1 :=
                Int.mul_ediv_cancel_of_dvd hd3
              by_cases h3 : p.D ∣ q
              · {
                  obtain ⟨b, hb⟩ := id h3
                  rw [hD] at hb
                  have hstep3 : RawStep p q = b := by
                    rw [RawStep, if_pos h3, hD, hb]
                    exact Int.mul_ediv_cancel_left b
                      (by decide : (3 : ℤ) ≠ 0)
                  rw [hstep3] at hcube
                  have hfalse : False := by
                    rw [hb] at hback
                    rw [hcube] at hback
                    omega
                  exact False.elim hfalse
                }
              · {
                  rw [RawStep, if_neg h3, hQ, hC] at hcube
                  have hq : q = -3 := by
                    rw [← hcube] at hback
                    omega
                  have hdiv : p.D ∣ q := by
                    rw [hq, hD]
                    decide
                  exact False.elim (h3 hdiv)
                }
            }
          · {
              have hstep2 : RawStep p (2 * n + 1) = 2 * (2 * n + 1) + 1 := by
                rw [RawStep, if_neg h2, hQ, hC]
              rw [hstep2] at hcube
              by_cases h3 : p.D ∣ (2 * (2 * n + 1) + 1)
              · {
                  have hstep3 : RawStep p (2 * (2 * n + 1) + 1) =
                      (2 * (2 * n + 1) + 1) / 3 := by
                    rw [RawStep, if_pos h3, hD]
                  rw [hstep3] at hcube
                  have hd3 : (3 : ℤ) ∣ (2 * (2 * n + 1) + 1) := by
                    rwa [hD] at h3
                  have hback :
                      3 * ((2 * (2 * n + 1) + 1) / 3) =
                        2 * (2 * n + 1) + 1 :=
                    Int.mul_ediv_cancel_of_dvd hd3
                  rw [hcube] at hback
                  have hn : n = -3 := by omega
                  have hdiv : p.D ∣ n := by
                    rw [hn, hD]
                    decide
                  exact False.elim (h1 hdiv)
                }
              · {
                  rw [RawStep, if_neg h3, hQ, hC] at hcube
                  right
                  omega
                }
            }
        }
    }
  · {
      intro h
      rcases h with h0 | hneg
      · {
          rw [h0, RawStepZero p hD, RawStepZero p hD, RawStepZero p hD]
        }
      · {
          rw [hneg, RawStepNegOne p hQ hC hD, RawStepNegOne p hQ hC hD,
            RawStepNegOne p hQ hC hD]
        }
    }

/-- There is no state of exact raw period three. -/
theorem NoExactPeriodThree (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (h : RawStep p (RawStep p (RawStep p n)) = n)
    (hne : RawStep p n ≠ n) : False := by
  rcases (CubeFixed p hQ hC hD n).mp h with h0 | hneg
  · {
      exact hne (by rw [h0]; exact RawStepZero p hD)
    }
  · {
      exact hne (by rw [hneg]; exact RawStepNegOne p hQ hC hD)
    }

/-- Residue `2` is invariant under the affine step. -/
theorem ResidueTwoInvariant (n : ℤ) (h : n % 3 = 2) :
    (2 * n + 1) % 3 = 2 := by
  set q : ℤ := n / 3
  have hsplit : n = 2 + 3 * q := by
    have hbase := (Int.emod_add_mul_ediv n 3).symm
    rw [h] at hbase
    simpa [q] using hbase
  have haff : 2 * n + 1 = 2 + 3 * (2 * q + 1) := by
    rw [hsplit]
    ring
  rw [haff, Int.add_mul_emod_self_left]
  decide

/-- The affine step grows at every integer other than `-1`. -/
theorem AffineGrows (n : ℤ) (hne : n ≠ -1) :
    n.natAbs < (2 * n + 1).natAbs := by
  by_cases hpos : 0 ≤ n
  · {
      have hn : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hpos
      have haff : ((2 * n + 1).natAbs : ℤ) = 2 * n + 1 := by
        apply Int.natAbs_of_nonneg
        omega
      omega
    }
  · {
      have hneg : n ≤ -2 := by omega
      have hn : (n.natAbs : ℤ) = -n := by
        exact Int.ofNat_natAbs_of_nonpos (by omega : n ≤ 0)
      have haff : ((2 * n + 1).natAbs : ℤ) = -(2 * n + 1) := by
        exact Int.ofNat_natAbs_of_nonpos (by omega : 2 * n + 1 ≤ 0)
      omega
    }

/-- A residue-`2` seed takes the affine step. -/
theorem ResidueTwoStep (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (h : n % 3 = 2) : RawStep p n = 2 * n + 1 := by
  have hnot : ¬ p.D ∣ n := by
    rw [hD]
    intro hd
    have hzero : n % 3 = 0 := Int.emod_eq_zero_of_dvd hd
    omega
  rw [RawStep, if_neg hnot, hQ, hC]

/-- A residue-`2` orbit stays in residue `2` and has the closed form `2^k n + 2^k - 1`. -/
theorem ResidueTwoOrbit (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (h : n % 3 = 2) (k : ℕ) :
    Iterate (RawStep p) k n % 3 = 2 ∧
      Iterate (RawStep p) k n =
        (2 : ℤ) ^ k * n + ((2 : ℤ) ^ k - 1) := by
  induction k with
  | zero => {
      refine ⟨?_, ?_⟩
      · {
          simpa [Iterate] using h
        }
      · {
          simp [Iterate]
        }
    }
  | succ k ih => {
      obtain ⟨hres, hform⟩ := ih
      refine ⟨?_, ?_⟩
      · {
          simp only [Iterate]
          rw [ResidueTwoStep p hQ hC hD _ hres]
          exact ResidueTwoInvariant _ hres
        }
      · {
          simp only [Iterate]
          rw [ResidueTwoStep p hQ hC hD _ hres, hform]
          ring
        }
    }

/-- A residue-`2` seed other than `-1` never returns. -/
theorem ResidueTwoNoCycle (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (h : n % 3 = 2) (hne : n ≠ -1) (k : ℕ) (hk : 0 < k)
    (hret : Iterate (RawStep p) k n = n) : False := by
  have hform := (ResidueTwoOrbit p hQ hC hD n h k).2
  rw [hret] at hform
  have hfac : ((2 : ℤ) ^ k - 1) * (n + 1) = 0 := by
    calc
      ((2 : ℤ) ^ k - 1) * (n + 1)
          = (2 : ℤ) ^ k * n + ((2 : ℤ) ^ k - 1) - n := by ring
      _ = 0 := by
        rw [← hform]
        ring
  have hpow : (2 : ℤ) ^ k - 1 ≠ 0 := by
    have hgt : (1 : ℤ) < (2 : ℤ) ^ k := by
      cases k with
      | zero => {
          omega
        }
      | succ k => {
          have hmul : (2 : ℤ) ^ (k + 1) = (2 : ℤ) ^ k * 2 := by
            rw [pow_succ]
          have hpos : (0 : ℤ) < (2 : ℤ) ^ k :=
            pow_pos (by decide : (0 : ℤ) < 2) k
          have hbase : (1 : ℤ) ≤ (2 : ℤ) ^ k := by omega
          rw [hmul]
          omega
        }
    omega
  have hprod := Int.mul_eq_zero.mp hfac
  rcases hprod with hzero | hseed
  · {
      exact hpow hzero
    }
  · {
      exact hne (by omega)
    }

/-- A residue-`2` orbit has an exact absolute value. -/
theorem ResidueTwoAbs (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (h : n % 3 = 2) (k : ℕ) :
    (Iterate (RawStep p) k n).natAbs =
      if 0 ≤ n then 2 ^ k * (n.natAbs + 1) - 1
      else 2 ^ k * (n.natAbs - 1) + 1 := by
  have hform := (ResidueTwoOrbit p hQ hC hD n h k).2
  have hstate : Iterate (RawStep p) k n =
      (2 : ℤ) ^ k * (n + 1) - 1 := by
    rw [hform]
    ring
  have hpow : (0 : ℤ) < (2 : ℤ) ^ k := pow_pos (by decide) k
  by_cases hpos : 0 ≤ n
  · {
      have hnn : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hpos
      have hseed : (1 : ℤ) ≤ n + 1 := by omega
      have hmul : (1 : ℤ) ≤ (2 : ℤ) ^ k * (n + 1) := by
        have hbase : (2 : ℤ) ^ k * 1 ≤ (2 : ℤ) ^ k * (n + 1) :=
          mul_le_mul_of_nonneg_left hseed hpow.le
        have hone : (2 : ℤ) ^ k * 1 = (2 : ℤ) ^ k := by ring
        rw [hone] at hbase
        exact le_trans (by omega : (1 : ℤ) ≤ (2 : ℤ) ^ k) hbase
      have hval : (0 : ℤ) ≤ (2 : ℤ) ^ k * (n + 1) - 1 := by omega
      have habs : ((Iterate (RawStep p) k n).natAbs : ℤ) =
          (2 : ℤ) ^ k * (n + 1) - 1 := by
        rw [hstate]
        exact Int.natAbs_of_nonneg hval
      simp [hpos]
      have hge : 1 ≤ 2 ^ k * (n.natAbs + 1) := by
        have hcast : ((2 ^ k * (n.natAbs + 1) : ℕ) : ℤ) =
            (2 : ℤ) ^ k * ((n.natAbs : ℤ) + 1) := by norm_cast
        rw [hnn] at hcast
        have hle : (1 : ℤ) ≤ ((2 ^ k * (n.natAbs + 1) : ℕ) : ℤ) := by
          rw [hcast]
          exact hmul
        exact Int.ofNat_le.mp hle
      apply Int.ofNat_inj.mp
      rw [habs, Int.ofNat_sub hge]
      have hcast : ((2 ^ k * (n.natAbs + 1) : ℕ) : ℤ) =
          (2 : ℤ) ^ k * ((n.natAbs : ℤ) + 1) := by norm_cast
      rw [hcast, hnn]
      ring
    }
  · {
      have hnn : (n.natAbs : ℤ) = -n :=
        Int.ofNat_natAbs_of_nonpos (by omega : n ≤ 0)
      have hseed : n + 1 ≤ 0 := by omega
      have hmul : (2 : ℤ) ^ k * (n + 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpow.le hseed
      have hval : (2 : ℤ) ^ k * (n + 1) - 1 ≤ 0 := by omega
      have habs : ((Iterate (RawStep p) k n).natAbs : ℤ) =
          -((2 : ℤ) ^ k * (n + 1) - 1) := by
        rw [hstate]
        exact Int.ofNat_natAbs_of_nonpos hval
      simp [hpos]
      have hge : 1 ≤ n.natAbs := by
        have hnz : n ≠ 0 := by omega
        exact Nat.succ_le_of_lt
          (Nat.pos_of_ne_zero ((Int.natAbs_eq_zero).not.mpr hnz))
      apply Int.ofNat_inj.mp
      rw [habs]
      have hright : ((2 ^ k * (n.natAbs - 1) + 1 : ℕ) : ℤ) =
          (2 : ℤ) ^ k * ((n.natAbs : ℤ) - 1) + 1 := by
        have hsub : ((n.natAbs - 1 : ℕ) : ℤ) = (n.natAbs : ℤ) - 1 :=
          Int.ofNat_sub hge
        norm_cast
      rw [hright, hnn]
      ring
    }

/-- Away from `-1`, a residue-`2` orbit strictly grows. -/
theorem ResidueTwoIncreases (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (h : n % 3 = 2) (hne : n ≠ -1) (k : ℕ) :
    (Iterate (RawStep p) k n).natAbs <
      (Iterate (RawStep p) (k + 1) n).natAbs := by
  have hk := ResidueTwoAbs p hQ hC hD n h k
  have hk1 := ResidueTwoAbs p hQ hC hD n h (k + 1)
  by_cases hpos : 0 ≤ n
  · {
      have hge : 2 ≤ n.natAbs := by
        by_contra hlt
        have hsmall : n.natAbs = 0 ∨ n.natAbs = 1 := by omega
        rcases hsmall with h0 | h1
        · {
            have hz : n = 0 := Int.natAbs_eq_zero.mp h0
            rw [hz] at h
            simp at h
          }
        · {
            have hone : n = 1 := by
              have hnn : (n.natAbs : ℤ) = n :=
                Int.natAbs_of_nonneg hpos
              rw [← hnn, h1]
              rfl
            rw [hone] at h
            norm_num at h
          }
      rw [if_pos hpos] at hk hk1
      rw [hk, hk1]
      have hm : 0 < n.natAbs + 1 := Nat.succ_pos n.natAbs
      have hmul : 2 ^ k * (n.natAbs + 1) * 1 <
          2 ^ k * (n.natAbs + 1) * 2 :=
        Nat.mul_lt_mul_of_pos_left (by decide : (1 : ℕ) < 2)
          (Nat.mul_pos (Nat.two_pow_pos k) hm)
      rw [Nat.mul_one] at hmul
      have hrw : 2 ^ (k + 1) * (n.natAbs + 1) =
          2 ^ k * (n.natAbs + 1) * 2 := by
        rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 (n.natAbs + 1),
          ← Nat.mul_assoc]
      have hlt : 2 ^ k * (n.natAbs + 1) <
          2 ^ (k + 1) * (n.natAbs + 1) := by
        rw [hrw]
        exact hmul
      have hle : 1 ≤ 2 ^ k * (n.natAbs + 1) :=
        Nat.succ_le_of_lt (Nat.mul_pos (Nat.two_pow_pos k) hm)
      exact Nat.sub_lt_sub_right hle hlt
    }
  · {
      have hge : 2 ≤ n.natAbs := by
        have hnz : n ≠ 0 := by omega
        have hone : 1 ≤ n.natAbs :=
          Nat.succ_le_of_lt
            (Nat.pos_of_ne_zero ((Int.natAbs_eq_zero).not.mpr hnz))
        by_contra hlt
        have heq : n.natAbs = 1 := by omega
        have hnn : (n.natAbs : ℤ) = -n :=
          Int.ofNat_natAbs_of_nonpos (by omega : n ≤ 0)
        rw [heq] at hnn
        have hseed : n = -1 := by omega
        exact hne hseed
      rw [if_neg hpos] at hk hk1
      rw [hk, hk1]
      have hm : 0 < n.natAbs - 1 := Nat.sub_pos_of_lt (by omega : 1 < n.natAbs)
      have hmul : 2 ^ k * (n.natAbs - 1) * 1 <
          2 ^ k * (n.natAbs - 1) * 2 :=
        Nat.mul_lt_mul_of_pos_left (by decide : (1 : ℕ) < 2)
          (Nat.mul_pos (Nat.two_pow_pos k) hm)
      rw [Nat.mul_one] at hmul
      have hrw : 2 ^ (k + 1) * (n.natAbs - 1) =
          2 ^ k * (n.natAbs - 1) * 2 := by
        rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 (n.natAbs - 1),
          ← Nat.mul_assoc]
      rw [hrw]
      exact Nat.add_lt_add_right hmul 1
    }

/-- The exact absolute increment on a residue-`2` orbit. -/
theorem ResidueTwoIncrement (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (h : n % 3 = 2) (k : ℕ) :
    (Iterate (RawStep p) (k + 1) n).natAbs =
      (Iterate (RawStep p) k n).natAbs +
        2 ^ k * (if 0 ≤ n then n.natAbs + 1 else n.natAbs - 1) := by
  have hk := ResidueTwoAbs p hQ hC hD n h k
  have hk1 := ResidueTwoAbs p hQ hC hD n h (k + 1)
  by_cases hpos : 0 ≤ n
  · {
      rw [if_pos hpos] at hk hk1
      rw [hk, hk1, if_pos hpos]
      set m := 2 ^ k * (n.natAbs + 1) with hmdef
      have hm : 1 ≤ m := by
        rw [hmdef]
        exact Nat.succ_le_of_lt
          (Nat.mul_pos (Nat.two_pow_pos k) (Nat.succ_pos n.natAbs))
      have htwo : 2 ^ (k + 1) * (n.natAbs + 1) = 2 * m := by
        rw [hmdef, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
      have harith : 2 * m - 1 = (m - 1) + m := by omega
      rw [htwo, harith]
    }
  · {
      rw [if_neg hpos] at hk hk1
      rw [hk, hk1, if_neg hpos]
      set t := 2 ^ k * (n.natAbs - 1) with htdef
      have htwo : 2 ^ (k + 1) * (n.natAbs - 1) = 2 * t := by
        rw [htdef, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
      have harith : 2 * t + 1 = (t + 1) + t := by omega
      rw [htwo, harith]
    }

/-- Every residue-`2` seed other than `-1` is unbounded. -/
theorem ResidueTwoUnbounded (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (h : n % 3 = 2) (hne : n ≠ -1) (N : ℕ) :
    ∃ k : ℕ, N < (Iterate (RawStep p) k n).natAbs := by
  refine ⟨N + 1, ?_⟩
  have hstep : ∀ i : ℕ,
      (Iterate (RawStep p) i n).natAbs <
        (Iterate (RawStep p) (i + 1) n).natAbs :=
    ResidueTwoIncreases p hQ hC hD n h hne
  have hgrow : ∀ k : ℕ, k ≤ (Iterate (RawStep p) k n).natAbs := by
    intro k
    induction k with
    | zero => {
        exact Nat.zero_le _
      }
    | succ k ih => {
        exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (hstep k))
      }
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (hgrow (N + 1))

/-- After any residue-`2` state, the later absolute values are exact. -/
theorem ResidueTwoTailAbs (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (j k : ℕ)
    (h : Iterate (RawStep p) j n % (3 : ℤ) = 2) :
    (Iterate (RawStep p) (j + k) n).natAbs =
      if 0 ≤ Iterate (RawStep p) j n then
        2 ^ k * ((Iterate (RawStep p) j n).natAbs + 1) - 1
      else
        2 ^ k * ((Iterate (RawStep p) j n).natAbs - 1) + 1 := by
  rw [IterateAdd (RawStep p) j k n]
  exact ResidueTwoAbs p hQ hC hD (Iterate (RawStep p) j n) h k

/-- A seed of absolute value at most four meets a terminal or residue two quickly. -/
theorem SmallFateByAbs (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (habs : n.natAbs ≤ 4) :
    ∃ j : ℕ, j ≤ n.natAbs ∧
      (Iterate (RawStep p) j n = 0 ∨ Iterate (RawStep p) j n = 1 ∨
        Iterate (RawStep p) j n = -1 ∨
          Iterate (RawStep p) j n % (3 : ℤ) = 2) := by
  have hlist : n = -4 ∨ n = -3 ∨ n = -2 ∨ n = -1 ∨ n = 0 ∨
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases hlist with hn | hn | hn | hn | hn | hn | hn | hn | hn
  · {
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [hn]
      exact Or.inr (Or.inr (Or.inr (by decide : (-4 : ℤ) % 3 = 2)))
    }
  · {
      have hd : p.D ∣ (-3 : ℤ) := by
        rw [hD]
        exact ⟨-1, by omega⟩
      have hdiv : (-3 : ℤ) / 3 = -1 := by
        have hnum : (-3 : ℤ) = (3 : ℤ) * -1 := by omega
        rw [hnum]
        exact QuotientCancelThree (-1)
      have hstep : RawStep p (-3) = -1 := by
        rw [RawStep, if_pos hd, hD, hdiv]
      refine ⟨1, ?_, ?_⟩
      · {
          rw [hn]
          omega
        }
      · {
          have hiter : Iterate (RawStep p) 1 n = -1 := by
            rw [hn]
            simpa [Iterate] using hstep
          exact Or.inr (Or.inr (Or.inl hiter))
        }
    }
  · {
      have hnd : ¬ p.D ∣ (-2 : ℤ) := by
        rw [hD]
        intro hd
        have hzero : (-2 : ℤ) % 3 = 0 :=
          (Int.dvd_iff_emod_eq_zero).mp hd
        have hone : (-2 : ℤ) % 3 = 1 := by decide
        omega
      have hfirst : RawStep p (-2) = -3 := by
        rw [RawStep, if_neg hnd, hQ, hC]
        omega
      have hd : p.D ∣ (-3 : ℤ) := by
        rw [hD]
        exact ⟨-1, by omega⟩
      have hdiv : (-3 : ℤ) / 3 = -1 := by
        have hnum : (-3 : ℤ) = (3 : ℤ) * -1 := by omega
        rw [hnum]
        exact QuotientCancelThree (-1)
      have hsecond : RawStep p (-3) = -1 := by
        rw [RawStep, if_pos hd, hD, hdiv]
      refine ⟨2, ?_, ?_⟩
      · {
          rw [hn]
          omega
        }
      · {
          have hiter : Iterate (RawStep p) 2 n = -1 := by
            rw [hn]
            have h1 : Iterate (RawStep p) 1 (-2 : ℤ) = -3 := by
              simpa [Iterate] using hfirst
            have h2 : Iterate (RawStep p) 2 (-2 : ℤ) =
                RawStep p (Iterate (RawStep p) 1 (-2 : ℤ)) := by
              simp [Iterate]
            rw [h2, h1, hsecond]
          exact Or.inr (Or.inr (Or.inl hiter))
        }
    }
  · {
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [hn]
      exact Or.inr (Or.inr (Or.inl rfl))
    }
  · {
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [hn]
      exact Or.inl rfl
    }
  · {
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [hn]
      exact Or.inr (Or.inl rfl)
    }
  · {
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [hn]
      exact Or.inr (Or.inr (Or.inr (by decide : (2 : ℤ) % 3 = 2)))
    }
  · {
      refine ⟨1, ?_, ?_⟩
      · {
          rw [hn]
          omega
        }
      · {
          have hiter : Iterate (RawStep p) 1 n = 1 := by
            rw [hn]
            simpa [Iterate] using RawStepThree p hD
          exact Or.inr (Or.inl hiter)
        }
    }
  · {
      refine ⟨3, ?_, ?_⟩
      · {
          rw [hn]
          omega
        }
      · {
          have h1 : Iterate (RawStep p) 1 (4 : ℤ) = 9 := by
            simpa [Iterate] using RawStepFour p hQ hC hD
          have h2 : Iterate (RawStep p) 2 (4 : ℤ) = 3 := by
            have hstep : Iterate (RawStep p) 2 (4 : ℤ) =
                RawStep p (Iterate (RawStep p) 1 (4 : ℤ)) := by
              simp [Iterate]
            rw [hstep, h1, RawStepNine p hD]
          have h3 : Iterate (RawStep p) 3 (4 : ℤ) = 1 := by
            have hstep : Iterate (RawStep p) 3 (4 : ℤ) =
                RawStep p (Iterate (RawStep p) 2 (4 : ℤ)) := by
              simp [Iterate]
            rw [hstep, h2, RawStepThree p hD]
          have hiter : Iterate (RawStep p) 3 n = 1 := by
            rw [hn]
            exact h3
          exact Or.inr (Or.inl hiter)
        }
    }

/-- Every seed meets `0`, `1`, `-1`, or residue `2` by time `|n|`. -/
theorem FateByAbs (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    ∃ j : ℕ, j ≤ n.natAbs ∧
      (Iterate (RawStep p) j n = 0 ∨ Iterate (RawStep p) j n = 1 ∨
        Iterate (RawStep p) j n = -1 ∨
          Iterate (RawStep p) j n % (3 : ℤ) = 2) := by
  have main : ∀ k : ℕ, ∀ n : ℤ, n.natAbs ≤ k →
      ∃ j : ℕ, j ≤ n.natAbs ∧
        (Iterate (RawStep p) j n = 0 ∨ Iterate (RawStep p) j n = 1 ∨
          Iterate (RawStep p) j n = -1 ∨
            Iterate (RawStep p) j n % (3 : ℤ) = 2) := by
    intro k
    induction k with
    | zero => {
        intro n hk
        have hz : n = 0 :=
          Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
        refine ⟨0, Nat.zero_le _, ?_⟩
        rw [hz]
        exact Or.inl rfl
      }
    | succ k ih => {
        intro n hk
        by_cases hsmall : n.natAbs ≤ k
        · {
            exact ih n hsmall
          }
        · {
            have heq : n.natAbs = k + 1 := by omega
            by_cases hfive : 5 ≤ n.natAbs
            · {
                rcases ResidueTrichotomy p hQ hC hD n with
                  hzero | hone | htwo
                · {
                    rcases hzero with ⟨hmod, _hhit, hret⟩
                    have hnz : n ≠ 0 := by
                      intro hz
                      rw [hz] at heq
                      omega
                    have hdvd : (3 : ℤ) ∣ n :=
                      (Int.dvd_iff_emod_eq_zero).mpr hmod
                    have hlt := QuotientAbsSmaller n hdvd hnz
                    have hle : (n / 3).natAbs ≤ k := by omega
                    obtain ⟨j, hj, htail⟩ := ih (n / 3) hle
                    refine ⟨1 + j, ?_, ?_⟩
                    · {
                        have hquot : (n / 3).natAbs ≤ n.natAbs - 1 := by
                          omega
                        omega
                      }
                    · {
                        have hstep : Iterate (RawStep p) 1 n = n / 3 := hret
                        have hshift : Iterate (RawStep p) (1 + j) n =
                            Iterate (RawStep p) j (n / 3) := by
                          rw [IterateAdd (RawStep p) 1 j n, hstep]
                        rw [hshift]
                        exact htail
                      }
                  }
                · {
                    rcases hone with ⟨hmod, _hhit, _haff, hret⟩
                    have hk2 : 2 ≤ n.natAbs := by omega
                    have hfac := FourThreeOne n hmod hk2
                    have hdrop : ((2 * n + 1) / 3).natAbs + 2 ≤
                        n.natAbs := by
                      by_contra hbad
                      have hge : n.natAbs - 1 ≤
                          ((2 * n + 1) / 3).natAbs := by omega
                      have hmul : 4 * (n.natAbs - 1) ≤ 3 * n.natAbs :=
                        Nat.le_trans (Nat.mul_le_mul_left 4 hge) hfac
                      omega
                    have hle : ((2 * n + 1) / 3).natAbs ≤ k := by omega
                    obtain ⟨j, hj, htail⟩ := ih ((2 * n + 1) / 3) hle
                    refine ⟨2 + j, ?_, ?_⟩
                    · {
                        omega
                      }
                    · {
                        have htwo : Iterate (RawStep p) 2 n =
                            (2 * n + 1) / 3 := hret
                        have hshift : Iterate (RawStep p) (2 + j) n =
                            Iterate (RawStep p) j ((2 * n + 1) / 3) := by
                          rw [IterateAdd (RawStep p) 2 j n, htwo]
                        rw [hshift]
                        exact htail
                      }
                  }
                · {
                    rcases htwo with ⟨hmod, _⟩
                    refine ⟨0, Nat.zero_le _, ?_⟩
                    exact Or.inr (Or.inr (Or.inr hmod))
                  }
              }
            · {
                have hfour : n.natAbs ≤ 4 := by omega
                exact SmallFateByAbs p hQ hC hD n hfour
              }
          }
      }
  exact main n.natAbs n (Nat.le_refl _)

/-- By time `|n|`, the orbit has met `0`, `1`, or `-1`, or has become unbounded. -/
theorem FateSplit (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    (∃ j : ℕ, j ≤ n.natAbs ∧ Iterate (RawStep p) j n = 0) ∨
      (∃ j : ℕ, j ≤ n.natAbs ∧ Iterate (RawStep p) j n = 1) ∨
        (∃ j : ℕ, j ≤ n.natAbs ∧ Iterate (RawStep p) j n = -1) ∨
          (∃ j : ℕ, j ≤ n.natAbs ∧
            Iterate (RawStep p) j n % (3 : ℤ) = 2 ∧
              Iterate (RawStep p) j n ≠ -1 ∧
                ∀ N : ℕ, ∃ k : ℕ,
                  N < (Iterate (RawStep p) k n).natAbs) := by
  obtain ⟨j, hj, h⟩ := FateByAbs p hQ hC hD n
  rcases h with h0 | h1 | hm1 | hres
  · {
      exact Or.inl ⟨j, hj, h0⟩
    }
  · {
      exact Or.inr (Or.inl ⟨j, hj, h1⟩)
    }
  · {
      exact Or.inr (Or.inr (Or.inl ⟨j, hj, hm1⟩))
    }
  · {
      by_cases hneg : Iterate (RawStep p) j n = -1
      · {
          exact Or.inr (Or.inr (Or.inl ⟨j, hj, hneg⟩))
        }
      · {
          refine Or.inr (Or.inr (Or.inr ⟨j, hj, hres, hneg, ?_⟩))
          intro N
          obtain ⟨k, hk⟩ :=
            ResidueTwoUnbounded p hQ hC hD
              (Iterate (RawStep p) j n) hres hneg N
          refine ⟨j + k, ?_⟩
          rw [IterateAdd (RawStep p) j k n]
          exact hk
        }
    }

/-- Largest absolute value on the first `j + 1` states. -/
def PrefixAbsMax (p : Parameters) (n : ℤ) : ℕ → ℕ
  | 0 => (Iterate (RawStep p) 0 n).natAbs
  | j + 1 =>
      max (PrefixAbsMax p n j) (Iterate (RawStep p) (j + 1) n).natAbs

/-- Every state through time `j` is bounded by the prefix maximum. -/
theorem PrefixAbsBound (p : Parameters) (n : ℤ) (j i : ℕ) (hi : i ≤ j) :
    (Iterate (RawStep p) i n).natAbs ≤ PrefixAbsMax p n j := by
  induction j with
  | zero => {
      have hiz : i = 0 := by omega
      rw [hiz]
      rfl
    }
  | succ j ih => {
      by_cases hle : i ≤ j
      · {
          exact Nat.le_trans (ih hle) (Nat.le_max_left _ _)
        }
      · {
          have heq : i = j + 1 := by omega
          rw [heq]
          exact Nat.le_max_right _ _
        }
    }

/-- After a visit to `1`, every later absolute value is at most `3`. -/
theorem TailAbsAfterOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (k t : ℕ) (hk : Iterate (RawStep p) k n = 1) (ht : k ≤ t) :
    (Iterate (RawStep p) t n).natAbs ≤ 3 := by
  rcases Nat.even_or_odd (t - k) with ⟨m, hm⟩ | ⟨m, hm⟩
  · {
      have hidx : t = k + 2 * m := by omega
      have htail := (AfterOne p hQ hC hD n k m hk).1
      rw [← hidx] at htail
      rw [htail]
      omega
    }
  · {
      have hidx : t = k + 2 * m + 1 := by omega
      have htail := (AfterOne p hQ hC hD n k m hk).2
      rw [← hidx] at htail
      rw [htail]
      omega
    }

/-- A visit to `1` makes every absolute value bounded. -/
theorem BoundedIfMeetsOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (k : ℕ) (hk : Iterate (RawStep p) k n = 1) :
    ∃ B : ℕ, ∀ t : ℕ, (Iterate (RawStep p) t n).natAbs ≤ B := by
  refine ⟨max (PrefixAbsMax p n k) 3, ?_⟩
  intro t
  by_cases ht : t ≤ k
  · {
      exact Nat.le_trans (PrefixAbsBound p n k t ht) (Nat.le_max_left _ _)
    }
  · {
      have hge : k ≤ t := by omega
      exact Nat.le_trans
        (TailAbsAfterOne p hQ hC hD n k t hk hge) (Nat.le_max_right _ _)
    }

/-- A visit to `-1` makes every absolute value bounded. -/
theorem BoundedIfMeetsNegOne (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (k : ℕ) (hk : Iterate (RawStep p) k n = -1) :
    ∃ B : ℕ, ∀ t : ℕ, (Iterate (RawStep p) t n).natAbs ≤ B := by
  refine ⟨max (PrefixAbsMax p n k) 1, ?_⟩
  intro t
  by_cases ht : t ≤ k
  · {
      exact Nat.le_trans (PrefixAbsBound p n k t ht) (Nat.le_max_left _ _)
    }
  · {
      have hge : k ≤ t := by omega
      have hidx : t = k + (t - k) := by omega
      have htail := AfterNegOne p hQ hC hD n k (t - k) hk
      rw [← hidx] at htail
      rw [htail]
      exact Nat.le_max_right _ _
    }

/-- A visit to `0` makes the orbit identically zero. -/
theorem BoundedIfMeetsZero (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (k : ℕ) (hk : Iterate (RawStep p) k n = 0) :
    ∀ t : ℕ, Iterate (RawStep p) t n = 0 := by
  have hn := MeetsZeroIffZero p hQ hC hD n k hk
  intro t
  rw [hn]
  exact IterateFixed p (0 : ℤ) (RawStepZero p hD) t

/-- The four alternatives of the time bound are pairwise exclusive. -/
theorem FateExclusive (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    ¬ ((∃ j, Iterate (RawStep p) j n = 0) ∧
        (∃ j, Iterate (RawStep p) j n = 1)) ∧
      ¬ ((∃ j, Iterate (RawStep p) j n = 0) ∧
          (∃ j, Iterate (RawStep p) j n = -1)) ∧
        ¬ ((∃ j, Iterate (RawStep p) j n = 1) ∧
            (∃ j, Iterate (RawStep p) j n = -1)) ∧
          ¬ ((∃ j, Iterate (RawStep p) j n = 0) ∧
              ∀ N : ℕ, ∃ k, N < (Iterate (RawStep p) k n).natAbs) ∧
            ¬ ((∃ j, Iterate (RawStep p) j n = 1) ∧
                ∀ N : ℕ, ∃ k, N < (Iterate (RawStep p) k n).natAbs) ∧
              ¬ ((∃ j, Iterate (RawStep p) j n = -1) ∧
                  ∀ N : ℕ, ∃ k,
                    N < (Iterate (RawStep p) k n).natAbs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · {
      intro h
      obtain ⟨j0, h0⟩ := h.1
      obtain ⟨j1, h1⟩ := h.2
      exact ZeroMissesOne p hQ hC hD n j0 j1 h0 h1
    }
  · {
      intro h
      obtain ⟨j0, h0⟩ := h.1
      obtain ⟨j1, h1⟩ := h.2
      exact ZeroMissesNegOne p hQ hC hD n j0 j1 h0 h1
    }
  · {
      intro h
      obtain ⟨j1, h1⟩ := h.1
      obtain ⟨j2, h2⟩ := h.2
      exact TerminalDisjoint p hQ hC hD n j1 j2 h1 h2
    }
  · {
      intro h
      obtain ⟨j0, h0⟩ := h.1
      have hstay := BoundedIfMeetsZero p hQ hC hD n j0 h0
      obtain ⟨k, hk⟩ := h.2 0
      rw [hstay k] at hk
      omega
    }
  · {
      intro h
      obtain ⟨j1, h1⟩ := h.1
      obtain ⟨B, hB⟩ := BoundedIfMeetsOne p hQ hC hD n j1 h1
      obtain ⟨k, hk⟩ := h.2 B
      exact Nat.lt_irrefl B (Nat.lt_of_lt_of_le hk (hB k))
    }
  · {
      intro h
      obtain ⟨j1, h1⟩ := h.1
      obtain ⟨B, hB⟩ := BoundedIfMeetsNegOne p hQ hC hD n j1 h1
      obtain ⟨k, hk⟩ := h.2 B
      exact Nat.lt_irrefl B (Nat.lt_of_lt_of_le hk (hB k))
    }

/-- Every seed has exactly one of the four fates, with the terminal hit by time `|n|`. -/
theorem FatePartition (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    ((∃ j : ℕ, j ≤ n.natAbs ∧ Iterate (RawStep p) j n = 0) ∧
        (¬ ∃ j : ℕ, Iterate (RawStep p) j n = 1) ∧
        (¬ ∃ j : ℕ, Iterate (RawStep p) j n = -1) ∧
        (¬ ∀ N : ℕ, ∃ k : ℕ,
          N < (Iterate (RawStep p) k n).natAbs)) ∨
      ((∃ j : ℕ, j ≤ n.natAbs ∧ Iterate (RawStep p) j n = 1) ∧
        (¬ ∃ j : ℕ, Iterate (RawStep p) j n = 0) ∧
        (¬ ∃ j : ℕ, Iterate (RawStep p) j n = -1) ∧
        (¬ ∀ N : ℕ, ∃ k : ℕ,
          N < (Iterate (RawStep p) k n).natAbs)) ∨
        ((∃ j : ℕ, j ≤ n.natAbs ∧ Iterate (RawStep p) j n = -1) ∧
          (¬ ∃ j : ℕ, Iterate (RawStep p) j n = 0) ∧
          (¬ ∃ j : ℕ, Iterate (RawStep p) j n = 1) ∧
          (¬ ∀ N : ℕ, ∃ k : ℕ,
            N < (Iterate (RawStep p) k n).natAbs)) ∨
          ((∃ j : ℕ, j ≤ n.natAbs ∧
              Iterate (RawStep p) j n % (3 : ℤ) = 2 ∧
                Iterate (RawStep p) j n ≠ -1) ∧
            (∀ N : ℕ, ∃ k : ℕ,
              N < (Iterate (RawStep p) k n).natAbs) ∧
            (¬ ∃ j : ℕ, Iterate (RawStep p) j n = 0) ∧
            (¬ ∃ j : ℕ, Iterate (RawStep p) j n = 1) ∧
            (¬ ∃ j : ℕ, Iterate (RawStep p) j n = -1)) := by
  have hex := FateExclusive p hQ hC hD n
  rcases FateSplit p hQ hC hD n with h0 | h1 | hm | hu
  · {
      refine Or.inl ⟨h0, ?_, ?_, ?_⟩
      · {
          intro h
          exact hex.1 ⟨⟨h0.choose, h0.choose_spec.2⟩, h⟩
        }
      · {
          intro h
          exact hex.2.1 ⟨⟨h0.choose, h0.choose_spec.2⟩, h⟩
        }
      · {
          intro h
          exact hex.2.2.2.1 ⟨⟨h0.choose, h0.choose_spec.2⟩, h⟩
        }
    }
  · {
      refine Or.inr (Or.inl ⟨h1, ?_, ?_, ?_⟩)
      · {
          intro h
          exact hex.1 ⟨h, ⟨h1.choose, h1.choose_spec.2⟩⟩
        }
      · {
          intro h
          exact hex.2.2.1 ⟨⟨h1.choose, h1.choose_spec.2⟩, h⟩
        }
      · {
          intro h
          exact hex.2.2.2.2.1 ⟨⟨h1.choose, h1.choose_spec.2⟩, h⟩
        }
    }
  · {
      refine Or.inr (Or.inr (Or.inl ⟨hm, ?_, ?_, ?_⟩))
      · {
          intro h
          exact hex.2.1 ⟨h, ⟨hm.choose, hm.choose_spec.2⟩⟩
        }
      · {
          intro h
          exact hex.2.2.1 ⟨h, ⟨hm.choose, hm.choose_spec.2⟩⟩
        }
      · {
          intro h
          exact hex.2.2.2.2.2 ⟨⟨hm.choose, hm.choose_spec.2⟩, h⟩
        }
    }
  · {
      obtain ⟨j, hj, hres, hneg, hunb⟩ := hu
      refine Or.inr (Or.inr (Or.inr ⟨⟨j, hj, hres, hneg⟩, hunb, ?_, ?_, ?_⟩))
      · {
          intro h
          exact hex.2.2.2.1 ⟨h, hunb⟩
        }
      · {
          intro h
          exact hex.2.2.2.2.1 ⟨h, hunb⟩
        }
      · {
          intro h
          exact hex.2.2.2.2.2 ⟨h, hunb⟩
        }
    }

/-- The orbit is eventually periodic when a positive shift fixes the whole tail. -/
def OrbitEventuallyPeriodic (p : Parameters) (n : ℤ) : Prop :=
  ∃ s q : ℕ, 0 < q ∧ ∀ m : ℕ,
    Iterate (RawStep p) (s + q + m) n =
      Iterate (RawStep p) (s + m) n

/-- A periodic tail repeats on every residue of the period. -/
theorem PeriodicReduce (p : Parameters) (n : ℤ) (s q m : ℕ)
    (hq : 0 < q)
    (hper : ∀ m : ℕ,
      Iterate (RawStep p) (s + q + m) n =
        Iterate (RawStep p) (s + m) n) :
    Iterate (RawStep p) (s + m) n =
      Iterate (RawStep p) (s + m % q) n := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hlt : m < q
    · {
        rw [Nat.mod_eq_of_lt hlt]
      }
    · {
        have hge : q ≤ m := by omega
        have hsmall : m - q < m := by omega
        have hidx : s + m = s + q + (m - q) := by omega
        rw [hidx, hper (m - q), ih (m - q) hsmall]
        have hmod : (m - q) % q = m % q :=
          (Nat.mod_eq_sub_mod hge).symm
        rw [hmod]
      }

/-- An eventually periodic orbit is bounded. -/
theorem PeriodicBounded (p : Parameters) (n : ℤ)
    (hper : OrbitEventuallyPeriodic p n) :
    ∃ B : ℕ, ∀ t : ℕ, (Iterate (RawStep p) t n).natAbs ≤ B := by
  obtain ⟨s, q, hq, hshift⟩ := hper
  refine ⟨PrefixAbsMax p n (s + q), ?_⟩
  intro t
  by_cases ht : t ≤ s + q
  · {
      exact PrefixAbsBound p n (s + q) t ht
    }
  · {
      have hge : s ≤ t := by omega
      have hred := PeriodicReduce p n s q (t - s) hq hshift
      have hidx : s + (t - s) = t := by omega
      rw [hidx] at hred
      have hlt : (t - s) % q < q := Nat.mod_lt _ hq
      have hle : s + (t - s) % q ≤ s + q := by omega
      rw [hred]
      exact PrefixAbsBound p n (s + q) _ hle
    }

/-- The orbit is eventually periodic exactly when it meets `0`, `1`, or `-1`. -/
theorem PeriodicIffTerminal (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    OrbitEventuallyPeriodic p n ↔
      (∃ j : ℕ, Iterate (RawStep p) j n = 0) ∨
        (∃ j : ℕ, Iterate (RawStep p) j n = 1) ∨
          (∃ j : ℕ, Iterate (RawStep p) j n = -1) := by
  constructor
  · {
      intro hper
      obtain ⟨B, hB⟩ := PeriodicBounded p n hper
      have hunb : ¬ ∀ N : ℕ, ∃ k : ℕ,
          N < (Iterate (RawStep p) k n).natAbs := by
        intro hall
        obtain ⟨k, hk⟩ := hall B
        exact Nat.lt_irrefl B (Nat.lt_of_lt_of_le hk (hB k))
      rcases FatePartition p hQ hC hD n with h0 | h1 | hm | hu
      · {
          exact Or.inl ⟨h0.1.choose, h0.1.choose_spec.2⟩
        }
      · {
          exact Or.inr (Or.inl ⟨h1.1.choose, h1.1.choose_spec.2⟩)
        }
      · {
          exact Or.inr (Or.inr ⟨hm.1.choose, hm.1.choose_spec.2⟩)
        }
      · {
          exact False.elim (hunb hu.2.1)
        }
    }
  · {
      intro h
      rcases h with ⟨j, h0⟩ | ⟨j, h1⟩ | ⟨j, hm⟩
      · {
          refine ⟨0, 1, Nat.one_pos, ?_⟩
          intro m
          have hstay := BoundedIfMeetsZero p hQ hC hD n j h0
          rw [hstay (0 + 1 + m), hstay (0 + m)]
        }
      · {
          refine ⟨j, 2, by omega, ?_⟩
          intro m
          rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
          · {
              have hleft : j + 2 + m = j + 2 * (r + 1) := by omega
              have hright : j + m = j + 2 * r := by omega
              rw [hleft, hright]
              rw [(AfterOne p hQ hC hD n j (r + 1) h1).1]
              rw [(AfterOne p hQ hC hD n j r h1).1]
            }
          · {
              have hleft : j + 2 + m = j + 2 * (r + 1) + 1 := by omega
              have hright : j + m = j + 2 * r + 1 := by omega
              rw [hleft, hright]
              rw [(AfterOne p hQ hC hD n j (r + 1) h1).2]
              rw [(AfterOne p hQ hC hD n j r h1).2]
            }
        }
      · {
          refine ⟨j, 1, Nat.one_pos, ?_⟩
          intro m
          have hleft := AfterNegOne p hQ hC hD n j (1 + m) hm
          have hright := AfterNegOne p hQ hC hD n j m hm
          have hidx : j + 1 + m = j + (1 + m) := by omega
          rw [hidx, hleft, hright]
        }
    }

/-- The eventual tail is identically zero, identically `-1`, or the cycle `1, 3`. -/
theorem TerminalTail (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    (∀ t : ℕ, Iterate (RawStep p) t n = 0) ∨
      (∃ j : ℕ, j ≤ n.natAbs ∧ ∀ m : ℕ,
        Iterate (RawStep p) (j + m) n = -1) ∨
        (∃ j : ℕ, j ≤ n.natAbs ∧ ∀ m : ℕ,
          Iterate (RawStep p) (j + 2 * m) n = 1 ∧
            Iterate (RawStep p) (j + 2 * m + 1) n = 3) ∨
          (∀ N : ℕ, ∃ k : ℕ,
            N < (Iterate (RawStep p) k n).natAbs) := by
  rcases FatePartition p hQ hC hD n with h0 | h1 | hm | hu
  · {
      obtain ⟨j, _hj, hhit⟩ := h0.1
      exact Or.inl (BoundedIfMeetsZero p hQ hC hD n j hhit)
    }
  · {
      obtain ⟨j, hj, hhit⟩ := h1.1
      refine Or.inr (Or.inr (Or.inl ⟨j, hj, ?_⟩))
      intro m
      exact AfterOne p hQ hC hD n j m hhit
    }
  · {
      obtain ⟨j, hj, hhit⟩ := hm.1
      refine Or.inr (Or.inl ⟨j, hj, ?_⟩)
      intro m
      exact AfterNegOne p hQ hC hD n j m hhit
    }
  · {
      exact Or.inr (Or.inr (Or.inr hu.2.1))
    }

/-- The first visit to `\{1,3\}` is `1` at time zero or `3` immediately before the first `1`. -/
theorem CycleEntry (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (hhit : ∃ j : ℕ, Iterate (RawStep p) j n = 1) :
    (Iterate (RawStep p) 0 n = 1 ∧ ∀ m : ℕ,
        Iterate (RawStep p) (2 * m) n = 1 ∧
          Iterate (RawStep p) (2 * m + 1) n = 3) ∨
      ∃ k : ℕ, 0 < k ∧ Iterate (RawStep p) (k - 1) n = 3 ∧
        (∀ i : ℕ, i < k - 1 →
          Iterate (RawStep p) i n ≠ 1 ∧ Iterate (RawStep p) i n ≠ 3) ∧
        ∀ m : ℕ,
          Iterate (RawStep p) (k - 1 + 2 * m) n = 3 ∧
            Iterate (RawStep p) (k - 1 + 2 * m + 1) n = 1 := by
  let k := Nat.find hhit
  have hk : Iterate (RawStep p) k n = 1 := Nat.find_spec hhit
  have hmin : ∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ 1 :=
    fun i hi => Nat.find_min hhit hi
  by_cases hk0 : k = 0
  · {
      refine Or.inl ⟨?_, ?_⟩
      · {
          rw [← hk0]
          exact hk
        }
      · {
          intro m
          have htail := AfterOne p hQ hC hD n 0 m (by simpa [hk0] using hk)
          have hleft : 0 + 2 * m = 2 * m := by omega
          rw [hleft] at htail
          exact htail
        }
    }
  · {
      have hpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hpred := BeforeOne p hQ hC hD n k hpos hk
      refine Or.inr ⟨k, hpos, hpred, ?_, ?_⟩
      · {
          intro i hi
          refine ⟨hmin i (Nat.lt_of_lt_of_le hi (Nat.sub_le k 1)), ?_⟩
          intro hthree
          have hnext : Iterate (RawStep p) (i + 1) n = 1 := by
            have hstep : Iterate (RawStep p) (i + 1) n =
                RawStep p (Iterate (RawStep p) i n) := by
              simp [Iterate]
            rw [hstep, hthree, RawStepThree p hD]
          have hlt : i + 1 < k := by omega
          exact hmin (i + 1) hlt hnext
        }
      · {
          intro m
          cases m with
          | zero => {
              have hidx : k - 1 + 1 = k := by omega
              constructor
              · {
                  exact hpred
                }
              · {
                  rw [hidx]
                  exact hk
                }
            }
          | succ r => {
              have hleft : k - 1 + 2 * (r + 1) = k + 2 * r + 1 := by omega
              have hright : k - 1 + 2 * (r + 1) + 1 = k + 2 * (r + 1) := by
                omega
              constructor
              · {
                  rw [hleft]
                  exact (AfterOne p hQ hC hD n k r hk).2
                }
              · {
                  rw [hright]
                  exact (AfterOne p hQ hC hD n k (r + 1) hk).1
                }
            }
        }
    }

/-- The first visit to `\{1,3\}` occurs by time `|n|`. -/
theorem CycleEntryBound (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (hhit : ∃ j : ℕ, Iterate (RawStep p) j n = 1) :
    ∃ j : ℕ, j ≤ n.natAbs ∧
      (Iterate (RawStep p) j n = 1 ∨ Iterate (RawStep p) j n = 3) ∧
      ∀ i : ℕ, i < j →
        Iterate (RawStep p) i n ≠ 1 ∧ Iterate (RawStep p) i n ≠ 3 := by
  have hex := FateExclusive p hQ hC hD n
  have hkle : Nat.find hhit ≤ n.natAbs := by
    obtain ⟨t, ht, htail⟩ := FateByAbs p hQ hC hD n
    rcases htail with hz | ho | hm | hr
    · {
        exact False.elim (hex.1 ⟨⟨t, hz⟩, hhit⟩)
      }
    · {
        exact Nat.le_trans (Nat.find_le ho) ht
      }
    · {
        exact False.elim (hex.2.2.1 ⟨hhit, ⟨t, hm⟩⟩)
      }
    · {
        by_cases hneg : Iterate (RawStep p) t n = -1
        · {
            exact False.elim (hex.2.2.1 ⟨hhit, ⟨t, hneg⟩⟩)
          }
        · {
            have hunb : ∀ N : ℕ, ∃ r : ℕ,
                N < (Iterate (RawStep p) r n).natAbs := by
              intro N
              obtain ⟨r, hrN⟩ := ResidueTwoUnbounded p hQ hC hD
                (Iterate (RawStep p) t n) hr hneg N
              refine ⟨t + r, ?_⟩
              rw [← IterateAdd (RawStep p) t r n] at hrN
              exact hrN
            exact False.elim (hex.2.2.2.2.1 ⟨hhit, hunb⟩)
          }
      }
  rcases CycleEntry p hQ hC hD n hhit with hseed | hpred
  · {
      refine ⟨0, Nat.zero_le _, Or.inl hseed.1, ?_⟩
      intro i hi
      omega
    }
  · {
      obtain ⟨k, hpos, hthree, hearly, htail⟩ := hpred
      have hk1 : Iterate (RawStep p) k n = 1 := by
        have hidx : k - 1 + 2 * 0 + 1 = k := by omega
        rw [← hidx]
        exact (htail 0).2
      have hleast : ∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ 1 := by
        intro i hi
        by_cases hlt : i < k - 1
        · {
            exact (hearly i hlt).1
          }
        · {
            have heqi : i = k - 1 := by omega
            rw [heqi, hthree]
            omega
          }
      have heq : k = Nat.find hhit :=
        ((Nat.find_eq_iff hhit).2 ⟨hk1, hleast⟩).symm
      refine ⟨k - 1, ?_, Or.inr hthree, hearly⟩
      rw [heq]
      omega
    }

/-- The first visit to `-1` occurs by time `|n|`, and the tail stays there. -/
theorem NegOneEntryBound (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (hhit : ∃ j : ℕ, Iterate (RawStep p) j n = -1) :
    ∃ j : ℕ, j ≤ n.natAbs ∧ Iterate (RawStep p) j n = -1 ∧
      (∀ i : ℕ, i < j → Iterate (RawStep p) i n ≠ -1) ∧
      ∀ m : ℕ, Iterate (RawStep p) (j + m) n = -1 := by
  let k := Nat.find hhit
  have hk : Iterate (RawStep p) k n = -1 := Nat.find_spec hhit
  have hmin : ∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ -1 :=
    fun i hi => Nat.find_min hhit hi
  have hex := FateExclusive p hQ hC hD n
  have hkle : k ≤ n.natAbs := by
    obtain ⟨t, ht, htail⟩ := FateByAbs p hQ hC hD n
    rcases htail with hz | ho | hm | hr
    · {
        exact False.elim (hex.2.1 ⟨⟨t, hz⟩, hhit⟩)
      }
    · {
        exact False.elim (hex.2.2.1 ⟨⟨t, ho⟩, hhit⟩)
      }
    · {
        exact Nat.le_trans (Nat.find_le hm) ht
      }
    · {
        by_cases hneg : Iterate (RawStep p) t n = -1
        · {
            exact Nat.le_trans (Nat.find_le hneg) ht
          }
        · {
            have hunb : ∀ N : ℕ, ∃ r : ℕ,
                N < (Iterate (RawStep p) r n).natAbs := by
              intro N
              obtain ⟨r, hrN⟩ := ResidueTwoUnbounded p hQ hC hD
                (Iterate (RawStep p) t n) hr hneg N
              refine ⟨t + r, ?_⟩
              rw [← IterateAdd (RawStep p) t r n] at hrN
              exact hrN
            exact False.elim (hex.2.2.2.2.2 ⟨hhit, hunb⟩)
          }
      }
  refine ⟨k, hkle, hk, hmin, ?_⟩
  intro m
  exact AfterNegOne p hQ hC hD n k m hk

/-- The orbit is the zero seed, a first visit to `-1`, a first visit to `\{1,3\}`, or unbounded. -/
theorem EntryClassification (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    n = 0 ∨
      (∃ j : ℕ, j ≤ n.natAbs ∧ Iterate (RawStep p) j n = -1 ∧
        (∀ i : ℕ, i < j → Iterate (RawStep p) i n ≠ -1) ∧
        ∀ m : ℕ, Iterate (RawStep p) (j + m) n = -1) ∨
        (∃ j : ℕ, j ≤ n.natAbs ∧
          (Iterate (RawStep p) j n = 1 ∨ Iterate (RawStep p) j n = 3) ∧
          (∀ i : ℕ, i < j →
            Iterate (RawStep p) i n ≠ 1 ∧
              Iterate (RawStep p) i n ≠ 3) ∧
          ∀ m : ℕ,
            (Iterate (RawStep p) j n = 1 →
              Iterate (RawStep p) (2 * m) n = 1 ∧
                Iterate (RawStep p) (2 * m + 1) n = 3) ∧
            (Iterate (RawStep p) j n = 3 →
              Iterate (RawStep p) (j + 2 * m) n = 3 ∧
                Iterate (RawStep p) (j + 2 * m + 1) n = 1)) ∨
          (∀ N : ℕ, ∃ k : ℕ,
            N < (Iterate (RawStep p) k n).natAbs) := by
  rcases FatePartition p hQ hC hD n with h0 | h1 | hm | hu
  · {
      obtain ⟨j, _hj, hhit⟩ := h0.1
      exact Or.inl (MeetsZeroIffZero p hQ hC hD n j hhit)
    }
  · {
      have hhit : ∃ j : ℕ, Iterate (RawStep p) j n = 1 :=
        ⟨h1.1.choose, h1.1.choose_spec.2⟩
      refine Or.inr (Or.inr (Or.inl ?_))
      rcases CycleEntry p hQ hC hD n hhit with hseed | hpred
      · {
          refine ⟨0, Nat.zero_le _, Or.inl hseed.1, ?_, ?_⟩
          · {
              intro i hi
              omega
            }
          · {
              intro m
              constructor
              · {
                  intro _
                  exact hseed.2 m
                }
              · {
                  intro hthree
                  have hneq : (1 : ℤ) = 3 := by
                    rw [← hseed.1]
                    exact hthree
                  omega
                }
            }
        }
      · {
          obtain ⟨k, hpos, hthree, hearly, htail⟩ := hpred
          obtain ⟨j, hj, hstate, hbefore⟩ :=
            CycleEntryBound p hQ hC hD n hhit
          have hjle : j ≤ k - 1 := by
            by_contra hbad
            have hlt : k - 1 < j := by omega
            exact (hbefore (k - 1) hlt).2 hthree
          have hkle : k - 1 ≤ j := by
            by_contra hbad
            have hlt : j < k - 1 := by omega
            rcases hstate with hs1 | hs3
            · {
                exact (hearly j hlt).1 hs1
              }
            · {
                exact (hearly j hlt).2 hs3
              }
          have heq : j = k - 1 := by omega
          refine ⟨k - 1, ?_, Or.inr hthree, hearly, ?_⟩
          · {
              rw [← heq]
              exact hj
            }
          · {
              intro m
              constructor
              · {
                  intro hone
                  have hneq : (3 : ℤ) = 1 := by
                    rw [← hthree]
                    exact hone
                  omega
                }
              · {
                  intro _
                  exact htail m
                }
            }
        }
    }
  · {
      have hhit : ∃ j : ℕ, Iterate (RawStep p) j n = -1 :=
        ⟨hm.1.choose, hm.1.choose_spec.2⟩
      obtain ⟨j, hj, hstate, hmin, htail⟩ :=
        NegOneEntryBound p hQ hC hD n hhit
      exact Or.inr (Or.inl ⟨j, hj, hstate, hmin, htail⟩)
    }
  · {
      exact Or.inr (Or.inr (Or.inr hu.2.1))
    }

/-- An unbounded orbit grows by at least `2 ^ k + 1` after its residue-two state. -/
theorem UnboundedLower (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (hunb : ∀ N : ℕ, ∃ k : ℕ,
      N < (Iterate (RawStep p) k n).natAbs) :
    ∃ j : ℕ, j ≤ n.natAbs ∧ ∀ k : ℕ,
      2 ^ k + 1 ≤ (Iterate (RawStep p) (j + k) n).natAbs := by
  rcases FatePartition p hQ hC hD n with h0 | h1 | hm | hu
  · {
      exact False.elim (h0.2.2.2 hunb)
    }
  · {
      exact False.elim (h1.2.2.2 hunb)
    }
  · {
      exact False.elim (hm.2.2.2 hunb)
    }
  · {
      obtain ⟨j, hj, hres, hneg⟩ := hu.1
      refine ⟨j, hj, ?_⟩
      intro k
      let r := Iterate (RawStep p) j n
      have habs := ResidueTwoAbs p hQ hC hD r hres k
      have hge : 2 ≤ r.natAbs := by
        by_contra hbad
        have hsmall : r.natAbs ≤ 1 := by omega
        have hlist : r = -1 ∨ r = 0 ∨ r = 1 := by omega
        rcases hlist with hr | hr | hr
        · {
            exact hneg hr
          }
        · {
            have hzero : r % (3 : ℤ) = 0 := by
              rw [hr]
              decide
            omega
          }
        · {
            have hone : r % (3 : ℤ) = 1 := by
              rw [hr]
              decide
            omega
          }
      have hidx : Iterate (RawStep p) (j + k) n =
          Iterate (RawStep p) k r := by
        rw [IterateAdd (RawStep p) j k n]
      rw [hidx]
      by_cases hpos : 0 ≤ r
      · {
          rw [habs, if_pos hpos]
          have hthree : 3 ≤ r.natAbs + 1 := by omega
          have hmul : 2 ^ k * 3 ≤ 2 ^ k * (r.natAbs + 1) :=
            Nat.mul_le_mul_left (2 ^ k) hthree
          have hone : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
          have hbase : 2 ^ k + 1 ≤ 2 ^ k * 3 - 1 := by omega
          exact le_trans hbase (Nat.sub_le_sub_right hmul 1)
        }
      · {
          rw [habs, if_neg hpos]
          have hone : 1 ≤ r.natAbs - 1 := by omega
          have hmul : 2 ^ k * 1 ≤ 2 ^ k * (r.natAbs - 1) :=
            Nat.mul_le_mul_left (2 ^ k) hone
          have hleft : 2 ^ k + 1 ≤ 2 ^ k * 1 + 1 := by omega
          exact le_trans hleft (Nat.add_le_add_right hmul 1)
        }
    }

/-- Every natural number is below one more than its power of two. -/
theorem TwoPowAbove (N : ℕ) : N < 2 ^ N + 1 := by
  induction N with
  | zero => {
      decide
    }
  | succ N ih => {
      rw [Nat.pow_succ]
      have hone : 1 ≤ 2 ^ N := Nat.one_le_pow N 2 (by decide)
      have hstep : N + 1 ≤ 2 ^ N + 1 := Nat.succ_le_of_lt ih
      have hdouble : 2 ^ N + 1 < 2 ^ N * 2 + 1 := by omega
      exact lt_of_le_of_lt hstep hdouble
    }

/-- The absolute value exceeds `N` by time `|n| + N`. -/
theorem EscapeTime (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (hunb : ∀ N : ℕ, ∃ k : ℕ,
      N < (Iterate (RawStep p) k n).natAbs) (N : ℕ) :
    ∃ t : ℕ, t ≤ n.natAbs + N ∧
      N < (Iterate (RawStep p) t n).natAbs := by
  obtain ⟨j, hj, hgrow⟩ := UnboundedLower p hQ hC hD n hunb
  refine ⟨j + N, ?_, ?_⟩
  · {
      omega
    }
  · {
      have hgrowN : 2 ^ N + 1 ≤
          (Iterate (RawStep p) (j + N) n).natAbs := hgrow N
      exact lt_of_lt_of_le (TwoPowAbove N) hgrowN
    }

/-- The absolute value exceeds `N` by time `|n| + log2 N + 1`. -/
theorem EscapeTimeLog (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (hunb : ∀ N : ℕ, ∃ k : ℕ,
      N < (Iterate (RawStep p) k n).natAbs) (N : ℕ) :
    ∃ t : ℕ, t ≤ n.natAbs + Nat.log 2 N + 1 ∧
      N < (Iterate (RawStep p) t n).natAbs := by
  obtain ⟨j, hj, hgrow⟩ := UnboundedLower p hQ hC hD n hunb
  refine ⟨j + (Nat.log 2 N + 1), ?_, ?_⟩
  · {
      omega
    }
  · {
      have hgrowk : 2 ^ (Nat.log 2 N + 1) + 1 ≤
          (Iterate (RawStep p) (j + (Nat.log 2 N + 1)) n).natAbs :=
        hgrow (Nat.log 2 N + 1)
      have hlt : N < 2 ^ (Nat.log 2 N + 1) + 1 := by
        by_cases hN : N = 0
        · {
            simp [hN]
          }
        · {
            have hpos : 0 < N := Nat.pos_of_ne_zero hN
            have hpow : N < 2 ^ (Nat.log 2 N + 1) :=
              Nat.lt_pow_succ_log_self (b := 2) (by decide) N
            omega
          }
      exact lt_of_lt_of_le hlt hgrowk
    }

/-- The orbit of `2` has absolute value `3 * 2 ^ k - 1`. -/
theorem TwoOrbitAbs (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (k : ℕ) :
    (Iterate (RawStep p) k (2 : ℤ)).natAbs = 3 * 2 ^ k - 1 := by
  have hres : (2 : ℤ) % 3 = 2 := by decide
  have habs := ResidueTwoAbs p hQ hC hD (2 : ℤ) hres k
  have hpos : 0 ≤ (2 : ℤ) := by decide
  rw [habs, if_pos hpos]
  have hthree : (2 : ℤ).natAbs + 1 = 3 := by decide
  rw [hthree, Nat.mul_comm]

/-- Past `N`, the orbit of `2` has already passed the exact threshold. -/
theorem TwoFirstEscape (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (N : ℕ) :
    ∃ k : ℕ, N < 3 * 2 ^ k - 1 ∧
      (Iterate (RawStep p) k (2 : ℤ)).natAbs = 3 * 2 ^ k - 1 ∧
      ∀ i : ℕ, i < k → (Iterate (RawStep p) i (2 : ℤ)).natAbs ≤ N := by
  have hex : ∃ k : ℕ, N < 3 * 2 ^ k - 1 := by
    refine ⟨N + 1, ?_⟩
    have hlt : N < 2 ^ (N + 1) := by
      have hbase := TwoPowAbove (N + 1)
      omega
    have hmul : 2 ^ (N + 1) ≤ 3 * 2 ^ (N + 1) - 1 := by
      have hone : 1 ≤ 2 ^ (N + 1) := Nat.one_le_pow (N + 1) 2 (by decide)
      omega
    omega
  let k := Nat.find hex
  refine ⟨k, Nat.find_spec hex, ?_, ?_⟩
  · {
      exact TwoOrbitAbs p hQ hC hD k
    }
  · {
      intro i hi
      have hle : 3 * 2 ^ i - 1 ≤ N := by
        by_contra hgt
        exact Nat.find_min hex hi (by omega)
      rw [TwoOrbitAbs p hQ hC hD i]
      exact hle
    }

/-- A residue-two seed other than `-1` passes `N` at the least exact time. -/
theorem ResidueTwoFirstEscape (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (hres : n % 3 = 2) (hneg : n ≠ -1) (N : ℕ) :
    ∃ k : ℕ,
      N < (Iterate (RawStep p) k n).natAbs ∧
      (Iterate (RawStep p) k n).natAbs =
        (if 0 ≤ n then 2 ^ k * (n.natAbs + 1) - 1
          else 2 ^ k * (n.natAbs - 1) + 1) ∧
      ∀ i : ℕ, i < k → (Iterate (RawStep p) i n).natAbs ≤ N := by
  have hge : 2 ≤ n.natAbs := by
    by_contra hbad
    have hsmall : n.natAbs ≤ 1 := by omega
    have hlist : n = -1 ∨ n = 0 ∨ n = 1 := by omega
    rcases hlist with hn | hn | hn
    · {
        exact hneg hn
      }
    · {
        have hzero : n % (3 : ℤ) = 0 := by
          rw [hn]
          decide
        omega
      }
    · {
        have hone : n % (3 : ℤ) = 1 := by
          rw [hn]
          decide
        omega
      }
  have hex : ∃ k : ℕ, N <
      (if 0 ≤ n then 2 ^ k * (n.natAbs + 1) - 1
        else 2 ^ k * (n.natAbs - 1) + 1) := by
    refine ⟨N + 1, ?_⟩
    have hbase : N < 2 ^ (N + 1) := by
      have habove := TwoPowAbove (N + 1)
      omega
    by_cases hpos : 0 ≤ n
    · {
        rw [if_pos hpos]
        have hmul : 2 ^ (N + 1) ≤
            2 ^ (N + 1) * (n.natAbs + 1) - 1 := by
          have hone : 1 ≤ 2 ^ (N + 1) :=
            Nat.one_le_pow (N + 1) 2 (by decide)
          have hthree : 2 ≤ n.natAbs + 1 := by omega
          have hprod : 2 ^ (N + 1) * 2 ≤
              2 ^ (N + 1) * (n.natAbs + 1) :=
            Nat.mul_le_mul_left _ hthree
          omega
        omega
      }
    · {
        rw [if_neg hpos]
        have hone : 1 ≤ n.natAbs - 1 := by omega
        have hmul : 2 ^ (N + 1) ≤
            2 ^ (N + 1) * (n.natAbs - 1) :=
          Nat.le_mul_of_pos_right _ (by omega : 0 < n.natAbs - 1)
        omega
      }
  let k := Nat.find hex
  have hspec := Nat.find_spec hex
  have habs := ResidueTwoAbs p hQ hC hD n hres k
  refine ⟨k, ?_, habs, ?_⟩
  · {
      rw [habs]
      exact hspec
    }
  · {
      intro i hi
      have hform := ResidueTwoAbs p hQ hC hD n hres i
      have hle : (if 0 ≤ n then 2 ^ i * (n.natAbs + 1) - 1
          else 2 ^ i * (n.natAbs - 1) + 1) ≤ N := by
        by_contra hgt
        exact Nat.find_min hex hi (by omega)
      rw [hform]
      exact hle
    }

/-- An unbounded orbit passes `N` at a least offset from its residue-two state. -/
theorem UnboundedFirstEscape (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (hunb : ∀ M : ℕ, ∃ t : ℕ,
      M < (Iterate (RawStep p) t n).natAbs) (N : ℕ) :
    ∃ j k : ℕ, j ≤ n.natAbs ∧
      let r := Iterate (RawStep p) j n
      r % 3 = 2 ∧ r ≠ -1 ∧
      N < (Iterate (RawStep p) (j + k) n).natAbs ∧
      (Iterate (RawStep p) (j + k) n).natAbs =
        (if 0 ≤ r then 2 ^ k * (r.natAbs + 1) - 1
          else 2 ^ k * (r.natAbs - 1) + 1) ∧
      ∀ i : ℕ, i < k →
        (Iterate (RawStep p) (j + i) n).natAbs ≤ N := by
  rcases FatePartition p hQ hC hD n with h0 | h1 | hm | hu
  · {
      exact False.elim (h0.2.2.2 hunb)
    }
  · {
      exact False.elim (h1.2.2.2 hunb)
    }
  · {
      exact False.elim (hm.2.2.2 hunb)
    }
  · {
      obtain ⟨j, hj, hres, hneg⟩ := hu.1
      let r := Iterate (RawStep p) j n
      obtain ⟨k, hgt, heq, hearly⟩ :=
        ResidueTwoFirstEscape p hQ hC hD r hres hneg N
      refine ⟨j, k, hj, hres, hneg, ?_, ?_, ?_⟩
      · {
          have hidx : Iterate (RawStep p) (j + k) n =
              Iterate (RawStep p) k r := by
            rw [IterateAdd (RawStep p) j k n]
          rw [hidx]
          exact hgt
        }
      · {
          have hidx : Iterate (RawStep p) (j + k) n =
              Iterate (RawStep p) k r := by
            rw [IterateAdd (RawStep p) j k n]
          rw [hidx]
          exact heq
        }
      · {
          intro i hi
          have hidx : Iterate (RawStep p) (j + i) n =
              Iterate (RawStep p) i r := by
            rw [IterateAdd (RawStep p) j i n]
          rw [hidx]
          exact hearly i hi
        }
    }

/-- An unbounded orbit is eventually larger than every bound. -/
theorem UnboundedEventuallyLarge (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (hunb : ∀ M : ℕ, ∃ t : ℕ,
      M < (Iterate (RawStep p) t n).natAbs) (N : ℕ) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      N < (Iterate (RawStep p) t n).natAbs := by
  obtain ⟨j, k, hj, hres, hneg, hgt, _, _⟩ :=
    UnboundedFirstEscape p hQ hC hD n hunb N
  refine ⟨j + k, ?_⟩
  intro t ht
  let r := Iterate (RawStep p) j n
  have hmono : ∀ m : ℕ,
      (Iterate (RawStep p) (j + k) n).natAbs ≤
        (Iterate (RawStep p) (j + k + m) n).natAbs := by
    intro m
    induction m with
    | zero => {
        rw [Nat.add_zero]
      }
    | succ m ih => {
        have hstep :=
          ResidueTwoIncreases p hQ hC hD r hres hneg (k + m)
        have hleft : Iterate (RawStep p) (k + m) r =
            Iterate (RawStep p) (j + k + m) n := by
          rw [show j + k + m = j + (k + m) by omega,
            IterateAdd (RawStep p) j (k + m) n]
        have hright : Iterate (RawStep p) (k + m + 1) r =
            Iterate (RawStep p) (j + k + (m + 1)) n := by
          rw [show j + k + (m + 1) = j + (k + m + 1) by omega,
            IterateAdd (RawStep p) j (k + m + 1) n]
        rw [hleft, hright] at hstep
        exact le_trans ih (Nat.le_of_lt hstep)
      }
  have hsplit : t = j + k + (t - (j + k)) := by omega
  have hle := hmono (t - (j + k))
  rw [← hsplit] at hle
  omega

/-- The absolute value is eventually larger than every bound. -/
def OrbitTendsToInfinity (p : Parameters) (n : ℤ) : Prop :=
  ∀ N : ℕ, ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
    N < (Iterate (RawStep p) t n).natAbs

/-- The orbit tends to infinity exactly when it misses `0`, `1`, and `-1`. -/
theorem TendsToInfinityIffNotTerminal (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    OrbitTendsToInfinity p n ↔
      (¬ ∃ j : ℕ, Iterate (RawStep p) j n = 0) ∧
      (¬ ∃ j : ℕ, Iterate (RawStep p) j n = 1) ∧
      (¬ ∃ j : ℕ, Iterate (RawStep p) j n = -1) := by
  constructor
  · {
      intro hinf
      refine ⟨?_, ?_, ?_⟩
      · {
          intro ⟨j, hj⟩
          have hper : OrbitEventuallyPeriodic p n :=
            (PeriodicIffTerminal p hQ hC hD n).mpr (Or.inl ⟨j, hj⟩)
          obtain ⟨B, hB⟩ := PeriodicBounded p n hper
          obtain ⟨T, hT⟩ := hinf B
          exact Nat.lt_irrefl B
            (Nat.lt_of_lt_of_le (hT T (Nat.le_refl T)) (hB T))
        }
      · {
          intro ⟨j, hj⟩
          have hper : OrbitEventuallyPeriodic p n :=
            (PeriodicIffTerminal p hQ hC hD n).mpr
              (Or.inr (Or.inl ⟨j, hj⟩))
          obtain ⟨B, hB⟩ := PeriodicBounded p n hper
          obtain ⟨T, hT⟩ := hinf B
          exact Nat.lt_irrefl B
            (Nat.lt_of_lt_of_le (hT T (Nat.le_refl T)) (hB T))
        }
      · {
          intro ⟨j, hj⟩
          have hper : OrbitEventuallyPeriodic p n :=
            (PeriodicIffTerminal p hQ hC hD n).mpr
              (Or.inr (Or.inr ⟨j, hj⟩))
          obtain ⟨B, hB⟩ := PeriodicBounded p n hper
          obtain ⟨T, hT⟩ := hinf B
          exact Nat.lt_irrefl B
            (Nat.lt_of_lt_of_le (hT T (Nat.le_refl T)) (hB T))
        }
    }
  · {
      intro hmiss N
      obtain ⟨h0, h1, hm⟩ := hmiss
      have hunb : ∀ M : ℕ, ∃ t : ℕ,
          M < (Iterate (RawStep p) t n).natAbs := by
        intro M
        rcases FatePartition p hQ hC hD n with hzero | hone | hneg | hu
        · {
            exact False.elim
              (h0 ⟨hzero.1.choose, hzero.1.choose_spec.2⟩)
          }
        · {
            exact False.elim
              (h1 ⟨hone.1.choose, hone.1.choose_spec.2⟩)
          }
        · {
            exact False.elim
              (hm ⟨hneg.1.choose, hneg.1.choose_spec.2⟩)
          }
        · {
            exact hu.2.1 M
          }
      exact UnboundedEventuallyLarge p hQ hC hD n hunb N
    }

/-- One affine step is at most twice the absolute value, plus one. -/
theorem AffineNatAbs (n : ℤ) :
    (2 * n + 1).natAbs ≤ 2 * n.natAbs + 1 := by
  cases n with
  | ofNat k => {
      have hpos : 0 ≤ (2 : ℤ) * k + 1 := by omega
      have habs : (((2 : ℤ) * k + 1).natAbs : ℤ) =
          (2 : ℤ) * k + 1 := Int.natAbs_of_nonneg hpos
      omega
    }
  | negSucc k => {
      have hn : Int.negSucc k = -((k + 1 : ℕ) : ℤ) := rfl
      rw [hn]
      have hleft : ((2 : ℤ) * -((k + 1 : ℕ) : ℤ) + 1).natAbs =
          2 * (k + 1) - 1 := by
        have hcalc : (2 : ℤ) * -((k + 1 : ℕ) : ℤ) + 1 =
            -((2 * (k + 1) - 1 : ℕ) : ℤ) := by omega
        rw [hcalc, Int.natAbs_neg, Int.natAbs_natCast]
      have hright : (-((k + 1 : ℕ) : ℤ)).natAbs = k + 1 := by
        rw [Int.natAbs_neg, Int.natAbs_natCast]
      rw [hleft, hright]
      omega
    }

/-- Every term of a minimal terminal chain is at most the seed. -/
theorem ChainTermsSmall (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hsm : s m = 1 ∨ s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ s m)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1)) :
    ∀ i : ℕ, i ≤ m → (s i).natAbs ≤ n.natAbs := by
  intro i hi
  induction i with
  | zero => {
      rw [hs0]
    }
  | succ t ih => {
      have hlt : t < m := Nat.lt_of_succ_le hi
      have hbig :=
        ProperTermsLarge p hQ hC hD n m s L hs0 hsm hsmin hL t hlt
      have hdrop :=
        ChainStepDescent p hQ hC hD (s t) (L t) (hL t hlt).1 hbig
      rw [(hL t hlt).2] at hdrop
      exact Nat.le_trans (Nat.le_of_lt hdrop)
        (ih (Nat.le_of_lt hlt))
    }

/-- Before the terminal time, every state lies in a block of length one or two. -/
theorem ChainPrefixAbs (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3)
    (n : ℤ) (m k : ℕ) (s : ℕ → ℤ) (L : ℕ → ℕ)
    (hs0 : s 0 = n)
    (hsm : s m = 1 ∨ s m = -1)
    (hsmin : ∀ i : ℕ, i < m → s i ≠ s m)
    (hL : ∀ i : ℕ, i < m →
      IsFirstHit p (s i) (L i) ∧
        RawStep p (Iterate (RawStep p) (L i) (s i)) = s (i + 1))
    (hsum : RawLengthSum L m = k) :
    ∀ t : ℕ, t < k →
      (Iterate (RawStep p) t n).natAbs ≤ 2 * n.natAbs + 1 := by
  intro t ht
  have hlt : t < RawLengthSum L m := by
    rw [hsum]
    exact ht
  obtain ⟨i, hi, hle, hhi⟩ := BlockIndex L m t hlt
  have hsmall :=
    ChainTermsSmall p hQ hC hD n m s L hs0 hsm hsmin hL
  have hstate : Iterate (RawStep p) t n =
      Iterate (RawStep p) (t - RawLengthSum L i) (s i) := by
    have hidx : RawLengthSum L i + (t - RawLengthSum L i) = t := by
      omega
    have hshift := BlockShift p n (s i) (RawLengthSum L i)
      (t - RawLengthSum L i)
      (ReturnChainIsOrbit p n m s L hs0 hL i (Nat.le_of_lt hi))
    rw [hidx] at hshift
    exact hshift
  have hL01 :=
    FirstHitIsZeroOrOne p hQ hC hD (s i) (L i) (hL i hi).1
  have hrle : t - RawLengthSum L i ≤ L i := by
    have hrec : RawLengthSum L (i + 1) =
        RawLengthSum L i + (L i + 1) := rfl
    omega
  have hsi : (s i).natAbs ≤ n.natAbs :=
    hsmall i (Nat.le_of_lt hi)
  rcases hL01 with hL0 | hL1
  · {
      have hr0 : t - RawLengthSum L i = 0 := by omega
      rw [hstate, hr0]
      have hzero : Iterate (RawStep p) 0 (s i) = s i := rfl
      rw [hzero]
      omega
    }
  · {
      by_cases hr0 : t - RawLengthSum L i = 0
      · {
          rw [hstate, hr0]
          have hzero : Iterate (RawStep p) 0 (s i) = s i := rfl
          rw [hzero]
          omega
        }
      · {
          have hr1 : t - RawLengthSum L i = 1 := by omega
          rw [hstate, hr1]
          have hstep1 : Iterate (RawStep p) 1 (s i) = RawStep p (s i) :=
            rfl
          have hnot : ¬ p.D ∣ s i := by
            have hearly := (hL i hi).1.2 0 (by omega)
            rw [AffineStateZero p.Q p.C (s i)] at hearly
            exact hearly
          have haff : RawStep p (s i) = 2 * s i + 1 := by
            rw [RawStep, if_neg hnot, hQ, hC]
          rw [hstep1, haff]
          exact le_trans (AffineNatAbs (s i)) (by omega)
        }
    }

/-- A terminal orbit stays at most `2|n| + 1`. -/
theorem TerminalAbsBound (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ)
    (hterm : (∃ j : ℕ, Iterate (RawStep p) j n = 0) ∨
      (∃ j : ℕ, Iterate (RawStep p) j n = 1) ∨
      (∃ j : ℕ, Iterate (RawStep p) j n = -1)) :
    ∀ t : ℕ, (Iterate (RawStep p) t n).natAbs ≤ 2 * n.natAbs + 1 := by
  classical
  have hparity : ∀ d : ℕ, ∃ m0 : ℕ, d = 2 * m0 ∨ d = 2 * m0 + 1 := by
    intro d
    induction d with
    | zero => {
        exact ⟨0, Or.inl rfl⟩
      }
    | succ d ih => {
        obtain ⟨m0, hm0⟩ := ih
        rcases hm0 with heq | heq
        · {
            exact ⟨m0, Or.inr (by omega)⟩
          }
        · {
            exact ⟨m0 + 1, Or.inl (by omega)⟩
          }
      }
  rcases hterm with h0 | h1 | hm
  · {
      obtain ⟨k, hk⟩ := h0
      intro t
      have hzero := BoundedIfMeetsZero p hQ hC hD n k hk t
      rw [hzero]
      omega
    }
  · {
      obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
        ReturnChainToOne p hQ hC hD n h1
      let k := Nat.find h1
      have hk : Iterate (RawStep p) k n = 1 := Nat.find_spec h1
      have hkmin : ∀ i : ℕ, i < k → Iterate (RawStep p) i n ≠ 1 :=
        fun i hi => Nat.find_min h1 hi
      let L : ℕ → ℕ := fun i =>
        if hi : i < m then Classical.choose (hstep i hi) else 0
      have hL : ∀ i : ℕ, i < m →
          IsFirstHit p (s i) (L i) ∧
            RawStep p (Iterate (RawStep p) (L i) (s i)) =
              s (i + 1) := by
        intro i hi
        have hdef : L i = Classical.choose (hstep i hi) := by
          unfold L
          rw [dif_pos hi]
        rw [hdef]
        exact Classical.choose_spec (hstep i hi)
      have hsmin' : ∀ i : ℕ, i < m → s i ≠ s m := by
        intro i hi
        rw [hsm]
        exact hsmin i hi
      have hsum := ReturnChainAddsToHit p hQ hC hD n m k s L
        hs0 hsm hsmin hL hk hkmin
      have hpos : 1 ≤ n.natAbs := by
        by_contra hbad
        have hn0 : n = 0 := by
          have hzero : n.natAbs = 0 := by omega
          exact Int.natAbs_eq_zero.mp hzero
        have hiter : Iterate (RawStep p) k n = 0 := by
          rw [hn0]
          exact IterateFixed p (0 : ℤ) (RawStepZero p hD) k
        rw [hiter] at hk
        omega
      intro t
      by_cases ht : t < k
      · {
          exact ChainPrefixAbs p hQ hC hD n m k s L hs0
            (Or.inl hsm) hsmin' hL hsum t ht
        }
      · {
          have hge : k ≤ t := Nat.le_of_not_lt ht
          obtain ⟨m0, hm0⟩ := hparity (t - k)
          rcases hm0 with heq | heq
          · {
              have ht0 : t = k + 2 * m0 := by omega
              have htail := (AfterOne p hQ hC hD n k m0 hk).1
              rw [ht0, htail]
              have hone : ((1 : ℤ).natAbs) = 1 := by decide
              rw [hone]
              omega
            }
          · {
              have ht1 : t = k + 2 * m0 + 1 := by omega
              have htail := (AfterOne p hQ hC hD n k m0 hk).2
              rw [ht1, htail]
              have hthree : ((3 : ℤ).natAbs) = 3 := by decide
              rw [hthree]
              omega
            }
        }
    }
  · {
      obtain ⟨m, s, hs0, hsm, hsmin, hstep⟩ :=
        ReturnChainToNegOne p hQ hC hD n hm
      let k := Nat.find hm
      have hk : Iterate (RawStep p) k n = -1 := Nat.find_spec hm
      have hkmin : ∀ i : ℕ, i < k →
          Iterate (RawStep p) i n ≠ -1 :=
        fun i hi => Nat.find_min hm hi
      let L : ℕ → ℕ := fun i =>
        if hi : i < m then Classical.choose (hstep i hi) else 0
      have hL : ∀ i : ℕ, i < m →
          IsFirstHit p (s i) (L i) ∧
            RawStep p (Iterate (RawStep p) (L i) (s i)) =
              s (i + 1) := by
        intro i hi
        have hdef : L i = Classical.choose (hstep i hi) := by
          unfold L
          rw [dif_pos hi]
        rw [hdef]
        exact Classical.choose_spec (hstep i hi)
      have hsmin' : ∀ i : ℕ, i < m → s i ≠ s m := by
        intro i hi
        rw [hsm]
        exact hsmin i hi
      have hsum := ReturnChainAddsToNegOne p hQ hC hD n m k s L
        hs0 hsm hsmin hL hk hkmin
      intro t
      by_cases ht : t < k
      · {
          exact ChainPrefixAbs p hQ hC hD n m k s L hs0
            (Or.inr hsm) hsmin' hL hsum t ht
        }
      · {
          have hge : k ≤ t := Nat.le_of_not_lt ht
          have ht0 : t = k + (t - k) := by omega
          have htail := AfterNegOne p hQ hC hD n k (t - k) hk
          rw [ht0, htail]
          have hone : ((-1 : ℤ).natAbs) = 1 := by decide
          rw [hone]
          omega
        }
    }

/-- The orbit of `1` attains the terminal bound. -/
theorem TerminalAbsSharp (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    (Iterate (RawStep p) 1 (1 : ℤ)).natAbs =
      2 * ((1 : ℤ).natAbs) + 1 := by
  have hstep : RawStep p 1 = 3 := by
    unfold RawStep
    rw [hQ, hC, hD]
    decide
  have hiter : Iterate (RawStep p) 1 (1 : ℤ) = RawStep p 1 := rfl
  rw [hiter, hstep]
  decide

/-- The coefficient `2` is not a uniform terminal bound. -/
theorem TerminalAbsNotTwo (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    ¬ (Iterate (RawStep p) 1 (1 : ℤ)).natAbs ≤
      2 * ((1 : ℤ).natAbs) := by
  rw [TerminalAbsSharp p hQ hC hD]
  decide

/-- An orbit is eventually large, or it stays at most `2|n| + 1`. -/
theorem OrbitMagnitudeDichotomy (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) (n : ℤ) :
    (∀ N : ℕ, ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      N < (Iterate (RawStep p) t n).natAbs) ∨
    (∀ t : ℕ, (Iterate (RawStep p) t n).natAbs ≤ 2 * n.natAbs + 1) := by
  classical
  by_cases h0 : ∃ j : ℕ, Iterate (RawStep p) j n = 0
  · {
      exact Or.inr (TerminalAbsBound p hQ hC hD n (Or.inl h0))
    }
  · {
      by_cases h1 : ∃ j : ℕ, Iterate (RawStep p) j n = 1
      · {
          exact Or.inr
            (TerminalAbsBound p hQ hC hD n (Or.inr (Or.inl h1)))
        }
      · {
          by_cases hm : ∃ j : ℕ, Iterate (RawStep p) j n = -1
          · {
              exact Or.inr (TerminalAbsBound p hQ hC hD n
                (Or.inr (Or.inr hm)))
            }
          · {
              left
              exact (TendsToInfinityIffNotTerminal p hQ hC hD n).2
                ⟨h0, h1, hm⟩
            }
        }
    }

end GeneralizedCollatz
