-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Tactic.Ring

/-!
# Closed form of the signed offset sum

For `q ≥ 2` the offset sum is the exact nonnegative quotient
`(q^j - 1) / (q - 1)`. For every integer with absolute value at least `2`,
the absolute value of the offset sum obeys the positive geometric bound with
factor `|q| - 1`. The factor `|q| - 1` is not `|q - 1|` when `q` is negative:
`TrapSum (-2) 2 = -1`, while `(|-2|^2 - 1) / (|-2| - 1) = 3`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The affine state of multiplier `q`, offset `c`, time `j` and seed `n`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- The affine state meets `D` at time `j` and at no earlier time. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n

/-- A nonnegative multiplier keeps every offset sum nonnegative. -/
theorem TrapSumNonnegOfNonneg (q : ℤ) (j : ℕ) (hq : 0 ≤ q) : 0 ≤ TrapSum q j := by
  induction j with
  | zero => {
      rw [show TrapSum q 0 = 0 from rfl]
    }
  | succ j ih => {
      rw [TrapSum]
      exact add_nonneg ih (Int.pow_nonneg hq)
    }

/-- Absolute value at least `2` keeps the geometric denominator away from zero. -/
theorem TrapSumDenomNonzero (q : ℤ) (hq : 2 ≤ q.natAbs) : q - 1 ≠ 0 := by
  intro h
  have hq1 : q = 1 := by omega
  have hnat : q.natAbs = 1 := by
    rw [hq1]
    decide
  omega

/-- For `|q| ≥ 2` the offset sum is the exact integer quotient `(q^j - 1)/(q - 1)`. -/
theorem TrapSumExactQuotient (q : ℤ) (j : ℕ) (hq : 2 ≤ q.natAbs) :
    TrapSum q j = (q ^ j - 1) / (q - 1) := by
  have hden : q - 1 ≠ 0 := TrapSumDenomNonzero q hq
  have hmul : (q - 1) * TrapSum q j = q ^ j - 1 := TrapSumMulSubOne q j
  exact (Int.ediv_eq_of_eq_mul_right hden hmul.symm).symm

/-- For `q ≥ 2` the offset sum equals `(q^j - 1)/(q - 1)`, exactly and nonnegatively. -/
theorem PositiveClosedForm (q : ℤ) (j : ℕ) (hq : 2 ≤ q) :
    (q - 1) * TrapSum q j = q ^ j - 1 ∧
      (q - 1) ∣ q ^ j - 1 ∧
      TrapSum q j = (q ^ j - 1) / (q - 1) ∧
      0 ≤ TrapSum q j := by
  have hmul : (q - 1) * TrapSum q j = q ^ j - 1 := TrapSumMulSubOne q j
  have hnn : 0 ≤ TrapSum q j := TrapSumNonnegOfNonneg q j (by omega)
  have hqabs : 2 ≤ q.natAbs := by
    have hcast : (q.natAbs : ℤ) = q := Int.natAbs_of_nonneg (by omega)
    have hz : (2 : ℤ) ≤ (q.natAbs : ℤ) := by
      rw [hcast]
      exact hq
    exact (Int.ofNat_le).mp hz
  have hquot : TrapSum q j = (q ^ j - 1) / (q - 1) :=
    TrapSumExactQuotient q j hqabs
  have hdvd : q - 1 ∣ q ^ j - 1 := ⟨TrapSum q j, hmul.symm⟩
  exact ⟨hmul, hdvd, hquot, hnn⟩

/-- For `q ≥ 2` the affine state uses the exact nonnegative offset quotient. -/
theorem AffineStatePositiveOffset (q c n : ℤ) (j : ℕ) (hq : 2 ≤ q) :
    AffineState q c j n = q ^ j * n + c * ((q ^ j - 1) / (q - 1)) := by
  unfold AffineState
  have hquot : TrapSum q j = (q ^ j - 1) / (q - 1) :=
    (PositiveClosedForm q j hq).2.2.1
  rw [hquot]

/-- The second offset sum at multiplier `-2` is `-1`, not the positive repunit `3`. -/
theorem TrapSumNegTwoAtTwo : TrapSum (-2) 2 = -1 := by
  have h0 : TrapSum (-2) 0 = 0 := rfl
  have h1 : TrapSum (-2) 1 = 1 := by
    rw [TrapSumRec, h0]
    omega
  rw [TrapSumRec, h1]
  omega

/-- The signed quotient at `q = -2` is exact: division by `-3`, not by `1`. -/
theorem TrapSumNegTwoQuotient (j : ℕ) :
    TrapSum (-2) j = (((-2) ^ j - 1) / (-3)) := by
  have h := TrapSumExactQuotient (-2) j (by decide)
  have hden : (-2 : ℤ) - 1 = -3 := by omega
  rw [hden] at h
  exact h

/-- At `q = -2` and time `2`, the absolute sum is not `(|q|^2 - 1)/(|q| - 1)`. -/
theorem NegTwoNotPositiveRepunit :
    (TrapSum (-2) 2).natAbs ≠
      ((-2).natAbs ^ 2 - 1) / ((-2).natAbs - 1) := by
  have hsum : (TrapSum (-2) 2).natAbs = 1 := by
    rw [TrapSumNegTwoAtTwo]
    decide
  have hr : (-2 : ℤ).natAbs = 2 := by decide
  rw [hsum, hr]
  decide

/-- An even absolute step `b = r a + 1` preserves the geometric bound. -/
theorem GeometricStepPlus (r a j : ℕ) (hr : 1 ≤ r)
    (hb : (r - 1) * a ≤ r ^ j - 1) :
    (r - 1) * (r * a + 1) ≤ r ^ (j + 1) - 1 := by
  have hleft : (r - 1) * (r * a + 1) =
      r * ((r - 1) * a) + (r - 1) := by
    calc
      (r - 1) * (r * a + 1)
          = (r - 1) * (r * a) + (r - 1) * 1 := by rw [Nat.mul_add]
      _ = (r - 1) * (r * a) + (r - 1) := by rw [Nat.mul_one]
      _ = (r - 1) * r * a + (r - 1) := by rw [← Nat.mul_assoc]
      _ = r * ((r - 1) * a) + (r - 1) := by
          rw [Nat.mul_comm (r - 1) r, Nat.mul_assoc]
  have hscale : r * ((r - 1) * a) ≤ r * (r ^ j - 1) :=
    Nat.mul_le_mul_left r hb
  have hdist : r * (r ^ j - 1) = r ^ (j + 1) - r := by
    rw [Nat.mul_sub_one, Nat.pow_succ']
  have hadd : r * ((r - 1) * a) + (r - 1) ≤
      (r ^ (j + 1) - r) + (r - 1) := by
    rw [← hdist]
    exact Nat.add_le_add_right hscale (r - 1)
  have hrle : r ≤ r ^ (j + 1) := by
    have hpow : 1 ≤ r ^ j := Nat.one_le_pow j r hr
    have hmul : r * 1 ≤ r * r ^ j := Nat.mul_le_mul_left r hpow
    rw [Nat.mul_one] at hmul
    have hid : r * r ^ j = r ^ (j + 1) := by
      rw [Nat.mul_comm, ← Nat.pow_succ]
    rw [← hid]
    exact hmul
  have hcancel : r ^ (j + 1) - r + (r - 1) = r ^ (j + 1) - 1 := by
    have hmove := Nat.add_sub_assoc hr (r ^ (j + 1) - r)
    rw [← hmove, Nat.sub_add_cancel hrle]
  calc
    (r - 1) * (r * a + 1)
        = r * ((r - 1) * a) + (r - 1) := hleft
    _ ≤ (r ^ (j + 1) - r) + (r - 1) := hadd
    _ = r ^ (j + 1) - 1 := hcancel

/-- An odd absolute step `b = r a - 1` preserves the geometric bound. -/
theorem GeometricStepMinus (r a j : ℕ) (hr : 2 ≤ r)
    (hb : (r - 1) * a ≤ r ^ j - 1) :
    (r - 1) * (r * a - 1) ≤ r ^ (j + 1) - 1 := by
  have hr0 : 1 ≤ r := Nat.le_trans (by decide : 1 ≤ 2) hr
  have hleft : (r - 1) * (r * a - 1) =
      r * ((r - 1) * a) - (r - 1) := by
    calc
      (r - 1) * (r * a - 1)
          = (r - 1) * (r * a) - (r - 1) := by rw [Nat.mul_sub, Nat.mul_one]
      _ = (r - 1) * r * a - (r - 1) := by rw [← Nat.mul_assoc]
      _ = r * ((r - 1) * a) - (r - 1) := by
          rw [Nat.mul_comm (r - 1) r, Nat.mul_assoc]
  have hscale : r * ((r - 1) * a) ≤ r * (r ^ j - 1) :=
    Nat.mul_le_mul_left r hb
  have hdist : r * (r ^ j - 1) = r ^ (j + 1) - r := by
    rw [Nat.mul_sub_one, Nat.pow_succ']
  have hsub : r * ((r - 1) * a) - (r - 1) ≤
      (r ^ (j + 1) - r) - (r - 1) := by
    rw [← hdist]
    exact Nat.sub_le_sub_right hscale (r - 1)
  have hident : (r ^ (j + 1) - r) - (r - 1) ≤ r ^ (j + 1) - 1 := by
    have hsum : r + (r - 1) = 2 * r - 1 := by
      have hassoc : r + r - 1 = r + (r - 1) := Nat.add_sub_assoc hr0 r
      rw [← hassoc, ← Nat.two_mul]
    have htwo : 1 ≤ 2 * r - 1 := by
      have hle : 1 ≤ r + (r - 1) :=
        Nat.le_trans hr0 (Nat.le_add_right r (r - 1))
      rw [hsum] at hle
      exact hle
    have hcollapse : (r ^ (j + 1) - r) - (r - 1) =
        r ^ (j + 1) - (2 * r - 1) := by
      rw [Nat.sub_sub, hsum]
    rw [hcollapse]
    exact Nat.sub_le_sub_left htwo (r ^ (j + 1))
  calc
    (r - 1) * (r * a - 1)
        = r * ((r - 1) * a) - (r - 1) := hleft
    _ ≤ (r ^ (j + 1) - r) - (r - 1) := hsub
    _ ≤ r ^ (j + 1) - 1 := hident

/-- A multiplier at most `-1` is nonpositive at even times and positive at odd times. -/
theorem TrapSumModTwoSign (q : ℤ) (j : ℕ) (hq : q ≤ -1) :
    (j % 2 = 0 → TrapSum q j ≤ 0) ∧ (j % 2 = 1 → 0 < TrapSum q j) := by
  induction j with
  | zero => {
      refine ⟨?_, ?_⟩
      · intro _
        rw [show TrapSum q 0 = 0 from rfl]
      · intro hodd
        have hzero : (0 : ℕ) % 2 = 0 := Nat.zero_mod 2
        omega
    }
  | succ j ih => {
      have hrec : TrapSum q (j + 1) = q * TrapSum q j + 1 := TrapSumRec q j
      have hflip0 : j % 2 = 0 → (j + 1) % 2 = 1 := by
        intro h0
        omega
      have hflip1 : j % 2 = 1 → (j + 1) % 2 = 0 := by
        intro h1
        omega
      refine ⟨?_, ?_⟩
      · intro heven
        have hj : j % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one j with h0 | h1
          · {
              have := hflip0 h0
              omega
            }
          · {
              exact h1
            }
        have hpos : 0 < TrapSum q j := ih.2 hj
        have hT : (1 : ℤ) ≤ TrapSum q j := by omega
        have hmul : q * TrapSum q j ≤ - TrapSum q j := by
          have hnn : (0 : ℤ) ≤ TrapSum q j :=
            Int.le_trans (by decide : (0 : ℤ) ≤ 1) hT
          have hcmp := Int.mul_le_mul_of_nonneg_right hq hnn
          have hrew : (-1) * TrapSum q j = - TrapSum q j := by ring
          rw [hrew] at hcmp
          exact hcmp
        have hle : q * TrapSum q j + 1 ≤ 0 := by
          have h1 : q * TrapSum q j + 1 ≤ - TrapSum q j + 1 :=
            Int.add_le_add_right hmul 1
          have h2 : - TrapSum q j + 1 ≤ 0 := by omega
          exact Int.le_trans h1 h2
        rw [hrec]
        exact hle
      · intro hodd
        have hj : j % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one j with h0 | h1
          · {
              exact h0
            }
          · {
              have := hflip1 h1
              omega
            }
        have hnonpos : TrapSum q j ≤ 0 := ih.1 hj
        have hq0 : q ≤ 0 :=
          Int.le_trans hq (by decide : (-1 : ℤ) ≤ 0)
        have hprod : 0 ≤ q * TrapSum q j :=
          Int.mul_nonneg_of_nonpos_of_nonpos hq0 hnonpos
        rw [hrec]
        omega
    }

/-- From an even time, the next absolute offset is `r` times the old one, plus one. -/
theorem TrapSumAbsSuccEven (q : ℤ) (j : ℕ) (hq : q ≤ -1) (hmod : j % 2 = 0) :
    (TrapSum q (j + 1)).natAbs = q.natAbs * (TrapSum q j).natAbs + 1 := by
  have hnonpos : TrapSum q j ≤ 0 := (TrapSumModTwoSign q j hq).1 hmod
  have hqneg : q ≤ 0 := by omega
  have hnegq : q = - (q.natAbs : ℤ) := Int.eq_neg_natAbs_of_nonpos hqneg
  have hT : TrapSum q j = - ((TrapSum q j).natAbs : ℤ) :=
    Int.eq_neg_natAbs_of_nonpos hnonpos
  have hval : TrapSum q (j + 1) =
      ((q.natAbs * (TrapSum q j).natAbs + 1 : ℕ) : ℤ) := by
    generalize ha : (TrapSum q j).natAbs = a
    generalize hr : q.natAbs = r
    rw [ha] at hT
    rw [hr] at hnegq
    rw [TrapSumRec, hT, hnegq]
    have hring : (- (r : ℤ)) * (- (a : ℤ)) + 1 =
        (r : ℤ) * (a : ℤ) + 1 := by
      ring
    rw [hring, ← Int.natCast_mul, ← Int.natCast_one, ← Int.natCast_add]
  rw [hval, Int.natAbs_natCast]

/-- From an odd time, the next absolute offset is `r` times the old one, minus one. -/
theorem TrapSumAbsSuccOdd (q : ℤ) (j : ℕ) (hq : q ≤ -1) (hmod : j % 2 = 1) :
    (TrapSum q (j + 1)).natAbs = q.natAbs * (TrapSum q j).natAbs - 1 := by
  have hpos : 0 < TrapSum q j := (TrapSumModTwoSign q j hq).2 hmod
  have hT : ((TrapSum q j).natAbs : ℤ) = TrapSum q j :=
    Int.natAbs_of_nonneg (Int.le_of_lt hpos)
  have hqneg : q ≤ 0 := by omega
  have hnegq : q = - (q.natAbs : ℤ) := Int.eq_neg_natAbs_of_nonpos hqneg
  have ha1 : 1 ≤ (TrapSum q j).natAbs := by
    have h1 : (1 : ℤ) ≤ TrapSum q j := by omega
    have hineq : (1 : ℤ) ≤ ((TrapSum q j).natAbs : ℤ) := by
      rw [hT]
      exact h1
    exact (Int.ofNat_le).mp hineq
  have hr1 : 1 ≤ q.natAbs := by
    have habs : (q.natAbs : ℤ) = -q := Int.ofNat_natAbs_of_nonpos hqneg
    have h1 : (1 : ℤ) ≤ -q := by omega
    have h2 : (1 : ℤ) ≤ (q.natAbs : ℤ) := by
      rw [habs]
      exact h1
    exact (Int.ofNat_le).mp h2
  have hge : 1 ≤ q.natAbs * (TrapSum q j).natAbs := by
    have h11 : 1 * 1 ≤ q.natAbs * (TrapSum q j).natAbs :=
      Nat.mul_le_mul hr1 ha1
    rw [Nat.one_mul] at h11
    exact h11
  have hnegv : TrapSum q (j + 1) =
      - ((q.natAbs * (TrapSum q j).natAbs - 1 : ℕ) : ℤ) := by
    generalize ha : (TrapSum q j).natAbs = a
    generalize hrn : q.natAbs = r
    rw [ha] at hT
    rw [hrn] at hnegq
    have hge' : 1 ≤ r * a := by
      rw [← ha, ← hrn]
      exact hge
    have hsub : ((r * a - 1 : ℕ) : ℤ) = (r : ℤ) * (a : ℤ) - 1 := by
      rw [Int.ofNat_sub hge', Int.natCast_mul, Int.natCast_one]
    have hring : (- (r : ℤ)) * (a : ℤ) + 1 =
        - ((r : ℤ) * (a : ℤ) - 1) := by
      ring
    rw [TrapSumRec, ← hT, hnegq, hring, ← hsub]
  rw [hnegv, Int.natAbs_neg, Int.natAbs_natCast]

/-- For `q ≥ 2` the absolute geometric bound is equality with the positive repunit. -/
theorem GeometricAbsNonneg (q : ℤ) (j : ℕ) (hq : 2 ≤ q) :
    (q.natAbs - 1) * (TrapSum q j).natAbs = q.natAbs ^ j - 1 := by
  have hform := PositiveClosedForm q j hq
  have hmul : (q - 1) * TrapSum q j = q ^ j - 1 := hform.1
  have hnn : 0 ≤ TrapSum q j := hform.2.2.2
  have hq0 : 0 ≤ q := by omega
  have hqcast : (q.natAbs : ℤ) = q := Int.natAbs_of_nonneg hq0
  have hscast : ((TrapSum q j).natAbs : ℤ) = TrapSum q j :=
    Int.natAbs_of_nonneg hnn
  have hr1 : 1 ≤ q.natAbs := by
    have hz : (2 : ℤ) ≤ (q.natAbs : ℤ) := by
      rw [hqcast]
      exact hq
    have h2 : 2 ≤ q.natAbs := (Int.ofNat_le).mp hz
    omega
  have hpow1 : 1 ≤ q.natAbs ^ j := Nat.one_le_pow j q.natAbs (by omega)
  have hpowZ : ((q.natAbs ^ j : ℕ) : ℤ) = q ^ j := by
    rw [Int.natCast_pow, hqcast]
  have hdenZ : ((q.natAbs - 1 : ℕ) : ℤ) = q - 1 := by
    rw [Int.ofNat_sub hr1, hqcast, Int.natCast_one]
  have hnumZ : ((q.natAbs ^ j - 1 : ℕ) : ℤ) = q ^ j - 1 := by
    rw [Int.ofNat_sub hpow1, hpowZ, Int.natCast_one]
  have hmulZ : ((q.natAbs - 1 : ℕ) : ℤ) * ((TrapSum q j).natAbs : ℤ) =
      ((q.natAbs ^ j - 1 : ℕ) : ℤ) := by
    rw [hdenZ, hscast, hmul, hnumZ]
  apply Int.natCast_inj.mp
  rw [Int.natCast_mul]
  exact hmulZ

/-- For `q ≤ -2` the absolute bound follows from the alternating recurrence. -/
theorem GeometricAbsNeg (q : ℤ) (j : ℕ) (hq : 2 ≤ q.natAbs) (hqneg : q < 0) :
    (q.natAbs - 1) * (TrapSum q j).natAbs ≤ q.natAbs ^ j - 1 := by
  have hqle : q ≤ -1 := by
    have habs : (q.natAbs : ℤ) = -q :=
      Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hqneg)
    have hrZ : (2 : ℤ) ≤ (q.natAbs : ℤ) := (Int.ofNat_le).mpr hq
    have h2 : (2 : ℤ) ≤ -q := by
      rw [← habs]
      exact hrZ
    omega
  induction j with
  | zero => {
      rw [show TrapSum q 0 = 0 from rfl, Nat.pow_zero]
      simp
    }
  | succ j ih => {
      rcases Nat.mod_two_eq_zero_or_one j with h0 | h1
      · {
          have habs := TrapSumAbsSuccEven q j hqle h0
          rw [habs]
          exact GeometricStepPlus q.natAbs (TrapSum q j).natAbs j (by omega) ih
        }
      · {
          have habs := TrapSumAbsSuccOdd q j hqle h1
          rw [habs]
          exact GeometricStepMinus q.natAbs (TrapSum q j).natAbs j hq ih
        }
    }

/-- For `|q| ≥ 2`, `(|q| - 1)` times the absolute offset is at most `|q|^j - 1`. -/
theorem GeometricAbs (q : ℤ) (j : ℕ) (hq : 2 ≤ q.natAbs) :
    (q.natAbs - 1) * (TrapSum q j).natAbs ≤ q.natAbs ^ j - 1 := by
  by_cases hqneg : q < 0
  · {
      exact GeometricAbsNeg q j hq hqneg
    }
  · {
      have hqnn : 0 ≤ q := not_lt.mp hqneg
      have hq2 : (2 : ℤ) ≤ q := by
        have hcast : (q.natAbs : ℤ) = q := Int.natAbs_of_nonneg hqnn
        have hz : (2 : ℤ) ≤ (q.natAbs : ℤ) := (Int.ofNat_le).mpr hq
        rw [hcast] at hz
        exact hz
      exact le_of_eq (GeometricAbsNonneg q j hq2)
    }

end GeneralizedCollatz
