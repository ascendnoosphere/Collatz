-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# No uniform linear bound on one affine class

If `j` is a first hit and `|Q| ^ j ≥ |D|`, then no pair of natural numbers
`A < |D|` and `B` satisfies
`|D| * |(affine state)/D| ≤ A * |n| + B`
for every integer in the residue class of the seed. The proof moves the seed
by `t * |D|`, which stays in the class and keeps the first hit, and chooses
`t` so that the absolute value exceeds an explicit threshold built from `B`
and the offset sum. One large seed refutes the universal quantifier. A single
seed may still obey the inequality.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.SignedReturnObstruction

/-- Affine state after `j` undivided steps, with offset sum `TrapSum q j`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- `j` is the first time `p.D` divides the affine state of the seed `n`. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n

/-- Moving the seed by `t * d` adds exactly `q ^ j * t * d` at time `j`. -/
theorem AffineClassShift (q c n t d : ℤ) (j : ℕ) :
    AffineState q c j (n + t * d) =
      AffineState q c j n + q ^ j * t * d := by
  unfold AffineState
  ring

/-- At every time, the seed shift changes the affine state by a multiple of `d`. -/
theorem AffineDifferenceMultiple (q c n t d : ℤ) (j : ℕ) :
    d ∣ AffineState q c j (n + t * d) - AffineState q c j n := by
  have hdiff :
      AffineState q c j (n + t * d) - AffineState q c j n =
        q ^ j * t * d := by
    rw [AffineClassShift]
    ring
  rw [hdiff]
  refine ⟨q ^ j * t, ?_⟩
  ring

/-- Divisibility by `p.D` agrees at every time after a multiple seed shift. -/
theorem AffineDivisibilityShift (p : Parameters) (n t : ℤ) (i : ℕ) :
    p.D ∣ AffineState p.Q p.C i n ↔
      p.D ∣ AffineState p.Q p.C i (n + t * p.D) := by
  have hmul := AffineDifferenceMultiple p.Q p.C n t p.D i
  obtain ⟨k, hk⟩ := hmul
  constructor
  · {
      intro h
      obtain ⟨m, hm⟩ := h
      refine ⟨m + k, ?_⟩
      -- The shifted state is the original state plus a multiple of `p.D`.
      have hsum :
          AffineState p.Q p.C i (n + t * p.D) =
            AffineState p.Q p.C i n +
              (AffineState p.Q p.C i (n + t * p.D) -
                AffineState p.Q p.C i n) := by
        ring
      rw [hsum, hk, hm]
      ring
    }
  · {
      intro h
      obtain ⟨m, hm⟩ := h
      refine ⟨m - k, ?_⟩
      -- Subtracting the same multiple recovers the original state.
      have hsum :
          AffineState p.Q p.C i n =
            AffineState p.Q p.C i (n + t * p.D) -
              (AffineState p.Q p.C i (n + t * p.D) -
                AffineState p.Q p.C i n) := by
        ring
      rw [hsum, hk, hm]
      ring
    }

/-- A multiple of the divisor does not move the first affine divisibility time. -/
theorem FirstHitShift (p : Parameters) (n t : ℤ) (j : ℕ) :
    IsFirstHit p n j ↔ IsFirstHit p (n + t * p.D) j := by
  unfold IsFirstHit
  constructor
  · {
      intro h
      obtain ⟨hj, hearly⟩ := h
      refine ⟨(AffineDivisibilityShift p n t j).mp hj, ?_⟩
      -- Every earlier time differs by a multiple of `p.D`, so failure transports.
      intro i hi hdiv
      exact hearly i hi ((AffineDivisibilityShift p n t i).mpr hdiv)
    }
  · {
      intro h
      obtain ⟨hj, hearly⟩ := h
      refine ⟨(AffineDivisibilityShift p n t j).mpr hj, ?_⟩
      -- The same equivalence at each earlier time gives the opposite direction.
      intro i hi hdiv
      exact hearly i hi ((AffineDivisibilityShift p n t i).mp hdiv)
    }

/-- `|d|` equals `d` when `d` is nonnegative and equals `-d` otherwise. -/
theorem NatAbsEqSignMul (d : ℤ) :
    (d.natAbs : ℤ) = (if 0 ≤ d then (1 : ℤ) else -1) * d := by
  by_cases h : 0 ≤ d
  · {
      rw [if_pos h, Int.natAbs_of_nonneg h]
      exact (one_mul d).symm
    }
  · {
      have hlt : d < 0 := Int.not_le.mp h
      have hle : d ≤ 0 := le_of_lt hlt
      have hnn : 0 ≤ -d := neg_nonneg.mpr hle
      rw [if_neg h]
      have habs : (d.natAbs : ℤ) = -d := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg hnn
      rw [habs]
      exact (neg_one_mul d).symm
    }

/-- Adding a natural multiple of the modulus does not change the residue. -/
theorem ResidueNatAbsShift (n0 : ℤ) (m t : ℕ) :
    ((n0 + (t : ℤ) * (m : ℤ) : ℤ) : ZMod m) = (n0 : ZMod m) := by
  have hzero : ((m : ℤ) : ZMod m) = 0 := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_self m
  rw [Int.cast_add, Int.cast_mul, hzero, mul_zero, add_zero]

/-- A natural multiple of `|D|` is an integer multiple of `D` and keeps the hit. -/
theorem FirstHitNatAbsShift (p : Parameters) (n0 : ℤ) (j t : ℕ)
    (hhit : IsFirstHit p n0 j) :
    IsFirstHit p (n0 + (t : ℤ) * (p.D.natAbs : ℤ)) j := by
  -- `ε` absorbs the sign of `D`, so `t * |D|` equals `(ε * t) * D`.
  set ε : ℤ := if 0 ≤ p.D then (1 : ℤ) else -1 with hε
  have habs : (p.D.natAbs : ℤ) = ε * p.D := by
    rw [hε]
    exact NatAbsEqSignMul p.D
  have hs :
      (t : ℤ) * (p.D.natAbs : ℤ) = (ε * (t : ℤ)) * p.D := by
    calc
      (t : ℤ) * (p.D.natAbs : ℤ) = (t : ℤ) * (ε * p.D) := by rw [habs]
      _ = ((t : ℤ) * ε) * p.D := by rw [← mul_assoc]
      _ = (ε * (t : ℤ)) * p.D := by rw [mul_comm (t : ℤ) ε]
  have hseed :
      n0 + (t : ℤ) * (p.D.natAbs : ℤ) = n0 + (ε * (t : ℤ)) * p.D := by
    rw [hs]
  rw [hseed]
  exact (FirstHitShift p n0 (ε * (t : ℤ)) j).mp hhit

/-- For `m ≥ 1`, some `t` makes `|n0 + t * m|` at least the prescribed bound. -/
theorem ExistsNatAbsShiftGe (n0 : ℤ) (m bound : ℕ) (hm : 1 ≤ m) :
    ∃ t : ℕ, bound ≤ (n0 + (t : ℤ) * (m : ℤ)).natAbs := by
  refine ⟨n0.natAbs + bound, ?_⟩
  set t : ℕ := n0.natAbs + bound with ht
  have htcast : (t : ℤ) = (n0.natAbs : ℤ) + (bound : ℤ) := by
    rw [ht, Nat.cast_add]
  have hmul : (t : ℤ) ≤ (t : ℤ) * (m : ℤ) := by
    have hm1 : (1 : ℤ) ≤ (m : ℤ) := Nat.cast_le.mpr hm
    have hnonneg : (0 : ℤ) ≤ (t : ℤ) := Nat.cast_nonneg t
    have hgrow := Int.mul_le_mul_of_nonneg_left hm1 hnonneg
    rwa [mul_one] at hgrow
  have hprod : (t : ℤ) * (m : ℤ) = ((t * m : ℕ) : ℤ) := by
    exact (Nat.cast_mul t m).symm
  have hbase : (n0.natAbs : ℤ) + (bound : ℤ) ≤ ((t * m : ℕ) : ℤ) := by
    rw [← htcast, ← hprod]
    exact hmul
  have hsplit :
      (t : ℤ) * (m : ℤ) = (n0 + (t : ℤ) * (m : ℤ)) + (-n0) := by
    ring
  have htri :
      |(t : ℤ) * (m : ℤ)| ≤ |n0 + (t : ℤ) * (m : ℤ)| + |n0| := by
    nth_rw 1 [hsplit]
    have h := abs_add_le (n0 + (t : ℤ) * (m : ℤ)) (-n0)
    rw [abs_neg] at h
    exact h
  have hprodNonneg : (0 : ℤ) ≤ (t : ℤ) * (m : ℤ) :=
    mul_nonneg (Nat.cast_nonneg t) (Nat.cast_nonneg m)
  have habsProd : |(t : ℤ) * (m : ℤ)| = (t : ℤ) * (m : ℤ) :=
    abs_of_nonneg hprodNonneg
  -- Both absolute values below are the casts of the corresponding natural values.
  have hsum :
      ((t * m : ℕ) : ℤ) ≤
        ((n0 + (t : ℤ) * (m : ℤ)).natAbs : ℤ) + (n0.natAbs : ℤ) := by
    rw [← hprod]
    rw [Int.natCast_natAbs (n0 + (t : ℤ) * (m : ℤ))]
    rw [Int.natCast_natAbs n0]
    nth_rw 1 [← habsProd]
    exact htri
  have hcomm :
      (bound : ℤ) + (n0.natAbs : ℤ) ≤
        ((n0 + (t : ℤ) * (m : ℤ)).natAbs : ℤ) + (n0.natAbs : ℤ) := by
    have htrans := le_trans hbase hsum
    rwa [add_comm (n0.natAbs : ℤ) (bound : ℤ)] at htrans
  have hbound :
      (bound : ℤ) ≤ ((n0 + (t : ℤ) * (m : ℤ)).natAbs : ℤ) :=
    (add_le_add_iff_right (n0.natAbs : ℤ)).mp hcomm
  exact Nat.cast_le.mp hbound

/-- Exact division converts `|a|` into `|d| * |a / d|`. -/
theorem NatAbsQuotientMul (d a : ℤ) (h : d ∣ a) :
    d.natAbs * (a / d).natAbs = a.natAbs := by
  have hcancel : a / d * d = a := Int.ediv_mul_cancel h
  have hn := congrArg Int.natAbs hcancel
  rw [Int.natAbs_mul, Nat.mul_comm] at hn
  exact hn

/-- If the offset is no larger than the linear term, subtraction bounds the state. -/
theorem AffineNatAbsReverse (q c n : ℤ) (j : ℕ)
    (h : c.natAbs * (TrapSum q j).natAbs ≤ q.natAbs ^ j * n.natAbs) :
    q.natAbs ^ j * n.natAbs - c.natAbs * (TrapSum q j).natAbs ≤
      (AffineState q c j n).natAbs := by
  have hsplit :
      q ^ j * n = AffineState q c j n + -(c * TrapSum q j) := by
    unfold AffineState
    ring
  have htri :
      |q ^ j * n| ≤ |AffineState q c j n| + |c * TrapSum q j| := by
    rw [hsplit]
    have h := abs_add_le (AffineState q c j n) (-(c * TrapSum q j))
    rwa [abs_neg] at h
  have hsubInt :
      |q ^ j * n| - |c * TrapSum q j| ≤ |AffineState q c j n| := by
    have hsum :
        |q ^ j * n| - |c * TrapSum q j| + |c * TrapSum q j| ≤
          |AffineState q c j n| + |c * TrapSum q j| := by
      rw [sub_add_cancel]
      exact htri
    exact (add_le_add_iff_right (|c * TrapSum q j|)).mp hsum
  have hlin :
      |q ^ j * n| = ((q.natAbs ^ j * n.natAbs : ℕ) : ℤ) := by
    calc
      |q ^ j * n| = ((q ^ j * n).natAbs : ℤ) :=
        (Int.natCast_natAbs _).symm
      _ = (((q ^ j).natAbs * n.natAbs : ℕ) : ℤ) := by
        rw [Int.natAbs_mul]
      _ = ((q.natAbs ^ j * n.natAbs : ℕ) : ℤ) := by
        rw [Int.natAbs_pow]
  have hoff :
      |c * TrapSum q j| =
        ((c.natAbs * (TrapSum q j).natAbs : ℕ) : ℤ) := by
    calc
      |c * TrapSum q j| = ((c * TrapSum q j).natAbs : ℤ) :=
        (Int.natCast_natAbs _).symm
      _ = ((c.natAbs * (TrapSum q j).natAbs : ℕ) : ℤ) := by
        rw [Int.natAbs_mul]
  have haff :
      |AffineState q c j n| = ((AffineState q c j n).natAbs : ℤ) :=
    (Int.natCast_natAbs _).symm
  rw [hlin, hoff, haff] at hsubInt
  rw [← Nat.cast_sub h] at hsubInt
  exact Nat.cast_le.mp hsubInt

/-- One seed past the offset threshold already forbids the proposed pair `(A, B)`. -/
theorem NoUniformBoundAtLargeSeed (p : Parameters) (n : ℤ) (j A B : ℕ)
    (hhit : IsFirstHit p n j) (hpow : p.D.natAbs ≤ p.Q.natAbs ^ j)
    (hA : A < p.D.natAbs)
    (hbig : B + p.C.natAbs * (TrapSum p.Q j).natAbs + 1 ≤ n.natAbs)
    (hbound :
      p.D.natAbs * (AffineState p.Q p.C j n / p.D).natAbs ≤
        A * n.natAbs + B) :
    False := by
  have hdiv : p.D ∣ AffineState p.Q p.C j n := by
    unfold IsFirstHit at hhit
    exact hhit.1
  let M : ℕ := p.Q.natAbs ^ j
  let K : ℕ := p.C.natAbs * (TrapSum p.Q j).natAbs
  have hM : p.D.natAbs ≤ M := hpow
  have hcoeff : 1 ≤ M - A := by
    have hAM : A + 1 ≤ M := Nat.le_trans (Nat.succ_le_of_lt hA) hM
    have hAle : A ≤ M := Nat.le_of_succ_le hAM
    exact (Nat.le_sub_iff_add_le hAle).mpr (by rw [Nat.add_comm]; exact hAM)
  have hK : K ≤ M * n.natAbs := by
    have hKn : K ≤ n.natAbs := by
      have h1 : K ≤ B + K + 1 := by
        have hle : K ≤ B + K := Nat.le_add_left K B
        exact Nat.le_trans hle (Nat.le_succ (B + K))
      exact Nat.le_trans h1 hbig
    have h12 : 1 ≤ 2 := by decide
    have hM1 : 1 ≤ M := Nat.le_trans h12 (Nat.le_trans p.DAdmissible hM)
    have hmul : n.natAbs ≤ M * n.natAbs := by
      nth_rw 1 [← Nat.one_mul n.natAbs]
      exact Nat.mul_le_mul_right n.natAbs hM1
    exact Nat.le_trans hKn hmul
  have hrev := AffineNatAbsReverse p.Q p.C n j hK
  have hprod := NatAbsQuotientMul p.D (AffineState p.Q p.C j n) hdiv
  have haff : (AffineState p.Q p.C j n).natAbs ≤ A * n.natAbs + B := by
    rw [← hprod]
    exact hbound
  have hsub : M * n.natAbs - K ≤ A * n.natAbs + B := Nat.le_trans hrev haff
  have hsum : M * n.natAbs ≤ A * n.natAbs + (B + K) := by
    have h := (Nat.sub_le_iff_le_add).mp hsub
    rwa [Nat.add_assoc] at h
  have hdiff : M * n.natAbs - A * n.natAbs ≤ B + K :=
    (Nat.sub_le_iff_le_add').mpr hsum
  have hcoeffMul : (M - A) * n.natAbs ≤ B + K := by
    rw [Nat.mul_sub_right_distrib]
    exact hdiff
  have hge : n.natAbs ≤ (M - A) * n.natAbs := by
    have hmul := Nat.mul_le_mul_right n.natAbs hcoeff
    rwa [Nat.one_mul] at hmul
  have hsmall : n.natAbs ≤ B + K := Nat.le_trans hge hcoeffMul
  have hcontr : B + K + 1 ≤ B + K := Nat.le_trans hbig hsmall
  show False
  exact Nat.not_add_one_le_self (B + K) hcontr

/-- No single `A < |D|` and `B` bound the divided affine state on the whole class. -/
theorem NoUniformBoundOnClass (p : Parameters) (n0 : ℤ) (j : ℕ)
    (hhit : IsFirstHit p n0 j) (hpow : p.D.natAbs ≤ p.Q.natAbs ^ j) :
    ¬ ∃ A B : ℕ, A < p.D.natAbs ∧
        ∀ n : ℤ,
          ((n : ZMod p.D.natAbs) = (n0 : ZMod p.D.natAbs)) →
            p.D.natAbs * (AffineState p.Q p.C j n / p.D).natAbs ≤
              A * n.natAbs + B := by
  intro hEx
  obtain ⟨A, B, hA, hclass⟩ := hEx
  let K : ℕ := p.C.natAbs * (TrapSum p.Q j).natAbs
  have hm : 1 ≤ p.D.natAbs := by
    have h12 : 1 ≤ 2 := by decide
    exact Nat.le_trans h12 p.DAdmissible
  obtain ⟨t, ht⟩ := ExistsNatAbsShiftGe n0 p.D.natAbs (B + K + 1) hm
  set n : ℤ := n0 + (t : ℤ) * (p.D.natAbs : ℤ) with hn
  have hhitn : IsFirstHit p n j := by
    rw [hn]
    exact FirstHitNatAbsShift p n0 j t hhit
  have hres :
      ((n : ZMod p.D.natAbs) = (n0 : ZMod p.D.natAbs)) := by
    rw [hn]
    exact ResidueNatAbsShift n0 p.D.natAbs t
  have hbound := hclass n hres
  have hbig : B + K + 1 ≤ n.natAbs := by
    rw [hn]
    exact ht
  show False
  exact NoUniformBoundAtLargeSeed p n j A B hhitn hpow hA hbig hbound

/-- Congruence modulo `|D|` does not move the first hit. -/
theorem FirstHitMod (p : Parameters) (n n' : ℤ) (j : ℕ)
    (h : (p.D.natAbs : ℤ) ∣ n' - n) :
    IsFirstHit p n j ↔ IsFirstHit p n' j := by
  obtain ⟨k, hk⟩ := h
  set ε : ℤ := if 0 ≤ p.D then (1 : ℤ) else -1 with hε
  have habs : (p.D.natAbs : ℤ) = ε * p.D := by
    rw [hε]
    exact NatAbsEqSignMul p.D
  have hseed : n' = n + (ε * k) * p.D := by
    calc
      n' = n + (n' - n) := by ring
      _ = n + (p.D.natAbs : ℤ) * k := by rw [hk]
      _ = n + (ε * p.D) * k := by rw [habs]
      _ = n + (ε * k) * p.D := by ring
  rw [hseed]
  exact FirstHitShift p n (ε * k) j

/-- A class never hits, or its one hit has large slope, or small slope. -/
theorem ClassTrichotomy (p : Parameters) (n0 : ℤ) :
    (∀ n : ℤ, (p.D.natAbs : ℤ) ∣ n - n0 →
      ∀ j : ℕ, ¬ IsFirstHit p n j) ∨
    (∃ j : ℕ, IsFirstHit p n0 j ∧ p.D.natAbs ≤ p.Q.natAbs ^ j ∧
      ∀ n : ℤ, (p.D.natAbs : ℤ) ∣ n - n0 → IsFirstHit p n j) ∨
    (∃ j : ℕ, IsFirstHit p n0 j ∧ p.Q.natAbs ^ j < p.D.natAbs ∧
      ∀ n : ℤ, (p.D.natAbs : ℤ) ∣ n - n0 → IsFirstHit p n j) := by
  classical
  by_cases hhit : ∃ j : ℕ, IsFirstHit p n0 j
  · {
      obtain ⟨j, hj⟩ := hhit
      have hclass : ∀ n : ℤ, (p.D.natAbs : ℤ) ∣ n - n0 →
          IsFirstHit p n j := by
        intro n hn
        exact (FirstHitMod p n0 n j hn).mp hj
      rcases Nat.lt_or_ge (p.Q.natAbs ^ j) p.D.natAbs with hlt | hge
      · {
          exact Or.inr (Or.inr ⟨j, hj, hlt, hclass⟩)
        }
      · {
          exact Or.inr (Or.inl ⟨j, hj, hge, hclass⟩)
        }
    }
  · {
      left
      intro n hn j hj
      have hback : IsFirstHit p n0 j :=
        (FirstHitMod p n0 n j hn).mpr hj
      exact hhit ⟨j, hback⟩
    }

end GeneralizedCollatz.SignedReturnObstruction
