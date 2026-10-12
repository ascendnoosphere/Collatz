-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Tactic.Ring

/-!
# Division-free affine prefixes

If the signed divisor meets no raw state before time `j`, the raw state at time
`j` is the affine state `q^j n + c * TrapSum q j`. The same induction, with the
non-divisibility hypothesis read on affine states, identifies a division-free
affine prefix with the raw prefix. Divisibility at time `j` itself is allowed.
The next raw step is the exact quotient of that state. No later state is
described.
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

/-- A raw prefix with no division before time `j` equals the affine state. -/
theorem PrefixAffine (p : Parameters) (n : ℤ) (j : ℕ)
    (h : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n) :
    Iterate (RawStep p) j n = AffineState p.Q p.C j n := by
  induction j with
  | zero => {
      change n = AffineState p.Q p.C 0 n
      unfold AffineState
      have hsum : TrapSum p.Q 0 = 0 := rfl
      rw [hsum]
      ring
    }
  | succ j ih => {
      have hlt : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self j))
      have hj : ¬ p.D ∣ Iterate (RawStep p) j n :=
        h j (Nat.lt_succ_self j)
      have hstep : Iterate (RawStep p) (j + 1) n =
          RawStep p (Iterate (RawStep p) j n) := rfl
      have haffine : RawStep p (Iterate (RawStep p) j n) =
          p.Q * Iterate (RawStep p) j n + p.C :=
        RawStepAffine p _ hj
      rw [hstep, haffine, ih hlt]
      unfold AffineState
      show p.Q * (p.Q ^ j * n + p.C * TrapSum p.Q j) + p.C =
        p.Q ^ (j + 1) * n + p.C * TrapSum p.Q (j + 1)
      rw [TrapSumRec]
      ring
    }

/-- An affine prefix with no division before time `j` equals the raw state. -/
theorem AffinePrefixRaw (p : Parameters) (n : ℤ) (j : ℕ)
    (h : ∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n) :
    Iterate (RawStep p) j n = AffineState p.Q p.C j n := by
  induction j with
  | zero => {
      change n = AffineState p.Q p.C 0 n
      unfold AffineState
      have hsum : TrapSum p.Q 0 = 0 := rfl
      rw [hsum]
      ring
    }
  | succ j ih => {
      have hlt : ∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self j))
      have ihj : Iterate (RawStep p) j n = AffineState p.Q p.C j n := ih hlt
      have hj : ¬ p.D ∣ AffineState p.Q p.C j n :=
        h j (Nat.lt_succ_self j)
      have hnd : ¬ p.D ∣ Iterate (RawStep p) j n := by
        rw [ihj]
        exact hj
      have hstep : Iterate (RawStep p) (j + 1) n =
          RawStep p (Iterate (RawStep p) j n) := rfl
      have haffine : RawStep p (Iterate (RawStep p) j n) =
          p.Q * Iterate (RawStep p) j n + p.C :=
        RawStepAffine p _ hnd
      rw [hstep, haffine, ihj]
      unfold AffineState
      show p.Q * (p.Q ^ j * n + p.C * TrapSum p.Q j) + p.C =
        p.Q ^ (j + 1) * n + p.C * TrapSum p.Q (j + 1)
      rw [TrapSumRec]
      ring
    }

/-- Every earlier time of a division-free raw prefix equals its affine state. -/
theorem RawPrefixEqAffine (p : Parameters) (n : ℤ) (j k : ℕ)
    (h : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n) (hk : k ≤ j) :
    Iterate (RawStep p) k n = AffineState p.Q p.C k n := by
  have hpre : ∀ i < k, ¬ p.D ∣ Iterate (RawStep p) i n := by
    intro i hi
    exact h i (Nat.lt_of_lt_of_le hi hk)
  exact PrefixAffine p n k hpre

/-- A division-free affine prefix equals the raw prefix at every earlier time. -/
theorem AffinePrefixEqRaw (p : Parameters) (n : ℤ) (j k : ℕ)
    (h : ∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n) (hk : k ≤ j) :
    Iterate (RawStep p) k n = AffineState p.Q p.C k n := by
  have hpre : ∀ i < k, ¬ p.D ∣ AffineState p.Q p.C i n := by
    intro i hi
    exact h i (Nat.lt_of_lt_of_le hi hk)
  exact AffinePrefixRaw p n k hpre

/-- The first affine hit is the first raw hit, with no claim after that time. -/
theorem IsFirstHitIffRaw (p : Parameters) (n : ℤ) (j : ℕ) :
    IsFirstHit p n j ↔
      p.D ∣ Iterate (RawStep p) j n ∧
        ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n := by
  constructor
  · intro h
    unfold IsFirstHit at h
    have hdvd : p.D ∣ AffineState p.Q p.C j n := h.left
    have hfree : ∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n := h.right
    refine ⟨?_, ?_⟩
    · rw [AffinePrefixRaw p n j hfree]
      exact hdvd
    · intro i hi
      have hpre : ∀ k < i, ¬ p.D ∣ AffineState p.Q p.C k n := by
        intro k hk
        exact hfree k (Nat.lt_trans hk hi)
      rw [AffinePrefixRaw p n i hpre]
      exact hfree i hi
  · intro h
    obtain ⟨hdvd, hfree⟩ := h
    unfold IsFirstHit
    refine ⟨?_, ?_⟩
    · have heq : Iterate (RawStep p) j n = AffineState p.Q p.C j n :=
        PrefixAffine p n j hfree
      rw [← heq]
      exact hdvd
    · intro i hi
      have hpre : ∀ k < i, ¬ p.D ∣ Iterate (RawStep p) k n := by
        intro k hk
        exact hfree k (Nat.lt_trans hk hi)
      have heq : Iterate (RawStep p) i n = AffineState p.Q p.C i n :=
        PrefixAffine p n i hpre
      rw [← heq]
      exact hfree i hi

/-- The raw step at a first hit is the exact quotient of the affine state. -/
theorem FirstHitQuotient (p : Parameters) (n : ℤ) (j : ℕ)
    (h : IsFirstHit p n j) :
    Iterate (RawStep p) (j + 1) n =
      AffineState p.Q p.C j n / p.D := by
  have hraw := (IsFirstHitIffRaw p n j).mp h
  obtain ⟨hdvd, hfree⟩ := hraw
  have heq : Iterate (RawStep p) j n = AffineState p.Q p.C j n :=
    PrefixAffine p n j hfree
  have hstep : Iterate (RawStep p) (j + 1) n =
      RawStep p (Iterate (RawStep p) j n) := rfl
  have hdiv : RawStep p (Iterate (RawStep p) j n) =
      Iterate (RawStep p) j n / p.D := by
    unfold RawStep
    exact if_pos hdvd
  rw [hstep, hdiv, heq]

/-- Multiplying the immediate quotient by the divisor recovers the hit. -/
theorem FirstHitReconstruction (p : Parameters) (n : ℤ) (j : ℕ)
    (h : IsFirstHit p n j) :
    p.D * Iterate (RawStep p) (j + 1) n =
      AffineState p.Q p.C j n := by
  have hraw := (IsFirstHitIffRaw p n j).mp h
  have heq : Iterate (RawStep p) j n = AffineState p.Q p.C j n :=
    PrefixAffine p n j hraw.right
  rw [FirstHitQuotient p n j h, ← heq]
  exact Int.mul_ediv_cancel_of_dvd hraw.left

/-- Exact division preserves absolute value: `|d| * |a / d| = |a|`. -/
theorem NatAbsExactDiv (d a : ℤ) (h : d ∣ a) :
    d.natAbs * (a / d).natAbs = a.natAbs := by
  have hcancel : d * (a / d) = a := Int.mul_ediv_cancel_of_dvd h
  have habs : (d * (a / d)).natAbs = a.natAbs := by
    rw [hcancel]
  rw [Int.natAbs_mul] at habs
  exact habs

/-- Sum of the first `j` absolute powers, with the empty sum equal to zero. -/
def AbsPowerSum (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => AbsPowerSum a j + a ^ j

/-- Cancellation in the offset sum cannot increase its absolute value. -/
theorem TrapSumNatAbsLe (q : ℤ) (j : ℕ) :
    (TrapSum q j).natAbs ≤ AbsPowerSum q.natAbs j := by
  induction j with
  | zero => {
      simp [TrapSum, AbsPowerSum, Int.natAbs_zero]
    }
  | succ j ih => {
      have hrec : TrapSum q (j + 1) = TrapSum q j + q ^ j := rfl
      have hnext :
          AbsPowerSum q.natAbs (j + 1) =
            AbsPowerSum q.natAbs j + q.natAbs ^ j := rfl
      rw [hrec, hnext]
      have htri :
          (TrapSum q j + q ^ j).natAbs ≤
            (TrapSum q j).natAbs + (q ^ j).natAbs :=
        Int.natAbs_add_le (TrapSum q j) (q ^ j)
      have hpow : (q ^ j).natAbs = q.natAbs ^ j := Int.natAbs_pow q j
      calc
        (TrapSum q j + q ^ j).natAbs
            ≤ (TrapSum q j).natAbs + (q ^ j).natAbs := htri
        _ ≤ AbsPowerSum q.natAbs j + q.natAbs ^ j := by
          rw [hpow]
          exact Nat.add_le_add_right ih (q.natAbs ^ j)
    }

/-- One first hit: the raw successor obeys the affine triangle bound. -/
theorem FirstHitMagnitude (p : Parameters) (n : ℤ) (j : ℕ)
    (h : IsFirstHit p n j) :
    p.D.natAbs * (Iterate (RawStep p) (j + 1) n).natAbs ≤
      p.Q.natAbs ^ j * n.natAbs +
        p.C.natAbs * (TrapSum p.Q j).natAbs := by
  have hdvd : p.D ∣ AffineState p.Q p.C j n := by
    unfold IsFirstHit at h
    exact h.left
  have hquot := FirstHitQuotient p n j h
  have hid :
      p.D.natAbs * (AffineState p.Q p.C j n / p.D).natAbs =
        (AffineState p.Q p.C j n).natAbs :=
    NatAbsExactDiv p.D (AffineState p.Q p.C j n) hdvd
  rw [hquot, hid]
  unfold AffineState
  have htri :
      (p.Q ^ j * n + p.C * TrapSum p.Q j).natAbs ≤
        (p.Q ^ j * n).natAbs + (p.C * TrapSum p.Q j).natAbs :=
    Int.natAbs_add_le (p.Q ^ j * n) (p.C * TrapSum p.Q j)
  have hprod :
      (p.Q ^ j * n).natAbs = (p.Q ^ j).natAbs * n.natAbs :=
    Int.natAbs_mul (p.Q ^ j) n
  have hpow : (p.Q ^ j).natAbs = p.Q.natAbs ^ j := Int.natAbs_pow p.Q j
  have hoff :
      (p.C * TrapSum p.Q j).natAbs =
        p.C.natAbs * (TrapSum p.Q j).natAbs :=
    Int.natAbs_mul p.C (TrapSum p.Q j)
  calc
    (p.Q ^ j * n + p.C * TrapSum p.Q j).natAbs
        ≤ (p.Q ^ j * n).natAbs + (p.C * TrapSum p.Q j).natAbs := htri
    _ = p.Q.natAbs ^ j * n.natAbs +
          p.C.natAbs * (TrapSum p.Q j).natAbs := by
      rw [hprod, hpow, hoff]

/-- Replace the offset by the sum of absolute powers. -/
theorem FirstHitPowerMajorant (p : Parameters) (n : ℤ) (j : ℕ)
    (h : IsFirstHit p n j) :
    p.D.natAbs * (Iterate (RawStep p) (j + 1) n).natAbs ≤
      p.Q.natAbs ^ j * n.natAbs +
        p.C.natAbs * AbsPowerSum p.Q.natAbs j := by
  have hmag := FirstHitMagnitude p n j h
  have hsum := TrapSumNatAbsLe p.Q j
  have hscale :
      p.C.natAbs * (TrapSum p.Q j).natAbs ≤
        p.C.natAbs * AbsPowerSum p.Q.natAbs j :=
    Nat.mul_le_mul_left p.C.natAbs hsum
  have hright :
      p.Q.natAbs ^ j * n.natAbs +
          p.C.natAbs * (TrapSum p.Q j).natAbs ≤
        p.Q.natAbs ^ j * n.natAbs +
          p.C.natAbs * AbsPowerSum p.Q.natAbs j :=
    Nat.add_le_add_left hscale (p.Q.natAbs ^ j * n.natAbs)
  exact Nat.le_trans hmag hright

/-- The record \(q=2\), \(c=1\), \(d=3\). -/
def TwoOneThree : Parameters where
  Q := 2
  C := 1
  D := 3
  DAdmissible := by decide

/-- Every integer is congruent to \(0\), \(1\), or \(2\) modulo \(3\). -/
theorem EmodThree (n : ℤ) :
    n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
  have hnn : 0 ≤ n % 3 := Int.emod_nonneg n (by decide : (3 : ℤ) ≠ 0)
  have hlt : n % 3 < 3 := Int.emod_lt_of_pos n (by decide)
  omega

/-- The affine step for this record is doubling and adding one. -/
theorem AffineStep231 (n : ℤ) (j : ℕ) :
    AffineState 2 1 (j + 1) n = 2 * AffineState 2 1 j n + 1 := by
  unfold AffineState
  rw [TrapSumRec]
  ring

/-- Residue \(2\) is fixed by \(a \mapsto 2a+1\) modulo \(3\). -/
theorem ResidueTwoStep (a : ℤ) (h : a % 3 = 2) :
    (2 * a + 1) % 3 = 2 := by
  have hsplit : a = a % 3 + 3 * (a / 3) := (Int.emod_add_mul_ediv a 3).symm
  rw [h] at hsplit
  generalize hq : a / 3 = q at hsplit
  have hform : 2 * a + 1 = 2 + 3 * (2 * q + 1) := by
    rw [hsplit]
    ring
  rw [hform]
  have hmod : (2 + 3 * (2 * q + 1)) % 3 = 2 % 3 :=
    Int.add_mul_emod_self_left 2 3 (2 * q + 1)
  rw [hmod]
  decide

/-- If the seed is \(2\) modulo \(3\), every affine state stays there. -/
theorem AffineStaysTwo (n : ℤ) (h : n % 3 = 2) (j : ℕ) :
    AffineState 2 1 j n % 3 = 2 := by
  induction j with
  | zero => {
      have hzero : AffineState 2 1 0 n = n := by
        unfold AffineState
        rw [pow_zero]
        have hsum : TrapSum 2 0 = 0 := rfl
        rw [hsum]
        ring
      rw [hzero]
      exact h
    }
  | succ j ih => {
      rw [AffineStep231]
      exact ResidueTwoStep (AffineState 2 1 j n) ih
    }

/-- Three divides an integer exactly when the remainder modulo \(3\) is zero. -/
theorem DvdThreeIff (a : ℤ) : (3 : ℤ) ∣ a ↔ a % 3 = 0 := by
  exact Int.dvd_iff_emod_eq_zero

/-- Time \(0\) of this record is the seed. -/
theorem AffineZero231 (n : ℤ) : AffineState 2 1 0 n = n := by
  unfold AffineState
  rw [pow_zero]
  have hsum : TrapSum 2 0 = 0 := rfl
  rw [hsum]
  ring

/-- Time \(1\) of this record is \(2n+1\). -/
theorem AffineOne231 (n : ℤ) : AffineState 2 1 1 n = 2 * n + 1 := by
  have hstep := AffineStep231 n 0
  rw [AffineZero231] at hstep
  exact hstep

/-- Residue \(1\) makes \(2n+1\) divisible by \(3\). -/
theorem OneDivisible231 (n : ℤ) (h : n % 3 = 1) : (3 : ℤ) ∣ 2 * n + 1 := by
  have hsplit : n = n % 3 + 3 * (n / 3) := (Int.emod_add_mul_ediv n 3).symm
  rw [h] at hsplit
  generalize hq : n / 3 = q at hsplit
  have hform : 2 * n + 1 = 3 * (2 * q + 1) := by
    rw [hsplit]
    ring
  rw [hform]
  exact dvd_mul_right 3 (2 * q + 1)

/-- For \(q=2\), \(c=1\), \(d=3\), the first hit is at time \(0\), time \(1\), or never. -/
theorem TwoOneThreeHit (n : ℤ) :
    (IsFirstHit TwoOneThree n 0 ∧
        ∀ j, IsFirstHit TwoOneThree n j → j = 0) ∨
      (IsFirstHit TwoOneThree n 1 ∧
        ∀ j, IsFirstHit TwoOneThree n j → j = 1) ∨
      (∀ j, ¬ IsFirstHit TwoOneThree n j) := by
  have hQ : TwoOneThree.Q = 2 := rfl
  have hC : TwoOneThree.C = 1 := rfl
  have hD : TwoOneThree.D = 3 := rfl
  rcases EmodThree n with h0 | h1 | h2
  · {
      left
      refine ⟨?_, ?_⟩
      · {
          unfold IsFirstHit
          rw [hQ, hC, hD]
          refine ⟨?_, ?_⟩
          · {
              rw [AffineZero231]
              exact (DvdThreeIff n).mpr h0
            }
          · {
              intro i hi
              exact absurd hi (Nat.not_lt_zero i)
            }
        }
      · {
          intro j hj
          cases j with
          | zero => {
              rfl
            }
          | succ k => {
              unfold IsFirstHit at hj
              rw [hQ, hC, hD] at hj
              have hd0 : (3 : ℤ) ∣ AffineState 2 1 0 n := by
                rw [AffineZero231]
                exact (DvdThreeIff n).mpr h0
              exact absurd hd0 (hj.2 0 (Nat.succ_pos k))
            }
        }
    }
  · {
      right
      left
      refine ⟨?_, ?_⟩
      · {
          unfold IsFirstHit
          rw [hQ, hC, hD]
          refine ⟨?_, ?_⟩
          · {
              rw [AffineOne231]
              exact OneDivisible231 n h1
            }
          · {
              intro i hi
              have hi0 : i = 0 := by omega
              rw [hi0, AffineZero231]
              intro hd
              have hrem : n % 3 = 0 := (DvdThreeIff n).mp hd
              rw [h1] at hrem
              omega
            }
        }
      · {
          intro j hj
          cases j with
          | zero => {
              unfold IsFirstHit at hj
              rw [hQ, hC, hD] at hj
              have hd : (3 : ℤ) ∣ n := by
                rw [← AffineZero231 n]
                exact hj.1
              have hrem : n % 3 = 0 := (DvdThreeIff n).mp hd
              rw [h1] at hrem
              omega
            }
          | succ k => {
              cases k with
              | zero => {
                  rfl
                }
              | succ m => {
                  unfold IsFirstHit at hj
                  rw [hQ, hC, hD] at hj
                  have hdiv1 : (3 : ℤ) ∣ AffineState 2 1 1 n := by
                    rw [AffineOne231]
                    exact OneDivisible231 n h1
                  exact absurd hdiv1 (hj.2 1 (by omega))
                }
            }
        }
    }
  · {
      right
      right
      intro j hj
      unfold IsFirstHit at hj
      rw [hQ, hC, hD] at hj
      have hstay : AffineState 2 1 j n % 3 = 2 := AffineStaysTwo n h2 j
      have hzero : AffineState 2 1 j n % 3 = 0 :=
        (DvdThreeIff (AffineState 2 1 j n)).mp hj.1
      rw [hstay] at hzero
      omega
    }

/-- A hit for this record obeys \(3|T^{j+1}(n)|\le 2|n|+1\). -/
theorem TwoOneThreeBound (n : ℤ) (j : ℕ)
    (h : IsFirstHit TwoOneThree n j) :
    (3 : ℕ) * (Iterate (RawStep TwoOneThree) (j + 1) n).natAbs ≤
      2 * n.natAbs + 1 := by
  have hQ : TwoOneThree.Q = 2 := rfl
  have hC : TwoOneThree.C = 1 := rfl
  have hD : TwoOneThree.D = 3 := rfl
  rcases TwoOneThreeHit n with hzero | hone | hnever
  · {
      have hj : j = 0 := hzero.2 j h
      have hquot := FirstHitQuotient TwoOneThree n j h
      rw [hj, hQ, hC, hD, AffineZero231] at hquot
      have hdvd : (3 : ℤ) ∣ n := by
        have hhit := hzero.1
        unfold IsFirstHit at hhit
        rw [hQ, hC, hD, AffineZero231] at hhit
        exact hhit.1
      have habs := NatAbsExactDiv (3 : ℤ) n hdvd
      have hcoef : (3 : ℤ).natAbs = 3 := rfl
      rw [hcoef] at habs
      rw [hj, hquot, habs]
      omega
    }
  · {
      have hj : j = 1 := hone.2 j h
      have hquot := FirstHitQuotient TwoOneThree n j h
      rw [hj, hQ, hC, hD, AffineOne231] at hquot
      have hdvd : (3 : ℤ) ∣ 2 * n + 1 := by
        have hhit := hone.1
        unfold IsFirstHit at hhit
        rw [hQ, hC, hD, AffineOne231] at hhit
        exact hhit.1
      have habs := NatAbsExactDiv (3 : ℤ) (2 * n + 1) hdvd
      have htri : (2 * n + 1).natAbs ≤ 2 * n.natAbs + 1 := by
        have hsum :
            (2 * n + 1).natAbs ≤ (2 * n).natAbs + (1 : ℤ).natAbs :=
          Int.natAbs_add_le (2 * n) 1
        have hmul : (2 * n).natAbs = 2 * n.natAbs := by
          have hcoef : (2 : ℤ).natAbs = 2 := rfl
          rw [Int.natAbs_mul, hcoef]
        rw [hmul] at hsum
        simpa using hsum
      have hcoef : (3 : ℤ).natAbs = 3 := rfl
      rw [hcoef] at habs
      rw [hj, hquot, habs]
      exact htri
    }
  · {
      exact absurd h (hnever j)
    }

end GeneralizedCollatz
