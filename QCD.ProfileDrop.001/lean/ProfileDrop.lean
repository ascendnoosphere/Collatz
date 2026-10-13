-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace GeneralizedCollatz

/-!
Affine step `A(n) = q n + c` with `|q| ≥ 2`, and raw division by an integer
`d` with `|d| ≥ 2`. The displacement `z(n) = (q - 1) n + c` and the residue
modulo `|d|` separate the undivided step. A positive division-free orbit of
unbounded magnitude exists if and only if the induced residue map has a
cycle that avoids `0`.

The finite-window argument also bounds the first division time when no
zero-avoiding cycle exists. No assertion concerns the orbit after that division.
-/

/-- The affine branch `A(n) = q n + c`. -/
def AffineBranch (q c n : ℤ) : ℤ :=
  q * n + c

/-- Displacement `z(n) = (q - 1) n + c` of an integer state. -/
def Displacement (q c n : ℤ) : ℤ :=
  (q - 1) * n + c

/-- Iteration of the affine branch. The zeroth state is the seed. -/
def AffineIter (q c n : ℤ) : ℕ → ℤ
  | 0 => n
  | j + 1 => AffineBranch q c (AffineIter q c n j)

/-- Nonnegative residue of `n` modulo a positive integer `m`. -/
def Residue (m : ℕ) (n : ℤ) : ℕ :=
  (n % (m : ℤ)).toNat

/-- Residue map `f(r) = q r + c` modulo `m`, read on a nonnegative representative. -/
def ResidueMap (q c : ℤ) (m r : ℕ) : ℕ :=
  Residue m (q * (r : ℤ) + c)

/-- Iteration of the residue map. -/
def ResidueIter (q c : ℤ) (m : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | j + 1, r => ResidueMap q c m (ResidueIter q c m j r)

/-- One raw step: divide by `d` when the division is integral, otherwise apply `A`. -/
def RawBranch (q c d n : ℤ) : ℤ :=
  if d ∣ n then n / d else AffineBranch q c n

/-- Iteration of the raw step. -/
def RawIter (q c d n : ℤ) : ℕ → ℤ
  | 0 => n
  | j + 1 => RawBranch q c d (RawIter q c d n j)

/-- A cycle of `f(r) = q r + c mod m` whose states lie in `{1, ..., m - 1}`. -/
structure ZeroAvoidingCycle (q c : ℤ) (m : ℕ) where
  /-- Length of the repeating block. -/
  Period : ℕ
  /-- The repeating block is nonempty. -/
  PeriodPos : 0 < Period
  /-- States of one period, extended by the dummy value `0` outside it. -/
  State : ℕ → ℕ
  /-- Every period state is a residue modulo `m`. -/
  StateLt : ∀ k : ℕ, k < Period → State k < m
  /-- No period state is the zero residue. -/
  StateNonzero : ∀ k : ℕ, k < Period → State k ≠ 0
  /-- `f` advances the block and wraps at the last index. -/
  Step : ∀ k : ℕ, k < Period →
    ResidueMap q c m (State k) =
      State (if k + 1 = Period then 0 else k + 1)

/-- The cast of a nonnegative residue is the integer remainder. -/
theorem ResidueCast (m : ℕ) (hm : 0 < m) (n : ℤ) :
    ((Residue m n : ℕ) : ℤ) = n % (m : ℤ) := by
  have hb : (m : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hm)
  have hnn : 0 ≤ n % (m : ℤ) := Int.emod_nonneg n hb
  simp only [Residue]
  exact Int.toNat_of_nonneg hnn

/-- A nonnegative residue is strictly smaller than the modulus. -/
theorem ResidueLt (m : ℕ) (hm : 0 < m) (n : ℤ) : Residue m n < m := by
  have hlt : n % (m : ℤ) < (m : ℤ) :=
    Int.emod_lt_of_pos n (by exact_mod_cast hm)
  have hcast : ((Residue m n : ℕ) : ℤ) < (m : ℤ) := by
    rw [ResidueCast m hm n]
    exact hlt
  exact_mod_cast hcast

/-- The residue vanishes exactly when the modulus divides the integer. -/
theorem ResidueZeroIff (m : ℕ) (hm : 0 < m) (n : ℤ) :
    Residue m n = 0 ↔ (m : ℤ) ∣ n := by
  constructor
  · {
      intro h
      have hc := ResidueCast m hm n
      rw [h, Nat.cast_zero] at hc
      exact (Int.dvd_iff_emod_eq_zero).2 hc.symm
    }
  · {
      intro h
      have hz : n % (m : ℤ) = 0 := (Int.dvd_iff_emod_eq_zero).1 h
      have hc := ResidueCast m hm n
      have hzero : ((Residue m n : ℕ) : ℤ) = 0 := by
        rw [hc, hz]
      exact_mod_cast hzero
    }

/-- Divisibility by `d` is equivalent to divisibility by its positive magnitude. -/
theorem NatAbsDividesIff (d n : ℤ) :
    d ∣ n ↔ (d.natAbs : ℤ) ∣ n :=
  Int.natAbs_dvd.symm

/-- One affine step multiplies displacement by `q`. -/
theorem DisplacementAffine (q c n : ℤ) :
    Displacement q c (AffineBranch q c n) = q * Displacement q c n := by
  simp only [Displacement, AffineBranch]
  ring

/-- The affine residue depends only on the input residue. -/
theorem ResidueAffine (q c n : ℤ) (m : ℕ) (hm : 0 < m) :
    Residue m (AffineBranch q c n) = ResidueMap q c m (Residue m n) := by
  have hsplit : n = (m : ℤ) * (n / (m : ℤ)) + n % (m : ℤ) :=
    (Int.mul_ediv_add_emod n (m : ℤ)).symm
  have hshift :
      (q * n + c) % (m : ℤ) = (q * (n % (m : ℤ)) + c) % (m : ℤ) := by
    have harr :
        q * n + c =
          (q * (n % (m : ℤ)) + c) + (m : ℤ) * (q * (n / (m : ℤ))) := by
      calc
        q * n + c = q * ((m : ℤ) * (n / (m : ℤ)) + n % (m : ℤ)) + c :=
          congrArg (fun x : ℤ => q * x + c) hsplit
        _ = (q * (n % (m : ℤ)) + c) + (m : ℤ) * (q * (n / (m : ℤ))) := by
          ring
    rw [harr]
    exact Int.add_mul_emod_self_left _ (m : ℤ) _
  have hres :
      (q * ((Residue m n : ℕ) : ℤ) + c) % (m : ℤ) =
        (q * (n % (m : ℤ)) + c) % (m : ℤ) := by
    rw [ResidueCast m hm n]
  have heq :
      (AffineBranch q c n) % (m : ℤ) =
        (q * ((Residue m n : ℕ) : ℤ) + c) % (m : ℤ) := by
    simp only [AffineBranch]
    exact hshift.trans hres.symm
  have hL := ResidueCast m hm (AffineBranch q c n)
  have hR := ResidueCast m hm (q * ((Residue m n : ℕ) : ℤ) + c)
  have hZ :
      ((Residue m (AffineBranch q c n) : ℕ) : ℤ) =
        ((ResidueMap q c m (Residue m n) : ℕ) : ℤ) := by
    change ((Residue m (AffineBranch q c n) : ℕ) : ℤ) =
      ((Residue m (q * ((Residue m n : ℕ) : ℤ) + c) : ℕ) : ℤ)
    rw [hL, hR]
    exact heq
  exact_mod_cast hZ

/-- The two coordinates of one undivided step, stated together. -/
theorem MergedProfileStep (q c n : ℤ) (m : ℕ) (hm : 0 < m) :
    Displacement q c (AffineBranch q c n) = q * Displacement q c n ∧
      Residue m (AffineBranch q c n) =
        ResidueMap q c m (Residue m n) :=
  ⟨DisplacementAffine q c n, ResidueAffine q c n m hm⟩

/-- Iterating the affine branch multiplies the initial displacement by `q^j`. -/
theorem DisplacementIterated (q c n : ℤ) (j : ℕ) :
    Displacement q c (AffineIter q c n j) =
      q ^ j * Displacement q c n := by
  induction j with
  | zero => {
      rw [AffineIter.eq_1, pow_zero, one_mul]
    }
  | succ j ih => {
      rw [AffineIter.eq_2, DisplacementAffine, ih, pow_succ]
      ring
    }

/-- Closed form `(q - 1) A^j(n) = q^j z(n) - c`. -/
theorem DisplacementClosedForm (q c n : ℤ) (j : ℕ) :
    (q - 1) * AffineIter q c n j =
      q ^ j * Displacement q c n - c := by
  have h := DisplacementIterated q c n j
  rw [Displacement] at h
  exact eq_sub_of_add_eq h

/-- Affine iteration acts as residue iteration on the initial residue. -/
theorem ResidueAffineIter (q c n : ℤ) (m : ℕ) (hm : 0 < m) (j : ℕ) :
    Residue m (AffineIter q c n j) =
      ResidueIter q c m j (Residue m n) := by
  induction j with
  | zero => {
      rw [AffineIter.eq_1, ResidueIter.eq_1]
    }
  | succ j ih => {
      rw [AffineIter.eq_2, ResidueIter.eq_2, ResidueAffine q c _ m hm, ih]
    }

/-- For every natural number `B` there is a power of two strictly above `B`. -/
theorem NatLtTwoPowSucc (n : ℕ) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => {
      decide
    }
  | succ n ih => {
      have hge : n + 1 ≤ 2 ^ (n + 1) := Nat.succ_le_of_lt ih
      have hmul : 2 * (n + 1) ≤ 2 * 2 ^ (n + 1) :=
        Nat.mul_le_mul_left 2 hge
      have hlt : n + 1 < 2 * (n + 1) := by
        have hpos : 0 < n + 1 := Nat.succ_pos n
        have hsumLt : n + 1 + 0 < n + 1 + (n + 1) :=
          Nat.add_lt_add_left hpos (n + 1)
        rw [Nat.add_zero, ← Nat.two_mul (n + 1)] at hsumLt
        exact hsumLt
      have hpow : 2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by
        rw [pow_succ, Nat.mul_comm]
      rw [hpow]
      exact Nat.lt_of_lt_of_le hlt hmul
    }

/-- If `|q| ≥ 2` and `z(n) ≠ 0`, then `|A^j(n)|` eventually exceeds every bound. -/
theorem AffineNatAbsEventually (q c n : ℤ) (hq : 2 ≤ q.natAbs)
    (hz : Displacement q c n ≠ 0) (N : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → N < (AffineIter q c n j).natAbs := by
  have hqne : q ≠ 1 := by
    intro h
    rw [h, Int.natAbs_one] at hq
    omega
  have hdpos : 0 < (q - 1).natAbs := by
    have hne : q - 1 ≠ 0 := sub_ne_zero.mpr hqne
    exact Nat.pos_of_ne_zero ((Int.natAbs_eq_zero).not.mpr hne)
  have hzpos : 0 < (Displacement q c n).natAbs :=
    Nat.pos_of_ne_zero ((Int.natAbs_eq_zero).not.mpr hz)
  let D : ℕ := (q - 1).natAbs
  let Z : ℕ := (Displacement q c n).natAbs
  let C : ℕ := c.natAbs
  let B : ℕ := C + N * D
  have hpow : B < 2 ^ (B + 1) := NatLtTwoPowSucc B
  refine ⟨B + 1, ?_⟩
  intro j hj
  have h2 : B < 2 ^ j := by
    have hmono : 2 ^ (B + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (Nat.succ_pos 1) hj
    exact Nat.lt_of_lt_of_le hpow hmono
  have hbase : 2 ^ j ≤ q.natAbs ^ j := Nat.pow_le_pow_left hq j
  have hone : 1 ≤ Z := Nat.succ_le_of_lt hzpos
  have hmul : 2 ^ j ≤ q.natAbs ^ j * Z := by
    have hunit : 2 ^ j * 1 ≤ q.natAbs ^ j * Z := Nat.mul_le_mul hbase hone
    simpa using hunit
  have habs : (q ^ j * Displacement q c n).natAbs = q.natAbs ^ j * Z := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
  have hbig : B < (q ^ j * Displacement q c n).natAbs := by
    rw [habs]
    exact Nat.lt_of_lt_of_le h2 hmul
  have htri :
      (q ^ j * Displacement q c n).natAbs ≤
        (q ^ j * Displacement q c n - c).natAbs + C := by
    simpa [C] using
      Int.natAbs_add_le (q ^ j * Displacement q c n - c) c
  have hdiff :
      (q ^ j * Displacement q c n - c).natAbs =
        D * (AffineIter q c n j).natAbs := by
    have hform := DisplacementClosedForm q c n j
    calc
      (q ^ j * Displacement q c n - c).natAbs
          = ((q - 1) * AffineIter q c n j).natAbs := by rw [hform]
      _ = (q - 1).natAbs * (AffineIter q c n j).natAbs :=
          Int.natAbs_mul _ _
      _ = D * (AffineIter q c n j).natAbs := rfl
  have hsub :
      (q ^ j * Displacement q c n).natAbs - C ≤
        (q ^ j * Displacement q c n - c).natAbs :=
    Nat.sub_le_of_le_add htri
  have hND : N * D < (q ^ j * Displacement q c n).natAbs - C := by
    have hsum : N * D + C < (q ^ j * Displacement q c n).natAbs := by
      have hB : C + N * D < (q ^ j * Displacement q c n).natAbs := by
        simpa [B] using hbig
      rw [Nat.add_comm] at hB
      exact hB
    exact Nat.lt_sub_of_add_lt hsum
  have hprod : N * D < D * (AffineIter q c n j).natAbs := by
    have hbound :
        N * D < (q ^ j * Displacement q c n - c).natAbs :=
      Nat.lt_of_lt_of_le hND hsub
    rwa [hdiff] at hbound
  have hprod' : D * N < D * (AffineIter q c n j).natAbs := by
    rw [Nat.mul_comm D N]
    exact hprod
  exact (Nat.mul_lt_mul_left hdpos).mp hprod'

/-- A residue `r` has a positive lift whose displacement is nonzero. -/
theorem PositiveDisplacementLift (q c : ℤ) (m r : ℕ) (hm : 2 ≤ m)
    (hr : r < m) (hq : 2 ≤ q.natAbs) :
    ∃ n : ℕ, 0 < n ∧ Residue m (n : ℤ) = r ∧
      Displacement q c (n : ℤ) ≠ 0 := by
  have hmpos : 0 < m := Nat.lt_of_lt_of_le (Nat.succ_pos 1) hm
  have hqne : q ≠ 1 := by
    intro h
    rw [h, Int.natAbs_one] at hq
    omega
  have hspan : (q - 1) * (m : ℤ) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hqne) (by exact_mod_cast (Nat.ne_of_gt hmpos))
  have hresOf (k : ℕ) : Residue m ((r + k * m : ℕ) : ℤ) = r := by
    have hr0 : (0 : ℤ) ≤ (r : ℤ) := by
      exact_mod_cast (Nat.zero_le r)
    have hrl : (r : ℤ) < (m : ℤ) := by
      exact_mod_cast hr
    have hrm : (r : ℤ) % (m : ℤ) = (r : ℤ) := Int.emod_eq_of_lt hr0 hrl
    have hmod :
        ((r : ℤ) + (m : ℤ) * (k : ℤ)) % (m : ℤ) = (r : ℤ) % (m : ℤ) :=
      Int.add_mul_emod_self_left (r : ℤ) (m : ℤ) (k : ℤ)
    have hcast : ((r + k * m : ℕ) : ℤ) = (r : ℤ) + (m : ℤ) * (k : ℤ) := by
      simp only [Nat.cast_add, Nat.cast_mul]
      ring
    have hc := ResidueCast m hmpos ((r + k * m : ℕ) : ℤ)
    have hZ : ((Residue m ((r + k * m : ℕ) : ℤ) : ℕ) : ℤ) = (r : ℤ) := by
      rw [hc, hcast, hmod, hrm]
    exact_mod_cast hZ
  let n1 : ℕ := r + m
  let n2 : ℕ := r + m + m
  have hpos1 : 0 < n1 :=
    Nat.lt_of_lt_of_le hmpos (Nat.le_add_left m r)
  have hpos2 : 0 < n2 :=
    Nat.lt_of_lt_of_le hmpos (Nat.le_add_left m (r + m))
  have hn1 : n1 = r + 1 * m := by
    simp [n1]
  have hn2 : n2 = r + 2 * m := by
    change r + m + m = r + 2 * m
    rw [Nat.add_assoc, ← Nat.two_mul]
  have hdiff :
      Displacement q c (n2 : ℤ) =
        Displacement q c (n1 : ℤ) + (q - 1) * (m : ℤ) := by
    have hn : (n2 : ℤ) = (n1 : ℤ) + (m : ℤ) := by
      simp [n1, n2, Nat.cast_add]
    simp only [Displacement]
    rw [hn]
    ring
  by_cases hz : Displacement q c (n1 : ℤ) = 0
  · {
      refine ⟨n2, hpos2, ?_, ?_⟩
      · {
          rw [hn2]
          exact hresOf 2
        }
      · {
          rw [hdiff, hz, zero_add]
          exact hspan
        }
    }
  · {
      refine ⟨n1, hpos1, ?_, hz⟩
      rw [hn1]
      exact hresOf 1
    }

/-- The successor residue modulo `p` wraps exactly when the representative is `p - 1`. -/
theorem SuccMod (j p : ℕ) (hp : 0 < p) :
    (j + 1) % p = if j % p + 1 = p then 0 else j % p + 1 := by
  have hlt : j % p < p := Nat.mod_lt j hp
  have hbase : p * (j / p) + j % p = j := Nat.div_add_mod j p
  by_cases hwrap : j % p + 1 = p
  · {
      have hsum : j + 1 = p * (j / p + 1) := by
        have hstep : j + 1 = p * (j / p) + (j % p + 1) := by
          omega
        rw [hstep, hwrap]
        ring
      have hdvd : p ∣ j + 1 := ⟨j / p + 1, hsum⟩
      simp [hwrap, Nat.mod_eq_zero_of_dvd hdvd]
    }
  · {
      have hlt2 : j % p + 1 < p := by
        omega
      have hsplit : j + 1 = (j / p) * p + (j % p + 1) := by
        rw [Nat.mul_comm (j / p) p]
        omega
      have hmod : (j + 1) % p = j % p + 1 := by
        rw [hsplit]
        exact Nat.mul_add_mod_of_lt hlt2
      simp [hwrap, hmod]
    }

/-- A repeated nonzero residue on an `f`-orbit cuts out a zero-avoiding cycle. -/
theorem CycleFromRepeat (q c : ℤ) (m : ℕ) (u : ℕ → ℕ)
    (i j : ℕ) (hij : i < j)
    (huLt : ∀ k : ℕ, i ≤ k → k < j → u k < m)
    (huNe : ∀ k : ℕ, i ≤ k → k < j → u k ≠ 0)
    (hstep : ∀ k : ℕ, i ≤ k → k < j →
      u (k + 1) = ResidueMap q c m (u k)) (heq : u i = u j) :
    Nonempty (ZeroAvoidingCycle q c m) := by
  let p : ℕ := j - i
  have hp : 0 < p := Nat.sub_pos_of_lt hij
  let State : ℕ → ℕ := fun k => if k < p then u (i + k) else 0
  have hState (k : ℕ) (hk : k < p) : State k = u (i + k) := by
    simp [State, if_pos hk]
  refine ⟨{
    Period := p
    PeriodPos := hp
    State := State
    StateLt := ?_
    StateNonzero := ?_
    Step := ?_
  }⟩
  · {
      intro k hk
      rw [hState k hk]
      exact huLt (i + k) (by omega) (by omega)
    }
  · {
      intro k hk
      rw [hState k hk]
      exact huNe (i + k) (by omega) (by omega)
    }
  · {
      intro k hk
      rw [hState k hk]
      rw [← hstep (i + k) (by omega) (by omega)]
      by_cases hwrap : k + 1 = p
      · {
          have hidx : (if k + 1 = p then 0 else k + 1) = 0 := by
            simp [hwrap]
          rw [hidx]
          have hS0 : State 0 = u i := hState 0 hp
          rw [hS0]
          have hreach : i + k + 1 = j := by
            omega
          rw [hreach]
          exact heq.symm
        }
      · {
          have hk1 : k + 1 < p := by
            omega
          have hidx : (if k + 1 = p then 0 else k + 1) = k + 1 := by
            simp [if_neg hwrap]
          rw [hidx, hState (k + 1) hk1]
          have hadd : i + (k + 1) = i + k + 1 := by
            omega
          rw [hadd]
        }
    }

/-- Walking `f` along a cycle reproduces the periodic state list. -/
theorem CycleResidue (q c : ℤ) (m : ℕ) (C : ZeroAvoidingCycle q c m)
    (j : ℕ) :
    ResidueIter q c m j (C.State 0) = C.State (j % C.Period) := by
  induction j with
  | zero => {
      rw [ResidueIter.eq_1, Nat.zero_mod]
    }
  | succ j ih => {
      have hk : j % C.Period < C.Period := Nat.mod_lt j C.PeriodPos
      have hmod := SuccMod j C.Period C.PeriodPos
      rw [ResidueIter.eq_2, ih, C.Step (j % C.Period) hk, hmod]
    }

/-- While the affine orbit avoids division by `d`, the raw orbit agrees with it. -/
theorem RawFollowsAffine (q c d n : ℤ)
    (hfree : ∀ j : ℕ, ¬ d ∣ AffineIter q c n j) (j : ℕ) :
    RawIter q c d n j = AffineIter q c n j := by
  induction j with
  | zero => {
      rw [RawIter.eq_1, AffineIter.eq_1]
    }
  | succ j ih => {
      rw [RawIter.eq_2, AffineIter.eq_2, ih]
      simp only [RawBranch, AffineBranch, if_neg (hfree j)]
    }

/-- A nonzero cycle modulo any divisor of `d` prevents every raw division by `d`. -/
theorem LocalCycleEscape (q c d : ℤ) (m : ℕ) (hq : 2 ≤ q.natAbs)
    (_hd : 2 ≤ d.natAbs) (hm : 2 ≤ m) (hmd : (m : ℤ) ∣ d)
    (C : ZeroAvoidingCycle q c m) :
    ∃ n : ℕ, 0 < n ∧ (∀ j : ℕ, ¬ d ∣ RawIter q c d (n : ℤ) j) ∧
      (∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        N < (RawIter q c d (n : ℤ) j).natAbs) := by
  have hmpos : 0 < m := Nat.lt_of_lt_of_le (Nat.succ_pos 1) hm
  have h0lt : C.State 0 < m := C.StateLt 0 C.PeriodPos
  obtain ⟨n, hn, hres, hz⟩ :=
    PositiveDisplacementLift q c m (C.State 0) hm h0lt hq
  have horbit : ∀ j : ℕ,
      Residue m (AffineIter q c (n : ℤ) j) = C.State (j % C.Period) := by
    intro j
    rw [ResidueAffineIter q c (n : ℤ) m hmpos j, hres]
    exact CycleResidue q c m C j
  have hfreeA : ∀ j : ℕ, ¬ d ∣ AffineIter q c (n : ℤ) j := by
    intro j hdiv
    have hmdiv : (m : ℤ) ∣ AffineIter q c (n : ℤ) j := hmd.trans hdiv
    have hzero : Residue m (AffineIter q c (n : ℤ) j) = 0 :=
      (ResidueZeroIff m hmpos _).2 hmdiv
    rw [horbit j] at hzero
    exact C.StateNonzero (j % C.Period) (Nat.mod_lt j C.PeriodPos) hzero
  have hraw : ∀ j : ℕ,
      RawIter q c d (n : ℤ) j = AffineIter q c (n : ℤ) j :=
    fun j => RawFollowsAffine q c d (n : ℤ) hfreeA j
  refine ⟨n, hn, ?_, ?_⟩
  · {
      intro j hdiv
      exact hfreeA j (by rwa [hraw j] at hdiv)
    }
  · {
      intro N
      obtain ⟨J, hJ⟩ := AffineNatAbsEventually q c (n : ℤ) hq hz N
      refine ⟨J, ?_⟩
      intro j hj
      rw [hraw j]
      exact hJ j hj
    }

/-- A zero-avoiding residue cycle lifts to a positive division-free unbounded orbit. -/
theorem ZeroAvoidingCycleEscape (q c d : ℤ) (hq : 2 ≤ q.natAbs)
    (hd : 2 ≤ d.natAbs) (C : ZeroAvoidingCycle q c d.natAbs) :
    ∃ n : ℕ, 0 < n ∧ (∀ j : ℕ, ¬ d ∣ RawIter q c d (n : ℤ) j) ∧
      (∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        N < (RawIter q c d (n : ℤ) j).natAbs) := by
  have hmd : (d.natAbs : ℤ) ∣ d := (Int.natAbs_dvd).mpr (dvd_refl d)
  exact LocalCycleEscape q c d d.natAbs hq hd hd hmd C

/-- Avoiding division at the first `|d|` states already supplies a nonzero cycle. -/
theorem FiniteDivisionFreeGivesCycle (q c d n : ℤ) (hd : 2 ≤ d.natAbs)
    (hfree : ∀ j : ℕ, j < d.natAbs → ¬ d ∣ RawIter q c d n j) :
    Nonempty (ZeroAvoidingCycle q c d.natAbs) := by
  let m : ℕ := d.natAbs
  have hm : 2 ≤ m := hd
  have hmpos : 0 < m := Nat.lt_of_lt_of_le (Nat.succ_pos 1) hm
  let u : ℕ → ℕ := fun j => Residue m (RawIter q c d n j)
  have huLt : ∀ j : ℕ, u j < m := fun j => ResidueLt m hmpos _
  have huNe : ∀ j : ℕ, j < m → u j ≠ 0 := by
    intro j hj hz
    have hmdiv : (m : ℤ) ∣ RawIter q c d n j :=
      (ResidueZeroIff m hmpos _).1 hz
    exact hfree j hj ((Int.natAbs_dvd).mp hmdiv)
  have hstep : ∀ j : ℕ, j < m → u (j + 1) = ResidueMap q c m (u j) := by
    intro j hj
    have hraw :
        RawIter q c d n (j + 1) = AffineBranch q c (RawIter q c d n j) := by
      rw [RawIter.eq_2]
      simp only [RawBranch, AffineBranch, if_neg (hfree j hj)]
    simp only [u]
    rw [hraw]
    exact ResidueAffine q c _ m hmpos
  have hcard : Fintype.card (Fin (m - 1)) < Fintype.card (Fin m) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨x, y, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun j : Fin m =>
        (⟨u j.val - 1, by
          have hlt := huLt j.val
          have hpos := Nat.pos_of_ne_zero (huNe j.val j.isLt)
          omega⟩ : Fin (m - 1))) hcard
  have hu : u x.val = u y.val := by
    have hval : (u x.val - 1 : ℕ) = u y.val - 1 :=
      congrArg (fun t : Fin (m - 1) => t.val) heq
    have hx : 1 ≤ u x.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (huNe x.val x.isLt))
    have hy : 1 ≤ u y.val := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (huNe y.val y.isLt))
    calc
      u x.val = u x.val - 1 + 1 := (Nat.sub_add_cancel hx).symm
      _ = u y.val - 1 + 1 := by rw [hval]
      _ = u y.val := Nat.sub_add_cancel hy
  have hneVal : x.val ≠ y.val := by
    intro h
    exact hne (Fin.ext h)
  rcases Nat.lt_trichotomy x.val y.val with hlt | hxy | hgt
  · {
      exact CycleFromRepeat q c m u x.val y.val hlt
        (fun k _ _ => huLt k)
        (fun k _ hk => huNe k (Nat.lt_trans hk y.isLt))
        (fun k _ hk => hstep k (Nat.lt_trans hk y.isLt)) hu
    }
  · {
      exact absurd hxy hneVal
    }
  · {
      exact CycleFromRepeat q c m u y.val x.val hgt
        (fun k _ _ => huLt k)
        (fun k _ hk => huNe k (Nat.lt_trans hk x.isLt))
        (fun k _ hk => hstep k (Nat.lt_trans hk x.isLt)) hu.symm
    }

/-- Without a nonzero cycle, every integer seed divides within the first `|d|` states. -/
theorem NoCycleForcesDivision (q c d n : ℤ) (hd : 2 ≤ d.natAbs)
    (hno : ¬ Nonempty (ZeroAvoidingCycle q c d.natAbs)) :
    ∃ j : ℕ, j < d.natAbs ∧ d ∣ RawIter q c d n j := by
  classical
  by_contra h
  have hfree : ∀ j : ℕ, j < d.natAbs → ¬ d ∣ RawIter q c d n j := by
    intro j hj hdiv
    exact h ⟨j, hj, hdiv⟩
  exact hno (FiniteDivisionFreeGivesCycle q c d n hd hfree)

/-- A division-free raw orbit projects onto a zero-avoiding residue cycle. -/
theorem DivisionFreeGivesCycle (q c d n : ℤ) (hd : 2 ≤ d.natAbs)
    (hfree : ∀ j : ℕ, ¬ d ∣ RawIter q c d n j) :
    Nonempty (ZeroAvoidingCycle q c d.natAbs) := by
  exact FiniteDivisionFreeGivesCycle q c d n hd (fun j _ => hfree j)

/-- A nonzero cycle exists exactly when some residue never reaches zero. -/
theorem CycleIffNonzeroResiduePath (q c : ℤ) (m : ℕ) (hm : 2 ≤ m) :
    Nonempty (ZeroAvoidingCycle q c m) ↔
      ∃ r : ℕ, r < m ∧ ∀ j : ℕ, ResidueIter q c m j r ≠ 0 := by
  constructor
  · {
      intro h
      obtain ⟨C⟩ := h
      refine ⟨C.State 0, C.StateLt 0 C.PeriodPos, ?_⟩
      intro j
      rw [CycleResidue q c m C j]
      exact C.StateNonzero (j % C.Period) (Nat.mod_lt j C.PeriodPos)
    }
  · {
      intro h
      obtain ⟨r, hr, hpath⟩ := h
      have hmpos : 0 < m := Nat.lt_of_lt_of_le (Nat.succ_pos 1) hm
      have hres : Residue m (r : ℤ) = r := by
        have hmod : (r : ℤ) % (m : ℤ) = (r : ℤ) :=
          Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le r) (by exact_mod_cast hr)
        simp only [Residue, hmod, Int.toNat_natCast]
      have hfreeA : ∀ j : ℕ, ¬ (m : ℤ) ∣ AffineIter q c (r : ℤ) j := by
        intro j hdiv
        have hz : Residue m (AffineIter q c (r : ℤ) j) = 0 :=
          (ResidueZeroIff m hmpos _).2 hdiv
        rw [ResidueAffineIter q c (r : ℤ) m hmpos j, hres] at hz
        exact hpath j hz
      have hraw : ∀ j : ℕ,
          RawIter q c (m : ℤ) (r : ℤ) j = AffineIter q c (r : ℤ) j :=
        fun j => RawFollowsAffine q c (m : ℤ) (r : ℤ) hfreeA j
      have hfreeRaw : ∀ j : ℕ, ¬ (m : ℤ) ∣ RawIter q c (m : ℤ) (r : ℤ) j := by
        intro j
        rw [hraw j]
        exact hfreeA j
      have hd : 2 ≤ (m : ℤ).natAbs := by simpa using hm
      have hcycle := DivisionFreeGivesCycle q c (m : ℤ) (r : ℤ) hd hfreeRaw
      simpa using hcycle
    }

/-- Profile drop: a positive division-free unbounded raw seed is a zero-avoiding cycle. -/
theorem ProfileDrop (q c d : ℤ) (hq : 2 ≤ q.natAbs) (hd : 2 ≤ d.natAbs) :
    (∃ n : ℕ, 0 < n ∧ (∀ j : ℕ, ¬ d ∣ RawIter q c d (n : ℤ) j) ∧
      (∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        N < (RawIter q c d (n : ℤ) j).natAbs)) ↔
      Nonempty (ZeroAvoidingCycle q c d.natAbs) := by
  constructor
  · {
      intro h
      obtain ⟨n, _, hfree, _⟩ := h
      exact DivisionFreeGivesCycle q c d (n : ℤ) hd hfree
    }
  · {
      intro h
      obtain ⟨C⟩ := h
      exact ZeroAvoidingCycleEscape q c d hq hd C
    }

/-- A divisible difference gives the same nonnegative residue. -/
theorem ResidueEqOfDvdDifference (m : ℕ) (x y : ℤ) (h : (m : ℤ) ∣ x - y) :
    Residue m x = Residue m y := by
  obtain ⟨t, ht⟩ := h
  have hx : x = y + (m : ℤ) * t := by omega
  unfold Residue
  rw [hx, Int.add_mul_emod_self_left]

/-- Dependence on the starting state is multiplied by `q^j`. -/
theorem AffineIterDifference (q c x y : ℤ) (j : ℕ) :
    AffineIter q c x j - AffineIter q c y j = q ^ j * (x - y) := by
  induction j with
  | zero => {
      simp only [AffineIter, pow_zero, one_mul]
    }
  | succ j ih => {
      simp only [AffineIter, AffineBranch]
      calc
        q * AffineIter q c x j + c - (q * AffineIter q c y j + c) =
            q * (AffineIter q c x j - AffineIter q c y j) := by ring
        _ = q ^ (j + 1) * (x - y) := by rw [ih, pow_succ]; ring
    }

/-- Consecutive offsets differ by `q^j c`. -/
theorem AffineIterZeroIncrement (q c : ℤ) (j : ℕ) :
    AffineIter q c 0 (j + 1) - AffineIter q c 0 j = q ^ j * c := by
  induction j with
  | zero => {
      simp only [AffineIter, AffineBranch, mul_zero, zero_add, sub_zero,
        pow_zero, one_mul]
    }
  | succ j ih => {
      change q * AffineIter q c 0 (j + 1) + c -
        (q * AffineIter q c 0 j + c) = q ^ (j + 1) * c
      calc
        q * AffineIter q c 0 (j + 1) + c - (q * AffineIter q c 0 j + c) =
            q * (AffineIter q c 0 (j + 1) - AffineIter q c 0 j) := by ring
        _ = q ^ (j + 1) * c := by rw [ih, pow_succ]; ring
    }

/-- A representative already in the residue interval is unchanged. -/
theorem ResidueRepresentative (m r : ℕ) (hr : r < m) : Residue m (r : ℤ) = r := by
  have hmod : (r : ℤ) % (m : ℤ) = (r : ℤ) :=
    Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le r) (by exact_mod_cast hr)
  simp only [Residue, hmod, Int.toNat_natCast]

/-- If `m` divides `q^k`, every affine residue has the same value at time `k`. -/
theorem NilpotentResidueCollapse (q c : ℤ) (m k r : ℕ) (hm : 0 < m)
    (hnil : (m : ℤ) ∣ q ^ k) (hr : r < m) :
    ResidueIter q c m k r = Residue m (AffineIter q c 0 k) := by
  have hdiff : (m : ℤ) ∣ AffineIter q c (r : ℤ) k - AffineIter q c 0 k := by
    rw [AffineIterDifference]
    exact dvd_mul_of_dvd_left hnil _
  have h := ResidueEqOfDvdDifference m _ _ hdiff
  rw [ResidueAffineIter q c (r : ℤ) m hm k, ResidueRepresentative m r hr] at h
  exact h

/-- The common time-`k` residue is fixed by the affine residue map. -/
theorem NilpotentResidueFixed (q c : ℤ) (m k : ℕ) (hm : 0 < m)
    (hnil : (m : ℤ) ∣ q ^ k) :
    ResidueMap q c m (Residue m (AffineIter q c 0 k)) =
      Residue m (AffineIter q c 0 k) := by
  have hdiff : (m : ℤ) ∣ AffineIter q c 0 (k + 1) - AffineIter q c 0 k := by
    rw [AffineIterZeroIncrement]
    exact dvd_mul_of_dvd_left hnil c
  have h := ResidueEqOfDvdDifference m _ _ hdiff
  rw [AffineIter.eq_2, ResidueAffine q c _ m hm] at h
  exact h

/-- Iteration preserves a fixed residue at every time, including time zero. -/
theorem FixedResidueIter (q c : ℤ) (m r : ℕ) (hfix : ResidueMap q c m r = r)
    (j : ℕ) : ResidueIter q c m j r = r := by
  induction j with
  | zero => { rfl }
  | succ j ih => { rw [ResidueIter.eq_2, ih, hfix] }

/-- A divisible offset keeps every affine iterate of zero divisible. -/
theorem AffineZeroDivisible (q c : ℤ) (m : ℕ) (hc : (m : ℤ) ∣ c) (j : ℕ) :
    (m : ℤ) ∣ AffineIter q c 0 j := by
  induction j with
  | zero => { exact dvd_zero _ }
  | succ j ih => {
      exact Int.dvd_add (dvd_mul_of_dvd_right ih q) hc
    }

/-- For a nilpotent multiplier, all residues reach zero exactly when `m` divides `c`. -/
theorem NilpotentAllReachZeroIff (q c : ℤ) (m k : ℕ) (hm : 0 < m)
    (hnil : (m : ℤ) ∣ q ^ k) :
    (∀ r : ℕ, r < m → ∃ j : ℕ, ResidueIter q c m j r = 0) ↔ (m : ℤ) ∣ c := by
  constructor
  · {
      intro hall
      let s := Residue m (AffineIter q c 0 k)
      have hs : s < m := ResidueLt m hm _
      have hfix : ResidueMap q c m s = s := NilpotentResidueFixed q c m k hm hnil
      obtain ⟨j, hj⟩ := hall s hs
      rw [FixedResidueIter q c m s hfix j] at hj
      rw [hj] at hfix
      have hc : Residue m c = 0 := by simpa [ResidueMap] using hfix
      exact (ResidueZeroIff m hm c).1 hc
    }
  · {
      intro hc r hr
      refine ⟨k, ?_⟩
      rw [NilpotentResidueCollapse q c m k r hm hnil hr]
      exact (ResidueZeroIff m hm _).2 (AffineZeroDivisible q c m hc k)
    }

/-- A nilpotent multiplier has a nonzero cycle precisely when its offset is not divisible. -/
theorem NilpotentCycleIff (q c : ℤ) (m k : ℕ) (hm : 2 ≤ m)
    (hnil : (m : ℤ) ∣ q ^ k) :
    Nonempty (ZeroAvoidingCycle q c m) ↔ ¬ (m : ℤ) ∣ c := by
  have hmpos : 0 < m := by omega
  constructor
  · {
      intro hcycle hc
      obtain ⟨r, hr, hpath⟩ := (CycleIffNonzeroResiduePath q c m hm).1 hcycle
      obtain ⟨j, hj⟩ := (NilpotentAllReachZeroIff q c m k hmpos hnil).2 hc r hr
      exact hpath j hj
    }
  · {
      intro hc
      let s := Residue m (AffineIter q c 0 k)
      have hfix : ResidueMap q c m s = s := NilpotentResidueFixed q c m k hmpos hnil
      have hs : s ≠ 0 := by
        intro hz
        rw [hz] at hfix
        have hczero : Residue m c = 0 := by simpa [ResidueMap] using hfix
        exact hc ((ResidueZeroIff m hmpos c).1 hczero)
      apply (CycleIffNonzeroResiduePath q c m hm).2
      refine ⟨s, ResidueLt m hmpos _, ?_⟩
      intro j
      rw [FixedResidueIter q c m s hfix j]
      exact hs
    }

/-- If a base divides `q`, its `a`th power divides `q^a`; primality is not required. -/
theorem PowerDivisorAllReachZeroIff (q c : ℤ) (p a : ℕ) (hp : 0 < p)
    (hpq : (p : ℤ) ∣ q) :
    (∀ r : ℕ, r < p ^ a → ∃ j : ℕ, ResidueIter q c (p ^ a) j r = 0) ↔
      ((p ^ a : ℕ) : ℤ) ∣ c := by
  have hnil : ((p ^ a : ℕ) : ℤ) ∣ q ^ a := by
    simpa only [Nat.cast_pow] using pow_dvd_pow_of_dvd hpq a
  exact NilpotentAllReachZeroIff q c (p ^ a) a (Nat.pow_pos hp) hnil

/-- A failed nilpotent test on one divisor constructs escape for the full signed divisor. -/
theorem NilpotentLocalEscape (q c d : ℤ) (m k : ℕ) (hq : 2 ≤ q.natAbs)
    (hd : 2 ≤ d.natAbs) (hm : 2 ≤ m) (hmd : (m : ℤ) ∣ d)
    (hnil : (m : ℤ) ∣ q ^ k)
    (hc : ¬ (m : ℤ) ∣ c) :
    ∃ n : ℕ, 0 < n ∧ (∀ j : ℕ, ¬ d ∣ RawIter q c d (n : ℤ) j) ∧
      (∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        N < (RawIter q c d (n : ℤ) j).natAbs) := by
  obtain ⟨C⟩ := (NilpotentCycleIff q c m k hm hnil).2 hc
  exact LocalCycleEscape q c d m hq hd hm hmd C

/-- A unit multiplier and a divisible offset preserve the nonzero orbit of `1`. -/
theorem UnitDivisibleOffsetCycle (q c : ℤ) (m : ℕ) (hm : 2 ≤ m)
    (hcop : q.natAbs.Coprime m) (hc : (m : ℤ) ∣ c) :
    Nonempty (ZeroAvoidingCycle q c m) := by
  have hmpos : 0 < m := by omega
  apply (CycleIffNonzeroResiduePath q c m hm).2
  refine ⟨1, by omega, ?_⟩
  intro j hz
  have hrep : Residue m (1 : ℤ) = 1 := ResidueRepresentative m 1 (by omega)
  have hres : Residue m (AffineIter q c 1 j) = 0 := by
    rw [ResidueAffineIter q c 1 m hmpos j, hrep]
    exact hz
  have hdiv : (m : ℤ) ∣ AffineIter q c 1 j := (ResidueZeroIff m hmpos _).1 hres
  have hzero : (m : ℤ) ∣ AffineIter q c 0 j := AffineZeroDivisible q c m hc j
  have hpow : (m : ℤ) ∣ q ^ j := by
    have hdiff := Int.dvd_sub hdiv hzero
    rw [AffineIterDifference] at hdiff
    simpa using hdiff
  have hnat : m ∣ q.natAbs ^ j := by
    have habs := (Int.natAbs_dvd_natAbs).2 hpow
    simpa only [Int.natAbs_natCast, Int.natAbs_pow] using habs
  have hone : m = 1 := Nat.eq_one_of_dvd_coprimes (hcop.pow_left j) hnat (dvd_refl m)
  omega

/-- A unit multiplier with a divisible local offset yields full signed raw escape. -/
theorem UnitDivisibleOffsetLocalEscape (q c d : ℤ) (m : ℕ)
    (hq : 2 ≤ q.natAbs) (hd : 2 ≤ d.natAbs) (hm : 2 ≤ m)
    (hmd : (m : ℤ) ∣ d) (hcop : q.natAbs.Coprime m) (hc : (m : ℤ) ∣ c) :
    ∃ n : ℕ, 0 < n ∧ (∀ j : ℕ, ¬ d ∣ RawIter q c d (n : ℤ) j) ∧
      (∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        N < (RawIter q c d (n : ℤ) j).natAbs) := by
  obtain ⟨C⟩ := UnitDivisibleOffsetCycle q c m hm hcop hc
  exact LocalCycleEscape q c d m hq hd hm hmd C

/-- When `q + 1` is divisible by four and `c` is odd, `2` lies on a nonzero two-cycle. -/
theorem ModFourCycle (q c : ℤ) (hq : (4 : ℤ) ∣ q + 1) (hc : ¬ (2 : ℤ) ∣ c) :
    Nonempty (ZeroAvoidingCycle q c 4) := by
  let b := ResidueMap q c 4 2
  have hbLt : b < 4 := ResidueLt 4 (by decide) _
  have hbNe : b ≠ 0 := by
    intro hb
    have hfour : (4 : ℤ) ∣ q * 2 + c := (ResidueZeroIff 4 (by decide) _).1 hb
    have htwo : (2 : ℤ) ∣ q * 2 + c := (show (2 : ℤ) ∣ 4 by decide).trans hfour
    have htwoMul : (2 : ℤ) ∣ q * 2 := ⟨q, by ring⟩
    have hcDiv : (2 : ℤ) ∣ c := by
      simpa only [add_sub_cancel_left] using Int.dvd_sub htwo htwoMul
    exact hc hcDiv
  have hdiff : (4 : ℤ) ∣ AffineBranch q c (AffineBranch q c 2) - 2 := by
    have heq : AffineBranch q c (AffineBranch q c 2) - 2 =
        (q + 1) * (2 * (q - 1) + c) := by
      simp only [AffineBranch]
      ring
    rw [heq]
    exact dvd_mul_of_dvd_left hq (2 * (q - 1) + c)
  have hsecond : ResidueMap q c 4 b = 2 := by
    have h := ResidueEqOfDvdDifference 4 _ 2 hdiff
    have hrep : Residue 4 (2 : ℤ) = 2 := ResidueRepresentative 4 2 (by decide)
    rw [ResidueAffine q c (AffineBranch q c 2) 4 (by decide), hrep] at h
    exact h
  let State := fun k : ℕ => if k = 0 then 2 else if k = 1 then b else 0
  refine ⟨{
    Period := 2
    PeriodPos := by decide
    State := State
    StateLt := ?_
    StateNonzero := ?_
    Step := ?_
  }⟩
  · {
      intro k hk
      have hcases : k = 0 ∨ k = 1 := by omega
      rcases hcases with rfl | rfl
      · { change (2 : ℕ) < 4; decide }
      · { change b < 4; exact hbLt }
    }
  · {
      intro k hk
      have hcases : k = 0 ∨ k = 1 := by omega
      rcases hcases with rfl | rfl
      · { change (2 : ℕ) ≠ 0; decide }
      · { change b ≠ 0; exact hbNe }
    }
  · {
      intro k hk
      have hcases : k = 0 ∨ k = 1 := by omega
      rcases hcases with rfl | rfl
      · { change ResidueMap q c 4 2 = b; rfl }
      · { change ResidueMap q c 4 b = 2; exact hsecond }
    }

/-- The modulo-four obstruction lifts to escape for any signed divisor divisible by four. -/
theorem ModFourLocalEscape (q c d : ℤ) (hq : 2 ≤ q.natAbs)
    (hd : 2 ≤ d.natAbs) (hfour : (4 : ℤ) ∣ d)
    (hqFour : (4 : ℤ) ∣ q + 1) (hcOdd : ¬ (2 : ℤ) ∣ c) :
    ∃ n : ℕ, 0 < n ∧ (∀ j : ℕ, ¬ d ∣ RawIter q c d (n : ℤ) j) ∧
      (∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        N < (RawIter q c d (n : ℤ) j).natAbs) := by
  obtain ⟨C⟩ := ModFourCycle q c hqFour hcOdd
  exact LocalCycleEscape q c d 4 hq hd (by decide) hfour C

/-- An invertible `q - 1` and nondivisible offset give a nonzero fixed residue. -/
theorem CoprimeDifferenceCycle (q c : ℤ) (m : ℕ) (hm : 2 ≤ m)
    (hcop : (q - 1).natAbs.Coprime m) (hc : ¬ (m : ℤ) ∣ c) :
    Nonempty (ZeroAvoidingCycle q c m) := by
  have hmpos : 0 < m := by omega
  let a := Int.gcdA (q - 1) (m : ℤ)
  let b := Int.gcdB (q - 1) (m : ℤ)
  let x := -c * a
  have hgcd : Int.gcd (q - 1) (m : ℤ) = 1 := by
    simpa only [Int.gcd_def, Int.natAbs_natCast] using hcop.gcd_eq_one
  have hbezout : 1 = (q - 1) * a + (m : ℤ) * b := by
    simpa only [hgcd, Nat.cast_one] using Int.gcd_eq_gcd_ab (q - 1) (m : ℤ)
  have hlinear : 1 - (q - 1) * a = (m : ℤ) * b := by omega
  have hz : (m : ℤ) ∣ Displacement q c x := by
    refine ⟨c * b, ?_⟩
    calc
      Displacement q c x = c * (1 - (q - 1) * a) := by
        simp only [Displacement, x]
        ring
      _ = (m : ℤ) * (c * b) := by rw [hlinear]; ring
  let s := Residue m x
  have hfixed : ResidueMap q c m s = s := by
    have hdiff : (m : ℤ) ∣ AffineBranch q c x - x := by
      have heq : AffineBranch q c x - x = Displacement q c x := by
        simp only [AffineBranch, Displacement]
        ring
      rw [heq]
      exact hz
    have h := ResidueEqOfDvdDifference m _ x hdiff
    rw [ResidueAffine q c x m hmpos] at h
    exact h
  have hs : s ≠ 0 := by
    intro hsZero
    have hx : (m : ℤ) ∣ x := (ResidueZeroIff m hmpos x).1 hsZero
    have hxMul : (m : ℤ) ∣ (q - 1) * x := dvd_mul_of_dvd_right hx _
    have hcDiv : (m : ℤ) ∣ c := by
      have hsub := Int.dvd_sub hz hxMul
      simpa only [Displacement, add_sub_cancel_left] using hsub
    exact hc hcDiv
  apply (CycleIffNonzeroResiduePath q c m hm).2
  refine ⟨s, ResidueLt m hmpos x, ?_⟩
  intro j
  rw [FixedResidueIter q c m s hfixed j]
  exact hs

/-- A nonzero fixed residue modulo a local divisor recovers positive raw escape. -/
theorem CoprimeDifferenceLocalEscape (q c d : ℤ) (m : ℕ)
    (hq : 2 ≤ q.natAbs) (hd : 2 ≤ d.natAbs) (hm : 2 ≤ m)
    (hmd : (m : ℤ) ∣ d) (hcop : (q - 1).natAbs.Coprime m)
    (hc : ¬ (m : ℤ) ∣ c) :
    ∃ n : ℕ, 0 < n ∧ (∀ j : ℕ, ¬ d ∣ RawIter q c d (n : ℤ) j) ∧
      (∀ N : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        N < (RawIter q c d (n : ℤ) j).natAbs) := by
  obtain ⟨C⟩ := CoprimeDifferenceCycle q c m hm hcop hc
  exact LocalCycleEscape q c d m hq hd hm hmd C

end GeneralizedCollatz
