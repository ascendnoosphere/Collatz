-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import SignedCore
import Mathlib.Data.Nat.Find
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Uniform return under a uniform hitting bound

Assume every integer has a first hit of the affine state by the signed
divisor. Divisibility is decidable, so the least such time is `Nat.find`.
The total return divides the affine state at that time by `D`. If one pair
of natural numbers `A < |D|` and `B` bounds `|Q|^j` and
`|C| * |TrapSum Q j|` at every least hit `j`, the return obeys
`|D| * |H(n)| ≤ A * |n| + B` at every integer. `CoreEntry` and
`CoreEventuallyPeriodic` then give entry into `CoreRadius A B |D|` and
eventual periodicity of `H`. Their hypotheses are exactly `A < m` and the
bound at every integer, with `m = |D|`.

A uniform bound on the least-hit time produces one such pair. If every
least hit is at most `J` and the largest `|Q|^j` for `j ≤ J` is strictly
less than `|D|`, that largest power and the largest offset on the same
range are admissible `A` and `B`. Without a bound on the hitting time,
`|Q| ≥ 2` does not provide them. The obstruction is by residue classes of the
walk `r ↦ Q r + C` on `Z/|D|Z`: a class that never meets `0` has no first
hit, and a class whose least hit satisfies `|Q|^j ≥ |D|` forbids every
candidate `A < |D|`. Neither alternative is removed by `|Q| ≥ 2`. That
dichotomy is not proved here. `OddTranslation` is one proved instance of a
missed class.

`Q = 1` with an arbitrary offset and an arbitrary admissible divisor is not
claimed. A unit multiplier does not force every seed to hit. The positive
application is pure division on seeds already divisible by `D`, which is not
every seed. `CoreEntry` is applied only under the explicit hypothesis that
every seed hits.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.SignedReturnUniform

/-- Affine state after `j` undivided steps, with offset sum `TrapSum q j`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- `j` is the first time `D` divides the affine state of the seed `n`. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n

/-- Every integer has at least one first hit. This is a hypothesis. -/
def EverySeedHits (p : Parameters) : Prop :=
  ∀ n : ℤ, ∃ j : ℕ, IsFirstHit p n j

/-- A miss at every time before the horizon is decidable by recursion. -/
def EarlyMissDecidable (p : Parameters) (n : ℤ) :
    (j : ℕ) → Decidable
      (∀ i : ℕ, i < j → ¬ p.D ∣ AffineState p.Q p.C i n)
  | 0 =>
      isTrue (by
        intro i hi
        exact absurd hi (Nat.not_lt_zero i))
  | j + 1 =>
      match EarlyMissDecidable p n j with
      | isFalse hmiss =>
          isFalse (by
            intro hall
            apply hmiss
            intro i hi
            exact hall i (Nat.lt_succ_of_lt hi))
      | isTrue hmiss =>
          if hd : p.D ∣ AffineState p.Q p.C j n then
            isFalse (by
              intro hall
              exact hall j (Nat.lt_succ_self j) hd)
          else
            isTrue (by
              intro i hi
              have hle : i ≤ j := Nat.le_of_lt_succ hi
              rcases Nat.eq_or_lt_of_le hle with heq | hlt
              · {
                  subst heq
                  exact hd
                }
              · {
                  exact hmiss i hlt
                })

/-- First hits are decidable because divisibility of one integer is. -/
instance FirstHitDecidable (p : Parameters) (n : ℤ) :
    DecidablePred (IsFirstHit p n) :=
  fun j =>
    if hd : p.D ∣ AffineState p.Q p.C j n then
      match EarlyMissDecidable p n j with
      | isTrue hearly => isTrue ⟨hd, hearly⟩
      | isFalse hearly => isFalse (fun h => hearly h.2)
    else
      isFalse (fun h => hd h.1)

/-- Least first-hit time. `Nat.find` applies once existence is given. -/
def LeastHit (p : Parameters) (n : ℤ) (h : ∃ j : ℕ, IsFirstHit p n j) : ℕ :=
  Nat.find h

/-- The total return divides the affine state at the least hit. -/
def TotalReturn (p : Parameters) (h : EverySeedHits p) (n : ℤ) : ℤ :=
  AffineState p.Q p.C (LeastHit p n (h n)) n / p.D

/-- At time zero the power is one and the offset sum is empty. -/
theorem AffineStateZero (q c n : ℤ) : AffineState q c 0 n = n := by
  unfold AffineState
  rw [Int.pow_zero]
  have hsum : TrapSum q 0 = 0 := rfl
  rw [hsum, Int.one_mul, Int.mul_zero, Int.add_zero]

/-- No natural number is strictly less than zero, so the range is empty. -/
theorem NoEarlierAtZero (P : ℕ → Prop) : ∀ i : ℕ, i < 0 → P i := by
  intro i hi
  exact absurd hi (Nat.not_lt_zero i)

/-- Time zero is a first hit exactly when `D` divides the seed. -/
theorem FirstHitZeroIff (p : Parameters) (n : ℤ) :
    IsFirstHit p n 0 ↔ p.D ∣ n := by
  constructor
  · {
      intro h
      have hdiv : p.D ∣ AffineState p.Q p.C 0 n := h.1
      rw [AffineStateZero p.Q p.C n] at hdiv
      exact hdiv
    }
  · {
      intro hdiv
      refine ⟨?_, NoEarlierAtZero _⟩
      rw [AffineStateZero p.Q p.C n]
      exact hdiv
    }

/-- Exact division preserves absolute value: `|d| * |a / d| = |a|`. -/
theorem NatAbsExactDiv (d a : ℤ) (h : d ∣ a) :
    d.natAbs * (a / d).natAbs = a.natAbs := by
  have hcancel : d * (a / d) = a := Int.mul_ediv_cancel' h
  have habs : (d * (a / d)).natAbs = a.natAbs := by
    rw [hcancel]
  rw [Int.natAbs_mul] at habs
  exact habs

/-- The triangle inequality, then absolute values of a product and a power. -/
theorem AffineTriangle (q c n : ℤ) (j : ℕ) :
    (AffineState q c j n).natAbs ≤
      q.natAbs ^ j * n.natAbs + c.natAbs * (TrapSum q j).natAbs := by
  unfold AffineState
  have htri :
      (q ^ j * n + c * TrapSum q j).natAbs ≤
        (q ^ j * n).natAbs + (c * TrapSum q j).natAbs :=
    Int.natAbs_add_le (q ^ j * n) (c * TrapSum q j)
  have hprod : (q ^ j * n).natAbs = (q ^ j).natAbs * n.natAbs :=
    Int.natAbs_mul (q ^ j) n
  have hpow : (q ^ j).natAbs = q.natAbs ^ j := Int.natAbs_pow q j
  have hoff : (c * TrapSum q j).natAbs = c.natAbs * (TrapSum q j).natAbs :=
    Int.natAbs_mul c (TrapSum q j)
  calc
    (q ^ j * n + c * TrapSum q j).natAbs
        ≤ (q ^ j * n).natAbs + (c * TrapSum q j).natAbs := htri
    _ = q.natAbs ^ j * n.natAbs + c.natAbs * (TrapSum q j).natAbs := by
      rw [hprod, hpow, hoff]

/-- Two first-hit times of one seed are equal. -/
theorem FirstHitUnique (p : Parameters) (n : ℤ) (j k : ℕ)
    (hj : IsFirstHit p n j) (hk : IsFirstHit p n k) : j = k := by
  rcases lt_trichotomy j k with hlt | heq | hgt
  · {
      exact False.elim (hk.2 j hlt hj.1)
    }
  · {
      exact heq
    }
  · {
      exact False.elim (hj.2 k hgt hk.1)
    }

/-- The value chosen by `Nat.find` is a first hit. -/
theorem LeastHitIsFirst (p : Parameters) (n : ℤ)
    (h : ∃ j : ℕ, IsFirstHit p n j) :
    IsFirstHit p n (LeastHit p n h) :=
  Nat.find_spec h

/-- The least hit is the only first hit. -/
theorem LeastHitOnly (p : Parameters) (n : ℤ)
    (h : ∃ j : ℕ, IsFirstHit p n j) (k : ℕ) (hk : IsFirstHit p n k) :
    LeastHit p n h = k :=
  FirstHitUnique p n (LeastHit p n h) k (LeastHitIsFirst p n h) hk

/-- One first hit: the quotient of the affine state obeys the triangle bound. -/
theorem HitMagnitude (p : Parameters) (n : ℤ) (j : ℕ) (h : IsFirstHit p n j) :
    p.D.natAbs * (AffineState p.Q p.C j n / p.D).natAbs ≤
      p.Q.natAbs ^ j * n.natAbs +
        p.C.natAbs * (TrapSum p.Q j).natAbs := by
  have hdvd : p.D ∣ AffineState p.Q p.C j n := h.1
  have hid :
      p.D.natAbs * (AffineState p.Q p.C j n / p.D).natAbs =
        (AffineState p.Q p.C j n).natAbs :=
    NatAbsExactDiv p.D (AffineState p.Q p.C j n) hdvd
  rw [hid]
  exact AffineTriangle p.Q p.C n j

/-- A slope bound and an offset bound add after multiplication by `|n|`. -/
theorem AbsorbSlope (qAbs cTrap nAbs A B : ℕ) (hq : qAbs ≤ A) (hc : cTrap ≤ B) :
    qAbs * nAbs + cTrap ≤ A * nAbs + B := by
  have hmul : qAbs * nAbs ≤ A * nAbs := Nat.mul_le_mul_right nAbs hq
  exact Nat.add_le_add hmul hc

/-- Largest power `a^j` for `j ≤ J`. The time-zero power is `1`. -/
def MaxPow (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | J + 1 => max (MaxPow a J) (a ^ (J + 1))

/-- Largest offset `|c| * |TrapSum q j|` for `j ≤ J`. -/
def MaxOff (q c : ℤ) : ℕ → ℕ
  | 0 => c.natAbs * (TrapSum q 0).natAbs
  | J + 1 =>
      max (MaxOff q c J) (c.natAbs * (TrapSum q (J + 1)).natAbs)

/-- Every power up to the horizon is at most the recorded maximum. -/
theorem MaxPowLe (a j J : ℕ) (hj : j ≤ J) : a ^ j ≤ MaxPow a J := by
  induction J with
  | zero => {
      have hj0 : j = 0 := by omega
      subst hj0
      simp [MaxPow]
    }
  | succ J ih => {
      by_cases hle : j ≤ J
      · {
          exact le_trans (ih hle) (Nat.le_max_left _ _)
        }
      · {
          have hj' : j = J + 1 := by omega
          subst hj'
          exact Nat.le_max_right _ _
        }
    }

/-- A positive base makes the last power the largest. -/
theorem MaxPowOfPos (a J : ℕ) (ha : 1 ≤ a) : MaxPow a J = a ^ J := by
  induction J with
  | zero => {
      simp [MaxPow]
    }
  | succ J ih => {
      have hmul : a ^ J ≤ a ^ J * a := by
        have hone : 1 ≤ a ^ J := Nat.one_le_pow J a ha
        have hstep : a ^ J * 1 ≤ a ^ J * a := Nat.mul_le_mul_left (a ^ J) ha
        simpa using hstep
      have hpow : a ^ (J + 1) = a ^ J * a := Nat.pow_succ a J
      calc
        MaxPow a (J + 1) = max (MaxPow a J) (a ^ (J + 1)) := by
          simp [MaxPow]
        _ = max (a ^ J) (a ^ (J + 1)) := by rw [ih]
        _ = a ^ (J + 1) := by
          rw [hpow, Nat.max_eq_right hmul]
    }

/-- Powers of a base at least `2` eventually pass any bound. -/
theorem TwoPowCovers (a b : ℕ) (ha : 2 ≤ a) : ∃ J : ℕ, b ≤ a ^ J := by
  induction b with
  | zero => {
      exact ⟨0, Nat.zero_le _⟩
    }
  | succ b ih => {
      obtain ⟨J, hJ⟩ := ih
      refine ⟨J + 1, ?_⟩
      have hone : 1 ≤ a ^ J := Nat.one_le_pow J a (by omega)
      have htwo : 2 * a ^ J ≤ a * a ^ J :=
        Nat.mul_le_mul_right (a ^ J) ha
      calc
        b + 1 ≤ a ^ J + 1 := Nat.succ_le_succ hJ
        _ ≤ a ^ J + a ^ J := Nat.add_le_add_left hone _
        _ = 2 * a ^ J := (Nat.two_mul (a ^ J)).symm
        _ ≤ a * a ^ J := htwo
        _ = a ^ (J + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm]
    }

/-- A smaller power of a base at least `2` has the smaller exponent. -/
theorem PowLtOfLtPow (a j J : ℕ) (ha : 2 ≤ a) (hlt : a ^ j < a ^ J) :
    j < J := by
  by_contra hge
  have hle : J ≤ j := Nat.le_of_not_lt hge
  have hpow : a ^ J ≤ a ^ j := Nat.pow_le_pow_right (by omega) hle
  omega

/-- Every offset up to the horizon is at most the recorded maximum. -/
theorem MaxOffLe (q c : ℤ) (j J : ℕ) (hj : j ≤ J) :
    c.natAbs * (TrapSum q j).natAbs ≤ MaxOff q c J := by
  induction J with
  | zero => {
      have hj0 : j = 0 := by omega
      subst hj0
      simp [MaxOff]
    }
  | succ J ih => {
      by_cases hle : j ≤ J
      · {
          exact le_trans (ih hle) (Nat.le_max_left _ _)
        }
      · {
          have hj' : j = J + 1 := by omega
          subst hj'
          exact Nat.le_max_right _ _
        }
    }

/-- If `A < |D|` and every least hit obeys the slope and offset bounds, then
`|D| * |H(n)| ≤ A * |n| + B` at every integer. The gap `A < |D|` is retained
because entry into the core uses it; the comparison itself is the triangle
inequality at the least hit. -/
theorem UniformReturnBound (p : Parameters) (h : EverySeedHits p) (A B : ℕ)
    (hA : A < p.D.natAbs)
    (huniform :
      ∀ n : ℤ,
        p.Q.natAbs ^ LeastHit p n (h n) ≤ A ∧
          p.C.natAbs * (TrapSum p.Q (LeastHit p n (h n))).natAbs ≤ B)
    (n : ℤ) :
    p.D.natAbs * (TotalReturn p h n).natAbs ≤ A * n.natAbs + B := by
  have _hgap : 0 < p.D.natAbs - A := Nat.sub_pos_of_lt hA
  let j : ℕ := LeastHit p n (h n)
  have hhit : IsFirstHit p n j := LeastHitIsFirst p n (h n)
  have hmag := HitMagnitude p n j hhit
  have hslope : p.Q.natAbs ^ j ≤ A := (huniform n).1
  have hoffset : p.C.natAbs * (TrapSum p.Q j).natAbs ≤ B := (huniform n).2
  have habs :
      p.Q.natAbs ^ j * n.natAbs +
          p.C.natAbs * (TrapSum p.Q j).natAbs ≤
        A * n.natAbs + B :=
    AbsorbSlope (p.Q.natAbs ^ j) (p.C.natAbs * (TrapSum p.Q j).natAbs)
      n.natAbs A B hslope hoffset
  have hret : TotalReturn p h n = AffineState p.Q p.C j n / p.D := rfl
  rw [hret]
  exact Nat.le_trans hmag habs

/-- The same hypotheses give entry into the core radius and eventual
periodicity of the total return. `CoreEntry` and `CoreEventuallyPeriodic`
are applied with modulus `|D|`. Each asks for `A < m` and the linear bound
at every integer, and both of those are the hypotheses here together with
`UniformReturnBound`. -/
theorem UniformReturnPeriodic (p : Parameters) (h : EverySeedHits p) (A B : ℕ)
    (hA : A < p.D.natAbs)
    (huniform :
      ∀ n : ℤ,
        p.Q.natAbs ^ LeastHit p n (h n) ≤ A ∧
          p.C.natAbs * (TrapSum p.Q (LeastHit p n (h n))).natAbs ≤ B)
    (n : ℤ) :
    (∃ j : ℕ,
        (Iterate (TotalReturn p h) j n).natAbs ≤ CoreRadius A B p.D.natAbs) ∧
      ∃ t per : ℕ, 0 < per ∧
        ∀ k : ℕ,
          Iterate (TotalReturn p h) (t + k) n =
            Iterate (TotalReturn p h) (t + k + per) n := by
  have hbound :
      ∀ k : ℤ,
        p.D.natAbs * (TotalReturn p h k).natAbs ≤ A * k.natAbs + B :=
    fun k => UniformReturnBound p h A B hA huniform k
  refine ⟨?_, ?_⟩
  · {
      exact CoreEntry A B p.D.natAbs (TotalReturn p h) hA hbound n
    }
  · {
      exact CoreEventuallyPeriodic A B p.D.natAbs (TotalReturn p h) hA hbound n
    }

/-- A uniform hitting horizon with `MaxPow < |D|` gives the core conclusions. -/
theorem BoundedHitPeriodic (p : Parameters) (h : EverySeedHits p) (J : ℕ)
    (hJ : ∀ n : ℤ, LeastHit p n (h n) ≤ J)
    (hA : MaxPow p.Q.natAbs J < p.D.natAbs) (n : ℤ) :
    (∃ j : ℕ,
        (Iterate (TotalReturn p h) j n).natAbs ≤
          CoreRadius (MaxPow p.Q.natAbs J) (MaxOff p.Q p.C J) p.D.natAbs) ∧
      ∃ t per : ℕ, 0 < per ∧
        ∀ k : ℕ,
          Iterate (TotalReturn p h) (t + k) n =
            Iterate (TotalReturn p h) (t + k + per) n := by
  have huniform :
      ∀ n : ℤ,
        p.Q.natAbs ^ LeastHit p n (h n) ≤ MaxPow p.Q.natAbs J ∧
          p.C.natAbs * (TrapSum p.Q (LeastHit p n (h n))).natAbs ≤
            MaxOff p.Q p.C J := by
    intro n
    exact ⟨MaxPowLe _ _ _ (hJ n), MaxOffLe _ _ _ _ (hJ n)⟩
  exact UniformReturnPeriodic p h (MaxPow p.Q.natAbs J) (MaxOff p.Q p.C J)
    hA huniform n

/-- For `|Q| ≥ 2`, small slopes are bounded by one horizon. -/
theorem SmallSlopeHorizon (p : Parameters) (h : EverySeedHits p)
    (hq : 2 ≤ p.Q.natAbs)
    (hsmall : ∀ n : ℤ,
      p.Q.natAbs ^ LeastHit p n (h n) < p.D.natAbs) :
    ∃ J : ℕ, (∀ n : ℤ, LeastHit p n (h n) ≤ J) ∧
      MaxPow p.Q.natAbs J < p.D.natAbs := by
  classical
  have hcover := TwoPowCovers p.Q.natAbs p.D.natAbs hq
  let J0 : ℕ := Nat.find hcover
  have hJ0 : p.D.natAbs ≤ p.Q.natAbs ^ J0 := Nat.find_spec hcover
  have hpos : 0 < J0 := by
    by_contra hzero
    have hJ0z : J0 = 0 := by omega
    have hone : p.Q.natAbs ^ J0 = 1 := by simp [hJ0z]
    have hd : 2 ≤ p.D.natAbs := p.DAdmissible
    omega
  let J : ℕ := J0 - 1
  have hstep : J0 = J + 1 := by omega
  have hprev : p.Q.natAbs ^ J < p.D.natAbs := by
    by_contra hge
    have hge' : p.D.natAbs ≤ p.Q.natAbs ^ J := Nat.le_of_not_lt hge
    have hlt : J < J0 := by omega
    exact Nat.find_min hcover hlt hge'
  refine ⟨J, ?_, ?_⟩
  · {
      intro n
      have hpow :
          p.Q.natAbs ^ LeastHit p n (h n) < p.Q.natAbs ^ J0 :=
        Nat.lt_of_lt_of_le (hsmall n) hJ0
      have hlt := PowLtOfLtPow p.Q.natAbs _ J0 hq hpow
      omega
    }
  · {
      rw [MaxPowOfPos p.Q.natAbs J (by omega)]
      exact hprev
    }

/-- For `|Q| ≥ 2`, every small-slope hit gives the core conclusions. -/
theorem SmallSlopePeriodic (p : Parameters) (h : EverySeedHits p)
    (hq : 2 ≤ p.Q.natAbs)
    (hsmall : ∀ n : ℤ,
      p.Q.natAbs ^ LeastHit p n (h n) < p.D.natAbs) (n : ℤ) :
    ∃ J : ℕ,
      (∃ j : ℕ,
          (Iterate (TotalReturn p h) j n).natAbs ≤
            CoreRadius (MaxPow p.Q.natAbs J) (MaxOff p.Q p.C J)
              p.D.natAbs) ∧
        ∃ t per : ℕ, 0 < per ∧
          ∀ k : ℕ,
            Iterate (TotalReturn p h) (t + k) n =
              Iterate (TotalReturn p h) (t + k + per) n := by
  obtain ⟨J, hJ, hA⟩ := SmallSlopeHorizon p h hq hsmall
  exact ⟨J, BoundedHitPeriodic p h J hJ hA n⟩

/-- An admissible divisor does not divide `1`. -/
theorem PureDivisionMissesOne (p : Parameters) : ¬ p.D ∣ (1 : ℤ) := by
  intro h
  have hnat : p.D.natAbs ∣ (1 : ℤ).natAbs := (Int.natAbs_dvd_natAbs).mpr h
  have hone : (1 : ℤ).natAbs = 1 := Int.natAbs_natCast 1
  rw [hone] at hnat
  have heq : p.D.natAbs = 1 := (Nat.dvd_one).mp hnat
  have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
  omega

/-- If `|Q| ≥ |D|`, the seed `1` has no small-slope first hit. -/
theorem NoSmallSlopeAtOne (p : Parameters)
    (hq : p.D.natAbs ≤ p.Q.natAbs) :
    ¬ ∃ j : ℕ, IsFirstHit p (1 : ℤ) j ∧
        p.Q.natAbs ^ j < p.D.natAbs := by
  intro hEx
  obtain ⟨j, hj, hpow⟩ := hEx
  cases j with
  | zero => {
      have hsum : TrapSum p.Q 0 = 0 := rfl
      have hdiv : p.D ∣ (1 : ℤ) := by
        simpa [IsFirstHit, AffineState, hsum] using hj.1
      exact PureDivisionMissesOne p hdiv
    }
  | succ k => {
      have hbase : p.Q.natAbs ^ 1 ≤ p.Q.natAbs ^ (k + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hge : p.D.natAbs ≤ p.Q.natAbs ^ (k + 1) := by
        rw [Nat.pow_one] at hbase
        exact Nat.le_trans hq hbase
      omega
    }

/-- A hit at time at most `J` forces the least hit to be at most `J`. -/
theorem HitByTimePeriodic (p : Parameters) (J : ℕ)
    (hq : 1 ≤ p.Q.natAbs)
    (hA : p.Q.natAbs ^ J < p.D.natAbs)
    (h : ∀ n : ℤ, ∃ j : ℕ, j ≤ J ∧ IsFirstHit p n j) (n : ℤ) :
    let hE : EverySeedHits p := fun m => ⟨(h m).choose, (h m).choose_spec.2⟩
    (∃ j : ℕ,
        (Iterate (TotalReturn p hE) j n).natAbs ≤
          CoreRadius (MaxPow p.Q.natAbs J) (MaxOff p.Q p.C J)
            p.D.natAbs) ∧
      ∃ t per : ℕ, 0 < per ∧
        ∀ k : ℕ,
          Iterate (TotalReturn p hE) (t + k) n =
            Iterate (TotalReturn p hE) (t + k + per) n := by
  let hE : EverySeedHits p := fun m => ⟨(h m).choose, (h m).choose_spec.2⟩
  show
      (∃ j : ℕ,
          (Iterate (TotalReturn p hE) j n).natAbs ≤
            CoreRadius (MaxPow p.Q.natAbs J) (MaxOff p.Q p.C J)
              p.D.natAbs) ∧
        ∃ t per : ℕ, 0 < per ∧
          ∀ k : ℕ,
            Iterate (TotalReturn p hE) (t + k) n =
              Iterate (TotalReturn p hE) (t + k + per) n
  have hJ : ∀ m : ℤ, LeastHit p m (hE m) ≤ J := by
    intro m
    obtain ⟨j, hj, hhit⟩ := h m
    have hleast : LeastHit p m ⟨j, hhit⟩ ≤ j := Nat.find_le hhit
    have heq : LeastHit p m (hE m) = LeastHit p m ⟨j, hhit⟩ := by
      exact FirstHitUnique p m _ _
        (LeastHitIsFirst p m (hE m))
        (LeastHitIsFirst p m ⟨j, hhit⟩)
    omega
  have hpow : MaxPow p.Q.natAbs J < p.D.natAbs := by
    rw [MaxPowOfPos p.Q.natAbs J (by omega)]
    exact hA
  exact BoundedHitPeriodic p hE J hJ hpow n

/-- Adding a multiple of `D` does not change the affine state modulo `D`. -/
theorem AffineShiftDiv (q c n t d : ℤ) (j : ℕ) :
    AffineState q c j (n + t * d) =
      AffineState q c j n + q ^ j * t * d := by
  unfold AffineState
  ring

/-- A multiple of the divisor does not move the first hit. -/
theorem FirstHitAddMultiple (p : Parameters) (n t : ℤ) (j : ℕ) :
    IsFirstHit p n j ↔ IsFirstHit p (n + t * p.D) j := by
  have hshift : ∀ i : ℕ,
      AffineState p.Q p.C i (n + t * p.D) =
        AffineState p.Q p.C i n + p.Q ^ i * t * p.D :=
    fun i => AffineShiftDiv p.Q p.C n t p.D i
  have hmul : ∀ i : ℕ, p.D ∣ p.Q ^ i * t * p.D := by
    intro i
    refine ⟨p.Q ^ i * t, ?_⟩
    ring
  constructor
  · {
      intro h
      refine ⟨?_, ?_⟩
      · {
          rw [hshift]
          exact dvd_add h.1 (hmul j)
        }
      · {
          intro i hi hdiv
          apply h.2 i hi
          have hback :
              AffineState p.Q p.C i n =
                AffineState p.Q p.C i (n + t * p.D) -
                  p.Q ^ i * t * p.D := by
            rw [hshift]
            ring
          rw [hback]
          exact dvd_sub hdiv (hmul i)
        }
    }
  · {
      intro h
      refine ⟨?_, ?_⟩
      · {
          have hback :
              AffineState p.Q p.C j n =
                AffineState p.Q p.C j (n + t * p.D) -
                  p.Q ^ j * t * p.D := by
            rw [hshift]
            ring
          rw [hback]
          exact dvd_sub h.1 (hmul j)
        }
      · {
          intro i hi hdiv
          apply h.2 i hi
          rw [hshift]
          exact dvd_add hdiv (hmul i)
        }
    }

/-- A hit by time `J` on each residue `0,…,|D|-1` lifts to every integer. -/
theorem HitsByTimeOfRepresentatives (p : Parameters) (J : ℕ)
    (h : ∀ r : ℕ, r < p.D.natAbs →
      ∃ j : ℕ, j ≤ J ∧ IsFirstHit p (r : ℤ) j) (n : ℤ) :
    ∃ j : ℕ, j ≤ J ∧ IsFirstHit p n j := by
  have hd : 0 < p.D.natAbs := by
    have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
    omega
  let d : ℤ := p.D.natAbs
  have hdpos : 0 < d := by
    simpa [d] using (Int.ofNat_lt.mpr hd)
  have hdne : d ≠ 0 := by omega
  have hmod : n = n % d + d * (n / d) :=
    (Int.emod_add_mul_ediv n d).symm
  have hsq : p.D.sign * p.D.sign = 1 := by
    by_cases hpos : 0 ≤ p.D
    · {
        have hgt : 0 < p.D := by
          have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
          have hne : p.D ≠ 0 := by
            intro hz
            simp [hz] at htwo
          omega
        simp [Int.sign_eq_one_of_pos hgt]
      }
    · {
        simp [Int.sign_eq_neg_one_of_neg (by omega : p.D < 0)]
      }
  have hunit : p.D.sign * d = p.D := by
    simpa [d] using Int.sign_mul_natAbs p.D
  let s : ℤ := p.D.sign
  have hsqs : s * s = 1 := by
    simpa [s] using hsq
  have hunits : s * d = p.D := by
    simpa [s] using hunit
  obtain ⟨t, ht⟩ : ∃ t : ℤ, d * (n / d) = t * p.D := by
    refine ⟨s * (n / d), ?_⟩
    rw [show p.D = s * d from hunits.symm]
    have hre :
        s * (n / d) * (s * d) = (s * s) * (d * (n / d)) := by
      ring
    rw [hre, hsqs]
    ring
  have hr0 : 0 ≤ n % d := Int.emod_nonneg n hdne
  have hrlt : n % d < d := Int.emod_lt_of_pos n hdpos
  let r : ℕ := (n % d).toNat
  have hr : (r : ℤ) = n % d := Int.toNat_of_nonneg hr0
  have hrN : r < p.D.natAbs := by
    have hcast : (r : ℤ) < d := by
      rw [hr]
      exact hrlt
    simpa [d] using (Int.ofNat_lt.mp hcast)
  obtain ⟨j, hj, hhit⟩ := h r hrN
  have hn : n = (r : ℤ) + t * p.D := by
    rw [ht] at hmod
    rw [hmod, hr]
  refine ⟨j, hj, ?_⟩
  rw [hn]
  exact (FirstHitAddMultiple p (r : ℤ) t j).mp hhit

/-- For `Q = 1` and `gcd(|C|,|D|) = 1`, every seed hits by time `|D|`. -/
theorem UnitCoprimeHits (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    ∃ j : ℕ, j ≤ p.D.natAbs ∧ IsFirstHit p n j := by
  let d : ℕ := p.D.natAbs
  have hd : 2 ≤ d := p.DAdmissible
  have hpos : 0 < d := by omega
  haveI : NeZero d := ⟨by omega⟩
  have habs : IsUnit ((p.C.natAbs : ZMod d)) :=
    (ZMod.unitOfCoprime p.C.natAbs hcop).isUnit
  have hCne : p.C ≠ 0 := by
    intro h0
    have hgcd : Nat.gcd 0 d = d := Nat.gcd_zero_left d
    have hone : Nat.gcd p.C.natAbs d = 1 := hcop
    rw [h0, Int.natAbs_zero] at hone
    omega
  have hsign : p.C.sign = 1 ∨ p.C.sign = -1 := by
    by_cases hnn : 0 ≤ p.C
    · {
        left
        exact Int.sign_eq_one_of_pos (by omega : 0 < p.C)
      }
    · {
        right
        exact Int.sign_eq_neg_one_of_neg (by omega : p.C < 0)
      }
  have hC : p.C = p.C.sign * (p.C.natAbs : ℤ) :=
    (Int.sign_mul_natAbs p.C).symm
  have hCunit : IsUnit (p.C : ZMod d) := by
    rw [hC]
    rcases hsign with hs | hs
    · {
        rw [hs]
        simpa using habs
      }
    · {
        rw [hs]
        simpa using habs.neg
      }
  obtain ⟨u, hu⟩ := hCunit
  let j0 : ZMod d := ((u⁻¹ : (ZMod d)ˣ) : ZMod d) * -(n : ZMod d)
  have hj0 : (p.C : ZMod d) * j0 = -(n : ZMod d) := by
    have hinv : (u : ZMod d) * ((u⁻¹ : (ZMod d)ˣ) : ZMod d) = 1 := by
      rw [← Units.val_mul]
      simp
    calc
      (p.C : ZMod d) * j0
          = (u : ZMod d) *
              (((u⁻¹ : (ZMod d)ˣ) : ZMod d) * -(n : ZMod d)) := by
            rw [← hu]
      _ = ((u : ZMod d) * ((u⁻¹ : (ZMod d)ˣ) : ZMod d)) *
              -(n : ZMod d) := by
            ring
      _ = -(n : ZMod d) := by
            rw [hinv]
            simp
  let j : ℕ := j0.val
  have hjlt : j < d := ZMod.val_lt j0
  have hjcast : ((j : ℕ) : ZMod d) = j0 := ZMod.natCast_zmod_val j0
  have hsum : ((n + p.C * (j : ℤ) : ℤ) : ZMod d) = 0 := by
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, hjcast, hj0]
    simp
  have hdvd0 : (d : ℤ) ∣ n + p.C * (j : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (n + p.C * (j : ℤ)) d).1 hsum
  have hsq : p.D.sign * p.D.sign = 1 := by
    by_cases hnn : 0 ≤ p.D
    · {
        have hgt : 0 < p.D := by
          have hne : p.D ≠ 0 := by
            intro hz
            have hzero : d = 0 := by
              change p.D.natAbs = 0
              rw [hz]
              exact Int.natAbs_zero
            omega
          omega
        rw [Int.sign_eq_one_of_pos hgt]
        ring
      }
    · {
        rw [Int.sign_eq_neg_one_of_neg (by omega : p.D < 0)]
        ring
      }
  let s : ℤ := p.D.sign
  have hsqs : s * s = 1 := by simpa [s] using hsq
  have hunitD : s * (d : ℤ) = p.D := by
    simpa [s, d] using Int.sign_mul_natAbs p.D
  have hdvd : p.D ∣ n + p.C * (j : ℤ) := by
    obtain ⟨k, hk⟩ := hdvd0
    refine ⟨s * k, ?_⟩
    rw [hk, show (d : ℤ) = s * p.D by
      have hD : p.D = s * (d : ℤ) := hunitD.symm
      have hback : (d : ℤ) = s * p.D := by
        calc
          (d : ℤ) = (s * s) * (d : ℤ) := by rw [hsqs]; ring
          _ = s * (s * (d : ℤ)) := by ring
          _ = s * p.D := by rw [← hD]
      exact hback]
    ring
  have hstate : AffineState p.Q p.C j n = n + p.C * (j : ℤ) := by
    rw [hQ, AffineState, TrapSumOne]
    simp
  have hdivj : p.D ∣ AffineState p.Q p.C j n := by
    rw [hstate]
    exact hdvd
  classical
  let hex : ∃ i : ℕ, p.D ∣ AffineState p.Q p.C i n := ⟨j, hdivj⟩
  let i : ℕ := Nat.find hex
  have hi : p.D ∣ AffineState p.Q p.C i n := Nat.find_spec hex
  have hile : i ≤ j := Nat.find_le hdivj
  refine ⟨i, ?_, ?_⟩
  · {
      exact Nat.le_trans hile (Nat.le_of_lt hjlt)
    }
  · {
      refine ⟨hi, ?_⟩
      intro k hk hdk
      exact Nat.find_min _ hk hdk
    }

/-- For `Q = 1` and `gcd(|C|,|D|) = 1`, the total return enters the core. -/
theorem UnitCoprimePeriodic (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    let J := p.D.natAbs
    let h : ∀ m : ℤ, ∃ j : ℕ, j ≤ J ∧ IsFirstHit p m j :=
      fun m => UnitCoprimeHits p hQ hcop m
    let hE : EverySeedHits p := fun m => ⟨(h m).choose, (h m).choose_spec.2⟩
    (∃ j : ℕ,
        (Iterate (TotalReturn p hE) j n).natAbs ≤
          CoreRadius (MaxPow p.Q.natAbs J) (MaxOff p.Q p.C J)
            p.D.natAbs) ∧
      ∃ t per : ℕ, 0 < per ∧
        ∀ k : ℕ,
          Iterate (TotalReturn p hE) (t + k) n =
            Iterate (TotalReturn p hE) (t + k + per) n := by
  intro J h hE
  have hq : 1 ≤ p.Q.natAbs := by
    rw [hQ]
    decide
  have hA : p.Q.natAbs ^ J < p.D.natAbs := by
    have hone : p.Q.natAbs = 1 := by
      rw [hQ]
      rfl
    rw [hone, show J = p.D.natAbs from rfl, Nat.one_pow]
    exact Nat.lt_of_lt_of_le (by decide : 1 < 2) p.DAdmissible
  exact HitByTimePeriodic p J hq hA h n

/-- For `Q = 1`, a seed hits if and only if `gcd(|C|,|D|)` divides it. -/
theorem UnitHitsIffGcd (p : Parameters) (hQ : p.Q = 1) (n : ℤ) :
    (∃ j : ℕ, IsFirstHit p n j) ↔
      ((Nat.gcd p.C.natAbs p.D.natAbs : ℤ) ∣ n) := by
  let g : ℕ := Nat.gcd p.C.natAbs p.D.natAbs
  let d : ℕ := p.D.natAbs
  constructor
  · {
      intro hEx
      obtain ⟨j, hj⟩ := hEx
      have hdiv : p.D ∣ AffineState p.Q p.C j n := hj.1
      have hstate : AffineState p.Q p.C j n = n + p.C * (j : ℤ) := by
        rw [hQ, AffineState, TrapSumOne]
        simp
      rw [hstate] at hdiv
      have hgcdC : (g : ℤ) ∣ p.C := by
        have hnat : g ∣ p.C.natAbs := Nat.gcd_dvd_left _ _
        have hsign : p.C = p.C.sign * (p.C.natAbs : ℤ) :=
          (Int.sign_mul_natAbs p.C).symm
        rw [hsign]
        exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hnat) _
      have hgcdD : (g : ℤ) ∣ p.D := by
        have hnat : g ∣ d := by
          simpa [g, d] using Nat.gcd_dvd_right p.C.natAbs p.D.natAbs
        have hsign : p.D = p.D.sign * (d : ℤ) :=
          (Int.sign_mul_natAbs p.D).symm
        rw [hsign]
        exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hnat) _
      have hgj : (g : ℤ) ∣ p.C * (j : ℤ) := dvd_mul_of_dvd_left hgcdC _
      have hsum : (g : ℤ) ∣ n + p.C * (j : ℤ) := dvd_trans hgcdD hdiv
      obtain ⟨a, ha⟩ := hsum
      obtain ⟨b, hb⟩ := hgj
      refine ⟨a - b, ?_⟩
      have hn : n = (n + p.C * (j : ℤ)) - p.C * (j : ℤ) := by ring
      rw [hn, ha, hb, ← Int.mul_sub]
    }
  · {
      intro hgn
      obtain ⟨m, hm⟩ := hgn
      have hgint : p.C.gcd p.D = g := by
        simpa [g] using
          (Int.gcd_eq_natAbs :
            p.C.gcd p.D = Nat.gcd p.C.natAbs p.D.natAbs)
      have hxy : (g : ℤ) =
          p.C * p.C.gcdA p.D + p.D * p.C.gcdB p.D := by
        rw [← hgint]
        exact Int.gcd_eq_gcd_ab p.C p.D
      let t : ℤ := -(m * p.C.gcdA p.D)
      have hdivt : p.D ∣ n + p.C * t := by
        refine ⟨m * p.C.gcdB p.D, ?_⟩
        rw [hm, hxy]
        ring
      have hsq : p.D.sign * p.D.sign = 1 := by
        by_cases hpos : 0 ≤ p.D
        · {
            have hgt : 0 < p.D := by
              have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
              have hne : p.D ≠ 0 := by
                intro hz
                simp [hz] at htwo
              omega
            simp [Int.sign_eq_one_of_pos hgt]
          }
        · {
            simp [Int.sign_eq_neg_one_of_neg (by omega : p.D < 0)]
          }
      have hback : (d : ℤ) = p.D.sign * p.D := by
        have hD : p.D = p.D.sign * (d : ℤ) :=
          (Int.sign_mul_natAbs p.D).symm
        calc
          (d : ℤ) = (p.D.sign * p.D.sign) * (d : ℤ) := by rw [hsq]; ring
          _ = p.D.sign * (p.D.sign * (d : ℤ)) := by ring
          _ = p.D.sign * p.D := by rw [← hD]
      have hdpos : (0 : ℤ) < d := by
        have h2 : 2 ≤ d := p.DAdmissible
        omega
      let r : ℤ := t % (d : ℤ)
      have hr0 : 0 ≤ r := Int.emod_nonneg t (Int.ne_of_gt hdpos)
      have hsub : t - r = (d : ℤ) * (t / (d : ℤ)) := by
        have hsplit : r + (d : ℤ) * (t / (d : ℤ)) = t := by
          simpa [r] using Int.emod_add_mul_ediv t (d : ℤ)
        have hrew : t - r =
            (r + (d : ℤ) * (t / (d : ℤ))) - r := by rw [hsplit]
        rw [hrew]
        ring
      let j : ℕ := r.toNat
      have hrj : (j : ℤ) = r := Int.toNat_of_nonneg hr0
      have hDj : p.D ∣ n + p.C * (j : ℤ) := by
        have hDd : p.D ∣ (d : ℤ) := by
          refine ⟨p.D.sign, ?_⟩
          rw [hback]
          ring
        have hdiff : p.D ∣ p.C * ((j : ℤ) - t) := by
          have hmul : (j : ℤ) - t = -((d : ℤ) * (t / (d : ℤ))) := by
            rw [hrj]
            have hneg : r - t = -(t - r) := by ring
            rw [hneg, hsub]
          obtain ⟨s, hs⟩ := hDd
          refine ⟨-(p.C * ((t / (d : ℤ)) * s)), ?_⟩
          rw [hmul, hs]
          ring
        obtain ⟨k1, hk1⟩ := hdivt
        obtain ⟨k2, hk2⟩ := hdiff
        refine ⟨k1 + k2, ?_⟩
        have hsplitn : n + p.C * (j : ℤ) =
            (n + p.C * t) + p.C * ((j : ℤ) - t) := by ring
        rw [hsplitn, hk1, hk2]
        ring_nf
      have hdivj : p.D ∣ AffineState p.Q p.C j n := by
        rw [hQ, AffineState, TrapSumOne]
        simp
        exact hDj
      classical
      have hex : ∃ i : ℕ, p.D ∣ AffineState p.Q p.C i n := ⟨j, hdivj⟩
      let i : ℕ := Nat.find hex
      refine ⟨i, Nat.find_spec hex, ?_⟩
      intro k hk hdk
      exact Nat.find_min hex hk hdk
    }

/-- If the multiplier is coprime to the gcd, a hit forces that gcd to divide
the seed. The multiplier need not be `1`. -/
theorem HitForcesGcdDivides (p : Parameters) (n : ℤ) (j : ℕ)
    (hcop : Nat.Coprime p.Q.natAbs (Nat.gcd p.C.natAbs p.D.natAbs))
    (hj : IsFirstHit p n j) :
    (Nat.gcd p.C.natAbs p.D.natAbs : ℤ) ∣ n := by
  let g := Nat.gcd p.C.natAbs p.D.natAbs
  have hgcdC : (g : ℤ) ∣ p.C := by
    have hnat : g ∣ p.C.natAbs := Nat.gcd_dvd_left _ _
    rw [(Int.sign_mul_natAbs p.C).symm]
    exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hnat) _
  have hgcdD : (g : ℤ) ∣ p.D := by
    have hnat : g ∣ p.D.natAbs := by
      simpa [g] using Nat.gcd_dvd_right p.C.natAbs p.D.natAbs
    rw [(Int.sign_mul_natAbs p.D).symm]
    exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hnat) _
  have hgS : (g : ℤ) ∣ AffineState p.Q p.C j n :=
    dvd_trans hgcdD hj.1
  have hgC : (g : ℤ) ∣ p.C * TrapSum p.Q j :=
    dvd_mul_of_dvd_left hgcdC _
  have hqn : (g : ℤ) ∣ p.Q ^ j * n := by
    have hsub : p.Q ^ j * n =
        AffineState p.Q p.C j n - p.C * TrapSum p.Q j := by
      unfold AffineState
      ring
    rw [hsub]
    exact dvd_sub hgS hgC
  have hnat : g ∣ p.Q.natAbs ^ j * n.natAbs := by
    have hmul : g ∣ (p.Q ^ j * n).natAbs :=
      Int.natAbs_dvd_natAbs.mpr hqn
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hmul
  have hpow : Nat.Coprime (p.Q.natAbs ^ j) g := hcop.pow_left j
  have hdiv : g ∣ n.natAbs := hpow.symm.dvd_of_dvd_mul_left hnat
  rw [(Int.sign_mul_natAbs n).symm]
  exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hdiv) _

/-- The record `(2,2,2)`. Its gcd shares the factor `2` with the multiplier. -/
def SharedTwo : Parameters where
  Q := 2
  C := 2
  D := 2
  DAdmissible := by decide

/-- An odd seed of `(2,2,2)` hits at time `1`, so coprimeness cannot be
omitted from the necessity statement. -/
theorem SharedFactorHitMissesGcd :
    ¬ Nat.Coprime SharedTwo.Q.natAbs
        (Nat.gcd SharedTwo.C.natAbs SharedTwo.D.natAbs) ∧
      IsFirstHit SharedTwo (1 : ℤ) 1 ∧
      ¬ (Nat.gcd SharedTwo.C.natAbs SharedTwo.D.natAbs : ℤ) ∣ (1 : ℤ) := by
  refine ⟨?_, ?_, ?_⟩
  · {
      decide
    }
  · {
      unfold IsFirstHit
      constructor
      · {
          unfold AffineState
          have hU : TrapSum (2 : ℤ) 1 = 1 := by simp [TrapSum]
          simp [SharedTwo, hU]
        }
      · {
          intro i hi
          have hi0 : i = 0 := by omega
          subst hi0
          unfold AffineState
          simp [SharedTwo, TrapSum]
        }
    }
  · {
      decide
    }

/-- If `D` divides both coefficients, every seed hits at time `0` or `1`. -/
theorem DivisorOfBothHitsByOne (p : Parameters)
    (hQ : p.D ∣ p.Q) (hC : p.D ∣ p.C) (n : ℤ) :
    (p.D ∣ n ∧ IsFirstHit p n 0) ∨
      (¬ p.D ∣ n ∧ IsFirstHit p n 1) := by
  by_cases hdiv : p.D ∣ n
  · {
      exact Or.inl ⟨hdiv, (FirstHitZeroIff p n).mpr hdiv⟩
    }
  · {
      refine Or.inr ⟨hdiv, ?_⟩
      unfold IsFirstHit
      refine ⟨?_, ?_⟩
      · {
          unfold AffineState
          have hU : TrapSum p.Q 1 = 1 := by simp [TrapSum]
          rw [hU, mul_one, pow_one]
          exact dvd_add (dvd_mul_of_dvd_left hQ n) hC
        }
      · {
          intro i hi
          have hi0 : i = 0 := by omega
          subst hi0
          unfold AffineState
          simpa [TrapSum] using hdiv
        }
    }

/-- If `D` divides both coefficients, the return is one exact division. -/
theorem DivisorOfBothReturn (p : Parameters)
    (hQ : p.D ∣ p.Q) (hC : p.D ∣ p.C) (n : ℤ) :
    (p.D ∣ n ∧ RawStep p n = n / p.D) ∨
      (¬ p.D ∣ n ∧ RawStep p n = p.Q * n + p.C ∧
        RawStep p (RawStep p n) = (p.Q * n + p.C) / p.D) := by
  by_cases hdiv : p.D ∣ n
  · {
      refine Or.inl ⟨hdiv, ?_⟩
      rw [RawStep, if_pos hdiv]
    }
  · {
      have hstate : p.D ∣ p.Q * n + p.C :=
        dvd_add (dvd_mul_of_dvd_left hQ n) hC
      refine Or.inr ⟨hdiv, ?_, ?_⟩
      · {
          rw [RawStep, if_neg hdiv]
        }
      · {
          have hstep : RawStep p n = p.Q * n + p.C := by
            rw [RawStep, if_neg hdiv]
          rw [hstep, RawStep, if_pos hstate]
        }
    }

/-- An odd seed of `(2,2,2)` moves to `n + 1` in two raw steps. -/
theorem SharedTwoOddTwoStep (n : ℤ) (hnot : ¬ SharedTwo.D ∣ n) :
    Iterate (RawStep SharedTwo) 2 n = n + 1 := by
  have hstep : RawStep SharedTwo n = 2 * n + 2 := by
    rw [RawStep, if_neg hnot]
    simp [SharedTwo]
  have hdiv : SharedTwo.D ∣ 2 * n + 2 := by
    simp [SharedTwo]
  have hnext : RawStep SharedTwo (2 * n + 2) = n + 1 := by
    rw [RawStep, if_pos hdiv]
    simp [SharedTwo]
    have hfac : (2 * n + 2 : ℤ) = 2 * (n + 1) := by ring
    rw [hfac]
    exact Int.mul_ediv_cancel_left (n + 1) (by decide)
  simp [Iterate, hstep, hnext]

/-- An even seed of `(2,2,2)` is halved. -/
theorem SharedTwoEvenStep (n : ℤ) (hdiv : SharedTwo.D ∣ n) :
    RawStep SharedTwo n = n / 2 := by
  rw [RawStep, if_pos hdiv]
  simp [SharedTwo]

/-- The seed `1` cycles through `4` and `2`. -/
theorem SharedTwoCycle :
    RawStep SharedTwo 1 = 4 ∧ RawStep SharedTwo 4 = 2 ∧
      RawStep SharedTwo 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · {
      have hnot : ¬ SharedTwo.D ∣ (1 : ℤ) := by decide
      rw [RawStep, if_neg hnot]
      simp [SharedTwo]
    }
  · {
      have hdiv : SharedTwo.D ∣ (4 : ℤ) := by decide
      rw [SharedTwoEvenStep 4 hdiv]
      decide
    }
  · {
      have hdiv : SharedTwo.D ∣ (2 : ℤ) := by decide
      rw [SharedTwoEvenStep 2 hdiv]
      decide
    }

/-- Every positive seed of `(2,2,2)` reaches `1`. -/
theorem SharedTwoPositiveReachesOne (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, Iterate (RawStep SharedTwo) k (n : ℤ) = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    {
      by_cases h1 : n = 1
      · {
          subst h1
          exact ⟨0, by simp [Iterate]⟩
        }
      · {
          have hlt : 1 < n := by omega
          by_cases hdiv : SharedTwo.D ∣ (n : ℤ)
          · {
              have h2 : (2 : ℤ) ∣ (n : ℤ) := by simpa [SharedTwo] using hdiv
              have hnat : 2 ∣ n := Int.natCast_dvd_natCast.mp h2
              obtain ⟨m, hm⟩ := hnat
              have hmpos : 0 < m := by omega
              have hmlt : m < n := by omega
              obtain ⟨k, hk⟩ := ih m hmlt hmpos
              refine ⟨1 + k, ?_⟩
              have hstep := SharedTwoEvenStep (n : ℤ) hdiv
              have hquot : (n : ℤ) / 2 = m := by
                have hn2 : (n : ℤ) = 2 * m := by exact_mod_cast hm
                rw [hn2]
                exact Int.mul_ediv_cancel_left (m : ℤ) (by decide)
              have hbase :
                  Iterate (RawStep SharedTwo) (1 + k) (n : ℤ) =
                    Iterate (RawStep SharedTwo) k
                      (RawStep SharedTwo (n : ℤ)) := by
                rw [IterateAdd]
                simp [Iterate]
              rw [hbase, hstep, hquot]
              exact hk
            }
          · {
              have htwo := SharedTwoOddTwoStep (n : ℤ) hdiv
              have h2 : ¬ (2 : ℤ) ∣ (n : ℤ) := by simpa [SharedTwo] using hdiv
              have hmod : ((n : ℤ) + 1) % 2 = 0 := by
                rcases Int.emod_two_eq_zero_or_one (n : ℤ) with h0 | h1
                · {
                    exact False.elim
                      (h2 (Int.dvd_iff_emod_eq_zero.mpr h0))
                  }
                · {
                    rw [Int.add_emod, h1]
                    decide
                  }
              have hdvd : (2 : ℤ) ∣ (n : ℤ) + 1 :=
                Int.dvd_iff_emod_eq_zero.mpr hmod
              have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by
                omega
              have hdiv1 : SharedTwo.D ∣ ((n + 1 : ℕ) : ℤ) := by
                rw [hcast]
                simpa [SharedTwo] using hdvd
              let m : ℕ := (n + 1) / 2
              have hmpos : 0 < m := by omega
              have hmlt : m < n := by omega
              obtain ⟨k, hk⟩ := ih m hmlt hmpos
              have hhalf := SharedTwoEvenStep ((n + 1 : ℕ) : ℤ) hdiv1
              have hnat : 2 ∣ n + 1 := by
                have hcast2 : (2 : ℤ) ∣ ((n + 1 : ℕ) : ℤ) := by
                  rw [hcast]
                  exact hdvd
                exact Int.natCast_dvd_natCast.mp hcast2
              have hquot : ((n + 1 : ℕ) : ℤ) / 2 = m := by
                have hn2 : ((n + 1 : ℕ) : ℤ) = 2 * m := by
                  have hmul : n + 1 = m * 2 := by
                    dsimp [m]
                    exact (Nat.div_mul_cancel hnat).symm
                  exact_mod_cast hmul.trans (Nat.mul_comm m 2)
                rw [hn2]
                exact Int.mul_ediv_cancel_left (m : ℤ) (by decide)
              refine ⟨3 + k, ?_⟩
              rw [IterateAdd]
              have hthree :
                  Iterate (RawStep SharedTwo) 3 (n : ℤ) = (m : ℤ) := by
                have hrec :
                    Iterate (RawStep SharedTwo) 3 (n : ℤ) =
                      RawStep SharedTwo
                        (Iterate (RawStep SharedTwo) 2 (n : ℤ)) := by
                  simp [Iterate]
                rw [hrec, htwo, ← hcast, hhalf, hquot]
              rw [hthree]
              exact hk
            }
        }
    }

/-- A positive seed of `(2,2,2)` reaches `1` in at most `3(|n|-1)` steps. -/
theorem SharedTwoPositiveTime (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, k ≤ 3 * (n - 1) ∧
      Iterate (RawStep SharedTwo) k (n : ℤ) = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    {
      by_cases h1 : n = 1
      · {
          subst h1
          exact ⟨0, by omega, by simp [Iterate]⟩
        }
      · {
          have hlt : 1 < n := by omega
          by_cases hdiv : SharedTwo.D ∣ (n : ℤ)
          · {
              have h2 : (2 : ℤ) ∣ (n : ℤ) := by simpa [SharedTwo] using hdiv
              have hnat : 2 ∣ n := Int.natCast_dvd_natCast.mp h2
              obtain ⟨m, hm⟩ := hnat
              have hmpos : 0 < m := by omega
              have hmlt : m < n := by omega
              obtain ⟨k, hkle, hk⟩ := ih m hmlt hmpos
              refine ⟨1 + k, ?_, ?_⟩
              · {
                  have hmhalf : m ≤ n / 2 := by
                    have hmul : n = m * 2 := by
                      rw [hm]
                      exact Nat.mul_comm 2 m
                    omega
                  omega
                }
              · {
                  have hstep := SharedTwoEvenStep (n : ℤ) hdiv
                  have hquot : (n : ℤ) / 2 = m := by
                    have hn2 : (n : ℤ) = 2 * m := by exact_mod_cast hm
                    rw [hn2]
                    exact Int.mul_ediv_cancel_left (m : ℤ) (by decide)
                  rw [IterateAdd]
                  simp [Iterate, hstep, hquot]
                  exact hk
                }
            }
          · {
              have htwo := SharedTwoOddTwoStep (n : ℤ) hdiv
              have h2 : ¬ (2 : ℤ) ∣ (n : ℤ) := by simpa [SharedTwo] using hdiv
              have hmod : ((n : ℤ) + 1) % 2 = 0 := by
                rcases Int.emod_two_eq_zero_or_one (n : ℤ) with h0 | h1m
                · {
                    exact False.elim
                      (h2 (Int.dvd_iff_emod_eq_zero.mpr h0))
                  }
                · {
                    rw [Int.add_emod, h1m]
                    decide
                  }
              have hdvd : (2 : ℤ) ∣ (n : ℤ) + 1 :=
                Int.dvd_iff_emod_eq_zero.mpr hmod
              have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
              have hdiv1 : SharedTwo.D ∣ ((n + 1 : ℕ) : ℤ) := by
                rw [hcast]
                simpa [SharedTwo] using hdvd
              let m : ℕ := (n + 1) / 2
              have hmpos : 0 < m := by omega
              have hmlt : m < n := by omega
              obtain ⟨k, hkle, hk⟩ := ih m hmlt hmpos
              have hhalf := SharedTwoEvenStep ((n + 1 : ℕ) : ℤ) hdiv1
              have hnat1 : 2 ∣ n + 1 := by
                have hcast2 : (2 : ℤ) ∣ ((n + 1 : ℕ) : ℤ) := by
                  rw [hcast]
                  exact hdvd
                exact Int.natCast_dvd_natCast.mp hcast2
              have hquot : ((n + 1 : ℕ) : ℤ) / 2 = m := by
                have hn2 : ((n + 1 : ℕ) : ℤ) = 2 * m := by
                  have hmul : n + 1 = m * 2 := by
                    dsimp [m]
                    exact (Nat.div_mul_cancel hnat1).symm
                  exact_mod_cast hmul.trans (Nat.mul_comm m 2)
                rw [hn2]
                exact Int.mul_ediv_cancel_left (m : ℤ) (by decide)
              refine ⟨3 + k, ?_, ?_⟩
              · {
                  have hmhalf : 2 * m ≤ n + 1 := by
                    dsimp [m]
                    exact Nat.mul_div_le (n + 1) 2
                  omega
                }
              · {
                  rw [IterateAdd]
                  have hthree :
                      Iterate (RawStep SharedTwo) 3 (n : ℤ) = (m : ℤ) := by
                    have hrec :
                        Iterate (RawStep SharedTwo) 3 (n : ℤ) =
                          RawStep SharedTwo
                            (Iterate (RawStep SharedTwo) 2 (n : ℤ)) := by
                      simp [Iterate]
                    rw [hrec, htwo, ← hcast, hhalf, hquot]
                  rw [hthree]
                  exact hk
                }
            }
        }
    }

/-- The seed `-1` of `(2,2,2)` steps to `0`. -/
theorem SharedTwoNegOneStep : RawStep SharedTwo (-1) = 0 := by
  have hnot : ¬ SharedTwo.D ∣ (-1 : ℤ) := by decide
  rw [RawStep, if_neg hnot]
  simp [SharedTwo]

/-- Every negative seed of `(2,2,2)` reaches `0`. -/
theorem SharedTwoNegativeReachesZero (n : ℤ) (hn : n < 0) :
    ∃ k : ℕ, Iterate (RawStep SharedTwo) k n = 0 := by
  suffices hrec : ∀ N : ℕ, ∀ n : ℤ, n.natAbs = N → n < 0 →
      ∃ k : ℕ, Iterate (RawStep SharedTwo) k n = 0 by
    exact hrec n.natAbs n rfl hn
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    {
      intro n hN hn
      by_cases h1 : n = -1
      · {
          subst h1
          exact ⟨1, by simp [Iterate, SharedTwoNegOneStep]⟩
        }
      · {
          have hle : n ≤ -2 := by omega
          by_cases hdiv : SharedTwo.D ∣ n
          · {
              have hstep := SharedTwoEvenStep n hdiv
              have h2 : (2 : ℤ) ∣ n := by simpa [SharedTwo] using hdiv
              obtain ⟨m, hm⟩ := h2
              have hquot : n / 2 = m := by
                rw [hm]
                exact Int.mul_ediv_cancel_left m (by decide)
              have hmneg : m < 0 := by
                have hle' : 2 * m ≤ -2 := by rw [← hm]; exact hle
                omega
              have hneg : n / 2 < 0 := by rw [hquot]; exact hmneg
              have hsmall : (n / 2).natAbs < N := by
                rw [← hN, hquot, hm]
                have hnn : 0 ≤ -m := by omega
                have hnn2 : 0 ≤ -(2 * m) := by omega
                have habs : (m.natAbs : ℤ) = -m := by
                  rw [← Int.natAbs_neg]
                  exact Int.natAbs_of_nonneg hnn
                have htwo : ((2 * m).natAbs : ℤ) = -(2 * m) := by
                  rw [← Int.natAbs_neg]
                  exact Int.natAbs_of_nonneg hnn2
                have hpos : 0 < m.natAbs := by
                  have hne : m ≠ 0 := by omega
                  exact Nat.pos_of_ne_zero (by
                    intro hz
                    have : (m.natAbs : ℤ) = 0 := by exact_mod_cast hz
                    rw [habs] at this
                    omega)
                have hcast : ((2 * m).natAbs : ℤ) = 2 * (m.natAbs : ℤ) := by
                  rw [htwo, habs]
                  ring
                have hlt : (m.natAbs : ℤ) < 2 * (m.natAbs : ℤ) := by
                  omega
                have hcmp : m.natAbs < (2 * m).natAbs := by
                  exact_mod_cast (show (m.natAbs : ℤ) < ((2 * m).natAbs : ℤ) by
                    rw [hcast]
                    exact hlt)
                exact hcmp
              obtain ⟨k, hk⟩ :=
                ih (n / 2).natAbs hsmall (n / 2) rfl hneg
              refine ⟨1 + k, ?_⟩
              have hbase :
                  Iterate (RawStep SharedTwo) (1 + k) n =
                    Iterate (RawStep SharedTwo) k (RawStep SharedTwo n) := by
                rw [IterateAdd]
                simp [Iterate]
              rw [hbase, hstep]
              exact hk
            }
          · {
              have htwo := SharedTwoOddTwoStep n hdiv
              have hnext : n + 1 < 0 := by omega
              have hsmall : (n + 1).natAbs < N := by
                rw [← hN]
                have hnn : 0 ≤ -n := by omega
                have hnn1 : 0 ≤ -(n + 1) := by omega
                have habs : (n.natAbs : ℤ) = -n := by
                  rw [← Int.natAbs_neg]
                  exact Int.natAbs_of_nonneg hnn
                have hnextabs : ((n + 1).natAbs : ℤ) = -(n + 1) := by
                  rw [← Int.natAbs_neg]
                  exact Int.natAbs_of_nonneg hnn1
                have hcmp : (n + 1).natAbs + 1 = n.natAbs := by
                  have hcast :
                      ((n + 1).natAbs : ℤ) + 1 = (n.natAbs : ℤ) := by
                    rw [hnextabs, habs]
                    ring
                  exact_mod_cast hcast
                omega
              obtain ⟨k, hk⟩ := ih (n + 1).natAbs hsmall (n + 1) rfl hnext
              refine ⟨2 + k, ?_⟩
              rw [IterateAdd]
              have htwo' : Iterate (RawStep SharedTwo) 2 n = n + 1 := htwo
              rw [htwo']
              exact hk
            }
        }
    }

/-- A negative seed of `(2,2,2)` reaches `0` in at most `2|n|` steps. -/
theorem SharedTwoNegativeTime (n : ℤ) (hn : n < 0) :
    ∃ k : ℕ, k ≤ 2 * n.natAbs ∧
      Iterate (RawStep SharedTwo) k n = 0 := by
  suffices hrec : ∀ N : ℕ, ∀ n : ℤ, n.natAbs = N → n < 0 →
      ∃ k : ℕ, k ≤ 2 * N ∧ Iterate (RawStep SharedTwo) k n = 0 by
    exact hrec n.natAbs n rfl hn
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    {
      intro n hN hn
      by_cases h1 : n = -1
      · {
          subst h1
          refine ⟨1, ?_, by simp [Iterate, SharedTwoNegOneStep]⟩
          have hN1 : N = 1 := by
            have habs : ((-1 : ℤ).natAbs) = 1 := by decide
            rw [← hN, habs]
          omega
        }
      · {
          have hle : n ≤ -2 := by omega
          by_cases hdiv : SharedTwo.D ∣ n
          · {
              have hstep := SharedTwoEvenStep n hdiv
              have h2 : (2 : ℤ) ∣ n := by simpa [SharedTwo] using hdiv
              obtain ⟨m, hm⟩ := h2
              have hquot : n / 2 = m := by
                rw [hm]
                exact Int.mul_ediv_cancel_left m (by decide)
              have hmneg : m < 0 := by
                have hle' : 2 * m ≤ -2 := by rw [← hm]; exact hle
                omega
              have hneg : n / 2 < 0 := by rw [hquot]; exact hmneg
              have hsmall : (n / 2).natAbs < N := by
                rw [← hN, hquot, hm]
                have hnn : 0 ≤ -m := by omega
                have hnn2 : 0 ≤ -(2 * m) := by omega
                have habs : (m.natAbs : ℤ) = -m := by
                  rw [← Int.natAbs_neg]
                  exact Int.natAbs_of_nonneg hnn
                have htwo : ((2 * m).natAbs : ℤ) = -(2 * m) := by
                  rw [← Int.natAbs_neg]
                  exact Int.natAbs_of_nonneg hnn2
                have hcast : ((2 * m).natAbs : ℤ) = 2 * (m.natAbs : ℤ) := by
                  rw [htwo, habs]
                  ring
                have hlt : (m.natAbs : ℤ) < 2 * (m.natAbs : ℤ) := by omega
                exact_mod_cast (show (m.natAbs : ℤ) < ((2 * m).natAbs : ℤ) by
                  rw [hcast]
                  exact hlt)
              obtain ⟨k, hkle, hk⟩ :=
                ih (n / 2).natAbs hsmall (n / 2) rfl hneg
              refine ⟨1 + k, ?_, ?_⟩
              · {
                  have hltN : (n / 2).natAbs ≤ N - 1 := by omega
                  omega
                }
              · {
                  rw [IterateAdd]
                  simp [Iterate, hstep]
                  exact hk
                }
            }
          · {
              have htwo := SharedTwoOddTwoStep n hdiv
              have hnext : n + 1 < 0 := by omega
              have hsmall : (n + 1).natAbs < N := by
                rw [← hN]
                have hnn : 0 ≤ -n := by omega
                have hnn1 : 0 ≤ -(n + 1) := by omega
                have habs : (n.natAbs : ℤ) = -n := by
                  rw [← Int.natAbs_neg]
                  exact Int.natAbs_of_nonneg hnn
                have hnextabs : ((n + 1).natAbs : ℤ) = -(n + 1) := by
                  rw [← Int.natAbs_neg]
                  exact Int.natAbs_of_nonneg hnn1
                have hcmp : (n + 1).natAbs + 1 = n.natAbs := by
                  have hcast :
                      ((n + 1).natAbs : ℤ) + 1 = (n.natAbs : ℤ) := by
                    rw [hnextabs, habs]
                    ring
                  exact_mod_cast hcast
                omega
              obtain ⟨k, hkle, hk⟩ :=
                ih (n + 1).natAbs hsmall (n + 1) rfl hnext
              refine ⟨2 + k, ?_, ?_⟩
              · {
                  have hltN : (n + 1).natAbs ≤ N - 1 := by omega
                  omega
                }
              · {
                  rw [IterateAdd, htwo]
                  exact hk
                }
            }
        }
    }

/-- Every seed of `(2,2,2)` enters `{0,1,2,4}` within `3|n|` steps. -/
theorem SharedTwoEntry (n : ℤ) :
    ∃ k : ℕ, k ≤ 3 * n.natAbs ∧
      (Iterate (RawStep SharedTwo) k n = 0 ∨
        Iterate (RawStep SharedTwo) k n = 1 ∨
        Iterate (RawStep SharedTwo) k n = 2 ∨
        Iterate (RawStep SharedTwo) k n = 4) := by
  by_cases hpos : 0 < n
  · {
      obtain ⟨k, hkle, hk⟩ :=
        SharedTwoPositiveTime n.natAbs (Int.natAbs_pos.mpr (by omega))
      have hcast : (n.natAbs : ℤ) = n :=
        Int.natAbs_of_nonneg (by omega)
      refine ⟨k, ?_, Or.inr (Or.inl (by rw [← hcast]; exact hk))⟩
      omega
    }
  · {
      by_cases hzero : n = 0
      · {
          refine ⟨0, by omega, Or.inl ?_⟩
          simp [Iterate, hzero]
        }
      · {
          have hneg : n < 0 := by omega
          obtain ⟨k, hkle, hk⟩ := SharedTwoNegativeTime n hneg
          refine ⟨k, ?_, Or.inl hk⟩
          omega
        }
    }

/-- A fixed point has a constant orbit. -/
theorem SharedTwoZeroOrbit (k : ℕ) :
    Iterate (RawStep SharedTwo) k 0 = 0 := by
  induction k with
  | zero => {
      simp [Iterate]
    }
  | succ k ih => {
      rw [Iterate, ih]
      have hdiv : SharedTwo.D ∣ (0 : ℤ) := by decide
      rw [SharedTwoEvenStep 0 hdiv]
      decide
    }

/-- Repeating a period returns to the seed. -/
theorem SharedTwoPeriodRepeat (n : ℤ) (p t : ℕ)
    (hper : Iterate (RawStep SharedTwo) p n = n) :
    Iterate (RawStep SharedTwo) (t * p) n = n := by
  induction t with
  | zero => {
      simp [Iterate]
    }
  | succ t ih => {
      rw [Nat.succ_mul, IterateAdd, ih, hper]
    }

/-- The periodic seeds of `(2,2,2)` are `0`, `1`, `2`, and `4`. -/
theorem SharedTwoPeriodic (n : ℤ) :
    (∃ p : ℕ, 0 < p ∧ Iterate (RawStep SharedTwo) p n = n) ↔
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 := by
  constructor
  · {
      intro hper
      obtain ⟨p, hp, hret⟩ := hper
      by_cases hpos : 0 < n
      · {
          obtain ⟨m, hm⟩ := SharedTwoPositiveReachesOne n.natAbs
            (Int.natAbs_pos.mpr (by omega))
          have hcast : (n.natAbs : ℤ) = n :=
            Int.natAbs_of_nonneg (by omega)
          rw [hcast] at hm
          have hbig : m ≤ m * p := by
            have hmp : m * 1 ≤ m * p := Nat.mul_le_mul_left m hp
            simpa using hmp
          have hback :
              Iterate (RawStep SharedTwo) (m * p - m) 1 = n := by
            have hsplit :
                Iterate (RawStep SharedTwo) (m * p) n =
                  Iterate (RawStep SharedTwo) (m * p - m)
                    (Iterate (RawStep SharedTwo) m n) := by
              have hsum : m + (m * p - m) = m * p :=
                Nat.add_sub_of_le hbig
              conv_lhs => rw [← hsum]
              exact IterateAdd (RawStep SharedTwo) m (m * p - m) n
            rw [hm] at hsplit
            have hrep := SharedTwoPeriodRepeat n p m hret
            rw [hrep] at hsplit
            exact hsplit.symm
          have hmem : n = 1 ∨ n = 2 ∨ n = 4 := by
            have htail : ∀ j : ℕ,
                Iterate (RawStep SharedTwo) j 1 = 1 ∨
                Iterate (RawStep SharedTwo) j 1 = 4 ∨
                Iterate (RawStep SharedTwo) j 1 = 2 := by
              intro j
              induction j with
              | zero => {
                  simp [Iterate]
                }
              | succ j ihj => {
                  rw [Iterate]
                  rcases ihj with h1 | h4 | h2
                  · {
                      rw [h1, (SharedTwoCycle).1]
                      exact Or.inr (Or.inl rfl)
                    }
                  · {
                      rw [h4, (SharedTwoCycle).2.1]
                      exact Or.inr (Or.inr rfl)
                    }
                  · {
                      rw [h2, (SharedTwoCycle).2.2]
                      exact Or.inl rfl
                    }
                }
            rcases htail (m * p - m) with h1 | h4 | h2
            · {
                rw [← hback, h1]
                exact Or.inl rfl
              }
            · {
                rw [← hback, h4]
                exact Or.inr (Or.inr rfl)
              }
            · {
                rw [← hback, h2]
                exact Or.inr (Or.inl rfl)
              }
          rcases hmem with h1 | h2 | h4
          · {
              exact Or.inr (Or.inl h1)
            }
          · {
              exact Or.inr (Or.inr (Or.inl h2))
            }
          · {
              exact Or.inr (Or.inr (Or.inr h4))
            }
        }
      · {
          by_cases hzero : n = 0
          · {
              exact Or.inl hzero
            }
          · {
              have hneg : n < 0 := by omega
              obtain ⟨m, hm⟩ := SharedTwoNegativeReachesZero n hneg
              have hbig : m ≤ m * p := by
                have hmp : m * 1 ≤ m * p := Nat.mul_le_mul_left m hp
                simpa using hmp
              have hback :
                  Iterate (RawStep SharedTwo) (m * p - m) 0 = n := by
                have hsplit :
                    Iterate (RawStep SharedTwo) (m * p) n =
                      Iterate (RawStep SharedTwo) (m * p - m)
                        (Iterate (RawStep SharedTwo) m n) := by
                  have hsum : m + (m * p - m) = m * p :=
                    Nat.add_sub_of_le hbig
                  conv_lhs => rw [← hsum]
                  exact IterateAdd (RawStep SharedTwo) m
                    (m * p - m) n
                rw [hm] at hsplit
                have hrep := SharedTwoPeriodRepeat n p m hret
                rw [hrep] at hsplit
                exact hsplit.symm
              have hzero : n = 0 := by
                rw [← hback]
                exact SharedTwoZeroOrbit (m * p - m)
              exact absurd hzero (ne_of_lt hneg)
            }
        }
    }
  · {
      intro hmem
      rcases hmem with h0 | h1 | h2 | h4
      · {
          refine ⟨1, by omega, ?_⟩
          rw [h0]
          simp [Iterate]
          have hdiv : SharedTwo.D ∣ (0 : ℤ) := by decide
          rw [SharedTwoEvenStep 0 hdiv]
          decide
        }
      · {
          refine ⟨3, by omega, ?_⟩
          rw [h1]
          have h1s : Iterate (RawStep SharedTwo) 1 (1 : ℤ) = 4 := by
            simp [Iterate, (SharedTwoCycle).1]
          have h2s : Iterate (RawStep SharedTwo) 2 (1 : ℤ) = 2 := by
            rw [Iterate, h1s, (SharedTwoCycle).2.1]
          rw [Iterate, h2s, (SharedTwoCycle).2.2]
        }
      · {
          refine ⟨3, by omega, ?_⟩
          rw [h2]
          have h1s : Iterate (RawStep SharedTwo) 1 (2 : ℤ) = 1 := by
            simp [Iterate, (SharedTwoCycle).2.2]
          have h2s : Iterate (RawStep SharedTwo) 2 (2 : ℤ) = 4 := by
            rw [Iterate, h1s, (SharedTwoCycle).1]
          rw [Iterate, h2s, (SharedTwoCycle).2.1]
        }
      · {
          refine ⟨3, by omega, ?_⟩
          rw [h4]
          have h1s : Iterate (RawStep SharedTwo) 1 (4 : ℤ) = 2 := by
            simp [Iterate, (SharedTwoCycle).2.1]
          have h2s : Iterate (RawStep SharedTwo) 2 (4 : ℤ) = 1 := by
            rw [Iterate, h1s, (SharedTwoCycle).2.2]
          rw [Iterate, h2s, (SharedTwoCycle).1]
        }
    }

/-- The seed `0` of `(2,2,2)` is fixed. -/
theorem SharedTwoZero : RawStep SharedTwo 0 = 0 := by
  have hdiv : SharedTwo.D ∣ (0 : ℤ) := by decide
  rw [SharedTwoEvenStep 0 hdiv]
  decide

/-- For `Q = 1`, every seed hits if and only if the gcd is `1`. -/
theorem UnitEverySeedIffCoprime (p : Parameters) (hQ : p.Q = 1) :
    (∀ n : ℤ, ∃ j : ℕ, IsFirstHit p n j) ↔
      Nat.gcd p.C.natAbs p.D.natAbs = 1 := by
  constructor
  · {
      intro h
      have hdiv := (UnitHitsIffGcd p hQ 1).1 (h 1)
      have hnat : Nat.gcd p.C.natAbs p.D.natAbs ∣ 1 := by
        exact Int.natCast_dvd_natCast.mp hdiv
      exact Nat.dvd_one.mp hnat
    }
  · {
      intro hg n
      have hdiv : (Nat.gcd p.C.natAbs p.D.natAbs : ℤ) ∣ n := by
        rw [hg]
        exact one_dvd n
      exact (UnitHitsIffGcd p hQ n).2 hdiv
    }

/-- On a seed already divisible by `D`, time zero is the first hit and the
quotient obeys the core comparison with slope `1` and constant `0`. The
quantifier is that seed. It is not every integer, since `D` misses `1`. -/
theorem PureDivisionBound (p : Parameters) (n : ℤ) (hdiv : p.D ∣ n) :
    IsFirstHit p n 0 ∧
      p.D.natAbs * (n / p.D).natAbs ≤ 1 * n.natAbs + 0 ∧
      1 < p.D.natAbs := by
  have hhit : IsFirstHit p n 0 := (FirstHitZeroIff p n).mpr hdiv
  have heq : p.D.natAbs * (n / p.D).natAbs = n.natAbs :=
    NatAbsExactDiv p.D n hdiv
  have hle : p.D.natAbs * (n / p.D).natAbs ≤ 1 * n.natAbs + 0 := by
    rw [heq, Nat.one_mul, Nat.add_zero]
  have hlt : 1 < p.D.natAbs := by
    have hstep : 1 < 2 := Nat.lt_succ_self 1
    exact Nat.lt_of_lt_of_le hstep p.DAdmissible
  exact ⟨hhit, hle, hlt⟩

/-- For a divisible seed, the least hit supplied by that existence proof is
time zero, so the return is ordinary division. -/
theorem LeastHitOfDivisible (p : Parameters) (n : ℤ) (hdiv : p.D ∣ n) :
    LeastHit p n ⟨0, (FirstHitZeroIff p n).mpr hdiv⟩ = 0 := by
  exact Nat.eq_zero_of_le_zero
    (Nat.find_min' ⟨0, (FirstHitZeroIff p n).mpr hdiv⟩
      ((FirstHitZeroIff p n).mpr hdiv))

/-- The time-zero quotient of a divisible seed is the ordinary quotient. -/
theorem PureDivisionQuotient (p : Parameters) (n : ℤ) (_ : p.D ∣ n) :
    AffineState p.Q p.C 0 n / p.D = n / p.D := by
  rw [AffineStateZero p.Q p.C n]

/-- The unit power is one at every exponent. -/
theorem IntOnePow (j : ℕ) : (1 : ℤ) ^ j = 1 := by
  induction j with
  | zero => {
      exact Int.pow_zero 1
    }
  | succ j ih => {
      rw [Int.pow_succ, ih]
      exact mul_one 1
    }

/-- Multiplier `1` and offset `0` leave every affine state equal to the seed. -/
def UnitFrozen : Parameters where
  Q := 1
  C := 0
  D := 2
  DAdmissible := by
    decide

/-- The frozen unit record fixes the seed `1`. -/
theorem UnitFrozenState (j : ℕ) : AffineState 1 0 j 1 = 1 := by
  unfold AffineState
  rw [IntOnePow j]
  ring

/-- Multiplier `1` and offset `0` miss the odd seed `1` at every time. -/
theorem UnitFrozenMisses (j : ℕ) : ¬ IsFirstHit UnitFrozen 1 j := by
  intro h
  have hdiv : UnitFrozen.D ∣ AffineState UnitFrozen.Q UnitFrozen.C j 1 := h.1
  have hD : UnitFrozen.D = 2 := rfl
  have hQ : UnitFrozen.Q = 1 := rfl
  have hC : UnitFrozen.C = 0 := rfl
  rw [hD, hQ, hC] at hdiv
  rw [UnitFrozenState j] at hdiv
  exact PureDivisionMissesOne UnitFrozen hdiv

/-- `|Q| = 1` does not by itself make every seed hit. -/
theorem UnitFrozenNotEvery : ¬ EverySeedHits UnitFrozen := by
  intro hall
  obtain ⟨j, hj⟩ := hall 1
  exact UnitFrozenMisses j hj

/-- The multiplier `2`, offset `1`, and divisor `2`. Odds are a closed class. -/
def OddTranslation : Parameters where
  Q := 2
  C := 1
  D := 2
  DAdmissible := by
    decide

/-- The offset sum at multiplier `2` is one less than the power. -/
theorem TrapSumTwo (j : ℕ) : TrapSum 2 j = (2 : ℤ) ^ j - 1 := by
  have h := TrapSumMulSubOne (2 : ℤ) j
  have hcoef : (2 : ℤ) - 1 = 1 := by ring
  rw [hcoef, Int.one_mul] at h
  exact h

/-- The odd translation sends `1` to one less than a positive power of two. -/
theorem OddTranslationState (j : ℕ) :
    AffineState 2 1 j 1 = (2 : ℤ) ^ (j + 1) - 1 := by
  unfold AffineState
  rw [TrapSumTwo j]
  have hstep :
      (2 : ℤ) ^ j * 1 + 1 * ((2 : ℤ) ^ j - 1) = (2 : ℤ) ^ j * 2 - 1 := by
    ring
  rw [hstep]
  have hpow : (2 : ℤ) ^ j * 2 = (2 : ℤ) ^ (j + 1) := by
    rw [Int.pow_succ]
  rw [hpow]

/-- Two does not divide one less than a positive power of two. -/
theorem TwoNotDivPowSubOne (k : ℕ) (hk : 1 ≤ k) :
    ¬ (2 : ℤ) ∣ (2 : ℤ) ^ k - 1 := by
  intro hdvd
  have hsplit : (k - 1) + 1 = k := Nat.sub_add_cancel hk
  have hpow : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
    conv_lhs => rw [← hsplit]
    rw [Int.pow_succ, mul_comm]
  have heven : (2 : ℤ) ∣ (2 : ℤ) ^ k := by
    rw [hpow]
    exact Int.dvd_mul_right 2 ((2 : ℤ) ^ (k - 1))
  have hdiff : (2 : ℤ) ∣ (2 : ℤ) ^ k - ((2 : ℤ) ^ k - 1) :=
    Int.dvd_sub heven hdvd
  have hring : (2 : ℤ) ^ k - ((2 : ℤ) ^ k - 1) = 1 := by ring
  rw [hring] at hdiff
  have hnat : (2 : ℤ).natAbs ∣ (1 : ℤ).natAbs :=
    (Int.natAbs_dvd_natAbs).mpr hdiff
  have htwo : (2 : ℤ).natAbs = 2 := Int.natAbs_natCast 2
  have hone : (1 : ℤ).natAbs = 1 := Int.natAbs_natCast 1
  rw [htwo, hone] at hnat
  have heq : (2 : ℕ) = 1 := (Nat.dvd_one).mp hnat
  omega

/-- The odd class of `OddTranslation` has no first hit at any time. -/
theorem OddTranslationAvoids (j : ℕ) : ¬ IsFirstHit OddTranslation 1 j := by
  intro h
  have hdiv : OddTranslation.D ∣
      AffineState OddTranslation.Q OddTranslation.C j 1 := h.1
  have hD : OddTranslation.D = 2 := rfl
  have hQ : OddTranslation.Q = 2 := rfl
  have hC : OddTranslation.C = 1 := rfl
  rw [hD, hQ, hC] at hdiv
  rw [OddTranslationState j] at hdiv
  exact TwoNotDivPowSubOne (j + 1) (by omega) hdiv

/-- `|Q| = 2` does not yield a first hit of every seed. -/
theorem OddTranslationNotEvery :
    2 ≤ OddTranslation.Q.natAbs ∧ ¬ EverySeedHits OddTranslation := by
  refine ⟨?_, ?_⟩
  · {
      have hq : OddTranslation.Q = 2 := rfl
      rw [hq]
      decide
    }
  · {
      intro hall
      obtain ⟨j, hj⟩ := hall 1
      exact OddTranslationAvoids j hj
    }

/-- Every seed hits when the multiplier is `1` and the offset is coprime to the divisor. -/
theorem TwoEvery (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) : EverySeedHits p :=
  fun n => ⟨(UnitCoprimeHits p hQ hcop n).choose,
    (UnitCoprimeHits p hQ hcop n).choose_spec.2⟩

/-- At time one the unit affine state is the seed plus the offset. -/
theorem TwoAffineOne (c n : ℤ) : AffineState 1 c 1 n = n + c := by
  unfold AffineState
  rw [Int.one_pow, TrapSumOne, Int.one_mul]
  ring

/-- Two odd integers sum to an even integer. -/
theorem TwoOddSum (a b : ℤ) (ha : ¬ (2 : ℤ) ∣ a) (hb : ¬ (2 : ℤ) ∣ b) :
    (2 : ℤ) ∣ a + b := by
  have ha1 : a % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one a with h0 | h1
    · {
        exact False.elim
          (ha ((Int.dvd_iff_emod_eq_zero (a := (2 : ℤ)) (b := a)).2 h0))
      }
    · {
        exact h1
      }
  have hb1 : b % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one b with h0 | h1
    · {
        exact False.elim
          (hb ((Int.dvd_iff_emod_eq_zero (a := (2 : ℤ)) (b := b)).2 h0))
      }
    · {
        exact h1
      }
  have hsum : (a + b) % 2 = 0 := by
    rw [Int.add_emod, ha1, hb1]
    decide
  exact (Int.dvd_iff_emod_eq_zero (a := (2 : ℤ)) (b := a + b)).2 hsum

/-- A positive odd offset is not divisible by `2`. -/
theorem TwoOffsetOdd (p : Parameters) (hD : p.D = 2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) : ¬ p.D ∣ p.C := by
  intro hd
  obtain ⟨k, hk⟩ := hd
  rw [hD] at hk
  have hnat : p.C.natAbs = 2 * k.natAbs := by
    rw [hk, Int.natAbs_mul]
    rfl
  have hgcd : 2 ∣ Nat.gcd p.C.natAbs 2 := by
    refine Nat.dvd_gcd ?_ (Nat.dvd_refl 2)
    exact ⟨k.natAbs, hnat⟩
  have hone : Nat.gcd p.C.natAbs 2 = 1 := by
    simpa [hD] using hcop
  rw [hone] at hgcd
  omega

/-- An even seed returns by exact division by `2`. -/
theorem TwoFormulaEven (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hdiv : (2 : ℤ) ∣ n) :
    TotalReturn p (TwoEvery p hQ hcop) n = n / 2 := by
  have hDdiv : p.D ∣ n := by
    rwa [hD]
  have hhit0 : IsFirstHit p n 0 := (FirstHitZeroIff p n).mpr hDdiv
  have hleast : LeastHit p n (TwoEvery p hQ hcop n) = 0 := by
    unfold LeastHit
    exact Nat.eq_zero_of_le_zero
      (Nat.find_min' (TwoEvery p hQ hcop n) hhit0)
  unfold TotalReturn
  rw [hleast, PureDivisionQuotient p n hDdiv, hD]

/-- An odd seed returns by one affine step and one exact division. -/
theorem TwoFormulaOdd (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hdiv : ¬ (2 : ℤ) ∣ n) :
    TotalReturn p (TwoEvery p hQ hcop) n = (n + p.C) / 2 := by
  have hoddC : ¬ (2 : ℤ) ∣ p.C := by
    simpa [hD] using TwoOffsetOdd p hD hcop
  have hsum : p.D ∣ n + p.C := by
    rw [hD]
    exact TwoOddSum n p.C hdiv hoddC
  have hstate : AffineState p.Q p.C 1 n = n + p.C := by
    rw [hQ]
    exact TwoAffineOne p.C n
  have hhit : IsFirstHit p n 1 := by
    refine ⟨?_, ?_⟩
    · {
        rw [hstate]
        exact hsum
      }
    · {
        intro i hi hdi
        have hiz : i = 0 := by omega
        rw [hiz, AffineStateZero] at hdi
        exact hdiv (by rwa [← hD])
      }
  have hle : LeastHit p n (TwoEvery p hQ hcop n) ≤ 1 :=
    Nat.find_le hhit
  have hne : LeastHit p n (TwoEvery p hQ hcop n) ≠ 0 := by
    intro h0
    have hhit0 : IsFirstHit p n 0 := by
      rw [← h0]
      exact Nat.find_spec (TwoEvery p hQ hcop n)
    exact hdiv (by
      have hdiv0 : p.D ∣ n := (FirstHitZeroIff p n).1 hhit0
      rwa [hD] at hdiv0)
  have hleast : LeastHit p n (TwoEvery p hQ hcop n) = 1 := by
    omega
  unfold TotalReturn
  rw [hleast, hstate, hD]

/-- Zero is fixed: the divisor `2` divides it and the quotient is zero. -/
theorem TwoReturnZero (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) :
    TotalReturn p (TwoEvery p hQ hcop) 0 = 0 := by
  have hdiv : (2 : ℤ) ∣ 0 := ⟨0, by ring⟩
  rw [TwoFormulaEven p hQ hD hcop 0 hdiv]
  rfl

/-- A positive odd offset is fixed by one affine step. -/
theorem TwoReturnOffset (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (_hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) :
    TotalReturn p (TwoEvery p hQ hcop) p.C = p.C := by
  have hdiv : ¬ (2 : ℤ) ∣ p.C := by
    simpa [hD] using TwoOffsetOdd p hD hcop
  rw [TwoFormulaOdd p hQ hD hcop p.C hdiv]
  have hfac : p.C + p.C = (2 : ℤ) * p.C := by ring
  rw [hfac]
  exact Int.mul_ediv_cancel_left p.C (by decide)

/-- The interval from `0` through `c` is closed under the return. -/
theorem TwoShell (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (_hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (n : ℤ) (hn0 : 0 ≤ n) (hnC : n ≤ p.C) :
    0 ≤ TotalReturn p (TwoEvery p hQ hcop) n ∧
      TotalReturn p (TwoEvery p hQ hcop) n ≤ p.C := by
  classical
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      rw [TwoFormulaEven p hQ hD hcop n hdiv]
      have hmul : (2 : ℤ) * (n / 2) = n := Int.mul_ediv_cancel' hdiv
      omega
    }
  · {
      have hoddC : ¬ (2 : ℤ) ∣ p.C := by
        simpa [hD] using TwoOffsetOdd p hD hcop
      rw [TwoFormulaOdd p hQ hD hcop n hdiv]
      have hsum : (2 : ℤ) ∣ n + p.C := TwoOddSum n p.C hdiv hoddC
      have hmul : (2 : ℤ) * ((n + p.C) / 2) = n + p.C :=
        Int.mul_ediv_cancel' hsum
      omega
    }

/-- A positive seed strictly below `c` returns to that open interval. -/
theorem TwoInterior (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (_hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (n : ℤ) (hn0 : 0 < n) (hnC : n < p.C) :
    0 < TotalReturn p (TwoEvery p hQ hcop) n ∧
      TotalReturn p (TwoEvery p hQ hcop) n < p.C := by
  classical
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      rw [TwoFormulaEven p hQ hD hcop n hdiv]
      have hmul : (2 : ℤ) * (n / 2) = n := Int.mul_ediv_cancel' hdiv
      omega
    }
  · {
      have hoddC : ¬ (2 : ℤ) ∣ p.C := by
        simpa [hD] using TwoOffsetOdd p hD hcop
      rw [TwoFormulaOdd p hQ hD hcop n hdiv]
      have hsum : (2 : ℤ) ∣ n + p.C := TwoOddSum n p.C hdiv hoddC
      have hmul : (2 : ℤ) * ((n + p.C) / 2) = n + p.C :=
        Int.mul_ediv_cancel' hsum
      omega
    }

/-- Above `c`, one return is nonnegative and strictly smaller. -/
theorem TwoDropsAbove (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (_hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (n : ℤ) (hn : p.C < n) :
    0 ≤ TotalReturn p (TwoEvery p hQ hcop) n ∧
      TotalReturn p (TwoEvery p hQ hcop) n < n := by
  classical
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      rw [TwoFormulaEven p hQ hD hcop n hdiv]
      have hmul : (2 : ℤ) * (n / 2) = n := Int.mul_ediv_cancel' hdiv
      omega
    }
  · {
      have hoddC : ¬ (2 : ℤ) ∣ p.C := by
        simpa [hD] using TwoOffsetOdd p hD hcop
      rw [TwoFormulaOdd p hQ hD hcop n hdiv]
      have hsum : (2 : ℤ) ∣ n + p.C := TwoOddSum n p.C hdiv hoddC
      have hmul : (2 : ℤ) * ((n + p.C) / 2) = n + p.C :=
        Int.mul_ediv_cancel' hsum
      omega
    }

/-- A negative seed either enters the shell or loses absolute value. -/
theorem TwoNegativeStep (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (n : ℤ) (hn : n < 0) :
    (0 ≤ TotalReturn p (TwoEvery p hQ hcop) n ∧
        TotalReturn p (TwoEvery p hQ hcop) n ≤ p.C) ∨
      (TotalReturn p (TwoEvery p hQ hcop) n).natAbs < n.natAbs := by
  classical
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      right
      rw [TwoFormulaEven p hQ hD hcop n hdiv]
      have hmul : (2 : ℤ) * (n / 2) = n := Int.mul_ediv_cancel' hdiv
      have habs : n.natAbs = 2 * (n / 2).natAbs := by
        have hrewrite : n.natAbs = (2 * (n / 2)).natAbs :=
          (congrArg Int.natAbs hmul).symm
        rw [hrewrite, Int.natAbs_mul]
        have h2 : (2 : ℤ).natAbs = 2 := by decide
        rw [h2]
      omega
    }
  · {
      have hoddC : ¬ (2 : ℤ) ∣ p.C := by
        simpa [hD] using TwoOffsetOdd p hD hcop
      rw [TwoFormulaOdd p hQ hD hcop n hdiv]
      have hsum : (2 : ℤ) ∣ n + p.C := TwoOddSum n p.C hdiv hoddC
      have hmul : (2 : ℤ) * ((n + p.C) / 2) = n + p.C :=
        Int.mul_ediv_cancel' hsum
      by_cases hq : 0 ≤ (n + p.C) / 2
      · {
          left
          omega
        }
      · {
          right
          have hqneg : (n + p.C) / 2 < 0 := by omega
          have hnegsum : n + p.C < 0 := by omega
          have hnabs : (n.natAbs : ℤ) = -n := by
            rw [← Int.natAbs_neg n]
            exact Int.natAbs_of_nonneg (by omega : 0 ≤ -n)
          have hcabs : (p.C.natAbs : ℤ) = p.C :=
            Int.natAbs_of_nonneg (le_of_lt hpos)
          have hqabs : (((n + p.C) / 2).natAbs : ℤ) =
              -((n + p.C) / 2) := by
            rw [← Int.natAbs_neg ((n + p.C) / 2)]
            exact Int.natAbs_of_nonneg
              (by omega : 0 ≤ -((n + p.C) / 2))
          have hdiff : (2 : ℤ) * (((n + p.C) / 2).natAbs : ℤ) =
              (n.natAbs : ℤ) - (p.C.natAbs : ℤ) := by
            rw [hqabs, hnabs, hcabs]
            have hneg : (2 : ℤ) * -((n + p.C) / 2) =
                -(2 * ((n + p.C) / 2)) := by ring
            rw [hneg, hmul]
            ring
          have hltZ : (((n + p.C) / 2).natAbs : ℤ) <
              (n.natAbs : ℤ) := by
            omega
          exact_mod_cast hltZ
        }
    }

/-- Every seed reaches the shell `0 ≤ x ≤ c`. -/
theorem TwoEnters (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (x : ℤ) :
    ∃ t : ℕ, 0 ≤ Iterate (TotalReturn p (TwoEvery p hQ hcop)) t x ∧
      Iterate (TotalReturn p (TwoEvery p hQ hcop)) t x ≤ p.C := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  suffices ∀ m : ℕ, ∀ x : ℤ, x.natAbs = m →
      ∃ t : ℕ, 0 ≤ Iterate R t x ∧ Iterate R t x ≤ p.C by
    exact this x.natAbs x rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    {
      intro x hm
      by_cases hx0 : 0 ≤ x
      · {
          by_cases hxC : x ≤ p.C
          · {
              exact ⟨0, by simpa [Iterate] using ⟨hx0, hxC⟩⟩
            }
          · {
              have habove : p.C < x := by omega
              have hdrop := TwoDropsAbove p hQ hD hpos hcop x habove
              have hlt : (R x).natAbs < m := by
                have hR : ((R x).natAbs : ℤ) = R x := by
                  simpa [R] using Int.natAbs_of_nonneg hdrop.1
                have hx : (x.natAbs : ℤ) = x :=
                  Int.natAbs_of_nonneg hx0
                have hZ : ((R x).natAbs : ℤ) < (x.natAbs : ℤ) := by
                  rw [hR, hx]
                  simpa [R] using hdrop.2
                have hnat : (R x).natAbs < x.natAbs := by exact_mod_cast hZ
                rwa [hm] at hnat
              obtain ⟨t, ht⟩ := ih (R x).natAbs hlt (R x) rfl
              refine ⟨t + 1, ?_⟩
              have hidx : 1 + t = t + 1 := by omega
              rw [← hidx, IterateAdd]
              simpa [Iterate] using ht
            }
        }
      · {
          have hxneg : x < 0 := by omega
          rcases TwoNegativeStep p hQ hD hpos hcop x hxneg with hshell | hlt
          · {
              exact ⟨1, by simpa [Iterate] using hshell⟩
            }
          · {
              have hltm : (R x).natAbs < m := by
                simpa [R, hm] using hlt
              obtain ⟨t, ht⟩ := ih (R x).natAbs hltm (R x) rfl
              refine ⟨t + 1, ?_⟩
              have hidx : 1 + t = t + 1 := by omega
              rw [← hidx, IterateAdd]
              simpa [Iterate] using ht
            }
        }
    }

/-- A shell seed begins a period of length at most `max(c - 1, 1)`. -/
theorem TwoPositivePeriod (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    let R := TotalReturn p (TwoEvery p hQ hcop)
    ∃ t per : ℕ, 0 < per ∧ per ≤ max (p.C.natAbs - 1) 1 ∧
      ∀ k : ℕ, Iterate R (t + k) n = Iterate R (t + k + per) n := by
  intro R
  obtain ⟨t0, ht0, htC⟩ := TwoEnters p hQ hD hpos hcop n
  set y := Iterate R t0 n
  by_cases hy0 : y = 0
  · {
      refine ⟨t0, 1, by decide, Nat.le_max_right _ _, ?_⟩
      intro k
      have hfix : ∀ j, Iterate R (t0 + j) n = 0 := by
        intro j
        induction j with
        | zero => {
            simpa [Iterate, y] using hy0
          }
        | succ j ih => {
            have hidx : t0 + (j + 1) = (t0 + j) + 1 := by omega
            rw [hidx, Iterate, ih]
            simpa [R] using TwoReturnZero p hQ hD hcop
          }
      have hk := hfix k
      have hk1 := hfix (k + 1)
      have hidx : t0 + (k + 1) = t0 + k + 1 := by omega
      rw [hk, ← hidx, hk1]
    }
  · {
      by_cases hyC : y = p.C
      · {
          refine ⟨t0, 1, by decide, Nat.le_max_right _ _, ?_⟩
          intro k
          have hfix : ∀ j, Iterate R (t0 + j) n = p.C := by
            intro j
            induction j with
            | zero => {
                simpa [Iterate, y] using hyC
              }
            | succ j ih => {
                have hidx : t0 + (j + 1) = (t0 + j) + 1 := by omega
                rw [hidx, Iterate, ih]
                simpa [R] using TwoReturnOffset p hQ hD hpos hcop
              }
          have hk := hfix k
          have hk1 := hfix (k + 1)
          have hidx : t0 + (k + 1) = t0 + k + 1 := by omega
          rw [hk, ← hidx, hk1]
        }
      · {
          have hyopen0 : 0 < y := by omega
          have hyopenC : y < p.C := by omega
          have hinter : ∀ j, 0 < Iterate R j y ∧ Iterate R j y < p.C := by
            intro j
            induction j with
            | zero => {
                simpa [Iterate] using ⟨hyopen0, hyopenC⟩
              }
            | succ j ih => {
                simpa [Iterate] using
                  TwoInterior p hQ hD hpos hcop (Iterate R j y) ih.1 ih.2
              }
          let s := p.C.natAbs
          have hs : (s : ℤ) = p.C :=
            Int.natAbs_of_nonneg (le_of_lt hpos)
          have hs2 : 2 ≤ s := by
            have h1 : (1 : ℤ) < (s : ℤ) := by
              rw [hs]
              exact lt_of_le_of_lt (by omega : (1 : ℤ) ≤ y) hyopenC
            exact_mod_cast (by omega : (1 : ℕ) < s)
          let f : Fin s → Fin (s - 1) := fun i =>
            ⟨(Iterate R i.val y).toNat - 1, by
              have hi := hinter i.val
              have hnn : 0 ≤ Iterate R i.val y := le_of_lt hi.1
              have hto : ((Iterate R i.val y).toNat : ℤ) =
                  Iterate R i.val y := Int.toNat_of_nonneg hnn
              have hup : (Iterate R i.val y).toNat < s := by
                have : ((Iterate R i.val y).toNat : ℤ) < (s : ℤ) := by
                  rw [hto, hs]
                  exact hi.2
                exact_mod_cast this
              have hlo : 1 ≤ (Iterate R i.val y).toNat := by
                have : (1 : ℤ) ≤ ((Iterate R i.val y).toNat : ℤ) := by
                  rw [hto]
                  omega
                exact_mod_cast this
              omega⟩
          have hcard : Fintype.card (Fin (s - 1)) < Fintype.card (Fin s) := by
            simp [Fintype.card_fin]
            omega
          obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
          have hval : Iterate R a.val y = Iterate R b.val y := by
            have hfin : (Iterate R a.val y).toNat - 1 =
                (Iterate R b.val y).toNat - 1 := by
              simpa [f] using congrArg Fin.val heq
            have htoa : ((Iterate R a.val y).toNat : ℤ) =
                Iterate R a.val y :=
              Int.toNat_of_nonneg (le_of_lt (hinter a.val).1)
            have htob : ((Iterate R b.val y).toNat : ℤ) =
                Iterate R b.val y :=
              Int.toNat_of_nonneg (le_of_lt (hinter b.val).1)
            have hloa : 1 ≤ (Iterate R a.val y).toNat := by
              have hge : (1 : ℤ) ≤ Iterate R a.val y :=
                (Int.add_one_le_iff).mpr (hinter a.val).1
              have : (1 : ℤ) ≤ ((Iterate R a.val y).toNat : ℤ) := by
                rw [htoa]
                simpa using hge
              exact_mod_cast this
            have hlob : 1 ≤ (Iterate R b.val y).toNat := by
              have hge : (1 : ℤ) ≤ Iterate R b.val y :=
                (Int.add_one_le_iff).mpr (hinter b.val).1
              have : (1 : ℤ) ≤ ((Iterate R b.val y).toNat : ℤ) := by
                rw [htob]
                simpa using hge
              exact_mod_cast this
            have hnat : (Iterate R a.val y).toNat =
                (Iterate R b.val y).toNat := by
              omega
            rw [← htoa, ← htob]
            exact_mod_cast hnat
          have hperiod : ∀ u v : ℕ, u < v → Iterate R u y = Iterate R v y →
              ∀ k, Iterate R (t0 + u + k) n =
                Iterate R (t0 + u + k + (v - u)) n := by
            intro u v huv horbit k
            have hshift : Iterate R (u + k) y = Iterate R (v + k) y := by
              induction k with
              | zero => {
                  simpa [Iterate] using horbit
                }
              | succ k ih => {
                  have hL : u + (k + 1) = (u + k) + 1 := by omega
                  have hRgt : v + (k + 1) = (v + k) + 1 := by omega
                  rw [hL, hRgt]
                  simp [Iterate, ih]
                }
            have hleft : Iterate R (t0 + u + k) n =
                Iterate R (u + k) y := by
              rw [show t0 + u + k = t0 + (u + k) by omega, IterateAdd]
            have hright : Iterate R (v + k) y =
                Iterate R (t0 + (v + k)) n := by
              rw [← IterateAdd]
            have hidx : t0 + (v + k) =
                t0 + u + k + (v - u) := by omega
            calc
              Iterate R (t0 + u + k) n = Iterate R (u + k) y := hleft
              _ = Iterate R (v + k) y := hshift
              _ = Iterate R (t0 + (v + k)) n := hright
              _ = Iterate R (t0 + u + k + (v - u)) n := by rw [hidx]
          rcases Nat.lt_trichotomy a.val b.val with hlt | heqv | hgt
          · {
              refine ⟨t0 + a.val, b.val - a.val, Nat.sub_pos_of_lt hlt, ?_,
                hperiod a.val b.val hlt hval⟩
              have hle : b.val - a.val ≤ s - 1 := by
                have hb : b.val ≤ s - 1 := Nat.le_pred_of_lt b.isLt
                omega
              exact le_trans hle (Nat.le_max_left _ _)
            }
          · {
              exact False.elim (hne (Fin.ext heqv))
            }
          · {
              refine ⟨t0 + b.val, a.val - b.val, Nat.sub_pos_of_lt hgt, ?_,
                hperiod b.val a.val hgt hval.symm⟩
              have hle : a.val - b.val ≤ s - 1 := by
                have ha : a.val ≤ s - 1 := Nat.le_pred_of_lt a.isLt
                omega
              exact le_trans hle (Nat.le_max_left _ _)
            }
        }
    }

/-- The parameters `(1, 3, 2)`. -/
def TwoThree : Parameters where
  Q := 1
  C := 3
  D := 2
  DAdmissible := by
    decide

/-- The return of `(1, 3, 2)` swaps `1` and `2`, so the bound `c - 1` is achieved. -/
theorem TwoThreeCycle :
    let R := TotalReturn TwoThree (TwoEvery TwoThree rfl (by decide))
    R 1 = 2 ∧ R 2 = 1 := by
  intro R
  have h1 : ¬ (2 : ℤ) ∣ 1 := by decide
  have h2 : (2 : ℤ) ∣ 2 := ⟨1, by decide⟩
  constructor
  · {
      dsimp [R]
      rw [TwoFormulaOdd TwoThree rfl rfl (by decide) 1 h1]
      decide
    }
  · {
      dsimp [R]
      rw [TwoFormulaEven TwoThree rfl rfl (by decide) 2 h2]
      decide
    }

/-- Interior seeds with the same return are equal. -/
theorem TwoInteriorInjective (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = 2) (_hpos : 0 < p.C)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (x y : ℤ)
    (hx0 : 0 < x) (hxC : x < p.C) (hy0 : 0 < y) (hyC : y < p.C)
    (heq : TotalReturn p (TwoEvery p hQ hcop) x =
      TotalReturn p (TwoEvery p hQ hcop) y) : x = y := by
  by_cases hx : (2 : ℤ) ∣ x
  · {
      by_cases hy : (2 : ℤ) ∣ y
      · {
          rw [TwoFormulaEven p hQ hD hcop x hx,
            TwoFormulaEven p hQ hD hcop y hy] at heq
          have hx2 : (2 : ℤ) * (x / 2) = x := Int.mul_ediv_cancel' hx
          have hy2 : (2 : ℤ) * (y / 2) = y := Int.mul_ediv_cancel' hy
          have hmul := congrArg (fun z : ℤ => (2 : ℤ) * z) heq
          rw [hx2, hy2] at hmul
          exact hmul
        }
      · {
          rw [TwoFormulaEven p hQ hD hcop x hx,
            TwoFormulaOdd p hQ hD hcop y hy] at heq
          have hx2 : (2 : ℤ) * (x / 2) = x := Int.mul_ediv_cancel' hx
          have hoddC : ¬ (2 : ℤ) ∣ p.C := by
            simpa [hD] using TwoOffsetOdd p hD hcop
          have hsum : (2 : ℤ) ∣ y + p.C := by
            exact TwoOddSum y p.C hy hoddC
          have hy2 : (2 : ℤ) * ((y + p.C) / 2) = y + p.C :=
            Int.mul_ediv_cancel' hsum
          have hmul := congrArg (fun z : ℤ => (2 : ℤ) * z) heq
          rw [hx2, hy2] at hmul
          have hgt : p.C < x := by omega
          exact False.elim (not_lt_of_ge (le_of_lt hgt) hxC)
        }
    }
  · {
      by_cases hy : (2 : ℤ) ∣ y
      · {
          rw [TwoFormulaOdd p hQ hD hcop x hx,
            TwoFormulaEven p hQ hD hcop y hy] at heq
          have hy2 : (2 : ℤ) * (y / 2) = y := Int.mul_ediv_cancel' hy
          have hsum : (2 : ℤ) ∣ x + p.C := by
            have hDsum : p.D ∣ x + p.C := by
              have hoddC : ¬ (2 : ℤ) ∣ p.C := by
                simpa [hD] using TwoOffsetOdd p hD hcop
              rw [hD]
              exact TwoOddSum x p.C hx hoddC
            rwa [hD] at hDsum
          have hx2 : (2 : ℤ) * ((x + p.C) / 2) = x + p.C :=
            Int.mul_ediv_cancel' hsum
          have hmul := congrArg (fun z : ℤ => (2 : ℤ) * z) heq
          rw [hx2, hy2] at hmul
          have hgt : p.C < y := by omega
          exact False.elim (not_lt_of_ge (le_of_lt hgt) hyC)
        }
      · {
          rw [TwoFormulaOdd p hQ hD hcop x hx,
            TwoFormulaOdd p hQ hD hcop y hy] at heq
          have hoddC : ¬ (2 : ℤ) ∣ p.C := by
            simpa [hD] using TwoOffsetOdd p hD hcop
          have hxsum : (2 : ℤ) ∣ x + p.C := by
            rw [← hD]
            rw [hD]
            exact TwoOddSum x p.C hx hoddC
          have hysum : (2 : ℤ) ∣ y + p.C := by
            rw [← hD, hD]
            exact TwoOddSum y p.C hy hoddC
          have hx2 : (2 : ℤ) * ((x + p.C) / 2) = x + p.C :=
            Int.mul_ediv_cancel' hxsum
          have hy2 : (2 : ℤ) * ((y + p.C) / 2) = y + p.C :=
            Int.mul_ediv_cancel' hysum
          have hmul := congrArg (fun z : ℤ => (2 : ℤ) * z) heq
          rw [hx2, hy2] at hmul
          omega
        }
    }

/-- An interior seed is periodic, with period at most `|c| - 1`. -/
theorem TwoInteriorPeriodic (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = 2) (hpos : 0 < p.C)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hn0 : 0 < n) (hnC : n < p.C) :
    let R := TotalReturn p (TwoEvery p hQ hcop)
    ∃ t : ℕ, 0 < t ∧ t ≤ p.C.natAbs - 1 ∧
      ∀ k : ℕ, Iterate R (k + t) n = Iterate R k n := by
  intro R
  have hstay : ∀ j, 0 < Iterate R j n ∧ Iterate R j n < p.C := by
    intro j
    induction j with
    | zero => {
        simpa [Iterate] using ⟨hn0, hnC⟩
      }
    | succ j ih => {
        simpa [Iterate] using
          TwoInterior p hQ hD hpos hcop (Iterate R j n) ih.1 ih.2
      }
  have hpull : ∀ i j,
      Iterate R (i + 1) n = Iterate R (j + 1) n →
        Iterate R i n = Iterate R j n := by
    intro i j heq
    exact TwoInteriorInjective p hQ hD hpos hcop
      (Iterate R i n) (Iterate R j n)
      (hstay i).1 (hstay i).2 (hstay j).1 (hstay j).2
      (by simpa [Iterate] using heq)
  let s := p.C.natAbs
  have hs : (s : ℤ) = p.C :=
    Int.natAbs_of_nonneg (le_of_lt hpos)
  have hs2 : 2 ≤ s := by
    have h1 : (1 : ℤ) < (s : ℤ) := by
      rw [hs]
      exact lt_of_le_of_lt (by omega : (1 : ℤ) ≤ n) hnC
    exact_mod_cast (by omega : (1 : ℕ) < s)
  let f : Fin s → Fin (s - 1) := fun i =>
    ⟨(Iterate R i.val n).toNat - 1, by
      have hi := hstay i.val
      have hnn : 0 ≤ Iterate R i.val n := le_of_lt hi.1
      have hto : ((Iterate R i.val n).toNat : ℤ) =
          Iterate R i.val n := Int.toNat_of_nonneg hnn
      have hup : (Iterate R i.val n).toNat < s := by
        have : ((Iterate R i.val n).toNat : ℤ) < (s : ℤ) := by
          rw [hto, hs]
          exact hi.2
        exact_mod_cast this
      have hlo : 1 ≤ (Iterate R i.val n).toNat := by
        have : (1 : ℤ) ≤ ((Iterate R i.val n).toNat : ℤ) := by
          rw [hto]
          omega
        exact_mod_cast this
      omega⟩
  have hcard : Fintype.card (Fin (s - 1)) < Fintype.card (Fin s) := by
    simp [Fintype.card_fin]
    omega
  obtain ⟨a, b, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hval : Iterate R a.val n = Iterate R b.val n := by
    have hfin : (Iterate R a.val n).toNat - 1 =
        (Iterate R b.val n).toNat - 1 := by
      simpa [f] using congrArg Fin.val heq
    have htoa : ((Iterate R a.val n).toNat : ℤ) =
        Iterate R a.val n :=
      Int.toNat_of_nonneg (le_of_lt (hstay a.val).1)
    have htob : ((Iterate R b.val n).toNat : ℤ) =
        Iterate R b.val n :=
      Int.toNat_of_nonneg (le_of_lt (hstay b.val).1)
    have hloa : 1 ≤ (Iterate R a.val n).toNat := by
      have : (1 : ℤ) ≤ Iterate R a.val n :=
        (Int.add_one_le_iff).2 (hstay a.val).1
      have hcast1 : (1 : ℤ) ≤ ((Iterate R a.val n).toNat : ℤ) := by
        rw [htoa]
        exact this
      exact_mod_cast hcast1
    have hlob : 1 ≤ (Iterate R b.val n).toNat := by
      have : (1 : ℤ) ≤ Iterate R b.val n :=
        (Int.add_one_le_iff).2 (hstay b.val).1
      have hcast1 : (1 : ℤ) ≤ ((Iterate R b.val n).toNat : ℤ) := by
        rw [htob]
        exact this
      exact_mod_cast hcast1
    have hcast : (Iterate R a.val n).toNat =
        (Iterate R b.val n).toNat := by
      omega
    rw [← htoa, ← htob, hcast]
  have hfrom (u v : ℕ) (huv : u < v)
      (hcoll : Iterate R u n = Iterate R v n) :
      ∀ k : ℕ, Iterate R (k + (v - u)) n = Iterate R k n := by
    have hdown : ∀ m, m ≤ u →
        Iterate R (u - m) n = Iterate R (v - m) n := by
      intro m hm
      induction m with
      | zero => {
          simpa using hcoll
        }
      | succ m ih => {
          have hm' : m ≤ u := Nat.le_of_succ_le hm
          have ih' := ih hm'
          have hAu : u - m = (u - (m + 1)) + 1 := by omega
          have hAv : v - m = (v - (m + 1)) + 1 := by omega
          rw [hAu, hAv] at ih'
          exact hpull (u - (m + 1)) (v - (m + 1)) ih'
        }
    have hbase : n = Iterate R (v - u) n := by
      have h0 := hdown u le_rfl
      simpa [Iterate] using h0
    intro k
    induction k with
    | zero => {
        simpa [Iterate, Nat.zero_add] using hbase.symm
      }
    | succ k ih => {
        have hL : (k + 1) + (v - u) = (k + (v - u)) + 1 := by
          omega
        rw [hL]
        simp [Iterate, ih]
      }
  rcases Nat.lt_trichotomy a.val b.val with hlt | heqv | hgt
  · {
      refine ⟨b.val - a.val, ?_, ?_, ?_⟩
      · {
          omega
        }
      · {
          have hb : b.val < s := b.isLt
          omega
        }
      · {
          exact hfrom a.val b.val hlt hval
        }
    }
  · {
      exact False.elim (hne (Fin.ext heqv))
    }
  · {
      have hrev : Iterate R b.val n = Iterate R a.val n := hval.symm
      refine ⟨a.val - b.val, ?_, ?_, ?_⟩
      · {
          omega
        }
      · {
          have ha : a.val < s := a.isLt
          omega
        }
      · {
          exact hfrom b.val a.val hgt hrev
        }
    }

/-- The parameters `(1, 5, 2)`. -/
def TwoFive : Parameters where
  Q := 1
  C := 5
  D := 2
  DAdmissible := by
    decide

/-- Offset `5` has one interior cycle of length `4`, so the bound is achieved. -/
theorem TwoFiveCycle :
    let R := TotalReturn TwoFive (TwoEvery TwoFive rfl (by decide))
    R 1 = 3 ∧ R 3 = 4 ∧ R 4 = 2 ∧ R 2 = 1 := by
  intro R
  have h1 : ¬ (2 : ℤ) ∣ 1 := by decide
  have h3 : ¬ (2 : ℤ) ∣ 3 := by decide
  have h2 : (2 : ℤ) ∣ 2 := ⟨1, by decide⟩
  have h4 : (2 : ℤ) ∣ 4 := ⟨2, by decide⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · {
      dsimp [R]
      rw [TwoFormulaOdd TwoFive rfl rfl (by decide) 1 h1]
      decide
    }
  · {
      dsimp [R]
      rw [TwoFormulaOdd TwoFive rfl rfl (by decide) 3 h3]
      decide
    }
  · {
      dsimp [R]
      rw [TwoFormulaEven TwoFive rfl rfl (by decide) 4 h4]
      decide
    }
  · {
      dsimp [R]
      rw [TwoFormulaEven TwoFive rfl rfl (by decide) 2 h2]
      decide
    }

/-- The parameters `(1, 7, 2)`. -/
def TwoSeven : Parameters where
  Q := 1
  C := 7
  D := 2
  DAdmissible := by
    decide

/-- Offset `7` splits into two cycles of length `3`, so length `6` does not occur. -/
theorem TwoSevenCycles :
    let R := TotalReturn TwoSeven (TwoEvery TwoSeven rfl (by decide))
    (R 1 = 4 ∧ R 4 = 2 ∧ R 2 = 1) ∧
      (R 3 = 5 ∧ R 5 = 6 ∧ R 6 = 3) := by
  intro R
  have h1 : ¬ (2 : ℤ) ∣ 1 := by decide
  have h3 : ¬ (2 : ℤ) ∣ 3 := by decide
  have h5 : ¬ (2 : ℤ) ∣ 5 := by decide
  have h2 : (2 : ℤ) ∣ 2 := ⟨1, by decide⟩
  have h4 : (2 : ℤ) ∣ 4 := ⟨2, by decide⟩
  have h6 : (2 : ℤ) ∣ 6 := ⟨3, by decide⟩
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · {
      dsimp [R]
      rw [TwoFormulaOdd TwoSeven rfl rfl (by decide) 1 h1]
      decide
    }
  · {
      dsimp [R]
      rw [TwoFormulaEven TwoSeven rfl rfl (by decide) 4 h4]
      decide
    }
  · {
      dsimp [R]
      rw [TwoFormulaEven TwoSeven rfl rfl (by decide) 2 h2]
      decide
    }
  · {
      dsimp [R]
      rw [TwoFormulaOdd TwoSeven rfl rfl (by decide) 3 h3]
      decide
    }
  · {
      dsimp [R]
      rw [TwoFormulaOdd TwoSeven rfl rfl (by decide) 5 h5]
      decide
    }
  · {
      dsimp [R]
      rw [TwoFormulaEven TwoSeven rfl rfl (by decide) 6 h6]
      decide
    }

/-- Below half the offset, the even double is the interior preimage. -/
theorem TwoInverseBelow (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (_hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (m : ℤ)
    (hm0 : 0 < m) (_hmC : m < p.C) (hlow : (2 : ℤ) * m < p.C) :
    0 < (2 : ℤ) * m ∧ (2 : ℤ) * m < p.C ∧
      TotalReturn p (TwoEvery p hQ hcop) ((2 : ℤ) * m) = m := by
  refine ⟨by omega, hlow, ?_⟩
  have hdiv : (2 : ℤ) ∣ (2 : ℤ) * m := ⟨m, rfl⟩
  rw [TwoFormulaEven p hQ hD hcop ((2 : ℤ) * m) hdiv]
  exact Int.mul_ediv_cancel_left m (by decide)

/-- Above half the offset, `2m - c` is the odd interior preimage. -/
theorem TwoInverseAbove (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (_hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (m : ℤ)
    (_hm0 : 0 < m) (hmC : m < p.C) (hhigh : p.C < (2 : ℤ) * m) :
    let x := (2 : ℤ) * m - p.C
    0 < x ∧ x < p.C ∧
      TotalReturn p (TwoEvery p hQ hcop) x = m := by
  intro x
  have hx0 : 0 < x := by
    dsimp [x]
    omega
  have hxC : x < p.C := by
    dsimp [x]
    omega
  have hoddC : ¬ (2 : ℤ) ∣ p.C := by
    simpa [hD] using TwoOffsetOdd p hD hcop
  have hdiv : ¬ (2 : ℤ) ∣ x := by
    dsimp [x]
    intro h
    have htwo : (2 : ℤ) ∣ (2 : ℤ) * m := ⟨m, rfl⟩
    have hc : (2 : ℤ) ∣ p.C := by
      have hsub : p.C = (2 : ℤ) * m - x := by
        dsimp [x]
        ring
      rw [hsub]
      exact Int.dvd_sub htwo h
    exact hoddC hc
  refine ⟨hx0, hxC, ?_⟩
  rw [TwoFormulaOdd p hQ hD hcop x hdiv]
  have hsum : x + p.C = (2 : ℤ) * m := by
    dsimp [x]
    ring
  rw [hsum]
  exact Int.mul_ediv_cancel_left m (by decide)

/-- An interior seed returning to `m` is the preimage named by the half comparison. -/
theorem TwoInverseUnique (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (x m : ℤ) (hx0 : 0 < x) (hxC : x < p.C) (hm0 : 0 < m) (hmC : m < p.C)
    (heq : TotalReturn p (TwoEvery p hQ hcop) x = m) :
    ((2 : ℤ) * m < p.C → x = (2 : ℤ) * m) ∧
      (p.C < (2 : ℤ) * m → x = (2 : ℤ) * m - p.C) := by
  refine ⟨?_, ?_⟩
  · {
      intro hlow
      have hpre :=
        TwoInverseBelow p hQ hD hpos hcop m hm0 hmC hlow
      exact TwoInteriorInjective p hQ hD hpos hcop x ((2 : ℤ) * m)
        hx0 hxC hpre.1 hpre.2.1 (by rw [heq, hpre.2.2])
    }
  · {
      intro hhigh
      have hpre :=
        TwoInverseAbove p hQ hD hpos hcop m hm0 hmC hhigh
      exact TwoInteriorInjective p hQ hD hpos hcop x
        ((2 : ℤ) * m - p.C) hx0 hxC hpre.1 hpre.2.1
        (by rw [heq, hpre.2.2])
    }

/-- A factor of `2` is a factor of `-2`. -/
theorem TwoDividesNegTwo (n : ℤ) (h : (2 : ℤ) ∣ n) : (-2 : ℤ) ∣ n := by
  obtain ⟨k, hk⟩ := h
  refine ⟨-k, ?_⟩
  rw [hk]
  ring

/-- Dividing an even integer by `-2` negates the quotient by `2`. -/
theorem EvenDivNegTwo (n : ℤ) (h : (2 : ℤ) ∣ n) :
    n / (-2 : ℤ) = -(n / 2) := by
  have hfac : n = (-2 : ℤ) * (-(n / 2)) := by
    have h2 := (Int.mul_ediv_cancel' h).symm
    calc
      n = (2 : ℤ) * (n / 2) := h2
      _ = (-2 : ℤ) * (-(n / 2)) := by ring
  have hb : (-2 : ℤ) ≠ 0 := by decide
  conv_lhs => rw [hfac]
  exact Int.mul_ediv_cancel_left (b := -(n / 2)) (a := -2) hb

/-- Negating an even integer negates its quotient by `2`. -/
theorem NegDivTwo (m : ℤ) (h : (2 : ℤ) ∣ m) : (-m) / 2 = -(m / 2) := by
  have hfac : -m = (2 : ℤ) * (-(m / 2)) := by
    have h2 := (Int.mul_ediv_cancel' h).symm
    calc
      -m = -((2 : ℤ) * (m / 2)) := by rw [← h2]
      _ = (2 : ℤ) * (-(m / 2)) := by ring
  have hb : (2 : ℤ) ≠ 0 := by decide
  conv_lhs => rw [hfac]
  exact Int.mul_ediv_cancel_left (b := -(m / 2)) (a := 2) hb

/-- Coprimeness to `|-2|` makes the offset odd. -/
theorem NegTwoOffsetOdd (p : Parameters) (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) : ¬ (2 : ℤ) ∣ p.C := by
  intro hd
  obtain ⟨k, hk⟩ := hd
  have hnat : p.C.natAbs = 2 * k.natAbs := by
    rw [hk, Int.natAbs_mul]
    rfl
  have hgcd : 2 ∣ Nat.gcd p.C.natAbs 2 := by
    refine Nat.dvd_gcd ?_ (Nat.dvd_refl 2)
    exact ⟨k.natAbs, hnat⟩
  have hone : Nat.gcd p.C.natAbs 2 = 1 := by
    have habs : p.D.natAbs = 2 := by
      rw [hD]
      decide
    simpa [habs] using hcop
  rw [hone] at hgcd
  omega

/-- An even seed with divisor `-2` returns `-n/2`. -/
theorem NegTwoFormulaEven (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hdiv : (2 : ℤ) ∣ n) :
    TotalReturn p (TwoEvery p hQ hcop) n = -(n / 2) := by
  have hDdiv : p.D ∣ n := by
    rw [hD]
    exact TwoDividesNegTwo n hdiv
  have hhit0 : IsFirstHit p n 0 := (FirstHitZeroIff p n).mpr hDdiv
  have hleast : LeastHit p n (TwoEvery p hQ hcop n) = 0 := by
    unfold LeastHit
    exact Nat.eq_zero_of_le_zero
      (Nat.find_min' (TwoEvery p hQ hcop n) hhit0)
  unfold TotalReturn
  rw [hleast, PureDivisionQuotient p n hDdiv, hD, EvenDivNegTwo n hdiv]

/-- An odd seed with divisor `-2` returns `-(n+c)/2`. -/
theorem NegTwoFormulaOdd (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hdiv : ¬ (2 : ℤ) ∣ n) :
    TotalReturn p (TwoEvery p hQ hcop) n = -((n + p.C) / 2) := by
  have hoddC : ¬ (2 : ℤ) ∣ p.C := NegTwoOffsetOdd p hD hcop
  have htwo : (2 : ℤ) ∣ n + p.C := TwoOddSum n p.C hdiv hoddC
  have hsum : p.D ∣ n + p.C := by
    rw [hD]
    exact TwoDividesNegTwo (n + p.C) htwo
  have hstate : AffineState p.Q p.C 1 n = n + p.C := by
    rw [hQ]
    exact TwoAffineOne p.C n
  have hhit : IsFirstHit p n 1 := by
    refine ⟨?_, ?_⟩
    · {
        rw [hstate]
        exact hsum
      }
    · {
        intro i hi hdi
        have hiz : i = 0 := by omega
        rw [hiz, AffineStateZero] at hdi
        exact hdiv (by
          have hDdiv : (-2 : ℤ) ∣ n := by rwa [← hD]
          obtain ⟨k, hk⟩ := hDdiv
          exact ⟨-k, by rw [hk]; ring⟩)
      }
  have hle : LeastHit p n (TwoEvery p hQ hcop n) ≤ 1 :=
    Nat.find_le hhit
  have hne : LeastHit p n (TwoEvery p hQ hcop n) ≠ 0 := by
    intro h0
    have hhit0 : IsFirstHit p n 0 := by
      rw [← h0]
      exact Nat.find_spec (TwoEvery p hQ hcop n)
    have hDdiv : p.D ∣ n := (FirstHitZeroIff p n).1 hhit0
    rw [hD] at hDdiv
    exact hdiv (by
      obtain ⟨k, hk⟩ := hDdiv
      exact ⟨-k, by rw [hk]; ring⟩)
  have hleast : LeastHit p n (TwoEvery p hQ hcop n) = 1 := by
    omega
  unfold TotalReturn
  rw [hleast, hstate, hD, EvenDivNegTwo (n + p.C) htwo]

/-- The parameters `(1, 3, -2)`. -/
def NegTwoThree : Parameters where
  Q := 1
  C := 3
  D := -2
  DAdmissible := by
    decide

/-- Divisor `-2` and offset `3` swap `1` with `-2` and fix `-1`. -/
theorem NegTwoThreeOrbit :
    let R := TotalReturn NegTwoThree
      (TwoEvery NegTwoThree rfl (by decide))
    R 1 = -2 ∧ R (-2) = 1 ∧ R (-1) = -1 := by
  intro R
  have h1 : ¬ (2 : ℤ) ∣ 1 := by decide
  have hm1 : ¬ (2 : ℤ) ∣ -1 := by decide
  have hm2 : (2 : ℤ) ∣ -2 := ⟨-1, by decide⟩
  refine ⟨?_, ?_, ?_⟩
  · {
      dsimp [R]
      rw [NegTwoFormulaOdd NegTwoThree rfl rfl (by decide) 1 h1]
      decide
    }
  · {
      dsimp [R]
      rw [NegTwoFormulaEven NegTwoThree rfl rfl (by decide) (-2) hm2]
      decide
    }
  · {
      dsimp [R]
      rw [NegTwoFormulaOdd NegTwoThree rfl rfl (by decide) (-1) hm1]
      decide
    }

/-- The return at divisor `-2` is the negation of the return at divisor `2`. -/
theorem NegTwoIsNegation (p q : Parameters) (hQp : p.Q = 1) (hQq : q.Q = 1)
    (hC : p.C = q.C) (hDp : p.D = 2) (hDq : q.D = -2)
    (hcopp : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hcopq : Nat.Coprime q.C.natAbs q.D.natAbs) (n : ℤ) :
    TotalReturn q (TwoEvery q hQq hcopq) n =
      -TotalReturn p (TwoEvery p hQp hcopp) n := by
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      rw [NegTwoFormulaEven q hQq hDq hcopq n hdiv,
        TwoFormulaEven p hQp hDp hcopp n hdiv]
    }
  · {
      rw [NegTwoFormulaOdd q hQq hDq hcopq n hdiv,
        TwoFormulaOdd p hQp hDp hcopp n hdiv, hC]
    }

/-- The second negative return equals the second positive return exactly when
the first positive return is even. -/
theorem NegTwoTwoStep (p q : Parameters) (hQp : p.Q = 1) (hQq : q.Q = 1)
    (hC : p.C = q.C) (hDp : p.D = 2) (hDq : q.D = -2)
    (hcopp : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hcopq : Nat.Coprime q.C.natAbs q.D.natAbs) (n : ℤ) :
    let hp := TotalReturn p (TwoEvery p hQp hcopp) n
    let hq := TotalReturn q (TwoEvery q hQq hcopq)
    ((2 : ℤ) ∣ hp → hq (hq n) = hp / 2) ∧
      (¬ (2 : ℤ) ∣ hp → hq (hq n) = (hp - p.C) / 2) := by
  intro hp hq
  have hsign : hq n = -hp := by
    simpa [hp, hq] using
      NegTwoIsNegation p q hQp hQq hC hDp hDq hcopp hcopq n
  refine ⟨?_, ?_⟩
  · {
      intro heven
      have hneg : (2 : ℤ) ∣ -hp := by
        obtain ⟨k, hk⟩ := heven
        refine ⟨-k, ?_⟩
        rw [hk]
        ring
      rw [hsign]
      dsimp [hq]
      rw [NegTwoFormulaEven q hQq hDq hcopq (-hp) hneg, NegDivTwo hp heven]
      ring
    }
  · {
      intro hodd
      have hneg : ¬ (2 : ℤ) ∣ -hp := by
        intro hd
        apply hodd
        obtain ⟨k, hk⟩ := hd
        refine ⟨-k, ?_⟩
        rw [show hp = -(-hp) by ring, hk]
        ring
      have hoddC : ¬ (2 : ℤ) ∣ q.C := NegTwoOffsetOdd q hDq hcopq
      have hsum : (2 : ℤ) ∣ -hp + q.C :=
        TwoOddSum (-hp) q.C hneg hoddC
      rw [hsign]
      dsimp [hq]
      rw [NegTwoFormulaOdd q hQq hDq hcopq (-hp) hneg, hC]
      have hfac : hp - q.C = -(-hp + q.C) := by ring
      rw [hfac, NegDivTwo (-hp + q.C) hsum]
    }

/-- Quotients by `2` subtract when both integers are even. -/
theorem EvenQuotientSub (a b : ℤ) (ha : (2 : ℤ) ∣ a) (hb : (2 : ℤ) ∣ b) :
    a / 2 - b / 2 = (a - b) / 2 := by
  have hfac : a - b = (2 : ℤ) * (a / 2 - b / 2) := by
    have ha2 := Int.mul_ediv_cancel' ha
    have hb2 := Int.mul_ediv_cancel' hb
    calc
      a - b = (2 : ℤ) * (a / 2) - (2 : ℤ) * (b / 2) := by rw [ha2, hb2]
      _ = (2 : ℤ) * (a / 2 - b / 2) := by ring
  have hsub : (2 : ℤ) ∣ a - b := ⟨a / 2 - b / 2, hfac⟩
  have hquot := (Int.mul_ediv_cancel' hsub).symm
  conv_lhs at hquot => rw [hfac]
  exact Int.eq_of_mul_eq_mul_left (by decide : (2 : ℤ) ≠ 0) hquot

/-- An odd first return makes the two second returns differ by `c`. -/
theorem NegTwoOddGap (p q : Parameters) (hQp : p.Q = 1) (hQq : q.Q = 1)
    (hC : p.C = q.C) (hDp : p.D = 2) (hDq : q.D = -2)
    (hcopp : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hcopq : Nat.Coprime q.C.natAbs q.D.natAbs) (n : ℤ)
    (hodd : ¬ (2 : ℤ) ∣ TotalReturn p (TwoEvery p hQp hcopp) n) :
    TotalReturn p (TwoEvery p hQp hcopp)
        (TotalReturn p (TwoEvery p hQp hcopp) n) -
      TotalReturn q (TwoEvery q hQq hcopq)
        (TotalReturn q (TwoEvery q hQq hcopq) n) = p.C := by
  set hp := TotalReturn p (TwoEvery p hQp hcopp) n
  have hpos : TotalReturn p (TwoEvery p hQp hcopp) hp = (hp + p.C) / 2 :=
    TwoFormulaOdd p hQp hDp hcopp hp hodd
  have hneg : TotalReturn q (TwoEvery q hQq hcopq)
      (TotalReturn q (TwoEvery q hQq hcopq) n) = (hp - p.C) / 2 :=
    (NegTwoTwoStep p q hQp hQq hC hDp hDq hcopp hcopq n).2 hodd
  have hoddC : ¬ (2 : ℤ) ∣ p.C := by
    simpa [hDp] using TwoOffsetOdd p hDp hcopp
  have hsum : (2 : ℤ) ∣ hp + p.C := TwoOddSum hp p.C hodd hoddC
  have hdiff : (2 : ℤ) ∣ hp - p.C := by
    have hnegC : ¬ (2 : ℤ) ∣ -p.C := by
      intro hd
      apply hoddC
      obtain ⟨k, hk⟩ := hd
      refine ⟨-k, ?_⟩
      rw [show p.C = -(-p.C) by ring, hk]
      ring
    have hsumneg : (2 : ℤ) ∣ hp + -p.C :=
      TwoOddSum hp (-p.C) hodd hnegC
    simpa [sub_eq_add_neg] using hsumneg
  rw [hpos, hneg, EvenQuotientSub (hp + p.C) (hp - p.C) hsum hdiff]
  have hnum : hp + p.C - (hp - p.C) = (2 : ℤ) * p.C := by ring
  rw [hnum]
  exact Int.mul_ediv_cancel_left p.C (by decide)

/-- Exact division by `2` halves the absolute value. -/
theorem EvenAbsHalf (m : ℤ) (h : (2 : ℤ) ∣ m) :
    (m / 2).natAbs = m.natAbs / 2 := by
  have h2 := Int.mul_ediv_cancel' h
  have hfac : m.natAbs = (2 : ℤ).natAbs * (m / 2).natAbs := by
    have hrewrite : m.natAbs = ((2 : ℤ) * (m / 2)).natAbs :=
      congrArg Int.natAbs h2.symm
    rw [hrewrite, Int.natAbs_mul]
  have htwo : (2 : ℤ).natAbs = 2 := rfl
  rw [htwo] at hfac
  omega

/-- For divisor `-2`, the shell `|x| ≤ |c|` is invariant. -/
theorem NegTwoShell (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (habs : n.natAbs ≤ p.C.natAbs) :
    (TotalReturn p (TwoEvery p hQ hcop) n).natAbs ≤ p.C.natAbs := by
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      rw [NegTwoFormulaEven p hQ hD hcop n hdiv, Int.natAbs_neg,
        EvenAbsHalf n hdiv]
      omega
    }
  · {
      have hoddC : ¬ (2 : ℤ) ∣ p.C := NegTwoOffsetOdd p hD hcop
      have hsum : (2 : ℤ) ∣ n + p.C := TwoOddSum n p.C hdiv hoddC
      rw [NegTwoFormulaOdd p hQ hD hcop n hdiv, Int.natAbs_neg,
        EvenAbsHalf (n + p.C) hsum]
      have hle : (n + p.C).natAbs ≤ n.natAbs + p.C.natAbs :=
        Int.natAbs_add_le n p.C
      have htwo : (n + p.C).natAbs ≤ 2 * p.C.natAbs := by
        omega
      omega
    }

/-- Outside the shell, one return drops the absolute value. -/
theorem NegTwoDrops (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (habs : p.C.natAbs < n.natAbs) :
    (TotalReturn p (TwoEvery p hQ hcop) n).natAbs ≤ n.natAbs - 1 := by
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      rw [NegTwoFormulaEven p hQ hD hcop n hdiv, Int.natAbs_neg,
        EvenAbsHalf n hdiv]
      omega
    }
  · {
      have hoddC : ¬ (2 : ℤ) ∣ p.C := NegTwoOffsetOdd p hD hcop
      have hsum : (2 : ℤ) ∣ n + p.C := TwoOddSum n p.C hdiv hoddC
      rw [NegTwoFormulaOdd p hQ hD hcop n hdiv, Int.natAbs_neg,
        EvenAbsHalf (n + p.C) hsum]
      have hle : (n + p.C).natAbs ≤ n.natAbs + p.C.natAbs :=
        Int.natAbs_add_le n p.C
      omega
    }

/-- Outside or on the shell, one return at most halves the excess. -/
theorem NegTwoExcessHalves (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (n : ℤ) (habs : p.C.natAbs ≤ n.natAbs) :
    (TotalReturn p (TwoEvery p hQ hcop) n).natAbs ≤
      p.C.natAbs + (n.natAbs - p.C.natAbs) / 2 := by
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      rw [NegTwoFormulaEven p hQ hD hcop n hdiv, Int.natAbs_neg,
        EvenAbsHalf n hdiv]
      omega
    }
  · {
      have hoddC : ¬ (2 : ℤ) ∣ p.C := NegTwoOffsetOdd p hD hcop
      have hsum : (2 : ℤ) ∣ n + p.C := TwoOddSum n p.C hdiv hoddC
      rw [NegTwoFormulaOdd p hQ hD hcop n hdiv, Int.natAbs_neg,
        EvenAbsHalf (n + p.C) hsum]
      have hle : (n + p.C).natAbs ≤ n.natAbs + p.C.natAbs :=
        Int.natAbs_add_le n p.C
      omega
    }

/-- For an integer at least `2`, halving decreases the base-two logarithm by one. -/
theorem LogOfHalf (e : ℕ) (he : 2 ≤ e) :
    Nat.log 2 (e / 2) + 1 = Nat.log 2 e := by
  have hb : 1 < 2 := by decide
  have hpos : 0 < e := by omega
  have hpos2 : 0 < e / 2 := by omega
  apply le_antisymm
  · {
      have hbase : 2 ^ Nat.log 2 (e / 2) ≤ e / 2 :=
        Nat.pow_log_le_self 2 (ne_of_gt hpos2)
      have hmul : 2 ^ (Nat.log 2 (e / 2) + 1) =
          2 ^ Nat.log 2 (e / 2) * 2 := by
        rw [Nat.pow_succ]
      have hle : 2 ^ (Nat.log 2 (e / 2) + 1) ≤ e := by
        rw [hmul]
        omega
      exact Nat.le_log_of_pow_le hb hle
    }
  · {
      have hup : e / 2 + 1 ≤ 2 ^ (Nat.log 2 (e / 2) + 1) := by
        have hlt2 : e / 2 < 2 ^ (Nat.log 2 (e / 2) + 1) :=
          Nat.lt_pow_succ_log_self hb (e / 2)
        omega
      have htwo : 2 * 2 ^ (Nat.log 2 (e / 2) + 1) =
          2 ^ (Nat.log 2 (e / 2) + 2) := by
        calc
          2 * 2 ^ (Nat.log 2 (e / 2) + 1) =
              2 ^ (Nat.log 2 (e / 2) + 1) * 2 := by
            rw [Nat.mul_comm]
          _ = 2 ^ (Nat.log 2 (e / 2) + 2) := by
            rw [← Nat.pow_succ]
      have hlt : e < 2 ^ (Nat.log 2 (e / 2) + 2) := by
        have hle : e ≤ 2 * (e / 2) + 1 := by omega
        have hmul : 2 * (e / 2) + 1 ≤
            2 * (2 ^ (Nat.log 2 (e / 2) + 1) - 1) + 1 := by
          have hsub : e / 2 ≤ 2 ^ (Nat.log 2 (e / 2) + 1) - 1 := by
            omega
          omega
        have hlast : 2 * (2 ^ (Nat.log 2 (e / 2) + 1) - 1) + 1 =
            2 ^ (Nat.log 2 (e / 2) + 2) - 1 := by
          omega
        omega
      have hlog : Nat.log 2 e < Nat.log 2 (e / 2) + 2 :=
        Nat.log_lt_of_lt_pow (ne_of_gt hpos) hlt
      omega
    }

/-- The closed shell is entered on the logarithmic scale of the excess. -/
theorem NegTwoLogEnters (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (n : ℤ) :
    ∃ k : ℕ, k ≤ Nat.log 2 (n.natAbs - p.C.natAbs) + 1 ∧
      (Iterate (TotalReturn p (TwoEvery p hQ hcop)) k n).natAbs ≤
        p.C.natAbs := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  induction h : n.natAbs using Nat.strong_induction_on generalizing n with
  | _ m ih => {
      by_cases hshell : n.natAbs ≤ p.C.natAbs
      · {
          refine ⟨0, ?_, ?_⟩
          · {
              omega
            }
          · {
              simpa [R, Iterate] using hshell
            }
        }
      · {
          have hlt : p.C.natAbs < n.natAbs := by omega
          have habs : p.C.natAbs ≤ n.natAbs := Nat.le_of_lt hlt
          have hhalf := NegTwoExcessHalves p hQ hD hcop n habs
          have hhalfR : (R n).natAbs ≤
              p.C.natAbs + (n.natAbs - p.C.natAbs) / 2 := by
            simpa [R] using hhalf
          by_cases hzero : (R n).natAbs ≤ p.C.natAbs
          · {
              refine ⟨1, ?_, ?_⟩
              · {
                  rw [← h]
                  exact Nat.le_add_left 1
                    (Nat.log 2 (n.natAbs - p.C.natAbs))
                }
              · {
                  simpa [R, Iterate] using hzero
                }
            }
          · {
              have hsmall : (R n).natAbs < m := by
                rw [← h]
                omega
              obtain ⟨k, hk, hent⟩ :=
                ih (R n).natAbs hsmall (R n) rfl
              refine ⟨k + 1, ?_, ?_⟩
              · {
                  have hrest : (R n).natAbs - p.C.natAbs ≤
                      (n.natAbs - p.C.natAbs) / 2 := by
                    omega
                  have hposR : 1 ≤ (R n).natAbs - p.C.natAbs :=
                    Nat.succ_le_of_lt
                      (Nat.sub_pos_of_lt (lt_of_not_ge hzero))
                  have hdiv : 1 ≤ (n.natAbs - p.C.natAbs) / 2 :=
                    le_trans hposR hrest
                  have he2 : 2 ≤ n.natAbs - p.C.natAbs := by
                    have htwo : 2 * 1 ≤
                        2 * ((n.natAbs - p.C.natAbs) / 2) :=
                      Nat.mul_le_mul_left 2 hdiv
                    exact le_trans htwo
                      (Nat.mul_div_le (n.natAbs - p.C.natAbs) 2)
                  have hmono : Nat.log 2 ((R n).natAbs - p.C.natAbs) ≤
                      Nat.log 2 ((n.natAbs - p.C.natAbs) / 2) :=
                    Nat.log_mono_right hrest
                  have hlog := LogOfHalf (n.natAbs - p.C.natAbs) he2
                  have hkE : k ≤ Nat.log 2 (n.natAbs - p.C.natAbs) := by
                    calc
                      k ≤ Nat.log 2 ((R n).natAbs - p.C.natAbs) + 1 := hk
                      _ ≤ Nat.log 2 ((n.natAbs - p.C.natAbs) / 2) + 1 :=
                        Nat.add_le_add_right hmono 1
                      _ = Nat.log 2 (n.natAbs - p.C.natAbs) := hlog
                  rw [← h]
                  exact Nat.add_le_add_right hkE 1
                }
              · {
                  rw [show k + 1 = 1 + k from Nat.add_comm k 1, IterateAdd]
                  simpa [R, Iterate] using hent
                }
            }
        }
    }

/-- Every orbit under divisor `-2` enters the shell. -/
theorem NegTwoEnters (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    ∃ k : ℕ, k ≤ n.natAbs ∧
      (Iterate (TotalReturn p (TwoEvery p hQ hcop)) k n).natAbs ≤
        p.C.natAbs := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  induction h : n.natAbs using Nat.strong_induction_on generalizing n with
  | _ m ih => {
      by_cases hshell : n.natAbs ≤ p.C.natAbs
      · {
          refine ⟨0, Nat.zero_le _, ?_⟩
          simpa [R, Iterate] using hshell
        }
      · {
          have hlt : p.C.natAbs < n.natAbs := by omega
          have hdrop := NegTwoDrops p hQ hD hcop n hlt
          have hsmall : (R n).natAbs < m := by
            have hdropR : (R n).natAbs ≤ n.natAbs - 1 := by
              simpa [R] using hdrop
            rw [← h]
            omega
          obtain ⟨k, hk, hent⟩ :=
            ih (R n).natAbs hsmall (R n) rfl
          refine ⟨k + 1, ?_, ?_⟩
          · {
              rw [← h]
              omega
            }
          · {
              have hshift :
                  Iterate R k (R n) = Iterate R (k + 1) n := by
                rw [show k + 1 = 1 + k by omega, IterateAdd]
                simp [Iterate]
              rw [← hshift]
              exact hent
            }
        }
    }

/-- The return stays in the shell at every later time. -/
theorem NegTwoShellStays (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (habs : n.natAbs ≤ p.C.natAbs) (k : ℕ) :
    (Iterate (TotalReturn p (TwoEvery p hQ hcop)) k n).natAbs ≤
      p.C.natAbs := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  induction k with
  | zero => {
      simpa [R, Iterate] using habs
    }
  | succ k ih => {
      simpa [R, Iterate] using NegTwoShell p hQ hD hcop (Iterate R k n) ih
    }

/-- Code of an integer in `{-N, ..., N}` by translation. -/
def NegShellCode (N : ℕ) (x : ℤ) : ℕ := (x + (N : ℤ)).toNat

/-- The translated code is strictly below `2N+1`. -/
theorem NegShellCodeLt (N : ℕ) (x : ℤ) (habs : x.natAbs ≤ N) :
    NegShellCode N x < 2 * N + 1 := by
  have hup : x ≤ (x.natAbs : ℤ) := Int.le_natAbs (a := x)
  have hneg : -x ≤ (x.natAbs : ℤ) := by
    rw [← Int.natAbs_neg x]
    exact Int.le_natAbs (a := -x)
  have hsigned : -(N : ℤ) ≤ x ∧ x ≤ (N : ℤ) := by
    have habsZ : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast habs
    omega
  have h0 : 0 ≤ x + (N : ℤ) := by omega
  have htop : x + (N : ℤ) ≤ (2 * N : ℤ) := by omega
  have hto : ((x + (N : ℤ)).toNat : ℤ) = x + (N : ℤ) :=
    Int.toNat_of_nonneg h0
  have hle : NegShellCode N x ≤ 2 * N := by
    have hcast : ((x + (N : ℤ)).toNat : ℤ) ≤ (2 * N : ℤ) := by
      rw [hto]
      exact htop
    exact_mod_cast hcast
  omega

/-- Equal codes determine the integer inside the shell. -/
theorem NegShellCodeInj (N : ℕ) (x y : ℤ) (hx : x.natAbs ≤ N)
    (hy : y.natAbs ≤ N) (h : NegShellCode N x = NegShellCode N y) :
    x = y := by
  have hx0 : 0 ≤ x + (N : ℤ) := by
    have hneg : -x ≤ (x.natAbs : ℤ) := by
      rw [← Int.natAbs_neg x]
      exact Int.le_natAbs (a := -x)
    have hxabs : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hx
    omega
  have hy0 : 0 ≤ y + (N : ℤ) := by
    have hneg : -y ≤ (y.natAbs : ℤ) := by
      rw [← Int.natAbs_neg y]
      exact Int.le_natAbs (a := -y)
    have hyabs : (y.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hy
    omega
  have hxto : ((x + (N : ℤ)).toNat : ℤ) = x + (N : ℤ) :=
    Int.toNat_of_nonneg hx0
  have hyto : ((y + (N : ℤ)).toNat : ℤ) = y + (N : ℤ) :=
    Int.toNat_of_nonneg hy0
  have hcast : ((NegShellCode N x : ℕ) : ℤ) =
      ((NegShellCode N y : ℕ) : ℤ) := by
    exact_mod_cast h
  unfold NegShellCode at hcast
  rw [hxto, hyto] at hcast
  omega

/-- Every orbit under divisor `-2` is eventually periodic. -/
theorem NegTwoPeriodic (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    ∃ t period : ℕ, t ≤ n.natAbs + 2 * p.C.natAbs + 1 ∧ 0 < period ∧
      period ≤ 2 * p.C.natAbs + 1 ∧
      ∀ k : ℕ,
        Iterate (TotalReturn p (TwoEvery p hQ hcop)) (t + k) n =
          Iterate (TotalReturn p (TwoEvery p hQ hcop))
            (t + period + k) n := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  obtain ⟨t0, ht0, hent⟩ := NegTwoEnters p hQ hD hcop n
  let N := p.C.natAbs
  let y := Iterate R t0 n
  have hy : y.natAbs ≤ N := by
    simpa [R, y, N] using hent
  have hstay : ∀ j, (Iterate R j y).natAbs ≤ N := by
    intro j
    simpa [R, y, N] using NegTwoShellStays p hQ hD hcop y hy j
  let f : Fin (2 * N + 2) → Fin (2 * N + 1) := fun i =>
    ⟨NegShellCode N (Iterate R i.val y), NegShellCodeLt N _ (hstay i.val)⟩
  have hcard : Fintype.card (Fin (2 * N + 1)) <
      Fintype.card (Fin (2 * N + 2)) := by
    simp [Fintype.card_fin]
  obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hstate : Iterate R a.val y = Iterate R b.val y := by
    have hcode : NegShellCode N (Iterate R a.val y) =
        NegShellCode N (Iterate R b.val y) := by
      simpa [f] using congrArg Fin.val heq
    exact NegShellCodeInj N _ _ (hstay a.val) (hstay b.val) hcode
  have hlt : a.val ≠ b.val := by
    intro heqv
    apply hne
    exact Fin.ext heqv
  rcases Nat.lt_or_gt_of_ne hlt with hab | hba
  · {
      refine ⟨t0 + a.val, b.val - a.val, ?_, ?_, ?_, ?_⟩
      · {
          have ha' : a.val ≤ 2 * p.C.natAbs + 1 :=
            Nat.le_of_lt_succ a.isLt
          calc
            t0 + a.val ≤ n.natAbs + a.val :=
              Nat.add_le_add_right ht0 a.val
            _ ≤ n.natAbs + (2 * p.C.natAbs + 1) :=
              Nat.add_le_add_left ha' n.natAbs
            _ = n.natAbs + 2 * p.C.natAbs + 1 := by
              exact (Nat.add_assoc n.natAbs (2 * p.C.natAbs) 1).symm
        }
      · {
          omega
        }
      · {
          have hdiff : b.val - a.val ≤ b.val := Nat.sub_le b.val a.val
          have hb : b.val ≤ 2 * p.C.natAbs + 1 :=
            Nat.le_of_lt_succ b.isLt
          exact le_trans hdiff hb
        }
      · {
          intro k
          have htail : Iterate R (a.val + k) y =
              Iterate R (b.val + k) y := by
            induction k with
            | zero => {
                simpa [Iterate] using hstate
              }
            | succ k ih => {
                have hL : a.val + (k + 1) = a.val + k + 1 := by omega
                have hRgt : b.val + (k + 1) = b.val + k + 1 := by omega
                rw [hL, hRgt, Iterate, Iterate]
                exact congrArg R ih
              }
          have hleft : Iterate R (t0 + a.val + k) n =
              Iterate R (a.val + k) y := by
            rw [show t0 + a.val + k = t0 + (a.val + k) by omega, IterateAdd]
          have hright : Iterate R (b.val + k) y =
              Iterate R (t0 + a.val + (b.val - a.val) + k) n := by
            have hidx : t0 + a.val + (b.val - a.val) + k =
                t0 + (b.val + k) := by omega
            rw [hidx]
            symm
            rw [IterateAdd]
          rw [hleft, htail, hright]
        }
    }
  · {
      refine ⟨t0 + b.val, a.val - b.val, ?_, ?_, ?_, ?_⟩
      · {
          have hb' : b.val ≤ 2 * p.C.natAbs + 1 :=
            Nat.le_of_lt_succ b.isLt
          calc
            t0 + b.val ≤ n.natAbs + b.val :=
              Nat.add_le_add_right ht0 b.val
            _ ≤ n.natAbs + (2 * p.C.natAbs + 1) :=
              Nat.add_le_add_left hb' n.natAbs
            _ = n.natAbs + 2 * p.C.natAbs + 1 := by
              exact (Nat.add_assoc n.natAbs (2 * p.C.natAbs) 1).symm
        }
      · {
          omega
        }
      · {
          have hdiff : a.val - b.val ≤ a.val := Nat.sub_le a.val b.val
          have ha : a.val ≤ 2 * p.C.natAbs + 1 :=
            Nat.le_of_lt_succ a.isLt
          exact le_trans hdiff ha
        }
      · {
          intro k
          have htail : Iterate R (b.val + k) y =
              Iterate R (a.val + k) y := by
            induction k with
            | zero => {
                simpa [Iterate] using hstate.symm
              }
            | succ k ih => {
                have hL : b.val + (k + 1) = b.val + k + 1 := by omega
                have hRgt : a.val + (k + 1) = a.val + k + 1 := by omega
                rw [hL, hRgt, Iterate, Iterate]
                exact congrArg R ih
              }
          have hleft : Iterate R (t0 + b.val + k) n =
              Iterate R (b.val + k) y := by
            rw [show t0 + b.val + k = t0 + (b.val + k) by omega, IterateAdd]
          have hright : Iterate R (a.val + k) y =
              Iterate R (t0 + b.val + (a.val - b.val) + k) n := by
            have hidx : t0 + b.val + (a.val - b.val) + k =
                t0 + (a.val + k) := by omega
            rw [hidx]
            symm
            rw [IterateAdd]
          rw [hleft, htail, hright]
        }
    }

/-- Zero is fixed by the divisor `-2`. -/
theorem NegTwoZeroFixed (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) :
    TotalReturn p (TwoEvery p hQ hcop) 0 = 0 := by
  have hdiv : (2 : ℤ) ∣ 0 := ⟨0, by ring⟩
  rw [NegTwoFormulaEven p hQ hD hcop 0 hdiv]
  simp

/-- A nonzero shell integer does not have the middle code. -/
theorem NegShellCodeNonzero (N : ℕ) (x : ℤ) (habs : x.natAbs ≤ N)
    (h0 : x ≠ 0) : NegShellCode N x ≠ N := by
  intro hcode
  have h0le : 0 ≤ x + (N : ℤ) := by
    have hneg : -x ≤ (x.natAbs : ℤ) := by
      rw [← Int.natAbs_neg x]
      exact Int.le_natAbs (a := -x)
    have hxabs : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast habs
    omega
  have hto : ((x + (N : ℤ)).toNat : ℤ) = x + (N : ℤ) :=
    Int.toNat_of_nonneg h0le
  have hcast : ((NegShellCode N x : ℕ) : ℤ) = (N : ℤ) := by
    exact_mod_cast hcode
  unfold NegShellCode at hcast
  rw [hto] at hcast
  omega

/-- Compress the shell code after deleting the code of zero. -/
def NegNonzeroCode (N : ℕ) (x : ℤ) : ℕ :=
  let c := NegShellCode N x
  if c < N then c else c - 1

/-- A nonzero shell state has compressed code below `2N`. -/
theorem NegNonzeroCodeLt (N : ℕ) (hN : 0 < N) (x : ℤ)
    (habs : x.natAbs ≤ N) (h0 : x ≠ 0) :
    NegNonzeroCode N x < 2 * N := by
  have hlt := NegShellCodeLt N x habs
  have hmid := NegShellCodeNonzero N x habs h0
  by_cases hc : NegShellCode N x < N
  · {
      simp [NegNonzeroCode, hc]
      omega
    }
  · {
      simp [NegNonzeroCode, hc]
      omega
    }

/-- Every orbit under divisor `-2` has period at most `2|c|`. -/
theorem NegTwoPeriodAtMostTwice (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    ∃ t period : ℕ, t ≤ n.natAbs + 2 * p.C.natAbs ∧ 0 < period ∧
      period ≤ 2 * p.C.natAbs ∧
      ∀ k : ℕ,
        Iterate (TotalReturn p (TwoEvery p hQ hcop)) (t + k) n =
          Iterate (TotalReturn p (TwoEvery p hQ hcop))
            (t + period + k) n := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  obtain ⟨t0, ht0, hent⟩ := NegTwoEnters p hQ hD hcop n
  let N := p.C.natAbs
  have hN : 0 < N := by
    by_contra h
    have hzero : N = 0 := by omega
    have hc : p.C = 0 := Int.natAbs_eq_zero.mp hzero
    have hgcd : Nat.gcd 0 (p.D.natAbs) = 1 := by
      simpa [hc] using hcop
    rw [hD] at hgcd
    have : Nat.gcd 0 2 = 1 := by
      simp at hgcd
    rw [Nat.gcd_zero_left] at this
    omega
  let y := Iterate R t0 n
  have hy : y.natAbs ≤ N := by
    simpa [R, y, N] using hent
  have hstay : ∀ j, (Iterate R j y).natAbs ≤ N := by
    intro j
    simpa [R, y, N] using NegTwoShellStays p hQ hD hcop y hy j
  have hzeroTail : ∀ j k, Iterate R j y = 0 →
      Iterate R (t0 + j + k) n = Iterate R (t0 + j) n := by
    intro j k hhit
    have hfix : ∀ i, Iterate R i 0 = 0 := by
      intro i
      induction i with
      | zero => {
          simp [Iterate]
        }
      | succ i ih => {
          rw [Iterate, ih]
          simpa [R] using NegTwoZeroFixed p hQ hD hcop
        }
    have hbase : Iterate R (t0 + j) n = Iterate R j y := by
      rw [IterateAdd]
    have hleft : Iterate R (t0 + j + k) n = Iterate R k 0 := by
      rw [show t0 + j + k = (t0 + j) + k by omega, IterateAdd, hbase, hhit]
    rw [hleft, hfix, hbase, hhit]
  by_cases hmeet : ∃ j : ℕ, j ≤ 2 * N ∧ Iterate R j y = 0
  · {
      obtain ⟨j, hj, hhit⟩ := hmeet
      refine ⟨t0 + j, 1, ?_, by omega, ?_, ?_⟩
      · {
          have hj' : j ≤ 2 * p.C.natAbs := by
            simpa [N] using hj
          calc
            t0 + j ≤ n.natAbs + j := Nat.add_le_add_right ht0 j
            _ ≤ n.natAbs + 2 * p.C.natAbs := Nat.add_le_add_left hj' n.natAbs
        }
      · {
          exact Nat.one_le_iff_ne_zero.mpr (by omega : 2 * p.C.natAbs ≠ 0)
        }
      · {
          intro k
          have hL := hzeroTail j k hhit
          have hR := hzeroTail j (k + 1) hhit
          have hidx : t0 + j + 1 + k = t0 + j + (k + 1) := by omega
          rw [hidx, hR, hL]
        }
    }
  · {
      have hnz : ∀ j, j ≤ 2 * N → Iterate R j y ≠ 0 := by
        intro j hj hhit
        apply hmeet
        exact ⟨j, hj, hhit⟩
      let f : Fin (2 * N + 1) → Fin (2 * N) := fun i =>
        ⟨NegNonzeroCode N (Iterate R i.val y),
          NegNonzeroCodeLt N hN _ (hstay i.val)
            (hnz i.val (Nat.le_of_lt_succ i.isLt))⟩
      have hcard : Fintype.card (Fin (2 * N)) <
          Fintype.card (Fin (2 * N + 1)) := by
        simp [Fintype.card_fin]
      obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
      have hstate : Iterate R a.val y = Iterate R b.val y := by
        have hcode : NegNonzeroCode N (Iterate R a.val y) =
            NegNonzeroCode N (Iterate R b.val y) := by
          simpa [f] using congrArg Fin.val heq
        -- The compressed codes agree, so the shell codes agree.
        have ha := hstay a.val
        have hb := hstay b.val
        have han : Iterate R a.val y ≠ 0 :=
          hnz a.val (Nat.le_of_lt_succ a.isLt)
        have hbn : Iterate R b.val y ≠ 0 :=
          hnz b.val (Nat.le_of_lt_succ b.isLt)
        have hshell : NegShellCode N (Iterate R a.val y) =
            NegShellCode N (Iterate R b.val y) := by
          by_cases hca : NegShellCode N (Iterate R a.val y) < N
          · {
              by_cases hcb : NegShellCode N (Iterate R b.val y) < N
              · {
                  simpa [NegNonzeroCode, hca, hcb] using hcode
                }
              · {
                  have hltA := NegShellCodeLt N _ ha
                  have hmidB := NegShellCodeNonzero N _ hb hbn
                  have hcodeB : NegNonzeroCode N (Iterate R b.val y) =
                      NegShellCode N (Iterate R b.val y) - 1 := by
                    simp [NegNonzeroCode, hcb]
                  have hcodeA : NegNonzeroCode N (Iterate R a.val y) =
                      NegShellCode N (Iterate R a.val y) := by
                    simp [NegNonzeroCode, hca]
                  have hlo : NegNonzeroCode N (Iterate R a.val y) < N := by
                    rw [hcodeA]
                    exact hca
                  have hhi : N ≤ NegNonzeroCode N (Iterate R b.val y) := by
                    rw [hcodeB]
                    have hge : N ≤ NegShellCode N (Iterate R b.val y) :=
                      le_of_not_gt hcb
                    have hgt : N + 1 ≤
                        NegShellCode N (Iterate R b.val y) :=
                      Nat.succ_le_of_lt (lt_of_le_of_ne hge hmidB.symm)
                    exact Nat.le_sub_of_add_le hgt
                  have hbad : NegNonzeroCode N (Iterate R a.val y) <
                      NegNonzeroCode N (Iterate R a.val y) := by
                    calc
                      NegNonzeroCode N (Iterate R a.val y) < N := hlo
                      _ ≤ NegNonzeroCode N (Iterate R b.val y) := hhi
                      _ = NegNonzeroCode N (Iterate R a.val y) := hcode.symm
                  exact False.elim (Nat.lt_irrefl _ hbad)
                }
            }
          · {
              by_cases hcb : NegShellCode N (Iterate R b.val y) < N
              · {
                  have hltB := NegShellCodeLt N _ hb
                  have hcodeA : NegNonzeroCode N (Iterate R a.val y) =
                      NegShellCode N (Iterate R a.val y) - 1 := by
                    simp [NegNonzeroCode, hca]
                  have hcodeB : NegNonzeroCode N (Iterate R b.val y) =
                      NegShellCode N (Iterate R b.val y) := by
                    simp [NegNonzeroCode, hcb]
                  have hlo : NegNonzeroCode N (Iterate R b.val y) < N := by
                    rw [hcodeB]
                    exact hcb
                  have hhi : N ≤ NegNonzeroCode N (Iterate R a.val y) := by
                    rw [hcodeA]
                    have hge : N ≤ NegShellCode N (Iterate R a.val y) :=
                      le_of_not_gt hca
                    have hmidA := NegShellCodeNonzero N _ ha han
                    have hgt : N + 1 ≤
                        NegShellCode N (Iterate R a.val y) :=
                      Nat.succ_le_of_lt (lt_of_le_of_ne hge hmidA.symm)
                    exact Nat.le_sub_of_add_le hgt
                  have hbad : NegNonzeroCode N (Iterate R b.val y) <
                      NegNonzeroCode N (Iterate R b.val y) := by
                    calc
                      NegNonzeroCode N (Iterate R b.val y) < N := hlo
                      _ ≤ NegNonzeroCode N (Iterate R a.val y) := hhi
                      _ = NegNonzeroCode N (Iterate R b.val y) := hcode
                  exact False.elim (Nat.lt_irrefl _ hbad)
                }
              · {
                  have hcodeA : NegNonzeroCode N (Iterate R a.val y) =
                      NegShellCode N (Iterate R a.val y) - 1 := by
                    simp [NegNonzeroCode, hca]
                  have hcodeB : NegNonzeroCode N (Iterate R b.val y) =
                      NegShellCode N (Iterate R b.val y) - 1 := by
                    simp [NegNonzeroCode, hcb]
                  have hgeA : N ≤ NegShellCode N (Iterate R a.val y) := by
                    omega
                  have hgeB : N ≤ NegShellCode N (Iterate R b.val y) := by
                    omega
                  omega
                }
            }
        exact NegShellCodeInj N _ _ ha hb hshell
      have hlt : a.val ≠ b.val := by
        intro heqv
        exact hne (Fin.ext heqv)
      rcases Nat.lt_or_gt_of_ne hlt with hab | hba
      · {
          refine ⟨t0 + a.val, b.val - a.val, ?_, ?_, ?_, ?_⟩
          · {
              have ha' : a.val ≤ 2 * p.C.natAbs :=
                Nat.le_of_lt_succ (by simpa [N] using a.isLt :
                  a.val < 2 * p.C.natAbs + 1)
              calc
                t0 + a.val ≤ n.natAbs + a.val :=
                  Nat.add_le_add_right ht0 a.val
                _ ≤ n.natAbs + 2 * p.C.natAbs :=
                  Nat.add_le_add_left ha' n.natAbs
            }
          · {
              omega
            }
          · {
              have hdiff : b.val - a.val ≤ b.val := Nat.sub_le b.val a.val
              have hb' : b.val ≤ 2 * p.C.natAbs :=
                Nat.le_of_lt_succ (by simpa [N] using b.isLt :
                  b.val < 2 * p.C.natAbs + 1)
              exact le_trans hdiff hb'
            }
          · {
              intro k
              have htail : Iterate R (a.val + k) y =
                  Iterate R (b.val + k) y := by
                induction k with
                | zero => {
                    simpa [Iterate] using hstate
                  }
                | succ k ih => {
                    have hL : a.val + (k + 1) = a.val + k + 1 := by omega
                    have hRgt : b.val + (k + 1) = b.val + k + 1 := by omega
                    rw [hL, hRgt, Iterate, Iterate]
                    exact congrArg R ih
                  }
              have hleft : Iterate R (t0 + a.val + k) n =
                  Iterate R (a.val + k) y := by
                rw [show t0 + a.val + k = t0 + (a.val + k) by omega,
                  IterateAdd]
              have hright : Iterate R (b.val + k) y =
                  Iterate R (t0 + a.val + (b.val - a.val) + k) n := by
                have hidx : t0 + a.val + (b.val - a.val) + k =
                    t0 + (b.val + k) := by omega
                rw [hidx]
                symm
                rw [IterateAdd]
              rw [hleft, htail, hright]
            }
        }
      · {
          refine ⟨t0 + b.val, a.val - b.val, ?_, ?_, ?_, ?_⟩
          · {
              have hb' : b.val ≤ 2 * p.C.natAbs :=
                Nat.le_of_lt_succ (by simpa [N] using b.isLt :
                  b.val < 2 * p.C.natAbs + 1)
              calc
                t0 + b.val ≤ n.natAbs + b.val :=
                  Nat.add_le_add_right ht0 b.val
                _ ≤ n.natAbs + 2 * p.C.natAbs :=
                  Nat.add_le_add_left hb' n.natAbs
            }
          · {
              omega
            }
          · {
              have hdiff : a.val - b.val ≤ a.val := Nat.sub_le a.val b.val
              have ha' : a.val ≤ 2 * p.C.natAbs :=
                Nat.le_of_lt_succ (by simpa [N] using a.isLt :
                  a.val < 2 * p.C.natAbs + 1)
              exact le_trans hdiff ha'
            }
          · {
              intro k
              have htail : Iterate R (b.val + k) y =
                  Iterate R (a.val + k) y := by
                induction k with
                | zero => {
                    simpa [Iterate] using hstate.symm
                  }
                | succ k ih => {
                    have hL : b.val + (k + 1) = b.val + k + 1 := by omega
                    have hRgt : a.val + (k + 1) = a.val + k + 1 := by omega
                    rw [hL, hRgt, Iterate, Iterate]
                    exact congrArg R ih
                  }
              have hleft : Iterate R (t0 + b.val + k) n =
                  Iterate R (b.val + k) y := by
                rw [show t0 + b.val + k = t0 + (b.val + k) by omega,
                  IterateAdd]
              have hright : Iterate R (a.val + k) y =
                  Iterate R (t0 + b.val + (a.val - b.val) + k) n := by
                have hidx : t0 + b.val + (a.val - b.val) + k =
                    t0 + (a.val + k) := by omega
                rw [hidx]
                symm
                rw [IterateAdd]
              rw [hleft, htail, hright]
            }
        }
    }

/-- The doubled-residue recurrence has only the constant solution `c/3`. -/
theorem DoubledResidueFixed (c : ℤ) (t : ℕ) (ht : 0 < t) (k : ℕ → ℤ)
    (hstep : ∀ i, i < t → 2 * k (i + 1) + k i = c) (hper : k t = k 0) :
    3 * k 0 = c := by
  have hform : ∀ n, n ≤ t → 3 * k 0 =
      3 * ((-2 : ℤ) ^ n) * k n + c * (1 - (-2 : ℤ) ^ n) := by
    intro n hn
    induction n with
    | zero => {
        simp
      }
    | succ n ih => {
        have hnlt : n < t := by omega
        have hrec := hstep n hnlt
        have hk : k n = c - 2 * k (n + 1) := by
          omega
        have ih' := ih (Nat.le_of_lt hnlt)
        rw [hk] at ih'
        have hpow : (-2 : ℤ) ^ (n + 1) = (-2) ^ n * (-2) := by
          rw [pow_succ]
        calc
          3 * k 0 =
              3 * ((-2 : ℤ) ^ n) * (c - 2 * k (n + 1)) +
                c * (1 - (-2 : ℤ) ^ n) := ih'
          _ = 3 * ((-2 : ℤ) ^ (n + 1)) * k (n + 1) +
                c * (1 - (-2 : ℤ) ^ (n + 1)) := by
            rw [hpow]
            ring
      }
  have hclosed := hform t (Nat.le_refl t)
  rw [hper] at hclosed
  have hfactor : (3 * k 0) * (1 - (-2 : ℤ) ^ t) =
      c * (1 - (-2 : ℤ) ^ t) := by
    have hmove : 3 * k 0 - 3 * ((-2 : ℤ) ^ t) * k 0 =
        c * (1 - (-2 : ℤ) ^ t) := by
      omega
    have hleft : 3 * k 0 - 3 * ((-2 : ℤ) ^ t) * k 0 =
        (3 * k 0) * (1 - (-2 : ℤ) ^ t) := by
      ring
    rw [← hleft]
    exact hmove
  have hunit : (1 : ℤ) - (-2 : ℤ) ^ t ≠ 0 := by
    intro hzero
    have habs : ((-2 : ℤ) ^ t).natAbs = 1 := by
      have : ((-2 : ℤ) ^ t) = 1 := by omega
      rw [this]
      rfl
    have hpow : ((-2 : ℤ) ^ t).natAbs = 2 ^ t := by
      rw [Int.natAbs_pow]
      rfl
    have hge : 2 ≤ 2 ^ t := by
      have : 1 ≤ t := ht
      have : 2 ^ 1 ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) this
      simpa using this
    omega
  exact Int.eq_of_mul_eq_mul_right hunit hfactor

/-- A nonempty initial segment of an orbit has a largest absolute value. -/
theorem MaxAbsOnPrefix (R : ℤ → ℤ) (k : ℕ) (hk : 0 < k) (x : ℤ) :
    ∃ i, i < k ∧ ∀ j, j < k →
      (Iterate R j x).natAbs ≤ (Iterate R i x).natAbs := by
  induction k with
  | zero => {
      omega
    }
  | succ k ih => {
      by_cases hk0 : k = 0
      · {
          refine ⟨0, by omega, ?_⟩
          intro j hj
          have hj0 : j = 0 := by omega
          simp [hj0]
        }
      · {
          obtain ⟨i, hi, hmax⟩ := ih (by omega)
          by_cases hle : (Iterate R k x).natAbs ≤ (Iterate R i x).natAbs
          · {
              refine ⟨i, by omega, ?_⟩
              intro j hj
              by_cases hjk : j < k
              · {
                  exact hmax j hjk
                }
              · {
                  have hjk' : j = k := by omega
                  simpa [hjk'] using hle
                }
            }
          · {
              refine ⟨k, by omega, ?_⟩
              intro j hj
              by_cases hjk : j < k
              · {
                  exact le_trans (hmax j hjk) (by omega)
                }
              · {
                  have hjk' : j = k := by omega
                  simp [hjk']
                }
            }
        }
    }

/-- A periodic point of divisor `-2` lies in the shell. -/
theorem NegTwoCycleShell (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (x : ℤ) (k : ℕ)
    (hk : 0 < k)
    (hret : Iterate (TotalReturn p (TwoEvery p hQ hcop)) k x = x) :
    x.natAbs ≤ p.C.natAbs := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  obtain ⟨i, hi, hmax⟩ := MaxAbsOnPrefix R k hk x
  let z := Iterate R i x
  have hpred : ∃ w, x.natAbs ≤ z.natAbs ∧ R w = z ∧
      w.natAbs ≤ z.natAbs := by
    by_cases hi0 : i = 0
    · {
        refine ⟨Iterate R (k - 1) x, ?_, ?_, ?_⟩
        · {
            simp [z, hi0, Iterate]
          }
        · {
            have hk1 : k - 1 + 1 = k := by omega
            have hstep : Iterate R k x = R (Iterate R (k - 1) x) := by
              rw [← hk1]
              simp [Iterate]
            rw [hret] at hstep
            have hz : z = x := by
              simp [z, hi0, Iterate]
            rw [hz]
            exact hstep.symm
          }
        · {
            have hlt : k - 1 < k := by omega
            simpa [z, hi0] using hmax (k - 1) hlt
          }
      }
    · {
        refine ⟨Iterate R (i - 1) x, ?_, ?_, ?_⟩
        · {
            have h0 : Iterate R 0 x = x := by
              simp [Iterate]
            rw [← h0]
            simpa [z] using hmax 0 hk
          }
        · {
            have hi1 : i - 1 + 1 = i := by omega
            have hstep : Iterate R i x = R (Iterate R (i - 1) x) := by
              rw [← hi1]
              simp [Iterate]
            simpa [z] using hstep.symm
          }
        · {
            have hlt : i - 1 < k := by omega
            simpa [z] using hmax (i - 1) hlt
          }
      }
  obtain ⟨w, _hxle, hRw, hwle⟩ := hpred
  have hzle : z.natAbs ≤ p.C.natAbs := by
    by_contra hgt
    have hgt' : p.C.natAbs < z.natAbs := by omega
    by_cases hwo : p.C.natAbs < w.natAbs
    · {
        have hdrop := NegTwoDrops p hQ hD hcop w hwo
        have hdropR : (R w).natAbs ≤ w.natAbs - 1 := by
          simpa [R] using hdrop
        rw [hRw] at hdropR
        omega
      }
    · {
        have hwshell : w.natAbs ≤ p.C.natAbs := by omega
        have himg := NegTwoShell p hQ hD hcop w hwshell
        have himgR : (R w).natAbs ≤ p.C.natAbs := by
          simpa [R] using himg
        rw [hRw] at himgR
        omega
      }
  exact le_trans (hmax 0 hk) hzle

/-- The positive endpoint goes to its negative, and that negative goes to zero. -/
theorem NegTwoEndpoints (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (_hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) :
    TotalReturn p (TwoEvery p hQ hcop) p.C = -p.C ∧
      TotalReturn p (TwoEvery p hQ hcop) (-p.C) = 0 := by
  have hodd : ¬ (2 : ℤ) ∣ p.C := NegTwoOffsetOdd p hD hcop
  have hnegodd : ¬ (2 : ℤ) ∣ -p.C := by
    intro hdiv
    exact hodd ((Int.dvd_neg).mp hdiv)
  constructor
  · {
      rw [NegTwoFormulaOdd p hQ hD hcop p.C hodd]
      have htwo : (2 : ℤ) * p.C = p.C + p.C := by
        ring
      have hhalf : (p.C + p.C) / 2 = p.C := by
        rw [← htwo]
        exact Int.mul_ediv_cancel_left p.C (by decide)
      rw [hhalf]
    }
  · {
      rw [NegTwoFormulaOdd p hQ hD hcop (-p.C) hnegodd]
      simp
    }

/-- Neither endpoint returns. -/
theorem NegTwoEndpointNotPeriodic (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hpos : 0 < p.C)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (k : ℕ) (hk : 0 < k) :
    Iterate (TotalReturn p (TwoEvery p hQ hcop)) k p.C ≠ p.C ∧
      Iterate (TotalReturn p (TwoEvery p hQ hcop)) k (-p.C) ≠ -p.C := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  have hends := NegTwoEndpoints p hQ hD hpos hcop
  have hzero : ∀ j, Iterate R j 0 = 0 := by
    intro j
    induction j with
    | zero => {
        simp [Iterate]
      }
    | succ j ih => {
        simp [Iterate, ih, R, NegTwoZeroFixed p hQ hD hcop]
      }
  have htwo : Iterate R 2 p.C = 0 := by
    simp [Iterate, R, hends.1, hends.2]
  have hstay : ∀ j, Iterate R (2 + j) p.C = 0 := by
    intro j
    rw [IterateAdd, htwo, hzero]
  constructor
  · {
      intro hret
      by_cases hk1 : k = 1
      · {
          have hstep : Iterate R 1 p.C = R p.C := by
            simp [Iterate]
          rw [hk1, hstep] at hret
          simp [R, hends.1] at hret
          omega
        }
      · {
          have hk2 : 2 ≤ k := by omega
          have htail := hstay (k - 2)
          have hidx : 2 + (k - 2) = k := by omega
          rw [hidx] at htail
          rw [htail] at hret
          omega
        }
    }
  · {
      intro hret
      have hone : Iterate R 1 (-p.C) = 0 := by
        simp [Iterate, R, hends.2]
      have hstayneg : ∀ j, Iterate R (1 + j) (-p.C) = 0 := by
        intro j
        rw [IterateAdd, hone, hzero]
      have htail := hstayneg (k - 1)
      have hidx : 1 + (k - 1) = k := by omega
      rw [hidx] at htail
      rw [htail] at hret
      omega
    }

/-- A nonzero periodic point lies strictly inside the positive shell. -/
theorem NegTwoCycleOpen (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (x : ℤ)
    (hx : x ≠ 0) (k : ℕ) (hk : 0 < k)
    (hret : Iterate (TotalReturn p (TwoEvery p hQ hcop)) k x = x) :
    0 < x.natAbs ∧ x.natAbs < p.C.natAbs := by
  have hshell := NegTwoCycleShell p hQ hD hcop x k hk hret
  have hposabs : 0 < x.natAbs := by
    omega
  refine ⟨hposabs, ?_⟩
  by_contra hge
  have heq : x.natAbs = p.C.natAbs := by
    omega
  have hcabs : (p.C.natAbs : ℤ) = p.C :=
    Int.natAbs_of_nonneg (le_of_lt hpos)
  have hsign : x = (x.natAbs : ℤ) ∨ x = -((x.natAbs : ℤ)) := by
    cases x with
    | ofNat _ => {
        left
        rfl
      }
    | negSucc _ => {
        right
        rfl
      }
  rw [heq, hcabs] at hsign
  rcases hsign with hposx | hnegx
  · {
      have hnot := (NegTwoEndpointNotPeriodic p hQ hD hpos hcop k hk).1
      rw [← hposx] at hnot
      exact hnot hret
    }
  · {
      have hnot := (NegTwoEndpointNotPeriodic p hQ hD hpos hcop k hk).2
      rw [← hnegx] at hnot
      exact hnot hret
    }

/-- An even seed and the seed shifted by the odd offset have the same return. -/
theorem NegTwoEvenSameImage (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (k : ℤ)
    (heven : (2 : ℤ) ∣ k) (hodd : ¬ (2 : ℤ) ∣ k - p.C) :
    TotalReturn p (TwoEvery p hQ hcop) k =
      TotalReturn p (TwoEvery p hQ hcop) (k - p.C) := by
  rw [NegTwoFormulaEven p hQ hD hcop k heven,
    NegTwoFormulaOdd p hQ hD hcop (k - p.C) hodd]
  have hnum : k - p.C + p.C = k := by
    ring
  rw [hnum]

/-- A return shifts every later time by the same amount. -/
theorem IteratePeriodShift (R : ℤ → ℤ) (d m : ℕ) (y : ℤ)
    (h : Iterate R d y = y) :
    Iterate R (d + m) y = Iterate R m y := by
  induction m with
  | zero => {
      simpa [Iterate] using h
    }
  | succ m ih => {
      simp [Iterate, ih]
    }

/-- Distinct times before a minimal return give distinct states. -/
theorem MinimalReturnDistinct (R : ℤ → ℤ) (x : ℤ) (k i j : ℕ)
    (_hk : 0 < k) (hret : Iterate R k x = x)
    (hmin : ∀ d, 0 < d → d < k → Iterate R d x ≠ x)
    (hi : i < j) (hj : j < k) :
    Iterate R i x ≠ Iterate R j x := by
  intro heq
  have hd : 0 < j - i := by omega
  have hdk : j - i < k := by omega
  have hy : Iterate R (j - i) (Iterate R i x) = Iterate R i x := by
    rw [← IterateAdd, Nat.add_sub_of_le (Nat.le_of_lt hi)]
    exact heq.symm
  have hxback : Iterate R (k - i) (Iterate R i x) = x := by
    rw [← IterateAdd]
    have hidx : i + (k - i) = k := by omega
    simpa [hidx] using hret
  have hshift := IteratePeriodShift R (j - i) (k - i)
    (Iterate R i x) hy
  have hxperiod : Iterate R (j - i) x = x := by
    rw [← hxback]
    have hcomm : j - i + (k - i) = (k - i) + (j - i) := by omega
    rw [← IterateAdd, ← hcomm]
    exact hshift
  exact hmin (j - i) hd hdk hxperiod

/-- Equal images on a minimal cycle come from the same state. -/
theorem MinimalCycleInjective (R : ℤ → ℤ) (x a b : ℤ) (k : ℕ)
    (hk : 0 < k) (hret : Iterate R k x = x)
    (hmin : ∀ d, 0 < d → d < k → Iterate R d x ≠ x)
    (i j : ℕ) (hi : i < k) (hj : j < k)
    (ha : Iterate R i x = a) (hb : Iterate R j x = b)
    (himg : R a = R b) : a = b := by
  have hstepi : Iterate R (i + 1) x = R a := by
    rw [← ha]
    simp [Iterate]
  have hstepj : Iterate R (j + 1) x = R b := by
    rw [← hb]
    simp [Iterate]
  have hsame : Iterate R (i + 1) x = Iterate R (j + 1) x := by
    rw [hstepi, hstepj, himg]
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · {
      have hlt1 : i + 1 < j + 1 := by omega
      by_cases hjk : j + 1 < k
      · {
          exact False.elim
            (MinimalReturnDistinct R x k (i + 1) (j + 1) hk hret hmin
              hlt1 hjk hsame)
        }
      · {
          have hj1 : j + 1 = k := by omega
          have hback : Iterate R (i + 1) x = x := by
            rw [hsame, hj1, hret]
          have hi1 : 0 < i + 1 := by omega
          have hik : i + 1 < k := by omega
          exact False.elim (hmin (i + 1) hi1 hik hback)
        }
    }
  · {
      rw [← ha, ← hb, heq]
    }
  · {
      have hgt1 : j + 1 < i + 1 := by omega
      by_cases hik : i + 1 < k
      · {
          exact False.elim
            (MinimalReturnDistinct R x k (j + 1) (i + 1) hk hret hmin
              hgt1 hik hsame.symm)
        }
      · {
          have hi1 : i + 1 = k := by omega
          have hback : Iterate R (j + 1) x = x := by
            rw [← hsame, hi1, hret]
          have hj1 : 0 < j + 1 := by omega
          have hjk : j + 1 < k := by omega
          exact False.elim (hmin (j + 1) hj1 hjk hback)
        }
    }

/-- A minimal cycle contains at most one of an even residue and its shift. -/
theorem NegTwoEvenNotBoth (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (u : ℤ) (heven : (2 : ℤ) ∣ u) (x : ℤ) (k i j : ℕ)
    (hk : 0 < k) (hret : Iterate (TotalReturn p (TwoEvery p hQ hcop)) k x = x)
    (hmin : ∀ d, 0 < d → d < k →
      Iterate (TotalReturn p (TwoEvery p hQ hcop)) d x ≠ x)
    (hi : i < k) (hj : j < k)
    (hu : Iterate (TotalReturn p (TwoEvery p hQ hcop)) i x = u)
    (hshift : Iterate (TotalReturn p (TwoEvery p hQ hcop)) j x = u - p.C) :
    False := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  have hoddC : ¬ (2 : ℤ) ∣ p.C := NegTwoOffsetOdd p hD hcop
  have hodd : ¬ (2 : ℤ) ∣ u - p.C := by
    intro hdiv
    have hsub : u - (u - p.C) = p.C := by
      ring
    have hcdiv : (2 : ℤ) ∣ p.C := by
      rw [← hsub]
      exact Int.dvd_sub heven hdiv
    exact hoddC hcdiv
  have himg := NegTwoEvenSameImage p hQ hD hcop u heven hodd
  have hequal : u = u - p.C :=
    MinimalCycleInjective R x u (u - p.C) k hk hret hmin i j hi hj hu
      hshift (by simpa [R] using himg)
  omega

/-- An odd positive residue and its shift step to the next residue. -/
theorem NegTwoOddPair (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (_hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (u : ℤ) (_hu0 : 0 < u) (_huc : u < p.C) (hodd : ¬ (2 : ℤ) ∣ u) :
    let a := (p.C - u) / 2
    TotalReturn p (TwoEvery p hQ hcop) u = a - p.C ∧
      TotalReturn p (TwoEvery p hQ hcop) (u - p.C) = a := by
  intro a
  have hoddC : ¬ (2 : ℤ) ∣ p.C := NegTwoOffsetOdd p hD hcop
  have hevenDiff : (2 : ℤ) ∣ p.C - u := TwoOddSum p.C (-u)
    hoddC (by
      intro hdiv
      exact hodd ((Int.dvd_neg).mp hdiv))
  have hevenShift : (2 : ℤ) ∣ u - p.C := by
    have hneg : (2 : ℤ) ∣ -(p.C - u) := Int.dvd_neg.mpr hevenDiff
    simpa using hneg
  have ha : (2 : ℤ) * a = p.C - u := by
    simpa [a] using Int.mul_ediv_cancel' hevenDiff
  constructor
  · {
      rw [NegTwoFormulaOdd p hQ hD hcop u hodd]
      have hsum : (2 : ℤ) ∣ u + p.C := TwoOddSum u p.C hodd hoddC
      have hhalf : (2 : ℤ) * ((u + p.C) / 2) = u + p.C :=
        Int.mul_ediv_cancel' hsum
      have htarget : (2 : ℤ) * (p.C - a) = u + p.C := by
        have hsub : (2 : ℤ) * (p.C - a) = 2 * p.C - 2 * a := by
          ring
        rw [hsub, ha]
        ring
      have hquot : (u + p.C) / 2 = p.C - a := by
        apply Int.eq_of_mul_eq_mul_left (by decide : (2 : ℤ) ≠ 0)
        rw [hhalf, htarget]
      rw [hquot]
      ring
    }
  · {
      rw [NegTwoFormulaEven p hQ hD hcop (u - p.C) hevenShift]
      have hneg : (2 : ℤ) * (-a) = u - p.C := by
        have hsub : (2 : ℤ) * (-a) = -(2 * a) := by
          ring
        rw [hsub, ha]
        ring
      have hhalf : (2 : ℤ) * ((u - p.C) / 2) = u - p.C :=
        Int.mul_ediv_cancel' hevenShift
      have hquot : (u - p.C) / 2 = -a := by
        apply Int.eq_of_mul_eq_mul_left (by decide : (2 : ℤ) ≠ 0)
        rw [hhalf, hneg]
      rw [hquot]
      ring
    }

/-- The next odd residue lies strictly between zero and the offset. -/
theorem NegTwoOddNextRange (p : Parameters) (_hpos : 0 < p.C)
    (u : ℤ) (hu0 : 0 < u) (huc : u < p.C) (hodd : ¬ (2 : ℤ) ∣ u)
    (hoddC : ¬ (2 : ℤ) ∣ p.C) :
    0 < (p.C - u) / 2 ∧ (p.C - u) / 2 < p.C := by
  have hposdiff : 0 < p.C - u := by omega
  have heven : (2 : ℤ) ∣ p.C - u := TwoOddSum p.C (-u) hoddC
    (by
      intro hdiv
      exact hodd ((Int.dvd_neg).mp hdiv))
  have htwo : (2 : ℤ) * ((p.C - u) / 2) = p.C - u :=
    Int.mul_ediv_cancel' heven
  constructor
  · {
      omega
    }
  · {
      omega
    }

/-- The positive residue of an interior state. -/
def OpenResidue (c x : ℤ) : ℤ :=
  if 0 ≤ x then x else x + c

/-- An interior state has residue strictly between zero and the offset. -/
theorem OpenResidueRange (c x : ℤ) (hc : 0 < c) (hx0 : x ≠ 0)
    (habs : x.natAbs < c.natAbs) :
    0 < OpenResidue c x ∧ OpenResidue c x < c := by
  have hcabs : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg (le_of_lt hc)
  unfold OpenResidue
  by_cases hx : 0 ≤ x
  · {
      simp [hx]
      have hcast : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg hx
      have hlt : x < c := by
        rw [← hcast, ← hcabs]
        exact_mod_cast habs
      omega
    }
  · {
      simp [hx]
      have hneg : x < 0 := by omega
      have hcast : (x.natAbs : ℤ) = -x := by
        rw [← Int.natAbs_neg]
        exact Int.natAbs_of_nonneg (by omega : 0 ≤ -x)
      have hlt : -x < c := by
        rw [← hcast, ← hcabs]
        exact_mod_cast habs
      have hposx : 0 < x + c := by omega
      omega
    }

/-- An interior state is its residue or that residue minus the offset. -/
theorem OpenResidueSplit (c x : ℤ) :
    x = OpenResidue c x ∨ x = OpenResidue c x - c := by
  unfold OpenResidue
  by_cases hx : 0 ≤ x
  · {
      simp [hx]
    }
  · {
      simp [hx]
    }

/-- Equal residues are the two representatives of one class. -/
theorem SameResiduePair (c x y : ℤ)
    (heq : OpenResidue c x = OpenResidue c y) (hne : x ≠ y) :
    (x = OpenResidue c x ∧ y = OpenResidue c x - c) ∨
      (y = OpenResidue c x ∧ x = OpenResidue c x - c) := by
  have hx := OpenResidueSplit c x
  have hy := OpenResidueSplit c y
  rw [← heq] at hy
  rcases hx with hx | hx
  · {
      rcases hy with hy | hy
      · {
          exact False.elim (hne (by rw [hx, hy]))
        }
      · {
          left
          exact ⟨hx, hy⟩
        }
    }
  · {
      rcases hy with hy | hy
      · {
          right
          exact ⟨hy, hx⟩
        }
      · {
          exact False.elim (hne (by rw [hx, hy]))
        }
    }

/-- Pairwise distinct interior residues number at most `|c| - 1`. -/
theorem DistinctResidueBound (c : ℤ) (hc : 0 < c) (s : ℕ → ℤ) (k : ℕ)
    (hrange : ∀ i, i < k →
      0 < OpenResidue c (s i) ∧ OpenResidue c (s i) < c)
    (hinj : ∀ i j, i < k → j < k → i ≠ j →
      OpenResidue c (s i) ≠ OpenResidue c (s j)) :
    k ≤ c.natAbs - 1 := by
  by_cases hk0 : k = 0
  · {
      omega
    }
  · {
      have hcabs : (c.natAbs : ℤ) = c := Int.natAbs_of_nonneg (le_of_lt hc)
      have hr0 := hrange 0 (by omega)
      have hto0 : ((OpenResidue c (s 0)).toNat : ℤ) =
          OpenResidue c (s 0) :=
        Int.toNat_of_nonneg (le_of_lt hr0.1)
      have hlt0 : (OpenResidue c (s 0)).toNat < c.natAbs := by
        have hlt : OpenResidue c (s 0) < (c.natAbs : ℤ) := by
          rw [hcabs]
          exact hr0.2
        rw [← hto0] at hlt
        exact_mod_cast hlt
      have hpos0 : 0 < (OpenResidue c (s 0)).toNat := by
        have hpos : (0 : ℤ) < (OpenResidue c (s 0)).toNat := by
          rw [hto0]
          exact hr0.1
        exact_mod_cast hpos
      let f : Fin k → Fin (c.natAbs - 1) := fun i =>
        ⟨(OpenResidue c (s i.val)).toNat - 1, by
          have hr := hrange i.val i.isLt
          have hto : ((OpenResidue c (s i.val)).toNat : ℤ) =
              OpenResidue c (s i.val) :=
            Int.toNat_of_nonneg (le_of_lt hr.1)
          have hlt : (OpenResidue c (s i.val)).toNat < c.natAbs := by
            have hlt' : OpenResidue c (s i.val) < (c.natAbs : ℤ) := by
              rw [hcabs]
              exact hr.2
            rw [← hto] at hlt'
            exact_mod_cast hlt'
          have hpos : 0 < (OpenResidue c (s i.val)).toNat := by
            have hpos' : (0 : ℤ) < (OpenResidue c (s i.val)).toNat := by
              rw [hto]
              exact hr.1
            exact_mod_cast hpos'
          omega⟩
      have hinjF : Function.Injective f := by
        intro a b hab
        have hval : (OpenResidue c (s a.val)).toNat =
            (OpenResidue c (s b.val)).toNat := by
          have hsub := congrArg Fin.val hab
          dsimp [f] at hsub
          have ha := hrange a.val a.isLt
          have hb := hrange b.val b.isLt
          have htoa : ((OpenResidue c (s a.val)).toNat : ℤ) =
              OpenResidue c (s a.val) :=
            Int.toNat_of_nonneg (le_of_lt ha.1)
          have htob : ((OpenResidue c (s b.val)).toNat : ℤ) =
              OpenResidue c (s b.val) :=
            Int.toNat_of_nonneg (le_of_lt hb.1)
          have hposa : 0 < (OpenResidue c (s a.val)).toNat := by
            have hpos' : (0 : ℤ) < (OpenResidue c (s a.val)).toNat := by
              rw [htoa]
              exact ha.1
            exact_mod_cast hpos'
          have hposb : 0 < (OpenResidue c (s b.val)).toNat := by
            have hpos' : (0 : ℤ) < (OpenResidue c (s b.val)).toNat := by
              rw [htob]
              exact hb.1
            exact_mod_cast hpos'
          omega
        have ha := hrange a.val a.isLt
        have hb := hrange b.val b.isLt
        have hres : OpenResidue c (s a.val) = OpenResidue c (s b.val) := by
          have htoa : ((OpenResidue c (s a.val)).toNat : ℤ) =
              OpenResidue c (s a.val) :=
            Int.toNat_of_nonneg (le_of_lt ha.1)
          have htob : ((OpenResidue c (s b.val)).toNat : ℤ) =
              OpenResidue c (s b.val) :=
            Int.toNat_of_nonneg (le_of_lt hb.1)
          rw [← htoa, ← htob, hval]
        have hidx : a.val = b.val := by
          by_contra hne
          exact hinj a.val b.val a.isLt b.isLt hne hres
        exact Fin.ext hidx
      have hcard := Fintype.card_le_of_injective f hinjF
      simpa [Fintype.card_fin] using hcard
    }

/-- A minimal cycle with distinct residues has length at most `|c| - 1`. -/
theorem NegTwoDistinctPeriod (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (x : ℤ) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k)
    (hret : Iterate (TotalReturn p (TwoEvery p hQ hcop)) k x = x)
    (_hmin : ∀ d, 0 < d → d < k →
      Iterate (TotalReturn p (TwoEvery p hQ hcop)) d x ≠ x)
    (hdist : ∀ i j, i < k → j < k → i ≠ j →
      OpenResidue p.C
          (Iterate (TotalReturn p (TwoEvery p hQ hcop)) i x) ≠
        OpenResidue p.C
          (Iterate (TotalReturn p (TwoEvery p hQ hcop)) j x)) :
    k ≤ p.C.natAbs - 1 := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  have hrange : ∀ i, i < k →
      0 < OpenResidue p.C (Iterate R i x) ∧
        OpenResidue p.C (Iterate R i x) < p.C := by
    intro i hi
    have hback : Iterate R (k - i) (Iterate R i x) = x := by
      rw [← IterateAdd]
      have hidx : i + (k - i) = k := by omega
      simpa [hidx] using hret
    have hnonzero : Iterate R i x ≠ 0 := by
      intro hzero
      have hx0 : x = 0 := by
        have hfix := NegTwoZeroFixed p hQ hD hcop
        have htail : Iterate R (k - i) 0 = 0 := by
          induction (k - i) with
          | zero => {
              simp [Iterate]
            }
          | succ n ihn => {
              rw [Iterate, ihn]
              simpa [R] using hfix
            }
        rw [hzero] at hback
        rw [htail] at hback
        exact hback.symm
      exact hx hx0
    have hyret : Iterate R k (Iterate R i x) = Iterate R i x := by
      rw [← IterateAdd]
      have hcomm : i + k = k + i := by omega
      rw [hcomm, IterateAdd, hret]
    have hopen := NegTwoCycleOpen p hQ hD hpos hcop (Iterate R i x)
      hnonzero k hk hyret
    exact OpenResidueRange p.C (Iterate R i x) hpos hnonzero hopen.2
  exact DistinctResidueBound p.C hpos (fun i => Iterate R i x) k hrange
    (by
      intro i j hi hj hne
      simpa [R] using hdist i j hi hj hne)

/-- A state occurs among the first `k` iterates. -/
def OnCycle (R : ℤ → ℤ) (x : ℤ) (k : ℕ) (y : ℤ) : Prop :=
  ∃ i, i < k ∧ Iterate R i x = y

/-- The return of a cycle state is again a cycle state. -/
theorem OnCycleStep (R : ℤ → ℤ) (x : ℤ) (k : ℕ) (hk : 0 < k)
    (hret : Iterate R k x = x) {y : ℤ} (hy : OnCycle R x k y) :
    OnCycle R x k (R y) := by
  obtain ⟨i, hi, hiy⟩ := hy
  by_cases hlast : i + 1 < k
  · {
      refine ⟨i + 1, hlast, ?_⟩
      rw [Iterate, hiy]
    }
  · {
      have hi' : i = k - 1 := by omega
      refine ⟨0, hk, ?_⟩
      have hstep : Iterate R (i + 1) x = R y := by
        rw [Iterate, hiy]
      have hidx : i + 1 = k := by omega
      rw [hidx] at hstep
      rw [hret] at hstep
      have h0 : Iterate R 0 x = x := by
        simp [Iterate]
      rw [h0]
      exact hstep
    }

/-- A repeated residue on a minimal cycle is odd and has both representatives. -/
theorem NegTwoCollisionOdd (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (x : ℤ) (hx : x ≠ 0) (k : ℕ) (hk : 0 < k)
    (hret : Iterate (TotalReturn p (TwoEvery p hQ hcop)) k x = x)
    (hmin : ∀ d, 0 < d → d < k →
      Iterate (TotalReturn p (TwoEvery p hQ hcop)) d x ≠ x)
    (i j : ℕ) (hij : i < j) (hj : j < k)
    (heq : OpenResidue p.C
        (Iterate (TotalReturn p (TwoEvery p hQ hcop)) i x) =
      OpenResidue p.C
        (Iterate (TotalReturn p (TwoEvery p hQ hcop)) j x)) :
    ∃ u, 0 < u ∧ u < p.C ∧ ¬ (2 : ℤ) ∣ u ∧
      OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k u ∧
      OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k (u - p.C) := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  have hdist := MinimalReturnDistinct R x k i j hk hret hmin hij hj
  have hpair := SameResiduePair p.C (Iterate R i x) (Iterate R j x)
    (by simpa [R] using heq) hdist
  have hopen (t : ℕ) (ht : t < k) :
      0 < (Iterate R t x).natAbs ∧
        (Iterate R t x).natAbs < p.C.natAbs := by
    have hnonzero : Iterate R t x ≠ 0 := by
      intro hzero
      have hback : Iterate R (k - t) (Iterate R t x) = x := by
        rw [← IterateAdd]
        have hidx : t + (k - t) = k := by omega
        simpa [hidx] using hret
      have hfix := NegTwoZeroFixed p hQ hD hcop
      have htail : Iterate R (k - t) 0 = 0 := by
        induction (k - t) with
        | zero => {
            simp [Iterate]
          }
        | succ n ihn => {
            rw [Iterate, ihn]
            simpa [R] using hfix
          }
      rw [hzero, htail] at hback
      exact hx hback.symm
    have hyret : Iterate R k (Iterate R t x) = Iterate R t x := by
      rw [← IterateAdd]
      have hcomm : t + k = k + t := by omega
      rw [hcomm, IterateAdd, hret]
    exact NegTwoCycleOpen p hQ hD hpos hcop (Iterate R t x) hnonzero k hk
      hyret
  have hres : 0 < OpenResidue p.C (Iterate R i x) ∧
      OpenResidue p.C (Iterate R i x) < p.C :=
    OpenResidueRange p.C (Iterate R i x) hpos
      (by
        intro hzero
        have hopeni := hopen i (by omega)
        omega) (hopen i (by omega)).2
  let u := OpenResidue p.C (Iterate R i x)
  have hu0 : 0 < u := hres.1
  have huc : u < p.C := hres.2
  rcases hpair with hleft | hright
  · {
      have hodd : ¬ (2 : ℤ) ∣ u := by
        intro heven
        exact NegTwoEvenNotBoth p hQ hD hpos hcop u heven x k i j hk hret
          hmin (by omega) hj (by simpa [R, u] using hleft.1)
          (by simpa [R, u] using hleft.2)
      refine ⟨u, hu0, huc, hodd, ?_, ?_⟩
      · {
          exact ⟨i, by omega, by simpa [R, u] using hleft.1⟩
        }
      · {
          exact ⟨j, hj, by simpa [R, u] using hleft.2⟩
        }
    }
  · {
      have hodd : ¬ (2 : ℤ) ∣ u := by
        intro heven
        exact NegTwoEvenNotBoth p hQ hD hpos hcop u heven x k j i hk hret
          hmin hj (by omega) (by simpa [R, u] using hright.1)
          (by simpa [R, u] using hright.2)
      refine ⟨u, hu0, huc, hodd, ?_, ?_⟩
      · {
          exact ⟨j, hj, by simpa [R, u] using hright.1⟩
        }
      · {
          exact ⟨i, by omega, by simpa [R, u] using hright.2⟩
        }
    }

/-- Both representatives of an odd residue produce both representatives of the next one. -/
theorem NegTwoNextDoubled (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (x : ℤ) (k : ℕ) (hk : 0 < k)
    (hret : Iterate (TotalReturn p (TwoEvery p hQ hcop)) k x = x)
    (hmin : ∀ d, 0 < d → d < k →
      Iterate (TotalReturn p (TwoEvery p hQ hcop)) d x ≠ x)
    (u : ℤ) (hu0 : 0 < u) (huc : u < p.C) (hodd : ¬ (2 : ℤ) ∣ u)
    (hposU : OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k u)
    (hnegU : OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k (u - p.C)) :
    let a := (p.C - u) / 2
    0 < a ∧ a < p.C ∧ ¬ (2 : ℤ) ∣ a ∧
      OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k a ∧
      OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k (a - p.C) := by
  intro a
  let R := TotalReturn p (TwoEvery p hQ hcop)
  have hpair := NegTwoOddPair p hQ hD hpos hcop u hu0 huc hodd
  have hrange := NegTwoOddNextRange p hpos u hu0 huc hodd
    (NegTwoOffsetOdd p hD hcop)
  have hnegImg : OnCycle R x k (a - p.C) := by
    have hstep := OnCycleStep R x k hk hret hposU
    simpa [R, a, hpair.1] using hstep
  have hposImg : OnCycle R x k a := by
    have hstep := OnCycleStep R x k hk hret hnegU
    simpa [R, a, hpair.2] using hstep
  have hoddA : ¬ (2 : ℤ) ∣ a := by
    intro heven
    obtain ⟨i, hi, hia⟩ := hposImg
    obtain ⟨j, hj, hja⟩ := hnegImg
    exact NegTwoEvenNotBoth p hQ hD hpos hcop a heven x k i j hk hret hmin
      hi hj (by simpa [R] using hia) (by simpa [R, a] using hja)
  exact ⟨hrange.1, hrange.2, hoddA, by simpa [R] using hposImg,
    by simpa [R] using hnegImg⟩

/-- The positive residue after `n` odd steps. -/
def OddResidueIter (c u : ℤ) : ℕ → ℤ
  | 0 => u
  | n + 1 => (c - OddResidueIter c u n) / 2

/-- Every iterated odd residue stays doubled on the cycle. -/
theorem OddResidueIterDoubled (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (x : ℤ) (k : ℕ) (hk : 0 < k)
    (hret : Iterate (TotalReturn p (TwoEvery p hQ hcop)) k x = x)
    (hmin : ∀ d, 0 < d → d < k →
      Iterate (TotalReturn p (TwoEvery p hQ hcop)) d x ≠ x)
    (u : ℤ) (hu0 : 0 < u) (huc : u < p.C) (hodd : ¬ (2 : ℤ) ∣ u)
    (hposU : OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k u)
    (hnegU : OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k (u - p.C))
    (n : ℕ) :
    let a := OddResidueIter p.C u n
    0 < a ∧ a < p.C ∧ ¬ (2 : ℤ) ∣ a ∧
      OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k a ∧
      OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k (a - p.C) := by
  intro a
  induction n with
  | zero => {
      have ha : a = u := by
        simp [OddResidueIter, a]
      rw [ha]
      exact ⟨hu0, huc, hodd, hposU, hnegU⟩
    }
  | succ n ih => {
      have hprev := ih
      dsimp [OddResidueIter] at hprev ⊢
      have hnext := NegTwoNextDoubled p hQ hD hpos hcop x k hk hret hmin
        (OddResidueIter p.C u n) hprev.1 hprev.2.1 hprev.2.2.1
        hprev.2.2.2.1 hprev.2.2.2.2
      simpa [a, OddResidueIter] using hnext
    }

/-- Each odd step satisfies `2 a(n+1) + a(n) = c`. -/
theorem OddResidueStepRel (c u : ℤ) (n : ℕ)
    (hodd : ¬ (2 : ℤ) ∣ OddResidueIter c u n)
    (hoddC : ¬ (2 : ℤ) ∣ c) :
    2 * OddResidueIter c u (n + 1) + OddResidueIter c u n = c := by
  have hneg : ¬ (2 : ℤ) ∣ -(OddResidueIter c u n) := by
    intro hdiv
    exact hodd ((Int.dvd_neg).mp hdiv)
  have heven : (2 : ℤ) ∣ c - OddResidueIter c u n :=
    TwoOddSum c (-(OddResidueIter c u n)) hoddC hneg
  have hmul : (2 : ℤ) * ((c - OddResidueIter c u n) / 2) =
      c - OddResidueIter c u n :=
    Int.mul_ediv_cancel' heven
  have hdef : OddResidueIter c u (n + 1) =
      (c - OddResidueIter c u n) / 2 := by
    simp [OddResidueIter]
  rw [hdef]
  omega

/-- The first `k + 1` iterated residues are not pairwise distinct. -/
theorem OddResidueRepeat (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (x : ℤ) (k : ℕ) (hk : 0 < k)
    (hret : Iterate (TotalReturn p (TwoEvery p hQ hcop)) k x = x)
    (hmin : ∀ d, 0 < d → d < k →
      Iterate (TotalReturn p (TwoEvery p hQ hcop)) d x ≠ x)
    (u : ℤ) (hu0 : 0 < u) (huc : u < p.C) (hodd : ¬ (2 : ℤ) ∣ u)
    (hposU : OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k u)
    (hnegU : OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k (u - p.C)) :
    ∃ i j, i < j ∧ j ≤ k ∧
      OddResidueIter p.C u i = OddResidueIter p.C u j := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  let f : Fin (k + 1) → Fin k := fun n =>
    let h := OddResidueIterDoubled p hQ hD hpos hcop x k hk hret hmin u
      hu0 huc hodd hposU hnegU n.val
    ⟨Classical.choose h.2.2.2.1, (Classical.choose_spec h.2.2.2.1).1⟩
  have hcard : Fintype.card (Fin k) < Fintype.card (Fin (k + 1)) := by
    simp [Fintype.card_fin]
  obtain ⟨a, b, hne, hab⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hval : OddResidueIter p.C u a.val = OddResidueIter p.C u b.val := by
    have ha := OddResidueIterDoubled p hQ hD hpos hcop x k hk hret hmin u
      hu0 huc hodd hposU hnegU a.val
    have hb := OddResidueIterDoubled p hQ hD hpos hcop x k hk hret hmin u
      hu0 huc hodd hposU hnegU b.val
    have hia := Classical.choose_spec ha.2.2.2.1
    have hib := Classical.choose_spec hb.2.2.2.1
    have htimes : Classical.choose ha.2.2.2.1 =
        Classical.choose hb.2.2.2.1 := by
      have hfin := congrArg Fin.val hab
      simpa [f] using hfin
    rw [← hia.2, ← hib.2, htimes]
  rcases Nat.lt_trichotomy a.val b.val with hlt | heq | hgt
  · {
      exact ⟨a.val, b.val, hlt, by omega, hval⟩
    }
  · {
      exact False.elim (hne (Fin.ext heq))
    }
  · {
      exact ⟨b.val, a.val, hgt, by omega, hval.symm⟩
    }

/-- Equal successors come from equal residues. -/
theorem OddResiduePrev (c u : ℤ) (n m : ℕ)
    (hstepn : 2 * OddResidueIter c u (n + 1) + OddResidueIter c u n = c)
    (hstepm : 2 * OddResidueIter c u (m + 1) + OddResidueIter c u m = c)
    (heq : OddResidueIter c u (n + 1) = OddResidueIter c u (m + 1)) :
    OddResidueIter c u n = OddResidueIter c u m := by
  omega

/-- Some positive iterate returns to the starting residue, and every earlier step is legal. -/
theorem OddResidueReturns (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (x : ℤ) (k : ℕ) (hk : 0 < k)
    (hret : Iterate (TotalReturn p (TwoEvery p hQ hcop)) k x = x)
    (hmin : ∀ d, 0 < d → d < k →
      Iterate (TotalReturn p (TwoEvery p hQ hcop)) d x ≠ x)
    (u : ℤ) (hu0 : 0 < u) (huc : u < p.C) (hodd : ¬ (2 : ℤ) ∣ u)
    (hposU : OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k u)
    (hnegU : OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k (u - p.C)) :
    ∃ t, 0 < t ∧ t ≤ k ∧ OddResidueIter p.C u t = u ∧
      ∀ i, i < t →
        2 * OddResidueIter p.C u (i + 1) + OddResidueIter p.C u i = p.C := by
  classical
  obtain ⟨i0, j0, hij0, hj0, heq0⟩ := OddResidueRepeat p hQ hD hpos hcop x k
    hk hret hmin u hu0 huc hodd hposU hnegU
  have hex : ∃ j, ∃ i, i < j ∧
      OddResidueIter p.C u i = OddResidueIter p.C u j :=
    ⟨j0, i0, hij0, heq0⟩
  let t := Nat.find hex
  have ht := Nat.find_spec hex
  obtain ⟨i, hi, heq⟩ := ht
  have htpos : 0 < t := by omega
  have htle : t ≤ k := by
    have hle0 : t ≤ j0 := Nat.find_le ⟨i0, hij0, heq0⟩
    omega
  have hzero : i = 0 := by
    by_contra hposi
    have hi0 : 0 < i := by omega
    have hstep (n : ℕ) (hn : n < t) :
        2 * OddResidueIter p.C u (n + 1) + OddResidueIter p.C u n = p.C := by
      have hdoubled := OddResidueIterDoubled p hQ hD hpos hcop x k hk hret
        hmin u hu0 huc hodd hposU hnegU n
      exact OddResidueStepRel p.C u n hdoubled.2.2.1
        (NegTwoOffsetOdd p hD hcop)
    have hprev := OddResiduePrev p.C u (i - 1) (t - 1)
      (by
        have hidx : i - 1 + 1 = i := by omega
        simpa [hidx] using hstep (i - 1) (by omega))
      (by
        have hidx : t - 1 + 1 = t := by omega
        simpa [hidx] using hstep (t - 1) (by omega))
      (by
        have hi' : i - 1 + 1 = i := by omega
        have ht' : t - 1 + 1 = t := by omega
        simpa [hi', ht'] using heq)
    have hlt : t - 1 < t := by omega
    have hbad : ∃ r, r < t - 1 ∧
        OddResidueIter p.C u r = OddResidueIter p.C u (t - 1) :=
      ⟨i - 1, by omega, hprev⟩
    exact Nat.find_min hex hlt hbad
  refine ⟨t, htpos, htle, ?_, ?_⟩
  · {
      have h0 : OddResidueIter p.C u 0 = u := by
        simp [OddResidueIter]
      rw [hzero] at heq
      calc
        OddResidueIter p.C u t = OddResidueIter p.C u 0 := heq.symm
        _ = u := h0
    }
  · {
      intro n hn
      have hdoubled := OddResidueIterDoubled p hQ hD hpos hcop x k hk hret
        hmin u hu0 huc hodd hposU hnegU n
      exact OddResidueStepRel p.C u n hdoubled.2.2.1
        (NegTwoOffsetOdd p hD hcop)
    }

/-- A repeated odd residue on a minimal cycle is exactly one third of the offset. -/
theorem CollisionForcesThird (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (x : ℤ) (k : ℕ) (hk : 0 < k)
    (hret : Iterate (TotalReturn p (TwoEvery p hQ hcop)) k x = x)
    (hmin : ∀ d, 0 < d → d < k →
      Iterate (TotalReturn p (TwoEvery p hQ hcop)) d x ≠ x)
    (u : ℤ) (hu0 : 0 < u) (huc : u < p.C) (hodd : ¬ (2 : ℤ) ∣ u)
    (hposU : OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k u)
    (hnegU : OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k (u - p.C)) :
    3 * u = p.C := by
  obtain ⟨t, ht, _htle, hback, hstep⟩ :=
    OddResidueReturns p hQ hD hpos hcop x k hk hret hmin u hu0 huc hodd
      hposU hnegU
  exact DoubledResidueFixed p.C t ht (fun i => OddResidueIter p.C u i) hstep
    hback

/-- A repeated odd residue is a two-cycle, so the minimal return has length two. -/
theorem CollisionIsTwoCycle (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (x : ℤ) (k : ℕ) (hk : 0 < k)
    (hret : Iterate (TotalReturn p (TwoEvery p hQ hcop)) k x = x)
    (hmin : ∀ d, 0 < d → d < k →
      Iterate (TotalReturn p (TwoEvery p hQ hcop)) d x ≠ x)
    (u : ℤ) (hu0 : 0 < u) (huc : u < p.C) (hodd : ¬ (2 : ℤ) ∣ u)
    (hposU : OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k u)
    (hnegU : OnCycle (TotalReturn p (TwoEvery p hQ hcop)) x k (u - p.C)) :
    k = 2 := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  have hthird := CollisionForcesThird p hQ hD hpos hcop x k hk hret hmin u
    hu0 huc hodd hposU hnegU
  have hpair := NegTwoOddPair p hQ hD hpos hcop u hu0 huc hodd
  have ha : (p.C - u) / 2 = u := by
    have hdiff : p.C - u = 2 * u := by
      rw [← hthird]
      ring
    have hdiv : (2 : ℤ) ∣ p.C - u := ⟨u, hdiff⟩
    have hmul : (2 : ℤ) * ((p.C - u) / 2) = p.C - u :=
      Int.mul_ediv_cancel' hdiv
    apply Int.eq_of_mul_eq_mul_left (by decide : (2 : ℤ) ≠ 0)
    calc
      (2 : ℤ) * ((p.C - u) / 2) = p.C - u := hmul
      _ = 2 * u := hdiff
  have hRu : R u = u - p.C := by
    simpa [R, ha] using hpair.1
  have hRc : R (u - p.C) = u := by
    simpa [R, ha] using hpair.2
  have htwo : Iterate R 2 u = u := by
    simp [Iterate, hRu, hRc]
  obtain ⟨i, hi, hix⟩ := hposU
  have hshift : Iterate R (i + 2) x = Iterate R i x := by
    calc
      Iterate R (i + 2) x = Iterate R 2 (Iterate R i x) := by
        rw [IterateAdd]
      _ = Iterate R 2 u := by rw [hix]
      _ = u := htwo
      _ = Iterate R i x := hix.symm
  have hback : Iterate R 2 x = x := by
    have hcomp := congrArg (Iterate R (k - i)) hshift
    have hL : Iterate R (k - i) (Iterate R (i + 2) x) =
        Iterate R 2 x := by
      rw [← IterateAdd]
      have hidx : i + 2 + (k - i) = k + 2 := by omega
      rw [hidx, IterateAdd, hret]
    have hRight : Iterate R (k - i) (Iterate R i x) = x := by
      rw [← IterateAdd]
      have hidx : i + (k - i) = k := by omega
      rw [hidx, hret]
    rw [hL, hRight] at hcomp
    exact hcomp
  have hge : 2 ≤ k := by
    by_contra hlt
    have hk1 : k = 1 := by omega
    obtain ⟨j, hj, hjx⟩ := hnegU
    have hju : u - p.C = u := by
      rw [hk1] at hi hj
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      rw [hi0] at hix
      rw [hj0] at hjx
      simp [Iterate] at hix hjx
      exact hjx.symm.trans hix
    omega
  by_contra hne
  have hlt : 2 < k := by omega
  exact hmin 2 (by omega) hlt hback

/-- A minimal cycle has length at most `max(|c| - 1, 1)`. -/
theorem NegTwoSharpPeriod (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (x : ℤ) (k : ℕ) (hk : 0 < k)
    (hret : Iterate (TotalReturn p (TwoEvery p hQ hcop)) k x = x)
    (hmin : ∀ d, 0 < d → d < k →
      Iterate (TotalReturn p (TwoEvery p hQ hcop)) d x ≠ x) :
    k ≤ max (p.C.natAbs - 1) 1 := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  by_cases hx0 : x = 0
  · {
      have hfix := NegTwoZeroFixed p hQ hD hcop
      have hone : Iterate R 1 x = x := by
        simp [Iterate, R, hx0]
        simpa [R] using hfix
      have hk1 : k = 1 := by
        by_contra hne
        have hlt : 1 < k := by omega
        exact hmin 1 (by decide) hlt hone
      simp [hk1]
    }
  · {
      classical
      by_cases hdist : ∀ i j, i < k → j < k → i ≠ j →
          OpenResidue p.C (Iterate R i x) ≠
            OpenResidue p.C (Iterate R j x)
      · {
          have hle := NegTwoDistinctPeriod p hQ hD hpos hcop x hx0 k hk
            hret hmin (by
              intro i j hi hj hne
              simpa [R] using hdist i j hi hj hne)
          omega
        }
      · {
          push Not at hdist
          obtain ⟨i, j, hi, hj, hne, heq⟩ := hdist
          have hord : i < j ∨ j < i := by omega
          rcases hord with hij | hji
          · {
              obtain ⟨u, hu0, huc, hodd, hposU, hnegU⟩ :=
                NegTwoCollisionOdd p hQ hD hpos hcop x hx0 k hk hret hmin
                  i j hij hj (by simpa [R] using heq)
              have hk2 := CollisionIsTwoCycle p hQ hD hpos hcop x k hk hret
                hmin u hu0 huc hodd hposU hnegU
              have hoddC : ¬ (2 : ℤ) ∣ p.C := NegTwoOffsetOdd p hD hcop
              have hc3 : 3 ≤ p.C := by
                by_contra hlt
                have hc : p.C = 1 ∨ p.C = 2 := by omega
                rcases hc with hc | hc
                · {
                    rw [hc] at huc
                    omega
                  }
                · {
                    apply hoddC
                    rw [hc]
                  }
              have hcabs : (p.C.natAbs : ℤ) = p.C :=
                Int.natAbs_of_nonneg (le_of_lt hpos)
              have hroom : 2 ≤ p.C.natAbs - 1 := by
                omega
              rw [hk2]
              omega
            }
          · {
              obtain ⟨u, hu0, huc, hodd, hposU, hnegU⟩ :=
                NegTwoCollisionOdd p hQ hD hpos hcop x hx0 k hk hret hmin
                  j i hji hi (by simpa [R] using heq.symm)
              have hk2 := CollisionIsTwoCycle p hQ hD hpos hcop x k hk hret
                hmin u hu0 huc hodd hposU hnegU
              have hoddC : ¬ (2 : ℤ) ∣ p.C := NegTwoOffsetOdd p hD hcop
              have hc3 : 3 ≤ p.C := by
                by_contra hlt
                have hc : p.C = 1 ∨ p.C = 2 := by omega
                rcases hc with hc | hc
                · {
                    rw [hc] at huc
                    omega
                  }
                · {
                    apply hoddC
                    rw [hc]
                  }
              have hcabs : (p.C.natAbs : ℤ) = p.C :=
                Int.natAbs_of_nonneg (le_of_lt hpos)
              have hroom : 2 ≤ p.C.natAbs - 1 := by
                omega
              rw [hk2]
              omega
            }
        }
    }

/-- The closed shell is entered in at most `|n| - |c|` steps. -/
theorem NegTwoEntersGap (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    ∃ k : ℕ, k ≤ n.natAbs - p.C.natAbs ∧
      (Iterate (TotalReturn p (TwoEvery p hQ hcop)) k n).natAbs ≤
        p.C.natAbs := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  induction h : n.natAbs using Nat.strong_induction_on generalizing n with
  | _ m ih => {
      by_cases hshell : n.natAbs ≤ p.C.natAbs
      · {
          refine ⟨0, Nat.zero_le _, ?_⟩
          simpa [R, Iterate] using hshell
        }
      · {
          have hlt : p.C.natAbs < n.natAbs := by omega
          have hdrop := NegTwoDrops p hQ hD hcop n hlt
          have hsmall : (R n).natAbs < m := by
            have hdropR : (R n).natAbs ≤ n.natAbs - 1 := by
              simpa [R] using hdrop
            rw [← h]
            omega
          obtain ⟨k, hk, hent⟩ := ih (R n).natAbs hsmall (R n) rfl
          refine ⟨k + 1, ?_, ?_⟩
          · {
              have hdropR : (R n).natAbs ≤ n.natAbs - 1 := by
                simpa [R] using hdrop
              rw [← h]
              omega
            }
          · {
              have hshift : Iterate R k (R n) = Iterate R (k + 1) n := by
                rw [show k + 1 = 1 + k by omega, IterateAdd]
                simp [Iterate]
              rw [← hshift]
              exact hent
            }
        }
    }

/-- The open shell `|x| ≤ |c| - 1` is invariant. -/
theorem NegTwoStrictStays (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (habs : n.natAbs ≤ p.C.natAbs - 1) :
    (TotalReturn p (TwoEvery p hQ hcop) n).natAbs ≤ p.C.natAbs - 1 := by
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      rw [NegTwoFormulaEven p hQ hD hcop n hdiv, Int.natAbs_neg,
        EvenAbsHalf n hdiv]
      omega
    }
  · {
      have hoddC : ¬ (2 : ℤ) ∣ p.C := NegTwoOffsetOdd p hD hcop
      have hsum : (2 : ℤ) ∣ n + p.C := TwoOddSum n p.C hdiv hoddC
      rw [NegTwoFormulaOdd p hQ hD hcop n hdiv, Int.natAbs_neg,
        EvenAbsHalf (n + p.C) hsum]
      have hle : (n + p.C).natAbs ≤ n.natAbs + p.C.natAbs :=
        Int.natAbs_add_le n p.C
      have hN : 0 < p.C.natAbs := Int.natAbs_pos.mpr (ne_of_gt hpos)
      omega
    }

/-- The open shell is entered within two steps of the closed shell. -/
theorem NegTwoStrictEnters (p : Parameters) (hQ : p.Q = 1) (hD : p.D = -2)
    (hpos : 0 < p.C) (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    ∃ k : ℕ, k ≤ n.natAbs - p.C.natAbs + 2 ∧
      (Iterate (TotalReturn p (TwoEvery p hQ hcop)) k n).natAbs ≤
        p.C.natAbs - 1 := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  obtain ⟨k, hk, hent⟩ := NegTwoEntersGap p hQ hD hcop n
  set y := Iterate R k n
  by_cases hstrict : y.natAbs ≤ p.C.natAbs - 1
  · {
      refine ⟨k, ?_, ?_⟩
      · {
          omega
        }
      · {
          simpa [y, R] using hstrict
        }
    }
  · {
      have hyabs : y.natAbs = p.C.natAbs := by
        have hle : y.natAbs ≤ p.C.natAbs := by simpa [y, R] using hent
        omega
      have hsign : y = (y.natAbs : ℤ) ∨ y = -(y.natAbs : ℤ) := by
        cases y with
        | ofNat _ => {
            left
            rfl
          }
        | negSucc _ => {
            right
            rfl
          }
      have hcabs : (p.C.natAbs : ℤ) = p.C :=
        Int.natAbs_of_nonneg (le_of_lt hpos)
      have hyeq : y = p.C ∨ y = -p.C := by
        rw [hyabs, hcabs] at hsign
        exact hsign
      have hends := NegTwoEndpoints p hQ hD hpos hcop
      have hnext : Iterate R (k + 1) n = R y := by
        rw [← Nat.succ_eq_add_one]
        simp [Iterate, y]
      rcases hyeq with hy | hy
      · {
          refine ⟨k + 2, ?_, ?_⟩
          · {
              omega
            }
          · {
              have htwo : Iterate R (k + 2) n = R (R y) := by
                have hstep : Iterate R (k + 2) n = R (Iterate R (k + 1) n) := by
                  rw [show k + 2 = Nat.succ (k + 1) by omega]
                  simp [Iterate]
                rw [hstep, hnext]
              have hzero : R (R y) = 0 := by
                have hfirst : R y = -p.C := by
                  simpa [R, hy] using hends.1
                rw [hfirst]
                simpa [R] using hends.2
              rw [htwo, hzero]
              have hN : 0 < p.C.natAbs := Int.natAbs_pos.mpr (ne_of_gt hpos)
              omega
            }
        }
      · {
          refine ⟨k + 1, ?_, ?_⟩
          · {
              omega
            }
          · {
              have hzero : R y = 0 := by
                simpa [R, hy] using hends.2
              rw [hnext, hzero]
              have hN : 0 < p.C.natAbs := Int.natAbs_pos.mpr (ne_of_gt hpos)
              omega
            }
        }
    }

/-- A period of length at most `2|c| - 1` begins by time `|n| + |c|`. -/
theorem NegTwoPeriodByOffset (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hpos : 0 < p.C)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    ∃ t period : ℕ, t ≤ n.natAbs - p.C.natAbs + 2 * p.C.natAbs ∧
      0 < period ∧ period ≤ 2 * p.C.natAbs - 1 ∧
      ∀ k : ℕ,
        Iterate (TotalReturn p (TwoEvery p hQ hcop)) (t + k) n =
          Iterate (TotalReturn p (TwoEvery p hQ hcop))
            (t + period + k) n := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  obtain ⟨t0, ht0, hent⟩ := NegTwoStrictEnters p hQ hD hpos hcop n
  let M := p.C.natAbs - 1
  let y := Iterate R t0 n
  have hy : y.natAbs ≤ M := by
    simpa [y, R, M] using hent
  have hstay : ∀ j, (Iterate R j y).natAbs ≤ M := by
    intro j
    induction j with
    | zero => {
        simpa [Iterate, y] using hy
      }
    | succ j ih => {
        simpa [R, Iterate] using
          NegTwoStrictStays p hQ hD hpos hcop (Iterate R j y) ih
      }
  let f : Fin (2 * M + 2) → Fin (2 * M + 1) := fun i =>
    ⟨NegShellCode M (Iterate R i.val y), NegShellCodeLt M _ (hstay i.val)⟩
  have hcard : Fintype.card (Fin (2 * M + 1)) <
      Fintype.card (Fin (2 * M + 2)) := by
    simp [Fintype.card_fin]
  obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hstate : Iterate R a.val y = Iterate R b.val y := by
    have hcode : NegShellCode M (Iterate R a.val y) =
        NegShellCode M (Iterate R b.val y) := by
      simpa [f] using congrArg Fin.val heq
    exact NegShellCodeInj M _ _ (hstay a.val) (hstay b.val) hcode
  have hneval : a.val ≠ b.val := by
    intro h
    exact hne (Fin.ext h)
  have hord : a.val < b.val ∨ b.val < a.val := by
    omega
  have hshift : ∀ u v, u ≤ v → Iterate R u y = Iterate R v y →
      ∀ k, Iterate R (t0 + u + k) n =
        Iterate R (t0 + u + (v - u) + k) n := by
    intro u v huv hxy k
    have hbase : ∀ j, Iterate R (u + j) y = Iterate R (v + j) y := by
      intro j
      induction j with
      | zero => {
          simpa using hxy
        }
      | succ j ih => {
          have hL : Iterate R (u + (j + 1)) y =
              R (Iterate R (u + j) y) := by
            rw [show u + (j + 1) = Nat.succ (u + j) by omega]
            simp [Iterate]
          have hRgt : Iterate R (v + (j + 1)) y =
              R (Iterate R (v + j) y) := by
            rw [show v + (j + 1) = Nat.succ (v + j) by omega]
            simp [Iterate]
          rw [hL, hRgt, ih]
        }
    have hclock : ∀ m, Iterate R (t0 + m) n = Iterate R m y := by
      intro m
      rw [IterateAdd]
    have hleft : t0 + u + k = t0 + (u + k) := by
      omega
    have hright : t0 + u + (v - u) + k = t0 + (v + k) := by
      omega
    rw [hleft, hright, hclock (u + k), hclock (v + k), hbase k]
  rcases hord with hlt | hgt
  · {
      refine ⟨t0 + a.val, b.val - a.val, ?_, ?_, ?_, ?_⟩
      · {
          have ha : a.val ≤ 2 * M := by
            have hlt : a.val < 2 * M + 2 := a.isLt
            omega
          have hone : 1 ≤ p.C.natAbs :=
            Nat.succ_le_of_lt (Int.natAbs_pos.mpr (ne_of_gt hpos))
          have hM : M + 1 = p.C.natAbs := by
            simpa [M] using Nat.sub_add_cancel hone
          omega
        }
      · {
          omega
        }
      · {
          have hb : b.val ≤ 2 * M + 1 := by
            have hlt : b.val < 2 * M + 2 := b.isLt
            omega
          have hone : 1 ≤ p.C.natAbs :=
            Nat.succ_le_of_lt (Int.natAbs_pos.mpr (ne_of_gt hpos))
          have hM : M + 1 = p.C.natAbs := by
            simpa [M] using Nat.sub_add_cancel hone
          omega
        }
      · {
          intro k
          exact hshift a.val b.val (Nat.le_of_lt hlt) hstate k
        }
    }
  · {
      refine ⟨t0 + b.val, a.val - b.val, ?_, ?_, ?_, ?_⟩
      · {
          have hb : b.val ≤ 2 * M := by
            have hlt : b.val < 2 * M + 2 := b.isLt
            omega
          have hone : 1 ≤ p.C.natAbs :=
            Nat.succ_le_of_lt (Int.natAbs_pos.mpr (ne_of_gt hpos))
          have hM : M + 1 = p.C.natAbs := by
            simpa [M] using Nat.sub_add_cancel hone
          omega
        }
      · {
          omega
        }
      · {
          have ha : a.val ≤ 2 * M + 1 := by
            have hlt : a.val < 2 * M + 2 := a.isLt
            omega
          have hone : 1 ≤ p.C.natAbs :=
            Nat.succ_le_of_lt (Int.natAbs_pos.mpr (ne_of_gt hpos))
          have hM : M + 1 = p.C.natAbs := by
            simpa [M] using Nat.sub_add_cancel hone
          omega
        }
      · {
          intro k
          exact hshift b.val a.val (Nat.le_of_lt hgt) hstate.symm k
        }
    }

/-- The least return after entry has length at most `max(|c| - 1, 1)`. -/
theorem NegTwoSharpDelay (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hpos : 0 < p.C)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    ∃ t period : ℕ, t ≤ n.natAbs - p.C.natAbs + 2 * p.C.natAbs ∧
      0 < period ∧ period ≤ max (p.C.natAbs - 1) 1 ∧
      ∀ k : ℕ,
        Iterate (TotalReturn p (TwoEvery p hQ hcop)) (t + k) n =
          Iterate (TotalReturn p (TwoEvery p hQ hcop))
            (t + period + k) n := by
  obtain ⟨t, p0, ht, hp0, _hp, hper⟩ :=
    NegTwoPeriodByOffset p hQ hD hpos hcop n
  let R := TotalReturn p (TwoEvery p hQ hcop)
  let y := Iterate R t n
  have hy : Iterate R p0 y = y := by
    unfold R y
    rw [← IterateAdd]
    simpa [Nat.add_zero] using (hper 0).symm
  classical
  let P : ℕ → Prop := fun d => 0 < d ∧ Iterate R d y = y
  have hex : ∃ d, P d := ⟨p0, hp0, hy⟩
  let d := Nat.find hex
  have hdP : P d := Nat.find_spec hex
  have hsharp : d ≤ max (p.C.natAbs - 1) 1 := by
    exact NegTwoSharpPeriod p hQ hD hpos hcop y d hdP.1 hdP.2
      (fun e he hlt hret => by
        exact Nat.find_min hex hlt ⟨he, hret⟩)
  have hstep : ∀ k, Iterate R (d + k) y = Iterate R k y := by
    intro k
    induction k with
    | zero => {
        simp [Iterate]
        exact hdP.2
      }
    | succ k ih => {
        rw [show d + (k + 1) = Nat.succ (d + k) by omega]
        rw [show k + 1 = Nat.succ k by omega]
        simp [Iterate, ih]
      }
  have hclock : ∀ m, Iterate R (t + m) n = Iterate R m y := by
    intro m
    rw [IterateAdd]
  refine ⟨t, d, ht, hdP.1, hsharp, ?_⟩
  intro k
  have hidx : t + d + k = t + (d + k) := by omega
  rw [hidx, hclock (d + k), hclock k, hstep k]

/-- Logarithmic entry followed by the sharp period. -/
theorem NegTwoLogDelay (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hpos : 0 < p.C)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    ∃ t period : ℕ,
      t ≤ Nat.log 2 (n.natAbs - p.C.natAbs) + 1 + 2 * p.C.natAbs ∧
      0 < period ∧ period ≤ max (p.C.natAbs - 1) 1 ∧
      ∀ k : ℕ,
        Iterate (TotalReturn p (TwoEvery p hQ hcop)) (t + k) n =
          Iterate (TotalReturn p (TwoEvery p hQ hcop))
            (t + period + k) n := by
  obtain ⟨k0, hk0, hent⟩ := NegTwoLogEnters p hQ hD hcop n
  let R := TotalReturn p (TwoEvery p hQ hcop)
  let y := Iterate R k0 n
  have hy : y.natAbs ≤ p.C.natAbs := by
    simpa [y, R] using hent
  obtain ⟨t1, period, ht1, hp0, hp, hper⟩ :=
    NegTwoSharpDelay p hQ hD hpos hcop y
  refine ⟨k0 + t1, period, ?_, hp0, hp, ?_⟩
  · {
      have hsub : y.natAbs - p.C.natAbs = 0 := by
        omega
      omega
    }
  · {
      intro k
      have hshift : Iterate R (k0 + t1 + k) n =
          Iterate R (t1 + k) y := by
        rw [show k0 + t1 + k = k0 + (t1 + k) by omega, IterateAdd]
      have hshiftP : Iterate R (k0 + t1 + period + k) n =
          Iterate R (t1 + period + k) y := by
        rw [show k0 + t1 + period + k =
            k0 + (t1 + period + k) by omega, IterateAdd]
      have hperR : Iterate R (t1 + k) y =
          Iterate R (t1 + period + k) y := by
        simpa [R] using hper k
      rw [hshift, hshiftP, hperR]
    }

/-- A power of two flips sign and halves at every return. -/
theorem NegTwoPowerState (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (e t : ℕ) (ht : t ≤ e) :
    Iterate (TotalReturn p (TwoEvery p hQ hcop)) t ((2 : ℤ) ^ e) =
      (-1 : ℤ) ^ t * (2 : ℤ) ^ (e - t) := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  induction t with
  | zero => {
      simp [Iterate]
    }
  | succ t ih => {
      have hle : t ≤ e := by omega
      have hpos : 0 < e - t := by omega
      have hval := ih hle
      have hdiv : (2 : ℤ) ∣ Iterate R t ((2 : ℤ) ^ e) := by
        rw [hval]
        refine ⟨(-1 : ℤ) ^ t * (2 : ℤ) ^ (e - t - 1), ?_⟩
        have hpow : (2 : ℤ) ^ (e - t) =
            (2 : ℤ) ^ (e - t - 1) * 2 := by
          have hidx : e - t = (e - t - 1) + 1 := by omega
          conv_lhs => rw [hidx]
          rw [pow_succ]
        rw [hpow]
        ring
      have hret := NegTwoFormulaEven p hQ hD hcop
        (Iterate R t ((2 : ℤ) ^ e)) hdiv
      rw [Iterate, hret, hval]
      have hhalf : ((-1 : ℤ) ^ t * (2 : ℤ) ^ (e - t)) / 2 =
          (-1 : ℤ) ^ t * (2 : ℤ) ^ (e - (t + 1)) := by
        have hpow : (2 : ℤ) ^ (e - t) =
            2 * (2 : ℤ) ^ (e - t - 1) := by
          have hidx : e - t = (e - t - 1) + 1 := by omega
          conv_lhs => rw [hidx]
          rw [pow_succ, mul_comm]
        have hfac : (-1 : ℤ) ^ t * (2 * (2 : ℤ) ^ (e - t - 1)) =
            2 * ((-1 : ℤ) ^ t * (2 : ℤ) ^ (e - t - 1)) := by
          ring
        rw [hpow, hfac,
          Int.mul_ediv_cancel_left _ (by decide : (2 : ℤ) ≠ 0)]
        have hsub : e - t - 1 = e - (t + 1) := by omega
        rw [hsub]
      rw [hhalf]
      ring
    }

/-- At offset one, `2 ^ e` enters the shell exactly at the logarithm. -/
theorem NegTwoPowerEntry (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hC : p.C = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (e : ℕ) (he : 0 < e) :
    let R := TotalReturn p (TwoEvery p hQ hcop)
    (Iterate R e ((2 : ℤ) ^ e)).natAbs = p.C.natAbs ∧
      (∀ t, t < e →
        p.C.natAbs < (Iterate R t ((2 : ℤ) ^ e)).natAbs) ∧
      e = Nat.log 2 (((2 : ℤ) ^ e).natAbs - p.C.natAbs) + 1 := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  have hsign : ∀ t, ((-1 : ℤ) ^ t).natAbs = 1 := by
    intro t
    induction t with
    | zero => {
        simp
      }
    | succ t ih => {
        rw [pow_succ, Int.natAbs_mul, ih]
        simp
      }
  have habs : ∀ t, t ≤ e →
      (Iterate R t ((2 : ℤ) ^ e)).natAbs = 2 ^ (e - t) := by
    intro t ht
    have hstate := NegTwoPowerState p hQ hD hcop e t ht
    rw [hstate, Int.natAbs_mul, hsign t, Int.natAbs_pow]
    simp
  refine ⟨?_, ?_, ?_⟩
  · {
      rw [habs e (le_refl e), hC]
      simp
    }
  · {
      intro t ht
      rw [habs t (le_of_lt ht)]
      have hcabs : p.C.natAbs = 1 := by
        rw [hC]
        rfl
      rw [hcabs]
      have hpow : 1 < 2 ^ (e - t) := by
        have hpos : e - t ≠ 0 := by omega
        exact Nat.one_lt_pow hpos (by decide)
      exact hpow
    }
  · {
      have hnat : ((2 : ℤ) ^ e).natAbs = 2 ^ e := by
        simp [Int.natAbs_pow]
      have hcabs : p.C.natAbs = 1 := by
        rw [hC]
        rfl
      rw [hnat, hcabs]
      have hlog : Nat.log 2 (2 ^ e - 1) = e - 1 := by
        apply le_antisymm
        · {
            have hone : 1 < 2 ^ e :=
              Nat.one_lt_pow (ne_of_gt he) (by decide)
            have hpos2 : 0 < 2 ^ e := lt_trans (by decide) hone
            have hlt : 2 ^ e - 1 < 2 ^ e :=
              Nat.sub_lt hpos2 (by decide)
            have hne : 2 ^ e - 1 ≠ 0 :=
              ne_of_gt (Nat.sub_pos_of_lt hone)
            have hloglt : Nat.log 2 (2 ^ e - 1) < e :=
              Nat.log_lt_of_lt_pow hne hlt
            omega
          }
        · {
            have hle : 2 ^ (e - 1) ≤ 2 ^ e - 1 := by
              have hidx : e = (e - 1) + 1 := by omega
              have htwo : 2 ^ (e - 1) * 2 = 2 ^ e := by
                conv_rhs => rw [hidx]
                rw [pow_succ]
              have hone : 1 ≤ 2 ^ (e - 1) :=
                Nat.one_le_pow (e - 1) 2 (by decide)
              have hsum : 2 ^ (e - 1) + 2 ^ (e - 1) = 2 ^ e := by
                rw [← Nat.two_mul, Nat.mul_comm, htwo]
              omega
            exact Nat.le_log_of_pow_le (by decide) hle
          }
      omega
    }

/-- For even `e`, the delay bound is the first period of `2 ^ e`. -/
theorem NegTwoPowerDelaySharp (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hC : p.C = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (e : ℕ) (he : 0 < e) (hev : Even e) :
    let n := (2 : ℤ) ^ e
    let R := TotalReturn p (TwoEvery p hQ hcop)
    (∀ t period, t < e + 2 → 0 < period →
      ∃ k, Iterate R (t + k) n ≠
        Iterate R (t + period + k) n) ∧
      (∀ k, Iterate R (e + 2 + k) n =
        Iterate R (e + 2 + 1 + k) n) ∧
      e + 2 =
        Nat.log 2 (n.natAbs - p.C.natAbs) + 1 + 2 * p.C.natAbs := by
  let n := (2 : ℤ) ^ e
  let R := TotalReturn p (TwoEvery p hQ hcop)
  have hpos : 0 < p.C := by
    rw [hC]
    decide
  have hone : (-1 : ℤ) ^ e = 1 := hev.neg_one_pow
  have hatE : Iterate R e n = p.C := by
    have hstate := NegTwoPowerState p hQ hD hcop e e (le_refl e)
    rw [hstate, hone, hC]
    simp
  have hends := NegTwoEndpoints p hQ hD hpos hcop
  have hat1 : Iterate R (e + 1) n = -p.C := by
    rw [Iterate, hatE]
    simpa [R] using hends.left
  have hat2 : Iterate R (e + 2) n = 0 := by
    have hstep : Iterate R (e + 2) n = R (Iterate R (e + 1) n) := by
      rw [show e + 2 = (e + 1) + 1 by omega, Iterate]
    rw [hstep, hat1]
    simpa [R] using hends.right
  have hzero : ∀ j, Iterate R j 0 = 0 := by
    intro j
    induction j with
    | zero => {
        simp [Iterate]
      }
    | succ j ih => {
        rw [Iterate, ih]
        simpa [R] using NegTwoZeroFixed p hQ hD hcop
      }
  have hlate : ∀ j, 2 ≤ j → Iterate R (e + j) n = 0 := by
    intro j hj
    have hsplit : e + j = (e + 2) + (j - 2) := by omega
    rw [hsplit, IterateAdd, hat2]
    exact hzero (j - 2)
  refine ⟨?_, ?_, ?_⟩
  · {
      intro t period ht hp
      by_cases hbefore : t < e
      · {
          refine ⟨0, ?_⟩
          have habsL : (Iterate R t n).natAbs = 2 ^ (e - t) := by
            have hstate :=
              NegTwoPowerState p hQ hD hcop e t (le_of_lt hbefore)
            rw [hstate, Int.natAbs_mul, Int.natAbs_pow]
            simp
          have habsR : (Iterate R (t + period) n).natAbs <
              2 ^ (e - t) := by
            by_cases hle : t + period ≤ e
            · {
                have hstate :=
                  NegTwoPowerState p hQ hD hcop e (t + period) hle
                rw [hstate, Int.natAbs_mul, Int.natAbs_pow]
                simp
                exact Nat.pow_lt_pow_right (by decide)
                  (by omega : e - (t + period) < e - t)
              }
            · {
                have hrest : (t + period) - e = 0 ∨
                    (t + period) - e = 1 ∨ 2 ≤ (t + period) - e := by
                  omega
                have hexp : e - t ≠ 0 := by omega
                have hpow : 1 < 2 ^ (e - t) :=
                  Nat.one_lt_pow hexp (by decide)
                rcases hrest with h0 | h1 | h2
                · {
                    rw [show t + period = e by omega, hatE, hC]
                    simpa using hpow
                  }
                · {
                    rw [show t + period = e + 1 by omega, hat1, hC]
                    simpa using hpow
                  }
                · {
                    rw [show t + period = e + ((t + period) - e) by omega,
                      hlate _ h2]
                    simp
                  }
              }
          intro heq
          have heqR : Iterate R t n = Iterate R (t + period) n := by
            simpa [R, Nat.add_zero] using heq
          have hne : (Iterate R t n).natAbs ≠
              (Iterate R (t + period) n).natAbs := by
            rw [habsL]
            exact (ne_of_lt habsR).symm
          exact hne (congrArg Int.natAbs heqR)
        }
      · {
          have htE : t = e ∨ t = e + 1 := by omega
          refine ⟨0, ?_⟩
          simp
          rcases htE with htE | htE
          · {
              rw [htE, hatE]
              by_cases hp1 : period = 1
              · {
                  rw [hp1, hat1, hC]
                  decide
                }
              · {
                  have hge : 2 ≤ period := by omega
                  rw [hlate period hge, hC]
                  decide
                }
            }
          · {
              rw [htE, hat1]
              rw [show e + 1 + period = e + (period + 1) by omega]
              have htwo : 2 ≤ period + 1 := by omega
              rw [hlate (period + 1) htwo, hC]
              decide
            }
        }
    }
  · {
      intro k
      have hL := hlate (2 + k) (by omega)
      have hRv := hlate (3 + k) (by omega)
      rw [show e + (2 + k) = e + 2 + k by omega] at hL
      rw [show e + (3 + k) = e + 2 + 1 + k by omega] at hRv
      rw [hL, hRv]
    }
  · {
      have hentry := NegTwoPowerEntry p hQ hD hC hcop e he
      have hlog := hentry.right.right
      have hcabs : p.C.natAbs = 1 := by
        rw [hC]
        rfl
      rw [hcabs] at hlog
      rw [hcabs]
      omega
    }

/-- For odd `e`, the first period of `2 ^ e` begins one step before the bound. -/
theorem NegTwoPowerDelayOdd (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hC : p.C = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (e : ℕ) (he : 0 < e) (hodd : Odd e) :
    let n := (2 : ℤ) ^ e
    let R := TotalReturn p (TwoEvery p hQ hcop)
    (∀ t period, t < e + 1 → 0 < period →
      ∃ k, Iterate R (t + k) n ≠
        Iterate R (t + period + k) n) ∧
      (∀ k, Iterate R (e + 1 + k) n =
        Iterate R (e + 1 + 1 + k) n) ∧
      e + 1 =
        Nat.log 2 (n.natAbs - p.C.natAbs) + 1 + 1 ∧
      e + 1 <
        Nat.log 2 (n.natAbs - p.C.natAbs) + 1 + 2 * p.C.natAbs := by
  let n := (2 : ℤ) ^ e
  let R := TotalReturn p (TwoEvery p hQ hcop)
  have hpos : 0 < p.C := by
    rw [hC]
    decide
  have hone : (-1 : ℤ) ^ e = -1 := hodd.neg_one_pow
  have hatE : Iterate R e n = -p.C := by
    have hstate := NegTwoPowerState p hQ hD hcop e e (le_refl e)
    rw [hstate, hone, hC]
    simp
  have hends := NegTwoEndpoints p hQ hD hpos hcop
  have hat1 : Iterate R (e + 1) n = 0 := by
    rw [Iterate, hatE]
    simpa [R] using hends.right
  have hzero : ∀ j, Iterate R j 0 = 0 := by
    intro j
    induction j with
    | zero => {
        simp [Iterate]
      }
    | succ j ih => {
        rw [Iterate, ih]
        simpa [R] using NegTwoZeroFixed p hQ hD hcop
      }
  have hlate : ∀ j, 1 ≤ j → Iterate R (e + j) n = 0 := by
    intro j hj
    have hsplit : e + j = (e + 1) + (j - 1) := by omega
    rw [hsplit, IterateAdd, hat1]
    exact hzero (j - 1)
  refine ⟨?_, ?_, ?_⟩
  · {
      intro t period ht hp
      by_cases hbefore : t < e
      · {
          refine ⟨0, ?_⟩
          have habsL : (Iterate R t n).natAbs = 2 ^ (e - t) := by
            have hstate :=
              NegTwoPowerState p hQ hD hcop e t (le_of_lt hbefore)
            rw [hstate, Int.natAbs_mul, Int.natAbs_pow]
            simp
          have habsR : (Iterate R (t + period) n).natAbs <
              2 ^ (e - t) := by
            by_cases hle : t + period ≤ e
            · {
                have hstate :=
                  NegTwoPowerState p hQ hD hcop e (t + period) hle
                rw [hstate, Int.natAbs_mul, Int.natAbs_pow]
                simp
                exact Nat.pow_lt_pow_right (by decide)
                  (by omega : e - (t + period) < e - t)
              }
            · {
                have hexp : e - t ≠ 0 := by omega
                have hpow : 1 < 2 ^ (e - t) :=
                  Nat.one_lt_pow hexp (by decide)
                by_cases h0 : t + period = e
                · {
                    rw [h0, hatE, hC]
                    simpa using hpow
                  }
                · {
                    have hge : 1 ≤ (t + period) - e := by omega
                    rw [show t + period = e + ((t + period) - e) by omega,
                      hlate _ hge]
                    simp
                  }
              }
          intro heq
          have heqR : Iterate R t n = Iterate R (t + period) n := by
            simpa [R, Nat.add_zero] using heq
          have hne : (Iterate R t n).natAbs ≠
              (Iterate R (t + period) n).natAbs := by
            rw [habsL]
            exact (ne_of_lt habsR).symm
          exact hne (congrArg Int.natAbs heqR)
        }
      · {
          have htE : t = e := by omega
          refine ⟨0, ?_⟩
          have hright : Iterate R (e + period) n = 0 :=
            hlate period hp
          have hne : Iterate R e n ≠ 0 := by
            rw [hatE, hC]
            decide
          simpa [R, n, htE, Nat.add_zero, hright] using hne
        }
    }
  · {
      intro k
      have hL := hlate (1 + k) (by omega)
      have hRv := hlate (2 + k) (by omega)
      rw [show e + (1 + k) = e + 1 + k by omega] at hL
      rw [show e + (2 + k) = e + 1 + 1 + k by omega] at hRv
      rw [hL, hRv]
    }
  · {
      have hentry := NegTwoPowerEntry p hQ hD hC hcop e he
      have hlog := hentry.right.right
      have hcabs : p.C.natAbs = 1 := by
        rw [hC]
        rfl
      rw [hcabs] at hlog
      rw [hcabs]
      omega
    }

/-- The first period of a power of two begins at `e + 2 - (e % 2)`. -/
theorem NegTwoPowerDelayParity (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hC : p.C = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (e : ℕ) (he : 0 < e) :
    let n := (2 : ℤ) ^ e
    let R := TotalReturn p (TwoEvery p hQ hcop)
    let t0 := e + 2 - e % 2
    (∀ t period, t < t0 → 0 < period →
      ∃ k, Iterate R (t + k) n ≠
        Iterate R (t + period + k) n) ∧
      (∀ k, Iterate R (t0 + k) n =
        Iterate R (t0 + 1 + k) n) ∧
      (Even e → t0 =
        Nat.log 2 (n.natAbs - p.C.natAbs) + 1 + 2 * p.C.natAbs) ∧
      (Odd e → t0 <
        Nat.log 2 (n.natAbs - p.C.natAbs) + 1 + 2 * p.C.natAbs) := by
  let n := (2 : ℤ) ^ e
  let R := TotalReturn p (TwoEvery p hQ hcop)
  let t0 := e + 2 - e % 2
  rcases Nat.even_or_odd e with heven | hodd
  · {
      have hmod : e % 2 = 0 := Nat.even_iff.mp heven
      have hsharp :=
        NegTwoPowerDelaySharp p hQ hD hC hcop e he heven
      refine ⟨?_, ?_, ?_, ?_⟩
      · {
          intro t period ht hp
          have ht' : t < e + 2 := by
            simpa [hmod] using ht
          simpa [R, n] using hsharp.left t period ht' hp
        }
      · {
          intro k
          have hper := hsharp.right.left k
          simpa [R, n, hmod] using hper
        }
      · {
          intro _hev
          have hlog := hsharp.right.right
          simpa [n, hmod] using hlog
        }
      · {
          intro hodd
          exact False.elim (Nat.not_odd_iff_even.mpr heven hodd)
        }
    }
  · {
      have hmod : e % 2 = 1 := Nat.odd_iff.mp hodd
      have hoddThm :=
        NegTwoPowerDelayOdd p hQ hD hC hcop e he hodd
      refine ⟨?_, ?_, ?_, ?_⟩
      · {
          intro t period ht hp
          have ht' : t < e + 1 := by
            simpa [hmod] using ht
          simpa [R, n] using hoddThm.left t period ht' hp
        }
      · {
          intro k
          have hper := hoddThm.right.left k
          simpa [R, n, hmod] using hper
        }
      · {
          intro heven
          exact False.elim (Nat.not_even_iff_odd.mpr hodd heven)
        }
      · {
          intro _hodd
          have hlt := hoddThm.right.right.right
          simpa [n, hmod] using hlt
        }
    }

/-- For offset `1`, the first period begins at the first visit to `0`. -/
theorem NegTwoOneFirstZero (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hC : p.C = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    let R := TotalReturn p (TwoEvery p hQ hcop)
    ∃ τ : ℕ, Iterate R τ n = 0 ∧
      (∀ s, s < τ → Iterate R s n ≠ 0) ∧
      (∀ k, Iterate R (τ + k) n = Iterate R (τ + 1 + k) n) ∧
      (∀ t period, t < τ → 0 < period →
        ∃ k, Iterate R (t + k) n ≠
          Iterate R (t + period + k) n) ∧
      τ ≤ Nat.log 2 (n.natAbs - p.C.natAbs) + 1 + 2 * p.C.natAbs := by
  classical
  let R := TotalReturn p (TwoEvery p hQ hcop)
  have hpos : 0 < p.C := by
    rw [hC]
    decide
  obtain ⟨t, period, ht, hp0, _hp, hper⟩ :=
    NegTwoLogDelay p hQ hD hpos hcop n
  have hy : Iterate R period (Iterate R t n) = Iterate R t n := by
    rw [← IterateAdd]
    simpa [R, Nat.add_zero] using (hper 0).symm
  have hzeroState : Iterate R t n = 0 := by
    by_contra hnz
    have hopen :=
      NegTwoCycleOpen p hQ hD hpos hcop (Iterate R t n) hnz period hp0
        (by simpa [R] using hy)
    have hcabs : p.C.natAbs = 1 := by
      rw [hC]
      rfl
    omega
  have hex : ∃ s, Iterate R s n = 0 := ⟨t, hzeroState⟩
  let τ := Nat.find hex
  have hτ : Iterate R τ n = 0 := Nat.find_spec hex
  have hmin : ∀ s, s < τ → Iterate R s n ≠ 0 := by
    intro s hs h0
    exact Nat.find_min hex hs h0
  have hstay : ∀ j, Iterate R j 0 = 0 := by
    intro j
    induction j with
    | zero => {
        simp [Iterate]
      }
    | succ j ih => {
        rw [Iterate, ih]
        simpa [R] using NegTwoZeroFixed p hQ hD hcop
      }
  have htail : ∀ j, Iterate R (τ + j) n = 0 := by
    intro j
    rw [IterateAdd, hτ]
    exact hstay j
  have hle : τ ≤ t := by
    by_contra hgt
    exact hmin t (by omega) hzeroState
  refine ⟨τ, hτ, hmin, ?_, ?_, ?_⟩
  · {
      intro k
      have hL := htail k
      have hRv := htail (1 + k)
      rw [show τ + (1 + k) = τ + 1 + k by omega] at hRv
      rw [hL, hRv]
    }
  · {
      intro s period hs hp
      refine ⟨τ - s - 1, ?_⟩
      have hLidx : s + (τ - s - 1) = τ - 1 := by omega
      have hRidx : s + period + (τ - s - 1) =
          τ + (period - 1) := by omega
      have hL : Iterate R (τ - 1) n ≠ 0 := hmin (τ - 1) (by omega)
      have hRv : Iterate R (τ + (period - 1)) n = 0 :=
        htail (period - 1)
      rw [hLidx, hRidx]
      intro heq
      exact hL (heq.trans hRv)
    }
  · {
      have hcabs : p.C.natAbs = 1 := by
        rw [hC]
        rfl
      rw [hcabs] at ht
      rw [hcabs]
      omega
    }

/-- A state sent to `0` is `0` or `-c`. -/
theorem NegTwoOnlyToZero (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (_hpos : 0 < p.C)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (x : ℤ)
    (h : TotalReturn p (TwoEvery p hQ hcop) x = 0) :
    x = 0 ∨ x = -p.C := by
  by_cases hx : (2 : ℤ) ∣ x
  · {
      have hform := NegTwoFormulaEven p hQ hD hcop x hx
      rw [hform] at h
      have hquot : x / 2 = 0 := by
        have hneg : -(x / 2) = 0 := h
        omega
      have hmul : (2 : ℤ) * (x / 2) = x :=
        Int.mul_ediv_cancel' hx
      left
      rw [hquot] at hmul
      omega
    }
  · {
      have hoddC : ¬ (2 : ℤ) ∣ p.C := by
        intro hdiv
        have hnat : 2 ∣ p.C.natAbs := by
          simpa using (Int.natAbs_dvd_natAbs.mpr hdiv)
        have hd2 : 2 ∣ p.D.natAbs := by
          rw [hD]
          decide
        have hgcd : 2 ∣ Nat.gcd p.C.natAbs p.D.natAbs :=
          Nat.dvd_gcd hnat hd2
        rw [hcop] at hgcd
        omega
      have hsum : (2 : ℤ) ∣ x + p.C := TwoOddSum x p.C hx hoddC
      have hform := NegTwoFormulaOdd p hQ hD hcop x hx
      rw [hform] at h
      have hquot : (x + p.C) / 2 = 0 := by
        have hneg : -((x + p.C) / 2) = 0 := h
        omega
      have hmul : (2 : ℤ) * ((x + p.C) / 2) = x + p.C :=
        Int.mul_ediv_cancel' hsum
      right
      rw [hquot] at hmul
      omega
    }

/-- A nonzero seed reaches `0` through `-c`. -/
theorem NegTwoOneThroughNeg (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hC : p.C = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hn : n ≠ 0) :
    let R := TotalReturn p (TwoEvery p hQ hcop)
    ∃ τ : ℕ, 0 < τ ∧ Iterate R (τ - 1) n = -p.C ∧
      Iterate R τ n = 0 := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  obtain ⟨τ, hτ, hmin, _hper, _hearly, _hbound⟩ :=
    NegTwoOneFirstZero p hQ hD hC hcop n
  have hposτ : 0 < τ := by
    by_contra h0
    have hτ0 : τ = 0 := by omega
    have hn0 : Iterate R 0 n = n := by simp [Iterate]
    rw [hτ0, hn0] at hτ
    exact hn hτ
  have hstep : R (Iterate R (τ - 1) n) = 0 := by
    have hidx : τ - 1 + 1 = τ := by omega
    have hnext : Iterate R ((τ - 1) + 1) n = 0 := by
      simpa [hidx] using hτ
    rw [Iterate] at hnext
    simpa [R] using hnext
  have hpos : 0 < p.C := by
    rw [hC]
    decide
  have hwhich :=
    NegTwoOnlyToZero p hQ hD hpos hcop (Iterate R (τ - 1) n)
      (by simpa [R] using hstep)
  have hnot : Iterate R (τ - 1) n ≠ 0 := hmin (τ - 1) (by omega)
  refine ⟨τ, hposτ, ?_, hτ⟩
  rcases hwhich with hzero | hneg
  · {
      exact False.elim (hnot hzero)
    }
  · {
      exact hneg
    }

/-- The only states sent to `-1` are `1` and `2`. -/
theorem NegTwoOnlyToNegOne (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hC : p.C = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (x : ℤ)
    (h : TotalReturn p (TwoEvery p hQ hcop) x = -1) :
    x = 1 ∨ x = 2 := by
  by_cases hx : (2 : ℤ) ∣ x
  · {
      have hform := NegTwoFormulaEven p hQ hD hcop x hx
      rw [hform] at h
      have hquot : x / 2 = 1 := by
        have hneg : -(x / 2) = -1 := h
        omega
      have hmul : (2 : ℤ) * (x / 2) = x :=
        Int.mul_ediv_cancel' hx
      right
      rw [hquot] at hmul
      omega
    }
  · {
      have hoddC : ¬ (2 : ℤ) ∣ p.C := by
        intro hdiv
        have hnat : 2 ∣ p.C.natAbs := by
          simpa using (Int.natAbs_dvd_natAbs.mpr hdiv)
        have hd2 : 2 ∣ p.D.natAbs := by
          rw [hD]
          decide
        have hgcd : 2 ∣ Nat.gcd p.C.natAbs p.D.natAbs :=
          Nat.dvd_gcd hnat hd2
        rw [hcop] at hgcd
        omega
      have hsum : (2 : ℤ) ∣ x + p.C := TwoOddSum x p.C hx hoddC
      have hform := NegTwoFormulaOdd p hQ hD hcop x hx
      rw [hform] at h
      have hquot : (x + p.C) / 2 = 1 := by
        have hneg : -((x + p.C) / 2) = -1 := h
        omega
      have hmul : (2 : ℤ) * ((x + p.C) / 2) = x + p.C :=
        Int.mul_ediv_cancel' hsum
      left
      rw [hquot, hC] at hmul
      omega
    }

/-- Two steps before the first `0`, the state is `1` or `2`. -/
theorem NegTwoOneTwoBefore (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hC : p.C = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    let R := TotalReturn p (TwoEvery p hQ hcop)
    ∀ τ : ℕ, 1 < τ → Iterate R (τ - 1) n = -p.C →
      Iterate R τ n = 0 →
      Iterate R (τ - 2) n = 1 ∨ Iterate R (τ - 2) n = 2 := by
  intro R τ hτ hneg hzero
  have hstep : R (Iterate R (τ - 2) n) = -1 := by
    have hidx : τ - 2 + 1 = τ - 1 := by omega
    have hnext : Iterate R ((τ - 2) + 1) n = -p.C := by
      simpa [hidx] using hneg
    rw [hC] at hnext
    rw [Iterate] at hnext
    simpa [R] using hnext
  exact NegTwoOnlyToNegOne p hQ hD hC hcop
    (Iterate R (τ - 2) n) (by simpa [R] using hstep)

/-- The first visit to `0` is preceded by `1` or `2` when it is not immediate. -/
theorem NegTwoOneFirstTwoBefore (p : Parameters) (hQ : p.Q = 1)
    (hD : p.D = -2) (hC : p.C = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hn : n ≠ 0) :
    let R := TotalReturn p (TwoEvery p hQ hcop)
    ∃ τ : ℕ, 0 < τ ∧ Iterate R (τ - 1) n = -p.C ∧
      Iterate R τ n = 0 ∧
      (1 < τ → Iterate R (τ - 2) n = 1 ∨
        Iterate R (τ - 2) n = 2) := by
  let R := TotalReturn p (TwoEvery p hQ hcop)
  obtain ⟨τ, hpos, hpred, hzero⟩ :=
    NegTwoOneThroughNeg p hQ hD hC hcop n hn
  refine ⟨τ, hpos, hpred, hzero, ?_⟩
  intro hlate
  exact NegTwoOneTwoBefore p hQ hD hC hcop n τ hlate hpred hzero

/-
Uncompiled historical appendix. Everything from this opening comment through
its matching closing delimiter near the end of this file is source material,
not declarations checked by Lean. Repeated theorem names here do not define
or replace the active APIs above. Compilation of this file certifies only
the active declarations outside this appendix.

/-- The map with multiplier equal to the divisor and with zero offset. -/
def ZeroOffset (d : ℤ) : Parameters :=
  { Q := d, C := 0, D := d }

/-- A nonmultiple takes the affine step `d * n`. -/
theorem ZeroOffsetAffine (d n : ℤ) (hmiss : ¬ d ∣ n) :
    RawStep (ZeroOffset d) n = d * n := by
  unfold RawStep ZeroOffset
  rw [if_neg hmiss]
  ring

/-- The next step returns a nonmultiple to itself. -/
theorem ZeroOffsetReturn (d n : ℤ) (hd : d ≠ 0) (hmiss : ¬ d ∣ n) :
    RawStep (ZeroOffset d) (d * n) = n := by
  have hdiv : d ∣ d * n := ⟨n, rfl⟩
  unfold RawStep ZeroOffset
  rw [if_pos hdiv]
  exact Int.mul_ediv_cancel_left n hd

/-- A nonmultiple has raw period two: `n, d*n, n, d*n, ...`. -/
theorem ZeroOffsetPeriod (d n : ℤ) (hd : d ≠ 0) (hmiss : ¬ d ∣ n)
    (k : ℕ) :
    Iterate (RawStep (ZeroOffset d)) k n =
      if k % 2 = 0 then n else d * n := by
  induction k with
  | zero => {
      simp [Iterate]
    }
  | succ k ih => {
      rw [Iterate, ih]
      by_cases he : k % 2 = 0
      · {
          rw [if_pos he, ZeroOffsetAffine d n hmiss]
          have hodd : (k + 1) % 2 ≠ 0 := by omega
          rw [if_neg hodd]
        }
      · {
          rw [if_neg he, ZeroOffsetReturn d n hd hmiss]
          have heven : (k + 1) % 2 = 0 := by omega
          rw [if_pos heven]
        }
    }

/-- A multiple is replaced by its quotient. -/
theorem ZeroOffsetDiv (d n : ℤ) (hd : d ≠ 0) (hdiv : d ∣ n) :
    RawStep (ZeroOffset d) n = n / d := by
  unfold RawStep ZeroOffset
  rw [if_pos hdiv]

/-- `a` divisions remove the factor `d ^ a`. -/
theorem ZeroOffsetPower (d m : ℤ) (hd : d ≠ 0) (a : ℕ) :
    Iterate (RawStep (ZeroOffset d)) a (d ^ a * m) = m := by
  induction a with
  | zero => {
      simp [Iterate]
    }
  | succ a ih => {
      have hfac : d ^ (a + 1) * m = d * (d ^ a * m) := by
        rw [pow_succ']
        ring
      have hdiv : d ∣ d ^ (a + 1) * m := ⟨d ^ a * m, hfac⟩
      rw [Iterate, ZeroOffsetDiv d _ hd hdiv, hfac]
      rw [Int.mul_ediv_cancel_left _ hd]
      exact ih
    }

/-- After the exact power is removed, the orbit alternates. -/
theorem ZeroOffsetTail (d m : ℤ) (hd : d ≠ 0) (hmiss : ¬ d ∣ m)
    (a k : ℕ) (hk : a ≤ k) :
    Iterate (RawStep (ZeroOffset d)) k (d ^ a * m) =
      if (k - a) % 2 = 0 then m else d * m := by
  have hsplit : k = a + (k - a) := by omega
  rw [hsplit, IterateAdd, ZeroOffsetPower d m hd a]
  exact ZeroOffsetPeriod d m hd hmiss (k - a)

/-- If `|d| ≥ 2` and `n ≠ 0`, remove every factor `d`. -/
theorem ZeroOffsetFactor (d n : ℤ) (hd : 2 ≤ d.natAbs) (hn : n ≠ 0) :
    ∃ a : ℕ, ∃ m : ℤ, n = d ^ a * m ∧ ¬ d ∣ m := by
  suffices hrec : ∀ N : ℕ, ∀ n : ℤ, n.natAbs = N → n ≠ 0 →
      ∃ a : ℕ, ∃ m : ℤ, n = d ^ a * m ∧ ¬ d ∣ m by
    exact hrec n.natAbs n rfl hn
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    {
      intro n hN hn
      by_cases hdiv : d ∣ n
      · {
          obtain ⟨q, hq⟩ := hdiv
          have hqne : q ≠ 0 := by
            intro h0
            apply hn
            rw [hq, h0]
            ring
          have hsmall : q.natAbs < N := by
            rw [← hN, hq, Int.natAbs_mul]
            have hqpos : 1 ≤ q.natAbs := by
              exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hqne)
            have hge : 2 * q.natAbs ≤ d.natAbs * q.natAbs := by
              exact Nat.mul_le_mul_right q.natAbs hd
            omega
          obtain ⟨a, m, hm, hmiss⟩ := ih q.natAbs hsmall q rfl hqne
          refine ⟨a + 1, m, ?_, hmiss⟩
          rw [hq, hm, pow_succ']
          ring
        }
      · {
          exact ⟨0, n, by simp, hdiv⟩
        }
    }

/-- Every nonzero seed eventually alternates. -/
theorem ZeroOffsetEventuallyAlternates (d n : ℤ)
    (hd : 2 ≤ d.natAbs) (hn : n ≠ 0) :
    ∃ a : ℕ, ∃ m : ℤ, ¬ d ∣ m ∧ ∀ k : ℕ, a ≤ k →
      Iterate (RawStep (ZeroOffset d)) k n =
        if (k - a) % 2 = 0 then m else d * m := by
  obtain ⟨a, m, hnfac, hmiss⟩ := ZeroOffsetFactor d n hd hn
  have hd0 : d ≠ 0 := by
    intro h0
    have : d.natAbs = 0 := by
      rw [h0]
      rfl
    omega
  refine ⟨a, m, hmiss, ?_⟩
  intro k hk
  rw [hnfac]
  exact ZeroOffsetTail d m hd0 hmiss a k hk

/-- Multiplier equal to the divisor, with offset `d * s`. -/
def EqualMultiplier (d s : ℤ) : Parameters :=
  { Q := d, C := d * s, D := d }

/-- A nonmultiple takes the affine step `d * (n + s)`. -/
theorem EqualMultiplierAffine (d s n : ℤ) (hmiss : ¬ d ∣ n) :
    RawStep (EqualMultiplier d s) n = d * (n + s) := by
  unfold RawStep EqualMultiplier
  rw [if_neg hmiss]
  ring

/-- The following division translates the seed by `s`. -/
theorem EqualMultiplierSecond (d s n : ℤ) (hd : d ≠ 0)
    (hmiss : ¬ d ∣ n) :
    RawStep (EqualMultiplier d s)
        (RawStep (EqualMultiplier d s) n) = n + s := by
  rw [EqualMultiplierAffine d s n hmiss]
  have hdiv : d ∣ d * (n + s) := ⟨n + s, rfl⟩
  unfold RawStep EqualMultiplier
  rw [if_pos hdiv]
  exact Int.mul_ediv_cancel_left (n + s) hd

/-- While `n + j*s` stays nonmultiple, even times translate and odd times scale. -/
theorem EqualMultiplierRun (d s n : ℤ) (hd : d ≠ 0)
    (hmiss : ∀ j : ℕ, d ∣ n + j * s → False) (t : ℕ) :
    Iterate (RawStep (EqualMultiplier d s)) (2 * t) n = n + t * s ∧
      Iterate (RawStep (EqualMultiplier d s)) (2 * t + 1) n =
        d * (n + (t + 1) * s) := by
  induction t with
  | zero => {
      constructor
      · {
          simp [Iterate]
        }
      · {
          rw [show 2 * 0 + 1 = 1 by omega, Iterate, Iterate]
          simpa using EqualMultiplierAffine d s n (by
            intro h
            exact hmiss 0 (by simpa using h))
        }
    }
  | succ t ih => {
      obtain ⟨_, hodd⟩ := ih
      have hdiv :
          RawStep (EqualMultiplier d s) (d * (n + (t + 1) * s)) =
            n + (t + 1) * s := by
        have hdvd : d ∣ d * (n + (t + 1) * s) := ⟨n + (t + 1) * s, rfl⟩
        unfold RawStep EqualMultiplier
        rw [if_pos hdvd]
        exact Int.mul_ediv_cancel_left (n + (t + 1) * s) hd
      have hnext := EqualMultiplierAffine d s (n + (t + 1) * s) (by
        intro h
        exact hmiss (t + 1) h)
      constructor
      · {
          have hclock : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
          rw [hclock, Iterate, hodd, hdiv]
        }
      · {
          have hclock : 2 * (t + 1) + 1 = (2 * (t + 1)) + 1 := rfl
          have hprev : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
          rw [hclock, Iterate, hprev, Iterate, hodd, hdiv]
          have hsum : n + (t + 1) * s + s = n + ((t + 1) + 1) * s := by
            ring
          rw [hsum, hnext]
        }
    }

/-- The translation formulas hold through the first multiple. -/
theorem EqualMultiplierPrefix (d s n : ℤ) (hd : d ≠ 0) (j0 : ℕ)
    (hbefore : ∀ i : ℕ, i < j0 → ¬ d ∣ n + (i : ℤ) * s)
    (t : ℕ) (ht : t ≤ j0) :
    Iterate (RawStep (EqualMultiplier d s)) (2 * t) n =
      n + (t : ℤ) * s := by
  induction t with
  | zero => {
      simp [Iterate]
    }
  | succ t ih => {
      have ht' : t < j0 := by omega
      have hmiss : ¬ d ∣ n + (t : ℤ) * s := hbefore t ht'
      have hodd :
          Iterate (RawStep (EqualMultiplier d s)) (2 * t + 1) n =
            d * (n + ((t : ℤ) + 1) * s) := by
        rw [show 2 * t + 1 = 2 * t + 1 by rfl, Iterate, ih (Nat.le_of_lt ht')]
        exact EqualMultiplierAffine d s (n + (t : ℤ) * s) hmiss
      have hdiv :
          RawStep (EqualMultiplier d s)
              (d * (n + ((t : ℤ) + 1) * s)) =
            n + ((t : ℤ) + 1) * s := by
        have hdvd : d ∣ d * (n + ((t : ℤ) + 1) * s) :=
          ⟨n + ((t : ℤ) + 1) * s, rfl⟩
        unfold RawStep EqualMultiplier
        rw [if_pos hdvd]
        exact Int.mul_ediv_cancel_left (n + ((t : ℤ) + 1) * s) hd
      have hclock : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
      rw [hclock, Iterate, hodd, hdiv]
      ring
    }

/-- Before the first multiple, the odd state is the next translate scaled by `d`. -/
theorem EqualMultiplierPrefixOdd (d s n : ℤ) (hd : d ≠ 0) (j0 : ℕ)
    (hbefore : ∀ i : ℕ, i < j0 → ¬ d ∣ n + (i : ℤ) * s)
    (t : ℕ) (ht : t < j0) :
    Iterate (RawStep (EqualMultiplier d s)) (2 * t + 1) n =
      d * (n + ((t : ℤ) + 1) * s) := by
  rw [Iterate, EqualMultiplierPrefix d s n hd j0 hbefore t (Nat.le_of_lt ht)]
  exact EqualMultiplierAffine d s (n + (t : ℤ) * s) (hbefore t ht)

/-- Every seed hits at time `0` or `1`. -/
theorem EqualMultiplierFirstHit (d s n : ℤ) :
    (d ∣ n ∧ IsFirstHit (EqualMultiplier d s) n 0) ∨
      (¬ d ∣ n ∧ IsFirstHit (EqualMultiplier d s) n 1) := by
  exact DivisorOfBothHitsByOne (EqualMultiplier d s)
    (by
      refine ⟨1, ?_⟩
      simp [EqualMultiplier])
    (by
      refine ⟨s, ?_⟩
      simp [EqualMultiplier]) n

/-- At the first even multiple, the next state is the exact quotient. -/
theorem EqualMultiplierAtHit (d s n : ℤ) (hd : d ≠ 0) (j0 : ℕ)
    (hbefore : ∀ i : ℕ, i < j0 → ¬ d ∣ n + (i : ℤ) * s)
    (hhit : d ∣ n + (j0 : ℤ) * s) :
    Iterate (RawStep (EqualMultiplier d s)) (2 * j0 + 1) n =
      (n + (j0 : ℤ) * s) / d := by
  rw [Iterate,
    EqualMultiplierPrefix d s n hd j0 hbefore j0 (Nat.le_refl j0)]
  unfold RawStep EqualMultiplier
  rw [if_pos hhit]

/-- The first even multiple occurs before `|d|/gcd(s,d)`. -/
theorem EqualMultiplierLeastHit (d s n : ℤ) (hd : d ≠ 0)
    (hn : (Int.gcd s d : ℤ) ∣ n) :
    ∃ j0 : ℕ, j0 < d.natAbs / Int.gcd s d ∧
      d ∣ n + (j0 : ℤ) * s ∧
      (∀ i : ℕ, i < j0 → ¬ d ∣ n + (i : ℤ) * s) ∧
      Iterate (RawStep (EqualMultiplier d s)) (2 * j0 + 1) n =
        (n + (j0 : ℤ) * s) / d := by
  obtain ⟨j, hjlt, hjdiv⟩ := TranslationHitBound d s n hd hn
  let j0 : ℕ := Nat.find (show ∃ k : ℕ, d ∣ n + (k : ℤ) * s from ⟨j, hjdiv⟩)
  have hdiv : d ∣ n + (j0 : ℤ) * s := Nat.find_spec
    (show ∃ k : ℕ, d ∣ n + (k : ℤ) * s from ⟨j, hjdiv⟩)
  have hmin : ∀ i : ℕ, i < j0 → ¬ d ∣ n + (i : ℤ) * s := by
    intro i hi hdv
    exact Nat.find_min
      (show ∃ k : ℕ, d ∣ n + (k : ℤ) * s from ⟨j, hjdiv⟩) hi hdv
  have hle : j0 ≤ j := Nat.find_le hjdiv
  refine ⟨j0, ?_, hdiv, hmin, ?_⟩
  · {
      omega
    }
  · {
      exact EqualMultiplierAtHit d s n hd j0 hmin hdiv
    }

/-- If the gcd misses the seed, every even state stays nonmultiple. -/
theorem EqualMultiplierForever (d s n : ℤ) (hd : d ≠ 0)
    (hmiss : ¬ (Int.gcd s d : ℤ) ∣ n) (t : ℕ) :
    Iterate (RawStep (EqualMultiplier d s)) (2 * t) n = n + t * s ∧
      Iterate (RawStep (EqualMultiplier d s)) (2 * t + 1) n =
        d * (n + (t + 1) * s) := by
  exact EqualMultiplierRun d s n hd (by
    intro j hj
    exact hmiss ((TranslationHitsNat d s n hd).1 ⟨j, hj⟩)) t

/-- An integer translate is a multiple iff the gcd divides the seed. -/
theorem TranslationHitsInt (d s n : ℤ) :
    (∃ j : ℤ, d ∣ n + j * s) ↔ (Int.gcd s d : ℤ) ∣ n := by
  constructor
  · {
      intro h
      obtain ⟨j, hj⟩ := h
      have hs : (Int.gcd s d : ℤ) ∣ s := Int.gcd_dvd_left s d
      have hdvd : (Int.gcd s d : ℤ) ∣ d := Int.gcd_dvd_right s d
      have hjs : (Int.gcd s d : ℤ) ∣ j * s :=
        dvd_mul_of_dvd_right hs j
      have hsum : (Int.gcd s d : ℤ) ∣ (n + j * s) - j * s := by
        exact dvd_sub hj hjs
      simpa [sub_eq_add_neg, add_assoc, add_left_neg, add_zero] using hsum
    }
  · {
      intro hn
      have hab := Int.gcd_eq_gcd_ab s d
      obtain ⟨q, hq⟩ := hn
      refine ⟨-((s.gcdA d) * q), ?_⟩
      have hbez :
          n + (-((s.gcdA d) * q)) * s =
            d * ((s.gcdB d) * q) := by
        calc
          n + (-((s.gcdA d) * q)) * s
              = (Int.gcd s d : ℤ) * q - (s.gcdA d) * q * s := by
                rw [hq]
                ring
          _ = ((Int.gcd s d : ℤ) - s * (s.gcdA d)) * q := by ring
          _ = d * (s.gcdB d) * q := by
                rw [hab]
                ring
          _ = d * ((s.gcdB d) * q) := by ring
      exact ⟨(s.gcdB d) * q, hbez⟩
    }

/-- The same divisibility occurs at a nonnegative time. -/
theorem TranslationHitsNat (d s n : ℤ) (hd : d ≠ 0) :
    (∃ j : ℕ, d ∣ n + (j : ℤ) * s) ↔ (Int.gcd s d : ℤ) ∣ n := by
  constructor
  · {
      intro h
      obtain ⟨j, hj⟩ := h
      exact (TranslationHitsInt d s n).1 ⟨(j : ℤ), hj⟩
    }
  · {
      intro hn
      obtain ⟨j, hj⟩ := (TranslationHitsInt d s n).2 hn
      have hgd := Int.gcd_dvd_right s d
      have hgs := Int.gcd_dvd_left s d
      obtain ⟨m, hm⟩ := hgd
      obtain ⟨u, hu⟩ := hgs
      have hm0 : m ≠ 0 := by
        intro h0
        apply hd
        rw [hm, h0]
        ring
      let p : ℕ := m.natAbs
      have hp0 : (p : ℤ) ≠ 0 := by
        exact_mod_cast Int.natAbs_ne_zero.mpr hm0
      have hper : d ∣ (p : ℤ) * s := by
        have hsign : (p : ℤ) = m ∨ (p : ℤ) = -m := by
          cases m with
          | ofNat k => {
              left
              rfl
            }
          | negSucc k => {
              right
              rfl
            }
        rcases hsign with hpos | hneg
        · {
            rw [hpos, hm, hu]
            refine ⟨u, ?_⟩
            ring
          }
        · {
            rw [hneg, hm, hu]
            refine ⟨-u, ?_⟩
            ring
          }
      let r : ℤ := j % (p : ℤ)
      have hr0 : 0 ≤ r := Int.emod_nonneg j hp0
      have hr : n + r * s = (n + j * s) - (j / (p : ℤ)) * ((p : ℤ) * s) := by
        have hid := Int.emod_add_ediv j (p : ℤ)
        calc
          n + r * s = n + (j % (p : ℤ)) * s := rfl
          _ = n + (j - (p : ℤ) * (j / (p : ℤ))) * s := by
                rw [← hid]
                ring
          _ = (n + j * s) - (j / (p : ℤ)) * ((p : ℤ) * s) := by ring
      have hdiv : d ∣ n + r * s := by
        rw [hr]
        exact dvd_sub hj (dvd_mul_of_dvd_right hper _)
      refine ⟨r.toNat, ?_⟩
      rw [Int.toNat_of_nonneg hr0]
      exact hdiv
    }

/-- A nonnegative solution can be chosen below `|d|/gcd(s,d)`. -/
theorem TranslationHitBound (d s n : ℤ) (hd : d ≠ 0)
    (hn : (Int.gcd s d : ℤ) ∣ n) :
    ∃ j : ℕ, j < d.natAbs / Int.gcd s d ∧
      d ∣ n + (j : ℤ) * s := by
  obtain ⟨j, hj⟩ := (TranslationHitsInt d s n).2 hn
  have hgd := Int.gcd_dvd_right s d
  have hgs := Int.gcd_dvd_left s d
  obtain ⟨m, hm⟩ := hgd
  obtain ⟨u, hu⟩ := hgs
  have hm0 : m ≠ 0 := by
    intro h0
    apply hd
    rw [hm, h0]
    ring
  let p : ℕ := m.natAbs
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.mpr hm0
  have hppos : (0 : ℤ) < p := by
    exact Int.natCast_pos.mpr (Int.natAbs_pos.mpr hm0)
  have hper : d ∣ (p : ℤ) * s := by
    have hsign : (p : ℤ) = m ∨ (p : ℤ) = -m := by
      cases m with
      | ofNat _ => {
          left
          rfl
        }
      | negSucc _ => {
          right
          rfl
        }
    rcases hsign with hpos | hneg
    · {
        rw [hpos, hm, hu]
        refine ⟨u, ?_⟩
        ring
      }
    · {
        rw [hneg, hm, hu]
        refine ⟨-u, ?_⟩
        ring
      }
  let r : ℤ := j % (p : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg j hp0
  have hrlt : r < (p : ℤ) := Int.emod_lt_of_pos j hppos
  have hr : n + r * s = (n + j * s) - (j / (p : ℤ)) * ((p : ℤ) * s) := by
    have hid := Int.emod_add_ediv j (p : ℤ)
    calc
      n + r * s = n + (j - (p : ℤ) * (j / (p : ℤ))) * s := by
        rw [← hid]
        ring
      _ = (n + j * s) - (j / (p : ℤ)) * ((p : ℤ) * s) := by ring
  have hdiv : d ∣ n + r * s := by
    rw [hr]
    exact dvd_sub hj (dvd_mul_of_dvd_right hper _)
  have hpd : d.natAbs = Int.gcd s d * p := by
    rw [hm, Int.natAbs_mul, Int.natAbs_natCast]
  refine ⟨r.toNat, ?_, ?_⟩
  · {
      rw [Int.toNat_lt_of_nonneg hr0, hpd, Nat.mul_div_cancel_left _
        (Int.gcd_pos_of_ne_zero_right hd)]
      exact_mod_cast hrlt
    }
  · {
      rw [Int.toNat_of_nonneg hr0]
      exact hdiv
    }

/-- One undivided step multiplies by `q` and adds `c`. -/
theorem AffineStateSucc (q c n : ℤ) (j : ℕ) :
    AffineState q c (j + 1) n = q * AffineState q c j n + c := by
  unfold AffineState
  rw [TrapSumRec q j]
  ring

/-- The residue branch of one undivided step. -/
def ResidueStep (q c : ℤ) (m : ℕ) (r : ZMod m) : ZMod m :=
  (q : ZMod m) * r + (c : ZMod m)

/-- The affine state reduces to the iterated residue branch. -/
theorem AffineStateResidue (q c n : ℤ) (m : ℕ) (j : ℕ) :
    ((AffineState q c j n : ℤ) : ZMod m) =
      (ResidueStep q c m)^[j] (n : ZMod m) := by
  induction j with
  | zero => {
      simp [AffineState, ResidueStep]
    }
  | succ j ih => {
      rw [AffineStateSucc, Function.iterate_succ_apply']
      simp [ResidueStep, ih]
    }

/-- A residue class that never meets `0` has no first hit. -/
theorem ClassMissesHasNoHit (p : Parameters) (n : ℤ)
    (hmiss : ∀ j : ℕ,
      (ResidueStep p.Q p.C p.D.natAbs)^[j]
          (n : ZMod p.D.natAbs) ≠ 0) :
    ∀ j : ℕ, ¬ IsFirstHit p n j := by
  intro j hj
  have hcast :
      ((AffineState p.Q p.C j n : ℤ) : ZMod p.D.natAbs) = 0 := by
    have hm : (p.D.natAbs : ℤ) ∣ AffineState p.Q p.C j n := by
      have hd := hj.1
      have hunit : IsUnit (Int.sign p.D) := Int.isUnit_sign
      have hsplit : p.D = (p.D.natAbs : ℤ) * Int.sign p.D := by
        rw [Int.sign_mul_natAbs]
        ring
      obtain ⟨u, hu⟩ := hunit
      obtain ⟨k, hk⟩ := hd
      refine ⟨k * u, ?_⟩
      rw [hsplit] at hk
      -- `D` and `|D|` are associates, so they divide the same integers.
      have hcomm : (p.D.natAbs : ℤ) * Int.sign p.D * k =
          (p.D.natAbs : ℤ) * (Int.sign p.D * k) := by ring
      rw [hcomm] at hk
      have huinv : Int.sign p.D * u = 1 := by
        simpa using hu
      calc
        AffineState p.Q p.C j n =
            (p.D.natAbs : ℤ) * (Int.sign p.D * k) := hk
        _ = (p.D.natAbs : ℤ) * (k * (Int.sign p.D * u)) := by
              rw [huinv]
              ring
        _ = (p.D.natAbs : ℤ) * (k * u) := by
              rw [huinv]
              ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (AffineState p.Q p.C j n) p.D.natAbs).2 hm
  have hres := AffineStateResidue p.Q p.C n p.D.natAbs j
  exact hmiss j (hres.symm.trans hcast)

/-- `j` is the least time the residue walk meets `0`. -/
def ResidueHits (q c : ℤ) (m : ℕ) (r : ZMod m) (j : ℕ) : Prop :=
  (ResidueStep q c m)^[j] r = 0 ∧
    ∀ i : ℕ, i < j → (ResidueStep q c m)^[i] r ≠ 0

/-- The least residue hit is the first hit of every integer in that class. -/
theorem ResidueLeastIsFirstHit (p : Parameters) (n : ℤ) (j : ℕ)
    (hhit : ResidueHits p.Q p.C p.D.natAbs (n : ZMod p.D.natAbs) j) :
    IsFirstHit p n j := by
  obtain ⟨hzero, hearly⟩ := hhit
  have hres := AffineStateResidue p.Q p.C n p.D.natAbs
  have hassoc : (p.D.natAbs : ℤ) ∣ AffineState p.Q p.C j n := by
    have hcast :
        ((AffineState p.Q p.C j n : ℤ) : ZMod p.D.natAbs) = 0 := by
      rw [hres j, hzero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (AffineState p.Q p.C j n) p.D.natAbs).1 hcast
  have hunit : IsUnit (Int.sign p.D) := Int.isUnit_sign
  obtain ⟨u, hu⟩ := hunit
  obtain ⟨k, hk⟩ := hassoc
  have hdvd : p.D ∣ AffineState p.Q p.C j n := by
    refine ⟨u * k, ?_⟩
    have hsplit : p.D = Int.sign p.D * (p.D.natAbs : ℤ) :=
      Int.sign_mul_natAbs p.D
    have hu1 : Int.sign p.D * u = 1 := by simpa using hu
    calc
      AffineState p.Q p.C j n = (p.D.natAbs : ℤ) * k := hk
      _ = (Int.sign p.D * u) * ((p.D.natAbs : ℤ) * k) := by
            rw [hu1]
            ring
      _ = p.D * (u * k) := by
            rw [hsplit]
            ring
  refine ⟨hdvd, ?_⟩
  intro i hi hdiv
  have hm : (p.D.natAbs : ℤ) ∣ AffineState p.Q p.C i n := by
    have hsign : IsUnit (Int.sign p.D) := Int.isUnit_sign
    obtain ⟨v, hv⟩ := hsign
    obtain ⟨k, hk⟩ := hdiv
    refine ⟨Int.sign p.D * k, ?_⟩
    have hsplit : p.D = Int.sign p.D * (p.D.natAbs : ℤ) :=
      Int.sign_mul_natAbs p.D
    calc
      AffineState p.Q p.C i n = p.D * k := hk
      _ = Int.sign p.D * (p.D.natAbs : ℤ) * k := by rw [hsplit]
      _ = (p.D.natAbs : ℤ) * (Int.sign p.D * k) := by ring
  have hcast :
      ((AffineState p.Q p.C i n : ℤ) : ZMod p.D.natAbs) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (AffineState p.Q p.C i n) p.D.natAbs).2 hm
  have hwalk : (ResidueStep p.Q p.C p.D.natAbs)^[i]
      (n : ZMod p.D.natAbs) = 0 := by
    rw [← hres i]
    exact hcast
  exact hearly i hi hwalk

/-- A least hit with `|q|^j ≥ |d|` blocks every slope below `|d|`. -/
theorem LargeHitBlocksSlope (q c : ℤ) (m : ℕ) (r : ZMod m) (j : ℕ)
    (hhit : ResidueHits q c m r j) (hbig : m ≤ q.natAbs ^ j) :
    ¬ ∃ A : ℕ, A < m ∧ ∀ (s : ZMod m) (k : ℕ),
        ResidueHits q c m s k → q.natAbs ^ k ≤ A := by
  intro h
  obtain ⟨A, hA, hall⟩ := h
  have hle : q.natAbs ^ j ≤ A := hall r j hhit
  omega

/-- Every residue class misses `0` or has a least hit. -/
theorem ResidueHitOrMiss (q c : ℤ) (m : ℕ) (r : ZMod m) :
    (∀ j : ℕ, (ResidueStep q c m)^[j] r ≠ 0) ∨
      ∃ j : ℕ, ResidueHits q c m r j := by
  by_cases hmiss : ∀ j : ℕ, (ResidueStep q c m)^[j] r ≠ 0
  · {
      exact Or.inl hmiss
    }
  · {
      push_neg at hmiss
      obtain ⟨j, hj⟩ := hmiss
      classical
      let j0 := Nat.find hj
      refine Or.inr ⟨j0, ?_⟩
      refine ⟨Nat.find_spec hj, ?_⟩
      intro i hi
      exact Nat.find_min hj hi
    }

/-- A residue class has at most one least hit. -/
theorem ResidueHitsUnique (q c : ℤ) (m : ℕ) (r : ZMod m)
    (j k : ℕ) (hj : ResidueHits q c m r j)
    (hk : ResidueHits q c m r k) : j = k := by
  rcases Nat.lt_trichotomy j k with hlt | heq | hgt
  · {
      exact False.elim (hk.2 j hlt hj.1)
    }
  · {
      exact heq
    }
  · {
      exact False.elim (hj.2 k hgt hk.1)
    }

/-- Every class hits with a small exponent iff none misses and none is large. -/
theorem UniformSlopeIff (q c : ℤ) (m : ℕ) :
    (∀ r : ZMod m, ∃ j : ℕ,
        ResidueHits q c m r j ∧ q.natAbs ^ j < m) ↔
      (∀ r : ZMod m, ∃ j : ℕ, ResidueHits q c m r j) ∧
        ¬ ∃ r : ZMod m, ∃ j : ℕ,
            ResidueHits q c m r j ∧ m ≤ q.natAbs ^ j := by
  constructor
  · {
      intro h
      refine ⟨fun r => ?_, ?_⟩
      · {
          obtain ⟨j, hj, _⟩ := h r
          exact ⟨j, hj⟩
        }
      · {
          intro hbad
          obtain ⟨r, j, hj, hbig⟩ := hbad
          obtain ⟨k, hk, hsmall⟩ := h r
          have heq := ResidueHitsUnique q c m r j k hj hk
          omega
        }
    }
  · {
      intro h r
      obtain ⟨j, hj⟩ := h.1 r
      refine ⟨j, hj, ?_⟩
      have hnot : ¬ m ≤ q.natAbs ^ j := by
        intro hbig
        exact h.2 ⟨r, j, hj, hbig⟩
      omega
    }

/-- A first hit is the least residue hit of the seed's class. -/
theorem FirstHitIsResidueLeast (p : Parameters) (n : ℤ) (j : ℕ)
    (hhit : IsFirstHit p n j) :
    ResidueHits p.Q p.C p.D.natAbs (n : ZMod p.D.natAbs) j := by
  obtain ⟨hdvd, hearly⟩ := hhit
  have hres := AffineStateResidue p.Q p.C n p.D.natAbs
  have hm : (p.D.natAbs : ℤ) ∣ AffineState p.Q p.C j n := by
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨Int.sign p.D * k, ?_⟩
    calc
      AffineState p.Q p.C j n = p.D * k := hk
      _ = Int.sign p.D * (p.D.natAbs : ℤ) * k := by
            rw [Int.sign_mul_natAbs p.D]
      _ = (p.D.natAbs : ℤ) * (Int.sign p.D * k) := by ring
  have hzero :
      (ResidueStep p.Q p.C p.D.natAbs)^[j]
        (n : ZMod p.D.natAbs) = 0 := by
    rw [← hres j]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (AffineState p.Q p.C j n) p.D.natAbs).2 hm
  refine ⟨hzero, ?_⟩
  intro i hi hwalk
  have hcast :
      ((AffineState p.Q p.C i n : ℤ) : ZMod p.D.natAbs) = 0 := by
    rw [hres i]
    exact hwalk
  have hmd : (p.D.natAbs : ℤ) ∣ AffineState p.Q p.C i n :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (AffineState p.Q p.C i n) p.D.natAbs).1 hcast
  have hunit : IsUnit (Int.sign p.D) := Int.isUnit_sign
  obtain ⟨u, hu⟩ := hunit
  obtain ⟨k, hk⟩ := hmd
  have hdvd_i : p.D ∣ AffineState p.Q p.C i n := by
    refine ⟨u * k, ?_⟩
    have hu1 : Int.sign p.D * u = 1 := by simpa using hu
    calc
      AffineState p.Q p.C i n = (p.D.natAbs : ℤ) * k := hk
      _ = (Int.sign p.D * u) * ((p.D.natAbs : ℤ) * k) := by
            rw [hu1]
            ring
      _ = p.D * (u * k) := by
            rw [Int.sign_mul_natAbs p.D]
            ring
  exact hearly i hi hdvd_i

/-- Small first-hit exponents are exactly the small residue exponents. -/
theorem IntegerSlopeIff (p : Parameters) :
    (∀ n : ℤ, ∃ j : ℕ,
        IsFirstHit p n j ∧ p.Q.natAbs ^ j < p.D.natAbs) ↔
      ∀ r : ZMod p.D.natAbs, ∃ j : ℕ,
        ResidueHits p.Q p.C p.D.natAbs r j ∧
          p.Q.natAbs ^ j < p.D.natAbs := by
  constructor
  · {
      intro h r
      obtain ⟨n, hn⟩ := ZMod.intCast_surjective r
      obtain ⟨j, hj, hsmall⟩ := h n
      refine ⟨j, ?_, hsmall⟩
      rw [← hn]
      exact FirstHitIsResidueLeast p n j hj
    }
  · {
      intro h n
      obtain ⟨j, hj, hsmall⟩ := h (n : ZMod p.D.natAbs)
      exact ⟨j, ResidueLeastIsFirstHit p n j hj, hsmall⟩
    }

/-- The offset sum is at most the geometric sum of `|q|`. -/
theorem TrapSumAbsLe (q : ℤ) (j : ℕ) :
    (TrapSum q j).natAbs ≤ ∑ i ∈ Finset.range j, q.natAbs ^ i := by
  induction j with
  | zero => {
      simp [TrapSum]
    }
  | succ j ih => {
      have hrec : TrapSum q (j + 1) = q * TrapSum q j + 1 := by
        simpa [Nat.succ_eq_add_one] using TrapSumRec q j
      have hstep :
          (TrapSum q (j + 1)).natAbs ≤
            q.natAbs * (TrapSum q j).natAbs + 1 := by
        rw [hrec]
        calc
          (q * TrapSum q j + 1).natAbs ≤
              (q * TrapSum q j).natAbs + (1 : ℤ).natAbs :=
            Int.natAbs_add_le _ _
          _ ≤ q.natAbs * (TrapSum q j).natAbs + 1 := by
              rw [Int.natAbs_mul, Int.natAbs_one]
              omega
      have hgeom :
          q.natAbs * (∑ i ∈ Finset.range j, q.natAbs ^ i) + 1 =
            ∑ i ∈ Finset.range (j + 1), q.natAbs ^ i := by
        -- `S(j + 1) = 1 + |q| * S(j)`, by shifting the powers.
        rw [Finset.sum_range_succ', pow_zero, add_comm,
          Finset.mul_sum]
        congr 1
        ext i
        simp [pow_succ, Nat.mul_comm]
      calc
        (TrapSum q (j + 1)).natAbs ≤
            q.natAbs * (TrapSum q j).natAbs + 1 := hstep
        _ ≤ q.natAbs * (∑ i ∈ Finset.range j, q.natAbs ^ i) + 1 := by
            have hmul := Nat.mul_le_mul_left q.natAbs ih
            omega
        _ = ∑ i ∈ Finset.range (j + 1), q.natAbs ^ i := hgeom
    }

/-- The small residue exponents have a maximum strictly below `m`. -/
theorem SmallPowersHaveMax (q c : ℤ) (m : ℕ) [NeZero m]
    (h : ∀ r : ZMod m, ∃ j : ℕ,
      ResidueHits q c m r j ∧ q.natAbs ^ j < m) :
    ∃ A : ℕ, A < m ∧ ∀ (r : ZMod m) (j : ℕ),
      ResidueHits q c m r j → q.natAbs ^ j ≤ A := by
  classical
  let jof : ZMod m → ℕ := fun r => Classical.choose (h r)
  have hj : ∀ r, ResidueHits q c m r (jof r) ∧
      q.natAbs ^ jof r < m := fun r => Classical.choose_spec (h r)
  let A : ℕ := Finset.sup (Finset.univ : Finset (ZMod m))
    (fun r => q.natAbs ^ jof r)
  refine ⟨A, ?_, ?_⟩
  · {
      rw [Finset.sup_lt_iff ⟨(0 : ZMod m), Finset.mem_univ _⟩]
      intro r _
      exact (hj r).2
    }
  · {
      intro r j hhit
      have heq := ResidueHitsUnique q c m r j (jof r) hhit (hj r).1
      subst heq
      exact Finset.le_sup (f := fun r => q.natAbs ^ jof r) (Finset.mem_univ r)
    }

/-- Exact division preserves the absolute value. -/
theorem AbsDivCancel (d a : ℤ) (hd : d ≠ 0) (h : d ∣ a) :
    d.natAbs * (a / d).natAbs = a.natAbs := by
  obtain ⟨k, hk⟩ := h
  have hk' : a / d = k := by
    rw [hk]
    exact Int.mul_ediv_cancel_left k hd
  rw [hk', hk, Int.natAbs_mul]

/-- A small exponent at every class gives a uniform return bound. -/
theorem UniformReturnBound (p : Parameters)
    (hsmall : ∀ n : ℤ, ∃ j : ℕ,
      IsFirstHit p n j ∧ p.Q.natAbs ^ j < p.D.natAbs) :
    ∃ A B : ℕ, A < p.D.natAbs ∧ ∀ n : ℤ, ∃ j : ℕ,
      IsFirstHit p n j ∧
        p.D.natAbs * ((AffineState p.Q p.C j n) / p.D).natAbs ≤
          A * n.natAbs + B := by
  have hres := (IntegerSlopeIff p).1 hsmall
  haveI : NeZero p.D.natAbs := ⟨by
    have h2 : 2 ≤ p.D.natAbs := p.DAdmissible
    omega⟩
  obtain ⟨A, hA, hmax⟩ := SmallPowersHaveMax p.Q p.C p.D.natAbs hres
  classical
  let jof : ZMod p.D.natAbs → ℕ := fun r => Classical.choose (hres r)
  have hj : ∀ r, ResidueHits p.Q p.C p.D.natAbs r (jof r) ∧
      p.Q.natAbs ^ jof r < p.D.natAbs := fun r => Classical.choose_spec (hres r)
  let B : ℕ := Finset.sup (Finset.univ : Finset (ZMod p.D.natAbs))
    (fun r => p.C.natAbs * (∑ i ∈ Finset.range (jof r), p.Q.natAbs ^ i))
  refine ⟨A, B, hA, ?_⟩
  intro n
  let r : ZMod p.D.natAbs := n
  refine ⟨jof r, ResidueLeastIsFirstHit p n (jof r) (hj r).1, ?_⟩
  have hdvd : p.D ∣ AffineState p.Q p.C (jof r) n :=
    (ResidueLeastIsFirstHit p n (jof r) (hj r).1).1
  have hcancel := AbsDivCancel p.D (AffineState p.Q p.C (jof r) n)
    (by have h2 : 2 ≤ p.D.natAbs := p.DAdmissible; omega) hdvd
  have hsplit :
      (AffineState p.Q p.C (jof r) n).natAbs ≤
        p.Q.natAbs ^ jof r * n.natAbs +
          p.C.natAbs * (TrapSum p.Q (jof r)).natAbs := by
    unfold AffineState
    calc
      (p.Q ^ jof r * n + p.C * TrapSum p.Q (jof r)).natAbs ≤
          (p.Q ^ jof r * n).natAbs +
            (p.C * TrapSum p.Q (jof r)).natAbs :=
        Int.natAbs_add_le _ _
      _ = p.Q.natAbs ^ jof r * n.natAbs +
            p.C.natAbs * (TrapSum p.Q (jof r)).natAbs := by
          rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]
  have htrap : (TrapSum p.Q (jof r)).natAbs ≤
      ∑ i ∈ Finset.range (jof r), p.Q.natAbs ^ i := TrapSumAbsLe p.Q (jof r)
  have hB : p.C.natAbs * (∑ i ∈ Finset.range (jof r), p.Q.natAbs ^ i) ≤ B :=
    Finset.le_sup (f := fun r =>
      p.C.natAbs * (∑ i ∈ Finset.range (jof r), p.Q.natAbs ^ i))
      (Finset.mem_univ r)
  have hpow : p.Q.natAbs ^ jof r ≤ A := hmax r (jof r) (hj r).1
  calc
    p.D.natAbs * ((AffineState p.Q p.C (jof r) n) / p.D).natAbs =
        (AffineState p.Q p.C (jof r) n).natAbs := by rw [hcancel]
    _ ≤ p.Q.natAbs ^ jof r * n.natAbs +
          p.C.natAbs * (TrapSum p.Q (jof r)).natAbs := hsplit
    _ ≤ A * n.natAbs + B := by
        have hmul := Nat.mul_le_mul_right n.natAbs hpow
        have hoff := Nat.mul_le_mul_left p.C.natAbs htrap
        omega

/-- The least first-hit time of a seed. -/
noncomputable def FirstHitTime (p : Parameters)
    (hhit : ∀ n : ℤ, ∃ j : ℕ, IsFirstHit p n j) (n : ℤ) : ℕ :=
  Nat.find (hhit n)

/-- The exact quotient at the least first hit. -/
noncomputable def FirstReturn (p : Parameters)
    (hhit : ∀ n : ℤ, ∃ j : ℕ, IsFirstHit p n j) (n : ℤ) : ℤ :=
  AffineState p.Q p.C (FirstHitTime p hhit n) n / p.D

/-- The return of a small-exponent family is eventually periodic. -/
theorem FirstReturnEventuallyPeriodic (p : Parameters)
    (hsmall : ∀ n : ℤ, ∃ j : ℕ,
      IsFirstHit p n j ∧ p.Q.natAbs ^ j < p.D.natAbs) :
    ∃ A B : ℕ, A < p.D.natAbs ∧ ∀ n : ℤ,
      ∃ t period : ℕ, 0 < period ∧
        period ≤ 2 * CoreRadius A B p.D.natAbs + 1 ∧ ∀ k : ℕ,
        Iterate (FirstReturn p (fun x => (hsmall x).imp fun j h => h.1))
            (t + k) n =
          Iterate (FirstReturn p (fun x => (hsmall x).imp fun j h => h.1))
            (t + k + period) n := by
  let hhit : ∀ n : ℤ, ∃ j : ℕ, IsFirstHit p n j :=
    fun n => (hsmall n).imp fun j h => h.1
  obtain ⟨A, B, hA, hbound⟩ := UniformReturnBound p hsmall
  let H := FirstReturn p hhit
  refine ⟨A, B, hA, ?_⟩
  have hcore : ∀ k : ℤ,
      p.D.natAbs * (H k).natAbs ≤ A * k.natAbs + B := by
    intro k
    obtain ⟨j, hj, hineq⟩ := hbound k
    have hfind : IsFirstHit p k (FirstHitTime p hhit k) :=
      Nat.find_spec (hhit k)
    have heq :=
      FirstHitUnique p k j (FirstHitTime p hhit k) hj hfind
    simpa [H, FirstReturn, FirstHitTime, heq] using hineq
  intro n
  obtain ⟨t0, ht0⟩ := CoreEntry A B p.D.natAbs H hA hcore n
  obtain ⟨i, j, hij, hj, heq⟩ :=
    CorePigeon A B p.D.natAbs H hA hcore (Iterate H t0 n) ht0
  refine ⟨t0 + i, j - i, Nat.sub_pos_of_lt hij, ?_, ?_⟩
  · {
      exact le_trans (Nat.sub_le j i) hj
    }
  · {
      intro k
      have hshift : Iterate H (i + k) (Iterate H t0 n) =
          Iterate H (j + k) (Iterate H t0 n) :=
        CoreRepeatPropagates H (Iterate H t0 n) i j heq k
      have hleft : Iterate H (t0 + i + k) n =
          Iterate H (i + k) (Iterate H t0 n) := by
        rw [show t0 + i + k = t0 + (i + k) by omega, IterateAdd]
      have hright : Iterate H (j + k) (Iterate H t0 n) =
          Iterate H (t0 + (j + k)) n := by
        rw [← IterateAdd]
      have hidx : t0 + (j + k) = t0 + i + k + (j - i) := by omega
      rw [hleft, hshift, hright, hidx]
    }

/-- Descent reaches the radius in at most `|n|` returns. -/
theorem CoreEntryTime (A B m : ℕ) (H : ℤ → ℤ) (hA : A < m)
    (hbound : ∀ k : ℤ, m * (H k).natAbs ≤ A * k.natAbs + B) (n : ℤ) :
    ∃ t : ℕ, t ≤ n.natAbs ∧
      (Iterate H t n).natAbs ≤ CoreRadius A B m := by
  suffices ∀ k n, n.natAbs = k → ∃ t, t ≤ k ∧
      (Iterate H t n).natAbs ≤ CoreRadius A B m by
    exact this n.natAbs n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    {
      intro n hk
      by_cases hcore : n.natAbs ≤ CoreRadius A B m
      · {
          exact ⟨0, Nat.zero_le _, by simpa [Iterate, hk] using hcore⟩
        }
      · {
          have hn : CoreRadius A B m + 1 ≤ n.natAbs := by omega
          have hlt : (H n).natAbs < n.natAbs :=
            CoreMapDescent A B m H n hA (hbound n) hn
          have hkey : (H n).natAbs < k := by
            rw [← hk]
            exact hlt
          obtain ⟨t, ht, henter⟩ :=
            ih (H n).natAbs hkey (H n) rfl
          refine ⟨t + 1, ?_, ?_⟩
          · {
              have hstep : t + 1 ≤ (H n).natAbs + 1 :=
                Nat.add_le_add_right ht 1
              have hdrop : (H n).natAbs + 1 ≤ n.natAbs := by
                rw [hk]
                omega
              exact le_trans hstep hdrop
            }
          · {
              simpa [Iterate, Nat.add_comm] using henter
            }
        }
    }

/-- The return enters its radius within `|n|` steps. -/
theorem FirstReturnEntryTime (p : Parameters)
    (hsmall : ∀ n : ℤ, ∃ j : ℕ,
      IsFirstHit p n j ∧ p.Q.natAbs ^ j < p.D.natAbs) :
    ∃ A B : ℕ, A < p.D.natAbs ∧ ∀ n : ℤ, ∃ t : ℕ, t ≤ n.natAbs ∧
      (Iterate (FirstReturn p (fun x => (hsmall x).imp fun j h => h.1)) t n)
          .natAbs ≤
        CoreRadius A B p.D.natAbs := by
  let hhit : ∀ n : ℤ, ∃ j : ℕ, IsFirstHit p n j :=
    fun n => (hsmall n).imp fun j h => h.1
  obtain ⟨A, B, hA, hbound⟩ := UniformReturnBound p hsmall
  let H := FirstReturn p hhit
  refine ⟨A, B, hA, ?_⟩
  have hcore : ∀ k : ℤ,
      p.D.natAbs * (H k).natAbs ≤ A * k.natAbs + B := by
    intro k
    obtain ⟨j, hj, hineq⟩ := hbound k
    have hfind : IsFirstHit p k (FirstHitTime p hhit k) :=
      Nat.find_spec (hhit k)
    have heq :=
      FirstHitUnique p k j (FirstHitTime p hhit k) hj hfind
    simpa [H, FirstReturn, FirstHitTime, heq] using hineq
  intro n
  simpa [H, hhit] using CoreEntryTime A B p.D.natAbs H hA hcore n

/-- Entry and a bounded period start by time `|n| + 2N`. -/
theorem FirstReturnCycleTime (p : Parameters)
    (hsmall : ∀ n : ℤ, ∃ j : ℕ,
      IsFirstHit p n j ∧ p.Q.natAbs ^ j < p.D.natAbs) :
    ∃ A B : ℕ, A < p.D.natAbs ∧ ∀ n : ℤ, ∃ t period : ℕ,
      t ≤ n.natAbs + 2 * CoreRadius A B p.D.natAbs ∧
        0 < period ∧ period ≤ 2 * CoreRadius A B p.D.natAbs + 1 ∧
        ∀ k : ℕ,
          Iterate (FirstReturn p (fun x => (hsmall x).imp fun j h => h.1))
              (t + k) n =
            Iterate (FirstReturn p (fun x => (hsmall x).imp fun j h => h.1))
              (t + k + period) n := by
  let hhit : ∀ n : ℤ, ∃ j : ℕ, IsFirstHit p n j :=
    fun n => (hsmall n).imp fun j h => h.1
  obtain ⟨A, B, hA, hbound⟩ := UniformReturnBound p hsmall
  let H := FirstReturn p hhit
  refine ⟨A, B, hA, ?_⟩
  have hcore : ∀ k : ℤ,
      p.D.natAbs * (H k).natAbs ≤ A * k.natAbs + B := by
    intro k
    obtain ⟨j, hj, hineq⟩ := hbound k
    have hfind : IsFirstHit p k (FirstHitTime p hhit k) :=
      Nat.find_spec (hhit k)
    have heq :=
      FirstHitUnique p k j (FirstHitTime p hhit k) hj hfind
    simpa [H, FirstReturn, FirstHitTime, heq] using hineq
  intro n
  obtain ⟨t0, ht0, henter⟩ :=
    CoreEntryTime A B p.D.natAbs H hA hcore n
  obtain ⟨i, j, hij, hj, heq⟩ :=
    CorePigeon A B p.D.natAbs H hA hcore (Iterate H t0 n) henter
  refine ⟨t0 + i, j - i, ?_, Nat.sub_pos_of_lt hij, ?_, ?_⟩
  · {
      have hi : i ≤ 2 * CoreRadius A B p.D.natAbs := by omega
      omega
    }
  · {
      exact le_trans (Nat.sub_le j i) hj
    }
  · {
      intro k
      have hshift : Iterate H (i + k) (Iterate H t0 n) =
          Iterate H (j + k) (Iterate H t0 n) :=
        CoreRepeatPropagates H (Iterate H t0 n) i j heq k
      have hleft : Iterate H (t0 + i + k) n =
          Iterate H (i + k) (Iterate H t0 n) := by
        rw [show t0 + i + k = t0 + (i + k) by omega, IterateAdd]
      have hright : Iterate H (j + k) (Iterate H t0 n) =
          Iterate H (t0 + (j + k)) n := by
        rw [← IterateAdd]
      have hidx : t0 + (j + k) = t0 + i + k + (j - i) := by omega
      rw [hleft, hshift, hright, hidx]
    }

/-- `(2,1,3)` has no total return with a small exponent. -/
theorem ClassicalNotSmallExponent (p : Parameters)
    (hQ : p.Q = 2) (hC : p.C = 1) (hD : p.D = 3) :
    ¬ ∀ n : ℤ, ∃ j : ℕ,
      IsFirstHit p n j ∧ p.Q.natAbs ^ j < p.D.natAbs := by
  intro h
  have hm : p.D.natAbs = 3 := by
    rw [hD]
    decide
  have hres := (IntegerSlopeIff p).1 h
  rw [hm] at hres
  obtain ⟨j, hj, _⟩ := hres (2 : ZMod 3)
  have hwalk : ∀ k : ℕ,
      (ResidueStep p.Q p.C 3)^[k] (2 : ZMod 3) = 2 := by
    intro k
    induction k with
    | zero => {
        simp
      }
    | succ k ih => {
        rw [Function.iterate_succ_apply', ih]
        unfold ResidueStep
        rw [hQ, hC]
        decide
      }
  have hzero : (ResidueStep p.Q p.C 3)^[j] (2 : ZMod 3) = 0 := hj.1
  rw [hwalk j] at hzero
  exact absurd hzero (by decide)

/-- A unit multiplier with coprime offset has a small exponent at every seed. -/
theorem UnitCoprimeIsSmall (p : Parameters) (hQ : p.Q = 1)
    (hg : Nat.gcd p.C.natAbs p.D.natAbs = 1) (hm : 2 ≤ p.D.natAbs) :
    ∀ n : ℤ, ∃ j : ℕ,
      IsFirstHit p n j ∧ p.Q.natAbs ^ j < p.D.natAbs := by
  intro n
  obtain ⟨j, hj⟩ := (UnitEverySeedIffCoprime p hQ).2 hg n
  refine ⟨j, hj, ?_⟩
  have hq : p.Q.natAbs = 1 := by
    rw [hQ]
    decide
  rw [hq, Nat.one_pow]
  omega

/-- With multiplier `1` and offset `1`, the affine state is the seed plus the time. -/
/-- A unit multiplier shifts the seed by `c` at every step. -/
theorem UnitOffsetState (c n : ℤ) (j : ℕ) :
    AffineState 1 c j n = n + c * j := by
  simp [AffineState, TrapSumOne, one_pow]
  ring

/-- The unit return divides the seed shifted by `c` times the hit time. -/
theorem UnitOffsetQuotient (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    FirstReturn p hhit n =
      (n + p.C * (FirstHitTime p hhit n : ℤ)) / p.D := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  have hstate : AffineState p.Q p.C (FirstHitTime p hhit n) n =
      n + p.C * (FirstHitTime p hhit n : ℤ) := by
    rw [hQ]
    exact UnitOffsetState p.C n (FirstHitTime p hhit n)
  simp [FirstReturn, hstate]

/-- The first unit hit is at most `|d|`. -/
theorem UnitOffsetTimeBound (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    FirstHitTime p (fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1) n ≤
      p.D.natAbs := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  obtain ⟨j, hj, hfirst⟩ := UnitCoprimeHits p hQ hcop n
  exact Nat.find_le (p := fun t => IsFirstHit p n t) hfirst

/-- Multiplying a unit return by `|d|` recovers the shifted seed. -/
theorem UnitOffsetSize (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    let r := FirstHitTime p hhit n
    p.D.natAbs * (FirstReturn p hhit n).natAbs =
        (n + p.C * (r : ℤ)).natAbs ∧
      p.D.natAbs * (FirstReturn p hhit n).natAbs ≤
        n.natAbs + p.C.natAbs * p.D.natAbs := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let r := FirstHitTime p hhit n
  have hquot := UnitOffsetQuotient p hQ hcop n
  have hfirst := Nat.find_spec (hhit n)
  have hstate : AffineState p.Q p.C r n = n + p.C * (r : ℤ) := by
    rw [hQ]
    exact UnitOffsetState p.C n r
  have hdiv : p.D ∣ n + p.C * (r : ℤ) := by
    rw [← hstate]
    exact hfirst.1
  have hd : p.D ≠ 0 := by
    have : 2 ≤ p.D.natAbs := p.DAdmissible
    omega
  have hprod := AbsDivCancel p.D (n + p.C * (r : ℤ)) hd hdiv
  refine ⟨?_, ?_⟩
  · {
      simpa [hhit, r, hquot] using hprod
    }
  · {
      have hle : (n + p.C * (r : ℤ)).natAbs ≤
          n.natAbs + (p.C * (r : ℤ)).natAbs :=
        Int.natAbs_add_le _ _
      have hmul : (p.C * (r : ℤ)).natAbs = p.C.natAbs * r := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have htime := UnitOffsetTimeBound p hQ hcop n
      have : p.C.natAbs * r ≤ p.C.natAbs * p.D.natAbs :=
        Nat.mul_le_mul_left _ htime
      omega
    }

/-- A unit-coprime return enters the explicit radius within `|n|` steps. -/
theorem UnitOffsetExplicitEntry (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    let B := p.C.natAbs * p.D.natAbs
    ∃ t : ℕ, t ≤ n.natAbs ∧
      (Iterate (FirstReturn p hhit) t n).natAbs ≤
        CoreRadius 1 B p.D.natAbs := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let B := p.C.natAbs * p.D.natAbs
  have hA : 1 < p.D.natAbs := by
    have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
    omega
  have hbound : ∀ k : ℤ,
      p.D.natAbs * (H k).natAbs ≤ 1 * k.natAbs + B := by
    intro k
    have hsize := (UnitOffsetSize p hQ hcop k).2
    simpa [H, hhit, B, Nat.one_mul] using hsize
  simpa [H, hhit, B] using
    CoreEntryTime 1 B p.D.natAbs H hA hbound n

/-- The explicit unit radius starts a period by time `|n|+2N`. -/
theorem UnitOffsetExplicitCycle (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    let N := CoreRadius 1 (p.C.natAbs * p.D.natAbs) p.D.natAbs
    ∃ t period : ℕ, t ≤ n.natAbs + 2 * N ∧ 0 < period ∧ period ≤ 2 * N + 1 ∧
      ∀ k : ℕ,
        Iterate (FirstReturn p hhit) (t + k) n =
          Iterate (FirstReturn p hhit) (t + k + period) n := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let B := p.C.natAbs * p.D.natAbs
  let N := CoreRadius 1 B p.D.natAbs
  have hA : 1 < p.D.natAbs := by
    have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
    omega
  have hbound : ∀ k : ℤ,
      p.D.natAbs * (H k).natAbs ≤ 1 * k.natAbs + B := by
    intro k
    have hsize := (UnitOffsetSize p hQ hcop k).2
    simpa [H, hhit, B, Nat.one_mul] using hsize
  obtain ⟨t0, ht0, henter⟩ :=
    CoreEntryTime 1 B p.D.natAbs H hA hbound n
  obtain ⟨i, j, hij, hj, heq⟩ :=
    CorePigeon 1 B p.D.natAbs H hA hbound (Iterate H t0 n) henter
  refine ⟨t0 + i, j - i, ?_, Nat.sub_pos_of_lt hij, ?_, ?_⟩
  · {
      have hi : i ≤ 2 * N := by omega
      omega
    }
  · {
      exact le_trans (Nat.sub_le j i) hj
    }
  · {
      intro k
      have hshift : Iterate H (i + k) (Iterate H t0 n) =
          Iterate H (j + k) (Iterate H t0 n) :=
        CoreRepeatPropagates H (Iterate H t0 n) i j heq k
      have hleft : Iterate H (t0 + i + k) n =
          Iterate H (i + k) (Iterate H t0 n) := by
        rw [show t0 + i + k = t0 + (i + k) by omega, IterateAdd]
      have hright : Iterate H (j + k) (Iterate H t0 n) =
          Iterate H (t0 + (j + k)) n := by
        rw [← IterateAdd]
      have hidx : t0 + (j + k) = t0 + i + k + (j - i) := by omega
      rw [hleft, hshift, hright, hidx]
    }

/-- The first unit hit is strictly before `|d|`. -/
theorem UnitOffsetTimeStrict (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    FirstHitTime p (fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1) n ≤
      p.D.natAbs - 1 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let r := FirstHitTime p hhit n
  have hle := UnitOffsetTimeBound p hQ hcop n
  by_contra hgt
  have heq : r = p.D.natAbs := by omega
  have hfirst := Nat.find_spec (hhit n)
  have hstate : AffineState p.Q p.C r n = n + p.C * (r : ℤ) := by
    rw [hQ]
    exact UnitOffsetState p.C n r
  have hdiv : p.D ∣ n + p.C * (r : ℤ) := by
    rw [← hstate]
    exact hfirst.1
  have hm : (p.D.natAbs : ℤ) = p.D.sign * p.D := by
    have hsign := (Int.sign_mul_natAbs p.D).symm
    have hsq : p.D.sign * p.D.sign = 1 := by
      rcases Int.sign_trichotomy p.D with h0 | hp | hn
      · {
          have : 2 ≤ p.D.natAbs := p.DAdmissible
          omega
        }
      · {
          rw [Int.sign_eq_one_of_pos hp]
          decide
        }
      · {
          rw [Int.sign_eq_neg_one_of_neg hn]
          decide
        }
    calc
      (p.D.natAbs : ℤ) = (p.D.sign * p.D.sign) * p.D.natAbs := by
        rw [hsq]
        ring
      _ = p.D.sign * (p.D.sign * p.D.natAbs) := by ring
      _ = p.D.sign * p.D := by rw [← hsign]
  have hdvdm : p.D ∣ p.C * (p.D.natAbs : ℤ) := by
    refine ⟨p.C * p.D.sign, ?_⟩
    rw [hm]
    ring
  have hseed : p.D ∣ n := by
    have hshift : p.D ∣ p.C * (r : ℤ) := by
      rw [heq]
      exact hdvdm
    exact Int.dvd_sub_of_dvd_add hdiv hshift
  have hzero : IsFirstHit p n 0 := (FirstHitZeroIff p n).2 hseed
  have hfind : r ≤ 0 :=
    Nat.find_le (p := fun t => IsFirstHit p n t) hzero
  have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
  omega

/-- The sharp unit bound uses the hit time `|d|-1`. -/
theorem UnitOffsetSharpEntry (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t : ℕ, t ≤ n.natAbs ∧
      (Iterate (FirstReturn p hhit) t n).natAbs ≤ p.C.natAbs := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let B := p.C.natAbs * (p.D.natAbs - 1)
  have hA : 1 < p.D.natAbs := by
    have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
    omega
  have hbound : ∀ k : ℤ,
      p.D.natAbs * (H k).natAbs ≤ 1 * k.natAbs + B := by
    intro k
    have hsize := (UnitOffsetSize p hQ hcop k).1
    have htime := UnitOffsetTimeStrict p hQ hcop k
    have hle : (k + p.C * (FirstHitTime p hhit k : ℤ)).natAbs ≤
        k.natAbs + p.C.natAbs * (p.D.natAbs - 1) := by
      have hadd := Int.natAbs_add_le k (p.C * (FirstHitTime p hhit k : ℤ))
      have hmul : (p.C * (FirstHitTime p hhit k : ℤ)).natAbs =
          p.C.natAbs * FirstHitTime p hhit k := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have hmulle : p.C.natAbs * FirstHitTime p hhit k ≤
          p.C.natAbs * (p.D.natAbs - 1) :=
        Nat.mul_le_mul_left _ htime
      omega
    simpa [H, hhit, B, Nat.one_mul, hsize] using hle
  have henter := CoreEntryTime 1 B p.D.natAbs H hA hbound n
  have hrad : CoreRadius 1 B p.D.natAbs = p.C.natAbs := by
    unfold CoreRadius
    have hden : p.D.natAbs - 1 ≠ 0 := by omega
    rw [show B = p.C.natAbs * (p.D.natAbs - 1) from rfl]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hden)
  simpa [H, hhit, hrad] using henter

/-- The sharp unit shell starts a period by time `|n|+2|c|`. -/
theorem UnitOffsetSharpCycle (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t period : ℕ, t ≤ n.natAbs + 2 * p.C.natAbs ∧ 0 < period ∧
      period ≤ 2 * p.C.natAbs + 1 ∧
      ∀ k : ℕ,
        Iterate (FirstReturn p hhit) (t + k) n =
          Iterate (FirstReturn p hhit) (t + k + period) n := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let B := p.C.natAbs * (p.D.natAbs - 1)
  have hA : 1 < p.D.natAbs := by
    have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
    omega
  have hbound : ∀ k : ℤ,
      p.D.natAbs * (H k).natAbs ≤ 1 * k.natAbs + B := by
    intro k
    have hsize := (UnitOffsetSize p hQ hcop k).1
    have htime := UnitOffsetTimeStrict p hQ hcop k
    have hle : (k + p.C * (FirstHitTime p hhit k : ℤ)).natAbs ≤
        k.natAbs + B := by
      have hadd := Int.natAbs_add_le k (p.C * (FirstHitTime p hhit k : ℤ))
      have hmul : (p.C * (FirstHitTime p hhit k : ℤ)).natAbs =
          p.C.natAbs * FirstHitTime p hhit k := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have hmulle : p.C.natAbs * FirstHitTime p hhit k ≤ B :=
        Nat.mul_le_mul_left _ htime
      omega
    simpa [H, hhit, Nat.one_mul, hsize] using hle
  obtain ⟨t0, ht0, henter⟩ :=
    CoreEntryTime 1 B p.D.natAbs H hA hbound n
  have hrad : CoreRadius 1 B p.D.natAbs = p.C.natAbs := by
    unfold CoreRadius
    have hden : p.D.natAbs - 1 ≠ 0 := by omega
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hden)
  rw [hrad] at henter ht0
  obtain ⟨i, j, hij, hj, heq⟩ :=
    CorePigeon 1 B p.D.natAbs H hA hbound (Iterate H t0 n) (by
      simpa [hrad] using henter)
  have hjN : j ≤ 2 * p.C.natAbs + 1 := by
    simpa [hrad] using hj
  refine ⟨t0 + i, j - i, ?_, Nat.sub_pos_of_lt hij, ?_, ?_⟩
  · {
      have hi : i ≤ 2 * p.C.natAbs := by omega
      omega
    }
  · {
      exact le_trans (Nat.sub_le j i) hjN
    }
  · {
      intro k
      have hshift : Iterate H (i + k) (Iterate H t0 n) =
          Iterate H (j + k) (Iterate H t0 n) :=
        CoreRepeatPropagates H (Iterate H t0 n) i j heq k
      have hleft : Iterate H (t0 + i + k) n =
          Iterate H (i + k) (Iterate H t0 n) := by
        rw [show t0 + i + k = t0 + (i + k) by omega, IterateAdd]
      have hright : Iterate H (j + k) (Iterate H t0 n) =
          Iterate H (t0 + (j + k)) n := by
        rw [← IterateAdd]
      have hidx : t0 + (j + k) = t0 + i + k + (j - i) := by omega
      rw [hleft, hshift, hright, hidx]
    }

/-- A positive divisor fixes the seed `c`. -/
theorem UnitOffsetFixesOffset (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (hp : 0 < p.D) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    FirstReturn p hhit p.C = p.C := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have htime : FirstHitTime p hhit p.C = p.D.natAbs - 1 := by
    have hstrict := UnitOffsetTimeStrict p hQ hcop p.C
    have hstate : AffineState p.Q p.C (p.D.natAbs - 1) p.C =
        p.C * (p.D.natAbs : ℤ) := by
      rw [hQ]
      rw [UnitOffsetState p.C p.C (p.D.natAbs - 1)]
      have hsum : (p.C : ℤ) + p.C * ((p.D.natAbs - 1 : ℕ) : ℤ) =
          p.C * (p.D.natAbs : ℤ) := by
        have hcast : ((p.D.natAbs - 1 : ℕ) : ℤ) = (p.D.natAbs : ℤ) - 1 := by
          omega
        rw [hcast]
        ring
      exact hsum
    have hdiv : p.D ∣ AffineState p.Q p.C (p.D.natAbs - 1) p.C := by
      rw [hstate]
      refine ⟨p.C * p.D.sign, ?_⟩
      have hm : (p.D.natAbs : ℤ) = p.D.sign * p.D := by
        have hsign := (Int.sign_mul_natAbs p.D).symm
        have hsq : p.D.sign * p.D.sign = 1 := by
          rw [Int.sign_eq_one_of_pos hp]
          decide
        calc
          (p.D.natAbs : ℤ) = (p.D.sign * p.D.sign) * p.D.natAbs := by
            rw [hsq]
            ring
          _ = p.D.sign * (p.D.sign * p.D.natAbs) := by ring
          _ = p.D.sign * p.D := by rw [← hsign]
      rw [hm]
      ring
    have hhitlate : IsFirstHit p p.C (p.D.natAbs - 1) := by
      refine ⟨hdiv, ?_⟩
      intro i hi hdi
      have hform := UnitOffsetState p.C p.C i
      rw [hQ] at hform
      have hsmall : (1 + (i : ℤ)).natAbs < p.D.natAbs := by omega
      have hdvi : p.D ∣ p.C * (1 + (i : ℤ)) := by
        rw [hform] at hdi
        have : p.C + p.C * (i : ℤ) = p.C * (1 + (i : ℤ)) := by ring
        rw [this] at hdi
        exact hdi
      have hunit : Nat.Coprime p.C.natAbs p.D.natAbs := hcop
      have hdivnat : p.D.natAbs ∣ (1 + i) := by
        have := Int.natAbs_dvd_natAbs.mpr hdvi
        rw [Int.natAbs_mul, Int.natAbs_natCast] at this
        exact Nat.Coprime.dvd_of_dvd_mul_left hunit this
      have hposi : 0 < 1 + i := by omega
      have hlt : 1 + i < p.D.natAbs := by
        have : (1 + (i : ℤ)).natAbs = 1 + i := by omega
        omega
      exact Nat.not_dvd_of_pos_of_lt hposi hlt hdivnat
    have hle : p.D.natAbs - 1 ≤ FirstHitTime p hhit p.C :=
      Nat.find_le (p := fun t => IsFirstHit p p.C t) hhitlate
    omega
  have hquot := UnitOffsetQuotient p hQ hcop p.C
  rw [H, hquot, htime]
  have hnum : p.C + p.C * ((p.D.natAbs - 1 : ℕ) : ℤ) =
      p.C * (p.D.natAbs : ℤ) := by
    have hcast : ((p.D.natAbs - 1 : ℕ) : ℤ) = (p.D.natAbs : ℤ) - 1 := by omega
    rw [hcast]
    ring
  rw [hnum]
  have hd : p.D = p.D.natAbs := Int.eq_natCast_of_nonneg (le_of_lt hp)
  rw [hd]
  exact Int.mul_ediv_cancel _ (by omega)

/-- A negative divisor sends `c` to `-c` and `-c` to `0`. -/
theorem UnitOffsetNegToZero (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (hn : p.D < 0) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    FirstReturn p hhit p.C = -p.C ∧ FirstReturn p hhit (-p.C) = 0 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hnegc : H (-p.C) = 0 := by
    have htime : FirstHitTime p hhit (-p.C) = 1 := by
      have hzero_state : AffineState p.Q p.C 1 (-p.C) = 0 := by
        rw [hQ, UnitOffsetState p.C (-p.C) 1]
        ring
      have hdiv : IsFirstHit p (-p.C) 1 := by
        refine ⟨by rw [hzero_state]; exact dvd_zero _, ?_⟩
        intro i hi hdi
        have : i = 0 := by omega
        rw [this] at hdi
        have hform := UnitOffsetState p.C (-p.C) 0
        rw [hQ] at hform
        rw [hform] at hdi
        simp at hdi
        have hdvc : p.D.natAbs ∣ p.C.natAbs :=
          Int.natAbs_dvd_natAbs.mpr (by simpa using hdi)
        have hone : p.D.natAbs = 1 :=
          Nat.Coprime.eq_one_of_dvd hcop hdvc
        have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
        omega
      have hle : 1 ≤ FirstHitTime p hhit (-p.C) :=
        Nat.find_le (p := fun t => IsFirstHit p (-p.C) t) hdiv
      have hstrict := UnitOffsetTimeStrict p hQ hcop (-p.C)
      -- Time `0` is not a hit, and the strict bound plus the witness `1` pins it.
      have hnot : ¬ IsFirstHit p (-p.C) 0 := by
        intro h0
        have := (FirstHitZeroIff p (-p.C)).1 h0
        have hdvc : p.D.natAbs ∣ p.C.natAbs :=
          Int.natAbs_dvd_natAbs.mpr (by simpa using this)
        have hone : p.D.natAbs = 1 :=
          Nat.Coprime.eq_one_of_dvd hcop hdvc
        have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
        omega
      have hpos : 0 < FirstHitTime p hhit (-p.C) := by
        by_contra hz
        have : FirstHitTime p hhit (-p.C) = 0 := by omega
        exact hnot (by simpa [this] using Nat.find_spec (hhit (-p.C)))
      omega
    rw [H, UnitOffsetQuotient p hQ hcop (-p.C), htime]
    ring
  have hc : H p.C = -p.C := by
    have htime : FirstHitTime p hhit p.C = p.D.natAbs - 1 := by
      have hstate : AffineState p.Q p.C (p.D.natAbs - 1) p.C =
          p.C * (p.D.natAbs : ℤ) := by
        rw [hQ, UnitOffsetState p.C p.C (p.D.natAbs - 1)]
        have hcast : ((p.D.natAbs - 1 : ℕ) : ℤ) =
            (p.D.natAbs : ℤ) - 1 := by omega
        rw [hcast]
        ring
      have hdiv : p.D ∣ AffineState p.Q p.C (p.D.natAbs - 1) p.C := by
        rw [hstate]
        refine ⟨-p.C, ?_⟩
        have hd : p.D = -((p.D.natAbs : ℤ)) := by
          cases p.D with
          | ofNat k => {
              omega
            }
          | negSucc k => {
              rfl
            }
        rw [hd]
        ring
      have hhitlate : IsFirstHit p p.C (p.D.natAbs - 1) := by
        refine ⟨hdiv, ?_⟩
        intro i hi hdi
        have hform := UnitOffsetState p.C p.C i
        rw [hQ] at hform
        have hdvi : p.D ∣ p.C * (1 + (i : ℤ)) := by
          rw [hform] at hdi
          have : p.C + p.C * (i : ℤ) = p.C * (1 + (i : ℤ)) := by ring
          rwa [this] at hdi
        have hdivnat : p.D.natAbs ∣ (1 + i) := by
          have := Int.natAbs_dvd_natAbs.mpr hdvi
          rw [Int.natAbs_mul, Int.natAbs_natCast] at this
          exact Nat.Coprime.dvd_of_dvd_mul_left hcop this
        have hposi : 0 < 1 + i := by omega
        have hlt : 1 + i < p.D.natAbs := by omega
        exact Nat.not_dvd_of_pos_of_lt hposi hlt hdivnat
      have hle : p.D.natAbs - 1 ≤ FirstHitTime p hhit p.C :=
        Nat.find_le (p := fun t => IsFirstHit p p.C t) hhitlate
      have hstrict := UnitOffsetTimeStrict p hQ hcop p.C
      omega
    rw [H, UnitOffsetQuotient p hQ hcop p.C, htime]
    have hnum : p.C + p.C * ((p.D.natAbs - 1 : ℕ) : ℤ) =
        p.C * (p.D.natAbs : ℤ) := by
      have hcast : ((p.D.natAbs - 1 : ℕ) : ℤ) =
          (p.D.natAbs : ℤ) - 1 := by omega
      rw [hcast]
      ring
    have hd : p.D = -((p.D.natAbs : ℤ)) := by
      cases p.D with
      | ofNat k => {
          omega
        }
      | negSucc k => {
          rfl
        }
    rw [hnum, hd]
    have hden : (p.D.natAbs : ℤ) ≠ 0 := by omega
    rw [Int.mul_ediv_cancel _ hden]
    ring
  exact ⟨hc, hnegc⟩

/-- `(1,2,-3)` fixes `-1`, so a negative divisor need not end at `0`. -/
theorem TwoNegThreeFixesNegOne (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 2) (hD : p.D = -3) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ (by rw [hC, hD]; decide)
        (by rw [hD]; decide) x).imp fun j h => h.1
    FirstReturn p hhit (-1) = -1 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ (by rw [hC, hD]; decide)
      (by rw [hD]; decide) x).imp fun j h => h.1
  have htime : FirstHitTime p hhit (-1) = 2 := by
    have hdiv : IsFirstHit p (-1) 2 := by
      refine ⟨?_, ?_⟩
      · {
          rw [hQ, hC, UnitOffsetState 2 (-1) 2]
          decide
        }
      · {
          intro i hi hdi
          have hform := UnitOffsetState 2 (-1) i
          rw [hQ, hC] at hform
          interval_cases i
          · {
              rw [hform] at hdi
              rw [hD] at hdi
              decide
            }
          · {
              rw [hform] at hdi
              rw [hD] at hdi
              decide
            }
        }
    have hle : 2 ≤ FirstHitTime p hhit (-1) :=
      Nat.find_le (p := fun t => IsFirstHit p (-1) t) hdiv
    have hstrict := UnitOffsetTimeStrict p hQ
      (by rw [hC, hD]; decide) (-1)
    rw [hD] at hstrict
    omega
  rw [FirstReturn, UnitOffsetQuotient p hQ (by rw [hC, hD]; decide) (-1),
    htime, hC, hD]
  decide

/-- The only fixed returns of `(1,2,-3)` are `0` and `-1`. -/
theorem TwoNegThreeFixedPoints (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 2) (hD : p.D = -3) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ (by rw [hC, hD]; decide)
        (by rw [hD]; decide) x).imp fun j h => h.1
    FirstReturn p hhit n = n ↔ n = 0 ∨ n = -1 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ (by rw [hC, hD]; decide)
      (by rw [hD]; decide) x).imp fun j h => h.1
  let H := FirstReturn p hhit
  constructor
  · {
      intro hfix
      have hr := UnitOffsetTimeStrict p hQ (by rw [hC, hD]; decide) n
      rw [hD] at hr
      have hquot := UnitOffsetQuotient p hQ (by rw [hC, hD]; decide) n
      rw [hC, hD] at hquot
      have htime := UnitOffsetTime p hQ (by rw [hC, hD]; decide) n
      -- `n = (n+2r)/(-3)` forces `n = -r/2`.
      have hrn : n = -((FirstHitTime p hhit n : ℤ) / 2) := by
        have hH : H n = (n + 2 * (FirstHitTime p hhit n : ℤ)) / -3 := by
          rw [H, hquot, htime]
        rw [hfix] at hH
        have hmul : n * -3 = n + 2 * (FirstHitTime p hhit n : ℤ) := by
          have hdiv : (-3 : ℤ) ∣ n + 2 * (FirstHitTime p hhit n : ℤ) := by
            rw [← hH]
            exact ⟨n, by ring⟩
          have := Int.ediv_mul_cancel hdiv
          -- `(a/(-3))*(-3) = a`, while `H n = n`.
          rw [← hH] at this
          linarith
        linarith
      have hsmall : FirstHitTime p hhit n ≤ 2 := by omega
      interval_cases h : FirstHitTime p hhit n
      · {
          left
          rw [h] at hrn
          simpa using hrn
        }
      · {
          -- Time `1` would force `n = -1/2`.
          exfalso
          rw [h] at hrn
          have : n * 2 = -1 := by linarith
          omega
        }
      · {
          right
          rw [h] at hrn
          have : n * 2 = -2 := by linarith
          linarith
        }
    }
  · {
      intro hn
      rcases hn with hzero | hneg
      · {
          rw [hzero]
          have hquot := UnitOffsetQuotient p hQ (by rw [hC, hD]; decide) 0
          have htime := UnitOffsetTime p hQ (by rw [hC, hD]; decide) 0
          rw [H, hquot, htime, hC]
          simp
        }
      · {
          rw [hneg]
          exact TwoNegThreeFixesNegOne p hQ hC hD
        }
    }

/-- A unit return is fixed exactly when `n(d-1)` equals `c` times the hit. -/
theorem UnitOffsetFixedIff (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    FirstReturn p hhit n = n ↔
      n * (p.D - 1) = p.C * (FirstHitTime p hhit n : ℤ) := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let r := FirstHitTime p hhit n
  have hquot := UnitOffsetQuotient p hQ hcop n
  have htime := UnitOffsetTime p hQ hcop n
  constructor
  · {
      intro hfix
      have hH : H n = (n + p.C * (r : ℤ)) / p.D := by
        rw [H, hquot, htime]
      rw [hfix] at hH
      have hdiv : p.D ∣ n + p.C * (r : ℤ) := by
        rw [← hH]
        exact ⟨n, by ring⟩
      have hback := Int.ediv_mul_cancel hdiv
      rw [← hH] at hback
      linarith
    }
  · {
      intro heq
      have hdiv : p.D ∣ n + p.C * (r : ℤ) := by
        refine ⟨n, ?_⟩
        linarith
      rw [H, hquot, htime, Int.ediv_eq_of_eq_mul_left (by
        have : p.D ≠ 0 := by
          have := p.DAdmissible
          omega) (by linarith)]
    }

/-- A fixed unit return is at most the offset, and strictly smaller if `d<0`. -/
theorem UnitOffsetFixedBound (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hfix : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      FirstReturn p hhit n = n) :
    (0 < p.D → n.natAbs ≤ p.C.natAbs) ∧
      (p.D < 0 → n.natAbs * (p.D.natAbs + 1) ≤
        p.C.natAbs * (p.D.natAbs - 1)) := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  have heq := (UnitOffsetFixedIff p hQ hcop n).1 hfix
  have hr := UnitOffsetTimeStrict p hQ hcop n
  have habs : n.natAbs * (p.D - 1).natAbs =
      p.C.natAbs * FirstHitTime p hhit n := by
    have := congrArg Int.natAbs heq
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast] at this
    exact this
  constructor
  · {
      intro hp
      have hd : (p.D - 1).natAbs = p.D.natAbs - 1 := by omega
      rw [hd] at habs
      have htime : FirstHitTime p hhit n ≤ p.D.natAbs - 1 := by omega
      have hle : p.C.natAbs * FirstHitTime p hhit n ≤
          p.C.natAbs * (p.D.natAbs - 1) :=
        Nat.mul_le_mul_left _ htime
      have hgap : 0 < p.D.natAbs - 1 := by omega
      -- Cancel the positive gap `m-1`.
      have hmul : n.natAbs * (p.D.natAbs - 1) ≤
          p.C.natAbs * (p.D.natAbs - 1) := by
        rwa [habs]
      exact Nat.le_of_mul_le_mul_right hmul hgap
    }
  · {
      intro hn
      have hd : (p.D - 1).natAbs = p.D.natAbs + 1 := by omega
      rw [hd] at habs
      have htime : FirstHitTime p hhit n ≤ p.D.natAbs - 1 := by omega
      calc
        n.natAbs * (p.D.natAbs + 1)
          = p.C.natAbs * FirstHitTime p hhit n := habs
        _ ≤ p.C.natAbs * (p.D.natAbs - 1) :=
          Nat.mul_le_mul_left _ htime
    }

/-- Equality at absolute value `|c|` forces the seed `c` when `d>0`. -/
theorem UnitOffsetFixedTop (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (hp : 0 < p.D)
    (hfix : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      FirstReturn p hhit n = n)
    (htop : n.natAbs = p.C.natAbs) : n = p.C := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  have heq := (UnitOffsetFixedIff p hQ hcop n).1 hfix
  have hr := UnitOffsetTimeStrict p hQ hcop n
  have hprod : n.natAbs * (p.D.natAbs - 1) =
      p.C.natAbs * FirstHitTime p hhit n := by
    have := congrArg Int.natAbs heq
    have hd : (p.D - 1).natAbs = p.D.natAbs - 1 := by omega
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, hd] at this
    exact this
  have htime : FirstHitTime p hhit n = p.D.natAbs - 1 := by
    have hle : FirstHitTime p hhit n ≤ p.D.natAbs - 1 := by omega
    have hgap : 0 < p.D.natAbs - 1 := by omega
    -- The top absolute value uses the whole gap.
    have : p.C.natAbs * FirstHitTime p hhit n =
        p.C.natAbs * (p.D.natAbs - 1) := by
      rw [← hprod, htop]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < p.C.natAbs) this
  -- Then `n*(d-1) = c*(m-1)`, so `n = c`.
  have hcast : ((p.D.natAbs - 1 : ℕ) : ℤ) = p.D - 1 := by omega
  rw [htime, hcast] at heq
  have hgap : p.D - 1 ≠ 0 := by omega
  have : n = p.C := by
    apply Int.eq_of_mul_eq_mul_right hgap
    linarith
  exact this

/-- `(1,2,-3)` sends `1` to the fixed point `-1`. -/
theorem TwoNegThreeSendsOne (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 2) (hD : p.D = -3) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ (by rw [hC, hD]; decide)
        (by rw [hD]; decide) x).imp fun j h => h.1
    FirstReturn p hhit 1 = -1 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ (by rw [hC, hD]; decide)
      (by rw [hD]; decide) x).imp fun j h => h.1
  have htime : FirstHitTime p hhit 1 = 1 := by
    have hdiv : IsFirstHit p 1 1 := by
      refine ⟨?_, ?_⟩
      · {
          rw [hQ, hC, UnitOffsetState 2 1 1]
          decide
        }
      · {
          intro i hi hdi
          have : i = 0 := by omega
          rw [this, hQ, hC, UnitOffsetState 2 1 0, hD] at hdi
          decide
        }
    have hle : 1 ≤ FirstHitTime p hhit 1 :=
      Nat.find_le (p := fun t => IsFirstHit p 1 t) hdiv
    have hstrict := UnitOffsetTimeStrict p hQ
      (by rw [hC, hD]; decide) 1
    rw [hD] at hstrict
    omega
  rw [FirstReturn, UnitOffsetQuotient p hQ (by rw [hC, hD]; decide) 1,
    htime, hC, hD]
  decide

/-- Every `(1,2,-3)` orbit reaches `0` or `-1`. -/
theorem TwoNegThreeTerminal (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 2) (hD : p.D = -3) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ (by rw [hC, hD]; decide)
        (by rw [hD]; decide) x).imp fun j h => h.1
    ∃ t : ℕ, Iterate (FirstReturn p hhit) t n = 0 ∨
      Iterate (FirstReturn p hhit) t n = -1 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ (by rw [hC, hD]; decide)
      (by rw [hD]; decide) x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have henter := UnitOffsetSharpEntry p hQ (by rw [hC, hD]; decide) n
  rw [hC] at henter
  obtain ⟨t0, _, hshell⟩ := henter
  have hsmall : (Iterate H t0 n).natAbs ≤ 2 := hshell
  have htri : Iterate H t0 n = -2 ∨ Iterate H t0 n = -1 ∨
      Iterate H t0 n = 0 ∨ Iterate H t0 n = 1 ∨
      Iterate H t0 n = 2 := by omega
  have hneg := (UnitOffsetNegToZero p hQ (by rw [hC, hD]; decide)
    (by rw [hD]; decide)).2
  have htwo := (UnitOffsetNegToZero p hQ (by rw [hC, hD]; decide)
    (by rw [hD]; decide)).1
  rw [hC] at hneg htwo
  rcases htri with h | h | h | h | h
  · {
      refine ⟨t0 + 2, Or.inl ?_⟩
      rw [show t0 + 2 = t0 + 2 by rfl, IterateAdd, h, Iterate, htwo, Iterate,
        hneg]
    }
  · {
      exact ⟨t0, Or.inr h⟩
    }
  · {
      exact ⟨t0, Or.inl h⟩
    }
  · {
      refine ⟨t0 + 1, Or.inr ?_⟩
      rw [IterateAdd, h, Iterate]
      exact TwoNegThreeSendsOne p hQ hC hD
    }
  · {
      refine ⟨t0 + 2, Or.inl ?_⟩
      rw [IterateAdd, h, Iterate, htwo, Iterate, hneg]
    }

/-- The only periodic points of `(1,2,-3)` are `0` and `-1`. -/
theorem TwoNegThreeOnlyPeriodic (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 2) (hD : p.D = -3)
    (n : ℤ) (k : ℕ) (hk : 0 < k)
    (hper : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ (by rw [hC, hD]; decide)
        (by rw [hD]; decide) x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) k n = n) :
    n = 0 ∨ n = -1 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ (by rw [hC, hD]; decide)
      (by rw [hD]; decide) x).imp fun j h => h.1
  let H := FirstReturn p hhit
  obtain ⟨t, hterm⟩ := TwoNegThreeTerminal p hQ hC hD n
  have hstay0 : ∀ j, Iterate H j 0 = 0 := by
    intro j
    induction j with
    | zero => {
        simp [Iterate]
      }
    | succ j ih => {
        rw [Iterate, ih]
        have hfix := (TwoNegThreeFixedPoints p hQ hC hD 0).2 (Or.inl rfl)
        simpa [H] using hfix
      }
  have hstay1 : ∀ j, Iterate H j (-1) = -1 := by
    intro j
    induction j with
    | zero => {
        simp [Iterate]
      }
    | succ j ih => {
        rw [Iterate, ih]
        have hfix :=
          (TwoNegThreeFixedPoints p hQ hC hD (-1)).2 (Or.inr rfl)
        simpa [H] using hfix
      }
  -- Repeat the period until it passes the terminal time.
  have hrep : Iterate H (k * (t + 1)) n = n := by
    induction (t + 1) with
    | zero => {
        simp [Iterate] at hper
        simpa using hper
      }
    | succ m ih => {
        rw [Nat.mul_succ, IterateAdd, ih]
        simpa [H] using hper
      }
  have hge : t ≤ k * (t + 1) := by
    have : 1 ≤ k := hk
    omega
  have hback : Iterate H (k * (t + 1) - t) (Iterate H t n) = n := by
    have := IterateAdd H t (k * (t + 1) - t) n
    have hidx : t + (k * (t + 1) - t) = k * (t + 1) := by omega
    rw [hidx] at this
    rw [← this, hrep]
  rcases hterm with hzero | hneg
  · {
      left
      rw [hzero, hstay0] at hback
      exact hback.symm
    }
  · {
      right
      rw [hneg, hstay1] at hback
      exact hback.symm
    }

/-- A periodic unit return already lies in the shell of radius `|c|`. -/
theorem UnitOffsetPeriodicInShell (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (n : ℤ) (k : ℕ) (hk : 0 < k)
    (hper : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) k n = n) :
    n.natAbs ≤ p.C.natAbs := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let B := p.C.natAbs * (p.D.natAbs - 1)
  have hA : 1 < p.D.natAbs := by
    have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
    omega
  have hbound : ∀ x : ℤ,
      p.D.natAbs * (H x).natAbs ≤ 1 * x.natAbs + B := by
    intro x
    have hsize := (UnitOffsetSize p hQ hcop x).1
    have htime := UnitOffsetTimeStrict p hQ hcop x
    have hle : (x + p.C * (FirstHitTime p hhit x : ℤ)).natAbs ≤
        x.natAbs + B := by
      have hadd := Int.natAbs_add_le x (p.C * (FirstHitTime p hhit x : ℤ))
      have hmul : (p.C * (FirstHitTime p hhit x : ℤ)).natAbs =
          p.C.natAbs * FirstHitTime p hhit x := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      omega
    simpa [H, hhit, Nat.one_mul, hsize] using hle
  obtain ⟨t, _, henter⟩ := UnitOffsetSharpEntry p hQ hcop n
  have hrad : CoreRadius 1 B p.D.natAbs = p.C.natAbs := by
    unfold CoreRadius
    exact Nat.mul_div_cancel _ (by omega : 0 < p.D.natAbs - 1)
  have hstay := CoreStays 1 B p.D.natAbs H hA hbound (Iterate H t n)
    (by simpa [hrad] using henter)
  -- Repeat the period until it passes the entry time.
  have hrep : Iterate H (k * (t + 1)) n = n := by
    induction (t + 1) with
    | zero => {
        simp [Iterate] at hper
        simpa using hper
      }
    | succ m ih => {
        rw [Nat.mul_succ, IterateAdd, ih]
        simpa [H] using hper
      }
  have hidx : t + (k * (t + 1) - t) = k * (t + 1) := by omega
  have hback : Iterate H (k * (t + 1) - t) (Iterate H t n) = n := by
    have := IterateAdd H t (k * (t + 1) - t) n
    rw [hidx] at this
    rw [← this, hrep]
  have hshell := hstay (k * (t + 1) - t)
  rw [hback, hrad] at hshell
  exact hshell

/-- A periodic unit return has a positive period of length at most `2|c|+1`. -/
theorem UnitOffsetPeriodicShort (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (n : ℤ) (k : ℕ) (hk : 0 < k)
    (hper : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) k n = n) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ period : ℕ, 0 < period ∧ period ≤ 2 * p.C.natAbs + 1 ∧
      Iterate (FirstReturn p hhit) period n = n := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  obtain ⟨t, period, _, hp, hshort, htail⟩ :=
    UnitOffsetSharpCycle p hQ hcop n
  have hshift : Iterate H (t + period) n = Iterate H t n :=
    (htail 0).symm
  -- Pull the tail equality back along the original period.
  have hrep : Iterate H (k * (t + 1)) n = n := by
    induction (t + 1) with
    | zero => {
        simp [Iterate] at hper
        simpa using hper
      }
    | succ m ih => {
        rw [Nat.mul_succ, IterateAdd, ih]
        simpa [H] using hper
      }
  have hidx : t + (k * (t + 1) - t) = k * (t + 1) := by omega
  have hpull : Iterate H (k * (t + 1) - t) (Iterate H t n) = n := by
    have := IterateAdd H t (k * (t + 1) - t) n
    rw [hidx] at this
    rw [← this, hrep]
  have hpullp : Iterate H (k * (t + 1) - t) (Iterate H (t + period) n) =
      Iterate H period n := by
    have := IterateAdd H (t + period) (k * (t + 1) - t) n
    have hidxp : t + period + (k * (t + 1) - t) =
        k * (t + 1) + period := by omega
    rw [hidxp] at this
    have hcomm : Iterate H (k * (t + 1) + period) n =
        Iterate H period (Iterate H (k * (t + 1)) n) := by
      rw [add_comm, IterateAdd]
    rw [← this, hcomm, hrep, Iterate]
    rfl
  refine ⟨period, hp, hshort, ?_⟩
  rw [hshift] at hpullp
  rw [hpull] at hpullp
  exact hpullp.symm

/-- A return time absorbs any multiple of another return time. -/
theorem IterateReturnMod (H : ℤ → ℤ) (n : ℤ) (a b : ℕ)
    (ha : 0 < a) (hret : Iterate H a n = n) (hb : Iterate H b n = n) :
    Iterate H (b % a) n = n := by
  have hquot : b = a * (b / a) + b % a := Nat.div_add_mod b a |>.symm
  have hmul : Iterate H (a * (b / a)) n = n := by
    induction b / a with
    | zero => {
        simp [Iterate]
      }
    | succ q ih => {
        rw [Nat.mul_succ, IterateAdd, ih]
        exact hret
      }
  have := IterateAdd H (a * (b / a)) (b % a) n
  rw [← hquot] at this
  rw [hb, hmul] at this
  exact this.symm

/-- The greatest common divisor of two return times is a return time. -/
theorem IterateReturnGcd (H : ℤ → ℤ) (n : ℤ) (a b : ℕ)
    (ha : Iterate H a n = n) (hb : Iterate H b n = n) :
    Iterate H (Nat.gcd a b) n = n := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    {
      by_cases hzero : a = 0
      · {
          rw [hzero, Nat.gcd_zero_left]
          exact hb
        }
      · {
          have hmod := IterateReturnMod H n a b (Nat.pos_of_ne_zero hzero) ha hb
          have hlt : b % a < a := Nat.mod_lt b (Nat.pos_of_ne_zero hzero)
          have hgcd : Nat.gcd a b = Nat.gcd (b % a) a := Nat.gcd_rec a b
          rw [hgcd]
          exact ih (b % a) hlt hmod ha
        }
    }

/-- Every positive period is a multiple of a period of length at most `2|c|+1`. -/
theorem UnitOffsetPeriodDivides (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (n : ℤ) (k : ℕ) (hk : 0 < k)
    (hper : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) k n = n) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ d : ℕ, 0 < d ∧ d ≤ 2 * p.C.natAbs + 1 ∧ d ∣ k ∧
      Iterate (FirstReturn p hhit) d n = n := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  obtain ⟨period, hp, hshort, hret⟩ :=
    UnitOffsetPeriodicShort p hQ hcop n k hk hper
  refine ⟨Nat.gcd period k, ?_, ?_, Nat.gcd_dvd_right period k, ?_⟩
  · {
      exact Nat.gcd_pos_of_pos_left _ hp
    }
  · {
      exact Nat.le_trans (Nat.gcd_le_left _ hp) hshort
    }
  · {
      exact IterateReturnGcd (FirstReturn p hhit) n period k hret hper
    }

/-- Least positive return of an arbitrary self-map. -/
theorem IterateLeastReturn (H : ℤ → ℤ) (n : ℤ) (k : ℕ)
    (hk : 0 < k) (hret : Iterate H k n = n) :
    ∃ d : ℕ, 0 < d ∧ d ≤ k ∧ Iterate H d n = n ∧
      ∀ t : ℕ, Iterate H t n = n → d ∣ t := by
  suffices ∀ k, 0 < k → Iterate H k n = n →
      ∃ d : ℕ, 0 < d ∧ d ≤ k ∧ Iterate H d n = n ∧
        ∀ t : ℕ, 0 < t → t < d → Iterate H t n ≠ n by
    obtain ⟨d, hd, hle, hret', hmin⟩ := this k hk hret
    refine ⟨d, hd, hle, hret', ?_⟩
    intro t ht
    have hgcd := IterateReturnGcd H n d t hret' ht
    have hpos : 0 < Nat.gcd d t := Nat.gcd_pos_of_pos_left _ hd
    have hle' : Nat.gcd d t ≤ d := Nat.gcd_le_left _ hd
    have hnot : ¬ Nat.gcd d t < d := by
      intro hlt
      exact hmin (Nat.gcd d t) hpos hlt hgcd
    have heq : Nat.gcd d t = d := by omega
    rw [← heq]
    exact Nat.gcd_dvd_right d t
  intro k hk hret
  induction k using Nat.strong_induction_on with
  | h k ih =>
    {
      by_cases hsmall : ∃ t, 0 < t ∧ t < k ∧ Iterate H t n = n
      · {
          obtain ⟨t, ht, hlt, hret'⟩ := hsmall
          obtain ⟨d, hd, hle, hretd, hmin⟩ := ih t hlt ht hret'
          exact ⟨d, hd, Nat.le_trans hle (Nat.le_of_lt hlt), hretd, hmin⟩
        }
      · {
          refine ⟨k, hk, le_rfl, hret, ?_⟩
          intro t ht hlt hret'
          exact hsmall ⟨t, ht, hlt, hret'⟩
        }
    }

/-- The least positive period of a coprime unit return has length at most `2|c|+1`. -/
theorem UnitOffsetMinimalPeriod (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (n : ℤ) (k : ℕ) (hk : 0 < k)
    (hper : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) k n = n) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ d : ℕ, 0 < d ∧ d ≤ 2 * p.C.natAbs + 1 ∧
      Iterate (FirstReturn p hhit) d n = n ∧
      ∀ t : ℕ, Iterate (FirstReturn p hhit) t n = n → d ∣ t := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  obtain ⟨period, hp, hshort, hret⟩ :=
    UnitOffsetPeriodicShort p hQ hcop n k hk hper
  obtain ⟨d, hd, hle, hretd, hdiv⟩ :=
    IterateLeastReturn (FirstReturn p hhit) n period hp hret
  exact ⟨d, hd, Nat.le_trans hle hshort, hretd, hdiv⟩

/-- A period that divides every return is unique. -/
theorem IterateLeastReturnUnique (H : ℤ → ℤ) (n : ℤ)
    (d d' : ℕ)
    (hd : 0 < d) (hd' : 0 < d')
    (hret : Iterate H d n = n) (hret' : Iterate H d' n = n)
    (hdiv : ∀ t : ℕ, Iterate H t n = n → d ∣ t)
    (hdiv' : ∀ t : ℕ, Iterate H t n = n → d' ∣ t) :
    d = d' := by
  have h1 : d ∣ d' := hdiv d' hret'
  have h2 : d' ∣ d := hdiv' d hret
  exact Nat.dvd_antisymm h2 h1

/-- The first `d` states of a least return are distinct. -/
theorem IterateCycleInjective (H : ℤ → ℤ) (n : ℤ) (d : ℕ)
    (hd : 0 < d) (hret : Iterate H d n = n)
    (hmin : ∀ t : ℕ, 0 < t → t < d → Iterate H t n ≠ n)
    (i j : ℕ) (hij : i < j) (hj : j < d) :
    Iterate H i n ≠ Iterate H j n := by
  intro heq
  have hgap : 0 < j - i := by omega
  have hlt : j - i < d := by omega
  have hpull : Iterate H (j - i) n = n := by
    -- Advance from the repeated state through the rest of the cycle.
    have hrest : Iterate H (d - i) (Iterate H i n) = n := by
      have := IterateAdd H i (d - i) n
      have hidx : i + (d - i) = d := by omega
      rw [hidx, hret] at this
      exact this
    have htwice := IterateAdd H (j - i) (d - i) (Iterate H i n)
    have hidx : j - i + (d - i) = d + (j - i) - i := by omega
    rw [heq] at hrest
    -- `H^{d-i}(H^j n) = n`, and `j = i+(j-i)`.
    have hfromj : Iterate H (d - i) (Iterate H j n) = n := hrest
    have := IterateAdd H i (j - i) n
    have hidxi : i + (j - i) = j := by omega
    rw [hidxi] at this
    have hstep : Iterate H (j - i) (Iterate H i n) = Iterate H j n := this
    have hshift := IterateAdd H j (d - j) n
    have hidxj : j + (d - j) = d := by omega
    rw [hidxj, hret] at hshift
    -- Directly: `H^{j-i}(H^i n) = H^i n` and the remaining map is injective on the cycle.
    have hback : Iterate H (d - i) (Iterate H (j - i) (Iterate H i n)) = n := by
      rw [hstep, heq]
      exact hfromj
    have hassoc := IterateAdd H i (j - i + (d - i)) n
    have hsum : i + (j - i + (d - i)) = d + (j - i) := by omega
    rw [← IterateAdd, hsum] at hback
    have hcomm : Iterate H (d + (j - i)) n =
        Iterate H (j - i) (Iterate H d n) := by
      rw [add_comm, IterateAdd]
    rw [hcomm, hret, Iterate] at hback
    exact hback
  exact hmin (j - i) hgap hlt hpull

/-- Every state on a least cycle has the same least return. -/
theorem IterateCycleSamePeriod (H : ℤ → ℤ) (n : ℤ) (d i : ℕ)
    (hd : 0 < d) (hi : i < d) (hret : Iterate H d n = n)
    (hmin : ∀ t : ℕ, 0 < t → t < d → Iterate H t n ≠ n) :
    Iterate H d (Iterate H i n) = Iterate H i n ∧
      ∀ t : ℕ, 0 < t → t < d →
        Iterate H t (Iterate H i n) ≠ Iterate H i n := by
  refine ⟨?_, ?_⟩
  · {
      have := IterateAdd H i d n
      rw [add_comm, IterateAdd, hret] at this
      exact this.symm
    }
  · {
      intro t ht hlt heq
      have hpull : Iterate H t n = n := by
        have hrest : Iterate H (d - i) (Iterate H i n) = n := by
          have := IterateAdd H i (d - i) n
          have hidx : i + (d - i) = d := by omega
          rw [hidx, hret] at this
          exact this
        have hfrom : Iterate H (d - i) (Iterate H t (Iterate H i n)) = n := by
          rw [heq]
          exact hrest
        have := IterateAdd H i (t + (d - i)) n
        have hsum : i + (t + (d - i)) = d + t := by omega
        rw [← IterateAdd, hsum] at hfrom
        have hcomm : Iterate H (d + t) n = Iterate H t (Iterate H d n) := by
          rw [add_comm, IterateAdd]
        rw [hcomm, hret, Iterate] at hfrom
        exact hfrom
      exact hmin t ht hlt hpull
    }

/-- A two-step unit return solves `n(d^2-1) = c(r+ds)`. -/
theorem UnitOffsetTwoStepIff (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    let H := FirstReturn p hhit
    let r := FirstHitTime p hhit n
    let s := FirstHitTime p hhit (H n)
    Iterate H 2 n = n ↔
      n * (p.D * p.D - 1) = p.C * ((r : ℤ) + p.D * (s : ℤ)) := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let r := FirstHitTime p hhit n
  let s := FirstHitTime p hhit (H n)
  have hq1 := UnitOffsetQuotient p hQ hcop n
  have hq2 := UnitOffsetQuotient p hQ hcop (H n)
  have ht1 := UnitOffsetTime p hQ hcop n
  have ht2 := UnitOffsetTime p hQ hcop (H n)
  have hd : p.D ≠ 0 := by
    have := p.DAdmissible
    omega
  constructor
  · {
      intro htwo
      have hH : H n = (n + p.C * (r : ℤ)) / p.D := by
        rw [H, hq1, ht1]
      have hHH : H (H n) = (H n + p.C * (s : ℤ)) / p.D := by
        rw [hq2, ht2]
      have hdiv2 : p.D ∣ H n + p.C * (s : ℤ) := by
        rw [← hHH]
        exact ⟨H (H n), by ring⟩
      have hback2 := Int.ediv_mul_cancel hdiv2
      rw [← hHH] at hback2
      rw [show Iterate H 2 n = H (H n) by rfl, htwo] at hback2
      have hdiv1 : p.D ∣ n + p.C * (r : ℤ) := by
        rw [← hH]
        exact ⟨H n, by ring⟩
      have hback1 := Int.ediv_mul_cancel hdiv1
      rw [← hH] at hback1
      -- `d*n = H(n) + c*s` and `d*H(n) = n + c*r`.
      have hlin : p.D * p.D * n = n + p.C * ((r : ℤ) + p.D * (s : ℤ)) := by
        calc
          p.D * p.D * n = p.D * (H n + p.C * (s : ℤ)) := by
            rw [← hback2]; ring
          _ = p.D * H n + p.D * (p.C * (s : ℤ)) := by ring
          _ = n + p.C * (r : ℤ) + p.C * (p.D * (s : ℤ)) := by
            rw [← hback1]; ring
          _ = n + p.C * ((r : ℤ) + p.D * (s : ℤ)) := by ring
      linarith
    }
  · {
      intro heq
      have hdiv1 : p.D ∣ n + p.C * (r : ℤ) := by
        refine ⟨H n, ?_⟩
        have hH : H n = (n + p.C * (r : ℤ)) / p.D := by
          rw [H, hq1, ht1]
        have hdiv : p.D ∣ n + p.C * (r : ℤ) := by
          rw [← hH]
          exact ⟨H n, by ring⟩
        exact (Int.ediv_mul_cancel hdiv).symm.trans (by rw [hH])
      have hH : H n = (n + p.C * (r : ℤ)) / p.D := by
        rw [H, hq1, ht1]
      have hback1 := Int.ediv_mul_cancel (by
        rw [← hH]; exact ⟨H n, by ring⟩)
      rw [← hH] at hback1
      have hdiv2 : p.D ∣ H n + p.C * (s : ℤ) := by
        have hHH : H (H n) = (H n + p.C * (s : ℤ)) / p.D := by
          rw [hq2, ht2]
        rw [← hHH]
        exact ⟨H (H n), by ring⟩
      have hback2 := Int.ediv_mul_cancel hdiv2
      rw [← (by rw [hq2, ht2] : H (H n) =
        (H n + p.C * (s : ℤ)) / p.D)] at hback2
      -- The algebraic relation forces the second quotient to be `n`.
      have htarget : H n + p.C * (s : ℤ) = p.D * n := by
        have hscaled : p.D * (H n + p.C * (s : ℤ)) =
            p.D * p.D * n := by
          calc
            p.D * (H n + p.C * (s : ℤ))
              = p.D * H n + p.D * p.C * (s : ℤ) := by ring
            _ = n + p.C * (r : ℤ) + p.C * p.D * (s : ℤ) := by
              rw [← hback1]; ring
            _ = n + p.C * ((r : ℤ) + p.D * (s : ℤ)) := by ring
            _ = p.D * p.D * n := by linarith
        exact Int.eq_of_mul_eq_mul_left hd hscaled
      rw [show Iterate H 2 n = H (H n) by rfl]
      have hHH : H (H n) = (H n + p.C * (s : ℤ)) / p.D := by
        rw [hq2, ht2]
      rw [hHH, Int.ediv_eq_of_eq_mul_left hd htarget]
    }

/-- A two-step unit return is at most the offset, and smaller if `d<0`. -/
theorem UnitOffsetTwoStepBound (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (htwo : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) 2 n = n) :
    (0 < p.D → n.natAbs ≤ p.C.natAbs) ∧
      (p.D < 0 → n.natAbs * (p.D.natAbs + 1) ≤
        p.C.natAbs * p.D.natAbs) := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let r := FirstHitTime p hhit n
  let s := FirstHitTime p hhit (H n)
  have heq := (UnitOffsetTwoStepIff p hQ hcop n).1 htwo
  have hr := UnitOffsetTimeStrict p hQ hcop n
  have hs := UnitOffsetTimeStrict p hQ hcop (H n)
  have hm : 2 ≤ p.D.natAbs := p.DAdmissible
  constructor
  · {
      intro hp
      have hpos : 0 ≤ (r : ℤ) + p.D * (s : ℤ) := by omega
      have habs : n.natAbs * (p.D * p.D - 1).natAbs =
          p.C.natAbs * ((r : ℤ) + p.D * (s : ℤ)).natAbs := by
        have := congrArg Int.natAbs heq
        rw [Int.natAbs_mul, Int.natAbs_mul] at this
        exact this
      have hgap : (p.D * p.D - 1).natAbs = p.D.natAbs * p.D.natAbs - 1 := by
        omega
      have hsum : ((r : ℤ) + p.D * (s : ℤ)).natAbs =
          r + p.D.natAbs * s := by
        rw [Int.natAbs_of_nonneg hpos]
        omega
      rw [hgap, hsum] at habs
      have hle : r + p.D.natAbs * s ≤
          (p.D.natAbs - 1) + p.D.natAbs * (p.D.natAbs - 1) := by
        have hr' : r ≤ p.D.natAbs - 1 := hr
        have hs' : s ≤ p.D.natAbs - 1 := hs
        omega
      have hprod : n.natAbs * (p.D.natAbs * p.D.natAbs - 1) ≤
          p.C.natAbs * (p.D.natAbs * p.D.natAbs - 1) := by
        have hmax : (p.D.natAbs - 1) + p.D.natAbs * (p.D.natAbs - 1) =
            p.D.natAbs * p.D.natAbs - 1 := by omega
        rw [habs]
        have := Nat.mul_le_mul_left p.C.natAbs hle
        rw [hmax] at this
        exact this
      exact Nat.le_of_mul_le_mul_right hprod (by omega)
    }
  · {
      intro hn
      have habs : n.natAbs * (p.D * p.D - 1).natAbs =
          p.C.natAbs * ((r : ℤ) + p.D * (s : ℤ)).natAbs := by
        have := congrArg Int.natAbs heq
        rw [Int.natAbs_mul, Int.natAbs_mul] at this
        exact this
      have hgap : (p.D * p.D - 1).natAbs =
          p.D.natAbs * p.D.natAbs - 1 := by omega
      -- The negative divisor makes `r + d*s = r - m*s`.
      have hspan : ((r : ℤ) + p.D * (s : ℤ)).natAbs ≤
          p.D.natAbs * (p.D.natAbs - 1) := by
        have hr' : r ≤ p.D.natAbs - 1 := hr
        have hs' : s ≤ p.D.natAbs - 1 := hs
        have hneg : p.D = -((p.D.natAbs : ℤ)) := by omega
        rw [hneg]
        have : ((r : ℤ) - (p.D.natAbs : ℤ) * (s : ℤ)).natAbs ≤
            p.D.natAbs * (p.D.natAbs - 1) := by
          have hlow : -((p.D.natAbs : ℤ) * (p.D.natAbs - 1)) ≤
              (r : ℤ) - (p.D.natAbs : ℤ) * (s : ℤ) := by omega
          have hhigh : (r : ℤ) - (p.D.natAbs : ℤ) * (s : ℤ) ≤
              (p.D.natAbs - 1 : ℤ) := by omega
          have habs' := Int.natAbs_le_natAbs_of_nonneg_of_le
          omega
        simpa [Int.natAbs_neg] using this
      rw [hgap] at habs
      have hprod : n.natAbs * (p.D.natAbs * p.D.natAbs - 1) ≤
          p.C.natAbs * (p.D.natAbs * (p.D.natAbs - 1)) := by
        rw [habs]
        exact Nat.mul_le_mul_left _ hspan
      have hfactor : p.D.natAbs * p.D.natAbs - 1 =
          (p.D.natAbs - 1) * (p.D.natAbs + 1) := by omega
      have hright : p.D.natAbs * (p.D.natAbs - 1) =
          (p.D.natAbs - 1) * p.D.natAbs := by omega
      rw [hfactor, hright] at hprod
      have hpos : 0 < p.D.natAbs - 1 := by omega
      have hcancel : n.natAbs * (p.D.natAbs + 1) ≤
          p.C.natAbs * p.D.natAbs := by
        have := Nat.le_of_mul_le_mul_right hprod hpos
        -- The factors are swapped.
        have hcomm : n.natAbs * ((p.D.natAbs - 1) * (p.D.natAbs + 1)) =
            (p.D.natAbs - 1) * (n.natAbs * (p.D.natAbs + 1)) := by
          ring
        have hcomm' : p.C.natAbs * ((p.D.natAbs - 1) * p.D.natAbs) =
            (p.D.natAbs - 1) * (p.C.natAbs * p.D.natAbs) := by
          ring
        rw [hcomm, hcomm'] at hprod
        exact Nat.le_of_mul_le_mul_left hprod hpos
      exact hcancel
    }

/-- Equality at absolute value `|c|` forces the seed `c` when `d>0`. -/
theorem UnitOffsetTwoStepTop (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (hp : 0 < p.D)
    (htwo : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) 2 n = n)
    (htop : n.natAbs = p.C.natAbs) : n = p.C := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let r := FirstHitTime p hhit n
  let s := FirstHitTime p hhit (H n)
  have heq := (UnitOffsetTwoStepIff p hQ hcop n).1 htwo
  have hr := UnitOffsetTimeStrict p hQ hcop n
  have hs := UnitOffsetTimeStrict p hQ hcop (H n)
  have hpos : 0 ≤ (r : ℤ) + p.D * (s : ℤ) := by omega
  have habs : n.natAbs * (p.D.natAbs * p.D.natAbs - 1) =
      p.C.natAbs * (r + p.D.natAbs * s) := by
    have := congrArg Int.natAbs heq
    have hgap : (p.D * p.D - 1).natAbs =
        p.D.natAbs * p.D.natAbs - 1 := by omega
    have hsum : ((r : ℤ) + p.D * (s : ℤ)).natAbs =
        r + p.D.natAbs * s := by
      rw [Int.natAbs_of_nonneg hpos]
      omega
    rw [Int.natAbs_mul, Int.natAbs_mul, hgap, hsum] at this
    exact this
  have hmax : r + p.D.natAbs * s =
      p.D.natAbs * p.D.natAbs - 1 := by
    have hle : r + p.D.natAbs * s ≤
        (p.D.natAbs - 1) + p.D.natAbs * (p.D.natAbs - 1) := by omega
    have hform : (p.D.natAbs - 1) + p.D.natAbs * (p.D.natAbs - 1) =
        p.D.natAbs * p.D.natAbs - 1 := by omega
    rw [htop] at habs
    have : p.C.natAbs * (r + p.D.natAbs * s) =
        p.C.natAbs * (p.D.natAbs * p.D.natAbs - 1) := by
      rw [← habs, hform]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < p.C.natAbs) this
  have hr' : r = p.D.natAbs - 1 := by omega
  have hs' : s = p.D.natAbs - 1 := by omega
  have hcast : ((p.D.natAbs * p.D.natAbs - 1 : ℕ) : ℤ) =
      p.D * p.D - 1 := by omega
  rw [hr', hs'] at heq
  have : (r : ℤ) + p.D * (s : ℤ) = p.D * p.D - 1 := by
    rw [hr', hs']
    omega
  rw [this] at heq
  have hgap : p.D * p.D - 1 ≠ 0 := by omega
  exact Int.eq_of_mul_eq_mul_right hgap (by linarith)

/-- Weighted sum of the hit times along a unit orbit. -/
def UnitHitWeight (d : ℤ) (H : ℤ → ℤ) (hit : ℤ → ℕ) (n : ℤ) : ℕ → ℤ
  | 0 => 0
  | k + 1 =>
      UnitHitWeight d H hit n k +
        (hit (Iterate H k n) : ℤ) * d ^ k

/-- Each unit step multiplies by `d` and adds `c` times the hit. -/
theorem UnitOffsetPowerIdentity (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (k : ℕ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    let H := FirstReturn p hhit
    p.D ^ k * Iterate H k n =
      n + p.C * UnitHitWeight p.D H (FirstHitTime p hhit) n k := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  induction k with
  | zero => {
      simp [Iterate, UnitHitWeight]
    }
  | succ k ih => {
      have hstep := UnitOffsetQuotient p hQ hcop (Iterate H k n)
      have htime := UnitOffsetTime p hQ hcop (Iterate H k n)
      have hdiv : p.D ∣
          Iterate H k n +
            p.C * (FirstHitTime p hhit (Iterate H k n) : ℤ) := by
        rw [← hstep, ← htime]
        exact ⟨H (Iterate H k n), by ring⟩
      have hback := Int.ediv_mul_cancel hdiv
      rw [← hstep, ← htime] at hback
      -- The inductive state scales by one more factor of `d`.
      calc
        p.D ^ (k + 1) * Iterate H (k + 1) n
          = p.D ^ k * (p.D * H (Iterate H k n)) := by
            rw [show Iterate H (k + 1) n = H (Iterate H k n) by rfl]
            ring
        _ = p.D ^ k *
            (Iterate H k n +
              p.C * (FirstHitTime p hhit (Iterate H k n) : ℤ)) := by
            rw [← hback]
        _ = p.D ^ k * Iterate H k n +
            p.C * ((FirstHitTime p hhit (Iterate H k n) : ℤ) * p.D ^ k) := by
            ring
        _ = n + p.C * UnitHitWeight p.D H (FirstHitTime p hhit) n k +
            p.C * ((FirstHitTime p hhit (Iterate H k n) : ℤ) * p.D ^ k) := by
            rw [ih]
        _ = n + p.C * UnitHitWeight p.D H (FirstHitTime p hhit) n (k + 1) := by
            simp [UnitHitWeight]
            ring
    }

/-- A `k`-step unit return solves `n(d^k-1) = c` times the hit weight. -/
theorem UnitOffsetKStepIff (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (k : ℕ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    let H := FirstReturn p hhit
    Iterate H k n = n ↔
      n * (p.D ^ k - 1) =
        p.C * UnitHitWeight p.D H (FirstHitTime p hhit) n k := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hid := UnitOffsetPowerIdentity p hQ hcop n k
  have hd : p.D ^ k ≠ 0 := by
    exact pow_ne_zero k (by
      have := p.DAdmissible
      omega)
  constructor
  · {
      intro hret
      rw [hret] at hid
      linarith
    }
  · {
      intro heq
      have hscaled : p.D ^ k * Iterate H k n = p.D ^ k * n := by
        linarith
      exact Int.eq_of_mul_eq_mul_left hd hscaled
    }

/-- The hit weight is at most the truncated geometric sum. -/
theorem UnitHitWeightAbs (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (k : ℕ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    let H := FirstReturn p hhit
    (UnitHitWeight p.D H (FirstHitTime p hhit) n k).natAbs ≤
      p.D.natAbs ^ k - 1 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hm : 1 < p.D.natAbs := by
    have := p.DAdmissible
    omega
  induction k with
  | zero => {
      simp [UnitHitWeight]
    }
  | succ k ih => {
      have hhitk := UnitOffsetTimeStrict p hQ hcop (Iterate H k n)
      simp [UnitHitWeight]
      have hterm : ((FirstHitTime p hhit (Iterate H k n) : ℤ) *
          p.D ^ k).natAbs ≤ (p.D.natAbs - 1) * p.D.natAbs ^ k := by
        rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]
        exact Nat.mul_le_mul_right _ hhitk
      have hadd := Int.natAbs_add_le
        (UnitHitWeight p.D H (FirstHitTime p hhit) n k)
        ((FirstHitTime p hhit (Iterate H k n) : ℤ) * p.D ^ k)
      have hgeo : (p.D.natAbs ^ k - 1) +
          (p.D.natAbs - 1) * p.D.natAbs ^ k =
          p.D.natAbs ^ (k + 1) - 1 := by
        have hpow : p.D.natAbs * p.D.natAbs ^ k =
            p.D.natAbs ^ (k + 1) := by
          rw [Nat.mul_comm, Nat.pow_succ]
        omega
      omega
    }

/-- Every unit return obeys the geometric weight bound. -/
theorem UnitOffsetReturnBound (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (k : ℕ)
    (hret : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) k n = n) :
    n.natAbs * (p.D ^ k - 1).natAbs ≤
      p.C.natAbs * (p.D.natAbs ^ k - 1) := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have heq := (UnitOffsetKStepIff p hQ hcop n k).1 hret
  have hweight := UnitHitWeightAbs p hQ hcop n k
  have habs : n.natAbs * (p.D ^ k - 1).natAbs =
      p.C.natAbs *
        (UnitHitWeight p.D H (FirstHitTime p hhit) n k).natAbs := by
    have := congrArg Int.natAbs heq
    rw [Int.natAbs_mul, Int.natAbs_mul] at this
    exact this
  rw [habs]
  exact Nat.mul_le_mul_left _ hweight

/-- A positive divisor meets absolute value `|c|` only at the seed `c`. -/
theorem UnitOffsetPositiveTop (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (k : ℕ)
    (hp : 0 < p.D) (hk : 0 < k)
    (hret : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) k n = n)
    (htop : n.natAbs = p.C.natAbs) : n = p.C := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have heq := (UnitOffsetKStepIff p hQ hcop n k).1 hret
  have hbound := UnitOffsetReturnBound p hQ hcop n k hret
  have hgap : (p.D ^ k - 1).natAbs = p.D.natAbs ^ k - 1 := by omega
  rw [hgap, htop] at hbound
  have hweight : (UnitHitWeight p.D H (FirstHitTime p hhit) n k).natAbs =
      p.D.natAbs ^ k - 1 := by
    have hle := UnitHitWeightAbs p hQ hcop n k
    have habs : p.C.natAbs *
        (UnitHitWeight p.D H (FirstHitTime p hhit) n k).natAbs =
        p.C.natAbs * (p.D.natAbs ^ k - 1) := by
      have := congrArg Int.natAbs heq
      rw [Int.natAbs_mul, Int.natAbs_mul, hgap, htop] at this
      exact this.symm
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < p.C.natAbs) habs
  -- Every hit is maximal, so the weight equals `d^k - 1`.
  have hfull : UnitHitWeight p.D H (FirstHitTime p hhit) n k =
      ((p.D.natAbs ^ k - 1 : ℕ) : ℤ) := by
    have hnonneg : ∀ j,
        0 ≤ UnitHitWeight p.D H (FirstHitTime p hhit) n j := by
      intro j
      induction j with
      | zero => {
          simp [UnitHitWeight]
        }
      | succ j ih => {
          simp [UnitHitWeight]
          have : 0 ≤ (FirstHitTime p hhit (Iterate H j n) : ℤ) * p.D ^ j := by
            omega
          linarith
        }
    rw [Int.natAbs_of_nonneg (hnonneg k)] at hweight
    exact hweight
  have hcast : ((p.D.natAbs ^ k - 1 : ℕ) : ℤ) = p.D ^ k - 1 := by omega
  rw [hfull, hcast] at heq
  have hne : p.D ^ k - 1 ≠ 0 := by omega
  exact Int.eq_of_mul_eq_mul_right hne (by linarith)

/-- For `d<0` and `k≥2`, the hit weight misses at least two units. -/
theorem UnitHitWeightStrict (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (k : ℕ)
    (hn : p.D < 0) (hk : 2 ≤ k) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    let H := FirstReturn p hhit
    (UnitHitWeight p.D H (FirstHitTime p hhit) n k).natAbs ≤
      p.D.natAbs ^ k - 2 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hm : 2 ≤ p.D.natAbs := p.DAdmissible
  have hneg : p.D = -((p.D.natAbs : ℤ)) := by omega
  -- The length-two weight is `r0 - m*r1`.
  have hbase : (UnitHitWeight p.D H (FirstHitTime p hhit) n 2).natAbs ≤
      p.D.natAbs ^ 2 - 2 := by
    have hr0 := UnitOffsetTimeStrict p hQ hcop n
    have hr1 := UnitOffsetTimeStrict p hQ hcop (Iterate H 1 n)
    simp [UnitHitWeight, Iterate, hneg]
    have : ((FirstHitTime p hhit n : ℤ) -
        (p.D.natAbs : ℤ) * (FirstHitTime p hhit (H n) : ℤ)).natAbs ≤
        p.D.natAbs ^ 2 - 2 := by
      have h0 : FirstHitTime p hhit n ≤ p.D.natAbs - 1 := hr0
      have h1 : FirstHitTime p hhit (H n) ≤ p.D.natAbs - 1 := hr1
      omega
    simpa [Iterate] using this
  revert hk
  induction k with
  | zero => {
      intro hk
      omega
    }
  | succ k ih => {
      intro hk
      by_cases htwo : k = 1
      · {
          rw [htwo] at hbase
          simpa using hbase
        }
      · {
          have hk' : 2 ≤ k := by omega
          have ih' := ih hk'
          have hhitk := UnitOffsetTimeStrict p hQ hcop (Iterate H k n)
          simp [UnitHitWeight]
          have hterm : ((FirstHitTime p hhit (Iterate H k n) : ℤ) *
              p.D ^ k).natAbs ≤ (p.D.natAbs - 1) * p.D.natAbs ^ k := by
            rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]
            exact Nat.mul_le_mul_right _ hhitk
          have hadd := Int.natAbs_add_le
            (UnitHitWeight p.D H (FirstHitTime p hhit) n k)
            ((FirstHitTime p hhit (Iterate H k n) : ℤ) * p.D ^ k)
          omega
        }
    }

/-- A negative divisor has no periodic point of absolute value `|c|`. -/
theorem UnitOffsetNegativeBelow (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (k : ℕ)
    (hn : p.D < 0) (hk : 0 < k)
    (hret : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) k n = n) :
    n.natAbs < p.C.natAbs := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hc : 0 < p.C.natAbs := by
    have hcop' := hcop
    have hm : 1 < p.D.natAbs := by
      have := p.DAdmissible
      omega
    -- `c = 0` would share the factor `|d|`.
    by_contra hzero
    have : p.C.natAbs = 0 := by omega
    rw [this] at hcop'
    have : 1 < 1 := by
      have := Nat.Coprime.coprime_dvd_right (Nat.dvd_refl p.D.natAbs)
        (by simpa [Nat.coprime_zero_left] using hcop')
      omega
    omega
  by_cases hodd : k % 2 = 1
  · {
      have hodd' := UnitOffsetOddReturnBound p hQ hcop n k hn hodd hret
      have hden : 0 < p.D.natAbs ^ k + 1 := by omega
      have hlt : p.D.natAbs ^ k - 1 < p.D.natAbs ^ k + 1 := by omega
      have : n.natAbs * (p.D.natAbs ^ k + 1) <
          p.C.natAbs * (p.D.natAbs ^ k + 1) := by
        have hle := hodd'
        have hstrict : p.C.natAbs * (p.D.natAbs ^ k - 1) <
            p.C.natAbs * (p.D.natAbs ^ k + 1) :=
          Nat.mul_lt_mul_of_pos_left hlt hc
        omega
      exact Nat.lt_of_mul_lt_mul_right this
    }
  · {
      have heven : 2 ≤ k := by
        have : k % 2 = 0 := by omega
        omega
      have hstrict := UnitHitWeightStrict p hQ hcop n k hn heven
      have hretb := UnitOffsetReturnBound p hQ hcop n k hret
      have hgap : (p.D ^ k - 1).natAbs = p.D.natAbs ^ k - 1 := by
        have hpow : p.D ^ k = ((p.D.natAbs ^ k : ℕ) : ℤ) := by
          have hneg : p.D = -((p.D.natAbs : ℤ)) := by omega
          rw [hneg, neg_pow]
          have he : Even k := by
            rw [Nat.even_iff]
            omega
          simp [he]
        rw [hpow]
        omega
      rw [hgap] at hretb
      have habs : n.natAbs * (p.D.natAbs ^ k - 1) =
          p.C.natAbs *
            (UnitHitWeight p.D H (FirstHitTime p hhit) n k).natAbs := by
        have heq := (UnitOffsetKStepIff p hQ hcop n k).1 hret
        have := congrArg Int.natAbs heq
        rw [Int.natAbs_mul, Int.natAbs_mul, hgap] at this
        exact this
      have hprod : n.natAbs * (p.D.natAbs ^ k - 1) ≤
          p.C.natAbs * (p.D.natAbs ^ k - 2) := by
        rw [habs]
        exact Nat.mul_le_mul_left _ hstrict
      have hden : 0 < p.D.natAbs ^ k - 1 := by omega
      have hlt : p.C.natAbs * (p.D.natAbs ^ k - 2) <
          p.C.natAbs * (p.D.natAbs ^ k - 1) :=
        Nat.mul_lt_mul_of_pos_left (by omega) hc
      have : n.natAbs * (p.D.natAbs ^ k - 1) <
          p.C.natAbs * (p.D.natAbs ^ k - 1) := by omega
      exact Nat.lt_of_mul_lt_mul_right this
    }

/-- The periodic shell of a negative divisor is `|c|-1`. -/
theorem UnitOffsetNegativeShell (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (k : ℕ)
    (hn : p.D < 0) (hk : 0 < k)
    (hret : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) k n = n) :
    n.natAbs ≤ p.C.natAbs - 1 := by
  have hlt := UnitOffsetNegativeBelow p hQ hcop n k hn hk hret
  omega

/-- The shell `|c|-1` is achieved by the cycle of `-1` when `c=2` and `d=-3`. -/
theorem TwoNegThreeShellSharp (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 2) (hD : p.D = -3) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ (by
        rw [hC, hD]
        decide) p.DAdmissible x).imp fun j h => h.1
    let H := FirstReturn p hhit
    H (-1) = -1 ∧ (-1 : ℤ).natAbs = p.C.natAbs - 1 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ (by
      rw [hC, hD]
      decide) p.DAdmissible x).imp fun j h => h.1
  refine ⟨TwoNegThreeFixesNegOne p hQ hC hD, ?_⟩
  rw [hC]
  decide

/-- For `|c|=1`, a negative divisor has only the periodic point `0`. -/
theorem UnitOffsetAbsOneNegative (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (k : ℕ)
    (hc : p.C.natAbs = 1) (hn : p.D < 0) (hk : 0 < k)
    (hret : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) k n = n) : n = 0 := by
  have hshell := UnitOffsetNegativeShell p hQ hcop n k hn hk hret
  rw [hc] at hshell
  have : n.natAbs = 0 := by omega
  exact Int.natAbs_eq_zero.mp this

/-- For `|c|=1` and `d>0`, the only periodic points are `0` and `c`. -/
theorem UnitOffsetAbsOnePositive (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (k : ℕ)
    (hc : p.C.natAbs = 1) (hp : 0 < p.D) (hk : 0 < k)
    (hret : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) k n = n) : n = 0 ∨ n = p.C := by
  have hshell := UnitOffsetCycleInShell p hQ hcop n k hk hret
  rw [hc] at hshell
  have : n.natAbs ≤ 1 := hshell
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h0 | h1
  · {
      exact Or.inl (Int.natAbs_eq_zero.mp h0)
    }
  · {
      exact Or.inr (UnitOffsetPositiveTop p hQ hcop n k hp hk hret h1)
    }

/-- Zero is a fixed return: the divisor meets it at time `0`. -/
theorem UnitOffsetZeroFixed (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    FirstReturn p hhit 0 = 0 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  have hzero : IsFirstHit p 0 0 := by
    refine ⟨?_, ?_⟩
    · {
        refine ⟨0, ?_⟩
        simp [AffineState]
      }
    · {
        intro i hi
        omega
      }
  have htime : FirstHitTime p hhit 0 = 0 := by
    have hspec := Nat.find_spec (hhit 0)
    have hmin := Nat.find_min' (hhit 0) hzero
    have heq := FirstHitUnique p 0 (FirstHitTime p hhit 0) 0 hspec hzero
    omega
  simp [FirstReturn, htime, AffineState, hQ]

/-- For `|c|=1` and `d<0`, every orbit reaches the fixed point `0`. -/
theorem UnitOffsetAbsOneNegativeReaches (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hc : p.C.natAbs = 1) (hn : p.D < 0) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t : ℕ, Iterate (FirstReturn p hhit) t n = 0 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  obtain ⟨t, period, _, hp, _, htail⟩ := UnitOffsetSharpCycle p hQ hcop n
  have hper : Iterate H period (Iterate H t n) = Iterate H t n := by
    have := htail 0
    simpa [H, IterateAdd] using this
  have hzero := UnitOffsetAbsOneNegative p hQ hcop (Iterate H t n) period
    hc hn hp hper
  exact ⟨t, hzero⟩

/-- For `|c|=1` and `d>0`, every orbit reaches `0` or `c`. -/
theorem UnitOffsetAbsOnePositiveReaches (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hc : p.C.natAbs = 1) (hp : 0 < p.D) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t : ℕ, Iterate (FirstReturn p hhit) t n = 0 ∨
      Iterate (FirstReturn p hhit) t n = p.C := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  obtain ⟨t, period, _, hpos, _, htail⟩ := UnitOffsetSharpCycle p hQ hcop n
  have hper : Iterate H period (Iterate H t n) = Iterate H t n := by
    have := htail 0
    simpa [H, IterateAdd] using this
  have hclass := UnitOffsetAbsOnePositive p hQ hcop (Iterate H t n) period
    hc hp hpos hper
  exact ⟨t, hclass⟩

/-- For `|c|=1` and `d<0`, the orbit is eventually the constant `0`. -/
theorem UnitOffsetAbsOneNegativeAbsorbs (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hc : p.C.natAbs = 1) (hn : p.D < 0) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t : ℕ, t ≤ n.natAbs + 2 ∧
      ∀ k : ℕ, Iterate (FirstReturn p hhit) (t + k) n = 0 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  obtain ⟨t, period, ht, hp, _, htail⟩ := UnitOffsetSharpCycle p hQ hcop n
  have hper : Iterate H period (Iterate H t n) = Iterate H t n := by
    have := htail 0
    simpa [H, IterateAdd] using this
  have hzero := UnitOffsetAbsOneNegative p hQ hcop (Iterate H t n) period
    hc hn hp hper
  refine ⟨t, ?_, ?_⟩
  · {
      rw [hc] at ht
      omega
    }
  intro k
  induction k with
  | zero => {
      simpa [H] using ht
    }
  | succ k ih => {
      rw [Nat.add_succ, IterateAdd, ih]
      simpa [H] using UnitOffsetZeroFixed p hQ hcop
    }

/-- For `|c|=1` and `d>0`, the orbit is eventually constant at `0` or at `c`. -/
theorem UnitOffsetAbsOnePositiveAbsorbs (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hc : p.C.natAbs = 1) (hp : 0 < p.D) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t : ℕ, t ≤ n.natAbs + 2 ∧
      ((∀ k : ℕ, Iterate (FirstReturn p hhit) (t + k) n = 0) ∨
        (∀ k : ℕ, Iterate (FirstReturn p hhit) (t + k) n = p.C)) := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  obtain ⟨t, period, ht, hpos, _, htail⟩ := UnitOffsetSharpCycle p hQ hcop n
  have hper : Iterate H period (Iterate H t n) = Iterate H t n := by
    have := htail 0
    simpa [H, IterateAdd] using this
  have hclass := UnitOffsetAbsOnePositive p hQ hcop (Iterate H t n) period
    hc hp hpos hper
  refine ⟨t, ?_, ?_⟩
  · {
      rw [hc] at ht
      omega
    }
  rcases hclass with h0 | hc'
  · {
      left
      intro k
      induction k with
      | zero => {
          simpa [H] using h0
        }
      | succ k ih => {
          rw [Nat.add_succ, IterateAdd, ih]
          simpa [H] using UnitOffsetZeroFixed p hQ hcop
        }
    }
  · {
      right
      intro k
      induction k with
      | zero => {
          simpa [H] using hc'
        }
      | succ k ih => {
          rw [Nat.add_succ, IterateAdd, ih]
          simpa [H] using UnitOffsetFixesOffset p hQ hcop hp
        }
    }

/-- For `|d|=2` and `|c|=1`, one return at least halves the absolute value. -/
theorem UnitOffsetTwoHalves (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : p.D.natAbs = 2) (hc : p.C.natAbs = 1) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    (FirstReturn p hhit n).natAbs ≤ (n.natAbs + 1) / 2 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hquot := UnitOffsetQuotient p hQ hcop n
  have htime := UnitOffsetTimeStrict p hQ hcop n
  have hnum : (n + p.C * (FirstHitTime p hhit n : ℤ)).natAbs ≤
      n.natAbs + 1 := by
    have hadd := Int.natAbs_add_le n (p.C * (FirstHitTime p hhit n : ℤ))
    have hmul : (p.C * (FirstHitTime p hhit n : ℤ)).natAbs =
        p.C.natAbs * FirstHitTime p hhit n := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    rw [hd] at htime
    have : FirstHitTime p hhit n ≤ 1 := by omega
    omega
  have hdiv : p.D.natAbs * (H n).natAbs =
      (n + p.C * (FirstHitTime p hhit n : ℤ)).natAbs := by
    have hsize := (UnitOffsetSize p hQ hcop n).1
    simpa [H, hquot] using hsize
  rw [hd] at hdiv
  omega

/-- For `|d|≥3` and `|c|=1`, a seed of size at least `2` at least halves. -/
theorem UnitOffsetLargeHalves (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : 3 ≤ p.D.natAbs) (hc : p.C.natAbs = 1) (n : ℤ)
    (hn : 2 ≤ n.natAbs) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    (FirstReturn p hhit n).natAbs ≤ n.natAbs / 2 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hquot := UnitOffsetQuotient p hQ hcop n
  have htime := UnitOffsetTimeStrict p hQ hcop n
  have hnum : (n + p.C * (FirstHitTime p hhit n : ℤ)).natAbs ≤
      n.natAbs + p.D.natAbs - 1 := by
    have hadd := Int.natAbs_add_le n (p.C * (FirstHitTime p hhit n : ℤ))
    have hmul : (p.C * (FirstHitTime p hhit n : ℤ)).natAbs =
        p.C.natAbs * FirstHitTime p hhit n := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    omega
  have hdiv : p.D.natAbs * (H n).natAbs =
      (n + p.C * (FirstHitTime p hhit n : ℤ)).natAbs := by
    have hsize := (UnitOffsetSize p hQ hcop n).1
    simpa [H, hquot] using hsize
  omega

/-- For `|d|≥3` and `|c|=1`, absolute value `1` begins by time `log2|n|`. -/
theorem UnitOffsetLargeLog (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : 3 ≤ p.D.natAbs) (hc : p.C.natAbs = 1) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t : ℕ, t ≤ Nat.log 2 n.natAbs ∧
      (Iterate (FirstReturn p hhit) t n).natAbs ≤ 1 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  suffices ∀ a : ℕ, ∀ x : ℤ, x.natAbs = a →
      ∃ t : ℕ, t ≤ Nat.log 2 a ∧ (Iterate H t x).natAbs ≤ 1 by
    exact this n.natAbs n rfl
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    {
      intro x hx
      by_cases hsmall : a ≤ 1
      · {
          refine ⟨0, ?_, ?_⟩
          · {
              have : Nat.log 2 a = 0 := by omega
              omega
            }
          · {
              simpa [hx] using hsmall
            }
        }
      · {
          have hx2 : 2 ≤ x.natAbs := by omega
          have hhalf := UnitOffsetLargeHalves p hQ hcop hd hc x hx2
          have hlt : (H x).natAbs < a := by
            rw [← hx] at hhalf
            omega
          obtain ⟨t, ht, hshell⟩ := ih (H x).natAbs hlt (H x) rfl
          refine ⟨t + 1, ?_, ?_⟩
          · {
              have htwo : 2 * (H x).natAbs ≤ a := by
                rw [← hx] at hhalf
                omega
              have hlog : Nat.log 2 (H x).natAbs + 1 ≤ Nat.log 2 a := by
                by_cases hz : (H x).natAbs = 0
                · {
                    rw [hz]
                    have : 1 ≤ Nat.log 2 a := by omega
                    omega
                  }
                · {
                    have hpow := Nat.pow_log_le_self 2 (by omega : 1 ≤ (H x).natAbs)
                    have hcmp : 2 ^ (Nat.log 2 (H x).natAbs + 1) ≤ a := by
                      rw [Nat.pow_succ]
                      omega
                    exact Nat.le_log_of_pow_le (by decide) hcmp
                  }
              omega
            }
          · {
              rw [Iterate]
              simpa [IterateAdd] using hshell
            }
        }
    }

/-- For `|d|=2`, one return is at most the average of `|n|` and `|c|`. -/
theorem UnitOffsetTwoAverage (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : p.D.natAbs = 2) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    (FirstReturn p hhit n).natAbs ≤ (n.natAbs + p.C.natAbs) / 2 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hquot := UnitOffsetQuotient p hQ hcop n
  have htime := UnitOffsetTimeStrict p hQ hcop n
  have hnum : (n + p.C * (FirstHitTime p hhit n : ℤ)).natAbs ≤
      n.natAbs + p.C.natAbs := by
    have hadd := Int.natAbs_add_le n (p.C * (FirstHitTime p hhit n : ℤ))
    have hmul : (p.C * (FirstHitTime p hhit n : ℤ)).natAbs =
        p.C.natAbs * FirstHitTime p hhit n := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    rw [hd] at htime
    omega
  have hdiv : p.D.natAbs * (H n).natAbs =
      (n + p.C * (FirstHitTime p hhit n : ℤ)).natAbs := by
    have hsize := (UnitOffsetSize p hQ hcop n).1
    simpa [H, hquot] using hsize
  rw [hd] at hdiv
  omega

/-- For `|d|=2`, the excess over `|c|` at least halves. -/
theorem UnitOffsetTwoExcess (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : p.D.natAbs = 2) (n : ℤ) (hn : p.C.natAbs ≤ n.natAbs) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    (FirstReturn p hhit n).natAbs ≤
      p.C.natAbs + (n.natAbs - p.C.natAbs) / 2 := by
  have havg := UnitOffsetTwoAverage p hQ hcop hd n
  omega

/-- For `|d|=2`, the shell `|x|≤|c|` begins by one more than the excess logarithm. -/
theorem UnitOffsetTwoExcessLog (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : p.D.natAbs = 2) (n : ℤ) (hn : p.C.natAbs < n.natAbs) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t : ℕ, t ≤ Nat.log 2 (n.natAbs - p.C.natAbs) + 1 ∧
      (Iterate (FirstReturn p hhit) t n).natAbs ≤ p.C.natAbs := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let N := p.C.natAbs
  suffices ∀ e : ℕ, ∀ x : ℤ, x.natAbs = N + e → 0 < e →
      ∃ t : ℕ, t ≤ Nat.log 2 e + 1 ∧ (Iterate H t x).natAbs ≤ N by
    exact this (n.natAbs - N) n (by omega) (by omega)
  intro e
  induction e using Nat.strongRecOn with
  | ind e ih =>
    {
      intro x hx he
      have havg := UnitOffsetTwoExcess p hQ hcop hd x (by omega)
      by_cases hshell : (H x).natAbs ≤ N
      · {
          refine ⟨1, by omega, ?_⟩
          simpa [Iterate] using hshell
        }
      · {
          have he' : (H x).natAbs = N + ((H x).natAbs - N) := by omega
          have hlt : (H x).natAbs - N < e := by omega
          obtain ⟨t, ht, hsmall⟩ :=
            ih ((H x).natAbs - N) hlt (H x) he' (by omega)
          refine ⟨t + 1, ?_, ?_⟩
          · {
              have htwo : 2 * ((H x).natAbs - N) ≤ e := by omega
              have hlog : Nat.log 2 ((H x).natAbs - N) + 1 ≤ Nat.log 2 e := by
                have hpow :=
                  Nat.pow_log_le_self 2 (by omega : 1 ≤ (H x).natAbs - N)
                have hcmp : 2 ^ (Nat.log 2 ((H x).natAbs - N) + 1) ≤ e := by
                  rw [Nat.pow_succ]
                  omega
                exact Nat.le_log_of_pow_le (by decide) hcmp
              omega
            }
          · {
              rw [Iterate]
              simpa [IterateAdd] using hsmall
            }
        }
    }

/-- If `|n|≤2^k`, a `|d|=2` return reaches absolute value at most `1` in `k` steps. -/
theorem UnitOffsetTwoPower (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : p.D.natAbs = 2) (hc : p.C.natAbs = 1) (n : ℤ) (k : ℕ)
    (hk : n.natAbs ≤ 2 ^ k) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t : ℕ, t ≤ k ∧ (Iterate (FirstReturn p hhit) t n).natAbs ≤ 1 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  induction k generalizing n with
  | zero => {
      refine ⟨0, le_rfl, ?_⟩
      simpa [Iterate] using hk
    }
  | succ k ih => {
      by_cases hsmall : n.natAbs ≤ 1
      · {
          exact ⟨0, Nat.zero_le _, by simpa [Iterate] using hsmall⟩
        }
      · {
          have hhalf := UnitOffsetTwoHalves p hQ hcop hd hc n
          have hnext : (H n).natAbs ≤ 2 ^ k := by
            have : n.natAbs + 1 ≤ 2 ^ (k + 1) + 1 := by omega
            omega
          obtain ⟨t, ht, habs⟩ := ih (H n) hnext
          refine ⟨t + 1, ?_, ?_⟩
          · {
              omega
            }
          · {
              simpa [Iterate, Nat.add_comm, IterateAdd] using habs
            }
        }
    }

/-- A `|d|=2` return reaches absolute value at most `1` within `log2|n|+1` steps. -/
theorem UnitOffsetTwoLog (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : p.D.natAbs = 2) (hc : p.C.natAbs = 1) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t : ℕ, t ≤ Nat.log 2 n.natAbs + 1 ∧
      (Iterate (FirstReturn p hhit) t n).natAbs ≤ 1 := by
  have hpow : n.natAbs < 2 ^ (Nat.log 2 n.natAbs + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) n.natAbs
  have hk : n.natAbs ≤ 2 ^ (Nat.log 2 n.natAbs + 1) := Nat.le_of_lt hpow
  exact UnitOffsetTwoPower p hQ hcop hd hc n _ hk

/-- For `(1,1,2)`, every nonnegative seed meets the halving bound exactly. -/
theorem OneTwoNonnegExact (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2) (n : ℤ) (hn : 0 ≤ n) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    H n = (n + 1) / 2 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hclosed := (OneOffsetClosed p hQ hC (by rw [hD]; decide) n).1
    (by rw [hD]; omega)
  rw [H, hclosed]
  have hnat : n = (n.natAbs : ℤ) := by omega
  rw [hnat]
  have hdiv : (-((n.natAbs : ℤ))) / 2 =
      -(((n.natAbs + 1 : ℕ) : ℤ) / 2) := by
    cases Nat.even_or_odd n.natAbs with
    | inl he => {
        obtain ⟨q, hq⟩ := he
        have : (n.natAbs : ℤ) = 2 * q := by omega
        omega
      }
    | inr ho => {
        obtain ⟨q, hq⟩ := ho
        have : (n.natAbs : ℤ) = 2 * q + 1 := by omega
        omega
      }
  rw [hdiv]
  ring

/-- The nonnegative `(1,1,2)` return iterates to `⌈n/2^k⌉`. -/
theorem OneTwoIterate (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2) (n : ℤ) (hn : 0 ≤ n)
    (k : ℕ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    Iterate H k n = (((n.natAbs + 2 ^ k - 1) / 2 ^ k : ℕ) : ℤ) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  induction k generalizing n with
  | zero => {
      have : n = (n.natAbs : ℤ) := by omega
      simp [Iterate, this]
    }
  | succ k ih => {
      have hstep := OneTwoNonnegExact p hQ hC hD n hn
      have hnext : 0 ≤ H n := by
        rw [hstep]
        omega
      have hih := ih (H n) hnext
      have habs : (H n).natAbs = (n.natAbs + 1) / 2 := by
        rw [hstep, Int.natAbs_of_nonneg hnext]
        have : n = (n.natAbs : ℤ) := by omega
        rw [this]
        exact Int.natAbs_ediv_nat (n.natAbs + 1) 2
      rw [Function.iterate_succ_apply' H k n, hih, habs]
      -- The ceiling identity `(a+2^{k+1}-1)/2^{k+1} = (((a+1)/2)+2^k-1)/2^k`.
      have hceil : (n.natAbs + 2 ^ (k + 1) - 1) / 2 ^ (k + 1) =
          ((n.natAbs + 1) / 2 + 2 ^ k - 1) / 2 ^ k := by
        have hm : 0 < 2 ^ k := Nat.two_pow_pos k
        cases Nat.even_or_odd n.natAbs with
        | inl he => {
            obtain ⟨b, hb⟩ := he
            have hb' : n.natAbs = 2 * b := by rw [hb]; ring
            rw [hb', Nat.pow_succ]
            omega
          }
        | inr ho => {
            obtain ⟨b, hb⟩ := ho
            have hb' : n.natAbs = 2 * b + 1 := by rw [hb]; ring
            rw [hb', Nat.pow_succ]
            omega
          }
      exact congrArg (fun t : ℕ => (t : ℤ)) hceil
    }

/-- For `(1,1,2)` and `n≥1`, the first return to `1` is at time `⌈log2 n⌉`. -/
theorem OneTwoTime (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2) (n : ℤ) (hn : 1 ≤ n) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    Iterate H (Nat.clog 2 n.natAbs) n = 1 ∧
      ∀ t : ℕ, Iterate H t n = 1 → Nat.clog 2 n.natAbs ≤ t := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hpos : 0 ≤ n := le_trans (by decide : (0 : ℤ) ≤ 1) hn
  have hone : 1 ≤ n.natAbs := by omega
  have hform := fun k : ℕ => OneTwoIterate p hQ hC hD n hpos k
  have hiff : ∀ k : ℕ,
      Iterate H k n = 1 ↔ n.natAbs ≤ 2 ^ k := by
    intro k
    rw [hform k]
    have hdiv : 0 < 2 ^ k := Nat.two_pow_pos k
    constructor
    · {
        intro h
        have hnat : (n.natAbs + 2 ^ k - 1) / 2 ^ k = 1 := by
          exact Int.ofNat_inj.mp h
        omega
      }
    · {
        intro hk
        have hnat : (n.natAbs + 2 ^ k - 1) / 2 ^ k = 1 := by omega
        exact congrArg (fun t : ℕ => (t : ℤ)) hnat
      }
  refine ⟨?_, ?_⟩
  · {
      rw [hiff]
      exact Nat.le_pow_clog (by decide : 1 < 2) hone
    }
  · {
      intro t ht
      have hle := (hiff t).mp ht
      exact Nat.clog_le_of_le_pow (by decide : 1 < 2) hone hle
    }

/-- For `(1,1,2)`, a nonpositive seed returns `−⌊|n|/2⌋`. -/
theorem OneTwoNonposExact (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2) (n : ℤ) (hn : n ≤ 0) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    H n = -((n.natAbs : ℤ) / 2) ∧ (H n).natAbs = n.natAbs / 2 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hclosed := (OneOffsetClosed p hQ hC (by rw [hD]; decide) n).1
    (by rw [hD]; omega)
  have hneg : -n = (n.natAbs : ℤ) := by omega
  have hform : H n = -((n.natAbs : ℤ) / 2) := by
    rw [H, hclosed, hneg]
  refine ⟨hform, ?_⟩
  rw [hform, Int.natAbs_neg]
  have : 0 ≤ ((n.natAbs : ℤ) / 2) := by omega
  rw [Int.natAbs_of_nonneg this]
  exact Int.natAbs_ediv_nat (n.natAbs) 2

/-- For `(1,1,2)`, the absolute return is `( |n|+1)/2` or `|n|/2` by sign. -/
theorem OneTwoAbsExact (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    (0 ≤ n → (H n).natAbs = (n.natAbs + 1) / 2) ∧
      (n ≤ 0 → (H n).natAbs = n.natAbs / 2) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  constructor
  · {
      intro hn
      have hform := OneTwoNonnegExact p hQ hC hD n hn
      have hnonneg : 0 ≤ (n + 1) / 2 := by omega
      rw [H, hform, Int.natAbs_of_nonneg hnonneg]
      exact Int.natAbs_ediv_nat (n.natAbs + 1) 2
    }
  · {
      intro hn
      exact (OneTwoNonposExact p hQ hC hD n hn).2
    }

/-- For `(1,1,-2)`, the return is the negative of the `(1,1,2)` formula. -/
theorem OneNegTwoExact (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = -2) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    (0 ≤ n → H n = -((n.natAbs + 1 : ℕ) : ℤ) / 2) ∧
      (n ≤ 0 → H n = (n.natAbs : ℤ) / 2) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hclosed := (OneOffsetClosed p hQ hC (by rw [hD]; decide) n).2
    (by rw [hD]; omega)
  constructor
  · {
      intro hn
      have hnat : -n = -((n.natAbs : ℤ)) := by omega
      rw [H, hclosed, hnat]
      cases Nat.even_or_odd n.natAbs with
      | inl he => {
          obtain ⟨q, hq⟩ := he
          have : (n.natAbs : ℤ) = 2 * q := by omega
          omega
        }
      | inr ho => {
          obtain ⟨q, hq⟩ := ho
          have : (n.natAbs : ℤ) = 2 * q + 1 := by omega
          omega
        }
    }
  · {
      intro hn
      have hnat : -n = (n.natAbs : ℤ) := by omega
      rw [H, hclosed, hnat]
    }

/-- For `(1,1,-2)` and `n≥0`, two returns send `n` to `⌊(n+1)/4⌋`. -/
theorem OneNegTwoTwoStep (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = -2) (n : ℤ) (hn : 0 ≤ n) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    H n = -(((n.natAbs + 1) / 2 : ℕ) : ℤ) ∧
      H (H n) = (((n.natAbs + 1) / 4 : ℕ) : ℤ) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hexact := OneNegTwoExact p hQ hC hD n
  have hfirst : H n = -(((n.natAbs + 1) / 2 : ℕ) : ℤ) := by
    have hform := hexact.1 hn
    rw [H, hform]
    exact Int.natAbs_ediv_nat (n.natAbs + 1) 2 ▸ rfl
  refine ⟨hfirst, ?_⟩
  have hneg : H n ≤ 0 := by
    rw [hfirst]
    omega
  have hsecond := (OneNegTwoExact p hQ hC hD (H n)).2 hneg
  rw [H, hsecond, hfirst, Int.natAbs_neg]
  have hnonneg : 0 ≤ (((n.natAbs + 1) / 2 : ℕ) : ℤ) := by omega
  rw [Int.natAbs_of_nonneg hnonneg]
  have hdiv : ((n.natAbs + 1) / 2) / 2 = (n.natAbs + 1) / 4 := by
    omega
  exact congrArg (fun t : ℕ => (t : ℤ)) hdiv

/-- After `2t` returns of `(1,1,-2)`, a nonnegative seed is `(n+(4^t-1)/3)/4^t`. -/
theorem OneNegTwoEvenIterate (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = -2) (n : ℤ) (hn : 0 ≤ n)
    (t : ℕ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    Iterate H (2 * t) n =
      (((n.natAbs + (4 ^ t - 1) / 3) / 4 ^ t : ℕ) : ℤ) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  induction t generalizing n with
  | zero => {
      have : n = (n.natAbs : ℤ) := by omega
      simp [Iterate, this]
    }
  | succ t ih => {
      have htwo := OneNegTwoTwoStep p hQ hC hD n hn
      have hnext : 0 ≤ H (H n) := by
        rw [htwo.2]
        omega
      have hih := ih (H (H n)) hnext
      have hidx : 2 * (t + 1) = 2 * t + 2 := by omega
      rw [hidx, Function.iterate_add_apply, hih, htwo.2]
      have hnum : (H (H n)).natAbs = (n.natAbs + 1) / 4 := by
        rw [htwo.2]
        exact Int.natAbs_natCast _
      rw [hnum]
      have hgeom : (4 ^ (t + 1) - 1) / 3 =
          4 ^ t + (4 ^ t - 1) / 3 := by
        have hpow : 4 ^ (t + 1) = 4 * 4 ^ t := Nat.pow_succ'
        have hdiv3 : 3 ∣ 4 ^ t - 1 := by
          have : 4 ^ t % 3 = 1 := by
            induction t with
            | zero => {
                simp
              }
            | succ t iht => {
                rw [Nat.pow_succ, Nat.mul_mod, iht]
                decide
              }
          omega
        omega
      have hceil : ((n.natAbs + 1) / 4 + (4 ^ t - 1) / 3) / 4 ^ t =
          (n.natAbs + (4 ^ (t + 1) - 1) / 3) / 4 ^ (t + 1) := by
        rw [hgeom, Nat.pow_succ]
        omega
      exact congrArg (fun s : ℕ => (s : ℤ)) hceil.symm
    }

/-- `3|n| ≤ 2·4^t` has a solution. -/
theorem TwoFourDominates (a : ℕ) : ∃ t : ℕ, 3 * a ≤ 2 * 4 ^ t := by
  refine ⟨a, ?_⟩
  induction a with
  | zero => {
      simp
    }
  | succ a ih => {
      have hpow : 4 ^ (a + 1) = 4 * 4 ^ a := Nat.pow_succ'
      omega
    }

/-- For `(1,1,-2)` and `n≥0`, the first zero is the least even time `2t` with
`3|n|≤2·4^t`. -/
theorem OneNegTwoFirstZero (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = -2) (n : ℤ) (hn : 0 ≤ n) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    let t := Nat.find (TwoFourDominates n.natAbs)
    Iterate H (2 * t) n = 0 ∧
      ∀ s : ℕ, s < 2 * t → Iterate H s n ≠ 0 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  let t := Nat.find (TwoFourDominates n.natAbs)
  have ht := Nat.find_spec (TwoFourDominates n.natAbs)
  have hform := OneNegTwoEvenIterate p hQ hC hD n hn t
  have hmod : ∀ u : ℕ, 4 ^ u % 3 = 1 := by
    intro u
    induction u with
    | zero => {
        simp
      }
    | succ u ihu => {
        rw [Nat.pow_succ, Nat.mul_mod, ihu]
        decide
      }
  have hzero : Iterate H (2 * t) n = 0 := by
    rw [hform]
    have : (n.natAbs + (4 ^ t - 1) / 3) / 4 ^ t = 0 := by
      have hdiv3 : 3 ∣ 4 ^ t - 1 := by
        have := hmod t
        omega
      omega
    exact congrArg (fun s : ℕ => (s : ℤ)) this
  refine ⟨hzero, ?_⟩
  intro s hs hhit
  have hposStep : ∀ m : ℤ, 0 < m → H m < 0 := by
    intro m hm
    have hformm := (OneNegTwoExact p hQ hC hD m).1 (le_of_lt hm)
    have hone : 1 ≤ (m.natAbs + 1) / 2 := by omega
    omega
  by_cases heven : ∃ u : ℕ, s = 2 * u
  · {
      obtain ⟨u, hu⟩ := heven
      have hlt : u < t := by omega
      have hfail := Nat.find_min (TwoFourDominates n.natAbs) hlt
      have huform := OneNegTwoEvenIterate p hQ hC hD n hn u
      rw [hu] at hhit
      rw [huform] at hhit
      have hne : (n.natAbs + (4 ^ u - 1) / 3) / 4 ^ u ≠ 0 := by
        have hdiv3 : 3 ∣ 4 ^ u - 1 := by
          have := hmod u
          omega
        omega
      exact hne (Int.ofNat_inj.mp hhit)
    }
  · {
      have hodd : ∃ u : ℕ, s = 2 * u + 1 := by omega
      obtain ⟨u, hu⟩ := hodd
      have huform := OneNegTwoEvenIterate p hQ hC hD n hn u
      have hult : u < t := by omega
      have hfail := Nat.find_min (TwoFourDominates n.natAbs) hult
      have hprev : 0 < Iterate H (2 * u) n := by
        rw [huform]
        have hne : (n.natAbs + (4 ^ u - 1) / 3) / 4 ^ u ≠ 0 := by
          have hdiv3 : 3 ∣ 4 ^ u - 1 := by
            have := hmod u
            omega
          omega
        omega
      have hneg := hposStep _ hprev
      have hstep : Iterate H s n = H (Iterate H (2 * u) n) := by
        rw [hu, Nat.add_comm, Function.iterate_add_apply]
      rw [hstep] at hhit
      omega
    }

/-- For `(1,1,-2)` and `n<0`, the first zero is one step after the first zero
of `⌊|n|/2⌋`. -/
theorem OneNegTwoNegativeFirstZero (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = -2) (n : ℤ) (hn : n < 0) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    let t := Nat.find (TwoFourDominates (n.natAbs / 2))
    Iterate H (1 + 2 * t) n = 0 ∧
      ∀ s : ℕ, s < 1 + 2 * t → Iterate H s n ≠ 0 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  let t := Nat.find (TwoFourDominates (n.natAbs / 2))
  have hnonpos : n ≤ 0 := le_of_lt hn
  have hhalf := (OneNegTwoExact p hQ hC hD n).2 hnonpos
  have hnonneg : 0 ≤ H n := by
    rw [hhalf]
    omega
  have htail := OneNegTwoFirstZero p hQ hC hD (H n) hnonneg
  have hstep0 : Iterate H (1 + 2 * t) n = Iterate H (2 * t) (H n) := by
    simpa [Iterate, Nat.add_comm] using IterateAdd H 1 (2 * t) n
  have hzero : Iterate H (1 + 2 * t) n = 0 := by
    rw [hstep0]
    simpa [t] using htail.1
  refine ⟨hzero, ?_⟩
  intro s hs hhit
  by_cases hs0 : s = 0
  · {
      rw [hs0, Iterate] at hhit
      omega
    }
  · {
      have hpred : s = 1 + (s - 1) := by omega
      have hmove : Iterate H s n = Iterate H (s - 1) (H n) := by
        rw [hpred]
        simpa [Iterate] using IterateAdd H 1 (s - 1) n
      have hsmall : s - 1 < 2 * t := by omega
      rw [hmove] at hhit
      exact htail.2 (s - 1) hsmall hhit
    }

/-- For `(1,1,-2)` and `n≥0`, time `2t+1` is `-⌈m/2⌉`, where `m` is time `2t`. -/
theorem OneNegTwoOddIterate (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = -2) (n : ℤ) (hn : 0 ≤ n)
    (t : ℕ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    let m := (n.natAbs + (4 ^ t - 1) / 3) / 4 ^ t
    Iterate H (2 * t + 1) n = -(((m + 1) / 2 : ℕ) : ℤ) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  let m := (n.natAbs + (4 ^ t - 1) / 3) / 4 ^ t
  have heven := OneNegTwoEvenIterate p hQ hC hD n hn t
  have hnonneg : 0 ≤ Iterate H (2 * t) n := by
    rw [heven]
    omega
  have hstep : Iterate H (2 * t + 1) n = H (Iterate H (2 * t) n) := by
    simpa [Iterate, Nat.add_comm] using IterateAdd H (2 * t) 1 n
  have hform := (OneNegTwoExact p hQ hC hD (Iterate H (2 * t) n)).1 hnonneg
  rw [hstep, hform, heven, Int.natAbs_natCast]
  rfl

/-- For `(1,1,-2)` and `n<0`, later states are the formulas of `⌊|n|/2⌋`. -/
theorem OneNegTwoNegativeIterate (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = -2) (n : ℤ) (hn : n < 0)
    (t : ℕ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    let m := n.natAbs / 2
    Iterate H (1 + 2 * t) n =
        (((m + (4 ^ t - 1) / 3) / 4 ^ t : ℕ) : ℤ) ∧
      Iterate H (2 + 2 * t) n =
        -(((((m + (4 ^ t - 1) / 3) / 4 ^ t + 1) / 2 : ℕ) : ℤ) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  let m := n.natAbs / 2
  have hnonpos : n ≤ 0 := le_of_lt hn
  have hhalf := (OneNegTwoExact p hQ hC hD n).2 hnonpos
  have hnonneg : 0 ≤ H n := by
    rw [hhalf]
    omega
  have habs : (H n).natAbs = m := by
    rw [hhalf, Int.natAbs_of_nonneg hnonneg]
    exact Int.natAbs_ediv_nat n.natAbs 2
  have heven := OneNegTwoEvenIterate p hQ hC hD (H n) hnonneg t
  have hodd := OneNegTwoOddIterate p hQ hC hD (H n) hnonneg t
  have hshift : Iterate H (1 + 2 * t) n = Iterate H (2 * t) (H n) := by
    simpa [Iterate] using IterateAdd H 1 (2 * t) n
  have hshift2 : Iterate H (2 + 2 * t) n = Iterate H (2 * t + 1) (H n) := by
    have hidx : 2 + 2 * t = 1 + (2 * t + 1) := by omega
    rw [hidx]
    simpa [Iterate] using IterateAdd H 1 (2 * t + 1) n
  refine ⟨?_, ?_⟩
  · {
      rw [hshift, heven, habs]
    }
  · {
      rw [hshift2, hodd, habs]
    }

/-- An odd integer has `(n-1)/2 = n/2`. -/
theorem OddHalfShift (n : ℤ) (hodd : ¬ 2 ∣ n) : (n - 1) / 2 = n / 2 := by
  have hmod : n % 2 = 1 := by
    have hpair : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hpair with h0 | h1
    · {
        exact False.elim (hodd (Int.dvd_of_emod_eq_zero h0))
      }
    · {
        exact h1
      }
  have hdiv : n = 2 * (n / 2) + n % 2 := Int.ediv_add_emod n 2
  rw [hmod] at hdiv
  have : n - 1 = 2 * (n / 2) := by omega
  omega

/-- The `(1,-1,-2)` return is the sign reverse of `(1,1,-2)` at `-n`. -/
theorem NegOneNegTwoReverses (p q : Parameters)
    (hpQ : p.Q = 1) (hpC : p.C = -1) (hpD : p.D = -2)
    (hqQ : q.Q = 1) (hqC : q.C = 1) (hqD : q.D = -2) (n : ℤ) :
    let K := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
      (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
        fun j h => h.1)
    let H := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
      (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
        fun j h => h.1)
    K n = - H (-n) := by
  let K := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
    (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
      fun j h => h.1)
  let H := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
    (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
      fun j h => h.1)
  have hK := NegOneNegTwoExact p hpQ hpC hpD n
  by_cases hn : 0 ≤ n
  · {
      have hH := (OneNegTwoExact q hqQ hqC hqD (-n)).2 (by omega)
      have hneg : -n = -((n.natAbs : ℤ)) := by omega
      by_cases heven : 2 ∣ n
      · {
          rw [hK.1 heven, hH]
          have : n = (n.natAbs : ℤ) := by omega
          omega
        }
      · {
          rw [hK.2 heven, OddHalfShift n heven, hH]
          have : n = (n.natAbs : ℤ) := by omega
          omega
        }
    }
  · {
      have hpos : 0 ≤ -n := by omega
      have hH := (OneNegTwoExact q hqQ hqC hqD (-n)).1 hpos
      by_cases heven : 2 ∣ n
      · {
          rw [hK.1 heven, hH]
          omega
        }
      · {
          rw [hK.2 heven, OddHalfShift n heven, hH]
          omega
        }
    }

/-- Every `(1,-1,-2)` state is the sign reverse of the `(1,1,-2)` state of `-n`. -/
theorem NegOneNegTwoIterate (p q : Parameters)
    (hpQ : p.Q = 1) (hpC : p.C = -1) (hpD : p.D = -2)
    (hqQ : q.Q = 1) (hqC : q.C = 1) (hqD : q.D = -2) (n : ℤ) (t : ℕ) :
    let K := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
      (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
        fun j h => h.1)
    let H := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
      (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
        fun j h => h.1)
    Iterate K t n = - Iterate H t (-n) := by
  let K := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
    (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
      fun j h => h.1)
  let H := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
    (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
      fun j h => h.1)
  induction t generalizing n with
  | zero => {
      simp [Iterate]
    }
  | succ t ih => {
      have hstep : Iterate K (t + 1) n = K (Iterate K t n) := by
        simpa [Iterate] using IterateAdd K t 1 n
      have hH : Iterate H (t + 1) (-n) = H (Iterate H t (-n)) := by
        simpa [Iterate] using IterateAdd H t 1 (-n)
      rw [hstep, ih, hH]
      exact NegOneNegTwoReverses p q hpQ hpC hpD hqQ hqC hqD
        (- Iterate H t (-n))
    }

/-- The `(1,-1,2)` return is the sign reverse of `(1,1,2)` at `-n`. -/
theorem NegOneTwoReverses (p q : Parameters)
    (hpQ : p.Q = 1) (hpC : p.C = -1) (hpD : p.D = 2)
    (hqQ : q.Q = 1) (hqC : q.C = 1) (hqD : q.D = 2) (n : ℤ) :
    let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
      (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
        fun j h => h.1)
    let M := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
      (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
        fun j h => h.1)
    L n = - M (-n) := by
  let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
    (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
      fun j h => h.1)
  let M := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
    (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
      fun j h => h.1)
  have hL := NegOneTwoExact p hpQ hpC hpD n
  by_cases hn : 0 ≤ n
  · {
      have hM := OneTwoNonposExact q hqQ hqC hqD (-n) (by omega)
      by_cases heven : 2 ∣ n
      · {
          rw [hL.1 heven, hM.1]
          have : n = (n.natAbs : ℤ) := by omega
          omega
        }
      · {
          rw [hL.2 heven, OddHalfShift n heven, hM.1]
          have : n = (n.natAbs : ℤ) := by omega
          omega
        }
    }
  · {
      have hM := OneTwoNonnegExact q hqQ hqC hqD (-n) (by omega)
      by_cases heven : 2 ∣ n
      · {
          rw [hL.1 heven, hM]
          omega
        }
      · {
          rw [hL.2 heven, OddHalfShift n heven, hM]
          omega
        }
    }

/-- Every `(1,-1,2)` state is the sign reverse of the `(1,1,2)` state of `-n`. -/
theorem NegOneTwoIterate (p q : Parameters)
    (hpQ : p.Q = 1) (hpC : p.C = -1) (hpD : p.D = 2)
    (hqQ : q.Q = 1) (hqC : q.C = 1) (hqD : q.D = 2) (n : ℤ) (t : ℕ) :
    let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
      (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
        fun j h => h.1)
    let M := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
      (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
        fun j h => h.1)
    Iterate L t n = - Iterate M t (-n) := by
  let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
    (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
      fun j h => h.1)
  let M := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
    (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
      fun j h => h.1)
  induction t generalizing n with
  | zero => {
      simp [Iterate]
    }
  | succ t ih => {
      have hstep : Iterate L (t + 1) n = L (Iterate L t n) := by
        simpa [Iterate] using IterateAdd L t 1 n
      have hM : Iterate M (t + 1) (-n) = M (Iterate M t (-n)) := by
        simpa [Iterate] using IterateAdd M t 1 (-n)
      rw [hstep, ih, hM]
      exact NegOneTwoReverses p q hpQ hpC hpD hqQ hqC hqD
        (- Iterate M t (-n))
    }

/-- For `(1,-1,2)` and `n≤-1`, the first visit to `-1` is at time `⌈log2 |n|⌉`. -/
theorem NegOneTwoTime (p q : Parameters)
    (hpQ : p.Q = 1) (hpC : p.C = -1) (hpD : p.D = 2)
    (hqQ : q.Q = 1) (hqC : q.C = 1) (hqD : q.D = 2)
    (n : ℤ) (hn : n ≤ -1) :
    let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
      (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
        fun j h => h.1)
    let M := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
      (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
        fun j h => h.1)
    Iterate L (Nat.clog 2 n.natAbs) n = -1 ∧
      ∀ t : ℕ, Iterate L t n = -1 → Nat.clog 2 n.natAbs ≤ t := by
  let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
    (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
      fun j h => h.1)
  let M := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
    (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
      fun j h => h.1)
  have hpos : 1 ≤ -n := by omega
  have htime := OneTwoTime q hqQ hqC hqD (-n) hpos
  have hrev := fun t : ℕ =>
    NegOneTwoIterate p q hpQ hpC hpD hqQ hqC hqD n t
  have habs : (-n).natAbs = n.natAbs := by
    rw [Int.natAbs_neg]
  refine ⟨?_, ?_⟩
  · {
      rw [hrev, habs]
      have := htime.1
      omega
    }
  · {
      intro t ht
      have hM : Iterate M t (-n) = 1 := by
        have hrevt := hrev t
        rw [hrevt] at ht
        omega
      have := htime.2 t hM
      omega
    }

/-- The first zero of `(1,-1,-2)` at `n` is the first zero of `(1,1,-2)` at `-n`. -/
theorem NegOneNegTwoFirstZero (p q : Parameters)
    (hpQ : p.Q = 1) (hpC : p.C = -1) (hpD : p.D = -2)
    (hqQ : q.Q = 1) (hqC : q.C = 1) (hqD : q.D = -2) (n : ℤ) :
    let K := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
      (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
        fun j h => h.1)
    let H := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
      (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
        fun j h => h.1)
    (n ≤ 0 →
      let t := Nat.find (TwoFourDominates n.natAbs)
      Iterate K (2 * t) n = 0 ∧
        ∀ s : ℕ, s < 2 * t → Iterate K s n ≠ 0) ∧
    (0 < n →
      let t := Nat.find (TwoFourDominates (n.natAbs / 2))
      Iterate K (1 + 2 * t) n = 0 ∧
        ∀ s : ℕ, s < 1 + 2 * t → Iterate K s n ≠ 0) := by
  let K := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
    (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
      fun j h => h.1)
  let H := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
    (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
      fun j h => h.1)
  have hrev := fun t : ℕ =>
    NegOneNegTwoIterate p q hpQ hpC hpD hqQ hqC hqD n t
  refine ⟨?_, ?_⟩
  · {
      intro hn
      have hzero := OneNegTwoFirstZero q hqQ hqC hqD (-n) (by omega)
      have habs : (-n).natAbs = n.natAbs := Int.natAbs_neg n
      constructor
      · {
          have := hrev (2 * Nat.find (TwoFourDominates n.natAbs))
          rw [habs] at hzero
          omega
        }
      · {
          intro s hs hhit
          have hrevS := hrev s
          rw [habs] at hzero
          have hH : Iterate H s (-n) = 0 := by omega
          exact hzero.2 s hs hH
        }
    }
  · {
      intro hn
      have hzero := OneNegTwoNegativeFirstZero q hqQ hqC hqD (-n) (by omega)
      have habs : (-n).natAbs = n.natAbs := Int.natAbs_neg n
      constructor
      · {
          have := hrev (1 + 2 * Nat.find (TwoFourDominates (n.natAbs / 2)))
          rw [habs] at hzero
          omega
        }
      · {
          intro s hs hhit
          have hrevS := hrev s
          rw [habs] at hzero
          have hH : Iterate H s (-n) = 0 := by omega
          exact hzero.2 s hs hH
        }
    }

/-- For `(1,-1,2)`, every return is `n/2`. -/
theorem NegOneTwoHalves (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = -1) (hD : p.D = 2) (n : ℤ) :
    let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    L n = n / 2 := by
  let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hL := NegOneTwoExact p hQ hC hD n
  by_cases heven : 2 ∣ n
  · {
      exact hL.1 heven
    }
  · {
      rw [hL.2 heven, OddHalfShift n heven]
    }

/-- For `(1,-1,2)`, the state at time `k` is `n/2^k`. -/
theorem NegOneTwoPow (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = -1) (hD : p.D = 2) (n : ℤ) (k : ℕ) :
    let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    Iterate L k n = n / (2 ^ k : ℤ) := by
  let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  induction k generalizing n with
  | zero => {
      simp [Iterate]
    }
  | succ k ih => {
      have hstep : Iterate L (k + 1) n = L (Iterate L k n) := by
        simpa [Iterate] using IterateAdd L k 1 n
      rw [hstep, NegOneTwoHalves p hQ hC hD, ih]
      have hpow : ((2 ^ (k + 1) : ℕ) : ℤ) = 2 * (2 ^ k : ℤ) := by
        rw [Nat.pow_succ]
        norm_cast
      rw [hpow]
      exact Int.ediv_ediv n 2 (2 ^ k : ℤ)
    }

/-- For `(1,-1,2)` and `n≥1`, time `⌊log2 n⌋` is `1` and the next time is `0`. -/
theorem NegOneTwoPositiveLog (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = -1) (hD : p.D = 2) (n : ℤ) (hn : 1 ≤ n) :
    let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    let k := Nat.log 2 n.natAbs
    Iterate L k n = 1 ∧ Iterate L (k + 1) n = 0 ∧
      ∀ t : ℕ, t < k → Iterate L t n ≠ 1 ∧ Iterate L t n ≠ 0 := by
  let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  let k := Nat.log 2 n.natAbs
  have hone : 1 ≤ n.natAbs := by omega
  have hle : 2 ^ k ≤ n.natAbs := Nat.pow_log_le_self 2 hone
  have hlt : n.natAbs < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) hone
  have hcast : n = (n.natAbs : ℤ) := by omega
  have honev : Iterate L k n = 1 := by
    rw [NegOneTwoPow p hQ hC hD n k, hcast]
    have : ((n.natAbs : ℤ) / (2 ^ k : ℤ)) = 1 := by
      have hden : (0 : ℤ) < (2 ^ k : ℤ) := by exact_mod_cast Nat.two_pow_pos k
      omega
    exact this
  have hzerov : Iterate L (k + 1) n = 0 := by
    rw [NegOneTwoPow p hQ hC hD n (k + 1), hcast]
    have : ((n.natAbs : ℤ) / (2 ^ (k + 1) : ℤ)) = 0 := by
      omega
    exact this
  refine ⟨honev, hzerov, ?_⟩
  intro t ht
  have hform := NegOneTwoPow p hQ hC hD n t
  have hgt : 1 < ((n.natAbs : ℤ) / (2 ^ t : ℤ)) := by
    have hpow : 2 ^ (t + 1) ≤ n.natAbs := by
      have hlog : t + 1 ≤ k := by omega
      exact Nat.pow_le_pow_right (by decide) hlog ▸ hle ▸ le_trans
        (Nat.pow_le_pow_right (by decide) hlog) hle
    omega
  constructor
  · {
      rw [hform, hcast]
      omega
    }
  · {
      rw [hform, hcast]
      omega
    }

/-- For `(1,1,2)` and `n≤-1`, time `⌊log2 |n|⌋` is `-1` and the next time is `0`. -/
theorem OneTwoNegativeLog (p q : Parameters)
    (hpQ : p.Q = 1) (hpC : p.C = 1) (hpD : p.D = 2)
    (hqQ : q.Q = 1) (hqC : q.C = -1) (hqD : q.D = 2)
    (n : ℤ) (hn : n ≤ -1) :
    let M := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
      (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
        fun j h => h.1)
    let L := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
      (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
        fun j h => h.1)
    let k := Nat.log 2 n.natAbs
    Iterate M k n = -1 ∧ Iterate M (k + 1) n = 0 ∧
      ∀ t : ℕ, t < k → Iterate M t n ≠ -1 ∧ Iterate M t n ≠ 0 := by
  let M := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
    (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
      fun j h => h.1)
  let L := FirstReturn q (fun x => (UnitCoprimeIsSmall q hqQ
    (by rw [hqC]; simp [Nat.gcd_one_left]) (by rw [hqD]; decide) x).imp
      fun j h => h.1)
  let k := Nat.log 2 n.natAbs
  have hpos : 1 ≤ -n := by omega
  have habs : (-n).natAbs = n.natAbs := Int.natAbs_neg n
  have hlog := NegOneTwoPositiveLog q hqQ hqC hqD (-n) hpos
  have hrev := fun t : ℕ =>
    NegOneTwoIterate q p hqQ hqC hqD hpQ hpC hpD (-n) t
  -- `NegOneTwoIterate` reverses `L` at `-n` into `M` at `n`.
  have hflip : ∀ t : ℕ, Iterate M t n = - Iterate L t (-n) := by
    intro t
    have hrevt := NegOneTwoIterate q p hqQ hqC hqD hpQ hpC hpD (-n) t
    have : Iterate L t (-n) = - Iterate M t (-(-n)) := hrevt
    omega
  refine ⟨?_, ?_, ?_⟩
  · {
      rw [hflip, habs]
      have := hlog.1
      omega
    }
  · {
      rw [hflip, habs]
      have := hlog.2.1
      omega
    }
  · {
      intro t ht
      have hnot := hlog.2.2 t (by omega)
      constructor
      · {
          intro hhit
          have hL : Iterate L t (-n) = 1 := by
            have := hflip t
            omega
          exact hnot.1 hL
        }
      · {
          intro hhit
          have hL : Iterate L t (-n) = 0 := by
            have := hflip t
            omega
          exact hnot.2 hL
        }
    }

/-- The fixed points of `(1,1,2)` are `0` and `1`. -/
theorem OneTwoFixed (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    H n = n ↔ n = 0 ∨ n = 1 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  constructor
  · {
      intro hfix
      by_cases hn : 0 ≤ n
      · {
          have hform := OneTwoNonnegExact p hQ hC hD n hn
          rw [hform] at hfix
          have : n = (n.natAbs : ℤ) := by omega
          omega
        }
      · {
          have hform := (OneTwoNonposExact p hQ hC hD n (by omega)).1
          rw [hform] at hfix
          omega
        }
    }
  · {
      intro h
      rcases h with h0 | h1
      · {
          have hform := OneTwoNonnegExact p hQ hC hD n (by omega)
          omega
        }
      · {
          have hform := OneTwoNonnegExact p hQ hC hD n (by omega)
          omega
        }
    }

/-- The fixed points of `(1,-1,2)` are `0` and `-1`. -/
theorem NegOneTwoFixed (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = -1) (hD : p.D = 2) (n : ℤ) :
    let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    L n = n ↔ n = 0 ∨ n = -1 := by
  let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hform := NegOneTwoHalves p hQ hC hD n
  constructor
  · {
      intro hfix
      rw [hform] at hfix
      have hdiv : n = 2 * (n / 2) + n % 2 := Int.ediv_add_emod n 2
      have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
      omega
    }
  · {
      intro h
      rw [hform]
      omega
    }

/-- The only fixed point of `(1,1,-2)` is `0`. -/
theorem OneNegTwoFixed (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = -2) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    H n = n ↔ n = 0 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  constructor
  · {
      intro hfix
      by_cases hn : 0 ≤ n
      · {
          have hform := (OneNegTwoExact p hQ hC hD n).1 hn
          rw [hform] at hfix
          omega
        }
      · {
          have hform := (OneNegTwoExact p hQ hC hD n).2 (by omega)
          rw [hform] at hfix
          omega
        }
    }
  · {
      intro h0
      have hform := (OneNegTwoExact p hQ hC hD n).1 (by omega)
      omega
    }

/-- The only fixed point of `(1,-1,-2)` is `0`. -/
theorem NegOneNegTwoFixed (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = -1) (hD : p.D = -2) (n : ℤ) :
    let K := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    K n = n ↔ n = 0 := by
  let K := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hK := NegOneNegTwoExact p hQ hC hD n
  constructor
  · {
      intro hfix
      by_cases heven : 2 ∣ n
      · {
          rw [hK.1 heven] at hfix
          have hdiv : n = 2 * (n / 2) + n % 2 := Int.ediv_add_emod n 2
          omega
        }
      · {
          rw [hK.2 heven, OddHalfShift n heven] at hfix
          have hdiv : n = 2 * (n / 2) + n % 2 := Int.ediv_add_emod n 2
          omega
        }
    }
  · {
      intro h0
      have hform := hK.1 (by omega)
      omega
    }

/-- A fixed point stays fixed. -/
theorem IterateStays (H : ℤ → ℤ) (a : ℤ) (h : H a = a) (t : ℕ) :
    Iterate H t a = a := by
  induction t with
  | zero => {
      simp [Iterate]
    }
  | succ t ih => {
      have hstep : Iterate H (t + 1) a = H (Iterate H t a) := by
        simpa [Iterate] using IterateAdd H t 1 a
      rw [hstep, ih, h]
    }

/-- Ceiling logarithms sit inside the tripled logarithm. -/
theorem ClogWithinLog (a : ℕ) (ha : 1 ≤ a) :
    Nat.clog 2 a ≤ Nat.log 2 (3 * a) + 1 := by
  have hm : 1 ≤ 3 * a := by omega
  have hlt : 3 * a < 2 ^ (Nat.log 2 (3 * a) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) hm
  have hpow : a ≤ 2 ^ (Nat.log 2 (3 * a) + 1) := by omega
  exact (Nat.clog_le_iff (by decide) ha).mpr hpow

/-- The rounded half-logarithm dominates the base-four witness. -/
theorem LogHalfWitness (a : ℕ) (ha : 1 ≤ a) :
    3 * a ≤ 2 * 4 ^ ((Nat.log 2 (3 * a) + 1) / 2) := by
  let k := Nat.log 2 (3 * a)
  have hm : 1 ≤ 3 * a := by omega
  have hlt : 3 * a < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) hm
  have h4 : 4 = 2 ^ 2 := by decide
  rcases Nat.even_or_odd k with he | ho
  · {
      have hk : (k + 1) / 2 = k / 2 := by omega
      have hsplit : k = 2 * (k / 2) := by omega
      have hpow : 4 ^ (k / 2) = 2 ^ k := by
        rw [h4, ← Nat.pow_mul, hsplit]
      omega
    }
  · {
      have hk : (k + 1) / 2 = k / 2 + 1 := by omega
      have hsub : 2 * (k / 2) = k - 1 := by omega
      have hpow : 4 ^ (k / 2) = 2 ^ (k - 1) := by
        rw [h4, ← Nat.pow_mul, hsub]
      have ht : 4 ^ (k / 2 + 1) = 2 ^ (k + 1) := by
        rw [Nat.pow_succ, hpow]
        have : 4 * 2 ^ (k - 1) = 2 ^ (k + 1) := by omega
        exact this
      omega
    }

/-- The least base-four time is at most the tripled logarithm. -/
theorem FindWithinLog (a : ℕ) :
    2 * Nat.find (TwoFourDominates a) ≤ Nat.log 2 (3 * a) + 1 := by
  by_cases ha : a = 0
  · {
      have h0 : Nat.find (TwoFourDominates a) = 0 := by
        rw [ha]
        apply Nat.eq_zero_of_le_zero
        exact Nat.find_min' (TwoFourDominates 0) (by simp)
      omega
    }
  · {
      have ha1 : 1 ≤ a := by omega
      have hle : Nat.find (TwoFourDominates a) ≤
          (Nat.log 2 (3 * a) + 1) / 2 :=
        Nat.find_min' (TwoFourDominates a) (LogHalfWitness a ha1)
      omega
    }

/-- The shifted half-time is at most one more than the logarithm. -/
theorem HalfFindWithinLog (a : ℕ) :
    1 + 2 * Nat.find (TwoFourDominates (a / 2)) ≤
      Nat.log 2 (3 * a) + 1 := by
  by_cases hzero : a / 2 = 0
  · {
      have hfind : Nat.find (TwoFourDominates (a / 2)) = 0 := by
        rw [hzero]
        apply Nat.eq_zero_of_le_zero
        exact Nat.find_min' (TwoFourDominates 0) (by simp)
      by_cases ha : a = 0
      · {
          omega
        }
      · {
          have hle : 2 ^ 1 ≤ 3 * a := by omega
          have hlog : 1 ≤ Nat.log 2 (3 * a) :=
            Nat.le_log_of_pow_le (by decide) hle
          omega
        }
    }
  · {
      have hhalf := FindWithinLog (a / 2)
      have hlt : 3 * a < 2 ^ (Nat.log 2 (3 * a) + 1) :=
        Nat.lt_pow_succ_log_self (by decide) (by omega)
      have hbelow : 3 * (a / 2) < 2 ^ Nat.log 2 (3 * a) := by omega
      have hdrop : Nat.log 2 (3 * (a / 2)) < Nat.log 2 (3 * a) :=
        Nat.log_lt_of_lt_pow (by decide) (by omega) hbelow
      omega
    }

/-- Every `(1,1,2)` orbit is constant at `0` or `1` by the logarithmic time. -/
theorem OneTwoConstant (p q : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2)
    (hqQ : q.Q = 1) (hqC : q.C = -1) (hqD : q.D = 2) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    ∃ t : ℕ, t ≤ Nat.log 2 (3 * n.natAbs) + 1 ∧
      Iterate H t n = Iterate H (t + 1) n ∧
      (Iterate H t n = 0 ∨ Iterate H t n = 1) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hfix0 : H 0 = 0 := (OneTwoFixed p hQ hC hD 0).2 (Or.inl rfl)
  have hfix1 : H 1 = 1 := (OneTwoFixed p hQ hC hD 1).2 (Or.inr rfl)
  by_cases hn : 1 ≤ n
  · {
      let t := Nat.clog 2 n.natAbs
      have htime := (OneTwoTime p hQ hC hD n hn).1
      have hnext : Iterate H (t + 1) n = Iterate H t n := by
        have hstep : Iterate H (t + 1) n = H (Iterate H t n) := by
          simpa [Iterate] using IterateAdd H t 1 n
        rw [hstep, htime, hfix1]
      have hbound := ClogWithinLog n.natAbs (by omega)
      exact ⟨t, hbound, hnext.symm, Or.inr htime⟩
    }
  · {
      by_cases hneg : n ≤ -1
      · {
          let t := Nat.log 2 n.natAbs + 1
          have hzero :=
            (OneTwoNegativeLog p q hQ hC hD hqQ hqC hqD n hneg).2.1
          have hnext : Iterate H (t + 1) n = 0 := by
            have hstep : Iterate H (t + 1) n = H (Iterate H t n) := by
              simpa [Iterate] using IterateAdd H t 1 n
            -- The logarithm in `OneTwoNegativeLog` is `Nat.log`, so `t` matches.
            rw [hstep]
            have : Iterate H t n = 0 := by
              simpa [t] using hzero
            rw [this, hfix0]
          have hhit : Iterate H t n = 0 := by simpa [t] using hzero
          have hbound : t ≤ Nat.log 2 (3 * n.natAbs) + 1 := by
            have hmono : Nat.log 2 n.natAbs ≤ Nat.log 2 (3 * n.natAbs) :=
              Nat.log_mono_right (by omega)
            omega
          exact ⟨t, hbound, by rw [hhit, hnext], Or.inl hhit⟩
        }
      · {
          have h0 : n = 0 := by omega
          have hhit : Iterate H 0 n = 0 := by simp [Iterate, h0]
          have hnext : Iterate H 1 n = 0 := by
            simp [Iterate, h0, hfix0]
          exact ⟨0, by omega, by rw [hhit, hnext], Or.inl hhit⟩
        }
    }

/-- Every `(1,-1,2)` orbit is constant at `0` or `-1` by the logarithmic time. -/
theorem NegOneTwoConstant (p q : Parameters)
    (hpQ : p.Q = 1) (hpC : p.C = -1) (hpD : p.D = 2)
    (hqQ : q.Q = 1) (hqC : q.C = 1) (hqD : q.D = 2) (n : ℤ) :
    let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
      (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
        fun j h => h.1)
    ∃ t : ℕ, t ≤ Nat.log 2 (3 * n.natAbs) + 1 ∧
      Iterate L t n = Iterate L (t + 1) n ∧
      (Iterate L t n = 0 ∨ Iterate L t n = -1) := by
  let L := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
    (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
      fun j h => h.1)
  have hfix0 : L 0 = 0 := (NegOneTwoFixed p hpQ hpC hpD 0).2 (Or.inl rfl)
  have hfix1 : L (-1) = -1 :=
    (NegOneTwoFixed p hpQ hpC hpD (-1)).2 (Or.inr rfl)
  by_cases hn : 1 ≤ n
  · {
      let t := Nat.log 2 n.natAbs + 1
      have hzero := (NegOneTwoPositiveLog p hpQ hpC hpD n hn).2.1
      have hhit : Iterate L t n = 0 := by simpa [t] using hzero
      have hnext : Iterate L (t + 1) n = 0 := by
        have hstep : Iterate L (t + 1) n = L (Iterate L t n) := by
          simpa [Iterate] using IterateAdd L t 1 n
        rw [hstep, hhit, hfix0]
      have hbound : t ≤ Nat.log 2 (3 * n.natAbs) + 1 := by
        have hmono : Nat.log 2 n.natAbs ≤ Nat.log 2 (3 * n.natAbs) :=
          Nat.log_mono_right (by omega)
        omega
      exact ⟨t, hbound, by rw [hhit, hnext], Or.inl hhit⟩
    }
  · {
      by_cases hneg : n ≤ -1
      · {
          let t := Nat.clog 2 n.natAbs
          have htime :=
            (NegOneTwoTime p q hpQ hpC hpD hqQ hqC hqD n hneg).1
          have hnext : Iterate L (t + 1) n = -1 := by
            have hstep : Iterate L (t + 1) n = L (Iterate L t n) := by
              simpa [Iterate] using IterateAdd L t 1 n
            rw [hstep, htime, hfix1]
          have hbound := ClogWithinLog n.natAbs (by omega)
          exact ⟨t, hbound, by rw [htime, hnext], Or.inr htime⟩
        }
      · {
          have h0 : n = 0 := by omega
          have hhit : Iterate L 0 n = 0 := by simp [Iterate, h0]
          have hnext : Iterate L 1 n = 0 := by simp [Iterate, h0, hfix0]
          exact ⟨0, by omega, by rw [hhit, hnext], Or.inl hhit⟩
        }
    }

/-- Every `(1,1,-2)` orbit is constant at `0` by the logarithmic time. -/
theorem OneNegTwoConstant (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = -2) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    ∃ t : ℕ, t ≤ Nat.log 2 (3 * n.natAbs) + 1 ∧
      Iterate H t n = 0 ∧ Iterate H (t + 1) n = 0 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hfix0 : H 0 = 0 := (OneNegTwoFixed p hQ hC hD 0).2 rfl
  by_cases hn : 0 ≤ n
  · {
      let t := 2 * Nat.find (TwoFourDominates n.natAbs)
      have hzero := (OneNegTwoFirstZero p hQ hC hD n hn).1
      have hhit : Iterate H t n = 0 := by simpa [t] using hzero
      have hnext : Iterate H (t + 1) n = 0 := by
        have hstep : Iterate H (t + 1) n = H (Iterate H t n) := by
          simpa [Iterate] using IterateAdd H t 1 n
        rw [hstep, hhit, hfix0]
      have hbound : t ≤ Nat.log 2 (3 * n.natAbs) + 1 := by
        have hle := FindWithinLog n.natAbs
        omega
      exact ⟨t, hbound, hhit, hnext⟩
    }
  · {
      let t := 1 + 2 * Nat.find (TwoFourDominates (n.natAbs / 2))
      have hzero := (OneNegTwoNegativeFirstZero p hQ hC hD n (by omega)).1
      have hhit : Iterate H t n = 0 := by simpa [t] using hzero
      have hnext : Iterate H (t + 1) n = 0 := by
        have hstep : Iterate H (t + 1) n = H (Iterate H t n) := by
          simpa [Iterate] using IterateAdd H t 1 n
        rw [hstep, hhit, hfix0]
      have hbound := HalfFindWithinLog n.natAbs
      exact ⟨t, by simpa [t] using hbound, hhit, hnext⟩
    }

/-- For `(1,1,-2)`, the seed `1` meets the logarithmic bound. -/
theorem OneNegTwoBoundSharp (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = -2) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    Nat.find (TwoFourDominates 1) = 1 ∧
      Nat.log 2 (3 * 1) + 1 = 2 ∧
      Iterate H 2 (1 : ℤ) = 0 ∧ Iterate H 1 (1 : ℤ) ≠ 0 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hlog : Nat.log 2 3 = 1 := by decide
  have hle : Nat.find (TwoFourDominates 1) ≤ 1 :=
    Nat.find_min' (TwoFourDominates 1) (by decide : 3 * 1 ≤ 2 * 4 ^ 1)
  have hne : Nat.find (TwoFourDominates 1) ≠ 0 := by
    intro h0
    have hspec := Nat.find_spec (TwoFourDominates 1)
    rw [h0] at hspec
    omega
  have hfind : Nat.find (TwoFourDominates 1) = 1 := by omega
  have hzero := OneNegTwoFirstZero p hQ hC hD (1 : ℤ) (by decide)
  refine ⟨hfind, by omega, ?_, ?_⟩
  · {
      simpa [hfind] using hzero.1
    }
  · {
      have hnot := hzero.2 1 (by omega)
      simpa [hfind] using hnot
    }

/-- Every `(1,-1,-2)` orbit is constant at `0` by the logarithmic time. -/
theorem NegOneNegTwoConstant (p q : Parameters)
    (hpQ : p.Q = 1) (hpC : p.C = -1) (hpD : p.D = -2)
    (hqQ : q.Q = 1) (hqC : q.C = 1) (hqD : q.D = -2) (n : ℤ) :
    let K := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
      (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
        fun j h => h.1)
    ∃ t : ℕ, t ≤ Nat.log 2 (3 * n.natAbs) + 1 ∧
      Iterate K t n = 0 ∧ Iterate K (t + 1) n = 0 := by
  let K := FirstReturn p (fun x => (UnitCoprimeIsSmall p hpQ
    (by rw [hpC]; simp [Nat.gcd_one_left]) (by rw [hpD]; decide) x).imp
      fun j h => h.1)
  have hfix0 : K 0 = 0 := (NegOneNegTwoFixed p hpQ hpC hpD 0).2 rfl
  by_cases hn : n ≤ 0
  · {
      let t := 2 * Nat.find (TwoFourDominates n.natAbs)
      have hzero :=
        (NegOneNegTwoFirstZero p q hpQ hpC hpD hqQ hqC hqD n).1 hn
      have hhit : Iterate K t n = 0 := by simpa [t] using hzero.1
      have hnext : Iterate K (t + 1) n = 0 := by
        have hstep : Iterate K (t + 1) n = K (Iterate K t n) := by
          simpa [Iterate] using IterateAdd K t 1 n
        rw [hstep, hhit, hfix0]
      have hbound : t ≤ Nat.log 2 (3 * n.natAbs) + 1 := by
        have hle := FindWithinLog n.natAbs
        omega
      exact ⟨t, hbound, hhit, hnext⟩
    }
  · {
      let t := 1 + 2 * Nat.find (TwoFourDominates (n.natAbs / 2))
      have hzero :=
        (NegOneNegTwoFirstZero p q hpQ hpC hpD hqQ hqC hqD n).2 (by omega)
      have hhit : Iterate K t n = 0 := by simpa [t] using hzero.1
      have hnext : Iterate K (t + 1) n = 0 := by
        have hstep : Iterate K (t + 1) n = K (Iterate K t n) := by
          simpa [Iterate] using IterateAdd K t 1 n
        rw [hstep, hhit, hfix0]
      have hbound := HalfFindWithinLog n.natAbs
      exact ⟨t, by simpa [t] using hbound, hhit, hnext⟩
    }

/-- For `(1,-1,2)`, an even seed returns `n/2` and an odd seed returns `(n-1)/2`. -/
theorem NegOneTwoExact (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = -1) (hD : p.D = 2) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    (2 ∣ n → H n = n / 2) ∧ (¬ 2 ∣ n → H n = (n - 1) / 2) := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ (by rw [hC]; simp [Nat.gcd_one_left])
      (by rw [hD]; decide) x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hquot := UnitOffsetQuotient p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) n
  have hstate0 : AffineState p.Q p.C 0 n = n := by
    rw [hQ]
    simpa using UnitOffsetState p.C n 0
  have hstate1 : AffineState p.Q p.C 1 n = n - 1 := by
    rw [hQ, hC]
    have hshift := UnitOffsetState (-1) n 1
    simpa using hshift
  constructor
  · {
      intro heven
      have hhit0 : IsFirstHit p n 0 := by
        refine ⟨?_, ?_⟩
        · {
            rw [hstate0, hD]
            exact heven
          }
        · {
            intro i hi
            omega
          }
      have htime : FirstHitTime p hhit n = 0 :=
        Nat.find_eq_zero.mpr hhit0
      rw [H, hquot, htime, hC, hD]
      ring
    }
  · {
      intro hodd
      have hnot0 : ¬ IsFirstHit p n 0 := by
        intro h
        rw [hstate0, hD] at h
        exact hodd h.1
      have hdiv1 : 2 ∣ n - 1 := by
        rcases Int.emod_two_eq_zero_or_one n with h0 | h1
        · {
            exact False.elim (hodd (Int.dvd_of_emod_eq_zero h0))
          }
        · {
            have : (n - 1) % 2 = 0 := by omega
            exact Int.dvd_of_emod_eq_zero this
          }
      have hhit1 : IsFirstHit p n 1 := by
        refine ⟨?_, ?_⟩
        · {
            rw [hstate1, hD]
            exact hdiv1
          }
        · {
            intro i hi hdiv
            have : i = 0 := by omega
            rw [this] at hdiv
            exact hnot0 ⟨hdiv, by intro j hj; omega⟩
          }
      have htime : FirstHitTime p hhit n = 1 := by
        have hle := Nat.find_le (p := fun t => IsFirstHit p n t) hhit1
        have hne : FirstHitTime p hhit n ≠ 0 := by
          intro h0
          exact hnot0 (by simpa [h0] using Nat.find_spec (hhit n))
        omega
      rw [H, hquot, htime, hC, hD]
      ring
    }

/-- For `(1,-1,-2)`, the return is the negative of the `(1,-1,2)` formula. -/
theorem NegOneNegTwoExact (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = -1) (hD : p.D = -2) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    (2 ∣ n → H n = -(n / 2)) ∧ (¬ 2 ∣ n → H n = -((n - 1) / 2)) := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ (by rw [hC]; simp [Nat.gcd_one_left])
      (by rw [hD]; decide) x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hquot := UnitOffsetQuotient p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) n
  have hstate0 : AffineState p.Q p.C 0 n = n := by
    rw [hQ]
    simpa using UnitOffsetState p.C n 0
  have hstate1 : AffineState p.Q p.C 1 n = n - 1 := by
    rw [hQ, hC]
    simpa using UnitOffsetState (-1) n 1
  constructor
  · {
      intro heven
      have hhit0 : IsFirstHit p n 0 := by
        refine ⟨?_, ?_⟩
        · {
            rw [hstate0, hD]
            exact Int.dvd_neg.mpr heven
          }
        · {
            intro i hi
            omega
          }
      have htime : FirstHitTime p hhit n = 0 :=
        Nat.find_eq_zero.mpr hhit0
      have hdiv : n / (-2) = -(n / 2) := by
        have : (2 : ℤ) ∣ n := heven
        obtain ⟨k, hk⟩ := this
        have hk' : n = k * 2 := by rw [hk]; ring
        rw [hk']
        ring
      rw [H, hquot, htime, hC, hD, hdiv]
    }
  · {
      intro hodd
      have hnot0 : ¬ IsFirstHit p n 0 := by
        intro h
        rw [hstate0, hD] at h
        exact hodd (Int.dvd_neg.mp h.1)
      have hdiv1 : 2 ∣ n - 1 := by
        rcases Int.emod_two_eq_zero_or_one n with h0 | h1
        · {
            exact False.elim (hodd (Int.dvd_of_emod_eq_zero h0))
          }
        · {
            have : (n - 1) % 2 = 0 := by omega
            exact Int.dvd_of_emod_eq_zero this
          }
      have hhit1 : IsFirstHit p n 1 := by
        refine ⟨?_, ?_⟩
        · {
            rw [hstate1, hD]
            exact Int.dvd_neg.mpr hdiv1
          }
        · {
            intro i hi hdiv
            have : i = 0 := by omega
            rw [this] at hdiv
            exact hnot0 ⟨hdiv, by intro j hj; omega⟩
          }
      have htime : FirstHitTime p hhit n = 1 := by
        have hle := Nat.find_le (p := fun t => IsFirstHit p n t) hhit1
        have hne : FirstHitTime p hhit n ≠ 0 := by
          intro h0
          exact hnot0 (by simpa [h0] using Nat.find_spec (hhit n))
        omega
      have hdiv : (n - 1) / (-2) = -((n - 1) / 2) := by
        obtain ⟨k, hk⟩ := hdiv1
        have hk' : n - 1 = k * 2 := by rw [hk]; ring
        rw [hk']
        ring
      rw [H, hquot, htime, hC, hD, hdiv]
    }

/-- For `(1,-1,±2)`, the absolute return depends only on parity. -/
theorem NegOneTwoAbs (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = -1) (hD : p.D = 2 ∨ p.D = -2) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left])
      (by rcases hD with h | h <;> rw [h] <;> decide) x).imp fun j h => h.1)
    (2 ∣ n → (H n).natAbs = n.natAbs / 2) ∧
      (¬ 2 ∣ n → (H n).natAbs = (n - 1).natAbs / 2) := by
  let hcop : Nat.Coprime p.C.natAbs p.D.natAbs := by
    rw [hC]
    rcases hD with h | h
    · {
        rw [h]
        simp [Nat.gcd_one_left]
      }
    · {
        rw [h]
        simp [Nat.gcd_one_left]
      }
  let hm : 2 ≤ p.D.natAbs := by
    rcases hD with h | h <;> rw [h] <;> decide
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop hm x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hform : (2 ∣ n → H n = n / 2 ∨ H n = -(n / 2)) ∧
      (¬ 2 ∣ n → H n = (n - 1) / 2 ∨ H n = -((n - 1) / 2)) := by
    rcases hD with h | h
    · {
        have hexact := NegOneTwoExact p hQ hC h n
        constructor
        · {
            intro heven
            exact Or.inl (hexact.1 heven)
          }
        · {
            intro hodd
            exact Or.inl (hexact.2 hodd)
          }
      }
    · {
        have hexact := NegOneNegTwoExact p hQ hC h n
        constructor
        · {
            intro heven
            exact Or.inr (hexact.1 heven)
          }
        · {
            intro hodd
            exact Or.inr (hexact.2 hodd)
          }
      }
  constructor
  · {
      intro heven
      rcases hform.1 heven with hpos | hneg
      · {
          rw [H, hpos]
          obtain ⟨k, hk⟩ := heven
          have hk' : n = k * 2 := by rw [hk]; ring
          have hquot : (k * 2) / 2 = k := Int.mul_ediv_cancel k (by decide)
          rw [hk', hquot]
          have habs : (k * 2).natAbs = k.natAbs * 2 := by
            rw [Int.natAbs_mul]
            simp
          omega
        }
      · {
          rw [H, hneg, Int.natAbs_neg]
          obtain ⟨k, hk⟩ := heven
          have hk' : n = k * 2 := by rw [hk]; ring
          have hquot : (k * 2) / 2 = k := Int.mul_ediv_cancel k (by decide)
          rw [hk', hquot]
          have habs : (k * 2).natAbs = k.natAbs * 2 := by
            rw [Int.natAbs_mul]
            simp
          omega
        }
    }
  · {
      intro hodd
      have hdiv1 : 2 ∣ n - 1 := by
        rcases Int.emod_two_eq_zero_or_one n with h0 | h1
        · {
            exact False.elim (hodd (Int.dvd_of_emod_eq_zero h0))
          }
        · {
            have : (n - 1) % 2 = 0 := by omega
            exact Int.dvd_of_emod_eq_zero this
          }
      rcases hform.2 hodd with hpos | hneg
      · {
          rw [H, hpos]
          obtain ⟨k, hk⟩ := hdiv1
          have hk' : n - 1 = k * 2 := by rw [hk]; ring
          have hquot : (k * 2) / 2 = k := Int.mul_ediv_cancel k (by decide)
          rw [hk', hquot]
          have habs : (k * 2).natAbs = k.natAbs * 2 := by
            rw [Int.natAbs_mul]
            simp
          omega
        }
      · {
          rw [H, hneg, Int.natAbs_neg]
          obtain ⟨k, hk⟩ := hdiv1
          have hk' : n - 1 = k * 2 := by rw [hk]; ring
          have hquot : (k * 2) / 2 = k := Int.mul_ediv_cancel k (by decide)
          rw [hk', hquot]
          have habs : (k * 2).natAbs = k.natAbs * 2 := by
            rw [Int.natAbs_mul]
            simp
          omega
        }
    }

/-- For `(1,-1,±2)`, compare the absolute return with `(|n|+1)/2`. -/
theorem NegOneParityBound (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = -1) (hD : p.D = 2 ∨ p.D = -2) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left])
      (by rcases hD with h | h <;> rw [h] <;> decide) x).imp fun j h => h.1)
    (2 ∣ n → (H n).natAbs = (n.natAbs + 1) / 2) ∧
      (¬ 2 ∣ n →
        (0 ≤ n → (H n).natAbs + 1 = (n.natAbs + 1) / 2) ∧
          (n ≤ 0 → (H n).natAbs = (n.natAbs + 1) / 2)) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left])
    (by rcases hD with h | h <;> rw [h] <;> decide) x).imp fun j h => h.1)
  have habs := NegOneTwoAbs p hQ hC hD n
  constructor
  · {
      intro heven
      have hhalf := habs.1 heven
      have : n.natAbs / 2 = (n.natAbs + 1) / 2 := by
        obtain ⟨k, hk⟩ := Int.natAbs_dvd.mpr heven
        omega
      omega
    }
  · {
      intro hodd
      have hhalf := habs.2 hodd
      constructor
      · {
          intro hn
          have hpos : (n - 1).natAbs = n.natAbs - 1 := by omega
          rw [hhalf, hpos]
          have hone : 1 ≤ n.natAbs := by
            have : n ≠ 0 := by
              intro h0
              exact hodd (by rw [h0])
            omega
          omega
        }
      · {
          intro hn
          have hneg : (n - 1).natAbs = n.natAbs + 1 := by omega
          rw [hhalf, hneg]
        }
    }

/-- For `|c|=1` and `|d|=2`, the halving defect is `1` only on an opposite-sign odd. -/
theorem TwoAbsDefect (p : Parameters) (hQ : p.Q = 1)
    (hd : p.D.natAbs = 2) (hc : p.C.natAbs = 1) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [show p.C.natAbs = 1 from hc]; simp [Nat.gcd_one_left])
      (by rw [hd]; decide) x).imp fun j h => h.1)
    let defect := (p.C = 1 ∧ n < 0 ∧ ¬ 2 ∣ n) ∨ (p.C = -1 ∧ 0 < n ∧ ¬ 2 ∣ n)
    (¬ defect → (H n).natAbs = (n.natAbs + 1) / 2) ∧
      (defect → (H n).natAbs + 1 = (n.natAbs + 1) / 2) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [show p.C.natAbs = 1 from hc]; simp [Nat.gcd_one_left])
    (by rw [hd]; decide) x).imp fun j h => h.1)
  have hc' : p.C = 1 ∨ p.C = -1 := by
    cases p.C with
    | ofNat k => {
        left
        have : k = 1 := by simpa using hc
        simp [this]
      }
    | negSucc k => {
        right
        have : k + 1 = 1 := by simpa [Int.natAbs] using hc
        have : k = 0 := by omega
        simp [this]
      }
  have hd' : p.D = 2 ∨ p.D = -2 := by
    cases p.D with
    | ofNat k => {
        left
        have : k = 2 := by simpa using hd
        simp [this]
      }
    | negSucc k => {
        right
        have : k + 1 = 2 := by simpa [Int.natAbs] using hd
        have : k = 1 := by omega
        simp [this]
      }
  rcases hc' with hc1 | hcm
  · {
      have hsplit : (0 ≤ n → (H n).natAbs = (n.natAbs + 1) / 2) ∧
          (n ≤ 0 → (H n).natAbs = n.natAbs / 2) := by
        rcases hd' with hd2 | hdm
        · {
            simpa [H, hc1, hd2] using OneTwoAbsExact p hQ hc1 hd2 n
          }
        · {
            have hexact := OneNegTwoExact p hQ hc1 hdm n
            constructor
            · {
                intro hn
                have hform := hexact.1 hn
                rw [H, hform, Int.natAbs_neg]
                exact Int.natAbs_ediv_nat (n.natAbs + 1) 2
              }
            · {
                intro hn
                have hform := hexact.2 hn
                rw [H, hform]
                have : 0 ≤ ((n.natAbs : ℤ) / 2) := by omega
                rw [Int.natAbs_of_nonneg this]
                exact Int.natAbs_ediv_nat n.natAbs 2
              }
          }
      refine ⟨?_, ?_⟩
      · {
          intro hnodef
          by_cases hsign : 0 ≤ n
          · {
              exact hsplit.1 hsign
            }
          · {
              have hn : n < 0 := by omega
              have heven : 2 ∣ n := by
                by_contra hodd
                exact hnodef (Or.inl ⟨hc1, hn, hodd⟩)
              have hhalf := hsplit.2 (le_of_lt hn)
              have heq : n.natAbs / 2 = (n.natAbs + 1) / 2 := by
                obtain ⟨k, hk⟩ := Int.natAbs_dvd.mpr heven
                omega
              omega
            }
        }
      · {
          intro hdef
          have hn : n < 0 := by
            rcases hdef with h | h
            · {
                exact h.2.1
              }
            · {
                rw [hc1] at h
                simp at h
              }
          have hodd : ¬ 2 ∣ n := by
            rcases hdef with h | h
            · {
                exact h.2.2
              }
            · {
                rw [hc1] at h
                simp at h
              }
          have hhalf := hsplit.2 (le_of_lt hn)
          have : 1 ≤ n.natAbs := by omega
          omega
        }
    }
  · {
      have hbound := NegOneParityBound p hQ hcm hd' n
      refine ⟨?_, ?_⟩
      · {
          intro hnodef
          by_cases hodd : 2 ∣ n
          · {
              exact hbound.1 hodd
            }
          · {
              have hn : n ≤ 0 := by
                by_contra hpos
                exact hnodef (Or.inr ⟨hcm, by omega, hodd⟩)
              exact (hbound.2 hodd).2 hn
            }
        }
      · {
          intro hdef
          have hpos : 0 < n := by
            rcases hdef with h | h
            · {
                rw [hcm] at h
                simp at h
              }
            · {
                exact h.2.1
              }
          have hodd : ¬ 2 ∣ n := by
            rcases hdef with h | h
            · {
                rw [hcm] at h
                simp at h
              }
            · {
                exact h.2.2
              }
          exact (hbound.2 hodd).1 (le_of_lt hpos)
        }
    }

/-- For `|d|=2`, `|c|=1` and `d<0`, the constant `0` begins by time `log2|n|+4`. -/
theorem UnitOffsetTwoNegativeAbsorbs (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : p.D.natAbs = 2) (hc : p.C.natAbs = 1) (hn : p.D < 0) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t : ℕ, t ≤ Nat.log 2 n.natAbs + 4 ∧
      ∀ k : ℕ, Iterate (FirstReturn p hhit) (t + k) n = 0 := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  obtain ⟨t0, ht0, habs⟩ := UnitOffsetTwoLog p hQ hcop hd hc n
  obtain ⟨t1, ht1, htail⟩ :=
    UnitOffsetAbsOneNegativeAbsorbs p hQ hcop (Iterate H t0 n) hc hn
  refine ⟨t0 + t1, ?_, ?_⟩
  · {
      have : (Iterate H t0 n).natAbs ≤ 1 := habs
      omega
    }
  · {
      intro k
      have hcomp := IterateAdd H t0 (t1 + k) n
      have hidx : t0 + (t1 + k) = t0 + t1 + k := by omega
      rw [← hidx, hcomp]
      simpa [H] using htail k
    }

/-- For `|d|=2`, `|c|=1` and `d>0`, a constant tail begins by time `log2|n|+3`. -/
theorem UnitOffsetTwoPositiveAbsorbs (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : p.D.natAbs = 2) (hc : p.C.natAbs = 1) (hp : 0 < p.D) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t : ℕ, t ≤ Nat.log 2 n.natAbs + 4 ∧
      ((∀ k : ℕ, Iterate (FirstReturn p hhit) (t + k) n = 0) ∨
        (∀ k : ℕ, Iterate (FirstReturn p hhit) (t + k) n = p.C)) := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  obtain ⟨t0, ht0, habs⟩ := UnitOffsetTwoLog p hQ hcop hd hc n
  obtain ⟨t1, ht1, htail⟩ :=
    UnitOffsetAbsOnePositiveAbsorbs p hQ hcop (Iterate H t0 n) hc hp
  refine ⟨t0 + t1, ?_, ?_⟩
  · {
      have : (Iterate H t0 n).natAbs ≤ 1 := habs
      omega
    }
  · {
      rcases htail with h0 | hc'
      · {
          left
          intro k
          have hcomp := IterateAdd H t0 (t1 + k) n
          have hidx : t0 + (t1 + k) = t0 + t1 + k := by omega
          rw [← hidx, hcomp]
          simpa [H] using h0 k
        }
      · {
          right
          intro k
          have hcomp := IterateAdd H t0 (t1 + k) n
          have hidx : t0 + (t1 + k) = t0 + t1 + k := by omega
          rw [← hidx, hcomp]
          simpa [H] using hc' k
        }
    }

/-- The geometric sum `1+m+...+m^{k-1}` equals `(m^k-1)/(m-1)`. -/
theorem GeoSum (m k : ℕ) (hm : 1 < m) :
    (m - 1) * (List.range k).foldl (fun s i => s + m ^ i) 0 =
      m ^ k - 1 := by
  induction k with
  | zero => {
      simp
    }
  | succ k ih => {
      have hfold : (List.range (k + 1)).foldl (fun s i => s + m ^ i) 0 =
          (List.range k).foldl (fun s i => s + m ^ i) 0 + m ^ k := by
        simp [List.range_succ, List.foldl_append]
      rw [hfold]
      have hmul := congrArg (fun t => t + (m - 1) * m ^ k) ih
      have : (m - 1) *
          ((List.range k).foldl (fun s i => s + m ^ i) 0 + m ^ k) =
          (m - 1) * (List.range k).foldl (fun s i => s + m ^ i) 0 +
            (m - 1) * m ^ k := by ring
      rw [this, ih]
      have hpow : (m - 1) * m ^ k = m ^ (k + 1) - m ^ k := by
        have hfac : m * m ^ k = m ^ (k + 1) := by rw [Nat.mul_comm, Nat.pow_succ]
        omega
      omega
    }

/-- An odd return of a negative divisor is strictly inside the shell. -/
theorem UnitOffsetOddReturnBound (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ) (k : ℕ)
    (hn : p.D < 0) (hodd : k % 2 = 1)
    (hret : let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
      Iterate (FirstReturn p hhit) k n = n) :
    n.natAbs * (p.D.natAbs ^ k + 1) ≤
      p.C.natAbs * (p.D.natAbs ^ k - 1) := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have heq := (UnitOffsetKStepIff p hQ hcop n k).1 hret
  have hid := UnitOffsetPowerIdentity p hQ hcop n k
  -- Odd powers of a negative divisor are negative.
  have hpow : p.D ^ k = -((p.D.natAbs ^ k : ℕ) : ℤ) := by
    have hsign : ∀ j, j % 2 = 1 → p.D ^ j = -((p.D.natAbs ^ j : ℕ) : ℤ) := by
      intro j hj
      have hneg : p.D = -((p.D.natAbs : ℤ)) := by omega
      rw [hneg, neg_pow]
      have hodd' : ¬ Even j := by
        rw [Nat.even_iff]
        omega
      simp [hodd', Int.natAbs_neg]
    exact hsign k hodd
  have hgap : (p.D ^ k - 1).natAbs = p.D.natAbs ^ k + 1 := by
    rw [hpow]
    omega
  have habs : n.natAbs * (p.D.natAbs ^ k + 1) =
      p.C.natAbs * (UnitHitWeight p.D H (FirstHitTime p hhit) n k).natAbs := by
    have := congrArg Int.natAbs heq
    rw [Int.natAbs_mul, Int.natAbs_mul, hgap] at this
    exact this
  -- The weight is an alternating sum bounded by the geometric sum.
  have hweight : (UnitHitWeight p.D H (FirstHitTime p hhit) n k).natAbs ≤
      p.D.natAbs ^ k - 1 := by
    have hm : 1 < p.D.natAbs := by
      have := p.DAdmissible
      omega
    have hstep : ∀ j ≤ k,
        (UnitHitWeight p.D H (FirstHitTime p hhit) n j).natAbs ≤
          p.D.natAbs ^ j - 1 := by
      intro j hj
      induction j with
      | zero => {
          simp [UnitHitWeight]
        }
      | succ j ih => {
          have hhitj := UnitOffsetTimeStrict p hQ hcop (Iterate H j n)
          have hrec := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj))
          simp [UnitHitWeight]
          have hterm : ((FirstHitTime p hhit (Iterate H j n) : ℤ) *
              p.D ^ j).natAbs ≤ (p.D.natAbs - 1) * p.D.natAbs ^ j := by
            rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_pow]
            exact Nat.mul_le_mul_right _ hhitj
          have hadd := Int.natAbs_add_le
            (UnitHitWeight p.D H (FirstHitTime p hhit) n j)
            ((FirstHitTime p hhit (Iterate H j n) : ℤ) * p.D ^ j)
          have hgeo : (p.D.natAbs ^ j - 1) +
              (p.D.natAbs - 1) * p.D.natAbs ^ j =
              p.D.natAbs ^ (j + 1) - 1 := by
            have hpow' : p.D.natAbs * p.D.natAbs ^ j =
                p.D.natAbs ^ (j + 1) := by
              rw [Nat.mul_comm, Nat.pow_succ]
            omega
          omega
        }
    exact hstep k le_rfl
  rw [habs]
  exact Nat.mul_le_mul_left _ hweight

/-- Iterating the affine branch with multiplier and offset one adds the elapsed ticks. -/
theorem OneOffsetState (n : ℤ) (j : ℕ) :
    AffineState 1 1 j n = n + j := by
  simp [AffineState, TrapSumOne, one_pow]

/-- The `(1,1)` return divides the seed shifted by its first hit time. -/
theorem OneOffsetQuotient (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hm : 2 ≤ p.D.natAbs) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
    H n = (n + FirstHitTime p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1) n) /
        p.D := by
  let hhit : ∀ x : ℤ, ∃ j : ℕ, IsFirstHit p x j :=
    fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1
  have htime := Nat.find_spec (hhit n)
  have hstate : AffineState p.Q p.C (FirstHitTime p hhit n) n =
      n + FirstHitTime p hhit n := by
    rw [hQ, hC]
    exact OneOffsetState n (FirstHitTime p hhit n)
  simp [FirstReturn, hstate]

/-- The first `(1,1)` hit is the remainder of `-n` modulo `|d|`. -/
theorem OneOffsetTime (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hm : 2 ≤ p.D.natAbs) (n : ℤ) :
    FirstHitTime p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1) n =
      ((-n) % (p.D.natAbs : ℤ)).toNat := by
  let hhit : ∀ x : ℤ, ∃ j : ℕ, IsFirstHit p x j :=
    fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1
  let m : ℤ := p.D.natAbs
  have hmpos : 0 < m := by
    change 0 < (p.D.natAbs : ℤ)
    omega
  let r : ℤ := (-n) % m
  have hge : 0 ≤ r := Int.emod_nonneg (-n) (by omega)
  have hlt : r < m := Int.emod_lt_of_pos (-n) hmpos
  have hsplit := Int.emod_add_mul_ediv (-n) m
  have hdvdm : m ∣ n + r := by
    refine ⟨-(((-n) / m)), ?_⟩
    have : n + r = -m * ((-n) / m) := by
      have hrw : -n = m * ((-n) / m) + r := by
        simpa [r, m] using hsplit.symm
      linarith
    simpa [mul_comm] using this
  have hsign : p.D = m ∨ p.D = -m := by
    cases p.D with
    | ofNat k => {
        left
        rfl
      }
    | negSucc k => {
        right
        rfl
      }
  have hdvd : p.D ∣ n + r := by
    rcases hsign with hp | hn
    · {
        rwa [hp]
      }
    · {
        rw [hn]
        exact dvd_neg.mpr hdvdm
      }
  have hhit0 : IsFirstHit p n r.toNat := by
    refine ⟨?_, ?_⟩
    · {
        have hrnat : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hge
        rw [← hQ, ← hC] at hdvd
        have hstate := OneOffsetState n r.toNat
        rw [← hrnat] at hdvd
        simpa [AffineState, hQ, hC] using hdvd
      }
    · {
        intro i hi hdiv
        have hstate := OneOffsetState n i
        rw [hQ, hC] at hdiv
        have hdvdm_i : m ∣ n + i := by
          rcases hsign with hp | hn
          · {
              rwa [← hp]
            }
          · {
              have : -m ∣ n + i := by rwa [← hn]
              exact (dvd_neg.mp this)
            }
        obtain ⟨a, ha⟩ := hdvdm
        obtain ⟨b, hb⟩ := hdvdm_i
        have hdiff : m ∣ (r - i) := by
          refine ⟨a - b, ?_⟩
          have : r - i = m * a - m * b := by
            have hr : r = m * a - n := by linarith
            have hi' : (i : ℤ) = m * b - n := by linarith
            linarith
          linarith
        have hpos : 0 < r - i := by
          have hi' : (i : ℤ) < r := by
            have : (i : ℤ) = i := rfl
            have hineq : (i : ℤ) < r.toNat := by exact_mod_cast hi
            rwa [Int.toNat_of_nonneg hge] at hineq
          omega
        have hsmall : r - i < m := by omega
        obtain ⟨c, hc⟩ := hdiff
        have hc0 : c = 0 := by
          have : m * c = r - i := by linarith
          nlinarith
        linarith
      }
  exact FirstHitUnique p n _ _ (Nat.find_spec (hhit n)) hhit0

/-- A `(1,1)` seed of absolute value at least `2` strictly decreases. -/
theorem OneOffsetDescent (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hm : 2 ≤ p.D.natAbs) (n : ℤ)
    (hbig : 2 ≤ n.natAbs) :
    (FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1) n).natAbs <
      n.natAbs := by
  let hhit : ∀ x : ℤ, ∃ j : ℕ, IsFirstHit p x j :=
    fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1
  have htime := OneOffsetTime p hQ hC hm n
  have hquot := OneOffsetQuotient p hQ hC hm n
  have hr : ((-n) % (p.D.natAbs : ℤ)).toNat < p.D.natAbs := by
    have hlt := Int.emod_lt_of_pos (-n)
      (show 0 < (p.D.natAbs : ℤ) by omega)
    have hge := Int.emod_nonneg (-n)
      (show (p.D.natAbs : ℤ) ≠ 0 by omega)
    exact_mod_cast (by rwa [Int.toNat_of_nonneg hge] :
      ((-n) % (p.D.natAbs : ℤ)) < p.D.natAbs)
  have hstate : n + (hhit n).choose =
      n + ((-n) % (p.D.natAbs : ℤ)).toNat := by
    -- The time used below is the named first-hit time.
    rfl
  have hdiv : (p.D.natAbs : ℤ) ∣
      n + ((-n) % (p.D.natAbs : ℤ)).toNat := by
    have hhitspec := Nat.find_spec (hhit n)
    have hstate' : AffineState p.Q p.C (FirstHitTime p hhit n) n =
        n + FirstHitTime p hhit n := by
      rw [hQ, hC]
      exact OneOffsetState n _
    rw [htime] at hstate'
    have hdvd := hhitspec.1
    rw [hstate'] at hdvd
    rcases (by
        cases p.D with
        | ofNat _ => { exact Or.inl rfl }
        | negSucc _ => { exact Or.inr rfl : }
        p.D = (p.D.natAbs : ℤ) ∨ p.D = -((p.D.natAbs : ℤ))) with
      | inl hp => rwa [hp] at hdvd
      | inr hn =>
          exact dvd_neg.mp (by rwa [hn] at hdvd)
  rw [hquot, htime]
  have habs : ((n + ((-n) % (p.D.natAbs : ℤ)).toNat) / p.D).natAbs =
      (n + ((-n) % (p.D.natAbs : ℤ)).toNat).natAbs / p.D.natAbs := by
    rcases (by
        cases p.D with
        | ofNat _ => { exact Or.inl rfl }
        | negSucc _ => { exact Or.inr rfl : }
        p.D = (p.D.natAbs : ℤ) ∨ p.D = -((p.D.natAbs : ℤ))) with
      | inl hp =>
          rw [hp]
          exact Int.natAbs_ediv_of_dvd hdiv
      | inr hn =>
          rw [hn, Int.neg_ediv_of_dvd (dvd_neg.mpr hdiv), Int.natAbs_neg]
          exact Int.natAbs_ediv_of_dvd hdiv
  rw [habs]
  have hsum : (n + ((-n) % (p.D.natAbs : ℤ)).toNat).natAbs ≤
      n.natAbs + ((-n) % (p.D.natAbs : ℤ)).toNat :=
    Int.natAbs_add_le _ _
  have hfrac : n.natAbs + ((-n) % (p.D.natAbs : ℤ)).toNat <
      n.natAbs * p.D.natAbs := by
    have hr' : ((-n) % (p.D.natAbs : ℤ)).toNat ≤ p.D.natAbs - 1 := by
      omega
    have hm1 : 1 ≤ p.D.natAbs - 1 := by omega
    nlinarith
  exact Nat.div_lt_of_lt_mul (by omega) (le_trans hsum (Nat.le_of_lt hfrac))

/-- A `(1,1)` orbit enters absolute value at most `1` within `|n|` steps. -/
theorem OneOffsetEnters (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hm : 2 ≤ p.D.natAbs) (n : ℤ) :
    ∃ t : ℕ, t ≤ n.natAbs ∧
      (Iterate (FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
        (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)) t n).natAbs ≤
        1 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
  suffices ∀ k n, n.natAbs = k → ∃ t, t ≤ k ∧ (Iterate H t n).natAbs ≤ 1 by
    simpa [H] using this n.natAbs n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    {
      intro n hk
      by_cases hsmall : n.natAbs ≤ 1
      · {
          exact ⟨0, Nat.zero_le _, by simpa [Iterate, hk] using hsmall⟩
        }
      · {
          have hbig : 2 ≤ n.natAbs := by omega
          have hdrop := OneOffsetDescent p hQ hC hm n hbig
          have hkey : (H n).natAbs < k := by
            rw [← hk]
            exact hdrop
          obtain ⟨t, ht, henter⟩ := ih (H n).natAbs hkey (H n) rfl
          refine ⟨t + 1, ?_, ?_⟩
          · {
              have hstep : t + 1 ≤ (H n).natAbs + 1 :=
                Nat.add_le_add_right ht 1
              omega
            }
          · {
              simpa [Iterate, Nat.add_comm] using henter
            }
        }
    }

/-- The `(1,1)` shell of radius `1` is invariant. -/
theorem OneOffsetShell (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hm : 2 ≤ p.D.natAbs) (n : ℤ)
    (hsmall : n.natAbs ≤ 1) :
    (FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1) n).natAbs ≤
      1 := by
  have htri : n = -1 ∨ n = 0 ∨ n = 1 := by omega
  have hquot := OneOffsetQuotient p hQ hC hm n
  have htime := OneOffsetTime p hQ hC hm n
  rcases htri with hneg | hzero | hone
  · {
      rw [hquot, htime, hneg]
      have hrem : ((-(-1 : ℤ)) % (p.D.natAbs : ℤ)).toNat = 1 := by
        have hmpos : 0 < (p.D.natAbs : ℤ) := by omega
        have hmod : (1 : ℤ) % (p.D.natAbs : ℤ) = 1 := by
          exact Int.emod_eq_of_lt (by decide) (by omega)
        simpa [hmod]
      rw [hrem]
      simp
    }
  · {
      rw [hquot, htime, hzero]
      simp
    }
  · {
      rw [hquot, htime, hone]
      have hrem : ((-(1 : ℤ)) % (p.D.natAbs : ℤ)).toNat =
          p.D.natAbs - 1 := by
        have hmpos : 0 < (p.D.natAbs : ℤ) := by omega
        have hmod : (-1 : ℤ) % (p.D.natAbs : ℤ) =
            (p.D.natAbs : ℤ) - 1 := by
          rw [Int.emod_neg, Int.emod_eq_of_lt (by decide) (by omega)]
          -- `-1 = q*m + r` with `r = m-1` and `q = -1`.
          have : (p.D.natAbs : ℤ) - 1 =
              (-1) % (p.D.natAbs : ℤ) := by
            rw [Int.neg_emod]
            have hone : (1 : ℤ) % (p.D.natAbs : ℤ) = 1 :=
              Int.emod_eq_of_lt (by decide) (by omega)
            rw [hone]
            omega
          linarith
        have hge : 0 ≤ (-1 : ℤ) % (p.D.natAbs : ℤ) :=
          Int.emod_nonneg _ (by omega)
        exact_mod_cast (by rwa [Int.toNat_of_nonneg hge] :
          ((-1 : ℤ) % (p.D.natAbs : ℤ)) = (p.D.natAbs : ℤ) - 1)
      rw [hrem]
      have hnum : (1 : ℤ) + (p.D.natAbs - 1) = p.D.natAbs := by omega
      rw [hnum]
      rcases (by
          cases p.D with
          | ofNat _ => { exact Or.inl rfl }
          | negSucc _ => { exact Or.inr rfl : }
          p.D = (p.D.natAbs : ℤ) ∨ p.D = -((p.D.natAbs : ℤ))) with
        | inl hp =>
            rw [hp]
            simp
        | inr hn =>
            rw [hn]
            simp
    }

/-- A `(1,1)` orbit begins a period of size at most `3` by time `|n|+2`. -/
theorem OneOffsetPeriodic (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hm : 2 ≤ p.D.natAbs) (n : ℤ) :
    ∃ t period : ℕ, t ≤ n.natAbs + 2 ∧ 0 < period ∧ period ≤ 3 ∧
      ∀ k : ℕ,
        Iterate (FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
          (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1))
            (t + k) n =
          Iterate (FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
            (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1))
            (t + k + period) n := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
  obtain ⟨t0, ht0, henter⟩ := OneOffsetEnters p hQ hC hm n
  have hstay : ∀ k, (Iterate H (t0 + k) n).natAbs ≤ 1 := by
    intro k
    induction k with
    | zero => {
        simpa using henter
      }
    | succ k ih => {
        rw [show t0 + (k + 1) = (t0 + k) + 1 by omega, Iterate]
        exact OneOffsetShell p hQ hC hm _ ih
      }
  let code : ℤ → Fin 3 := fun x =>
    if x = -1 then 0 else if x = 0 then 1 else 2
  have hpair : ∃ i j, i < j ∧ j ≤ 3 ∧
      Iterate H (t0 + i) n = Iterate H (t0 + j) n := by
    let f : Fin 4 → Fin 3 := fun a => code (Iterate H (t0 + a) n)
    have hcard : Fintype.card (Fin 3) < Fintype.card (Fin 4) := by
      simp
    obtain ⟨a, b, hne, heq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt f hcard
    have hab : a.val ≠ b.val := by
      intro h
      exact hne (Fin.ext h)
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · {
        refine ⟨a.val, b.val, hlt, Nat.lt_succ_iff.mp b.isLt, ?_⟩
        -- The code of a shell state determines the state.
        have hdecode : ∀ x, x.natAbs ≤ 1 → code x = code (Iterate H (t0 + a) n) →
            x = Iterate H (t0 + a) n := by
          intro x hx hcode
          have hxtri : x = -1 ∨ x = 0 ∨ x = 1 := by omega
          have htri : Iterate H (t0 + a) n = -1 ∨
              Iterate H (t0 + a) n = 0 ∨
              Iterate H (t0 + a) n = 1 := by
            have := hstay a
            omega
          fin_cases a <;> fin_cases b <;> simp_all [code, f]
        exact hdecode _ (hstay b) (by simpa [code, f] using heq)
      }
    · {
        refine ⟨b.val, a.val, hgt, Nat.lt_succ_iff.mp a.isLt, ?_⟩
        fin_cases a <;> fin_cases b <;> simp_all [code, f, hstay]
      }
  obtain ⟨i, j, hij, hj, heq⟩ := hpair
  refine ⟨t0 + i, j - i, ?_, Nat.sub_pos_of_lt hij, ?_, ?_⟩
  · {
      omega
    }
  · {
      omega
    }
  · {
      intro k
      have hshift : Iterate H (i + k) (Iterate H t0 n) =
          Iterate H (j + k) (Iterate H t0 n) :=
        CoreRepeatPropagates H (Iterate H t0 n) i j heq k
      have hleft : Iterate H (t0 + i + k) n =
          Iterate H (i + k) (Iterate H t0 n) := by
        rw [show t0 + i + k = t0 + (i + k) by omega, IterateAdd]
      have hright : Iterate H (j + k) (Iterate H t0 n) =
          Iterate H (t0 + (j + k)) n := by
        rw [← IterateAdd]
      have hidx : t0 + (j + k) = t0 + i + k + (j - i) := by omega
      rw [hleft, hshift, hright, hidx]
    }

/-- The three `(1,1)` shell returns, split by the sign of the divisor. -/
theorem OneOffsetShellValues (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hm : 2 ≤ p.D.natAbs) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
    H 0 = 0 ∧ H (-1) = 0 ∧
      (0 < p.D → H 1 = 1) ∧ (p.D < 0 → H 1 = -1) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
  have hzero := OneOffsetQuotient p hQ hC hm 0
  have htime0 := OneOffsetTime p hQ hC hm 0
  have hneg := OneOffsetQuotient p hQ hC hm (-1)
  have htimen := OneOffsetTime p hQ hC hm (-1)
  have hone := OneOffsetQuotient p hQ hC hm 1
  have htime1 := OneOffsetTime p hQ hC hm 1
  have hrem0 : ((-(0 : ℤ)) % (p.D.natAbs : ℤ)).toNat = 0 := by
    simp
  have hremn : ((-(-1 : ℤ)) % (p.D.natAbs : ℤ)).toNat = 1 := by
    have hmod : (1 : ℤ) % (p.D.natAbs : ℤ) = 1 :=
      Int.emod_eq_of_lt (by decide) (by omega)
    simpa [hmod]
  have hrem1 : ((-(1 : ℤ)) % (p.D.natAbs : ℤ)).toNat =
      p.D.natAbs - 1 := by
    have hmod : (1 : ℤ) % (p.D.natAbs : ℤ) = 1 :=
      Int.emod_eq_of_lt (by decide) (by omega)
    have hnegmod : (-1 : ℤ) % (p.D.natAbs : ℤ) =
        (p.D.natAbs : ℤ) - 1 := by
      rw [Int.neg_emod, hmod]
      omega
    have hge : 0 ≤ (-1 : ℤ) % (p.D.natAbs : ℤ) :=
      Int.emod_nonneg _ (by omega)
    exact_mod_cast (by rwa [Int.toNat_of_nonneg hge] :
      ((-1 : ℤ) % (p.D.natAbs : ℤ)) = (p.D.natAbs : ℤ) - 1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · {
      simpa [H, htime0, hrem0] using hzero
    }
  · {
      simpa [H, htimen, hremn] using hneg
    }
  · {
      intro hp
      have hd : p.D = p.D.natAbs := by
        have hnn : 0 ≤ p.D := le_of_lt hp
        exact Int.eq_natCast_of_nonneg hnn
      have hnum : (1 : ℤ) + (p.D.natAbs - 1) = p.D.natAbs := by omega
      rw [H, hone, htime1, hrem1, hnum, hd]
      exact Int.ediv_self (by omega)
    }
  · {
      intro hn
      have hd : p.D = -((p.D.natAbs : ℤ)) := by
        have hnp : p.D ≤ 0 := le_of_lt hn
        have hne : p.D ≠ 0 := by omega
        cases p.D with
        | ofNat k => {
            omega
          }
        | negSucc k => {
            rfl
          }
      have hnum : (1 : ℤ) + (p.D.natAbs - 1) = p.D.natAbs := by omega
      rw [H, hone, htime1, hrem1, hnum, hd]
      have : ((p.D.natAbs : ℤ) / -((p.D.natAbs : ℤ))) = -1 := by
        rw [Int.ediv_neg, Int.ediv_self (by omega)]
        simp
      exact this
    }

/-- Positive divisors end at `0` or `1`; negative divisors end at `0`. -/
theorem OneOffsetTerminal (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hm : 2 ≤ p.D.natAbs) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
    (0 < p.D → ∃ t : ℕ, t ≤ n.natAbs + 1 ∧
      (Iterate H t n = 0 ∨ Iterate H t n = 1)) ∧
      (p.D < 0 → ∃ t : ℕ, t ≤ n.natAbs + 2 ∧ Iterate H t n = 0) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
  obtain ⟨h0, hneg, hpos, hnp⟩ := OneOffsetShellValues p hQ hC hm
  obtain ⟨t0, _, henter⟩ := OneOffsetEnters p hQ hC hm n
  have htri : Iterate H t0 n = -1 ∨ Iterate H t0 n = 0 ∨
      Iterate H t0 n = 1 := by
    have hsmall : (Iterate H t0 n).natAbs ≤ 1 := henter
    omega
  constructor
  · {
      intro hp
      rcases htri with hshell | hshell | hshell
      · {
          refine ⟨t0 + 1, by omega, Or.inl ?_⟩
          rw [IterateAdd, hshell, hneg]
        }
      · {
          exact ⟨t0, by omega, Or.inl hshell⟩
        }
      · {
          exact ⟨t0, by omega, Or.inr hshell⟩
        }
    }
  · {
      intro hn
      rcases htri with hshell | hshell | hshell
      · {
          refine ⟨t0 + 1, by omega, ?_⟩
          rw [IterateAdd, hshell, hneg]
        }
      · {
          exact ⟨t0, by omega, hshell⟩
        }
      · {
          refine ⟨t0 + 2, by omega, ?_⟩
          rw [IterateAdd, hshell, hnp hn, Iterate, hneg]
        }
    }

/-- The `(1,1)` return is one floor division of `-n` by `|d|`. -/
theorem OneOffsetClosed (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hm : 2 ≤ p.D.natAbs) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
    (0 < p.D → H n = - ((-n) / (p.D.natAbs : ℤ))) ∧
      (p.D < 0 → H n = (-n) / (p.D.natAbs : ℤ)) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
  have hquot := OneOffsetQuotient p hQ hC hm n
  have htime := OneOffsetTime p hQ hC hm n
  have hrem : ((-n) % (p.D.natAbs : ℤ)).toNat =
      ((-n) % (p.D.natAbs : ℤ)).toNat := rfl
  have hsplit := Int.ediv_add_emod (-n) (p.D.natAbs : ℤ)
  -- `n + r = -m * k`, where `k` is the floor quotient of `-n`.
  have hnum : n + ((-n) % (p.D.natAbs : ℤ)) =
      -((p.D.natAbs : ℤ) * ((-n) / (p.D.natAbs : ℤ))) := by
    have hpair := Int.emod_add_ediv (-n) (p.D.natAbs : ℤ)
    linarith
  have hcast : (((-n) % (p.D.natAbs : ℤ)).toNat : ℤ) =
      (-n) % (p.D.natAbs : ℤ) := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  constructor
  · {
      intro hp
      have hd : p.D = p.D.natAbs := Int.eq_natCast_of_nonneg (le_of_lt hp)
      rw [H, hquot, htime, hcast, hnum, hd]
      have hden : (p.D.natAbs : ℤ) ≠ 0 := by omega
      rw [Int.neg_mul, Int.neg_ediv_of_dvd]
      · {
          exact Int.mul_ediv_cancel _ hden
        }
      · {
          exact ⟨(-n) / (p.D.natAbs : ℤ), by ring⟩
        }
    }
  · {
      intro hn
      have hd : p.D = -((p.D.natAbs : ℤ)) := by
        cases p.D with
        | ofNat k => {
            omega
          }
        | negSucc k => {
            rfl
          }
      rw [H, hquot, htime, hcast, hnum, hd]
      have hden : (p.D.natAbs : ℤ) ≠ 0 := by omega
      rw [Int.neg_mul, Int.neg_ediv, Int.mul_ediv_cancel _ hden]
      ring
    }

/-- Below one modulus, a positive divisor returns `0`, `1`, or `-1`. -/
theorem OneOffsetBelowModulus (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hm : 2 ≤ p.D.natAbs)
    (n : ℤ) (habs : n.natAbs ≤ p.D.natAbs) (hp : 0 < p.D) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
    H n = 0 ∨ H n = 1 ∨ H n = -1 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
  have hclosed := (OneOffsetClosed p hQ hC hm n).1 hp
  have htri : -(p.D.natAbs : ℤ) ≤ n ∧ n ≤ (p.D.natAbs : ℤ) := by
    omega
  -- The floor quotient of a value in `(-m, m]` is `0`, `-1`, or `1`.
  have hquot : (-n) / (p.D.natAbs : ℤ) = -1 ∨
      (-n) / (p.D.natAbs : ℤ) = 0 ∨
      (-n) / (p.D.natAbs : ℤ) = 1 := by
    omega
  rw [H, hclosed]
  rcases hquot with hq | hq | hq
  · {
      simp [hq]
    }
  · {
      simp [hq]
    }
  · {
      simp [hq]
    }

/-- Multiplying the return by `|d|` recovers the numerator. -/
theorem OneOffsetSize (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hm : 2 ≤ p.D.natAbs) (n : ℤ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
    let r := ((-n) % (p.D.natAbs : ℤ)).toNat
    (p.D.natAbs : ℤ) * (H n).natAbs = (n + r).natAbs ∧
      (H n).natAbs * p.D.natAbs ≤ n.natAbs + p.D.natAbs - 1 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
  let r := ((-n) % (p.D.natAbs : ℤ)).toNat
  have hquot := OneOffsetQuotient p hQ hC hm n
  have htime := OneOffsetTime p hQ hC hm n
  have hr : r < p.D.natAbs := by
    have hlt := Int.emod_lt_of_pos (-n)
      (show 0 < (p.D.natAbs : ℤ) by omega)
    have hge := Int.emod_nonneg (-n) (show (p.D.natAbs : ℤ) ≠ 0 by omega)
    exact_mod_cast (by
      rw [Int.toNat_of_nonneg hge]
      exact hlt : ((-n) % (p.D.natAbs : ℤ)) < (p.D.natAbs : ℤ))
  have hprod : (p.D.natAbs : ℤ) * (H n).natAbs = (n + r).natAbs := by
    rw [H, hquot, htime]
    rcases (by
        cases p.D with
        | ofNat _ => { exact Or.inl rfl }
        | negSucc _ => { exact Or.inr rfl : }
        p.D = (p.D.natAbs : ℤ) ∨ p.D = -((p.D.natAbs : ℤ))) with
      | inl hp =>
          rw [hp]
          have hdiv : (p.D.natAbs : ℤ) ∣ n + r := by
            rw [← hp]
            exact OneOffsetDivisible p hQ hC hm n
          have := Int.natAbs_mul (p.D.natAbs : ℤ) ((n + r) / p.D)
          -- The exact quotient has the product identity.
          rw [Int.mul_natAbs, Int.natAbs_natCast]
          have hback := Int.natAbs_ediv_of_dvd hdiv
          rw [Int.mul_comm, hback]
          ring
      | inr hn =>
          rw [hn]
          rw [Int.mul_natAbs, Int.natAbs_neg, Int.natAbs_natCast]
          ring
  refine ⟨hprod, ?_⟩
  have hle : (n + r).natAbs ≤ n.natAbs + r := by
    exact Int.natAbs_add_le n r
  have hrle : r ≤ p.D.natAbs - 1 := by omega
  have hcast : (r : ℤ).natAbs = r := by simp
  omega

/-- A seed no larger than `m^k` enters the shell within `k` steps. -/
theorem OneOffsetPowerEntry (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hm : 2 ≤ p.D.natAbs)
    (k : ℕ) (n : ℤ) (hpow : n.natAbs ≤ p.D.natAbs ^ k) :
    ∃ t : ℕ, t ≤ k ∧
      (Iterate (FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
        (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1))
        t n).natAbs ≤ 1 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) hm x).imp fun j h => h.1)
  induction k generalizing n with
  | zero => {
      refine ⟨0, le_rfl, ?_⟩
      simpa [Iterate] using hpow
    }
  | succ k ih => {
      by_cases hsmall : n.natAbs ≤ 1
      · {
          exact ⟨0, Nat.zero_le _, by simpa [Iterate] using hsmall⟩
        }
      · {
          have hsize := (OneOffsetSize p hQ hC hm n).2
          have hnext : (H n).natAbs ≤ p.D.natAbs ^ k := by
            by_contra hgt
            have hge : p.D.natAbs ^ k + 1 ≤ (H n).natAbs := by omega
            have hmul : (p.D.natAbs ^ k + 1) * p.D.natAbs ≤
                (H n).natAbs * p.D.natAbs := by
              exact Nat.mul_le_mul_right _ hge
            have hbig : p.D.natAbs ^ (k + 1) + p.D.natAbs ≤
                n.natAbs + p.D.natAbs - 1 := by
              calc
                p.D.natAbs ^ (k + 1) + p.D.natAbs
                  = (p.D.natAbs ^ k + 1) * p.D.natAbs := by
                      ring
                _ ≤ (H n).natAbs * p.D.natAbs := hmul
                _ ≤ n.natAbs + p.D.natAbs - 1 := hsize
            omega
          obtain ⟨t, ht, henter⟩ := ih (H n) hnext
          refine ⟨t + 1, by omega, ?_⟩
          simpa [Iterate, Nat.add_comm] using henter
        }
    }

/-- A positive power of the modulus descends one exponent at each return. -/
theorem OneOffsetPowerOrbit (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hp : 2 ≤ p.D)
    (k j : ℕ) (hj : j ≤ k) :
    Iterate (FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left])
        (by omega : 2 ≤ p.D.natAbs) x).imp fun i h => h.1))
      j (p.D ^ k) = p.D ^ (k - j) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left])
      (by omega : 2 ≤ p.D.natAbs) x).imp fun i h => h.1)
  induction j with
  | zero => {
      simp [Iterate]
    }
  | succ j ih => {
      have hj' : j ≤ k := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj)
      rw [Iterate, ih hj']
      have hclosed := (OneOffsetClosed p hQ hC
        (by omega : 2 ≤ p.D.natAbs) (p.D ^ (k - j))).1 (by omega)
      -- `-m^(k-j)` divides evenly by `m`, so the floor quotient is `-m^(k-j-1)`.
      have hpow : k - j = (k - (j + 1)) + 1 := by omega
      rw [H, hclosed, hpow, pow_succ]
      have hneg : (-((p.D : ℤ) ^ (k - (j + 1)) * p.D)) / p.D =
          -((p.D : ℤ) ^ (k - (j + 1))) := by
        rw [Int.neg_mul, Int.neg_ediv]
        exact Int.mul_ediv_cancel _ (by omega)
      rw [hneg]
      ring
    }

/-- A negative divisor alternates the sign of a modulus power. -/
theorem OneOffsetNegativePowerStep (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hn : p.D ≤ -2) (a : ℕ) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left])
        (by omega : 2 ≤ p.D.natAbs) x).imp fun i h => h.1)
    H ((p.D.natAbs : ℤ) ^ a) = -((p.D.natAbs : ℤ) ^ a) / p.D.natAbs ∧
      H (-((p.D.natAbs : ℤ) ^ (a + 1))) =
        (p.D.natAbs : ℤ) ^ a := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left])
      (by omega : 2 ≤ p.D.natAbs) x).imp fun i h => h.1)
  have hm : 2 ≤ p.D.natAbs := by omega
  have hnegd : p.D < 0 := by omega
  have hpos := (OneOffsetClosed p hQ hC hm ((p.D.natAbs : ℤ) ^ a)).2 hnegd
  have hneg := (OneOffsetClosed p hQ hC hm
    (-((p.D.natAbs : ℤ) ^ (a + 1)))).2 hnegd
  refine ⟨?_, ?_⟩
  · {
      simpa [H] using hpos
    }
  · {
      rw [H, hneg]
      have hden : (p.D.natAbs : ℤ) ≠ 0 := by omega
      have : ((p.D.natAbs : ℤ) ^ (a + 1)) / (p.D.natAbs : ℤ) =
          (p.D.natAbs : ℤ) ^ a := by
        rw [pow_succ, Int.mul_ediv_cancel _ hden]
      simpa [Int.neg_neg] using this
    }

/-- A negative divisor sends `m^k` to `(-1)^j m^(k-j)`. -/
theorem OneOffsetNegativePowerOrbit (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hn : p.D ≤ -2)
    (k j : ℕ) (hj : j ≤ k) :
    Iterate (FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left])
        (by omega : 2 ≤ p.D.natAbs) x).imp fun i h => h.1))
      j ((p.D.natAbs : ℤ) ^ k) =
        (-1 : ℤ) ^ j * (p.D.natAbs : ℤ) ^ (k - j) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left])
      (by omega : 2 ≤ p.D.natAbs) x).imp fun i h => h.1)
  induction j with
  | zero => {
      simp [Iterate]
    }
  | succ j ih => {
      have hj' : j ≤ k :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj)
      rw [Iterate, ih hj']
      have hstep := (OneOffsetNegativePowerStep p hQ hC hn (k - (j + 1))).1
      have hpow : k - j = (k - (j + 1)) + 1 := by omega
      -- The sign `(-1)^j` moves through the negative return.
      have hsign : (-1 : ℤ) ^ (j + 1) = (-1) ^ j * -1 := by
        rw [pow_succ]
        ring
      rw [hpow, pow_succ, hsign]
      -- `H` of a positive power is the negative of the lower power.
      have hpos : (p.D.natAbs : ℤ) ^ (k - (j + 1)) * (p.D.natAbs : ℤ) =
          (p.D.natAbs : ℤ) ^ ((k - (j + 1)) + 1) := by
        rw [pow_succ]
        ring
      have happ := hstep
      -- Apply the step to the positive power `m^(k-j)`.
      have : H ((p.D.natAbs : ℤ) ^ (k - j)) =
          -((p.D.natAbs : ℤ) ^ (k - (j + 1))) := by
        rw [← hpow]
        have hden : (p.D.natAbs : ℤ) ≠ 0 := by omega
        have hdiv : (-((p.D.natAbs : ℤ) ^ (k - j))) / (p.D.natAbs : ℤ) =
            -((p.D.natAbs : ℤ) ^ (k - j)) / (p.D.natAbs : ℤ) := rfl
        rw [(OneOffsetNegativePowerStep p hQ hC hn (k - j)).1]
        rw [hpow, pow_succ, Int.neg_mul, Int.neg_ediv,
          Int.mul_ediv_cancel _ hden]
      -- The induction hypothesis has a sign in front of the power.
      have hmul : H ((-1 : ℤ) ^ j * (p.D.natAbs : ℤ) ^ (k - j)) =
          (-1 : ℤ) ^ j * H ((p.D.natAbs : ℤ) ^ (k - j)) := by
        -- The return is homogeneous of degree one on this ray.
        rcases Nat.even_or_odd j with heven | hodd
        · {
            obtain ⟨t, ht⟩ := heven
            rw [ht, pow_mul, pow_two]
            simp [H]
          }
        · {
            obtain ⟨t, ht⟩ := hodd
            rw [ht, pow_succ]
            simp [H]
          }
      rw [hmul, this]
      ring
    }

/-- The `(1,1,2)` return halves, after one affine step when the seed is odd. -/
theorem OneOneTwoQuotient (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2) (n : ℤ) :
    FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC, hD]; decide) (by rw [hD]; decide) x).imp
        fun j h => h.1) n =
      if 2 ∣ n then n / 2 else (n + 1) / 2 := by
  let hhit : ∀ x : ℤ, ∃ j : ℕ, IsFirstHit p x j :=
    fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC, hD]; decide) (by rw [hD]; decide) x).imp
        fun j h => h.1
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      have hhit0 : IsFirstHit p n 0 :=
        (FirstHitZeroIff p n).mpr (by rwa [hD] at hdiv)
      have htime : FirstHitTime p hhit n = 0 :=
        FirstHitUnique p n (FirstHitTime p hhit n) 0
          (Nat.find_spec (hhit n)) hhit0
      simp [FirstReturn, htime, AffineState, TrapSum, hdiv]
    }
  · {
      have hodd : ¬ p.D ∣ n := by rwa [hD]
      have hsum : p.D ∣ n + 1 := by
        rw [hD]
        have hmod : n % 2 = 1 := by
          have hne : n % 2 ≠ 0 := by
            intro hz
            exact hdiv (Int.dvd_of_emod_eq_zero hz)
          have hlt : n % 2 < 2 := Int.emod_lt_of_pos n (by decide)
          have hge : 0 ≤ n % 2 := Int.emod_nonneg n (by decide)
          omega
        have hsplit := Int.ediv_add_emod n 2
        -- n = 2*(n/2) + 1, so n+1 is divisible by 2.
        have : n + 1 = 2 * (n / 2) + (n % 2 + 1) := by
          rw [← hsplit]
          ring
        rw [hmod] at this
        rw [this]
        exact ⟨n / 2 + 1, by ring⟩
      have hhit1 : IsFirstHit p n 1 := by
        refine ⟨?_, ?_⟩
        · {
            unfold AffineState
            simp [TrapSum, hQ, hC, pow_one]
            exact hsum
          }
        · {
            intro i hi
            have hi0 : i = 0 := by omega
            subst hi0
            simpa [AffineState, TrapSum] using hodd
          }
      have htime : FirstHitTime p hhit n = 1 :=
        FirstHitUnique p n (FirstHitTime p hhit n) 1
          (Nat.find_spec (hhit n)) hhit1
      have hstate : AffineState p.Q p.C 1 n = n + 1 := by
        simp [AffineState, TrapSum, hQ, hC, pow_one]
      simp [FirstReturn, htime, hstate, hdiv, hD]
    }

/-- The `(1,1,2)` return hits `0` or `1` within `|n|` steps. -/
theorem OneOneTwoEnters (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2) (n : ℤ) :
    ∃ t : ℕ, t ≤ n.natAbs ∧
      let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
        (by rw [hC, hD]; decide) (by rw [hD]; decide) x).imp
          fun j h => h.1)
      Iterate H t n = 0 ∨ Iterate H t n = 1 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC, hD]; decide) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  suffices ∀ k n, n.natAbs = k → ∃ t, t ≤ k ∧
      Iterate H t n = 0 ∨ Iterate H t n = 1 by
    simpa [H] using this n.natAbs n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    {
      intro n hk
      by_cases hsmall : n.natAbs ≤ 1
      · {
          have htri : n = -1 ∨ n = 0 ∨ n = 1 := by
            omega
          rcases htri with hneg | hzero | hone
          · {
              have hquot := OneOneTwoQuotient p hQ hC hD n
              have hodd : ¬ (2 : ℤ) ∣ n := by
                rw [hneg]
                decide
              rw [if_neg hodd] at hquot
              refine ⟨1, by omega, ?_⟩
              rw [show (1 : ℕ) = 0 + 1 by omega, Iterate]
              rw [hquot, hneg]
              decide
            }
          · {
              exact ⟨0, Nat.zero_le _, Or.inl (by simpa [Iterate, hzero])⟩
            }
          · {
              exact ⟨0, Nat.zero_le _, Or.inr (by simpa [Iterate, hone])⟩
            }
        }
      · {
          have hbig : 2 ≤ n.natAbs := by omega
          have hquot := OneOneTwoQuotient p hQ hC hD n
          have hdrop : (H n).natAbs < n.natAbs := by
            by_cases hdiv : (2 : ℤ) ∣ n
            · {
                rw [if_pos hdiv] at hquot
                have hhalf : (n / 2).natAbs = n.natAbs / 2 := by
                  obtain ⟨m, hm⟩ := hdiv
                  have hm2 : n = m * 2 := by rw [hm]; ring
                  rw [hm2, Int.mul_ediv_cancel _ (by decide : (2 : ℤ) ≠ 0)]
                  rw [Int.natAbs_mul, show (2 : ℤ).natAbs = 2 by decide]
                  omega
                rw [hquot, hhalf]
                omega
              }
            · {
                rw [if_neg hdiv] at hquot
                have hmod : n % 2 = 1 := by
                  have hne : n % 2 ≠ 0 := by
                    intro hz
                    exact hdiv (Int.dvd_of_emod_eq_zero hz)
                  have hlt : n % 2 < 2 :=
                    Int.emod_lt_of_pos n (by decide)
                  have hge : 0 ≤ n % 2 :=
                    Int.emod_nonneg n (by decide)
                  omega
                have hsplit := Int.emod_add_mul_ediv n 2
                have habs : ((n + 1) / 2).natAbs < n.natAbs := by
                  have hrewrite : n + 1 = 2 * (n / 2) + 2 := by
                    rw [← hsplit, hmod]
                    ring
                  have hquot2 : (n + 1) / 2 = n / 2 + 1 := by
                    rw [hrewrite]
                    exact Int.add_mul_ediv_right (n / 2) 1 (by decide)
                  -- The odd seed is at least 3 in absolute value.
                  have h3 : 3 ≤ n.natAbs := by
                    have hnot2 : n.natAbs ≠ 2 := by
                      intro h2
                      have hsign : n = 2 ∨ n = -2 := by
                        have : n = (n.natAbs : ℤ) ∨
                            n = -((n.natAbs : ℤ)) := by
                          cases n with
                          | ofNat _ => { left; rfl }
                          | negSucc _ => { right; rfl }
                        rw [h2] at this
                        exact this
                      rcases hsign with hp | hn
                      · exact hdiv (by rw [hp]; exact ⟨1, by decide⟩)
                      · exact hdiv (by rw [hn]; exact ⟨-1, by decide⟩)
                    omega
                  rw [hquot2]
                  -- |n/2 + 1| is strictly smaller than |n| for |n|≥3.
                  have hbound : (n / 2 + 1).natAbs ≤ (n.natAbs + 1) / 2 := by
                    have hle : (n / 2).natAbs ≤ n.natAbs / 2 :=
                      Int.natAbs_ediv_le_natAbs_div_natAbs n 2
                    -- Not always |a+1| ≤ |a|+1 is enough, then compare.
                    have hone : (n / 2 + 1).natAbs ≤ (n / 2).natAbs + 1 :=
                      Int.natAbs_add_le (n / 2) 1
                    have h1 : (1 : ℤ).natAbs = 1 := by decide
                    rw [h1] at hone
                    omega
                  omega
                rw [hquot]
                exact habs
              }
          have hkey : (H n).natAbs < k := by
            rw [← hk]
            exact hdrop
          obtain ⟨t, ht, henter⟩ :=
            ih (H n).natAbs hkey (H n) rfl
          refine ⟨t + 1, ?_, ?_⟩
          · {
              have hstep : t + 1 ≤ (H n).natAbs + 1 :=
                Nat.add_le_add_right ht 1
              have hlt : (H n).natAbs + 1 ≤ n.natAbs := by
                rw [hk]
                omega
              exact le_trans hstep hlt
            }
          · {
              simpa [Iterate, Nat.add_comm, H] using henter
            }
        }
    }

/-- A nonnegative seed has a nonnegative `(1,1,2)` return. -/
theorem OneOneTwoNonneg (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2)
    (n : ℤ) (hn : 0 ≤ n) :
    0 ≤ FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC, hD]; decide) (by rw [hD]; decide) x).imp
        fun j h => h.1) n := by
  have hquot := OneOneTwoQuotient p hQ hC hD n
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      rw [if_pos hdiv] at hquot
      rw [hquot]
      exact Int.ediv_nonneg hn (by decide)
    }
  · {
      rw [if_neg hdiv] at hquot
      rw [hquot]
      exact Int.ediv_nonneg (by omega) (by decide)
    }

/-- A nonpositive seed has a nonpositive `(1,1,2)` return. -/
theorem OneOneTwoNonpos (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2)
    (n : ℤ) (hn : n ≤ 0) :
    FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC, hD]; decide) (by rw [hD]; decide) x).imp
        fun j h => h.1) n ≤ 0 := by
  have hquot := OneOneTwoQuotient p hQ hC hD n
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      rw [if_pos hdiv] at hquot
      rw [hquot]
      exact Int.ediv_nonpos_of_nonpos_of_nonneg hn (by decide)
    }
  · {
      rw [if_neg hdiv] at hquot
      rw [hquot]
      have hsum : n + 1 ≤ 1 := by omega
      -- An odd nonpositive seed is at most `-1`, so `n+1 ≤ 0`.
      have hodd : n ≤ -1 := by
        by_contra hgt
        have hzero : n = 0 := by omega
        exact hdiv (by rw [hzero]; exact ⟨0, by decide⟩)
      exact Int.ediv_nonpos_of_nonpos_of_nonneg (by omega) (by decide)
    }

/-- A positive seed has a positive `(1,1,2)` return. -/
theorem OneOneTwoPositive (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2)
    (n : ℤ) (hn : 1 ≤ n) :
    1 ≤ FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC, hD]; decide) (by rw [hD]; decide) x).imp
        fun j h => h.1) n := by
  have hquot := OneOneTwoQuotient p hQ hC hD n
  by_cases hdiv : (2 : ℤ) ∣ n
  · {
      rw [if_pos hdiv] at hquot
      rw [hquot]
      have htwo : 2 ≤ n := by
        by_contra hlt
        have hone : n = 1 := by omega
        exact hdiv (by rw [hone]; decide)
      omega
    }
  · {
      rw [if_neg hdiv] at hquot
      rw [hquot]
      omega
    }

/-- Positive seeds reach `1`, and nonpositive seeds reach `0`. -/
theorem OneOneTwoTerminal (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2) (n : ℤ) :
    (1 ≤ n → ∃ t : ℕ,
      Iterate (FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
        (by rw [hC, hD]; decide) (by rw [hD]; decide) x).imp
          fun j h => h.1)) t n = 1) ∧
    (n ≤ 0 → ∃ t : ℕ,
      Iterate (FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
        (by rw [hC, hD]; decide) (by rw [hD]; decide) x).imp
          fun j h => h.1)) t n = 0) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC, hD]; decide) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  constructor
  · {
      intro hn
      obtain ⟨t, _, henter⟩ := OneOneTwoEnters p hQ hC hD n
      rcases henter with hzero | hone
      · {
          exfalso
          -- Every prefix of a positive orbit stays at least `1`.
          have hstay : ∀ k, 1 ≤ Iterate H k n := by
            intro k
            induction k with
            | zero => {
                simpa [Iterate] using hn
              }
            | succ k ih => {
                rw [Iterate]
                exact OneOneTwoPositive p hQ hC hD _ ih
              }
          have hbad := hstay t
          rw [hzero] at hbad
          omega
        }
      · {
          exact ⟨t, hone⟩
        }
    }
  · {
      intro hn
      obtain ⟨t, _, henter⟩ := OneOneTwoEnters p hQ hC hD n
      rcases henter with hzero | hone
      · {
          exact ⟨t, hzero⟩
        }
      · {
          exfalso
          have hstay : ∀ k, Iterate H k n ≤ 0 := by
            intro k
            induction k with
            | zero => {
                simpa [Iterate] using hn
              }
            | succ k ih => {
                rw [Iterate]
                exact OneOneTwoNonpos p hQ hC hD _ ih
              }
          have hbad := hstay t
          rw [hone] at hbad
          omega
        }
    }

/-- For `(1,1,3)`, the seed `2` meets the logarithmic bound. -/
theorem OneThreeBoundSharp (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 3) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    Nat.log 2 ((2 : ℤ).natAbs) = 1 ∧
      ((2 : ℤ)).natAbs = 2 ∧ (H (2 : ℤ)).natAbs = 1 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hclosed :=
    (OneOffsetClosed p hQ hC (by rw [hD]; decide) (2 : ℤ)).1
      (by rw [hD]; decide)
  have hform : H (2 : ℤ) = -((-2) / (3 : ℤ)) := by
    simpa [H, hD] using hclosed
  decide

/-- For `(1,1,2)`, the seed `2` meets the excess logarithm. -/
theorem OneTwoExcessSharp (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = 2) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    Nat.log 2 (((2 : ℤ).natAbs) - p.C.natAbs) + 1 = 1 ∧
      p.C.natAbs < ((2 : ℤ).natAbs) ∧ (H (2 : ℤ)).natAbs = 1 := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hclosed :=
    (OneOffsetClosed p hQ hC (by rw [hD]; decide) (2 : ℤ)).1
      (by rw [hD]; decide)
  have hform : H (2 : ℤ) = -((-2) / (2 : ℤ)) := by
    simpa [H, hD] using hclosed
  rw [hC]
  decide

/-- For `|d|≥2`, the excess over `|c|` is divided by `|d|`. -/
theorem UnitOffsetExcess (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : 2 ≤ p.D.natAbs) (n : ℤ) (hn : p.C.natAbs ≤ n.natAbs) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    (FirstReturn p hhit n).natAbs ≤
      p.C.natAbs + (n.natAbs - p.C.natAbs) / p.D.natAbs := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hquot := UnitOffsetQuotient p hQ hcop n
  have htime := UnitOffsetTimeStrict p hQ hcop n
  have hnum : (n + p.C * (FirstHitTime p hhit n : ℤ)).natAbs ≤
      n.natAbs + p.C.natAbs * (p.D.natAbs - 1) := by
    have hadd := Int.natAbs_add_le n (p.C * (FirstHitTime p hhit n : ℤ))
    have hmul : (p.C * (FirstHitTime p hhit n : ℤ)).natAbs =
        p.C.natAbs * FirstHitTime p hhit n := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    omega
  have hdiv : p.D.natAbs * (H n).natAbs =
      (n + p.C * (FirstHitTime p hhit n : ℤ)).natAbs := by
    have hsize := (UnitOffsetSize p hQ hcop n).1
    simpa [H, hquot] using hsize
  omega

/-- For `|d|≥2`, the shell begins by one more than the base-`|d|` logarithm. -/
theorem UnitOffsetExcessLog (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : 2 ≤ p.D.natAbs) (n : ℤ) (hn : p.C.natAbs < n.natAbs) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t : ℕ, t ≤ Nat.log p.D.natAbs (n.natAbs - p.C.natAbs) + 1 ∧
      (Iterate (FirstReturn p hhit) t n).natAbs ≤ p.C.natAbs := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let N := p.C.natAbs
  let m := p.D.natAbs
  suffices ∀ e : ℕ, ∀ x : ℤ, x.natAbs = N + e → 0 < e →
      ∃ t : ℕ, t ≤ Nat.log m e + 1 ∧ (Iterate H t x).natAbs ≤ N by
    exact this (n.natAbs - N) n (by omega) (by omega)
  intro e
  induction e using Nat.strongRecOn with
  | ind e ih =>
    {
      intro x hx he
      have hstep := UnitOffsetExcess p hQ hcop hd x (by omega)
      by_cases hshell : (H x).natAbs ≤ N
      · {
          refine ⟨1, by omega, ?_⟩
          simpa [Iterate] using hshell
        }
      · {
          have he' : (H x).natAbs = N + ((H x).natAbs - N) := by omega
          have hlt : (H x).natAbs - N < e := by omega
          obtain ⟨t, ht, hsmall⟩ :=
            ih ((H x).natAbs - N) hlt (H x) he' (by omega)
          refine ⟨t + 1, ?_, ?_⟩
          · {
              have hmul : m * ((H x).natAbs - N) ≤ e := by omega
              have hlog :
                  Nat.log m ((H x).natAbs - N) + 1 ≤ Nat.log m e := by
                have hpow :=
                  Nat.pow_log_le_self m (by omega : 1 ≤ (H x).natAbs - N)
                have hcmp : m ^ (Nat.log m ((H x).natAbs - N) + 1) ≤ e := by
                  rw [Nat.pow_succ]
                  omega
                exact Nat.le_log_of_pow_le hd hcmp
              omega
            }
          · {
              rw [Iterate]
              simpa [IterateAdd] using hsmall
            }
        }
    }

/-- An excess of one enters the shell at the logarithmic time `1`. -/
theorem UnitOffsetExcessOne (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs)
    (hd : 2 ≤ p.D.natAbs) (n : ℤ) (hn : n.natAbs = p.C.natAbs + 1) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    Nat.log p.D.natAbs (n.natAbs - p.C.natAbs) + 1 = 1 ∧
      p.C.natAbs < n.natAbs ∧
      (FirstReturn p hhit n).natAbs ≤ p.C.natAbs := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  have hstep := UnitOffsetExcess p hQ hcop hd n (by omega)
  have hlog : Nat.log p.D.natAbs 1 = 0 := by
    have hpow : p.D.natAbs ^ 1 = p.D.natAbs := by simp
    have hle : Nat.log p.D.natAbs 1 ≤ 0 := by
      by_contra hgt
      have hge : 1 ≤ Nat.log p.D.natAbs 1 := by omega
      have hcmp := Nat.pow_log_le_self p.D.natAbs (by omega : 1 ≤ (1 : ℕ))
      omega
    omega
  omega

/-- A state in the shell `|x|≤|c|` begins a short period within `2|c|` steps. -/
theorem UnitOffsetShellPeriod (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hn : n.natAbs ≤ p.C.natAbs) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ i period : ℕ, i ≤ 2 * p.C.natAbs ∧ 0 < period ∧
      period ≤ 2 * p.C.natAbs + 1 ∧
      ∀ k : ℕ,
        Iterate (FirstReturn p hhit) (i + k) n =
          Iterate (FirstReturn p hhit) (i + k + period) n := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let B := p.C.natAbs * (p.D.natAbs - 1)
  have hA : 1 < p.D.natAbs := by
    have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
    omega
  have hbound : ∀ k : ℤ,
      p.D.natAbs * (H k).natAbs ≤ 1 * k.natAbs + B := by
    intro k
    have hsize := (UnitOffsetSize p hQ hcop k).1
    have htime := UnitOffsetTimeStrict p hQ hcop k
    have hle : (k + p.C * (FirstHitTime p hhit k : ℤ)).natAbs ≤
        k.natAbs + B := by
      have hadd := Int.natAbs_add_le k (p.C * (FirstHitTime p hhit k : ℤ))
      have hmul : (p.C * (FirstHitTime p hhit k : ℤ)).natAbs =
          p.C.natAbs * FirstHitTime p hhit k := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have hmulle : p.C.natAbs * FirstHitTime p hhit k ≤ B :=
        Nat.mul_le_mul_left _ htime
      omega
    simpa [H, hhit, Nat.one_mul, hsize] using hle
  have hrad : CoreRadius 1 B p.D.natAbs = p.C.natAbs := by
    unfold CoreRadius
    have hden : p.D.natAbs - 1 ≠ 0 := by omega
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hden)
  have hnrad : n.natAbs ≤ CoreRadius 1 B p.D.natAbs := by
    rw [hrad]
    exact hn
  obtain ⟨i, j, hij, hj, heq⟩ :=
    CorePigeon 1 B p.D.natAbs H hA hbound n hnrad
  have hjN : j ≤ 2 * p.C.natAbs + 1 := by simpa [hrad] using hj
  refine ⟨i, j - i, ?_, Nat.sub_pos_of_lt hij, ?_, ?_⟩
  · {
      omega
    }
  · {
      exact le_trans (Nat.sub_le j i) hjN
    }
  · {
      intro k
      have hshift : Iterate H (i + k) n = Iterate H (j + k) n :=
        CoreRepeatPropagates H n i j heq k
      have hidx : j + k = i + k + (j - i) := by omega
      rw [hshift, hidx]
    }

/-- Outside the shell, a short period begins by the logarithm plus `2|c|`. -/
theorem UnitOffsetLogCycle (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hn : p.C.natAbs < n.natAbs) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t period : ℕ,
      t ≤ Nat.log p.D.natAbs (n.natAbs - p.C.natAbs) + 1 +
        2 * p.C.natAbs ∧
      0 < period ∧ period ≤ 2 * p.C.natAbs + 1 ∧
      ∀ k : ℕ,
        Iterate (FirstReturn p hhit) (t + k) n =
          Iterate (FirstReturn p hhit) (t + k + period) n := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hd : 2 ≤ p.D.natAbs := p.DAdmissible
  obtain ⟨t0, ht0, henter⟩ := UnitOffsetExcessLog p hQ hcop hd n hn
  have hshell : (Iterate H t0 n).natAbs ≤ p.C.natAbs := by
    simpa [H, hhit] using henter
  obtain ⟨i, period, hi, hp, hper, hrep⟩ :=
    UnitOffsetShellPeriod p hQ hcop (Iterate H t0 n) hshell
  refine ⟨t0 + i, period, ?_, hp, hper, ?_⟩
  · {
      omega
    }
  · {
      intro k
      have hleft : Iterate H (t0 + i + k) n =
          Iterate H (i + k) (Iterate H t0 n) := by
        rw [show t0 + i + k = t0 + (i + k) by omega, IterateAdd]
      have hright : Iterate H (i + k + period) (Iterate H t0 n) =
          Iterate H (t0 + (i + k + period)) n := by
        rw [← IterateAdd]
      have hidx : t0 + (i + k + period) = t0 + i + k + period := by omega
      rw [hleft, hrep k, hright, hidx]
    }

/-- For `(1,1,-2)`, the shell delay `2|c|` is attained at the seed `1`. -/
theorem UnitOffsetShellDelaySharp (p : Parameters)
    (hQ : p.Q = 1) (hC : p.C = 1) (hD : p.D = -2) :
    let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
      (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
        fun j h => h.1)
    Iterate H 1 (1 : ℤ) = -1 ∧ Iterate H 2 (1 : ℤ) = 0 ∧
      ∀ t period : ℕ, t < 2 → 0 < period →
        ∃ k : ℕ,
          Iterate H (t + k) (1 : ℤ) ≠
            Iterate H (t + k + period) (1 : ℤ) := by
  let H := FirstReturn p (fun x => (UnitCoprimeIsSmall p hQ
    (by rw [hC]; simp [Nat.gcd_one_left]) (by rw [hD]; decide) x).imp
      fun j h => h.1)
  have hodd := OneNegTwoOddIterate p hQ hC hD (1 : ℤ) (by decide) 0
  have hone : Iterate H 1 (1 : ℤ) = -1 := by
    simpa using hodd
  have htwo : Iterate H 2 (1 : ℤ) = 0 :=
    (OneNegTwoBoundSharp p hQ hC hD).2.2.1
  have hfix : H 0 = 0 :=
    (OneNegTwoFixed p hQ hC hD 0).2 rfl
  have htail : ∀ s : ℕ, 2 ≤ s → Iterate H s (1 : ℤ) = 0 := by
    intro s hs
    induction s with
    | zero => {
        omega
      }
    | succ s ih => {
        by_cases htwo' : s = 1
        · {
            simpa [htwo'] using htwo
          }
        · {
            have hs' : 2 ≤ s := by omega
            have hprev := ih hs'
            rw [Iterate, hprev, hfix]
          }
      }
  refine ⟨hone, htwo, ?_⟩
  intro t period ht hp
  refine ⟨0, ?_⟩
  cases t with
  | zero => {
      have hright : Iterate H period (1 : ℤ) = 0 := by
        exact htail period hp
      simpa [Iterate, hright] using (by decide : (1 : ℤ) ≠ 0)
    }
  | succ t' => {
      have ht0 : t' = 0 := by omega
      have hright : Iterate H (1 + period) (1 : ℤ) = 0 := by
        exact htail (1 + period) (by omega)
      simpa [ht0, Iterate, hone, hright] using (by decide : (-1 : ℤ) ≠ 0)
    }

/-- The shell period is at most `2|c|`, since `0` is a separate fixed point. -/
theorem UnitOffsetPeriodAtMostTwice (p : Parameters) (hQ : p.Q = 1)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (n : ℤ)
    (hn : n.natAbs ≤ p.C.natAbs) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ i period : ℕ, i ≤ 2 * p.C.natAbs ∧ 0 < period ∧
      period ≤ 2 * p.C.natAbs ∧
      ∀ k : ℕ,
        Iterate (FirstReturn p hhit) (i + k) n =
          Iterate (FirstReturn p hhit) (i + k + period) n := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let N := p.C.natAbs
  let B := N * (p.D.natAbs - 1)
  have hA : 1 < p.D.natAbs := by
    have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
    omega
  have hN : 0 < N := by
    by_contra hzero
    have hcop0 : Nat.Coprime 0 p.D.natAbs := by simpa [N] using hcop
    have hd1 : p.D.natAbs = 1 := Nat.coprime_zero_left.mp hcop0
    have htwo : 2 ≤ p.D.natAbs := p.DAdmissible
    omega
  have hbound : ∀ k : ℤ,
      p.D.natAbs * (H k).natAbs ≤ 1 * k.natAbs + B := by
    intro k
    have hsize := (UnitOffsetSize p hQ hcop k).1
    have htime := UnitOffsetTimeStrict p hQ hcop k
    have hle : (k + p.C * (FirstHitTime p hhit k : ℤ)).natAbs ≤
        k.natAbs + B := by
      have hadd := Int.natAbs_add_le k (p.C * (FirstHitTime p hhit k : ℤ))
      have hmul : (p.C * (FirstHitTime p hhit k : ℤ)).natAbs =
          p.C.natAbs * FirstHitTime p hhit k := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have hmulle : p.C.natAbs * FirstHitTime p hhit k ≤ B :=
        Nat.mul_le_mul_left _ htime
      omega
    simpa [H, hhit, Nat.one_mul, hsize] using hle
  have hrad : CoreRadius 1 B p.D.natAbs = N := by
    unfold CoreRadius
    have hden : p.D.natAbs - 1 ≠ 0 := by omega
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hden)
  have hstay : ∀ t : ℕ, (Iterate H t n).natAbs ≤ N := by
    intro t
    have hcore := CoreStays 1 B p.D.natAbs H hA hbound n
      (by rw [hrad]; exact hn) t
    simpa [hrad] using hcore
  have hfix : H 0 = 0 := UnitOffsetZeroFixed p hQ hcop
  by_cases hhit0 : ∃ t : ℕ, t ≤ 2 * N ∧ Iterate H t n = 0
  · {
      obtain ⟨t, ht, hz⟩ := hhit0
      have htail : ∀ r : ℕ, Iterate H (t + r) n = 0 := by
        intro r
        induction r with
        | zero => {
            simpa using hz
          }
        | succ r ih => {
            rw [show t + (r + 1) = (t + r) + 1 by omega, Iterate, ih, hfix]
          }
      refine ⟨t, 1, ht, by decide, by omega, ?_⟩
      intro k
      have hleft := htail k
      have hright := htail (k + 1)
      simpa [Nat.add_assoc, hleft, hright]
    }
  · {
      have hnonzero : ∀ t : ℕ, t ≤ 2 * N → Iterate H t n ≠ 0 := by
        intro t ht hz
        exact hhit0 ⟨t, ht, hz⟩
      let code : ℤ → ℕ := fun z =>
        if 0 < z then z.natAbs - 1 else N + (z.natAbs - 1)
      have hcode : ∀ z : ℤ, z ≠ 0 → z.natAbs ≤ N → code z < 2 * N := by
        intro z hz hle
        by_cases hzp : 0 < z
        · {
            have habs : 1 ≤ z.natAbs := by omega
            simp [code, hzp, habs]
            omega
          }
        · {
            have hzneg : z < 0 := by omega
            have habs : 1 ≤ z.natAbs := by omega
            simp [code, hzp, habs]
            omega
          }
      have hinj : ∀ z w : ℤ, z ≠ 0 → w ≠ 0 → z.natAbs ≤ N →
          w.natAbs ≤ N → code z = code w → z = w := by
        intro z w hz hw hzn hwn hcw
        by_cases hzp : 0 < z
        · {
            by_cases hwp : 0 < w
            · {
                have hz1 : 1 ≤ z.natAbs := by omega
                have hw1 : 1 ≤ w.natAbs := by omega
                simp [code, hzp, hwp] at hcw
                have habs : z.natAbs = w.natAbs := by omega
                have hzpos : z = z.natAbs := by omega
                have hwpos : w = w.natAbs := by omega
                omega
              }
            · {
                have hz1 : 1 ≤ z.natAbs := by omega
                have hw1 : 1 ≤ w.natAbs := by omega
                simp [code, hzp, hwp] at hcw
                omega
              }
          }
        · {
            by_cases hwp : 0 < w
            · {
                have hz1 : 1 ≤ z.natAbs := by omega
                have hw1 : 1 ≤ w.natAbs := by omega
                simp [code, hzp, hwp] at hcw
                omega
              }
            · {
                have hzneg : z < 0 := by omega
                have hwneg : w < 0 := by omega
                have hz1 : 1 ≤ z.natAbs := by omega
                have hw1 : 1 ≤ w.natAbs := by omega
                simp [code, hzp, hwp] at hcw
                have habs : z.natAbs = w.natAbs := by omega
                have hzform : z = -z.natAbs := by omega
                have hwform : w = -w.natAbs := by omega
                omega
              }
          }
      let f : Fin (2 * N + 1) → Fin (2 * N) := fun t =>
        ⟨code (Iterate H t.val n), hcode _ (hnonzero t.val (Nat.le_of_lt_succ t.isLt))
          (hstay t.val)⟩
      have hcard :
          Fintype.card (Fin (2 * N)) < Fintype.card (Fin (2 * N + 1)) := by
        simp [Fintype.card_fin]
      obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
      have hstate : Iterate H a.val n = Iterate H b.val n := by
        have hcodeeq : code (Iterate H a.val n) = code (Iterate H b.val n) := by
          simpa using heq
        exact hinj _ _ (hnonzero a.val (Nat.le_of_lt_succ a.isLt))
          (hnonzero b.val (Nat.le_of_lt_succ b.isLt)) (hstay a.val) (hstay b.val)
          hcodeeq
      rcases Nat.lt_trichotomy a.val b.val with hlt | heqv | hgt
      · {
          refine ⟨a.val, b.val - a.val, ?_, Nat.sub_pos_of_lt hlt, ?_, ?_⟩
          · {
              have hb : b.val ≤ 2 * N := Nat.le_of_lt_succ b.isLt
              omega
            }
          · {
              have hb : b.val ≤ 2 * N := Nat.le_of_lt_succ b.isLt
              omega
            }
          · {
              intro k
              have hshift := CoreRepeatPropagates H n a.val b.val hstate k
              have hidx : b.val + k = a.val + k + (b.val - a.val) := by omega
              rw [hshift, hidx]
            }
        }
      · {
          exact False.elim (hne (Fin.ext heqv))
        }
      · {
          refine ⟨b.val, a.val - b.val, ?_, Nat.sub_pos_of_lt hgt, ?_, ?_⟩
          · {
              have ha : a.val ≤ 2 * N := Nat.le_of_lt_succ a.isLt
              omega
            }
          · {
              have ha : a.val ≤ 2 * N := Nat.le_of_lt_succ a.isLt
              omega
            }
          · {
              intro k
              have hshift :=
                CoreRepeatPropagates H n b.val a.val hstate.symm k
              have hidx : a.val + k = b.val + k + (a.val - b.val) := by omega
              rw [hshift, hidx]
            }
        }
    }

/-- For divisor `2`, an even seed is halved and an odd seed is shifted once. -/
theorem TwoDivisorStep (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (hp : 0 < p.C) (n : ℤ) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    let H := FirstReturn p hhit
    (2 ∣ n → H n = n / 2) ∧ (¬ 2 ∣ n → H n = (n + p.C) / 2) := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  have hmodc : p.C % 2 = 1 := by
    have hpos : p.C = p.C.natAbs := by omega
    have hne : ¬ 2 ∣ p.C.natAbs := by
      intro hdvd
      have hgcd : Nat.gcd p.C.natAbs 2 = 2 := Nat.gcd_eq_right hdvd
      have hone : Nat.gcd p.C.natAbs 2 = 1 := by
        simpa [hD] using hcop
      omega
    have hmod : p.C.natAbs % 2 = 1 := by
      have hor := Nat.mod_two_eq_zero_or_one p.C.natAbs
      rcases hor with h0 | h1
      · {
          exact False.elim (hne (Nat.dvd_of_mod_eq_zero h0))
        }
      · {
          exact h1
        }
    rw [hpos]
    exact_mod_cast hmod
  have hquot := UnitOffsetQuotient p hQ hcop n
  by_cases heven : 2 ∣ n
  · {
      have hhit0 : IsFirstHit p n 0 := by
        refine ⟨?_, ?_⟩
        · {
            rw [hD]
            exact heven
          }
        · {
            intro i hi
            omega
          }
      have htime : FirstHitTime p hhit n = 0 := by
        have hle := Nat.find_le (p := fun t => IsFirstHit p n t) hhit0
        have hge : 0 ≤ FirstHitTime p hhit n := by omega
        omega
      have hstate : AffineState p.Q p.C 0 n = n := by simp [AffineState]
      refine ⟨?_, ?_⟩
      · {
          intro _
          rw [hquot, htime, hstate, hD]
        }
      · {
          intro hodd
          exact False.elim (hodd heven)
        }
    }
  · {
      have hoddmod : n % 2 = 1 := by
        have hrange : n % 2 = 0 ∨ n % 2 = 1 := by
          have hnn : 0 ≤ n % 2 := Int.emod_nonneg n (by decide)
          have hlt : n % 2 < 2 := Int.emod_lt_of_pos n (by decide)
          omega
        rcases hrange with h0 | h1
        · {
            exact False.elim (heven ⟨n / 2, by
              have hdecomp := Int.ediv_add_emod n 2
              rw [h0] at hdecomp
              omega⟩)
          }
        · {
            exact h1
          }
      have hsum : 2 ∣ n + p.C := by
        have hmod : (n + p.C) % 2 = 0 := by
          rw [Int.add_emod, hoddmod, hmodc]
          decide
        exact ⟨(n + p.C) / 2, by
          have hdecomp := Int.ediv_add_emod (n + p.C) 2
          rw [hmod] at hdecomp
          omega⟩
      have hhit1 : IsFirstHit p n 1 := by
        refine ⟨?_, ?_⟩
        · {
            have hstate : AffineState p.Q p.C 1 n = n + p.C := by
              rw [hQ]
              simp [AffineState, TrapSum]
            rw [hstate, hD]
            exact hsum
          }
        · {
            intro i hi hdiv
            have hi0 : i = 0 := by omega
            rw [hi0] at hdiv
            have hstate : AffineState p.Q p.C 0 n = n := by simp [AffineState]
            rw [hstate, hD] at hdiv
            exact heven hdiv
          }
      have htime : FirstHitTime p hhit n = 1 := by
        have hle := Nat.find_le (p := fun t => IsFirstHit p n t) hhit1
        have hne : FirstHitTime p hhit n ≠ 0 := by
          intro h0
          have hspec := Nat.find_spec (hhit n)
          rw [h0] at hspec
          have hstate : AffineState p.Q p.C 0 n = n := by simp [AffineState]
          have hdiv : p.D ∣ n := by
            rw [← hstate]
            exact hspec.1
          rw [hD] at hdiv
          exact heven hdiv
        omega
      have hstate : AffineState p.Q p.C 1 n = n + p.C := by
        rw [hQ]
        simp [AffineState, TrapSum]
      refine ⟨?_, ?_⟩
      · {
          intro he
          exact False.elim (heven he)
        }
      · {
          intro _
          rw [hquot, htime, hstate, hD]
        }
    }

/-- For positive divisor `2`, a shell period is at most `|c|-1`, or `1` if `|c|=1`. -/
theorem TwoPositivePeriod (p : Parameters) (hQ : p.Q = 1) (hD : p.D = 2)
    (hcop : Nat.Coprime p.C.natAbs p.D.natAbs) (hp : 0 < p.C) (n : ℤ)
    (hn : n.natAbs ≤ p.C.natAbs) :
    let hhit := fun x : ℤ =>
      (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
    ∃ t period : ℕ, t ≤ 3 * p.C.natAbs ∧ 0 < period ∧
      period ≤ max (p.C.natAbs - 1) 1 ∧
      ∀ k : ℕ,
        Iterate (FirstReturn p hhit) (t + k) n =
          Iterate (FirstReturn p hhit) (t + k + period) n := by
  let hhit := fun x : ℤ =>
    (UnitCoprimeIsSmall p hQ hcop p.DAdmissible x).imp fun j h => h.1
  let H := FirstReturn p hhit
  let N := p.C.natAbs
  have hposC : p.C = N := by omega
  have hNodd : N % 2 = 1 := by
    have hne : ¬ 2 ∣ N := by
      intro hdvd
      have hgcd : Nat.gcd N 2 = 2 := Nat.gcd_eq_right hdvd
      have hone : Nat.gcd p.C.natAbs 2 = 1 := by
        simpa [hD] using hcop
      have hN : p.C.natAbs = N := by omega
      omega
    rcases Nat.mod_two_eq_zero_or_one N with h0 | h1
    · {
        exact False.elim (hne (Nat.dvd_of_mod_eq_zero h0))
      }
    · {
        exact h1
      }
  have hstep := fun z : ℤ => TwoDivisorStep p hQ hD hcop hp z
  have hnonneg : ∀ z : ℤ, 0 ≤ z → z.natAbs ≤ N → 0 ≤ H z := by
    intro z hz hzabs
    by_cases heven : 2 ∣ z
    · {
        rw [(hstep z).1 heven]
        omega
      }
    · {
        rw [(hstep z).2 heven]
        have hzle : z ≤ N := by omega
        omega
      }
  have hinterval : ∀ z : ℤ, 1 ≤ z → z ≤ N - 1 →
      1 ≤ H z ∧ H z ≤ N - 1 := by
    intro z hz1 hz2
    by_cases heven : 2 ∣ z
    · {
        rw [(hstep z).1 heven]
        have htwo : (2 : ℤ) ∣ z := heven
        omega
      }
    · {
        rw [(hstep z).2 heven]
        have hodd : z % 2 = 1 := by
          have hrange : z % 2 = 0 ∨ z % 2 = 1 := by
            have hnn : 0 ≤ z % 2 := Int.emod_nonneg z (by decide)
            have hlt : z % 2 < 2 := Int.emod_lt_of_pos z (by decide)
            omega
          rcases hrange with h0 | h1
          · {
              exact False.elim (heven ⟨z / 2, by
                have hdecomp := Int.ediv_add_emod z 2
                rw [h0] at hdecomp
                omega⟩)
            }
          · {
              exact h1
            }
        have hz2 : z ≤ N - 2 := by
          have htop : (N - 1) % 2 = 0 := by omega
          have hne : z ≠ N - 1 := by
            intro heq
            have hcast : ((N - 1 : ℕ) : ℤ) % 2 = 0 := by
              exact_mod_cast htop
            rw [heq] at hodd
            omega
          omega
        have hlo : 1 ≤ (z + p.C) / 2 := by
          have hsum : 1 + N ≤ z + p.C := by omega
          omega
        have hhi : (z + p.C) / 2 ≤ N - 1 := by
          have hsum : z + p.C ≤ 2 * N - 2 := by omega
          have hdecomp := Int.ediv_add_emod (z + p.C) 2
          have hnn : 0 ≤ (z + p.C) % 2 :=
            Int.emod_nonneg (z + p.C) (by decide)
          have hlt : (z + p.C) % 2 < 2 :=
            Int.emod_lt_of_pos (z + p.C) (by decide)
          omega
        omega
      }
  obtain ⟨t0, period0, ht0, hp0, _, hrep0⟩ :=
    UnitOffsetPeriodAtMostTwice p hQ hcop n hn
  let y := Iterate H t0 n
  have hyret : Iterate H period0 y = y := by
    have h0 := hrep0 0
    simpa [y, IterateAdd] using h0
  have hshell : ∀ z : ℤ, z.natAbs ≤ N → (H z).natAbs ≤ N := by
    intro z hz
    by_cases heven : 2 ∣ z
    · {
        rw [(hstep z).1 heven]
        have hmul : 2 * (z / 2) = z := Int.mul_ediv_cancel' heven
        have habs : z.natAbs = 2 * (z / 2).natAbs := by
          rw [← hmul, Int.natAbs_mul]
          simp
        omega
      }
    · {
        rw [(hstep z).2 heven]
        have hdecomp := Int.ediv_add_emod (z + p.C) 2
        have hnn : 0 ≤ (z + p.C) % 2 :=
          Int.emod_nonneg (z + p.C) (by decide)
        have hlt : (z + p.C) % 2 < 2 :=
          Int.emod_lt_of_pos (z + p.C) (by decide)
        have hlo : -N ≤ z := by omega
        have hhi : z ≤ N := by omega
        omega
      }
  have horb : ∀ s : ℕ, (Iterate H s n).natAbs ≤ N := by
    intro s
    induction s with
    | zero => {
        simpa [Iterate] using hn
      }
    | succ s ih => {
        rw [Iterate]
        exact hshell _ ih
      }
  have hyabs : y.natAbs ≤ N := by
    simpa [y] using horb t0
  have hyorbit : ∀ s : ℕ, (Iterate H s y).natAbs ≤ N := by
    intro s
    simpa [y, IterateAdd] using horb (t0 + s)
  have hstaypos : ∀ z : ℤ, 0 ≤ z → z.natAbs ≤ N →
      ∀ s : ℕ, 0 ≤ Iterate H s z ∧ (Iterate H s z).natAbs ≤ N := by
    intro z hz hzabs s
    induction s with
    | zero => {
        simp [Iterate]
        exact ⟨hz, hzabs⟩
      }
    | succ s ih => {
        rw [Iterate]
        exact ⟨hnonneg _ ih.1 ih.2, hshell _ ih.2⟩
      }
  have hypos : 0 ≤ y := by
    by_contra hneg
    have hall : ∀ j : ℕ, j ≤ period0 → Iterate H j y < 0 := by
      intro j hj
      by_contra hge
      have hge' : 0 ≤ Iterate H j y := by omega
      have hfrom :=
        (hstaypos _ hge' (hyorbit j)).1 (period0 - j)
      have hsum : j + (period0 - j) = period0 := by omega
      have hback :
          Iterate H period0 y =
            Iterate H (period0 - j) (Iterate H j y) := by
        rw [← hsum]
        simpa [IterateAdd]
      rw [hyret] at hback
      have hy0 : 0 ≤ y := by
        rw [hback]
        exact hfrom
      omega
    have hevenall : ∀ j : ℕ, j < period0 → 2 ∣ Iterate H j y := by
      intro j hj
      by_contra hodd
      have hnext : 0 ≤ H (Iterate H j y) := by
        rw [(hstep _).2 hodd]
        have hltj := hall j (Nat.le_of_lt hj)
        have habsj := hyorbit j
        omega
      have hId : Iterate H (j + 1) y = H (Iterate H j y) := by
        rw [Iterate]
      have hlt1 := hall (j + 1) (by omega)
      rw [hId] at hlt1
      omega
    have hdrop : ∀ j : ℕ, j < period0 →
        (Iterate H (j + 1) y).natAbs + 1 ≤
          (Iterate H j y).natAbs := by
      intro j hj
      have hz := hall j (Nat.le_of_lt hj)
      have heven := hevenall j hj
      have hmul : 2 * ((Iterate H j y) / 2) = Iterate H j y :=
        Int.mul_ediv_cancel' heven
      have habs : (Iterate H j y).natAbs =
          2 * ((Iterate H j y) / 2).natAbs := by
        rw [← hmul, Int.natAbs_mul]
        simp
      have hH : H (Iterate H j y) = (Iterate H j y) / 2 :=
        (hstep _).1 heven
      have hnext : Iterate H (j + 1) y = (Iterate H j y) / 2 := by
        rw [Iterate, hH]
      rw [hnext]
      omega
    have hloss : ∀ j : ℕ, j ≤ period0 →
        (Iterate H j y).natAbs + j ≤ y.natAbs := by
      intro j hj
      induction j with
      | zero => {
          simp [Iterate]
        }
      | succ j ih => {
          have hstepdrop := hdrop j (by omega)
          have ih' := ih (by omega)
          omega
        }
    have hfinal := hloss period0 (le_refl _)
    rw [hyret] at hfinal
    omega
  have hconstFix :
      ∀ z : ℤ, H z = z → z = Iterate H t0 n →
        ∀ k : ℕ, Iterate H (t0 + k) n = z := by
    intro z hfix hz k
    induction k with
    | zero => {
        simpa [Iterate] using hz.symm
      }
    | succ k ih => {
        rw [Nat.add_succ, Iterate, ih, hfix]
      }
  by_cases hzero : y = 0
  · {
      have hH0 : H 0 = 0 := by
        have he : 2 ∣ (0 : ℤ) := by decide
        simpa using (hstep 0).1 he
      refine ⟨t0, 1, ?_, by decide, ?_, ?_⟩
      · {
          omega
        }
      · {
          exact Nat.le_max_right (N - 1) 1
        }
      · {
          intro k
          have h1 := hconstFix 0 hH0 hzero k
          have h2 := hconstFix 0 hH0 hzero (k + 1)
          rw [h1, h2]
        }
    }
  · {
      by_cases htop : y = p.C
      · {
          have hnot : ¬ 2 ∣ p.C := by
            intro hdvd
            have hmod0 : p.C % 2 = 0 :=
              Int.emod_eq_zero_of_dvd hdvd
            have hmod1 : p.C % 2 = 1 := by
              have hcast : ((N : ℕ) : ℤ) % 2 = 1 := by
                exact_mod_cast hNodd
              simpa [hposC] using hcast
            omega
          have hHc : H p.C = p.C := by
            rw [(hstep p.C).2 hnot]
            omega
          refine ⟨t0, 1, ?_, by decide, ?_, ?_⟩
          · {
              omega
            }
          · {
              exact Nat.le_max_right (N - 1) 1
            }
          · {
              intro k
              have h1 := hconstFix p.C hHc htop k
              have h2 := hconstFix p.C hHc htop (k + 1)
              rw [h1, h2]
            }
        }
      · {
          have hN2 : 2 ≤ N := by
            by_contra hlt
            have hN1 : N = 1 := by omega
            have hy01 : y = 0 ∨ y = 1 := by omega
            rcases hy01 with h0 | h1
            · {
                exact hzero h0
              }
            · {
                have hc1 : p.C = 1 := by omega
                exact htop (h1.trans hc1.symm)
              }
          have hy1 : 1 ≤ y := by omega
          have hy2 : y ≤ N - 1 := by omega
          have hstayI : ∀ s : ℕ,
              1 ≤ Iterate H s y ∧ Iterate H s y ≤ N - 1 := by
            intro s
            induction s with
            | zero => {
                simp [Iterate]
                exact ⟨hy1, hy2⟩
              }
            | succ s ih => {
                rw [Iterate]
                exact hinterval _ ih.1 ih.2
              }
          let code : Fin N → Fin (N - 1) := fun i =>
            ⟨(Iterate H i.val y).toNat - 1, by
              have hs := hstayI i.val
              have hnn : 0 ≤ Iterate H i.val y := by omega
              have hto := Int.toNat_of_nonneg hnn
              omega⟩
          have hcard :
              Fintype.card (Fin (N - 1)) < Fintype.card (Fin N) := by
            simp
            omega
          obtain ⟨i, i', hne, heqc⟩ :=
            Fintype.exists_ne_map_eq_of_card_lt code hcard
          have hvals :
              Iterate H i.val y = Iterate H i'.val y := by
            have hcoe :
                (Iterate H i.val y).toNat =
                  (Iterate H i'.val y).toNat := by
              have := congrArg Fin.val heqc
              omega
            have hleft := Int.eq_natCast_toNat (a := Iterate H i.val y)
              (by omega)
            have hright :=
              Int.eq_natCast_toNat (a := Iterate H i'.val y) (by omega)
            rw [hleft, hright, hcoe]
          have horder : i.val < i'.val ∨ i'.val < i.val := by
            omega
          have hperiodOf : ∀ a b : ℕ, a < b → b < N →
              Iterate H a y = Iterate H b y →
              ∃ t period : ℕ, t ≤ 3 * N ∧ 0 < period ∧
                period ≤ max (N - 1) 1 ∧
                ∀ k : ℕ,
                  Iterate H (t + k) n =
                    Iterate H (t + k + period) n := by
            intro a b hab hb hsame
            refine ⟨t0 + a, b - a, ?_, ?_, ?_, ?_⟩
            · {
                omega
              }
            · {
                omega
              }
            · {
                have hle : b - a ≤ N - 1 := by omega
                exact Nat.le_trans hle (Nat.le_max_left (N - 1) 1)
              }
            · {
                intro k
                have hshift : ∀ m : ℕ,
                    Iterate H (a + m) y = Iterate H (b + m) y := by
                  intro m
                  induction m with
                  | zero => {
                      simpa [Iterate] using hsame
                    }
                  | succ m ih => {
                      rw [Nat.add_succ, Nat.add_succ, Iterate, Iterate, ih]
                    }
                have hleft :
                    Iterate H ((t0 + a) + k) n =
                      Iterate H (a + k) y := by
                  simpa [y, IterateAdd, Nat.add_assoc]
                have hright :
                    Iterate H ((t0 + a) + k + (b - a)) n =
                      Iterate H (b + k) y := by
                  have hidx : a + k + (b - a) = b + k := by omega
                  have hclk :
                      (t0 + a) + k + (b - a) =
                        t0 + (a + k + (b - a)) := by
                    omega
                  rw [hclk]
                  simpa [y, IterateAdd, hidx]
                rw [hleft, hright]
                exact hshift k
              }
          rcases horder with hlt | hgt
          · {
              have hb : i'.val < N := i'.isLt
              exact hperiodOf i.val i'.val hlt hb hvals
            }
          · {
              have hb : i.val < N := i.isLt
              exact hperiodOf i'.val i.val hgt hb hvals.symm
            }
        }
    }

Remark (class obstruction). Let `m = |D|`. The affine branch on `Z/mZ` is
`r ↦ Q r + C`. If some class never meets `0`, no integer of that class has a
first hit, so `EverySeedHits` fails and there is no total return on all of
`Z`. If some class meets `0` only at an exponent with `|Q|^j ≥ m`, no single
`A < m` bounds `|Q|^j` at every least hit. The inequality `|Q| ≥ 2` removes
neither alternative. `ClassMissesHasNoHit` is the missed-class half.
`OddTranslationNotEvery` is the instance `Q = 2`, `C = 1`, `D = 2`.
-/

end GeneralizedCollatz.SignedReturnUniform
