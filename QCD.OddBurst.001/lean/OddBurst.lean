-- SPDX-License-Identifier: CC-BY-4.0
import GeneralizedCollatz
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
Initial odd-burst occupation.

`Shortcut` halves an even input and sends an odd input to `(3n+1)/2`.
The initial odd-burst length of `n` is `0` when `n` is even and is
`v_2(n+1)` when `n` is odd. For a finite family of odd seeds at least `3`
whose burst lengths are at least `A`, the source-weighted square-root
occupation is at most `(2560/27)*(7/16)^A`. The source weights remain attached
to the original seeds throughout the proof.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.OddBurst

open Finset

/-- Halve an even input and send an odd input to the integer `(3n+1)/2`. -/
def Shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- An odd residue is not the even branch. -/
theorem NotEvenOfOdd (n : ℕ) (h : n % 2 = 1) : ¬ n % 2 = 0 := by
  intro hz
  have heq : (1 : ℕ) = 0 := by
    rw [← h, hz]
  exact Nat.one_ne_zero heq

/-- The odd branch is the integer `(3n+1)/2`. -/
theorem ShortcutOdd (n : ℕ) (h : n % 2 = 1) :
    Shortcut n = (3 * n + 1) / 2 := by
  simp [Shortcut, NotEvenOfOdd n h]

/-- The initial odd-burst length vanishes on an even seed and otherwise
records the exact power of `2` dividing `n + 1`. -/
def OddBurstLength (n : ℕ) : ℕ :=
  if n % 2 = 0 then 0 else padicValNat 2 (n + 1)

/-- The odd cofactor of `n + 1` after the burst power of `2` is removed.
The even-seed value is unused. -/
def OddBurstCofactor (n : ℕ) : ℕ :=
  if n % 2 = 0 then 0 else Nat.divMaxPow (n + 1) 2

/-- An even seed has an empty initial odd burst. -/
theorem OddBurstLengthEven (n : ℕ) (h : n % 2 = 0) :
    OddBurstLength n = 0 := by
  simp [OddBurstLength, h]

/-- On an odd seed the burst length is the `2`-adic valuation of `n + 1`. -/
theorem OddBurstLengthOfOdd (n : ℕ) (h : n % 2 = 1) :
    OddBurstLength n = padicValNat 2 (n + 1) := by
  rw [OddBurstLength, if_neg (NotEvenOfOdd n h)]

/-- On an odd seed the cofactor is `n + 1` with its factors `2` removed. -/
theorem OddBurstCofactorOfOdd (n : ℕ) (h : n % 2 = 1) :
    OddBurstCofactor n = Nat.divMaxPow (n + 1) 2 := by
  rw [OddBurstCofactor, if_neg (NotEvenOfOdd n h)]

/-- An odd seed has burst length at least one, since `n + 1` is even. -/
theorem OddBurstLengthGeOne (n : ℕ) (h : n % 2 = 1) :
    1 ≤ OddBurstLength n := by
  rw [OddBurstLengthOfOdd n h]
  have hne : n + 1 ≠ 0 := by omega
  have hdvd : 2 ^ 1 ∣ n + 1 := by
    have hmod : (n + 1) % 2 = 0 := by
      rw [← Nat.even_iff, Nat.even_add_one, Nat.not_even_iff]
      exact h
    simpa [pow_one] using Nat.dvd_of_mod_eq_zero hmod
  exact (Nat.pow_dvd_iff_le_padicValNat (by decide : (2 : ℕ) ≠ 1) hne).1 hdvd

/-- Odd data reconstruct `n + 1` and leave an odd cofactor. -/
theorem OddBurstSplit (n : ℕ) (h : n % 2 = 1) :
    2 ^ OddBurstLength n * OddBurstCofactor n = n + 1 ∧
      OddBurstCofactor n % 2 = 1 := by
  rw [OddBurstLengthOfOdd n h, OddBurstCofactorOfOdd n h]
  have hne : n + 1 ≠ 0 := by omega
  refine ⟨Nat.pow_padicValNat_mul_divMaxPow 2 (n + 1), ?_⟩
  have hnot : ¬ 2 ∣ Nat.divMaxPow (n + 1) 2 :=
    Nat.not_dvd_divMaxPow (by decide : 1 < 2) hne
  exact Nat.two_dvd_ne_zero.mp hnot

/-- The odd cofactor is a positive odd integer. -/
theorem OddBurstCofactorPos (n : ℕ) (h : n % 2 = 1) :
    1 ≤ OddBurstCofactor n := by
  have hmod : OddBurstCofactor n % 2 = 1 := (OddBurstSplit n h).2
  have hne : OddBurstCofactor n ≠ 0 := by
    intro h0
    rw [h0] at hmod
    norm_num at hmod
  exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)

/-- `2t - 1` is odd once `t` is positive. -/
theorem TwoMulSubOneMod (t : ℕ) (ht : 1 ≤ t) : (2 * t - 1) % 2 = 1 := by
  have hrewrite : 2 * t - 1 = 2 * (t - 1) + 1 := by omega
  rw [hrewrite, Nat.add_mod,
    Nat.mod_eq_zero_of_dvd (dvd_mul_right 2 (t - 1)), Nat.zero_add, Nat.mod_mod]

/-- The odd-branch numerator at height `2t` is twice the next lowered height. -/
theorem ThreeOddStep (t : ℕ) (ht : 1 ≤ t) :
    3 * (2 * t - 1) + 1 = 2 * (3 * t - 1) := by
  omega

/-- Through the burst, the shortcut satisfies
`T^j(n) + 1 = 3^j * 2^(A(n) - j) * u(n)`. -/
theorem OddBurstClosedForm (n j : ℕ) (hn : n % 2 = 1)
    (hj : j ≤ OddBurstLength n) :
    Iterate Shortcut j n + 1 =
      3 ^ j * 2 ^ (OddBurstLength n - j) * OddBurstCofactor n := by
  suffices ∀ k, k ≤ OddBurstLength n →
      Iterate Shortcut k n + 1 =
        3 ^ k * 2 ^ (OddBurstLength n - k) * OddBurstCofactor n by
    exact this j hj
  intro k
  induction k with
  | zero => {
      intro _hk
      simp only [Iterate, pow_zero, Nat.sub_zero, one_mul]
      exact (OddBurstSplit n hn).1.symm
    }
  | succ k ih => {
      intro hk
      set a := OddBurstLength n
      set u := OddBurstCofactor n
      have hkLe : k ≤ a := Nat.le_of_succ_le hk
      have ihv := ih hkLe
      set e := a - (k + 1)
      have hpow : a - k = e + 1 := by omega
      have htpos : 1 ≤ 3 ^ k * 2 ^ e * u := by
        have h3 : 0 < 3 ^ k := pow_pos (by decide : 0 < 3) k
        have h2 : 0 < 2 ^ e := pow_pos (by decide : 0 < 2) e
        have hu : 0 < u := by
          have hcof := OddBurstCofactorPos n hn
          omega
        exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos h3 h2) hu)
      set t := 3 ^ k * 2 ^ e * u with ht
      have htwo : 3 ^ k * 2 ^ (a - k) * u = 2 * t := by
        rw [hpow, Nat.pow_succ, ht]
        calc
          3 ^ k * (2 ^ e * 2) * u = 3 ^ k * (2 * 2 ^ e) * u := by
            rw [Nat.mul_comm (2 ^ e) 2]
          _ = (3 ^ k * 2) * 2 ^ e * u := by
            rw [← Nat.mul_assoc]
          _ = (2 * 3 ^ k) * 2 ^ e * u := by
            rw [Nat.mul_comm (3 ^ k) 2]
          _ = 2 * (3 ^ k * 2 ^ e * u) := by
            simp only [Nat.mul_assoc]
      have hstate : Iterate Shortcut k n = 2 * t - 1 := by
        have heq : Iterate Shortcut k n + 1 = 2 * t := by
          rw [ihv, htwo]
        omega
      have hodd : Iterate Shortcut k n % 2 = 1 := by
        rw [hstate]
        exact TwoMulSubOneMod t htpos
      have hnum : 3 * Iterate Shortcut k n + 1 = 2 * (3 * t - 1) := by
        rw [hstate]
        exact ThreeOddStep t htpos
      have hnext : Iterate Shortcut (k + 1) n = 3 * t - 1 := by
        simp only [Iterate]
        rw [ShortcutOdd _ hodd, hnum]
        exact Nat.mul_div_cancel_left (3 * t - 1) (by decide : 0 < 2)
      have hsucc : Iterate Shortcut (k + 1) n + 1 = 3 * t := by
        rw [hnext]
        have h3t : 1 ≤ 3 * t := by omega
        omega
      rw [hsucc]
      calc
        3 * t = 3 * (3 ^ k * 2 ^ e * u) := by rw [ht]
        _ = (3 * 3 ^ k) * 2 ^ e * u := by
          rw [← Nat.mul_assoc, ← Nat.mul_assoc]
        _ = 3 ^ (k + 1) * 2 ^ e * u := by
          rw [← Nat.pow_succ']
    }

/-- Before the burst ends, the shortcut state is strictly below its closed height. -/
theorem OddBurstStateLt (n j : ℕ) (hn : n % 2 = 1) (hj : j < OddBurstLength n) :
    Iterate Shortcut j n <
      3 ^ j * 2 ^ (OddBurstLength n - j) * OddBurstCofactor n := by
  have hform := OddBurstClosedForm n j hn (Nat.le_of_lt hj)
  have h3 : 0 < 3 ^ j := pow_pos (by decide : 0 < 3) j
  have h2 : 0 < 2 ^ (OddBurstLength n - j) :=
    pow_pos (by decide : 0 < 2) _
  have hu : 0 < OddBurstCofactor n := by
    have hcof := OddBurstCofactorPos n hn
    omega
  have hpos :
      0 < 3 ^ j * 2 ^ (OddBurstLength n - j) * OddBurstCofactor n :=
    Nat.mul_pos (Nat.mul_pos h3 h2) hu
  omega

/-- Every strict prefix of the burst is odd. -/
theorem OddBurstOddUntilExit (n j : ℕ) (hn : n % 2 = 1)
    (hj : j < OddBurstLength n) :
    Iterate Shortcut j n % 2 = 1 := by
  have hform := OddBurstClosedForm n j hn (Nat.le_of_lt hj)
  have hge : 1 ≤ OddBurstLength n - j := by omega
  have hdvdPow : 2 ^ 1 ∣ 2 ^ (OddBurstLength n - j) := pow_dvd_pow 2 hge
  have hdvd :
      2 ∣ 3 ^ j * 2 ^ (OddBurstLength n - j) * OddBurstCofactor n := by
    refine dvd_mul_of_dvd_left ?_ _
    exact dvd_mul_of_dvd_right (by simpa [pow_one] using hdvdPow) _
  have hmod : (Iterate Shortcut j n + 1) % 2 = 0 := by
    rw [hform]
    exact Nat.mod_eq_zero_of_dvd hdvd
  rcases Nat.mod_two_eq_zero_or_one (Iterate Shortcut j n) with h0 | h1
  · {
    exfalso
    have hsucc : (Iterate Shortcut j n + 1) % 2 = 1 := by
      rw [Nat.add_mod, h0, Nat.zero_add]
    have hcontr : (0 : ℕ) = 1 := by
      rw [← hmod, hsucc]
    exact Nat.zero_ne_one hcontr
  }
  · { exact h1 }

/-- The first state at time `A(n)` is even. -/
theorem OddBurstExitEven (n : ℕ) (hn : n % 2 = 1) :
    Iterate Shortcut (OddBurstLength n) n % 2 = 0 := by
  have hform :=
    OddBurstClosedForm n (OddBurstLength n) hn (Nat.le_refl _)
  have hpow : ∀ k : ℕ, (3 ^ k) % 2 = 1 := by
    intro k
    induction k with
    | zero => { simp }
    | succ k ih => {
        rw [pow_succ, Nat.mul_mod, ih]
      }
  have hu : OddBurstCofactor n % 2 = 1 := (OddBurstSplit n hn).2
  have hprod :
      (3 ^ OddBurstLength n * OddBurstCofactor n) % 2 = 1 := by
    rw [Nat.mul_mod, hpow, hu]
  have hclosed : Iterate Shortcut (OddBurstLength n) n + 1 =
      3 ^ OddBurstLength n * OddBurstCofactor n := by
    simpa [pow_zero, Nat.sub_self, one_mul] using hform
  have hmod : (Iterate Shortcut (OddBurstLength n) n + 1) % 2 = 1 := by
    rw [hclosed]
    exact hprod
  exact (Nat.succ_mod_two_eq_one_iff).mp hmod

noncomputable section

/-- Source weight `2/(n(n-1))`, used for seeds `n ≥ 3`. -/
def SourceAtom (n : ℕ) : ℝ :=
  2 / ((n : ℝ) * ((n : ℝ) - 1))

/-- Square-root occupation of the initial odd burst. -/
def BurstSqrtOccupation (n : ℕ) : ℝ :=
  ∑ j ∈ range (OddBurstLength n), Real.sqrt ((Iterate Shortcut j n : ℕ) : ℝ)

/-- Reciprocal odd weight `1/(u√u)`. -/
def OddRecip (u : ℕ) : ℝ :=
  1 / ((u : ℝ) * Real.sqrt (u : ℝ))

/-- One step of the odd-cofactor telescope. -/
def OddGap (m : ℕ) : ℝ :=
  1 / Real.sqrt (2 * (m : ℝ) + 1) - 1 / Real.sqrt (2 * (m : ℝ) + 3)

/-- The inequality that produces `7/16`: `√3/4 < 7/16`. -/
theorem SqrtThreeOverFourLtSevenSixteenths :
    Real.sqrt 3 / 4 < (7 : ℝ) / 16 := by
  have hsqrt : Real.sqrt 3 < 7 / 4 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 7 / 4)]
    norm_num
  have hdiv := div_lt_div_of_pos_right hsqrt (by norm_num : (0 : ℝ) < 4)
  have hrewrite : (7 : ℝ) / 4 / 4 = 7 / 16 := by norm_num
  exact hdiv.trans_eq hrewrite

/-- The fifth comparison `√(3/2) - 1 > 1/5`, used to replace the geometric
denominator. -/
theorem SqrtThreeHalvesSubOneGtOneFifth :
    Real.sqrt ((3 : ℝ) / 2) - 1 > 1 / 5 := by
  have hsqrt : (6 : ℝ) / 5 < Real.sqrt ((3 : ℝ) / 2) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 6 / 5)]
    norm_num
  linarith

/-- The reciprocal of `√(3/2) - 1` is strictly less than `5`. -/
theorem ReciprocalSqrtThreeHalvesLtFive :
    (1 : ℝ) / (Real.sqrt ((3 : ℝ) / 2) - 1) < 5 := by
  have hgt := SqrtThreeHalvesSubOneGtOneFifth
  have hpos : 0 < Real.sqrt ((3 : ℝ) / 2) - 1 := by linarith
  rw [div_lt_iff₀ hpos]
  linarith

/-- Square roots commute with nonnegative powers. -/
theorem SqrtPow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => { simp }
  | succ n ih => {
      rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih]
    }

/-- Closed height has square root `√u * (√2)^a * (√(3/2))^j`. -/
theorem SqrtHeight (j a u : ℕ) (hj : j ≤ a) :
    Real.sqrt ((3 ^ j * 2 ^ (a - j) * u : ℕ) : ℝ) =
      Real.sqrt (u : ℝ) * (Real.sqrt 2) ^ a *
        (Real.sqrt ((3 : ℝ) / 2)) ^ j := by
  have hcast :
      ((3 ^ j * 2 ^ (a - j) * u : ℕ) : ℝ) =
        (3 : ℝ) ^ j * (2 : ℝ) ^ (a - j) * (u : ℝ) := by
    simp [Nat.cast_mul, Nat.cast_pow]
  rw [hcast,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ j * (2 : ℝ) ^ (a - j)),
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ j)]
  rw [SqrtPow (3 : ℝ) (by positivity) j, SqrtPow (2 : ℝ) (by positivity) (a - j)]
  have hsqrt3 : Real.sqrt 3 = Real.sqrt 2 * Real.sqrt ((3 : ℝ) / 2) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    norm_num
  have hexp : a - j + j = a := by omega
  calc
    (Real.sqrt 3) ^ j * (Real.sqrt 2) ^ (a - j) * Real.sqrt (u : ℝ)
      = Real.sqrt (u : ℝ) *
          ((Real.sqrt 2) ^ (a - j) * (Real.sqrt 3) ^ j) := by ring
    _ = Real.sqrt (u : ℝ) * ((Real.sqrt 2) ^ (a - j) *
          (Real.sqrt 2 * Real.sqrt ((3 : ℝ) / 2)) ^ j) := by
        rw [hsqrt3]
    _ = Real.sqrt (u : ℝ) * ((Real.sqrt 2) ^ (a - j) *
          ((Real.sqrt 2) ^ j * (Real.sqrt ((3 : ℝ) / 2)) ^ j)) := by
        rw [mul_pow]
    _ = Real.sqrt (u : ℝ) * ((Real.sqrt 2) ^ a *
          (Real.sqrt ((3 : ℝ) / 2)) ^ j) := by
        rw [← mul_assoc (Real.sqrt 2 ^ (a - j)) (Real.sqrt 2 ^ j)
          (Real.sqrt ((3 : ℝ) / 2) ^ j), ← pow_add, hexp]
    _ = Real.sqrt (u : ℝ) * (Real.sqrt 2) ^ a *
          (Real.sqrt ((3 : ℝ) / 2)) ^ j := by ring

/-- The burst of closed heights is strictly below `5 √u (√3)^a`. -/
theorem HeightSqrtSumLt (a u : ℕ) (_ha : 1 ≤ a) (hu : 1 ≤ u) :
    (∑ j ∈ range a, Real.sqrt ((3 ^ j * 2 ^ (a - j) * u : ℕ) : ℝ)) <
      5 * Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a := by
  set r : ℝ := Real.sqrt ((3 : ℝ) / 2)
  have hr1 : 1 < r := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  have hrne : r ≠ 1 := ne_of_gt hr1
  have hposr : 0 < r - 1 := by linarith
  have hsumEq :
      (∑ j ∈ range a, Real.sqrt ((3 ^ j * 2 ^ (a - j) * u : ℕ) : ℝ)) =
        Real.sqrt (u : ℝ) * (Real.sqrt 2) ^ a * ∑ j ∈ range a, r ^ j := by
    calc
      (∑ j ∈ range a, Real.sqrt ((3 ^ j * 2 ^ (a - j) * u : ℕ) : ℝ))
        = ∑ j ∈ range a, Real.sqrt (u : ℝ) * (Real.sqrt 2) ^ a * r ^ j := by
          refine sum_congr rfl ?_
          intro j hj
          have hjle : j ≤ a := Nat.le_of_lt (mem_range.mp hj)
          simpa [r] using SqrtHeight j a u hjle
      _ = Real.sqrt (u : ℝ) * (Real.sqrt 2) ^ a * ∑ j ∈ range a, r ^ j := by
        rw [← mul_sum]
  have hgeom : ∑ j ∈ range a, r ^ j = (r ^ a - 1) / (r - 1) :=
    geom_sum_eq hrne a
  have hltgeom : (r ^ a - 1) / (r - 1) < r ^ a / (r - 1) := by
    have hnum : r ^ a - 1 < r ^ a := by linarith
    exact div_lt_div_of_pos_right hnum hposr
  have hc0 : 0 < Real.sqrt (u : ℝ) * (Real.sqrt 2) ^ a := by
    have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
    positivity
  have hsumLt :
      Real.sqrt (u : ℝ) * (Real.sqrt 2) ^ a * ∑ j ∈ range a, r ^ j <
        Real.sqrt (u : ℝ) * (Real.sqrt 2) ^ a * (r ^ a / (r - 1)) := by
    rw [hgeom]
    exact mul_lt_mul_of_pos_left hltgeom hc0
  have hbase : Real.sqrt 2 * r = Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    norm_num
  have hfac :
      Real.sqrt (u : ℝ) * (Real.sqrt 2) ^ a * (r ^ a / (r - 1)) =
        Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a / (r - 1) := by
    calc
      Real.sqrt (u : ℝ) * (Real.sqrt 2) ^ a * (r ^ a / (r - 1))
        = (Real.sqrt (u : ℝ) * ((Real.sqrt 2) ^ a * r ^ a)) / (r - 1) := by
          rw [← mul_div_assoc, mul_assoc]
      _ = (Real.sqrt (u : ℝ) * (Real.sqrt 2 * r) ^ a) / (r - 1) := by
        rw [← mul_pow]
      _ = Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a / (r - 1) := by
        rw [hbase]
  have hfive :
      Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a / (r - 1) <
        5 * Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a := by
    have hrec := ReciprocalSqrtThreeHalvesLtFive
    have hcoeff : 0 < Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a := by
      have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
      positivity
    have hmul := mul_lt_mul_of_pos_left hrec hcoeff
    have hrewrite :
        Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a / (r - 1) =
          Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a *
            (1 / (r - 1)) := by
      rw [div_eq_mul_inv, ← one_div]
    rw [hrewrite]
    have hcomm :
        Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a * 5 =
          5 * Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a := by ring
    rw [hcomm] at hmul
    exact hmul
  have hnext :
      Real.sqrt (u : ℝ) * (Real.sqrt 2) ^ a * (r ^ a / (r - 1)) <
        5 * Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a := by
    rw [hfac]
    exact hfive
  rw [hsumEq]
  exact hsumLt.trans hnext

/-- Occupation of one odd burst is strictly below the closed-height sum. -/
theorem BurstSqrtOccupationLt (n : ℕ) (hn : n % 2 = 1) :
    BurstSqrtOccupation n <
      ∑ j ∈ range (OddBurstLength n),
        Real.sqrt ((3 ^ j * 2 ^ (OddBurstLength n - j) *
          OddBurstCofactor n : ℕ) : ℝ) := by
  unfold BurstSqrtOccupation
  have ha : 1 ≤ OddBurstLength n := OddBurstLengthGeOne n hn
  have hne : (range (OddBurstLength n)).Nonempty :=
    nonempty_range_iff.2 (by omega)
  refine sum_lt_sum_of_nonempty hne ?_
  intro j hj
  have hlt := OddBurstStateLt n j hn (mem_range.mp hj)
  have hcast :
      ((Iterate Shortcut j n : ℕ) : ℝ) <
        ((3 ^ j * 2 ^ (OddBurstLength n - j) * OddBurstCofactor n : ℕ) : ℝ) :=
    by exact_mod_cast hlt
  exact Real.sqrt_lt_sqrt (Nat.cast_nonneg _) hcast

/-- For `n ≥ 3`, the source weight is at most `16/(3(n+1)^2)`. -/
theorem SourceAtomBound (n : ℕ) (h3 : 3 ≤ n) :
    SourceAtom n ≤ 16 / (3 * ((n : ℝ) + 1) ^ 2) := by
  have hn : (3 : ℝ) ≤ n := by exact_mod_cast h3
  have hlow1 : (3 / 4) * ((n : ℝ) + 1) ≤ (n : ℝ) := by
    have hrew : (3 / 4) * ((n : ℝ) + 1) = 3 * ((n : ℝ) + 1) / 4 := by ring
    rw [hrew, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hlow2 : (1 / 2) * ((n : ℝ) + 1) ≤ (n : ℝ) - 1 := by
    have hrew : (1 / 2) * ((n : ℝ) + 1) = ((n : ℝ) + 1) / 2 := by ring
    rw [hrew, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hprod :
      (3 / 4) * ((n : ℝ) + 1) * ((1 / 2) * ((n : ℝ) + 1)) ≤
        (n : ℝ) * ((n : ℝ) - 1) :=
    mul_le_mul_of_nonneg' hlow1 hlow2 (by positivity) (by positivity)
  have heq :
      (3 / 4) * ((n : ℝ) + 1) * ((1 / 2) * ((n : ℝ) + 1)) =
        (3 / 8) * ((n : ℝ) + 1) ^ 2 := by ring
  have hthree : (3 / 8) * ((n : ℝ) + 1) ^ 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    rw [← heq]
    exact hprod
  have hposL : (0 : ℝ) < (3 / 8) * ((n : ℝ) + 1) ^ 2 := by positivity
  have hposR : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have hsub : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    exact mul_pos (by linarith) hsub
  have hinv :
      1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤
        1 / ((3 / 8) * ((n : ℝ) + 1) ^ 2) := by
    rw [one_div, one_div]
    exact (inv_le_inv₀ hposR hposL).2 hthree
  have htwo := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
  have hsrc : SourceAtom n = 2 * (1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
    unfold SourceAtom
    rw [div_eq_mul_inv, one_div]
  have hright :
      2 * (1 / ((3 / 8) * ((n : ℝ) + 1) ^ 2)) =
        16 / (3 * ((n : ℝ) + 1) ^ 2) := by
    have hinv38 : ((3 / 8 : ℝ)⁻¹) = 8 / 3 := by norm_num
    calc
      2 * (1 / ((3 / 8) * ((n : ℝ) + 1) ^ 2))
        = 2 * (((3 / 8 : ℝ)⁻¹) * (((n : ℝ) + 1) ^ 2)⁻¹) := by
          rw [div_eq_mul_inv, mul_inv, one_mul]
      _ = 2 * ((8 / 3) * (((n : ℝ) + 1) ^ 2)⁻¹) := by rw [hinv38]
      _ = (16 / 3) / ((n : ℝ) + 1) ^ 2 := by
        rw [← mul_assoc, ← div_eq_mul_inv]
        have hnum : (2 : ℝ) * (8 / 3) = 16 / 3 := by norm_num
        rw [hnum]
      _ = 16 / (3 * ((n : ℝ) + 1) ^ 2) := by
        rw [div_div]
  rw [hsrc]
  exact htwo.trans_eq hright

/-- After the odd splitting, the source weight is at most `16/(3*4^A(n)*u(n)^2)`. -/
theorem SourceAtomSplit (n : ℕ) (h3 : 3 ≤ n) (hodd : n % 2 = 1) :
    SourceAtom n ≤ 16 / (3 * (4 : ℝ) ^ OddBurstLength n *
      (OddBurstCofactor n : ℝ) ^ 2) := by
  have hbound := SourceAtomBound n h3
  have hsplit := (OddBurstSplit n hodd).1
  have hcast : ((n : ℝ) + 1) =
      (2 : ℝ) ^ OddBurstLength n * OddBurstCofactor n := by
    exact_mod_cast hsplit.symm
  have hsq : ((n : ℝ) + 1) ^ 2 =
      (4 : ℝ) ^ OddBurstLength n * (OddBurstCofactor n : ℝ) ^ 2 := by
    rw [hcast, mul_pow]
    have hpow : ((2 : ℝ) ^ OddBurstLength n) ^ 2 =
        (4 : ℝ) ^ OddBurstLength n := by
      rw [← pow_mul, show OddBurstLength n * 2 = 2 * OddBurstLength n by
        exact Nat.mul_comm _ _, pow_mul]
      norm_num
    rw [hpow]
  rw [hsq] at hbound
  simpa [mul_assoc] using hbound

/-- The weighted closed-height product is the odd reciprocal times `(√3/4)^a`. -/
theorem BurstMassConstant (a : ℕ) {u : ℝ} (hu : 0 < u) :
    (16 / (3 * (4 : ℝ) ^ a * u ^ 2)) *
        (5 * Real.sqrt u * (Real.sqrt 3) ^ a) =
      (80 / 3) * ((Real.sqrt 3 / 4) ^ a) * (1 / (u * Real.sqrt u)) := by
  set S : ℝ := Real.sqrt u
  set Q : ℝ := (Real.sqrt 3) ^ a
  set A : ℝ := (4 : ℝ) ^ a
  have hS : 0 < S := Real.sqrt_pos.mpr hu
  have hsq : S * S = u := Real.mul_self_sqrt hu.le
  have hdiv : (Real.sqrt 3 / 4) ^ a = Q / A := by
    simp [Q, A, div_pow]
  rw [hdiv]
  have hleft :
      16 / (3 * A * u ^ 2) * (5 * S * Q) = (80 * S * Q) / (3 * A * u ^ 2) := by
    rw [div_mul_eq_mul_div]
    congr 1
    ring
  have hright :
      (80 / 3) * (Q / A) * (1 / (u * S)) = (80 * S * Q) / (3 * A * u ^ 2) := by
    have hstep : (80 / 3) * (Q / A) = (80 * Q) / (3 * A) := by
      calc
        (80 / 3) * (Q / A) = (80 / 3) * Q / A := by
          rw [← mul_div_assoc]
        _ = (80 * Q / 3) / A := by
          rw [div_mul_eq_mul_div]
        _ = 80 * Q / (3 * A) := by
          rw [div_div]
    rw [hstep]
    have hdenL : u * S * (3 * A) ≠ 0 := by positivity
    have hdenR : 3 * A * u ^ 2 ≠ 0 := by positivity
    have hfrac :
        (80 * Q) / (3 * A) * (1 / (u * S)) = (80 * Q) / (u * S * (3 * A)) := by
      rw [div_mul_eq_mul_div, mul_one_div, div_div]
    rw [hfrac]
    apply (div_eq_div_iff hdenL hdenR).2
    calc
      80 * Q * (3 * A * u ^ 2) = 80 * Q * 3 * A * u * u := by ring
      _ = 80 * Q * 3 * A * u * (S * S) := by rw [hsq]
      _ = 80 * S * Q * (u * S * (3 * A)) := by ring
  exact hleft.trans hright.symm

/-- One odd seed of burst length `a` contributes strictly less than
`(80/3)*(7/16)^a/(u√u)`. -/
theorem OneBurstMass (n : ℕ) (h3 : 3 ≤ n) (hodd : n % 2 = 1) :
    SourceAtom n * BurstSqrtOccupation n <
      (80 / 3) * ((7 : ℝ) / 16) ^ OddBurstLength n *
        OddRecip (OddBurstCofactor n) := by
  set a := OddBurstLength n
  set u := OddBurstCofactor n
  have ha : 1 ≤ a := OddBurstLengthGeOne n hodd
  have hu : 1 ≤ u := OddBurstCofactorPos n hodd
  have hocc := BurstSqrtOccupationLt n hodd
  have hheight := HeightSqrtSumLt a u ha hu
  have htrans : BurstSqrtOccupation n <
      5 * Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a := hocc.trans hheight
  have hsource := SourceAtomSplit n h3 hodd
  have hCpos : 0 < 16 / (3 * (4 : ℝ) ^ a * (u : ℝ) ^ 2) := by positivity
  have hocc0 : 0 ≤ BurstSqrtOccupation n := by
    unfold BurstSqrtOccupation
    exact sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hle : SourceAtom n * BurstSqrtOccupation n ≤
      16 / (3 * (4 : ℝ) ^ a * (u : ℝ) ^ 2) * BurstSqrtOccupation n :=
    mul_le_mul_of_nonneg_right hsource hocc0
  have hlt : 16 / (3 * (4 : ℝ) ^ a * (u : ℝ) ^ 2) * BurstSqrtOccupation n <
      16 / (3 * (4 : ℝ) ^ a * (u : ℝ) ^ 2) *
        (5 * Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a) :=
    mul_lt_mul_of_pos_left htrans hCpos
  have hconst := BurstMassConstant a (by exact_mod_cast hu : (0 : ℝ) < u)
  have hpow : (Real.sqrt 3 / 4) ^ a < ((7 : ℝ) / 16) ^ a :=
    pow_lt_pow_left₀ SqrtThreeOverFourLtSevenSixteenths (by positivity)
      (by omega)
  have hbase := mul_lt_mul_of_pos_left hpow (by norm_num : (0 : ℝ) < 80 / 3)
  have hrecpos : 0 < OddRecip u := by
    have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
    unfold OddRecip
    positivity
  have hreplace := mul_lt_mul_of_pos_right hbase hrecpos
  have hrecip : 1 / ((u : ℝ) * Real.sqrt (u : ℝ)) = OddRecip u := by
    simp [OddRecip]
  have hwritten :
      (80 / 3) * ((Real.sqrt 3 / 4) ^ a) *
          (1 / ((u : ℝ) * Real.sqrt (u : ℝ))) =
        (80 / 3) * (Real.sqrt 3 / 4) ^ a * OddRecip u := by
    rw [hrecip]
  have hfinal :
      16 / (3 * (4 : ℝ) ^ a * (u : ℝ) ^ 2) *
          (5 * Real.sqrt (u : ℝ) * (Real.sqrt 3) ^ a) <
        (80 / 3) * ((7 : ℝ) / 16) ^ a * OddRecip u := by
    rw [hconst, hwritten]
    exact hreplace
  exact hle.trans_lt (hlt.trans hfinal)

/-- The odd reciprocal is nonnegative, including at the unused value `0`. -/
theorem OddRecipNonneg (u : ℕ) : 0 ≤ OddRecip u := by
  by_cases hu : u = 0
  · subst hu
    simp [OddRecip]
  · have hpos : (0 : ℝ) < u := by exact_mod_cast Nat.pos_of_ne_zero hu
    unfold OddRecip
    positivity

/-- An odd integer at least `3` is strictly below one telescope step. -/
theorem OddTermLtGap (m : ℕ) : OddRecip (2 * m + 3) < OddGap m := by
  set a : ℝ := 2 * (m : ℝ) + 1
  set b : ℝ := a + 2
  have hb : b = 2 * (m : ℝ) + 3 := by
    dsimp [a, b]
    ring
  have ha : 0 < a := by positivity
  have hbpos : 0 < b := by positivity
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbpos
  have hsum : 0 < Real.sqrt a + Real.sqrt b := add_pos hsa hsb
  have hsq : (Real.sqrt b) ^ 2 - (Real.sqrt a) ^ 2 = b - a := by
    rw [Real.sq_sqrt hbpos.le, Real.sq_sqrt ha.le]
  have hdiff : Real.sqrt b - Real.sqrt a =
      (b - a) / (Real.sqrt a + Real.sqrt b) := by
    rw [eq_div_iff_mul_eq hsum.ne']
    have hdiffsq : (Real.sqrt b - Real.sqrt a) *
        (Real.sqrt b + Real.sqrt a) =
        (Real.sqrt b) ^ 2 - (Real.sqrt a) ^ 2 := by ring
    rw [add_comm (Real.sqrt a) (Real.sqrt b), hdiffsq, hsq]
  have hsub : 1 / Real.sqrt a - 1 / Real.sqrt b =
      (Real.sqrt b - Real.sqrt a) / (Real.sqrt a * Real.sqrt b) := by
    have hden : Real.sqrt a * Real.sqrt b ≠ 0 := mul_ne_zero hsa.ne' hsb.ne'
    rw [eq_div_iff_mul_eq hden]
    rw [sub_mul]
    have h1 : (1 / Real.sqrt a) * (Real.sqrt a * Real.sqrt b) = Real.sqrt b := by
      rw [← mul_assoc, div_mul_cancel₀ _ hsa.ne', one_mul]
    have h2 : (1 / Real.sqrt b) * (Real.sqrt a * Real.sqrt b) = Real.sqrt a := by
      rw [mul_left_comm, div_mul_cancel₀ _ hsb.ne', mul_one]
    rw [h1, h2]
  have hba : b - a = 2 := by
    dsimp [b]
    ring
  have hgap : OddGap m =
      2 / ((Real.sqrt a + Real.sqrt b) * Real.sqrt a * Real.sqrt b) := by
    unfold OddGap
    rw [show (2 * (m : ℝ) + 1) = a by rfl, ← hb, hsub, hdiff, hba, div_div,
      mul_assoc]
  have hdenG : 0 < (Real.sqrt a + Real.sqrt b) * Real.sqrt a * Real.sqrt b := by
    positivity
  have hdenT : 0 < b * Real.sqrt b := by positivity
  have hcmp : (Real.sqrt a + Real.sqrt b) * Real.sqrt a < 2 * b := by
    have hsumsq : (Real.sqrt a + Real.sqrt b) * Real.sqrt a =
        a + Real.sqrt (a * b) := by
      rw [add_mul, Real.mul_self_sqrt ha.le,
        mul_comm (Real.sqrt b) (Real.sqrt a), ← Real.sqrt_mul ha.le]
    rw [hsumsq]
    have h2b : 2 * b = a + (a + 4) := by
      dsimp [b]
      ring
    rw [h2b, add_lt_add_iff_left]
    have hnonneg : 0 ≤ a + 4 := by positivity
    have hsqrtnn : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
    rw [← sq_lt_sq₀ hsqrtnn hnonneg, Real.sq_sqrt (mul_nonneg ha.le hbpos.le)]
    have hpoly : (a + 4) ^ 2 - a * b = 6 * a + 16 := by
      dsimp [b]
      ring
    have hpos : 0 < 6 * a + 16 := by positivity
    linarith
  have hmul : (Real.sqrt a + Real.sqrt b) * Real.sqrt a * Real.sqrt b <
      2 * b * Real.sqrt b :=
    mul_lt_mul_of_pos_right hcmp hsb
  have hcross : 1 * ((Real.sqrt a + Real.sqrt b) * Real.sqrt a * Real.sqrt b) <
      2 * (b * Real.sqrt b) := by
    simpa [one_mul, mul_assoc] using hmul
  have hfrac : 1 / (b * Real.sqrt b) <
      2 / ((Real.sqrt a + Real.sqrt b) * Real.sqrt a * Real.sqrt b) :=
    (div_lt_div_iff₀ hdenT hdenG).2 hcross
  have hcast : ((2 * m + 3 : ℕ) : ℝ) = b := by
    rw [hb]
    simp
  unfold OddRecip
  rw [hcast, hgap]
  simpa using hfrac

/-- The telescope sums to `1 - 1/√(2K+1)`. -/
theorem OddGapSum (K : ℕ) :
    ∑ m ∈ range K, OddGap m = 1 - 1 / Real.sqrt (2 * (K : ℝ) + 1) := by
  induction K with
  | zero => { simp [Real.sqrt_one] }
  | succ K ih => {
      rw [sum_range_succ, ih]
      simp only [OddGap]
      have hidx : (2 * ((K + 1 : ℕ) : ℝ) + 1) = 2 * (K : ℝ) + 3 := by
        have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by simp
        rw [hcast]
        ring
      rw [hidx]
      ring
    }

/-- Every finite set of odd positive integers has reciprocal sum at most `2`. -/
theorem OddReciprocalSum (t : Finset ℕ) (hmem : ∀ u ∈ t, u % 2 = 1) :
    ∑ u ∈ t, OddRecip u ≤ 2 := by
  let ones := t.filter (fun u => u = 1)
  let rest := t.filter (fun u => 3 ≤ u)
  have hsplit : ∀ u ∈ t, u = 1 ∨ 3 ≤ u := by
    intro u hu
    have hodd := hmem u hu
    omega
  have hunion : t = ones ∪ rest := by
    ext u
    constructor
    · intro hu
      rcases hsplit u hu with h1 | h3
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hu, h1⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hu, h3⟩))
    · intro hu
      rcases mem_union.mp hu with hu | hu
      · exact (mem_filter.mp hu).1
      · exact (mem_filter.mp hu).1
  have hdisj : Disjoint ones rest := by
    rw [disjoint_left]
    intro u hu1 hu3
    have h1 := (mem_filter.mp hu1).2
    have h3 := (mem_filter.mp hu3).2
    omega
  rw [hunion, sum_union hdisj]
  have hones : ∑ u ∈ ones, OddRecip u ≤ 1 := by
    by_cases h : (1 : ℕ) ∈ ones
    · have hone : ones = {1} := by
        ext u
        constructor
        · intro hu
          have hu1 := (mem_filter.mp hu).2
          simp [hu1]
        · intro hu
          simp at hu
          subst hu
          exact h
      rw [hone]
      simp [OddRecip, Real.sqrt_one]
    · have hempty : ones = ∅ := by
        ext u
        constructor
        · intro hu
          have hu1 := (mem_filter.mp hu).2
          subst hu1
          exact False.elim (h hu)
        · intro hu
          exact False.elim (notMem_empty u hu)
      rw [hempty]
      simp
  have hrest : ∑ u ∈ rest, OddRecip u ≤ 1 := by
    by_cases hempty : rest = ∅
    · rw [hempty]
      simp
    · have hne : rest.Nonempty := nonempty_of_ne_empty hempty
      let M := rest.max' hne
      have hle : ∀ u ∈ rest, u ≤ M := (isGreatest_max' rest hne).2
      have hMge : 3 ≤ M := (mem_filter.mp (max'_mem rest hne)).2
      have hsub : rest ⊆ (range M).image (fun m => 2 * m + 3) := by
        intro u hu
        have h3 : 3 ≤ u := (mem_filter.mp hu).2
        have hodd : u % 2 = 1 := hmem u (mem_filter.mp hu).1
        have hule : u ≤ M := hle u hu
        have huform : u = 2 * (u / 2) + 1 := by
          have hdiv := Nat.div_add_mod u 2
          rw [hodd] at hdiv
          exact hdiv.symm
        have hhalf : 1 ≤ u / 2 := by
          have hge : 3 ≤ 2 * (u / 2) + 1 := by
            rw [← huform]
            exact h3
          omega
        have hdiff : u - 3 = 2 * (u / 2 - 1) := by
          rw [huform]
          omega
        have hcancel : (u - 3) / 2 = u / 2 - 1 := by
          rw [hdiff]
          exact Nat.mul_div_cancel_left (u / 2 - 1) (by decide : 0 < 2)
        refine mem_image.mpr ⟨(u - 3) / 2, ?_, ?_⟩
        · rw [mem_range]
          have hdivle : (u - 3) / 2 ≤ (M - 3) / 2 :=
            Nat.div_le_div_right (Nat.sub_le_sub_right hule 3)
          have hMlt : (M - 3) / 2 < M := by omega
          exact lt_of_le_of_lt hdivle hMlt
        · rw [hcancel, huform]
          omega
      have hinj : Set.InjOn (fun m => 2 * m + 3) (range M) := by
        intro m _hm m' _hm' heq
        change 2 * m + 3 = 2 * m' + 3 at heq
        omega
      have himage :
          ∑ u ∈ (range M).image (fun m => 2 * m + 3), OddRecip u =
            ∑ m ∈ range M, OddRecip (2 * m + 3) :=
        sum_image (f := OddRecip) hinj
      have hsumle :
          ∑ u ∈ rest, OddRecip u ≤
            ∑ u ∈ (range M).image (fun m => 2 * m + 3), OddRecip u :=
        sum_le_sum_of_subset_of_nonneg hsub fun u _hu _hnot => OddRecipNonneg u
      have hterm : ∑ m ∈ range M, OddRecip (2 * m + 3) ≤
          ∑ m ∈ range M, OddGap m :=
        sum_le_sum fun m _ => le_of_lt (OddTermLtGap m)
      have hgap : ∑ m ∈ range M, OddGap m ≤ 1 := by
        rw [OddGapSum M]
        have hnnroot : 0 ≤ 1 / Real.sqrt (2 * (M : ℝ) + 1) := by positivity
        exact sub_le_self _ hnnroot
      rw [himage] at hsumle
      exact hsumle.trans (hterm.trans hgap)
  linarith

/-- A finite geometric tail of ratio `7/16` is at most `(7/16)^A * 16/9`. -/
theorem SevenGeomTail (A B : ℕ) (hAB : A ≤ B) :
    ∑ a ∈ Ico A B, ((7 : ℝ) / 16) ^ a ≤
      ((7 : ℝ) / 16) ^ A * (16 / 9) := by
  have hr : ((7 : ℝ) / 16) ≠ 1 := by norm_num
  rw [geom_sum_Ico' hr hAB]
  have hden : (1 : ℝ) - 7 / 16 = 9 / 16 := by norm_num
  rw [hden]
  have hsub : ((7 : ℝ) / 16) ^ A - ((7 : ℝ) / 16) ^ B ≤ ((7 : ℝ) / 16) ^ A := by
    have hnn : 0 ≤ ((7 : ℝ) / 16) ^ B := by positivity
    linarith
  have hdiv :
      (((7 : ℝ) / 16) ^ A - ((7 : ℝ) / 16) ^ B) / (9 / 16) ≤
        ((7 : ℝ) / 16) ^ A / (9 / 16) :=
    div_le_div_of_nonneg_right hsub (by norm_num : (0 : ℝ) ≤ 9 / 16)
  have heq : ((7 : ℝ) / 16) ^ A / (9 / 16) =
      ((7 : ℝ) / 16) ^ A * (16 / 9) := by
    have hinv : ((9 : ℝ) / 16)⁻¹ = 16 / 9 := by norm_num
    rw [div_eq_mul_inv, hinv]
  exact hdiv.trans_eq heq

/-- Finite odd seeds of burst length at least `A` have source-weighted
square-root occupation at most `(2560/27)*(7/16)^A`. -/
theorem InitialOddBurstOccupation (A : ℕ) (_hA : 1 ≤ A) (s : Finset ℕ)
    (hmem : ∀ n ∈ s, 3 ≤ n ∧ n % 2 = 1 ∧ A ≤ OddBurstLength n) :
    ∑ n ∈ s, SourceAtom n * BurstSqrtOccupation n ≤
      (2560 / 27) * ((7 : ℝ) / 16) ^ A := by
  rcases eq_empty_or_nonempty s with rfl | hs
  · {
    simp
    positivity
  }
  · {
    have hterm : ∀ n ∈ s, SourceAtom n * BurstSqrtOccupation n ≤
        (80 / 3) * ((7 : ℝ) / 16) ^ OddBurstLength n *
          OddRecip (OddBurstCofactor n) := by
      intro n hn
      exact le_of_lt (OneBurstMass n (hmem n hn).1 (hmem n hn).2.1)
    have hsumSeed := sum_le_sum hterm
    let lengths := s.image OddBurstLength
    let cofactors := s.image OddBurstCofactor
    let g : ℕ → ℕ × ℕ := fun n => (OddBurstLength n, OddBurstCofactor n)
    -- Exact burst coordinates determine the original seed, so no source weight is merged.
    have hinj : Set.InjOn g s := by
      intro n hn m hm heq
      have hn1 := (OddBurstSplit n (hmem n hn).2.1).1
      have hm1 := (OddBurstSplit m (hmem m hm).2.1).1
      have heqN : n + 1 = m + 1 := by
        rw [← hn1, ← hm1]
        obtain ⟨hl, hc⟩ := Prod.ext_iff.mp heq
        simp only [g] at hl hc
        rw [hl, hc]
      omega
    have himage :
        ∑ p ∈ s.image g, ((7 : ℝ) / 16) ^ p.1 * OddRecip p.2 =
          ∑ n ∈ s, ((7 : ℝ) / 16) ^ OddBurstLength n *
            OddRecip (OddBurstCofactor n) := by
      simpa [g] using sum_image (f := fun p : ℕ × ℕ =>
        ((7 : ℝ) / 16) ^ p.1 * OddRecip p.2) hinj
    -- Positivity permits the rectangle bound without any independence assumption.
    have hrect : s.image g ⊆ lengths ×ˢ cofactors := by
      have hsub := subset_product (s := s.image g)
      have h1 : (s.image g).image Prod.fst = lengths := by
        rw [image_image]
        rfl
      have h2 : (s.image g).image Prod.snd = cofactors := by
        rw [image_image]
        rfl
      simpa [h1, h2] using hsub
    have hnnRect : ∀ p ∈ lengths ×ˢ cofactors,
        0 ≤ ((7 : ℝ) / 16) ^ p.1 * OddRecip p.2 := by
      intro p _hp
      exact mul_nonneg (by positivity) (OddRecipNonneg p.2)
    have hfact :
        ∑ p ∈ lengths ×ˢ cofactors, ((7 : ℝ) / 16) ^ p.1 * OddRecip p.2 =
          (∑ a ∈ lengths, ((7 : ℝ) / 16) ^ a) *
            ∑ u ∈ cofactors, OddRecip u := by
      calc
        ∑ p ∈ lengths ×ˢ cofactors, ((7 : ℝ) / 16) ^ p.1 * OddRecip p.2
          = ∑ a ∈ lengths, ∑ u ∈ cofactors,
              ((7 : ℝ) / 16) ^ a * OddRecip u := by
            rw [sum_product]
        _ = ∑ a ∈ lengths, ((7 : ℝ) / 16) ^ a *
              ∑ u ∈ cofactors, OddRecip u := by
            refine sum_congr rfl ?_
            intro a _ha
            symm
            exact mul_sum _ _ _
        _ = (∑ a ∈ lengths, ((7 : ℝ) / 16) ^ a) *
              ∑ u ∈ cofactors, OddRecip u := by
          rw [← sum_mul]
    have hlne : lengths.Nonempty := by
      obtain ⟨n, hn⟩ := hs
      exact ⟨OddBurstLength n, mem_image_of_mem _ hn⟩
    let M := lengths.max' hlne
    have hAleM : A ≤ M := by
      obtain ⟨n, hn⟩ := hs
      have hmemlen : OddBurstLength n ∈ lengths := mem_image_of_mem _ hn
      have hAlen : A ≤ OddBurstLength n := (hmem n hn).2.2
      exact hAlen.trans ((isGreatest_max' lengths hlne).2 hmemlen)
    have hIco : lengths ⊆ Ico A (M + 1) := by
      intro a ha
      obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
      exact mem_Ico.mpr ⟨(hmem n hn).2.2,
        Nat.lt_succ_of_le ((isGreatest_max' lengths hlne).2 ha)⟩
    have hgeom : ∑ a ∈ lengths, ((7 : ℝ) / 16) ^ a ≤
        ((7 : ℝ) / 16) ^ A * (16 / 9) := by
      have htail := SevenGeomTail A (M + 1) (by omega)
      have hmono : (∑ a ∈ lengths, ((7 : ℝ) / 16) ^ a) ≤
          ∑ a ∈ Ico A (M + 1), ((7 : ℝ) / 16) ^ a :=
        sum_le_sum_of_subset_of_nonneg hIco (fun a _ha _hnot => by positivity)
      exact hmono.trans htail
    have hcofOdd : ∀ u ∈ cofactors, u % 2 = 1 := by
      intro u hu
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hu
      exact (OddBurstSplit n (hmem n hn).2.1).2
    have hcofSum : ∑ u ∈ cofactors, OddRecip u ≤ 2 :=
      OddReciprocalSum cofactors hcofOdd
    have hprod : (∑ a ∈ lengths, ((7 : ℝ) / 16) ^ a) *
        ∑ u ∈ cofactors, OddRecip u ≤
          (((7 : ℝ) / 16) ^ A * (16 / 9)) * 2 := by
      have hX : 0 ≤ ∑ a ∈ lengths, ((7 : ℝ) / 16) ^ a :=
        sum_nonneg fun _ _ => by positivity
      have hY : 0 ≤ ∑ u ∈ cofactors, OddRecip u :=
        sum_nonneg fun u _ => OddRecipNonneg u
      exact mul_le_mul hgeom hcofSum hY (by positivity)
    have hpair : ∑ n ∈ s, ((7 : ℝ) / 16) ^ OddBurstLength n *
        OddRecip (OddBurstCofactor n) ≤
          (((7 : ℝ) / 16) ^ A * (16 / 9)) * 2 := by
      have himageLe :
          ∑ n ∈ s, ((7 : ℝ) / 16) ^ OddBurstLength n *
              OddRecip (OddBurstCofactor n) ≤
            ∑ p ∈ lengths ×ˢ cofactors,
              ((7 : ℝ) / 16) ^ p.1 * OddRecip p.2 := by
        rw [← himage]
        exact sum_le_sum_of_subset_of_nonneg hrect fun p hp _hnot =>
          hnnRect p hp
      exact himageLe.trans (by rw [hfact]; exact hprod)
    have hscaled := mul_le_mul_of_nonneg_left hpair
      (by norm_num : (0 : ℝ) ≤ 80 / 3)
    have hconst : (80 / 3) * ((((7 : ℝ) / 16) ^ A * (16 / 9)) * 2) =
        (2560 / 27) * ((7 : ℝ) / 16) ^ A := by
      ring
    have hsumForm : ∑ n ∈ s, (80 / 3) * ((7 : ℝ) / 16) ^ OddBurstLength n *
        OddRecip (OddBurstCofactor n) =
          (80 / 3) * ∑ n ∈ s, ((7 : ℝ) / 16) ^ OddBurstLength n *
            OddRecip (OddBurstCofactor n) := by
      symm
      simpa [mul_assoc] using mul_sum s (fun n =>
        ((7 : ℝ) / 16) ^ OddBurstLength n * OddRecip (OddBurstCofactor n))
        (80 / 3)
    have hseed : ∑ n ∈ s, SourceAtom n * BurstSqrtOccupation n ≤
        (80 / 3) * ∑ n ∈ s, ((7 : ℝ) / 16) ^ OddBurstLength n *
          OddRecip (OddBurstCofactor n) := by
      rw [← hsumForm]
      simpa [mul_assoc] using hsumSeed
    exact hseed.trans (hscaled.trans_eq hconst)
  }

/-- The original source weight is positive on its stated seed domain. -/
theorem SourceAtomPos (n : ℕ) (h3 : 3 ≤ n) : 0 < SourceAtom n := by
  have hn : (3 : ℝ) ≤ n := by exact_mod_cast h3
  unfold SourceAtom
  exact div_pos (by norm_num) (mul_pos (by linarith) (by linarith))

/-- Every term of the initial square-root occupation is nonnegative. -/
theorem BurstSqrtOccupationNonneg (n : ℕ) : 0 ≤ BurstSqrtOccupation n := by
  unfold BurstSqrtOccupation
  exact sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- Extend the admissible source contribution by zero outside the rank tail. -/
def OddBurstTailAtom (A n : ℕ) : ℝ :=
  if 3 ≤ n ∧ n % 2 = 1 ∧ A ≤ OddBurstLength n then
    SourceAtom n * BurstSqrtOccupation n else 0

/-- Zero extension keeps the contribution nonnegative at every natural seed. -/
theorem OddBurstTailNonneg (A n : ℕ) : 0 ≤ OddBurstTailAtom A n := by
  by_cases h : 3 ≤ n ∧ n % 2 = 1 ∧ A ≤ OddBurstLength n
  · rw [OddBurstTailAtom, if_pos h]
    exact mul_nonneg (SourceAtomPos n h.1).le (BurstSqrtOccupationNonneg n)
  · simp [OddBurstTailAtom, h]

/-- Filtering an arbitrary finite set recovers precisely the admissible source sum. -/
theorem OddBurstTailFiniteBound (A : ℕ) (hA : 1 ≤ A) (s : Finset ℕ) :
    ∑ n ∈ s, OddBurstTailAtom A n ≤ (2560 / 27) * ((7 : ℝ) / 16) ^ A := by
  let seeds := s.filter (fun n => 3 ≤ n ∧ n % 2 = 1 ∧ A ≤ OddBurstLength n)
  have hsum : ∑ n ∈ s, OddBurstTailAtom A n =
      ∑ n ∈ seeds, SourceAtom n * BurstSqrtOccupation n := by
    dsimp only [seeds]
    rw [sum_filter]
    rfl
  rw [hsum]
  apply InitialOddBurstOccupation A hA seeds
  intro n hn
  exact (mem_filter.mp hn).2

/-- The full source-weighted tail converges and satisfies the same uniform bound. -/
theorem InitialOddBurstSeries (A : ℕ) (hA : 1 ≤ A) :
    Summable (OddBurstTailAtom A) ∧
      ∑' n, OddBurstTailAtom A n ≤ (2560 / 27) * ((7 : ℝ) / 16) ^ A := by
  have hn : 0 ≤ OddBurstTailAtom A := fun n => OddBurstTailNonneg A n
  have hb := OddBurstTailFiniteBound A hA
  exact ⟨summable_of_sum_le hn hb, Real.tsum_le_of_sum_le hn hb⟩

/-- Every admissible odd seed belongs to the rank-one tail. -/
theorem OddBurstTailOne (n : ℕ) (h3 : 3 ≤ n) (hodd : n % 2 = 1) :
    OddBurstTailAtom 1 n = SourceAtom n * BurstSqrtOccupation n := by
  rw [OddBurstTailAtom, if_pos ⟨h3, hodd, OddBurstLengthGeOne n hodd⟩]

/-- Summing all original odd sources gives the explicit bound `1120/27`. -/
theorem InitialOddBurstTotal :
    Summable (OddBurstTailAtom 1) ∧ ∑' n, OddBurstTailAtom 1 n ≤ (1120 : ℝ) / 27 := by
  have h := InitialOddBurstSeries 1 (by decide)
  norm_num at h
  exact h

end

end GeneralizedCollatz.OddBurst
