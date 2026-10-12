-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import Mathlib.Algebra.Ring.Parity

/-!
Equal odd components of a two-affine word.

A two-affine word of positive letters `a` and `b` asks for positive integers
`n` and `y` and a multiplier `q` such that `q n + 1 = 2^a y` and
`q y + 1 = 2^b n`. If the two components are equal, the letters agree, the
length `a + b` is even, and the only positive solution is the unit state
`n = 1` with `q = 2^a - 1`. A component of size at least `3` is therefore
impossible. The same identity does not exclude unequal components.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The equal-component relation `q n + 1 = 2^a n`. -/
abbrev EqualClosure (q a n : ℕ) : Prop :=
  q * n + 1 = 2 ^ a * n

/-- The two affine relations of letters `a` and `b` on components `n` and `y`. -/
abbrev TwoAffine (q a b n y : ℕ) : Prop :=
  q * n + 1 = 2 ^ a * y ∧ q * y + 1 = 2 ^ b * n

/-- A positive power of two is a sum of two equal natural numbers. -/
theorem TwoPowEven (a : ℕ) (ha : 1 ≤ a) : Even (2 ^ a) := by
  cases a with
  | zero => {
      exact absurd ha (Nat.not_succ_le_zero 0)
    }
  | succ k => {
      refine ⟨2 ^ k, ?_⟩
      show 2 ^ Nat.succ k = 2 ^ k + 2 ^ k
      calc
        2 ^ Nat.succ k = 2 ^ k * 2 := Nat.pow_succ 2 k
        _ = 2 ^ k * (1 + 1) := by
          rw [show (2 : ℕ) = 1 + 1 from rfl]
        _ = 2 ^ k * 1 + 2 ^ k * 1 := Nat.mul_add _ _ _
        _ = 2 ^ k + 2 ^ k := by rw [Nat.mul_one]
    }

/-- Equal powers of two have the same exponent. -/
theorem TwoPowInjective (a b : ℕ) (h : 2 ^ a = 2 ^ b) : a = b := by
  induction a generalizing b with
  | zero => {
      cases b with
      | zero => {
          rfl
        }
      | succ j => {
          have hpow : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
          rw [hpow] at h
          have hmod : (2 ^ j * 2) % 2 = 0 := Nat.mul_mod_left (2 ^ j) 2
          have hone : (1 : ℕ) % 2 = 1 :=
            Nat.mod_eq_of_lt (by decide : 1 < 2)
          have hcong : (1 : ℕ) % 2 = (2 ^ j * 2) % 2 :=
            congrArg (fun t => t % 2) h
          have h10 : (1 : ℕ) = 0 := by
            calc
              (1 : ℕ) = 1 % 2 := hone.symm
              _ = (2 ^ j * 2) % 2 := hcong
              _ = 0 := hmod
          exact absurd h10 Nat.one_ne_zero
        }
    }
  | succ k ih => {
      cases b with
      | zero => {
          have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
          rw [hpow] at h
          have hmod : (2 ^ k * 2) % 2 = 0 := Nat.mul_mod_left (2 ^ k) 2
          have hone : (1 : ℕ) % 2 = 1 :=
            Nat.mod_eq_of_lt (by decide : 1 < 2)
          have hcong : (2 ^ k * 2) % 2 = (1 : ℕ) % 2 :=
            congrArg (fun t => t % 2) h
          have h01 : (0 : ℕ) = 1 := by
            calc
              (0 : ℕ) = (2 ^ k * 2) % 2 := hmod.symm
              _ = 1 % 2 := hcong
              _ = 1 := hone
          exact absurd h01 Nat.zero_ne_one
        }
      | succ j => {
          have hleft : 2 ^ (k + 1) = 2 * 2 ^ k := by
            rw [Nat.pow_succ, Nat.mul_comm]
          have hright : 2 ^ (j + 1) = 2 * 2 ^ j := by
            rw [Nat.pow_succ, Nat.mul_comm]
          rw [hleft, hright] at h
          have hdiv : 2 ^ k = 2 ^ j := by
            calc
              2 ^ k = (2 * 2 ^ k) / 2 :=
                (Nat.mul_div_cancel_left (2 ^ k) (by decide : 0 < 2)).symm
              _ = (2 * 2 ^ j) / 2 := by rw [h]
              _ = 2 ^ j :=
                Nat.mul_div_cancel_left (2 ^ j) (by decide : 0 < 2)
          have hk : k = j := ih j hdiv
          show k + 1 = j + 1
          exact congrArg Nat.succ hk
        }
    }

/-- One positive state cannot satisfy two different equal-component letters. -/
theorem EqualLetters (q a b n : ℕ) (hn : 0 < n)
    (h1 : EqualClosure q a n) (h2 : EqualClosure q b n) : a = b := by
  have hmul : 2 ^ a * n = 2 ^ b * n := by
    rw [← h1]
    exact h2
  have hpow : 2 ^ a = 2 ^ b := Nat.eq_of_mul_eq_mul_right hn hmul
  exact TwoPowInjective a b hpow

/-- Equal letters make the word length a double. -/
theorem EqualLettersEvenLength (a : ℕ) : Even (a + a) :=
  ⟨a, rfl⟩

/-- An intermediate term cancels in truncated subtraction. -/
theorem SubAddSub (a b c : ℕ) (hcb : c ≤ b) (hba : b ≤ a) :
    a - b + (b - c) = a - c := by
  have h1 : a - b + (b - c) + c = a := by
    calc
      a - b + (b - c) + c = a - b + ((b - c) + c) := Nat.add_assoc _ _ _
      _ = a - b + b := by rw [Nat.sub_add_cancel hcb]
      _ = a := Nat.sub_add_cancel hba
  have hca : c ≤ a := Nat.le_trans hcb hba
  have h2 : a - c + c = a := Nat.sub_add_cancel hca
  have hEq : a - b + (b - c) + c = a - c + c := by
    rw [h1, h2]
  exact Nat.add_right_cancel hEq

/-- The difference of squares factors when the subtracted term is at most the root. -/
theorem DifferenceOfSquares (A q : ℕ) (hq : q ≤ A) :
    (A - q) * (A + q) = A * A - q * q := by
  have hcomm : q * A = A * q := Nat.mul_comm q A
  have hle1 : q * A ≤ A * A := Nat.mul_le_mul_right A hq
  have hle1' : A * q ≤ A * A := by
    rw [← hcomm]
    exact hle1
  have hle2 : q * q ≤ A * q := Nat.mul_le_mul_right q hq
  calc
    (A - q) * (A + q)
        = (A - q) * A + (A - q) * q := Nat.mul_add (A - q) A q
    _ = (A * A - q * A) + (A * q - q * q) := by
        rw [Nat.mul_sub_right_distrib A q A,
          Nat.mul_sub_right_distrib A q q]
    _ = (A * A - A * q) + (A * q - q * q) := by rw [hcomm]
    _ = A * A - q * q :=
        SubAddSub (A * A) (A * q) (q * q) hle2 hle1'

/-- An even length `2m` splits `2^{2m} - q^2` as a difference of squares. -/
theorem EvenDeltaFactor (q m : ℕ) (hq : q ≤ 2 ^ m) :
    (2 ^ m - q) * (2 ^ m + q) = 2 ^ (m + m) - q * q := by
  have hsq := DifferenceOfSquares (2 ^ m) q hq
  have hpow : (2 ^ m) * (2 ^ m) = 2 ^ (m + m) := (Nat.pow_add 2 m m).symm
  rw [hpow] at hsq
  exact hsq

/-- Equal components force the cofactor product `(2^a - q) n = 1`. -/
theorem EqualCofactor (q a n : ℕ) (_ : 0 < n) (h : EqualClosure q a n) :
    (2 ^ a - q) * n = 1 := by
  have hlt : q * n < 2 ^ a * n := by
    rw [← h]
    exact Nat.lt_succ_self (q * n)
  have hcancel := Nat.sub_add_cancel (Nat.le_of_lt hlt)
  have hsum : 1 + q * n = 2 ^ a * n := by
    rw [Nat.add_comm]
    exact h
  have hdiff : 2 ^ a * n - q * n + q * n = 1 + q * n := by
    rw [hcancel, hsum]
  have hsub : 2 ^ a * n - q * n = 1 := Nat.add_right_cancel hdiff
  show (2 ^ a - q) * n = 1
  rw [Nat.mul_sub_right_distrib (2 ^ a) q n]
  exact hsub

/-- A positive product equal to one has both factors equal to one. -/
theorem NatMulEqOne (d n : ℕ) (hn : 0 < n) (h : d * n = 1) : d = 1 ∧ n = 1 := by
  cases d with
  | zero => {
      simp at h
    }
  | succ d => {
      cases d with
      | zero => {
          have hn1 : n = 1 := by simpa using h
          exact ⟨rfl, hn1⟩
        }
      | succ d => {
          have hd : 2 ≤ Nat.succ (Nat.succ d) :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le d))
          have hprod : 2 ≤ Nat.succ (Nat.succ d) * n := by
            have hbase : 2 * 1 ≤ Nat.succ (Nat.succ d) * n :=
              Nat.mul_le_mul hd hn
            simp at hbase
            exact hbase
          have h21 : (2 : ℕ) ≤ 1 := by
            simp [h] at hprod
          exact absurd h21 (Nat.not_le_of_lt (by decide : 1 < 2))
        }
    }

/-- A truncated difference equal to one splits as a predecessor. -/
theorem SubOneSplit (A q : ℕ) (h : A - q = 1) : q < A ∧ A = q + 1 := by
  have hle : q ≤ A := by
    by_contra hlt
    have hgt : A < q := Nat.gt_of_not_le hlt
    have hge : A ≤ q := Nat.le_of_lt hgt
    have hzero : A - q = 0 := Nat.sub_eq_zero_of_le hge
    simp [hzero] at h
  have hA : A = q + 1 := by
    calc
      A = A - q + q := (Nat.sub_add_cancel hle).symm
      _ = 1 + q := by rw [h]
      _ = q + 1 := Nat.add_comm 1 q
  have hltA : q < A := by
    rw [hA]
    exact Nat.lt_succ_self q
  exact ⟨hltA, hA⟩

/-- An equal-component closure is the unit state `n = 1` with `2^a = q + 1`. -/
theorem EqualClosureUnit (q a n : ℕ) (hn : 0 < n) (h : EqualClosure q a n) :
    n = 1 ∧ 2 ^ a = q + 1 := by
  have hfac : (2 ^ a - q) * n = 1 := EqualCofactor q a n hn h
  have hpair := NatMulEqOne (2 ^ a - q) n hn hfac
  have hsplit := SubOneSplit (2 ^ a) q hpair.1
  exact ⟨hpair.2, hsplit.2⟩

/-- An odd equal component forces the multiplier to be odd when the letter is positive. -/
theorem EqualClosureMultiplierOdd (q a n : ℕ) (ha : 1 ≤ a) (_ : Odd n)
    (h : EqualClosure q a n) : Odd q := by
  rcases TwoPowEven a ha with ⟨r, hr⟩
  have hright : Even (2 ^ a * n) := by
    refine ⟨r * n, ?_⟩
    show 2 ^ a * n = r * n + r * n
    calc
      2 ^ a * n = (r + r) * n := by rw [hr]
      _ = r * n + r * n := Nat.add_mul r r n
  have hleft : Even (q * n + 1) := by
    rw [h]
    exact hright
  have hiff := (Nat.even_add' (m := q * n) (n := 1)).mp hleft
  have hprod : Odd (q * n) := hiff.mpr (odd_one : Odd (1 : ℕ))
  exact ((Nat.odd_mul (m := q) (n := n)).mp hprod).1

/-- The doubled fixed point of one is an equal-component solution below size 3. -/
theorem UnitDoubleLetter (a : ℕ) (ha : 1 ≤ a) :
    EqualClosure (2 ^ a - 1) a 1 ∧ Odd (2 ^ a - 1) ∧ ¬ (3 ≤ (1 : ℕ)) := by
  have hle : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have he : Even (2 ^ a) := TwoPowEven a ha
  refine ⟨?_, ?_, ?_⟩
  · show EqualClosure (2 ^ a - 1) a 1
    calc
      (2 ^ a - 1) * 1 + 1 = 2 ^ a - 1 + 1 := by rw [Nat.mul_one]
      _ = 2 ^ a := Nat.sub_add_cancel hle
      _ = 2 ^ a * 1 := (Nat.mul_one (2 ^ a)).symm
  · have hnot : ¬ Even (2 ^ a - 1) := by
      intro h
      have hiff := (Nat.even_sub' hle).mp h
      have hodd : Odd (2 ^ a) := hiff.mpr (odd_one : Odd (1 : ℕ))
      exact (Nat.not_odd_iff_even.mpr he) hodd
    exact Nat.not_even_iff_odd.mp hnot
  · exact Nat.not_le_of_lt (by decide : (1 : ℕ) < 3)

/-- The equal-component equation is the determinant equation `n(2^{2a} - q^2) = q + 2^a`. -/
theorem EqualClosureSeed (q a n : ℕ) (hn : 0 < n) (h : EqualClosure q a n) :
    (2 ^ (a + a) - q * q) * n = q + 2 ^ a := by
  have hfac : (2 ^ a - q) * n = 1 := EqualCofactor q a n hn h
  have hpair := NatMulEqOne (2 ^ a - q) n hn hfac
  have hsplit := SubOneSplit (2 ^ a) q hpair.1
  have hqle : q ≤ 2 ^ a := Nat.le_of_lt hsplit.1
  have hdelta := EvenDeltaFactor q a hqle
  have hre :
      (2 ^ a - q) * (2 ^ a + q) * n =
        (2 ^ a - q) * n * (2 ^ a + q) := by
    calc
      (2 ^ a - q) * (2 ^ a + q) * n
          = (2 ^ a - q) * ((2 ^ a + q) * n) := Nat.mul_assoc _ _ _
      _ = (2 ^ a - q) * (n * (2 ^ a + q)) := by
          rw [Nat.mul_comm (2 ^ a + q) n]
      _ = (2 ^ a - q) * n * (2 ^ a + q) := (Nat.mul_assoc _ _ _).symm
  calc
    (2 ^ (a + a) - q * q) * n
        = (2 ^ a - q) * (2 ^ a + q) * n := by rw [hdelta]
    _ = (2 ^ a - q) * n * (2 ^ a + q) := hre
    _ = 1 * (2 ^ a + q) := by rw [hfac]
    _ = 2 ^ a + q := Nat.one_mul _
    _ = q + 2 ^ a := Nat.add_comm _ _

/-- If the determinant equation holds and `q ≤ 2^a`, the cofactor product is one. -/
theorem EqualSeedCofactor (q a n : ℕ) (hq : q ≤ 2 ^ a)
    (h : (2 ^ (a + a) - q * q) * n = q + 2 ^ a) :
    (2 ^ a - q) * n = 1 := by
  have hdelta := EvenDeltaFactor q a hq
  have hmul : (2 ^ a - q) * (2 ^ a + q) * n = 2 ^ a + q := by
    calc
      (2 ^ a - q) * (2 ^ a + q) * n
          = (2 ^ (a + a) - q * q) * n := by rw [hdelta]
      _ = q + 2 ^ a := h
      _ = 2 ^ a + q := Nat.add_comm _ _
  have hre :
      (2 ^ a - q) * n * (2 ^ a + q) =
        (2 ^ a - q) * (2 ^ a + q) * n := by
    calc
      (2 ^ a - q) * n * (2 ^ a + q)
          = (2 ^ a - q) * (n * (2 ^ a + q)) := Nat.mul_assoc _ _ _
      _ = (2 ^ a - q) * ((2 ^ a + q) * n) := by
          rw [Nat.mul_comm n (2 ^ a + q)]
      _ = (2 ^ a - q) * (2 ^ a + q) * n := (Nat.mul_assoc _ _ _).symm
  have hpos : 0 < 2 ^ a + q := by
    have hpow : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
    exact Nat.lt_of_lt_of_le (by decide : 0 < 1)
      (Nat.le_trans hpow (Nat.le_add_right (2 ^ a) q))
  have hcancel :
      (2 ^ a - q) * n * (2 ^ a + q) = 1 * (2 ^ a + q) := by
    rw [hre, hmul]
    exact (Nat.one_mul (2 ^ a + q)).symm
  exact Nat.eq_of_mul_eq_mul_right hpos hcancel

/-- Equal components of size at least three do not close a two-affine word. -/
theorem NoEqualComponentsAtLeastThree (q a b n y : ℕ) (hn : 3 ≤ n) (hy : 3 ≤ y)
    (hEq : n = y) (h : TwoAffine q a b n y) : False := by
  have h1' : EqualClosure q a n := by simpa [← hEq] using h.1
  have h2' : EqualClosure q b n := by simpa [← hEq] using h.2
  have hnPos : 0 < n := Nat.lt_of_lt_of_le (by decide : 0 < 3) hn
  have hab : a = b := EqualLetters q a b n hnPos h1' h2'
  have heven : Even (a + b) := by
    rw [← hab]
    exact EqualLettersEvenLength a
  rcases heven with ⟨t, ht⟩
  have hsum : a + a = t + t := by simpa [hab] using ht
  have haEq : a = t := by
    have hmul : a * 2 = t * 2 := by
      rw [Nat.mul_two, Nat.mul_two]
      exact hsum
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) hmul
  have hunit := EqualClosureUnit q t n hnPos (by simpa [haEq] using h1')
  have hboth : 3 ≤ n ∧ 3 ≤ y := ⟨hn, hy⟩
  have hnot : ¬ (3 ≤ n) := by
    simp [hunit.1]
  exact hnot hboth.1

/-- If the length is even, equal odd components of size at least three do not close. -/
theorem NoEqualComponentsEvenLength (q a b n y : ℕ) (hK : Even (a + b))
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hn : 3 ≤ n) (hy : 3 ≤ y) (hnOdd : Odd n)
    (hyOdd : Odd y) (hEq : n = y) (h : TwoAffine q a b n y) : False := by
  rcases hK with ⟨t, ht⟩
  have h1' : EqualClosure q a n := by simpa [← hEq] using h.1
  have h2' : EqualClosure q b n := by simpa [← hEq] using h.2
  have hnPos : 0 < n := Nat.lt_of_lt_of_le (by decide : 0 < 3) hn
  have hab : a = b := EqualLetters q a b n hnPos h1' h2'
  have hsum : a + a = t + t := by simpa [hab] using ht
  have haEq : a = t := by
    have hmul : a * 2 = t * 2 := by
      rw [Nat.mul_two, Nat.mul_two]
      exact hsum
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) hmul
  have hlen : 2 ≤ a + b := Nat.add_le_add ha hb
  have hdouble : 2 ≤ t + t := by
    simp [ht] at hlen
    exact hlen
  have ht1 : 1 ≤ t := by
    cases t with
    | zero => {
        have hle : (2 : ℕ) ≤ 0 := by
          simp at hdouble
        exact absurd hle (Nat.not_succ_le_zero 1)
      }
    | succ s => {
        exact Nat.succ_le_succ (Nat.zero_le s)
      }
  have hunit := EqualClosureUnit q t n hnPos (by simpa [haEq] using h1')
  have hseed := EqualClosureSeed q t n hnPos (by simpa [haEq] using h1')
  have hoddState : Odd n ∧ Odd y := ⟨hnOdd, hyOdd⟩
  have hmul : Odd q :=
    EqualClosureMultiplierOdd q t n ht1 hoddState.1 (by simpa [haEq] using h1')
  have hboundary := UnitDoubleLetter t ht1
  have hboth : 3 ≤ n ∧ 3 ≤ y := ⟨hn, hy⟩
  have hnot : ¬ (3 ≤ n) := by
    rw [hunit.1]
    exact hboundary.2.2
  have hseedUnit : 2 ^ (t + t) - q * q = q + 2 ^ t := by
    simpa [hunit.1] using hseed
  have hpack :
      Odd q ∧ 2 ^ (t + t) - q * q = q + 2 ^ t ∧ ¬ (3 ≤ n) :=
    ⟨hmul, hseedUnit, hnot⟩
  exact hpack.2.2 hboth.1

/-- An odd length admits no positive equal-component solution. -/
theorem NoEqualComponentsOddLength (q a b n : ℕ) (hK : Odd (a + b)) (hn : 0 < n)
    (h1 : EqualClosure q a n) (h2 : EqualClosure q b n) : False := by
  have hab : a = b := EqualLetters q a b n hn h1 h2
  have heven : Even (a + b) := by
    rw [← hab]
    exact EqualLettersEvenLength a
  exact (Nat.not_even_iff_odd.mpr hK) heven

end GeneralizedCollatz
