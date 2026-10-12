-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Cyclic two-run gap

A positive-exponent word on the letters `1` and `2` has odd-acceleration
length `r`, exponent sum `K`, numerator `B`, and determinant `Delta = 2^K - 3^r`.
Positive odd closure requires `Delta > 0` and `Delta ∣ B`.

For the two-run word `1^p 2^q`, the identity
`B - Delta = 2 * 3^q * (3^p - 2^p)` forces any positive divisor `Delta` of `B`
to divide `3^p - 2^p`, and then `Delta * 3^q < 3^(p+q)`. The second-block
lengths `q = 1` and `q = 2` contradict that bound. A pure power of the letter
`1` has negative determinant. A pure power of the letter `2` has numerator
equal to its positive determinant and fixes `1`; that exception is not removed.

One rotation preserves the determinant and, because the determinant is coprime
to `6`, preserves divisibility of the numerator. Thus `1^p 2^q 1^s` carries
the same gap as `1^(p+s) 2^q`.

No claim is made for a second block of length at least `3`, for four cyclic
blocks, or for the assertion that every positive integer reaches `1`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Sum of the odd-acceleration exponents. -/
def ExponentSum : List ℕ → ℕ
  | [] => 0
  | a :: as => a + ExponentSum as

/-- The exponent sum adds across a concatenation. -/
theorem ExponentSumAppend (xs ys : List ℕ) :
    ExponentSum (xs ++ ys) = ExponentSum xs + ExponentSum ys := by
  induction xs with
  | nil => {
      rw [List.nil_append]
      have hE : ExponentSum ([] : List ℕ) = 0 := rfl
      rw [hE, Nat.zero_add]
    }
  | cons a xs ih => {
      rw [List.cons_append]
      have hL : ExponentSum (a :: (xs ++ ys)) =
          a + ExponentSum (xs ++ ys) := rfl
      have hR : ExponentSum (a :: xs) = a + ExponentSum xs := rfl
      rw [hL, ih, hR, Nat.add_assoc]
    }

/-- Replicating one exponent multiplies that exponent by the length. -/
theorem ExponentSumReplicate (n a : ℕ) :
    ExponentSum (List.replicate n a) = n * a := by
  induction n with
  | zero => {
      rw [List.replicate_zero, Nat.zero_mul]
      rfl
    }
  | succ n ih => {
      rw [List.replicate_succ]
      have hE : ExponentSum (a :: List.replicate n a) =
          a + ExponentSum (List.replicate n a) := rfl
      rw [hE, ih, Nat.succ_mul, Nat.add_comm]
    }

/-- Accelerated numerator, reading the word from the left. -/
def AccB : ℕ → List ℕ → ℕ
  | _, [] => 0
  | shift, a :: as =>
      3 ^ as.length * 2 ^ shift + AccB (shift + a) as

/-- Numerator of a word, with the first exponent unshifted. -/
def WordB (xs : List ℕ) : ℕ :=
  AccB 0 xs

/-- Determinant `2^K - 3^r` of a word. -/
def WordDelta (xs : List ℕ) : ℤ :=
  (2 : ℤ) ^ ExponentSum xs - (3 : ℤ) ^ xs.length

/-- Shifting the numerator multiplies it by the shift power of two. -/
theorem AccBShift (shift : ℕ) (xs : List ℕ) :
    AccB shift xs = 2 ^ shift * AccB 0 xs := by
  induction xs generalizing shift with
  | nil => {
      simp [AccB]
    }
  | cons a xs ih => {
      have hS : AccB shift (a :: xs) =
          3 ^ xs.length * 2 ^ shift + AccB (shift + a) xs := rfl
      have h0 : AccB 0 (a :: xs) =
          3 ^ xs.length * 2 ^ 0 + AccB (0 + a) xs := rfl
      simp at h0
      rw [hS, ih (shift + a), h0]
      have ih0 := ih a
      rw [ih0, Nat.pow_add]
      have hre :
          3 ^ xs.length * 2 ^ shift +
              2 ^ shift * 2 ^ a * AccB 0 xs =
            2 ^ shift * 3 ^ xs.length +
              2 ^ shift * (2 ^ a * AccB 0 xs) := by
        rw [Nat.mul_comm (3 ^ xs.length), Nat.mul_assoc]
      rw [hre, ← Nat.mul_add]
    }

/-- The numerator of a concatenation splits into a head term and a tail. -/
theorem AccBAppend (shift : ℕ) (xs ys : List ℕ) :
    AccB shift (xs ++ ys) =
      3 ^ ys.length * AccB shift xs +
        AccB (shift + ExponentSum xs) ys := by
  induction xs generalizing shift with
  | nil => {
      rw [List.nil_append]
      have hE : ExponentSum ([] : List ℕ) = 0 := rfl
      have hA : AccB shift ([] : List ℕ) = 0 := rfl
      rw [hE, hA, Nat.add_zero, Nat.mul_zero, Nat.zero_add]
    }
  | cons a xs ih => {
      rw [List.cons_append]
      have hB : AccB shift (a :: xs) =
          3 ^ xs.length * 2 ^ shift + AccB (shift + a) xs := rfl
      have hE : ExponentSum (a :: xs) = a + ExponentSum xs := rfl
      rw [hB, hE]
      have hL : (xs ++ ys).length = xs.length + ys.length :=
        List.length_append
      have hstep : AccB shift (a :: (xs ++ ys)) =
          3 ^ (xs ++ ys).length * 2 ^ shift +
            AccB (shift + a) (xs ++ ys) := rfl
      rw [hstep, hL, Nat.pow_add, ih (shift + a)]
      have hsum : shift + a + ExponentSum xs =
          shift + (a + ExponentSum xs) := by
        rw [Nat.add_assoc]
      rw [hsum]
      have hmul :
          3 ^ xs.length * 3 ^ ys.length * 2 ^ shift =
            3 ^ ys.length * (3 ^ xs.length * 2 ^ shift) := by
        calc
          3 ^ xs.length * 3 ^ ys.length * 2 ^ shift
              = 3 ^ xs.length * (3 ^ ys.length * 2 ^ shift) := by
                rw [Nat.mul_assoc]
          _ = 3 ^ ys.length * (3 ^ xs.length * 2 ^ shift) := by
                rw [Nat.mul_left_comm]
      calc
        3 ^ xs.length * 3 ^ ys.length * 2 ^ shift +
            (3 ^ ys.length * AccB (shift + a) xs +
              AccB (shift + (a + ExponentSum xs)) ys)
          = 3 ^ ys.length * (3 ^ xs.length * 2 ^ shift) +
              (3 ^ ys.length * AccB (shift + a) xs +
                AccB (shift + (a + ExponentSum xs)) ys) := by
              rw [hmul]
        _ = 3 ^ ys.length * (3 ^ xs.length * 2 ^ shift) +
              3 ^ ys.length * AccB (shift + a) xs +
              AccB (shift + (a + ExponentSum xs)) ys := by
              rw [Nat.add_assoc]
        _ = 3 ^ ys.length *
              (3 ^ xs.length * 2 ^ shift + AccB (shift + a) xs) +
              AccB (shift + (a + ExponentSum xs)) ys := by
              rw [← Nat.mul_add]
    }

/-- A block of letters `1` has numerator `2^shift * (3^p - 2^p)`. -/
theorem AccBOnesInt (shift p : ℕ) :
    ((AccB shift (List.replicate p 1) : ℕ) : ℤ) =
      (2 : ℤ) ^ shift * ((3 : ℤ) ^ p - (2 : ℤ) ^ p) := by
  induction p generalizing shift with
  | zero => {
      rw [List.replicate_zero]
      simp [AccB, pow_zero]
    }
  | succ p ih => {
      rw [List.replicate_succ]
      have hstep : AccB shift (1 :: List.replicate p 1) =
          3 ^ (List.replicate p 1).length * 2 ^ shift +
            AccB (shift + 1) (List.replicate p 1) := rfl
      rw [hstep, List.length_replicate, Nat.cast_add, ih (shift + 1)]
      have hmul : ((3 ^ p * 2 ^ shift : ℕ) : ℤ) =
          (3 : ℤ) ^ p * (2 : ℤ) ^ shift := by
        norm_cast
      rw [hmul]
      have hs : (2 : ℤ) ^ (shift + 1) = (2 : ℤ) ^ shift * 2 := by
        rw [pow_succ]
      have hp3 : (3 : ℤ) ^ (p + 1) = (3 : ℤ) ^ p * 3 := by
        rw [pow_succ]
      have hp2 : (2 : ℤ) ^ (p + 1) = (2 : ℤ) ^ p * 2 := by
        rw [pow_succ]
      rw [hs, hp3, hp2]
      ring
    }

/-- A block of letters `2` has numerator `2^shift * (4^q - 3^q)`. -/
theorem AccBTwosInt (shift q : ℕ) :
    ((AccB shift (List.replicate q 2) : ℕ) : ℤ) =
      (2 : ℤ) ^ shift * ((4 : ℤ) ^ q - (3 : ℤ) ^ q) := by
  induction q generalizing shift with
  | zero => {
      rw [List.replicate_zero]
      simp [AccB, pow_zero]
    }
  | succ q ih => {
      rw [List.replicate_succ]
      have hstep : AccB shift (2 :: List.replicate q 2) =
          3 ^ (List.replicate q 2).length * 2 ^ shift +
            AccB (shift + 2) (List.replicate q 2) := rfl
      rw [hstep, List.length_replicate, Nat.cast_add, ih (shift + 2)]
      have hmul : ((3 ^ q * 2 ^ shift : ℕ) : ℤ) =
          (3 : ℤ) ^ q * (2 : ℤ) ^ shift := by
        norm_cast
      rw [hmul]
      have hs : (2 : ℤ) ^ (shift + 2) = (2 : ℤ) ^ shift * 4 := by
        rw [pow_add]
        norm_num
      have hq4 : (4 : ℤ) ^ (q + 1) = 4 * (4 : ℤ) ^ q := by
        rw [pow_succ, mul_comm]
      have hq3 : (3 : ℤ) ^ (q + 1) = 3 * (3 : ℤ) ^ q := by
        rw [pow_succ, mul_comm]
      rw [hs, hq4, hq3]
      ring
    }

/-- The word `1^p 2^q`. -/
def TwoRunWord (p q : ℕ) : List ℕ :=
  List.replicate p 1 ++ List.replicate q 2

/-- Length and exponent sum of `1^p 2^q`. -/
theorem TwoRunShape (p q : ℕ) :
    (TwoRunWord p q).length = p + q ∧
      ExponentSum (TwoRunWord p q) = p + 2 * q := by
  constructor
  · {
      rw [TwoRunWord, List.length_append, List.length_replicate,
        List.length_replicate]
    }
  · {
      rw [TwoRunWord, ExponentSumAppend, ExponentSumReplicate,
        ExponentSumReplicate, Nat.mul_one, Nat.mul_comm]
    }

/-- Closed integer form of the two-run numerator. -/
theorem TwoRunBInt (p q : ℕ) :
    ((WordB (TwoRunWord p q) : ℕ) : ℤ) =
      (3 : ℤ) ^ (p + q) + (2 : ℤ) ^ (p + 2 * q) -
        (2 : ℤ) ^ (p + 1) * (3 : ℤ) ^ q := by
  have happ :=
    AccBAppend 0 (List.replicate p 1) (List.replicate q 2)
  have hlen : (List.replicate q 2).length = q := List.length_replicate
  have hsum : ExponentSum (List.replicate p 1) = p := by
    rw [ExponentSumReplicate, Nat.mul_one]
  rw [WordB, TwoRunWord, happ, hlen, hsum, Nat.add_zero, Nat.zero_add]
  rw [Nat.cast_add, Nat.cast_mul, AccBOnesInt 0 p, AccBTwosInt p q]
  simp only [pow_zero, one_mul]
  have h4 : (4 : ℤ) ^ q = (2 : ℤ) ^ (2 * q) := by
    have hb : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
    rw [hb, ← pow_mul]
  rw [h4]
  have hrhs :
      (3 : ℤ) ^ (p + q) + (2 : ℤ) ^ (p + 2 * q) -
          (2 : ℤ) ^ (p + 1) * (3 : ℤ) ^ q =
        (3 : ℤ) ^ p * (3 : ℤ) ^ q + (2 : ℤ) ^ p * (2 : ℤ) ^ (2 * q) -
          2 * (2 : ℤ) ^ p * (3 : ℤ) ^ q := by
    rw [pow_add, pow_add, pow_succ]
    ring
  have hdiff :
      (3 : ℤ) ^ q * ((3 : ℤ) ^ p - (2 : ℤ) ^ p) +
          (2 : ℤ) ^ p * ((2 : ℤ) ^ (2 * q) - (3 : ℤ) ^ q) -
        ((3 : ℤ) ^ p * (3 : ℤ) ^ q +
          (2 : ℤ) ^ p * (2 : ℤ) ^ (2 * q) -
          2 * (2 : ℤ) ^ p * (3 : ℤ) ^ q) = 0 := by
    ring
  rw [hrhs]
  exact sub_eq_zero.mp hdiff

/-- The two-run numerator plus the correction term is `3^(p+q) + 2^(p+2q)`. -/
theorem TwoRunClosed (p q : ℕ) :
    WordB (TwoRunWord p q) + 2 ^ (p + 1) * 3 ^ q =
      3 ^ (p + q) + 2 ^ (p + 2 * q) := by
  have hB := TwoRunBInt p q
  apply (Nat.cast_inj (R := ℤ)).mp
  calc
    ((WordB (TwoRunWord p q) + 2 ^ (p + 1) * 3 ^ q : ℕ) : ℤ)
        = ((WordB (TwoRunWord p q) : ℕ) : ℤ) +
            ((2 ^ (p + 1) * 3 ^ q : ℕ) : ℤ) := by
          rw [Nat.cast_add]
    _ = ((WordB (TwoRunWord p q) : ℕ) : ℤ) +
          (2 : ℤ) ^ (p + 1) * (3 : ℤ) ^ q := by
          norm_cast
    _ = ((3 : ℤ) ^ (p + q) + (2 : ℤ) ^ (p + 2 * q) -
          (2 : ℤ) ^ (p + 1) * (3 : ℤ) ^ q) +
          (2 : ℤ) ^ (p + 1) * (3 : ℤ) ^ q := by
          rw [hB]
    _ = (3 : ℤ) ^ (p + q) + (2 : ℤ) ^ (p + 2 * q) := by
          ring
    _ = ((3 ^ (p + q) + 2 ^ (p + 2 * q) : ℕ) : ℤ) := by
          norm_cast

/-- Difference between the two-run numerator and its determinant. -/
theorem TwoRunDifference (p q : ℕ) :
    ((WordB (TwoRunWord p q) : ℕ) : ℤ) -
        ((2 : ℤ) ^ (p + 2 * q) - (3 : ℤ) ^ (p + q)) =
      (2 : ℤ) * (3 : ℤ) ^ q * ((3 : ℤ) ^ p - (2 : ℤ) ^ p) := by
  have hB := TwoRunBInt p q
  have hs : (2 : ℤ) ^ (p + 1) = 2 * (2 : ℤ) ^ p := by
    rw [pow_succ, mul_comm]
  have hp : (3 : ℤ) ^ (p + q) = (3 : ℤ) ^ p * (3 : ℤ) ^ q := by
    rw [pow_add]
  calc
    ((WordB (TwoRunWord p q) : ℕ) : ℤ) -
        ((2 : ℤ) ^ (p + 2 * q) - (3 : ℤ) ^ (p + q))
      = ((3 : ℤ) ^ (p + q) + (2 : ℤ) ^ (p + 2 * q) -
          (2 : ℤ) ^ (p + 1) * (3 : ℤ) ^ q) -
          ((2 : ℤ) ^ (p + 2 * q) - (3 : ℤ) ^ (p + q)) := by
        rw [hB]
    _ = (2 : ℤ) * (3 : ℤ) ^ q * ((3 : ℤ) ^ p - (2 : ℤ) ^ p) := by
        rw [hs, hp]
        ring

/-- Powers of two modulo `3` are `1` or `2`. -/
theorem PowTwoModThree (n : ℕ) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => {
      left
      decide
    }
  | succ n ih => {
      rw [Nat.pow_succ, Nat.mul_mod]
      cases ih with
      | inl h1 => {
          rw [h1]
          right
          decide
        }
      | inr h2 => {
          rw [h2]
          left
          decide
        }
    }

/-- Powers of three are odd. -/
theorem PowThreeModTwo (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => {
      decide
    }
  | succ n ih => {
      rw [Nat.pow_succ, Nat.mul_mod, ih]
    }

/-- Three does not divide a power of two. -/
theorem NotDvdPowTwoByThree (n : ℕ) : ¬ 3 ∣ 2 ^ n := by
  intro h
  have h0 : 2 ^ n % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  cases PowTwoModThree n with
  | inl h1 => {
      omega
    }
  | inr h2 => {
      rw [h2] at h0
      omega
    }

/-- Two does not divide a power of three. -/
theorem NotDvdPowThreeByTwo (n : ℕ) : ¬ 2 ∣ 3 ^ n := by
  intro h
  have h0 : 3 ^ n % 2 = 0 := Nat.mod_eq_zero_of_dvd h
  rw [PowThreeModTwo n] at h0
  omega

/-- For positive exponents, `|2^K - 3^r|` is coprime to `6`. -/
theorem DetCoprimeSix (K r : ℕ) (hK : 1 ≤ K) (hr : 1 ≤ r) :
    Nat.Coprime (Int.natAbs ((2 : ℤ) ^ K - (3 : ℤ) ^ r)) 6 := by
  have h2pow : 2 ∣ 2 ^ K := by
    have hstep : K = (K - 1) + 1 := by omega
    rw [hstep, Nat.pow_succ, Nat.mul_comm]
    exact Nat.dvd_mul_right 2 (2 ^ (K - 1))
  have h3pow : 3 ∣ 3 ^ r := by
    have hstep : r = (r - 1) + 1 := by omega
    rw [hstep, Nat.pow_succ, Nat.mul_comm]
    exact Nat.dvd_mul_right 3 (3 ^ (r - 1))
  by_cases hle : 3 ^ r ≤ 2 ^ K
  · {
      have hN : Int.natAbs ((2 : ℤ) ^ K - (3 : ℤ) ^ r) =
          2 ^ K - 3 ^ r := by
        have h2c : ((2 : ℤ) ^ K) = ((2 ^ K : ℕ) : ℤ) := by norm_cast
        have h3c : ((3 : ℤ) ^ r) = ((3 ^ r : ℕ) : ℤ) := by norm_cast
        rw [h2c, h3c]
        exact Int.natAbs_natCast_sub_natCast_of_ge hle
      set N := 2 ^ K - 3 ^ r
      have hnot2 : ¬ 2 ∣ N := by
        intro h
        have hsub : 2 ∣ 2 ^ K - N := Nat.dvd_sub h2pow h
        have heq : 2 ^ K - N = 3 ^ r := Nat.sub_sub_self hle
        rw [heq] at hsub
        exact NotDvdPowThreeByTwo r hsub
      have hnot3 : ¬ 3 ∣ N := by
        intro h
        have hsum : N + 3 ^ r = 2 ^ K := Nat.sub_add_cancel hle
        have hd : 3 ∣ N + 3 ^ r := Nat.dvd_add h h3pow
        rw [hsum] at hd
        exact NotDvdPowTwoByThree K hd
      have hc2 : Nat.Coprime N 2 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnot2).symm
      have hc3 : Nat.Coprime N 3 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnot3).symm
      have hc6 : Nat.Coprime N (2 * 3) :=
        Nat.coprime_mul_iff_right.mpr ⟨hc2, hc3⟩
      rw [hN, show (6 : ℕ) = 2 * 3 from rfl]
      exact hc6
    }
  · {
      have hlt : 2 ^ K ≤ 3 ^ r := by omega
      have hN : Int.natAbs ((2 : ℤ) ^ K - (3 : ℤ) ^ r) =
          3 ^ r - 2 ^ K := by
        have h2c : ((2 : ℤ) ^ K) = ((2 ^ K : ℕ) : ℤ) := by norm_cast
        have h3c : ((3 : ℤ) ^ r) = ((3 ^ r : ℕ) : ℤ) := by norm_cast
        rw [h2c, h3c]
        exact Int.natAbs_natCast_sub_natCast_of_le hlt
      set N := 3 ^ r - 2 ^ K
      have hnot2 : ¬ 2 ∣ N := by
        intro h
        have hsum : N + 2 ^ K = 3 ^ r := Nat.sub_add_cancel hlt
        have hd : 2 ∣ N + 2 ^ K := Nat.dvd_add h h2pow
        rw [hsum] at hd
        exact NotDvdPowThreeByTwo r hd
      have hnot3 : ¬ 3 ∣ N := by
        intro h
        have hsub : 3 ∣ 3 ^ r - N := Nat.dvd_sub h3pow h
        have heq : 3 ^ r - N = 2 ^ K := Nat.sub_sub_self hlt
        rw [heq] at hsub
        exact NotDvdPowTwoByThree K hsub
      have hc2 : Nat.Coprime N 2 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnot2).symm
      have hc3 : Nat.Coprime N 3 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnot3).symm
      have hc6 : Nat.Coprime N (2 * 3) :=
        Nat.coprime_mul_iff_right.mpr ⟨hc2, hc3⟩
      rw [hN, show (6 : ℕ) = 2 * 3 from rfl]
      exact hc6
    }

/-- Cancel a natural factor coprime to the divisor from an integer product. -/
theorem IntDvdCancel (m n : ℕ) (z : ℤ) (hcop : Nat.Coprime m n)
    (hdvd : (m : ℤ) ∣ (n : ℤ) * z) : (m : ℤ) ∣ z := by
  cases hdvd with
  | intro t ht => {
      have habs : n * z.natAbs = m * t.natAbs := by
        have hnat := congrArg Int.natAbs ht
        rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast,
          Int.natAbs_natCast] at hnat
        exact hnat
      have hdiv : m ∣ n * z.natAbs := ⟨t.natAbs, habs⟩
      exact Int.ofNat_dvd_left.mpr (hcop.dvd_of_dvd_mul_left hdiv)
    }

/-- Divisibility by an integer agrees with divisibility by its absolute value. -/
theorem AbsDvdIff (d z : ℤ) :
    d ∣ z ↔ ((Int.natAbs d : ℕ) : ℤ) ∣ z := by
  rcases Int.natAbs_eq d with hp | hn
  · {
      rw [hp]
      simp [Int.natAbs_natCast]
    }
  · {
      rw [hn, Int.neg_dvd]
      simp [Int.natAbs_neg, Int.natAbs_natCast]
    }

/-- If the first block is at least as long as the second, the determinant is negative. -/
theorem TwoRunNegative (p q : ℕ) (hq : 1 ≤ q) (hpq : q ≤ p) :
    2 ^ (p + 2 * q) < 3 ^ (p + q) := by
  have ht : p = (p - q) + q := by omega
  rw [ht]
  set t := p - q
  have hl : 2 ^ ((t + q) + 2 * q) = 2 ^ t * 8 ^ q := by
    have hs : (t + q) + 2 * q = t + 3 * q := by omega
    rw [hs, Nat.pow_add]
    have h8 : 8 ^ q = 2 ^ (3 * q) := by
      have hb : (8 : ℕ) = 2 ^ 3 := by decide
      rw [hb, ← Nat.pow_mul]
    rw [h8]
  have hr : 3 ^ ((t + q) + q) = 3 ^ t * 9 ^ q := by
    have hs : (t + q) + q = t + 2 * q := by omega
    rw [hs, Nat.pow_add]
    have h9 : 9 ^ q = 3 ^ (2 * q) := by
      have hb : (9 : ℕ) = 3 ^ 2 := by decide
      rw [hb, ← Nat.pow_mul]
    rw [h9]
  rw [hl, hr]
  have h8lt : 8 ^ q < 9 ^ q :=
    Nat.pow_lt_pow_left (by decide : (8 : ℕ) < 9) (by omega)
  have h2le : 2 ^ t ≤ 3 ^ t :=
    Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 3) t
  have hpos : 0 < 3 ^ t := by
    have h1 : 1 ≤ 3 ^ t := Nat.one_le_pow t 3 (by decide)
    omega
  exact lt_of_le_of_lt (Nat.mul_le_mul_right (8 ^ q) h2le)
    (Nat.mul_lt_mul_of_pos_left h8lt hpos)

/-- A positive determinant dividing the two-run numerator is strictly below `3^(p+q)/3^q`. -/
theorem TwoRunGap (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpos : (3 : ℤ) ^ (p + q) < (2 : ℤ) ^ (p + 2 * q))
    (hdvd : WordDelta (TwoRunWord p q) ∣
      ((WordB (TwoRunWord p q) : ℕ) : ℤ)) :
    2 ^ (p + 2 * q) - 3 ^ (p + q) ∣ 3 ^ p - 2 ^ p ∧
      (2 ^ (p + 2 * q) - 3 ^ (p + q)) * 3 ^ q < 3 ^ (p + q) ∧
      0 < 2 ^ (p + 2 * q) - 3 ^ (p + q) := by
  have hnat : 3 ^ (p + q) < 2 ^ (p + 2 * q) := by
    exact_mod_cast hpos
  set K := p + 2 * q
  set r := p + q
  set N := 2 ^ K - 3 ^ r
  have hposN : 0 < N := Nat.sub_pos_of_lt hnat
  have hshape := TwoRunShape p q
  have hdel : WordDelta (TwoRunWord p q) = ((N : ℕ) : ℤ) := by
    rw [WordDelta, hshape.1, hshape.2, Nat.cast_sub (Nat.le_of_lt hnat),
      Nat.cast_pow, Nat.cast_pow]
    rfl
  have hdiff := TwoRunDifference p q
  have hle : 2 ^ p ≤ 3 ^ p :=
    Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 3) p
  have hM :
      (2 : ℤ) * (3 : ℤ) ^ q * ((3 : ℤ) ^ p - (2 : ℤ) ^ p) =
        ((2 * 3 ^ q * (3 ^ p - 2 ^ p) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hle, Nat.cast_pow,
      Nat.cast_pow, Nat.cast_pow]
    ring
  rw [hdel] at hdvd
  have hsub : ((N : ℕ) : ℤ) ∣
      ((WordB (TwoRunWord p q) : ℕ) : ℤ) - ((N : ℕ) : ℤ) :=
    Int.dvd_sub hdvd (dvd_refl _)
  have hcast : ((2 : ℤ) ^ (p + 2 * q) - (3 : ℤ) ^ (p + q)) =
      ((N : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hnat), Nat.cast_pow, Nat.cast_pow]
    rfl
  have hsubPow : ((N : ℕ) : ℤ) ∣
      ((WordB (TwoRunWord p q) : ℕ) : ℤ) -
        ((2 : ℤ) ^ (p + 2 * q) - (3 : ℤ) ^ (p + q)) := by
    rw [hcast]
    exact hsub
  rw [hdiff, hM] at hsubPow
  have hNat : N ∣ 2 * 3 ^ q * (3 ^ p - 2 ^ p) := by
    have hmul := Int.ofNat_dvd_left.mp hsubPow
    have habs :
        (2 * 3 ^ q * ((3 ^ p - 2 ^ p : ℕ) : ℤ)).natAbs =
          2 * 3 ^ q * (3 ^ p - 2 ^ p) := by
      rw [Int.natAbs_mul, Int.natAbs_mul]
      simp [Int.natAbs_natCast]
    exact habs ▸ hmul
  have hcop := DetCoprimeSix K r (by omega) (by omega)
  have hAbs : Int.natAbs ((2 : ℤ) ^ K - (3 : ℤ) ^ r) = N := by
    have h2c : ((2 : ℤ) ^ K) = ((2 ^ K : ℕ) : ℤ) := by norm_cast
    have h3c : ((3 : ℤ) ^ r) = ((3 ^ r : ℕ) : ℤ) := by norm_cast
    rw [h2c, h3c]
    exact Int.natAbs_natCast_sub_natCast_of_ge (Nat.le_of_lt hnat)
  have hNcop : Nat.Coprime N 6 := by
    rw [← hAbs]
    exact hcop
  have hsix : (6 : ℕ) = 2 * 3 := rfl
  have hsplit := Nat.coprime_mul_iff_right.mp (by rwa [hsix] at hNcop)
  have hc2 : Nat.Coprime N 2 := hsplit.1
  have hc3 : Nat.Coprime N 3 := hsplit.2
  have hc3q : Nat.Coprime N (3 ^ q) := hc3.pow_right q
  have hcf : Nat.Coprime N (2 * 3 ^ q) :=
    Nat.coprime_mul_iff_right.mpr ⟨hc2, hc3q⟩
  have hdN : N ∣ 3 ^ p - 2 ^ p := (hcf.dvd_mul_left).mp hNat
  have h2pos : 0 < 2 ^ p := by
    have h1 : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by decide)
    omega
  have hgapPos : 0 < 3 ^ p - 2 ^ p := by
    have hlt : 2 ^ p < 3 ^ p :=
      Nat.pow_lt_pow_left (by decide : (2 : ℕ) < 3) (by omega)
    exact Nat.sub_pos_of_lt hlt
  have hleN : N ≤ 3 ^ p - 2 ^ p := Nat.le_of_dvd hgapPos hdN
  have hmulLe : N * 3 ^ q ≤ (3 ^ p - 2 ^ p) * 3 ^ q :=
    Nat.mul_le_mul_right (3 ^ q) hleN
  have hltD : 3 ^ p - 2 ^ p < 3 ^ p :=
    Nat.sub_lt_of_pos_le h2pos hle
  have hqpos : 0 < 3 ^ q := by
    have h1 : 1 ≤ 3 ^ q := Nat.one_le_pow q 3 (by decide)
    omega
  have hstrict : (3 ^ p - 2 ^ p) * 3 ^ q < 3 ^ p * 3 ^ q :=
    Nat.mul_lt_mul_of_pos_right hltD hqpos
  have hprod : 3 ^ p * 3 ^ q = 3 ^ (p + q) := by
    rw [← Nat.pow_add]
  have hbound : N * 3 ^ q < 3 ^ (p + q) :=
    lt_of_le_of_lt hmulLe (by simpa [hprod] using hstrict)
  exact ⟨hdN, hbound, hposN⟩

/-- The word `1^1 2^2` has numerator `23` and determinant `5`. -/
theorem TwoRunWitnessOneTwo :
    WordB (TwoRunWord 1 2) = 23 ∧
      2 ^ (1 + 2 * 2) - 3 ^ (1 + 2) = 5 ∧
      ¬ 5 ∣ 23 := by
  decide

/-- A second block of length one or two has no positive divisibility. -/
theorem TwoRunSmallSecondExcluded (p q : ℕ) (hp : 1 ≤ p)
    (hq : q = 1 ∨ q = 2) :
    ¬ (WordDelta (TwoRunWord p q) ∣ ((WordB (TwoRunWord p q) : ℕ) : ℤ) ∧
        (3 : ℤ) ^ (p + q) < (2 : ℤ) ^ (p + 2 * q)) := by
  intro h
  rcases hq with rfl | rfl
  · {
      have hneg := TwoRunNegative p 1 (by decide) hp
      have hcontra : 3 ^ (p + 1) < 2 ^ (p + 2 * 1) := by
        exact_mod_cast h.2
      omega
    }
  · {
      by_cases hp1 : p = 1
      · {
          subst hp1
          have hgap :=
            TwoRunGap 1 2 (by decide) (by decide) h.2 h.1
          have hd := hgap.1
          have hNv : 2 ^ (1 + 2 * 2) - 3 ^ (1 + 2) = 5 := by
            decide
          have hDv : 3 ^ 1 - 2 ^ 1 = 1 := by decide
          rw [hNv, hDv] at hd
          have hle : 5 ≤ 1 := Nat.le_of_dvd (by decide) hd
          omega
        }
      · {
          have hpq : 2 ≤ p := by omega
          have hneg := TwoRunNegative p 2 (by decide) hpq
          have hcontra : 3 ^ (p + 2) < 2 ^ (p + 2 * 2) := by
            exact_mod_cast h.2
          omega
        }
    }

/-- A positive power of the letter `1` has negative determinant. -/
theorem AllOnesNegative (p : ℕ) (hp : 1 ≤ p) :
    (2 : ℤ) ^ p - (3 : ℤ) ^ p < 0 := by
  have hlt : 2 ^ p < 3 ^ p :=
    Nat.pow_lt_pow_left (by decide : (2 : ℕ) < 3) (by omega)
  exact sub_neg_of_lt (by exact_mod_cast hlt)

/-- Integer numerator of a pure power of the letter `2`. -/
theorem AllTwosBInt (q : ℕ) :
    ((WordB (List.replicate q 2) : ℕ) : ℤ) =
      (4 : ℤ) ^ q - (3 : ℤ) ^ q := by
  have h := AccBTwosInt 0 q
  unfold WordB
  simpa [pow_zero] using h

/-- A positive power of the letter `2` equals its positive determinant and fixes `1`. -/
theorem AllTwosFixedPoint (q : ℕ) (hq : 1 ≤ q) :
    (3 : ℤ) ^ q < (2 : ℤ) ^ (2 * q) ∧
      WordDelta (List.replicate q 2) =
        ((WordB (List.replicate q 2) : ℕ) : ℤ) ∧
      (4 : ℤ) * 1 = (3 : ℤ) * 1 + 1 := by
  have hlt : 3 ^ q < 4 ^ q :=
    Nat.pow_lt_pow_left (by decide : (3 : ℕ) < 4) (by omega)
  have h4n : (4 : ℕ) ^ q = 2 ^ (2 * q) := by
    rw [show (4 : ℕ) = 2 ^ 2 by decide, ← Nat.pow_mul]
  rw [h4n] at hlt
  have hI : (3 : ℤ) ^ q < (2 : ℤ) ^ (2 * q) := by
    have hcast := Int.ofNat_lt.mpr hlt
    rw [Nat.cast_pow, Nat.cast_pow] at hcast
    exact hcast
  have h4i : (4 : ℤ) ^ q = (2 : ℤ) ^ (2 * q) := by
    have hb : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
    rw [hb, ← pow_mul]
  have hsum : ExponentSum (List.replicate q 2) = 2 * q := by
    rw [ExponentSumReplicate, Nat.mul_comm]
  have hlen : (List.replicate q 2).length = q := List.length_replicate
  have hdel : WordDelta (List.replicate q 2) =
      (2 : ℤ) ^ (2 * q) - (3 : ℤ) ^ q := by
    rw [WordDelta, hsum, hlen]
  have hB := AllTwosBInt q
  have heq : WordDelta (List.replicate q 2) =
      ((WordB (List.replicate q 2) : ℕ) : ℤ) := by
    rw [hdel, ← h4i, hB]
  have hfix : (4 : ℤ) * 1 = (3 : ℤ) * 1 + 1 := by norm_num
  exact ⟨hI, heq, hfix⟩

/-- Move the first letter to the end. -/
def Rotate1 : List ℕ → List ℕ
  | [] => []
  | a :: as => as ++ [a]

/-- The rotated numerator satisfies `2^a B_1 = 3 B_0 + Delta`. -/
theorem RotateIdentity (a : ℕ) (as : List ℕ) :
    (2 : ℤ) ^ a * ((WordB (Rotate1 (a :: as)) : ℕ) : ℤ) =
      (3 : ℤ) * ((WordB (a :: as) : ℕ) : ℤ) +
        WordDelta (a :: as) := by
  have hrot : Rotate1 (a :: as) = as ++ [a] := rfl
  have happ := AccBAppend 0 as [a]
  have hlen : ([a] : List ℕ).length = 1 := rfl
  have hsing : AccB (ExponentSum as) [a] = 2 ^ ExponentSum as := by
    have hA : AccB (ExponentSum as) [a] =
        3 ^ ([] : List ℕ).length * 2 ^ ExponentSum as +
          AccB (ExponentSum as + a) [] := rfl
    rw [hA]
    simp [AccB, List.length]
  rw [WordB, hrot, happ, hlen, Nat.pow_one, Nat.zero_add, hsing]
  have hB : AccB 0 (a :: as) =
      3 ^ as.length + AccB a as := by
    have hstep : AccB 0 (a :: as) =
        3 ^ as.length * 2 ^ 0 + AccB (0 + a) as := rfl
    simp at hstep
    exact hstep
  have hsh := AccBShift a as
  have hdel : WordDelta (a :: as) =
      (2 : ℤ) ^ (a + ExponentSum as) - (3 : ℤ) ^ (as.length + 1) := by
    have hE : ExponentSum (a :: as) = a + ExponentSum as := rfl
    have hL : (a :: as).length = as.length + 1 := rfl
    rw [WordDelta, hE, hL]
  unfold WordB
  rw [hB, hsh, hdel]
  have hlenp : (3 : ℤ) ^ (as.length + 1) =
      (3 : ℤ) ^ as.length * 3 := by
    rw [pow_succ]
  have hsump : (2 : ℤ) ^ (a + ExponentSum as) =
      (2 : ℤ) ^ a * (2 : ℤ) ^ ExponentSum as := by
    rw [pow_add]
  simp [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hlenp, hsump]
  ring

/-- Rotation preserves length and exponent sum. -/
theorem Rotate1Shape (xs : List ℕ) :
    ExponentSum (Rotate1 xs) = ExponentSum xs ∧
      (Rotate1 xs).length = xs.length := by
  cases xs with
  | nil => {
      simp [Rotate1, ExponentSum]
    }
  | cons a as => {
      have hrot : Rotate1 (a :: as) = as ++ [a] := rfl
      rw [hrot, ExponentSumAppend, List.length_append]
      have hE : ExponentSum (a :: as) = a + ExponentSum as := rfl
      have hL : (a :: as).length = as.length + 1 := rfl
      have hS : ExponentSum [a] = a := rfl
      have hOne : ([a] : List ℕ).length = 1 := rfl
      constructor
      · {
          rw [hS, hE, Nat.add_comm]
        }
      · {
          rw [hOne, hL]
        }
    }

/-- A nonempty word remains nonempty after one rotation. -/
theorem Rotate1Nonempty (xs : List ℕ) (hne : xs ≠ []) :
    Rotate1 xs ≠ [] := by
  cases xs with
  | nil => {
      exact absurd rfl hne
    }
  | cons a as => {
      intro h
      have hnil : as ++ [a] = [] := by
        simpa [Rotate1] using h
      cases as with
      | nil => {
          simp at hnil
        }
      | cons b bs => {
          simp at hnil
        }
    }

/-- One rotation preserves divisibility of the numerator by the determinant. -/
theorem RotatePreservesDiv (xs : List ℕ) (hK : 1 ≤ ExponentSum xs)
    (hne : xs ≠ []) :
    WordDelta xs ∣ ((WordB xs : ℕ) : ℤ) ↔
      WordDelta xs ∣ ((WordB (Rotate1 xs) : ℕ) : ℤ) := by
  cases xs with
  | nil => {
      exact absurd rfl hne
    }
  | cons a as => {
      have hlen : 1 ≤ (a :: as).length := by simp
      have hcop :=
        DetCoprimeSix (ExponentSum (a :: as)) (a :: as).length hK hlen
      let N := Int.natAbs (WordDelta (a :: as))
      have hc6 : Nat.Coprime N 6 := by
        simpa [N, WordDelta] using hcop
      have hsix : (6 : ℕ) = 2 * 3 := rfl
      have hsplit := Nat.coprime_mul_iff_right.mp (by rwa [hsix] at hc6)
      have hc2 : Nat.Coprime N 2 := hsplit.1
      have hc3 : Nat.Coprime N 3 := hsplit.2
      have hca : Nat.Coprime N (2 ^ a) := hc2.pow_right a
      have hEq := RotateIdentity a as
      constructor
      · {
          intro hB
          have hmul : WordDelta (a :: as) ∣
              (2 : ℤ) ^ a * ((WordB (Rotate1 (a :: as)) : ℕ) : ℤ) := by
            rw [hEq]
            exact Int.dvd_add (dvd_mul_of_dvd_right hB (3 : ℤ))
              (dvd_refl _)
          have hAbs :=
            (AbsDvdIff (WordDelta (a :: as)) _).mp hmul
          have hpow : (2 : ℤ) ^ a = ((2 ^ a : ℕ) : ℤ) := by
            norm_cast
          rw [hpow] at hAbs
          have hB1 := IntDvdCancel N (2 ^ a) _ hca hAbs
          exact (AbsDvdIff (WordDelta (a :: as)) _).mpr hB1
        }
      · {
          intro hB1
          have hmul : WordDelta (a :: as) ∣
              (2 : ℤ) ^ a * ((WordB (Rotate1 (a :: as)) : ℕ) : ℤ) :=
            dvd_mul_of_dvd_right hB1 _
          have heqsub :
              (2 : ℤ) ^ a * ((WordB (Rotate1 (a :: as)) : ℕ) : ℤ) -
                  WordDelta (a :: as) =
                (3 : ℤ) * ((WordB (a :: as) : ℕ) : ℤ) := by
            rw [hEq]
            ring
          have hsub : WordDelta (a :: as) ∣
              (2 : ℤ) ^ a * ((WordB (Rotate1 (a :: as)) : ℕ) : ℤ) -
                WordDelta (a :: as) :=
            Int.dvd_sub hmul (dvd_refl _)
          rw [heqsub] at hsub
          have hAbs := (AbsDvdIff (WordDelta (a :: as)) _).mp hsub
          have hthree : (3 : ℤ) = ((3 : ℕ) : ℤ) := rfl
          rw [hthree] at hAbs
          have hB0 := IntDvdCancel N 3 _ hc3 hAbs
          exact (AbsDvdIff (WordDelta (a :: as)) _).mpr hB0
        }
    }

/-- Rotate the first letter to the end, `n` times. -/
def RotateN : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | n + 1, xs => RotateN n (Rotate1 xs)

/-- Rotation by a sum is rotation in succession. -/
theorem RotateNAdd (m n : ℕ) (xs : List ℕ) :
    RotateN (m + n) xs = RotateN n (RotateN m xs) := by
  induction m generalizing xs with
  | zero => {
      simp [RotateN]
    }
  | succ m ih => {
      rw [Nat.succ_add]
      have hdef : RotateN ((m + n) + 1) xs =
          RotateN (m + n) (Rotate1 xs) := rfl
      rw [hdef, ih (Rotate1 xs)]
      have hrec : RotateN (m + 1) xs = RotateN m (Rotate1 xs) := rfl
      rw [hrec]
    }

/-- Any positive number of rotations preserves numerator divisibility. -/
theorem RotateNPreservesDiv (n : ℕ) (xs : List ℕ)
    (hK : 1 ≤ ExponentSum xs) (hne : xs ≠ []) :
    WordDelta xs ∣ ((WordB xs : ℕ) : ℤ) ↔
      WordDelta xs ∣ ((WordB (RotateN n xs) : ℕ) : ℤ) := by
  induction n generalizing xs with
  | zero => {
      simp [RotateN]
    }
  | succ n ih => {
      have hstep := RotatePreservesDiv xs hK hne
      have hshape := Rotate1Shape xs
      have hK' : 1 ≤ ExponentSum (Rotate1 xs) := by
        rw [hshape.1]
        exact hK
      have hne' : Rotate1 xs ≠ [] := Rotate1Nonempty xs hne
      have ih' := ih (Rotate1 xs) hK' hne'
      have hdel : WordDelta (Rotate1 xs) = WordDelta xs := by
        rw [WordDelta, WordDelta, hshape.1, hshape.2]
      rw [hdel] at ih'
      have hdef : RotateN (n + 1) xs = RotateN n (Rotate1 xs) := rfl
      rw [hdef]
      exact hstep.trans ih'
    }

/-- Rotating a constant prefix past the suffix moves that prefix to the end. -/
theorem RotateNFront (n a : ℕ) (ys : List ℕ) :
    RotateN n (List.replicate n a ++ ys) =
      ys ++ List.replicate n a := by
  induction n generalizing ys with
  | zero => {
      simp [RotateN, List.replicate_zero]
    }
  | succ n ih => {
      rw [List.replicate_succ, List.cons_append]
      have hdef : RotateN (n + 1)
          (a :: (List.replicate n a ++ ys)) =
          RotateN n (Rotate1 (a :: (List.replicate n a ++ ys))) := rfl
      rw [hdef]
      have hrot : Rotate1 (a :: (List.replicate n a ++ ys)) =
          (List.replicate n a ++ ys) ++ [a] := rfl
      rw [hrot]
      have hassoc : (List.replicate n a ++ ys) ++ [a] =
          List.replicate n a ++ (ys ++ [a]) := by
        simp [List.append_assoc]
      rw [hassoc, ih (ys ++ [a])]
      simp [List.append_assoc, List.replicate_succ]
    }

/-- The word `1^p 2^q 1^s`. -/
def ThreeRunWord (p q s : ℕ) : List ℕ :=
  List.replicate p 1 ++ List.replicate q 2 ++ List.replicate s 1

/-- Length and exponent sum of `1^p 2^q 1^s`. -/
theorem ThreeRunShape (p q s : ℕ) :
    (ThreeRunWord p q s).length = p + q + s ∧
      ExponentSum (ThreeRunWord p q s) = p + s + 2 * q := by
  constructor
  · {
      rw [ThreeRunWord, List.length_append, List.length_append,
        List.length_replicate, List.length_replicate,
        List.length_replicate]
    }
  · {
      rw [ThreeRunWord, ExponentSumAppend, ExponentSumAppend,
        ExponentSumReplicate, ExponentSumReplicate, ExponentSumReplicate,
        Nat.mul_one, Nat.mul_one]
      omega
    }

/-- Rotating `1^p 2^q 1^s` by `p + q` letters yields `1^(p+s) 2^q`. -/
theorem ThreeRunRotate (p q s : ℕ) :
    RotateN (p + q) (ThreeRunWord p q s) =
      TwoRunWord (p + s) q := by
  rw [ThreeRunWord, TwoRunWord]
  have hassoc : List.replicate p 1 ++ List.replicate q 2 ++
      List.replicate s 1 =
      List.replicate p 1 ++
        (List.replicate q 2 ++ List.replicate s 1) := by
    simp [List.append_assoc]
  rw [RotateNAdd, hassoc]
  have h1 :=
    RotateNFront p 1 (List.replicate q 2 ++ List.replicate s 1)
  rw [h1]
  have hassoc2 : (List.replicate q 2 ++ List.replicate s 1) ++
      List.replicate p 1 =
      List.replicate q 2 ++
        (List.replicate s 1 ++ List.replicate p 1) := by
    simp [List.append_assoc]
  rw [hassoc2]
  have h2 :=
    RotateNFront q 2 (List.replicate s 1 ++ List.replicate p 1)
  rw [h2]
  have hrep : List.replicate s 1 ++ List.replicate p 1 =
      List.replicate (s + p) 1 := by
    rw [← List.replicate_add]
  rw [hrep, Nat.add_comm s p]

/-- The three-run determinant equals the determinant of the merged two-run word. -/
theorem ThreeRunDeltaEq (p q s : ℕ) :
    WordDelta (ThreeRunWord p q s) =
      WordDelta (TwoRunWord (p + s) q) := by
  have h3 := ThreeRunShape p q s
  have h2 := TwoRunShape (p + s) q
  have hlen : (ThreeRunWord p q s).length =
      (TwoRunWord (p + s) q).length := by
    rw [h3.1, h2.1]
    omega
  have hsum : ExponentSum (ThreeRunWord p q s) =
      ExponentSum (TwoRunWord (p + s) q) := by
    rw [h3.2, h2.2]
  rw [WordDelta, WordDelta, hlen, hsum]

/-- Positive three-run words are nonempty and have positive exponent sum. -/
theorem ThreeRunNonempty (p q s : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hs : 1 ≤ s) :
    ThreeRunWord p q s ≠ [] ∧ 1 ≤ ExponentSum (ThreeRunWord p q s) := by
  have hshape := ThreeRunShape p q s
  constructor
  · {
      intro h
      have hlen := hshape.1
      rw [h, List.length_nil] at hlen
      omega
    }
  · {
      rw [hshape.2]
      omega
    }

/-- Divisibility for `1^p 2^q 1^s` is divisibility for `1^(p+s) 2^q`. -/
theorem ThreeRunDivIff (p q s : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hs : 1 ≤ s) :
    WordDelta (ThreeRunWord p q s) ∣
        ((WordB (ThreeRunWord p q s) : ℕ) : ℤ) ↔
      WordDelta (TwoRunWord (p + s) q) ∣
        ((WordB (TwoRunWord (p + s) q) : ℕ) : ℤ) := by
  have hne := ThreeRunNonempty p q s hp hq hs
  have hiff :=
    RotateNPreservesDiv (p + q) (ThreeRunWord p q s) hne.2 hne.1
  have hrot := ThreeRunRotate p q s
  rw [hrot] at hiff
  have hdel := ThreeRunDeltaEq p q s
  conv_rhs at hiff => rw [hdel]
  exact hiff

/-- The two-run gap passes to `1^p 2^q 1^s` through the merged exponents `p + s` and `q`. -/
theorem ThreeRunGap (p q s : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (hpos : (3 : ℤ) ^ ((p + s) + q) < (2 : ℤ) ^ ((p + s) + 2 * q))
    (hdvd : WordDelta (ThreeRunWord p q s) ∣
      ((WordB (ThreeRunWord p q s) : ℕ) : ℤ)) :
    2 ^ ((p + s) + 2 * q) - 3 ^ ((p + s) + q) ∣
        3 ^ (p + s) - 2 ^ (p + s) ∧
      (2 ^ ((p + s) + 2 * q) - 3 ^ ((p + s) + q)) * 3 ^ q <
        3 ^ ((p + s) + q) ∧
      0 < 2 ^ ((p + s) + 2 * q) - 3 ^ ((p + s) + q) := by
  have hiff := ThreeRunDivIff p q s hp hq hs
  have hdvd2 := hiff.mp hdvd
  exact TwoRunGap (p + s) q (by omega) hq hpos hdvd2

/-- If the second block has length one or two, `1^p 2^q 1^s` has no positive closure. -/
theorem ThreeRunSmallSecondExcluded (p q s : ℕ) (hp : 1 ≤ p)
    (hs : 1 ≤ s) (hq : q = 1 ∨ q = 2) :
    ¬ (WordDelta (ThreeRunWord p q s) ∣
          ((WordB (ThreeRunWord p q s) : ℕ) : ℤ) ∧
        (3 : ℤ) ^ (p + s + q) < (2 : ℤ) ^ (p + s + 2 * q)) := by
  intro h
  have hq1 : 1 ≤ q := by
    rcases hq with rfl | rfl
    · exact (by decide)
    · exact (by decide)
  have hiff := ThreeRunDivIff p q s hp hq1 hs
  have hbad := TwoRunSmallSecondExcluded (p + s) q (by omega) hq
  apply hbad
  constructor
  · {
      exact hiff.mp h.1
    }
  · {
      exact h.2
    }

end GeneralizedCollatz
