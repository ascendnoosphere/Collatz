-- SPDX-License-Identifier: CC-BY-4.0
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Equal halves of a binary parity word.

An odd letter is `true` and an even letter is `false`, read chronologically.
For halves of common length `h` and common odd-step count `r`, with `q` odd and
`Q = 2^h - q^r > 0`, the closure denominator of the concatenation divides the
unscaled numerator if and only if both factors below vanish. The concatenation
identity is established first and is then rearranged, before either direction,
as

  `A(UV) - q^r (A(U) - A(V)) = M A(V)`,
  `A(UV) = q^r (A(U) + A(V)) + Q A(V)`,

where `M = 2^h + q^r`. Equal odd-step counts are a hypothesis. Vanishing of one
factor is not a closure, and no orbit is claimed to reach `1`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Number of odd letters in a chronological parity word. -/
def OddCount (w : List Bool) : ℕ := w.count true

/-- The empty word has no odd letters. -/
theorem OddCountNil : OddCount ([] : List Bool) = 0 := rfl

/-- An odd letter contributes one to the odd-step count. -/
theorem OddCountTrue (bs : List Bool) :
    OddCount (true :: bs) = OddCount bs + 1 := by
  simp [OddCount, List.count_cons_self]

/-- An even letter does not change the odd-step count. -/
theorem OddCountFalse (bs : List Bool) :
    OddCount (false :: bs) = OddCount bs := by
  simp [OddCount, List.count_cons_of_ne (by decide : false ≠ true)]

/-- Unscaled numerator of a suffix whose first letter has index `j`.

An even letter contributes nothing. An odd letter at index `j` contributes
`q` to the number of later odd letters, times `2^j`. -/
def WordNumeratorFrom (q j : ℕ) : List Bool → ℕ
  | [] => 0
  | false :: bs => WordNumeratorFrom q (j + 1) bs
  | true :: bs =>
      q ^ OddCount bs * 2 ^ j + WordNumeratorFrom q (j + 1) bs

/-- The empty suffix has numerator zero. -/
theorem WordNumeratorFromNil (q j : ℕ) : WordNumeratorFrom q j [] = 0 := rfl

/-- An even letter shifts the index and adds nothing. -/
theorem WordNumeratorFalse (q j : ℕ) (bs : List Bool) :
    WordNumeratorFrom q j (false :: bs) = WordNumeratorFrom q (j + 1) bs := rfl

/-- An odd letter contributes `q` to the later odd count, times `2^j`. -/
theorem WordNumeratorTrue (q j : ℕ) (bs : List Bool) :
    WordNumeratorFrom q j (true :: bs) =
      q ^ OddCount bs * 2 ^ j + WordNumeratorFrom q (j + 1) bs := rfl

/-- Unscaled numerator of a word, with the first letter at index zero. -/
def WordNumerator (q : ℕ) (w : List Bool) : ℕ := WordNumeratorFrom q 0 w

/-- Raising the index by `k` multiplies the numerator by `2^k`. -/
theorem WordNumeratorFromShift (q j k : ℕ) (w : List Bool) :
    WordNumeratorFrom q (j + k) w = 2 ^ k * WordNumeratorFrom q j w := by
  induction w generalizing j with
  | nil =>
      rw [WordNumeratorFromNil, WordNumeratorFromNil, Nat.mul_zero]
  | cons b bs ih =>
      cases b with
      | false =>
          rw [WordNumeratorFalse, WordNumeratorFalse]
          have hidx : j + k + 1 = j + 1 + k := by omega
          rw [hidx]
          exact ih (j + 1)
      | true =>
          rw [WordNumeratorTrue, WordNumeratorTrue]
          have hidx : j + k + 1 = j + 1 + k := by omega
          rw [hidx, ih (j + 1)]
          have hpow : 2 ^ (j + k) = 2 ^ j * 2 ^ k := by
            rw [Nat.add_comm j k, Nat.pow_add, Nat.mul_comm]
          rw [hpow, ← Nat.mul_assoc,
            Nat.mul_comm (q ^ OddCount bs * 2 ^ j) (2 ^ k), ← Nat.mul_add]

/-- The odd-letter contribution splits across a concatenation of blocks. -/
theorem NumeratorTrueStep (a b x y z : ℕ) :
    (a * b) * x + (b * y + z) = b * (a * x + y) + z := by
  rw [← Nat.add_assoc, Nat.mul_comm a b, Nat.mul_assoc, ← Nat.mul_add]

/-- Suffix numerator of a concatenation, with the first letter at index `j`. -/
theorem WordNumeratorAppend (q j : ℕ) (U V : List Bool) :
    WordNumeratorFrom q j (U ++ V) =
      q ^ OddCount V * WordNumeratorFrom q j U +
        2 ^ (j + U.length) * WordNumerator q V := by
  induction U generalizing j with
  | nil =>
      rw [List.nil_append, List.length_nil, Nat.add_zero]
      have hshift := WordNumeratorFromShift q 0 j V
      have hidx : 0 + j = j := Nat.zero_add j
      rw [hidx] at hshift
      rw [hshift, WordNumerator, WordNumeratorFromNil, Nat.mul_zero,
        Nat.zero_add]
  | cons b bs ih =>
      cases b with
      | false =>
          rw [List.cons_append, List.length_cons, WordNumeratorFalse,
            WordNumeratorFalse]
          have hexp : j + 1 + bs.length = j + (bs.length + 1) := by omega
          rw [ih (j + 1), hexp]
      | true =>
          rw [List.cons_append, List.length_cons, WordNumeratorTrue,
            WordNumeratorTrue]
          have hc : OddCount (bs ++ V) = OddCount bs + OddCount V := by
            rw [OddCount, List.count_append, ← OddCount, ← OddCount]
          have hexp : j + 1 + bs.length = j + (bs.length + 1) := by omega
          rw [ih (j + 1), hc, Nat.pow_add, hexp]
          exact NumeratorTrueStep (q ^ OddCount bs) (q ^ OddCount V) (2 ^ j)
            (WordNumeratorFrom q (j + 1) bs)
            (2 ^ (j + (bs.length + 1)) * WordNumerator q V)

/-- Source identity: the numerator of `UV` splits by the odd count of `V`. -/
theorem WordNumeratorConcat (q : ℕ) (U V : List Bool) :
    WordNumerator q (U ++ V) =
      q ^ OddCount V * WordNumerator q U +
        2 ^ U.length * WordNumerator q V := by
  have happ := WordNumeratorAppend q 0 U V
  rw [Nat.zero_add] at happ
  exact happ

/-- The source identity at a common half-length and a fixed odd count of `V`. -/
theorem EqualHalvesSource (q h r : ℕ) (U V : List Bool) (hU : U.length = h)
    (rV : OddCount V = r) :
    WordNumerator q (U ++ V) =
      q ^ r * WordNumerator q U + 2 ^ h * WordNumerator q V := by
  rw [WordNumeratorConcat, rV, hU]

/-- Equal length and equal odd count add in the concatenation. -/
theorem EqualHalvesTotal (h r : ℕ) (U V : List Bool) (hU : U.length = h)
    (hV : V.length = h) (rU : OddCount U = r) (rV : OddCount V = r) :
    (U ++ V).length = 2 * h ∧ OddCount (U ++ V) = 2 * r := by
  constructor
  · rw [List.length_append, hU, hV, Nat.two_mul]
  · rw [OddCount, List.count_append, ← OddCount, ← OddCount, rU, rV, Nat.two_mul]

/-- Adding the second half cancels the cross term against `M = 2^h + q^r`. -/
theorem EqualHalvesDifferenceNat (q h r Au Av : ℕ) :
    q ^ r * Au + 2 ^ h * Av + q ^ r * Av =
      q ^ r * Au + (2 ^ h + q ^ r) * Av := by
  rw [Nat.add_assoc, ← Nat.add_mul]

/-- From the source identity, `M` divides `A(UV)` exactly when it divides the
cross term `q^r (A(U) - A(V))`. The rearrangement is the difference bridge. -/
theorem EqualHalvesDifferenceBridge (q h r Au Av : ℕ) :
    ((q ^ r * Au + 2 ^ h * Av : ℕ) : ℤ) -
        (q ^ r : ℤ) * ((Au : ℤ) - (Av : ℤ)) =
      ((2 ^ h + q ^ r : ℕ) : ℤ) * (Av : ℤ) := by
  push_cast
  ring

/-- From the source identity and `2^h = Q + q^r`, the sum bridge displays `Q`. -/
theorem EqualHalvesSumBridge (q h r Au Av : ℕ) (hle : q ^ r ≤ 2 ^ h) :
    q ^ r * Au + 2 ^ h * Av =
      q ^ r * (Au + Av) + (2 ^ h - q ^ r) * Av := by
  have h2 : 2 ^ h = 2 ^ h - q ^ r + q ^ r := (Nat.sub_add_cancel hle).symm
  calc
    q ^ r * Au + 2 ^ h * Av
        = q ^ r * Au + (2 ^ h - q ^ r + q ^ r) * Av := by
          conv_lhs => rw [h2]
    _ = q ^ r * Au + ((2 ^ h - q ^ r) * Av + q ^ r * Av) := by
          rw [Nat.add_mul]
    _ = q ^ r * Au + (q ^ r * Av + (2 ^ h - q ^ r) * Av) := by
          rw [Nat.add_comm ((2 ^ h - q ^ r) * Av)]
    _ = q ^ r * Au + q ^ r * Av + (2 ^ h - q ^ r) * Av := by
          rw [← Nat.add_assoc]
    _ = q ^ r * (Au + Av) + (2 ^ h - q ^ r) * Av := by
          rw [← Nat.mul_add]

/-- The closure denominator factors as the product of the two half-moduli. -/
theorem EqualHalvesDeterminant (q h r : ℕ) :
    (2 ^ h - q ^ r) * (2 ^ h + q ^ r) = 2 ^ (2 * h) - q ^ (2 * r) := by
  have hsq := Nat.pow_two_sub_pow_two (2 ^ h) (q ^ r)
  have hprod : (2 ^ h - q ^ r) * (2 ^ h + q ^ r) =
      (2 ^ h) ^ 2 - (q ^ r) ^ 2 := by
    rw [Nat.mul_comm, ← hsq]
  rw [hprod, ← Nat.pow_mul', ← Nat.pow_mul']

/-- A residue of `1` modulo `2` is coprime to `2`. -/
theorem CoprimeTwoOfModOne (n : ℕ) (hn : n % 2 = 1) : Nat.Coprime n 2 := by
  rw [Nat.coprime_two_right]
  exact Nat.odd_iff.mpr hn

/-- Odd powers of an odd base remain odd. -/
theorem PowModTwoOfModOne (q r : ℕ) (hq : q % 2 = 1) : q ^ r % 2 = 1 := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih, hq]

/-- `q^r` is coprime to both half-moduli, and the half-moduli are coprime. -/
theorem EqualHalvesCoprime (q h r : ℕ) (hq : q % 2 = 1)
    (hQpos : 0 < 2 ^ h - q ^ r) :
    Nat.Coprime (q ^ r) (2 ^ h + q ^ r) ∧
      Nat.Coprime (q ^ r) (2 ^ h - q ^ r) ∧
        Nat.Coprime (2 ^ h + q ^ r) (2 ^ h - q ^ r) := by
  have hle : q ^ r ≤ 2 ^ h := Nat.le_of_lt (Nat.lt_of_sub_pos hQpos)
  have hqpos : 0 < q := by
    have hd := Nat.div_add_mod q 2
    rw [hq] at hd
    omega
  have hh : 1 ≤ h := by
    by_contra hh
    have hz : h = 0 := by omega
    have hlt : q ^ r < 1 := by
      have hpos := hQpos
      rw [hz, Nat.pow_zero] at hpos
      exact Nat.lt_of_sub_pos hpos
    have hge : 1 ≤ q ^ r := Nat.one_le_pow r q hqpos
    omega
  have hqr : Nat.Coprime (q ^ r) 2 :=
    (CoprimeTwoOfModOne q hq).pow_left r
  have hqr2 : Nat.Coprime (q ^ r) (2 ^ h) := hqr.pow_right h
  have hM : Nat.Coprime (q ^ r) (2 ^ h + q ^ r) :=
    Nat.coprime_add_self_right.mpr hqr2
  have hQ : Nat.Coprime (q ^ r) (2 ^ h - q ^ r) := by
    have hback : Nat.Coprime (q ^ r) ((2 ^ h - q ^ r) + q ^ r) := by
      rw [Nat.sub_add_cancel hle]
      exact hqr2
    exact Nat.coprime_add_self_right.mp hback
  have hQodd : (2 ^ h - q ^ r) % 2 = 1 := by
    have hpow : 2 ^ h % 2 = 0 := by
      have hs : (h - 1) + 1 = h := Nat.sub_add_cancel hh
      rw [← hs, Nat.pow_succ, Nat.mul_comm, Nat.mul_mod_right]
    have hmod : ((2 ^ h - q ^ r) + q ^ r) % 2 = 0 := by
      rw [Nat.sub_add_cancel hle, hpow]
    have hsplit : ((2 ^ h - q ^ r) % 2 + (q ^ r) % 2) % 2 = 0 := by
      rw [← Nat.add_mod]
      exact hmod
    rw [PowModTwoOfModOne q r hq] at hsplit
    cases Nat.mod_two_eq_zero_or_one (2 ^ h - q ^ r) with
    | inl h0 =>
        have hcontra : (0 + 1) % 2 = 1 := by decide
        rw [h0, hcontra] at hsplit
        exact absurd hsplit (by decide)
    | inr h1 =>
        exact h1
  have hQ2 : Nat.Coprime (2 ^ h - q ^ r) 2 :=
    CoprimeTwoOfModOne (2 ^ h - q ^ r) hQodd
  have hmul : Nat.Coprime (2 * q ^ r) (2 ^ h - q ^ r) :=
    (hQ2.mul_right hQ.symm).symm
  have hform : 2 ^ h + q ^ r = (2 ^ h - q ^ r) + 2 * q ^ r := by
    have hback : 2 ^ h = (2 ^ h - q ^ r) + q ^ r :=
      (Nat.sub_add_cancel hle).symm
    calc
      2 ^ h + q ^ r = (2 ^ h - q ^ r) + q ^ r + q ^ r := by
          conv_lhs => rw [hback]
      _ = (2 ^ h - q ^ r) + (q ^ r + q ^ r) := by rw [Nat.add_assoc]
      _ = (2 ^ h - q ^ r) + 2 * q ^ r := by rw [← Nat.two_mul]
  have hMQ : Nat.Coprime (2 ^ h + q ^ r) (2 ^ h - q ^ r) := by
    rw [hform]
    exact Nat.coprime_self_add_left.mpr hmul
  exact ⟨hM, hQ, hMQ⟩

/-- Cancel a factor coprime to the divisor from an integer divisibility. -/
theorem IntDvdCancel (m n : ℕ) (z : ℤ) (hcop : Nat.Coprime m n)
    (hdvd : (m : ℤ) ∣ (n : ℤ) * z) : (m : ℤ) ∣ z := by
  cases hdvd with
  | intro t ht =>
      have habs : n * z.natAbs = m * t.natAbs := by
        have hnat := congrArg Int.natAbs ht
        rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast,
          Int.natAbs_natCast] at hnat
        exact hnat
      have hdiv : m ∣ n * z.natAbs := ⟨t.natAbs, habs⟩
      exact Int.ofNat_dvd_left.mpr (hcop.dvd_of_dvd_mul_left hdiv)

/-- Closure by the factored denominator is the joint vanishing of both factors.

Equal length and equal odd count make `2^{|UV|} - q^{o(UV)}` equal to
`M Q`. The two bridges, proved from the source identity before this
equivalence, convert divisibility by `M` into divisibility of `A(U) - A(V)`
and divisibility by `Q` into divisibility of `A(U) + A(V)`. -/
theorem EqualHalvesCriterion (q h r : ℕ) (U V : List Bool) (hq : q % 2 = 1)
    (hQpos : 0 < 2 ^ h - q ^ r) (hU : U.length = h) (hV : V.length = h)
    (rU : OddCount U = r) (rV : OddCount V = r) :
    (2 ^ (U ++ V).length - q ^ OddCount (U ++ V)) ∣
        WordNumerator q (U ++ V) ↔
      ((2 ^ h + q ^ r : ℕ) : ℤ) ∣
          ((WordNumerator q U : ℤ) - (WordNumerator q V : ℤ)) ∧
        (2 ^ h - q ^ r) ∣ WordNumerator q U + WordNumerator q V := by
  have hsrc := EqualHalvesSource q h r U V hU rV
  have hle : q ^ r ≤ 2 ^ h := Nat.le_of_lt (Nat.lt_of_sub_pos hQpos)
  have hcop := EqualHalvesCoprime q h r hq hQpos
  have hqrM := hcop.1
  have hqrQ := hcop.2.1
  have hMQ := hcop.2.2
  have hbridge := EqualHalvesDifferenceBridge q h r (WordNumerator q U)
    (WordNumerator q V)
  rw [← hsrc] at hbridge
  have hsum := EqualHalvesSumBridge q h r (WordNumerator q U)
    (WordNumerator q V) hle
  rw [← hsrc] at hsum
  have hQiff :
      (2 ^ h - q ^ r) ∣ WordNumerator q (U ++ V) ↔
        (2 ^ h - q ^ r) ∣
          q ^ r * (WordNumerator q U + WordNumerator q V) := by
    rw [hsum]
    exact (Nat.dvd_add_iff_left
      (Nat.dvd_mul_right (2 ^ h - q ^ r) (WordNumerator q V))).symm
  have hQsum :
      (2 ^ h - q ^ r) ∣ WordNumerator q (U ++ V) ↔
        (2 ^ h - q ^ r) ∣ WordNumerator q U + WordNumerator q V := by
    rw [hQiff]
    constructor
    · intro hmul
      exact (hqrQ.symm).dvd_of_dvd_mul_left hmul
    · intro hdiv
      exact Nat.dvd_mul_left_of_dvd hdiv (q ^ r)
  have hMiff :
      ((2 ^ h + q ^ r : ℕ) : ℤ) ∣ (WordNumerator q (U ++ V) : ℤ) ↔
        ((2 ^ h + q ^ r : ℕ) : ℤ) ∣
          (q ^ r : ℤ) *
            ((WordNumerator q U : ℤ) - (WordNumerator q V : ℤ)) :=
    Int.dvd_iff_dvd_of_dvd_sub (by
      rw [hbridge]
      exact Int.dvd_mul_right _ _)
  have hMdiff :
      ((2 ^ h + q ^ r : ℕ) : ℤ) ∣ (WordNumerator q (U ++ V) : ℤ) ↔
        ((2 ^ h + q ^ r : ℕ) : ℤ) ∣
          (WordNumerator q U : ℤ) - (WordNumerator q V : ℤ) := by
    rw [hMiff]
    constructor
    · intro hmul
      exact IntDvdCancel (2 ^ h + q ^ r) (q ^ r)
        ((WordNumerator q U : ℤ) - (WordNumerator q V : ℤ)) hqrM.symm hmul
    · intro hdiv
      cases hdiv with
      | intro k hk =>
          refine ⟨(q ^ r : ℤ) * k, ?_⟩
          rw [hk, Int.mul_left_comm]
  have htot := EqualHalvesTotal h r U V hU hV rU rV
  have hden : 2 ^ (U ++ V).length - q ^ OddCount (U ++ V) =
      2 ^ (2 * h) - q ^ (2 * r) := by
    rw [htot.1, htot.2]
  rw [hden, ← EqualHalvesDeterminant q h r, Nat.mul_comm]
  constructor
  · intro hprod
    have hMnat : (2 ^ h + q ^ r) ∣ WordNumerator q (U ++ V) :=
      Nat.dvd_trans
        (Nat.dvd_mul_right (2 ^ h + q ^ r) (2 ^ h - q ^ r)) hprod
    have hQnat : (2 ^ h - q ^ r) ∣ WordNumerator q (U ++ V) :=
      Nat.dvd_trans
        (Nat.dvd_mul_left (2 ^ h - q ^ r) (2 ^ h + q ^ r)) hprod
    refine ⟨(hMdiff.mp (Int.natCast_dvd_natCast.mpr hMnat)), hQsum.mp hQnat⟩
  · intro hboth
    have hMnat : (2 ^ h + q ^ r) ∣ WordNumerator q (U ++ V) :=
      Int.natCast_dvd_natCast.mp (hMdiff.mpr hboth.1)
    have hQnat : (2 ^ h - q ^ r) ∣ WordNumerator q (U ++ V) :=
      hQsum.mpr hboth.2
    exact hMQ.mul_dvd_of_dvd_of_dvd hMnat hQnat

/-- Four even letters followed by two odd letters. -/
def ExampleLeft : List Bool := [false, false, false, false, true, true]

/-- Odd, even, odd, then three even letters. -/
def ExampleRight : List Bool := [true, false, true, false, false, false]

/-- `000011` has two odd letters. -/
theorem ExampleLeftOdd : OddCount ExampleLeft = 2 := by
  rw [ExampleLeft, OddCountFalse, OddCountFalse, OddCountFalse, OddCountFalse,
    OddCountTrue, OddCountTrue, OddCountNil]

/-- `101000` has two odd letters. -/
theorem ExampleRightOdd : OddCount ExampleRight = 2 := by
  rw [ExampleRight, OddCountTrue, OddCountFalse, OddCountTrue, OddCountFalse,
    OddCountFalse, OddCountFalse, OddCountNil]

/-- The numerator of `000011` at `q = 3` is `3 * 2^4 + 2^5`. -/
theorem ExampleLeftNum : WordNumerator 3 ExampleLeft = 80 := by
  rw [WordNumerator, ExampleLeft, WordNumeratorFalse, WordNumeratorFalse,
    WordNumeratorFalse, WordNumeratorFalse, WordNumeratorTrue,
    WordNumeratorTrue, WordNumeratorFromNil, OddCountTrue]
  decide

/-- The numerator of `101000` at `q = 3` is `3 * 2^0 + 2^2`. -/
theorem ExampleRightNum : WordNumerator 3 ExampleRight = 7 := by
  have htail : OddCount [false, false, false] = 0 := by
    rw [OddCountFalse, OddCountFalse, OddCountFalse, OddCountNil]
  have hzero : WordNumeratorFrom 3 3 [false, false, false] = 0 := by
    rw [WordNumeratorFalse, WordNumeratorFalse, WordNumeratorFalse,
      WordNumeratorFromNil]
  have hmid : WordNumeratorFrom 3 2 [true, false, false, false] = 4 := by
    rw [WordNumeratorTrue, hzero, htail, Nat.pow_zero, Nat.add_zero]
    decide
  have hpre : OddCount [false, true, false, false, false] = 1 := by
    rw [OddCountFalse, OddCountTrue, htail]
  rw [WordNumerator, ExampleRight, WordNumeratorTrue, WordNumeratorFalse, hpre,
    hmid, Nat.pow_zero]
  decide

/-- The difference factor may vanish while the sum factor does not. -/
theorem EqualHalvesSeparateFactors :
    OddCount ExampleLeft = 2 ∧ OddCount ExampleRight = 2 ∧
      ExampleLeft.length = 6 ∧ ExampleRight.length = 6 ∧
        WordNumerator 3 ExampleLeft = 80 ∧ WordNumerator 3 ExampleRight = 7 ∧
          ((2 ^ 6 + 3 ^ 2 : ℕ) : ℤ) ∣ ((80 : ℤ) - 7) ∧
            ¬ (2 ^ 6 - 3 ^ 2) ∣ 80 + 7 := by
  refine ⟨ExampleLeftOdd, ExampleRightOdd, rfl, rfl, ExampleLeftNum,
    ExampleRightNum, ?_, by decide⟩
  have hsum : (2 ^ 6 + 3 ^ 2 : ℕ) = 73 := by decide
  have hdiff : (80 - 7 : ℕ) = 73 := by decide
  have hcast : ((80 : ℤ) - 7) = ((80 - 7 : ℕ) : ℤ) :=
    (Int.ofNat_sub (by decide : (7 : ℕ) ≤ 80)).symm
  rw [hsum, hcast, hdiff]

/-- This equal-halves word is not a numerator closure: the sum factor fails. -/
theorem EqualHalvesNotClosed :
    ¬ (2 ^ (ExampleLeft ++ ExampleRight).length -
        3 ^ OddCount (ExampleLeft ++ ExampleRight)) ∣
      WordNumerator 3 (ExampleLeft ++ ExampleRight) := by
  intro hdiv
  have hq : (3 : ℕ) % 2 = 1 := by decide
  have hQ : 0 < 2 ^ 6 - 3 ^ 2 := by decide
  have hcrit := EqualHalvesCriterion 3 6 2 ExampleLeft ExampleRight hq hQ rfl rfl
    ExampleLeftOdd ExampleRightOdd
  have hsum := (hcrit.mp hdiv).2
  rw [ExampleLeftNum, ExampleRightNum] at hsum
  exact (by decide : ¬ (2 ^ 6 - 3 ^ 2) ∣ 80 + 7) hsum

end GeneralizedCollatz
