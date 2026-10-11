import GuardedDynamics
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Integer numerator data for rational affine words, with chronological composition.

These formulas retain denominators and offsets but deliberately do not certify
raw branch legality. In the exponent-word convention the full offset is `c * B`;
first-division words instead have a full offset already containing `c`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- An integer affine presentation carries an explicit nonzero denominator. -/
@[ext]
structure AffineData where
  P : ℤ
  B : ℤ
  Q : ℤ
  QNonzero : Q ≠ 0

/-- Evaluate the rational relaxation, without asserting that an integer branch is legal. -/
def RationalAction (a : AffineData) (x : ℚ) : ℚ :=
  ((a.P : ℚ) * x + (a.B : ℚ)) / (a.Q : ℚ)

/-- Integer data for executing `first` and then `second`. -/
def AffineThen (first second : AffineData) : AffineData where
  P := second.P * first.P
  B := second.P * first.B + second.B * first.Q
  Q := second.Q * first.Q
  QNonzero := mul_ne_zero second.QNonzero first.QNonzero

/-- Chronological affine composition gives precisely the composed rational function. -/
theorem RationalActionThen (first second : AffineData) (x : ℚ) :
    RationalAction (AffineThen first second) x =
      RationalAction second (RationalAction first x) := by
  have hf : (first.Q : ℚ) ≠ 0 := by
    exact_mod_cast first.QNonzero
  have hs : (second.Q : ℚ) ≠ 0 := by
    exact_mod_cast second.QNonzero
  simp only [RationalAction, AffineThen, Int.cast_mul, Int.cast_add]
  field_simp
  ring

/-- Integer presentation composition is associative, before any normalization or cancellation. -/
theorem AffineThenAssociative (a b c : AffineData) :
    AffineThen (AffineThen a b) c = AffineThen a (AffineThen b c) := by
  ext <;> simp only [AffineThen] <;> ring

/-- The empty word is represented by the identity numerator and denominator. -/
def EmptyAffine : AffineData where
  P := 1
  B := 0
  Q := 1
  QNonzero := one_ne_zero

/-- The empty affine presentation is a left identity, including its offset and denominator. -/
theorem EmptyAffineThen (a : AffineData) : AffineThen EmptyAffine a = a := by
  ext <;> simp [AffineThen, EmptyAffine]

/-- The empty affine presentation is a right identity, including unreduced integer data. -/
theorem AffineThenEmpty (a : AffineData) : AffineThen a EmptyAffine = a := by
  ext <;> simp [AffineThen, EmptyAffine]

/-- One exponent letter presents `(q*x+c)/base^a`; zero letters remain algebraically legal. -/
def ExponentLetter (q c base : ℤ) (hbase : base ≠ 0) (a : ℕ) : AffineData where
  P := q
  B := c
  Q := base ^ a
  QNonzero := pow_ne_zero a hbase

/-- A chronological exponent word is a rational relaxation, not an itinerary certificate. -/
def ExponentWord (q c base : ℤ) (hbase : base ≠ 0) : List ℕ → AffineData
  | [] => EmptyAffine
  | a :: word => AffineThen (ExponentLetter q c base hbase a)
      (ExponentWord q c base hbase word)

/-- Appending words executes the first word and then the second with all numerator data intact. -/
theorem ExponentWordAppend (q c base : ℤ) (hbase : base ≠ 0) (u v : List ℕ) :
    ExponentWord q c base hbase (u ++ v) =
      AffineThen (ExponentWord q c base hbase u) (ExponentWord q c base hbase v) := by
  induction u with
  | nil => {
      simp [ExponentWord, EmptyAffineThen]
    }
  | cons a u ih => {
      simp only [List.cons_append, ExponentWord, ih]
      exact (AffineThenAssociative _ _ _).symm
    }

/-- The word multiplier is `q^length`, independently of the offset and exponents. -/
theorem ExponentWordMultiplier (q c base : ℤ) (hbase : base ≠ 0) (word : List ℕ) :
    (ExponentWord q c base hbase word).P = q ^ word.length := by
  induction word with
  | nil => {
      simp [ExponentWord, EmptyAffine]
    }
  | cons a word ih => {
      simp [ExponentWord, AffineThen, ExponentLetter, ih, pow_succ]
    }

/-- The unreduced word denominator is `base^(sum exponents)`, including the empty word. -/
theorem ExponentWordDenominator (q c base : ℤ) (hbase : base ≠ 0) (word : List ℕ) :
    (ExponentWord q c base hbase word).Q = base ^ word.sum := by
  induction word with
  | nil => {
      simp [ExponentWord, EmptyAffine]
    }
  | cons a word ih => {
      simp [ExponentWord, AffineThen, ExponentLetter, ih, pow_add, mul_comm]
    }

/-- The determinant is the denominator minus the multiplier; neutral words need no division. -/
def Determinant (a : AffineData) : ℤ := a.Q - a.P

/-- Fixed-point closure is the exact scalar equation, including the neutral determinant case. -/
theorem RationalFixedPointEquation (a : AffineData) (x : ℚ) :
    RationalAction a x = x ↔ (Determinant a : ℚ) * x = (a.B : ℚ) := by
  have hq : (a.Q : ℚ) ≠ 0 := by
    exact_mod_cast a.QNonzero
  rw [RationalAction, div_eq_iff hq]
  simp only [Determinant, Int.cast_sub]
  constructor
  · intro h
    calc
      ((a.Q : ℚ) - (a.P : ℚ)) * x = x * (a.Q : ℚ) - (a.P : ℚ) * x := by
        ring
      _ = a.B := by
        rw [← h]
        ring
  · intro h
    calc
      (a.P : ℚ) * x + (a.B : ℚ) = (a.P : ℚ) * x +
          ((a.Q : ℚ) - (a.P : ℚ)) * x := by rw [h]
      _ = x * (a.Q : ℚ) := by ring

/-- A nonneutral relaxation has one fixed point; this does not prove guarded integer closure. -/
theorem RationalFixedPointUnique (a : AffineData) (h : Determinant a ≠ 0) (x : ℚ) :
    RationalAction a x = x ↔ x = (a.B : ℚ) / (Determinant a : ℚ) := by
  have hd : (Determinant a : ℚ) ≠ 0 := by
    exact_mod_cast h
  rw [RationalFixedPointEquation, eq_div_iff hd]
  exact ⟨fun hx => by simpa [mul_comm] using hx,
    fun hx => by simpa [mul_comm] using hx⟩

/-- An unscaled exponent-word offset keeps the additive parameter separate. -/
def ExponentOffset (q base : ℤ) : List ℕ → ℤ
  | [] => 0
  | a :: word => q ^ word.length + base ^ a * ExponentOffset q base word

/-- The full affine offset is `c * B`, preventing a generalized-offset omission. -/
theorem ExponentWordOffset (q c base : ℤ) (hbase : base ≠ 0) (word : List ℕ) :
    (ExponentWord q c base hbase word).B = c * ExponentOffset q base word := by
  induction word with
  | nil => {
      simp [ExponentWord, EmptyAffine, ExponentOffset]
    }
  | cons a word ih => {
      simp only [ExponentWord, AffineThen, ExponentLetter, ExponentOffset]
      rw [ExponentWordMultiplier, ih]
      ring
    }

/-- The rational presentation of one raw instruction intentionally omits its guard. -/
def RawLetterAffine (p : Parameters) : RawLetter → AffineData
  | .Affine => { P := p.Q, B := p.C, Q := 1, QNonzero := one_ne_zero }
  | .Divide => { P := 1, B := 0, Q := p.D, QNonzero := p.DNonzero }

/-- The affine presentation follows the same chronological recursion as guarded execution. -/
def RawWordAffine (p : Parameters) : List RawLetter → AffineData
  | [] => EmptyAffine
  | letter :: word => AffineThen (RawLetterAffine p letter) (RawWordAffine p word)

/-- Legal raw instructions agree with their rational presentations for both divisor signs. -/
theorem ExecuteLetterAffine (p : Parameters) (letter : RawLetter) (n m : ℤ)
    (legal : ExecuteLetter p letter n = some m) :
    RationalAction (RawLetterAffine p letter) (n : ℚ) = (m : ℚ) := by
  cases letter with
  | Affine => {
      by_cases hd : p.D ∣ n
      · simp [ExecuteLetter, hd] at legal
      · have hm : p.Q * n + p.C = m := by
          simpa [ExecuteLetter, hd] using legal
        simpa [RationalAction, RawLetterAffine] using
          congrArg (fun z : ℤ => (z : ℚ)) hm
    }
  | Divide => {
      by_cases hd : p.D ∣ n
      · have hm : n / p.D = m := by
          simpa [ExecuteLetter, hd] using legal
        have heq : m * p.D = n := by
          rw [← hm]
          exact DivisionRecoversInput p n hd
        have hq : (p.D : ℚ) ≠ 0 := by
          exact_mod_cast p.DNonzero
        change (1 * (n : ℚ) + 0) / (p.D : ℚ) = (m : ℚ)
        simp only [one_mul, add_zero]
        apply (div_eq_iff hq).2
        exact_mod_cast heq.symm
      · simp [ExecuteLetter, hd] at legal
    }

/-- Legal intermediate states reconstruct the whole word's affine value without dropping guards. -/
theorem ExecuteWordAffine (p : Parameters) (word : List RawLetter) (n m : ℤ)
    (legal : ExecuteWord p word n = some m) :
    RationalAction (RawWordAffine p word) (n : ℚ) = (m : ℚ) := by
  induction word generalizing n m with
  | nil => {
      have hm : n = m := by
        simpa [ExecuteWord, PartialIdentity] using legal
      simp [RawWordAffine, EmptyAffine, RationalAction, hm]
    }
  | cons letter word ih => {
      cases hl : ExecuteLetter p letter n with
      | none => {
          simp [ExecuteWord, PartialThen, hl] at legal
        }
      | some k => {
          have tail : ExecuteWord p word k = some m := by
            simpa [ExecuteWord, PartialThen, hl] using legal
          rw [RawWordAffine, RationalActionThen, ExecuteLetterAffine p letter n k hl]
          exact ih k m tail
        }
    }

/-- A guarded closed integer word satisfies the full determinant equation, including zero. -/
theorem GuardedWordClosure (p : Parameters) (word : List RawLetter) (n : ℤ)
    (legal : ExecuteWord p word n = some n) :
    Determinant (RawWordAffine p word) * n = (RawWordAffine p word).B := by
  have hr := ExecuteWordAffine p word n n legal
  have heq := (RationalFixedPointEquation (RawWordAffine p word) (n : ℚ)).mp hr
  exact_mod_cast heq

/-- Integral cycle closure forces determinant divisibility, but does not supply branch legality. -/
theorem GuardedWordDivisibility (p : Parameters) (word : List RawLetter) (n : ℤ)
    (legal : ExecuteWord p word n = some n) :
    Determinant (RawWordAffine p word) ∣ (RawWordAffine p word).B := by
  exact ⟨n, (GuardedWordClosure p word n legal).symm⟩

/-- A legal neutral closed word must have zero offset; division by its determinant is forbidden. -/
theorem GuardedNeutralClosure (p : Parameters) (word : List RawLetter) (n : ℤ)
    (legal : ExecuteWord p word n = some n)
    (neutral : Determinant (RawWordAffine p word) = 0) :
    (RawWordAffine p word).B = 0 := by
  have heq := GuardedWordClosure p word n legal
  rw [neutral, zero_mul] at heq
  exact heq.symm

end GeneralizedCollatz
