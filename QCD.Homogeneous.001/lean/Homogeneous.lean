import GeneralizedCollatz
import Mathlib.Order.Filter.Cofinite

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Parameters for the positive homogeneous raw map. -/
def HomogeneousParameters (q D : ℕ) (DAdmissible : 2 ≤ D) : Parameters where
  Q := q
  C := 0
  D := D
  DAdmissible := by simpa using DAdmissible

/-- The affine-letter count of a raw word. -/
def HomogeneousAffineCount (word : List RawLetter) : ℕ := word.count .Affine

/-- The division-letter count of a raw word. -/
def HomogeneousDivisionCount (word : List RawLetter) : ℕ := word.count .Divide

/-- The two homogeneous instruction counts partition a raw word. -/
theorem HomogeneousCountTotal (word : List RawLetter) :
    HomogeneousAffineCount word + HomogeneousDivisionCount word = word.length := by
  induction word with
  | nil => { simp [HomogeneousAffineCount, HomogeneousDivisionCount] }
  | cons letter word ih =>
    {
      cases letter <;>
        simp [HomogeneousAffineCount, HomogeneousDivisionCount] at ih ⊢ <;>
        omega
    }

/-- Homogeneous raw words have zero offset and monomial numerator data. -/
theorem HomogeneousWordData (q D : ℕ) (DAdmissible : 2 ≤ D) (word : List RawLetter) :
    let p := HomogeneousParameters q D DAdmissible
    (RawWordAffine p word).P = (q : ℤ) ^ HomogeneousAffineCount word ∧
      (RawWordAffine p word).B = 0 ∧
      (RawWordAffine p word).Q = (D : ℤ) ^ HomogeneousDivisionCount word := by
  let p := HomogeneousParameters q D DAdmissible
  change (RawWordAffine p word).P = (q : ℤ) ^ HomogeneousAffineCount word ∧
    (RawWordAffine p word).B = 0 ∧
    (RawWordAffine p word).Q = (D : ℤ) ^ HomogeneousDivisionCount word
  have pQ : p.Q = (q : ℤ) := rfl
  have pC : p.C = 0 := rfl
  have pD : p.D = (D : ℤ) := rfl
  induction word with
  | nil =>
    {
      simp [RawWordAffine, EmptyAffine, HomogeneousAffineCount,
        HomogeneousDivisionCount]
    }
  | cons letter word ih =>
    {
      rcases ih with ⟨multiplier, offset, denominator⟩
      cases letter <;>
        simp [RawWordAffine, RawLetterAffine, AffineThen, HomogeneousAffineCount,
          HomogeneousDivisionCount, pQ, pC, pD, multiplier, offset, denominator,
          pow_succ', mul_comm]
    }

/-- Positive powers witness multiplicative dependence of the coefficients. -/
def MultiplicativelyIndependent (q D : ℕ) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → q ^ a ≠ D ^ b

/-- Multiplicatively independent homogeneous coefficients admit no nonempty
positive closed word. -/
theorem HomogeneousNoClosedWord (q D : ℕ) (qLower : 2 ≤ q) (DLower : 2 ≤ D)
    (independent : MultiplicativelyIndependent q D) (n : ℤ) (nPositive : 0 < n)
    (word : List RawLetter) (wordNonempty : word ≠ [])
    (legal : ExecuteWord (HomogeneousParameters q D DLower) word n = some n) : False := by
  let a := HomogeneousAffineCount word
  let b := HomogeneousDivisionCount word
  have data := HomogeneousWordData q D DLower word
  change (RawWordAffine (HomogeneousParameters q D DLower) word).P = (q : ℤ) ^ a ∧
    (RawWordAffine (HomogeneousParameters q D DLower) word).B = 0 ∧
    (RawWordAffine (HomogeneousParameters q D DLower) word).Q = (D : ℤ) ^ b at data
  rcases data with ⟨multiplier, offset, denominator⟩
  have closure := GuardedWordClosure (HomogeneousParameters q D DLower) word n legal
  rw [offset] at closure
  simp only [Determinant, multiplier, denominator] at closure
  have nNonzero : n ≠ 0 := ne_of_gt nPositive
  have determinant : (D : ℤ) ^ b - (q : ℤ) ^ a = 0 :=
    (Int.mul_eq_zero.mp closure).resolve_right nNonzero
  have castEquality : (D : ℤ) ^ b = (q : ℤ) ^ a := sub_eq_zero.mp determinant
  have powerEquality : D ^ b = q ^ a := by
    exact_mod_cast castEquality
  have total : a + b = word.length := HomogeneousCountTotal word
  have lengthPositive : 0 < word.length := List.length_pos_iff.mpr wordNonempty
  have aPositive : 0 < a := by
    by_contra notPositive
    have aZero : a = 0 := Nat.eq_zero_of_not_pos notPositive
    have bPositive : 0 < b := by omega
    have powerOne : D ^ b = 1 := by simpa [aZero] using powerEquality
    have powerLarge : 1 < D ^ b := Nat.one_lt_pow bPositive.ne' (by omega)
    omega
  have bPositive : 0 < b := by
    by_contra notPositive
    have bZero : b = 0 := Nat.eq_zero_of_not_pos notPositive
    have aPositive' : 0 < a := by omega
    have powerOne : q ^ a = 1 := by simpa [bZero] using powerEquality.symm
    have powerLarge : 1 < q ^ a := Nat.one_lt_pow aPositive'.ne' (by omega)
    omega
  exact independent a b aPositive bPositive powerEquality.symm

/-- Positive homogeneous dynamics written directly on natural-number states. -/
def PositiveHomogeneousStep (q D n : ℕ) : ℕ :=
  if D ∣ n then n / D else q * n

/-- The natural positive map is exactly the foundational signed raw map on natural casts. -/
theorem PositiveHomogeneousStepCast (q D n : ℕ) (DLower : 2 ≤ D) :
    (PositiveHomogeneousStep q D n : ℤ) =
      RawStep (HomogeneousParameters q D DLower) (n : ℤ) := by
  by_cases divides : D ∣ n
  · have castDivides : (D : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr divides
    simp [PositiveHomogeneousStep, RawStep, HomogeneousParameters, divides,
      castDivides, Int.natCast_ediv]
  · have castDoesNotDivide : ¬(D : ℤ) ∣ (n : ℤ) := by
      simpa only [Int.natCast_dvd_natCast] using divides
    simp [PositiveHomogeneousStep, RawStep, HomogeneousParameters, divides,
      castDoesNotDivide]

/-- Every positive state remains positive under one homogeneous raw instruction. -/
theorem PositiveHomogeneousStepPositive (q D n : ℕ) (qLower : 2 ≤ q)
    (DLower : 2 ≤ D) (nPositive : 0 < n) : 0 < PositiveHomogeneousStep q D n := by
  simp only [PositiveHomogeneousStep]
  split
  next divides =>
    exact Nat.div_pos (Nat.le_of_dvd nPositive divides) (by omega)
  next doesNotDivide =>
    exact Nat.mul_pos (by omega) nPositive

/-- Every finite positive homogeneous orbit remains in the positive states. -/
theorem PositiveHomogeneousIteratePositive (q D n k : ℕ) (qLower : 2 ≤ q)
    (DLower : 2 ≤ D) (nPositive : 0 < n) :
    0 < Iterate (PositiveHomogeneousStep q D) k n := by
  induction k with
  | zero => { simpa [Iterate] using nPositive }
  | succ k ih =>
    {
      simp only [Iterate]
      exact PositiveHomogeneousStepPositive q D _ qLower DLower ih
    }

/-- Natural iteration and foundational signed raw iteration agree at every raw time. -/
theorem PositiveHomogeneousIterateCast (q D n k : ℕ) (DLower : 2 ≤ D) :
    ((Iterate (PositiveHomogeneousStep q D) k n : ℕ) : ℤ) =
      Iterate (RawStep (HomogeneousParameters q D DLower)) k (n : ℤ) := by
  exact SemiconjugacyIterates (PositiveHomogeneousStep q D)
    (RawStep (HomogeneousParameters q D DLower)) (fun x : ℕ => (x : ℤ))
    (fun x => PositiveHomogeneousStepCast q D x DLower) k n

/-- No positive homogeneous orbit can return at a nonzero time under independence. -/
theorem PositiveHomogeneousNoReturn (q D n k : ℕ) (qLower : 2 ≤ q)
    (DLower : 2 ≤ D) (independent : MultiplicativelyIndependent q D)
    (nPositive : 0 < n) (kPositive : 0 < k) :
    Iterate (PositiveHomogeneousStep q D) k n ≠ n := by
  intro returns
  let p := HomogeneousParameters q D DLower
  let word := RawTrace p k (n : ℤ)
  have wordLength : word.length = k := RawTraceLength p k (n : ℤ)
  have wordNonempty : word ≠ [] := by
    intro empty
    rw [empty] at wordLength
    simp at wordLength
    omega
  have rawReturn : Iterate (RawStep p) k (n : ℤ) = (n : ℤ) := by
    rw [← PositiveHomogeneousIterateCast q D n k DLower, returns]
  have legal : ExecuteWord p word (n : ℤ) = some (n : ℤ) := by
    rw [show word = RawTrace p k (n : ℤ) by rfl]
    simpa [rawReturn] using RawTraceExecutes p k (n : ℤ)
  exact HomogeneousNoClosedWord q D qLower DLower independent (n : ℤ)
    (by exact_mod_cast nPositive) word wordNonempty legal

/-- Multiplicative independence makes each positive homogeneous orbit injective in raw time. -/
theorem PositiveHomogeneousOrbitInjective (q D n : ℕ) (qLower : 2 ≤ q)
    (DLower : 2 ≤ D) (independent : MultiplicativelyIndependent q D)
    (nPositive : 0 < n) :
    Function.Injective (fun k => Iterate (PositiveHomogeneousStep q D) k n) := by
  let f := PositiveHomogeneousStep q D
  have collisionImpossible : ∀ {i j : ℕ}, i < j →
      Iterate f i n = Iterate f j n → False := by
    intro i j earlier collision
    let gap := j - i
    have gapPositive : 0 < gap := Nat.sub_pos_of_lt earlier
    have splitTime : Iterate f j n = Iterate f gap (Iterate f i n) := by
      rw [show j = i + gap by omega]
      exact IterateAdd f i gap n
    have returnAtIntermediate : Iterate f gap (Iterate f i n) = Iterate f i n := by
      rw [← splitTime, ← collision]
    have intermediatePositive : 0 < Iterate f i n := by
      exact PositiveHomogeneousIteratePositive q D n i qLower DLower nPositive
    exact PositiveHomogeneousNoReturn q D (Iterate f i n) gap qLower DLower
      independent intermediatePositive gapPositive returnAtIntermediate
  intro i j collision
  by_contra distinct
  rcases lt_or_gt_of_ne distinct with earlier | later
  · exact collisionImpossible earlier collision
  · exact collisionImpossible later collision.symm

/-- Every positive homogeneous orbit escapes to infinity under multiplicative independence. -/
theorem PositiveHomogeneousIndependentEscape (q D n : ℕ) (qLower : 2 ≤ q)
    (DLower : 2 ≤ D) (independent : MultiplicativelyIndependent q D)
    (nPositive : 0 < n) :
    Filter.Tendsto (fun k => Iterate (PositiveHomogeneousStep q D) k n)
      Filter.atTop Filter.atTop := by
  exact Function.Injective.nat_tendsto_atTop
    (PositiveHomogeneousOrbitInjective q D n qLower DLower independent nPositive)

end GeneralizedCollatz
