import DynamicalMorphisms
import GuardedDynamics

/-!
Exact recovery between guarded raw words and finite raw orbits.

A rational affine presentation does not carry these conclusions on its own.
Successful guarded execution determines both the itinerary and the raw clock.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Moving the first step into the input preserves the actual iteration count. -/
theorem IterateFirst {α : Type*} (f : α → α) (k : ℕ) (x : α) :
    Iterate f k (f x) = Iterate f (k + 1) x := by
  have h := IterateAdd f 1 k x
  simpa [Iterate, Nat.add_comm] using h.symm

/-- A successful guarded instruction is exactly one step of the original raw map. -/
theorem ExecuteLetterRaw (p : Parameters) (letter : RawLetter) (n m : ℤ)
    (legal : ExecuteLetter p letter n = some m) : m = RawStep p n := by
  cases letter with
  | Affine => {
      by_cases hd : p.D ∣ n
      · simp [ExecuteLetter, hd] at legal
      · have hm : p.Q * n + p.C = m := by
          simpa [ExecuteLetter, hd] using legal
        simpa [RawStep, hd] using hm.symm
    }
  | Divide => {
      by_cases hd : p.D ∣ n
      · have hm : n / p.D = m := by
          simpa [ExecuteLetter, hd] using legal
        simpa [RawStep, hd] using hm.symm
      · simp [ExecuteLetter, hd] at legal
    }

/-- A legal word recovers its exact raw endpoint after its full number of letters. -/
theorem ExecuteWordRaw (p : Parameters) (word : List RawLetter) (n m : ℤ)
    (legal : ExecuteWord p word n = some m) :
    m = Iterate (RawStep p) word.length n := by
  induction word generalizing n m with
  | nil => {
      simpa [ExecuteWord, PartialIdentity, Iterate] using legal.symm
    }
  | cons letter word ih => {
      cases hl : ExecuteLetter p letter n with
      | none => {
          simp [ExecuteWord, PartialThen, hl] at legal
        }
      | some k => {
          have tail : ExecuteWord p word k = some m := by
            simpa [ExecuteWord, PartialThen, hl] using legal
          have hk := ExecuteLetterRaw p letter n k hl
          rw [List.length_cons, ← IterateFirst, ← hk]
          exact ih k m tail
        }
    }

/-- Choose the only raw instruction allowed by division precedence at the current state. -/
def RawChoice (p : Parameters) (n : ℤ) : RawLetter :=
  if p.D ∣ n then .Divide else .Affine

/-- The chosen instruction is legal, including at zero and for a negative divisor. -/
theorem RawChoiceExecutes (p : Parameters) (n : ℤ) :
    ExecuteLetter p (RawChoice p n) n = some (RawStep p n) := by
  by_cases hd : p.D ∣ n
  · simp [RawChoice, ExecuteLetter, RawStep, hd]
  · simp [RawChoice, ExecuteLetter, RawStep, hd]

/-- The deterministic trace retains every intermediate guard and every raw step. -/
def RawTrace (p : Parameters) : ℕ → ℤ → List RawLetter
  | 0, _ => []
  | k + 1, n => RawChoice p n :: RawTrace p k (RawStep p n)

/-- The generated trace neither compresses nor inserts raw clock steps. -/
theorem RawTraceLength (p : Parameters) (k : ℕ) (n : ℤ) :
    (RawTrace p k n).length = k := by
  induction k generalizing n with
  | zero => {
      rfl
    }
  | succ k ih => {
      simp [RawTrace, ih]
    }

/-- Every finite raw orbit has a legal word whose endpoint is the original orbit endpoint. -/
theorem RawTraceExecutes (p : Parameters) (k : ℕ) (n : ℤ) :
    ExecuteWord p (RawTrace p k n) n = some (Iterate (RawStep p) k n) := by
  induction k generalizing n with
  | zero => {
      rfl
    }
  | succ k ih => {
      simp only [RawTrace, ExecuteWord, PartialThen, RawChoiceExecutes, Option.bind_some]
      rw [ih, IterateFirst]
    }

/-- Guard legality determines the instruction, unlike the relaxed affine value alone. -/
theorem ExecuteLetterChoice (p : Parameters) (letter : RawLetter) (n m : ℤ)
    (legal : ExecuteLetter p letter n = some m) : letter = RawChoice p n := by
  cases letter with
  | Affine => {
      by_cases hd : p.D ∣ n
      · simp [ExecuteLetter, hd] at legal
      · simp [RawChoice, hd]
    }
  | Divide => {
      by_cases hd : p.D ∣ n
      · simp [RawChoice, hd]
      · simp [ExecuteLetter, hd] at legal
    }

/-- A successfully executed word is the actual raw itinerary, not just one endpoint witness. -/
theorem ExecuteWordTrace (p : Parameters) (word : List RawLetter) (n m : ℤ)
    (legal : ExecuteWord p word n = some m) :
    word = RawTrace p word.length n := by
  induction word generalizing n m with
  | nil => {
      rfl
    }
  | cons letter word ih => {
      cases hl : ExecuteLetter p letter n with
      | none => {
          simp [ExecuteWord, PartialThen, hl] at legal
        }
      | some k => {
          have tail : ExecuteWord p word k = some m := by
            simpa [ExecuteWord, PartialThen, hl] using legal
          have hk := ExecuteLetterRaw p letter n k hl
          have hc := ExecuteLetterChoice p letter n k hl
          simp only [List.length_cons, RawTrace]
          rw [← hc, ← hk, ← ih k m tail]
        }
    }

end GeneralizedCollatz
