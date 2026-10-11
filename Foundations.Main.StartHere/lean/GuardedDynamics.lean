import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

/-!
Guarded raw integer dynamics and chronological word execution.

The signed divisor is retained. `Parameters` does not assert positivity of the
state or the affine branch. A legal word is a partial computation, not an
arbitrary affine relaxation.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Raw integer parameters, including signed division and the zero state. -/
structure Parameters where
  Q : ℤ
  C : ℤ
  D : ℤ
  DAdmissible : 2 ≤ D.natAbs

/-- The division parameter in the declared domain cannot be zero. -/
theorem Parameters.DNonzero (p : Parameters) : p.D ≠ 0 := by
  intro h
  have hd := p.DAdmissible
  simp [h] at hd

/-- A raw branch letter includes its arithmetic guard in its execution semantics. -/
inductive RawLetter where
  | Affine
  | Divide
  deriving DecidableEq

/-- Total signed raw dynamics, using exact division only on a divisible state. -/
def RawStep (p : Parameters) (n : ℤ) : ℤ :=
  if p.D ∣ n then n / p.D else p.Q * n + p.C

/-- Partial maps use `none` for an illegal input and therefore forget no guard. -/
abbrev PartialMap (α β : Type*) := α → Option β

/-- Execute the first partial map and then the second, preserving undefinedness. -/
def PartialThen {α β γ : Type*} (f : PartialMap α β) (g : PartialMap β γ) :
    PartialMap α γ :=
  fun x => (f x).bind g

/-- An empty computation is defined at every input and changes no state. -/
def PartialIdentity (α : Type*) : PartialMap α α := some

/-- Partial-map composition is associative, including illegal intermediate states. -/
theorem PartialThenAssociative {α β γ δ : Type*}
    (f : PartialMap α β) (g : PartialMap β γ) (h : PartialMap γ δ) :
    PartialThen (PartialThen f g) h = PartialThen f (PartialThen g h) := by
  funext x
  cases hf : f x with
  | none => {
      simp [PartialThen, hf]
    }
  | some y => {
      cases hg : g y with
      | none => {
          simp [PartialThen, hf, hg]
        }
      | some z => {
          simp [PartialThen, hf, hg]
        }
    }

/-- The empty computation is a left identity for partial composition. -/
theorem PartialIdentityThen {α β : Type*} (f : PartialMap α β) :
    PartialThen (PartialIdentity α) f = f := by
  funext x
  rfl

/-- The empty computation is a right identity even at illegal inputs. -/
theorem PartialThenIdentity {α β : Type*} (f : PartialMap α β) :
    PartialThen f (PartialIdentity β) = f := by
  funext x
  cases hf : f x with
  | none => {
      simp [PartialThen, PartialIdentity, hf]
    }
  | some y => {
      simp [PartialThen, PartialIdentity, hf]
    }

/-- Each letter is legal exactly on the corresponding raw branch domain. -/
def ExecuteLetter (p : Parameters) : RawLetter → PartialMap ℤ ℤ
  | .Affine => fun n => if p.D ∣ n then none else some (p.Q * n + p.C)
  | .Divide => fun n => if p.D ∣ n then some (n / p.D) else none

/-- Word order is chronological: the head letter is executed first. -/
def ExecuteWord (p : Parameters) : List RawLetter → PartialMap ℤ ℤ
  | [] => PartialIdentity ℤ
  | letter :: word => PartialThen (ExecuteLetter p letter) (ExecuteWord p word)

/-- Concatenation has the exact guarded composition law, not merely an affine identity. -/
theorem ExecuteAppend (p : Parameters) (u v : List RawLetter) :
    ExecuteWord p (u ++ v) = PartialThen (ExecuteWord p u) (ExecuteWord p v) := by
  induction u with
  | nil => {
      simp [ExecuteWord, PartialIdentityThen]
    }
  | cons letter u ih => {
      simp only [List.cons_append, ExecuteWord, ih]
      exact (PartialThenAssociative _ _ _).symm
    }

/-- A successful concatenation has one common, legal intermediate witness. -/
theorem ExecuteAppendWitness (p : Parameters) (u v : List RawLetter) (n m : ℤ) :
    ExecuteWord p (u ++ v) n = some m ↔
      ∃ k, ExecuteWord p u n = some k ∧ ExecuteWord p v k = some m := by
  rw [ExecuteAppend]
  simp only [PartialThen]
  cases ExecuteWord p u n with
  | none => {
      simp
    }
  | some k => {
      simp
    }

/-- A divisible input has precisely the guarded division output. -/
theorem ExecuteDivision (p : Parameters) (n : ℤ) (h : p.D ∣ n) :
    ExecuteLetter p .Divide n = some (RawStep p n) := by
  simp [ExecuteLetter, RawStep, h]

/-- A nondivisible input has precisely the guarded affine output. -/
theorem ExecuteAffine (p : Parameters) (n : ℤ) (h : ¬p.D ∣ n) :
    ExecuteLetter p .Affine n = some (RawStep p n) := by
  simp [ExecuteLetter, RawStep, h]

/-- A legal division satisfies the original integer equation without rounding. -/
theorem DivisionRecoversInput (p : Parameters) (n : ℤ) (h : p.D ∣ n) :
    n / p.D * p.D = n := by
  exact Int.ediv_mul_cancel h

end GeneralizedCollatz
