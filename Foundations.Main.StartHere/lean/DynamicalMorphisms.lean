import Mathlib.Data.Nat.Basic

/-!
Target-reflecting semiconjugacies and positive variable clocks.

These are structural recovery theorems. A morphism alone does not reduce the
remaining Collatz obligation; the reduced system must be solved independently.
The variable-clock result transports only the forward capture direction.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- Iteration records the actual number of steps, including the zero-step state. -/
def Iterate {α : Type*} (f : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => f (Iterate f n x)

/-- Splitting a clock retains both intervals in their chronological order. -/
theorem IterateAdd {α : Type*} (f : α → α) (m n : ℕ) (x : α) :
    Iterate f (m + n) x = Iterate f n (Iterate f m x) := by
  induction n with
  | zero => {
      simp [Iterate]
    }
  | succ n ih => {
      simp [Iterate, ih]
    }

/-- A one-step commuting map commutes with every finite trajectory. -/
theorem SemiconjugacyIterates {α β : Type*} (f : α → α) (g : β → β)
    (h : α → β) (commutes : ∀ x, h (f x) = g (h x)) (n : ℕ) (x : α) :
    h (Iterate f n x) = Iterate g n (h x) := by
  induction n with
  | zero => {
      rfl
    }
  | succ n ih => {
      simp only [Iterate]
      rw [commutes, ih]
    }

/-- Capture below a semiconjugacy is reflected at the same time when the target preimage is. -/
theorem ReflectingCapture {α β : Type*} (f : α → α) (g : β → β)
    (h : α → β) (a : α → Prop) (b : β → Prop)
    (commutes : ∀ x, h (f x) = g (h x))
    (reflects : ∀ x, b (h x) → a x) (x : α)
    (captured : ∃ n, b (Iterate g n (h x))) :
    ∃ n, b (Iterate g n (h x)) ∧ a (Iterate f n x) := by
  obtain ⟨n, hn⟩ := captured
  refine ⟨n, hn, reflects _ ?_⟩
  rw [SemiconjugacyIterates f g h commutes]
  exact hn

/-- Sum state-dependent return times along the source trajectory, without assuming constancy. -/
def AccumulatedClock {α : Type*} (f : α → α) (clock : α → ℕ) : ℕ → α → ℕ
  | 0, _ => 0
  | n + 1, x => AccumulatedClock f clock n x + clock (Iterate f n x)

/-- Positive return times prevent a simulated infinite path from stopping its raw clock. -/
theorem AccumulatedClockLower {α : Type*} (f : α → α) (clock : α → ℕ)
    (positive : ∀ x, 1 ≤ clock x) (n : ℕ) (x : α) :
    n ≤ AccumulatedClock f clock n x := by
  induction n with
  | zero => {
      exact Nat.zero_le _
    }
  | succ n ih => {
      exact Nat.add_le_add ih (positive (Iterate f n x))
    }

/-- A state-dependent commuting square transports every return to its exact raw clock time. -/
theorem VariableClockIterates {α β : Type*} (f : α → α) (g : β → β)
    (h : α → β) (clock : α → ℕ)
    (commutes : ∀ x, h (f x) = Iterate g (clock x) (h x)) (n : ℕ) (x : α) :
    h (Iterate f n x) = Iterate g (AccumulatedClock f clock n x) (h x) := by
  induction n with
  | zero => {
      rfl
    }
  | succ n ih => {
      simp only [Iterate, AccumulatedClock]
      rw [commutes, ih, IterateAdd]
    }

/-- Forward target preservation suffices for transport from return-map capture to raw capture. -/
theorem VariableClockCapture {α β : Type*} (f : α → α) (g : β → β)
    (h : α → β) (clock : α → ℕ) (a : α → Prop) (b : β → Prop)
    (commutes : ∀ x, h (f x) = Iterate g (clock x) (h x))
    (preserves : ∀ x, a x → b (h x)) (x : α)
    (captured : ∃ n, a (Iterate f n x)) :
    ∃ k, b (Iterate g k (h x)) := by
  obtain ⟨n, hn⟩ := captured
  refine ⟨AccumulatedClock f clock n x, ?_⟩
  rw [← VariableClockIterates f g h clock commutes]
  exact preserves _ hn

end GeneralizedCollatz
