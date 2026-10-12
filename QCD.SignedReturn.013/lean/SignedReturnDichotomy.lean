-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere
import GeneralizedCollatz
import SignedTraps
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Ring

/-!
# First hits are exactly the untrapped orbits

A seed has a first affine hit if and only if some raw iterate is divisible by
the signed divisor. The forward direction turns the affine guard into a raw
guard and applies the division-free prefix formula. The reverse direction
selects the least raw division time by `Nat.find`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The affine state of multiplier `q`, offset `c`, time `j` and seed `n`. -/
def AffineState (q c : ℤ) (j : ℕ) (n : ℤ) : ℤ :=
  q ^ j * n + c * TrapSum q j

/-- The affine state meets `D` at time `j` and at no earlier time. -/
def IsFirstHit (p : Parameters) (n : ℤ) (j : ℕ) : Prop :=
  p.D ∣ AffineState p.Q p.C j n ∧
    ∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n

/-- A raw prefix with no division before time `j` equals the affine state. -/
theorem PrefixAffine (p : Parameters) (n : ℤ) (j : ℕ)
    (h : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n) :
    Iterate (RawStep p) j n = AffineState p.Q p.C j n := by
  induction j with
  | zero => {
      change n = AffineState p.Q p.C 0 n
      unfold AffineState
      have hsum : TrapSum p.Q 0 = 0 := rfl
      rw [hsum]
      ring
    }
  | succ j ih => {
      have hlt : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self j))
      have hj : ¬ p.D ∣ Iterate (RawStep p) j n :=
        h j (Nat.lt_succ_self j)
      have hstep : Iterate (RawStep p) (j + 1) n =
          RawStep p (Iterate (RawStep p) j n) := rfl
      have haffine : RawStep p (Iterate (RawStep p) j n) =
          p.Q * Iterate (RawStep p) j n + p.C :=
        RawStepAffine p _ hj
      rw [hstep, haffine, ih hlt]
      unfold AffineState
      show p.Q * (p.Q ^ j * n + p.C * TrapSum p.Q j) + p.C =
        p.Q ^ (j + 1) * n + p.C * TrapSum p.Q (j + 1)
      rw [TrapSumRec]
      ring
    }

/-- An affine guard before time `j` is a raw guard before time `j`. -/
theorem RawFreeOfAffineFree (p : Parameters) (n : ℤ) (j : ℕ)
    (h : ∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n) :
    ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n := by
  induction j with
  | zero => {
      intro i hi
      exact absurd hi (Nat.not_lt_zero i)
    }
  | succ j ih => {
      intro i hi
      have hlt : ∀ k < j, ¬ p.D ∣ AffineState p.Q p.C k n := by
        intro k hk
        exact h k (Nat.lt_trans hk (Nat.lt_succ_self j))
      have hraw : ∀ k < j, ¬ p.D ∣ Iterate (RawStep p) k n :=
        ih hlt
      have hle : i ≤ j := Nat.le_of_lt_succ hi
      cases Nat.lt_or_eq_of_le hle with
      | inl hik => {
          exact hraw i hik
        }
      | inr heq => {
          rw [heq]
          have haff : ¬ p.D ∣ AffineState p.Q p.C j n :=
            h j (Nat.lt_succ_self j)
          have heqState : Iterate (RawStep p) j n =
              AffineState p.Q p.C j n :=
            PrefixAffine p n j hraw
          rw [heqState]
          exact haff
        }
    }

/-- Divisibility of each raw iterate by `D` is decidable via the integer test. -/
@[reducible]
def RawDividesDecidable (p : Parameters) (n : ℤ) :
    DecidablePred (fun j : ℕ => p.D ∣ Iterate (RawStep p) j n) :=
  fun j => Int.decidableDvd p.D (Iterate (RawStep p) j n)

/-- A seed has a first hit if and only if its raw orbit is not division-free.
The converse takes the least raw division time by `Nat.find`. The two
hypotheses of that operator are `RawDividesDecidable`, built from
`Int.decidableDvd`, and existence of one raw division, obtained from
`¬ NeverDivides` by `Classical.byContradiction`. `Nat.find_spec` and
`Nat.find_min`, with `PrefixAffine`, make that least time a first hit. -/
theorem ExistsHitIffNotTrapped (p : Parameters) (n : ℤ) :
    (∃ j, IsFirstHit p n j) ↔ ¬ NeverDivides p n := by
  constructor
  · intro hex hnever
    obtain ⟨j, hj⟩ := hex
    have hdvd : p.D ∣ AffineState p.Q p.C j n := hj.left
    have hfree : ∀ i < j, ¬ p.D ∣ AffineState p.Q p.C i n := hj.right
    have hraw : ∀ i < j, ¬ p.D ∣ Iterate (RawStep p) i n :=
      RawFreeOfAffineFree p n j hfree
    have heq : Iterate (RawStep p) j n = AffineState p.Q p.C j n :=
      PrefixAffine p n j hraw
    have hdiv : p.D ∣ Iterate (RawStep p) j n := by
      rw [heq]
      show p.D ∣ AffineState p.Q p.C j n
      exact hdvd
    exact hnever j hdiv
  · intro hnot
    let P : ℕ → Prop := fun j => p.D ∣ Iterate (RawStep p) j n
    have hexists : ∃ j, P j :=
      Classical.byContradiction fun hnone =>
        hnot <| by
          intro j hj
          exact hnone ⟨j, hj⟩
    have hdec : DecidablePred P := RawDividesDecidable p n
    let j0 : ℕ := @Nat.find P hdec hexists
    have hspec : P j0 := @Nat.find_spec P hdec hexists
    have hmin : ∀ i, i < j0 → ¬ P i := by
      intro i hi
      exact @Nat.find_min P hdec hexists i hi
    have hraw : ∀ i, i < j0 → ¬ p.D ∣ Iterate (RawStep p) i n := by
      intro i hi
      exact hmin i hi
    have heq : Iterate (RawStep p) j0 n = AffineState p.Q p.C j0 n :=
      PrefixAffine p n j0 hraw
    refine ⟨j0, ?_⟩
    show IsFirstHit p n j0
    unfold IsFirstHit
    refine ⟨?_, ?_⟩
    · rw [← heq]
      exact hspec
    · intro i hi
      have hpre : ∀ k < i, ¬ p.D ∣ Iterate (RawStep p) k n := by
        intro k hk
        exact hraw k (Nat.lt_trans hk hi)
      have heqi : Iterate (RawStep p) i n = AffineState p.Q p.C i n :=
        PrefixAffine p n i hpre
      rw [← heqi]
      exact hraw i hi

end GeneralizedCollatz
