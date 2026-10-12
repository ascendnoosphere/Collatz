-- SPDX-License-Identifier: CC-BY-4.0

import GeneralizedCollatz

/-!
The odd burst along the Collatz shortcut, starting at `2 ^ a - 1`.

The shortcut halves an even input and sends an odd input to `(3 * n + 1) / 2`.
For every `k ≤ a`, the `k`-th shortcut iterate of `2 ^ a - 1` equals
`3 ^ k * 2 ^ (a - k) - 1`. The case `k = a` is `3 ^ a - 1`. Each of the `a`
inputs is odd, so each of those steps is the odd branch. The arrival value is
even. For `a ≥ 2` it is strictly larger than the seed.

Nothing proved here asserts that an iterate equals `1`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- One odd branch `(3 * n + 1) / 2` of the Collatz shortcut. -/
def OddBurstStep (n : ℕ) : ℕ :=
  (3 * n + 1) / 2

/-- Collatz shortcut: halve an even input, and use the odd branch otherwise. -/
def BurstShortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The monomial `3 ^ k * 2 ^ (a - k)` one above the closed orbit term. -/
def BurstMonomial (a k : ℕ) : ℕ :=
  3 ^ k * 2 ^ (a - k)

/-- The closed term `3 ^ k * 2 ^ (a - k) - 1`. -/
def BurstTerm (a k : ℕ) : ℕ :=
  BurstMonomial a k - 1

/-- Below the terminal index, the power of two contributes one explicit factor. -/
theorem BurstPowSplit (a k : ℕ) (hk : k < a) :
    2 ^ (a - k) = 2 * 2 ^ (a - (k + 1)) := by
  have hsucc : a - k = a - (k + 1) + 1 := by omega
  rw [hsucc, Nat.pow_add_one, Nat.mul_comm]

/-- For `k < a`, the monomial is twice the monomial with one fewer factor of two. -/
theorem BurstMonomialEven (a k : ℕ) (hk : k < a) :
    BurstMonomial a k = 2 * (3 ^ k * 2 ^ (a - (k + 1))) := by
  unfold BurstMonomial
  rw [BurstPowSplit a k hk, ← Nat.mul_assoc, Nat.mul_comm (3 ^ k) 2,
    Nat.mul_assoc]

/-- Adding one restores the monomial, so the closed subtraction does not truncate. -/
theorem BurstTermSucc (a k : ℕ) :
    BurstTerm a k + 1 = BurstMonomial a k := by
  unfold BurstTerm BurstMonomial
  have hpos : 1 ≤ 3 ^ k * 2 ^ (a - k) := by
    have hmul := Nat.mul_le_mul
      (Nat.one_le_pow k 3 (by decide))
      (Nat.one_le_pow (a - k) 2 (by decide))
    simpa using hmul
  exact Nat.sub_add_cancel hpos

/-- Each closed term before the terminal index is odd. -/
theorem BurstTermOdd (a k : ℕ) (hk : k < a) : BurstTerm a k % 2 = 1 := by
  -- The successor of the term is divisible by two, so the term is odd.
  have hterm : BurstTerm a k + 1 =
      2 * (3 ^ k * 2 ^ (a - (k + 1))) := by
    rw [BurstTermSucc a k, BurstMonomialEven a k hk]
  have hmod : (BurstTerm a k + 1) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd
      ⟨3 ^ k * 2 ^ (a - (k + 1)), hterm⟩
  cases Nat.mod_two_eq_zero_or_one (BurstTerm a k) with
  | inl heven => {
      have hcalc : (BurstTerm a k + 1) % 2 = 1 := by
        rw [Nat.add_mod, heven]
      rw [hmod] at hcalc
      exact absurd hcalc Nat.zero_ne_one
    }
  | inr hodd => {
      exact hodd
    }

/-- For positive `q`, the odd-branch numerator is twice `3 * q - 1`. -/
theorem BurstNumerator (q : ℕ) (hq : 1 ≤ q) :
    3 * (2 * q - 1) + 1 = 2 * (3 * q - 1) := by
  have hmul : 6 * 1 ≤ 6 * q := Nat.mul_le_mul_left 6 hq
  have h6 : 6 ≤ 6 * q := by
    rw [Nat.mul_one] at hmul
    exact hmul
  have h3 : 3 ≤ 6 * q := Nat.le_trans (by decide : (3 : ℕ) ≤ 6) h6
  have h2 : 2 ≤ 6 * q := Nat.le_trans (by decide : (2 : ℕ) ≤ 6) h6
  have hshift : (6 * q - 3) + 1 = 6 * q - 2 := by
    apply Nat.add_right_cancel (m := 2)
    calc ((6 * q - 3) + 1) + 2
        = (6 * q - 3) + (1 + 2) := Nat.add_assoc _ _ _
      _ = (6 * q - 3) + 3 := rfl
      _ = 6 * q := Nat.sub_add_cancel h3
      _ = (6 * q - 2) + 2 := (Nat.sub_add_cancel h2).symm
  have hleft : 3 * (2 * q - 1) + 1 = 6 * q - 2 := by
    have hdist : 3 * (2 * q - 1) = 3 * (2 * q) - 3 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have hsix : 3 * (2 * q) = 6 * q := by
      rw [← Nat.mul_assoc]
    rw [hdist, hsix]
    exact hshift
  have hright : 2 * (3 * q - 1) = 6 * q - 2 := by
    have hdist : 2 * (3 * q - 1) = 2 * (3 * q) - 2 := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have hsix : 2 * (3 * q) = 6 * q := by
      rw [← Nat.mul_assoc]
    rw [hdist, hsix]
  exact hleft.trans hright.symm

/-- One odd branch advances the closed term from index `k` to index `k + 1`. -/
theorem BurstStepClosed (a k : ℕ) (hk : k < a) :
    OddBurstStep (BurstTerm a k) = BurstTerm a (k + 1) := by
  let q : ℕ := 3 ^ k * 2 ^ (a - (k + 1))
  have hqdef : q = 3 ^ k * 2 ^ (a - (k + 1)) := rfl
  have hq : 1 ≤ q := by
    rw [hqdef]
    exact Nat.mul_le_mul
      (Nat.one_le_pow k 3 (by decide))
      (Nat.one_le_pow (a - (k + 1)) 2 (by decide))
  have hterm : BurstTerm a k = 2 * q - 1 := by
    have hsum : BurstTerm a k + 1 = 2 * q := by
      rw [BurstTermSucc a k, BurstMonomialEven a k hk, hqdef]
    exact Nat.eq_sub_of_add_eq hsum
  have hnext : BurstTerm a (k + 1) = 3 * q - 1 := by
    have hsum : BurstTerm a (k + 1) + 1 = 3 * q := by
      rw [BurstTermSucc a (k + 1), hqdef]
      unfold BurstMonomial
      rw [Nat.pow_succ', ← Nat.mul_assoc]
    exact Nat.eq_sub_of_add_eq hsum
  have hnum : 3 * BurstTerm a k + 1 = 2 * BurstTerm a (k + 1) := by
    rw [hterm, hnext, BurstNumerator q hq]
  unfold OddBurstStep
  exact Nat.div_eq_of_eq_mul_right (by decide : 0 < 2) hnum

/-- On an odd input the shortcut selects the odd branch. -/
theorem BurstShortcutOnOdd (n : ℕ) (h : n % 2 = 1) :
    BurstShortcut n = OddBurstStep n := by
  have hne : ¬ n % 2 = 0 := by
    intro hz
    have hone : (1 : ℕ) = 0 := by
      rw [← h, hz]
    exact Nat.one_ne_zero hone
  unfold BurstShortcut OddBurstStep
  rw [if_neg hne]

/-- `k` shortcut steps from `2 ^ a - 1` stay on the closed term while `k ≤ a`. -/
theorem BurstClosedForm (a k : ℕ) :
    k ≤ a → Iterate BurstShortcut k (2 ^ a - 1) = BurstTerm a k := by
  induction k with
  | zero => {
      intro _
      unfold BurstTerm BurstMonomial
      rw [Nat.pow_zero, Nat.one_mul, Nat.sub_zero]
      rfl
    }
  | succ k ih => {
      intro hk
      have hklt : k < a := Nat.lt_of_succ_le hk
      have hprev := ih (Nat.le_of_lt hklt)
      have hstep : Iterate BurstShortcut (k + 1) (2 ^ a - 1) =
          BurstShortcut (Iterate BurstShortcut k (2 ^ a - 1)) := rfl
      rw [hstep, hprev, BurstShortcutOnOdd (BurstTerm a k)
        (BurstTermOdd a k hklt)]
      exact BurstStepClosed a k hklt
    }

/-- Every positive power of three exceeds the same power of two. -/
theorem TwoPowLtThreePow (n : ℕ) : 2 ^ (n + 1) < 3 ^ (n + 1) := by
  induction n with
  | zero => {
      decide
    }
  | succ n ih => {
      have hx : 0 < 2 ^ (n + 1) :=
        Nat.one_le_pow (n + 1) 2 (by decide)
      have htwo : 2 * 2 ^ (n + 1) < 3 * 2 ^ (n + 1) := by
        have hadd : 2 * 2 ^ (n + 1) <
            2 * 2 ^ (n + 1) + 2 ^ (n + 1) :=
          Nat.lt_add_of_pos_right hx
        have hsum : 2 * 2 ^ (n + 1) + 2 ^ (n + 1) =
            3 * 2 ^ (n + 1) :=
          (Nat.succ_mul 2 (2 ^ (n + 1))).symm
        rw [← hsum]
        exact hadd
      have hthree : 3 * 2 ^ (n + 1) < 3 * 3 ^ (n + 1) :=
        Nat.mul_lt_mul_of_pos_left ih (by decide : 3 > 0)
      calc 2 ^ (n + 2)
          = 2 * 2 ^ (n + 1) := by rw [Nat.pow_succ']
        _ < 3 * 2 ^ (n + 1) := htwo
        _ < 3 * 3 ^ (n + 1) := hthree
        _ = 3 ^ (n + 2) := by rw [← Nat.pow_succ']
    }

/-- For `a ≥ 2`, the arrival value is strictly larger than the seed. -/
theorem BurstStrict (a : ℕ) (ha : 2 ≤ a) : 2 ^ a - 1 < 3 ^ a - 1 := by
  have hidx : a = (a - 1) + 1 := by omega
  have hlt : 2 ^ a < 3 ^ a := by
    rw [hidx]
    exact TwoPowLtThreePow (a - 1)
  have hone : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
  have hnz : 2 ^ a ≠ 0 := Nat.ne_of_gt (show 0 < 2 ^ a from hone)
  have hpred : 2 ^ a - 1 < 2 ^ a := Nat.sub_one_lt hnz
  have hle : 2 ^ a ≤ 3 ^ a - 1 := Nat.le_sub_one_of_lt hlt
  exact Nat.lt_of_lt_of_le hpred hle

/-- Every power of three is odd. -/
theorem ThreePowOdd (a : ℕ) : 3 ^ a % 2 = 1 := by
  induction a with
  | zero => {
      decide
    }
  | succ a ih => {
      rw [Nat.pow_succ', Nat.mul_mod, ih]
    }

/-- The arrival value `3 ^ a - 1` is even, so the next shortcut is not odd. -/
theorem BurstArrivalEven (a : ℕ) : (3 ^ a - 1) % 2 = 0 := by
  have hodd : 3 ^ a % 2 = 1 := ThreePowOdd a
  have hsplit : 2 * (3 ^ a / 2) + 3 ^ a % 2 = 3 ^ a :=
    Nat.div_add_mod (3 ^ a) 2
  rw [hodd] at hsplit
  have hsub : 3 ^ a - 1 = 2 * (3 ^ a / 2) :=
    (Nat.eq_sub_of_add_eq hsplit).symm
  exact Nat.mod_eq_zero_of_dvd ⟨3 ^ a / 2, hsub⟩

/-- The shortcut orbit of `2 ^ a - 1` reaches `3 ^ a - 1` by `a` odd steps.
For `a ≥ 2` that value is strictly larger than the seed. The arrival value is
even. This does not assert that an iterate equals `1`. -/
theorem BurstGrowth (a : ℕ) :
    (∀ k, k ≤ a →
      Iterate BurstShortcut k (2 ^ a - 1) =
        3 ^ k * 2 ^ (a - k) - 1) ∧
    Iterate BurstShortcut a (2 ^ a - 1) = 3 ^ a - 1 ∧
    (∀ k, k < a →
      Iterate BurstShortcut k (2 ^ a - 1) % 2 = 1 ∧
        Iterate BurstShortcut (k + 1) (2 ^ a - 1) =
          (3 * Iterate BurstShortcut k (2 ^ a - 1) + 1) / 2) ∧
    (3 ^ a - 1) % 2 = 0 ∧
    (2 ≤ a → 2 ^ a - 1 < 3 ^ a - 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · {
      intro k hk
      rw [BurstClosedForm a k hk]
      rfl
    }
  · {
      have hend := BurstClosedForm a a (Nat.le_refl a)
      rw [hend]
      unfold BurstTerm BurstMonomial
      rw [Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    }
  · {
      intro k hk
      have hle : k ≤ a := Nat.le_of_lt hk
      have hsuc : k + 1 ≤ a := hk
      have hstate := BurstClosedForm a k hle
      have hnext := BurstClosedForm a (k + 1) hsuc
      refine ⟨?_, ?_⟩
      · {
          rw [hstate]
          exact BurstTermOdd a k hk
        }
      · {
          rw [hstate, hnext, ← BurstStepClosed a k hk]
          rfl
        }
    }
  · {
      exact BurstArrivalEven a
    }
  · {
      intro ha
      exact BurstStrict a ha
    }

end GeneralizedCollatz
