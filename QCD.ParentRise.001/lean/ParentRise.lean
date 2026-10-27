-- SPDX-License-Identifier: CC-BY-4.0
import GeneralizedCollatz
import Mathlib.Tactic.Ring

/-!
The shortcut orbit of 27 through its first odd-even-even block.

An even input is halved. An odd input is sent to `(3n+1)/2`. The block
starting at 445 has saturated parent 222, and 222 is strictly larger than 27.
Nothing below asserts that an iterate equals 1.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.ParentRiseExample

/-- Classical binary parameters: affine branch `3n+1`, exact division by `2`. -/
def ClassicalBinary : Parameters where
  Q := 3
  C := 1
  D := 2
  DAdmissible := by decide

/-- Halve an even input, and send an odd input to the integer `(3n+1)/2`. -/
def Shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The even branch is ordinary halving. -/
theorem ShortcutEven (n : ℕ) (h : n % 2 = 0) : Shortcut n = n / 2 := by
  simp [Shortcut, h]

/-- An odd residue is not the even branch. -/
theorem NotEvenOfOdd (n : ℕ) (h : n % 2 = 1) : ¬ n % 2 = 0 := by
  intro hz
  have heq : (1 : ℕ) = 0 := by
    rw [← h, hz]
  exact Nat.one_ne_zero heq

/-- The odd branch is the integer `(3n+1)/2`. -/
theorem ShortcutOdd (n : ℕ) (h : n % 2 = 1) :
    Shortcut n = (3 * n + 1) / 2 := by
  simp [Shortcut, NotEvenOfOdd n h]

/-- A natural number not divisible by `2` has residue `1`. -/
theorem ModTwoOne (n : ℕ) (h : ¬ n % 2 = 0) : n % 2 = 1 := by
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide : 0 < 2)
  cases hmod : n % 2 with
  | zero => {
      exact False.elim (h hmod)
    }
  | succ k => {
      cases k with
      | zero => {
          exact Nat.zero_add 1
        }
      | succ k => {
          rw [hmod] at hlt
          have hk : k < 0 :=
            Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hlt)
          exact absurd hk (Nat.not_lt_zero k)
        }
    }

/-- Evenness of a natural number is divisibility by `2` after casting to `ℤ`. -/
theorem TwoDvdIntOfEven (n : ℕ) (h : n % 2 = 0) : (2 : ℤ) ∣ (n : ℤ) := by
  exact Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero h)

/-- An odd natural number is not divisible by `2` in `ℤ`. -/
theorem TwoNotDvdIntOfOdd (n : ℕ) (h : n % 2 = 1) : ¬ (2 : ℤ) ∣ (n : ℤ) := by
  intro hd
  have hn : 2 ∣ n := Int.natCast_dvd_natCast.mp hd
  exact NotEvenOfOdd n h (Nat.mod_eq_zero_of_dvd hn)

/-- Halving in `ℕ` and in `ℤ` agree on an even input. -/
theorem CastHalve (n : ℕ) (h : n % 2 = 0) :
    ((n / 2 : ℕ) : ℤ) = (n : ℤ) / 2 := by
  have hsplit : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  rw [h, Nat.add_zero] at hsplit
  have hnat : n = 2 * (n / 2) := hsplit.symm
  have hcast : (n : ℤ) = ((n / 2 : ℕ) : ℤ) * 2 := by
    conv_lhs => rw [hnat]
    rw [Nat.cast_mul, Int.mul_comm]
    simp
  exact (Int.ediv_eq_of_eq_mul_left (by decide : (2 : ℤ) ≠ 0) hcast).symm

/-- If `n` is odd, then `3n+1` is even. -/
theorem ThreeOddEven (n : ℕ) (h : n % 2 = 1) : (3 * n + 1) % 2 = 0 := by
  have hsplit : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  rw [h] at hsplit
  have hn : n = 2 * (n / 2) + 1 := hsplit.symm
  have hexp : 3 * n + 1 = 2 * (3 * (n / 2) + 2) := by
    rw [hn]
    omega
  exact Nat.mod_eq_zero_of_dvd ⟨3 * (n / 2) + 2, hexp⟩

/-- One even shortcut is one raw step, and one odd shortcut is two raw steps. -/
theorem ShortcutMatchesRaw (n : ℕ) :
    (Shortcut n : ℤ) =
      Iterate (RawStep ClassicalBinary)
        (if n % 2 = 0 then 1 else 2) (n : ℤ) := by
  by_cases h : n % 2 = 0
  · {
      -- An even input uses one raw division.
      have hclock : (if n % 2 = 0 then 1 else 2) = 1 := if_pos h
      have hone : Iterate (RawStep ClassicalBinary) 1 (n : ℤ) =
          RawStep ClassicalBinary (n : ℤ) := by
        rfl
      have hd : (2 : ℤ) ∣ (n : ℤ) := TwoDvdIntOfEven n h
      have hraw : RawStep ClassicalBinary (n : ℤ) = (n : ℤ) / 2 := by
        simp [RawStep, ClassicalBinary, hd]
      rw [hclock, hone, hraw, ShortcutEven n h]
      exact CastHalve n h
    }
  · {
      have h1 : n % 2 = 1 := ModTwoOne n h
      -- An odd input uses the affine raw step and then one division.
      have hclock : (if n % 2 = 0 then 1 else 2) = 2 := if_neg h
      have htwo : Iterate (RawStep ClassicalBinary) 2 (n : ℤ) =
          RawStep ClassicalBinary (RawStep ClassicalBinary (n : ℤ)) := by
        rfl
      have hnot : ¬ (2 : ℤ) ∣ (n : ℤ) := TwoNotDvdIntOfOdd n h1
      have hfirst : RawStep ClassicalBinary (n : ℤ) = 3 * (n : ℤ) + 1 := by
        simp [RawStep, ClassicalBinary, hnot]
      have heven : (3 * n + 1) % 2 = 0 := ThreeOddEven n h1
      have hcast : ((3 * n + 1 : ℕ) : ℤ) = 3 * (n : ℤ) + 1 := by
        simp
      have hd : (2 : ℤ) ∣ (3 * (n : ℤ) + 1) := by
        rw [← hcast]
        exact TwoDvdIntOfEven (3 * n + 1) heven
      have hsecond : RawStep ClassicalBinary (3 * (n : ℤ) + 1) =
          (3 * (n : ℤ) + 1) / 2 := by
        simp [RawStep, ClassicalBinary, hd]
      rw [hclock, htwo, hfirst, hsecond, ShortcutOdd n h1, ← hcast]
      exact CastHalve (3 * n + 1) heven
    }

/-- The shortcut orbit of `27`, with time `0` equal to the seed. -/
def Orbit27 : ℕ → ℕ
  | 0 => 27
  | k + 1 => Shortcut (Orbit27 k)

/-- Each later orbit state is one shortcut step. -/
theorem Orbit27Step (k : ℕ) : Orbit27 (k + 1) = Shortcut (Orbit27 k) := by
  rfl

/-- The first ten shortcut states of `27` are the stated prefix. -/
theorem Orbit27Prefix :
    Orbit27 0 = 27 ∧ Orbit27 1 = 41 ∧ Orbit27 2 = 62 ∧
      Orbit27 3 = 31 ∧ Orbit27 4 = 47 ∧ Orbit27 5 = 71 ∧
      Orbit27 6 = 107 ∧ Orbit27 7 = 161 ∧ Orbit27 8 = 242 ∧
      Orbit27 9 = 121 := by
  decide

/-- The orbit continues through the join at time `26`. -/
theorem Orbit27ThroughJoin :
    Orbit27 10 = 182 ∧ Orbit27 11 = 91 ∧ Orbit27 12 = 137 ∧
      Orbit27 13 = 206 ∧ Orbit27 14 = 103 ∧ Orbit27 15 = 155 ∧
      Orbit27 16 = 233 ∧ Orbit27 17 = 350 ∧ Orbit27 18 = 175 ∧
      Orbit27 19 = 263 ∧ Orbit27 20 = 395 ∧ Orbit27 21 = 593 ∧
      Orbit27 22 = 890 ∧ Orbit27 23 = 445 ∧ Orbit27 24 = 668 ∧
      Orbit27 25 = 334 ∧ Orbit27 26 = 167 := by
  decide

/-- Both this state and the next state are even. -/
def BothEven (t : ℕ) : Bool :=
  (Orbit27 t % 2 == 0) && (Orbit27 (t + 1) % 2 == 0)

/-- A false boolean witness excludes two consecutive even states. -/
theorem BothEvenFalse (t : ℕ) (h : BothEven t = false) :
    ¬ (Orbit27 t % 2 = 0 ∧ Orbit27 (t + 1) % 2 = 0) := by
  intro hpair
  rcases hpair with ⟨h0, h1⟩
  have hb : BothEven t = true := by
    unfold BothEven
    rw [h0, h1]
    decide
  rw [hb] at h
  cases h

/-- True when some time strictly before `k` starts two even states. -/
def EarlierDoubleEven : ℕ → Bool
  | 0 => false
  | t + 1 => BothEven t || EarlierDoubleEven t

/-- A false scan before time `k` means no earlier consecutive even pair. -/
theorem EarlierDoubleEvenSound (k : ℕ) :
    EarlierDoubleEven k = false →
      ∀ t, t < k →
        ¬ (Orbit27 t % 2 = 0 ∧ Orbit27 (t + 1) % 2 = 0) := by
  induction k with
  | zero => {
      intro _ t ht
      exact absurd ht (Nat.not_lt_zero t)
    }
  | succ k ih => {
      intro h t ht
      have hstep : EarlierDoubleEven (k + 1) =
          (BothEven k || EarlierDoubleEven k) := by
        rfl
      rw [hstep] at h
      cases hB : BothEven k with
      | true => {
          rw [hB, Bool.true_or] at h
          cases h
        }
      | false => {
          rw [hB, Bool.false_or] at h
          have ht' : t < k ∨ t = k := Nat.lt_succ_iff_lt_or_eq.mp ht
          cases ht' with
          | inl hlt => {
              exact ih h t hlt
            }
          | inr heq => {
              rw [heq]
              exact BothEvenFalse k hB
            }
        }
    }

/-- Time `24` is the first consecutive even pair, and time `23` is odd. -/
theorem FirstDoubleEvenScan :
    EarlierDoubleEven 24 = false ∧
      BothEven 24 = true ∧
      Orbit27 23 % 2 = 1 := by
  decide

/-- No time before `24` has two consecutive even orbit states. -/
theorem NoEarlierDoubleEven :
    ∀ t, t < 24 →
      ¬ (Orbit27 t % 2 = 0 ∧ Orbit27 (t + 1) % 2 = 0) :=
  EarlierDoubleEvenSound 24 FirstDoubleEvenScan.1

/-- For odd `m`, three steps from `4m+1` meet two steps from `2m`. -/
theorem OddEvenEvenJoin (m : ℕ) (hm : m % 2 = 1) :
    Shortcut (4 * m + 1) = 2 * (3 * m + 1) ∧
      Shortcut (2 * (3 * m + 1)) = 3 * m + 1 ∧
      Shortcut (3 * m + 1) = (3 * m + 1) / 2 ∧
      Shortcut (2 * m) = m ∧
      Shortcut m = (3 * m + 1) / 2 := by
  have hzMod : (4 * m + 1) % 2 = 1 := by
    have hfac : 4 * m + 1 = 1 + 2 * (2 * m) := by
      omega
    rw [hfac]
    rw [Nat.add_mul_mod_self_left]
  have haffine : 3 * (4 * m + 1) + 1 = 2 * (2 * (3 * m + 1)) := by
    ring
  have hquot : (3 * (4 * m + 1) + 1) / 2 = 2 * (3 * m + 1) := by
    rw [haffine]
    exact Nat.mul_div_cancel_left (2 * (3 * m + 1)) (by decide : 0 < 2)
  have hfirst : Shortcut (4 * m + 1) = 2 * (3 * m + 1) := by
    rw [ShortcutOdd (4 * m + 1) hzMod]
    exact hquot
  have hsecondMod : (2 * (3 * m + 1)) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd ⟨3 * m + 1, rfl⟩
  have hsecond : Shortcut (2 * (3 * m + 1)) = 3 * m + 1 := by
    rw [ShortcutEven (2 * (3 * m + 1)) hsecondMod]
    exact Nat.mul_div_cancel_left (3 * m + 1) (by decide : 0 < 2)
  have hthirdMod : (3 * m + 1) % 2 = 0 := ThreeOddEven m hm
  have hthird : Shortcut (3 * m + 1) = (3 * m + 1) / 2 :=
    ShortcutEven (3 * m + 1) hthirdMod
  have hparentMod : (2 * m) % 2 = 0 := Nat.mod_eq_zero_of_dvd ⟨m, rfl⟩
  have hparent : Shortcut (2 * m) = m := by
    rw [ShortcutEven (2 * m) hparentMod]
    exact Nat.mul_div_cancel_left m (by decide : 0 < 2)
  have hoddStep : Shortcut m = (3 * m + 1) / 2 := ShortcutOdd m hm
  exact ⟨hfirst, hsecond, hthird, hparent, hoddStep⟩

/-- The odd-even-even block and the even parent reach the same join. -/
theorem OddEvenEvenClock (m : ℕ) (hm : m % 2 = 1) :
    Shortcut (Shortcut (Shortcut (4 * m + 1))) =
      Shortcut (Shortcut (2 * m)) := by
  rcases OddEvenEvenJoin m hm with ⟨h1, h2, h3, h4, h5⟩
  rw [h1, h2, h3, h4, h5]

/-- At `m = 111`, the block `445` and the parent `222` join at `167`. -/
theorem JoinAt111 :
    Shortcut (Shortcut (Shortcut (4 * 111 + 1))) =
      Shortcut (Shortcut (2 * 111)) :=
  OddEvenEvenClock 111 (by decide : 111 % 2 = 1)

/-- The prefix, the first odd-even-even parent, and the comparison with `27`. -/
theorem ParentRise :
    (Orbit27 0 = 27 ∧ Orbit27 1 = 41 ∧ Orbit27 2 = 62 ∧
      Orbit27 3 = 31 ∧ Orbit27 4 = 47 ∧ Orbit27 5 = 71 ∧
      Orbit27 6 = 107 ∧ Orbit27 7 = 161 ∧ Orbit27 8 = 242 ∧
      Orbit27 9 = 121) ∧
    (Orbit27 10 = 182 ∧ Orbit27 11 = 91 ∧ Orbit27 12 = 137 ∧
      Orbit27 13 = 206 ∧ Orbit27 14 = 103 ∧ Orbit27 15 = 155 ∧
      Orbit27 16 = 233 ∧ Orbit27 17 = 350 ∧ Orbit27 18 = 175 ∧
      Orbit27 19 = 263 ∧ Orbit27 20 = 395 ∧ Orbit27 21 = 593 ∧
      Orbit27 22 = 890 ∧ Orbit27 23 = 445 ∧ Orbit27 24 = 668 ∧
      Orbit27 25 = 334 ∧ Orbit27 26 = 167) ∧
    (∀ t, t < 24 →
      ¬ (Orbit27 t % 2 = 0 ∧ Orbit27 (t + 1) % 2 = 0)) ∧
    (Orbit27 23 % 2 = 1 ∧ Orbit27 24 % 2 = 0 ∧ Orbit27 25 % 2 = 0) ∧
    ((445 - 1) / 2 = 222 ∧
      4 * 111 + 1 = 445 ∧ 2 * 111 = 222 ∧
      Shortcut (Shortcut (Shortcut (4 * 111 + 1))) =
        Shortcut (Shortcut (2 * 111)) ∧
      Shortcut 445 = 668 ∧ Shortcut 668 = 334 ∧ Shortcut 334 = 167 ∧
      Shortcut 222 = 111 ∧ Shortcut 111 = 167) ∧
    (222 = 2 * 111 ∧ 111 % 2 = 1) ∧
    (222 % 3 = 0 ∧ ¬ (3 ∣ (222 + 1)) ∧
      2 ^ 0 * (222 + 1) - 1 = 222) ∧
    (167 % 3 = 2 ∧ (2 * 167 - 1) / 3 = 111) ∧
    27 < 222 := by
  refine ⟨Orbit27Prefix, Orbit27ThroughJoin, NoEarlierDoubleEven, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact ⟨FirstDoubleEvenScan.2.2, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide, JoinAt111, by decide, by decide,
      by decide, by decide, by decide⟩
  · decide
  · decide
  · decide
  · decide

end GeneralizedCollatz.ParentRiseExample
