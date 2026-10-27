-- SPDX-License-Identifier: CC-BY-4.0
import GeneralizedCollatz
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic

/-!
A greatest-common-divisor stratum obstruction for the positive offset map

  `OffsetStep c n = n / 2` for even `n`, and `OffsetStep c n = 3 * n + c` for odd `n`,

with a positive natural offset `c`.  If `m` divides `c` and `m` is coprime to `6`,
then one step leaves the greatest common divisor with `m` unchanged.  Consequently
every orbit is confined to the stratum `gcd n m` of its seed, the three states
`c`, `4 * c`, `2 * c` form a cycle, and no seed coprime to `m` enters that cycle.
Multiples of `m` have upper density at most `1 / m`, so a nontrivial stratum `m > 1`
excludes every seed coprime to `m`.  For even `c` all odd states have an odd
successor and strictly increase, while the dyadic prefix of any positive seed is
consumed exactly, so every orbit is unbounded.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The positive offset step: halve even states and apply `3 * n + c` to odd states. -/
def OffsetStep (c n : ℕ) : ℕ :=
  if 2 ∣ n then n / 2 else 3 * n + c

/-- Even states are halved. -/
theorem OffsetStepEven (c n : ℕ) (even : 2 ∣ n) : OffsetStep c n = n / 2 := by
  rw [OffsetStep, if_pos even]

/-- Odd states take the affine branch. -/
theorem OffsetStepOdd (c n : ℕ) (odd : ¬ 2 ∣ n) : OffsetStep c n = 3 * n + c := by
  rw [OffsetStep, if_neg odd]

/-- A successor iterate may execute its first instruction before the remaining ones. -/
theorem OffsetIterateSuccFirst {α : Type*} (f : α → α) (k : ℕ) (x : α) :
    Iterate f (k + 1) x = Iterate f k (f x) := by
  rw [show k + 1 = 1 + k by omega, IterateAdd]
  rfl

/-- Division by two preserves the gcd with an odd modulus. -/
theorem OffsetTwoMulGcd (m k : ℕ) (coprime : Nat.Coprime m 2) :
    Nat.gcd (2 * k) m = Nat.gcd k m := by
  refine Nat.dvd_antisymm ?_ ?_
  · have dividesM : Nat.gcd (2 * k) m ∣ m := Nat.gcd_dvd_right (2 * k) m
    have dividesTwoK : Nat.gcd (2 * k) m ∣ 2 * k := Nat.gcd_dvd_left (2 * k) m
    have coprimeTwo : Nat.Coprime (Nat.gcd (2 * k) m) 2 :=
      Nat.Coprime.of_dvd_left dividesM coprime
    exact Nat.dvd_gcd (coprimeTwo.dvd_of_dvd_mul_left dividesTwoK) dividesM
  · have dividesK : Nat.gcd k m ∣ k := Nat.gcd_dvd_left k m
    have dividesM : Nat.gcd k m ∣ m := Nat.gcd_dvd_right k m
    exact Nat.dvd_gcd (dvd_mul_of_dvd_right dividesK 2) dividesM

/-- The offset step preserves the gcd with every divisor `m` of `c` coprime to `6`. -/
theorem OffsetStepGcd (c m n : ℕ) (divides : m ∣ c) (coprime : Nat.Coprime m 6) :
    Nat.gcd (OffsetStep c n) m = Nat.gcd n m := by
  have coprimeTwo : Nat.Coprime m 2 := Nat.Coprime.of_dvd_right (by decide) coprime
  have coprimeThree : Nat.Coprime m 3 := Nat.Coprime.of_dvd_right (by decide) coprime
  by_cases even : 2 ∣ n
  · obtain ⟨k, rfl⟩ := even
    have halves : OffsetStep c (2 * k) = k := by
      rw [OffsetStepEven c (2 * k) (dvd_mul_right 2 k),
        Nat.mul_div_cancel_left k (by omega)]
    rw [halves, OffsetTwoMulGcd m k coprimeTwo]
  · have affine : OffsetStep c n = 3 * n + c := OffsetStepOdd c n even
    rw [affine]
    refine Nat.dvd_antisymm ?_ ?_
    · have dividesGcd : Nat.gcd (3 * n + c) m ∣ Nat.gcd n m := by
        have dividesM : Nat.gcd (3 * n + c) m ∣ m := Nat.gcd_dvd_right (3 * n + c) m
        have dividesSum : Nat.gcd (3 * n + c) m ∣ 3 * n + c :=
          Nat.gcd_dvd_left (3 * n + c) m
        have dividesC : Nat.gcd (3 * n + c) m ∣ c := dvd_trans dividesM divides
        have dividesProduct : Nat.gcd (3 * n + c) m ∣ 3 * n :=
          (Nat.dvd_add_iff_right dividesC).mpr (by simpa [Nat.add_comm] using dividesSum)
        have coprimeThreeGcd : Nat.Coprime (Nat.gcd (3 * n + c) m) 3 :=
          Nat.Coprime.of_dvd_left dividesM coprimeThree
        exact Nat.dvd_gcd (coprimeThreeGcd.dvd_of_dvd_mul_left dividesProduct) dividesM
      exact dividesGcd
    · have dividesN : Nat.gcd n m ∣ n := Nat.gcd_dvd_left n m
      have dividesM : Nat.gcd n m ∣ m := Nat.gcd_dvd_right n m
      have dividesC : Nat.gcd n m ∣ c := dvd_trans dividesM divides
      have dividesSum : Nat.gcd n m ∣ 3 * n + c :=
        Nat.dvd_add (dvd_mul_of_dvd_right dividesN 3) dividesC
      exact Nat.dvd_gcd dividesSum dividesM

/-- Every orbit stays in the gcd stratum of its seed. -/
theorem OffsetOrbitStratum (c m n : ℕ) (divides : m ∣ c) (coprime : Nat.Coprime m 6)
    (k : ℕ) : Nat.gcd (Iterate (OffsetStep c) k n) m = Nat.gcd n m := by
  induction k with
  | zero => { simp [Iterate] }
  | succ k horizon =>
    {
      show Nat.gcd (OffsetStep c (Iterate (OffsetStep c) k n)) m = Nat.gcd n m
      rw [OffsetStepGcd c m _ divides coprime, horizon]
    }

/-- An odd offset returns to itself after one step through `4 * c`. -/
theorem OffsetCycleStepSelf (c : ℕ) (odd : ¬ 2 ∣ c) : OffsetStep c c = 4 * c := by
  rw [OffsetStepOdd c c odd]
  ring

/-- The state `4 * c` is halved to `2 * c`. -/
theorem OffsetCycleStepFour (c : ℕ) : OffsetStep c (4 * c) = 2 * c := by
  rw [OffsetStepEven c (4 * c) ⟨2 * c, by ring⟩]
  rw [show 4 * c = 2 * (2 * c) by ring]
  exact Nat.mul_div_cancel_left (2 * c) (by omega)

/-- The state `2 * c` is halved to `c`. -/
theorem OffsetCycleStepTwo (c : ℕ) : OffsetStep c (2 * c) = c := by
  rw [OffsetStepEven c (2 * c) ⟨c, by ring⟩]
  exact Nat.mul_div_cancel_left c (by omega)

/-- Every odd offset carries the cycle `c → 4 * c → 2 * c → c`. -/
theorem OffsetCycle (c : ℕ) (odd : ¬ 2 ∣ c) : Iterate (OffsetStep c) 3 c = c := by
  show OffsetStep c (OffsetStep c (OffsetStep c c)) = c
  rw [OffsetCycleStepSelf c odd, OffsetCycleStepFour, OffsetCycleStepTwo]

/-- No seed coprime to `m` ever meets the cycle of a divisor `m` of `c` coprime to `6`. -/
theorem OffsetCoprimeSeedAvoidsCycle (c m n : ℕ) (divides : m ∣ c)
    (coprime : Nat.Coprime m 6) (nontrivial : 1 < m) (seed : Nat.Coprime n m) (k : ℕ) :
    Iterate (OffsetStep c) k n ≠ c ∧ Iterate (OffsetStep c) k n ≠ 4 * c ∧
      Iterate (OffsetStep c) k n ≠ 2 * c := by
  have stratum : Nat.gcd (Iterate (OffsetStep c) k n) m = 1 := by
    rw [OffsetOrbitStratum c m n divides coprime k]
    exact seed
  have escape : ¬ m ∣ Iterate (OffsetStep c) k n := by
    intro dividesState
    have dividesOne : m ∣ 1 := by
      have := Nat.dvd_gcd dividesState (dvd_refl m)
      rwa [stratum] at this
    have bound : m ≤ 1 := Nat.le_of_dvd (by omega) dividesOne
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro reaches
    rw [reaches] at escape
    exact escape divides
  · intro reaches
    rw [reaches] at escape
    exact escape (dvd_mul_of_dvd_right divides 4)
  · intro reaches
    rw [reaches] at escape
    exact escape (dvd_mul_of_dvd_right divides 2)

/-- The multiples of `m` below `N` number at most `N / m + 1`. -/
theorem OffsetMultipleCountLe (m N : ℕ) :
    ((Finset.range N).filter (fun n => m ∣ n)).card ≤ N / m + 1 := by
  have key : ((Finset.range N).filter (fun n => m ∣ n)).card ≤
      (Finset.range (N / m + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun n => n / m) ?_ ?_
    · intro n member
      have split : n < N ∧ m ∣ n := by simpa using (Finset.mem_filter.mp member)
      have bound : n / m < N / m + 1 := by
        have stepOne : n ≤ N - 1 := Nat.le_sub_one_of_lt split.1
        have stepTwo : n / m ≤ (N - 1) / m := Nat.div_le_div_right stepOne
        have stepThree : (N - 1) / m ≤ N / m := Nat.div_le_div_right (Nat.sub_le N 1)
        exact Nat.lt_succ_of_le (le_trans stepTwo stepThree)
      simpa using bound
    · intro a memberA b memberB equal
      have dividesA : m ∣ a := (Finset.mem_filter.mp memberA).2
      have dividesB : m ∣ b := (Finset.mem_filter.mp memberB).2
      have halves : a / m = b / m := equal
      rw [← Nat.div_mul_cancel dividesA, ← Nat.div_mul_cancel dividesB, halves]
  simpa [Finset.card_range] using key

/-- Multiples of `m` occupy at most `N + m` of the first `N` states, density at most `1 / m`. -/
theorem OffsetMultipleDensity (m N : ℕ) :
    m * ((Finset.range N).filter (fun n => m ∣ n)).card ≤ N + m := by
  have scaled := Nat.mul_le_mul_left m (OffsetMultipleCountLe m N)
  have divisionBound : m * (N / m) ≤ N := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self N m
  calc m * ((Finset.range N).filter (fun n => m ∣ n)).card
      ≤ m * (N / m + 1) := scaled
    _ = m * (N / m) + m := by ring
    _ ≤ N + m := Nat.add_le_add_right divisionBound m

/-- An odd state over an even offset has an odd strictly larger successor. -/
theorem OffsetEvenOffsetOddStep (c n : ℕ) (evenOffset : 2 ∣ c) (odd : ¬ 2 ∣ n) :
    ¬ 2 ∣ OffsetStep c n ∧ n < OffsetStep c n := by
  have affine : OffsetStep c n = 3 * n + c := OffsetStepOdd c n odd
  constructor
  · rw [affine]
    intro dividesSum
    have dividesThreeN : 2 ∣ 3 * n := (Nat.dvd_add_iff_left evenOffset).mpr dividesSum
    exact odd ((Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 2 3)) dividesThreeN)
  · rw [affine]
    have positive : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact odd (dvd_zero 2))
    omega

/-- Oddness persists along every orbit of an even offset. -/
theorem OffsetEvenOffsetOddPersist (c n : ℕ) (evenOffset : 2 ∣ c) (odd : ¬ 2 ∣ n)
    (j : ℕ) : ¬ 2 ∣ Iterate (OffsetStep c) j n := by
  induction j with
  | zero => { simpa [Iterate] using odd }
  | succ j horizon => { exact (OffsetEvenOffsetOddStep c _ evenOffset horizon).1 }

/-- Along an even offset, an odd seed grows by at least one per step. -/
theorem OffsetEvenOffsetGrowthLower (c n : ℕ) (evenOffset : 2 ∣ c) (odd : ¬ 2 ∣ n) :
    ∀ j, n + j ≤ Iterate (OffsetStep c) j n := by
  intro j
  induction j with
  | zero => { simp [Iterate] }
  | succ j horizon =>
    {
      have persists := OffsetEvenOffsetOddPersist c n evenOffset odd j
      have grows := (OffsetEvenOffsetOddStep c _ evenOffset persists).2
      have unfold : Iterate (OffsetStep c) (j + 1) n =
          OffsetStep c (Iterate (OffsetStep c) j n) := rfl
      rw [unfold]
      omega
    }

/-- The dyadic prefix of a positive seed is consumed exactly. -/
theorem OffsetHalvePrefix (c u : ℕ) : ∀ v, Iterate (OffsetStep c) v (2 ^ v * u) = u := by
  intro v
  induction v generalizing u with
  | zero => { simp [Iterate] }
  | succ v horizon =>
    {
      rw [OffsetIterateSuccFirst]
      have halves : OffsetStep c (2 ^ (v + 1) * u) = 2 ^ v * u := by
        rw [OffsetStepEven c _ ⟨2 ^ v * u, by rw [pow_succ]; ring⟩]
        rw [show 2 ^ (v + 1) * u = 2 * (2 ^ v * u) by rw [pow_succ]; ring]
        exact Nat.mul_div_cancel_left (2 ^ v * u) (by omega)
      rw [halves]
      exact horizon u
    }

/-- Every orbit of an even offset is unbounded. -/
theorem OffsetEvenOffsetUnbounded (c n : ℕ) (evenOffset : 2 ∣ c) (positive : 0 < n) :
    ∀ bound, ∃ k, bound < Iterate (OffsetStep c) k n := by
  intro bound
  obtain ⟨v, u, odd, expansion⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.pos_iff_ne_zero.mp positive)
  have odd' : ¬ 2 ∣ u := odd.not_two_dvd_nat
  refine ⟨v + (bound + 1), ?_⟩
  rw [expansion, IterateAdd, OffsetHalvePrefix]
  have grows := OffsetEvenOffsetGrowthLower c u evenOffset odd' (bound + 1)
  have height : bound < u + (bound + 1) := by omega
  exact lt_of_lt_of_le height grows

/-- The offset `3 ^ a` scales the offset-one dynamics by the same power of three. -/
theorem OffsetStepScaling (a n : ℕ) :
    OffsetStep (3 ^ a) (3 ^ a * n) = 3 ^ a * OffsetStep 1 n := by
  have coprime : Nat.Coprime 2 (3 ^ a) := (by decide : Nat.Coprime 2 3).pow_right a
  by_cases even : 2 ∣ n
  · rw [OffsetStepEven _ _ (dvd_mul_of_dvd_right even _), OffsetStepEven _ _ even,
      Nat.mul_div_assoc (3 ^ a) even]
  · have oddMultiple : ¬ 2 ∣ 3 ^ a * n := fun divides => even (coprime.dvd_of_dvd_mul_left divides)
    rw [OffsetStepOdd _ _ oddMultiple, OffsetStepOdd _ _ even]
    ring

/-- The scaled identity lifts to every iterate. -/
theorem OffsetIterateScaling (a n : ℕ) :
    ∀ k, Iterate (OffsetStep (3 ^ a)) k (3 ^ a * n) = 3 ^ a * Iterate (OffsetStep 1) k n := by
  intro k
  induction k with
  | zero => { simp [Iterate] }
  | succ k horizon =>
    {
      simp only [Iterate]
      rw [horizon, OffsetStepScaling]
    }

end GeneralizedCollatz
