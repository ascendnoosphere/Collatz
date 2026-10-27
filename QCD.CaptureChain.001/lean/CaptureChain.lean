-- SPDX-License-Identifier: CC-BY-4.0
import GeneralizedCollatz

/-!
A legal join is a positive-length exact orbit segment of the raw map.
A finite chain of such joins, ending at `1`, with each parent strictly
smaller in absolute value, puts `1` on the raw orbit of the first state.
The argument is induction along the chain.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.CaptureChain

/-- A legal join is a positive-length exact raw orbit segment from `n` to `m`. -/
def LegalJoin (p : Parameters) (n m : ℤ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ Iterate (RawStep p) k n = m

/-- Consecutive legal joins with parents of strictly smaller absolute value.
    A one-state list has no join. Each added parent is a later raw state. -/
inductive DecreasingCaptureChain (p : Parameters) : List ℤ → Prop where
  /-- A single state is a chain with no parent. -/
  | single (n : ℤ) : DecreasingCaptureChain p [n]
  /-- A legal join to a strictly smaller parent extends a chain. -/
  | link (n m : ℤ) (rest : List ℤ)
      (hjoin : LegalJoin p n m)
      (hdrop : m.natAbs < n.natAbs)
      (htail : DecreasingCaptureChain p (m :: rest)) :
      DecreasingCaptureChain p (n :: m :: rest)

/-- First state of a list. Only nonempty chains occur in the theorem. -/
def ChainHead : List ℤ → ℤ
  | [] => 0
  | n :: _ => n

/-- Last state of a list. Only nonempty chains occur in the theorem. -/
def ChainLast : List ℤ → ℤ
  | [] => 0
  | [n] => n
  | _ :: rest => ChainLast rest

/-- The head of a nonempty list is its first entry. -/
theorem ChainHeadCons (n : ℤ) (rest : List ℤ) :
    ChainHead (n :: rest) = n := by
  rfl

/-- A one-state list ends at that state. -/
theorem ChainLastSingleton (n : ℤ) : ChainLast [n] = n := by
  rfl

/-- The terminal state is unchanged by deleting the first state. -/
theorem ChainLastConsCons (n m : ℤ) (rest : List ℤ) :
    ChainLast (n :: m :: rest) = ChainLast (m :: rest) := by
  rfl

/-- Exact orbit segments concatenate by adding their lengths. -/
theorem CaptureChainConcat (p : Parameters) (n m : ℤ) (k N : ℕ)
    (hk : Iterate (RawStep p) k n = m)
    (hN : Iterate (RawStep p) N m = 1) :
    Iterate (RawStep p) (k + N) n = 1 := by
  -- `C^(k+N)(n) = C^N(C^k(n))`.
  rw [IterateAdd, hk, hN]

/-- A decreasing chain of legal joins ending at `1` reaches `1` by raw iteration.
    The number of states is at most the absolute value of the first state.
    The chain `1` is certified at time `0`. A longer chain is certified at a
    positive time, and its first parent is strictly smaller in absolute value. -/
theorem CaptureChainReachesOne (p : Parameters) (chain : List ℤ)
    (hdec : DecreasingCaptureChain p chain)
    (hlast : ChainLast chain = 1) :
    ∃ N : ℕ,
      Iterate (RawStep p) N (ChainHead chain) = 1 ∧
      chain.length ≤ (ChainHead chain).natAbs ∧
      (chain.length = 1 → N = 0 ∧ ChainHead chain = 1) ∧
      (2 ≤ chain.length →
        0 < N ∧
          (ChainHead chain.tail).natAbs < (ChainHead chain).natAbs) := by
  revert hlast
  induction hdec with
  | single n => {
      intro hlast
      -- The chain is the single state `1`, reached in zero steps.
      refine ⟨0, ?_, ?_, ?_, ?_⟩
      · rw [ChainHeadCons]
        rw [ChainLastSingleton] at hlast
        -- Zero iterations leave the state unchanged.
        exact hlast
      · rw [ChainHeadCons]
        rw [ChainLastSingleton] at hlast
        have hlen : ([n] : List ℤ).length = 1 := by
          rfl
        rw [hlen, hlast]
        have hAbs : (1 : ℤ).natAbs = 1 := by
          rfl
        rw [hAbs]
      · intro _
        rw [ChainHeadCons]
        rw [ChainLastSingleton] at hlast
        exact ⟨rfl, hlast⟩
      · intro htwo
        have hlen : ([n] : List ℤ).length = 1 := by
          rfl
        rw [hlen] at htwo
        exact False.elim (Nat.not_succ_le_self 1 htwo)
    }
  | link n m rest hjoin hdrop _ ih => {
      intro hlast
      -- Concatenate the given join with the certificate for the tail.
      have hlastTail : ChainLast (m :: rest) = 1 := by
        rw [ChainLastConsCons] at hlast
        exact hlast
      rcases ih hlastTail with ⟨Ntail, hReach, hBound, _, _⟩
      rcases hjoin with ⟨k, hkPos, hk⟩
      have hlenFull :
          (n :: m :: rest).length = (m :: rest).length + 1 := by
        rfl
      have hhead : ChainHead (n :: m :: rest) = n := by
        rfl
      have hheadTail : ChainHead (m :: rest) = m := by
        rfl
      have htailList : (n :: m :: rest).tail = m :: rest := by
        rfl
      refine ⟨k + Ntail, ?_, ?_, ?_, ?_⟩
      · have hReachTail : Iterate (RawStep p) Ntail m = 1 := by
          rw [hheadTail] at hReach
          exact hReach
        exact CaptureChainConcat p n m k Ntail hk hReachTail
      · rw [hlenFull, hhead]
        have htailLen : (m :: rest).length ≤ m.natAbs := by
          rw [hheadTail] at hBound
          exact hBound
        have hsucc : (m :: rest).length + 1 ≤ m.natAbs + 1 :=
          Nat.succ_le_succ htailLen
        exact Nat.le_trans hsucc hdrop
      · intro hEq
        have htailPos : 1 ≤ (m :: rest).length := by
          have hrest : (m :: rest).length = rest.length + 1 := by
            rfl
          rw [hrest]
          exact Nat.succ_le_succ (Nat.zero_le rest.length)
        have hge : 2 ≤ (n :: m :: rest).length := by
          rw [hlenFull]
          exact Nat.succ_le_succ htailPos
        have hcontra : 2 ≤ 1 := by
          rw [hEq] at hge
          exact hge
        exact False.elim (Nat.not_succ_le_self 1 hcontra)
      · intro _
        refine ⟨?_, ?_⟩
        · have hkLe : k ≤ k + Ntail := Nat.le_add_right k Ntail
          exact Nat.lt_of_lt_of_le hkPos hkLe
        · rw [htailList, hheadTail, hhead]
          exact hdrop
    }

/-- Binary parameters for the raw rule with affine branch `3n+1`. -/
def ClassicalBinary : Parameters where
  Q := 3
  C := 1
  D := 2
  DAdmissible := by
    have hAbs : (2 : ℤ).natAbs = 2 := by
      rfl
    rw [hAbs]

/-- Under those parameters, one raw step divides `2` by `2`. -/
theorem ClassicalBinaryTwoStep : RawStep ClassicalBinary 2 = 1 := by
  have hD : ClassicalBinary.D = 2 := by
    rfl
  have hdvd : ClassicalBinary.D ∣ (2 : ℤ) := by
    rw [hD]
  unfold RawStep
  rw [if_pos hdvd, hD]
  have hne : (2 : ℤ) ≠ 0 := by
    intro h
    have hnat : (2 : ℕ) = 0 := (Int.ofNat_eq_zero).mp h
    exact Nat.succ_ne_zero 1 hnat
  exact Int.ediv_self hne

/-- Absolute values of the first two positive integers. -/
theorem ClassicalBinaryOneLtTwo : (1 : ℤ).natAbs < (2 : ℤ).natAbs := by
  have h1 : (1 : ℤ).natAbs = 1 := by
    rfl
  have h2 : (2 : ℤ).natAbs = 2 := by
    rfl
  rw [h1, h2]
  -- `1 < 2` is `2 ≤ 2`.
  exact Nat.le_refl 2

/-- The one-state chain at `1` satisfies the capture hypotheses. -/
theorem ClassicalBinaryChainOne :
    DecreasingCaptureChain ClassicalBinary [1] ∧ ChainLast [1] = 1 := by
  exact ⟨DecreasingCaptureChain.single 1, rfl⟩

/-- The chain `2`, `1` is one legal join to a strictly smaller parent. -/
theorem ClassicalBinaryChainTwo :
    DecreasingCaptureChain ClassicalBinary [2, 1] ∧
      ChainLast [2, 1] = 1 := by
  refine ⟨?_, rfl⟩
  exact DecreasingCaptureChain.link 2 1 []
    ⟨1, Nat.succ_pos 0, ClassicalBinaryTwoStep⟩
    ClassicalBinaryOneLtTwo
    (DecreasingCaptureChain.single 1)

/-- The chain `1` certifies that the raw orbit of `1` reaches `1` at time `0`. -/
theorem ClassicalBinaryOneReaches :
    ∃ N : ℕ, N = 0 ∧ Iterate (RawStep ClassicalBinary) N 1 = 1 := by
  rcases ClassicalBinaryChainOne with ⟨hdec, hlast⟩
  rcases CaptureChainReachesOne ClassicalBinary [1] hdec hlast with
    ⟨N, hN, _, hbase, _⟩
  have hlen : ([1] : List ℤ).length = 1 := by
    rfl
  rcases hbase hlen with ⟨hZero, _⟩
  rw [ChainHeadCons] at hN
  exact ⟨N, hZero, hN⟩

/-- The chain `2`, `1` certifies that the raw orbit of `2` reaches `1`.
    The recorded join has length `1`, so one raw step is an exact witness. -/
theorem ClassicalBinaryTwoReaches :
    (∃ N : ℕ, 0 < N ∧ Iterate (RawStep ClassicalBinary) N 2 = 1) ∧
      Iterate (RawStep ClassicalBinary) 1 2 = 1 := by
  refine ⟨?_, ClassicalBinaryTwoStep⟩
  rcases ClassicalBinaryChainTwo with ⟨hdec, hlast⟩
  rcases CaptureChainReachesOne ClassicalBinary [2, 1] hdec hlast with
    ⟨N, hN, _, _, hlong⟩
  have hlen : 2 ≤ ([2, 1] : List ℤ).length := by
    have heq : ([2, 1] : List ℤ).length = 2 := by
      rfl
    rw [heq]
  rcases hlong hlen with ⟨hPos, _⟩
  rw [ChainHeadCons] at hN
  exact ⟨N, hPos, hN⟩

end GeneralizedCollatz.CaptureChain
