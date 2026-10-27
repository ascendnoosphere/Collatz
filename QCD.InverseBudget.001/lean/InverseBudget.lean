-- SPDX-License-Identifier: CC-BY-4.0
-- Copyright (c) 2026 ascendnoosphere

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

/-!
# Inverse budget

The raw step sends `n` to `n / D` when `D` divides `n`, and to `q * n + c`
otherwise. One affine step followed by one division is `(q * n + c) / D`.
A word is legal when every letter is applied to an integer that admits it.
If the start is strictly smaller than the terminal value, the denominator
power is strictly smaller than `(q + c)` to the affine count. For fixed
positive counts the words form a finite duplicate-free list, and each word
has at most one start replaying to a fixed terminal value. The inequality
does not bound an unbounded affine depth, and it does not send every
positive integer to `1`.
-/

set_option autoImplicit false

namespace GeneralizedCollatz.InverseBudgetAnalysis

/-- Affine branch or exact division by `D`. -/
inductive Letter where
  | affine
  | division
  deriving DecidableEq, Repr

/-- Place an affine letter at the head. -/
def ConsA (w : List Letter) : List Letter := Letter.affine :: w

/-- Place a division letter at the head. -/
def ConsE (w : List Letter) : List Letter := Letter.division :: w

/-- Number of affine letters. -/
def AffineCount : List Letter → ℕ
  | [] => 0
  | Letter.affine :: t => AffineCount t + 1
  | Letter.division :: t => AffineCount t

/-- Number of division letters. -/
def DivisionCount : List Letter → ℕ
  | [] => 0
  | Letter.affine :: t => DivisionCount t
  | Letter.division :: t => DivisionCount t + 1

/-- Read a word from the head. Division truncates when it is not exact. -/
def Replay (q c D : ℕ) : List Letter → ℕ → ℕ
  | [], p => p
  | Letter.affine :: t, p => Replay q c D t (q * p + c)
  | Letter.division :: t, p => Replay q c D t (p / D)

/-- Every affine letter meets a nonmultiple and every division meets a multiple. -/
def Legal (q c D : ℕ) : List Letter → ℕ → Prop
  | [], _ => True
  | Letter.affine :: t, p => ¬ D ∣ p ∧ Legal q c D t (q * p + c)
  | Letter.division :: t, p => D ∣ p ∧ Legal q c D t (p / D)

/-- Head-first offset: an affine letter adds `q` to the affine count of its tail. -/
def Offset (q D : ℕ) : List Letter → ℕ
  | [] => 0
  | Letter.affine :: t => q ^ AffineCount t + Offset q D t
  | Letter.division :: t => D * Offset q D t

/-- Words whose affine count is zero. -/
def DivWords : ℕ → List (List Letter)
  | 0 => [[]]
  | e + 1 => (DivWords e).map ConsE

/-- One extra affine letter, using the already built lists of smaller affine count. -/
def AffRow (prev : ℕ → List (List Letter)) : ℕ → List (List Letter)
  | 0 => (prev 0).map ConsA
  | e + 1 => (prev (e + 1)).map ConsA ++ (AffRow prev e).map ConsE

/-- Every word with `s` affine letters and `e` division letters. -/
def Words : ℕ → ℕ → List (List Letter)
  | 0, e => DivWords e
  | s + 1, e => AffRow (Words s) e

/-- The empty counts list is the empty word. -/
theorem WordsZeroZero : Words 0 0 = [[]] := rfl

/-- A pure division list is a division letter on a shorter list. -/
theorem WordsZeroSucc (e : ℕ) :
    Words 0 (e + 1) = (Words 0 e).map ConsE := rfl

/-- A pure affine list is an affine letter on a shorter list. -/
theorem WordsSuccZero (s : ℕ) :
    Words (s + 1) 0 = (Words s 0).map ConsA := rfl

/-- A mixed list splits into an affine head and a division head. -/
theorem WordsSuccSucc (s e : ℕ) :
    Words (s + 1) (e + 1) =
      (Words s (e + 1)).map ConsA ++ (Words (s + 1) e).map ConsE := rfl

/-- The word consisting of `e` division letters. -/
def DivisionWord : ℕ → List Letter
  | 0 => []
  | e + 1 => Letter.division :: DivisionWord e

/-- One affine step followed by one division is `(q * n + c) / D`. -/
theorem AcceleratedEdge (q c D n : ℕ) :
    Replay q c D [Letter.affine, Letter.division] n = (q * n + c) / D := by
  simp [Replay]

/-- The accelerated edge is legal exactly at a nonmultiple whose image is a multiple. -/
theorem AcceleratedLegal (q c D n : ℕ) :
    Legal q c D [Letter.affine, Letter.division] n ↔
      ¬ D ∣ n ∧ D ∣ q * n + c := by
  constructor
  · intro h
    unfold Legal at h
    rcases h with ⟨hA, hrest⟩
    unfold Legal at hrest
    rcases hrest with ⟨hE, _⟩
    exact ⟨hA, hE⟩
  · intro h
    rcases h with ⟨hA, hE⟩
    unfold Legal
    refine ⟨hA, ?_⟩
    unfold Legal
    exact ⟨hE, trivial⟩

/-- An affine step does not outgrow multiplication by `q + c`. -/
theorem AffineBound (q c p : ℕ) (_hc : 1 ≤ c) (hp : 1 ≤ p) :
    q * p + c ≤ (q + c) * p := by
  have hcMul : c * 1 ≤ c * p := Nat.mul_le_mul_left c hp
  have hcLe : c ≤ c * p := by simpa using hcMul
  calc
    q * p + c ≤ q * p + c * p := Nat.add_le_add_left hcLe (q * p)
    _ = (q + c) * p := by rw [← Nat.add_mul]

/-- A legal Replay stays positive and is bounded by the affine expansion. -/
theorem PathHeight (q c D : ℕ) (w : List Letter) (p : ℕ)
    (hc : 1 ≤ c) (hp : 1 ≤ p) (hleg : Legal q c D w p) :
    1 ≤ Replay q c D w p ∧
      D ^ DivisionCount w * Replay q c D w p ≤
        p * (q + c) ^ AffineCount w := by
  induction w generalizing p with
  | nil => {
    refine ⟨hp, ?_⟩
    simp [Replay, DivisionCount, AffineCount]
    }
  | cons b t ih => {
    cases b with
    | affine => {
      unfold Legal at hleg
      rcases hleg with ⟨_, htail⟩
      have hy : 1 ≤ q * p + c := by omega
      have ih' := ih (q * p + c) hy htail
      refine ⟨ih'.1, ?_⟩
      have hbound : q * p + c ≤ (q + c) * p := AffineBound q c p hc hp
      have hscale :
          (q * p + c) * (q + c) ^ AffineCount t ≤
            ((q + c) * p) * (q + c) ^ AffineCount t :=
        Nat.mul_le_mul_right ((q + c) ^ AffineCount t) hbound
      have hright :
          ((q + c) * p) * (q + c) ^ AffineCount t =
            p * (q + c) ^ (AffineCount t + 1) := by
        calc
          ((q + c) * p) * (q + c) ^ AffineCount t
              = (p * (q + c)) * (q + c) ^ AffineCount t := by
                rw [Nat.mul_comm (q + c) p]
          _ = p * ((q + c) * (q + c) ^ AffineCount t) := by
                rw [Nat.mul_assoc]
          _ = p * ((q + c) ^ AffineCount t * (q + c)) := by
                rw [Nat.mul_comm (q + c) ((q + c) ^ AffineCount t)]
          _ = p * (q + c) ^ (AffineCount t + 1) := by
                rw [← Nat.pow_succ]
      have hleft :
          D ^ DivisionCount (Letter.affine :: t) *
              Replay q c D (Letter.affine :: t) p =
            D ^ DivisionCount t * Replay q c D t (q * p + c) := by
        simp [DivisionCount, Replay]
      have hAff : AffineCount (Letter.affine :: t) = AffineCount t + 1 := by
        simp [AffineCount]
      calc
        D ^ DivisionCount (Letter.affine :: t) *
            Replay q c D (Letter.affine :: t) p
            = D ^ DivisionCount t * Replay q c D t (q * p + c) := hleft
        _ ≤ (q * p + c) * (q + c) ^ AffineCount t := ih'.2
        _ ≤ ((q + c) * p) * (q + c) ^ AffineCount t := hscale
        _ = p * (q + c) ^ (AffineCount t + 1) := hright
        _ = p * (q + c) ^ AffineCount (Letter.affine :: t) := by rw [hAff]
      }
    | division => {
      unfold Legal at hleg
      rcases hleg with ⟨hdvd, htail⟩
      have hquot : D * (p / D) = p := Nat.mul_div_cancel' hdvd
      have hy : 1 ≤ p / D := by
        apply Nat.one_le_iff_ne_zero.mpr
        intro hz
        have hpzero : p = 0 := hquot.symm.trans (by rw [hz, Nat.mul_zero])
        exact (Nat.one_le_iff_ne_zero.mp hp) hpzero
      have ih' := ih (p / D) hy htail
      refine ⟨ih'.1, ?_⟩
      have hscale :
          D * (D ^ DivisionCount t * Replay q c D t (p / D)) ≤
            D * ((p / D) * (q + c) ^ AffineCount t) :=
        Nat.mul_le_mul_left D ih'.2
      have hpull :
          D * (D ^ DivisionCount t * Replay q c D t (p / D)) =
            D ^ DivisionCount (Letter.division :: t) *
              Replay q c D (Letter.division :: t) p := by
        simp only [DivisionCount, Replay]
        rw [Nat.pow_succ]
        calc
          D * (D ^ DivisionCount t * Replay q c D t (p / D))
              = (D * D ^ DivisionCount t) *
                  Replay q c D t (p / D) := by rw [← Nat.mul_assoc]
          _ = (D ^ DivisionCount t * D) * Replay q c D t (p / D) := by
                rw [Nat.mul_comm D (D ^ DivisionCount t)]
      have hpush :
          D * ((p / D) * (q + c) ^ AffineCount t) =
            p * (q + c) ^ AffineCount t := by
        calc
          D * ((p / D) * (q + c) ^ AffineCount t)
              = (D * (p / D)) * (q + c) ^ AffineCount t := by
                rw [← Nat.mul_assoc]
          _ = p * (q + c) ^ AffineCount t := by rw [hquot]
      have hAff : AffineCount (Letter.division :: t) = AffineCount t := by
        simp [AffineCount]
      calc
        D ^ DivisionCount (Letter.division :: t) *
            Replay q c D (Letter.division :: t) p
            = D * (D ^ DivisionCount t * Replay q c D t (p / D)) := by
              exact hpull.symm
        _ ≤ D * ((p / D) * (q + c) ^ AffineCount t) := hscale
        _ = p * (q + c) ^ AffineCount t := hpush
        _ = p * (q + c) ^ AffineCount (Letter.division :: t) := by rw [hAff]

      }
    }
/-- An ascending legal Replay forces the denominator below the affine expansion. -/
theorem AscendingGate (q c D m p : ℕ) (w : List Letter)
    (hc : 1 ≤ c) (hD : 2 ≤ D) (hp : 1 ≤ p) (hlt : p < m)
    (hleg : Legal q c D w p) (hend : Replay q c D w p = m) :
    D ^ DivisionCount w < (q + c) ^ AffineCount w := by
  have hheight := PathHeight q c D w p hc hp hleg
  have hle :
      D ^ DivisionCount w * m ≤ p * (q + c) ^ AffineCount w := by
    simpa [hend] using hheight.2
  have hposE : 0 < D ^ DivisionCount w := by
    have hone : 1 ≤ D ^ DivisionCount w :=
      Nat.one_le_pow (DivisionCount w) D (by omega)
    omega
  have hstep :
      D ^ DivisionCount w * (p + 1) ≤ D ^ DivisionCount w * m :=
    Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hlt)
  have hsplit :
      D ^ DivisionCount w * (p + 1) =
        D ^ DivisionCount w * p + D ^ DivisionCount w := by
    rw [Nat.mul_add, Nat.mul_one]
  have hsum :
      D ^ DivisionCount w * p + D ^ DivisionCount w ≤
        p * (q + c) ^ AffineCount w := by
    rw [← hsplit]
    exact Nat.le_trans hstep hle
  have hltp :
      D ^ DivisionCount w * p <
        D ^ DivisionCount w * p + D ^ DivisionCount w :=
    Nat.lt_add_of_pos_right hposE
  have hstrict :
      D ^ DivisionCount w * p < p * (q + c) ^ AffineCount w :=
    lt_of_lt_of_le hltp hsum
  have hp0 : 0 < p := by omega
  have hcomm :
      p * D ^ DivisionCount w < p * (q + c) ^ AffineCount w := by
    simpa [Nat.mul_comm] using hstrict
  exact (Nat.mul_lt_mul_left hp0).mp hcomm

/-- The offset identity converts a legal Replay into multiplication by `q ^ s`. -/
theorem OffsetFormula (q c D : ℕ) (w : List Letter) (p : ℕ)
    (hleg : Legal q c D w p) :
    D ^ DivisionCount w * Replay q c D w p =
      q ^ AffineCount w * p + c * Offset q D w := by
  induction w generalizing p with
  | nil => {
    simp [Replay, DivisionCount, AffineCount, Offset]
    }
  | cons b t ih => {
    cases b with
    | affine => {
      unfold Legal at hleg
      rcases hleg with ⟨_, htail⟩
      have ih' := ih (q * p + c) htail
      simp only [Replay, DivisionCount, AffineCount, Offset]
      rw [ih']
      calc
        q ^ AffineCount t * (q * p + c) + c * Offset q D t
            = q ^ AffineCount t * (q * p) + q ^ AffineCount t * c +
                c * Offset q D t := by rw [Nat.mul_add]
        _ = (q ^ AffineCount t * q) * p + q ^ AffineCount t * c +
              c * Offset q D t := by rw [← Nat.mul_assoc]
        _ = q ^ (AffineCount t + 1) * p + c * q ^ AffineCount t +
              c * Offset q D t := by
            rw [← Nat.pow_succ, Nat.mul_comm (q ^ AffineCount t) c]
        _ = q ^ (AffineCount t + 1) * p +
              c * (q ^ AffineCount t + Offset q D t) := by
            rw [Nat.add_assoc, ← Nat.mul_add]
      }
    | division => {
      unfold Legal at hleg
      rcases hleg with ⟨hdvd, htail⟩
      have ih' := ih (p / D) htail
      have hquot : D * (p / D) = p := Nat.mul_div_cancel' hdvd
      simp only [Replay, DivisionCount, AffineCount, Offset]
      rw [Nat.pow_succ]
      have hQy :
          D * (q ^ AffineCount t * (p / D)) =
            q ^ AffineCount t * (D * (p / D)) := by
        calc
          D * (q ^ AffineCount t * (p / D))
              = (D * q ^ AffineCount t) * (p / D) := by rw [← Nat.mul_assoc]
          _ = (q ^ AffineCount t * D) * (p / D) := by
                rw [Nat.mul_comm D (q ^ AffineCount t)]
          _ = q ^ AffineCount t * (D * (p / D)) := by rw [Nat.mul_assoc]
      have hCo :
          D * (c * Offset q D t) = c * (D * Offset q D t) := by
        calc
          D * (c * Offset q D t) = (D * c) * Offset q D t := by
            rw [← Nat.mul_assoc]
          _ = (c * D) * Offset q D t := by rw [Nat.mul_comm D c]
          _ = c * (D * Offset q D t) := by rw [Nat.mul_assoc]
      calc
        (D ^ DivisionCount t * D) * Replay q c D t (p / D)
            = D * (D ^ DivisionCount t * Replay q c D t (p / D)) := by
              calc
                (D ^ DivisionCount t * D) * Replay q c D t (p / D)
                    = (D * D ^ DivisionCount t) *
                        Replay q c D t (p / D) := by
                      rw [Nat.mul_comm (D ^ DivisionCount t) D]
                _ = D * (D ^ DivisionCount t * Replay q c D t (p / D)) := by
                      rw [Nat.mul_assoc]
        _ = D * (q ^ AffineCount t * (p / D) + c * Offset q D t) := by
              rw [ih']
        _ = D * (q ^ AffineCount t * (p / D)) + D * (c * Offset q D t) := by
              rw [Nat.mul_add]
        _ = q ^ AffineCount t * (D * (p / D)) + c * (D * Offset q D t) := by
              rw [hQy, hCo]
        _ = q ^ AffineCount t * p + c * (D * Offset q D t) := by rw [hquot]

      }
    }
/-- A legal Replay to `m` solves a linear equation for the start. -/
theorem SolvedStart (q c D m p : ℕ) (w : List Letter)
    (hleg : Legal q c D w p) (hend : Replay q c D w p = m) :
    q ^ AffineCount w * p =
      D ^ DivisionCount w * m - c * Offset q D w := by
  have hform := OffsetFormula q c D w p hleg
  rw [hend] at hform
  rw [hform]
  exact (Nat.add_sub_cancel (q ^ AffineCount w * p) (c * Offset q D w)).symm

/-- Distinct legal starts of one word cannot Replay to the same value. -/
theorem UniquePreimage (q c D m p1 p2 : ℕ) (w : List Letter) (hq : 1 ≤ q)
    (h1 : Legal q c D w p1) (h2 : Legal q c D w p2)
    (e1 : Replay q c D w p1 = m) (e2 : Replay q c D w p2 = m) :
    p1 = p2 := by
  have s1 := SolvedStart q c D m p1 w h1 e1
  have s2 := SolvedStart q c D m p2 w h2 e2
  have heq : q ^ AffineCount w * p1 = q ^ AffineCount w * p2 := by rw [s1, s2]
  have hpos : 0 < q ^ AffineCount w := by
    have hone : 1 ≤ q ^ AffineCount w := Nat.one_le_pow (AffineCount w) q (by omega)
    omega
  exact Nat.eq_of_mul_eq_mul_left hpos heq

/-- Every natural number is strictly below the same power of two. -/
theorem NatLtTwoPow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => {
    simp
    }
  | succ n ih => {
    have hle : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt ih
    have hpos : 0 < 2 ^ n := by
      have hone : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
      omega
    have hmul : 2 ^ n * 1 < 2 ^ n * 2 :=
      (Nat.mul_lt_mul_left hpos).mpr (by omega)
    have hpow : 2 ^ n < 2 ^ (n + 1) := by
      rw [Nat.pow_succ]
      simpa using hmul
    exact lt_of_le_of_lt hle hpow

    }
/-- A denominator power below `R` has exponent below `R` once the base is at least two. -/
theorem ExponentBelowBudget (D R e : ℕ) (hD : 2 ≤ D) (h : D ^ e < R) : e < R := by
  by_contra hge
  have hle : R ≤ e := by omega
  have htwo : e < 2 ^ e := NatLtTwoPow e
  have hbase : 2 ^ e ≤ D ^ e := Nat.pow_le_pow_left hD e
  have hR : R < D ^ e := lt_of_le_of_lt hle (lt_of_lt_of_le htwo hbase)
  omega

/-- Consing a fixed letter is injective, so it preserves duplicate-free lists. -/
theorem ConsAInj (a b : List Letter) (h : ConsA a = ConsA b) : a = b := by
  simpa [ConsA] using h

/-- Consing a division letter is injective. -/
theorem ConsEInj (a b : List Letter) (h : ConsE a = ConsE b) : a = b := by
  simpa [ConsE] using h

/-- The image of a duplicate-free list under an injective cons is duplicate-free. -/
theorem NodupMap (f : List Letter → List Letter)
    (inj : ∀ a b, f a = f b → a = b) (l : List (List Letter))
    (hl : l.Nodup) : (List.map f l).Nodup := by
  induction l with
  | nil => {
    simp
    }
  | cons a l ih => {
    simp only [List.map, List.nodup_cons] at hl ⊢
    refine ⟨?_, ih hl.2⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨b, hb, heq⟩
    have hab : a = b := inj a b heq.symm
    exact hl.1 (hab ▸ hb)

    }
/-- An affine-headed word is not division-headed. -/
theorem HeadSplit (l1 l2 : List (List Letter)) (w : List Letter)
    (h1 : w ∈ List.map ConsA l1) (h2 : w ∈ List.map ConsE l2) : False := by
  rcases List.mem_map.mp h1 with ⟨u, _, rfl⟩
  rcases List.mem_map.mp h2 with ⟨v, _, hv⟩
  have hv' : Letter.affine :: u = Letter.division :: v := by
    simpa [ConsA, ConsE] using hv.symm
  injection hv' with hhead htail
  clear htail
  injection hhead

/-- Every listed word has the counts that index the list. -/
theorem WordsSound (s : ℕ) :
    ∀ e w, w ∈ Words s e → AffineCount w = s ∧ DivisionCount w = e := by
  induction s with
  | zero => {
      intro e
      induction e with
      | zero => {
          intro w hw
          have hw' : w = [] := by simpa [WordsZeroZero] using hw
          subst w
          exact ⟨rfl, rfl⟩
        }
      | succ e ih => {
          intro w hw
          rw [WordsZeroSucc] at hw
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
          obtain ⟨ha, he⟩ := ih t ht
          simp [ConsE, AffineCount, DivisionCount, ha, he]
        }
    }
  | succ s ihs => {
      intro e
      induction e with
      | zero => {
          intro w hw
          rw [WordsSuccZero] at hw
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
          obtain ⟨ha, he⟩ := ihs 0 t ht
          simp [ConsA, AffineCount, DivisionCount, ha, he]
        }
      | succ e ihe => {
          intro w hw
          rw [WordsSuccSucc] at hw
          rcases List.mem_append.mp hw with hA | hE
          · {
              obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hA
              obtain ⟨ha, he⟩ := ihs (e + 1) t ht
              simp [ConsA, AffineCount, DivisionCount, ha, he]
            }
          · {
              obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hE
              obtain ⟨ha, he⟩ := ihe t ht
              simp [ConsE, AffineCount, DivisionCount, ha, he]
            }
        }
    }

/-- The two head classes are disjoint, so their recursive lists have no duplicates. -/
theorem WordsNodup (s : ℕ) : ∀ e, (Words s e).Nodup := by
  induction s with
  | zero => {
      intro e
      induction e with
      | zero => { simp [WordsZeroZero] }
      | succ e ih => {
          rw [WordsZeroSucc]
          exact NodupMap ConsE ConsEInj _ ih
        }
    }
  | succ s ihs => {
      intro e
      induction e with
      | zero => {
          rw [WordsSuccZero]
          exact NodupMap ConsA ConsAInj _ (ihs 0)
        }
      | succ e ihe => {
          rw [WordsSuccSucc]
          have hA := NodupMap ConsA ConsAInj _ (ihs (e + 1))
          have hE := NodupMap ConsE ConsEInj _ ihe
          refine List.nodup_append.mpr ⟨hA, hE, ?_⟩
          intro a ha b hb hab
          exact HeadSplit _ _ b (hab ▸ ha) hb
        }
    }

/-- The recursion has exactly one entry for each placement of the affine letters. -/
theorem WordsLength (s e : ℕ) : (Words s e).length = (s + e).choose s := by
  induction s generalizing e with
  | zero => {
      induction e with
      | zero => { simp [WordsZeroZero] }
      | succ e ih => {
          rw [WordsZeroSucc, List.length_map, ih]
          simp
        }
    }
  | succ s ihs => {
      induction e with
      | zero => {
          rw [WordsSuccZero, List.length_map, ihs]
          simp
        }
      | succ e ihe => {
          rw [WordsSuccSucc, List.length_append, List.length_map, List.length_map]
          rw [ihs, ihe]
          have hsum : s + 1 + (e + 1) = (s + (e + 1)) + 1 := by omega
          rw [hsum, Nat.choose_succ_succ']
          have hleft : s + 1 + e = s + (e + 1) := by omega
          rw [hleft]
        }
    }

/-- Every word occurs on the list indexed by its own counts. -/
theorem WordsComplete (w : List Letter) :
    w ∈ Words (AffineCount w) (DivisionCount w) := by
  induction w with
  | nil => {
    rw [AffineCount, DivisionCount, WordsZeroZero]
    exact List.mem_singleton.mpr rfl
    }
  | cons b t ih => {
    cases b with
    | affine => {
      cases hE : DivisionCount t with
      | zero => {
        have ht : t ∈ Words (AffineCount t) 0 := by simpa [hE] using ih
        simp only [AffineCount, DivisionCount, hE]
        have hmap : ConsA t ∈ List.map ConsA (Words (AffineCount t) 0) :=
          List.mem_map_of_mem ht
        rw [WordsSuccZero]
        simpa [ConsA] using hmap
        }
      | succ e => {
        have ht : t ∈ Words (AffineCount t) (e + 1) := by simpa [hE] using ih
        simp only [AffineCount, DivisionCount, hE]
        have hmap :
            ConsA t ∈ List.map ConsA (Words (AffineCount t) (e + 1)) :=
          List.mem_map_of_mem ht
        have hmem : ConsA t ∈
            List.map ConsA (Words (AffineCount t) (e + 1)) ++
              List.map ConsE (Words (AffineCount t + 1) e) :=
          List.mem_append_left _ hmap
        rw [WordsSuccSucc]
        simpa [ConsA] using hmem
        }
      }
    | division => {
      cases hA : AffineCount t with
      | zero => {
        cases hE : DivisionCount t with
        | zero => {
          have ht : t ∈ Words 0 0 := by simpa [hA, hE] using ih
          simp only [AffineCount, DivisionCount, hA, hE]
          have hmap : ConsE t ∈ List.map ConsE (Words 0 0) :=
            List.mem_map_of_mem ht
          rw [WordsZeroSucc]
          simpa [ConsE] using hmap
          }
        | succ e => {
          have ht : t ∈ Words 0 (e + 1) := by simpa [hA, hE] using ih
          simp only [AffineCount, DivisionCount, hA, hE]
          have hmap : ConsE t ∈ List.map ConsE (Words 0 (e + 1)) :=
            List.mem_map_of_mem ht
          rw [WordsZeroSucc]
          simpa [ConsE] using hmap
          }
        }
      | succ s => {
        cases hE : DivisionCount t with
        | zero => {
          have ht : t ∈ Words (s + 1) 0 := by simpa [hA, hE] using ih
          simp only [AffineCount, DivisionCount, hA, hE]
          have hmap : ConsE t ∈ List.map ConsE (Words (s + 1) 0) :=
            List.mem_map_of_mem ht
          have hmem :=
            List.mem_append_right (List.map ConsA (Words s 1)) hmap
          rw [WordsSuccSucc]
          simpa [ConsE] using hmem
          }
        | succ e => {
          have ht : t ∈ Words (s + 1) (e + 1) := by simpa [hA, hE] using ih
          simp only [AffineCount, DivisionCount, hA, hE]
          have hmap :
              ConsE t ∈ List.map ConsE (Words (s + 1) (e + 1)) :=
            List.mem_map_of_mem ht
          have hmem :=
            List.mem_append_right (List.map ConsA (Words s (e + 2))) hmap
          rw [WordsSuccSucc]
          simpa [ConsE] using hmem

          }
        }
      }
    }
/-- A fixed affine ceiling gives a finite integer bound on every ascending word. -/
theorem AscendingDepthBound (q c D m p S : ℕ) (w : List Letter)
    (hc : 1 ≤ c) (hD : 2 ≤ D) (hp : 1 ≤ p) (hlt : p < m)
    (hleg : Legal q c D w p) (hend : Replay q c D w p = m)
    (hcount : AffineCount w ≤ S) :
    DivisionCount w < (q + c) ^ S ∧
      w ∈ Words (AffineCount w) (DivisionCount w) := by
  have hgate := AscendingGate q c D m p w hc hD hp hlt hleg hend
  have hpower : (q + c) ^ AffineCount w ≤ (q + c) ^ S :=
    Nat.pow_le_pow_right (by omega) hcount
  have hfull : D ^ DivisionCount w < (q + c) ^ S := lt_of_lt_of_le hgate hpower
  exact ⟨ExponentBelowBudget D ((q + c) ^ S) (DivisionCount w) hD hfull,
    WordsComplete w⟩

/-- A pure division word has no affine letter and `e` division letters. -/
theorem DivisionWordCounts (e : ℕ) :
    AffineCount (DivisionWord e) = 0 ∧ DivisionCount (DivisionWord e) = e := by
  induction e with
  | zero => {
    simp [DivisionWord, AffineCount, DivisionCount]
    }
  | succ e ih => {
    simp [DivisionWord, AffineCount, DivisionCount, ih]

    }
/-- Dividing `D ^ e * m` by `D`, once for each letter, returns `m`. -/
theorem DivisionWordReplay (q c D m e : ℕ) (hD : 2 ≤ D) :
    Legal q c D (DivisionWord e) (D ^ e * m) ∧
      Replay q c D (DivisionWord e) (D ^ e * m) = m := by
  induction e with
  | zero => {
    simp [DivisionWord, Legal, Replay, Nat.pow_zero, Nat.one_mul]
    }
  | succ e ih => {
    rcases ih with ⟨hleg, hrep⟩
    have hD0 : 0 < D := by omega
    have hmul : D * (D ^ e * m) / D = D ^ e * m :=
      Nat.mul_div_cancel_left (D ^ e * m) hD0
    have hp : D ^ (e + 1) * m = D * (D ^ e * m) := by
      calc
        D ^ (e + 1) * m = (D ^ e * D) * m := by rw [Nat.pow_succ]
        _ = D * (D ^ e * m) := by
          rw [Nat.mul_comm (D ^ e) D, Nat.mul_assoc]
    refine ⟨?_, ?_⟩
    · rw [DivisionWord, Legal, hp]
      refine ⟨Nat.dvd_mul_right D (D ^ e * m), ?_⟩
      simpa [hmul] using hleg
    · rw [DivisionWord, Replay, hp, hmul, hrep]

    }
/-- A positive division tower starts strictly above `m` and misses the budget. -/
theorem DivisionTowerAbove (q c D m e : ℕ) (hD : 2 ≤ D) (hm : 1 ≤ m)
    (he : 1 ≤ e) :
    m < D ^ e * m ∧ ¬ D ^ e < (q + c) ^ AffineCount (DivisionWord e) := by
  have hlarge : 1 < D ^ e := by
    have hpow : D ^ 1 ≤ D ^ e := Nat.pow_le_pow_right (by omega) he
    have hDle : D ≤ D ^ e := by simpa using hpow
    omega
  have hm0 : 0 < m := by omega
  have hlt : m * 1 < m * D ^ e := (Nat.mul_lt_mul_left hm0).mpr hlarge
  refine ⟨by simpa [Nat.mul_comm, Nat.mul_one] using hlt, ?_⟩
  have hcount : AffineCount (DivisionWord e) = 0 := (DivisionWordCounts e).1
  rw [hcount, Nat.pow_zero]
  intro hbudget
  omega

/-- Ascending preimages of fixed positive depth and exponent are a finite list. -/
theorem InverseBudget (D q c s e m : ℕ) (hD : 2 ≤ D) (hq : 1 ≤ q) (hc : 1 ≤ c)
    (hs : 1 ≤ s) (he : 1 ≤ e) :
    (∀ n,
      Replay q c D [Letter.affine, Letter.division] n = (q * n + c) / D) ∧
    (∀ n,
      Legal q c D [Letter.affine, Letter.division] n ↔
        ¬ D ∣ n ∧ D ∣ q * n + c) ∧
    (Words s e).Nodup ∧
    (∀ w, w ∈ Words s e ↔ AffineCount w = s ∧ DivisionCount w = e) ∧
    (∀ w, w ∈ Words s e → 0 < AffineCount w ∧ 0 < DivisionCount w) ∧
    (∀ w p1 p2,
      Legal q c D w p1 → Legal q c D w p2 →
        Replay q c D w p1 = m → Replay q c D w p2 = m → p1 = p2) ∧
    (∀ w p,
      w ∈ Words s e → Legal q c D w p → Replay q c D w p = m →
        1 ≤ p → p < m →
          AffineCount w = s ∧ DivisionCount w = e ∧
            D ^ e < (q + c) ^ s) ∧
    (∀ w p,
      Legal q c D w p → Replay q c D w p = m → 1 ≤ p → p < m →
        AffineCount w = s → DivisionCount w = e →
          D ^ e < (q + c) ^ s ∧ w ∈ Words s e) ∧
    (¬ D ^ e < (q + c) ^ s →
      ∀ w p,
        AffineCount w = s → DivisionCount w = e →
          Legal q c D w p → Replay q c D w p = m →
            1 ≤ p → p < m → False) ∧
    (D ^ e < (q + c) ^ s → e < (q + c) ^ s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact AcceleratedEdge q c D n
  · intro n
    exact AcceleratedLegal q c D n
  · exact WordsNodup s e
  · intro w
    constructor
    · intro hw
      exact WordsSound s e w hw
    · intro hcount
      rcases hcount with ⟨hsC, heC⟩
      have hmem := WordsComplete w
      simpa [hsC, heC] using hmem
  · intro w hw
    have hsound := WordsSound s e w hw
    have hspos : 0 < s := by omega
    have hepos : 0 < e := by omega
    rw [hsound.1, hsound.2]
    exact ⟨hspos, hepos⟩
  · intro w p1 p2 h1 h2 e1 e2
    exact UniquePreimage q c D m p1 p2 w hq h1 h2 e1 e2
  · intro w p hw hleg hend hp hlt
    have hsound := WordsSound s e w hw
    have hgate := AscendingGate q c D m p w hc hD hp hlt hleg hend
    rw [hsound.1, hsound.2] at hgate
    exact ⟨hsound.1, hsound.2, hgate⟩
  · intro w p hleg hend hp hlt hsCount heCount
    have hgate := AscendingGate q c D m p w hc hD hp hlt hleg hend
    have hmem := WordsComplete w
    rw [hsCount, heCount] at hgate hmem
    exact ⟨hgate, hmem⟩
  · intro hfail w p hsCount heCount hleg hend hp hlt
    have hgate := AscendingGate q c D m p w hc hD hp hlt hleg hend
    rw [hsCount, heCount] at hgate
    exact hfail hgate
  · intro hlt
    exact ExponentBelowBudget D ((q + c) ^ s) e hD hlt

/-- The accelerated edge at `5` reaches `8` for `q = 3`, `c = 1`, and `D = 2`. -/
theorem ReplayFive : Replay 3 1 2 [Letter.affine, Letter.division] 5 = 8 ∧
    Legal 3 1 2 [Letter.affine, Letter.division] 5 := by
  refine ⟨by decide, ?_⟩
  rw [AcceleratedLegal]
  decide

/-- Two accelerated edges carry `3` to `8`. -/
theorem ReplayThree :
    Replay 3 1 2
        [Letter.affine, Letter.division, Letter.affine, Letter.division] 3 = 8 ∧
      Legal 3 1 2
        [Letter.affine, Letter.division, Letter.affine, Letter.division] 3 := by
  refine ⟨by decide, ?_⟩
  unfold Legal
  refine ⟨by decide, ?_⟩
  unfold Legal
  refine ⟨by decide, ?_⟩
  unfold Legal
  refine ⟨by decide, ?_⟩
  unfold Legal
  exact ⟨by decide, trivial⟩

/-- A division before the two accelerated edges carries `6` to `8`. -/
theorem ReplaySix :
    Replay 3 1 2 [Letter.division, Letter.affine, Letter.division,
        Letter.affine, Letter.division] 6 = 8 ∧
      Legal 3 1 2 [Letter.division, Letter.affine, Letter.division,
        Letter.affine, Letter.division] 6 := by
  refine ⟨by decide, ?_⟩
  unfold Legal
  refine ⟨by decide, ?_⟩
  unfold Legal
  refine ⟨by decide, ?_⟩
  unfold Legal
  refine ⟨by decide, ?_⟩
  unfold Legal
  refine ⟨by decide, ?_⟩
  unfold Legal
  exact ⟨by decide, trivial⟩

end GeneralizedCollatz.InverseBudgetAnalysis
