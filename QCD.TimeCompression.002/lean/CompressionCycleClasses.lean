-- SPDX-License-Identifier: CC-BY-4.0
import CompressionPeriods
import AdditiveCycles
import Mathlib.Data.Quot

/-!
A bijection of periodic cycle classes under common-power compression.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- A periodic affine image has no divisor-power predecessor on any periodic orbit. -/
theorem PeriodicAffineImagePowerIsolation (p : Parameters) (e hx hy : ℕ) (x y : ℤ)
    (ePositive : 0 < e) (hxPositive : 0 < hx) (hyPositive : 0 < hy)
    (xReturn : Iterate (RawStep p) hx x = x)
    (yReturn : Iterate (RawStep p) hy y = y) (affineGuard : ¬p.D ∣ x) :
    y ≠ p.D ^ e * RawStep p x := by
  intro atPower
  let h := hx * hy
  have hPositive : 0 < h := Nat.mul_pos hxPositive hyPositive
  have xCommon : Iterate (RawStep p) h x = x :=
    IterateReturnMultiple (RawStep p) x hx hy xReturn
  have yCommon : Iterate (RawStep p) h y = y := by
    dsimp [h]
    rw [Nat.mul_comm]
    exact IterateReturnMultiple (RawStep p) y hy hx yReturn
  have exponent : e - (e - 1) = 1 := by omega
  have stage : Iterate (RawStep p) (e - 1) y = p.D * RawStep p x := by
    calc
      Iterate (RawStep p) (e - 1) y =
          Iterate (RawStep p) (e - 1) (p.D ^ e * RawStep p x) :=
        congrArg (Iterate (RawStep p) (e - 1)) atPower
      _ = p.D ^ (e - (e - 1)) * RawStep p x :=
        PowerDivisionPrefix p e (e - 1) _ (by omega)
      _ = p.D * RawStep p x := by rw [exponent, pow_one]
  have stageDivisible : p.D ∣ Iterate (RawStep p) (e - 1) y :=
    ⟨RawStep p x, stage⟩
  have sameNext : RawStep p (Iterate (RawStep p) (e - 1) y) = RawStep p x := by
    calc
      RawStep p (Iterate (RawStep p) (e - 1) y) =
          Iterate (RawStep p) (e - 1) y / p.D := by
        simp only [RawStep, if_pos stageDivisible]
      _ = RawStep p x := by
        apply Int.ediv_eq_of_eq_mul_left p.DNonzero
        rw [stage]
        ring
  have samePoints := CommonReturnStepInjective (RawStep p) h
    (Iterate (RawStep p) (e - 1) y) x hPositive
    (ReturnPeriodPropagates (RawStep p) h (e - 1) y yCommon) xCommon sameNext
  exact affineGuard (samePoints ▸ stageDivisible)

/-- Positive-time block interiors cannot contain any periodic compressed point. -/
theorem CompressionPeriodicPointsNoInterior (p : Parameters) (q c : ℤ)
    (a hx hy k s : ℕ) (qFactor : p.Q = p.D ^ a * q)
    (cFactor : p.C = p.D ^ a * c) (x y : ℤ)
    (hxPositive : 0 < hx) (hyPositive : 0 < hy)
    (xReturn : Iterate (RawStep (CompressedParameters p q c)) hx x = x)
    (yReturn : Iterate (RawStep (CompressedParameters p q c)) hy y = y)
    (sPositive : 0 < s)
    (inside : s < CompressionClock p a
      (Iterate (RawStep (CompressedParameters p q c)) k x)) :
    Iterate (RawStep p) s (Iterate (RawStep (CompressedParameters p q c)) k x) ≠ y := by
  intro interiorHit
  let g := RawStep (CompressedParameters p q c)
  change s < CompressionClock p a (Iterate g k x) at inside
  have affineGuard : ¬p.D ∣ Iterate g k x := by
    intro divisible
    simp only [CompressionClock, if_pos divisible] at inside
    omega
  have clockValue : CompressionClock p a (Iterate g k x) = a + 1 := by
    simp [CompressionClock, affineGuard]
  have sBound : s ≤ a + 1 := by omega
  have exponentPositive : 0 < a + 1 - s := by omega
  have intermediate := CompressionAffineIntermediate p q c a s qFactor cFactor
    (Iterate g k x) affineGuard sPositive sBound
  have atPower : y = p.D ^ (a + 1 - s) * g (Iterate g k x) :=
    interiorHit.symm.trans intermediate
  exact PeriodicAffineImagePowerIsolation (CompressedParameters p q c)
    (a + 1 - s) hx hy (Iterate g k x) y exponentPositive hxPositive hyPositive
    (ReturnPeriodPropagates g hx k x xReturn) yReturn affineGuard atPower

/-- A periodic point has some positive return, without a chosen least period. -/
def PeriodicPoint {α : Type*} (f : α → α) (x : α) : Prop :=
  ∃ h : ℕ, 0 < h ∧ Iterate f h x = x

/-- Reachability records one nonnegative forward iterate and its exact endpoint. -/
def OrbitReaches {α : Type*} (f : α → α) (x y : α) : Prop :=
  ∃ r : ℕ, Iterate f r x = y

/-- Mutual reachability identifies phases of one cycle when restricted to periodic points. -/
def CycleRelation {α : Type*} (f : α → α) (x y : α) : Prop :=
  OrbitReaches f x y ∧ OrbitReaches f y x

/-- Mutual reachability is reflexive, including the zero-clock witness. -/
theorem CycleRelationRefl {α : Type*} (f : α → α) (x : α) : CycleRelation f x x := by
  exact ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩

/-- Swapping the two endpoint witnesses reverses mutual reachability. -/
theorem CycleRelationSymm {α : Type*} (f : α → α) (x y : α)
    (related : CycleRelation f x y) : CycleRelation f y x :=
  ⟨related.2, related.1⟩

/-- Concatenating both directed witness paths preserves mutual reachability. -/
theorem CycleRelationTrans {α : Type*} (f : α → α) (x y z : α)
    (first : CycleRelation f x y) (second : CycleRelation f y z) :
    CycleRelation f x z := by
  obtain ⟨⟨a, xy⟩, ⟨b, yx⟩⟩ := first
  obtain ⟨⟨c, yz⟩, ⟨d, zy⟩⟩ := second
  constructor
  · refine ⟨a + c, ?_⟩
    rw [IterateAdd, xy, yz]
  · refine ⟨d + b, ?_⟩
    rw [IterateAdd, zy, yx]

/-- Expansion sends every periodic compressed point to a periodic raw point. -/
theorem CompressionPeriodicPoint (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (x : ℤ)
    (periodic : PeriodicPoint (RawStep (CompressedParameters p q c)) x) :
    PeriodicPoint (RawStep p) x := by
  obtain ⟨h, hPositive, returned⟩ := periodic
  refine ⟨AccumulatedClock (RawStep (CompressedParameters p q c))
    (CompressionClock p a) h x, ?_, ?_⟩
  · exact lt_of_lt_of_le hPositive (AccumulatedClockLower _ _
      (CompressionClockPositive p a) h x)
  · rwa [← CompressionIterates p q c a qFactor cFactor h x]

/-- Every compressed reachability witness expands with its own exact raw clock. -/
theorem CompressionOrbitReaches (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (x y : ℤ)
    (reaches : OrbitReaches (RawStep (CompressedParameters p q c)) x y) :
    OrbitReaches (RawStep p) x y := by
  obtain ⟨r, hit⟩ := reaches
  refine ⟨AccumulatedClock (RawStep (CompressedParameters p q c))
    (CompressionClock p a) r x, ?_⟩
  rwa [← CompressionIterates p q c a qFactor cFactor r x]

/-- Raw reachability reflects between periodic compressed points, not arbitrary seeds. -/
theorem CompressionPeriodicOrbitReachesIff (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (x y : ℤ)
    (xPeriodic : PeriodicPoint (RawStep (CompressedParameters p q c)) x)
    (yPeriodic : PeriodicPoint (RawStep (CompressedParameters p q c)) y) :
    OrbitReaches (RawStep (CompressedParameters p q c)) x y ↔
      OrbitReaches (RawStep p) x y := by
  constructor
  · exact CompressionOrbitReaches p q c a qFactor cFactor x y
  · intro reaches
    obtain ⟨r, hit⟩ := reaches
    obtain ⟨hx, hxPositive, xReturn⟩ := xPeriodic
    obtain ⟨hy, hyPositive, yReturn⟩ := yPeriodic
    let g := RawStep (CompressedParameters p q c)
    let clock := CompressionClock p a
    obtain ⟨k, s, _, inside, time⟩ :=
      PositiveClockCover g clock (CompressionClockPositive p a) x r
    have state : Iterate (RawStep p) r x = Iterate (RawStep p) s (Iterate g k x) := by
      rw [time, IterateAdd, ← CompressionIterates p q c a qFactor cFactor k x]
    have interiorHit := state.symm.trans hit
    by_cases zeroTime : s = 0
    · exact ⟨k, by simpa only [zeroTime, Iterate] using interiorHit⟩
    · exact False.elim (CompressionPeriodicPointsNoInterior p q c a hx hy k s
        qFactor cFactor x y hxPositive hyPositive xReturn yReturn (by omega) inside interiorHit)

/-- Expansion and periodic reachability reflection identify exactly the same cycle pairs. -/
theorem CompressionCycleRelationIff (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (x y : ℤ)
    (xPeriodic : PeriodicPoint (RawStep (CompressedParameters p q c)) x)
    (yPeriodic : PeriodicPoint (RawStep (CompressedParameters p q c)) y) :
    CycleRelation (RawStep (CompressedParameters p q c)) x y ↔
      CycleRelation (RawStep p) x y := by
  exact and_congr
    (CompressionPeriodicOrbitReachesIff p q c a qFactor cFactor x y xPeriodic yPeriodic)
    (CompressionPeriodicOrbitReachesIff p q c a qFactor cFactor y x yPeriodic xPeriodic)

/-- Every raw cycle has a compressed-periodic representative on that same raw cycle. -/
theorem CompressionRawCycleRepresentative (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) (y : ℤ)
    (yPeriodic : PeriodicPoint (RawStep p) y) :
    ∃ x : ℤ, PeriodicPoint (RawStep (CompressedParameters p q c)) x ∧
      CycleRelation (RawStep p) y x := by
  obtain ⟨h, hPositive, returned⟩ := yPeriodic
  by_cases zeroSeed : y = 0
  · refine ⟨0, ⟨1, by decide, ?_⟩, ?_⟩
    · simp [RawStep, Iterate]
    · rw [zeroSeed]
      exact CycleRelationRefl (RawStep p) 0
  · obtain ⟨k, kBound, affineGuard⟩ :=
      RawNonzeroReturnHasAffinePhase p h y hPositive returned zeroSeed
    let x := Iterate (RawStep p) k y
    have phaseReturn : Iterate (RawStep p) h x = x :=
      ReturnPeriodPropagates (RawStep p) h k y returned
    obtain ⟨r, _, time, compressedReturn⟩ :=
      CompressionAffineRawReturnBoundary p q c a h qFactor cFactor x affineGuard phaseReturn
    have rPositive : 0 < r := by
      by_contra zeroIndex
      have rZero : r = 0 := by omega
      simp only [rZero, AccumulatedClock] at time
      omega
    refine ⟨x, ⟨r, rPositive, compressedReturn⟩, ⟨⟨k, rfl⟩, ⟨h - k, ?_⟩⟩⟩
    change Iterate (RawStep p) (h - k) (Iterate (RawStep p) k y) = y
    rw [← IterateAdd, Nat.add_sub_of_le (Nat.le_of_lt kBound), returned]

/-- Restrict mutual reachability to periodic points before forming cycle classes. -/
def CycleSetoid {α : Type*} (f : α → α) : Setoid {x : α // PeriodicPoint f x} where
  r x y := CycleRelation f x.val y.val
  iseqv := ⟨fun x => CycleRelationRefl f x.val,
    fun {x y} => CycleRelationSymm f x.val y.val,
    fun {x y z} => CycleRelationTrans f x.val y.val z.val⟩

/-- A cycle class is a periodic orbit with its choice of phase forgotten. -/
def CycleClasses {α : Type*} (f : α → α) := Quotient (CycleSetoid f)

/-- Common-power expansion maps periodic representatives while preserving their integer state. -/
def CompressionPeriodicEmbedding (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) :
    {x : ℤ // PeriodicPoint (RawStep (CompressedParameters p q c)) x} →
      {x : ℤ // PeriodicPoint (RawStep p) x} :=
  fun x => ⟨x.val, CompressionPeriodicPoint p q c a qFactor cFactor x.val x.property⟩

/-- Expansion descends to cycle classes because both chronological paths expand legally. -/
def CompressionCycleMap (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) :
    CycleClasses (RawStep (CompressedParameters p q c)) → CycleClasses (RawStep p) :=
  Quotient.map' (CompressionPeriodicEmbedding p q c a qFactor cFactor)
    (fun x y related =>
      (CompressionCycleRelationIff p q c a qFactor cFactor x.val y.val
        x.property y.property).mp related)

/-- Two compressed cycle classes with one expanded raw class were already equal. -/
theorem CompressionCycleMapInjective (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) :
    Function.Injective (CompressionCycleMap p q c a qFactor cFactor) := by
  intro left right
  refine Quotient.inductionOn₂ left right ?_
  intro x y same
  apply Quotient.sound
  have rawRelated := Quotient.exact same
  exact (CompressionCycleRelationIff p q c a qFactor cFactor x.val y.val
    x.property y.property).mpr rawRelated

/-- Selecting an affine phase or zero recovers every expanded raw cycle class. -/
theorem CompressionCycleMapSurjective (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) :
    Function.Surjective (CompressionCycleMap p q c a qFactor cFactor) := by
  intro rawClass
  refine Quotient.inductionOn rawClass ?_
  intro y
  obtain ⟨x, xPeriodic, related⟩ :=
    CompressionRawCycleRepresentative p q c a qFactor cFactor y.val y.property
  refine ⟨Quotient.mk (CycleSetoid _) ⟨x, xPeriodic⟩, ?_⟩
  apply Quotient.sound
  exact CycleRelationSymm (RawStep p) y.val x related

/-- Common divisor-power time compression is a bijection of periodic cycle classes. -/
theorem CompressionCycleMapBijective (p : Parameters) (q c : ℤ) (a : ℕ)
    (qFactor : p.Q = p.D ^ a * q) (cFactor : p.C = p.D ^ a * c) :
    Function.Bijective (CompressionCycleMap p q c a qFactor cFactor) :=
  ⟨CompressionCycleMapInjective p q c a qFactor cFactor,
    CompressionCycleMapSurjective p q c a qFactor cFactor⟩


end GeneralizedCollatz
