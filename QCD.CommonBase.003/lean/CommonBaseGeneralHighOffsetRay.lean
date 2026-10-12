-- SPDX-License-Identifier: CC-BY-4.0
import CommonBaseRebasing

/-!
Phase-bearing normalized events count all forced divisions, without assuming u < v.
Each event is recovered on the same signed raw orbit.
-/

set_option autoImplicit false

namespace GeneralizedCollatz

/-- The phase determines the full forced division run after one affine operation. -/
def WholeBaseGeneralPhaseEvent (p : Parameters) (u v : ℕ) (z : ℕ × ℤ) : ℕ × ℤ :=
  ((z.1 + u) % v, (p.Q * z.2 + p.C) / p.D ^ ((z.1 + u) / v))

/-- The physical event length includes one affine operation and every forced division. -/
def WholeBaseGeneralPhaseClock (u v : ℕ) (z : ℕ × ℤ) : ℕ :=
  1 + (z.1 + u) / v

/-- Exact coefficient division gives the signed residual update at any normalized phase. -/
theorem WholeBaseGeneralPhaseValue (p : Parameters) (t u v a k : ℕ) (s n w : ℤ)
    (tLower : 2 ≤ t) (kBelow : k < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s) (state : n = (t : ℤ) ^ k * w) :
    (WholeBaseGeneralPhaseEvent p u v (k, n)).2 =
      (t : ℤ) ^ ((k + u) % v) * (w + (t : ℤ) ^ (a - u - k) * s) := by
  have baseNonzero : (t : ℤ) ≠ 0 := by omega
  have exponent : k + u + (a - u - k) = a := by omega
  have split := Nat.div_add_mod (k + u) v
  have offsetPower : (t : ℤ) ^ a =
      (t : ℤ) ^ (k + u) * (t : ℤ) ^ (a - u - k) := by
    rw [← pow_add, exponent]
  have splitPower : (t : ℤ) ^ (k + u) =
      (t : ℤ) ^ (v * ((k + u) / v)) * (t : ℤ) ^ ((k + u) % v) := by
    rw [← pow_add, split]
  change (p.Q * n + p.C) / p.D ^ ((k + u) / v) = _
  apply Int.ediv_eq_of_eq_mul_left
    (pow_ne_zero _ (by rw [divisor]; exact pow_ne_zero _ baseNonzero))
  rw [multiplier, offset, state, divisor, ← pow_mul]
  calc
    (t : ℤ) ^ u * ((t : ℤ) ^ k * w) + (t : ℤ) ^ a * s =
        (t : ℤ) ^ (k + u) * (w + (t : ℤ) ^ (a - u - k) * s) := by
      rw [offsetPower, pow_add]
      ring
    _ = (t : ℤ) ^ ((k + u) % v) * (w + (t : ℤ) ^ (a - u - k) * s) *
        (t : ℤ) ^ (v * ((k + u) / v)) := by
      rw [splitPower]
      ring

/-- The computed event stays normalized and is realized by its exact legal raw clock. -/
theorem WholeBaseGeneralPhaseLaw (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (kBelow : k < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s) (atOrder : WholeBaseOrderAt t n k) :
    WholeBaseOrderAt t (WholeBaseGeneralPhaseEvent p u v (k, n)).2 ((k + u) % v) ∧
      (WholeBaseGeneralPhaseEvent p u v (k, n)).2 =
        Iterate (RawStep p) (WholeBaseGeneralPhaseClock u v (k, n)) n := by
  have inputGuard : ¬p.D ∣ n := by
    rw [divisor]
    exact WholeBaseOrderAtPowerNotDivides t k v n tLower kBelow atOrder
  have first : RawStep p n = (t : ℤ) ^ u * n + (t : ℤ) ^ a * s := by
    simp only [RawStep, if_neg inputGuard, multiplier, offset]
  have affineOrder := WholeBaseHighOffsetAffineOrder t u v a k s n
    kBelow highOffset atOrder
  have reconstruction := Nat.div_add_mod (k + u) v
  have quotientOrder := WholeBaseOrderAtPowerQuotient t (k + u)
    (v * ((k + u) / v)) ((t : ℤ) ^ u * n + (t : ℤ) ^ a * s)
    tLower (by omega) affineOrder
  have difference : k + u - v * ((k + u) / v) = (k + u) % v := by omega
  have outputOrder : WholeBaseOrderAt t
      (WholeBaseGeneralPhaseEvent p u v (k, n)).2 ((k + u) % v) := by
    simpa only [WholeBaseGeneralPhaseEvent, divisor, multiplier, offset,
      ← pow_mul, difference] using quotientOrder
  refine ⟨outputOrder, ?_⟩
  rcases affineOrder with ⟨w, affineState, _⟩
  have factored : RawStep p n = p.D ^ ((k + u) / v) *
      ((t : ℤ) ^ ((k + u) % v) * w) := by
    rw [first, affineState, divisor, ← pow_mul, ← mul_assoc, ← pow_add, reconstruction]
  have divided := PowerDivisionRun p ((k + u) / v) ((t : ℤ) ^ ((k + u) % v) * w)
  have output : (WholeBaseGeneralPhaseEvent p u v (k, n)).2 =
      (t : ℤ) ^ ((k + u) % v) * w := by
    change (p.Q * n + p.C) / p.D ^ ((k + u) / v) = _
    have denominatorNonzero : p.D ^ ((k + u) / v) ≠ 0 := by
      rw [divisor]
      exact pow_ne_zero _ (pow_ne_zero _ (by omega : (t : ℤ) ≠ 0))
    apply Int.ediv_eq_of_eq_mul_left denominatorNonzero
    have affine : p.Q * n + p.C = RawStep p n := by
      simp only [RawStep, if_neg inputGuard]
    rw [affine, factored]
    ring
  change (WholeBaseGeneralPhaseEvent p u v (k, n)).2 =
    Iterate (RawStep p) (1 + (k + u) / v) n
  rw [Nat.add_comm 1, ← IterateFirst, factored, divided]
  exact output

/-- Iterated phase-bearing events retain every normalized order witness. -/
theorem WholeBaseGeneralPhaseTrace (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (kBelow : k < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s) (atOrder : WholeBaseOrderAt t n k) :
    ∀ i : ℕ, (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n)).1 =
        (k + i * u) % v ∧
      WholeBaseOrderAt t (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n)).2
        ((k + i * u) % v) := by
  have vPositive : 0 < v := by omega
  intro i
  induction i with
  | zero => {
      constructor
      · simp [Iterate, Nat.mod_eq_of_lt kBelow]
      · simpa [Iterate, Nat.mod_eq_of_lt kBelow] using atOrder
    }
  | succ i ih => {
      have law := WholeBaseGeneralPhaseLaw p t u v a ((k + i * u) % v) s
        (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n)).2 tLower
        (Nat.mod_lt _ vPositive) highOffset divisor multiplier offset ih.2
      have phase : ((k + i * u) % v + u) % v = (k + (i + 1) * u) % v := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1
        ring
      constructor
      · simp only [Iterate, WholeBaseGeneralPhaseEvent, ih.1, phase]
      · simpa only [Iterate, WholeBaseGeneralPhaseEvent, ih.1, phase] using law.1
    }

/-- Every accumulated event endpoint is on the original, not a changed, raw orbit. -/
theorem WholeBaseGeneralPhaseRawIterates (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (kBelow : k < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s) (atOrder : WholeBaseOrderAt t n k) :
    ∀ i : ℕ, (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n)).2 =
      Iterate (RawStep p) (AccumulatedClock (WholeBaseGeneralPhaseEvent p u v)
        (WholeBaseGeneralPhaseClock u v) i (k, n)) n := by
  have vPositive : 0 < v := by omega
  intro i
  induction i with
  | zero => { rfl }
  | succ i ih => {
      have trace := WholeBaseGeneralPhaseTrace p t u v a k s n tLower kBelow
        highOffset divisor multiplier offset atOrder i
      have law := WholeBaseGeneralPhaseLaw p t u v a ((k + i * u) % v) s
        (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n)).2 tLower
        (Nat.mod_lt _ vPositive) highOffset divisor multiplier offset trace.2
      rw [← trace.1] at law
      have legal : (WholeBaseGeneralPhaseEvent p u v
          (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n))).2 =
          Iterate (RawStep p)
            (WholeBaseGeneralPhaseClock u v
              (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n)))
            (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n)).2 := by
        simpa only [Prod.mk.eta] using law.2
      calc
        (Iterate (WholeBaseGeneralPhaseEvent p u v) (i + 1) (k, n)).2 =
            Iterate (RawStep p)
              (WholeBaseGeneralPhaseClock u v
                (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n)))
              (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n)).2 := by
          simpa only [Iterate] using legal
        _ = Iterate (RawStep p)
            (AccumulatedClock (WholeBaseGeneralPhaseEvent p u v)
              (WholeBaseGeneralPhaseClock u v) (i + 1) (k, n)) n := by
          rw [ih, ← IterateAdd]
          rfl
    }

/-- Euclidean wrap counts retain all affine operations and all physical divisions. -/
theorem WholeBaseGeneralPhasePrefixClock (p : Parameters) (t u v a k : ℕ) (s n : ℤ)
    (tLower : 2 ≤ t) (kBelow : k < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s) (atOrder : WholeBaseOrderAt t n k) :
    ∀ i : ℕ, AccumulatedClock (WholeBaseGeneralPhaseEvent p u v)
      (WholeBaseGeneralPhaseClock u v) i (k, n) = i + (k + i * u) / v := by
  have vPositive : 0 < v := by omega
  intro i
  induction i with
  | zero => { simp [AccumulatedClock, Nat.div_eq_of_lt kBelow] }
  | succ i ih => {
      have trace := WholeBaseGeneralPhaseTrace p t u v a k s n tLower kBelow
        highOffset divisor multiplier offset atOrder i
      have clock : WholeBaseGeneralPhaseClock u v
          (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n)) =
          1 + ((k + i * u) % v + u) / v := by
        simp only [WholeBaseGeneralPhaseClock, trace.1]
      have counts := WholeBaseHighOffsetDivisionRecurrence u v k i vPositive
      rw [AccumulatedClock, ih, clock, counts]
      omega
    }

/-- Residual corrections retain their actual phase at every normalized affine event. -/
theorem WholeBaseGeneralPhaseResidualTrace (p : Parameters) (t u v a k : ℕ)
    (s n w : ℤ) (tLower : 2 ≤ t) (kBelow : k < v) (highOffset : u + v ≤ a)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s) (atOrder : WholeBaseOrderAt t n k)
    (state : n = (t : ℤ) ^ k * w) :
    ∀ i : ℕ, (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n)).2 =
      (t : ℤ) ^ ((k + i * u) % v) *
        (w + s * ∑ j ∈ Finset.range i, (t : ℤ) ^ (a - u - (k + j * u) % v)) := by
  have vPositive : 0 < v := by omega
  intro i
  induction i with
  | zero => { simp [Iterate, Nat.mod_eq_of_lt kBelow, state] }
  | succ i ih => {
      have trace := WholeBaseGeneralPhaseTrace p t u v a k s n tLower kBelow
        highOffset divisor multiplier offset atOrder i
      have value := WholeBaseGeneralPhaseValue p t u v a ((k + i * u) % v) s
        (Iterate (WholeBaseGeneralPhaseEvent p u v) i (k, n)).2
        (w + s * ∑ j ∈ Finset.range i, (t : ℤ) ^ (a - u - (k + j * u) % v))
        tLower (Nat.mod_lt _ vPositive) highOffset divisor multiplier offset ih
      have phase : ((k + i * u) % v + u) % v = (k + (i + 1) * u) % v := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1
        ring
      simp only [WholeBaseGeneralPhaseEvent] at value
      simp only [Iterate, WholeBaseGeneralPhaseEvent]
      rw [trace.1, value, phase, Finset.sum_range_succ]
      ring
    }

/-- A complete coprime phase sweep is a translation at exactly u+v raw steps. -/
theorem WholeBaseGeneralHighOffsetRawSweep (p : Parameters) (t u v a k : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (kBelow : k < v) (highOffset : u + v ≤ a)
    (coprime : Nat.Coprime u v) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt t n k) :
    WholeBaseOrderAt t (Iterate (RawStep p) (u + v) n) k ∧
      Iterate (RawStep p) (u + v) n =
        n + s * (t : ℤ) ^ (a - u - v + 1 + k) * WholeBaseGeometricSum t v := by
  have vPositive : 0 < v := by omega
  have phase : (k + v * u) % v = k := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt kBelow]
  have clock := WholeBaseGeneralPhasePrefixClock p t u v a k s n tLower kBelow
    highOffset divisor multiplier offset atOrder v
  rw [Nat.add_mul_div_left k u vPositive, Nat.div_eq_of_lt kBelow] at clock
  have raw := WholeBaseGeneralPhaseRawIterates p t u v a k s n tLower kBelow
    highOffset divisor multiplier offset atOrder v
  rw [clock] at raw
  have rawEndpoint : (Iterate (WholeBaseGeneralPhaseEvent p u v) v (k, n)).2 =
      Iterate (RawStep p) (u + v) n := by simpa only [Nat.add_zero, Nat.add_comm] using raw
  have trace := WholeBaseGeneralPhaseTrace p t u v a k s n tLower kBelow
    highOffset divisor multiplier offset atOrder v
  refine ⟨?_, ?_⟩
  · rw [← rawEndpoint]
    simpa only [phase] using trace.2
  · rcases atOrder with ⟨w, state, guard⟩
    have residual := WholeBaseGeneralPhaseResidualTrace p t u v a k s n w tLower
      kBelow highOffset divisor multiplier offset ⟨w, state, guard⟩ state v
    have kernel : (∑ j ∈ Finset.range v, (t : ℤ) ^ (a - u - (k + j * u) % v)) =
        (t : ℤ) ^ (a - u - (v - 1)) * WholeBaseGeometricSum t v := by
      rw [Finset.sum_range]
      exact WholeBaseHighOffsetPhaseKernel t u v a k vPositive coprime highOffset
    have exponent : k + (a - u - (v - 1)) = a - u - v + 1 + k := by omega
    rw [phase, kernel, rawEndpoint] at residual
    calc
      Iterate (RawStep p) (u + v) n = (t : ℤ) ^ k *
          (w + s * ((t : ℤ) ^ (a - u - (v - 1)) * WholeBaseGeometricSum t v)) := residual
      _ = n + s * (t : ℤ) ^ (a - u - v + 1 + k) * WholeBaseGeometricSum t v := by
        rw [state]
        have product : (t : ℤ) ^ (a - u - v + 1 + k) =
            (t : ℤ) ^ k * (t : ℤ) ^ (a - u - (v - 1)) := by
          rw [← pow_add, exponent]
        rw [product]
        ring

/-- Repeated legal sweeps give the same phase-preserving ray for every raw sweep index. -/
theorem WholeBaseGeneralHighOffsetRawRay (p : Parameters) (t u v a k : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (kBelow : k < v) (highOffset : u + v ≤ a)
    (coprime : Nat.Coprime u v) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt t n k) :
    ∀ j : ℕ, WholeBaseOrderAt t (Iterate (RawStep p) (j * (u + v)) n) k ∧
      Iterate (RawStep p) (j * (u + v)) n =
        n + (j : ℤ) * (s * (t : ℤ) ^ (a - u - v + 1 + k) *
          WholeBaseGeometricSum t v) := by
  intro j
  induction j with
  | zero => { simpa [Iterate] using And.intro atOrder (Eq.refl n) }
  | succ j ih => {
      have sweep := WholeBaseGeneralHighOffsetRawSweep p t u v a k s
        (Iterate (RawStep p) (j * (u + v)) n) tLower kBelow highOffset coprime
        divisor multiplier offset ih.1
      have time : (j + 1) * (u + v) = j * (u + v) + (u + v) := by ring
      constructor
      · simpa only [time, IterateAdd] using sweep.1
      · rw [time, IterateAdd, sweep.2, ih.2, Nat.cast_add, Nat.cast_one]
        ring
    }

/-- Gcd rebasing is admissible without an ordering assumption on the two exponents. -/
theorem WholeBaseGeneralRebasedAdmissible (t u v a : ℕ)
    (tLower : 2 ≤ t) (uPositive : 0 < u) (vPositive : 0 < v)
    (highOffset : u + v ≤ a) :
    2 ≤ t ^ Nat.gcd u v ∧ 0 < u / Nat.gcd u v ∧ 0 < v / Nat.gcd u v ∧
      u / Nat.gcd u v + v / Nat.gcd u v ≤ a / Nat.gcd u v ∧
      Nat.Coprime (u / Nat.gcd u v) (v / Nat.gcd u v) := by
  let g := Nat.gcd u v
  have gPositive : 0 < g := Nat.gcd_pos_of_pos_left v uPositive
  have gLeft : g ∣ u := Nat.gcd_dvd_left u v
  have gRight : g ∣ v := Nat.gcd_dvd_right u v
  have base : 2 ≤ t ^ g := by
    have powers := Nat.pow_le_pow_right (by omega : 0 < t) (show 1 ≤ g by omega)
    have baseBelow : t ≤ t ^ g := by simpa using powers
    exact tLower.trans baseBelow
  have leftPositive : 0 < u / g :=
    Nat.div_pos (Nat.le_of_dvd uPositive gLeft) gPositive
  have rightPositive : 0 < v / g :=
    Nat.div_pos (Nat.le_of_dvd vPositive gRight) gPositive
  have high : u / g + v / g ≤ a / g := by
    apply (Nat.le_div_iff_mul_le gPositive).2
    rw [Nat.add_mul, Nat.div_mul_cancel gLeft, Nat.div_mul_cancel gRight]
    exact highOffset
  exact ⟨base, leftPositive, rightPositive, high, Nat.coprime_div_gcd_div_gcd gPositive⟩

/-- Arbitrary positive exponents have the same exact signed ray after gcd rebasing. -/
theorem WholeBaseGeneralHighOffsetRawRayRebased (p : Parameters) (t u v a k : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (uPositive : 0 < u) (vPositive : 0 < v)
    (highOffset : u + v ≤ a) (kBelow : k < v / Nat.gcd u v)
    (divisor : p.D = (t : ℤ) ^ v) (multiplier : p.Q = (t : ℤ) ^ u)
    (offset : p.C = (t : ℤ) ^ a * s)
    (atOrder : WholeBaseOrderAt (t ^ Nat.gcd u v) n k) (j : ℕ) :
    WholeBaseOrderAt (t ^ Nat.gcd u v)
        (Iterate (RawStep p) (j * (u / Nat.gcd u v + v / Nat.gcd u v)) n) k ∧
      Iterate (RawStep p) (j * (u / Nat.gcd u v + v / Nat.gcd u v)) n =
        n + (j : ℤ) * ((t : ℤ) ^ (a % Nat.gcd u v) * s *
          ((t ^ Nat.gcd u v : ℕ) : ℤ) ^
            (a / Nat.gcd u v - u / Nat.gcd u v - v / Nat.gcd u v + 1 + k) *
          WholeBaseGeometricSum (t ^ Nat.gcd u v) (v / Nat.gcd u v)) := by
  rcases WholeBaseGeneralRebasedAdmissible t u v a tLower uPositive vPositive highOffset
    with ⟨base, _, _, high, coprime⟩
  rcases WholeBaseRebasedCoefficients t u v a s with ⟨left, right, coefficients⟩
  exact WholeBaseGeneralHighOffsetRawRay p (t ^ Nat.gcd u v) (u / Nat.gcd u v)
    (v / Nat.gcd u v) (a / Nat.gcd u v) k ((t : ℤ) ^ (a % Nat.gcd u v) * s) n
    base kBelow high coprime (divisor.trans right) (multiplier.trans left)
    (offset.trans coefficients) atOrder j

/-- Every nonzero signed seed reaches the same physical arithmetic ray after legal divisions. -/
theorem WholeBaseGeneralHighOffsetNormalizeRawRay (p : Parameters) (t u v a : ℕ)
    (s n : ℤ) (tLower : 2 ≤ t) (uPositive : 0 < u) (vPositive : 0 < v)
    (highOffset : u + v ≤ a) (divisor : p.D = (t : ℤ) ^ v)
    (multiplier : p.Q = (t : ℤ) ^ u) (offset : p.C = (t : ℤ) ^ a * s)
    (nNonzero : n ≠ 0) :
    ∃ r k : ℕ, ∃ x : ℤ, r ≤ n.natAbs ∧ k < v / Nat.gcd u v ∧
      Iterate (RawStep p) r n = x ∧ WholeBaseOrderAt (t ^ Nat.gcd u v) x k ∧
      x.natAbs ≤ n.natAbs ∧
      ∀ j : ℕ, Iterate (RawStep p) (r + j *
        (u / Nat.gcd u v + v / Nat.gcd u v)) n =
        x + (j : ℤ) * ((t : ℤ) ^ (a % Nat.gcd u v) * s *
          ((t ^ Nat.gcd u v : ℕ) : ℤ) ^
            (a / Nat.gcd u v - u / Nat.gcd u v - v / Nat.gcd u v + 1 + k) *
          WholeBaseGeometricSum (t ^ Nat.gcd u v) (v / Nat.gcd u v)) := by
  have admissible := WholeBaseGeneralRebasedAdmissible t u v a tLower
    uPositive vPositive highOffset
  have coefficients := WholeBaseRebasedCoefficients t u v a s
  obtain ⟨r, k, x, rBound, kBelow, reached, atOrder, magnitude⟩ :=
    WholeBaseNormalizeRaw p (t ^ Nat.gcd u v) (v / Nat.gcd u v) n
      admissible.1 admissible.2.2.1 (divisor.trans coefficients.2.1) nNonzero
  refine ⟨r, k, x, rBound, kBelow, reached, atOrder, magnitude, ?_⟩
  intro j
  rw [IterateAdd, reached]
  exact (WholeBaseGeneralHighOffsetRawRayRebased p t u v a k s x tLower
    uPositive vPositive highOffset kBelow divisor multiplier offset atOrder j).2

end GeneralizedCollatz
