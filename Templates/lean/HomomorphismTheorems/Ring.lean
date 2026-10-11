import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
Ring homomorphism theorems matching `Templates/tex/Template.tex`.
-/

variable {R S : Type*} [Ring R] [Ring S]

/-- Induced map \(\overline{\varphi}:R/\ker\varphi\to\operatorname{im}\varphi\). -/
def RingInducedToRange (φ : R →+* S) :
    R ⧸ RingHom.ker φ →+* φ.range :=
  Ideal.Quotient.lift (RingHom.ker φ) φ.rangeRestrict <| by
    intro r hr
    have hr0 : φ r = 0 := hr
    apply Subtype.ext
    show (φ.rangeRestrict r).val = (0 : φ.range).val
    simpa using hr0

/-- The induced map sends the class of `r` to `φ r` in the image. -/
theorem RingInducedToRangeMk (φ : R →+* S) (r : R) :
    RingInducedToRange φ (Ideal.Quotient.mk (RingHom.ker φ) r) =
      φ.rangeRestrict r := by
  rfl

/-- The induced ring map is injective. -/
theorem RingInducedToRangeInjective (φ : R →+* S) :
    Function.Injective (RingInducedToRange φ) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨r, hr⟩ :=
    (Ideal.Quotient.mk_surjective (I := RingHom.ker φ)) x
  have hx0 : RingInducedToRange φ x = 0 := hx
  have hres : φ.rangeRestrict r = 0 := by
    have : RingInducedToRange φ
        (Ideal.Quotient.mk (RingHom.ker φ) r) = 0 := by
      simpa [hr] using hx0
    simpa [RingInducedToRangeMk] using this
  have hφ : φ r = 0 := by
    have hval := congrArg Subtype.val hres
    simpa using hval
  have hrker : r ∈ RingHom.ker φ := hφ
  have : x = 0 := by
    have hmk : Ideal.Quotient.mk (RingHom.ker φ) r = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hrker
    simpa [hr] using hmk
  exact this

/-- The induced ring map is surjective onto the image. -/
theorem RingInducedToRangeSurjective (φ : R →+* S) :
    Function.Surjective (RingInducedToRange φ) := by
  intro y
  rcases y with ⟨s, hy⟩
  obtain ⟨r, hr⟩ := RingHom.mem_range.mp hy
  refine ⟨Ideal.Quotient.mk (RingHom.ker φ) r, ?_⟩
  apply Subtype.ext
  show (RingInducedToRange φ
      (Ideal.Quotient.mk (RingHom.ker φ) r)).val = s
  have hmk : RingInducedToRange φ
      (Ideal.Quotient.mk (RingHom.ker φ) r) =
      φ.rangeRestrict r := RingInducedToRangeMk φ r
  have : (RingInducedToRange φ
      (Ideal.Quotient.mk (RingHom.ker φ) r)).val = φ r := by
    simp [hmk]
  exact this.trans hr

/-- Uniqueness of the induced ring isomorphism on cosets. -/
theorem RingInducedToRangeUnique (φ : R →+* S)
    (ψ : R ⧸ RingHom.ker φ →+* φ.range)
    (hψ : ∀ r : R,
      ψ (Ideal.Quotient.mk (RingHom.ker φ) r) =
        φ.rangeRestrict r) :
    ψ = RingInducedToRange φ := by
  apply RingHom.ext
  intro x
  obtain ⟨r, hr⟩ :=
    (Ideal.Quotient.mk_surjective (I := RingHom.ker φ)) x
  have hx : x = Ideal.Quotient.mk (RingHom.ker φ) r := hr.symm
  have hψr : ψ (Ideal.Quotient.mk (RingHom.ker φ) r) =
      φ.rangeRestrict r := hψ r
  have hind : RingInducedToRange φ
      (Ideal.Quotient.mk (RingHom.ker φ) r) =
      φ.rangeRestrict r := RingInducedToRangeMk φ r
  have : ψ x = RingInducedToRange φ x := by
    simpa [hx] using hψr.trans hind.symm
  exact this

/-- First homomorphism theorem: \(R/\ker\varphi\cong\operatorname{im}\varphi\). -/
noncomputable def RingFirstIso (φ : R →+* S) :
    (R ⧸ RingHom.ker φ) ≃+* φ.range :=
  RingEquiv.ofBijective (RingInducedToRange φ)
    ⟨RingInducedToRangeInjective φ,
      RingInducedToRangeSurjective φ⟩

/-- First theorem with the image identified with a surjective map's codomain. -/
noncomputable def RingFirstIsoSurjective (φ : R →+* S)
    (hφ : Function.Surjective φ) : (R ⧸ RingHom.ker φ) ≃+* S := by
  refine (RingFirstIso φ).trans (RingEquiv.ofBijective φ.range.subtype ?_)
  constructor
  · exact Subtype.val_injective
  · intro y
    obtain ⟨r, hr⟩ := hφ y
    exact ⟨⟨y, ⟨r, hr⟩⟩, rfl⟩

/-- The sum A + I is the preimage of the image of A in R/I. -/
def RingSum (A : Subring R) (I : Ideal R) [I.IsTwoSided] : Subring R :=
  ((Ideal.Quotient.mk I).comp A.subtype).range.comap (Ideal.Quotient.mk I)

/-- Membership in the preimage description is exactly an additive decomposition. -/
theorem RingSumMem (A : Subring R) (I : Ideal R) [I.IsTwoSided] (x : R) :
    x ∈ RingSum A I ↔ ∃ a ∈ A, ∃ i ∈ I, a + i = x := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := hx
    have hi : x - (a : R) ∈ I := Ideal.Quotient.eq.mp ha.symm
    exact ⟨a, a.property, x - a, hi, by rw [add_comm, sub_add_cancel]⟩
  · rintro ⟨a, ha, i, hi, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    show Ideal.Quotient.mk I a = Ideal.Quotient.mk I (a + i)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hi, add_zero]

/-- A embeds in its sum with I by adding zero. -/
theorem RingLeSum (A : Subring R) (I : Ideal R) [I.IsTwoSided] :
    A ≤ RingSum A I := by
  intro a ha
  exact (RingSumMem A I a).mpr ⟨a, ha, 0, I.zero_mem, add_zero a⟩

/-- Restriction of the quotient map of A + I to A. -/
def RingSecondMap (A : Subring R) (I : Ideal R) [I.IsTwoSided] :
    A →+* RingSum A I ⧸ I.comap (RingSum A I).subtype :=
  (Ideal.Quotient.mk (I.comap (RingSum A I).subtype)).comp
    (Subring.inclusion (RingLeSum A I))

/-- Kernel of the restricted quotient map is the intersection in A. -/
theorem RingSecondMapKer (A : Subring R) (I : Ideal R) [I.IsTwoSided] :
    RingHom.ker (RingSecondMap A I) = I.comap A.subtype := by
  ext x
  constructor
  · intro hx
    have hx0 : RingSecondMap A I x = 0 := hx
    have hxI := Ideal.Quotient.eq_zero_iff_mem.mp hx0
    show (x : R) ∈ I
    exact hxI
  · intro hx
    have hxI : Subring.inclusion (RingLeSum A I) x ∈
        I.comap (RingSum A I).subtype := hx
    show RingSecondMap A I x = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxI

/-- Every coset in the sum quotient has a representative in A. -/
theorem RingSecondMapSurjective (A : Subring R) (I : Ideal R) [I.IsTwoSided] :
    Function.Surjective (RingSecondMap A I) := by
  intro y
  obtain ⟨x, hx⟩ := (Ideal.Quotient.mk_surjective
    (I := I.comap (RingSum A I).subtype)) y
  obtain ⟨a, ha, i, hi, hai⟩ := (RingSumMem A I x).mp x.property
  let a' : RingSum A I := Subring.inclusion (RingLeSum A I) ⟨a, ha⟩
  let i' : RingSum A I :=
    ⟨i, (RingSumMem A I i).mpr ⟨0, A.zero_mem, i, hi, zero_add i⟩⟩
  have hsum : a' + i' = x := Subtype.ext hai
  have hi0 : Ideal.Quotient.mk (I.comap (RingSum A I).subtype) i' = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hi
  refine ⟨⟨a, ha⟩, ?_⟩
  show Ideal.Quotient.mk (I.comap (RingSum A I).subtype) a' = y
  calc
    Ideal.Quotient.mk (I.comap (RingSum A I).subtype) a' =
        Ideal.Quotient.mk (I.comap (RingSum A I).subtype) (a' + i') := by
      rw [map_add, hi0, add_zero]
    _ = y := by rw [hsum]; exact hx

/-- Second theorem: quotient by the intersection equals the sum quotient. -/
noncomputable def RingSecondIso (A : Subring R) (I : Ideal R) [I.IsTwoSided] :
    (A ⧸ I.comap A.subtype) ≃+* RingSum A I ⧸ I.comap (RingSum A I).subtype :=
  (Ideal.quotEquivOfEq (RingSecondMapKer A I).symm).trans
    (RingFirstIsoSurjective (RingSecondMap A I) (RingSecondMapSurjective A I))

/-- Induced map \(R/I\to R/J\) when \(I\le J\). -/
def RingThirdMap (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided] (hIJ : I ≤ J) : R ⧸ I →+* R ⧸ J :=
  Ideal.Quotient.lift I (Ideal.Quotient.mk J) <| by
    intro x hx
    have hxJ : x ∈ J := hIJ hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hxJ

/-- The third ring map is surjective. -/
theorem RingThirdMapSurjective (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided] (hIJ : I ≤ J) :
    Function.Surjective (RingThirdMap I J hIJ) := by
  intro y
  obtain ⟨r, hr⟩ := (Ideal.Quotient.mk_surjective (I := J)) y
  refine ⟨Ideal.Quotient.mk I r, ?_⟩
  have : RingThirdMap I J hIJ (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk J r := by
    rfl
  simpa [hr] using this

/-- Kernel of the third ring map is \(J/I\). -/
theorem RingThirdMapKer (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided] (hIJ : I ≤ J) :
    RingHom.ker (RingThirdMap I J hIJ) =
      J.map (Ideal.Quotient.mk I) := by
  ext x
  constructor
  · intro hx
    rw [Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I)
      (Ideal.Quotient.mk_surjective (I := I))]
    obtain ⟨r, hr⟩ :=
      (Ideal.Quotient.mk_surjective (I := I)) x
    have hx0 : RingThirdMap I J hIJ x = 0 := hx
    have hmk : Ideal.Quotient.mk J r = 0 := by
      have : RingThirdMap I J hIJ (Ideal.Quotient.mk I r) = 0 := by
        simpa [hr] using hx0
      simpa [RingThirdMap] using this
    have hrJ : r ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hmk
    exact ⟨r, hrJ, hr⟩
  · intro hx
    rw [Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I)
      (Ideal.Quotient.mk_surjective (I := I))] at hx
    obtain ⟨r, hrJ, hrx⟩ := hx
    have hmk : Ideal.Quotient.mk J r = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hrJ
    have hthird :
        RingThirdMap I J hIJ (Ideal.Quotient.mk I r) = 0 := by
      simpa [RingThirdMap] using hmk
    have : RingThirdMap I J hIJ x = 0 := by
      have hxeq : x = Ideal.Quotient.mk I r := by
        simpa using hrx.symm
      simpa [hxeq] using hthird
    exact this

/-- Third homomorphism theorem: \((R/I)/(J/I)\cong R/J\). -/
noncomputable def RingThirdIso (I J : Ideal R) [I.IsTwoSided] [J.IsTwoSided] (hIJ : I ≤ J) :
    ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃+* R ⧸ J :=
  (Ideal.quotEquivOfEq (RingThirdMapKer I J hIJ).symm).trans
    (RingFirstIsoSurjective (RingThirdMap I J hIJ) (RingThirdMapSurjective I J hIJ))
