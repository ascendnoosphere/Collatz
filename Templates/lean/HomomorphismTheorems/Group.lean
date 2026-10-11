import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
Group homomorphism theorems matching `Templates/tex/Template.tex`.
-/

variable {G H : Type*} [Group G] [Group H]

/-- Induced map \(\overline{\varphi}:G/\ker\varphi\to\operatorname{im}\varphi\). -/
def InducedToRange (φ : G →* H) : G ⧸ φ.ker →* φ.range :=
  QuotientGroup.lift φ.ker φ.rangeRestrict <| by
    intro x hx
    have hx1 : φ x = 1 := hx
    apply Subtype.ext
    show (φ.rangeRestrict x).val = (1 : φ.range).val
    simpa using hx1

/-- The induced map sends the class of `g` to `φ g` in the image. -/
theorem InducedToRangeMk (φ : G →* H) (g : G) :
    InducedToRange φ (QuotientGroup.mk g) = φ.rangeRestrict g := by
  rfl

/-- The induced map is injective. -/
theorem InducedToRangeInjective (φ : G →* H) :
    Function.Injective (InducedToRange φ) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := (QuotientGroup.mk'_surjective φ.ker) x
    have hx1 : InducedToRange φ x = 1 := hx
    have hxeq : x = QuotientGroup.mk g := hg.symm
    have hxg : InducedToRange φ (QuotientGroup.mk g) = 1 := by
      simpa [hxeq] using hx1
    have hres : φ.rangeRestrict g = 1 := by
      simpa [InducedToRangeMk] using hxg
    have hφ : φ g = 1 := congrArg Subtype.val hres
    have hgker : g ∈ φ.ker := hφ
    have hmk : QuotientGroup.mk g = (1 : G ⧸ φ.ker) :=
      (QuotientGroup.eq_one_iff g).mpr hgker
    have : x = 1 := by
      simpa [hxeq] using hmk
    simp [this]
  · intro hx
    have : x = 1 := hx
    simp [this]

/-- The induced map is surjective onto the image. -/
theorem InducedToRangeSurjective (φ : G →* H) :
    Function.Surjective (InducedToRange φ) := by
  intro y
  rcases y with ⟨h, hy⟩
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hy
  refine ⟨QuotientGroup.mk g, ?_⟩
  apply Subtype.ext
  show (InducedToRange φ (QuotientGroup.mk g)).val = h
  have hmk : InducedToRange φ (QuotientGroup.mk g) =
      φ.rangeRestrict g := InducedToRangeMk φ g
  have : (InducedToRange φ (QuotientGroup.mk g)).val = φ g := by
    simp [hmk]
  exact this.trans hg

/-- Uniqueness of the induced isomorphism on cosets. -/
theorem InducedToRangeUnique (φ : G →* H)
    (ψ : G ⧸ φ.ker →* φ.range)
    (hψ : ∀ g : G, ψ (QuotientGroup.mk g) = φ.rangeRestrict g) :
    ψ = InducedToRange φ := by
  apply MonoidHom.ext
  intro x
  obtain ⟨g, hg⟩ := (QuotientGroup.mk'_surjective φ.ker) x
  have hx : x = QuotientGroup.mk g := by
    simpa using hg.symm
  have hψg : ψ (QuotientGroup.mk g) = φ.rangeRestrict g := hψ g
  have hind : InducedToRange φ (QuotientGroup.mk g) =
      φ.rangeRestrict g := InducedToRangeMk φ g
  have : ψ x = InducedToRange φ x := by
    simpa [hx] using hψg.trans hind.symm
  exact this

/-- First homomorphism theorem: \(G/\ker\varphi\cong\operatorname{im}\varphi\). -/
noncomputable def FirstIso (φ : G →* H) : (G ⧸ φ.ker) ≃* φ.range :=
  MulEquiv.ofBijective (InducedToRange φ)
    ⟨InducedToRangeInjective φ, InducedToRangeSurjective φ⟩

/-- First theorem with the image identified with a surjective map's codomain. -/
noncomputable def FirstIsoSurjective (φ : G →* H) (hφ : Function.Surjective φ) :
    (G ⧸ φ.ker) ≃* H := by
  refine (FirstIso φ).trans (MulEquiv.ofBijective φ.range.subtype ?_)
  constructor
  · exact Subtype.val_injective
  · intro y
    obtain ⟨g, hg⟩ := hφ y
    exact ⟨⟨y, ⟨g, hg⟩⟩, rfl⟩

/-- Restriction of the quotient map of the product subgroup to A. -/
def SecondMap (A N : Subgroup G) [N.Normal] :
    A →* (A ⊔ N : Subgroup G) ⧸ N.subgroupOf (A ⊔ N) :=
  (QuotientGroup.mk' (N.subgroupOf (A ⊔ N))).comp (Subgroup.inclusion le_sup_left)

/-- Kernel of the restricted quotient map is the intersection in A. -/
theorem SecondMapKer (A N : Subgroup G) [N.Normal] :
    (SecondMap A N).ker = N.subgroupOf A := by
  ext x
  constructor
  · intro hx
    have hx1 : SecondMap A N x = 1 := hx
    have hxN :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion le_sup_left x)).mp hx1
    show (x : G) ∈ N
    exact hxN
  · intro hx
    have hxN : Subgroup.inclusion (show A ≤ A ⊔ N from le_sup_left) x ∈
        N.subgroupOf (A ⊔ N) := hx
    show SecondMap A N x = 1
    exact (QuotientGroup.eq_one_iff _).mpr hxN

/-- Every coset in the product quotient has a representative in A. -/
theorem SecondMapSurjective (A N : Subgroup G) [N.Normal] :
    Function.Surjective (SecondMap A N) := by
  intro y
  obtain ⟨g, hg⟩ := (QuotientGroup.mk'_surjective (N.subgroupOf (A ⊔ N))) y
  obtain ⟨a, ha, n, hn, han⟩ := Subgroup.mem_sup_of_normal_right.mp g.property
  let a' : (A ⊔ N : Subgroup G) := ⟨a, (show A ≤ A ⊔ N from le_sup_left) ha⟩
  let n' : (A ⊔ N : Subgroup G) := ⟨n, (show N ≤ A ⊔ N from le_sup_right) hn⟩
  have hprod : a' * n' = g := Subtype.ext han
  have hn1 : QuotientGroup.mk' (N.subgroupOf (A ⊔ N)) n' = 1 :=
    (QuotientGroup.eq_one_iff n').mpr hn
  refine ⟨⟨a, ha⟩, ?_⟩
  show QuotientGroup.mk' (N.subgroupOf (A ⊔ N)) a' = y
  calc
    QuotientGroup.mk' (N.subgroupOf (A ⊔ N)) a' =
        QuotientGroup.mk' (N.subgroupOf (A ⊔ N)) (a' * n') := by
      rw [map_mul, hn1, mul_one]
    _ = y := by rw [hprod]; exact hg

/-- Second theorem: quotient by the intersection equals the product quotient. -/
noncomputable def SecondIso (A N : Subgroup G) [N.Normal] :
    (A ⧸ N.subgroupOf A) ≃* (A ⊔ N : Subgroup G) ⧸ N.subgroupOf (A ⊔ N) :=
  (QuotientGroup.quotientMulEquivOfEq (SecondMapKer A N).symm).trans
    (FirstIsoSurjective (SecondMap A N) (SecondMapSurjective A N))

/-- Induced map \(G/N\to G/M\) when \(N\le M\). -/
def ThirdMap (N M : Subgroup G) [N.Normal] [M.Normal] (hNM : N ≤ M) :
    G ⧸ N →* G ⧸ M :=
  QuotientGroup.lift N (QuotientGroup.mk' M) <| by
    intro x hx
    have hxM : x ∈ M := hNM hx
    have : QuotientGroup.mk' M x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hxM
    exact this

/-- The third map is surjective. -/
theorem ThirdMapSurjective (N M : Subgroup G) [N.Normal] [M.Normal]
    (hNM : N ≤ M) :
    Function.Surjective (ThirdMap N M hNM) := by
  intro y
  obtain ⟨g, hg⟩ := (QuotientGroup.mk'_surjective M) y
  refine ⟨QuotientGroup.mk g, ?_⟩
  have hlift : ThirdMap N M hNM (QuotientGroup.mk g) =
      QuotientGroup.mk' M g := rfl
  have : ThirdMap N M hNM (QuotientGroup.mk g) = y := by
    simpa [hg] using hlift
  exact this

/-- Kernel of the third map is \(M/N\). -/
theorem ThirdMapKer (N M : Subgroup G) [N.Normal] [M.Normal]
    (hNM : N ≤ M) :
    (ThirdMap N M hNM).ker = M.map (QuotientGroup.mk' N) := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := (QuotientGroup.mk'_surjective N) x
    have hx1 : ThirdMap N M hNM x = 1 := hx
    have hxeq : x = QuotientGroup.mk g := hg.symm
    have hmk : QuotientGroup.mk' M g = 1 := by
      have : ThirdMap N M hNM (QuotientGroup.mk g) = 1 := by
        simpa [hxeq] using hx1
      simpa [ThirdMap] using this
    have hgM : g ∈ M := (QuotientGroup.eq_one_iff g).mp hmk
    refine ⟨g, hgM, hg⟩
  · intro hx
    obtain ⟨g, hgM, hgx⟩ := hx
    have hmk : QuotientGroup.mk g = (1 : G ⧸ M) :=
      (QuotientGroup.eq_one_iff g).mpr hgM
    have hthird :
        ThirdMap N M hNM (QuotientGroup.mk g) = 1 := by
      simpa [ThirdMap] using hmk
    have : ThirdMap N M hNM x = 1 := by
      have hxeq : x = QuotientGroup.mk g := by
        simpa using hgx.symm
      simpa [hxeq] using hthird
    exact this

/-- Third homomorphism theorem: \((G/N)/(M/N)\cong G/M\). -/
noncomputable def ThirdIso (N M : Subgroup G) [N.Normal] [M.Normal]
    (hNM : N ≤ M) :
    ((G ⧸ N) ⧸ M.map (QuotientGroup.mk' N)) ≃* G ⧸ M := by
  letI : (M.map (QuotientGroup.mk' N)).Normal := by
    rw [← ThirdMapKer N M hNM]
    infer_instance
  exact (QuotientGroup.quotientMulEquivOfEq (ThirdMapKer N M hNM).symm).trans
    (FirstIsoSurjective (ThirdMap N M hNM) (ThirdMapSurjective N M hNM))
