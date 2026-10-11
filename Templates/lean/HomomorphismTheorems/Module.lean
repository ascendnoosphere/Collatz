import Mathlib.LinearAlgebra.Quotient.Basic

/-!
Module homomorphism theorems matching `Templates/tex/Template.tex`.
-/

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Induced map \(\overline{\varphi}:M/\ker\varphi\to\operatorname{im}\varphi\). -/
def ModuleInducedToRange (φ : M →ₗ[R] N) :
    M ⧸ LinearMap.ker φ →ₗ[R] LinearMap.range φ :=
  (LinearMap.ker φ).liftQ φ.rangeRestrict <| by
    intro m hm
    have hm0 : φ m = 0 := hm
    apply Subtype.ext
    show (φ.rangeRestrict m).val = (0 : LinearMap.range φ).val
    simpa using hm0

/-- The induced map sends the class of `m` to `φ m` in the image. -/
theorem ModuleInducedToRangeMk (φ : M →ₗ[R] N) (m : M) :
    ModuleInducedToRange φ (Submodule.Quotient.mk m) =
      φ.rangeRestrict m := by
  rfl

/-- The induced module map is injective. -/
theorem ModuleInducedToRangeInjective (φ : M →ₗ[R] N) :
    Function.Injective (ModuleInducedToRange φ) := by
  apply (LinearMap.ker_eq_bot (f := ModuleInducedToRange φ)).mp
  ext x
  constructor
  · intro hx
    obtain ⟨m, hm⟩ :=
      (Submodule.Quotient.mk_surjective (LinearMap.ker φ)) x
    have hx0 : ModuleInducedToRange φ x = 0 := hx
    have hres : φ.rangeRestrict m = 0 := by
      have : ModuleInducedToRange φ
          (Submodule.Quotient.mk m) = 0 := by
        simpa [hm] using hx0
      simpa [ModuleInducedToRangeMk] using this
    have hφ : φ m = 0 := by
      have hval := congrArg Subtype.val hres
      simpa using hval
    have hmker : m ∈ LinearMap.ker φ := hφ
    have : x = 0 := by
      have hmk :
          (Submodule.Quotient.mk m : M ⧸ LinearMap.ker φ) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr hmker
      simpa [hm] using hmk
    simpa using this
  · intro hx
    have : x = 0 := hx
    simp [this]

/-- The induced module map is surjective onto the image. -/
theorem ModuleInducedToRangeSurjective (φ : M →ₗ[R] N) :
    Function.Surjective (ModuleInducedToRange φ) := by
  intro y
  rcases y with ⟨n, hy⟩
  obtain ⟨m, hm⟩ := LinearMap.mem_range.mp hy
  refine ⟨Submodule.Quotient.mk m, ?_⟩
  apply Subtype.ext
  show (ModuleInducedToRange φ
      (Submodule.Quotient.mk m)).val = n
  have hmk : ModuleInducedToRange φ
      (Submodule.Quotient.mk m) =
      φ.rangeRestrict m := ModuleInducedToRangeMk φ m
  have : (ModuleInducedToRange φ
      (Submodule.Quotient.mk m)).val = φ m := by
    simp [hmk]
  exact this.trans hm

/-- Uniqueness of the induced module isomorphism on cosets. -/
theorem ModuleInducedToRangeUnique (φ : M →ₗ[R] N)
    (ψ : M ⧸ LinearMap.ker φ →ₗ[R] LinearMap.range φ)
    (hψ : ∀ m : M,
      ψ (Submodule.Quotient.mk m) = φ.rangeRestrict m) :
    ψ = ModuleInducedToRange φ := by
  apply LinearMap.ext
  intro x
  obtain ⟨m, hm⟩ :=
    (Submodule.Quotient.mk_surjective (LinearMap.ker φ)) x
  have hx : x = Submodule.Quotient.mk m := hm.symm
  have hψm : ψ (Submodule.Quotient.mk m) =
      φ.rangeRestrict m := hψ m
  have hind : ModuleInducedToRange φ
      (Submodule.Quotient.mk m) =
      φ.rangeRestrict m := ModuleInducedToRangeMk φ m
  have : ψ x = ModuleInducedToRange φ x := by
    simpa [hx] using hψm.trans hind.symm
  exact this

/-- First homomorphism theorem: \(M/\ker\varphi\cong\operatorname{im}\varphi\). -/
noncomputable def ModuleFirstIso (φ : M →ₗ[R] N) :
    (M ⧸ LinearMap.ker φ) ≃ₗ[R] LinearMap.range φ :=
  LinearEquiv.ofBijective (ModuleInducedToRange φ)
    ⟨ModuleInducedToRangeInjective φ,
      ModuleInducedToRangeSurjective φ⟩

/-- First theorem with the image identified with a surjective map's codomain. -/
noncomputable def ModuleFirstIsoSurjective (φ : M →ₗ[R] N)
    (hφ : Function.Surjective φ) : (M ⧸ LinearMap.ker φ) ≃ₗ[R] N := by
  refine (ModuleFirstIso φ).trans
    (LinearEquiv.ofBijective (LinearMap.range φ).subtype ?_)
  constructor
  · exact Subtype.val_injective
  · intro y
    obtain ⟨m, hm⟩ := hφ y
    exact ⟨⟨y, ⟨m, hm⟩⟩, rfl⟩

/-- Restriction of the quotient map of the sum to A. -/
def ModuleSecondMap (A B : Submodule R M) :
    A →ₗ[R] (A ⊔ B : Submodule R M) ⧸ B.comap (A ⊔ B).subtype :=
  (B.comap (A ⊔ B).subtype).mkQ.comp (Submodule.inclusion le_sup_left)

/-- Kernel of the restricted quotient map is the intersection in A. -/
theorem ModuleSecondMapKer (A B : Submodule R M) :
    LinearMap.ker (ModuleSecondMap A B) = B.comap A.subtype := by
  ext x
  constructor
  · intro hx
    have hx0 : ModuleSecondMap A B x = 0 := hx
    have hxB := (Submodule.Quotient.mk_eq_zero (B.comap (A ⊔ B).subtype)).mp hx0
    show (x : M) ∈ B
    exact hxB
  · intro hx
    have hxB : Submodule.inclusion (show A ≤ A ⊔ B from le_sup_left) x ∈
        B.comap (A ⊔ B).subtype := hx
    show ModuleSecondMap A B x = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hxB

/-- Every coset in the sum quotient has a representative in A. -/
theorem ModuleSecondMapSurjective (A B : Submodule R M) :
    Function.Surjective (ModuleSecondMap A B) := by
  intro y
  obtain ⟨m, hm⟩ := (Submodule.Quotient.mk_surjective (B.comap (A ⊔ B).subtype)) y
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp m.property
  let a' : (A ⊔ B : Submodule R M) := ⟨a, (show A ≤ A ⊔ B from le_sup_left) ha⟩
  let b' : (A ⊔ B : Submodule R M) := ⟨b, (show B ≤ A ⊔ B from le_sup_right) hb⟩
  have hsum : a' + b' = m := Subtype.ext hab
  have hb0 : (B.comap (A ⊔ B).subtype).mkQ b' = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hb
  refine ⟨⟨a, ha⟩, ?_⟩
  show (B.comap (A ⊔ B).subtype).mkQ a' = y
  calc
    (B.comap (A ⊔ B).subtype).mkQ a' =
        (B.comap (A ⊔ B).subtype).mkQ (a' + b') := by
      rw [map_add, hb0, add_zero]
    _ = y := by rw [hsum]; exact hm

/-- Second theorem: quotient by the intersection equals the sum quotient. -/
noncomputable def ModuleSecondIso (A B : Submodule R M) :
    (A ⧸ B.comap A.subtype) ≃ₗ[R]
      (A ⊔ B : Submodule R M) ⧸ B.comap (A ⊔ B).subtype :=
  (Submodule.quotEquivOfEq _ _ (ModuleSecondMapKer A B).symm).trans
    (ModuleFirstIsoSurjective (ModuleSecondMap A B) (ModuleSecondMapSurjective A B))

/-- Induced map \(M/N\to M/P\) when \(N\le P\). -/
def ModuleThirdMap (N P : Submodule R M) (hNP : N ≤ P) :
    M ⧸ N →ₗ[R] M ⧸ P :=
  N.liftQ P.mkQ <| by
    intro x hx
    have hxP : x ∈ P := hNP hx
    exact (Submodule.Quotient.mk_eq_zero P).mpr hxP

/-- The third module map is surjective. -/
theorem ModuleThirdMapSurjective (N P : Submodule R M)
    (hNP : N ≤ P) :
    Function.Surjective (ModuleThirdMap N P hNP) := by
  intro y
  obtain ⟨m, hm⟩ := (Submodule.Quotient.mk_surjective P) y
  refine ⟨Submodule.Quotient.mk m, ?_⟩
  have : ModuleThirdMap N P hNP (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk m := by
    rfl
  simpa [hm] using this

/-- Kernel of the third module map is \(P/N\). -/
theorem ModuleThirdMapKer (N P : Submodule R M) (hNP : N ≤ P) :
    LinearMap.ker (ModuleThirdMap N P hNP) = P.map N.mkQ := by
  ext x
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := (Submodule.Quotient.mk_surjective N) x
    have hx0 : ModuleThirdMap N P hNP x = 0 := hx
    have hmk : P.mkQ m = 0 := by
      have : ModuleThirdMap N P hNP
          (Submodule.Quotient.mk m) = 0 := by
        simpa [hm] using hx0
      simpa [ModuleThirdMap] using this
    have hmP : m ∈ P :=
      (Submodule.Quotient.mk_eq_zero P).mp hmk
    refine ⟨m, hmP, hm⟩
  · intro hx
    obtain ⟨m, hmP, hmx⟩ := hx
    have hmk : P.mkQ m = 0 :=
      (Submodule.Quotient.mk_eq_zero P).mpr hmP
    have hthird :
        ModuleThirdMap N P hNP (Submodule.Quotient.mk m) = 0 := by
      simpa [ModuleThirdMap] using hmk
    have : ModuleThirdMap N P hNP x = 0 := by
      have hxeq : x = Submodule.Quotient.mk m := by
        simpa using hmx.symm
      simpa [hxeq] using hthird
    exact this

/-- Third homomorphism theorem: \((M/N)/(P/N)\cong M/P\). -/
noncomputable def ModuleThirdIso (N P : Submodule R M)
    (hNP : N ≤ P) :
    ((M ⧸ N) ⧸ P.map N.mkQ) ≃ₗ[R] M ⧸ P :=
  (Submodule.quotEquivOfEq _ _ (ModuleThirdMapKer N P hNP).symm).trans
    (ModuleFirstIsoSurjective (ModuleThirdMap N P hNP) (ModuleThirdMapSurjective N P hNP))
