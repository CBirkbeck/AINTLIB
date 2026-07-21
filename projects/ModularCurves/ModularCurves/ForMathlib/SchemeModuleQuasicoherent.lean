import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Localization.Finiteness
import ModularCurves.ForMathlib.SchemeModuleBaseCechBasic
import ModularCurves.ForMathlib.SpecBasicOpenAway

/-!
# Quasicoherent modules on affine schemes

This file records the exact closure and global-section properties of quasicoherent scheme modules
needed for affine sheaf-cohomology vanishing. The proofs use the equivalence between modules and
quasicoherent modules on an affine scheme supplied by `tilde`.
-/

open CategoryTheory Limits Opposite TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Scheme

open Modules

variable {X Y : Scheme.{u}} {R : CommRingCat.{u}}

variable (X) in
/-- Quasicoherence as an object property on scheme modules. -/
abbrev Modules.isQuasicoherent : ObjectProperty X.Modules :=
  SheafOfModules.isQuasicoherent X.ringCatSheaf

@[simp]
lemma Modules.isQuasicoherent_def {M : X.Modules} :
    Modules.isQuasicoherent X M ↔ M.IsQuasicoherent := by
  rfl

instance : (Modules.isQuasicoherent X).IsClosedUnderIsomorphisms :=
  inferInstanceAs
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderIsomorphisms

variable {J : Type w} [Category.{v} J] [HasColimitsOfShape J AddCommGrpCat]

instance : (Modules.isQuasicoherent (Spec R)).IsClosedUnderColimitsOfShape J := by
  change (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderColimitsOfShape J
  rw [← AlgebraicGeometry.essImage_tilde]
  exact
    instIsClosedUnderColimitsOfShapeEssImageOfHasColimitsOfShapeOfPreservesColimitsOfShapeOfFullOfFaithful
      (tilde.functor R)

instance [Finite J] :
    (Modules.isQuasicoherent (Spec R)).IsClosedUnderLimitsOfShape (Discrete J) := by
  change (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderLimitsOfShape
    (Discrete J)
  rw [← AlgebraicGeometry.essImage_tilde]
  exact
    instIsClosedUnderLimitsOfShapeEssImageOfHasLimitsOfShapeOfPreservesLimitsOfShapeOfFullOfFaithful
      (tilde.functor R)

/-- On an affine spectrum, global sections send epimorphisms of quasicoherent modules to
epimorphisms of modules. -/
lemma Modules.moduleSpecΓ_epi_of_epi {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Epi (moduleSpecΓFunctor.map f) := by
  haveI : IsIso M.fromTildeΓ := inferInstance
  haveI : IsIso N.fromTildeΓ := inferInstance
  have hnat : tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f := by
    have h := Scheme.Modules.fromTildeΓNatTrans.naturality f
    change tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f at h
    exact h
  have hright : Epi (M.fromTildeΓ ≫ f) :=
    epi_comp' (by infer_instance) (by infer_instance)
  have hcomp : Epi (tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ) :=
    hnat.symm ▸ hright
  have hmapped : Epi (tilde.map (moduleSpecΓFunctor.map f)) :=
    (epi_comp_iff_of_isIso _ N.fromTildeΓ).mp hcomp
  exact (tilde.functor R).epi_of_epi_map hmapped

/-- On an affine spectrum, an epimorphism of quasicoherent modules is surjective on global
sections. -/
theorem Modules.isQuasicoherent_spec_surjective_of_epi
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op ⊤)).hom :=
  (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map f)).mp
    (Modules.moduleSpecΓ_epi_of_epi f)

noncomputable section

/-- A section of a quasicoherent module on `D(f)` extends globally after multiplication by a
power of `f`. -/
theorem Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R)
    (s : Γ(M, specBasicOpen R f)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)),
      M.presheaf.map (specBasicOpen R f).leTop.op t = f ^ n • s := by
  have hlocal : IsLocalizing (modulesSpecToSheaf.obj M) :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  letI : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj M).obj.map (specBasicOpen R f).leTop.op).hom :=
    hlocal f
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj
    ((modulesSpecToSheaf.obj M).obj.map (specBasicOpen R f).leTop.op).hom f s
  exact ⟨n, t, ht.symm⟩

/-- Finitely many sections of a quasicoherent module on `D(f)` extend globally after
multiplication by one common power of `f`. -/
theorem Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent_finite
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R)
    {ι : Type*} [Finite ι] (s : ι → Γ(M, specBasicOpen R f)) :
    ∃ (n : ℕ) (t : ι → Γ(M, ⊤)), ∀ i,
      M.presheaf.map (specBasicOpen R f).leTop.op (t i) = f ^ n • s i := by
  choose n t ht using fun i ↦
    Modules.exists_restrict_eq_pow_smul_of_isQuasicoherent M f (s i)
  have hle (i : ι) : n i ≤ ⨆ i, n i :=
    le_ciSup (Finite.bddAbove_range n) i
  refine ⟨⨆ i, n i, fun i ↦ f ^ ((⨆ i, n i) - n i) • t i, fun i ↦ ?_⟩
  rw [M.map_smul_Spec, ht i, ← mul_smul, ← pow_add,
    Nat.sub_add_cancel (hle i)]

/-- A quasicoherent module on an affine spectrum with finitely many global generators has a
finite module of global sections. -/
theorem Modules.globalSections_module_finite_of_generatingSections
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (G : M.GeneratingSections) [G.IsFiniteType] :
    Module.Finite R Γ(M, ⊤) := by
  haveI : Finite G.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  let f : SheafOfModules.free G.I ⟶ M := G.π
  letI : Epi f := G.epi
  haveI : Module.Finite R (G.I →₀ R) :=
    Module.finite_finsupp_self_iff.mpr (.inr inferInstance)
  letI : (SheafOfModules.free G.I (R := (Spec R).ringCatSheaf)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (tildeFinsupp G.I) (by infer_instance)
  let e : ModuleCat.of R (G.I →₀ R) ≅
      moduleSpecΓFunctor.obj (SheafOfModules.free G.I) :=
    tilde.isoTop (ModuleCat.of R (G.I →₀ R)) ≪≫
      moduleSpecΓFunctor.mapIso (tildeFinsupp G.I)
  haveI : Module.Finite R
      (moduleSpecΓFunctor.obj (SheafOfModules.free G.I)) :=
    Module.Finite.equiv e.toLinearEquiv
  have hf : Epi f := inferInstance
  have hsurj : Function.Surjective (moduleSpecΓFunctor.map f).hom := by
    have h := @Modules.isQuasicoherent_spec_surjective_of_epi R
      (SheafOfModules.free G.I) M f inferInstance inferInstance hf
    exact h
  exact Module.Finite.of_surjective
    (moduleSpecΓFunctor.map f).hom hsurj

namespace Modules

variable (φ : X ≅ Y)

/-- Pullback of scheme modules along a scheme isomorphism is an equivalence. -/
theorem pullback_isEquivalence_of_iso :
    (pullback φ.hom).IsEquivalence :=
  Functor.IsEquivalence.mk' (pullback φ.inv)
    ((pullbackComp φ.inv φ.hom ≪≫ pullbackCongr φ.inv_hom_id ≪≫ pullbackId Y).symm)
    (pullbackComp φ.hom φ.inv ≪≫ pullbackCongr φ.hom_inv_id ≪≫ pullbackId X)

/-- Restricting along an isomorphism and then along its inverse is naturally the identity. -/
def restrictFunctor_inv_restrictFunctor_hom_id :
    restrictFunctor φ.inv ⋙ restrictFunctor φ.hom ≅ 𝟭 X.Modules :=
  (restrictFunctorComp φ.hom φ.inv).symm ≪≫
    restrictFunctorCongr φ.hom_inv_id ≪≫ restrictFunctorId

instance : (restrictFunctor φ.hom).IsEquivalence :=
  Functor.IsEquivalence.mk' _
    (restrictFunctor_inv_restrictFunctor_hom_id φ.symm).symm
    (restrictFunctor_inv_restrictFunctor_hom_id φ)

/-- Quasicoherence is invariant under restriction along a scheme isomorphism. -/
theorem isQuasicoherent_restrictFunctor_iff {M : Y.Modules} :
    (M.restrict φ.hom).IsQuasicoherent ↔ M.IsQuasicoherent := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  apply ObjectProperty.prop_of_iso _
    ((restrictFunctor_inv_restrictFunctor_hom_id φ.symm).app M)
  simp only [Iso.symm_inv, Iso.symm_hom, Functor.comp_obj]
  infer_instance

/-- Under a scheme isomorphism, quasicoherence is the inverse image of quasicoherence. -/
theorem isQuasicoherent_inverseImage_iso :
    (isQuasicoherent X).inverseImage (restrictFunctor φ.hom) = isQuasicoherent Y := by
  ext M
  simp [isQuasicoherent_restrictFunctor_iff]

instance isQuasicoherent_pushforward_of_iso {φ : X ⟶ Y} [IsIso φ]
    {M : X.Modules} [M.IsQuasicoherent] :
    ((pushforward φ).obj M).IsQuasicoherent := by
  apply (isQuasicoherent_restrictFunctor_iff (asIso φ)).mp
  apply (isQuasicoherent X).prop_of_iso
    ((restrictFunctorAdjCounitIso φ).app M).symm
  change M.IsQuasicoherent
  infer_instance

instance {S T : CommRingCat.{u}} (ψ : S ⟶ T) {M : (Spec T).Modules}
    [M.IsQuasicoherent] :
    ((pushforward (Spec.map ψ)).obj M).IsQuasicoherent := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ] at ⊢
  exact isIso_fromTildeΓ_pushforward ψ M

instance isQuasicoherent_of_pushforward [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  rw [show f = (X.isoSpec.hom ≫ Spec.map (Hom.appTop f)) ≫ Y.isoSpec.inv by
    simp [isoSpec_hom_naturality f]]
  let e := (pushforward X.isoSpec.hom).isoWhiskerLeft
      (pushforwardComp (Spec.map (Hom.appTop f)) Y.isoSpec.inv) ≪≫
    pushforwardComp X.isoSpec.hom (Spec.map (Hom.appTop f) ≫ Y.isoSpec.inv)
  have : ((pushforward X.isoSpec.hom ⋙ pushforward (Spec.map (Hom.appTop f)) ⋙
      pushforward Y.isoSpec.inv).obj M).IsQuasicoherent := by
    simp only [Functor.comp_obj]
    infer_instance
  exact (isQuasicoherent Y).prop_of_iso (e.app M) this

variable [IsAffine X] (F : J ⥤ X.Modules)

instance : (isQuasicoherent X).IsClosedUnderColimitsOfShape J := by
  rw [← isQuasicoherent_inverseImage_iso (isoSpec X).symm]
  exact ObjectProperty.IsClosedUnderColimitsOfShape.inverseImage ..

instance [Finite J] :
    (isQuasicoherent X).IsClosedUnderLimitsOfShape (Discrete J) := by
  rw [← isQuasicoherent_inverseImage_iso (isoSpec X).symm]
  exact ObjectProperty.IsClosedUnderLimitsOfShape.inverseImage ..

end Modules

/-- On an affine scheme, an epimorphism of quasicoherent modules is surjective on global
sections. -/
theorem Modules.isQuasicoherent_surjective_of_epi [IsAffine X]
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op ⊤)).hom := by
  rw [← (isoSpec X).inv.opensRange_of_isIso,
    ← (isoSpec X).inv.image_top_eq_opensRange]
  change Function.Surjective
    (((restrictFunctor (isoSpec X).inv).map f).val.app (op ⊤))
  exact Modules.isQuasicoherent_spec_surjective_of_epi
    ((restrictFunctor (isoSpec X).inv).map f)

/-- The global sections of a finite free sheaf form a finite module. -/
theorem Modules.free_globalSections_module_finite
    (X : Scheme.{u}) (I : Type u) [Finite I] :
    Module.Finite (X.ringCatSheaf.obj.obj (op ⊤))
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj
        (SheafOfModules.free I (R := X.ringCatSheaf))) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let U := fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf
  letI : HasBiproduct U := HasBiproduct.of_hasCoproduct U
  letI : F.Additive := by
    change (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).Additive
    unfold SheafOfModules.evaluation
    infer_instance
  letI : PreservesLimit (Discrete.functor U) F := by
    dsimp [F]
    infer_instance
  letI : PreservesBiproduct U F :=
    preservesBiproduct_of_preservesProduct F
  let e : F.obj (SheafOfModules.free I) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op ⊤))
        (∀ i, F.obj (U i)) :=
    F.mapIso (biproduct.isoCoproduct U).symm ≪≫
      F.mapBiproduct U ≪≫
      biproduct.isoProduct (F.obj ∘ U) ≪≫
      ModuleCat.piIsoPi (F.obj ∘ U)
  have hfinite (i : I) :
      Module.Finite (X.ringCatSheaf.obj.obj (op ⊤)) (F.obj (U i)) := by
    change Module.Finite (X.ringCatSheaf.obj.obj (op ⊤))
      (X.ringCatSheaf.obj.obj (op ⊤))
    infer_instance
  haveI : Module.Finite (X.ringCatSheaf.obj.obj (op ⊤)) (∀ i, F.obj (U i)) :=
    @Module.Finite.pi _ _ I (fun i ↦ F.obj (U i)) inferInstance
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) hfinite
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- A quasicoherent module on an affine scheme with finitely many global generators has a
finite module of global sections. -/
theorem Modules.globalSections_module_finite_of_generatingSections_of_isAffine
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (G : M.GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, ⊤) Γ(M, ⊤) := by
  haveI : Finite G.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  let L : X.Modules := SheafOfModules.free G.I
  let f : L ⟶ M := G.π
  letI : Epi f := G.epi
  letI : L.IsQuasicoherent := inferInstance
  have hL : Module.Finite Γ(X, ⊤) Γ(L, ⊤) := by
    change Module.Finite (X.ringCatSheaf.obj.obj (op ⊤))
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj
        (SheafOfModules.free G.I (R := X.ringCatSheaf)))
    exact Modules.free_globalSections_module_finite X G.I
  letI : Module.Finite Γ(X, ⊤) Γ(L, ⊤) := hL
  have hf : Epi f := inferInstance
  have hsurj : Function.Surjective (f.val.app (op ⊤)).hom := by
    exact @Modules.isQuasicoherent_surjective_of_epi X inferInstance
      L M f inferInstance inferInstance hf
  exact @Module.Finite.of_surjective
    _ _ _ _ _ _ _ _ _ _ _ RingHomSurjective.ids hL
    (f.val.app (op ⊤)).hom hsurj

private theorem Modules.module_finite_restrict_of_over_generators
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) := by
  letI : IsAffine U.toScheme := hU
  let F := (Modules.overEquiv U).functor
  letI : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    (Modules.overEquiv U).toAdjunction.leftAdjoint_preservesColimits
  have hF : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    inferInstance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G F hF (Iso.refl _)
  let G'' := SheafOfModules.GeneratingSections.equivOfIso
    ((Modules.overFunctorEquiv U).app M) G'
  haveI : G''.IsFiniteType := ⟨by
    change Finite G.I
    infer_instance⟩
  exact Modules.globalSections_module_finite_of_generatingSections_of_isAffine
    (M.restrict U.ι) G''

private theorem Modules.module_finite_app_of_over_generators
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, U) Γ(M, U) := by
  have hfinite : Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) :=
    Modules.module_finite_restrict_of_over_generators M U hU G
  let eR' := U.ι.appIso (⊤ : U.toScheme.Opens)
  let eR : Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) ≃+* Γ(U.toScheme, ⊤) :=
    eR'.commRingCatIsoToRingEquiv
  let eM' := M.restrictAppIso U.ι ⊤
  let σ : Γ(U.toScheme, ⊤) →+*
      Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := eR'.inv.hom
  let eM : Γ(M.restrict U.ι, ⊤) →ₛₗ[σ]
      Γ(M, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) :=
    { toFun := eM'.hom
      map_add' := eM'.hom.hom.map_add
      map_smul' := by
        intro r x
        change eM'.hom (r • x) = eR'.inv.hom r • eM'.hom x
        exact Modules.smul_restrictAppIso_hom_apply U.ι M ⊤ r x }
  have hσ : Function.Surjective σ := by
    change Function.Surjective
      (eR.symm : Γ(U.toScheme, ⊤) →+*
        Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)))
    exact eR.symm.surjective
  letI : RingHomSurjective σ := ⟨hσ⟩
  have heM : Function.Bijective eM := by
    change Function.Bijective eM'.hom
    exact ConcreteCategory.bijective_of_isIso eM'.hom
  have htarget : Module.Finite
      Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens))
      Γ(M, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) :=
    (eM.finite_iff_of_bijective heM).mp hfinite
  rw [U.ι_image_top] at htarget
  exact htarget

private theorem Modules.module_finite_app_of_over_generators_of_le
    (M : X.Modules) [M.IsQuasicoherent]
    {U V : X.Opens} (hVU : V ≤ U) (hV : IsAffineOpen V)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, V) Γ(M, V) := by
  let i : V ⟶ U := homOfLE hVU
  let F := SheafOfModules.overMap X.ringCatSheaf i
  letI : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    (SheafOfModules.overMapPushforwardAdj X.ringCatSheaf i).leftAdjoint_preservesColimits
  have hF : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    inferInstance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G F hF
      (SheafOfModules.overMapUnitIso i).symm
  let G'' := SheafOfModules.GeneratingSections.equivOfIso
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app M) G'
  haveI : G''.IsFiniteType := ⟨by
    change Finite G.I
    infer_instance⟩
  exact Modules.module_finite_app_of_over_generators M V hV G''

/-- A finite-type quasicoherent module on an affine spectrum has finite global sections. -/
theorem Modules.globalSections_module_finite_of_isFiniteType
    (M : (Spec R).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R Γ(M, ⊤) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  letI : q.IsFiniteType := hq
  let t : Set R := { f | ∃ i, specBasicOpen R f ≤ q.X i }
  have hqcover : ⨆ i, q.X i = ⊤ := by
    simpa only [IsOpenCover] using
      (Opens.coversTop_iff (T := Spec R) q.X).mp q.coversTop
  have hopen : ⨆ f ∈ t, specBasicOpen R f = ⊤ := by
    apply top_unique
    rw [← hqcover]
    refine iSup_le fun i ↦ ?_
    rintro x hx
    obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx (q.X i).2
    have hle : specBasicOpen R f ≤ ⨆ f ∈ t, specBasicOpen R f :=
      le_iSup_of_le f (le_iSup_of_le (show f ∈ t from ⟨i, hf⟩) le_rfl)
    exact hle hxf
  have ht : Ideal.span t = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hopen
  let φ : (g : t) → Γ(M, ⊤) →ₗ[R] Γ(M, specBasicOpen R g.1) :=
    fun g ↦ ((modulesSpecToSheaf.obj M).obj.map
      (specBasicOpen R g.1).leTop.op).hom
  have hlocal : IsLocalizing (modulesSpecToSheaf.obj M) :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  letI (g : t) : Algebra R Γ(Spec R, specBasicOpen R g.1) :=
    inferInstance
  letI (g : t) : IsLocalization.Away g.1
      Γ(Spec R, specBasicOpen R g.1) := inferInstance
  letI (g : t) : IsScalarTower R
      Γ(Spec R, specBasicOpen R g.1) Γ(M, specBasicOpen R g.1) :=
    inferInstance
  letI : ∀ g : t, IsLocalizedModule.Away g.1 (φ g) :=
    fun g ↦ hlocal g.1
  refine Module.Finite.of_localizationSpan'
    (Mₚ := fun g : t ↦ Γ(M, specBasicOpen R g.1))
    (Rₚ := fun g : t ↦ Γ(Spec R, specBasicOpen R g.1))
    t ht φ ?_
  intro g
  obtain ⟨i, hi⟩ := g.2
  letI : (q.generators i).IsFiniteType := hq.isFiniteType i
  exact Modules.module_finite_app_of_over_generators_of_le M hi
    (IsAffineOpen.Spec_basicOpen g.1) (q.generators i)

private theorem Modules.isLocalizedModuleAway_of_iso_square
    {A : Type u} [CommRing A] {M N M' N' : ModuleCat.{u} A}
    (r : A) (f : M ⟶ N) (g : M' ⟶ N') (eM : M ≅ M') (eN : N ≅ N')
    (hsquare : f ≫ eN.hom = eM.hom ≫ g)
    (hf : IsLocalizedModule.Away r f.hom) :
    IsLocalizedModule.Away r g.hom := by
  have hconj : eM.inv ≫ f ≫ eN.hom = g := by
    rw [hsquare, ← Category.assoc, eM.inv_hom_id, Category.id_comp]
  let f' := f.hom.comp eM.symm.toLinearEquiv.toLinearMap
  letI : IsLocalizedModule.Away r f.hom := hf
  letI : IsLocalizedModule.Away r f' :=
    IsLocalizedModule.of_linearEquiv_right
      (Submonoid.powers r) f.hom eM.symm.toLinearEquiv
  let g' := eN.toLinearEquiv.toLinearMap.comp f'
  letI : IsLocalizedModule.Away r g' :=
    IsLocalizedModule.of_linearEquiv
      (Submonoid.powers r) f' eN.toLinearEquiv
  have hg' : IsLocalizedModule.Away r g' := inferInstance
  convert hg' using 1
  ext x
  exact (ConcreteCategory.congr_hom hconj x).symm

private theorem Modules.baseModulePresheaf_isLocalized_image_of_restrict
    {Y S Z : Scheme.{u}} (π : Y ⟶ S) (j : Z ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) {U V : Z.Opens} (i : op V ⟶ op U)
    (r : Γ(S, ⊤))
    (h : IsLocalizedModule.Away r
      ((baseModulePresheaf (j ≫ π) (M.restrict j)).map i).hom) :
    IsLocalizedModule.Away r
      ((baseModulePresheaf π M).map
        (homOfLE (j.image_mono (leOfHom i.unop))).op).hom := by
  exact Modules.isLocalizedModuleAway_of_iso_square r
    ((baseModulePresheaf (j ≫ π) (M.restrict j)).map i)
    ((baseModulePresheaf π M).map
      (homOfLE (j.image_mono (leOfHom i.unop))).op)
    (Modules.baseModulePresheafRestrictAppIso π j M V)
    (Modules.baseModulePresheafRestrictAppIso π j M U)
    (Modules.baseModulePresheafRestrictAppIso_hom_naturality π j M i)
    h

private theorem Modules.isoSpecInv_isLocalized_basicOpen
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Γ(X, ⊤)) :
    IsLocalizedModule.Away f
      ((baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X)
        (M.restrict X.isoSpec.inv)).map
          (PrimeSpectrum.basicOpen f).leTop.op).hom := by
  let N : (Spec Γ(X, ⊤)).Modules := M.restrict X.isoSpec.inv
  haveI : N.IsQuasicoherent := inferInstance
  have hlocal : IsLocalizing (modulesSpecToSheaf.obj N) :=
    (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance
  have hf := hlocal f
  let ψ := ((baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X) N).map
    (PrimeSpectrum.basicOpen f).leTop.op).hom
  change IsLocalizedModule.Away f ψ
  show IsLocalizedModule.Away f ψ
  ·
    have happ : X.isoSpec.inv.appTop =
        (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).inv := by
      have hhom : X.isoSpec.hom.appTop =
          (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).hom := by
        simp [Scheme.isoSpec, Scheme.toSpecΓ_appTop]
      rw [← cancel_mono (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).hom]
      rw [← hhom]
      rw [← Scheme.Hom.comp_appTop]
      rw [X.isoSpec.hom_inv_id]
      rw [hhom]
      simp
    let e (V : (Spec Γ(X, (⊤ : X.Opens))).Opens) :
        (baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X) N).obj (op V) ≅
          (modulesSpecToSheaf.obj N).obj.obj (op V) := by
      refine ModuleCat.isoMk (Iso.refl _) ?_
      intro r
      ext (x : Γ(N, V))
      change
        (Spec Γ(X, (⊤ : X.Opens))).presheaf.map V.leTop.op
              ((Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).inv r) • x =
          (Spec Γ(X, (⊤ : X.Opens))).presheaf.map V.leTop.op
              (X.isoSpec.inv.appTop r) • x
      rw [happ]
    let φ := ((modulesSpecToSheaf.obj N).obj.map
      (PrimeSpectrum.basicOpen f).leTop.op).hom
    let eTop :=
      (e (⊤ : (Spec Γ(X, (⊤ : X.Opens))).Opens)).toLinearEquiv
    let eBasic := (e (PrimeSpectrum.basicOpen f)).toLinearEquiv
    let g := φ.comp eTop.toLinearMap
    letI : IsLocalizedModule.Away f φ := hf
    letI : IsLocalizedModule.Away f g :=
      IsLocalizedModule.of_linearEquiv_right
        (Submonoid.powers f) φ eTop
    let h := eBasic.symm.toLinearMap.comp g
    letI : IsLocalizedModule.Away f h :=
      IsLocalizedModule.of_linearEquiv
        (Submonoid.powers f) g eBasic.symm
    have hh : IsLocalizedModule.Away f h := inferInstance
    convert hh using 1
    ext x
    rfl

private lemma Modules.isoSpecInv_image_top [IsAffine X] :
    X.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(X, ⊤)).Opens) = ⊤ := by
  rw [Scheme.Hom.inv_image]
  simp

private lemma Modules.isoSpecInv_image_basic [IsAffine X]
    (f : Γ(X, ⊤)) :
    X.isoSpec.inv ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f :=
  (Scheme.Hom.inv_image X.isoSpec (PrimeSpectrum.basicOpen f)).trans
    (Scheme.map_PrimeSpectrum_basicOpen_of_affine X f)

private theorem Modules.isLocalizedModuleAway_map_of_eq
    {A T : Type u} [CommRing A] [TopologicalSpace T]
    (F : (TopologicalSpace.Opens T)ᵒᵖ ⥤ ModuleCat.{u} A)
    {U V U' V' : TopologicalSpace.Opens T}
    (i : op V ⟶ op U) (i' : op V' ⟶ op U')
    (hU : U = U') (hV : V = V') (r : A)
    (h : IsLocalizedModule.Away r (F.map i).hom) :
    IsLocalizedModule.Away r (F.map i').hom := by
  subst U'
  subst V'
  have hi : i' = i := Subsingleton.elim _ _
  subst i'
  exact h

/-- On an affine scheme, restriction of a quasicoherent module to a basic open is localization at
the function defining that open. -/
theorem Modules.baseModulePresheaf_isLocalized_basicOpen
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Γ(X, ⊤)) :
    IsLocalizedModule.Away f
      ((baseModulePresheaf (𝟙 X) M).map
        (X.basicOpen f).leTop.op).hom := by
  let U : (Spec Γ(X, ⊤)).Opens := PrimeSpectrum.basicOpen f
  let i := U.leTop.op
  have hsource : IsLocalizedModule.Away f
      ((baseModulePresheaf (X.isoSpec.inv ≫ 𝟙 X)
        (M.restrict X.isoSpec.inv)).map i).hom := by
    simpa only [i, U] using Modules.isoSpecInv_isLocalized_basicOpen M f
  have himage :=
    Modules.baseModulePresheaf_isLocalized_image_of_restrict
      (π := 𝟙 X) (j := X.isoSpec.inv) (M := M)
      (i := i) (r := f) hsource
  exact Modules.isLocalizedModuleAway_map_of_eq
    (baseModulePresheaf (𝟙 X) M)
    (homOfLE (X.isoSpec.inv.image_mono (leOfHom i.unop))).op
    (X.basicOpen f).leTop.op
    (show X.isoSpec.inv ''ᵁ U = X.basicOpen f by
      simpa only [U] using Modules.isoSpecInv_image_basic f)
    Modules.isoSpecInv_image_top f himage

/-- A finite-type quasicoherent module on an affine scheme has finite global sections. -/
theorem Modules.globalSections_module_finite_of_isFiniteType_of_isAffine
    [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(X, ⊤) Γ(M, ⊤) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  letI : q.IsFiniteType := hq
  let t : Set Γ(X, ⊤) := { f | ∃ i, X.basicOpen f ≤ q.X i }
  have hqcover : ⨆ i, q.X i = ⊤ := by
    simpa only [IsOpenCover] using
      (Opens.coversTop_iff (T := X) q.X).mp q.coversTop
  have hopen : ⨆ f : t, X.basicOpen f.1 = ⊤ := by
    apply top_unique
    calc
      ⊤ = ⨆ i, q.X i := hqcover.symm
      _ ≤ ⨆ f : t, X.basicOpen f.1 := by
        refine iSup_le fun i ↦ ?_
        rintro x hx
        obtain ⟨f, hf, hxf⟩ :=
          (isAffineOpen_top X).exists_basicOpen_le ⟨x, hx⟩ (by simp)
        have hle : X.basicOpen f ≤ ⨆ f : t, X.basicOpen f.1 :=
          le_iSup_of_le ⟨f, i, hf⟩ le_rfl
        exact hle hxf
  have ht : Ideal.span t = ⊤ :=
    (isAffineOpen_top X).iSup_basicOpen_eq_self_iff.mp hopen
  let B := baseModulePresheaf (𝟙 X) M
  letI (g : t) : Algebra Γ(X, ⊤) Γ(X, X.basicOpen g.1) :=
    inferInstance
  letI (g : t) : Module Γ(X, ⊤) Γ(M, X.basicOpen g.1) :=
    Module.compHom _ (algebraMap _ Γ(X, X.basicOpen g.1))
  letI (g : t) : IsLocalization.Away g.1 Γ(X, X.basicOpen g.1) :=
    inferInstance
  letI (g : t) : IsScalarTower Γ(X, ⊤)
      Γ(X, X.basicOpen g.1) Γ(M, X.basicOpen g.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eTop : B.obj (op ⊤) ≅ ModuleCat.of Γ(X, ⊤) Γ(M, ⊤) := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext (x : Γ(M, ⊤))
    change r • x =
      X.presheaf.map
        ((initialOpOfTerminal isTerminalTop).to (op (⊤ : X.Opens)))
          (Scheme.Hom.appTop (𝟙 X) r) • x
    rw [Scheme.Hom.id_appTop]
    rw [Subsingleton.elim
      ((initialOpOfTerminal isTerminalTop).to (op (⊤ : X.Opens))) (𝟙 _)]
    simp
  let eBasic (g : t) :
      B.obj (op (X.basicOpen g.1)) ≅
        ModuleCat.of Γ(X, ⊤) Γ(M, X.basicOpen g.1) := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext (x : Γ(M, X.basicOpen g.1))
    change
      algebraMap Γ(X, ⊤) Γ(X, X.basicOpen g.1) r • x =
        X.presheaf.map
          ((initialOpOfTerminal isTerminalTop).to
            (op (X.basicOpen g.1)))
            (Scheme.Hom.appTop (𝟙 X) r) • x
    rw [Scheme.Hom.id_appTop]
    rfl
  let φCat (g : t) :
      ModuleCat.of Γ(X, ⊤) Γ(M, ⊤) ⟶
        ModuleCat.of Γ(X, ⊤) Γ(M, X.basicOpen g.1) :=
    eTop.inv ≫ B.map (X.basicOpen g.1).leTop.op ≫ (eBasic g).hom
  let φ : (g : t) → Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(M, X.basicOpen g.1) :=
    fun g ↦ (φCat g).hom
  letI : ∀ g : t, IsLocalizedModule.Away g.1 (φ g) := fun g ↦ by
    exact Modules.isLocalizedModuleAway_of_iso_square g.1
      (B.map (X.basicOpen g.1).leTop.op) (φCat g)
      eTop (eBasic g) (by simp [φCat])
      (Modules.baseModulePresheaf_isLocalized_basicOpen M g.1)
  refine Module.Finite.of_localizationSpan'
    (Mₚ := fun g : t ↦ Γ(M, X.basicOpen g.1))
    (Rₚ := fun g : t ↦ Γ(X, X.basicOpen g.1))
    t ht φ ?_
  intro g
  obtain ⟨i, hi⟩ := g.2
  letI : (q.generators i).IsFiniteType := hq.isFiniteType i
  exact Modules.module_finite_app_of_over_generators_of_le M hi
    ((isAffineOpen_top X).basicOpen g.1) (q.generators i)

/-- An epimorphism of quasicoherent modules is surjective on sections over an affine open. -/
theorem Modules.isQuasicoherent_app_surjective_of_epi
    (U : X.Opens) (hU : IsAffineOpen U)
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op U)).hom := by
  letI : IsAffine U.toScheme := hU
  have h := Modules.isQuasicoherent_surjective_of_epi
    ((restrictFunctor U.ι).map f)
  change Function.Surjective
    (f.val.app (op (U.ι ''ᵁ (⊤ : U.toScheme.Opens)))).hom at h
  rw [U.ι_image_top] at h
  exact h

end

end AlgebraicGeometry.Scheme
