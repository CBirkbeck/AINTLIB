import Mathlib.AlgebraicGeometry.Modules.Tilde

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

end

end AlgebraicGeometry.Scheme
