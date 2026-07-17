import ModularCurves.GroupScheme.PatchKunneth

/-!
# Affine source patches under base change

For an affine open `U` in the source of `f : X ⟶ S`, its inverse image in
`X ×_S T` is canonically the fibre product `U ×_S T`.  When the base and
base-change scheme are affine, its section ring is the corresponding tensor
product.
-/

open CategoryTheory Limits TensorProduct

universe u

namespace AlgebraicGeometry

private noncomputable def isoAppTop {X Y : Scheme.{u}} (e : X ≅ Y) :
    Γ(Y, (⊤ : Y.Opens)) ≅ Γ(X, (⊤ : X.Opens)) where
  hom := e.hom.appTop
  inv := e.inv.appTop
  hom_inv_id := by
    rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]
  inv_hom_id := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, Scheme.Hom.id_appTop]

/-- The inverse image of a source open in a base-changed scheme is the fibre
product of that open with the new base. -/
noncomputable def pullbackPreimageIsoPullbackRestrict
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (U : X.Opens) :
    (pullback.fst f t ⁻¹ᵁ U).toScheme ≅ pullback (U.ι ≫ f) t :=
  (pullbackRestrictIsoRestrict (pullback.fst f t) U).symm ≪≫
    pullbackSymmetry (pullback.fst f t) U.ι ≪≫
      pullbackRightPullbackFstIso f t U.ι

/-- The inverse image of an affine source patch by an affine base change is
affine. -/
theorem IsAffineOpen.preimage_pullback_fst
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) {U : X.Opens}
    (hU : IsAffineOpen U) [IsAffine S] [IsAffine T] :
    IsAffineOpen (pullback.fst f t ⁻¹ᵁ U) := by
  letI : IsAffine U.toScheme := hU
  exact IsAffine.of_isIso
    (pullbackPreimageIsoPullbackRestrict f t U).hom

/-- Sections on the inverse image of an affine source patch are the tensor
product of the patch sections with the new affine base. -/
noncomputable def pullbackPreimageΓIsoTensor
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (U : X.Opens)
    (hU : IsAffineOpen U) [IsAffine S] [IsAffine T] :
    letI : Algebra Γ(S, (⊤ : S.Opens))
        Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
      ((U.ι ≫ f).appTop.hom).toAlgebra
    letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
      t.appTop.hom.toAlgebra
    Γ(pullback f t, pullback.fst f t ⁻¹ᵁ U) ≅
      CommRingCat.of
        (Γ(U.toScheme, (⊤ : U.toScheme.Opens)) ⊗[Γ(S, (⊤ : S.Opens))]
          Γ(T, (⊤ : T.Opens))) := by
  letI : IsAffine U.toScheme := hU
  let e := pullbackPreimageIsoPullbackRestrict f t U
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
    ((U.ι ≫ f).appTop.hom).toAlgebra
  letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
    t.appTop.hom.toAlgebra
  letI : IsIso (affineKunnethΓ (U.ι ≫ f) t rfl rfl) :=
    isIso_affineKunnethΓ (U.ι ≫ f) t rfl rfl
  exact (pullback.fst f t ⁻¹ᵁ U).topIso.symm ≪≫
    (isoAppTop e).symm ≪≫
      asIso (affineKunnethΓ (U.ι ≫ f) t rfl rfl)

/-- The inverse of the affine-patch section isomorphism is the inverse
Kunneth map, followed by transport across the geometric patch isomorphism
and the ambient-open comparison. -/
theorem pullbackPreimageΓIsoTensor_inv
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (U : X.Opens)
    (hU : IsAffineOpen U) [IsAffine S] [IsAffine T] :
    letI : IsAffine U.toScheme := hU
    letI : Algebra Γ(S, (⊤ : S.Opens))
        Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
      ((U.ι ≫ f).appTop.hom).toAlgebra
    letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
      t.appTop.hom.toAlgebra
    letI : IsIso (affineKunnethΓ (U.ι ≫ f) t rfl rfl) :=
      isIso_affineKunnethΓ (U.ι ≫ f) t rfl rfl
    (pullbackPreimageΓIsoTensor f t U hU).inv =
      inv (affineKunnethΓ (U.ι ≫ f) t rfl rfl) ≫
        (pullbackPreimageIsoPullbackRestrict f t U).hom.appTop ≫
          (pullback.fst f t ⁻¹ᵁ U).topIso.hom := by
  letI : IsAffine U.toScheme := hU
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
    ((U.ι ≫ f).appTop.hom).toAlgebra
  letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
    t.appTop.hom.toAlgebra
  letI : IsIso (affineKunnethΓ (U.ι ≫ f) t rfl rfl) :=
    isIso_affineKunnethΓ (U.ι ≫ f) t rfl rfl
  rfl

end AlgebraicGeometry
