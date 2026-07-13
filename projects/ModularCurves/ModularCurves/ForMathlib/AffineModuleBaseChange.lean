import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-!
# Affine base change for quasicoherent modules

On affine spectra, global sections of a pulled-back quasicoherent module are
obtained by extension of scalars. The construction compares the composite
tilde-pullback adjunction with the extension-of-scalars-tilde adjunction.
-/

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def moduleSpecPushforwardΓIso₁
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      (modulesSpecToSheaf ⋙
          TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map φ).base ⋙
            sheafCompose (Opens.grothendieckTopology (Spec R))
              (ModuleCat.restrictScalars φ.hom)) ⋙
        TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
          (evaluation (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
            (op (⊤ : (Spec R).Opens)) := by
  let H := TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
    (evaluation (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
      (op (⊤ : (Spec R).Opens))
  exact (Functor.associator
      (pushforward (Spec.map φ)) modulesSpecToSheaf H).symm ≪≫
    Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ) H

private noncomputable def moduleSpecPushforwardΓIsoApp₂
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (N : (Spec S).Modules) :
    (((modulesSpecToSheaf ⋙
          TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map φ).base ⋙
            sheafCompose (Opens.grothendieckTopology (Spec R))
              (ModuleCat.restrictScalars φ.hom)) ⋙
        TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
          (evaluation (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
            (op (⊤ : (Spec R).Opens))).obj N) ≅
      (moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom).obj N := by
  have htop :
      (Opens.map (Spec.map φ).base).op.obj (op (⊤ : (Spec R).Opens)) =
        op (⊤ : (Spec S).Opens) := by
    simp
  exact (ModuleCat.restrictScalars φ.hom).mapIso
    ((modulesSpecToSheaf.obj N).presheaf.mapIso (eqToIso htop))

private noncomputable def moduleSpecPushforwardΓIso₂
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    (modulesSpecToSheaf ⋙
          TopCat.Sheaf.pushforward (ModuleCat S) (Spec.map φ).base ⋙
            sheafCompose (Opens.grothendieckTopology (Spec R))
              (ModuleCat.restrictScalars φ.hom)) ⋙
        TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
          (evaluation (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
            (op (⊤ : (Spec R).Opens)) ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (moduleSpecPushforwardΓIsoApp₂ φ) (by
    intro M N f
    have htop :
        (Opens.map (Spec.map φ).base).op.obj (op (⊤ : (Spec R).Opens)) =
          op (⊤ : (Spec S).Opens) := by
      simp
    change
      (ModuleCat.restrictScalars φ.hom).map
            ((modulesSpecToSheaf.map f).1.app
              ((Opens.map (Spec.map φ).base).op.obj
                (op (⊤ : (Spec R).Opens)))) ≫
          (ModuleCat.restrictScalars φ.hom).map
            ((modulesSpecToSheaf.obj N).presheaf.map (eqToHom htop)) =
        (ModuleCat.restrictScalars φ.hom).map
              ((modulesSpecToSheaf.obj M).presheaf.map (eqToHom htop)) ≫
          (ModuleCat.restrictScalars φ.hom).map
            ((modulesSpecToSheaf.map f).1.app
              (op (⊤ : (Spec S).Opens)))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (ModuleCat.restrictScalars φ.hom).map
      ((modulesSpecToSheaf.map f).1.naturality (eqToHom htop)).symm)

private noncomputable def moduleSpecPushforwardΓIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  moduleSpecPushforwardΓIso₁ φ ≪≫ moduleSpecPushforwardΓIso₂ φ

private noncomputable def tildePullbackIsoExtendScalars
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde.functor R ⋙ pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S := by
  let adj₁ := (tilde.adjunction (R := R)).comp
    (pullbackPushforwardAdjunction (Spec.map φ))
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
    (tilde.adjunction (R := S))
  exact ((conjugateIsoEquiv adj₁ adj₂).symm
    (moduleSpecPushforwardΓIso φ)).symm

/-- Global sections of a quasicoherent module pulled back along a morphism of
affine spectra are obtained by extension of scalars. -/
noncomputable def specPullbackΓIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec R).Modules)
    [M.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) ≅
      moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M) := by
  letI : IsIso M.fromTildeΓ :=
    isIso_fromTildeΓ_of_isQuasicoherent M
  let A := moduleSpecΓFunctor.obj M
  let e₀ : (ModuleCat.extendScalars φ.hom).obj A ≅
      moduleSpecΓFunctor.obj
        ((tilde.functor S).obj ((ModuleCat.extendScalars φ.hom).obj A)) :=
    tilde.isoTop _
  let e₁ := moduleSpecΓFunctor.mapIso
    ((tildePullbackIsoExtendScalars φ).app A).symm
  let e₂ := moduleSpecΓFunctor.mapIso
    ((pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ))
  exact e₀ ≪≫ e₁ ≪≫ e₂

private theorem extendScalars_toOpen_naturality
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M N : (Spec R).Modules} (f : M ⟶ N) :
    (ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map f) ≫
        tilde.toOpen
          ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj N)) ⊤ =
      tilde.toOpen
            ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M)) ⊤ ≫
        moduleSpecΓFunctor.map
          ((tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map
            (moduleSpecΓFunctor.map f))) := by
  exact (tilde.toOpen_map_app
    ((ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map f))
      (⊤ : (Spec S).Opens)).symm

private theorem tildePullbackIsoExtendScalars_inv_Γ_naturality
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M N : (Spec R).Modules} (f : M ⟶ N) :
    moduleSpecΓFunctor.map
          ((tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map
            (moduleSpecΓFunctor.map f))) ≫
        moduleSpecΓFunctor.map
          ((tildePullbackIsoExtendScalars φ).inv.app
            (moduleSpecΓFunctor.obj N)) =
      moduleSpecΓFunctor.map
          ((tildePullbackIsoExtendScalars φ).inv.app
            (moduleSpecΓFunctor.obj M)) ≫
        moduleSpecΓFunctor.map
          ((pullback (Spec.map φ)).map
            ((tilde.functor R).map (moduleSpecΓFunctor.map f))) := by
  have h := (tildePullbackIsoExtendScalars φ).inv.naturality
    (moduleSpecΓFunctor.map f)
  have h' := congrArg moduleSpecΓFunctor.map h
  simp only [Functor.comp_map, Functor.map_comp] at h'
  exact h'

private theorem fromTildeΓ_pullback_Γ_naturality
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M N : (Spec R).Modules} (f : M ⟶ N) :
    moduleSpecΓFunctor.map
          ((pullback (Spec.map φ)).map
            ((tilde.functor R).map (moduleSpecΓFunctor.map f))) ≫
        moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map N.fromTildeΓ) =
      moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map M.fromTildeΓ) ≫
        moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map f) := by
  have h := (fromTildeΓNatTrans (R := R)).naturality f
  change (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ f at h
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg moduleSpecΓFunctor.map
    (congrArg (pullback (Spec.map φ)).map h)

private noncomputable def extendScalarsTildeΓNatTrans
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    moduleSpecΓFunctor ⋙ ModuleCat.extendScalars φ.hom ⟶
      ((moduleSpecΓFunctor ⋙ ModuleCat.extendScalars φ.hom) ⋙
        tilde.functor S) ⋙ moduleSpecΓFunctor where
  app M :=
    tilde.toOpen
      ((ModuleCat.extendScalars φ.hom).obj
        (moduleSpecΓFunctor.obj M)) ⊤
  naturality {M N} f := by
    change
      (ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map f) ≫
          tilde.toOpen
            ((ModuleCat.extendScalars φ.hom).obj
              (moduleSpecΓFunctor.obj N)) ⊤ =
        tilde.toOpen
              ((ModuleCat.extendScalars φ.hom).obj
                (moduleSpecΓFunctor.obj M)) ⊤ ≫
          moduleSpecΓFunctor.map
            ((tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map
              (moduleSpecΓFunctor.map f)))
    exact extendScalars_toOpen_naturality φ f

private noncomputable def tildePullbackΓNatTrans
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    ((moduleSpecΓFunctor ⋙ ModuleCat.extendScalars φ.hom) ⋙
          tilde.functor S) ⋙ moduleSpecΓFunctor ⟶
      ((moduleSpecΓFunctor ⋙ tilde.functor R) ⋙
          pullback (Spec.map φ)) ⋙ moduleSpecΓFunctor where
  app M := moduleSpecΓFunctor.map
    ((tildePullbackIsoExtendScalars φ).app
      (moduleSpecΓFunctor.obj M)).inv
  naturality {M N} f := by
    change
      moduleSpecΓFunctor.map
            ((tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map
              (moduleSpecΓFunctor.map f))) ≫
          moduleSpecΓFunctor.map
            ((tildePullbackIsoExtendScalars φ).inv.app
              (moduleSpecΓFunctor.obj N)) =
        moduleSpecΓFunctor.map
              ((tildePullbackIsoExtendScalars φ).inv.app
                (moduleSpecΓFunctor.obj M)) ≫
          moduleSpecΓFunctor.map
            ((pullback (Spec.map φ)).map
              ((tilde.functor R).map (moduleSpecΓFunctor.map f)))
    exact tildePullbackIsoExtendScalars_inv_Γ_naturality φ f

private noncomputable def fromTildeΓPullbackΓNatTrans
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    ((moduleSpecΓFunctor ⋙ tilde.functor R) ⋙
          pullback (Spec.map φ)) ⋙ moduleSpecΓFunctor ⟶
      pullback (Spec.map φ) ⋙ moduleSpecΓFunctor where
  app M := moduleSpecΓFunctor.map
    ((pullback (Spec.map φ)).map M.fromTildeΓ)
  naturality {M N} f := by
    change
      moduleSpecΓFunctor.map
            ((pullback (Spec.map φ)).map
              ((tilde.functor R).map (moduleSpecΓFunctor.map f))) ≫
          moduleSpecΓFunctor.map
            ((pullback (Spec.map φ)).map N.fromTildeΓ) =
        moduleSpecΓFunctor.map
              ((pullback (Spec.map φ)).map M.fromTildeΓ) ≫
          moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map f)
    exact fromTildeΓ_pullback_Γ_naturality φ f

private noncomputable def specPullbackΓNatTrans
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    moduleSpecΓFunctor ⋙ ModuleCat.extendScalars φ.hom ⟶
      pullback (Spec.map φ) ⋙ moduleSpecΓFunctor :=
  extendScalarsTildeΓNatTrans φ ≫ tildePullbackΓNatTrans φ ≫
    fromTildeΓPullbackΓNatTrans φ

private theorem specPullbackΓIso_hom
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec R).Modules)
    [M.IsQuasicoherent] :
    (specPullbackΓIso φ M).hom = (specPullbackΓNatTrans φ).app M := by
  rfl

/-- The affine-spectrum pullback comparison is natural in the
quasicoherent module. -/
theorem specPullbackΓIso_naturality
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) :
    (ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map f) ≫
        (specPullbackΓIso φ N).hom =
      (specPullbackΓIso φ M).hom ≫
        moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map f) := by
  rw [specPullbackΓIso_hom, specPullbackΓIso_hom]
  exact (specPullbackΓNatTrans φ).naturality f

end AlgebraicGeometry.Scheme.Modules
