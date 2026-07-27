import ModularCurves.ForMathlib.AdjunctionUnitIsoTransport
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
          (CategoryTheory.evaluation
            (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
            (op (⊤ : (Spec R).Opens)) := by
  let H := TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
    (CategoryTheory.evaluation
      (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
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
          (CategoryTheory.evaluation
            (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
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
          (CategoryTheory.evaluation
            (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
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
  have hPullback := congrArg (pullback (Spec.map φ)).map h
  have hSections := congrArg moduleSpecΓFunctor.map hPullback
  have hCombineSections :
      moduleSpecΓFunctor.map
          ((pullback (Spec.map φ)).map
            ((tilde.functor R).map (moduleSpecΓFunctor.map f))) ≫
        moduleSpecΓFunctor.map
          ((pullback (Spec.map φ)).map N.fromTildeΓ) =
      moduleSpecΓFunctor.map
        ((pullback (Spec.map φ)).map
            ((tilde.functor R).map (moduleSpecΓFunctor.map f)) ≫
          (pullback (Spec.map φ)).map N.fromTildeΓ) :=
    (moduleSpecΓFunctor.map_comp _ _).symm
  have hCombinePullback :
      moduleSpecΓFunctor.map
        ((pullback (Spec.map φ)).map
            ((tilde.functor R).map (moduleSpecΓFunctor.map f)) ≫
          (pullback (Spec.map φ)).map N.fromTildeΓ) =
      moduleSpecΓFunctor.map
        ((pullback (Spec.map φ)).map
          ((tilde.functor R).map (moduleSpecΓFunctor.map f) ≫
            N.fromTildeΓ)) :=
    congrArg moduleSpecΓFunctor.map
      ((pullback (Spec.map φ)).map_comp _ _).symm
  have hSplitPullback :
      moduleSpecΓFunctor.map
          ((pullback (Spec.map φ)).map (M.fromTildeΓ ≫ f)) =
        moduleSpecΓFunctor.map
          ((pullback (Spec.map φ)).map M.fromTildeΓ ≫
            (pullback (Spec.map φ)).map f) :=
    congrArg moduleSpecΓFunctor.map
      ((pullback (Spec.map φ)).map_comp _ _)
  have hSplitSections :
      moduleSpecΓFunctor.map
          ((pullback (Spec.map φ)).map M.fromTildeΓ ≫
            (pullback (Spec.map φ)).map f) =
        moduleSpecΓFunctor.map
            ((pullback (Spec.map φ)).map M.fromTildeΓ) ≫
          moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map f) :=
    moduleSpecΓFunctor.map_comp _ _
  exact hCombineSections.trans <| hCombinePullback.trans <|
    hSections.trans <| hSplitPullback.trans hSplitSections

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

private noncomputable def affineΓFunctor (X : Scheme.{u}) :
    X.Modules ⥤ ModuleCat.{u} Γ(X, (⊤ : X.Opens)) :=
  toPresheafOfModules X ⋙
    PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : X.Opens)) (Limits.initialOpOfTerminal Limits.isTerminalTop) ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ
      (ModuleCat Γ(X, (⊤ : X.Opens)))).obj
      (op (⊤ : X.Opens))

private noncomputable def affineΓPushforwardIsoSpecApp
    (X : Scheme.{u}) [IsAffine X] (M : X.Modules) :
    (pushforward X.isoSpec.hom ⋙ moduleSpecΓFunctor).obj M ≅
      (affineΓFunctor X).obj M := by
  have htop :
      (Opens.map X.isoSpec.hom.base).op.obj
          (op (⊤ : (Spec Γ(X, (⊤ : X.Opens))).Opens)) =
        op (⊤ : X.Opens) := by
    rfl
  let F := (PresheafOfModules.forgetToPresheafModuleCat
    (op (⊤ : X.Opens)) (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj M.1
  let e₀ : (pushforward X.isoSpec.hom ⋙ moduleSpecΓFunctor).obj M ≅
      F.obj ((Opens.map X.isoSpec.hom.base).op.obj
        (op (⊤ : (Spec Γ(X, (⊤ : X.Opens))).Opens))) := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    change (F.obj ((Opens.map X.isoSpec.hom.base).op.obj
      (op (⊤ : (Spec Γ(X, (⊤ : X.Opens))).Opens)))).smul r =
        ((pushforward X.isoSpec.hom ⋙ moduleSpecΓFunctor).obj M).smul r
    change
      (M.1.obj ((Opens.map X.isoSpec.hom.base).op.obj
        (op (⊤ : (Spec Γ(X, (⊤ : X.Opens))).Opens)))).smul
          ((X.presheaf.map ((Limits.initialOpOfTerminal Limits.isTerminalTop).to
            ((Opens.map X.isoSpec.hom.base).op.obj
              (op (⊤ : (Spec Γ(X, (⊤ : X.Opens))).Opens))))).hom r) =
        (M.1.obj ((Opens.map X.isoSpec.hom.base).op.obj
          (op (⊤ : (Spec Γ(X, (⊤ : X.Opens))).Opens)))).smul
            ((X.isoSpec.hom.app (⊤ : (Spec Γ(X, (⊤ : X.Opens))).Opens)).hom
              ((Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).inv.hom r))
    congr 1
    change
      (X.presheaf.map ((Limits.initialOpOfTerminal Limits.isTerminalTop).to
        (op (⊤ : X.Opens)))).hom r =
        X.isoSpec.hom.appTop.hom
          ((Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).inv.hom r)
    rw [show X.isoSpec.hom.appTop =
      (Scheme.ΓSpecIso Γ(X, (⊤ : X.Opens))).hom from
        Scheme.toSpecΓ_appTop X]
    simp
  exact e₀ ≪≫ F.mapIso (eqToIso htop)

private noncomputable def affineΓPushforwardIsoSpec
    (X : Scheme.{u}) [IsAffine X] :
    pushforward X.isoSpec.hom ⋙ moduleSpecΓFunctor ≅ affineΓFunctor X :=
  NatIso.ofComponents (affineΓPushforwardIsoSpecApp X) (by
    intro M N f
    let FM := (PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : X.Opens)) (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj M.1
    let FN := (PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : X.Opens)) (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj N.1
    have htop :
        (Opens.map X.isoSpec.hom.base).op.obj
            (op (⊤ : (Spec Γ(X, (⊤ : X.Opens))).Opens)) =
          op (⊤ : X.Opens) := by
      rfl
    ext m
    change
      (FN.map (eqToHom htop)).hom
          ((f.app ((X.isoSpec.hom ⁻¹ᵁ
            (⊤ : (Spec Γ(X, (⊤ : X.Opens))).Opens)))).hom m) =
        (f.app (⊤ : X.Opens)).hom
          ((FM.map (eqToHom htop)).hom m)
    exact ConcreteCategory.congr_hom (f.1.naturality (eqToHom htop)).symm m)

private noncomputable def affineTildeFunctor (X : Scheme.{u}) [IsAffine X] :
    ModuleCat.{u} Γ(X, (⊤ : X.Opens)) ⥤ X.Modules :=
  tilde.functor Γ(X, (⊤ : X.Opens)) ⋙ pullback X.isoSpec.hom

private noncomputable def affineTildeAdjunction (X : Scheme.{u}) [IsAffine X] :
    affineTildeFunctor X ⊣ affineΓFunctor X :=
  ((tilde.adjunction (R := Γ(X, (⊤ : X.Opens)))).comp
    (pullbackPushforwardAdjunction X.isoSpec.hom)).ofNatIsoRight
      (affineΓPushforwardIsoSpec X)

private noncomputable def affinePushforwardΓIsoApp
    {X Y : Scheme.{u}} (g : Y ⟶ X) (N : Y.Modules) :
    (pushforward g ⋙ affineΓFunctor X).obj N ≅
      (affineΓFunctor Y ⋙ ModuleCat.restrictScalars g.appTop.hom).obj N := by
  have htop :
      (Opens.map g.base).op.obj (op (⊤ : X.Opens)) =
        op (⊤ : Y.Opens) := by
    rfl
  let F := (PresheafOfModules.forgetToPresheafModuleCat
    (op (⊤ : Y.Opens)) (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj N.1
  let W := (Opens.map g.base).op.obj (op (⊤ : X.Opens))
  let e₀ : (pushforward g ⋙ affineΓFunctor X).obj N ≅
      (ModuleCat.restrictScalars g.appTop.hom).obj (F.obj W) := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    change
      (N.1.obj W).smul
          ((Y.presheaf.map
            ((Limits.initialOpOfTerminal Limits.isTerminalTop).to W)).hom
              (g.appTop.hom r)) =
        (N.1.obj W).smul
          ((g.app (⊤ : X.Opens)).hom
            ((X.presheaf.map
              ((Limits.initialOpOfTerminal Limits.isTerminalTop).to
                (op (⊤ : X.Opens)))).hom r))
    congr 1
    exact (ConcreteCategory.congr_hom
      (g.naturality ((Limits.initialOpOfTerminal Limits.isTerminalTop).to
        (op (⊤ : X.Opens)))) r).symm
  exact e₀ ≪≫ (ModuleCat.restrictScalars g.appTop.hom).mapIso
    (F.mapIso (eqToIso htop))

private noncomputable def affinePushforwardΓIso
    {X Y : Scheme.{u}} (g : Y ⟶ X) :
    pushforward g ⋙ affineΓFunctor X ≅
      affineΓFunctor Y ⋙ ModuleCat.restrictScalars g.appTop.hom :=
  NatIso.ofComponents (affinePushforwardΓIsoApp g) (by
    intro M N f
    let FM := (PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : Y.Opens)) (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj M.1
    let FN := (PresheafOfModules.forgetToPresheafModuleCat
      (op (⊤ : Y.Opens)) (Limits.initialOpOfTerminal Limits.isTerminalTop)).obj N.1
    have htop :
        (Opens.map g.base).op.obj (op (⊤ : X.Opens)) =
          op (⊤ : Y.Opens) := by
      rfl
    ext m
    change
      (FN.map (eqToHom htop)).hom
          ((f.app (g ⁻¹ᵁ (⊤ : X.Opens))).hom m) =
        (f.app (⊤ : Y.Opens)).hom
          ((FM.map (eqToHom htop)).hom m)
    exact ConcreteCategory.congr_hom (f.1.naturality (eqToHom htop)).symm m)

private noncomputable def affineTildePullbackIsoExtendScalars
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : Y ⟶ X) :
    affineTildeFunctor X ⋙ pullback g ≅
      ModuleCat.extendScalars g.appTop.hom ⋙ affineTildeFunctor Y := by
  let adj₁ := (affineTildeAdjunction X).comp
    (pullbackPushforwardAdjunction g)
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj g.appTop.hom).comp
    (affineTildeAdjunction Y)
  exact ((conjugateIsoEquiv adj₁ adj₂).symm
    (affinePushforwardΓIso g)).symm

private theorem isIso_affineTildeAdjunction_counit_app
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] :
    IsIso ((affineTildeAdjunction X).counit.app M) := by
  letI : (pullback X.isoSpec.hom).IsEquivalence :=
    pullback_isEquivalence_of_iso X.isoSpec
  letI : (pushforward X.isoSpec.hom).IsEquivalence :=
    (pullbackPushforwardAdjunction X.isoSpec.hom).isEquivalence_right_of_isEquivalence_left
  letI : IsIso (pullbackPushforwardAdjunction X.isoSpec.hom).counit := by
    infer_instance
  let PM := (pushforward X.isoSpec.hom).obj M
  letI : PM.IsQuasicoherent := by
    dsimp only [PM]
    infer_instance
  letI : IsIso (tilde.adjunction (R := Γ(X, (⊤ : X.Opens))).counit.app PM) := by
    change IsIso PM.fromTildeΓ
    infer_instance
  let adj := (tilde.adjunction (R := Γ(X, (⊤ : X.Opens)))).comp
    (pullbackPushforwardAdjunction X.isoSpec.hom)
  have hAdj : IsIso (adj.counit.app M) := by
    let α := (pullback X.isoSpec.hom).map
      ((tilde.adjunction (R := Γ(X, (⊤ : X.Opens)))).counit.app PM)
    let β := (pullbackPushforwardAdjunction X.isoSpec.hom).counit.app M
    have hα : IsIso α := by
      dsimp only [α]
      infer_instance
    have hβ : IsIso β := by
      dsimp only [β]
      infer_instance
    change IsIso (α ≫ β)
    exact @IsIso.comp_isIso _ _ _ _ _ α β hα hβ
  let α := (affineTildeFunctor X).map ((affineΓPushforwardIsoSpec X).inv.app M)
  have hα : IsIso α := by
    dsimp only [α]
    infer_instance
  change IsIso (α ≫ adj.counit.app M)
  exact @IsIso.comp_isIso _ _ _ _ _ α (adj.counit.app M)
    hα hAdj

private theorem isIso_affineTildeAdjunction_unit_app
    {X : Scheme.{u}} [IsAffine X]
    (A : ModuleCat.{u} Γ(X, (⊤ : X.Opens))) :
    IsIso ((affineTildeAdjunction X).unit.app A) := by
  letI : (pullback X.isoSpec.hom).IsEquivalence :=
    pullback_isEquivalence_of_iso X.isoSpec
  letI : (pushforward X.isoSpec.hom).IsEquivalence :=
    (pullbackPushforwardAdjunction X.isoSpec.hom).isEquivalence_right_of_isEquivalence_left
  letI : IsIso (pullbackPushforwardAdjunction X.isoSpec.hom).unit := by
    infer_instance
  let adj := (tilde.adjunction (R := Γ(X, (⊤ : X.Opens)))).comp
    (pullbackPushforwardAdjunction X.isoSpec.hom)
  have hAdj : IsIso (adj.unit.app A) := by
    let α := (tilde.adjunction (R := Γ(X, (⊤ : X.Opens)))).unit.app A
    let β := moduleSpecΓFunctor.map
      ((pullbackPushforwardAdjunction X.isoSpec.hom).unit.app
        ((tilde.functor Γ(X, (⊤ : X.Opens))).obj A))
    have hα : IsIso α := by
      dsimp only [α]
      infer_instance
    have hβ : IsIso β := by
      dsimp only [β]
      infer_instance
    change IsIso (α ≫ β)
    exact @IsIso.comp_isIso _ _ _ _ _ α β hα hβ
  let α := adj.unit.app A
  let β := (affineΓPushforwardIsoSpec X).hom.app ((affineTildeFunctor X).obj A)
  have hα : IsIso α := hAdj
  have hβ : IsIso β := by
    dsimp only [β]
    infer_instance
  change IsIso (α ≫ β)
  exact @IsIso.comp_isIso _ _ _ _ _ α β hα hβ

/-- Pullback between affine schemes preserves quasicoherent modules. -/
theorem isQuasicoherent_pullback_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : Y ⟶ X)
    (M : X.Modules) [M.IsQuasicoherent] :
    ((pullback g).obj M).IsQuasicoherent := by
  let A := (affineΓFunctor X).obj M
  let B := (ModuleCat.extendScalars g.appTop.hom).obj A
  letI : IsIso ((affineTildeAdjunction X).counit.app M) :=
    isIso_affineTildeAdjunction_counit_app M
  let eTilde := (affineTildePullbackIsoExtendScalars g).app A
  let eCounit := (pullback g).mapIso
    (asIso ((affineTildeAdjunction X).counit.app M))
  let e : (affineTildeFunctor Y).obj B ≅ (pullback g).obj M :=
    eTilde.symm ≪≫ eCounit
  have hTilde : ((affineTildeFunctor Y).obj B).IsQuasicoherent := by
    let Q := (tilde.functor Γ(Y, (⊤ : Y.Opens))).obj B
    letI : Q.IsQuasicoherent := inferInstance
    letI : (Q.restrict Y.isoSpec.hom).IsQuasicoherent := inferInstance
    exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      ((restrictFunctorIsoPullback Y.isoSpec.hom).app Q) inferInstance
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    e hTilde

private noncomputable def affineΓLiteralIso (X : Scheme.{u}) (M : X.Modules) :
    ModuleCat.of Γ(X, (⊤ : X.Opens)) Γ(M, (⊤ : X.Opens)) ≅
      (affineΓFunctor X).obj M := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  change
    (M.1.obj (op (⊤ : X.Opens))).smul
        ((X.presheaf.map
          ((Limits.initialOpOfTerminal Limits.isTerminalTop).to
            (op (⊤ : X.Opens)))).hom r) =
      (M.1.obj (op (⊤ : X.Opens))).smul r
  congr 1
  rw [show (Limits.initialOpOfTerminal Limits.isTerminalTop).to
    (op (⊤ : X.Opens)) = 𝟙 _ from Subsingleton.elim _ _]
  simp
  rfl

/-- The map on top-level sections induced by a morphism of scheme modules,
viewed as a linear map over the top-level ring of functions. -/
noncomputable def affineΓMap {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    ModuleCat.of Γ(X, (⊤ : X.Opens)) Γ(M, (⊤ : X.Opens)) ⟶
      ModuleCat.of Γ(X, (⊤ : X.Opens)) Γ(N, (⊤ : X.Opens)) :=
  (affineΓLiteralIso X M).hom ≫ (affineΓFunctor X).map f ≫
    (affineΓLiteralIso X N).inv

private noncomputable def affineUnitΓNatTrans
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : Y ⟶ X) :
    affineΓFunctor X ⋙ ModuleCat.extendScalars g.appTop.hom ⟶
      ((affineΓFunctor X ⋙ ModuleCat.extendScalars g.appTop.hom) ⋙
        affineTildeFunctor Y) ⋙ affineΓFunctor Y where
  app M := (affineTildeAdjunction Y).unit.app
    ((ModuleCat.extendScalars g.appTop.hom).obj ((affineΓFunctor X).obj M))
  naturality {M N} f := by
    change
      (ModuleCat.extendScalars g.appTop.hom).map ((affineΓFunctor X).map f) ≫
          (affineTildeAdjunction Y).unit.app
            ((ModuleCat.extendScalars g.appTop.hom).obj
              ((affineΓFunctor X).obj N)) =
        (affineTildeAdjunction Y).unit.app
              ((ModuleCat.extendScalars g.appTop.hom).obj
                ((affineΓFunctor X).obj M)) ≫
          (affineΓFunctor Y).map
            ((affineTildeFunctor Y).map
              ((ModuleCat.extendScalars g.appTop.hom).map
                ((affineΓFunctor X).map f)))
    exact (affineTildeAdjunction Y).unit.naturality
      ((ModuleCat.extendScalars g.appTop.hom).map ((affineΓFunctor X).map f))

private theorem affineTildePullbackIso_inv_Γ_naturality
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : Y ⟶ X)
    {M N : X.Modules} (f : M ⟶ N) :
    (affineΓFunctor Y).map
          ((affineTildeFunctor Y).map
            ((ModuleCat.extendScalars g.appTop.hom).map
              ((affineΓFunctor X).map f))) ≫
        (affineΓFunctor Y).map
          ((affineTildePullbackIsoExtendScalars g).inv.app
            ((affineΓFunctor X).obj N)) =
      (affineΓFunctor Y).map
          ((affineTildePullbackIsoExtendScalars g).inv.app
            ((affineΓFunctor X).obj M)) ≫
        (affineΓFunctor Y).map
          ((pullback g).map
            ((affineTildeFunctor X).map ((affineΓFunctor X).map f))) := by
  have h := (affineTildePullbackIsoExtendScalars g).inv.naturality
    ((affineΓFunctor X).map f)
  have h' := congrArg (affineΓFunctor Y).map h
  simp only [Functor.comp_map, Functor.map_comp] at h'
  exact h'

private noncomputable def affineTildePullbackΓNatTrans
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : Y ⟶ X) :
    ((affineΓFunctor X ⋙ ModuleCat.extendScalars g.appTop.hom) ⋙
          affineTildeFunctor Y) ⋙ affineΓFunctor Y ⟶
      ((affineΓFunctor X ⋙ affineTildeFunctor X) ⋙ pullback g) ⋙
        affineΓFunctor Y where
  app M := (affineΓFunctor Y).map
    ((affineTildePullbackIsoExtendScalars g).app
      ((affineΓFunctor X).obj M)).inv
  naturality {M N} f := by
    change
      (affineΓFunctor Y).map
            ((affineTildeFunctor Y).map
              ((ModuleCat.extendScalars g.appTop.hom).map
                ((affineΓFunctor X).map f))) ≫
          (affineΓFunctor Y).map
            ((affineTildePullbackIsoExtendScalars g).inv.app
              ((affineΓFunctor X).obj N)) =
        (affineΓFunctor Y).map
              ((affineTildePullbackIsoExtendScalars g).inv.app
                ((affineΓFunctor X).obj M)) ≫
          (affineΓFunctor Y).map
            ((pullback g).map
              ((affineTildeFunctor X).map ((affineΓFunctor X).map f)))
    exact affineTildePullbackIso_inv_Γ_naturality g f

private theorem affineCounit_pullback_Γ_naturality
    {X Y : Scheme.{u}} [IsAffine X] (g : Y ⟶ X)
    {M N : X.Modules} (f : M ⟶ N) :
    (affineΓFunctor Y).map
          ((pullback g).map
            ((affineTildeFunctor X).map ((affineΓFunctor X).map f))) ≫
        (affineΓFunctor Y).map
          ((pullback g).map ((affineTildeAdjunction X).counit.app N)) =
      (affineΓFunctor Y).map
          ((pullback g).map ((affineTildeAdjunction X).counit.app M)) ≫
        (affineΓFunctor Y).map ((pullback g).map f) := by
  have h := (affineTildeAdjunction X).counit.naturality f
  change
    (affineTildeFunctor X).map ((affineΓFunctor X).map f) ≫
        (affineTildeAdjunction X).counit.app N =
      (affineTildeAdjunction X).counit.app M ≫ f at h
  rw [← Functor.map_comp, ← Functor.map_comp]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (affineΓFunctor Y).map (congrArg (pullback g).map h)

private noncomputable def affineCounitPullbackΓNatTrans
    {X Y : Scheme.{u}} [IsAffine X] (g : Y ⟶ X) :
    ((affineΓFunctor X ⋙ affineTildeFunctor X) ⋙ pullback g) ⋙
          affineΓFunctor Y ⟶
      pullback g ⋙ affineΓFunctor Y where
  app M := (affineΓFunctor Y).map
    ((pullback g).map ((affineTildeAdjunction X).counit.app M))
  naturality {M N} f := by
    change
      (affineΓFunctor Y).map
            ((pullback g).map
              ((affineTildeFunctor X).map ((affineΓFunctor X).map f))) ≫
          (affineΓFunctor Y).map
            ((pullback g).map ((affineTildeAdjunction X).counit.app N)) =
        (affineΓFunctor Y).map
              ((pullback g).map ((affineTildeAdjunction X).counit.app M)) ≫
          (affineΓFunctor Y).map ((pullback g).map f)
    exact affineCounit_pullback_Γ_naturality g f

private noncomputable def affinePullbackΓNatTrans
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : Y ⟶ X) :
    affineΓFunctor X ⋙ ModuleCat.extendScalars g.appTop.hom ⟶
      pullback g ⋙ affineΓFunctor Y :=
  affineUnitΓNatTrans g ≫ affineTildePullbackΓNatTrans g ≫
    affineCounitPullbackΓNatTrans g

private noncomputable def affinePullbackΓCoreIso
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars g.appTop.hom).obj ((affineΓFunctor X).obj M) ≅
      (affineΓFunctor Y).obj ((pullback g).obj M) := by
  let A := (affineΓFunctor X).obj M
  let B := (ModuleCat.extendScalars g.appTop.hom).obj A
  have hCounit : IsIso ((affineTildeAdjunction X).counit.app M) :=
    isIso_affineTildeAdjunction_counit_app M
  have hUnit : IsIso ((affineTildeAdjunction Y).unit.app B) :=
    isIso_affineTildeAdjunction_unit_app B
  let e₀ := @asIso _ _ _ _ ((affineTildeAdjunction Y).unit.app B) hUnit
  let e₂ := @asIso _ _ _ _ ((affineTildeAdjunction X).counit.app M) hCounit
  exact e₀ ≪≫
    (affineΓFunctor Y).mapIso
      ((affineTildePullbackIsoExtendScalars g).app A).symm ≪≫
    (affineΓFunctor Y).mapIso
      ((pullback g).mapIso e₂)

private theorem affinePullbackΓCoreIso_hom
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent] :
    (affinePullbackΓCoreIso g M).hom = (affinePullbackΓNatTrans g).app M := by
  dsimp [affinePullbackΓCoreIso, affinePullbackΓNatTrans,
    affineUnitΓNatTrans, affineTildePullbackΓNatTrans,
    affineCounitPullbackΓNatTrans]
  rfl

private theorem affinePullbackΓCoreIso_naturality
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : Y ⟶ X)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) :
    (ModuleCat.extendScalars g.appTop.hom).map ((affineΓFunctor X).map f) ≫
        (affinePullbackΓCoreIso g N).hom =
      (affinePullbackΓCoreIso g M).hom ≫
        (affineΓFunctor Y).map ((pullback g).map f) := by
  rw [affinePullbackΓCoreIso_hom, affinePullbackΓCoreIso_hom]
  exact (affinePullbackΓNatTrans g).naturality f

/-- On arbitrary affine schemes, top-level sections of a pulled-back
quasicoherent module are obtained by extension of scalars. -/
noncomputable def affinePullbackΓIso
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars g.appTop.hom).obj
        (ModuleCat.of Γ(X, (⊤ : X.Opens)) Γ(M, (⊤ : X.Opens))) ≅
      ModuleCat.of Γ(Y, (⊤ : Y.Opens))
        Γ((pullback g).obj M, (⊤ : Y.Opens)) := by
  exact (ModuleCat.extendScalars g.appTop.hom).mapIso
      (affineΓLiteralIso X M) ≪≫
    affinePullbackΓCoreIso g M ≪≫
      (affineΓLiteralIso Y ((pullback g).obj M)).symm

/-- The top-level section obtained from the pullback-adjunction unit, with
the inverse image of the top open transported back to the top open. -/
noncomputable def affinePullbackUnitTop
    {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    (m : Γ(M, (⊤ : X.Opens))) :
    Γ((pullback g).obj M, (⊤ : Y.Opens)) :=
  ((pullback g).obj M).presheaf.map
      (eqToHom (show (⊤ : Y.Opens) = g ⁻¹ᵁ (⊤ : X.Opens) by simp)).op
    (((pullbackPushforwardAdjunction g).unit.app M).val.app
      (op (⊤ : X.Opens)) m)

private theorem affinePullbackΓCoreIso_hom_comp_unit
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app
          ((affineΓFunctor X).obj M) ≫
        (ModuleCat.restrictScalars g.appTop.hom).map
          (affinePullbackΓCoreIso g M).hom =
      (affineΓFunctor X).map
          ((pullbackPushforwardAdjunction g).unit.app M) ≫
        (affinePushforwardΓIso g).hom.app ((pullback g).obj M) := by
  have h := unit_conjugateEquiv_symm
    ((affineTildeAdjunction X).comp (pullbackPushforwardAdjunction g))
    ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).comp
      (affineTildeAdjunction Y))
    (affinePushforwardΓIso g).hom ((affineΓFunctor X).obj M)
  have hβ : (affineTildePullbackIsoExtendScalars g).inv =
      (conjugateEquiv
        ((affineTildeAdjunction X).comp (pullbackPushforwardAdjunction g))
        ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).comp
          (affineTildeAdjunction Y))).symm
        (affinePushforwardΓIso g).hom := by
    rfl
  have hMate :
      (ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app
            ((affineΓFunctor X).obj M) ≫
          (ModuleCat.restrictScalars g.appTop.hom).map
            ((affineTildeAdjunction Y).unit.app
                ((ModuleCat.extendScalars g.appTop.hom).obj
                  ((affineΓFunctor X).obj M)) ≫
              (affineΓFunctor Y).map
                ((affineTildePullbackIsoExtendScalars g).inv.app
                  ((affineΓFunctor X).obj M))) =
        ((affineTildeAdjunction X).comp
              (pullbackPushforwardAdjunction g)).unit.app
            ((affineΓFunctor X).obj M) ≫
          (affinePushforwardΓIso g).hom.app
            ((affineTildeFunctor X ⋙ pullback g).obj
                  ((affineΓFunctor X).obj M)) := by
    rw [hβ, Functor.map_comp]
    change
      ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).comp
            (affineTildeAdjunction Y)).unit.app
          ((affineΓFunctor X).obj M) ≫
        (affineΓFunctor Y ⋙
          ModuleCat.restrictScalars g.appTop.hom).map
          (((conjugateEquiv
              ((affineTildeAdjunction X).comp
                (pullbackPushforwardAdjunction g))
              ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).comp
                (affineTildeAdjunction Y))).symm
            (affinePushforwardΓIso g).hom).app
              ((affineΓFunctor X).obj M)) =
        ((affineTildeAdjunction X).comp
              (pullbackPushforwardAdjunction g)).unit.app
            ((affineΓFunctor X).obj M) ≫
          (affinePushforwardΓIso g).hom.app
            ((affineTildeFunctor X ⋙ pullback g).obj
              ((affineΓFunctor X).obj M))
    exact h.symm
  rw [affinePullbackΓCoreIso_hom]
  dsimp only [affinePullbackΓNatTrans, affineUnitΓNatTrans,
    affineTildePullbackΓNatTrans, affineCounitPullbackΓNatTrans]
  simp only [NatTrans.comp_app]
  let q := (pullback g).map ((affineTildeAdjunction X).counit.app M)
  have hr := (affinePushforwardΓIso g).hom.naturality q
  have hr' :
      (affinePushforwardΓIso g).hom.app
            ((affineTildeFunctor X ⋙ pullback g).obj
              ((affineΓFunctor X).obj M)) ≫
          (ModuleCat.restrictScalars g.appTop.hom).map
            ((affineΓFunctor Y).map q) =
        (pushforward g ⋙ affineΓFunctor X).map q ≫
          (affinePushforwardΓIso g).hom.app ((pullback g).obj M) := by
    change
      (affinePushforwardΓIso g).hom.app
            ((pullback g).obj
              ((affineΓFunctor X ⋙ affineTildeFunctor X).obj M)) ≫
          (affineΓFunctor Y ⋙
            ModuleCat.restrictScalars g.appTop.hom).map q =
        (pushforward g ⋙ affineΓFunctor X).map q ≫
          (affinePushforwardΓIso g).hom.app
            ((pullback g).obj ((𝟭 X.Modules).obj M))
    exact hr.symm
  have hg := (pullbackPushforwardAdjunction g).unit.naturality
    ((affineTildeAdjunction X).counit.app M)
  have hTri := (affineTildeAdjunction X).right_triangle_components M
  have hg' :
      (pullbackPushforwardAdjunction g).unit.app
            ((affineTildeFunctor X).obj ((affineΓFunctor X).obj M)) ≫
          (pushforward g).map q =
          (affineTildeAdjunction X).counit.app M ≫
          (pullbackPushforwardAdjunction g).unit.app M := by
    dsimp only [q]
    change
      (pullbackPushforwardAdjunction g).unit.app
            ((affineΓFunctor X ⋙ affineTildeFunctor X).obj M) ≫
          (pullback g ⋙ pushforward g).map
            ((affineTildeAdjunction X).counit.app M) =
        (affineTildeAdjunction X).counit.app M ≫
          (pullbackPushforwardAdjunction g).unit.app M
    exact hg.symm
  have hΓg :
      (affineΓFunctor X).map
            ((pullbackPushforwardAdjunction g).unit.app
              ((affineTildeFunctor X).obj ((affineΓFunctor X).obj M))) ≫
          (affineΓFunctor X).map ((pushforward g).map q) =
        (affineΓFunctor X).map
            ((affineTildeAdjunction X).counit.app M) ≫
          (affineΓFunctor X).map
            ((pullbackPushforwardAdjunction g).unit.app M) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (affineΓFunctor X).map hg'
  have hLast :
      ((affineTildeAdjunction X).unit.app
              ((affineΓFunctor X).obj M) ≫
            (affineΓFunctor X).map
              ((affineTildeAdjunction X).counit.app M)) ≫
          (affineΓFunctor X).map
            ((pullbackPushforwardAdjunction g).unit.app M) =
        (affineΓFunctor X).map
          ((pullbackPushforwardAdjunction g).unit.app M) := by
    calc
      _ = 𝟙 ((affineΓFunctor X).obj M) ≫
          (affineΓFunctor X).map
            ((pullbackPushforwardAdjunction g).unit.app M) :=
        congrArg (fun k ↦ k ≫ (affineΓFunctor X).map
          ((pullbackPushforwardAdjunction g).unit.app M)) hTri
      _ = _ := Category.id_comp _
  have hReduce :
      ((affineTildeAdjunction X).comp
            (pullbackPushforwardAdjunction g)).unit.app
          ((affineΓFunctor X).obj M) ≫
        (pushforward g ⋙ affineΓFunctor X).map q =
      (affineΓFunctor X).map
        ((pullbackPushforwardAdjunction g).unit.app M) := by
    rw [Adjunction.comp_unit_app]
    dsimp only [Functor.comp_map]
    let u := (affineTildeAdjunction X).unit.app
      ((affineΓFunctor X).obj M)
    let a := (affineΓFunctor X).map
      ((pullbackPushforwardAdjunction g).unit.app
        ((affineTildeFunctor X).obj ((affineΓFunctor X).obj M)))
    let b := (affineΓFunctor X).map ((pushforward g).map q)
    let c := (affineΓFunctor X).map
      ((affineTildeAdjunction X).counit.app M)
    let d := (affineΓFunctor X).map
      ((pullbackPushforwardAdjunction g).unit.app M)
    have h₁ : (u ≫ a) ≫ b = u ≫ (a ≫ b) :=
      Category.assoc _ _ _
    have h₂ : u ≫ (a ≫ b) = u ≫ (c ≫ d) :=
      congrArg (fun k ↦ u ≫ k) hΓg
    have h₃ : u ≫ (c ≫ d) = (u ≫ c) ≫ d :=
      (Category.assoc _ _ _).symm
    have h₄ : (u ≫ c) ≫ d = d := hLast
    exact h₁.trans (h₂.trans (h₃.trans h₄))
  let uY := (affineTildeAdjunction Y).unit.app
    ((ModuleCat.extendScalars g.appTop.hom).obj
      ((affineΓFunctor X).obj M))
  let vY := (affineΓFunctor Y).map
    ((affineTildePullbackIsoExtendScalars g).inv.app
      ((affineΓFunctor X).obj M))
  let wY := (affineΓFunctor Y).map q
  let R := ModuleCat.restrictScalars g.appTop.hom
  have hSplit : R.map (uY ≫ vY ≫ wY) =
      (R.map uY ≫ R.map vY) ≫ R.map wY := by
    calc
      R.map (uY ≫ vY ≫ wY) =
          R.map uY ≫ R.map (vY ≫ wY) := R.map_comp _ _
      _ = R.map uY ≫ (R.map vY ≫ R.map wY) :=
        congrArg (fun k ↦ R.map uY ≫ k) (R.map_comp _ _)
      _ = (R.map uY ≫ R.map vY) ≫ R.map wY :=
        (Category.assoc _ _ _).symm
  calc
    _ = ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app
            ((affineΓFunctor X).obj M) ≫
          (ModuleCat.restrictScalars g.appTop.hom).map
            ((affineTildeAdjunction Y).unit.app
                ((ModuleCat.extendScalars g.appTop.hom).obj
                  ((affineΓFunctor X).obj M)) ≫
              (affineΓFunctor Y).map
                ((affineTildePullbackIsoExtendScalars g).inv.app
                  ((affineΓFunctor X).obj M)))) ≫
        (ModuleCat.restrictScalars g.appTop.hom).map
          ((affineΓFunctor Y).map q) := by
      change
        (ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app
              ((affineΓFunctor X).obj M) ≫
            R.map (uY ≫ vY ≫ wY) =
          (ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app
              ((affineΓFunctor X).obj M) ≫
            ((R.map uY ≫ R.map vY) ≫ R.map wY)
      exact congrArg (fun k ↦
        (ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app
          ((affineΓFunctor X).obj M) ≫ k) hSplit
    _ = (((affineTildeAdjunction X).comp
              (pullbackPushforwardAdjunction g)).unit.app
            ((affineΓFunctor X).obj M) ≫
          (affinePushforwardΓIso g).hom.app
            ((affineTildeFunctor X ⋙ pullback g).obj
              ((affineΓFunctor X).obj M))) ≫
        (ModuleCat.restrictScalars g.appTop.hom).map
          ((affineΓFunctor Y).map q) :=
      congrArg (fun k ↦ k ≫
        (ModuleCat.restrictScalars g.appTop.hom).map
          ((affineΓFunctor Y).map q)) hMate
    _ = ((affineTildeAdjunction X).comp
            (pullbackPushforwardAdjunction g)).unit.app
          ((affineΓFunctor X).obj M) ≫
        ((pushforward g ⋙ affineΓFunctor X).map q ≫
          (affinePushforwardΓIso g).hom.app ((pullback g).obj M)) := by
      exact congrArg (fun k ↦
        ((affineTildeAdjunction X).comp
          (pullbackPushforwardAdjunction g)).unit.app
            ((affineΓFunctor X).obj M) ≫ k) hr'
    _ = (((affineTildeAdjunction X).comp
              (pullbackPushforwardAdjunction g)).unit.app
            ((affineΓFunctor X).obj M) ≫
          (pushforward g ⋙ affineΓFunctor X).map q) ≫
        (affinePushforwardΓIso g).hom.app ((pullback g).obj M) := by
      rw [Category.assoc]
    _ = _ := by
      exact congrArg (fun k ↦ k ≫
        (affinePushforwardΓIso g).hom.app ((pullback g).obj M)) hReduce

/-- The affine pullback comparison sends a pure tensor with coefficient one
to the section supplied by the pullback-adjunction unit. -/
theorem affinePullbackΓIso_hom_one_tmul
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent]
    (m : Γ(M, (⊤ : X.Opens))) :
    (affinePullbackΓIso g M).hom
        ((1 : Γ(Y, (⊤ : Y.Opens))) ⊗ₜ[Γ(X, (⊤ : X.Opens))] m) =
      affinePullbackUnitTop g M m := by
  have h := ConcreteCategory.congr_hom
    (affinePullbackΓCoreIso_hom_comp_unit g M) m
  exact h

/-- The arbitrary-affine pullback comparison is natural in the quasicoherent
module. -/
theorem affinePullbackΓIso_naturality
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : Y ⟶ X)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) :
    (ModuleCat.extendScalars g.appTop.hom).map (affineΓMap f) ≫
        (affinePullbackΓIso g N).hom =
      (affinePullbackΓIso g M).hom ≫ affineΓMap ((pullback g).map f) := by
  dsimp only [affinePullbackΓIso, affineΓMap]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  simp
  have h := congrArg (fun k =>
    (ModuleCat.extendScalars g.appTop.hom).map
          (affineΓLiteralIso X M).hom ≫
      k ≫ (affineΓLiteralIso Y ((pullback g).obj N)).inv)
    (affinePullbackΓCoreIso_naturality g f)
  simpa only [Category.assoc] using h

/-- On affine schemes, invertibility of the extension-of-scalars unit on
global sections implies invertibility of the geometric pullback unit. -/
theorem isIso_pullbackPushforward_unit_of_isAffine_of_isIso_extendScalars_unit
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent]
    [IsIso ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app
      (ModuleCat.of Γ(X, (⊤ : X.Opens)) Γ(M, (⊤ : X.Opens))))] :
    IsIso ((pullbackPushforwardAdjunction g).unit.app M) := by
  haveI hPullback : ((pullback g).obj M).IsQuasicoherent :=
    isQuasicoherent_pullback_of_isAffine g M
  haveI hPushforward :
      ((pushforward g).obj ((pullback g).obj M)).IsQuasicoherent :=
    isQuasicoherent_of_pushforward g ((pullback g).obj M)
  letI hSource : ((𝟭 X.Modules).obj M).IsQuasicoherent := by
    change M.IsQuasicoherent
    infer_instance
  letI hTarget :
      ((pullback g ⋙ pushforward g).obj M).IsQuasicoherent := by
    change ((pushforward g).obj ((pullback g).obj M)).IsQuasicoherent
    exact hPushforward
  haveI hAlgebraic :
      IsIso ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app
        ((affineΓFunctor X).obj M)) :=
    NatTrans.isIso_app_of_iso
      (ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit
      (affineΓLiteralIso X M).symm
  haveI hComposite :
      IsIso ((affineΓFunctor X).map
          ((pullbackPushforwardAdjunction g).unit.app M) ≫
        (affinePushforwardΓIso g).hom.app ((pullback g).obj M)) := by
    rw [← affinePullbackΓCoreIso_hom_comp_unit g M]
    infer_instance
  haveI hMapped :
      IsIso ((affineΓFunctor X).map
        ((pullbackPushforwardAdjunction g).unit.app M)) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _
      ((affineΓFunctor X).map
        ((pullbackPushforwardAdjunction g).unit.app M))
      ((affinePushforwardΓIso g).hom.app ((pullback g).obj M))
      (inferInstanceAs
        (IsIso ((affinePushforwardΓIso g).hom.app ((pullback g).obj M))))
      hComposite
  apply isIso_of_isQuasicoherent_of_isIso_app_top
  change IsIso (affineΓMap
    ((pullbackPushforwardAdjunction g).unit.app M))
  dsimp only [affineΓMap]
  infer_instance

/-- For a tilde sheaf on an affine spectrum, an invertible extension-of-scalars
unit implies that the geometric pullback unit is invertible. -/
theorem isIso_pullbackPushforward_unit_tilde_of_isIso_extendScalars_unit
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R)
    [IsIso ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M)] :
    IsIso ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)) := by
  let adj₁ := (tilde.adjunction (R := R)).comp
    (pullbackPushforwardAdjunction (Spec.map φ))
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
    (tilde.adjunction (R := S))
  haveI hAdj₂ : IsIso (adj₂.unit.app M) := by
    dsimp only [adj₂]
    rw [Adjunction.comp_unit_app]
    infer_instance
  haveI hAdj₁ : IsIso (adj₁.unit.app M) :=
    Adjunction.isIso_unit_app_of_natIso_left
      adj₁ adj₂ (tildePullbackIsoExtendScalars φ).symm M
  haveI hComposite :
      IsIso ((tilde.adjunction (R := R)).unit.app M ≫
        moduleSpecΓFunctor.map
          ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M))) := by
    exact hAdj₁
  haveI hMapped :
      IsIso (moduleSpecΓFunctor.map
        ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M))) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _
      ((tilde.adjunction (R := R)).unit.app M)
      (moduleSpecΓFunctor.map
        ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)))
      (inferInstanceAs (IsIso ((tilde.adjunction (R := R)).unit.app M)))
      hComposite
  haveI hPullback :
      ((pullback (Spec.map φ)).obj (tilde M)).IsQuasicoherent :=
    isQuasicoherent_pullback_of_isAffine (Spec.map φ) (tilde M)
  haveI hPushforward :
      ((pushforward (Spec.map φ)).obj
        ((pullback (Spec.map φ)).obj (tilde M))).IsQuasicoherent :=
    isQuasicoherent_of_pushforward (Spec.map φ)
      ((pullback (Spec.map φ)).obj (tilde M))
  letI hSource :
      ((𝟭 (Spec R).Modules).obj (tilde M)).IsQuasicoherent := by
    change (tilde M).IsQuasicoherent
    infer_instance
  letI hTarget :
      ((pullback (Spec.map φ) ⋙ pushforward (Spec.map φ)).obj
        (tilde M)).IsQuasicoherent := by
    change ((pushforward (Spec.map φ)).obj
      ((pullback (Spec.map φ)).obj (tilde M))).IsQuasicoherent
    exact hPushforward
  apply isIso_of_isQuasicoherent_of_isIso_app_top
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ConcreteCategory.bijective_of_isIso
    (moduleSpecΓFunctor.map
      ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)))

end AlgebraicGeometry.Scheme.Modules
