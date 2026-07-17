import ModularCurves.ForMathlib.AffineModuleBaseChange
import ModularCurves.ForMathlib.AffinePatchBaseChangeNaturality
import ModularCurves.ForMathlib.SchemeModuleBaseCech
import ModularCurves.Picard.DualPullback.OpenUnit

/-!
# Base change for module sections on affine patches

This file identifies sections of a quasicoherent module on an affine source
patch after affine base change.  The comparison is expressed over the new
base ring so that it can be assembled into a base-linear Cech complex.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem five_comp_apply {R : Type u} [CommRing R]
    {A B C D E F : ModuleCat.{u} R}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : D ⟶ E)
    (e : E ⟶ F) (x : A) :
    (a ≫ b ≫ c ≫ d ≫ e) x = e (d (c (b (a x)))) := by
  rfl

private noncomputable def tensorPushoutModuleAddEquiv
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra A C]
    (e : C ≃+* A ⊗[R] B)
    (heA : ∀ a, e (algebraMap A C a) = a ⊗ₜ[R] (1 : B))
    (P : Type u) [AddCommGroup P] [Module A P] [Module R P]
    [IsScalarTower R A P] :
    C ⊗[A] P ≃+ B ⊗[R] P := by
  let eA : C ≃ₗ[A] A ⊗[R] B :=
    { e.toAddEquiv with
      map_smul' := fun a c => by
        simp only [RingHom.id_apply, Algebra.smul_def]
        change e (algebraMap A C a * c) =
          algebraMap A (A ⊗[R] B) a * e c
        rw [e.map_mul, heA, Algebra.TensorProduct.algebraMap_apply]
        simp }
  exact (TensorProduct.congr eA (LinearEquiv.refl A P)).toAddEquiv |>.trans
    (TensorProduct.comm A (A ⊗[R] B) P).toAddEquiv |>.trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A P B).toAddEquiv |>.trans
    (TensorProduct.comm R P B).toAddEquiv

private theorem tensorPushoutModuleAddEquiv_symm_tmul
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra A C] [Algebra B C]
    (e : C ≃+* A ⊗[R] B)
    (heA : ∀ a, e (algebraMap A C a) = a ⊗ₜ[R] (1 : B))
    (heB : ∀ b, e (algebraMap B C b) = (1 : A) ⊗ₜ[R] b)
    (P : Type u) [AddCommGroup P] [Module A P] [Module R P]
    [IsScalarTower R A P] (b : B) (p : P) :
    (tensorPushoutModuleAddEquiv e heA P).symm (b ⊗ₜ[R] p) =
      algebraMap B C b ⊗ₜ[A] p := by
  dsimp only [tensorPushoutModuleAddEquiv]
  change e.symm ((1 : A) ⊗ₜ[R] b) ⊗ₜ[A] p =
    algebraMap B C b ⊗ₜ[A] p
  rw [← heB]
  simp

private noncomputable def tensorPushoutModuleIso
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra A C] [Algebra B C]
    (e : C ≃+* A ⊗[R] B)
    (heA : ∀ a, e (algebraMap A C a) = a ⊗ₜ[R] (1 : B))
    (heB : ∀ b, e (algebraMap B C b) = (1 : A) ⊗ₜ[R] b)
    (P : Type u) [AddCommGroup P] [Module A P] [Module R P]
    [IsScalarTower R A P] :
    letI : Module B (C ⊗[A] P) :=
      Module.compHom _ (algebraMap B C)
    ModuleCat.of B (B ⊗[R] P) ≅ ModuleCat.of B (C ⊗[A] P) := by
  letI : Module B (C ⊗[A] P) :=
    Module.compHom _ (algebraMap B C)
  let ψ : C ⊗[A] P ≃+ B ⊗[R] P :=
    tensorPushoutModuleAddEquiv e heA P
  have hψ (b : B) (p : P) :
      ψ.symm (b ⊗ₜ[R] p) = algebraMap B C b ⊗ₜ[A] p := by
    exact tensorPushoutModuleAddEquiv_symm_tmul e heA heB P b p
  refine ModuleCat.isoMk ψ.symm.toAddCommGrpIso ?_
  intro b
  ext (x : B ⊗[R] P)
  dsimp
  change algebraMap B C b • ψ.symm x = ψ.symm (b • x)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b' p =>
      rw [hψ]
      change (algebraMap B C b * algebraMap B C b') ⊗ₜ[A] p =
        ψ.symm ((b * b') ⊗ₜ[R] p)
      rw [hψ, map_mul]
  | add x y hx hy => simp [hx, hy]

private theorem tensorPushoutModuleIso_hom_tmul
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra A C] [Algebra B C]
    (e : C ≃+* A ⊗[R] B)
    (heA : ∀ a, e (algebraMap A C a) = a ⊗ₜ[R] (1 : B))
    (heB : ∀ b, e (algebraMap B C b) = (1 : A) ⊗ₜ[R] b)
    (P : Type u) [AddCommGroup P] [Module A P] [Module R P]
    [IsScalarTower R A P] (b : B) (p : P) :
    letI : Module B (C ⊗[A] P) :=
      Module.compHom _ (algebraMap B C)
    (tensorPushoutModuleIso e heA heB P).hom (b ⊗ₜ[R] p) =
      algebraMap B C b ⊗ₜ[A] p := by
  change (tensorPushoutModuleAddEquiv e heA P).symm (b ⊗ₜ[R] p) = _
  exact tensorPushoutModuleAddEquiv_symm_tmul e heA heB P b p

private noncomputable def baseModulePresheafRestrictIso
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) (U : X.Opens) :
    (baseModulePresheaf f M).obj (op U) ≅
      (ModuleCat.restrictScalars (U.ι ≫ f).appTop.hom).obj
        (ModuleCat.of Γ(U.toScheme, (⊤ : U.toScheme.Opens))
          Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens))) := by
  let eAdd := M.presheaf.mapIso (eqToIso U.ι_image_top).op ≪≫
    (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).symm
  refine ModuleCat.isoMk eAdd ?_
  intro r
  ext (x : Γ(M, U))
  change
    (U.ι ≫ f).appTop.hom r •
        (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).inv
          (M.presheaf.map (eqToHom U.ι_image_top).op x) =
      (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).inv
        (M.presheaf.map (eqToHom U.ι_image_top).op
          (((X.presheaf.map
            ((initialOpOfTerminal isTerminalTop).to (op U))).hom
              (f.appTop.hom r)) • x))
  rw [M.map_smul]
  rw [smul_restrictAppIso_inv_apply]
  congr 1
  rw [Scheme.Hom.comp_appTop]
  have hr : (U.ι.appIso (⊤ : U.toScheme.Opens)).hom
      (X.presheaf.map (eqToHom U.ι_image_top).op
        ((X.presheaf.map
          ((initialOpOfTerminal isTerminalTop).to (op U))).hom
            (f.appTop.hom r))) =
      U.topIso.inv
        ((X.presheaf.map
          ((initialOpOfTerminal isTerminalTop).to (op U))).hom
            (f.appTop.hom r)) := by
    rw [Scheme.Opens.topIso_inv]
    rw [Scheme.Opens.ι_appIso]
    rfl
  rw [hr]
  rw [Scheme.Opens.topIso_inv]
  rw [Scheme.Opens.ι_appTop]
  have hmap :
      X.presheaf.map
          (homOfLE (x := U.ι ''ᵁ (⊤ : U.toScheme.Opens)) le_top).op =
        X.presheaf.map
            ((initialOpOfTerminal isTerminalTop).to (op U)) ≫
          X.presheaf.map (eqToHom U.ι_image_top).op := by
    rw [← Functor.map_comp]
    congr
  rw [hmap]
  rfl

private theorem restrictUnit_transport_top
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (x : M.presheaf.obj (op U))
    (htop : (⊤ : U.toScheme.Opens) = U.ι ⁻¹ᵁ U) :
    (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).inv
        (M.presheaf.map (eqToHom U.ι_image_top).op x) =
      (M.restrict U.ι).presheaf.map (eqToHom htop).op
        (((restrictAdjunction U.ι).unit.app M).val.app (op U) x) := by
  have hleft :
      (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).inv
          (M.presheaf.map (eqToHom U.ι_image_top).op x) =
        M.presheaf.map (eqToHom U.ι_image_top).op x := by
    rfl
  have hunit :
      (((restrictAdjunction U.ι).unit.app M).val.app (op U)) x =
        M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op x := by
    exact ConcreteCategory.congr_hom
      (restrictAdjunction_unit_app_app U.ι M U) x
  have hrestrict :
      (M.restrict U.ι).presheaf.map (eqToHom htop).op
          (M.presheaf.map
            (homOfLE (U.ι.image_preimage_le U)).op x) =
        M.presheaf.map
          (U.ι.opensFunctor.map (eqToHom htop)).op
          (M.presheaf.map
            (homOfLE (U.ι.image_preimage_le U)).op x) := by
    exact ConcreteCategory.congr_hom
      (restrict_map M U.ι (eqToHom htop))
        (M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op x)
  rw [hleft, hunit, hrestrict]
  have hmaps :
      M.presheaf.map (eqToHom U.ι_image_top).op =
        M.presheaf.map
            (homOfLE (U.ι.image_preimage_le U)).op ≫
          M.presheaf.map
            (U.ι.opensFunctor.map (eqToHom htop)).op := by
    rw [← Functor.map_comp]
    exact M.presheaf.congr_map (Subsingleton.elim _ _)
  exact ConcreteCategory.congr_hom hmaps x

private theorem pullbackUnit_transport_top
    {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    (W : X.Opens) (Z : Y.Opens) (x : M.presheaf.obj (op W))
    (hW : (⊤ : X.Opens) = W) (hZ : (⊤ : Y.Opens) = Z)
    (hpre : Z = g ⁻¹ᵁ W) :
    affinePullbackUnitTop g M
        (M.presheaf.map (eqToHom hW).op x) =
      ((pullback g).obj M).presheaf.map (eqToHom hZ).op
        (((pullback g).obj M).presheaf.map (eqToHom hpre).op
          (((pullbackPushforwardAdjunction g).unit.app M).val.app
            (op W) x)) := by
  let P := (pullback g).obj M
  let htop : (⊤ : Y.Opens) = g ⁻¹ᵁ (⊤ : X.Opens) := by simp
  have hleft :
      affinePullbackUnitTop g M
          (M.presheaf.map (eqToHom hW).op x) =
        P.presheaf.map (eqToHom htop).op
          (((pullbackPushforwardAdjunction g).unit.app M).val.app
            (op (⊤ : X.Opens))
              (M.presheaf.map (eqToHom hW).op x)) := by
    rfl
  have hnat := PresheafOfModules.naturality_apply
    ((pullbackPushforwardAdjunction g).unit.app M).val
      (eqToHom hW).op x
  change
    (((pullbackPushforwardAdjunction g).unit.app M).val.app
      (op (⊤ : X.Opens)))
        (M.presheaf.map (eqToHom hW).op x) =
      P.presheaf.map
          (((TopologicalSpace.Opens.map g.base).map
            (eqToHom hW)).op)
        ((((pullbackPushforwardAdjunction g).unit.app M).val.app
          (op W)) x) at hnat
  have hmaps :
      P.presheaf.map
            (((TopologicalSpace.Opens.map g.base).map
              (eqToHom hW)).op) ≫
          P.presheaf.map (eqToHom htop).op =
        P.presheaf.map (eqToHom hpre).op ≫
          P.presheaf.map (eqToHom hZ).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact P.presheaf.congr_map (Subsingleton.elim _ _)
  calc
    _ = P.presheaf.map (eqToHom htop).op
          (((pullbackPushforwardAdjunction g).unit.app M).val.app
            (op (⊤ : X.Opens))
              (M.presheaf.map (eqToHom hW).op x)) := hleft
    _ = P.presheaf.map (eqToHom htop).op
          (P.presheaf.map
            (((TopologicalSpace.Opens.map g.base).map
              (eqToHom hW)).op)
                (((pullbackPushforwardAdjunction g).unit.app M).val.app
                  (op W) x)) := congrArg
      (fun z => P.presheaf.map (eqToHom htop).op z) hnat
    _ = _ := ConcreteCategory.congr_hom hmaps
      ((((pullbackPushforwardAdjunction g).unit.app M).val.app
        (op W)) x)

private theorem baseModulePresheafRestrictIso_hom_eq_transport_unit
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) (U : X.Opens)
    (x : (baseModulePresheaf f M).obj (op U))
    (htop : (⊤ : U.toScheme.Opens) = U.ι ⁻¹ᵁ U) :
    (baseModulePresheafRestrictIso f M U).hom x =
      (M.restrict U.ι).presheaf.map (eqToHom htop).op
        (((restrictAdjunction U.ι).unit.app M).val.app (op U) x) := by
  exact restrictUnit_transport_top M U x htop

private noncomputable def affineModuleSectionsSourceIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) :
    (ModuleCat.extendScalars t.appTop.hom).obj
        ((baseModulePresheaf f M).obj (op U)) ≅
      (ModuleCat.extendScalars t.appTop.hom).obj
        ((ModuleCat.restrictScalars (U.ι ≫ f).appTop.hom).obj
          (ModuleCat.of Γ(U.toScheme, (⊤ : U.toScheme.Opens))
            Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens)))) :=
  (ModuleCat.extendScalars t.appTop.hom).mapIso
    (baseModulePresheafRestrictIso f M U)

private noncomputable def affineModuleSectionsTensorIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) [IsAffine S] [IsAffine T] :
    (ModuleCat.extendScalars t.appTop.hom).obj
        ((ModuleCat.restrictScalars (U.ι ≫ f).appTop.hom).obj
          (ModuleCat.of Γ(U.toScheme, (⊤ : U.toScheme.Opens))
            Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens)))) ≅
      (ModuleCat.restrictScalars
          ((pullback.fst f t ⁻¹ᵁ U).ι ≫ pullback.snd f t).appTop.hom).obj
        ((ModuleCat.extendScalars (pullback.fst f t ∣_ U).appTop.hom).obj
          (ModuleCat.of Γ(U.toScheme, (⊤ : U.toScheme.Opens))
            Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens)))) := by
  let g := pullback.fst f t
  let U' := g ⁻¹ᵁ U
  letI : IsAffine U.toScheme := hU
  letI : IsAffine U'.toScheme :=
    IsAffineOpen.preimage_pullback_fst f t hU
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
    ((U.ι ≫ f).appTop.hom).toAlgebra
  letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
    t.appTop.hom.toAlgebra
  letI : Algebra Γ(U.toScheme, (⊤ : U.toScheme.Opens))
      Γ(U'.toScheme, (⊤ : U'.toScheme.Opens)) :=
    (g ∣_ U).appTop.hom.toAlgebra
  letI : Algebra Γ(T, (⊤ : T.Opens))
      Γ(U'.toScheme, (⊤ : U'.toScheme.Opens)) :=
    (U'.ι ≫ pullback.snd f t).appTop.hom.toAlgebra
  letI : Module Γ(S, (⊤ : S.Opens))
      Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens)) :=
    Module.compHom _ (algebraMap _ Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
  letI : IsScalarTower Γ(S, (⊤ : S.Opens))
      Γ(U.toScheme, (⊤ : U.toScheme.Opens))
      Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : Γ(U'.toScheme, (⊤ : U'.toScheme.Opens)) ≃+*
      Γ(U.toScheme, (⊤ : U.toScheme.Opens)) ⊗[Γ(S, (⊤ : S.Opens))]
        Γ(T, (⊤ : T.Opens)) :=
    (U'.topIso ≪≫ pullbackPreimageΓIsoTensor f t U hU).commRingCatIsoToRingEquiv
  have heA (a : Γ(U.toScheme, (⊤ : U.toScheme.Opens))) :
      e (algebraMap Γ(U.toScheme, (⊤ : U.toScheme.Opens))
          Γ(U'.toScheme, (⊤ : U'.toScheme.Opens)) a) =
        a ⊗ₜ[Γ(S, (⊤ : S.Opens))] (1 : Γ(T, (⊤ : T.Opens))) := by
    change (pullbackPreimageΓIsoTensor f t U hU).hom
        (U'.topIso.hom ((g ∣_ U).appTop.hom a)) = _
    have h := congrArg (fun q => q.hom a)
      (pullbackPreimageΓIsoTensor_inv_includeLeft f t U hU)
    have h' : (pullbackPreimageΓIsoTensor f t U hU).inv
        (a ⊗ₜ[Γ(S, (⊤ : S.Opens))] (1 : Γ(T, (⊤ : T.Opens)))) =
        U'.topIso.hom ((g ∣_ U).appTop.hom a) := by
      change (pullbackPreimageΓIsoTensor f t U hU).inv
          (Algebra.TensorProduct.includeLeftRingHom a) =
        U'.topIso.hom ((g ∣_ U).appTop.hom a) at h
      rw [Algebra.TensorProduct.includeLeftRingHom_apply] at h
      exact h
    rw [← h']
    exact Iso.inv_hom_id_apply _ _
  have heB (b : Γ(T, (⊤ : T.Opens))) :
      e (algebraMap Γ(T, (⊤ : T.Opens))
          Γ(U'.toScheme, (⊤ : U'.toScheme.Opens)) b) =
        (1 : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
          ⊗ₜ[Γ(S, (⊤ : S.Opens))] b := by
    change (pullbackPreimageΓIsoTensor f t U hU).hom
        (U'.topIso.hom ((U'.ι ≫ pullback.snd f t).appTop.hom b)) = _
    have h := congrArg (fun q => q.hom b)
      (pullbackPreimageΓIsoTensor_inv_includeRight f t U hU)
    have h' : (pullbackPreimageΓIsoTensor f t U hU).inv
        ((1 : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
          ⊗ₜ[Γ(S, (⊤ : S.Opens))] b) =
        U'.topIso.hom ((U'.ι ≫ pullback.snd f t).appTop.hom b) := by
      change (pullbackPreimageΓIsoTensor f t U hU).inv
          (Algebra.TensorProduct.includeRight b) =
        U'.topIso.hom ((U'.ι ≫ pullback.snd f t).appTop.hom b) at h
      rw [Algebra.TensorProduct.includeRight_apply] at h
      exact h
    rw [← h']
    exact Iso.inv_hom_id_apply _ _
  exact tensorPushoutModuleIso e heA heB
    Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens))

private noncomputable def affineModuleSectionsPullbackIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) [IsAffine S] [IsAffine T]
    [M.IsQuasicoherent] :
    (ModuleCat.restrictScalars
          ((pullback.fst f t ⁻¹ᵁ U).ι ≫ pullback.snd f t).appTop.hom).obj
        ((ModuleCat.extendScalars (pullback.fst f t ∣_ U).appTop.hom).obj
          (ModuleCat.of Γ(U.toScheme, (⊤ : U.toScheme.Opens))
            Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens)))) ≅
      (ModuleCat.restrictScalars
          ((pullback.fst f t ⁻¹ᵁ U).ι ≫ pullback.snd f t).appTop.hom).obj
        (ModuleCat.of
          Γ((pullback.fst f t ⁻¹ᵁ U).toScheme,
            (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))
          Γ((pullback (pullback.fst f t ∣_ U)).obj (M.restrict U.ι),
            (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))) := by
  letI : IsAffine U.toScheme := hU
  letI : IsAffine (pullback.fst f t ⁻¹ᵁ U).toScheme :=
    IsAffineOpen.preimage_pullback_fst f t hU
  exact (ModuleCat.restrictScalars
      ((pullback.fst f t ⁻¹ᵁ U).ι ≫ pullback.snd f t).appTop.hom).mapIso
    (affinePullbackΓIso (pullback.fst f t ∣_ U) (M.restrict U.ι))

private noncomputable def affineModuleSectionsLocalIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) :
    (ModuleCat.restrictScalars
          ((pullback.fst f t ⁻¹ᵁ U).ι ≫ pullback.snd f t).appTop.hom).obj
        (ModuleCat.of
          Γ((pullback.fst f t ⁻¹ᵁ U).toScheme,
            (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))
          Γ((pullback (pullback.fst f t ∣_ U)).obj (M.restrict U.ι),
            (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))) ≅
      (ModuleCat.restrictScalars
          ((pullback.fst f t ⁻¹ᵁ U).ι ≫ pullback.snd f t).appTop.hom).obj
        (ModuleCat.of
          Γ((pullback.fst f t ⁻¹ᵁ U).toScheme,
            (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))
          Γ(((pullback (pullback.fst f t)).obj M).restrict
              (pullback.fst f t ⁻¹ᵁ U).ι,
            (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))) := by
  let U' := pullback.fst f t ⁻¹ᵁ U
  let eLocal := asIso (Hom.app
    (localPullbackRestrictIso (pullback.fst f t) M U).hom
    (⊤ : U'.toScheme.Opens))
  let eLocalAdd :
      Γ((pullback (pullback.fst f t ∣_ U)).obj (M.restrict U.ι),
          (⊤ : U'.toScheme.Opens)) ≃+
        Γ(((pullback (pullback.fst f t)).obj M).restrict U'.ι,
          (⊤ : U'.toScheme.Opens)) :=
    { toFun := eLocal.hom
      invFun := eLocal.inv
      left_inv := eLocal.hom_inv_id_apply
      right_inv := eLocal.inv_hom_id_apply
      map_add' := eLocal.hom.hom.map_add }
  let eLocalLinear :
      Γ((pullback (pullback.fst f t ∣_ U)).obj (M.restrict U.ι),
          (⊤ : U'.toScheme.Opens)) ≃ₗ[Γ(U'.toScheme, (⊤ : U'.toScheme.Opens))]
        Γ(((pullback (pullback.fst f t)).obj M).restrict U'.ι,
          (⊤ : U'.toScheme.Opens)) :=
    { eLocalAdd with
      map_smul' := Hom.app_smul
        (localPullbackRestrictIso (pullback.fst f t) M U).hom }
  exact (ModuleCat.restrictScalars
      (U'.ι ≫ pullback.snd f t).appTop.hom).mapIso
    eLocalLinear.toModuleIso

private noncomputable def affineModuleSectionsTargetIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) :
    (ModuleCat.restrictScalars
          ((pullback.fst f t ⁻¹ᵁ U).ι ≫ pullback.snd f t).appTop.hom).obj
        (ModuleCat.of
          Γ((pullback.fst f t ⁻¹ᵁ U).toScheme,
            (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))
          Γ(((pullback (pullback.fst f t)).obj M).restrict
              (pullback.fst f t ⁻¹ᵁ U).ι,
            (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))) ≅
      (baseModulePresheaf (pullback.snd f t)
          ((pullback (pullback.fst f t)).obj M)).obj
        (op (pullback.fst f t ⁻¹ᵁ U)) :=
  (baseModulePresheafRestrictIso (pullback.snd f t)
    ((pullback (pullback.fst f t)).obj M)
      (pullback.fst f t ⁻¹ᵁ U)).symm

/-- Sections of a quasicoherent module on an affine patch commute with an
affine base change. -/
noncomputable def affineModuleSectionsBaseChangeIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) [IsAffine S] [IsAffine T]
    [M.IsQuasicoherent] :
    (ModuleCat.extendScalars t.appTop.hom).obj
        ((baseModulePresheaf f M).obj (op U)) ≅
      (baseModulePresheaf (pullback.snd f t)
          ((pullback (pullback.fst f t)).obj M)).obj
        (op (pullback.fst f t ⁻¹ᵁ U)) :=
  affineModuleSectionsSourceIso f t M U ≪≫
    affineModuleSectionsTensorIso f t M U hU ≪≫
      affineModuleSectionsPullbackIso f t M U hU ≪≫
        affineModuleSectionsLocalIso f t M U ≪≫
          affineModuleSectionsTargetIso f t M U

private theorem affineModuleSectionsSourceIso_hom_one_tmul
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) (m : (baseModulePresheaf f M).obj (op U)) :
    (affineModuleSectionsSourceIso f t M U).hom
        ((1 : Γ(T, (⊤ : T.Opens)))
          ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom] m) =
      (1 : Γ(T, (⊤ : T.Opens)))
        ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom]
        ((baseModulePresheafRestrictIso f M U).hom m) := by
  exact ModuleCat.ExtendScalars.map_tmul
    (f := t.appTop.hom) (baseModulePresheafRestrictIso f M U).hom
      (1 : Γ(T, (⊤ : T.Opens))) m

private theorem affineModuleSectionsTensorIso_hom_one_tmul
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) [IsAffine S] [IsAffine T]
    (p : Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens))) :
    (affineModuleSectionsTensorIso f t M U hU).hom
        ((1 : Γ(T, (⊤ : T.Opens)))
          ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom] p) =
      (1 : Γ((pullback.fst f t ⁻¹ᵁ U).toScheme,
        (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens)))
          ⊗ₜ[Γ(U.toScheme, (⊤ : U.toScheme.Opens)),
            (pullback.fst f t ∣_ U).appTop.hom] p := by
  let g := pullback.fst f t
  let U' := g ⁻¹ᵁ U
  letI : IsAffine U.toScheme := hU
  letI : IsAffine U'.toScheme :=
    IsAffineOpen.preimage_pullback_fst f t hU
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
    ((U.ι ≫ f).appTop.hom).toAlgebra
  letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
    t.appTop.hom.toAlgebra
  letI : Algebra Γ(U.toScheme, (⊤ : U.toScheme.Opens))
      Γ(U'.toScheme, (⊤ : U'.toScheme.Opens)) :=
    (g ∣_ U).appTop.hom.toAlgebra
  letI : Algebra Γ(T, (⊤ : T.Opens))
      Γ(U'.toScheme, (⊤ : U'.toScheme.Opens)) :=
    (U'.ι ≫ pullback.snd f t).appTop.hom.toAlgebra
  letI : Module Γ(S, (⊤ : S.Opens))
      Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens)) :=
    Module.compHom _ (algebraMap _ Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
  letI : IsScalarTower Γ(S, (⊤ : S.Opens))
      Γ(U.toScheme, (⊤ : U.toScheme.Opens))
      Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  dsimp only [affineModuleSectionsTensorIso]
  change
    (tensorPushoutModuleIso _ _ _
      Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens))).hom
        ((1 : Γ(T, (⊤ : T.Opens))) ⊗ₜ[Γ(S, (⊤ : S.Opens))] p) =
      (1 : Γ(U'.toScheme, (⊤ : U'.toScheme.Opens)))
        ⊗ₜ[Γ(U.toScheme, (⊤ : U.toScheme.Opens))] p
  simpa only [map_one] using
    (tensorPushoutModuleIso_hom_tmul
      (R := Γ(S, (⊤ : S.Opens)))
      (A := Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
      (B := Γ(T, (⊤ : T.Opens)))
      (C := Γ(U'.toScheme, (⊤ : U'.toScheme.Opens)))
      (e := _) (heA := _) (heB := _)
      Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens))
      (1 : Γ(T, (⊤ : T.Opens))) p)

private theorem affineModuleSectionsPullbackIso_hom_one_tmul
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) [IsAffine S] [IsAffine T]
    [M.IsQuasicoherent]
    (p : Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens))) :
    (affineModuleSectionsPullbackIso f t M U hU).hom
        ((1 : Γ((pullback.fst f t ⁻¹ᵁ U).toScheme,
          (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens)))
            ⊗ₜ[Γ(U.toScheme, (⊤ : U.toScheme.Opens))] p) =
      affinePullbackUnitTop (pullback.fst f t ∣_ U) (M.restrict U.ι) p := by
  letI : IsAffine U.toScheme := hU
  letI : IsAffine (pullback.fst f t ⁻¹ᵁ U).toScheme :=
    IsAffineOpen.preimage_pullback_fst f t hU
  change (affinePullbackΓIso (pullback.fst f t ∣_ U)
      (M.restrict U.ι)).hom _ = _
  exact affinePullbackΓIso_hom_one_tmul
    (pullback.fst f t ∣_ U) (M.restrict U.ι) p

private theorem affineModuleSectionsLocalTarget_hom_unit
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) (m : (baseModulePresheaf f M).obj (op U)) :
    ((affineModuleSectionsLocalIso f t M U ≪≫
        affineModuleSectionsTargetIso f t M U).hom)
      (affinePullbackUnitTop (pullback.fst f t ∣_ U) (M.restrict U.ι)
        ((baseModulePresheafRestrictIso f M U).hom m)) =
      (((pullbackPushforwardAdjunction (pullback.fst f t)).unit.app M).val.app
        (op U)) m := by
  let eTarget := baseModulePresheafRestrictIso (pullback.snd f t)
    ((pullback (pullback.fst f t)).obj M) (pullback.fst f t ⁻¹ᵁ U)
  have hlocal :
      (affineModuleSectionsLocalIso f t M U).hom
          (affinePullbackUnitTop (pullback.fst f t ∣_ U) (M.restrict U.ι)
            ((baseModulePresheafRestrictIso f M U).hom m)) =
        eTarget.hom
          ((((pullbackPushforwardAdjunction (pullback.fst f t)).unit.app M).val.app
            (op U)) m) := by
    let hpre : (pullback.fst f t ⁻¹ᵁ U).ι ⁻¹ᵁ
        (pullback.fst f t ⁻¹ᵁ U) =
        (pullback.fst f t ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      exact congrArg
        (fun q : (pullback.fst f t ⁻¹ᵁ U).toScheme ⟶ X ↦ q ⁻¹ᵁ U)
        (morphismRestrict_ι (pullback.fst f t) U).symm
    let lhsH :=
      (localPullbackRestrictIso (pullback.fst f t) M U).hom.val.app
        (op ((pullback.fst f t ⁻¹ᵁ U).ι ⁻¹ᵁ
          (pullback.fst f t ⁻¹ᵁ U)))
        (((restrictFunctor U.ι ⋙ pullback (pullback.fst f t ∣_ U)).obj M).presheaf.map
          (eqToHom hpre).op
          (((pullbackPushforwardAdjunction (pullback.fst f t ∣_ U)).unit.app
            ((restrictFunctor U.ι).obj M)).val.app (op (U.ι ⁻¹ᵁ U))
            (((restrictAdjunction U.ι).unit.app M).val.app (op U) m)))
    let rhsH :=
      ((restrictAdjunction (pullback.fst f t ⁻¹ᵁ U).ι).unit.app
        ((pullback (pullback.fst f t)).obj M)).val.app
          (op (pullback.fst f t ⁻¹ᵁ U))
        (((pullbackPushforwardAdjunction (pullback.fst f t)).unit.app M).val.app
          (op U) m)
    have hEq : lhsH = rhsH :=
      localPullbackRestrictIso_unit_appT (pullback.fst f t) M U m
    let N := ((pullback (pullback.fst f t)).obj M).restrict
      (pullback.fst f t ⁻¹ᵁ U).ι
    let htop : (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens) =
        (pullback.fst f t ⁻¹ᵁ U).ι ⁻¹ᵁ
          (pullback.fst f t ⁻¹ᵁ U) := by simp
    let tr := N.presheaf.map (eqToHom htop).op
    have hEqTop : tr lhsH = tr rhsH := congrArg tr hEq
    let hsourceTop : (⊤ : U.toScheme.Opens) = U.ι ⁻¹ᵁ U := by simp
    have hsource :=
      baseModulePresheafRestrictIso_hom_eq_transport_unit
        f M U m hsourceTop
    let localUnit :=
      (((restrictAdjunction U.ι).unit.app M).val.app (op U)) m
    let pulledLocalUnit :=
      (((pullbackPushforwardAdjunction (pullback.fst f t ∣_ U)).unit.app
        (M.restrict U.ι)).val.app (op (U.ι ⁻¹ᵁ U))) localUnit
    let transportedLocalUnit :=
      ((pullback (pullback.fst f t ∣_ U)).obj
        (M.restrict U.ι)).presheaf.map (eqToHom hpre).op pulledLocalUnit
    have hpull := pullbackUnit_transport_top
      (pullback.fst f t ∣_ U) (M.restrict U.ι)
        (U.ι ⁻¹ᵁ U)
        ((pullback.fst f t ⁻¹ᵁ U).ι ⁻¹ᵁ
          (pullback.fst f t ⁻¹ᵁ U))
        localUnit hsourceTop htop hpre
    have hpull' :
        affinePullbackUnitTop (pullback.fst f t ∣_ U) (M.restrict U.ι)
            ((baseModulePresheafRestrictIso f M U).hom m) =
          ((pullback (pullback.fst f t ∣_ U)).obj
            (M.restrict U.ι)).presheaf.map (eqToHom htop).op
              transportedLocalUnit := by
      rw [hsource]
      exact hpull
    have hlocalNat :
        (localPullbackRestrictIso (pullback.fst f t) M U).hom.val.app
            (op (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))
              (((pullback (pullback.fst f t ∣_ U)).obj
                (M.restrict U.ι)).presheaf.map
                  (eqToHom htop).op transportedLocalUnit) =
          N.presheaf.map (eqToHom htop).op
            ((localPullbackRestrictIso (pullback.fst f t) M U).hom.val.app
              (op ((pullback.fst f t ⁻¹ᵁ U).ι ⁻¹ᵁ
                (pullback.fst f t ⁻¹ᵁ U))) transportedLocalUnit) := by
      exact PresheafOfModules.naturality_apply
        (localPullbackRestrictIso (pullback.fst f t) M U).hom.val
          (eqToHom htop).op transportedLocalUnit
    have hLeftDef :
        (affineModuleSectionsLocalIso f t M U).hom
            (affinePullbackUnitTop (pullback.fst f t ∣_ U) (M.restrict U.ι)
              ((baseModulePresheafRestrictIso f M U).hom m)) =
          (localPullbackRestrictIso (pullback.fst f t) M U).hom.val.app
            (op (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))
              (affinePullbackUnitTop (pullback.fst f t ∣_ U)
                (M.restrict U.ι)
                  ((baseModulePresheafRestrictIso f M U).hom m)) := by
      rfl
    have hLeftPullback :
        (localPullbackRestrictIso (pullback.fst f t) M U).hom.val.app
            (op (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))
              (affinePullbackUnitTop (pullback.fst f t ∣_ U)
                (M.restrict U.ι)
                  ((baseModulePresheafRestrictIso f M U).hom m)) =
          (localPullbackRestrictIso (pullback.fst f t) M U).hom.val.app
            (op (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))
              (((pullback (pullback.fst f t ∣_ U)).obj
                (M.restrict U.ι)).presheaf.map
                  (eqToHom htop).op transportedLocalUnit) :=
      congrArg
        (fun q =>
          (localPullbackRestrictIso (pullback.fst f t) M U).hom.val.app
            (op (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens)) q)
        hpull'
    have hLeftTransport :
        N.presheaf.map (eqToHom htop).op
            ((localPullbackRestrictIso (pullback.fst f t) M U).hom.val.app
              (op ((pullback.fst f t ⁻¹ᵁ U).ι ⁻¹ᵁ
                (pullback.fst f t ⁻¹ᵁ U))) transportedLocalUnit) =
          tr lhsH := by
      rfl
    have hLeft :
        (affineModuleSectionsLocalIso f t M U).hom
            (affinePullbackUnitTop (pullback.fst f t ∣_ U) (M.restrict U.ι)
              ((baseModulePresheafRestrictIso f M U).hom m)) = tr lhsH :=
      hLeftDef.trans <| hLeftPullback.trans <| hlocalNat.trans hLeftTransport
    have hRight : eTarget.hom
          ((((pullbackPushforwardAdjunction (pullback.fst f t)).unit.app M).val.app
            (op U)) m) = tr rhsH := by
      exact baseModulePresheafRestrictIso_hom_eq_transport_unit
        (pullback.snd f t) ((pullback (pullback.fst f t)).obj M)
          (pullback.fst f t ⁻¹ᵁ U)
            ((((pullbackPushforwardAdjunction (pullback.fst f t)).unit.app M).val.app
              (op U)) m) htop
    exact hLeft.trans (hEqTop.trans hRight.symm)
  change eTarget.inv
      ((affineModuleSectionsLocalIso f t M U).hom
        (affinePullbackUnitTop (pullback.fst f t ∣_ U) (M.restrict U.ι)
          ((baseModulePresheafRestrictIso f M U).hom m))) = _
  rw [hlocal]
  exact eTarget.hom_inv_id_apply _

private theorem affineModuleSectionsSourceTensor_hom_one_tmul
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) [IsAffine S] [IsAffine T]
    (m : (baseModulePresheaf f M).obj (op U)) :
    (affineModuleSectionsTensorIso f t M U hU).hom
        ((affineModuleSectionsSourceIso f t M U).hom
          ((1 : Γ(T, (⊤ : T.Opens)))
            ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom] m)) =
      (1 : Γ((pullback.fst f t ⁻¹ᵁ U).toScheme,
        (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens)))
          ⊗ₜ[Γ(U.toScheme, (⊤ : U.toScheme.Opens)),
            (pullback.fst f t ∣_ U).appTop.hom]
            ((baseModulePresheafRestrictIso f M U).hom m) := by
  rw [affineModuleSectionsSourceIso_hom_one_tmul]
  exact affineModuleSectionsTensorIso_hom_one_tmul
    f t M U hU ((baseModulePresheafRestrictIso f M U).hom m)

private theorem affineModuleSectionsSourceTensorPullback_hom_one_tmul
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) [IsAffine S] [IsAffine T]
    [M.IsQuasicoherent] (m : (baseModulePresheaf f M).obj (op U)) :
    (affineModuleSectionsPullbackIso f t M U hU).hom
        ((affineModuleSectionsTensorIso f t M U hU).hom
          ((affineModuleSectionsSourceIso f t M U).hom
            ((1 : Γ(T, (⊤ : T.Opens)))
              ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom] m))) =
      affinePullbackUnitTop (pullback.fst f t ∣_ U) (M.restrict U.ι)
        ((baseModulePresheafRestrictIso f M U).hom m) := by
  rw [affineModuleSectionsSourceTensor_hom_one_tmul]
  exact affineModuleSectionsPullbackIso_hom_one_tmul
    f t M U hU ((baseModulePresheafRestrictIso f M U).hom m)

private theorem affineModuleSectionsBaseChangeIso_hom_apply
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) [IsAffine S] [IsAffine T]
    [M.IsQuasicoherent]
    (x : (ModuleCat.extendScalars t.appTop.hom).obj
      ((baseModulePresheaf f M).obj (op U))) :
    (affineModuleSectionsBaseChangeIso f t M U hU).hom x =
      (affineModuleSectionsTargetIso f t M U).hom
        ((affineModuleSectionsLocalIso f t M U).hom
          ((affineModuleSectionsPullbackIso f t M U hU).hom
            ((affineModuleSectionsTensorIso f t M U hU).hom
              ((affineModuleSectionsSourceIso f t M U).hom x)))) := by
  dsimp only [affineModuleSectionsBaseChangeIso]
  simp only [Iso.trans_hom, five_comp_apply]

private theorem affineModuleSectionsBaseChangeGeneratorChain
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) [IsAffine S] [IsAffine T]
    [M.IsQuasicoherent] (m : (baseModulePresheaf f M).obj (op U)) :
    (affineModuleSectionsTargetIso f t M U).hom
        ((affineModuleSectionsLocalIso f t M U).hom
          ((affineModuleSectionsPullbackIso f t M U hU).hom
            ((affineModuleSectionsTensorIso f t M U hU).hom
              ((affineModuleSectionsSourceIso f t M U).hom
                ((1 : Γ(T, (⊤ : T.Opens)))
                  ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom] m))))) =
      (((pullbackPushforwardAdjunction (pullback.fst f t)).unit.app M).val.app
        (op U)) m := by
  rw [affineModuleSectionsSourceTensorPullback_hom_one_tmul]
  exact affineModuleSectionsLocalTarget_hom_unit f t M U m

/-- The affine-patch module comparison sends `1 ⊗ m` to the section
obtained from the pullback-adjunction unit. -/
theorem affineModuleSectionsBaseChangeIso_hom_one_tmul
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) [IsAffine S] [IsAffine T]
    [M.IsQuasicoherent] (m : (baseModulePresheaf f M).obj (op U)) :
    (affineModuleSectionsBaseChangeIso f t M U hU).hom
        ((1 : Γ(T, (⊤ : T.Opens)))
          ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom] m) =
      (((pullbackPushforwardAdjunction (pullback.fst f t)).unit.app M).val.app
        (op U)) m := by
  exact (affineModuleSectionsBaseChangeIso_hom_apply f t M U hU
      ((1 : Γ(T, (⊤ : T.Opens)))
        ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom] m)).trans
    (affineModuleSectionsBaseChangeGeneratorChain f t M U hU m)

end AlgebraicGeometry.Scheme.Modules
