import ModularCurves.ForMathlib.AffineModuleBaseChange
import ModularCurves.ForMathlib.AffinePatchBaseChangeNaturality
import ModularCurves.ForMathlib.SchemeModuleBaseCech
import ModularCurves.Picard.DualPullback.OverRestriction

/-!
# Base change for module sections on affine patches

This file identifies sections of a quasicoherent module on an affine source
patch after affine base change.  The comparison is expressed over the new
base ring so that it can be assembled into a base-linear Cech complex.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

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
  let eA : C ≃ₗ[A] A ⊗[R] B :=
    { e.toAddEquiv with
      map_smul' := fun a c => by
        simp only [RingHom.id_apply, Algebra.smul_def]
        change e (algebraMap A C a * c) =
          algebraMap A (A ⊗[R] B) a * e c
        rw [e.map_mul, heA, Algebra.TensorProduct.algebraMap_apply]
        simp }
  let ψ : C ⊗[A] P ≃+ B ⊗[R] P :=
    (TensorProduct.congr eA (LinearEquiv.refl A P)).toAddEquiv |>.trans
      (TensorProduct.comm A (A ⊗[R] B) P).toAddEquiv |>.trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A P B).toAddEquiv |>.trans
      (TensorProduct.comm R P B).toAddEquiv
  have hψ (b : B) (p : P) :
      ψ.symm (b ⊗ₜ[R] p) = algebraMap B C b ⊗ₜ[A] p := by
    dsimp only [ψ]
    change e.symm ((1 : A) ⊗ₜ[R] b) ⊗ₜ[A] p =
      algebraMap B C b ⊗ₜ[A] p
    rw [← heB]
    simp
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
        (op (pullback.fst f t ⁻¹ᵁ U)) := by
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
        (1 : Γ(U.toScheme, (⊤ : U.toScheme.Opens))) ⊗ₜ[Γ(S, (⊤ : S.Opens))] b := by
    change (pullbackPreimageΓIsoTensor f t U hU).hom
        (U'.topIso.hom ((U'.ι ≫ pullback.snd f t).appTop.hom b)) = _
    have h := congrArg (fun q => q.hom b)
      (pullbackPreimageΓIsoTensor_inv_includeRight f t U hU)
    have h' : (pullbackPreimageΓIsoTensor f t U hU).inv
        ((1 : Γ(U.toScheme, (⊤ : U.toScheme.Opens))) ⊗ₜ[Γ(S, (⊤ : S.Opens))] b) =
        U'.topIso.hom ((U'.ι ≫ pullback.snd f t).appTop.hom b) := by
      change (pullbackPreimageΓIsoTensor f t U hU).inv
          (Algebra.TensorProduct.includeRight b) =
        U'.topIso.hom ((U'.ι ≫ pullback.snd f t).appTop.hom b) at h
      rw [Algebra.TensorProduct.includeRight_apply] at h
      exact h
    rw [← h']
    exact Iso.inv_hom_id_apply _ _
  let eLocal :
      Γ((pullback (pullback.fst f t ∣_ U)).obj (M.restrict U.ι),
          (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens)) ≅
        Γ(((pullback (pullback.fst f t)).obj M).restrict
            (pullback.fst f t ⁻¹ᵁ U).ι,
          (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens)) :=
    asIso (Hom.app
      (localPullbackRestrictIso (pullback.fst f t) M U).hom
      (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))
  let eLocalAdd :
      Γ((pullback (pullback.fst f t ∣_ U)).obj (M.restrict U.ι),
          (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens)) ≃+
        Γ(((pullback (pullback.fst f t)).obj M).restrict
            (pullback.fst f t ⁻¹ᵁ U).ι,
          (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens)) :=
    { toFun := eLocal.hom
      invFun := eLocal.inv
      left_inv := eLocal.hom_inv_id_apply
      right_inv := eLocal.inv_hom_id_apply
      map_add' := eLocal.hom.hom.map_add }
  let eLocalLinear :
      Γ((pullback (pullback.fst f t ∣_ U)).obj (M.restrict U.ι),
          (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens)) ≃ₗ[
        Γ((pullback.fst f t ⁻¹ᵁ U).toScheme,
          (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens))]
        Γ(((pullback (pullback.fst f t)).obj M).restrict
            (pullback.fst f t ⁻¹ᵁ U).ι,
          (⊤ : (pullback.fst f t ⁻¹ᵁ U).toScheme.Opens)) :=
    { eLocalAdd with
      map_smul' := Hom.app_smul
        (localPullbackRestrictIso (pullback.fst f t) M U).hom }
  let eLocalLiteral := eLocalLinear.toModuleIso
  exact (ModuleCat.extendScalars t.appTop.hom).mapIso
      (baseModulePresheafRestrictIso f M U) ≪≫
    tensorPushoutModuleIso e heA heB
      Γ(M.restrict U.ι, (⊤ : U.toScheme.Opens)) ≪≫
    (ModuleCat.restrictScalars
        ((pullback.fst f t ⁻¹ᵁ U).ι ≫ pullback.snd f t).appTop.hom).mapIso
      (affinePullbackΓIso (pullback.fst f t ∣_ U) (M.restrict U.ι)) ≪≫
    (ModuleCat.restrictScalars
        ((pullback.fst f t ⁻¹ᵁ U).ι ≫ pullback.snd f t).appTop.hom).mapIso
      eLocalLiteral ≪≫
    (baseModulePresheafRestrictIso (pullback.snd f t)
      ((pullback (pullback.fst f t)).obj M)
        (pullback.fst f t ⁻¹ᵁ U)).symm

end AlgebraicGeometry.Scheme.Modules
