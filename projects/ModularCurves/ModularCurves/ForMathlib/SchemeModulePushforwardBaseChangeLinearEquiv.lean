import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward

/-!
# Global sections from an isomorphic pushforward base-change component

For affine source and target bases, an isomorphic component of the
pullback--pushforward base-change morphism induces the expected linear
equivalence on global sections.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An isomorphic top component of a pushforward base-change morphism
induces the corresponding scalar-extension equivalence on base-linear
global sections. -/
noncomputable def baseSectionsPushforwardBaseChangeLinearEquivOfAppTopIso
    {X S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    [((pushforward f).obj M).IsQuasicoherent]
    (MT : (Limits.pullback f t).Modules)
    (φ : (pullback t).obj ((pushforward f).obj M) ⟶
      (pushforward (pullback.snd f t)).obj MT)
    [IsIso (φ.val.app (.op (⊤ : T.Opens)))] :
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    A ⊗[B] baseSections f M ≃ₗ[A]
      baseSections (pullback.snd f t) MT := by
  dsimp only
  let N := (pushforward f).obj M
  let q := pullback.snd f t
  let ePush :=
    baseSectionsPushforwardTopIso f M ≪≫
      (baseModulePresheafIdTopIso N).symm
  let eSourceIso :=
    (ModuleCat.extendScalars t.appTop.hom).mapIso
        ePush ≪≫
      affinePullbackΓIso t N
  let eTargetTopIso :=
    baseSectionsPushforwardTopIso q MT ≪≫
      (baseModulePresheafIdTopIso ((pushforward q).obj MT)).symm
  let φTop :
      Γ((pullback t).obj N, (⊤ : T.Opens)) →ₗ[Γ(T, (⊤ : T.Opens))]
        Γ((pushforward q).obj MT, (⊤ : T.Opens)) :=
    (φ.val.app (.op (⊤ : T.Opens))).hom
  have hφTop : Function.Bijective φTop := by
    exact ConcreteCategory.bijective_of_isIso
      (φ.val.app (.op (⊤ : T.Opens)))
  let eφ := LinearEquiv.ofBijective φTop hφTop
  exact eSourceIso.toLinearEquiv.trans
    (eφ.trans eTargetTopIso.symm.toLinearEquiv)

/-- The global-sections base-change equivalence sends a pure tensor with
coefficient one to the section represented by the canonical pullback unit
and the supplied base-change component. -/
theorem baseSectionsPushforwardBaseChangeLinearEquivOfAppTopIso_one_tmul
    {X S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    [((pushforward f).obj M).IsQuasicoherent]
    (MT : (Limits.pullback f t).Modules)
    (φ : (pullback t).obj ((pushforward f).obj M) ⟶
      (pushforward (pullback.snd f t)).obj MT)
    [IsIso (φ.val.app (.op (⊤ : T.Opens)))]
    (s : baseSections f M) :
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    pushforwardTopSection (pullback.snd f t) MT
        (baseSectionsPushforwardBaseChangeLinearEquivOfAppTopIso
          f t M MT φ ((1 : A) ⊗ₜ[B] s)) =
      (φ.val.app (.op (⊤ : T.Opens)))
        (affinePullbackUnitTop t ((pushforward f).obj M)
          (pushforwardTopSection f M s)) := by
  dsimp only
  let N := (pushforward f).obj M
  let q := pullback.snd f t
  let ePush :=
    baseSectionsPushforwardTopIso f M ≪≫
      (baseModulePresheafIdTopIso N).symm
  let eSourceIso :=
    (ModuleCat.extendScalars t.appTop.hom).mapIso ePush ≪≫
      affinePullbackΓIso t N
  let eSource := eSourceIso.toLinearEquiv
  let eTargetTopIso :=
    baseSectionsPushforwardTopIso q MT ≪≫
      (baseModulePresheafIdTopIso ((pushforward q).obj MT)).symm
  let eTargetTop := eTargetTopIso.toLinearEquiv
  let φTop :
      Γ((pullback t).obj N, (⊤ : T.Opens)) →ₗ[Γ(T, (⊤ : T.Opens))]
        Γ((pushforward q).obj MT, (⊤ : T.Opens)) :=
    (φ.val.app (.op (⊤ : T.Opens))).hom
  have hφTop : Function.Bijective φTop := by
    exact ConcreteCategory.bijective_of_isIso
      (φ.val.app (.op (⊤ : T.Opens)))
  let eφ := LinearEquiv.ofBijective φTop hφTop
  have hSource :
      eSource ((1 : Γ(T, (⊤ : T.Opens))) ⊗ₜ[Γ(S, (⊤ : S.Opens))] s) =
        affinePullbackUnitTop t N (pushforwardTopSection f M s) := by
    change (affinePullbackΓIso t N).hom
        (((ModuleCat.extendScalars t.appTop.hom).map ePush.hom)
          ((1 : Γ(T, (⊤ : T.Opens)))
            ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom] s)) = _
    rw [ModuleCat.ExtendScalars.map_tmul
      (f := t.appTop.hom) ePush.hom
        (1 : Γ(T, (⊤ : T.Opens))) s]
    change (affinePullbackΓIso t N).hom
        ((1 : Γ(T, (⊤ : T.Opens))) ⊗ₜ[Γ(S, (⊤ : S.Opens))]
          (baseModulePresheafIdTopIso N).inv
            ((baseSectionsPushforwardTopIso f M).hom s)) = _
    rw [baseSectionsPushforwardTopIso_hom_apply]
    exact affinePullbackΓIso_hom_one_tmul t N
      (pushforwardTopSection f M s)
  have hTarget (m : baseSections q MT) :
      eTargetTop m = pushforwardTopSection q MT m := by
    change (baseModulePresheafIdTopIso ((pushforward q).obj MT)).inv
        ((baseSectionsPushforwardTopIso q MT).hom m) = _
    rw [baseSectionsPushforwardTopIso_hom_apply]
    rfl
  change pushforwardTopSection q MT
      ((eSource.trans (eφ.trans eTargetTop.symm))
        ((1 : Γ(T, (⊤ : T.Opens))) ⊗ₜ[Γ(S, (⊤ : S.Opens))] s)) =
    _
  change pushforwardTopSection q MT
      (eTargetTop.symm (eφ
        (eSource
          ((1 : Γ(T, (⊤ : T.Opens))) ⊗ₜ[Γ(S, (⊤ : S.Opens))] s)))) =
    _
  rw [hSource]
  rw [← hTarget]
  exact eTargetTop.apply_symm_apply _

end AlgebraicGeometry.Scheme.Modules
