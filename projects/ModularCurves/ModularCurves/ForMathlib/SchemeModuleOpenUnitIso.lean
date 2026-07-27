import ModularCurves.ForMathlib.SchemeModuleRestrictPushforward
import ModularCurves.Picard.DualPullback.OpenAdjunction

/-!
# Pullback--pushforward units over an isomorphism locus

This file proves that the pullback--pushforward unit is an isomorphism along an
isomorphism of schemes. It then compares the global unit with the unit of a
restriction to an open subscheme.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private theorem restrictAdjunction_unit_app_isIso_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    IsIso ((restrictAdjunction f).unit.app M) := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  rw [restrictAdjunction_unit_app_app]
  let e : f ''ᵁ f ⁻¹ᵁ U ≅ U := eqToIso (by
    rw [f.image_preimage_eq_opensRange_inf, f.opensRange_of_isIso,
      top_inf_eq])
  have he : homOfLE (f.image_preimage_le U) = e.hom :=
    Subsingleton.elim _ _
  rw [he]
  letI : IsIso e.hom := e.isIso_hom
  letI : IsIso e.hom.op := inferInstance
  exact Functor.map_isIso M.presheaf e.hom.op

/-- Pullback--pushforward along an isomorphism has invertible adjunction unit. -/
instance pullbackPushforwardAdjunction_unit_app_isIso_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app M) := by
  letI (N : Y.Modules) : IsIso ((restrictAdjunction f).unit.app N) :=
    restrictAdjunction_unit_app_isIso_of_isIso f N
  letI : IsIso (restrictAdjunction f).unit :=
    NatIso.isIso_of_isIso_app _
  let hRestrict := (restrictAdjunction f).fullyFaithfulLOfIsIsoUnit
  let hPullback := hRestrict.ofIso (restrictFunctorIsoPullback f)
  letI : (pullback f).Full := hPullback.full
  letI : (pullback f).Faithful := hPullback.faithful
  infer_instance

private def openRestrictPushforwardIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    pushforward f ⋙ restrictFunctor U.ι ≅
      restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U) :=
  restrictPushforwardIsoOfIsPullback f (f ∣_ U)
    (f ⁻¹ᵁ U).ι U.ι (isPullback_morphismRestrict f U)

private def openRestrictPushforwardSquare
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    TwoSquare (pushforward f) (restrictFunctor (f ⁻¹ᵁ U).ι)
      (restrictFunctor U.ι) (pushforward (f ∣_ U)) :=
  TwoSquare.mk _ _ _ _ (openRestrictPushforwardIso f U).hom

private theorem openRestrictPushforwardSquare_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (M : X.Modules) :
    (openRestrictPushforwardSquare f U).natTrans.app M =
      (openRestrictPushforwardIso f U).hom.app M :=
  rfl

private def openRestrictPushforwardMate
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :=
  mateEquiv (restrictAdjunction (f ⁻¹ᵁ U).ι)
    (restrictAdjunction U.ι) (openRestrictPushforwardSquare f U)

private lemma restrictMate_app_app_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (M : (f ⁻¹ᵁ U).toScheme.Modules) (V : Y.Opens)
    (x : Γ((pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).obj M, V)) :
    ((openRestrictPushforwardMate f U).app M).app V x =
      (((pushforward U.ι).map
        ((pushforward (f ∣_ U)).map
          ((restrictAdjunction (f ⁻¹ᵁ U).ι).counit.app M))).app V
        (((pushforward U.ι).map
          ((openRestrictPushforwardSquare f U).natTrans.app
            ((pushforward (f ⁻¹ᵁ U).ι).obj M))).app V
          (((restrictAdjunction U.ι).unit.app
            ((pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).obj M)).app V x))) := by
  simp only [openRestrictPushforwardMate, mateEquiv_apply, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
    Hom.comp_app, ConcreteCategory.comp_apply]
  rfl

private theorem openRestrictUnit_app_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (M : (f ⁻¹ᵁ U).toScheme.Modules) (V : Y.Opens)
    (x : Γ((pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).obj M, V)) :
    let q := (restrictAdjunction U.ι).unit.app
      ((pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).obj M)
    (q.app V).hom x =
      (M.presheaf.map
        (((Opens.map (f ⁻¹ᵁ U).ι.base).map
          ((Opens.map f.base).map
            (homOfLE (U.ι.image_preimage_le V)))).op)).hom x := by
  dsimp only
  rw [restrictAdjunction_unit_app_app]
  rfl

private theorem openRestrictPushforwardIso_push_app_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (M : (f ⁻¹ᵁ U).toScheme.Modules) (V : Y.Opens)
    (x : Γ((restrictFunctor U.ι).obj
      ((pushforward f).obj ((pushforward (f ⁻¹ᵁ U).ι).obj M)),
      U.ι ⁻¹ᵁ V)) :
    let h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      (isPullback_morphismRestrict f U) (U.ι ⁻¹ᵁ V)
    let q := (pushforward U.ι).map
      ((openRestrictPushforwardIso f U).hom.app
        ((pushforward (f ⁻¹ᵁ U).ι).obj M))
    (q.app V).hom x =
      (M.presheaf.map
        (((Opens.map (f ⁻¹ᵁ U).ι.base).map (eqToHom h)).op)).hom x := by
  dsimp only
  rfl

private theorem openRestrictCounit_app_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (M : (f ⁻¹ᵁ U).toScheme.Modules) (V : Y.Opens)
    (x : Γ((pushforward U.ι).obj
      ((pushforward (f ∣_ U)).obj
        ((pushforward (f ⁻¹ᵁ U).ι ⋙
          restrictFunctor (f ⁻¹ᵁ U).ι).obj M)), V)) :
    let q := (pushforward U.ι).map
      ((pushforward (f ∣_ U)).map
        ((restrictAdjunction (f ⁻¹ᵁ U).ι).counit.app M))
    (q.app V).hom x =
      (M.presheaf.map
        (eqToHom ((f ⁻¹ᵁ U).ι.preimage_image_eq
          ((f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ V))).symm).op).hom x := by
  dsimp only
  rw [pushforward_map_app, pushforward_map_app,
    restrictAdjunction_counit_app_app]
  apply ConcreteCategory.congr_hom
  exact M.presheaf.congr_map (Subsingleton.elim _ _)

private theorem openPushforwardSquareIso_inv_app_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (M : (f ⁻¹ᵁ U).toScheme.Modules) (V : Y.Opens)
    (x : Γ((pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).obj M, V)) :
    let hpre : (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ V) =
        (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
      exact congrArg
        (fun q : (f ⁻¹ᵁ U).toScheme ⟶ Y ↦ q ⁻¹ᵁ V)
        (morphismRestrict_ι f U)
    (((openPushforwardSquareIsoT f U).inv.app M).app V).hom x =
      (M.presheaf.map (eqToHom hpre).op).hom x := by
  dsimp only
  simp only [openPushforwardSquareIsoT, Iso.trans_inv, NatTrans.comp_app,
    Hom.comp_app, pushforwardComp_inv_app_app,
    pushforwardCongr_inv_app_app]
  rfl

private theorem openRestrictPushforwardMate_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (openRestrictPushforwardMate f U).natTrans =
      (openPushforwardSquareIsoT f U).inv := by
  ext M V x
  rw [restrictMate_app_app_apply, openRestrictPushforwardSquare_app]
  let unitValue := (((restrictAdjunction U.ι).unit.app
    ((pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).obj M)).app V).hom x
  let directMap := (((pushforward U.ι).map
    ((openRestrictPushforwardIso f U).hom.app
      ((pushforward (f ⁻¹ᵁ U).ι).obj M))).app V).hom
  let directValue := directMap unitValue
  let counitMap := (((pushforward U.ι).map
    ((pushforward (f ∣_ U)).map
      ((restrictAdjunction (f ⁻¹ᵁ U).ι).counit.app M))).app V).hom
  let a := ((Opens.map (f ⁻¹ᵁ U).ι.base).map
    ((Opens.map f.base).map
      (homOfLE (U.ι.image_preimage_le V)))).op
  let h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (isPullback_morphismRestrict f U) (U.ι ⁻¹ᵁ V)
  let b := ((Opens.map (f ⁻¹ᵁ U).ι.base).map (eqToHom h)).op
  let c := (eqToHom ((f ⁻¹ᵁ U).ι.preimage_image_eq
    ((f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ V))).symm).op
  let hpre : (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ V) =
      (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    exact congrArg
      (fun q : (f ⁻¹ᵁ U).toScheme ⟶ Y ↦ q ⁻¹ᵁ V)
      (morphismRestrict_ι f U)
  let r := (eqToHom hpre).op
  change counitMap directValue = _
  have hunit : unitValue = (M.presheaf.map a).hom x := by
    dsimp only [unitValue, a]
    exact openRestrictUnit_app_apply f U M V x
  have hdirect : directValue = (M.presheaf.map b).hom unitValue := by
    dsimp only [directValue, directMap, b, h]
    exact openRestrictPushforwardIso_push_app_apply f U M V unitValue
  have hcounit :
      counitMap directValue = (M.presheaf.map c).hom directValue := by
    dsimp only [counitMap, c]
    exact openRestrictCounit_app_apply f U M V directValue
  have hright :
      (((openPushforwardSquareIsoT f U).inv.app M).app V).hom x =
        (M.presheaf.map r).hom x := by
    dsimp only [r, hpre]
    exact openPushforwardSquareIso_inv_app_apply f U M V x
  refine hcounit.trans ?_
  refine (congrArg (M.presheaf.map c).hom hdirect).trans ?_
  refine (congrArg
    (fun z ↦ (M.presheaf.map c).hom ((M.presheaf.map b).hom z))
    hunit).trans ?_
  have hmaps :
      M.presheaf.map a ≫ M.presheaf.map b ≫ M.presheaf.map c =
        M.presheaf.map r := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact M.presheaf.congr_map (Subsingleton.elim _ _)
  let x' : M.presheaf.obj
      (.op ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ V))) := x
  have hsections :
      (M.presheaf.map c).hom
          ((M.presheaf.map b).hom ((M.presheaf.map a).hom x)) =
        (M.presheaf.map r).hom x := by
    change (M.presheaf.map c).hom
        ((M.presheaf.map b).hom ((M.presheaf.map a).hom x')) =
      (M.presheaf.map r).hom x'
    exact ConcreteCategory.congr_hom hmaps x'
  exact hsections.trans hright.symm

private def openPullbackRestrictMate
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :=
  ((mateEquiv (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction (f ∣_ U))).symm
      (openRestrictPushforwardSquare f U)).natTrans

private def openPullbackExplicitSquare
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    TwoSquare (restrictFunctor U.ι) (pullback f)
      (pullback (f ∣_ U)) (restrictFunctor (f ⁻¹ᵁ U).ι) :=
  TwoSquare.mk _ _ _ _ (openPullbackSquareExplicitIsoT f U).hom

private theorem openPullbackExplicitSquare_iteratedMate_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (mateEquiv (restrictAdjunction (f ⁻¹ᵁ U).ι)
      (restrictAdjunction U.ι)
      (mateEquiv (pullbackPushforwardAdjunction f)
        (pullbackPushforwardAdjunction (f ∣_ U))
        (openPullbackExplicitSquare f U))).natTrans =
      (openPushforwardSquareIsoT f U).inv := by
  rw [iterated_mateEquiv_conjugateEquiv]
  exact conjugateEquiv_openPullbackSquareExplicitIso_homT f U

private theorem openPullbackExplicitSquare_mate_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    mateEquiv (pullbackPushforwardAdjunction f)
        (pullbackPushforwardAdjunction (f ∣_ U))
        (openPullbackExplicitSquare f U) =
      openRestrictPushforwardSquare f U := by
  let restrictMate := mateEquiv
    (G := pushforward f) (H := pushforward (f ∣_ U))
    (restrictAdjunction (f ⁻¹ᵁ U).ι) (restrictAdjunction U.ι)
  apply restrictMate.injective
  exact (openPullbackExplicitSquare_iteratedMate_eq f U).trans
    (openRestrictPushforwardMate_eq f U).symm

private theorem openPullbackRestrictMate_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    openPullbackRestrictMate f U =
      (openPullbackSquareExplicitIsoT f U).hom := by
  let pullMate := mateEquiv
    (G := restrictFunctor U.ι) (H := restrictFunctor (f ⁻¹ᵁ U).ι)
    (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction (f ∣_ U))
  change (pullMate.symm (openRestrictPushforwardSquare f U)).natTrans =
    (openPullbackExplicitSquare f U).natTrans
  have h :
      pullMate.symm (openRestrictPushforwardSquare f U) =
        openPullbackExplicitSquare f U := by
    apply pullMate.injective
    rw [pullMate.apply_symm_apply]
    exact (openPullbackExplicitSquare_mate_eq f U).symm
  exact congrArg TwoSquare.natTrans h

/-- If the unit for a morphism restricted over an open is invertible, then the
restriction of the original unit to that open is invertible. -/
theorem isIso_restrict_pullbackPushforward_unit_of_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (M : Y.Modules)
    [IsIso
      ((pullbackPushforwardAdjunction
        (f ∣_ U)).unit.app
          ((restrictFunctor U.ι).obj M))] :
    IsIso ((restrictFunctor U.ι).map
      ((pullbackPushforwardAdjunction f).unit.app M)) := by
  let a := (restrictFunctor U.ι).map
    ((pullbackPushforwardAdjunction f).unit.app M)
  let b := (openRestrictPushforwardIso f U).hom.app
    ((pullback f).obj M)
  let c := (pullbackPushforwardAdjunction (f ∣_ U)).unit.app
    ((restrictFunctor U.ι).obj M)
  let d := (pushforward (f ∣_ U)).map
    ((openPullbackSquareExplicitIsoT f U).hom.app M)
  have hmate (N : Y.Modules) :
      (((mateEquiv (pullbackPushforwardAdjunction f)
        (pullbackPushforwardAdjunction (f ∣_ U))).symm
          (openRestrictPushforwardSquare f U)).app N) =
        (openPullbackSquareExplicitIsoT f U).hom.app N := by
    exact congrArg (fun q ↦ q.app N) (openPullbackRestrictMate_eq f U)
  have hunit : a ≫ b = c ≫ d := by
    have h := unit_mateEquiv_symm
      (pullbackPushforwardAdjunction f)
      (pullbackPushforwardAdjunction (f ∣_ U))
      (openRestrictPushforwardSquare f U) M
    rw [hmate ((𝟭 Y.Modules).obj M)] at h
    change a ≫ b = c ≫ d at h
    exact h
  haveI hb : IsIso b := by
    dsimp only [b]
    infer_instance
  haveI hc : IsIso c := by
    dsimp only [c]
    infer_instance
  haveI hd : IsIso d := by
    dsimp only [d]
    infer_instance
  haveI hab : IsIso (a ≫ b) := by
    rw [hunit]
    infer_instance
  exact IsIso.of_isIso_comp_right a b

/-- The pullback--pushforward unit is invertible after restriction to an open
subscheme on which the morphism itself is an isomorphism. -/
theorem isIso_restrict_pullbackPushforward_unit_of_isIso_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [IsIso (f ∣_ U)] (M : Y.Modules) :
    IsIso ((restrictFunctor U.ι).map
      ((pullbackPushforwardAdjunction f).unit.app M)) :=
  isIso_restrict_pullbackPushforward_unit_of_restrict f U M

end

end AlgebraicGeometry.Scheme.Modules
