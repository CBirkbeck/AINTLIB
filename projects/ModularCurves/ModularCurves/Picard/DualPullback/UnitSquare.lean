import ModularCurves.Picard.DualPullback.UnitComp

/-!
# Pullback-square compatibility for structure modules

The pullback-square isomorphism sends the canonical structure-module comparison to the
canonical comparison around the pasted square.
-/

universe u

open AlgebraicGeometry CategoryTheory


namespace ModularCurves

theorem pullbackComp_inv_unitPairLow
    {A C D : Scheme.{u}} (c : A ⟶ C) (d : C ⟶ D) :
    ((Scheme.Modules.pullbackComp c d).app
          (Scheme.Modules.unitObj D)).inv ≫
        (Scheme.Modules.pullback c).map
          (Scheme.Modules.pullbackUnitIso d).hom ≫
        (Scheme.Modules.pullbackUnitIso c).hom =
      (Scheme.Modules.pullbackUnitIso (c ≫ d)).hom := by
  let e := (Scheme.Modules.pullbackComp c d).app
    (Scheme.Modules.unitObj D)
  have h := pullbackUnitIso_compLow c d
  calc
    e.inv ≫ ((Scheme.Modules.pullback c).map
          (Scheme.Modules.pullbackUnitIso d).hom ≫
        (Scheme.Modules.pullbackUnitIso c).hom) =
      e.inv ≫ (e.hom ≫
        (Scheme.Modules.pullbackUnitIso (c ≫ d)).hom) :=
      congrArg (fun k => e.inv ≫ k) h.symm
    _ = (Scheme.Modules.pullbackUnitIso (c ≫ d)).hom :=
      e.inv_hom_id_assoc _

theorem pullbackSquareIso_unitLow
    {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) :
    (Scheme.Modules.pullbackSquareIso a b c d h).hom.app
          (Scheme.Modules.unitObj D) ≫
        (Scheme.Modules.pullback c).map
          (Scheme.Modules.pullbackUnitIso d).hom ≫
        (Scheme.Modules.pullbackUnitIso c).hom =
      (Scheme.Modules.pullback a).map
          (Scheme.Modules.pullbackUnitIso b).hom ≫
        (Scheme.Modules.pullbackUnitIso a).hom := by
  let α := (Scheme.Modules.pullbackComp a b).app
    (Scheme.Modules.unitObj D)
  let γ := (Scheme.Modules.pullbackCongr h).app
    (Scheme.Modules.unitObj D)
  let β := (Scheme.Modules.pullbackComp c d).app
    (Scheme.Modules.unitObj D)
  have hβ := pullbackComp_inv_unitPairLow c d
  have hγ := pullbackUnitIso_congrLow h
  have hα := pullbackUnitIso_compLow a b
  change (α.hom ≫ γ.hom ≫ β.inv) ≫
      (Scheme.Modules.pullback c).map
        (Scheme.Modules.pullbackUnitIso d).hom ≫
      (Scheme.Modules.pullbackUnitIso c).hom = _
  calc
    (α.hom ≫ γ.hom ≫ β.inv) ≫
        (Scheme.Modules.pullback c).map
          (Scheme.Modules.pullbackUnitIso d).hom ≫
        (Scheme.Modules.pullbackUnitIso c).hom =
      α.hom ≫ γ.hom ≫
        (β.inv ≫
          (Scheme.Modules.pullback c).map
            (Scheme.Modules.pullbackUnitIso d).hom ≫
          (Scheme.Modules.pullbackUnitIso c).hom) := by
      simp only [Category.assoc]
    _ = α.hom ≫ γ.hom ≫
        (Scheme.Modules.pullbackUnitIso (c ≫ d)).hom :=
      congrArg (fun k => α.hom ≫ γ.hom ≫ k) hβ
    _ = α.hom ≫
        (Scheme.Modules.pullbackUnitIso (a ≫ b)).hom :=
      congrArg (fun k => α.hom ≫ k) hγ
    _ = (Scheme.Modules.pullback a).map
          (Scheme.Modules.pullbackUnitIso b).hom ≫
        (Scheme.Modules.pullbackUnitIso a).hom := hα

end ModularCurves

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable def unitSquareLeftVerticalO (f : Y ⟶ X)
    (V : X.Opens) : (f ⁻¹ᵁ V : Scheme) ⟶ V := f ∣_ V

noncomputable def unitSquareTopO {U V : X.Opens}
    (i : V ⟶ U) : (V : Scheme) ⟶ (U : Scheme) :=
  X.homOfLE (leOfHom i)

noncomputable def unitSquareBottomO (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    (f ⁻¹ᵁ V : Scheme) ⟶ (f ⁻¹ᵁ U : Scheme) :=
  Y.homOfLE (f.preimage_mono (leOfHom i))

instance unitSquareTopO_isOpenImmersion {U V : X.Opens} (i : V ⟶ U) :
    IsOpenImmersion (unitSquareTopO i) := by
  dsimp only [unitSquareTopO]
  infer_instance

instance unitSquareBottomO_isOpenImmersion (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    IsOpenImmersion (unitSquareBottomO f i) := by
  dsimp only [unitSquareBottomO]
  infer_instance

noncomputable def unitSquareRightVerticalO (f : Y ⟶ X)
    (U : X.Opens) : (f ⁻¹ᵁ U : Scheme) ⟶ U := f ∣_ U

theorem unitSquareLeftVerticalO_eq (f : Y ⟶ X) (V : X.Opens) :
    unitSquareLeftVerticalO f V = f ∣_ V := rfl

theorem unitSquareTopO_eq {U V : X.Opens} (i : V ⟶ U) :
    unitSquareTopO i = X.homOfLE (leOfHom i) := rfl

theorem unitSquareBottomO_eq (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    unitSquareBottomO f i =
      Y.homOfLE (f.preimage_mono (leOfHom i)) := rfl

theorem unitSquareRightVerticalO_eq (f : Y ⟶ X) (U : X.Opens) :
    unitSquareRightVerticalO f U = f ∣_ U := rfl

theorem unitSquare_commO (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    unitSquareLeftVerticalO f V ≫ unitSquareTopO i =
      unitSquareBottomO f i ≫ unitSquareRightVerticalO f U :=
  morphismRestrict_homOfLE f V U (leOfHom i)

noncomputable def unitNatSquareO (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  (pullbackSquareIso (unitSquareLeftVerticalO f V) (unitSquareTopO i)
    (unitSquareBottomO f i) (unitSquareRightVerticalO f U)
    (unitSquare_commO f i)).hom.app (unitObj U)

noncomputable def unitNatSourceAfterO (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  (pullback (unitSquareBottomO f i)).map
      (pullbackUnitIso (unitSquareRightVerticalO f U)).hom ≫
    (pullbackUnitIso (unitSquareBottomO f i)).hom

noncomputable def unitNatTargetAfterO (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  (pullback (unitSquareLeftVerticalO f V)).map
      (pullbackUnitIso (unitSquareTopO i)).hom ≫
    (pullbackUnitIso (unitSquareLeftVerticalO f V)).hom

theorem unitNat_square_sourceAfterO (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    unitNatSquareO f i ≫ unitNatSourceAfterO f i =
      unitNatTargetAfterO f i :=
  ModularCurves.pullbackSquareIso_unitLow
    (unitSquareLeftVerticalO f V) (unitSquareTopO i)
    (unitSquareBottomO f i) (unitSquareRightVerticalO f U)
    (unitSquare_commO f i)

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem overEquiv_unitObj_eqG (U : X.Opens) :
    (overEquiv U).functor.obj
        (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)) =
      unitObj U := by
  rfl

noncomputable def openPullbackRestrictIsoGroupedG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    restrictFunctor (X.homOfLE (leOfHom i)) ⋙ pullback (f ∣_ V) ≅
      pullback (f ∣_ U) ⋙
        restrictFunctor
          (Y.homOfLE (f.preimage_mono (leOfHom i))) :=
  Functor.isoWhiskerRight
      (restrictFunctorIsoPullback (unitSquareTopO i))
      (pullback (unitSquareLeftVerticalO f V)) ≪≫
    pullbackSquareIso (unitSquareLeftVerticalO f V) (unitSquareTopO i)
      (unitSquareBottomO f i) (unitSquareRightVerticalO f U)
      (unitSquare_commO f i) ≪≫
    Functor.isoWhiskerLeft (pullback (unitSquareRightVerticalO f U))
      (restrictFunctorIsoPullback
        (unitSquareBottomO f i)).symm

noncomputable def unitNatRhoG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  (pullback (unitSquareLeftVerticalO f V)).map
    ((restrictFunctorIsoPullback
      (unitSquareTopO i)).hom.app (unitObj U))

noncomputable def unitNatSquareG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  unitNatSquareO f i

noncomputable def unitNatSourceBeforeG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  (restrictFunctorIsoPullback (unitSquareBottomO f i)).inv.app
      ((pullback (unitSquareRightVerticalO f U)).obj (unitObj U)) ≫
    (restrictFunctor (unitSquareBottomO f i)).map
      (pullbackUnitIso (unitSquareRightVerticalO f U)).hom ≫
    (restrictUnitIso (unitSquareBottomO f i)).hom

noncomputable def unitNatSourceAfterG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  unitNatSourceAfterO f i

theorem unitNat_sourceBefore_eq_afterG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    unitNatSourceBeforeG f i = unitNatSourceAfterG f i := by
  let y := unitSquareBottomO f i
  let fu := unitSquareRightVerticalO f U
  letI : IsOpenImmersion y := by
    dsimp only [y]
    infer_instance
  let e := restrictFunctorIsoPullback y
  have hnat := e.inv.naturality (pullbackUnitIso fu).hom
  have hunit :=
    ModularCurves.restrictFunctorIsoPullback_inv_comp_restrictUnitIsoLow y
  have hfirst : e.inv.app ((pullback fu).obj (unitObj U)) ≫
      (restrictFunctor y).map (pullbackUnitIso fu).hom ≫
      (restrictUnitIso y).hom =
    (pullback y).map (pullbackUnitIso fu).hom ≫
      e.inv.app (unitObj (f ⁻¹ᵁ U)) ≫ (restrictUnitIso y).hom :=
    CategoryTheory.two_eq_two_assoc hnat.symm (restrictUnitIso y).hom
  have hsecond : (pullback y).map (pullbackUnitIso fu).hom ≫
      e.inv.app (unitObj (f ⁻¹ᵁ U)) ≫ (restrictUnitIso y).hom =
    (pullback y).map (pullbackUnitIso fu).hom ≫
      (pullbackUnitIso y).hom :=
    congrArg (fun k => (pullback y).map (pullbackUnitIso fu).hom ≫ k) hunit
  exact hfirst.trans hsecond

noncomputable def unitNatStage0G (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  unitNatRhoG f i ≫ unitNatSquareG f i ≫ unitNatSourceBeforeG f i

noncomputable def unitNatStage1G (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  unitNatRhoG f i ≫ unitNatSquareG f i ≫ unitNatSourceAfterG f i

theorem unitNat_stage0_eq_stage1G (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    unitNatStage0G f i = unitNatStage1G f i :=
  congrArg (fun k => unitNatRhoG f i ≫ unitNatSquareG f i ≫ k)
    (unitNat_sourceBefore_eq_afterG f i)

theorem unitNat_left_eq_stage0G (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    (openPullbackRestrictIsoGroupedG f i).hom.app (unitObj U) ≫
        (restrictFunctor (unitSquareBottomO f i)).map
          (pullbackUnitIso (unitSquareRightVerticalO f U)).hom ≫
        (restrictUnitIso (unitSquareBottomO f i)).hom =
      unitNatStage0G f i := by
  simp only [openPullbackRestrictIsoGroupedG, unitNatStage0G,
    unitNatRhoG, unitNatSquareG, unitNatSourceBeforeG,
    Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc]
  rfl

noncomputable def unitNatTargetAfterG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  unitNatTargetAfterO f i

theorem unitNat_square_sourceAfterG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    unitNatSquareG f i ≫ unitNatSourceAfterG f i =
      unitNatTargetAfterG f i :=
  unitNat_square_sourceAfterO f i

noncomputable def unitNatStage2G (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  unitNatRhoG f i ≫ unitNatTargetAfterG f i

theorem unitNat_stage1_eq_stage2G (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    unitNatStage1G f i = unitNatStage2G f i :=
  congrArg (fun k => unitNatRhoG f i ≫ k)
    (unitNat_square_sourceAfterG f i)

theorem restrictFunctorIsoPullback_hom_comp_pullbackUnitIsoG
    (f : Y ⟶ X) [IsOpenImmersion f] :
    (restrictFunctorIsoPullback f).hom.app (unitObj X) ≫
        (pullbackUnitIso f).hom =
      (restrictUnitIso f).hom := by
  let e := (restrictFunctorIsoPullback f).app (unitObj X)
  have h :=
    ModularCurves.restrictFunctorIsoPullback_inv_comp_restrictUnitIsoLow f
  change e.hom ≫ (pullbackUnitIso f).hom = (restrictUnitIso f).hom
  exact (e.inv_comp_eq.mp h).symm

noncomputable def unitNatTargetG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  (pullback (unitSquareLeftVerticalO f V)).map
      (restrictUnitIso (unitSquareTopO i)).hom ≫
    (pullbackUnitIso (unitSquareLeftVerticalO f V)).hom

theorem unitNat_stage2_eq_targetG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    unitNatStage2G f i = unitNatTargetG f i := by
  let P := pullback (unitSquareLeftVerticalO f V)
  let a :=
    (restrictFunctorIsoPullback (unitSquareTopO i)).hom.app (unitObj U)
  let b := (pullbackUnitIso (unitSquareTopO i)).hom
  have hbase := congrArg P.map
    (restrictFunctorIsoPullback_hom_comp_pullbackUnitIsoG
      (unitSquareTopO i))
  have hmap : unitNatRhoG f i ≫ P.map b =
      P.map (restrictUnitIso (unitSquareTopO i)).hom := by
    have hfirst : unitNatRhoG f i ≫ P.map b = P.map a ≫ P.map b := rfl
    have hsecond : P.map a ≫ P.map b = P.map (a ≫ b) :=
      (P.map_comp a b).symm
    exact hfirst.trans (hsecond.trans hbase)
  let z := (pullbackUnitIso (unitSquareLeftVerticalO f V)).hom
  change unitNatRhoG f i ≫ (P.map b ≫ z) =
    P.map (restrictUnitIso (unitSquareTopO i)).hom ≫ z
  have hassoc : unitNatRhoG f i ≫ (P.map b ≫ z) =
      (unitNatRhoG f i ≫ P.map b) ≫ z :=
    (Category.assoc _ _ _).symm
  exact hassoc.trans (congrArg (fun k => k ≫ z) hmap)

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem unitNat_rawStage0_eq_targetG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    (pullback (f ∣_ V)).map
          ((restrictFunctorIsoPullback
            (X.homOfLE (leOfHom i))).hom.app (unitObj U)) ≫
        (pullbackSquareIso (f ∣_ V) (X.homOfLE (leOfHom i))
          (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ∣_ U)
          (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app
            (unitObj U) ≫
        ((restrictFunctorIsoPullback
            (Y.homOfLE (f.preimage_mono (leOfHom i)))).inv.app
              ((pullback (f ∣_ U)).obj (unitObj U)) ≫
          (restrictFunctor
            (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
              (pullbackUnitIso (f ∣_ U)).hom ≫
          (restrictUnitIso
            (Y.homOfLE (f.preimage_mono (leOfHom i)))).hom) =
      (pullback (f ∣_ V)).map
          (restrictUnitIso (X.homOfLE (leOfHom i))).hom ≫
        (pullbackUnitIso (f ∣_ V)).hom := by
  have h := (unitNat_stage0_eq_stage1G f i).trans
    ((unitNat_stage1_eq_stage2G f i).trans
      (unitNat_stage2_eq_targetG f i))
  unfold unitNatStage0G unitNatRhoG unitNatSquareG
    unitNatSourceBeforeG unitNatTargetG at h
  simp only [unitSquareBottomO_eq, unitSquareRightVerticalO_eq,
    unitSquareLeftVerticalO_eq, unitSquareTopO_eq] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
