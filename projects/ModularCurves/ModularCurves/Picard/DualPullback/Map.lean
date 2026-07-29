import ModularCurves.Picard.DualPullback.UnitRestriction

/-!
# The canonical pullback map on dual modules

Local pullback of functionals is natural under restriction, hence bundles to the canonical
map `f^*(M^∨) ⟶ (f^*M)^∨`.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable def dualNatAlphaG (M : X.Modules) (U : X.Opens)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (overEquiv U).functor.obj (M.over U) ⟶ unitObj U :=
  (overEquiv U).functor.map α

noncomputable def dualNatModulePrefixG (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (localPullbackModuleIso f M V).inv ≫
    (pullback (f ∣_ V)).map (overRestrictModuleIso M i).hom

noncomputable def dualNatPullAlphaG (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  (pullback (f ∣_ V)).map
    ((restrictFunctor (X.homOfLE (leOfHom i))).map
      (dualNatAlphaG M U α))

noncomputable def dualNatOpenModuleG (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (openPullbackRestrictIso f i).hom.app
    ((overEquiv U).functor.obj (M.over U))

noncomputable def dualNatRestrictPullAlphaG (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  (restrictFunctor
    (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
      ((pullback (f ∣_ U)).map (dualNatAlphaG M U α))

noncomputable def dualNatUnitTailG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :=
  (restrictFunctor
      (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
        (localPullbackUnitIso f U).hom ≫
    (overRestrictUnitIso
      ((TopologicalSpace.Opens.map f.base).map i)).hom

noncomputable def dualNatModuleRightG (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U) :=
  (overRestrictModuleIso ((pullback f).obj M)
      ((TopologicalSpace.Opens.map f.base).map i)).hom ≫
    (restrictFunctor
      (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
        (localPullbackModuleIso f M U).inv

noncomputable def dualNatStage0G (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  dualNatModulePrefixG f M i ≫ dualNatPullAlphaG f M i α ≫
    localPullbackUnitRestrictRightG f i

noncomputable def dualNatStage1G (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  dualNatModulePrefixG f M i ≫ dualNatPullAlphaG f M i α ≫
    localPullbackUnitRestrictLeftG f i

theorem dualNat_stage0_eq_stage1G (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    dualNatStage0G f M i α = dualNatStage1G f M i α :=
  congrArg (fun k => dualNatModulePrefixG f M i ≫
      dualNatPullAlphaG f M i α ≫ k)
    (localPullbackUnitIso_restrict_homG f i).symm

noncomputable def dualNatStage2G (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  dualNatModulePrefixG f M i ≫ dualNatOpenModuleG f M i ≫
    dualNatRestrictPullAlphaG f M i α ≫ dualNatUnitTailG f i

theorem dualNat_pullAlpha_unitLeftG (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    dualNatPullAlphaG f M i α ≫ localPullbackUnitRestrictLeftG f i =
      dualNatOpenModuleG f M i ≫
        dualNatRestrictPullAlphaG f M i α ≫ dualNatUnitTailG f i := by
  let a := dualNatAlphaG M U α
  have h := (openPullbackRestrictIso f i).hom.naturality a
  unfold dualNatPullAlphaG localPullbackUnitRestrictLeftG
    dualNatOpenModuleG dualNatRestrictPullAlphaG dualNatUnitTailG
  exact CategoryTheory.two_eq_two_assoc h
    ((restrictFunctor
      (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
        (localPullbackUnitIso f U).hom ≫
      (overRestrictUnitIso
        ((TopologicalSpace.Opens.map f.base).map i)).hom)

theorem dualNat_stage1_eq_stage2G (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    dualNatStage1G f M i α = dualNatStage2G f M i α :=
  congrArg (fun k => dualNatModulePrefixG f M i ≫ k)
    (dualNat_pullAlpha_unitLeftG f M i α)

noncomputable def dualNatStage3G (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  dualNatModuleRightG f M i ≫ dualNatRestrictPullAlphaG f M i α ≫
    dualNatUnitTailG f i

noncomputable def dualNatStage2GroupedG (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  (dualNatModulePrefixG f M i ≫ dualNatOpenModuleG f M i) ≫
    (dualNatRestrictPullAlphaG f M i α ≫ dualNatUnitTailG f i)

theorem dualNat_stage2_eq_groupedG (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    dualNatStage2G f M i α = dualNatStage2GroupedG f M i α := by
  unfold dualNatStage2G dualNatStage2GroupedG
  exact (Category.assoc _ _ _).symm

theorem dualNat_grouped_eq_stage3G (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    dualNatStage2GroupedG f M i α = dualNatStage3G f M i α := by
  have h := localPullbackModuleIso_restrictS f M i
  have h' : dualNatModulePrefixG f M i ≫ dualNatOpenModuleG f M i =
      dualNatModuleRightG f M i := h
  unfold dualNatStage2GroupedG dualNatStage3G
  exact congrArg
    (fun k => k ≫
      (dualNatRestrictPullAlphaG f M i α ≫ dualNatUnitTailG f i)) h'

theorem dualNat_stage2_eq_stage3G (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    dualNatStage2G f M i α = dualNatStage3G f M i α :=
  (dualNat_stage2_eq_groupedG f M i α).trans
    (dualNat_grouped_eq_stage3G f M i α)

theorem dualNatStage0_eq_stage3G (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    dualNatStage0G f M i α = dualNatStage3G f M i α :=
  (dualNat_stage0_eq_stage1G f M i α).trans
    ((dualNat_stage1_eq_stage2G f M i α).trans
      (dualNat_stage2_eq_stage3G f M i α))

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable def dualNatCompactSourceG (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (_i : V ⟶ U) : (f ⁻¹ᵁ V : Scheme).Modules :=
  (overEquiv (f ⁻¹ᵁ V)).functor.obj (((pullback f).obj M).over (f ⁻¹ᵁ V))

noncomputable def dualNatCompactLeftG (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    dualNatCompactSourceG f M i ⟶ unitObj (f ⁻¹ᵁ V) :=
  (localPullbackModuleIso f M V).inv ≫
    (pullback (f ∣_ V)).map
      ((overRestrictModuleIso M i).hom ≫
        (restrictFunctor (X.homOfLE (leOfHom i))).map
            ((overEquiv U).functor.map α) ≫
          (overRestrictUnitIso i).hom) ≫
    (localPullbackUnitIso f V).hom

noncomputable def dualNatCompactRightG (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    dualNatCompactSourceG f M i ⟶ unitObj (f ⁻¹ᵁ V) :=
  (overRestrictModuleIso ((pullback f).obj M)
      ((TopologicalSpace.Opens.map f.base).map i)).hom ≫
    (restrictFunctor
      (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
      ((localPullbackModuleIso f M U).inv ≫
        (pullback (f ∣_ U)).map ((overEquiv U).functor.map α) ≫
          (localPullbackUnitIso f U).hom) ≫
    (overRestrictUnitIso
      ((TopologicalSpace.Opens.map f.base).map i)).hom

theorem dualNatCompactLeft_eq_stage0G (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    dualNatCompactLeftG f M i α = dualNatStage0G f M i α := by
  unfold dualNatCompactLeftG dualNatStage0G dualNatModulePrefixG
    dualNatPullAlphaG dualNatAlphaG localPullbackUnitRestrictRightG
  unfold dualNatCompactSourceG localPullbackUnitRestrictTargetG
  simp only [Functor.map_comp, Category.assoc]
  rfl

theorem dualNatStage3_eq_compactRightG (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    dualNatStage3G f M i α = dualNatCompactRightG f M i α := by
  unfold dualNatCompactRightG dualNatStage3G dualNatModuleRightG
    dualNatRestrictPullAlphaG dualNatAlphaG dualNatUnitTailG
  unfold dualNatCompactSourceG
  simp only [Functor.map_comp, Category.assoc]
  rfl

theorem dualNatCompact_eqG (f : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (i : V ⟶ U)
    (α : M.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    dualNatCompactLeftG f M i α = dualNatCompactRightG f M i α :=
  (dualNatCompactLeft_eq_stage0G f M i α).trans
    ((dualNatStage0_eq_stage3G f M i α).trans
      (dualNatStage3_eq_compactRightG f M i α))

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

theorem localDualPullback_restrictD (f : Y ⟶ X) (M : X.Modules)
    {U V : Opposite X.Opens} (i : U ⟶ V)
    (α : M.over U.unop ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :
    localDualPullback f M V.unop
        (ModularCurves.SheafOfModules.dualRestrict X.ringCatSheaf M i α) =
      ModularCurves.SheafOfModules.dualRestrict Y.ringCatSheaf
        ((pullback f).obj M)
        (((TopologicalSpace.Opens.map f.base).map i.unop).op)
        (localDualPullback f M U.unop α) := by
  apply (overEquiv (f ⁻¹ᵁ V.unop)).functor.map_injective
  let eV := (f ⁻¹ᵁ V.unop).sheafOfModulesEquivOverUnit Y.ringCatSheaf
  apply (cancel_mono eV.hom).1
  let k := (TopologicalSpace.Opens.map f.base).map i.unop
  have hY := overEquiv_map_dualRestrict ((pullback f).obj M) k
    (localDualPullback f M U.unop α)
  rw [show (overEquiv (f ⁻¹ᵁ V.unop)).functor.map
      (ModularCurves.SheafOfModules.dualRestrict Y.ringCatSheaf
        ((pullback f).obj M) k.op (localDualPullback f M U.unop α)) =
      (overRestrictModuleIso ((pullback f).obj M) k).hom ≫
        (restrictFunctor (Y.homOfLE (leOfHom k))).map
          ((overEquiv (f ⁻¹ᵁ U.unop)).functor.map
            (localDualPullback f M U.unop α)) ≫
        (overRestrictUnitIso k).hom by exact hY]
  simp only [localDualPullback, Functor.FullyFaithful.map_preimage]
  have hX := overEquiv_map_dualRestrict M i.unop α
  rw [show (overEquiv V.unop).functor.map
      (ModularCurves.SheafOfModules.dualRestrict X.ringCatSheaf M i α) =
      (overRestrictModuleIso M i.unop).hom ≫
        (restrictFunctor (X.homOfLE (leOfHom i.unop))).map
          ((overEquiv U.unop).functor.map α) ≫
        (overRestrictUnitIso i.unop).hom by
    simpa only [Quiver.Hom.op_unop] using hX]
  have h := congrArg (fun q => q ≫ eV.hom)
    (dualNatCompact_eqG f M i.unop α)
  unfold dualNatCompactLeftG dualNatCompactRightG
    dualNatCompactSourceG at h
  exact h

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

noncomputable def dualToPushforwardPresheafHomD
    (f : Y ⟶ X) (M : X.Modules) :
    (dualObj M).val ⟶
      ((pushforward f).obj (dualObj ((pullback f).obj M))).val where
  app U :=
    ModuleCat.homMk
      (AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (localDualPullback f M U.unop)
        (localDualPullback_add f M U.unop)))
      (by
        intro r
        ext α
        exact (localDualPullback_smul f M U.unop r α).symm)
  naturality := by
    intro U V i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    change localDualPullback f M V.unop
        (ModularCurves.SheafOfModules.dualRestrict
          X.ringCatSheaf M i α) =
      ModularCurves.SheafOfModules.dualRestrict Y.ringCatSheaf
        ((pullback f).obj M)
        (((TopologicalSpace.Opens.map f.base).map i.unop).op)
        (localDualPullback f M U.unop α)
    exact localDualPullback_restrictD f M i α

noncomputable def dualToPushforwardHomD (f : Y ⟶ X) (M : X.Modules) :
    dualObj M ⟶ (pushforward f).obj (dualObj ((pullback f).obj M)) :=
  ⟨dualToPushforwardPresheafHomD f M⟩

noncomputable def dualPullbackHomD (f : Y ⟶ X) (M : X.Modules) :
    (pullback f).obj (dualObj M) ⟶ dualObj ((pullback f).obj M) :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (dualToPushforwardHomD f M)

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

noncomputable def localPullbackModuleNatIsoD (f : Y ⟶ X)
    (U : X.Opens) :
    (SheafOfModules.overFunctor X.ringCatSheaf U ⋙
        (overEquiv U).functor) ⋙ pullback (f ∣_ U) ≅
      pullback f ⋙
        (SheafOfModules.overFunctor Y.ringCatSheaf (f ⁻¹ᵁ U) ⋙
          (overEquiv (f ⁻¹ᵁ U)).functor) :=
  Functor.isoWhiskerRight (overFunctorEquiv U) (pullback (f ∣_ U)) ≪≫
    Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι)
      (pullback (f ∣_ U)) ≪≫
    pullbackComp (f ∣_ U) U.ι ≪≫
    pullbackCongr (morphismRestrict_ι f U) ≪≫
    (pullbackComp (f ⁻¹ᵁ U).ι f).symm ≪≫
    Functor.isoWhiskerLeft (pullback f)
      (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).symm ≪≫
    Functor.isoWhiskerLeft (pullback f)
      (overFunctorEquiv (f ⁻¹ᵁ U)).symm

theorem localPullbackModuleNatIsoD_hom_app (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) :
    (localPullbackModuleNatIsoD f U).hom.app M =
      (localPullbackModuleIso f M U).hom := by
  rfl

theorem localPullbackModuleIso_naturalityD (f : Y ⟶ X)
    {M N : X.Modules} (q : M ⟶ N) (U : X.Opens) :
    (pullback (f ∣_ U)).map
          ((overEquiv U).functor.map
            ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map q)) ≫
        (localPullbackModuleIso f N U).hom =
      (localPullbackModuleIso f M U).hom ≫
        (overEquiv (f ⁻¹ᵁ U)).functor.map
          ((_root_.SheafOfModules.overFunctor Y.ringCatSheaf
            (f ⁻¹ᵁ U)).map ((pullback f).map q)) := by
  exact (localPullbackModuleNatIsoD f U).hom.naturality q

theorem localDualPullback_dualPrecompD (f : Y ⟶ X)
    {M N : X.Modules} (q : M ⟶ N) (U : X.Opens)
    (α : N.over U ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    localDualPullback f M U
        (ModularCurves.SheafOfModules.dualPrecomp
          X.ringCatSheaf q U α) =
      ModularCurves.SheafOfModules.dualPrecomp Y.ringCatSheaf
        ((pullback f).map q) (f ⁻¹ᵁ U)
        (localDualPullback f N U α) := by
  apply (overEquiv (f ⁻¹ᵁ U)).functor.map_injective
  simp only [localDualPullback, ModularCurves.SheafOfModules.dualPrecomp,
    Functor.FullyFaithful.map_preimage, Functor.map_comp]
  let eM := localPullbackModuleIso f M U
  let eN := localPullbackModuleIso f N U
  let b := (pullback (f ∣_ U)).map
    ((overEquiv U).functor.map
      ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U).map q))
  let d := (overEquiv (f ⁻¹ᵁ U)).functor.map
    ((_root_.SheafOfModules.overFunctor Y.ringCatSheaf
      (f ⁻¹ᵁ U)).map ((pullback f).map q))
  have hnat : b ≫ eN.hom = eM.hom ≫ d :=
    localPullbackModuleIso_naturalityD f q U
  have hinv : eM.inv ≫ b = d ≫ eN.inv :=
    CategoryTheory.Iso.inv_comp_eq_comp_inv_of_comp_eq eM eN b d hnat
  let a := (pullback (f ∣_ U)).map ((overEquiv U).functor.map α)
  let t := (localPullbackUnitIso f U).hom
  change (eM.inv ≫ b) ≫ a ≫ t = (d ≫ eN.inv) ≫ a ≫ t
  exact congrArg (fun k ↦ k ≫ a ≫ t) hinv

theorem pullbackAdjunction_homEquiv_dualPullbackHomD
    (f : Y ⟶ X) (M : X.Modules) :
    ((pullbackPushforwardAdjunction f).homEquiv _ _)
        (dualPullbackHomD f M) = dualToPushforwardHomD f M :=
  Equiv.apply_symm_apply _ _

theorem dualPullbackHom_naturalityD (f : Y ⟶ X)
    {M N : X.Modules} (q : M ⟶ N) :
    (pullback f).map (dualMapObj q) ≫ dualPullbackHomD f M =
      dualPullbackHomD f N ≫ dualMapObj ((pullback f).map q) := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]
  rw [pullbackAdjunction_homEquiv_dualPullbackHomD,
    pullbackAdjunction_homEquiv_dualPullbackHomD]
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  exact localDualPullback_dualPrecompD f q U.unop α

end AlgebraicGeometry.Scheme.Modules
