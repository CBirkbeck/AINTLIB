import ModularCurves.EllipticCurve.PullbackTensorSection

/-!
# Local evaluation of section contraction

This file evaluates contraction by a global tensor section after restricting that
section to an arbitrary open. The proof separates the structure-sheaf unit
comparisons from the associator and braiding calculation.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory SheafOfModules
  TopologicalSpace

universe u

namespace ModularCurves

noncomputable section

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

private noncomputable def tensorUnitStructureIso {X : Scheme.{u}} (M : X.Modules) :
    M ⊗ Scheme.Modules.unitObj X ≅ M :=
  (Iso.refl M ⊗ᵢ (monoidalUnitObjIso X).symm) ≪≫ ρ_ M

private theorem monoidalTensorObjIso_comp_tensorUnitStructureIso
    {X : Scheme.{u}} (M : X.Modules) :
    (monoidalTensorObjIso M (Scheme.Modules.unitObj X)).inv ≫
        (tensorUnitStructureIso M).hom =
      (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map (ρ_ M.val).hom ≫
        (Scheme.Modules.sheafifyValIso M).hom := by
  letI : (PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
    @PresheafOfModules.instSheafificationW_isMonoidal_commRingSheaf
      _ _ _ _ _ X.sheaf.obj X.ringCatSheaf.property
  let F : X.PresheafOfModules ⥤ X.Modules :=
    Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)
  letI : F.Monoidal := by
    change (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)).Monoidal
    infer_instance
  let cM : F.obj M.val ≅ M := Scheme.Modules.sheafifyValIso M
  let cA := monoidalUnitObjIso X
  change
    Functor.OplaxMonoidal.δ F M.val
          (𝟙_ X.PresheafOfModules) ≫
        (cM.hom ⊗ₘ cA.hom) ≫
          (𝟙 M ⊗ₘ cA.inv) ≫ (ρ_ M).hom =
      F.map (ρ_ M.val).hom ≫ cM.hom
  have hcancel :
      (cM.hom ⊗ₘ cA.hom) ≫ (𝟙 M ⊗ₘ cA.inv) =
        cM.hom ⊗ₘ 𝟙 (𝟙_ X.Modules) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [Category.comp_id, cA.hom_inv_id]
  have htail :
      (cM.hom ⊗ₘ cA.hom) ≫
          (𝟙 M ⊗ₘ cA.inv) ≫ (ρ_ M).hom =
        (cM.hom ⊗ₘ 𝟙 (𝟙_ X.Modules)) ≫ (ρ_ M).hom := by
    rw [← Category.assoc, hcancel]
  have hprefix :
      Functor.OplaxMonoidal.δ F M.val
          (𝟙_ X.PresheafOfModules) ≫
        (cM.hom ⊗ₘ cA.hom) ≫
        (𝟙 M ⊗ₘ cA.inv) ≫ (ρ_ M).hom =
      Functor.OplaxMonoidal.δ F M.val
          (𝟙_ X.PresheafOfModules) ≫
        ((cM.hom ⊗ₘ 𝟙 (𝟙_ X.Modules)) ≫ (ρ_ M).hom) := by
    calc
      _ = Functor.OplaxMonoidal.δ F M.val
            (𝟙_ X.PresheafOfModules) ≫
          ((cM.hom ⊗ₘ cA.hom) ≫
            (𝟙 M ⊗ₘ cA.inv) ≫ (ρ_ M).hom) := by
        rfl
      _ = _ := congrArg
        (fun k ↦ Functor.OplaxMonoidal.δ F M.val
          (𝟙_ X.PresheafOfModules) ≫ k) htail
  have htensorId :
      cM.hom ⊗ₘ 𝟙 (𝟙_ X.Modules) =
        cM.hom ▷ (𝟙_ X.Modules) :=
    MonoidalCategory.tensorHom_id cM.hom (𝟙_ X.Modules)
  have hrightTail :
      (cM.hom ⊗ₘ 𝟙 (𝟙_ X.Modules)) ≫ (ρ_ M).hom =
        (ρ_ (F.obj M.val)).hom ≫ cM.hom := by
    calc
      _ = (cM.hom ▷ (𝟙_ X.Modules)) ≫ (ρ_ M).hom :=
        congrArg (fun k ↦ k ≫ (ρ_ M).hom) htensorId
      _ = _ := MonoidalCategory.rightUnitor_naturality cM.hom
  have heta : Functor.OplaxMonoidal.η F = 𝟙 _ := by
    rfl
  have hunit := Functor.OplaxMonoidal.right_unitality_hom F M.val
  rw [heta] at hunit
  have hid :
      F.obj M.val ◁ 𝟙 (F.obj (𝟙_ X.PresheafOfModules)) = 𝟙 _ :=
    MonoidalCategory.whiskerLeft_id _ _
  have hwhisker :
      (F.obj M.val ◁ 𝟙 (F.obj (𝟙_ X.PresheafOfModules))) ≫
          (ρ_ (F.obj M.val)).hom = (ρ_ (F.obj M.val)).hom := by
    exact (congrArg (fun k ↦ k ≫ (ρ_ (F.obj M.val)).hom) hid).trans
      (Category.id_comp _)
  have hunitCore :
      Functor.OplaxMonoidal.δ F M.val
          (𝟙_ X.PresheafOfModules) ≫
        (ρ_ (F.obj M.val)).hom = F.map (ρ_ M.val).hom := by
    calc
      _ = Functor.OplaxMonoidal.δ F M.val
            (𝟙_ X.PresheafOfModules) ≫
          ((F.obj M.val ◁ 𝟙 (F.obj (𝟙_ X.PresheafOfModules))) ≫
            (ρ_ (F.obj M.val)).hom) :=
        congrArg
          (fun k ↦ Functor.OplaxMonoidal.δ F M.val
            (𝟙_ X.PresheafOfModules) ≫ k) hwhisker.symm
      _ = (Functor.OplaxMonoidal.δ F M.val
            (𝟙_ X.PresheafOfModules) ≫
          (F.obj M.val ◁ 𝟙 (F.obj (𝟙_ X.PresheafOfModules)))) ≫
            (ρ_ (F.obj M.val)).hom := (Category.assoc _ _ _).symm
      _ = _ := hunit
  calc
    _ = Functor.OplaxMonoidal.δ F M.val
          (𝟙_ X.PresheafOfModules) ≫
        ((cM.hom ⊗ₘ 𝟙 (𝟙_ X.Modules)) ≫ (ρ_ M).hom) := hprefix
    _ = Functor.OplaxMonoidal.δ F M.val
          (𝟙_ X.PresheafOfModules) ≫
        ((ρ_ (F.obj M.val)).hom ≫ cM.hom) :=
      congrArg
        (fun k ↦ Functor.OplaxMonoidal.δ F M.val
          (𝟙_ X.PresheafOfModules) ≫ k) hrightTail
    _ = (Functor.OplaxMonoidal.δ F M.val
          (𝟙_ X.PresheafOfModules) ≫
        (ρ_ (F.obj M.val)).hom) ≫ cM.hom :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k ↦ k ≫ cM.hom) hunitCore

private theorem tensorUnitStructureIso_hom_tensorSection
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (a : Γ(X, U)) :
    (tensorUnitStructureIso M).hom.val.app (.op U)
        (tensorSection M (Scheme.Modules.unitObj X) U x
          (show Γ(Scheme.Modules.unitObj X, U) from a)) =
      a • x := by
  let A := Scheme.Modules.unitObj X
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let cM : L.obj M.val ≅ M := Scheme.Modules.sheafifyValIso M
  let q₀ : (M.val ⊗ A.val).obj (.op U) :=
    x ⊗ₜ (show Γ(A, U) from a)
  let uq := (adj.unit.app (M.val ⊗ A.val)).app (.op U) q₀
  have hmor := monoidalTensorObjIso_comp_tensorUnitStructureIso M
  have hmorU := congrArg (fun k ↦ k.val.app (.op U)) hmor
  have hmorApply := ConcreteCategory.congr_hom hmorU uq
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hmorApply
  change (tensorUnitStructureIso M).hom.val.app (.op U)
      ((monoidalTensorObjIso M A).inv.val.app (.op U) uq) = _
  rw [hmorApply]
  let f := (ρ_ M.val).hom
  have hnat := adj.unit_naturality f
  have htri := adj.right_triangle_components M
  change adj.unit.app (M.val ⊗ A.val) ≫ (L.map f).val =
    f ≫ adj.unit.app M.val at hnat
  change adj.unit.app M.val ≫ cM.hom.val = 𝟙 M.val at htri
  have hpresheaf :
      adj.unit.app (M.val ⊗ A.val) ≫ (L.map f).val ≫ cM.hom.val = f := by
    have hnatp :
        (adj.unit.app (M.val ⊗ A.val) ≫ (L.map f).val) ≫ cM.hom.val =
          (f ≫ adj.unit.app M.val) ≫ cM.hom.val :=
      congrArg (fun k ↦ k ≫ cM.hom.val) hnat
    have htrip : f ≫ (adj.unit.app M.val ≫ cM.hom.val) = f ≫ 𝟙 M.val :=
      congrArg (fun k ↦ f ≫ k) htri
    exact (Category.assoc _ _ _).symm |>.trans <|
      hnatp.trans <| (Category.assoc _ _ _).trans <|
        htrip.trans (Category.comp_id f)
  have hpresheafU := congrArg (fun k ↦ k.app (.op U)) hpresheaf
  have hpresheafApply := ConcreteCategory.congr_hom hpresheafU q₀
  erw [PresheafOfModules.comp_app, ModuleCat.comp_apply,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hpresheafApply
  have hright : ((ρ_ M.val).hom.app (.op U)) q₀ = a • x := by
    erw [PresheafOfModules.rightUnitor_hom_app]
    exact ModuleCat.MonoidalCategory.rightUnitor_hom_apply
      (R := X.sheaf.obj.obj (.op U)) x
      (show X.sheaf.obj.obj (.op U) from a)
  dsimp only [uq]
  exact hpresheafApply.trans hright

private noncomputable def unitStructureTensorIso {X : Scheme.{u}} (M : X.Modules) :
    Scheme.Modules.unitObj X ⊗ M ≅ M :=
  ((monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl M) ≪≫ λ_ M

private theorem monoidalTensorObjIso_comp_unitStructureTensorIso
    {X : Scheme.{u}} (M : X.Modules) :
    (monoidalTensorObjIso (Scheme.Modules.unitObj X) M).inv ≫
        (unitStructureTensorIso M).hom =
      (PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map (λ_ M.val).hom ≫
        (Scheme.Modules.sheafifyValIso M).hom := by
  letI : (PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
    @PresheafOfModules.instSheafificationW_isMonoidal_commRingSheaf
      _ _ _ _ _ X.sheaf.obj X.ringCatSheaf.property
  let F : X.PresheafOfModules ⥤ X.Modules :=
    Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)
  letI : F.Monoidal := by
    change (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _)).Monoidal
    infer_instance
  let cM : F.obj M.val ≅ M := Scheme.Modules.sheafifyValIso M
  let cA := monoidalUnitObjIso X
  change
    Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules) M.val ≫
        (cA.hom ⊗ₘ cM.hom) ≫
          (cA.inv ⊗ₘ 𝟙 M) ≫ (λ_ M).hom =
      F.map (λ_ M.val).hom ≫ cM.hom
  have hcancel :
      (cA.hom ⊗ₘ cM.hom) ≫ (cA.inv ⊗ₘ 𝟙 M) =
        𝟙 (𝟙_ X.Modules) ⊗ₘ cM.hom := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [cA.hom_inv_id, Category.comp_id]
  have htail :
      (cA.hom ⊗ₘ cM.hom) ≫
          (cA.inv ⊗ₘ 𝟙 M) ≫ (λ_ M).hom =
        (𝟙 (𝟙_ X.Modules) ⊗ₘ cM.hom) ≫ (λ_ M).hom := by
    rw [← Category.assoc, hcancel]
  have hprefix :
      Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules) M.val ≫
        (cA.hom ⊗ₘ cM.hom) ≫
        (cA.inv ⊗ₘ 𝟙 M) ≫ (λ_ M).hom =
      Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules) M.val ≫
        ((𝟙 (𝟙_ X.Modules) ⊗ₘ cM.hom) ≫ (λ_ M).hom) := by
    calc
      _ = Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules) M.val ≫
          ((cA.hom ⊗ₘ cM.hom) ≫
            (cA.inv ⊗ₘ 𝟙 M) ≫ (λ_ M).hom) := by
        rfl
      _ = _ := congrArg
        (fun k ↦ Functor.OplaxMonoidal.δ F
          (𝟙_ X.PresheafOfModules) M.val ≫ k) htail
  have htensorId :
      𝟙 (𝟙_ X.Modules) ⊗ₘ cM.hom =
        (𝟙_ X.Modules) ◁ cM.hom :=
    MonoidalCategory.id_tensorHom (𝟙_ X.Modules) cM.hom
  have hleftTail :
      (𝟙 (𝟙_ X.Modules) ⊗ₘ cM.hom) ≫ (λ_ M).hom =
        (λ_ (F.obj M.val)).hom ≫ cM.hom := by
    calc
      _ = ((𝟙_ X.Modules) ◁ cM.hom) ≫ (λ_ M).hom :=
        congrArg (fun k ↦ k ≫ (λ_ M).hom) htensorId
      _ = _ := MonoidalCategory.leftUnitor_naturality cM.hom
  have heta : Functor.OplaxMonoidal.η F = 𝟙 _ := by
    rfl
  have hunit := Functor.OplaxMonoidal.left_unitality_hom F M.val
  rw [heta] at hunit
  have hid :
      𝟙 (F.obj (𝟙_ X.PresheafOfModules)) ▷ F.obj M.val = 𝟙 _ :=
    MonoidalCategory.id_whiskerRight _ _
  have hwhisker :
      (𝟙 (F.obj (𝟙_ X.PresheafOfModules)) ▷ F.obj M.val) ≫
          (λ_ (F.obj M.val)).hom = (λ_ (F.obj M.val)).hom := by
    exact (congrArg (fun k ↦ k ≫ (λ_ (F.obj M.val)).hom) hid).trans
      (Category.id_comp _)
  have hunitCore :
      Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules) M.val ≫
        (λ_ (F.obj M.val)).hom = F.map (λ_ M.val).hom := by
    calc
      _ = Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules) M.val ≫
          ((𝟙 (F.obj (𝟙_ X.PresheafOfModules)) ▷ F.obj M.val) ≫
            (λ_ (F.obj M.val)).hom) :=
        congrArg
          (fun k ↦ Functor.OplaxMonoidal.δ F
            (𝟙_ X.PresheafOfModules) M.val ≫ k) hwhisker.symm
      _ = (Functor.OplaxMonoidal.δ F
            (𝟙_ X.PresheafOfModules) M.val ≫
          (𝟙 (F.obj (𝟙_ X.PresheafOfModules)) ▷ F.obj M.val)) ≫
            (λ_ (F.obj M.val)).hom := (Category.assoc _ _ _).symm
      _ = _ := hunit
  calc
    _ = Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules) M.val ≫
        ((𝟙 (𝟙_ X.Modules) ⊗ₘ cM.hom) ≫ (λ_ M).hom) := hprefix
    _ = Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules) M.val ≫
        ((λ_ (F.obj M.val)).hom ≫ cM.hom) :=
      congrArg
        (fun k ↦ Functor.OplaxMonoidal.δ F
          (𝟙_ X.PresheafOfModules) M.val ≫ k) hleftTail
    _ = (Functor.OplaxMonoidal.δ F
          (𝟙_ X.PresheafOfModules) M.val ≫
        (λ_ (F.obj M.val)).hom) ≫ cM.hom :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun k ↦ k ≫ cM.hom) hunitCore

private theorem unitStructureTensorIso_hom_tensorSection
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (a : Γ(X, U)) (x : Γ(M, U)) :
    (unitStructureTensorIso M).hom.val.app (.op U)
        (tensorSection (Scheme.Modules.unitObj X) M U
          (show Γ(Scheme.Modules.unitObj X, U) from a) x) =
      a • x := by
  let A := Scheme.Modules.unitObj X
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let cM : L.obj M.val ≅ M := Scheme.Modules.sheafifyValIso M
  let q₀ : (A.val ⊗ M.val).obj (.op U) :=
    (show Γ(A, U) from a) ⊗ₜ x
  let uq := (adj.unit.app (A.val ⊗ M.val)).app (.op U) q₀
  have hmor := monoidalTensorObjIso_comp_unitStructureTensorIso M
  have hmorU := congrArg (fun k ↦ k.val.app (.op U)) hmor
  have hmorApply := ConcreteCategory.congr_hom hmorU uq
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hmorApply
  change (unitStructureTensorIso M).hom.val.app (.op U)
      ((monoidalTensorObjIso A M).inv.val.app (.op U) uq) = _
  rw [hmorApply]
  let f := (λ_ M.val).hom
  have hnat := adj.unit_naturality f
  have htri := adj.right_triangle_components M
  change adj.unit.app (A.val ⊗ M.val) ≫ (L.map f).val =
    f ≫ adj.unit.app M.val at hnat
  change adj.unit.app M.val ≫ cM.hom.val = 𝟙 M.val at htri
  have hpresheaf :
      adj.unit.app (A.val ⊗ M.val) ≫ (L.map f).val ≫ cM.hom.val = f := by
    have hnatp :
        (adj.unit.app (A.val ⊗ M.val) ≫ (L.map f).val) ≫ cM.hom.val =
          (f ≫ adj.unit.app M.val) ≫ cM.hom.val :=
      congrArg (fun k ↦ k ≫ cM.hom.val) hnat
    have htrip : f ≫ (adj.unit.app M.val ≫ cM.hom.val) = f ≫ 𝟙 M.val :=
      congrArg (fun k ↦ f ≫ k) htri
    exact (Category.assoc _ _ _).symm |>.trans <|
      hnatp.trans <| (Category.assoc _ _ _).trans <|
        htrip.trans (Category.comp_id f)
  have hpresheafU := congrArg (fun k ↦ k.app (.op U)) hpresheaf
  have hpresheafApply := ConcreteCategory.congr_hom hpresheafU q₀
  erw [PresheafOfModules.comp_app, ModuleCat.comp_apply,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at hpresheafApply
  have hleft : ((λ_ M.val).hom.app (.op U)) q₀ = a • x := by
    erw [PresheafOfModules.leftUnitor_hom_app]
    exact ModuleCat.MonoidalCategory.leftUnitor_hom_apply
      (R := X.sheaf.obj.obj (.op U))
      (show X.sheaf.obj.obj (.op U) from a) x
  dsimp only [uq]
  exact hpresheafApply.trans hleft

private theorem topSectionHom_app_apply_local
    {X : Scheme.{u}} (Q : X.Modules)
    (q : Γ(Q, (⊤ : X.Opens))) (U : X.Opens) (a : Γ(X, U)) :
    (Scheme.Modules.topSectionHom Q q).val.app (.op U) a =
      a • Q.presheaf.map
        (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op q := by
  rfl

private theorem sectionContractionStart_apply
    {X : Scheme.{u}} (L Q : X.Modules)
    (q : Γ(Q, (⊤ : X.Opens))) (U : X.Opens) (l : Γ(L, U)) :
    (((ρ_ L).inv ≫
      L ◁ ((monoidalUnitObjIso X).hom ≫
        Scheme.Modules.topSectionHom Q q)).val.app (.op U)) l =
      tensorSection L Q U l
        (Q.presheaf.map
          (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op q) := by
  let A := Scheme.Modules.unitObj X
  let t := tensorUnitStructureIso L
  let oneX : Γ(X, U) := 1
  let oneA : Γ(A, U) := show Γ(A, U) from oneX
  let w := tensorSection L A U l oneA
  have hhom : t.hom.val.app (.op U) w = l := by
    simpa only [t, w, A, oneA, oneX, one_smul] using
      tensorUnitStructureIso_hom_tensorSection L U l oneX
  have hinv : t.inv.val.app (.op U) l = w := by
    have happ := congrArg (fun z ↦ t.inv.val.app (.op U) z) hhom
    exact happ.symm.trans
      (Scheme.Modules.iso_hom_inv_app_applyT t (.op U) w)
  let a := Scheme.Modules.topSectionHom Q q
  have hmorph :
      (ρ_ L).inv ≫
          L ◁ ((monoidalUnitObjIso X).hom ≫ a) =
        t.inv ≫ (𝟙 L ⊗ₘ a) := by
    dsimp only [t, tensorUnitStructureIso]
    rw [Iso.trans_inv, tensorIso_inv, Iso.refl_inv, Iso.symm_inv]
    simp only [MonoidalCategory.id_tensorHom,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
  have hmorphU := congrArg (fun k ↦ k.val.app (.op U)) hmorph
  have hmorphApply := ConcreteCategory.congr_hom hmorphU l
  conv_lhs at hmorphApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  conv_rhs at hmorphApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  rw [hinv] at hmorphApply
  have hmap := tensorSection_map (𝟙 L) a U l oneA
  have htop : a.val.app (.op U) oneA =
      Q.presheaf.map
        (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op q := by
    simpa only [a, oneA, oneX, one_smul] using
      topSectionHom_app_apply_local Q q U oneX
  change ((𝟙 L ⊗ₘ a).val.app (.op U)) w = _ at hmap
  rw [htop] at hmap
  have hidL : ((𝟙 L : L ⟶ L).val.app (.op U)) l = l := rfl
  rw [hidL] at hmap
  have hmap' : ((𝟙 L ⊗ₘ a).val.app (.op U)) w =
      tensorSection L Q U l
        (Q.presheaf.map
          (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op q) := by
    exact hmap
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  exact hmorphApply.trans hmap'

private theorem unitStructureTensorIso_inv_apply
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    (unitStructureTensorIso M).inv.val.app (.op U) x =
      tensorSection (Scheme.Modules.unitObj X) M U
        (show Γ(Scheme.Modules.unitObj X, U) from (1 : Γ(X, U))) x := by
  let A := Scheme.Modules.unitObj X
  let e := unitStructureTensorIso M
  let oneX : Γ(X, U) := 1
  let oneA : Γ(A, U) := show Γ(A, U) from oneX
  let w := tensorSection A M U oneA x
  have hhom : e.hom.val.app (.op U) w = x := by
    simpa only [e, w, A, oneA, oneX, one_smul] using
      unitStructureTensorIso_hom_tensorSection M U oneX x
  have happ := congrArg (fun z ↦ e.inv.val.app (.op U) z) hhom
  exact happ.symm.trans
    (Scheme.Modules.iso_hom_inv_app_applyT e (.op U) w)

private theorem middleSwap_unit_morphism
    {X : Scheme.{u}} (L M P : X.Modules) :
    (α_ L M P).inv ≫ (β_ L M).hom ▷ P ≫ (α_ M L P).hom =
      ((λ_ L).inv ⊗ₘ 𝟙 (M ⊗ P)) ≫
        tensorμ (𝟙_ X.Modules) L M P ≫
        ((λ_ M).hom ⊗ₘ 𝟙 (L ⊗ P)) := by
  dsimp [tensorμ]
  monoidal

private theorem middleSwap_structureUnit_cancel
    {X : Scheme.{u}} (L M P : X.Modules) :
    ((unitStructureTensorIso L).inv ⊗ₘ 𝟙 (M ⊗ P)) ≫
        tensorμ (Scheme.Modules.unitObj X) L M P ≫
        ((unitStructureTensorIso M).hom ⊗ₘ 𝟙 (L ⊗ P)) =
      ((λ_ L).inv ⊗ₘ 𝟙 (M ⊗ P)) ≫
        tensorμ (𝟙_ X.Modules) L M P ≫
        ((λ_ M).hom ⊗ₘ 𝟙 (L ⊗ P)) := by
  let c := monoidalUnitObjIso X
  let start₀ := (λ_ L).inv ⊗ₘ 𝟙 (M ⊗ P)
  let start₁ := (c.hom ⊗ₘ 𝟙 L) ⊗ₘ 𝟙 (M ⊗ P)
  let finish₀ := (c.inv ⊗ₘ 𝟙 M) ⊗ₘ 𝟙 (L ⊗ P)
  let finish₁ := (λ_ M).hom ⊗ₘ 𝟙 (L ⊗ P)
  have hstart :
      (unitStructureTensorIso L).inv ⊗ₘ 𝟙 (M ⊗ P) =
        start₀ ≫ start₁ := by
    dsimp only [unitStructureTensorIso, Iso.trans_inv, tensorIso_inv,
      Iso.symm_inv, Iso.refl_inv, c, start₀, start₁]
    change (((λ_ L).inv ≫
      ((monoidalUnitObjIso X).hom ⊗ₘ 𝟙 L)) ⊗ₘ 𝟙 (M ⊗ P)) = _
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  have hfinish :
      (unitStructureTensorIso M).hom ⊗ₘ 𝟙 (L ⊗ P) =
        finish₀ ≫ finish₁ := by
    dsimp only [unitStructureTensorIso, Iso.trans_hom, tensorIso_hom,
      Iso.symm_hom, Iso.refl_hom, c, finish₀, finish₁]
    change (((monoidalUnitObjIso X).inv ⊗ₘ 𝟙 M) ≫
      (λ_ M).hom) ⊗ₘ 𝟙 (L ⊗ P) = _
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  have hnatural := tensorμ_natural c.hom (𝟙 L) (𝟙 M) (𝟙 P)
  have hnatural' :
      start₁ ≫ tensorμ (Scheme.Modules.unitObj X) L M P =
        tensorμ (𝟙_ X.Modules) L M P ≫
          ((c.hom ⊗ₘ 𝟙 M) ⊗ₘ 𝟙 (L ⊗ P)) := by
    simpa only [start₁, MonoidalCategory.id_tensorHom_id] using hnatural
  have hcancel :
      ((c.hom ⊗ₘ 𝟙 M) ⊗ₘ 𝟙 (L ⊗ P)) ≫ finish₀ = 𝟙 _ := by
    dsimp only [finish₀]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [c.hom_inv_id]
    simp only [Category.comp_id, MonoidalCategory.id_tensorHom_id]
  rw [hstart, hfinish]
  slice_lhs 2 3 => rw [hnatural']
  slice_lhs 3 4 => rw [hcancel]
  simp only [start₀, finish₁, Category.id_comp]

private theorem middleSwap_tensorSection
    {X : Scheme.{u}} (L M P : X.Modules) (U : X.Opens)
    (l : Γ(L, U)) (x : Γ(M, U)) (y : Γ(P, U)) :
    (((α_ L M P).inv ≫ (β_ L M).hom ▷ P ≫
      (α_ M L P).hom).val.app (.op U))
        (tensorSection L (M ⊗ P) U l
          (tensorSection M P U x y)) =
      tensorSection M (L ⊗ P) U x
        (tensorSection L P U l y) := by
  let A := Scheme.Modules.unitObj X
  let eL := unitStructureTensorIso L
  let eM := unitStructureTensorIso M
  let oneX : Γ(X, U) := 1
  let oneA : Γ(A, U) := show Γ(A, U) from oneX
  let z := tensorSection M P U x y
  let source := tensorSection L (M ⊗ P) U l z
  let source' := tensorSection (A ⊗ L) (M ⊗ P) U
    (tensorSection A L U oneA l) z
  let target' := tensorSection (A ⊗ M) (L ⊗ P) U
    (tensorSection A M U oneA x) (tensorSection L P U l y)
  let target := tensorSection M (L ⊗ P) U x
    (tensorSection L P U l y)
  let startMap := eL.inv ⊗ₘ 𝟙 (M ⊗ P)
  let finishMap := eM.hom ⊗ₘ 𝟙 (L ⊗ P)
  have hmorph :
      (α_ L M P).inv ≫ (β_ L M).hom ▷ P ≫
          (α_ M L P).hom =
        startMap ≫ tensorμ A L M P ≫ finishMap := by
    exact (middleSwap_unit_morphism L M P).trans
      (middleSwap_structureUnit_cancel L M P).symm
  have hstartMap := tensorSection_map eL.inv (𝟙 (M ⊗ P)) U l z
  have hinvL := unitStructureTensorIso_inv_apply L U l
  change startMap.val.app (.op U) source = _ at hstartMap
  rw [hinvL] at hstartMap
  have hidMP : ((𝟙 (M ⊗ P) : M ⊗ P ⟶ M ⊗ P).val.app (.op U)) z = z := rfl
  rw [hidMP] at hstartMap
  change startMap.val.app (.op U) source = source' at hstartMap
  have hmu := tensorMu_tensorSection A L M P U oneA l x y
  change (tensorμ A L M P).val.app (.op U) source' = target' at hmu
  have hfinishMap := tensorSection_map eM.hom (𝟙 (L ⊗ P)) U
    (tensorSection A M U oneA x) (tensorSection L P U l y)
  have hhomM : eM.hom.val.app (.op U) (tensorSection A M U oneA x) = x := by
    simpa only [eM, A, oneA, oneX, one_smul] using
      unitStructureTensorIso_hom_tensorSection M U oneX x
  change finishMap.val.app (.op U) target' = _ at hfinishMap
  rw [hhomM] at hfinishMap
  have hidLP :
      ((𝟙 (L ⊗ P) : L ⊗ P ⟶ L ⊗ P).val.app (.op U))
        (tensorSection L P U l y) = tensorSection L P U l y := rfl
  rw [hidLP] at hfinishMap
  change finishMap.val.app (.op U) target' = target at hfinishMap
  have hmorphU := congrArg (fun k ↦ k.val.app (.op U)) hmorph
  have hmorphApply := ConcreteCategory.congr_hom hmorphU source
  conv_rhs at hmorphApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  have hstartMu := congrArg
    (fun s ↦ (tensorμ A L M P).val.app (.op U) s) hstartMap
  have hstartFinish := congrArg
    (fun s ↦ finishMap.val.app (.op U) s) hstartMu
  have hmuFinish := congrArg
    (fun s ↦ finishMap.val.app (.op U) s) hmu
  exact hmorphApply.trans <|
    hstartFinish.trans <| hmuFinish.trans hfinishMap

private theorem sectionContractionTail_tensorSection
    {X : Scheme.{u}} (L M P : X.Modules)
    (pairing : L ⊗ P ⟶ Scheme.Modules.unitObj X)
    (U : X.Opens) (x : Γ(M, U)) (l : Γ(L, U)) (y : Γ(P, U)) :
    ((M ◁ pairing ≫ M ◁ (monoidalUnitObjIso X).inv ≫
      (ρ_ M).hom).val.app (.op U))
        (tensorSection M (L ⊗ P) U x
          (tensorSection L P U l y)) =
      (show Γ(X, U) from
        pairing.val.app (.op U) (tensorSection L P U l y)) • x := by
  let A := Scheme.Modules.unitObj X
  let e := tensorUnitStructureIso M
  let lp := tensorSection L P U l y
  let r : Γ(X, U) := pairing.val.app (.op U) lp
  let source := tensorSection M (L ⊗ P) U x lp
  let targetSection := tensorSection M A U x (show Γ(A, U) from r)
  let pairMap := 𝟙 M ⊗ₘ pairing
  have hmorph :
      M ◁ pairing ≫ M ◁ (monoidalUnitObjIso X).inv ≫ (ρ_ M).hom =
        pairMap ≫ e.hom := by
    dsimp only [pairMap, e, tensorUnitStructureIso, Iso.trans_hom,
      tensorIso_hom, Iso.refl_hom, Iso.symm_hom]
    rw [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom]
    simp only [MonoidalCategory.id_tensorHom]
  have hmap := tensorSection_map (𝟙 M) pairing U x lp
  change pairMap.val.app (.op U) source = _ at hmap
  have hidM : ((𝟙 M : M ⟶ M).val.app (.op U)) x = x := rfl
  rw [hidM] at hmap
  change pairMap.val.app (.op U) source = targetSection at hmap
  have heval := tensorUnitStructureIso_hom_tensorSection M U x r
  change e.hom.val.app (.op U) targetSection = r • x at heval
  have hmorphU := congrArg (fun k ↦ k.val.app (.op U)) hmorph
  have hmorphApply := ConcreteCategory.congr_hom hmorphU source
  conv_rhs at hmorphApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  exact hmorphApply.trans <|
    congrArg (fun s ↦ e.hom.val.app (.op U) s) hmap |>.trans heval

theorem sectionContractionHom_apply_of_restrict_eq_tensorSection
    {X : Scheme.{u}} (L M P : X.Modules)
    (pairing : L ⊗ P ⟶ Scheme.Modules.unitObj X)
    (q : Γ(M ⊗ P, (⊤ : X.Opens))) (U : X.Opens)
    (l : Γ(L, U)) (x : Γ(M, U)) (y : Γ(P, U))
    (hq : (M ⊗ P).presheaf.map
      (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op q =
        tensorSection M P U x y) :
    (sectionContractionHom L M P pairing q).val.app (.op U) l =
      (show Γ(X, U) from
        pairing.val.app (.op U) (tensorSection L P U l y)) • x := by
  let startMap := (ρ_ L).inv ≫
    L ◁ ((monoidalUnitObjIso X).hom ≫
      Scheme.Modules.topSectionHom (M ⊗ P) q)
  let middleMap := (α_ L M P).inv ≫
    (β_ L M).hom ▷ P ≫ (α_ M L P).hom
  let tailMap := M ◁ pairing ≫
    M ◁ (monoidalUnitObjIso X).inv ≫ (ρ_ M).hom
  let qU := (M ⊗ P).presheaf.map
    (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op q
  let firstSection := tensorSection L (M ⊗ P) U l
    (tensorSection M P U x y)
  let secondSection := tensorSection M (L ⊗ P) U x
    (tensorSection L P U l y)
  have hgroup :
      sectionContractionHom L M P pairing q =
        startMap ≫ middleMap ≫ tailMap := by
    dsimp only [sectionContractionHom, startMap, middleMap, tailMap]
    simp only [Category.assoc]
  have hstart := sectionContractionStart_apply L (M ⊗ P) q U l
  change startMap.val.app (.op U) l = tensorSection L (M ⊗ P) U l qU at hstart
  have hfirst : startMap.val.app (.op U) l = firstSection :=
    hstart.trans (congrArg (tensorSection L (M ⊗ P) U l) hq)
  have hmiddle := middleSwap_tensorSection L M P U l x y
  change middleMap.val.app (.op U) firstSection = secondSection at hmiddle
  have htail := sectionContractionTail_tensorSection
    L M P pairing U x l y
  change tailMap.val.app (.op U) secondSection = _ at htail
  have hgroupU := congrArg (fun k ↦ k.val.app (.op U)) hgroup
  have hgroupApply := ConcreteCategory.congr_hom hgroupU l
  conv_rhs at hgroupApply =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  have hfirstMiddle := congrArg
    (fun s ↦ middleMap.val.app (.op U) s) hfirst
  have hfirstMiddleTail := congrArg
    (fun s ↦ tailMap.val.app (.op U) s) (hfirstMiddle.trans hmiddle)
  exact hgroupApply.trans (hfirstMiddleTail.trans htail)

end

end ModularCurves
