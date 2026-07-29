import ModularCurves.Picard.DualPullback.OpenAdjunction

/-!
# Pulling back module sections

Component formulas for isomorphisms and the pullback-adjunction unit on a top-open
module section.
-/

-- v4.33 bump: neither the category instances nor the semireducible component types are
-- transparent enough for the steps below at `implicit` transparency.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

theorem iso_hom_inv_app_applyT {A B : X.Modules} (e : A ≅ B)
    (U : Opposite X.Opens) (x : A.val.obj U) :
    e.inv.val.app U (e.hom.val.app U x) = x := by
  have hcomp := congrArg (fun q ↦ q.val.app U) e.hom_inv_id
  have h := ConcreteCategory.congr_hom hcomp x
  erw [sheafOfModules_comp_app_apply] at h
  exact h

theorem iso_inv_hom_app_applyT {A B : X.Modules} (e : A ≅ B)
    (U : Opposite X.Opens) (x : B.val.obj U) :
    e.hom.val.app U (e.inv.val.app U x) = x := by
  have hcomp := congrArg (fun q ↦ q.val.app U) e.inv_hom_id
  have h := ConcreteCategory.congr_hom hcomp x
  erw [sheafOfModules_comp_app_apply] at h
  exact h

theorem dualIsoObj_inv_app_applyT {M N : X.Modules} (e : M ≅ N)
    (U : Opposite X.Opens)
    (alpha : M.over U.unop ⟶
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U.unop)) :
    ((dualIsoObj e).inv.val.app U) alpha =
      ModularCurves.SheafOfModules.dualPrecomp
        X.ringCatSheaf e.inv U.unop alpha := by
  rfl

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable def topSectionHom (M : X.Modules)
    (x : M.val.obj (.op ⊤)) : unitObj X ⟶ M :=
  M.unitHomEquiv.symm (ModularCurves.moduleSectionsOfTop M x)

@[simp]
theorem topSectionHom_app_top_apply_one (M : X.Modules)
    (x : M.val.obj (.op ⊤)) :
    (topSectionHom M x).val.app (.op ⊤)
      (show X.presheaf.obj (.op ⊤) from 1) = x := by
  change (M.unitHomEquiv (topSectionHom M x)).val (.op ⊤) = x
  let s := ModularCurves.moduleSectionsOfTop M x
  have he : M.unitHomEquiv (topSectionHom M x) = s := by
    exact Equiv.apply_symm_apply M.unitHomEquiv s
  have hv := congrArg (fun t ↦ t.val (.op (⊤ : X.Opens))) he
  rw [hv]
  -- the restriction is along the identity of `⊤`; phrase it on `M.presheaf`, where
  -- functoriality carries no `restrictScalars` coherence
  change M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op x = x
  first
  | simp
  | (rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]; rfl)
  | (rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ from Subsingleton.elim _ _]; simp)

theorem pullback_unit_unit_app_top_apply_oneT (f : Y ⟶ X) :
    ((pullbackPushforwardAdjunction f).unit.app (unitObj X)).val.app
        (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1) =
      (pullbackUnitIso f).inv.val.app (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
        ((f.app (⊤ : X.Opens)).hom
          (show X.presheaf.obj (.op ⊤) from 1)) := by
  let adj := pullbackPushforwardAdjunction f
  let e := pullbackUnitIso f
  have hAdj :=
    _root_.SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at hAdj
  let oneX : (unitObj X).val.obj (.op (⊤ : X.Opens)) := by
    change X.presheaf.obj (.op ⊤)
    exact 1
  have happ := congrArg
    (fun q ↦ q.val.app (.op (⊤ : X.Opens))
      oneX) hAdj
  erw [sheafOfModules_comp_app_apply] at happ
  change e.hom.val.app (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
      (((adj.unit.app (unitObj X)).val.app (.op ⊤)) oneX) =
    (f.app (⊤ : X.Opens)).hom oneX at happ
  dsimp only [oneX] at happ
  have hcancel := iso_hom_inv_app_applyT e
    (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
    (((adj.unit.app (unitObj X)).val.app (.op ⊤))
      (show X.presheaf.obj (.op ⊤) from 1))
  rw [← hcancel]
  exact congrArg
    (fun z ↦ e.inv.val.app (.op (f ⁻¹ᵁ (⊤ : X.Opens))) z) happ

theorem pullback_unit_app_top_applyT (f : Y ⟶ X) (M : X.Modules)
    (x : M.val.obj (.op ⊤)) :
    ((pullbackPushforwardAdjunction f).unit.app M).val.app (.op ⊤) x =
      (((pullbackUnitIso f).inv ≫
        (pullback f).map (topSectionHom M x)).val.app
          (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
            ((f.app (⊤ : X.Opens)).hom
              (show X.presheaf.obj (.op ⊤) from 1))) := by
  let adj := pullbackPushforwardAdjunction f
  let q := topSectionHom M x
  have hnat := adj.unit.naturality q
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hnat
  let oneX : (unitObj X).val.obj (.op (⊤ : X.Opens)) := by
    change X.presheaf.obj (.op ⊤)
    exact 1
  have happ := congrArg
    (fun r ↦ r.val.app (.op (⊤ : X.Opens)) oneX) hnat
  conv_lhs at happ => erw [sheafOfModules_comp_app_apply]
  conv_rhs at happ => erw [sheafOfModules_comp_app_apply]
  dsimp only [q] at happ
  have hqx : (topSectionHom M x).val.app (.op ⊤) oneX = x := by
    dsimp only [oneX]
    exact topSectionHom_app_top_apply_one M x
  rw [hqx] at happ
  have hunit : (adj.unit.app (unitObj X)).val.app (.op ⊤) oneX =
      (pullbackUnitIso f).inv.val.app (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
        ((f.app (⊤ : X.Opens)).hom oneX) := by
    dsimp only [adj, oneX]
    exact pullback_unit_unit_app_top_apply_oneT f
  let k := (pullback f).map (topSectionHom M x)
  change ((adj.unit.app M).val.app (.op ⊤)) x =
    k.val.app (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
      ((adj.unit.app (unitObj X)).val.app (.op ⊤) oneX) at happ
  have hk := congrArg
    (fun z ↦ k.val.app (.op (f ⁻¹ᵁ (⊤ : X.Opens))) z) hunit
  calc
    ((pullbackPushforwardAdjunction f).unit.app M).val.app (.op ⊤) x =
        k.val.app (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
          ((adj.unit.app (unitObj X)).val.app (.op ⊤) oneX) := happ
    _ = k.val.app (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
          ((pullbackUnitIso f).inv.val.app
            (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
              ((f.app (⊤ : X.Opens)).hom oneX)) := hk
    _ = (((pullbackUnitIso f).inv ≫
          (pullback f).map (topSectionHom M x)).val.app
            (.op (f ⁻¹ᵁ (⊤ : X.Opens)))
              ((f.app (⊤ : X.Opens)).hom
                (show X.presheaf.obj (.op ⊤) from 1))) := by
      dsimp only [k, oneX]
      erw [sheafOfModules_comp_app_apply]

end AlgebraicGeometry.Scheme.Modules
