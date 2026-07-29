import ModularCurves.Picard.InvertibleSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Scalar endomorphisms of structure sheaves under pullback

This file records the canonical scalar endomorphism of a scheme's structure module and
its compatibility with pushforward and pullback.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

/-- A section over the top open determines the compatible family of all its
restrictions. -/
noncomputable def moduleSectionsOfTop {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ M.val.map (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op x)
    (by
      intro U V g
      let iU := (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op
      let iV := (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
      change M.presheaf.map g (M.presheaf.map iU x) = M.presheaf.map iV x
      calc
        M.presheaf.map g (M.presheaf.map iU x) =
            M.presheaf.map (iU ≫ g) x :=
          (M.presheaf.map_comp_apply iU g x).symm
        _ = M.presheaf.map iV x := by
          rw [Subsingleton.elim (iU ≫ g) iV])

/-- Multiplication by a top-open section of the structure sheaf. -/
noncomputable def unitEndomorphismOfTopSection {X : Scheme.{u}}
    (r : Γ(X, (⊤ : X.Opens))) :
    Scheme.Modules.unitObj X ⟶ Scheme.Modules.unitObj X :=
  (Scheme.Modules.unitObj X).unitHomEquiv.symm
    (moduleSectionsOfTop _ r)

@[simp]
theorem unitEndomorphismOfTopSection_app_apply {X : Scheme.{u}}
    (r : Γ(X, (⊤ : X.Opens))) (W : X.Opens) (a : Γ(X, W)) :
    (unitEndomorphismOfTopSection r).val.app (.op W) a =
      a * X.presheaf.map (homOfLE (le_top : W ≤ (⊤ : X.Opens))).op r := by
  rfl

/-- Composition of structure-sheaf scalar endomorphisms is multiplication of
their defining top-open sections. -/
theorem unitEndomorphismOfTopSection_comp {X : Scheme.{u}}
    (r s : Γ(X, (⊤ : X.Opens))) :
    unitEndomorphismOfTopSection r ≫ unitEndomorphismOfTopSection s =
      unitEndomorphismOfTopSection (r * s) := by
  apply SheafOfModules.hom_ext
  ext U
  change (1 * X.presheaf.map
      (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op r) *
      X.presheaf.map
        (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op s =
    1 * X.presheaf.map
      (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op (r * s)
  rw [map_mul, mul_assoc]

/-- Multiplication by the unit section is the identity of the structure sheaf. -/
theorem unitEndomorphismOfTopSection_one {X : Scheme.{u}} :
    unitEndomorphismOfTopSection (1 : Γ(X, (⊤ : X.Opens))) = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  ext U
  change 1 * X.presheaf.map
      (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op 1 = 1
  rw [map_one, mul_one]

/-- A unit on the top open acts as an automorphism of the structure sheaf. -/
noncomputable def unitAutomorphismOfTopUnit {X : Scheme.{u}}
    (r : Γ(X, (⊤ : X.Opens))ˣ) :
    Scheme.Modules.unitObj X ≅ Scheme.Modules.unitObj X where
  hom := unitEndomorphismOfTopSection r
  inv := unitEndomorphismOfTopSection (↑r⁻¹ : Γ(X, (⊤ : X.Opens)))
  hom_inv_id := by
    rw [unitEndomorphismOfTopSection_comp]
    have h : (r : Γ(X, (⊤ : X.Opens))) *
        (↑r⁻¹ : Γ(X, (⊤ : X.Opens))) = 1 := r.mul_inv
    rw [h, unitEndomorphismOfTopSection_one]
  inv_hom_id := by
    rw [unitEndomorphismOfTopSection_comp]
    have h : (↑r⁻¹ : Γ(X, (⊤ : X.Opens))) *
        (r : Γ(X, (⊤ : X.Opens))) = 1 := r.inv_mul
    rw [h, unitEndomorphismOfTopSection_one]

@[simp]
theorem unitAutomorphismOfTopUnit_hom {X : Scheme.{u}}
    (r : Γ(X, (⊤ : X.Opens))ˣ) :
    (unitAutomorphismOfTopUnit r).hom = unitEndomorphismOfTopSection r :=
  rfl

@[simp]
theorem unitAutomorphismOfTopUnit_inv {X : Scheme.{u}}
    (r : Γ(X, (⊤ : X.Opens))ˣ) :
    (unitAutomorphismOfTopUnit r).inv =
      unitEndomorphismOfTopSection (↑r⁻¹ : Γ(X, (⊤ : X.Opens))) :=
  rfl

theorem unitEndomorphismOfTopSection_comp_unitToPushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, (⊤ : Y.Opens))) :
    unitEndomorphismOfTopSection r ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map
          (unitEndomorphismOfTopSection (f.appTop.hom r)) := by
  apply SheafOfModules.hom_ext
  ext W
  change (f.app W.unop).hom
      ((unitEndomorphismOfTopSection r).val.app W
        (show Γ(Y, W.unop) from 1)) =
    (unitEndomorphismOfTopSection (f.appTop.hom r)).val.app
      (.op (f ⁻¹ᵁ W.unop))
      ((f.app W.unop).hom (show Γ(Y, W.unop) from 1))
  rw [unitEndomorphismOfTopSection_app_apply,
    unitEndomorphismOfTopSection_app_apply, map_one, one_mul, one_mul]
  let i : Opposite.op (⊤ : Y.Opens) ⟶ W :=
    (homOfLE (le_top : W.unop ≤ (⊤ : Y.Opens))).op
  have h := congrArg (fun q ↦ q.hom r) (f.naturality i)
  have h' : (f.app W.unop).hom (Y.presheaf.map i r) =
      X.presheaf.map (((TopologicalSpace.Opens.map f.base).map i.unop).op)
        ((f.app ⊤).hom r) := by
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using h
  calc
    (f.app W.unop).hom
        (Y.presheaf.map (homOfLE (le_top : W.unop ≤ (⊤ : Y.Opens))).op r) =
      (f.app W.unop).hom (Y.presheaf.map i r) := by
        rfl
    _ = X.presheaf.map (((TopologicalSpace.Opens.map f.base).map i.unop).op)
        ((f.app ⊤).hom r) := h'
    _ = X.presheaf.map
        (homOfLE (le_top : f ⁻¹ᵁ W.unop ≤ (⊤ : X.Opens))).op
        (f.appTop.hom r) := by
      have hmap :
          X.presheaf.map (((TopologicalSpace.Opens.map f.base).map i.unop).op) =
            X.presheaf.map
              (homOfLE (le_top : f ⁻¹ᵁ W.unop ≤ (⊤ : X.Opens))).op :=
        X.presheaf.congr_map (Subsingleton.elim _ _)
      rw [hmap]
      congr 1

theorem pullback_unitEndomorphismOfTopSection
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, (⊤ : Y.Opens))) :
    (Scheme.Modules.pullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map (unitEndomorphismOfTopSection r) ≫
        (Scheme.Modules.pullbackUnitIso f).hom =
      unitEndomorphismOfTopSection (f.appTop.hom r) := by
  let e := Scheme.Modules.pullbackUnitIso f
  apply (cancel_epi e.hom).1
  change e.hom ≫ e.inv ≫
      (Scheme.Modules.pullback f).map (unitEndomorphismOfTopSection r) ≫ e.hom =
    e.hom ≫ unitEndomorphismOfTopSection (f.appTop.hom r)
  rw [Iso.hom_inv_id_assoc]
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]
  erw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  exact unitEndomorphismOfTopSection_comp_unitToPushforward f r

end ModularCurves
