import ModularCurves.Picard.DualPullback.TrivializationRestriction

/-!
# Transition units of invertible-sheaf trivializations

Changes between two trivializations of a line bundle are uniquely multiplication by a unit
of the ring of sections. This file packages those units and their cocycle laws.
-/

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

private noncomputable def trivializationTransitionEndUnit
    {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (End (SheafOfModules.unit (X.ringCatSheaf.over U)))ˣ where
  val := e.inv ≫ g.hom
  inv := g.inv ≫ e.hom
  val_inv := by
    rw [End.mul_def, End.one_def]
    simp
  inv_val := by
    rw [End.mul_def, End.one_def]
    simp

/-- The unit by which two over-site trivializations of an invertible sheaf differ. -/
noncomputable def trivializationTransitionUnit
    {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) : Γ(X, U)ˣ :=
  Units.map
    (ModularCurves.SheafOfModules.overUnitScalarEndRingEquiv
      X.ringCatSheaf U).symm.toMonoidHom
    (trivializationTransitionEndUnit U e g)

/-- Multiplication by the transition unit is the change between the two trivializations. -/
theorem overUnitScalarEnd_transitionUnit
    {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U
      (trivializationTransitionUnit U e g : Γ(X, U)) =
      e.inv ≫ g.hom := by
  rw [trivializationTransitionUnit, Units.coe_map]
  exact (ModularCurves.SheafOfModules.overUnitScalarEndRingEquiv
    X.ringCatSheaf U).apply_symm_apply _

@[simp]
theorem trivializationTransitionUnit_self
    {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    trivializationTransitionUnit U e e = 1 := by
  apply Units.ext
  let E := ModularCurves.SheafOfModules.overUnitScalarEndRingEquiv
    X.ringCatSheaf U
  have hee : E (trivializationTransitionUnit U e e : Γ(X, U)) =
      e.inv ≫ e.hom := by
    dsimp only [E]
    exact overUnitScalarEnd_transitionUnit U e e
  apply E.injective
  calc
    E (trivializationTransitionUnit U e e : Γ(X, U)) =
        (show End (SheafOfModules.unit (X.ringCatSheaf.over U)) from
          e.inv ≫ e.hom) := hee
    _ = (1 : End (SheafOfModules.unit (X.ringCatSheaf.over U))) := by
      rw [End.one_def]
      exact e.inv_hom_id
    _ = E (1 : Γ(X, U)) := E.map_one.symm

@[simp]
theorem trivializationTransitionUnit_symm
    {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    trivializationTransitionUnit U e g * trivializationTransitionUnit U g e = 1 := by
  apply Units.ext
  let E := ModularCurves.SheafOfModules.overUnitScalarEndRingEquiv
    X.ringCatSheaf U
  have heg : E (trivializationTransitionUnit U e g : Γ(X, U)) =
      e.inv ≫ g.hom := by
    dsimp only [E]
    exact overUnitScalarEnd_transitionUnit U e g
  have hge : E (trivializationTransitionUnit U g e : Γ(X, U)) =
      g.inv ≫ e.hom := by
    dsimp only [E]
    exact overUnitScalarEnd_transitionUnit U g e
  apply E.injective
  calc
    E (↑(trivializationTransitionUnit U e g *
        trivializationTransitionUnit U g e) : Γ(X, U)) =
        E (trivializationTransitionUnit U e g : Γ(X, U)) *
          E (trivializationTransitionUnit U g e : Γ(X, U)) := E.map_mul _ _
    _ = (show End (SheafOfModules.unit (X.ringCatSheaf.over U)) from
          e.inv ≫ g.hom) *
        (show End (SheafOfModules.unit (X.ringCatSheaf.over U)) from
          g.inv ≫ e.hom) := by
      exact congrArg₂ (· * ·) heg hge
    _ = 1 := by
      rw [End.mul_def, End.one_def]
      simp
    _ = E (1 : Γ(X, U)) := E.map_one.symm

/-- Transition units satisfy the cocycle law on a common open. -/
theorem trivializationTransitionUnit_trans
    {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (e g h : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    trivializationTransitionUnit U e g * trivializationTransitionUnit U g h =
      trivializationTransitionUnit U e h := by
  rw [mul_comm (trivializationTransitionUnit U e g)]
  apply Units.ext
  let E := ModularCurves.SheafOfModules.overUnitScalarEndRingEquiv
    X.ringCatSheaf U
  have hgh : E (trivializationTransitionUnit U g h : Γ(X, U)) =
      g.inv ≫ h.hom := by
    dsimp only [E]
    exact overUnitScalarEnd_transitionUnit U g h
  have heg : E (trivializationTransitionUnit U e g : Γ(X, U)) =
      e.inv ≫ g.hom := by
    dsimp only [E]
    exact overUnitScalarEnd_transitionUnit U e g
  have heh : E (trivializationTransitionUnit U e h : Γ(X, U)) =
      e.inv ≫ h.hom := by
    dsimp only [E]
    exact overUnitScalarEnd_transitionUnit U e h
  apply E.injective
  calc
    E (↑(trivializationTransitionUnit U g h *
        trivializationTransitionUnit U e g) : Γ(X, U)) =
        E (trivializationTransitionUnit U g h : Γ(X, U)) *
          E (trivializationTransitionUnit U e g : Γ(X, U)) := E.map_mul _ _
    _ = (show End (SheafOfModules.unit (X.ringCatSheaf.over U)) from
          g.inv ≫ h.hom) *
        (show End (SheafOfModules.unit (X.ringCatSheaf.over U)) from
          e.inv ≫ g.hom) := by
      exact congrArg₂ (· * ·) hgh heg
    _ = (show End (SheafOfModules.unit (X.ringCatSheaf.over U)) from
          e.inv ≫ h.hom) := by
      rw [End.mul_def]
      simp
    _ = E (trivializationTransitionUnit U e h : Γ(X, U)) := heh.symm

/-- Restricting two trivializations restricts their transition unit along the structure
sheaf map. -/
theorem trivializationTransitionUnit_restrict
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    let j : Over U := Over.mk (homOfLE hVU)
    trivializationTransitionUnit V
        (ModularCurves.SheafOfModules.restrictOverTrivialization
          X.ringCatSheaf M U e j)
        (ModularCurves.SheafOfModules.restrictOverTrivialization
          X.ringCatSheaf M U g j) =
      Units.map (X.presheaf.map (homOfLE hVU).op).hom.toMonoidHom
        (trivializationTransitionUnit U e g) := by
  dsimp only
  let j : Over U := Over.mk (homOfLE hVU)
  let eV := ModularCurves.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U e j
  let gV := ModularCurves.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U g j
  let s := trivializationTransitionUnit U e g
  let sV : Γ(X, V) := X.presheaf.map (homOfLE hVU).op (s : Γ(X, U))
  have htransition : g.hom = e.hom ≫
      ModularCurves.SheafOfModules.overUnitScalarEnd
        X.ringCatSheaf U (s : Γ(X, U)) := by
    rw [overUnitScalarEnd_transitionUnit]
    simp
  have hrestrict : gV.hom = eV.hom ≫
      ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf V sV := by
    have h := ModularCurves.restrictOverTrivialization_hom_eq_comp_scalar
      M hVU e g (s : Γ(X, U)) htransition
    simpa only [j, eV, gV, sV] using h
  have hcoordinate : eV.inv ≫ gV.hom =
      ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf V sV := by
    rw [hrestrict]
    exact eV.inv_hom_id_assoc _
  apply Units.ext
  change (trivializationTransitionUnit V eV gV : Γ(X, V)) = sV
  let E := ModularCurves.SheafOfModules.overUnitScalarEndRingEquiv
    X.ringCatSheaf V
  apply E.injective
  calc
    E (trivializationTransitionUnit V eV gV : Γ(X, V)) =
        (show End (SheafOfModules.unit (X.ringCatSheaf.over V)) from
          eV.inv ≫ gV.hom) := overUnitScalarEnd_transitionUnit V eV gV
    _ = ModularCurves.SheafOfModules.overUnitScalarEnd
        X.ringCatSheaf V sV := hcoordinate
    _ = E sV := rfl

end

end AlgebraicGeometry.Scheme.Modules
