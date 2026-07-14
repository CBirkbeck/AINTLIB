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

/-- The transition unit between two trivializations on an open subscheme. -/
noncomputable def openTrivializationTransitionUnit
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.restrict U.ι ≅ unitObj U.toScheme) : Γ(X, U)ˣ :=
  trivializationTransitionUnit U
    (overTrivializationOfRestrictIso M U e)
    (overTrivializationOfRestrictIso M U g)

@[simp]
theorem openTrivializationTransitionUnit_self
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    openTrivializationTransitionUnit M U e e = 1 :=
  trivializationTransitionUnit_self U _

@[simp]
theorem openTrivializationTransitionUnit_symm
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.restrict U.ι ≅ unitObj U.toScheme) :
    openTrivializationTransitionUnit M U e g *
      openTrivializationTransitionUnit M U g e = 1 :=
  trivializationTransitionUnit_symm U _ _

/-- Open-subscheme transition units satisfy the cocycle law. -/
theorem openTrivializationTransitionUnit_trans
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g h : M.restrict U.ι ≅ unitObj U.toScheme) :
    openTrivializationTransitionUnit M U e g *
        openTrivializationTransitionUnit M U g h =
      openTrivializationTransitionUnit M U e h :=
  trivializationTransitionUnit_trans U _ _ _

/-- The transition unit of two members of a trivializing family on any common refinement. -/
noncomputable def trivializingCoverTransitionUnitOn
    {X : Scheme.{u}} {M : X.Modules} {ι : Type u}
    (U : ι → X.Opens)
    (e : ∀ i, M.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (V : X.Opens) (i j : ι) (hVi : V ≤ U i) (hVj : V ≤ U j) : Γ(X, V)ˣ :=
  openTrivializationTransitionUnit M V
    (restrictOpenTrivialization hVi (e i))
    (restrictOpenTrivialization hVj (e j))

/-- Transition units from a trivializing family satisfy the cocycle law on every common
refinement. -/
theorem trivializingCoverTransitionUnitOn_trans
    {X : Scheme.{u}} {M : X.Modules} {ι : Type u}
    (U : ι → X.Opens)
    (e : ∀ i, M.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (V : X.Opens) (i j k : ι)
    (hVi : V ≤ U i) (hVj : V ≤ U j) (hVk : V ≤ U k) :
    trivializingCoverTransitionUnitOn U e V i j hVi hVj *
        trivializingCoverTransitionUnitOn U e V j k hVj hVk =
      trivializingCoverTransitionUnitOn U e V i k hVi hVk := by
  exact openTrivializationTransitionUnit_trans M V _ _ _

/-- The canonical transition unit on the pairwise overlap of two members of a trivializing
family. -/
noncomputable def trivializingCoverTransitionUnit
    {X : Scheme.{u}} {M : X.Modules} {ι : Type u}
    (U : ι → X.Opens)
    (e : ∀ i, M.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (i j : ι) : Γ(X, U i ⊓ U j)ˣ :=
  trivializingCoverTransitionUnitOn U e (U i ⊓ U j) i j inf_le_left inf_le_right

/-- The three direct transition units on a triple overlap satisfy the cocycle law. -/
theorem trivializingCoverTransitionUnitOn_triple
    {X : Scheme.{u}} {M : X.Modules} {ι : Type u}
    (U : ι → X.Opens)
    (e : ∀ i, M.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (i j k : ι) :
    let V := (U i ⊓ U j) ⊓ U k
    let hVi : V ≤ U i := inf_le_left.trans inf_le_left
    let hVj : V ≤ U j := inf_le_left.trans inf_le_right
    let hVk : V ≤ U k := inf_le_right
    trivializingCoverTransitionUnitOn U e V i j hVi hVj *
        trivializingCoverTransitionUnitOn U e V j k hVj hVk =
      trivializingCoverTransitionUnitOn U e V i k hVi hVk := by
  dsimp only
  exact trivializingCoverTransitionUnitOn_trans U e _ i j k _ _ _

end

end AlgebraicGeometry.Scheme.Modules
