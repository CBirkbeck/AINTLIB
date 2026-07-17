import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# The pullback pseudofunctor for scheme modules

This file exposes the left-adjoint part of mathlib's existing scheme-module pseudofunctor and
identifies its flexible composition isomorphisms with `pullbackComp` followed by `pullbackCongr`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The contravariant, `Cat`-valued pseudofunctor of sheaves of modules on schemes. This is
the left-adjoint part of `Scheme.Modules.pseudofunctor`. -/
def pullbackPseudofunctor :=
  pseudofunctor.comp Bicategory.Adj.forget₁

/-- The functor mapped by `pullbackPseudofunctor` is the usual pullback of scheme modules. -/
theorem pullbackPseudofunctor_map_toFunctor
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackPseudofunctor.map f.op.toLoc).toFunctor = pullback f := by
  rfl

/-- Mapping a module morphism by `pullbackPseudofunctor` is the usual pullback map. -/
theorem pullbackPseudofunctor_map_map
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : Y.Modules} (p : M ⟶ N) :
    (pullbackPseudofunctor.map f.op.toLoc).toFunctor.map p =
      (pullback f).map p := by
  rfl

/-- The hom of the flexible composition isomorphism for the pullback pseudofunctor, evaluated
on a module. -/
theorem pullbackPseudofunctor_mapComp'_hom_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (h : f ≫ g = k) (M : Z.Modules) :
    ((pullbackPseudofunctor.mapComp' g.op.toLoc f.op.toLoc k.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).hom.toNatTrans.app M) =
      ((((pullbackComp f g).app M) ≪≫ ((pullbackCongr h).app M)).inv) := by
  subst k
  have hcomp : g.op.toLoc ≫ f.op.toLoc = (f ≫ g).op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp]
  cases hcomp
  change
    ((pullbackPseudofunctor.mapComp' g.op.toLoc f.op.toLoc
      (g.op.toLoc ≫ f.op.toLoc) rfl).hom.toNatTrans.app M) = _
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  unfold pullbackPseudofunctor
  rw [Pseudofunctor.comp_mapComp,
    Bicategory.Adj.forget₁_mapComp]
  rfl

/-- The inverse of the flexible composition isomorphism for the pullback pseudofunctor,
evaluated on a module. -/
theorem pullbackPseudofunctor_mapComp'_inv_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (h : f ≫ g = k) (M : Z.Modules) :
    ((pullbackPseudofunctor.mapComp' g.op.toLoc f.op.toLoc k.op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h])).inv.toNatTrans.app M) =
      ((((pullbackComp f g).app M) ≪≫ ((pullbackCongr h).app M)).hom) := by
  subst k
  have hcomp : g.op.toLoc ≫ f.op.toLoc = (f ≫ g).op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp]
  cases hcomp
  change
    ((pullbackPseudofunctor.mapComp' g.op.toLoc f.op.toLoc
      (g.op.toLoc ≫ f.op.toLoc) rfl).inv.toNatTrans.app M) = _
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  unfold pullbackPseudofunctor
  rw [Pseudofunctor.comp_mapComp,
    Bicategory.Adj.forget₁_mapComp]
  rfl

/-- Pulling a morphism to a further scheme using the descent API is ordinary pullback,
conjugated by the two composition isomorphisms. -/
theorem pullbackPseudofunctor_pullHom
    {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (p : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := pullbackPseudofunctor) p g gf₁ gf₂ hgf₁ hgf₂ =
      (((pullbackComp g f₁).app M₁) ≪≫
          ((pullbackCongr hgf₁).app M₁)).inv ≫
        (pullback g).map p ≫
      (((pullbackComp g f₂).app M₂) ≪≫
          ((pullbackCongr hgf₂).app M₂)).hom := by
  unfold Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  rw [pullbackPseudofunctor_mapComp'_hom_app g f₁ hgf₁ M₁,
    pullbackPseudofunctor_mapComp'_inv_app g f₂ hgf₂ M₂]
  rfl

end


end AlgebraicGeometry.Scheme.Modules
