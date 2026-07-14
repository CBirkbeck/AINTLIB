import ModularCurves.Picard.InvertibleSheafFiniteStageModel
import ModularCurves.Picard.DualPullback.UnitComp

/-!
# Glue data from finite-stage invertible-sheaf cocycles

This file records the coherence laws for the chart transition isomorphisms attached to an
`AffineIntersectionUnitCocycle`. The statements retain the canonical pullback transports, so
they can be used directly in a later effectivity construction on the glued scheme.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private theorem diagonalFac
    (D : Scheme.GlueData) (i : D.J) :
    D.f i i = D.t i i ≫ D.f i i := by
  rw [D.t_id, Category.id_comp]

/-- Conjugating a chart transition by the canonical pullback-unit isomorphisms recovers its
scalar transition automorphism on the ordered overlap. -/
theorem AffineIntersectionUnitCocycle.chartTransitionIso_toUnit
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (pullbackUnitIso (D.f i j)).inv ≫
        (c.chartTransitionIso hopen hpush i j).hom ≫
        (pullbackUnitIso (D.t i j ≫ D.f j i)).hom =
      (c.overlapTransitionIso i j).hom := by
  dsimp only
  rw [AffineIntersectionUnitCocycle.chartTransitionIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The diagonal chart transition is the canonical transport along `t i i ≫ f i i = f i i`.
This is the type-correct identity law for local module descent data. -/
theorem AffineIntersectionUnitCocycle.chartTransitionIso_self
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (c.chartTransitionIso hopen hpush i i).hom =
      ((pullbackCongr (diagonalFac D i)).app (unitObj (D.U i))).hom := by
  dsimp only
  rw [AffineIntersectionUnitCocycle.chartTransitionIso_hom,
    c.overlapTransitionIso_self]
  simp only [Iso.refl_hom]
  rw [← cancel_mono (pullbackUnitIso
    ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).t i i ≫
      (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).f i i)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (ModularCurves.pullbackUnitIso_congrLow
    (diagonalFac
      (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush) i)).symm

end


end AlgebraicGeometry.Scheme.Modules
