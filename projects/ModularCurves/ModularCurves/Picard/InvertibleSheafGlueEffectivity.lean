import ModularCurves.Picard.InvertibleSheafGlueDataDescent

/-!
# Effectivity of affine-intersection line-bundle descent

This file glues the chartwise unit modules attached to an
`AffineIntersectionUnitCocycle`. The glued module is the usual Cech equalizer of
the chart extensions, with one overlap map twisted by the transition isomorphism.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private noncomputable def AffineIntersectionUnitCocycle.chartExtension
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (_c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    D.glued.Modules :=
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  (pushforward (D.ι i)).obj (unitObj (D.U i))

private noncomputable def AffineIntersectionUnitCocycle.overlapExtension
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (_c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    D.glued.Modules :=
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  (pushforward (D.f i j ≫ D.ι i)).obj (unitObj (D.V (i, j)))

private noncomputable def AffineIntersectionUnitCocycle.chartToOverlapLeft
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    c.chartExtension hopen hpush i ⟶ c.overlapExtension hopen hpush i j :=
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  (pushforward (D.ι i)).map
      ((pullbackPushforwardAdjunction (D.f i j)).homEquiv _ _
        ((c.chartTransitionIso hopen hpush i j).hom ≫
          (pullbackUnitIso (D.t i j ≫ D.f j i)).hom)) ≫
    (pushforwardComp (D.f i j) (D.ι i)).hom.app _

private noncomputable def AffineIntersectionUnitCocycle.chartToOverlapRight
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    c.chartExtension hopen hpush j ⟶ c.overlapExtension hopen hpush i j :=
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  (pushforward (D.ι j)).map
      ((pullbackPushforwardAdjunction (D.t i j ≫ D.f j i)).homEquiv _ _
        (pullbackUnitIso (D.t i j ≫ D.f j i)).hom) ≫
    (pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)).hom.app _ ≫
    (pushforwardCongr (D.glue_condition i j)).hom.app _

private noncomputable def AffineIntersectionUnitCocycle.chartGlueSource
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    D.glued.Modules :=
  ∏ᶜ fun i : J ↦ c.chartExtension hopen hpush i

private noncomputable def AffineIntersectionUnitCocycle.chartGlueTarget
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    D.glued.Modules :=
  ∏ᶜ fun ij : J × J ↦ c.overlapExtension hopen hpush ij.1 ij.2

private noncomputable def AffineIntersectionUnitCocycle.chartGlueLeft
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    c.chartGlueSource hopen hpush ⟶ c.chartGlueTarget hopen hpush :=
  Pi.lift fun ij ↦
    Pi.π (fun i : J ↦ c.chartExtension hopen hpush i) ij.1 ≫
      c.chartToOverlapLeft hopen hpush ij.1 ij.2

private noncomputable def AffineIntersectionUnitCocycle.chartGlueRight
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    c.chartGlueSource hopen hpush ⟶ c.chartGlueTarget hopen hpush :=
  Pi.lift fun ij ↦
    Pi.π (fun i : J ↦ c.chartExtension hopen hpush i) ij.2 ≫
      c.chartToOverlapRight hopen hpush ij.1 ij.2

/-- The module obtained by gluing the chartwise unit modules along the given
affine-intersection transition cocycle. -/
noncomputable def AffineIntersectionUnitCocycle.gluedModule
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    D.glued.Modules :=
  equalizer (c.chartGlueLeft hopen hpush) (c.chartGlueRight hopen hpush)

end

end AlgebraicGeometry.Scheme.Modules
