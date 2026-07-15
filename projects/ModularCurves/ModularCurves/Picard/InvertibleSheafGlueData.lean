import ModularCurves.Picard.InvertibleSheafFiniteStageModel
import ModularCurves.Picard.DualPullback.UnitComp
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

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

/-- The contravariant, `Cat`-valued pseudofunctor of sheaves of modules on schemes. This is
the left-adjoint part of `Scheme.Modules.pseudofunctor`. -/
def pullbackPseudofunctor :=
  pseudofunctor.comp Bicategory.Adj.forget₁

/-- The ordered affine overlap in the glue datum, regarded as the chosen pullback of the two
chart maps into the glued scheme. -/
def affineIntersectionChartChosenPullback
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    ChosenPullback (D.ι i) (D.ι j) := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  exact
    { pullback := D.V (i, j)
      p₁ := D.f i j
      p₂ := D.t i j ≫ D.f j i
      condition := (D.glue_condition i j).symm
      isLimit := D.vPullbackConeIsLimit i j }

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

private theorem isoEntry
    {C : Type u} [Category C] {O P N Q : C}
    (u : P ≅ O) (e : N ≅ P) (b : Q ≅ O) (a : N ⟶ Q)
    (h : e.hom ≫ u.hom = a ≫ b.hom) :
    u.inv ≫ e.inv ≫ a = b.inv := by
  rw [← cancel_mono b.hom]
  rw [Category.assoc, Category.assoc, ← h]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]

private theorem unitCompEntry
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackUnitIso (f ≫ g)).inv ≫
        ((pullbackComp f g).app (unitObj Z)).inv ≫
        (pullback f).map (pullbackUnitIso g).hom =
      (pullbackUnitIso f).inv := by
  let u := pullbackUnitIso (f ≫ g)
  let e := (pullbackComp f g).app (unitObj Z)
  let b := pullbackUnitIso f
  let a := (pullback f).map (pullbackUnitIso g).hom
  exact isoEntry u e b a (ModularCurves.pullbackUnitIso_compLow f g)

private theorem isoExit
    {C : Type u} [Category C] {O P N Q K : C}
    (a : N ≅ Q) (e : N ≅ P) (r : P ≅ K)
    (u : P ≅ O) (v : K ≅ O) (b : Q ≅ O)
    (hr : r.hom ≫ v.hom = u.hom)
    (he : e.hom ≫ u.hom = a.hom ≫ b.hom) :
    a.inv ≫ e.hom ≫ r.hom ≫ v.hom = b.hom := by
  rw [hr, he]
  simp only [Iso.inv_hom_id_assoc]

private theorem unitCompExit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (h : f ≫ g = k) :
    (pullback f).map (pullbackUnitIso g).inv ≫
        ((pullbackComp f g).app (unitObj Z)).hom ≫
        ((pullbackCongr h).app (unitObj Z)).hom ≫
        (pullbackUnitIso k).hom =
      (pullbackUnitIso f).hom := by
  let a := (pullback f).mapIso (pullbackUnitIso g)
  let e := (pullbackComp f g).app (unitObj Z)
  let r := (pullbackCongr h).app (unitObj Z)
  let u := pullbackUnitIso (f ≫ g)
  let v := pullbackUnitIso k
  let b := pullbackUnitIso f
  exact isoExit a e r u v b
    (ModularCurves.pullbackUnitIso_congrLow h)
    (ModularCurves.pullbackUnitIso_compLow f g)

private theorem pairSwapFac
    (D : Scheme.GlueData) (i j : D.J) :
    D.t i j ≫ (D.t j i ≫ D.f i j) = D.f i j := by
  rw [← Category.assoc, D.t_inv, Category.id_comp]

private theorem leftFromCoordinates
    {C : Type u} [Category C] {O A N B M : C}
    (u : A ≅ O) (e : N ≅ A) (a : N ≅ B) (v : B ≅ O)
    (b : M ≅ B) (p : N ⟶ M) (q : B ⟶ B)
    (hentry : u.inv ≫ e.inv ≫ a.hom = v.inv)
    (hcoord : a.inv ≫ p ≫ b.hom = q) :
    u.inv ≫ e.inv ≫ p ≫ b.hom = v.inv ≫ q := by
  calc
    u.inv ≫ e.inv ≫ p ≫ b.hom =
        (u.inv ≫ e.inv ≫ a.hom) ≫
          (a.inv ≫ p ≫ b.hom) := by
            simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = v.inv ≫ q := by rw [hentry, hcoord]

/-- The inverse chart transition also recovers the inverse scalar automorphism after
conjugation by the two pullback-unit isomorphisms. -/
theorem AffineIntersectionUnitCocycle.chartTransitionIso_inv_toUnit
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (pullbackUnitIso (D.t i j ≫ D.f j i)).inv ≫
        (c.chartTransitionIso hopen hpush i j).inv ≫
        (pullbackUnitIso (D.f i j)).hom =
      (c.overlapTransitionIso i j).inv := by
  dsimp only
  rw [AffineIntersectionUnitCocycle.chartTransitionIso_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- Pulling a chart transition back along the pair-swap map preserves its scalar-coordinate
description. -/
theorem AffineIntersectionUnitCocycle.pullback_chartTransitionIso_toUnit
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (pullback (D.t i j)).map (pullbackUnitIso (D.f j i)).inv ≫
        (pullback (D.t i j)).map
          (c.chartTransitionIso hopen hpush j i).hom ≫
        ((pullback (D.t i j)).mapIso
          (pullbackUnitIso (D.t j i ≫ D.f i j))).hom =
      (pullback (D.t i j)).map (c.overlapTransitionIso j i).hom := by
  dsimp only
  have h := congrArg (fun k => (pullback
      ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).t i j)).map k)
    (c.chartTransitionIso_toUnit hopen hpush j i)
  simpa only [Functor.map_comp, Functor.mapIso_hom] using h

private theorem chartTransitionIso_swap_left
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (pullbackUnitIso (D.t i j ≫ D.f j i)).inv ≫
        ((pullbackComp (D.t i j) (D.f j i)).app
          (unitObj (D.U j))).inv ≫
        (pullback (D.t i j)).map
          (c.chartTransitionIso hopen hpush j i).hom ≫
        ((pullback (D.t i j)).mapIso
          (pullbackUnitIso (D.t j i ≫ D.f i j))).hom =
      (pullbackUnitIso (D.t i j)).inv ≫
        (pullback (D.t i j)).map (c.overlapTransitionIso j i).hom := by
  dsimp only
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let u := pullbackUnitIso (D.t i j ≫ D.f j i)
  let e := (pullbackComp (D.t i j) (D.f j i)).app (unitObj (D.U j))
  let a := (pullback (D.t i j)).mapIso (pullbackUnitIso (D.f j i))
  let v := pullbackUnitIso (D.t i j)
  let b := (pullback (D.t i j)).mapIso
    (pullbackUnitIso (D.t j i ≫ D.f i j))
  let p := (pullback (D.t i j)).map
    (c.chartTransitionIso hopen hpush j i).hom
  let q := (pullback (D.t i j)).map (c.overlapTransitionIso j i).hom
  have hcoord : a.inv ≫ p ≫ b.hom = q := by
    simpa only [a, p, b, q, Functor.mapIso_hom,
      Functor.mapIso_inv] using
        (c.pullback_chartTransitionIso_toUnit hopen hpush i j)
  exact leftFromCoordinates u e a v b p q
    (unitCompEntry (D.t i j) (D.f j i)) hcoord

private theorem chartTransitionIso_swap_right
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let h := pairSwapFac D i j
    ((pullback (D.t i j)).mapIso
          (pullbackUnitIso (D.t j i ≫ D.f i j))).inv ≫
        ((pullbackComp (D.t i j) (D.t j i ≫ D.f i j)).app
          (unitObj (D.U i))).hom ≫
        ((pullbackCongr h).app (unitObj (D.U i))).hom ≫
        (pullbackUnitIso (D.f i j)).hom =
      (pullbackUnitIso (D.t i j)).hom := by
  dsimp only
  simpa only [Functor.mapIso_inv] using unitCompExit
    ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).t i j)
    ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).t j i ≫
      (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).f i j)
    (pairSwapFac
      (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush) i j)

private theorem composite_eq_of_conjugate
    {C : Type u} [Category C] {A B Q O : C}
    (u : A ≅ O) (w : Q ≅ O) (l : A ⟶ B) (r : B ⟶ Q)
    (t : A ⟶ Q) (a : O ⟶ B) (q : B ⟶ B) (b : B ⟶ O)
    (s : O ⟶ O)
    (hl : u.inv ≫ l = a ≫ q) (hr : r ≫ w.hom = b)
    (hs : a ≫ q ≫ b = s) (ht : u.inv ≫ t ≫ w.hom = s) :
    l ≫ r = t := by
  apply (cancel_epi u.inv).1
  apply (cancel_mono w.hom).1
  calc
    (u.inv ≫ (l ≫ r)) ≫ w.hom =
        (u.inv ≫ l) ≫ (r ≫ w.hom) := by
          simp only [Category.assoc]
    _ = (a ≫ q) ≫ b := by rw [hl, hr]
    _ = a ≫ q ≫ b := Category.assoc _ _ _
    _ = s := hs
    _ = u.inv ≫ t ≫ w.hom := ht.symm
    _ = (u.inv ≫ t) ≫ w.hom := (Category.assoc _ _ _).symm

private noncomputable def chartTransitionIsoSwapLeftHom
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (pullback (D.t i j ≫ D.f j i)).obj (unitObj (D.U j)) ⟶
      (pullback (D.t i j)).obj (unitObj (D.V (j, i))) :=
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  ((pullbackComp (D.t i j) (D.f j i)).app (unitObj (D.U j))).inv ≫
    (pullback (D.t i j)).map
      (c.chartTransitionIso hopen hpush j i).hom ≫
    ((pullback (D.t i j)).mapIso
      (pullbackUnitIso (D.t j i ≫ D.f i j))).hom

private noncomputable def chartTransitionIsoSwapRightHom
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (pullback (D.t i j)).obj (unitObj (D.V (j, i))) ⟶
      (pullback (D.f i j)).obj (unitObj (D.U i)) :=
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  (pullbackUnitIso (D.t i j)).hom ≫
    (pullbackUnitIso (D.f i j)).inv

/-- The reverse chart transition pulled back along the pair-swap map, with the entry and exit
transports expressed in their canonical pullback-unit normal forms. -/
noncomputable def AffineIntersectionUnitCocycle.chartTransitionIsoSwapHom
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (pullback (D.t i j ≫ D.f j i)).obj (unitObj (D.U j)) ⟶
      (pullback (D.f i j)).obj (unitObj (D.U i)) :=
  chartTransitionIsoSwapLeftHom c hopen hpush i j ≫
    chartTransitionIsoSwapRightHom hopen hpush i j

private theorem chartTransitionIsoSwapLeftHom_normalize
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    (pullbackUnitIso (D.t i j ≫ D.f j i)).inv ≫
        chartTransitionIsoSwapLeftHom c hopen hpush i j =
      (pullbackUnitIso (D.t i j)).inv ≫
        (pullback (D.t i j)).map (c.overlapTransitionIso j i).hom := by
  dsimp only [chartTransitionIsoSwapLeftHom]
  exact chartTransitionIso_swap_left c hopen hpush i j

private theorem chartTransitionIsoSwapRightHom_normalize
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    chartTransitionIsoSwapRightHom hopen hpush i j ≫
        (pullbackUnitIso (D.f i j)).hom =
      (pullbackUnitIso (D.t i j)).hom := by
  dsimp only [chartTransitionIsoSwapRightHom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Pulling the reverse chart transition along the pair-swap map gives the inverse of the
original chart transition, with all composite-pullback transports made explicit in
`chartTransitionIsoSwapHom`. -/
theorem AffineIntersectionUnitCocycle.chartTransitionIsoSwapHom_eq_inv
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    c.chartTransitionIsoSwapHom hopen hpush i j =
      (c.chartTransitionIso hopen hpush i j).inv := by
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  apply composite_eq_of_conjugate
    (pullbackUnitIso (D.t i j ≫ D.f j i))
    (pullbackUnitIso (D.f i j))
    (chartTransitionIsoSwapLeftHom c hopen hpush i j)
    (chartTransitionIsoSwapRightHom hopen hpush i j)
    (c.chartTransitionIso hopen hpush i j).inv
    (pullbackUnitIso (D.t i j)).inv
    ((pullback (D.t i j)).map (c.overlapTransitionIso j i).hom)
    (pullbackUnitIso (D.t i j)).hom
    (c.overlapTransitionIso i j).inv
  · exact chartTransitionIsoSwapLeftHom_normalize c hopen hpush i j
  · exact chartTransitionIsoSwapRightHom_normalize hopen hpush i j
  · exact c.overlapTransitionIso_swap i j
  · exact c.chartTransitionIso_inv_toUnit hopen hpush i j

private noncomputable def chartTransitionIsoCoordinatePullbackMiddle
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) {T : Scheme.{u}}
    (g : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j)) :
    (pullback g).obj (unitObj
        ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j))) ⟶
      (pullback g).obj (unitObj
        ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j))) :=
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  (pullback g).map (pullbackUnitIso (D.f i j)).inv ≫
    (pullback g).map (c.chartTransitionIso hopen hpush i j).hom ≫
    (pullback g).map (pullbackUnitIso (D.t i j ≫ D.f j i)).hom

private theorem chartTransitionIsoCoordinatePullbackMiddle_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) {T : Scheme.{u}}
    (g : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j)) :
    chartTransitionIsoCoordinatePullbackMiddle c hopen hpush i j g =
      (pullback g).map (c.overlapTransitionIso i j).hom := by
  dsimp only [chartTransitionIsoCoordinatePullbackMiddle]
  have h := congrArg (fun k => (pullback g).map k)
    (c.chartTransitionIso_toUnit hopen hpush i j)
  simpa only [Functor.map_comp] using h

/-- A chart transition pulled back to a further overlap and expressed as an endomorphism of
that overlap's unit sheaf. -/
noncomputable def AffineIntersectionUnitCocycle.chartTransitionIsoCoordinatePullback
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) {T : Scheme.{u}}
    (g : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j)) :
    unitObj T ⟶ unitObj T :=
  (pullbackUnitIso g).inv ≫
    chartTransitionIsoCoordinatePullbackMiddle c hopen hpush i j g ≫
    (pullbackUnitIso g).hom

/-- In unit coordinates, a pulled-back chart transition is multiplication by the pulled-back
overlap transition function. -/
theorem AffineIntersectionUnitCocycle.chartTransitionIsoCoordinatePullback_eq
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) {T : Scheme.{u}}
    (g : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j)) :
    c.chartTransitionIsoCoordinatePullback hopen hpush i j g =
      (pullbackUnitIso g).inv ≫
        (pullback g).map (c.overlapTransitionIso i j).hom ≫
        (pullbackUnitIso g).hom := by
  rw [chartTransitionIsoCoordinatePullback,
    chartTransitionIsoCoordinatePullbackMiddle_eq]

/-- The chart transitions satisfy the Cech equation after pullback to the canonical affine
triple intersection. The middle map is the `(j,k)` leg induced by the glue-data triple
transition. -/
theorem AffineIntersectionUnitCocycle.chartTransitionIsoCoordinatePullback_cocycle
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    let T := Spec (CommRingCat.of
      (F.obj (Scheme.GlueData.affineIntersectionTripleIndex i j k)))
    let fLeft : T ⟶ Scheme.GlueData.affineIntersectionOverlap F i j :=
      Spec.map (CommRingCat.ofHom ((F.map
        (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)).hom.toRingHom))
    let fMiddle : T ⟶ Scheme.GlueData.affineIntersectionOverlap F j k :=
      Spec.map (CommRingCat.ofHom ((F.map
        (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)).hom.toRingHom))
    let fRight : T ⟶ Scheme.GlueData.affineIntersectionOverlap F i k :=
      Spec.map (CommRingCat.ofHom ((F.map
        (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)).hom.toRingHom))
    c.chartTransitionIsoCoordinatePullback hopen hpush i j fLeft ≫
        c.chartTransitionIsoCoordinatePullback hopen hpush j k fMiddle =
      c.chartTransitionIsoCoordinatePullback hopen hpush i k fRight := by
  dsimp only
  rw [c.chartTransitionIsoCoordinatePullback_eq,
    c.chartTransitionIsoCoordinatePullback_eq,
    c.chartTransitionIsoCoordinatePullback_eq]
  exact c.overlapTransitionIso_cocycle i j k

end


end AlgebraicGeometry.Scheme.Modules
