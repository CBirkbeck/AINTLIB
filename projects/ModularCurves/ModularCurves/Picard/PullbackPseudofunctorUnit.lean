import ModularCurves.Picard.DualPullback.UnitComp
import ModularCurves.Picard.PullbackPseudofunctor

/-!
# Unit coordinates for pullback descent

This file identifies the generic descent pullback of a morphism between pulled-back structure
modules with ordinary pullback in structure-module coordinates.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private theorem isoEntry
    {C : Type u} [Category C] {O P N Q : C}
    (u : P ≅ O) (e : N ≅ P) (b : Q ≅ O) (a : N ⟶ Q)
    (h : e.hom ≫ u.hom = a ≫ b.hom) :
    u.inv ≫ e.inv ≫ a = b.inv := by
  rw [← cancel_mono b.hom]
  rw [Category.assoc, Category.assoc, ← h]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- Entry-side compatibility of the pullback composition isomorphism with structure modules. -/
theorem unitCompEntry
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullbackUnitIso (f ≫ g)).inv ≫
        ((pullbackComp f g).app (unitObj Z)).inv ≫
        (pullback f).map (pullbackUnitIso g).hom =
      (pullbackUnitIso f).inv := by
  exact isoEntry (pullbackUnitIso (f ≫ g))
    ((pullbackComp f g).app (unitObj Z)) (pullbackUnitIso f)
    ((pullback f).map (pullbackUnitIso g).hom)
    (ModularCurves.pullbackUnitIso_compLow f g)

private theorem isoExit
    {C : Type u} [Category C] {O P N Q K : C}
    (a : N ≅ Q) (e : N ≅ P) (r : P ≅ K)
    (u : P ≅ O) (v : K ≅ O) (b : Q ≅ O)
    (hr : r.hom ≫ v.hom = u.hom)
    (he : e.hom ≫ u.hom = a.hom ≫ b.hom) :
    a.inv ≫ e.hom ≫ r.hom ≫ v.hom = b.hom := by
  rw [hr, he]
  simp only [Iso.inv_hom_id_assoc]

/-- Exit-side compatibility of pullback composition and equality transport with structure
modules. -/
theorem unitCompExit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (h : f ≫ g = k) :
    (pullback f).map (pullbackUnitIso g).inv ≫
        ((pullbackComp f g).app (unitObj Z)).hom ≫
        ((pullbackCongr h).app (unitObj Z)).hom ≫
        (pullbackUnitIso k).hom =
      (pullbackUnitIso f).hom := by
  exact isoExit ((pullback f).mapIso (pullbackUnitIso g))
    ((pullbackComp f g).app (unitObj Z))
    ((pullbackCongr h).app (unitObj Z))
    (pullbackUnitIso (f ≫ g)) (pullbackUnitIso k) (pullbackUnitIso f)
    (ModularCurves.pullbackUnitIso_congrLow h)
    (ModularCurves.pullbackUnitIso_compLow f g)

private theorem pullbackUnitIso_compEntryCongr
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (h : f ≫ g = k) :
    (pullbackUnitIso k).inv ≫
        (((pullbackComp f g).app (unitObj Z)) ≪≫
          ((pullbackCongr h).app (unitObj Z))).inv ≫
        (pullback f).map (pullbackUnitIso g).hom =
      (pullbackUnitIso f).inv := by
  apply isoEntry
  rw [Iso.trans_hom, Category.assoc,
    ModularCurves.pullbackUnitIso_congrLow h,
    ModularCurves.pullbackUnitIso_compLow f g]

private theorem pullbackUnitIso_compExitCongr
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (h : f ≫ g = k) :
    (pullback f).map (pullbackUnitIso g).inv ≫
        (((pullbackComp f g).app (unitObj Z)) ≪≫
          ((pullbackCongr h).app (unitObj Z))).hom ≫
        (pullbackUnitIso k).hom =
      (pullbackUnitIso f).hom := by
  rw [Iso.trans_hom, ← Category.assoc]
  exact unitCompExit f g h

private theorem conjugateMiddle
    {C : Type u} [Category C] {O L P M Q R : C}
    (uLeft : L ≅ O) (eLeft : P ≅ L) (aLeft : P ≅ M)
    (p : P ⟶ Q) (aRight : Q ≅ M) (eRight : Q ≅ R)
    (uRight : R ≅ O) (uMiddle : M ≅ O)
    (hLeft : uLeft.inv ≫ eLeft.inv ≫ aLeft.hom = uMiddle.inv)
    (hRight : aRight.inv ≫ eRight.hom ≫ uRight.hom = uMiddle.hom) :
    uLeft.inv ≫ eLeft.inv ≫ p ≫ eRight.hom ≫ uRight.hom =
      uMiddle.inv ≫ (aLeft.inv ≫ p ≫ aRight.hom) ≫ uMiddle.hom := by
  calc
    uLeft.inv ≫ eLeft.inv ≫ p ≫ eRight.hom ≫ uRight.hom =
        (uLeft.inv ≫ eLeft.inv ≫ aLeft.hom) ≫
          (aLeft.inv ≫ p ≫ aRight.hom) ≫
          (aRight.inv ≫ eRight.hom ≫ uRight.hom) := by
            simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = uMiddle.inv ≫ (aLeft.inv ≫ p ≫ aRight.hom) ≫
        uMiddle.hom := by rw [hLeft, hRight]

/-- Pulling a morphism between two pulled-back structure modules and then passing to unit
coordinates is conjugation by the unit comparison over the further pullback. -/
theorem pullbackPseudofunctor_pullHom_unit
    {X₁ X₂ Y Y' : Scheme.{u}} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (p : (pullback f₁).obj (unitObj X₁) ⟶
      (pullback f₂).obj (unitObj X₂)) :
    (pullbackUnitIso gf₁).inv ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := pullbackPseudofunctor) p g gf₁ gf₂ hgf₁ hgf₂ ≫
        (pullbackUnitIso gf₂).hom =
      (pullbackUnitIso g).inv ≫
        (((pullback g).mapIso (pullbackUnitIso f₁)).inv ≫
          (pullback g).map p ≫
          ((pullback g).mapIso (pullbackUnitIso f₂)).hom) ≫
        (pullbackUnitIso g).hom := by
  let eLeft := ((pullbackComp g f₁).app (unitObj X₁)) ≪≫
    ((pullbackCongr hgf₁).app (unitObj X₁))
  let eRight := ((pullbackComp g f₂).app (unitObj X₂)) ≪≫
    ((pullbackCongr hgf₂).app (unitObj X₂))
  let uLeft := pullbackUnitIso gf₁
  let uRight := pullbackUnitIso gf₂
  let uMiddle := pullbackUnitIso g
  let aLeft := (pullback g).mapIso (pullbackUnitIso f₁)
  let aRight := (pullback g).mapIso (pullbackUnitIso f₂)
  let q := (pullback g).map p
  rw [pullbackPseudofunctor_pullHom]
  simp only [Category.assoc]
  exact conjugateMiddle uLeft eLeft aLeft q aRight eRight uRight uMiddle
    (pullbackUnitIso_compEntryCongr g f₁ hgf₁)
    (pullbackUnitIso_compExitCongr g f₂ hgf₂)

end

end AlgebraicGeometry.Scheme.Modules
