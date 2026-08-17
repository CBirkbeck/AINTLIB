/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FieldLeaf

/-!
# Restriction-compatibility of the native tensor-ideal trivialisation ([NAT-RESTRICT])

The `ORD-G` pointwise divisor computation (`.mathlib-quality/decomposition-e4a-self.md`,
cont.19) needs the transition units of the G2 chart dataset to decompose into *per-chart*
factors; the `a`/`b` dressing units of `transitionUnitOfCover_eq_dressed_native` live only
on overlaps, which blocks the germ-order reading away from the anchor chart. The fix is
that with the e-family built from `nativeTensorIdealTriv` the dressing disappears, because
the native trivialisation *restricts on the nose*:

* `nuPullback_app_restrictTransport` ([NR-1], the brick): the `ν`-comparison map is
  natural under the open-restriction transport, at the level of `⊤`-sections.
* `restrictTrivialization_nativeTensorIdealTriv_inv_comp_nu` ([NR-2]): the restricted
  native trivialisation satisfies the `W`-level `ν`-characterisation.
* `restrictTrivialization_nativeTensorIdealTriv` ([NR-3], NAT-RESTRICT): the restriction
  of the native trivialisation *is* the native trivialisation of the restricted
  generators.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

-- the semireducible sheaf-type wall (v4.33 idiom)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurves

section NativeRestriction

variable {X : Scheme.{u}} (M : X.Modules)
variable (J₁ J₂ : X.IdealSheafData)
variable (e : tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁) ≅
  AlgebraicGeometry.Scheme.Modules.idealModule J₂)

/-- The `⊤`-section transport of the open restriction `W ≤ V`: adjunction unit, `eqToHom`
re-indexing, composition iso, congruence — the composite whose value at the trivialising
section is computed by `restrictTrivialization_inv_app_top_one`. -/
noncomputable def restrictTransportSection {V W : X.Opens} (hWV : W ≤ V) (P : X.Modules)
    (htop : (⊤ : W.toScheme.Opens) = (X.homOfLE hWV) ⁻¹ᵁ (⊤ : V.toScheme.Opens))
    (x : ((Scheme.Modules.pullback V.ι).obj P).val.obj
      (Opposite.op (⊤ : V.toScheme.Opens))) :
    ((Scheme.Modules.pullback W.ι).obj P).val.obj
      (Opposite.op (⊤ : W.toScheme.Opens)) :=
  ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app P).inv.val.app
    (Opposite.op (⊤ : W.toScheme.Opens))
    (((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app P).hom.val.app
      (Opposite.op (⊤ : W.toScheme.Opens))
      (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
          ((Scheme.Modules.pullback V.ι).obj P)).presheaf.map (eqToHom htop).op
        (((Scheme.Modules.pullbackPushforwardAdjunction
            (X.homOfLE hWV)).unit.app
          ((Scheme.Modules.pullback V.ι).obj P)).val.app
          (Opposite.op (⊤ : V.toScheme.Opens)) x)))

/-- **([NR-ext])** A hom out of the unit sheaf of modules is determined by its value at
the `⊤`-section `1`: the section it corresponds to under `unitHomEquiv` is res-compatible,
so its `⊤`-value pins every value. -/
theorem unit_hom_ext {Y : Scheme.{u}} {N : Y.Modules} (f g : unitObj Y ⟶ N)
    (h : f.val.app (Opposite.op (⊤ : Y.Opens))
        (show Y.presheaf.obj (Opposite.op (⊤ : Y.Opens)) from 1) =
      g.val.app (Opposite.op (⊤ : Y.Opens))
        (show Y.presheaf.obj (Opposite.op (⊤ : Y.Opens)) from 1)) : f = g := by
  apply (SheafOfModules.unitHomEquiv N).injective
  refine PresheafOfModules.sections_ext _ _ (fun U => ?_)
  have hf := PresheafOfModules.sections_property ((SheafOfModules.unitHomEquiv N) f)
    (X := Opposite.op (⊤ : Y.Opens)) (Y := U) (homOfLE le_top).op
  have hg := PresheafOfModules.sections_property ((SheafOfModules.unitHomEquiv N) g)
    (X := Opposite.op (⊤ : Y.Opens)) (Y := U) (homOfLE le_top).op
  rw [← hf, ← hg]
  exact congrArg _ h

/-- **([NR-ots])** The open-restriction of an `openTopSection` along `W ≤ V` is the
`openTopSection` of the restricted section: the two cast-paths from `Γ(X, V)` to
`Γ(W, ⊤)` agree. -/
theorem openTopSection_homOfLE {X : Scheme.{u}} {V W : X.Opens} (hWV : W ≤ V)
    (htop : (⊤ : W.toScheme.Opens) = (X.homOfLE hWV) ⁻¹ᵁ (⊤ : V.toScheme.Opens))
    (r : Γ(X, V)) :
    W.toScheme.presheaf.map (eqToHom htop).op
        ((Scheme.Hom.app (X.homOfLE hWV) (⊤ : V.toScheme.Opens)).hom
          (Scheme.Modules.openTopSection V r)) =
      Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op r) := by
  simp only [Scheme.Modules.openTopSection, Scheme.Opens.ι_appIso, Iso.refl_hom,
    Scheme.homOfLE_app]
  rw [show W.toScheme.presheaf.map (eqToHom htop).op =
    X.presheaf.map (W.ι.opensFunctor.map (eqToHom htop)).op from rfl]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  simp only [Category.comp_id, Category.id_comp, ← Functor.map_comp, ← op_comp]
  exact congrArg
    (fun (q : (W.ι ''ᵁ (⊤ : W.toScheme.Opens) : X.Opens) ⟶ V) =>
      (ConcreteCategory.hom (X.presheaf.map q.op)) r)
    (Subsingleton.elim _ _)

/-- **([NR-1a])** The `⊤`-section transport is natural in the module: a global map of
modules walks through the four transport pieces (adjunction unit, `eqToHom` re-index,
composition iso, congruence — each a natural transformation). -/
theorem restrictTransportSection_naturality {V W : X.Opens} (hWV : W ≤ V)
    {A B : X.Modules} (f : A ⟶ B)
    (htop : (⊤ : W.toScheme.Opens) = (X.homOfLE hWV) ⁻¹ᵁ (⊤ : V.toScheme.Opens))
    (x : ((Scheme.Modules.pullback V.ι).obj A).val.obj
      (Opposite.op (⊤ : V.toScheme.Opens))) :
    ((Scheme.Modules.pullback W.ι).map f).val.app
        (Opposite.op (⊤ : W.toScheme.Opens))
        (restrictTransportSection hWV A htop x) =
      restrictTransportSection hWV B htop
        (((Scheme.Modules.pullback V.ι).map f).val.app
          (Opposite.op (⊤ : V.toScheme.Opens)) x) := by
  have h4 := congrArg
    (fun (q : (Scheme.Modules.pullback V.ι).obj A ⟶
        (Scheme.Modules.pushforward (X.homOfLE hWV)).obj
          ((Scheme.Modules.pullback (X.homOfLE hWV)).obj
            ((Scheme.Modules.pullback V.ι).obj B))) =>
      q.val.app (Opposite.op (⊤ : V.toScheme.Opens)) x)
    ((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.naturality
      ((Scheme.Modules.pullback V.ι).map f))
  have h3 := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullback (X.homOfLE hWV)).map
      ((Scheme.Modules.pullback V.ι).map f)).val (eqToHom htop).op
    (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
      ((Scheme.Modules.pullback V.ι).obj A)).val.app
      (Opposite.op (⊤ : V.toScheme.Opens)) x)
  have h2 := congrArg
    (fun (q : (Scheme.Modules.pullback (X.homOfLE hWV)).obj
        ((Scheme.Modules.pullback V.ι).obj A) ⟶
        (Scheme.Modules.pullback (X.homOfLE hWV ≫ V.ι)).obj B) =>
      q.val.app (Opposite.op (⊤ : W.toScheme.Opens))
        (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
            ((Scheme.Modules.pullback V.ι).obj A)).presheaf.map (eqToHom htop).op
          (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
            ((Scheme.Modules.pullback V.ι).obj A)).val.app
            (Opposite.op (⊤ : V.toScheme.Opens)) x)))
    ((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).hom.naturality f)
  have h1 := congrArg
    (fun (q : (Scheme.Modules.pullback (X.homOfLE hWV ≫ V.ι)).obj A ⟶
        (Scheme.Modules.pullback W.ι).obj B) =>
      q.val.app (Opposite.op (⊤ : W.toScheme.Opens))
        (((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app A).hom.val.app
          (Opposite.op (⊤ : W.toScheme.Opens))
          (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
              ((Scheme.Modules.pullback V.ι).obj A)).presheaf.map (eqToHom htop).op
            (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
              ((Scheme.Modules.pullback V.ι).obj A)).val.app
              (Opposite.op (⊤ : V.toScheme.Opens)) x))))
    ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).inv.naturality f)
  simp only [restrictTransportSection]
  have s1 : ((Scheme.Modules.pullback W.ι).map f).val.app
      (Opposite.op (⊤ : W.toScheme.Opens))
      (((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app A).inv.val.app
        (Opposite.op (⊤ : W.toScheme.Opens))
        (((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app A).hom.val.app
          (Opposite.op (⊤ : W.toScheme.Opens))
          (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
              ((Scheme.Modules.pullback V.ι).obj A)).presheaf.map (eqToHom htop).op
            (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
              ((Scheme.Modules.pullback V.ι).obj A)).val.app
              (Opposite.op (⊤ : V.toScheme.Opens)) x)))) =
      ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app B).inv.val.app
        (Opposite.op (⊤ : W.toScheme.Opens))
        (((Scheme.Modules.pullback (X.homOfLE hWV ≫ V.ι)).map f).val.app
          (Opposite.op (⊤ : W.toScheme.Opens))
          (((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app A).hom.val.app
            (Opposite.op (⊤ : W.toScheme.Opens))
            (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
                ((Scheme.Modules.pullback V.ι).obj A)).presheaf.map (eqToHom htop).op
              (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
                ((Scheme.Modules.pullback V.ι).obj A)).val.app
                (Opposite.op (⊤ : V.toScheme.Opens)) x)))) := h1.symm
  refine s1.trans ?_
  refine congrArg (((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app B).inv.val.app
    (Opposite.op (⊤ : W.toScheme.Opens))) ?_
  have s2 : ((Scheme.Modules.pullback (X.homOfLE hWV ≫ V.ι)).map f).val.app
      (Opposite.op (⊤ : W.toScheme.Opens))
      (((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app A).hom.val.app
        (Opposite.op (⊤ : W.toScheme.Opens))
        (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
            ((Scheme.Modules.pullback V.ι).obj A)).presheaf.map (eqToHom htop).op
          (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
            ((Scheme.Modules.pullback V.ι).obj A)).val.app
            (Opposite.op (⊤ : V.toScheme.Opens)) x))) =
      ((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app B).hom.val.app
        (Opposite.op (⊤ : W.toScheme.Opens))
        (((Scheme.Modules.pullback (X.homOfLE hWV)).map
            ((Scheme.Modules.pullback V.ι).map f)).val.app
          (Opposite.op (⊤ : W.toScheme.Opens))
          (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
              ((Scheme.Modules.pullback V.ι).obj A)).presheaf.map (eqToHom htop).op
            (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
              ((Scheme.Modules.pullback V.ι).obj A)).val.app
              (Opposite.op (⊤ : V.toScheme.Opens)) x))) := h2.symm
  refine s2.trans ?_
  refine congrArg (((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app B).hom.val.app
    (Opposite.op (⊤ : W.toScheme.Opens))) ?_
  have s3 : ((Scheme.Modules.pullback (X.homOfLE hWV)).map
      ((Scheme.Modules.pullback V.ι).map f)).val.app
      (Opposite.op (⊤ : W.toScheme.Opens))
      (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
          ((Scheme.Modules.pullback V.ι).obj A)).presheaf.map (eqToHom htop).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
          ((Scheme.Modules.pullback V.ι).obj A)).val.app
          (Opposite.op (⊤ : V.toScheme.Opens)) x)) =
      ((Scheme.Modules.pullback (X.homOfLE hWV)).obj
          ((Scheme.Modules.pullback V.ι).obj B)).presheaf.map (eqToHom htop).op
        (((Scheme.Modules.pullback (X.homOfLE hWV)).map
            ((Scheme.Modules.pullback V.ι).map f)).val.app
          (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (⊤ : V.toScheme.Opens)))
          (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
            ((Scheme.Modules.pullback V.ι).obj A)).val.app
            (Opposite.op (⊤ : V.toScheme.Opens)) x)) := h3
  refine s3.trans ?_
  refine congrArg (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
      ((Scheme.Modules.pullback V.ι).obj B)).presheaf.map (eqToHom htop).op) ?_
  have s4 : ((Scheme.Modules.pullback (X.homOfLE hWV)).map
      ((Scheme.Modules.pullback V.ι).map f)).val.app
      (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (⊤ : V.toScheme.Opens)))
      (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
        ((Scheme.Modules.pullback V.ι).obj A)).val.app
        (Opposite.op (⊤ : V.toScheme.Opens)) x) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
        ((Scheme.Modules.pullback V.ι).obj B)).val.app
        (Opposite.op (⊤ : V.toScheme.Opens))
        (((Scheme.Modules.pullback V.ι).map f).val.app
          (Opposite.op (⊤ : V.toScheme.Opens)) x) := h4.symm
  exact s4

/-- **([NR-sh-unit-nat])** The sheafification of a presheaf map, evaluated on a
sheafification-unit image: the abstract element form of the unit naturality (small
binders, so instantiation at large composites is cheap). -/
theorem sheafificationMap_app_unit {Y' : Scheme.{u}}
    {P Q : PresheafOfModules.{u} Y'.ringCatSheaf.obj} (g : P ⟶ Q)
    (V : (Opens ↥Y')ᵒᵖ) (w : P.obj V) :
    ((PresheafOfModules.sheafification (𝟙 Y'.ringCatSheaf.obj)).map g).val.app V
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y'.ringCatSheaf.obj)).unit.app P).app V w) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 Y'.ringCatSheaf.obj)).unit.app Q).app V (g.app V w) := by
  have hn := (PresheafOfModules.sheafificationAdjunction
    (𝟙 Y'.ringCatSheaf.obj)).unit.naturality g
  have happ := congrArg (fun (q : P ⟶
      (PresheafOfModules.sheafification (𝟙 Y'.ringCatSheaf.obj) ⋙
        SheafOfModules.forget Y'.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 Y'.ringCatSheaf.obj)).obj Q) =>
    q.app V w) hn
  exact happ.symm

/-- **([NR-sh-unit-nat-eq])** The composed form of `sheafificationMap_app_unit`: when
the presheaf-level value is known, the sheafified map on the unit image is the unit
image of that value (small binders — the congruence happens at the abstract codomain,
so instantiating at large tensor objects is cheap). -/
theorem sheafificationMap_app_unit_eq {Y' : Scheme.{u}}
    {P Q : PresheafOfModules.{u} Y'.ringCatSheaf.obj} (g : P ⟶ Q)
    (V : (Opens ↥Y')ᵒᵖ) (w : P.obj V) {w' : Q.obj V} (h : g.app V w = w') :
    ((PresheafOfModules.sheafification (𝟙 Y'.ringCatSheaf.obj)).map g).val.app V
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y'.ringCatSheaf.obj)).unit.app P).app V w) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 Y'.ringCatSheaf.obj)).unit.app Q).app V w' :=
  (sheafificationMap_app_unit g V w).trans
    (congrArg (((PresheafOfModules.sheafificationAdjunction
      (𝟙 Y'.ringCatSheaf.obj)).unit.app Q).app V) h)

/-- **([NR-pb-unit-nat])** The pullback of a module map, evaluated on a
pullback-adjunction-unit image (the R1 naturality pattern at the scheme-pullback
adjunction; small binders). -/
theorem pullbackMap_app_unit {X' Y' : Scheme.{u}} (f : Y' ⟶ X')
    {P Q : X'.Modules} (q : P ⟶ Q) (V : X'.Opens) (w : P.val.obj (Opposite.op V)) :
    ((Scheme.Modules.pullback f).map q).val.app (Opposite.op (f ⁻¹ᵁ V))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).val.app
          (Opposite.op V) w) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app Q).val.app
        (Opposite.op V) (q.val.app (Opposite.op V) w) := by
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality q
  have happ := congrArg (fun (g : P ⟶
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj Q)) =>
    g.val.app (Opposite.op V) w) hn
  exact happ.symm

/-- **([NR-comp-unit])** The pullback-composition comparison collapses the two-step
adjunction-unit image to the direct one: the value form of the `leftAdjointCompIso`
conjugation triangle. -/
theorem pullbackComp_hom_app_unit {X' Y' Z' : Scheme.{u}} (f : X' ⟶ Y') (g : Y' ⟶ Z')
    (P : Z'.Modules) (V : Z'.Opens) (w : P.val.obj (Opposite.op V)) :
    ((Scheme.Modules.pullbackComp f g).app P).hom.val.app
        (Opposite.op (f ⁻¹ᵁ (g ⁻¹ᵁ V)))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj P)).val.app (Opposite.op (g ⁻¹ᵁ V))
          (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app P).val.app
            (Opposite.op V) w)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app P).val.app
        (Opposite.op V) w := by
  have hu := CategoryTheory.unit_conjugateEquiv
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    ((Scheme.Modules.pullbackComp f g).hom) P
  have happ := congrArg (fun (q : P ⟶
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).obj
        ((Scheme.Modules.pullback (f ≫ g)).obj P)) =>
    q.val.app (Opposite.op V) w) hu
  refine Eq.trans (show _ = (fun (q : P ⟶
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g).obj
        ((Scheme.Modules.pullback (f ≫ g)).obj P)) =>
    q.val.app (Opposite.op V) w)
      ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app P ≫
        (CategoryTheory.conjugateEquiv
          (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
          ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
            (Scheme.Modules.pullbackPushforwardAdjunction f))
          ((Scheme.Modules.pullbackComp f g).hom)).app
          ((Scheme.Modules.pullback (f ≫ g)).obj P)) from happ.symm) ?_
  have hc : (CategoryTheory.conjugateEquiv
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f)))
      (Scheme.Modules.pullbackComp f g).hom =
      (Scheme.Modules.pushforwardComp f g).inv :=
    Equiv.apply_symm_apply _ _
  rw [hc]
  rfl

/-- **([NR-pRT-collapse])** The open-restriction transport on the two-step
adjunction-unit image: `pullbackComp` collapses the units, leaving the
`pullbackCongr` re-index of the composite-unit image (both sides of the slot square
end here symmetrically, so the walk meets at this stage). -/
theorem pullbackRestrictTransport_app_unit {V W : X.Opens} (hWV : W ≤ V)
    (P : X.Modules) (U : X.Opens) (w : P.val.obj (Opposite.op U)) :
    (pullbackRestrictTransport hWV P).val.app
        (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)))
        (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
          ((Scheme.Modules.pullback V.ι).obj P)).val.app (Opposite.op (V.ι ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app P).val.app
            (Opposite.op U) w)) =
      ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app P).inv.val.app
        (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)))
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (X.homOfLE hWV ≫ V.ι)).unit.app P).val.app (Opposite.op U) w) := by
  have hcomp := pullbackComp_hom_app_unit (X.homOfLE hWV) V.ι P U w
  exact congrArg
    (((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app P).inv.val.app
      (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)))) hcomp

/-- **([NR-s1])** The tensor-unit insertion on any section: `tensorObjUnitIso.symm`
reads a section as the sheafification-unit image of its tensor with `1` (small
binders). -/
theorem tensorObjUnitIso_symm_hom_app {Y' : Scheme.{u}} (Q : Y'.Modules)
    (V : (Opens ↥Y')ᵒᵖ) (q : Q.val.obj V) :
    (AlgebraicGeometry.Scheme.Modules.tensorObjUnitIso Q).symm.hom.val.app V q =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 Y'.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj Q.val (unitObj Y').val)).app V
        (q ⊗ₜ (1 : Y'.presheaf.obj V)) := by
  have hsplit : (AlgebraicGeometry.Scheme.Modules.tensorObjUnitIso Q).symm.hom.val.app
      V q =
      ((PresheafOfModules.sheafification (𝟙 Y'.ringCatSheaf.obj)).map
        (MonoidalCategoryStruct.rightUnitor Q.val).inv).val.app V
        ((sheafifyValIso Q).inv.val.app V q) := rfl
  refine hsplit.trans ?_
  refine (congrArg (fun z => ((PresheafOfModules.sheafification
      (𝟙 Y'.ringCatSheaf.obj)).map
      (MonoidalCategoryStruct.rightUnitor Q.val).inv).val.app V z)
    (sheafifyValIso_inv_app_apply Q V.unop q)).trans ?_
  refine (sheafificationMap_app_unit
    (MonoidalCategoryStruct.rightUnitor Q.val).inv V q).trans ?_
  refine congrArg (((PresheafOfModules.sheafificationAdjunction
    (𝟙 Y'.ringCatSheaf.obj)).unit.app
      (MonoidalCategoryStruct.tensorObj Q.val (unitObj Y').val)).app V) ?_
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **([NR-s2])** The generator trivialisation's inverse at the unit section `1`: the
pullback-adjunction-unit image of the restricted generator (up to the
preimage-image re-index). -/
theorem pullbackIdealTrivOfGen_symm_hom_app_one (J : X.IdealSheafData)
    (Wo : X.Opens) (g : Γ(X, Wo)) (hg : g ∈ idealSections J (Opposite.op Wo))
    (hgi : IsIso (idealGenHom J Wo g hg))
    (V : (Opens ↥Wo.toScheme)ᵒᵖ)
    (hpre : (Wo.ι ⁻¹ᵁ (Wo.ι ''ᵁ V.unop)) = V.unop) :
    (pullbackIdealTrivOfGen J Wo g hg hgi).symm.hom.val.app V
        (show Wo.toScheme.presheaf.obj V from 1) =
      ((Scheme.Modules.pullback Wo.ι).obj
          (AlgebraicGeometry.Scheme.Modules.idealModule J)).val.map
        (eqToHom hpre.symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app
          (AlgebraicGeometry.Scheme.Modules.idealModule J)).val.app
          (Opposite.op (Wo.ι ''ᵁ V.unop))
          (⟨X.presheaf.map (homOfLE (Wo.ι_image_le V.unop)).op g,
            idealSections_map J (homOfLE (Wo.ι_image_le V.unop)).op hg⟩)) := by
  have hsplit : (pullbackIdealTrivOfGen J Wo g hg hgi).symm.hom.val.app V
      (show Wo.toScheme.presheaf.obj V from 1) =
      ((restrictFunctorIsoPullback Wo.ι).app
        (AlgebraicGeometry.Scheme.Modules.idealModule J)).hom.val.app V
        ((idealGenHom J Wo g hg).val.app V
          (show Wo.toScheme.presheaf.obj V from 1)) := rfl
  refine hsplit.trans ?_
  have hgen1 : (idealGenHom J Wo g hg).val.app V
      (show Wo.toScheme.presheaf.obj V from 1) =
      ((restrictFunctor Wo.ι).obj
          (AlgebraicGeometry.Scheme.Modules.idealModule J)).val.map
        (eqToHom hpre.symm).op
        (((restrictAdjunction Wo.ι).unit.app
          (AlgebraicGeometry.Scheme.Modules.idealModule J)).val.app
          (Opposite.op (Wo.ι ''ᵁ V.unop)) (⟨X.presheaf.map (homOfLE (Wo.ι_image_le V.unop)).op g,
            idealSections_map J (homOfLE (Wo.ι_image_le V.unop)).op hg⟩)) := by
    refine Subtype.ext ?_
    show X.presheaf.map (homOfLE (Wo.ι_image_le V.unop)).op g *
        (Wo.ι.appIso V.unop).inv (show Wo.toScheme.presheaf.obj V from 1) = _
    rw [map_one, mul_one]
    -- residual: the subtype/restrict-layer value collapse (idealPresheaf-map .1 +
    -- unit_app_app + eqToHom-res fusion); outer rfl FAILS (one layer blocks);
    -- restrictAdjunction_unit_app_app is rfl (mathlib :442); the .app-sugar is
    -- forget₂-wrapped .val.app, bridged by the typed have
    have hu : ((restrictAdjunction Wo.ι).unit.app
        (AlgebraicGeometry.Scheme.Modules.idealModule J)).val.app
        (Opposite.op (Wo.ι ''ᵁ V.unop))
        (⟨X.presheaf.map (homOfLE (Wo.ι_image_le V.unop)).op g,
          idealSections_map J (homOfLE (Wo.ι_image_le V.unop)).op hg⟩) =
        (AlgebraicGeometry.Scheme.Modules.idealModule J).val.map
          (homOfLE (Scheme.Hom.image_preimage_le Wo.ι (Wo.ι ''ᵁ V.unop))).op
          (⟨X.presheaf.map (homOfLE (Wo.ι_image_le V.unop)).op g,
            idealSections_map J (homOfLE (Wo.ι_image_le V.unop)).op hg⟩) :=
      ConcreteCategory.congr_hom (restrictAdjunction_unit_app_app Wo.ι
        (AlgebraicGeometry.Scheme.Modules.idealModule J) (Wo.ι ''ᵁ V.unop)) _
    rw [hu]
    -- swap the single arrow for the composite path, then split twice; the aligned
    -- coe-unwinding then closes by rfl
    refine Eq.trans (congrArg (fun (σ : (Wo.ι ''ᵁ V.unop) ⟶ Wo) =>
      X.presheaf.map σ.op g) (Subsingleton.elim _
        ((Wo.ι.opensFunctor.map (eqToHom hpre.symm)) ≫
          (homOfLE (Scheme.Hom.image_preimage_le Wo.ι (Wo.ι ''ᵁ V.unop)) ≫
            homOfLE (Wo.ι_image_le V.unop))))) ?_
    refine Eq.trans (ConcreteCategory.congr_hom (X.presheaf.map_comp
      ((homOfLE (Scheme.Hom.image_preimage_le Wo.ι (Wo.ι ''ᵁ V.unop)) ≫
        homOfLE (Wo.ι_image_le V.unop))).op
      ((Wo.ι.opensFunctor.map (eqToHom hpre.symm))).op) g) ?_
    refine Eq.trans (congrArg (fun t => X.presheaf.map
      ((Wo.ι.opensFunctor.map (eqToHom hpre.symm))).op t)
      (ConcreteCategory.congr_hom
        (X.presheaf.map_comp (homOfLE (Wo.ι_image_le V.unop)).op
          (homOfLE (Scheme.Hom.image_preimage_le Wo.ι (Wo.ι ''ᵁ V.unop))).op) g)) ?_
    rfl
  refine (congrArg (((restrictFunctorIsoPullback Wo.ι).app
    (AlgebraicGeometry.Scheme.Modules.idealModule J)).hom.val.app V) hgen1).trans ?_
  have hnat := PresheafOfModules.naturality_apply
    ((restrictFunctorIsoPullback Wo.ι).app
      (AlgebraicGeometry.Scheme.Modules.idealModule J)).hom.val
    (eqToHom hpre.symm).op
    (((restrictAdjunction Wo.ι).unit.app
      (AlgebraicGeometry.Scheme.Modules.idealModule J)).val.app
      (Opposite.op (Wo.ι ''ᵁ V.unop)) (⟨X.presheaf.map (homOfLE (Wo.ι_image_le V.unop)).op g,
            idealSections_map J (homOfLE (Wo.ι_image_le V.unop)).op hg⟩))
  refine hnat.trans ?_
  exact congrArg (fun z =>
    ((Scheme.Modules.pullback Wo.ι).obj
        (AlgebraicGeometry.Scheme.Modules.idealModule J)).val.map
      (eqToHom hpre.symm).op z)
    (restrictFunctorIsoPullback_hom_unit_app_apply Wo.ι
      (AlgebraicGeometry.Scheme.Modules.idealModule J) (Wo.ι ''ᵁ V.unop)
      (⟨X.presheaf.map (homOfLE (Wo.ι_image_le V.unop)).op g,
        idealSections_map J (homOfLE (Wo.ι_image_le V.unop)).op hg⟩))

/-- **([NR-congr-unit])** `pullbackCongr` on an adjunction-unit image: for equal
morphisms the congruence re-index carries the `g`-unit image to the `f`-unit image
(proved by `subst`; the instantiation at `homOfLE_ι` supplies the propositional
crossing of the slot-square walk). -/
theorem pullbackCongr_app_inv_app_unit {X' Y' : Scheme.{u}} {f g : Y' ⟶ X'}
    (h : f = g) (P : X'.Modules) (U : X'.Opens) (w : P.val.obj (Opposite.op U)) :
    ((Scheme.Modules.pullbackCongr h).app P).inv.val.app
        (Opposite.op (f ⁻¹ᵁ U))
        ((show ((Scheme.Modules.pullback g).obj P).val.obj
            (Opposite.op (f ⁻¹ᵁ U)) from by
          rw [h]
          exact ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app P).val.app
            (Opposite.op U) w)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).val.app
        (Opposite.op U) w := by
  subst h
  rfl

/-- **([NR-unit-res])** The pullback-adjunction unit image restricts along preimages:
the unit naturality at a restriction arrow, in value form (small binders). -/
theorem pullbackUnit_app_res {X' Y' : Scheme.{u}} (f : Y' ⟶ X') (P : X'.Modules)
    {U U' : X'.Opens} (hle : U' ≤ U) (m : P.val.obj (Opposite.op U)) :
    ((Scheme.Modules.pullback f).obj P).val.map
        (homOfLE (by exact fun x hx => hle hx : f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ U)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).val.app
          (Opposite.op U) m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).val.app
        (Opposite.op U') (P.val.map (homOfLE hle).op m) := by
  have hnat := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).val
    (homOfLE hle).op m
  exact hnat.symm

/-- **([NR-congr-unit-tmul])** `tensorObjCongr` on a sheafification-unit image of a
pure tensor (small binders: the instantiation at the large pullback objects is by term
application). -/
theorem tensorObjCongr_hom_app_unit_tmul {Y' : Scheme.{u}}
    {M M' N N' : Y'.Modules} (eM : M ≅ M') (eN : N ≅ N')
    (V : (Opens ↥Y')ᵒᵖ) (a : M.val.obj V) (b : N.val.obj V) :
    (tensorObjCongr eM eN).hom.val.app V
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y'.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj M.val N.val)).app V (a ⊗ₜ b)) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 Y'.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj M'.val N'.val)).app V
        ((eM.hom.val.app V a) ⊗ₜ (eN.hom.val.app V b)) := by
  refine (sheafificationMap_app_unit
    (MonoidalCategoryStruct.tensorHom
      ((SheafOfModules.forget Y'.ringCatSheaf).map eM.hom)
      ((SheafOfModules.forget Y'.ringCatSheaf).map eN.hom)) V (a ⊗ₜ b)).trans ?_
  refine congrArg (((PresheafOfModules.sheafificationAdjunction
    (𝟙 Y'.ringCatSheaf.obj)).unit.app
      (MonoidalCategoryStruct.tensorObj M'.val N'.val)).app V) ?_
  exact PresheafOfModules.tensorHom_app_tmul (T := Y'.sheaf.obj)
    (g₁ := (SheafOfModules.forget Y'.ringCatSheaf).map eM.hom)
    (g₂ := (SheafOfModules.forget Y'.ringCatSheaf).map eN.hom) V a b

/-- **([NR-iso-inv-app])** Inverse evaluation from a forward evaluation (small binders;
the `hL3`-style inverse reads instantiate this by term application). -/
theorem iso_inv_app_of_hom_app {Y' : Scheme.{u}} {A' B' : Y'.Modules} (e : A' ≅ B')
    (V : (Opens ↥Y')ᵒᵖ) {w : A'.val.obj V} {z : B'.val.obj V}
    (h : e.hom.val.app V w = z) :
    e.inv.val.app V z = w :=
  (congrArg (fun t => e.inv.val.app V t) h.symm).trans
    (iso_hom_inv_app_applyT e V w)

section MuBridgePieces

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
variable (A B : X.Modules)

private theorem mu_bridge_rhs (U : (Opens ↥X)ᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y
    letI : (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
    (((Scheme.Modules.pullback f).mapIso
            (monoidalTensorObjIso A B).symm ≪≫
          (Functor.Monoidal.μIso (Scheme.Modules.pullback f) A B).symm ≪≫
          monoidalTensorObjIso ((Scheme.Modules.pullback f).obj A)
            ((Scheme.Modules.pullback f).obj B)).hom.val.app
          (Opposite.op (f ⁻¹ᵁ U.unop))
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            (tensorObj A B)).val.app U
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 X.ringCatSheaf.obj)).unit.app
                (MonoidalCategoryStruct.tensorObj A.val B.val)).app U
              (x ⊗ₜ y)))) =
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 Y.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj
                ((Scheme.Modules.pullback f).obj A).val
                ((Scheme.Modules.pullback f).obj B).val)).app
            (Opposite.op (f ⁻¹ᵁ U.unop))
            ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
              (Opposite.op U.unop) x) ⊗ₜ
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
                (Opposite.op U.unop) y)) := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  letI : (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
  have hR1 : ((Scheme.Modules.pullback f).map
      (monoidalTensorObjIso A B).inv).val.app
      (Opposite.op (f ⁻¹ᵁ U.unop))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (tensorObj A B)).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj A.val B.val)).app U
          (x ⊗ₜ y))) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (MonoidalCategoryStruct.tensorObj A B)).val.app
        (Opposite.op U.unop)
        (tensorSection A B U.unop x y) := by
    have hnat := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality
      (monoidalTensorObjIso A B).inv
    have happ := congrArg (fun (q : tensorObj A B ⟶
        (Scheme.Modules.pushforward f).obj
          ((Scheme.Modules.pullback f).obj
            (MonoidalCategoryStruct.tensorObj A B))) =>
      q.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj A.val B.val)).app U
          (x ⊗ₜ y))) hnat
    exact happ.symm
  have hR2 := ModularCurves.pullback_δ_unit_tensorSection f A B U.unop x y
  -- [R3] the target-side bridge cancels on the pure tensor
  have hR3 : (monoidalTensorObjIso ((Scheme.Modules.pullback f).obj A)
      ((Scheme.Modules.pullback f).obj B)).hom.val.app
      (Opposite.op (f ⁻¹ᵁ U.unop))
      (tensorSection ((Scheme.Modules.pullback f).obj A)
        ((Scheme.Modules.pullback f).obj B) (f ⁻¹ᵁ U.unop)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
          (Opposite.op U.unop) x)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
          (Opposite.op U.unop) y)) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 Y.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj
            ((Scheme.Modules.pullback f).obj A).val
            ((Scheme.Modules.pullback f).obj B).val)).app
        (Opposite.op (f ⁻¹ᵁ U.unop))
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
          (Opposite.op U.unop) x) ⊗ₜ
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
            (Opposite.op U.unop) y)) :=
    iso_inv_hom_app_applyT (monoidalTensorObjIso _ _) _ _
  -- assemble the μ-side value
  have hRHS : (((Scheme.Modules.pullback f).mapIso
            (monoidalTensorObjIso A B).symm ≪≫
          (Functor.Monoidal.μIso (Scheme.Modules.pullback f) A B).symm ≪≫
          monoidalTensorObjIso ((Scheme.Modules.pullback f).obj A)
            ((Scheme.Modules.pullback f).obj B)).hom.val.app
          (Opposite.op (f ⁻¹ᵁ U.unop))
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            (tensorObj A B)).val.app U
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 X.ringCatSheaf.obj)).unit.app
                (MonoidalCategoryStruct.tensorObj A.val B.val)).app U
              (x ⊗ₜ y)))) =
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 Y.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj
                ((Scheme.Modules.pullback f).obj A).val
                ((Scheme.Modules.pullback f).obj B).val)).app
            (Opposite.op (f ⁻¹ᵁ U.unop))
            ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
              (Opposite.op U.unop) x) ⊗ₜ
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
                (Opposite.op U.unop) y)) := by

      have hsplit : (((Scheme.Modules.pullback f).mapIso
            (monoidalTensorObjIso A B).symm ≪≫
          (Functor.Monoidal.μIso (Scheme.Modules.pullback f) A B).symm ≪≫
          monoidalTensorObjIso ((Scheme.Modules.pullback f).obj A)
            ((Scheme.Modules.pullback f).obj B)).hom.val.app
          (Opposite.op (f ⁻¹ᵁ U.unop))
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            (tensorObj A B)).val.app U
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 X.ringCatSheaf.obj)).unit.app
                (MonoidalCategoryStruct.tensorObj A.val B.val)).app U
              (x ⊗ₜ y)))) =
          (monoidalTensorObjIso ((Scheme.Modules.pullback f).obj A)
            ((Scheme.Modules.pullback f).obj B)).hom.val.app
            (Opposite.op (f ⁻¹ᵁ U.unop))
            ((Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A B).val.app
              (Opposite.op (f ⁻¹ᵁ U.unop))
              (((Scheme.Modules.pullback f).map
                (monoidalTensorObjIso A B).inv).val.app
                (Opposite.op (f ⁻¹ᵁ U.unop))
                (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
                  (tensorObj A B)).val.app U
                  (((PresheafOfModules.sheafificationAdjunction
                    (𝟙 X.ringCatSheaf.obj)).unit.app
                      (MonoidalCategoryStruct.tensorObj A.val B.val)).app U
                    (x ⊗ₜ y))))) := rfl
      rw [hsplit, hR1, hR2, hR3]
  exact hRHS

private theorem mu_bridge_lhs_e4 (U : (Opens ↥X)ᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y
    haveI : IsIso ((PresheafOfModules.sheafification
        (𝟙 Y.ringCatSheaf.obj)).map
        ((PresheafOfModules.pushforward (restrictRingHom f)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj A.val B.val)))) := by
      have hmem := sheafificationW_pushforward_unit_tensor f A B
      rw [PresheafOfModules.sheafificationW_iff] at hmem
      exact hmem
    ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map (PresheafOfModules.pushforwardTensorIso (restrictRingHom f) A.val B.val).inv).val.app (Opposite.op (f ⁻¹ᵁ U.unop))
      ((asIso ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map ((PresheafOfModules.pushforward (restrictRingHom f)).map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj A.val B.val))))).inv.val.app (Opposite.op (f ⁻¹ᵁ U.unop))
        ((sheafifyValIso ((restrictFunctor f).obj (tensorObj A B))).inv.val.app (Opposite.op (f ⁻¹ᵁ U.unop))
          (((restrictFunctorIsoPullback f).symm.app (tensorObj A B)).hom.val.app (Opposite.op (f ⁻¹ᵁ U.unop))
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
              (tensorObj A B)).val.app U (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj A.val B.val)).app U (x ⊗ₜ y)))))) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj
        ((PresheafOfModules.pushforward (restrictRingHom f)).obj A.val) ((PresheafOfModules.pushforward (restrictRingHom f)).obj B.val))).app (Opposite.op (f ⁻¹ᵁ U.unop))
        ((PresheafOfModules.pushforwardTensorIso (restrictRingHom f)
          A.val B.val).inv.app (Opposite.op (f ⁻¹ᵁ U.unop)) ((A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y))) := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  have hL1 := restrictFunctorIsoPullback_inv_unit_app_apply f (tensorObj A B)
    U.unop
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app
        (MonoidalCategoryStruct.tensorObj A.val B.val)).app U (x ⊗ₜ y))
  -- [L2] un-sheafify on the Y-side
  have hL2 := sheafifyValIso_inv_app_apply
    ((restrictFunctor f).obj (tensorObj A B)) (f ⁻¹ᵁ U.unop)
    (((restrictAdjunction f).unit.app (tensorObj A B)).val.app
      (Opposite.op U.unop)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj A.val B.val)).app U (x ⊗ₜ y)))
  -- [Lres] the restrict-unit value is the sheafification-unit image of the
  -- restricted pure tensor
  have hres : ((restrictAdjunction f).unit.app (tensorObj A B)).val.app
      (Opposite.op U.unop)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj A.val B.val)).app U (x ⊗ₜ y)) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj A.val B.val)).app
        (Opposite.op (f ''ᵁ (f ⁻¹ᵁ U.unop)))
        ((A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ
          (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y)) := by
    have hunit : ((restrictAdjunction f).unit.app (tensorObj A B)).val.app
        (Opposite.op U.unop)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj A.val B.val)).app U (x ⊗ₜ y)) =
        (tensorObj A B).val.map
          (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj A.val B.val)).app U
            (x ⊗ₜ y)) := rfl
    have hnat' : (tensorObj A B).val.map
        (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj A.val B.val)).app U
          (x ⊗ₜ y)) =
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj A.val B.val)).app
          (Opposite.op (f ''ᵁ (f ⁻¹ᵁ U.unop)))
          ((MonoidalCategoryStruct.tensorObj A.val B.val).map
            (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op
            (x ⊗ₜ y)) :=
      (PresheafOfModules.naturality_apply
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj A.val B.val))
        (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op (x ⊗ₜ y)).symm
    have htm' : (MonoidalCategoryStruct.tensorObj A.val B.val).map
        (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op (x ⊗ₜ y) =
        (A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ
          (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y) :=
      PresheafOfModules.Monoidal.tensorObj_map_tmul _ x y
    exact hunit.trans (hnat'.trans (congrArg
      (fun z => ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj A.val B.val)).app
        (Opposite.op (f ''ᵁ (f ⁻¹ᵁ U.unop))) z) htm'))
  -- [L3-fwd] the collapsed sheafification map on the Y-unit image of the
  -- restricted pure tensor (the R1 naturality pattern)
  have hfwd : ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
      ((PresheafOfModules.pushforward (restrictRingHom f)).map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj A.val B.val)))).val.app (Opposite.op (f ⁻¹ᵁ U.unop))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app ((PresheafOfModules.pushforward (restrictRingHom f)).obj (MonoidalCategoryStruct.tensorObj A.val B.val))).app (Opposite.op (f ⁻¹ᵁ U.unop)) ((A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y))) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app ((PresheafOfModules.pushforward (restrictRingHom f)).obj
        ((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj) ⋙ SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
            (MonoidalCategoryStruct.tensorObj A.val B.val)))).app (Opposite.op (f ⁻¹ᵁ U.unop))
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj A.val B.val)).app (Opposite.op (f ''ᵁ (f ⁻¹ᵁ U.unop))) ((A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y))) := by
    exact sheafificationMap_app_unit
      ((PresheafOfModules.pushforward (restrictRingHom f)).map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj A.val B.val))) (Opposite.op (f ⁻¹ᵁ U.unop)) ((A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y))
  haveI hWiso : IsIso ((PresheafOfModules.sheafification
      (𝟙 Y.ringCatSheaf.obj)).map
      ((PresheafOfModules.pushforward (restrictRingHom f)).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj A.val B.val)))) := by
    have hmem := sheafificationW_pushforward_unit_tensor f A B
    rw [PresheafOfModules.sheafificationW_iff] at hmem
    exact hmem
  -- [L3] the inverse of the collapsed sheafification map, evaluated
  have hL3 : (asIso ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
      ((PresheafOfModules.pushforward (restrictRingHom f)).map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj A.val B.val))))).inv.val.app (Opposite.op (f ⁻¹ᵁ U.unop))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app ((PresheafOfModules.pushforward (restrictRingHom f)).obj
        ((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj) ⋙ SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
            (MonoidalCategoryStruct.tensorObj A.val B.val)))).app (Opposite.op (f ⁻¹ᵁ U.unop))
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj A.val B.val)).app (Opposite.op (f ''ᵁ (f ⁻¹ᵁ U.unop))) ((A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y)))) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app ((PresheafOfModules.pushforward (restrictRingHom f)).obj (MonoidalCategoryStruct.tensorObj A.val B.val))).app (Opposite.op (f ⁻¹ᵁ U.unop)) ((A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y)) := by
    exact iso_inv_app_of_hom_app _ (Opposite.op (f ⁻¹ᵁ U.unop)) hfwd
  -- [L4] the pushforward tensor comparison on the Y-unit image
  have hL4 : ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
      (PresheafOfModules.pushforwardTensorIso (restrictRingHom f)
        A.val B.val).inv).val.app (Opposite.op (f ⁻¹ᵁ U.unop))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app ((PresheafOfModules.pushforward (restrictRingHom f)).obj (MonoidalCategoryStruct.tensorObj A.val B.val))).app (Opposite.op (f ⁻¹ᵁ U.unop)) ((A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y))) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj
        ((PresheafOfModules.pushforward (restrictRingHom f)).obj A.val) ((PresheafOfModules.pushforward (restrictRingHom f)).obj B.val))).app (Opposite.op (f ⁻¹ᵁ U.unop))
        ((PresheafOfModules.pushforwardTensorIso (restrictRingHom f)
          A.val B.val).inv.app (Opposite.op (f ⁻¹ᵁ U.unop)) ((A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y))) := by
    exact sheafificationMap_app_unit
      ((PresheafOfModules.pushforwardTensorIso (restrictRingHom f)
        A.val B.val).inv) (Opposite.op (f ⁻¹ᵁ U.unop)) ((A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y))
  -- [L4b] the pushforward tensor comparison is the identity on pure tensors
  have hL4b : (PresheafOfModules.pushforwardTensorIso (restrictRingHom f)
      A.val B.val).inv.app (Opposite.op (f ⁻¹ᵁ U.unop)) ((A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y)) =
      ((show ((PresheafOfModules.pushforward (restrictRingHom f)).obj A.val).obj (Opposite.op (f ⁻¹ᵁ U.unop)) from A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ
        (show ((PresheafOfModules.pushforward (restrictRingHom f)).obj B.val).obj (Opposite.op (f ⁻¹ᵁ U.unop)) from B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y)) := by
    rfl
  -- [L5] the final congruence piece: restrict-to-pullback on each tensor factor
  have hL5 : (tensorObjCongr ((restrictFunctorIsoPullback f).app A)
      ((restrictFunctorIsoPullback f).app B)).hom.val.app (Opposite.op (f ⁻¹ᵁ U.unop))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj
        ((restrictFunctor f).obj A).val ((restrictFunctor f).obj B).val)).app (Opposite.op (f ⁻¹ᵁ U.unop)) ((show ((restrictFunctor f).obj A).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ
        (show ((restrictFunctor f).obj B).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y))) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj
        ((Scheme.Modules.pullback f).obj A).val
        ((Scheme.Modules.pullback f).obj B).val)).app (Opposite.op (f ⁻¹ᵁ U.unop))
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
          (Opposite.op U.unop) x) ⊗ₜ
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
            (Opposite.op U.unop) y)) := by
    have hfac₁ : ((restrictFunctorIsoPullback f).app A).hom.val.app (Opposite.op (f ⁻¹ᵁ U.unop))
        (show ((restrictFunctor f).obj A).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from
          A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) =
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
          (Opposite.op U.unop) x :=
      restrictFunctorIsoPullback_hom_unit_app_apply f A U.unop x
    have hfac₂ : ((restrictFunctorIsoPullback f).app B).hom.val.app (Opposite.op (f ⁻¹ᵁ U.unop))
        (show ((restrictFunctor f).obj B).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from
          B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y) =
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
          (Opposite.op U.unop) y :=
      restrictFunctorIsoPullback_hom_unit_app_apply f B U.unop y
    refine (tensorObjCongr_hom_app_unit_tmul
      ((restrictFunctorIsoPullback f).app A)
      ((restrictFunctorIsoPullback f).app B) (Opposite.op (f ⁻¹ᵁ U.unop))
      (show ((restrictFunctor f).obj A).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x)
      (show ((restrictFunctor f).obj B).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y)).trans ?_
    refine congrArg (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj
      ((Scheme.Modules.pullback f).obj A).val
      ((Scheme.Modules.pullback f).obj B).val)).app (Opposite.op (f ⁻¹ᵁ U.unop))) ?_
    exact congrArg₂ (fun a b => a ⊗ₜ b) hfac₁ hfac₂
  -- assembly: split the composite application and chain the six values
  have hstep₂ := congrArg
    (fun z => (sheafifyValIso
      ((restrictFunctor f).obj (tensorObj A B))).inv.val.app (Opposite.op (f ⁻¹ᵁ U.unop)) z) hL1
  have hstep₂' := hstep₂.trans hL2
  have hstep₂'' := hstep₂'.trans (congrArg
    (fun z => ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj) ⋙ SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj) ⋙
      PresheafOfModules.pushforward (restrictRingHom f)).obj (MonoidalCategoryStruct.tensorObj A.val B.val))).app
      (Opposite.op (f ⁻¹ᵁ U.unop)) z) hres)
  have hstep₃ := (congrArg (fun z => (asIso ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map ((PresheafOfModules.pushforward (restrictRingHom f)).map ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj A.val B.val))))).inv.val.app (Opposite.op (f ⁻¹ᵁ U.unop)) z) hstep₂'').trans hL3
  have hstep₄ := (congrArg (fun z => ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map (PresheafOfModules.pushforwardTensorIso (restrictRingHom f) A.val B.val).inv).val.app (Opposite.op (f ⁻¹ᵁ U.unop)) z) hstep₃).trans hL4
  exact hstep₄

private theorem mu_bridge_l4b (U : (Opens ↥X)ᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) :
    (PresheafOfModules.pushforwardTensorIso (restrictRingHom f)
          A.val B.val).inv.app (Opposite.op (f ⁻¹ᵁ U.unop)) ((A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ (B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y)) =
          ((show ((PresheafOfModules.pushforward (restrictRingHom f)).obj A.val).obj (Opposite.op (f ⁻¹ᵁ U.unop)) from A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ
            (show ((PresheafOfModules.pushforward (restrictRingHom f)).obj B.val).obj (Opposite.op (f ⁻¹ᵁ U.unop)) from B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y)) := by

  rfl

private theorem mu_bridge_l5 (U : (Opens ↥X)ᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y
    (tensorObjCongr ((restrictFunctorIsoPullback f).app A)
          ((restrictFunctorIsoPullback f).app B)).hom.val.app (Opposite.op (f ⁻¹ᵁ U.unop))
          (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj
            ((restrictFunctor f).obj A).val ((restrictFunctor f).obj B).val)).app (Opposite.op (f ⁻¹ᵁ U.unop)) ((show ((restrictFunctor f).obj A).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ
            (show ((restrictFunctor f).obj B).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y))) =
          ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj
            ((Scheme.Modules.pullback f).obj A).val
            ((Scheme.Modules.pullback f).obj B).val)).app (Opposite.op (f ⁻¹ᵁ U.unop))
            ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
              (Opposite.op U.unop) x) ⊗ₜ
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
                (Opposite.op U.unop) y)) := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y

  have hfac₁ : ((restrictFunctorIsoPullback f).app A).hom.val.app (Opposite.op (f ⁻¹ᵁ U.unop))
      (show ((restrictFunctor f).obj A).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from
        A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
        (Opposite.op U.unop) x :=
    restrictFunctorIsoPullback_hom_unit_app_apply f A U.unop x
  have hfac₂ : ((restrictFunctorIsoPullback f).app B).hom.val.app (Opposite.op (f ⁻¹ᵁ U.unop))
      (show ((restrictFunctor f).obj B).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from
        B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
        (Opposite.op U.unop) y :=
    restrictFunctorIsoPullback_hom_unit_app_apply f B U.unop y
  refine (tensorObjCongr_hom_app_unit_tmul
    ((restrictFunctorIsoPullback f).app A)
    ((restrictFunctorIsoPullback f).app B) (Opposite.op (f ⁻¹ᵁ U.unop))
    (show ((restrictFunctor f).obj A).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x)
    (show ((restrictFunctor f).obj B).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y)).trans ?_
  refine congrArg (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj
    ((Scheme.Modules.pullback f).obj A).val
    ((Scheme.Modules.pullback f).obj B).val)).app (Opposite.op (f ⁻¹ᵁ U.unop))) ?_
  exact congrArg₂ (fun a b => a ⊗ₜ b) hfac₁ hfac₂
-- assembly: split the composite application and chain the six values

end MuBridgePieces

/-- **([μ-BRIDGE], statement)** The ad-hoc open-immersion tensor comparison is the
monoidal `μ` conjugated by the definite `tensorObj`-vs-`⊗` bridges. With it, every
transport square of the slot construction reduces to the `Functor.Monoidal` API and
`pullbackComp_hom_isMonoidal`. Proof route (cont.25b): compare on
adjunction-unit/`tensorSection` elements via the `PullbackTensorSection` formula
library, then sheafification-adjunction hom-ext. -/
theorem pullbackTensorObjIsoOfIsOpenImmersion_eq_mu {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (A B : X.Modules) :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y
    letI : (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
    pullbackTensorObjIsoOfIsOpenImmersion f A B =
      (Scheme.Modules.pullback f).mapIso (monoidalTensorObjIso A B).symm ≪≫
        (Functor.Monoidal.μIso (Scheme.Modules.pullback f) A B).symm ≪≫
        monoidalTensorObjIso ((Scheme.Modules.pullback f).obj A)
          ((Scheme.Modules.pullback f).obj B) := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y
  letI : (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
  apply Iso.ext
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x y =>
      rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply,
        Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
      have hcollapse : ∀ (T : Y.Modules) (g : (Scheme.Modules.pullback f).obj
          (tensorObj A B) ⟶ T),
          (ModuleCat.Hom.hom
            (((PresheafOfModules.sheafificationAdjunction
                (𝟙 X.ringCatSheaf.obj)).unit.app
                  (MonoidalCategoryStruct.tensorObj A.val B.val) ≫
                (SheafOfModules.forget X.ringCatSheaf ⋙
                  PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
                  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
                    (tensorObj A B) ≫
                    (Scheme.Modules.pushforward f).map g)).app U))
            (x ⊗ₜ y) =
          g.val.app (Opposite.op (f ⁻¹ᵁ U.unop))
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
              (tensorObj A B)).val.app U
              (((PresheafOfModules.sheafificationAdjunction
                (𝟙 X.ringCatSheaf.obj)).unit.app
                  (MonoidalCategoryStruct.tensorObj A.val B.val)).app U
                (x ⊗ₜ y))) := fun T g => rfl
      refine (hcollapse _ _).trans (Eq.trans ?_ (hcollapse _ _).symm)
      -- [R1] the pulled tensorObj-bridge on the double-unit image (adjUnit naturality;
      -- the `pullback_monoidalTensorObjIso_inv_unit` argument, inlined)
      have hRHS := mu_bridge_rhs f A B U x y
      refine Eq.trans ?_ hRHS.symm
      -- the open-immersion comparison, unfolded and walked on the double-unit image
      simp only [pullbackTensorObjIsoOfIsOpenImmersion, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_inv, Iso.refl_hom]
      -- [L1] the restrict-side reading of the double-unit image
      have hstep₄ := mu_bridge_lhs_e4 f A B U x y
      have hstep₄' := hstep₄.trans (congrArg
        (fun z => ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj
          ((PresheafOfModules.pushforward (restrictRingHom f)).obj A.val) ((PresheafOfModules.pushforward (restrictRingHom f)).obj B.val))).app (Opposite.op (f ⁻¹ᵁ U.unop)) z)
        (mu_bridge_l4b f A B U x y))
      have hcross : ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj
          ((PresheafOfModules.pushforward (restrictRingHom f)).obj A.val) ((PresheafOfModules.pushforward (restrictRingHom f)).obj B.val))).app (Opposite.op (f ⁻¹ᵁ U.unop))
          ((show ((PresheafOfModules.pushforward (restrictRingHom f)).obj A.val).obj (Opposite.op (f ⁻¹ᵁ U.unop)) from A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ
            (show ((PresheafOfModules.pushforward (restrictRingHom f)).obj B.val).obj (Opposite.op (f ⁻¹ᵁ U.unop)) from B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y)) =
          ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app (MonoidalCategoryStruct.tensorObj
            ((restrictFunctor f).obj A).val ((restrictFunctor f).obj B).val)).app
            (Opposite.op (f ⁻¹ᵁ U.unop))
            ((show ((restrictFunctor f).obj A).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from
              A.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op x) ⊗ₜ
              (show ((restrictFunctor f).obj B).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) from
                B.val.map (homOfLE (Scheme.Hom.image_preimage_le f U.unop)).op y)) := rfl
      have hstep₅ := (congrArg
        (fun z => (tensorObjCongr ((restrictFunctorIsoPullback f).app A)
          ((restrictFunctorIsoPullback f).app B)).hom.val.app (Opposite.op (f ⁻¹ᵁ U.unop)) z)
        (hstep₄'.trans hcross)).trans (mu_bridge_l5 f A B U x y)
      exact hstep₅
  | add s t hs ht =>
      simp only [map_add, hs, ht]

/-- **([NR-s3])** The open-immersion tensor comparison's inverse on the
sheafification-unit image of a pure tensor of pullback-unit sections: it is the
pullback-unit image of the `X`-side pure tensor. Consequence of the proven
`pullbackTensorObjIsoOfIsOpenImmersion_eq_mu` and the `μ`/`tensorSection` calculus. -/
theorem pullbackTensorObjIsoOfIsOpenImmersion_symm_hom_app_unit
    {Y' : Scheme.{u}} (f : Y' ⟶ X) [IsOpenImmersion f] (A B : X.Modules)
    (U : X.Opens) (x : A.val.obj (Opposite.op U)) (y : B.val.obj (Opposite.op U)) :
    letI := Scheme.Modules.monoidalCategory X
    letI := Scheme.Modules.monoidalCategory Y'
    letI : (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
    (pullbackTensorObjIsoOfIsOpenImmersion f A B).symm.hom.val.app
        (Opposite.op (f ⁻¹ᵁ U))
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y'.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj
              ((Scheme.Modules.pullback f).obj A).val
              ((Scheme.Modules.pullback f).obj B).val)).app
          (Opposite.op (f ⁻¹ᵁ U))
          ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
            (Opposite.op U) x) ⊗ₜ
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
              (Opposite.op U) y))) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (tensorObj A B)).val.app (Opposite.op U)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj A.val B.val)).app
          (Opposite.op U) (x ⊗ₜ y)) := by
  letI := Scheme.Modules.monoidalCategory X
  letI := Scheme.Modules.monoidalCategory Y'
  letI : (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
  have hmu := congrArg (fun (e : (Scheme.Modules.pullback f).obj (tensorObj A B) ≅
      tensorObj ((Scheme.Modules.pullback f).obj A)
        ((Scheme.Modules.pullback f).obj B)) => e.symm.hom.val.app
      (Opposite.op (f ⁻¹ᵁ U)))
    (pullbackTensorObjIsoOfIsOpenImmersion_eq_mu f A B)
  refine (congrArg (fun q => (ConcreteCategory.hom q)
    (((PresheafOfModules.sheafificationAdjunction
          (𝟙 Y'.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj
              ((Scheme.Modules.pullback f).obj A).val
              ((Scheme.Modules.pullback f).obj B).val)).app
          (Opposite.op (f ⁻¹ᵁ U))
          ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
            (Opposite.op U) x) ⊗ₜ
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
              (Opposite.op U) y)))) hmu).trans ?_
  -- the composite `.symm.hom` splits as mTOI.inv ≫ μ ≫ pb.map mTOI.hom
  have hv1 : (monoidalTensorObjIso ((Scheme.Modules.pullback f).obj A)
      ((Scheme.Modules.pullback f).obj B)).inv.val.app (Opposite.op (f ⁻¹ᵁ U))
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 Y'.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj
            ((Scheme.Modules.pullback f).obj A).val
            ((Scheme.Modules.pullback f).obj B).val)).app
        (Opposite.op (f ⁻¹ᵁ U))
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
          (Opposite.op U) x) ⊗ₜ
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
            (Opposite.op U) y))) =
      tensorSection ((Scheme.Modules.pullback f).obj A)
        ((Scheme.Modules.pullback f).obj B) (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
          (Opposite.op U) x)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
          (Opposite.op U) y) := rfl
  have hδ := ModularCurves.pullback_δ_unit_tensorSection f A B U x y
  have hv2 : (Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) A B).val.app
      (Opposite.op (f ⁻¹ᵁ U)) (tensorSection ((Scheme.Modules.pullback f).obj A)
        ((Scheme.Modules.pullback f).obj B) (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
          (Opposite.op U) x)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
          (Opposite.op U) y)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (MonoidalCategoryStruct.tensorObj A B)).val.app (Opposite.op U) (tensorSection A B U x y) := by
    have hdm := congrArg (fun (q : (Scheme.Modules.pullback f).obj
        (MonoidalCategoryStruct.tensorObj A B) ⟶ (Scheme.Modules.pullback f).obj
        (MonoidalCategoryStruct.tensorObj A B)) =>
      q.val.app (Opposite.op (f ⁻¹ᵁ U)) (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (MonoidalCategoryStruct.tensorObj A B)).val.app (Opposite.op U) (tensorSection A B U x y)))
      (Functor.Monoidal.δ_μ (Scheme.Modules.pullback f) A B)
    have hsplit : (Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) A B).val.app
        (Opposite.op (f ⁻¹ᵁ U))
        ((Functor.OplaxMonoidal.δ (Scheme.Modules.pullback f) A B).val.app
          (Opposite.op (f ⁻¹ᵁ U)) (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (MonoidalCategoryStruct.tensorObj A B)).val.app (Opposite.op U) (tensorSection A B U x y))) =
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (MonoidalCategoryStruct.tensorObj A B)).val.app (Opposite.op U) (tensorSection A B U x y) := hdm
    rw [hδ] at hsplit
    exact hsplit
  -- v3: transport back through the pulled tensorObj-bridge
  have hv3 := pullbackMap_app_unit f (monoidalTensorObjIso A B).hom U (tensorSection A B U x y)
  have hcancel : (monoidalTensorObjIso A B).hom.val.app (Opposite.op U) (tensorSection A B U x y) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj A.val B.val)).app
        (Opposite.op U) (x ⊗ₜ y) :=
    iso_inv_hom_app_applyT (monoidalTensorObjIso A B) (Opposite.op U) _
  -- assemble the three steps against the composite
  have hcomp : (((Scheme.Modules.pullback f).mapIso (monoidalTensorObjIso A B).symm ≪≫
      (Functor.Monoidal.μIso (Scheme.Modules.pullback f) A B).symm ≪≫
      monoidalTensorObjIso ((Scheme.Modules.pullback f).obj A)
        ((Scheme.Modules.pullback f).obj B)).symm.hom.val.app
      (Opposite.op (f ⁻¹ᵁ U))
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 Y'.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj
            ((Scheme.Modules.pullback f).obj A).val
            ((Scheme.Modules.pullback f).obj B).val)).app
        (Opposite.op (f ⁻¹ᵁ U))
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app
          (Opposite.op U) x) ⊗ₜ
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app B).val.app
            (Opposite.op U) y)))) =
      ((Scheme.Modules.pullback f).map (monoidalTensorObjIso A B).hom).val.app
        (Opposite.op (f ⁻¹ᵁ U))
        ((Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) A B).val.app
          (Opposite.op (f ⁻¹ᵁ U))
          ((monoidalTensorObjIso ((Scheme.Modules.pullback f).obj A)
            ((Scheme.Modules.pullback f).obj B)).inv.val.app
            (Opposite.op (f ⁻¹ᵁ U))
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 Y'.ringCatSheaf.obj)).unit.app
                (MonoidalCategoryStruct.tensorObj
                  ((Scheme.Modules.pullback f).obj A).val
                  ((Scheme.Modules.pullback f).obj B).val)).app
              (Opposite.op (f ⁻¹ᵁ U))
              ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
                A).val.app (Opposite.op U) x) ⊗ₜ
                (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
                  B).val.app (Opposite.op U) y))))) := rfl
  refine hcomp.trans ?_
  rw [hv1, hv2, hv3, hcancel]

/-- **([NR-unit-eq-res])** The unit image at `U` is the `eqToHom`-transport of the unit
image at a smaller open with equal preimage (small binders; the `hA2`-realignment of
the slot walk). -/
private theorem pullbackUnit_app_eq_res {X' Y' : Scheme.{u}} (f : Y' ⟶ X')
    (P : X'.Modules) {U IM' : X'.Opens} (hle : IM' ≤ U)
    (hpre : (f ⁻¹ᵁ IM') = f ⁻¹ᵁ U) (m : P.val.obj (Opposite.op U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).val.app
        (Opposite.op U) m =
      ((Scheme.Modules.pullback f).obj P).val.map (eqToHom hpre.symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).val.app
          (Opposite.op IM') (P.val.map (homOfLE hle).op m)) := by
  have h1 := pullbackUnit_app_res f P hle m
  have h2 : ∀ (z : (((Scheme.Modules.pullback f).obj P).val.obj (Opposite.op (f ⁻¹ᵁ U)))),
      ((Scheme.Modules.pullback f).obj P).val.map (eqToHom hpre.symm).op
        (((Scheme.Modules.pullback f).obj P).val.map
          (homOfLE (by exact fun x hx => hle hx : f ⁻¹ᵁ IM' ≤ f ⁻¹ᵁ U)).op z) = z := by
    intro z
    have hmapeq : (((Scheme.Modules.pullback f).obj P).presheaf.map
        (homOfLE (by exact fun x hx => hle hx : f ⁻¹ᵁ IM' ≤ f ⁻¹ᵁ U)).op) ≫
        (((Scheme.Modules.pullback f).obj P).presheaf.map (eqToHom hpre.symm).op) =
        𝟙 _ := by
      rw [← Functor.map_comp]
      rw [show ((homOfLE (by exact fun x hx => hle hx :
          f ⁻¹ᵁ IM' ≤ f ⁻¹ᵁ U)).op ≫ (eqToHom hpre.symm).op) =
        (𝟙 (Opposite.op (f ⁻¹ᵁ U))) from Subsingleton.elim _ _]
      exact CategoryTheory.Functor.map_id _ _
    have happ := ConcreteCategory.congr_hom hmapeq z
    exact happ
  exact ((h2 _).symm).trans (congrArg
    (((Scheme.Modules.pullback f).obj P).val.map (eqToHom hpre.symm).op) h1)

/-- **([slot-walk prefix])** The slot value through the `s1`/`congr-tmul`/`s2` stages. -/
private theorem slot_walk_prefix (Wo : X.Opens) (g₁ : Γ(X, Wo))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op Wo))
    (hgi₁ : IsIso (idealGenHom J₁ Wo g₁ hg₁))
    (U : X.Opens) (m : M.val.obj (Opposite.op U))
    (hpre : (Wo.ι ⁻¹ᵁ (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U))) = Wo.ι ⁻¹ᵁ U) :
    (tensorIdealSlotIso M J₁ Wo g₁ hg₁ hgi₁).hom.val.app
        (Opposite.op (Wo.ι ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app M).val.app
          (Opposite.op U) m) =
      ((pullbackTensorObjIsoOfIsOpenImmersion Wo.ι M
          (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).symm.hom.val.app
        (Opposite.op (Wo.ι ⁻¹ᵁ U))
        ((((PresheafOfModules.sheafificationAdjunction
          (𝟙 Wo.toScheme.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj
              ((Scheme.Modules.pullback Wo.ι).obj M).val
              ((Scheme.Modules.pullback Wo.ι).obj
                (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val)).app
          (Opposite.op (Wo.ι ⁻¹ᵁ U)))
          ((((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app M).val.app
              (Opposite.op U) m) ⊗ₜ
            (((Scheme.Modules.pullback Wo.ι).obj
                (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val.map
              (eqToHom hpre.symm).op
              (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app
                (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val.app
                (Opposite.op (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U))) (⟨X.presheaf.map (homOfLE (Wo.ι_image_le (Wo.ι ⁻¹ᵁ U))).op g₁,
        idealSections_map J₁ (homOfLE (Wo.ι_image_le (Wo.ι ⁻¹ᵁ U))).op hg₁⟩)))))) := by

  -- split the slot into its three pieces at the unit image
  have hsplit : (tensorIdealSlotIso M J₁ Wo g₁ hg₁ hgi₁).hom.val.app
      (Opposite.op (Wo.ι ⁻¹ᵁ U)) (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app M).val.app (Opposite.op U) m) =
      (pullbackTensorObjIsoOfIsOpenImmersion Wo.ι M
          (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).symm.hom.val.app
        (Opposite.op (Wo.ι ⁻¹ᵁ U))
        ((tensorObjCongr (Iso.refl ((Scheme.Modules.pullback Wo.ι).obj M))
            (pullbackIdealTrivOfGen J₁ Wo g₁ hg₁ hgi₁).symm).hom.val.app
          (Opposite.op (Wo.ι ⁻¹ᵁ U))
          ((AlgebraicGeometry.Scheme.Modules.tensorObjUnitIso
            ((Scheme.Modules.pullback Wo.ι).obj M)).symm.hom.val.app
            (Opposite.op (Wo.ι ⁻¹ᵁ U)) (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app M).val.app (Opposite.op U) m))) := rfl
  refine hsplit.trans ?_
  -- [s1] the unit insertion
  rw [tensorObjUnitIso_symm_hom_app]
  -- [congr-tmul] the generator trivialisation in the second slot
  rw [tensorObjCongr_hom_app_unit_tmul]
  -- [s2] the generator value at 1 (the refl-factor is definitionally untouched)
  rw [pullbackIdealTrivOfGen_symm_hom_app_one J₁ Wo g₁ hg₁ hgi₁
    (Opposite.op (Wo.ι ⁻¹ᵁ U)) hpre]
  -- collapse the `Iso.refl`-clothing on the first tensor slot (defeq to the identity)
  rfl

/-- **([A45 micro])** The comparison-after-sheafification-unit composite crosses an
`eqToHom` re-index: both naturalities at once, `subst`-discharged on a general section
(no tensor element in sight, so no carrier-defeq storm). -/
private theorem comparison_shUnit_app_map_eqToHom (Wo : X.Opens)
    {O₁ O₂ : Wo.toScheme.Opens} (h : O₂ = O₁)
    (z : (MonoidalCategoryStruct.tensorObj
        ((Scheme.Modules.pullback Wo.ι).obj M).val
        ((Scheme.Modules.pullback Wo.ι).obj
          (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val).obj
      (Opposite.op O₁)) :
    (pullbackTensorObjIsoOfIsOpenImmersion Wo.ι M
        (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).symm.hom.val.app
      (Opposite.op O₂)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 Wo.toScheme.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj
            ((Scheme.Modules.pullback Wo.ι).obj M).val
            ((Scheme.Modules.pullback Wo.ι).obj
              (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val)).app
        (Opposite.op O₂)
        ((MonoidalCategoryStruct.tensorObj
            ((Scheme.Modules.pullback Wo.ι).obj M).val
            ((Scheme.Modules.pullback Wo.ι).obj
              (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val).map
          (eqToHom h).op z)) =
      ((Scheme.Modules.pullback Wo.ι).obj
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
        (eqToHom h).op
        ((pullbackTensorObjIsoOfIsOpenImmersion Wo.ι M
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).symm.hom.val.app
          (Opposite.op O₁)
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 Wo.toScheme.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj
                ((Scheme.Modules.pullback Wo.ι).obj M).val
                ((Scheme.Modules.pullback Wo.ι).obj
                  (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val)).app
            (Opposite.op O₁) z)) :=
  PresheafOfModules.naturality_apply
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 Wo.toScheme.ringCatSheaf.obj)).unit.app
        (MonoidalCategoryStruct.tensorObj
          ((Scheme.Modules.pullback Wo.ι).obj M).val
          ((Scheme.Modules.pullback Wo.ι).obj
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val)) ≫
      (pullbackTensorObjIsoOfIsOpenImmersion Wo.ι M
        (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).symm.hom.val)
    (eqToHom h).op z

set_option backward.isDefEq.respectTransparency false in
/-- **([slot-walk tail])** From the both-factors-mapped form to the mapped unit image
of the sheafified tensor at the image open: fuse, cross the two naturalities, apply
the comparison formula. Fresh declaration per the per-decl-budget rule. The opacity
flip is for `tensorObj_map_tmul`, whose `DFunLike`-annotated statement (mathlib states
it under the same option) otherwise storms `isDefEq` against the goal spelling. -/
private theorem slot_walk_tail (Wo : X.Opens) (g₁ : Γ(X, Wo))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op Wo))
    (U : X.Opens) (m : M.val.obj (Opposite.op U))
    (hpre : (Wo.ι ⁻¹ᵁ (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U))) = Wo.ι ⁻¹ᵁ U)
    (hIMle : (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U)) ≤ U) :
    (pullbackTensorObjIsoOfIsOpenImmersion Wo.ι M
        (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).symm.hom.val.app
      (Opposite.op (Wo.ι ⁻¹ᵁ U))
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 Wo.toScheme.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj
            ((Scheme.Modules.pullback Wo.ι).obj M).val
            ((Scheme.Modules.pullback Wo.ι).obj
              (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val)).app
        (Opposite.op (Wo.ι ⁻¹ᵁ U))
        ((((Scheme.Modules.pullback Wo.ι).obj M).val.map (eqToHom hpre.symm).op
          (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app M).val.app
            (Opposite.op (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U)))
            (M.val.map (homOfLE hIMle).op m))) ⊗ₜ
        (((Scheme.Modules.pullback Wo.ι).obj
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val.map
          (eqToHom hpre.symm).op
          (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val.app
            (Opposite.op (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U)))
            (⟨X.presheaf.map (homOfLE (Wo.ι_image_le (Wo.ι ⁻¹ᵁ U))).op g₁,
              idealSections_map J₁
                (homOfLE (Wo.ι_image_le (Wo.ι ⁻¹ᵁ U))).op hg₁⟩))))) =
      ((Scheme.Modules.pullback Wo.ι).obj
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
        (eqToHom hpre.symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
          (Opposite.op (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U)))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj M.val
                (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
            (Opposite.op (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U)))
            ((M.val.map (homOfLE hIMle).op m) ⊗ₜ
              (⟨X.presheaf.map (homOfLE (Wo.ι_image_le (Wo.ι ⁻¹ᵁ U))).op g₁,
                idealSections_map J₁
                  (homOfLE (Wo.ι_image_le (Wo.ι ⁻¹ᵁ U))).op hg₁⟩)))) := by
  -- [A3] fuse the two mapped factors into the mapped tensor (typed have: the
  -- DFunLike annotation on `tensorObj_map_tmul` blocks `rw`; `exact` crosses it)
  have e3 : (((Scheme.Modules.pullback Wo.ι).obj M).val.map (eqToHom hpre.symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app M).val.app
          (Opposite.op (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U))) (M.val.map (homOfLE hIMle).op m))) ⊗ₜ
      (((Scheme.Modules.pullback Wo.ι).obj
          (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val.map
        (eqToHom hpre.symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app
          (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val.app
          (Opposite.op (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U)))
          (⟨X.presheaf.map (homOfLE (Wo.ι_image_le (Wo.ι ⁻¹ᵁ U))).op g₁,
            idealSections_map J₁ (homOfLE (Wo.ι_image_le (Wo.ι ⁻¹ᵁ U))).op hg₁⟩))) =
      (MonoidalCategoryStruct.tensorObj
          ((Scheme.Modules.pullback Wo.ι).obj M).val
          ((Scheme.Modules.pullback Wo.ι).obj
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val).map
        (eqToHom hpre.symm).op
        ((((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app M).val.app
            (Opposite.op (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U))) (M.val.map (homOfLE hIMle).op m)) ⊗ₜ
          (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val.app
            (Opposite.op (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U)))
            (⟨X.presheaf.map (homOfLE (Wo.ι_image_le (Wo.ι ⁻¹ᵁ U))).op g₁,
              idealSections_map J₁ (homOfLE (Wo.ι_image_le (Wo.ι ⁻¹ᵁ U))).op hg₁⟩))) :=
    rfl
  rw [e3]
  -- [A4+A5] cross the eqToHom re-index through the unit and the comparison at once
  refine Eq.trans (comparison_shUnit_app_map_eqToHom M J₁ Wo hpre.symm _) ?_
  -- [A6] the comparison value on the tmul of unit images at the image open
  exact congrArg (fun z =>
    ((Scheme.Modules.pullback Wo.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
      (eqToHom hpre.symm).op z)
    (pullbackTensorObjIsoOfIsOpenImmersion_symm_hom_app_unit Wo.ι M
      (AlgebraicGeometry.Scheme.Modules.idealModule J₁) (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U))
      (M.val.map (homOfLE hIMle).op m) _)

/-- **([slot-walk], statement)** The slot construction on a pullback-adjunction-unit
image: the value is the unit image of the sheafified pure tensor of the restricted
section with the restricted generator (all data at the image open `U ⊓ Wo`, re-indexed
by `hpre`). The per-side walk of the slot square. -/
private theorem slot_walk (Wo : X.Opens) (g₁ : Γ(X, Wo))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op Wo))
    (hgi₁ : IsIso (idealGenHom J₁ Wo g₁ hg₁))
    (U : X.Opens) (m : M.val.obj (Opposite.op U))
    (hpre : (Wo.ι ⁻¹ᵁ (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U))) = Wo.ι ⁻¹ᵁ U)
    (hIMle : (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U)) ≤ U) :
    (tensorIdealSlotIso M J₁ Wo g₁ hg₁ hgi₁).hom.val.app
        (Opposite.op (Wo.ι ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app M).val.app
          (Opposite.op U) m) =
      ((Scheme.Modules.pullback Wo.ι).obj
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
        (eqToHom hpre.symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction Wo.ι).unit.app
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
          (Opposite.op (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U)))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj M.val
                (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
            (Opposite.op (Wo.ι ''ᵁ (Wo.ι ⁻¹ᵁ U)))
            ((M.val.map (homOfLE hIMle).op m) ⊗ₜ
              (⟨X.presheaf.map (homOfLE (Wo.ι_image_le (Wo.ι ⁻¹ᵁ U))).op g₁,
                idealSections_map J₁
                  (homOfLE (Wo.ι_image_le (Wo.ι ⁻¹ᵁ U))).op hg₁⟩)))) := by
  refine (slot_walk_prefix M J₁ Wo g₁ hg₁ hgi₁ U m hpre).trans ?_
  -- [A2] the first factor as an eqToHom-mapped image-restricted unit image
  have hA2 := pullbackUnit_app_eq_res Wo.ι M hIMle hpre m
  rw [hA2]
  -- [A3–A6] the extracted tail (fresh per-decl budget)
  exact slot_walk_tail M J₁ Wo g₁ hg₁ U m hpre hIMle

/-- **([app-Congr-unit crossing])** A module map applied to the `Congr`-clothed
`g`-unit image, at the `g`-side index, is the single cast of its value on the `f`-unit
image: the one propositional `f = g` crossing, `subst`-discharged. -/
private theorem app_pullbackCongr_inv_unit {X' Y' : Scheme.{u}} {f g : Y' ⟶ X'}
    (he : f = g) (P : X'.Modules) {Q : Y'.Modules}
    (φ : (Scheme.Modules.pullback f).obj P ⟶ Q)
    (U : X'.Opens) (w : P.val.obj (Opposite.op U)) :
    φ.val.app (Opposite.op (g ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackCongr he).app P).inv.val.app
          (Opposite.op (g ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app P).val.app
            (Opposite.op U) w)) =
      (show Q.val.obj (Opposite.op (g ⁻¹ᵁ U)) by
        rw [← he]
        exact φ.val.app (Opposite.op (f ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).val.app
            (Opposite.op U) w)) := by
  subst he
  rfl

/-- **([Congr-unit arg crossing])** The `Congr`-clothed `g`-unit image at the
`g`-side index is the single cast of the `f`-unit image (argument-level form). -/
private theorem pullbackCongr_inv_unit_arg {X' Y' : Scheme.{u}} {f g : Y' ⟶ X'}
    (he : f = g) (P : X'.Modules) (U : X'.Opens) (w : P.val.obj (Opposite.op U)) :
    ((Scheme.Modules.pullbackCongr he).app P).inv.val.app
        (Opposite.op (g ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app P).val.app
          (Opposite.op U) w) =
      (show ((Scheme.Modules.pullback f).obj P).val.obj (Opposite.op (g ⁻¹ᵁ U)) by
        rw [← he]
        exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app P).val.app
          (Opposite.op U) w) := by
  subst he
  rfl

/-- **([map-eqToHom cast crossing])** A restriction along an `eqToHom` between
`g`-side preimages, applied to a cast value, is the cast of the `f`-side
restriction: parallel opens-equality proofs cross by proof irrelevance. -/
private theorem map_eqToHom_cast_crossing {X' Y' : Scheme.{u}} {f g : Y' ⟶ X'}
    (he : f = g) (Q : Y'.Modules) {O O' : X'.Opens}
    (eg : g ⁻¹ᵁ O = g ⁻¹ᵁ O') (ef : f ⁻¹ᵁ O = f ⁻¹ᵁ O')
    (y : Q.val.obj (Opposite.op (f ⁻¹ᵁ O'))) :
    Q.val.map (eqToHom eg).op
        ((show Q.val.obj (Opposite.op (g ⁻¹ᵁ O')) by
          rw [← he]
          exact y)) =
      (show Q.val.obj (Opposite.op (g ⁻¹ᵁ O)) by
        rw [← he]
        exact Q.val.map (eqToHom ef).op y) := by
  subst he
  rfl

/-- **([SLOT-SQ LHS-chain])** The transported slot on the double-unit image: collapse
the transport (Congr-stage), cross the propositional `W.ι = homOfLE ≫ V.ι` wall once
via `app_pullbackCongr_inv_unit`, then the `W`-walk under the cast. Own declaration
per the per-decl-budget rule. -/
private theorem slot_sq_lhs {V W : X.Opens} (hWV : W ≤ V)
    (he : W.ι = X.homOfLE hWV ≫ V.ι) (g₁ : Γ(X, V))
    (hg₁' : X.presheaf.map (homOfLE hWV).op g₁ ∈ idealSections J₁ (Opposite.op W))
    (hgi₁' : IsIso (idealGenHom J₁ W (X.presheaf.map (homOfLE hWV).op g₁) hg₁'))
    (U : X.Opens) (m : M.val.obj (Opposite.op U)) :
    (tensorIdealSlotIso M J₁ W (X.presheaf.map (homOfLE hWV).op g₁)
        hg₁' hgi₁').hom.val.app
      (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)))
      ((pullbackRestrictTransport hWV M).val.app
        (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)))
        (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
          ((Scheme.Modules.pullback V.ι).obj M)).val.app
          (Opposite.op (V.ι ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M).val.app
            (Opposite.op U) m))) =
      (show ((Scheme.Modules.pullback W.ι).obj
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.obj
        (Opposite.op ((X.homOfLE hWV ≫ V.ι) ⁻¹ᵁ U)) by
      rw [← he]
      exact ((Scheme.Modules.pullback W.ι).obj
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
        (eqToHom (Scheme.Hom.preimage_image_eq W.ι (W.ι ⁻¹ᵁ U)).symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
          (Opposite.op (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj M.val
                (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
            (Opposite.op (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)))
            ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le W.ι U)).op m) ⊗ₜ
              (⟨X.presheaf.map (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ U))).op
                  (X.presheaf.map (homOfLE hWV).op g₁),
                idealSections_map J₁
                  (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ U))).op hg₁'⟩))))) := by
  -- [L1] collapse the transport on the double-unit image (Congr-stage)
  refine Eq.trans (congrArg (fun z =>
    (tensorIdealSlotIso M J₁ W (X.presheaf.map (homOfLE hWV).op g₁)
        hg₁' hgi₁').hom.val.app
      (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U))) z)
    (pullbackRestrictTransport_app_unit hWV M U m)) ?_
  -- [L2] the single propositional crossing
  refine Eq.trans (app_pullbackCongr_inv_unit he M
    (tensorIdealSlotIso M J₁ W (X.presheaf.map (homOfLE hWV).op g₁)
      hg₁' hgi₁').hom U m) ?_
  -- [L3] the W-walk under the cast
  exact congrArg (fun v =>
    show ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.obj
      (Opposite.op ((X.homOfLE hWV ≫ V.ι) ⁻¹ᵁ U)) by
    rw [← he]
    exact v)
    (slot_walk M J₁ W (X.presheaf.map (homOfLE hWV).op g₁) hg₁' hgi₁'
      U m (Scheme.Hom.preimage_image_eq W.ι (W.ι ⁻¹ᵁ U))
      (Scheme.Hom.image_preimage_le W.ι U))

/-- **([SLOT-SQ RHS-chain], reversed)** The pulled slot then the transport on the
double-unit image, peeled to the Congr-stage form of the `V`-walk output. Stated
reversed so the peel closes by `rfl`. Own declaration per the per-decl-budget rule. -/
private theorem slot_sq_rhs {V W : X.Opens} (hWV : W ≤ V) (g₁ : Γ(X, V))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (hgi₁ : IsIso (idealGenHom J₁ V g₁ hg₁))
    (U : X.Opens) (m : M.val.obj (Opposite.op U)) :
    ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
      ((Opens.map (X.homOfLE hWV).base).map
        (eqToHom (Scheme.Hom.preimage_image_eq V.ι (V.ι ⁻¹ᵁ U)).symm)).op
      (((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).inv.val.app
        (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))))
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (X.homOfLE hWV ≫ V.ι)).unit.app
            (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
          (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj M.val
                (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
            (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
            ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
              (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
                idealSections_map J₁
                  (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩))))) =
    (pullbackRestrictTransport hWV
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
      (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)))
      (((Scheme.Modules.pullback (X.homOfLE hWV)).map
          (tensorIdealSlotIso M J₁ V g₁ hg₁ hgi₁).hom).val.app
        (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)))
        (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
          ((Scheme.Modules.pullback V.ι).obj M)).val.app
          (Opposite.op (V.ι ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M).val.app
            (Opposite.op U) m))) := by
  -- [R1] the pulled slot on the double-unit image
  refine Eq.trans ?_ (congrArg (fun z =>
    (pullbackRestrictTransport hWV
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
      (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U))) z)
    (pullbackMap_app_unit (X.homOfLE hWV)
      (tensorIdealSlotIso M J₁ V g₁ hg₁ hgi₁).hom (V.ι ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M).val.app
        (Opposite.op U) m))).symm
  -- [R2] the V-walk on the unit image, under the transport
  refine Eq.trans ?_ (congrArg (fun z =>
    (pullbackRestrictTransport hWV
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
      (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)))
      (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
        ((Scheme.Modules.pullback V.ι).obj
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁)))).val.app
        (Opposite.op (V.ι ⁻¹ᵁ U)) z))
    (slot_walk M J₁ V g₁ hg₁ hgi₁ U m
      (Scheme.Hom.preimage_image_eq V.ι (V.ι ⁻¹ᵁ U))
      (Scheme.Hom.image_preimage_le V.ι U))).symm
  -- [R3] the H-unit naturality across the eqToHom re-index, under the transport
  refine Eq.trans ?_ (congrArg (fun z =>
    (pullbackRestrictTransport hWV
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
      (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U))) z)
    (PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
        ((Scheme.Modules.pullback V.ι).obj
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁)))).val
      (eqToHom (Scheme.Hom.preimage_image_eq V.ι (V.ι ⁻¹ᵁ U)).symm).op
      (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
        (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj M.val
              (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
          (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
          ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
            (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
              idealSections_map J₁
                (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩)))))).symm
  -- [R4] the transport crosses the mapped re-index
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply
    (pullbackRestrictTransport hWV
      (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val
    ((Opens.map (X.homOfLE hWV).base).map
      (eqToHom (Scheme.Hom.preimage_image_eq V.ι (V.ι ⁻¹ᵁ U)).symm)).op
    (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
      ((Scheme.Modules.pullback V.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁)))).val.app
      (Opposite.op (V.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U))))
      (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
        (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj M.val
              (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
          (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
          ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
            (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
              idealSections_map J₁
                (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩)))))).symm
  -- [R5] collapse the transport on the image-open double-unit image (Congr-stage)
  refine Eq.trans ?_ (congrArg (fun z =>
    ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
      ((Opens.map (X.homOfLE hWV).base).map
        (eqToHom (Scheme.Hom.preimage_image_eq V.ι (V.ι ⁻¹ᵁ U)).symm)).op z)
    (pullbackRestrictTransport_app_unit hWV
      (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))
      (V.ι ''ᵁ (V.ι ⁻¹ᵁ U))
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj M.val
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
        (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
        ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
          (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
            idealSections_map J₁
              (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩))))).symm
  rfl

/-- **([SLOT-SQ meet, `X`-level tensor step])** The sheafified pure tensor at the
`W`-image open is the restriction of the one at the `V`-image open: sheafification
naturality, the tensor of restrictions, and the two composite-restriction legs. -/
private theorem slot_sq_meet_inner_x {V W : X.Opens} (hWV : W ≤ V) (g₁ : Γ(X, V))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (hg₁' : X.presheaf.map (homOfLE hWV).op g₁ ∈ idealSections J₁ (Opposite.op W))
    (U : X.Opens)
    (hle : (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)) ≤ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
    (m : M.val.obj (Opposite.op U)) :
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app
        (MonoidalCategoryStruct.tensorObj M.val
          (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
      (Opposite.op (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)))
      ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le W.ι U)).op m) ⊗ₜ
        (⟨X.presheaf.map (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ U))).op
            (X.presheaf.map (homOfLE hWV).op g₁),
          idealSections_map J₁
            (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ U))).op hg₁'⟩)) =
    (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val.map
      (homOfLE hle).op
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj M.val
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
        (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
        ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
          (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
            idealSections_map J₁
              (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩))) := by
  -- [b3] the sheafification unit is natural at the restriction (typed have: the
  -- adjunction-target functor spelling differs from the sheaf-`val` spelling)
  have h3 : (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁)).val.map
      (homOfLE hle).op
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj M.val
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
        (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
        ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
          (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
            idealSections_map J₁
              (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩))) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj M.val
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
        (Opposite.op (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)))
        ((MonoidalCategoryStruct.tensorObj M.val
          (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val).map
          (homOfLE hle).op
          ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
            (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
              idealSections_map J₁
                (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩))) :=
    (PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj M.val
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val))
      (homOfLE hle).op
      ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
        (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
          idealSections_map J₁
            (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩))).symm
  refine Eq.trans ?_ h3.symm
  refine congrArg (((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app
      (MonoidalCategoryStruct.tensorObj M.val
        (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
    (Opposite.op (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)))) ?_
  -- [b4] the tensor restriction on the pure tensor is the tensor of restrictions
  have e4 : (MonoidalCategoryStruct.tensorObj M.val
      (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val).map
      (homOfLE hle).op
      ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
        (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
          idealSections_map J₁
            (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩)) =
      (M.val.map (homOfLE hle).op
        (M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m)) ⊗ₜ
      ((AlgebraicGeometry.Scheme.Modules.idealModule J₁).val.map (homOfLE hle).op
        (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
          idealSections_map J₁
            (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩)) := rfl
  refine Eq.trans ?_ e4.symm
  -- [b5] the two legs: composite restrictions fuse (poset arrows are equal)
  have hm : M.val.map (homOfLE (Scheme.Hom.image_preimage_le W.ι U)).op m =
      M.val.map (homOfLE hle).op
        (M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) := by
    refine Eq.trans (congrArg (fun (σ : (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)) ⟶ U) =>
      M.val.map σ.op m) (Subsingleton.elim _
        (homOfLE hle ≫ homOfLE (Scheme.Hom.image_preimage_le V.ι U)))) ?_
    exact ConcreteCategory.congr_hom (M.val.map_comp
      (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op (homOfLE hle).op) m
  have hg : (⟨X.presheaf.map (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ U))).op
        (X.presheaf.map (homOfLE hWV).op g₁),
      idealSections_map J₁ (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ U))).op hg₁'⟩ :
        (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val.obj
          (Opposite.op (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)))) =
      (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val.map (homOfLE hle).op
        (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
          idealSections_map J₁ (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩) := by
    apply Subtype.ext
    show X.presheaf.map (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ U))).op
        (X.presheaf.map (homOfLE hWV).op g₁) =
      X.presheaf.map (homOfLE hle).op
        (X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁)
    refine Eq.trans (ConcreteCategory.congr_hom (X.presheaf.map_comp
      (homOfLE hWV).op (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ U))).op) g₁).symm ?_
    refine Eq.trans (congrArg (fun (σ : (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)) ⟶ V) =>
      X.presheaf.map σ.op g₁) (Subsingleton.elim _
        (homOfLE hle ≫ homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))))) ?_
    exact ConcreteCategory.congr_hom (X.presheaf.map_comp
      (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op (homOfLE hle).op) g₁
  exact congr_arg₂ (fun a b => a ⊗ₜ b) hm hg
/-- **([ef-split micro])** The `ef`-restriction on any section splits through the
`W`-image open: poset arrows are equal, then the functor law. Small binders. -/
private theorem map_ef_split {V W : X.Opens} (hWV : W ≤ V) (U : X.Opens)
    (ef : W.ι ⁻¹ᵁ U = W.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
    (hle : (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)) ≤ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
    (y : ((Scheme.Modules.pullback W.ι).obj
      (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.obj
      (Opposite.op (W.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U))))) :
    ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
      (eqToHom ef).op y =
    ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
      (eqToHom (Scheme.Hom.preimage_image_eq W.ι (W.ι ⁻¹ᵁ U)).symm).op
      (((Scheme.Modules.pullback W.ι).obj
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
        (homOfLE (by exact fun x hx => hle hx :
          W.ι ⁻¹ᵁ (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)) ≤ W.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))).op y) := by
  have hcomp : (eqToHom (Scheme.Hom.preimage_image_eq W.ι (W.ι ⁻¹ᵁ U)).symm ≫
      homOfLE (by exact fun x hx => hle hx :
        W.ι ⁻¹ᵁ (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)) ≤ W.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))) =
      eqToHom ef := Subsingleton.elim _ _
  refine Eq.trans (congrArg (fun (σ : (W.ι ⁻¹ᵁ U) ⟶
      (W.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))) =>
    ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map σ.op
      y) hcomp.symm) ?_
  exact ConcreteCategory.congr_hom (((Scheme.Modules.pullback W.ι).obj
    (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map_comp
      (homOfLE (by exact fun x hx => hle hx :
        W.ι ⁻¹ᵁ (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)) ≤ W.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))).op
      (eqToHom (Scheme.Hom.preimage_image_eq W.ι (W.ι ⁻¹ᵁ U)).symm).op) y

private theorem slot_sq_meet_inner {V W : X.Opens} (hWV : W ≤ V) (g₁ : Γ(X, V))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (hg₁' : X.presheaf.map (homOfLE hWV).op g₁ ∈ idealSections J₁ (Opposite.op W))
    (U : X.Opens)
    (ef : W.ι ⁻¹ᵁ U = W.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
    (m : M.val.obj (Opposite.op U)) :
    ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
      (eqToHom (Scheme.Hom.preimage_image_eq W.ι (W.ι ⁻¹ᵁ U)).symm).op
      (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
        (Opposite.op (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)))
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj M.val
              (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
          (Opposite.op (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)))
          ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le W.ι U)).op m) ⊗ₜ
            (⟨X.presheaf.map (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ U))).op
                (X.presheaf.map (homOfLE hWV).op g₁),
              idealSections_map J₁
                (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ U))).op hg₁'⟩)))) =
    ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
      (eqToHom ef).op
      (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
        (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app
            (MonoidalCategoryStruct.tensorObj M.val
              (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
          (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
          ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
            (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
              idealSections_map J₁
                (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩)))) := by
  have hle : (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)) ≤ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    exact inf_le_inf hWV le_rfl
  -- [b1] split the ef-restriction through the W-image open (micro)
  refine Eq.trans ?_ (map_ef_split M J₁ hWV U ef hle _).symm
  -- peel the shared outer restriction
  refine congrArg (fun z =>
    ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
      (eqToHom (Scheme.Hom.preimage_image_eq W.ι (W.ι ⁻¹ᵁ U)).symm).op z) ?_
  -- [b2] the unit restricts to the W-image open
  refine Eq.trans ?_ (pullbackUnit_app_res W.ι
    (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁)) hle
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app
        (MonoidalCategoryStruct.tensorObj M.val
          (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
      (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
      ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
        (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
          idealSections_map J₁
            (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩)))).symm
  -- [b3–b5] the X-level tensor step, under the W-unit
  refine congrArg (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app
    (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
    (Opposite.op (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)))) ?_
  exact slot_sq_meet_inner_x M J₁ hWV g₁ hg₁ hg₁' U hle m

/-- **([SLOT-SQ meet, RHS peel])** The Congr-stage `V`-form peeled to the cast
re-indexed `W`-unit reading at the `V`-image: the crossing, the arrow swap, and the
map-cast commutation. Own declaration per the per-decl-budget rule; stated reversed
so the peel closes by `rfl`. -/
private theorem slot_sq_meet_peel {V W : X.Opens} (hWV : W ≤ V)
    (he : W.ι = X.homOfLE hWV ≫ V.ι) (g₁ : Γ(X, V))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (U : X.Opens)
    (ef : W.ι ⁻¹ᵁ U = W.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
    (m : M.val.obj (Opposite.op U)) :
    (show ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.obj
      (Opposite.op ((X.homOfLE hWV ≫ V.ι) ⁻¹ᵁ U)) by
      rw [← he]
      exact ((Scheme.Modules.pullback W.ι).obj
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
        (eqToHom ef).op
        (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
          (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj M.val
                (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
            (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
            ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
              (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
                idealSections_map J₁
                  (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩))))) =
    ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
      ((Opens.map (X.homOfLE hWV).base).map
        (eqToHom (Scheme.Hom.preimage_image_eq V.ι (V.ι ⁻¹ᵁ U)).symm)).op
      (((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).inv.val.app
        (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))))
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (X.homOfLE hWV ≫ V.ι)).unit.app
            (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
          (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj M.val
                (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
            (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
            ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
              (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
                idealSections_map J₁
                  (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩))))) := by
  -- [M1] the Congr-clothed composite-unit image is the cast W-unit image
  refine Eq.trans ?_ (congrArg (fun z =>
    ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
      ((Opens.map (X.homOfLE hWV).base).map
        (eqToHom (Scheme.Hom.preimage_image_eq V.ι (V.ι ⁻¹ᵁ U)).symm)).op z)
    (pullbackCongr_inv_unit_arg he
      (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))
      (V.ι ''ᵁ (V.ι ⁻¹ᵁ U))
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj M.val
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
        (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
        ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
          (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
            idealSections_map J₁
              (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩))))).symm
  -- [M2] the mapped-arrow is the eqToHom of the mapped opens-equality
  refine Eq.trans ?_ (congrArg (fun (σ : ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)) ⟶
      ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U))))) =>
    ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map σ.op
      ((show ((Scheme.Modules.pullback W.ι).obj
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.obj
        (Opposite.op ((X.homOfLE hWV ≫ V.ι) ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))) by
        rw [← he]
        exact ((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
          (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj M.val
                (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
            (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
            ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
              (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
                idealSections_map J₁
                  (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩))))))
    (Subsingleton.elim
      ((Opens.map (X.homOfLE hWV).base).map
        (eqToHom (Scheme.Hom.preimage_image_eq V.ι (V.ι ⁻¹ᵁ U)).symm))
      (eqToHom (congrArg (fun O => (X.homOfLE hWV) ⁻¹ᵁ O)
        (Scheme.Hom.preimage_image_eq V.ι (V.ι ⁻¹ᵁ U)).symm)))).symm
  -- [M3] the restriction along the eqToHom crosses the cast
  refine Eq.trans ?_ (map_eqToHom_cast_crossing he
    ((Scheme.Modules.pullback W.ι).obj
      (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁)))
    (O := U) (O' := V.ι ''ᵁ (V.ι ⁻¹ᵁ U))
    (congrArg (fun O => (X.homOfLE hWV) ⁻¹ᵁ O)
      (Scheme.Hom.preimage_image_eq V.ι (V.ι ⁻¹ᵁ U)).symm)
    ef
    (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app
      (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
      (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app
          (MonoidalCategoryStruct.tensorObj M.val
            (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
        (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
        ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
          (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
            idealSections_map J₁
              (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩))))).symm
  rfl

/-- **([SLOT-SQ meet, cast-wrapped inner])** The pure-`W` inner comparison under the
shared cast: both sides in the composite spelling, one `congrArg`. -/
private theorem slot_sq_meet_inner_cast {V W : X.Opens} (hWV : W ≤ V)
    (he : W.ι = X.homOfLE hWV ≫ V.ι) (g₁ : Γ(X, V))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (hg₁' : X.presheaf.map (homOfLE hWV).op g₁ ∈ idealSections J₁ (Opposite.op W))
    (U : X.Opens)
    (ef : W.ι ⁻¹ᵁ U = W.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
    (m : M.val.obj (Opposite.op U)) :
    (show ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.obj
      (Opposite.op ((X.homOfLE hWV ≫ V.ι) ⁻¹ᵁ U)) by
      rw [← he]
      exact ((Scheme.Modules.pullback W.ι).obj
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
        (eqToHom (Scheme.Hom.preimage_image_eq W.ι (W.ι ⁻¹ᵁ U)).symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
          (Opposite.op (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj M.val
                (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
            (Opposite.op (W.ι ''ᵁ (W.ι ⁻¹ᵁ U)))
            ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le W.ι U)).op m) ⊗ₜ
              (⟨X.presheaf.map (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ U))).op
                  (X.presheaf.map (homOfLE hWV).op g₁),
                idealSections_map J₁
                  (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ U))).op hg₁'⟩))))) =
    (show ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.obj
      (Opposite.op ((X.homOfLE hWV ≫ V.ι) ⁻¹ᵁ U)) by
      rw [← he]
      exact ((Scheme.Modules.pullback W.ι).obj
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.map
        (eqToHom ef).op
        (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
          (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app
              (MonoidalCategoryStruct.tensorObj M.val
                (AlgebraicGeometry.Scheme.Modules.idealModule J₁).val)).app
            (Opposite.op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U)))
            ((M.val.map (homOfLE (Scheme.Hom.image_preimage_le V.ι U)).op m) ⊗ₜ
              (⟨X.presheaf.map (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op g₁,
                idealSections_map J₁
                  (homOfLE (V.ι_image_le (V.ι ⁻¹ᵁ U))).op hg₁⟩))))) :=
  congrArg (fun v =>
    show ((Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.obj
      (Opposite.op ((X.homOfLE hWV ≫ V.ι) ⁻¹ᵁ U)) by
    rw [← he]
    exact v)
    (slot_sq_meet_inner M J₁ hWV g₁ hg₁ hg₁' U ef m)

/-- **([SLOT-SQ], the map-level brick)** The tensor-slot construction commutes with the
open-restriction transport: the one genuinely monoidal square of the `ν`-naturality.
Both sides transposed along the two pullback adjunctions and compared on presheaf
elements of `M` at the double-unit image: the `W`-walk (under the one propositional
crossing), the pure-`W` generator-res-compat, and the peeled `V`-walk. -/
theorem pullbackRestrictTransport_tensorIdealSlotIso {V W : X.Opens} (hWV : W ≤ V)
    (g₁ : Γ(X, V)) (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (hgi₁ : IsIso (idealGenHom J₁ V g₁ hg₁))
    (hg₁' : X.presheaf.map (homOfLE hWV).op g₁ ∈ idealSections J₁ (Opposite.op W))
    (hgi₁' : IsIso (idealGenHom J₁ W (X.presheaf.map (homOfLE hWV).op g₁) hg₁')) :
    pullbackRestrictTransport hWV M ≫
        (tensorIdealSlotIso M J₁ W (X.presheaf.map (homOfLE hWV).op g₁)
          hg₁' hgi₁').hom =
      (Scheme.Modules.pullback (X.homOfLE hWV)).map
          (tensorIdealSlotIso M J₁ V g₁ hg₁ hgi₁).hom ≫
        pullbackRestrictTransport hWV
          (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁)) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).homEquiv
    _ _).injective
  apply ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).homEquiv _ _).injective
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  simp only [Adjunction.homEquiv_unit]
  show (tensorIdealSlotIso M J₁ W (X.presheaf.map (homOfLE hWV).op g₁)
      hg₁' hgi₁').hom.val.app
      (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U.unop)))
      ((pullbackRestrictTransport hWV M).val.app
        (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U.unop)))
        (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
          ((Scheme.Modules.pullback V.ι).obj M)).val.app
          (Opposite.op (V.ι ⁻¹ᵁ U.unop))
          (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M).val.app
            U m))) =
    (pullbackRestrictTransport hWV
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
      (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U.unop)))
      (((Scheme.Modules.pullback (X.homOfLE hWV)).map
          (tensorIdealSlotIso M J₁ V g₁ hg₁ hgi₁).hom).val.app
        (Opposite.op ((X.homOfLE hWV) ⁻¹ᵁ (V.ι ⁻¹ᵁ U.unop)))
        (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
          ((Scheme.Modules.pullback V.ι).obj M)).val.app
          (Opposite.op (V.ι ⁻¹ᵁ U.unop))
          (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M).val.app
            U m)))
  have hef : W.ι ⁻¹ᵁ U.unop = W.ι ⁻¹ᵁ (V.ι ''ᵁ (V.ι ⁻¹ᵁ U.unop)) := by
    rw [← X.homOfLE_ι hWV]
    exact congrArg (fun O => (X.homOfLE hWV) ⁻¹ᵁ O)
      (Scheme.Hom.preimage_image_eq V.ι (V.ι ⁻¹ᵁ U.unop)).symm
  exact (slot_sq_lhs M J₁ hWV (X.homOfLE_ι hWV).symm g₁ hg₁' hgi₁' U.unop m).trans
    ((slot_sq_meet_inner_cast M J₁ hWV (X.homOfLE_ι hWV).symm g₁ hg₁ hg₁' U.unop
        hef m).trans
      ((slot_sq_meet_peel M J₁ hWV (X.homOfLE_ι hWV).symm g₁ hg₁ U.unop hef m).trans
        (slot_sq_rhs M J₁ hWV g₁ hg₁ hgi₁ U.unop m)))

/-- **([NR-slot-T])** The slot square at transported `⊤`-sections: the `W`-slot on a
transported section is the transport of the `V`-slot value. `restrictTransportSection`
is definitionally `pullbackRestrictTransport` applied to the re-indexed unit image, so
this is SLOT-SQ evaluated there, with the pulled slot pushed through the two layers. -/
private theorem slot_restrictTransportSection {V W : X.Opens} (hWV : W ≤ V)
    (g₁ : Γ(X, V)) (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (hgi₁ : IsIso (idealGenHom J₁ V g₁ hg₁))
    (hg₁' : X.presheaf.map (homOfLE hWV).op g₁ ∈ idealSections J₁ (Opposite.op W))
    (hgi₁' : IsIso (idealGenHom J₁ W (X.presheaf.map (homOfLE hWV).op g₁) hg₁'))
    (htop : (⊤ : W.toScheme.Opens) = (X.homOfLE hWV) ⁻¹ᵁ (⊤ : V.toScheme.Opens))
    (x : ((Scheme.Modules.pullback V.ι).obj M).val.obj
      (Opposite.op (⊤ : V.toScheme.Opens))) :
    (tensorIdealSlotIso M J₁ W (X.presheaf.map (homOfLE hWV).op g₁)
        hg₁' hgi₁').hom.val.app (Opposite.op (⊤ : W.toScheme.Opens))
        (restrictTransportSection hWV M htop x) =
      restrictTransportSection hWV
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁)) htop
        ((tensorIdealSlotIso M J₁ V g₁ hg₁ hgi₁).hom.val.app
          (Opposite.op (⊤ : V.toScheme.Opens)) x) := by
  -- SLOT-SQ evaluated at the re-indexed unit image
  have hsq := congrArg (fun (q : (Scheme.Modules.pullback (X.homOfLE hWV)).obj
      ((Scheme.Modules.pullback V.ι).obj M) ⟶
      (Scheme.Modules.pullback W.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))) =>
    q.val.app (Opposite.op (⊤ : W.toScheme.Opens))
      (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
          ((Scheme.Modules.pullback V.ι).obj M)).presheaf.map (eqToHom htop).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
          ((Scheme.Modules.pullback V.ι).obj M)).val.app
          (Opposite.op (⊤ : V.toScheme.Opens)) x)))
    (pullbackRestrictTransport_tensorIdealSlotIso M J₁ hWV g₁ hg₁ hgi₁ hg₁' hgi₁')
  refine Eq.trans (show _ = ((pullbackRestrictTransport hWV
      (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
        (Opposite.op (⊤ : W.toScheme.Opens))
        (((Scheme.Modules.pullback (X.homOfLE hWV)).map
            (tensorIdealSlotIso M J₁ V g₁ hg₁ hgi₁).hom).val.app
          (Opposite.op (⊤ : W.toScheme.Opens))
          (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
              ((Scheme.Modules.pullback V.ι).obj M)).presheaf.map
            (eqToHom htop).op
            (((Scheme.Modules.pullbackPushforwardAdjunction
              (X.homOfLE hWV)).unit.app
              ((Scheme.Modules.pullback V.ι).obj M)).val.app
              (Opposite.op (⊤ : V.toScheme.Opens)) x)))) from hsq) ?_
  -- push the pulled slot through the re-index and the unit
  refine congrArg ((pullbackRestrictTransport hWV
    (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁))).val.app
    (Opposite.op (⊤ : W.toScheme.Opens))) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullback (X.homOfLE hWV)).map
      (tensorIdealSlotIso M J₁ V g₁ hg₁ hgi₁).hom).val
    (eqToHom htop).op
    (((Scheme.Modules.pullbackPushforwardAdjunction (X.homOfLE hWV)).unit.app
      ((Scheme.Modules.pullback V.ι).obj M)).val.app
      (Opposite.op (⊤ : V.toScheme.Opens)) x)) ?_
  exact congrArg (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
      ((Scheme.Modules.pullback V.ι).obj
        (tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁)))).presheaf.map
    (eqToHom htop).op)
    (pullbackMap_app_unit (X.homOfLE hWV)
      (tensorIdealSlotIso M J₁ V g₁ hg₁ hgi₁).hom (⊤ : V.toScheme.Opens) x)

/-- **([NR-1], the brick)** The `ν`-comparison map is natural under the open-restriction
transport at `⊤`-sections: evaluating the `W`-level `ν` on a transported `V`-section is
the scheme-restriction of the `V`-level `ν`-value. -/
theorem nuPullback_app_restrictTransport {V W : X.Opens} (hWV : W ≤ V)
    (g₁ : Γ(X, V)) (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (hgi₁ : IsIso (idealGenHom J₁ V g₁ hg₁))
    (hg₁' : X.presheaf.map (homOfLE hWV).op g₁ ∈ idealSections J₁ (Opposite.op W))
    (hgi₁' : IsIso (idealGenHom J₁ W (X.presheaf.map (homOfLE hWV).op g₁) hg₁'))
    (htop : (⊤ : W.toScheme.Opens) = (X.homOfLE hWV) ⁻¹ᵁ (⊤ : V.toScheme.Opens))
    (x : ((Scheme.Modules.pullback V.ι).obj M).val.obj
      (Opposite.op (⊤ : V.toScheme.Opens))) :
    (nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op g₁) hg₁' hgi₁').val.app
        (Opposite.op (⊤ : W.toScheme.Opens))
        (restrictTransportSection hWV M htop x) =
      W.toScheme.presheaf.map (eqToHom htop).op
        ((Scheme.Hom.app (X.homOfLE hWV) (⊤ : V.toScheme.Opens)).hom
          ((nuPullback M J₁ J₂ e V g₁ hg₁ hgi₁).val.app
            (Opposite.op (⊤ : V.toScheme.Opens)) x)) := by
  sorry

/-- **([NR-congr-symm])** The inverse component of `pullbackCongr` at a symmetrised
equation is the hom component at the original equation. -/
theorem pullbackCongr_symm_app_inv {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g)
    (P : Z.Modules) :
    ((Scheme.Modules.pullbackCongr h.symm).app P).inv =
      ((Scheme.Modules.pullbackCongr h).app P).hom := by
  subst h
  rfl

/-- **([NR-1b], the unit-tail)** The unit-cocycle coherence over `W.ι = homOfLE ≫ V.ι`:
the transport followed by the `W`-unit collapse is the pulled `V`-collapse followed by
the `homOfLE`-collapse. Assembly of `pullbackUnitIso_congrLow` and
`pullbackUnitIso_compLow`. -/
theorem pullbackRestrictTransport_unitIso {V W : X.Opens} (hWV : W ≤ V) :
    pullbackRestrictTransport hWV (unitObj X) ≫ (pullbackUnitIso W.ι).hom =
      (Scheme.Modules.pullback (X.homOfLE hWV)).map (pullbackUnitIso V.ι).hom ≫
        (pullbackUnitIso (X.homOfLE hWV)).hom := by
  have hcongr := ModularCurves.pullbackUnitIso_congrLow (X.homOfLE_ι hWV)
  have hcomp := ModularCurves.pullbackUnitIso_compLow (X.homOfLE hWV) V.ι
  calc pullbackRestrictTransport hWV (unitObj X) ≫ (pullbackUnitIso W.ι).hom
      = ((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app (unitObj X)).hom ≫
        (((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV)).app (unitObj X)).hom ≫
          (pullbackUnitIso W.ι).hom) := by
        rw [pullbackRestrictTransport, pullbackCongr_symm_app_inv (X.homOfLE_ι hWV),
          Category.assoc]
    _ = ((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app (unitObj X)).hom ≫
        (pullbackUnitIso (X.homOfLE hWV ≫ V.ι)).hom := by rw [hcongr]
    _ = _ := hcomp

/-- **([NR-endo-1])** The scalar endomorphism of the unit evaluated at the `⊤`-section
`1` returns its defining section. -/
theorem unitEndomorphismOfTopSection_app_top_one {Y : Scheme.{u}}
    (s : Γ(Y, (⊤ : Y.Opens))) :
    (ModularCurves.unitEndomorphismOfTopSection s).val.app
        (Opposite.op (⊤ : Y.Opens))
        (show Y.presheaf.obj (Opposite.op (⊤ : Y.Opens)) from 1) = s := by
  rw [show (ModularCurves.unitEndomorphismOfTopSection s).val.app
      (Opposite.op (⊤ : Y.Opens))
      (show Y.presheaf.obj (Opposite.op (⊤ : Y.Opens)) from 1) =
    (show Y.presheaf.obj (Opposite.op (⊤ : Y.Opens)) from 1) *
      Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op s from
    ModularCurves.unitEndomorphismOfTopSection_app_apply s ⊤ _]
  rw [show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) = 𝟙 (⊤ : Y.Opens) from
    Subsingleton.elim _ _]
  rw [op_id, CategoryTheory.Functor.map_id]
  rw [show (ConcreteCategory.hom (𝟙 (Y.presheaf.obj (Opposite.op (⊤ : Y.Opens))))) s
    = s from rfl]
  exact one_mul s

/-- **([NR-2])** The restricted native trivialisation satisfies the `W`-level
`ν`-characterisation with the restricted second generator. -/
theorem restrictTrivialization_nativeTensorIdealTriv_inv_comp_nu
    {V W : X.Opens} (hWV : W ≤ V)
    (g₁ g₂ : Γ(X, V))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (hgi₁ : IsIso (idealGenHom J₁ V g₁ hg₁))
    (hg₂ : g₂ ∈ idealSections J₂ (Opposite.op V))
    (hgi₂ : IsIso (idealGenHom J₂ V g₂ hg₂))
    (hg₁' : X.presheaf.map (homOfLE hWV).op g₁ ∈ idealSections J₁ (Opposite.op W))
    (hgi₁' : IsIso (idealGenHom J₁ W (X.presheaf.map (homOfLE hWV).op g₁) hg₁')) :
    (restrictTrivialization hWV
        (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂)).inv ≫
      nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op g₁) hg₁' hgi₁' =
      ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op g₂)) := by
  have htop : (⊤ : W.toScheme.Opens) =
      (X.homOfLE hWV) ⁻¹ᵁ (⊤ : V.toScheme.Opens) := by simp
  apply unit_hom_ext
  have hsplit : ((restrictTrivialization hWV
      (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂)).inv ≫
      nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op g₁) hg₁' hgi₁').val.app
        (Opposite.op (⊤ : W.toScheme.Opens))
        (show W.toScheme.presheaf.obj (Opposite.op (⊤ : W.toScheme.Opens)) from 1) =
      (nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op g₁)
        hg₁' hgi₁').val.app (Opposite.op (⊤ : W.toScheme.Opens))
        ((restrictTrivialization hWV
          (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂)).inv.val.app
          (Opposite.op (⊤ : W.toScheme.Opens))
          (show W.toScheme.presheaf.obj
            (Opposite.op (⊤ : W.toScheme.Opens)) from 1)) := rfl
  refine hsplit.trans ?_
  have h2 := restrictTrivialization_inv_app_top_one hWV
    (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂) htop
  rw [h2]
  have hfold : ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app M).inv.val.app
      (Opposite.op (⊤ : W.toScheme.Opens))
      (((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app M).hom.val.app
        (Opposite.op (⊤ : W.toScheme.Opens))
        (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
            ((Scheme.Modules.pullback V.ι).obj M)).presheaf.map (eqToHom htop).op
          (((Scheme.Modules.pullbackPushforwardAdjunction
              (X.homOfLE hWV)).unit.app
            ((Scheme.Modules.pullback V.ι).obj M)).val.app
            (Opposite.op (⊤ : V.toScheme.Opens))
            ((nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂
              hg₁ hgi₁ hg₂ hgi₂).inv.val.app
              (Opposite.op (⊤ : V.toScheme.Opens))
              (show V.toScheme.presheaf.obj
                (Opposite.op (⊤ : V.toScheme.Opens)) from 1))))) =
      restrictTransportSection hWV M htop
        ((nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂).inv.val.app
          (Opposite.op (⊤ : V.toScheme.Opens))
          (show V.toScheme.presheaf.obj
            (Opposite.op (⊤ : V.toScheme.Opens)) from 1)) := rfl
  rw [hfold]
  rw [nuPullback_app_restrictTransport M J₁ J₂ e hWV g₁ hg₁ hgi₁ hg₁' hgi₁' htop _]
  have hV : (nuPullback M J₁ J₂ e V g₁ hg₁ hgi₁).val.app
      (Opposite.op (⊤ : V.toScheme.Opens))
      ((nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂).inv.val.app
        (Opposite.op (⊤ : V.toScheme.Opens))
        (show V.toScheme.presheaf.obj
          (Opposite.op (⊤ : V.toScheme.Opens)) from 1)) =
      Scheme.Modules.openTopSection V g₂ := by
    have hVcomp := congrArg
      (fun (q : (Scheme.Modules.pullback V.ι).obj M ⟶ unitObj V.toScheme) =>
        q.val.app (Opposite.op (⊤ : V.toScheme.Opens))
        ((nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂).inv.val.app
          (Opposite.op (⊤ : V.toScheme.Opens))
          (show V.toScheme.presheaf.obj
            (Opposite.op (⊤ : V.toScheme.Opens)) from 1)))
      (rfl : nuPullback M J₁ J₂ e V g₁ hg₁ hgi₁ = nuPullback M J₁ J₂ e V g₁ hg₁ hgi₁)
    refine Eq.trans ?_ (unitEndomorphismOfTopSection_app_top_one
      (Scheme.Modules.openTopSection V g₂))
    have hVeq := congrArg
      (fun (q : unitObj V.toScheme ⟶ unitObj V.toScheme) => q.val.app
        (Opposite.op (⊤ : V.toScheme.Opens))
        (show V.toScheme.presheaf.obj
          (Opposite.op (⊤ : V.toScheme.Opens)) from 1))
      (nativeTensorIdealTriv_inv_comp_nu M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂)
    exact hVeq
  rw [hV]
  rw [openTopSection_homOfLE hWV htop g₂]
  exact (unitEndomorphismOfTopSection_app_top_one (Y := W.toScheme)
    (Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op g₂))).symm

/-- **([NR-3], NAT-RESTRICT)** The restriction of the native tensor-ideal trivialisation
is the native trivialisation of the restricted generators. -/
theorem restrictTrivialization_nativeTensorIdealTriv
    {V W : X.Opens} (hWV : W ≤ V)
    (g₁ g₂ : Γ(X, V))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (hgi₁ : IsIso (idealGenHom J₁ V g₁ hg₁))
    (hg₂ : g₂ ∈ idealSections J₂ (Opposite.op V))
    (hgi₂ : IsIso (idealGenHom J₂ V g₂ hg₂))
    (hg₁' : X.presheaf.map (homOfLE hWV).op g₁ ∈ idealSections J₁ (Opposite.op W))
    (hgi₁' : IsIso (idealGenHom J₁ W (X.presheaf.map (homOfLE hWV).op g₁) hg₁'))
    (hg₂' : X.presheaf.map (homOfLE hWV).op g₂ ∈ idealSections J₂ (Opposite.op W))
    (hgi₂' : IsIso (idealGenHom J₂ W (X.presheaf.map (homOfLE hWV).op g₂) hg₂'))
    (hmono : Mono (ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op g₂)))) :
    restrictTrivialization hWV
        (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂) =
      nativeTensorIdealTriv M J₁ J₂ e W
        (X.presheaf.map (homOfLE hWV).op g₁) (X.presheaf.map (homOfLE hWV).op g₂)
        hg₁' hgi₁' hg₂' hgi₂' := by
  have h₁ := restrictTrivialization_nativeTensorIdealTriv_inv_comp_nu M J₁ J₂ e hWV
    g₁ g₂ hg₁ hgi₁ hg₂ hgi₂ hg₁' hgi₁'
  have h₂ := nativeTensorIdealTriv_inv_comp_nu M J₁ J₂ e W
    (X.presheaf.map (homOfLE hWV).op g₁) (X.presheaf.map (homOfLE hWV).op g₂)
    hg₁' hgi₁' hg₂' hgi₂'
  have hread := pullbackTrivialization_inv_comp_hom_of_nu M
    (restrictTrivialization hWV
      (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂))
    (nativeTensorIdealTriv M J₁ J₂ e W
      (X.presheaf.map (homOfLE hWV).op g₁) (X.presheaf.map (homOfLE hWV).op g₂)
      hg₁' hgi₁' hg₂' hgi₂')
    (nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op g₁) hg₁' hgi₁')
    (X.presheaf.map (homOfLE hWV).op g₂) (X.presheaf.map (homOfLE hWV).op g₂) 1
    h₁ h₂ (one_mul _).symm hmono
  have hone : ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection W
        (1 : Γ(X, W))) = 𝟙 (unitObj W.toScheme) := by
    have h1 : Scheme.Modules.openTopSection W (1 : Γ(X, W)) =
        (1 : Γ(W.toScheme, ⊤)) := by
      simp [Scheme.Modules.openTopSection, map_one]
    rw [h1]
    exact ModularCurves.unitEndomorphismOfTopSection_one
  rw [hone] at hread
  have hhom : (nativeTensorIdealTriv M J₁ J₂ e W
      (X.presheaf.map (homOfLE hWV).op g₁) (X.presheaf.map (homOfLE hWV).op g₂)
      hg₁' hgi₁' hg₂' hgi₂').hom =
      (restrictTrivialization hWV
        (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂)).hom := by
    calc (nativeTensorIdealTriv M J₁ J₂ e W _ _ hg₁' hgi₁' hg₂' hgi₂').hom
        = (restrictTrivialization hWV
            (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂)).hom ≫
          (restrictTrivialization hWV
            (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂)).inv ≫
          (nativeTensorIdealTriv M J₁ J₂ e W _ _ hg₁' hgi₁' hg₂' hgi₂').hom := by
          rw [Iso.hom_inv_id_assoc]
      _ = _ := by rw [hread, Category.comp_id]
  exact (Iso.ext hhom.symm)

end NativeRestriction

end ModularCurves
