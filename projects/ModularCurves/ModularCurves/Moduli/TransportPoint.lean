/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Moduli.PullSectionCanonicity
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Fibre-point transport along an `Ell/R`-morphism (Y(N) D-track, [YF-D-MAP])

`Moduli/PullSectionCanonicity` transports **sections** (points over `𝟙 X.base`) along the
cartesian-square comparison isomorphism `curveIsoPullback`. The naive full-level moduli map
needs the same transport for **arbitrary fibre points** `x : X.curve.Point t` (its fibrewise
clause quantifies over all `N`-torsion points, not just the pulled sections) — so this file
provides `transportPoint`, the point-level analogue, and its additivity (the same
`isMonHom_of_pointedIso_records` group-hom equation, base-independent).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace ModularCurves

namespace EllHom

variable (R : CommRingCat.{u}) {X Y : EllObj R} (f : X ⟶ Y)

/-- Transport of a fibre point along the cartesian-square comparison isomorphism: post-compose
the underlying morphism with `curveIsoPullback`. -/
noncomputable def transportPoint {T : Scheme.{u}} (t : T ⟶ X.base) (x : X.curve.Point t) :
    (Y.curve.baseChange f.baseHom).Point t :=
  ⟨x.1 ≫ (curveIsoPullback R f).hom,
    (Category.assoc _ _ _).trans <|
      (congrArg (x.1 ≫ ·) f.isPullback.isoPullback_hom_snd).trans x.2⟩

@[simp]
lemma transportPoint_coe {T : Scheme.{u}} (t : T ⟶ X.base) (x : X.curve.Point t) :
    (transportPoint R f t x).1 = x.1 ≫ (curveIsoPullback R f).hom := rfl

/-- `transportPoint` is additive — the point-level analogue of
`transportSection_add_of_isMonHom`, over an arbitrary base `t`, from the same base-independent
group-hom equation. -/
lemma transportPoint_add {T : Scheme.{u}} (t : T ⟶ X.base) (x x' : X.curve.Point t) :
    transportPoint R f t (x + x') = transportPoint R f t x + transportPoint R f t x' := by
  have h64 := isMonHom_of_pointedIso_records X.curve (Y.curve.baseChange f.baseHom)
    (Over.isoMk (curveIsoPullback R f) f.isPullback.isoPullback_hom_snd)
    (curveIsoPullbackOver_one R f)
  have h64l : (μ[X.curve.asOver]).left ≫ (curveIsoPullback R f).hom
      = (MonoidalCategory.tensorHom (curveIsoPullbackOver R f)
          (curveIsoPullbackOver R f)).left
        ≫ (μ[(Y.curve.baseChange f.baseHom).asOver]).left :=
    ((Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left h64)).trans
      (Over.comp_left _ _ _ _ _)
  have hcs : X.curve.pointEquivOverHom t x ≫ curveIsoPullbackOver R f
      = (Y.curve.baseChange f.baseHom).pointEquivOverHom t (transportPoint R f t x) :=
    Over.OverMorphism.ext rfl
  have hcs' : X.curve.pointEquivOverHom t x' ≫ curveIsoPullbackOver R f
      = (Y.curve.baseChange f.baseHom).pointEquivOverHom t (transportPoint R f t x') :=
    Over.OverMorphism.ext rfl
  refine Subtype.ext ?_
  have hx : (x + x').1
      = (lift (X.curve.pointEquivOverHom t x) (X.curve.pointEquivOverHom t x')).left
        ≫ (μ[X.curve.asOver]).left :=
    (congrArg CommaMorphism.left (X.curve.pointEquivOverHom_add t x x')).trans
      (Over.comp_left _ _ _ _ _)
  have hR : (transportPoint R f t x + transportPoint R f t x').1
      = (lift ((Y.curve.baseChange f.baseHom).pointEquivOverHom t (transportPoint R f t x))
          ((Y.curve.baseChange f.baseHom).pointEquivOverHom t (transportPoint R f t x'))).left
        ≫ (μ[(Y.curve.baseChange f.baseHom).asOver]).left :=
    (congrArg CommaMorphism.left
      ((Y.curve.baseChange f.baseHom).pointEquivOverHom_add t _ _)).trans
      (Over.comp_left _ _ _ _ _)
  show (x + x').1 ≫ (curveIsoPullback R f).hom = _
  rw [hR]
  exact (congrArg (· ≫ (curveIsoPullback R f).hom) hx).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((lift (X.curve.pointEquivOverHom t x)
        (X.curve.pointEquivOverHom t x')).left ≫ ·) h64l).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (μ[(Y.curve.baseChange f.baseHom).asOver]).left)
      ((Over.comp_left _ _ _ _ _).symm.trans
        (congrArg CommaMorphism.left
          ((lift_map _ _ _ _).trans (congrArg₂ lift hcs hcs')))))

/-- The inverse comparison is over the base of the base-changed curve. -/
lemma curveIsoPullback_inv_π :
    (curveIsoPullback R f).inv ≫ X.curve.π = (Y.curve.baseChange f.baseHom).π := by
  rw [Iso.inv_comp_eq]
  exact f.isPullback.isoPullback_hom_snd.symm

/-- The inverse fibre transport: post-compose with `curveIsoPullback.inv`. -/
noncomputable def transportPointInv {T : Scheme.{u}} (t : T ⟶ X.base)
    (y : (Y.curve.baseChange f.baseHom).Point t) : X.curve.Point t :=
  ⟨y.1 ≫ (curveIsoPullback R f).inv,
    (Category.assoc _ _ _).trans <|
      (congrArg (y.1 ≫ ·) (curveIsoPullback_inv_π R f)).trans y.2⟩

/-- `transportPoint` packaged as an additive equivalence of fibre point groups. -/
noncomputable def transportPointEquiv {T : Scheme.{u}} (t : T ⟶ X.base) :
    X.curve.Point t ≃+ (Y.curve.baseChange f.baseHom).Point t where
  toFun := transportPoint R f t
  invFun := transportPointInv R f t
  left_inv x := Subtype.ext <|
    (congrArg (· ≫ (curveIsoPullback R f).inv) (transportPoint_coe R f t x)).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (x.1 ≫ ·) (curveIsoPullback R f).hom_inv_id).trans (Category.comp_id _)
  right_inv y := Subtype.ext <|
    (congrArg (· ≫ (curveIsoPullback R f).hom)
        (rfl : (transportPointInv R f t y).1 = y.1 ≫ (curveIsoPullback R f).inv)).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (y.1 ≫ ·) (curveIsoPullback R f).inv_hom_id).trans (Category.comp_id _)
  map_add' := transportPoint_add R f t

@[simp]
lemma transportPointEquiv_apply {T : Scheme.{u}} (t : T ⟶ X.base) (x : X.curve.Point t) :
    transportPointEquiv R f t x = transportPoint R f t x := rfl

/-- **The transport dictionary.** `transportPoint` sends the fibre restriction of a pulled
section to the fibre restriction of the base-changed section — reducing to the section-level
`transportSection_pullSection`. -/
lemma transportPoint_pull_pullSection {T : Scheme.{u}} (t : T ⟶ X.base) (P : Y.curve.Section) :
    transportPoint R f t (EllipticCurve.Point.pull X.curve t (EllHom.pullSection R f P))
      = EllipticCurve.Point.pull (Y.curve.baseChange f.baseHom) t
          (EllipticCurve.Point.asSection Y.curve f.baseHom
            (EllipticCurve.Point.pull Y.curve f.baseHom P)) := by
  refine Subtype.ext ?_
  rw [transportPoint_coe]
  show (t ≫ (EllHom.pullSection R f P).1) ≫ (curveIsoPullback R f).hom
      = t ≫ (EllipticCurve.Point.asSection Y.curve f.baseHom
          (EllipticCurve.Point.pull Y.curve f.baseHom P)).1
  rw [Category.assoc,
    show (EllHom.pullSection R f P).1 ≫ (curveIsoPullback R f).hom
      = (transportSection R f (EllHom.pullSection R f P)).1 from rfl,
    transportSection_pullSection, EllipticCurve.Point.asSection_coe]
  rfl

end EllHom

/-- An additive equivalence transports subgroup-closure membership: `e x` lies in the closure of
the image `e '' s` iff `x` lies in the closure of `s`. -/
lemma AddEquiv.mem_closure_image {G H : Type*} [AddGroup G] [AddGroup H] (e : G ≃+ H)
    (s : Set G) (x : G) :
    e x ∈ AddSubgroup.closure (e '' s) ↔ x ∈ AddSubgroup.closure s := by
  rw [show (e '' s) = (e.toAddMonoidHom '' s) from rfl,
    ← AddMonoidHom.map_closure e.toAddMonoidHom s, AddSubgroup.mem_map_equiv,
    AddEquiv.symm_apply_apply]

end ModularCurves
