/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.Representability
import ModularCurves.EllipticCurve.Rigidity

/-!
# Additivity of section-pullback over locally noetherian bases (T-E4a-noeth)

`EllHom.pullSection_add_of_isLocallyNoetherian`: pulling sections back along an `Ell/R`
morphism `f : X ⟶ Y` is additive, provided `X.base` is locally noetherian.

This is GME Cor 2.2.5 made effective through the canonicity chain: the cartesian square of
`f` gives a pointed isomorphism from `X.curve.E` onto the chosen pullback — the total
space of `(Y.curve).baseChange f.baseHom` — and `isMonHom_of_one_comp_eq'` (GIT Cor 6.4
over a locally noetherian base, T-W7.7) makes that isomorphism a homomorphism of the two
independent group structures. The base-changed side is additive by the T-H2b dictionary
(`Point.baseChangeEquiv`) and `Point.pull_add`, and injectivity of the transport closes.

The unrestricted statement (`EllHom.pullSection_add`, Representability.lean) stays parked
behind the arbitrary-base canonicity upgrade T-W7.8 per the owner decision (2026-07-08):
`EllObj R` keeps arbitrary bases.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

universe u

namespace ModularCurves

namespace EllHom

variable (R : CommRingCat.{u}) {X Y : EllObj R} (f : X ⟶ Y)

/-- The comparison isomorphism from the total space of `X.curve` onto the total space of
the base change of `Y.curve` along `f.baseHom`, from the cartesian square of `f`. -/
noncomputable def curveIsoPullback : X.curve.E ≅ pullback Y.curve.π f.baseHom :=
  f.isPullback.isoPullback

/-- The comparison isomorphism is pointed. -/
lemma zero_curveIsoPullback :
    X.curve.zero ≫ (curveIsoPullback R f).hom = (Y.curve.baseChange f.baseHom).zero := by
  -- Term mode throughout: `EllipticCurve.baseChange` is semireducible, so the right-hand side
  -- is only defeq — not syntactically equal — to a `pullback.lift`, and `rw` cannot see it.
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (X.curve.zero ≫ ·) (f.isPullback.isoPullback_hom_fst)).trans <|
      f.zero_w.trans (pullback.lift_fst _ _ _).symm
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (X.curve.zero ≫ ·) (f.isPullback.isoPullback_hom_snd)).trans <|
      X.curve.zero_π.trans (pullback.lift_snd _ _ _).symm

/-- The comparison isomorphism as a morphism over the base. -/
noncomputable def curveIsoPullbackOver :
    X.curve.asOver ⟶ (Y.curve.baseChange f.baseHom).asOver :=
  Over.homMk (curveIsoPullback R f).hom (f.isPullback.isoPullback_hom_snd)

/-- The transport of sections along the comparison isomorphism. -/
noncomputable def transportSection (s : X.curve.Section) :
    (Y.curve.baseChange f.baseHom).Section :=
  ⟨s.1 ≫ (curveIsoPullback R f).hom,
    (Category.assoc _ _ _).trans <|
      (congrArg (s.1 ≫ ·) (f.isPullback.isoPullback_hom_snd)).trans s.2⟩

/-- Transport along the comparison isomorphism is injective (it is composition with an iso). -/
lemma transportSection_injective : Function.Injective (transportSection R f) := fun _ _ h =>
  Subtype.ext <| (cancel_mono (curveIsoPullback R f).hom).mp (congrArg Subtype.val h)

/-- The transport of a pulled section is the base-changed pullback section. -/
lemma transportSection_pullSection (P : Y.curve.Section) :
    (transportSection R f (pullSection R f P)).1
      = pullback.lift (f.baseHom ≫ P.1) (𝟙 X.base)
          (by rw [Category.assoc, P.2, Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans <|
      (congrArg ((pullSection R f P).1 ≫ ·) (f.isPullback.isoPullback_hom_fst)).trans <|
      (f.isPullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
  · exact (Category.assoc _ _ _).trans <|
      (congrArg ((pullSection R f P).1 ≫ ·) (f.isPullback.isoPullback_hom_snd)).trans <|
      (f.isPullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm

/-- The dictionary image of a transported pullback section is the plain pullback of the
section along the composite. -/
lemma dict_transportSection_pullSection (P : Y.curve.Section) :
    EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom (𝟙 X.base)
        (transportSection R f (pullSection R f P))
      = EllipticCurve.Point.pull Y.curve (𝟙 X.base ≫ f.baseHom) P := by
  refine Subtype.ext ?_
  show (transportSection R f (pullSection R f P)).1
      ≫ pullback.fst Y.curve.π f.baseHom = _
  rw [transportSection_pullSection]
  exact (pullback.lift_fst _ _ _).trans
    (congrArg (· ≫ P.1) (Category.id_comp f.baseHom)).symm

/-- The comparison morphism is unit-compatible: it carries `X.curve`'s unit to the
base-changed curve's unit. No hypothesis on the base. -/
lemma curveIsoPullbackOver_one :
    η[X.curve.asOver] ≫ curveIsoPullbackOver R f
      = η[(Y.curve.baseChange f.baseHom).asOver] := by
  apply Over.OverMorphism.ext
  show (η[X.curve.asOver] : _ ⟶ X.curve.asOver).left ≫ (curveIsoPullback R f).hom = _
  exact (congrArg (· ≫ (curveIsoPullback R f).hom) X.curve.one_eq_zero).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((𝟙_ (Over X.base)).hom ≫ ·) (zero_curveIsoPullback R f)).trans <|
    (Y.curve.baseChange f.baseHom).one_eq_zero.symm

/-- **(GME Cor 2.2.5, the noetherian-free core)** Transport along the pointed comparison
isomorphism is additive **given** that the comparison morphism is a homomorphism of the two
independent group structures (the equation `h64`). Everything here is group algebra: the
base plays no role. The canonicity chain enters only when `h64` is supplied — over a locally
noetherian base by `isMonHom_of_one_comp_eq'` (`transportSection_add` below), over an
arbitrary base by the finite-presentation route (`Moduli/PullSectionCanonicity.lean`). -/
lemma transportSection_add_of_isMonHom
    (h64 : μ[X.curve.asOver] ≫ curveIsoPullbackOver R f
        = MonoidalCategory.tensorHom (curveIsoPullbackOver R f) (curveIsoPullbackOver R f)
          ≫ μ[(Y.curve.baseChange f.baseHom).asOver])
    (s s' : X.curve.Section) :
    transportSection R f (s + s')
      = transportSection R f s + transportSection R f s' := by
  have h64l : (μ[X.curve.asOver]).left ≫ (curveIsoPullback R f).hom
      = (MonoidalCategory.tensorHom (curveIsoPullbackOver R f)
          (curveIsoPullbackOver R f)).left
        ≫ (μ[(Y.curve.baseChange f.baseHom).asOver]).left :=
    ((Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left h64)).trans
      (Over.comp_left _ _ _ _ _)
  have hcs : X.curve.pointEquivOverHom (𝟙 X.base) s ≫ curveIsoPullbackOver R f
      = (Y.curve.baseChange f.baseHom).pointEquivOverHom (𝟙 X.base)
          (transportSection R f s) :=
    Over.OverMorphism.ext rfl
  have hcs' : X.curve.pointEquivOverHom (𝟙 X.base) s' ≫ curveIsoPullbackOver R f
      = (Y.curve.baseChange f.baseHom).pointEquivOverHom (𝟙 X.base)
          (transportSection R f s') :=
    Over.OverMorphism.ext rfl
  refine Subtype.ext ?_
  have hx : (s + s').1
      = (lift (X.curve.pointEquivOverHom (𝟙 X.base) s)
          (X.curve.pointEquivOverHom (𝟙 X.base) s')).left
        ≫ (μ[X.curve.asOver]).left :=
    (congrArg CommaMorphism.left (X.curve.pointEquivOverHom_add (𝟙 X.base) s s')).trans
      (Over.comp_left _ _ _ _ _)
  have hR : (transportSection R f s + transportSection R f s').1
      = (lift ((Y.curve.baseChange f.baseHom).pointEquivOverHom (𝟙 X.base)
            (transportSection R f s))
          ((Y.curve.baseChange f.baseHom).pointEquivOverHom (𝟙 X.base)
            (transportSection R f s'))).left
        ≫ (μ[(Y.curve.baseChange f.baseHom).asOver]).left :=
    (congrArg CommaMorphism.left
      ((Y.curve.baseChange f.baseHom).pointEquivOverHom_add (𝟙 X.base) _ _)).trans
      (Over.comp_left _ _ _ _ _)
  show (s + s').1 ≫ (curveIsoPullback R f).hom = _
  rw [hR]
  exact (congrArg (· ≫ (curveIsoPullback R f).hom) hx).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((lift (X.curve.pointEquivOverHom (𝟙 X.base) s)
        (X.curve.pointEquivOverHom (𝟙 X.base) s')).left ≫ ·) h64l).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (μ[(Y.curve.baseChange f.baseHom).asOver]).left)
      ((Over.comp_left _ _ _ _ _).symm.trans
        (congrArg CommaMorphism.left
          ((lift_map _ _ _ _).trans
            (congrArg₂ lift hcs hcs')))))

/-- **(GME Cor 2.2.5 over a locally noetherian base)** The transport along the pointed
comparison isomorphism is additive: the two independent group structures correspond, by
the canonicity chain (`isMonHom_of_one_comp_eq'`, GIT Cor 6.4). -/
lemma transportSection_add [IsLocallyNoetherian X.base] (s s' : X.curve.Section) :
    transportSection R f (s + s')
      = transportSection R f s + transportSection R f s' := by
  haveI : Smooth X.curve.π := SmoothOfRelativeDimension.smooth (n := 1) (f := X.curve.π)
  haveI : IsProper X.curve.asOver.hom := inferInstanceAs (IsProper X.curve.π)
  haveI : Flat X.curve.asOver.hom := inferInstanceAs (Flat X.curve.π)
  haveI : IsSeparated (Y.curve.baseChange f.baseHom).asOver.hom :=
    inferInstanceAs (IsSeparated (Y.curve.baseChange f.baseHom).π)
  exact transportSection_add_of_isMonHom R f
    (isMonHom_of_one_comp_eq' (A := X.curve.asOver)
      (G := (Y.curve.baseChange f.baseHom).asOver)
      X.curve.toEllipticCurveGeom.universallyOConnected (curveIsoPullbackOver R f)
      (curveIsoPullbackOver_one R f)) s s'

/-- **(T-E4a-noeth)** Section-pullback along an `Ell/R` morphism is additive when the
source base is locally noetherian: GME Cor 2.2.5 through the T-W7.7 canonicity chain.
The unrestricted `pullSection_add` stays parked behind T-W7.8 (owner decision
2026-07-08: `EllObj R` keeps arbitrary bases). -/
theorem pullSection_add_of_isLocallyNoetherian [IsLocallyNoetherian X.base]
    (P Q : Y.curve.Section) :
    pullSection R f (P + Q)
      = pullSection R f P + pullSection R f Q := by
  apply transportSection_injective R f
  rw [transportSection_add]
  apply (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom (𝟙 X.base)).injective
  rw [map_add, dict_transportSection_pullSection, dict_transportSection_pullSection,
    dict_transportSection_pullSection, EllipticCurve.Point.pull_add]

end EllHom

end ModularCurves
