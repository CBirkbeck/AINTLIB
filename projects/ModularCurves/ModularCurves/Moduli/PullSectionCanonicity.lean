/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Moduli.PullSectionAdd
import ModularCurves.EllipticCurve.RigiditySpreadingOut
import ModularCurves.EllipticCurve.RecordGroupUnique

/-!
# The T-E4 transport, reduced to the single canonicity primitive (Y1-D2)

`Moduli.PullSectionAdd` proves section-pullback additivity (`transportSection_add`,
`pullSection_add_of_isLocallyNoetherian`) over **locally noetherian** bases only, because it
invokes `isMonHom_of_one_comp_eq'` (GIT Cor 6.4, T-W7.7) — which currently carries
`[IsLocallyNoetherian S]`. The whole T-E4 family (unrestricted `pullSection_add`, the
`Γ₁`/`Γ(N)` naive functor-law memberships, and the Y₁(N) transport `Y1-D2`) inherits that
noetherian restriction — but **only through that one call**.

This file isolates the dependency. Reading `transportSection_add`'s proof, the base's
noetherianness is used **exclusively** to produce the group-homomorphism equation `h64` for
the comparison isomorphism `curveIsoPullbackOver`; everything downstream is noetherian-free
group algebra. So:

* `transportSection_add_of_isMonHom` takes that group-hom equation as a **hypothesis** and
  proves transport additivity **sorry-free, over an arbitrary base**. This is the single
  "one transport proof" that closes the whole family.

The hypothesis is supplied three ways, all feeding the *same* lemma:
* `isMonHom_of_one_comp_eq'` (`Rigidity.lean`, noetherian) — recovers the existing
  `pullSection_add_of_isLocallyNoetherian`;
* `isMonHom_of_one_comp_eq'_of_finitePresentation` (`RigiditySpreadingOut.lean`, **route (a)**,
  T-W7.8) — gives the arbitrary-base result the moment route (a) lands;
* the explicit base-change-natural group law (**route (c)**, c5β's endgame `mulModelHom` →
  `T-W7a`) — same, the moment the endgame lands.

So the entire T-E4 family is now **collapsed to the single primitive
`isMonHom_of_one_comp_eq'_of_finitePresentation`** (arbitrary-base GIT Cor 6.4), which lands
via route (a) or route (c).

## Holder wiring note (T-E4-family, [Y1-D2])

The standalone lemmas here (all over an **arbitrary** base) let the holders close their
parked/`sorry`'d transport gates. Every one bottoms out at the *single* primitive
`isMonHom_of_one_comp_eq'_of_finitePresentation`, so all go axiom-clean the moment route (a)
(this repo's `RigiditySpreadingOut.lean`) *or* route (c) (c5β's endgame `T-W7a`) lands.

* **`Moduli/Representability.lean` holder** — `EllHom.pullSection_add` (the parked `:= by sorry`,
  ~L207): replace with `EllHom.pullSection_add_of_finitePresentation R f P Q`. The two functor-law
  memberships `gammaOneNaiveProblem.map` / `gammaFullNaiveProblem.map` (~L214/L229) then close: the
  `(N : ℤ) • P = 0` killing clause transports by `pullSection_add_of_finitePresentation` +
  `pullSection_zsmul_of_finitePresentation`; the fibrewise `Point.pull` clauses transport barehanded
  (pull commutes with `pullSection`, no group data). `pullSection_zsmul` (GammaHRepresentability, and
  hence `pullAlong_glSmul`/GH) can drop its `pullSection_add` hypothesis onto the FP version.
* **`ModularCurve/YOneAssembly.lean` ([Y1-D2], NEW-Y1)** — `isNaiveGammaOne_pullSection_iff` closes
  the same way: the killing clause via the two FP `pullSection` lemmas above; the fibrewise clauses
  (`(N:ℤ) • Point.pull … = 0`, exact-order-`N`) barehanded via pull/`pullSection` compatibility. Do
  **not** shared-edit — this note is the coordination; assemble in your own file/PR.
* **Coordination (attack-1, no duplication):** the canonicity transport is proved *once* — here, in
  `transportSection_add_of_isMonHom` (sorry-free) — and everything above consumes it. Do not re-derive
  the group-iso transport in the holder files.

## References

* Loeffler, §3.3/§3.7/§3.8 (the `Ell/R`-presheaf functor laws).
* Katz–Mazur, 2.1.2 / 3.2 (canonicity of the group law; naive level structures).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

universe u

namespace ModularCurves

namespace EllHom

variable (R : CommRingCat.{u}) {X Y : EllObj R} (f : X ⟶ Y)

/-- **(T-E4a, the one transport proof — sorry-free, arbitrary base)** Transport of sections
along the pointed comparison isomorphism is additive, **given** that the comparison morphism
`curveIsoPullbackOver` is a homomorphism of the two independent group structures (the
equation `h64`). This is the noetherian-free core of `transportSection_add`: the base's
noetherianness in that lemma is used *only* to produce `h64` (via `isMonHom_of_one_comp_eq'`).
Supplying `h64` from the arbitrary-base canonicity (route (a)/(c)) removes the restriction. -/
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

/-- The comparison morphism is unit-compatible (noetherian-free). Extracted from
`transportSection_add`'s internal `hη`. -/
lemma curveIsoPullbackOver_one :
    η[X.curve.asOver] ≫ curveIsoPullbackOver R f
      = η[(Y.curve.baseChange f.baseHom).asOver] := by
  apply Over.OverMorphism.ext
  show (η[X.curve.asOver] : _ ⟶ X.curve.asOver).left ≫ (curveIsoPullback R f).hom = _
  exact (congrArg (· ≫ (curveIsoPullback R f).hom) X.curve.one_eq_zero).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((𝟙_ (Over X.base)).hom ≫ ·) (zero_curveIsoPullback R f)).trans <|
    (Y.curve.baseChange f.baseHom).one_eq_zero.symm

/-- **(T-E4a over an arbitrary base — now unconditional)**
Transport additivity, with the group-hom equation supplied by the arbitrary-base
records-level canonicity primitive `isMonHom_of_pointedIso_records`
(`RecordGroupUnique.lean`): the pointed comparison isomorphism onto the pullback is
automatically a homomorphism of the two group structures, so no finite-presentation or
noetherian hypothesis on the base is needed. (The name is retained for its consumers; the
finite-presentation route (a), `isMonHom_of_one_comp_eq'_of_finitePresentation`, is no
longer used here.) -/
theorem transportSection_add_of_finitePresentation (s s' : X.curve.Section) :
    transportSection R f (s + s')
      = transportSection R f s + transportSection R f s' :=
  transportSection_add_of_isMonHom R f
    (isMonHom_of_pointedIso_records X.curve (Y.curve.baseChange f.baseHom)
      (Over.isoMk (curveIsoPullback R f) f.isPullback.isoPullback_hom_snd)
      (curveIsoPullbackOver_one R f)) s s'

/-- **(T-E4a, `pullSection_add` over an arbitrary base)** Section-pullback is additive over an
arbitrary base — the unrestricted statement, modulo the single route (a)/(c) canonicity
primitive. Same proof as `pullSection_add_of_isLocallyNoetherian` but routed through
`transportSection_add_of_finitePresentation`, so the only remaining dependency is the
arbitrary-base GIT Cor 6.4 (not `[IsLocallyNoetherian]`). -/
theorem pullSection_add_of_finitePresentation (P Q : Y.curve.Section) :
    EllHom.pullSection R f (P + Q)
      = EllHom.pullSection R f P + EllHom.pullSection R f Q := by
  apply transportSection_injective R f
  rw [transportSection_add_of_finitePresentation]
  apply (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom (𝟙 X.base)).injective
  rw [map_add, dict_transportSection_pullSection, dict_transportSection_pullSection,
    dict_transportSection_pullSection, EllipticCurve.Point.pull_add]

/-- **(T-E4a, `pullSection_zsmul` over an arbitrary base)** `ℤ`-linearity of section-pullback
over an arbitrary base, from `pullSection_add_of_finitePresentation` via `map_zsmul`. Mirrors
`EllHom.pullSection_zsmul` (which assumes the noetherian/parked `pullSection_add`). Transports
the `(N : ℤ) • P = 0` killing clause of `IsNaiveGammaOne`/`IsNaiveFullLevel`. -/
theorem pullSection_zsmul_of_finitePresentation (n : ℤ) (P : Y.curve.Section) :
    EllHom.pullSection R f (n • P) = n • EllHom.pullSection R f P :=
  map_zsmul (AddMonoidHom.mk' (EllHom.pullSection R f)
    (pullSection_add_of_finitePresentation R f)) n P

end EllHom

end ModularCurves
