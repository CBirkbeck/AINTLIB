/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.LegendreDeltaRelRep
import ModularCurves.Moduli.LegendreDatumSymmetry
import ModularCurves.Moduli.AbscissaDifference
import ModularCurves.Moduli.LevelMarking
import ModularCurves.GroupScheme.SqrtUnitCover
import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# The `±ω` scale-torsor: gluing the square-root cover over the level-`2` locus (T-E14-AX2)

**(CHARTER-G, the terminal (G1) increment.)** This file assembles the finite étale
**scale-torsor** `Z₂ → fullLevelLocus 2` feeding the funnel
`legendreDelta_relRep_finiteEtale_of_scaleTorsor` (`Moduli/LegendreDeltaRelRep.lean`),
thereby closing `legendreDelta_relativelyRepresentable_finiteEtale`
(`Moduli/Bootstrap.lean`, KM 4.6.2's engine axiom 2 for the Legendre `δ`).

## Mathematical picture

Over `W := fullLevelLocus 2` of the universal curve, the tautological naive full
level-`2` pair `(P, Q)` is fibrewise nonzero (`pull_ne_zero_left/right_of_isNaiveFullLevel`),
so OMEGA's canonical `ω^{⊗-2}`-valued **abscissa difference** `d = x(Q) − x(P)`
(`abscissaDiff`, `Moduli/AbscissaDifference.lean`) is defined; over an atlas chart in
which `ω` is trivialized by a basis `b`, `d` trivializes to a unit `d_b ∈ Γ(W, V)ˣ`, and
`(L, b)` is a Legendre datum iff `d_b = 1` (the marking pins `x(P) = 0, x(Q) = 1`).

The `±ω` bases completing `(P, Q)` to a Legendre datum are hence the square roots
`u² = d_b⁻¹` of the twist relating two chart trivializations
(`u ↦ u·b` scales `d_b` by `u²`, `IsLegendreDatum.unit_sq_eq_one`); locally this is the
finite étale double cover `SqrtUnitCover` (`GroupScheme/SqrtUnitCover.lean`), and the
covers glue along the `ω`-cocycle by the twist `sqrtPairCongr`. The glued
`RelativeGluingData.glued` over the affine-opens-inside-charts cover of `W` is `Z₂`; it
is finite étale over `W` (locally so, `IsZariskiLocalAtTarget`) and its sections
classify the completing bases.

## Status

The funnel-assembly is proven here (`legendreDelta_relRep_finiteEtale`): given the
scale-torsor package (`ScaleTorsorData`, the funnel's four inputs bundled with the
sections classification as `Nonempty`-equivalences), `Bootstrap`'s AX2 statement
follows by `Classical`-extraction and the funnel. The geometric construction of the
package — the glued cover and the per-fibre sections classification — is isolated as the
single residual `exists_scaleTorsorData` (the `(2b)/(3)/(4)` build map: the Spec-pullback
squares, the `RelativeGluingData` over the chart cover, and the sheaf-glued
square-root/`b`↔`u` dictionary).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

open EllipticCurve

variable (R : CommRingCat.{u})

/-! ## The universal abscissa difference over the level-`2` locus (build-step 4 entry)

The geometric data feeding the residual's (unbuilt) proof: over `W := fullLevelLocus 2`,
the tautological naive full level-`2` pair `(P, Q)` is fibrewise nonzero
(`pull_ne_zero_left/right_of_isNaiveFullLevel`, `Moduli/LevelMarking.lean`), so OMEGA's
`ω^{⊗-2}`-valued abscissa difference `d = x(Q) − x(P)` (`abscissaDiff`,
`Moduli/AbscissaDifference.lean`) is defined. Its chart trivializations are the units
`d_b` whose square roots are the completing `±ω` bases; `univAbscissaDiff` is that `d`,
axiom-clean. -/

/-- The universal curve over the level-`2` locus `W := fullLevelLocus 2`: the base change
of `X.curve` along the finite étale structure map `W → X.base`. -/
noncomputable def locusCurve (X : EllObj R) (h2 : NIsInvertible X.base 2) :
    EllipticCurve (X.curve.fullLevelLocus 2 h2) :=
  X.curve.baseChange (X.curve.fullLevelLocusπ 2 h2)

/-- The tautological naive full level-`2` pair over the locus: the image of the identity
locus point under the classifying equivalence. -/
noncomputable def tautPair (X : EllObj R) (h2 : NIsInvertible X.base 2) :
    { PQ : (locusCurve R X h2).Section × (locusCurve R X h2).Section //
      (locusCurve R X h2).IsNaiveFullLevel 2 PQ.1 PQ.2 } :=
  X.curve.fullLevelLocusPointsEquiv 2 h2 (X.curve.fullLevelLocusπ 2 h2)
    ⟨𝟙 _, Category.id_comp _⟩

/-- **The universal abscissa difference** `d = x(Q) − x(P)` over the level-`2` locus: the
canonical `ω^{⊗-2}`-valued section of OMEGA's `abscissaDiff` for the tautological pair
(fibrewise nonzero by the locus condition). This is the section whose glued square-root
cover is the `±ω` scale-torsor `Z₂` of `ScaleTorsorData`. Axiom-clean. -/
noncomputable def univAbscissaDiff (X : EllObj R) (h2 : NIsInvertible X.base 2) :
    ((omegaCocycle (locusCurve R X h2).toEllipticCurveGeom).zpow (-2)).sections ⊤ :=
  abscissaDiff (G := (locusCurve R X h2).toEllipticCurveGeom)
    (σP := ((tautPair R X h2).1.1 : _ ⟶ _))
    (σQ := ((tautPair R X h2).1.2 : _ ⟶ _))
    (tautPair R X h2).1.1.2 (tautPair R X h2).1.2.2
    (fun k _ _ t => (locusCurve R X h2).pull_ne_zero_left_of_isNaiveFullLevel 2
      one_lt_two (NIsInvertible.of_hom (X.curve.fullLevelLocusπ 2 h2) h2)
      (tautPair R X h2).2 k t)
    (fun k _ _ t => (locusCurve R X h2).pull_ne_zero_right_of_isNaiveFullLevel 2
      one_lt_two (NIsInvertible.of_hom (X.curve.fullLevelLocusπ 2 h2) h2)
      (tautPair R X h2).2 k t)

/-! ## The scale-torsor package and the funnel assembly -/

/-- **The scale-torsor package** feeding the funnel `legendreDelta_relRep_finiteEtale_of_scaleTorsor`:
a finite étale cover `Z₂ → fullLevelLocus 2` whose `T`-sections over a locus point `w`
(lying over `g : T ⟶ X.base`) classify the `ω`-bases completing the corresponding level
structure to a Legendre datum. The sections classification is packaged as a family of
`Nonempty`-equivalences (the honest witnesses are produced by the sheaf-glued
square-root dictionary; `Classical.choice` promotes them to the funnel's `Equiv`
family). -/
structure ScaleTorsorData (X : EllObj R) (h2 : NIsInvertible X.base 2) where
  /-- The total space of the scale-torsor. -/
  Z₂ : Scheme.{u}
  /-- The finite étale structure map to the level-`2` locus. -/
  q : Z₂ ⟶ X.curve.fullLevelLocus 2 h2
  /-- Finiteness of the cover. -/
  isFinite : IsFinite q
  /-- Étaleness of the cover. -/
  etale : Etale q
  /-- The per-fibre sections classification: sections of `Z₂` over a locus point `w`
  correspond to the `ω`-bases making `(L_w, b)` a Legendre datum. -/
  spec : ∀ {T : Scheme.{u}} (g : T ⟶ X.base)
    (w : { w : T ⟶ X.curve.fullLevelLocus 2 h2 //
      w ≫ X.curve.fullLevelLocusπ 2 h2 = g }),
    Nonempty ({ s : T ⟶ Z₂ // s ≫ q = w.1 } ≃
      { b : OmegaBasis (X.pullbackAlong g).curve.toEllipticCurveGeom //
        IsLegendreDatum (X.pullbackAlong g)
          (X.curve.fullLevelLocusPointsEquiv 2 h2 g w) b })

/-- **(T-E14-AX2 — the geometric residual.)** For every elliptic curve over a base in
which `2` is invertible, the `±ω` scale-torsor over the level-`2` locus exists: the glued
square-root cover of the abscissa difference. This is the sole remaining geometric input
to `legendreDelta_relativelyRepresentable_finiteEtale`; the build map is
`(2b)` the Spec-pullback squares of the base-changed `sqrtPair` covers, `(3)` their
`RelativeGluingData` over the chart cover of `fullLevelLocus 2` (`glued`, finite étale via
`toBase_preimage_eq_opensRange_ι` + `IsZariskiLocalAtTarget`), and `(4)` the sections
classification via `sqrtCoverSectionsEquiv` + the `b`↔`u` dictionary
(`abscissaDiff`/`basisUnitAt` + `IsLegendreDatum.neg`/`unit_sq_eq_one`). -/
theorem exists_scaleTorsorData (X : EllObj R) (h2 : NIsInvertible X.base 2) :
    Nonempty (ScaleTorsorData R X h2) := by
  sorry

/-- **(T-E14-AX2, KM engine axiom 2 for the Legendre `δ` — the funnel assembly.)** For
every elliptic curve `E/S` over a base in which `2` is invertible, the `S`-scheme
relatively representing the Legendre-marked problem is finite étale over `S`. This is
`Bootstrap`'s `legendreDelta_relativelyRepresentable_finiteEtale`, proved by feeding the
scale-torsor package (`exists_scaleTorsorData`) through the funnel
`legendreDelta_relRep_finiteEtale_of_scaleTorsor`. -/
theorem legendreDelta_relRep_finiteEtale (hR : IsUnit (2 : R)) (X : EllObj R) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base), IsFinite f ∧ Etale f ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ X.base), Nonempty
        ({ h : T ⟶ Z // h ≫ f = g } ≃
          (legendreDeltaProblem R).obj (Opposite.op (X.pullbackAlong g))) := by
  have h2 : NIsInvertible X.base 2 :=
    nIsInvertible_base_of_isUnit R (by simpa using hR) X
  obtain ⟨D⟩ := exists_scaleTorsorData R X h2
  exact legendreDelta_relRep_finiteEtale_of_scaleTorsor R X h2 D.Z₂ D.q D.isFinite D.etale
    (fun g w => (D.spec g w).some)

end ModularCurves
