/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.GroupLaw
import ModularCurves.EllipticCurve.GroupLawConstruction
import ModularCurves.EllipticCurve.WeierstrassAtlasBundle

/-!
# Descent of the group law to every locally-Weierstrass family

**(T-W7 skeleton, join of lanes P0–P5 — `/develop --decompose` 2026-07-07.)** The group law
on an arbitrary geometric elliptic curve `G/S`: per chart of a bundled atlas, transport the
model group law (a base change of the universal one along the classifying map); overlap
agreement is the comparison theorem (`pointedIso_exists_variableChange` — the transition
between two pointed chart presentations is a variable change) composed with global
variable-change equivariance (`mulModelHom_vc`); glue. Each group axiom holds chart-locally
as a base change of the model identity (no flatness needed, no reducedness of `S` invoked),
hence globally by the cover extensionality. This yields the existence milestone **T-W7a**:
`abelEnrichment_exists`.

Sources: reviewer round 1 §3/§Q5 (existence by base change + atlas gluing, valid over
non-reduced `S`); audits A1/A6; `Scheme.Cover.glueMorphisms`/`hom_ext` (mathlib, verified).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

variable {S : Scheme.{u}} (G : EllipticCurveGeom S)

/-- **(T-W7.1)** Negation on a geometric elliptic curve, glued from the per-chart model
negations (overlaps agree: transitions are variable changes by the comparison theorem, and
negation is variable-change equivariant). -/
noncomputable def EllipticCurveGeom.negHom : G.E ⟶ G.E :=
  sorry

/-- **(T-W7.1-π)** Negation is a morphism over `S`. -/
@[reassoc]
theorem EllipticCurveGeom.negHom_π : G.negHom ≫ G.π = G.π := by
  sorry

/-- **(T-W7.1-zero)** Negation fixes the zero section. -/
theorem EllipticCurveGeom.negHom_zero : G.zero ≫ G.negHom = G.zero := by
  sorry

/-- **(T-W7.2)** Multiplication on a geometric elliptic curve, glued over the pullback cover
of `E ×_S E` induced by a bundled atlas from the per-chart base changes of the model
multiplication; overlap agreement = comparison theorem + variable-change equivariance. -/
noncomputable def EllipticCurveGeom.mulHom : pullback G.π G.π ⟶ G.E :=
  sorry

/-- **(T-W7.2-π)** Multiplication is a morphism over `S`. -/
@[reassoc]
theorem EllipticCurveGeom.mulHom_π :
    G.mulHom ≫ G.π = pullback.fst G.π G.π ≫ G.π := by
  sorry

/-- **(T-W7.3 → T-W7.6, the packaged group object)** The group-object structure on
`E/S` in `Over S`: multiplication and inverse glued above, unit the zero section; every
axiom holds because it holds per chart (base change of the model identity of
`GroupLawConstruction`) and morphism equality is chart-local (`Cover.hom_ext`). -/
noncomputable def EllipticCurveGeom.grpObj : GrpObj (Over.mk G.π) :=
  sorry

/-- **(T-W7.6-comm)** The glued structure is commutative (per chart: `mulOver_comm`). -/
theorem EllipticCurveGeom.grpObj_isCommMonObj :
    letI := G.grpObj
    IsCommMonObj (Over.mk G.π) := by
  sorry

/-- **(T-W7.6-one)** The unit of the glued structure is the zero section. -/
theorem EllipticCurveGeom.grpObj_one_eq_zero :
    letI := G.grpObj
    (η[Over.mk G.π] : _ ⟶ Over.mk G.π).left = (𝟙_ (Over S)).hom ≫ G.zero := by
  sorry

/-- **(T-W7.6 = MILESTONE T-W7a, assembly)** Every geometric elliptic curve enriches to the
working record: package `grpObj`, commutativity, and the unit normalisation. Discharges
`abelEnrichment_exists` as `⟨G.toEllipticCurve, toEllipticCurve_geom G⟩`. No rigidity, no
cohomology, no reducedness of `S` anywhere on this path. -/
noncomputable def EllipticCurveGeom.toEllipticCurve : EllipticCurve S :=
  { G with
    grp := G.grpObj
    comm := G.grpObj_isCommMonObj
    one_eq_zero := G.grpObj_one_eq_zero }

/-- **(T-W7.6-spec)** The enrichment forgets to the given geometry (definitional). -/
theorem EllipticCurveGeom.toEllipticCurve_geom :
    G.toEllipticCurve.toEllipticCurveGeom = G := rfl

end ModularCurves
