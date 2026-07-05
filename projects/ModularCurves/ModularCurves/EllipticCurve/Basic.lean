import ModularCurves.EllipticCurve.WeierstrassModel
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Elliptic curves over a base scheme: the geometric record

Per the expert-review integration (2026-07-05), elliptic curves are packaged in **two
records**:

* `EllipticCurveGeom` (this file): the pure geometry — a morphism `π : E ⟶ S`, smooth of
  relative dimension 1 and proper, a section `0 : S ⟶ E`, and pointed genus-1 fibres.
  This matches the definition of all sources (KM 2.1.1; Deligne–Rapoport II.1.1;
  Loeffler Def 3.3.1, verbatim: *"An elliptic curve over `S` is a scheme `ℰ` with a
  morphism `π : ℰ → S` (an `S`-scheme) such that `π` is proper and flat and all fibres
  are smooth genus 1 curves, given with a section `0 : S → ℰ`"*).
* `EllipticCurve` (`GroupLaw.lean`): the working record for the Katz–Mazur programme —
  the geometry **together with** a commutative group-scheme structure whose identity is
  the zero section. Mathematically the group datum is redundant (Abel), but it is the
  object KM Ch. 1 actually consumes ("a smooth commutative group-scheme of relative
  dimension one", KM 1.4.1), and carrying it as data unblocks the entire
  level-structure theory from the Picard/Abel chain. The canonicity theorems
  (`EllipticCurveGeom` admits a unique such enrichment) are the deferred
  "purity/comparison" project — see `GroupLaw.lean`.

## The genus-1 fibre condition (bridge form)

Mathlib has no coherent cohomology yet, so "genus 1" is not directly expressible. We
use the classical equivalent (Riemann–Roch over a field, black box BB-RR; Silverman
III.3.1): *a pointed smooth proper geometrically connected genus-1 curve over a field
is exactly a pointed plane Weierstrass cubic with unit discriminant.* Per the expert
review (Q2 answer), the condition is phrased as a **pointed isomorphism of
`κ(s)`-schemes** with the projective Weierstrass model — not as a functor-of-points
identification. Once coherent cohomology lands, the equivalence with the genus
formulation becomes a theorem (ticket `T-A9`, API gap AG-COH) and the geometric-fibre
genus form becomes the statement of record.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

/-- The point of the fibre `π.fiber s` induced by a section `z : S ⟶ E` of `π`. -/
noncomputable def sectionFiberPoint {E S : Scheme.{u}} (π : E ⟶ S) (z : S ⟶ E)
    (hz : z ≫ π = 𝟙 S) (s : S) : Spec (S.residueField s) ⟶ π.fiber s :=
  pullback.lift (S.fromSpecResidueField s ≫ z) (𝟙 _)
    (by simp [Category.assoc, hz])

/-- **The fibre condition** (bridge form, per expert review Q2): every fibre of `π`,
pointed by the zero section, is *pointed-isomorphic as a `κ(s)`-scheme* to the
projective Weierstrass model of some elliptic (unit-discriminant) Weierstrass curve
over the residue field. By Riemann–Roch over a field (black box BB-RR) this is
equivalent to: every fibre is a smooth proper geometrically connected genus-1 curve.
Source: Loeffler Def 3.3.1; KM 2.1.1; phrasing per reviewer (scheme isomorphism, not
functor of points). -/
def FibrewiseElliptic {E S : Scheme.{u}} (π : E ⟶ S) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) :
    Prop :=
  ∀ s : S, ∃ W : WeierstrassCurve (S.residueField s), W.IsElliptic ∧
    ∃ e : π.fiber s ≅ projModel W,
      e.hom ≫ projModelπ W = π.fiberToSpecResidueField s ∧
      sectionFiberPoint π z hz s ≫ e.hom = projModelZero W

/-- The **geometric record** of an elliptic curve over the scheme `S`: a smooth proper
relative curve with a section whose fibres are (pointed) genus-1 curves, the latter
expressed via `FibrewiseElliptic`.

This record carries *no group structure*; the working record `EllipticCurve`
(`GroupLaw.lean`) extends it with the (canonically unique) commutative group-scheme
datum. Source: KM 2.1.1; Deligne–Rapoport II.1.1; Loeffler Def 3.3.1. -/
structure EllipticCurveGeom (S : Scheme.{u}) where
  /-- The total space. -/
  E : Scheme.{u}
  /-- The structure morphism. -/
  π : E ⟶ S
  /-- The zero section. -/
  zero : S ⟶ E
  zero_π : zero ≫ π = 𝟙 S
  smooth : SmoothOfRelativeDimension 1 π
  proper : IsProper π
  fibres : FibrewiseElliptic π zero zero_π

namespace EllipticCurveGeom

attribute [instance] EllipticCurveGeom.smooth EllipticCurveGeom.proper

end EllipticCurveGeom

end ModularCurves
