import ModularCurves.EllipticCurve.AdditionChartHom

/-!
# Cross-index chart compatibility (T-W7.0c-c5β, c4.2 — the last crux)

The one statement standing between β4(b) and the glued `addOnY` / `addOnZ`.

β4(b) (`AdditionChartGlue.lean`) showed the *two laws* agree wherever both are regular — and
`isUnit_of_minor` showed they are then regular at the SAME index, so no cross-index comparison
between the laws is needed. What remains is cross-index compatibility for a SINGLE triple: on
`D(t k) ⊓ D(t l)` the chart morphisms built at index `k` and at index `l` land in *different*
chart rings (`chartAway W k` vs `chartAway W l`), so the ratio argument of β4(b) does not apply.
Geometrically this is nothing but the statement that a projective triple defines a morphism to
`Proj` — the original plan's `toProjOfBihomTriple`.

## Route (recorded; mathlib gap identified)

Mathlib supplies the chart-compatibility square
`AlgebraicGeometry.Proj.SpecMap_awayMap_awayι` (ProjectiveSpectrum/Basic.lean:248):

  `Spec.map (awayMap 𝒜 g_deg hx) ≫ awayι 𝒜 f = awayι 𝒜 (f * g)`.

So both sides of the goal factor through `awayι` at `X k * X l` once the two chart morphisms are
shown to come from a COMMON ring map `Away 𝒜 (X k * X l) → S`; the `X l * X k` versus `X k * X l`
mismatch is the repo's `ForMathlib/AwayCongr.lean` (`awayCongr`).

The common map exists because `D₊(X k) ⊓ D₊(X l)` is the basic open of `D₊(X k)` at the function
`X l / X k`, whose image `t l * u` is a unit in `S`; i.e. `Away 𝒜 (X k * X l)` should be the
localization of `Away 𝒜 (X k)` at that element, and the map is `IsLocalization.Away.lift`.

**MATHLIB GAP**: that `IsLocalization` instance does not exist — `HomogeneousLocalization.awayMap`
is defined (`HomogeneousLocalization.lean:820`) with `val_awayMap` computation lemmas, but nothing
identifies it as a localization map. Two routes, in preference order:
1. prove `IsLocalization.Away (mk (X l / X k)) (Away 𝒜 (X k * X l))` for the `awayMap` algebra
   structure (ForMathlib, upstream candidate), then `IsLocalization.Away.lift` gives the common
   map and both factorizations by `IsLocalization.lift_comp`;
2. or build the common map by hand from the `chartCoordEquiv`-style presentation of
   `Away 𝒜 (X k * X l)` and check the two factorizations on generators.
-/

open MvPolynomial ModularCurves AlgebraicGeometry CategoryTheory

namespace WeierstrassCurve.Projective

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
variable {S : Type} [CommRing S] [Algebra R S]

/-- **(c4.2, the last crux of c5β)** A projective triple on the curve, regular at two indices,
defines the same morphism to the model through either chart. Equivalently: the triple defines a
morphism to `Proj`, independent of the chart used to read it off.

Route and the identified mathlib gap are in the module docstring. Sub-ticket:
`T-W7.0c-c5β-projglue`. -/
theorem chartι_comp_specMap_chartAwayHom_eq (k l : Fin 3) (t : Fin 3 → S) (u v : S)
    (hu : t k * u = 1) (hv : t l * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t) :
    Spec.map (CommRingCat.ofHom (chartAwayHomOfTriple W k t u hu ht).toRingHom) ≫ chartι W k =
      Spec.map (CommRingCat.ofHom (chartAwayHomOfTriple W l t v hv ht).toRingHom) ≫
        chartι W l := by
  sorry

end WeierstrassCurve.Projective
