import ModularCurves.EllipticCurve.AdditionChartLadder
import ModularCurves.EllipticCurve.PoleFiltration

/-!
# The chart-product is a domain, and both laws land on the curve there (T-W7.0c-c5β, β2b)

The last β2b leaf. Over a **domain** base the `Z`-chart ring of the projective model is
mathlib's affine coordinate ring (`chartZAffineEquiv`, PoleFiltration), which mathlib already
knows is a domain (`WeierstrassCurve.Affine.CoordinateRing.instIsDomain`, proved by
Gauss/fraction-field descent from `irreducible_polynomial`). Feeding that through the ladder
(`biChartRingEquiv`) makes the `(Z,Z)` chart-product a domain — hence reduced — and Jacobson
is automatic, so the c5α theorems fire **unconditionally**:

* `equation_lawTwoTriple_zz` — the second Bosma–Lenstra law lands on the curve on the
  `(Z,Z)` chart-product, over any Jacobson domain with `Δ` a unit;
* `equation_lawOneTriple_zz` — likewise for mathlib's `addXYZ`.

The universal atlas `ℤ[a₁..a₆][Δ⁻¹]` is a Jacobson domain (finite type over `ℤ`), so this is
exactly the input the `addOnZ`/`addOnY` chart morphisms need on the affine chart-product.

The remaining chart is `Y` (`affineChartRing W 1`): PoleFiltration presents it as
`AdjoinRoot (infChartCubic W)` with `infChartCubic` monic (`chartYRingEquiv`,
`infChartCubic_monic`), so the same fraction-field descent applies once the cubic is known
prime over `Frac R [t]` — see `T-W7.0c-c5β` on the board.
-/

open MvPolynomial

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The `Z`-chart ring of the projective model is mathlib's affine coordinate ring. This is
`PoleFiltration.chartZAffineEquiv`, restated for the `affineChartRing` abbreviation. -/
noncomputable def affineChartRingZEquiv :
    affineChartRing W 2 ≃ₐ[R] W.toAffine.CoordinateRing :=
  ModularCurves.chartZAffineEquiv W

/-- **(β2b, `Z`-chart)** Over a domain, the `Z`-chart ring is a domain: it is mathlib's affine
coordinate ring, whose `IsDomain` instance descends from `irreducible_polynomial` through the
fraction field. -/
instance instIsDomainAffineChartRingZ [IsDomain R] : IsDomain (affineChartRing W 2) :=
  MulEquiv.isDomain W.toAffine.CoordinateRing
    (affineChartRingZEquiv W).toRingEquiv.toMulEquiv

/-- **(β2b, `(Z,Z)` chart-product)** Over a domain, the `(Z,Z)` chart-product ring is a
domain: the ladder identifies it with the `Z`-chart ring of the curve base-changed to the
`Z`-chart ring, and that base is itself a domain. -/
instance instIsDomainBiChartRingZZ [IsDomain R] : IsDomain (biChartRing W 2 2) :=
  isDomain_biChartRing W 2 2

/-! ## The payoff: both laws land on the curve on the `(Z,Z)` chart-product

`IsReduced` follows from `IsDomain`, `IsJacobsonRing (biChartRing …)` is automatic from
`[IsJacobsonRing R]` (`MvPolynomial.isJacobsonRing` + the quotient instance), so the c5α
theorems apply with no side conditions beyond `Δ` being a unit. -/

/-- **(c5β, `(Z,Z)` chart-product)** The second Bosma–Lenstra addition law lands on the curve
on the affine chart-product, over every Jacobson domain with `Δ` a unit — in particular over
the universal atlas `ℤ[a₁..a₆][Δ⁻¹]` (finite type over `ℤ`, hence Jacobson; a domain by
T-W7.0a). No polynomial certificate: this is c5α + the ladder + mathlib's coordinate-ring
domain instance. -/
theorem equation_lawTwoTriple_zz [IsDomain R] [IsJacobsonRing R] (hΔ : IsUnit W.Δ) :
    (W.map (algebraMap R (biChartRing W 2 2))).toProjective.Equation (lawTwoTriple W 2 2) :=
  equation_lawTwoTriple W 2 2 hΔ

/-- **(c5β, `(Z,Z)` chart-product)** Mathlib's addition law `addXYZ` lands on the curve on the
affine chart-product, over every Jacobson domain with `Δ` a unit. -/
theorem equation_lawOneTriple_zz [IsDomain R] [IsJacobsonRing R] (hΔ : IsUnit W.Δ) :
    (W.map (algebraMap R (biChartRing W 2 2))).toProjective.Equation (lawOneTriple W 2 2) :=
  equation_lawOneTriple W 2 2 hΔ

end WeierstrassCurve.Projective
