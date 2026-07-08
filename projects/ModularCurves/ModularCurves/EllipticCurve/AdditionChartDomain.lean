import ModularCurves.EllipticCurve.AdditionChartLadder
import ModularCurves.EllipticCurve.PoleFiltration
import ModularCurves.ForMathlib.MonicQuotientDescent
import ModularCurves.ForMathlib.WeierstrassProjectivePrime

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

open MvPolynomial ModularCurves HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

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

/-! ## The `Y`-chart: field case, then monic descent -/

section FieldCase

variable {K : Type*} [Field K]

/-- The class of the coordinate `X i` is nonzero in the projective coordinate ring: the cubic
has total degree `3` and cannot divide a linear form. -/
lemma mk_X_ne_zero (W : WeierstrassCurve K) (i : Fin 3) :
    (quotientGradingHom (projIdeal W)) (MvPolynomial.X i) ≠ 0 := by
  show Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i) ≠ 0
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem, projIdeal_toIdeal, Ideal.mem_span_singleton]
  intro hdvd
  have hX0 : (MvPolynomial.X i : MvPolynomial (Fin 3) K) ≠ 0 := MvPolynomial.X_ne_zero _
  have hF0 : W.toProjective.polynomial ≠ 0 := by
    rintro h
    rw [h] at hdvd
    exact hX0 (zero_dvd_iff.mp hdvd)
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd hX0
  rw [(projective_polynomial_isHomogeneous W).totalDegree hF0, MvPolynomial.totalDegree_X] at hle
  omega

/-- **(field case)** Over a field, every chart ring of the projective model is a domain: it is the
degree-zero part of the graded domain `projCoordRing W` localized at the nonzero element `[X i]`. -/
theorem isDomain_affineChartRing_of_field (W : WeierstrassCurve K) (i : Fin 3) :
    IsDomain (affineChartRing W i) := by
  haveI hdom : IsDomain (projCoordRing W) := inferInstance
  haveI : IsDomain (HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))) :=
    HomogeneousLocalization.isDomain_away _ (mk_X_ne_zero W i)
  exact MulEquiv.isDomain _ (chartCoordEquiv W i).toMulEquiv

end FieldCase

/-! ## The `Y`-chart over an arbitrary domain: monic descent -/

section YChart

variable {S : Type*} [CommRing S]

/-- The monic chart cubic commutes with base change. -/
lemma infChartCubic_map (φ : R →+* S) (W : WeierstrassCurve R) :
    infChartCubic (W.map φ) = (infChartCubic W).map (Polynomial.mapRingHom φ) := by
  simp only [infChartCubic, WeierstrassCurve.map, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    Polynomial.coe_mapRingHom]

/-- **(β2b, `Y`-chart)** Over a domain, the `Y`-chart ring is a domain: it is `AdjoinRoot` of the
monic chart cubic, whose domain-ness descends from the fraction field by monic descent
(`AdjoinRoot.isDomain_of_monic_of_map`), the field case being `isDomain_affineChartRing_of_field`. -/
instance instIsDomainAffineChartRingY [IsDomain R] : IsDomain (affineChartRing W 1) := by
  set K := FractionRing R with hK
  set φ : R →+* K := algebraMap R K with hφdef
  have hφ : Function.Injective φ := IsFractionRing.injective R K
  have hφP : Function.Injective (Polynomial.mapRingHom φ) := by
    simpa [Polynomial.coe_mapRingHom] using Polynomial.map_injective φ hφ
  -- the field case, transported to the `AdjoinRoot` presentation over `K`
  haveI hfield : IsDomain (AdjoinRoot (infChartCubic (W.map φ))) := by
    haveI := isDomain_affineChartRing_of_field (W.map φ) 1
    exact MulEquiv.isDomain _ (infChartQuotEquiv (W.map φ)).symm.toRingEquiv.toMulEquiv
  -- monic descent along `R[t] → K[t]`
  haveI : IsDomain (AdjoinRoot ((infChartCubic W).map (Polynomial.mapRingHom φ))) := by
    rwa [← infChartCubic_map]
  haveI : IsDomain (AdjoinRoot (infChartCubic W)) :=
    AdjoinRoot.isDomain_of_monic_of_map (Polynomial.mapRingHom φ) (infChartCubic W)
      (infChartCubic_monic W) hφP
  exact MulEquiv.isDomain _ (infChartQuotEquiv W).toRingEquiv.toMulEquiv

end YChart

variable (i j : Fin 3)

/-! ## The chart-products of the covering charts are domains

`chartY_sup_chartZ_eq_top` (T-W7.0i-b3) says the `Y`- and `Z`-charts already cover the model,
so the four products below cover `E ×_R E`. Each is a domain by the ladder: the `(i,j)`
chart-product is the `i`-chart of the curve base-changed to the (domain) `j`-chart ring. -/

instance instIsDomainBiChartRingYY [IsDomain R] : IsDomain (biChartRing W 1 1) :=
  isDomain_biChartRing W 1 1

instance instIsDomainBiChartRingYZ [IsDomain R] : IsDomain (biChartRing W 1 2) :=
  isDomain_biChartRing W 1 2

instance instIsDomainBiChartRingZY [IsDomain R] : IsDomain (biChartRing W 2 1) :=
  isDomain_biChartRing W 2 1

/-! ## The payoff: both laws land on the curve on every covering chart-product

`IsReduced` follows from `IsDomain`, `IsJacobsonRing (biChartRing …)` is automatic from
`[IsJacobsonRing R]` (`MvPolynomial.isJacobsonRing` + the quotient instance), so the c5α
theorems apply with no side conditions beyond `Δ` being a unit. -/

/-- **(c5β, β2 complete)** The second Bosma–Lenstra addition law lands on the curve on every
chart-product whose coordinate ring is a domain — by the instances above, on all four products
of the covering `Y`/`Z` charts, over every Jacobson domain with `Δ` a unit. In particular over
the universal atlas `ℤ[a₁..a₆][Δ⁻¹]` (finite type over `ℤ`, hence Jacobson; a domain by
T-W7.0a). No polynomial certificate: c5α + the ladder + monic descent. -/
theorem equation_lawTwoTriple_of_isDomain [IsJacobsonRing R] [IsDomain (biChartRing W i j)]
    (hΔ : IsUnit W.Δ) :
    (W.map (algebraMap R (biChartRing W i j))).toProjective.Equation (lawTwoTriple W i j) :=
  equation_lawTwoTriple W i j hΔ

/-- **(c5β, β2 complete)** Mathlib's addition law `addXYZ` lands on the curve on every
chart-product whose coordinate ring is a domain. -/
theorem equation_lawOneTriple_of_isDomain [IsJacobsonRing R] [IsDomain (biChartRing W i j)]
    (hΔ : IsUnit W.Δ) :
    (W.map (algebraMap R (biChartRing W i j))).toProjective.Equation (lawOneTriple W i j) :=
  equation_lawOneTriple W i j hΔ

/-- The `(Z,Z)` instance of `equation_lawTwoTriple_of_isDomain` (the affine chart-product). -/
theorem equation_lawTwoTriple_zz [IsDomain R] [IsJacobsonRing R] (hΔ : IsUnit W.Δ) :
    (W.map (algebraMap R (biChartRing W 2 2))).toProjective.Equation (lawTwoTriple W 2 2) :=
  equation_lawTwoTriple_of_isDomain W 2 2 hΔ

/-- The `(Z,Z)` instance of `equation_lawOneTriple_of_isDomain`. -/
theorem equation_lawOneTriple_zz [IsDomain R] [IsJacobsonRing R] (hΔ : IsUnit W.Δ) :
    (W.map (algebraMap R (biChartRing W 2 2))).toProjective.Equation (lawOneTriple W 2 2) :=
  equation_lawOneTriple_of_isDomain W 2 2 hΔ

/-- The `(Y,Y)` instance: the law-2 triple lands on the curve on the infinity chart-product —
the product that contains the diagonal at infinity, where law 1 is exceptional. -/
theorem equation_lawTwoTriple_yy [IsDomain R] [IsJacobsonRing R] (hΔ : IsUnit W.Δ) :
    (W.map (algebraMap R (biChartRing W 1 1))).toProjective.Equation (lawTwoTriple W 1 1) :=
  equation_lawTwoTriple_of_isDomain W 1 1 hΔ

end WeierstrassCurve.Projective
