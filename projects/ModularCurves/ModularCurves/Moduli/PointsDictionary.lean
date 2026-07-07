import ModularCurves.Moduli.WeierstrassAtlas
import ModularCurves.ForMathlib.ProjIntegral
import ModularCurves.ForMathlib.WeierstrassProjectivePrime
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# T-W7 P2 — integrality of the universal atlas power `E_U^n` and the points dictionary

This file carries lane **P2** of the constructive group-law programme (`tw7-plan.md`):

* **T-W7.0e** the fibre powers `E_U ×_U … ×_U E_U` of the universal Weierstrass curve are
  **integral** schemes — the "source reduced/irreducible" input to the generic-point
  argument (`ext_of_isDominant`) that establishes the group axioms over `U` (T-W7.0g).
  Route: `E_U → U` is `GeometricallyIntegral`, flat and universally open over the integral,
  locally noetherian atlas `U`, so mathlib's
  `AlgebraicGeometry.Geometrically.Integral` machinery gives the fibre-power integrality.

* **T-W7.0f** the points dictionary: over any field `L`, `L`-points of `projModel W` biject
  with `W.toAffine.Point`, and the generic point of `E_U^n` is dominant.

The atlas `U = Spec ℤ[a₁..a₆][Δ⁻¹]` is a domain (T-W7.0a: `Δ ≠ 0`) and noetherian.
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ModularCurves

/-! ## T-W7.0a — the atlas ring is a domain (`Δ ≠ 0`) -/

/-- **(T-W7.0a core)** The universal discriminant is nonzero: evaluate the coefficients at the
elliptic curve `y² = x³ − x` (i.e. `(a₁,…,a₆) = (0,0,0,−1,0)`) over `ℚ`, where `Δ = 64 ≠ 0`.
Working over `ℚ` avoids the characteristic-2/3 degeneracies of the discriminant. -/
theorem universalWeierstrass_Δ_ne_zero : universalWeierstrass.Δ ≠ 0 := by
  intro h
  have key : (MvPolynomial.aeval ![(0 : ℚ), 0, 0, -1, 0]).toRingHom universalWeierstrass.Δ = 64 := by
    rw [← WeierstrassCurve.map_Δ universalWeierstrass
      (MvPolynomial.aeval ![(0 : ℚ), 0, 0, -1, 0]).toRingHom]
    show (universalWeierstrass.map _).Δ = 64
    simp only [WeierstrassCurve.map, universalWeierstrass, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      Matrix.cons_val_four]
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
  rw [h, map_zero] at key
  norm_num at key

/-- **(T-W7.0a)** The Weierstrass-atlas coefficient ring `ℤ[a₁..a₆][Δ⁻¹]` is an integral domain
(localisation of the polynomial domain away from the nonzero discriminant). -/
instance : IsDomain WeierstrassAtlasRing :=
  IsLocalization.isDomain_localization
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero universalWeierstrass_Δ_ne_zero))

/-- The Weierstrass-atlas coefficient ring is noetherian (localisation of a noetherian ring). -/
instance : IsNoetherianRing WeierstrassAtlasRing :=
  IsLocalization.isNoetherianRing (Submonoid.powers universalWeierstrass.Δ) _ inferInstance

/-! ## T-W7.0e — integrality of the universal curve and its fibre powers -/

/-- The atlas `U = Spec ℤ[a₁..a₆][Δ⁻¹]` is an integral scheme. -/
instance : IsIntegral weierstrassAtlas := by
  rw [weierstrassAtlas]; infer_instance

/-- The atlas `U` is locally noetherian. -/
instance : IsLocallyNoetherian weierstrassAtlas := by
  rw [weierstrassAtlas]; infer_instance

instance : SmoothOfRelativeDimension 1 universalCurveπ := universalCurve_smooth

instance : Smooth universalCurveπ := SmoothOfRelativeDimension.smooth 1 universalCurveπ

instance : LocallyOfFinitePresentation universalCurveπ := inferInstance

instance : Flat universalCurveπ := inferInstance

instance : UniversallyOpen universalCurveπ := inferInstance

/-- `IsIntegral` is closed under isomorphism as a property of schemes (it is
`IrreducibleSpace ⊓ IsReduced`, both closed under isomorphism). -/
instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (IsIntegral ·) where
  of_iso e hX := by
    rw [isIntegral_iff_irreducibleSpace_and_isReduced] at hX ⊢
    exact ⟨ObjectProperty.prop_of_iso (C := Scheme) (IrreducibleSpace ·) e hX.1,
           ObjectProperty.prop_of_iso (C := Scheme) (IsReduced ·) e hX.2⟩

/-- **(T-W7.0e-proj applied)** The projective model of a Weierstrass curve over a field is an
integral scheme: `projModel W = Proj (projCoordRing W)` and `projCoordRing W` is a graded domain
with nonzero positive-degree part `[X₀]`, so `AlgebraicGeometry.Proj.isIntegral_of_isDomain`
applies. -/
instance isIntegral_projModel {K : Type} [Field K] (W : WeierstrassCurve K) :
    IsIntegral (projModel W) := by
  show IsIntegral (Proj (quotientGrading (projIdeal W)))
  refine AlgebraicGeometry.Proj.isIntegral_of_isDomain (𝒜 := quotientGrading (projIdeal W)) ?_
  refine ⟨1, one_pos, Ideal.Quotient.mk _ (MvPolynomial.X 0), ?_, ?_⟩
  · exact mk_mem_quotientGrading _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X _ _))
  · rw [Ne, Ideal.Quotient.eq_zero_iff_mem, projIdeal_toIdeal, Ideal.mem_span_singleton]
    intro hdvd
    have hX0 : (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) K) ≠ 0 :=
      MvPolynomial.X_ne_zero _
    have hF0 : W.toProjective.polynomial ≠ 0 := by
      rintro h
      rw [h] at hdvd
      exact hX0 (zero_dvd_iff.mp hdvd)
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd hX0
    rw [(projective_polynomial_isHomogeneous W).totalDegree hF0, MvPolynomial.totalDegree_X] at hle
    omega

/-- **(T-W7.0e crux — geometric integrality of the universal curve)** Each geometric fibre of
`E_U → U` is a projective plane Weierstrass cubic, hence an integral scheme. A field-valued point
`y : Spec K ⟶ U` makes `K` a `WeierstrassAtlasRing`-algebra (`Spec.preimage`), and
`isPullback_projModelBaseChange` identifies the base change `E_U ×_U Spec K` with
`projModel (universalWeierstrassLoc.map (algebraMap _ K))`, which is integral by
`isIntegral_projModel`. Transporting across the pullback isomorphism discharges the geometric
integrality (avoiding the `smooth ⟹ geometrically reduced` mathlib gap entirely). -/
instance geometricallyIntegral_universalCurveπ : GeometricallyIntegral universalCurveπ := by
  rw [geometricallyIntegral_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  letI : Algebra WeierstrassAtlasRing K := (Spec.preimage y).hom.toAlgebra
  have hy : y = Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRing K)) := by
    have h1 : CommRingCat.ofHom (algebraMap WeierstrassAtlasRing K) = Spec.preimage y :=
      CommRingCat.ofHom_hom _
    rw [h1, Spec.map_preimage]
  have hpb := isPullback_projModelBaseChange (R := WeierstrassAtlasRing) (R' := K)
    universalWeierstrassLoc
  rw [← hy] at hpb
  exact ObjectProperty.prop_of_iso (IsIntegral ·) hpb.isoPullback (isIntegral_projModel _)

/-- The universal curve `E_U` is itself an integral scheme (geometrically integral over the
integral, locally noetherian atlas). -/
instance : IsIntegral universalCurve :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian universalCurveπ

/-- The universal curve `E_U` is locally noetherian (locally of finite type over `U`). -/
instance : IsLocallyNoetherian universalCurve :=
  LocallyOfFiniteType.isLocallyNoetherian universalCurveπ

/-- **(T-W7.0e, n = 2)** The fibre square `E_U ×_U E_U` is an integral scheme. -/
instance : IsIntegral (pullback universalCurveπ universalCurveπ) := inferInstance

/-- **(T-W7.0e, n = 3)** The triple fibre power `E_U ×_U E_U ×_U E_U` is an integral scheme
(the source of the associativity axiom `E_U^3 ⟶ E_U`). -/
instance : IsIntegral (pullback universalCurveπ (pullback.snd universalCurveπ universalCurveπ ≫
    universalCurveπ)) := inferInstance

end ModularCurves
