/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

STREAM-FIN [K-VC] (board v10.323-FIN): the VariableChange affine fixed-point keystone.
-/
import ModularCurves.EllipticCurve.Comparison

/-!
# [K-VC] Pointed automorphisms with enough fixed points are the identity

The keystone route that BYPASSES the Hasse/Cauchy–Schwarz wall (board v10.323-FIN): a
pointed automorphism `e` of `projModel W` over a field acts on the affine coordinate
ring by `Φ(x) = αx + β`, `Φ(y) = γy + δx + ε` with `α, γ` units (the PROVEN T-W7.1b
coefficient extraction b3x/b3y). If `e` fixes
* two points with **distinct `x`-coordinates**, and
* one **`±`-pair** (same `x`, distinct `y`),
then the affine coefficients collapse (`α = 1, β = 0, γ = 1, δ = ε = 0`), so `Φ` fixes
the coordinate generators, hence `Φ = refl` — and by the T-W7.1b faithfulness
infrastructure `e = refl`.

This file builds the layers bottom-up:
* `coordEquiv_apply_eq_self_of_fixed` (**[KVC-alg]**, this increment): the pure
  coordinate-ring algebra — an `R`-algebra automorphism of `W.CoordinateRing` of the
  b3x/b3y affine shape, fixed by three evaluations in the above configuration, fixes
  `coordX` and `coordY`.

Consumers (increments to come): the evaluation bridge [KVC-eval] (a scheme point fixed
by `e` gives `ψ ∘ Φ = ψ`), the torsion-point supply [KVC-pts], the faithfulness wire
[KVC-faith], and the record-endo conjugation [KVC-conj] discharging the full-level
k̄-core (`aut_endo_eq_one_of_field`) and the narrowed `hbound` ([RIG-2′]).
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

variable {k : Type u} [Field k]

/-- **([KVC-alg] x-collapse)** An affine map `t ↦ α t + β` of a field with two distinct
fixed points is the identity: `α = 1` and `β = 0`. -/
theorem affine_fix_two {α β x₀ x₁ : k} (h₀ : α * x₀ + β = x₀) (h₁ : α * x₁ + β = x₁)
    (hne : x₀ ≠ x₁) : α = 1 ∧ β = 0 := by
  have hα : α = 1 := by
    have h3 : (α - 1) * (x₀ - x₁) = 0 := by linear_combination h₀ - h₁
    rcases mul_eq_zero.mp h3 with h4 | h4
    · have := sub_eq_zero.mp h4; linear_combination this
    · exact absurd (sub_eq_zero.mp h4) hne
  refine ⟨hα, ?_⟩
  have h := h₀
  rw [hα, one_mul] at h
  linear_combination h

/-- **([KVC-alg] the coordinate-fix collapse)** Let `Φ` be a `k`-algebra automorphism of
the affine coordinate ring with the b3x/b3y affine shape. If three `k`-point evaluations
`ψ₀, ψ₀', ψ₁` are `Φ`-fixed (`ψ ∘ Φ = ψ`), where `ψ₀, ψ₀'` share the `x`-value but have
distinct `y`-values (a `±`-pair) and `ψ₁` has a different `x`-value, then `Φ` fixes the
generators: `Φ (coordX W) = coordX W` and `Φ (coordY W) = coordY W`. -/
theorem coordEquiv_fixes_generators_of_fixed_points (W : WeierstrassCurve k)
    (Φ : W.toAffine.CoordinateRing ≃ₐ[k] W.toAffine.CoordinateRing)
    {α β γ δ ε : k} (hα : IsUnit α) (hγ : IsUnit γ)
    (hΦx : Φ (coordX W) = algebraMap k _ α * coordX W + algebraMap k _ β)
    (hΦy : Φ (coordY W) = algebraMap k _ γ * coordY W + algebraMap k _ δ * coordX W
      + algebraMap k _ ε)
    (ψ₀ ψ₀' ψ₁ : W.toAffine.CoordinateRing →ₐ[k] k)
    (hfix₀ : ∀ f, ψ₀ (Φ f) = ψ₀ f) (hfix₀' : ∀ f, ψ₀' (Φ f) = ψ₀' f)
    (hfix₁ : ∀ f, ψ₁ (Φ f) = ψ₁ f)
    (hxpair : ψ₀ (coordX W) = ψ₀' (coordX W))
    (hypair : ψ₀ (coordY W) ≠ ψ₀' (coordY W))
    (hxne : ψ₀ (coordX W) ≠ ψ₁ (coordX W)) :
    Φ (coordX W) = coordX W ∧ Φ (coordY W) = coordY W := by
  set x₀ := ψ₀ (coordX W) with hx₀
  set x₁ := ψ₁ (coordX W) with hx₁
  set y₀ := ψ₀ (coordY W) with hy₀
  set y₀' := ψ₀' (coordY W) with hy₀'
  -- the evaluated x-equations
  have hev : ∀ (ψ : W.toAffine.CoordinateRing →ₐ[k] k), (∀ f, ψ (Φ f) = ψ f) →
      α * ψ (coordX W) + β = ψ (coordX W) := by
    intro ψ hψ
    have h := hψ (coordX W)
    rw [hΦx] at h
    simpa [map_add, map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply] using h
  have hevy : ∀ (ψ : W.toAffine.CoordinateRing →ₐ[k] k), (∀ f, ψ (Φ f) = ψ f) →
      γ * ψ (coordY W) + δ * ψ (coordX W) + ε = ψ (coordY W) := by
    intro ψ hψ
    have h := hψ (coordY W)
    rw [hΦy] at h
    simpa [map_add, map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply] using h
  -- α = 1, β = 0 from the two distinct fixed x-values
  obtain ⟨hα1, hβ0⟩ := affine_fix_two (hev ψ₀ hfix₀) (hev ψ₁ hfix₁) hxne
  -- γ = 1 from the ±pair (same x, distinct y)
  have h₀ := hevy ψ₀ hfix₀
  have h₀' := hevy ψ₀' hfix₀'
  rw [← hxpair] at h₀'
  have hγ1 : γ = 1 := by
    have h3 : (γ - 1) * (y₀ - y₀') = 0 := by linear_combination h₀ - h₀'
    rcases mul_eq_zero.mp h3 with h4 | h4
    · have := sub_eq_zero.mp h4; linear_combination this
    · exact absurd (sub_eq_zero.mp h4) hypair
  -- δ·x₀ + ε = 0 and δ·x₁ + ε = 0 ⟹ δ = 0, ε = 0
  have hde₀ : δ * x₀ + ε = 0 := by
    have h := h₀; rw [hγ1, one_mul] at h; linear_combination h
  have h₁y := hevy ψ₁ hfix₁
  have hde₁ : δ * x₁ + ε = 0 := by
    have h := h₁y; rw [hγ1, one_mul] at h; linear_combination h
  have hδ0 : δ = 0 := by
    have h3 : δ * (x₀ - x₁) = 0 := by linear_combination hde₀ - hde₁
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · exact absurd (sub_eq_zero.mp h4) hxne
  have hε0 : ε = 0 := by
    have := hde₀; rw [hδ0, zero_mul, zero_add] at this; exact this
  constructor
  · rw [hΦx, hα1, hβ0, map_one, one_mul, map_zero, add_zero]
  · rw [hΦy, hγ1, hδ0, hε0, map_one, one_mul, map_zero, zero_mul, add_zero, add_zero]

/-! ### [KVC-faith] — a pointed automorphism whose coordinate equivalence fixes the
generators is the identity (the T-W7.1b faithfulness chain, replayed for `e` vs `refl`). -/

/-- **(coordinate-ring extensionality on the generators)** Two `R`-algebra homomorphisms
out of the affine coordinate ring agreeing on `coordX` and `coordY` are equal (public
replay of the local `coordEquiv_ext` inside `pointedIso_exists_variableChange`). -/
theorem coordRingAlgHom_ext {R : Type u} [CommRing R] {W' : WeierstrassCurve R}
    {A : Type u} [CommRing A] [Algebra R A]
    (φ ψ : W'.toAffine.CoordinateRing →ₐ[R] A)
    (hX : φ (coordX W') = ψ (coordX W')) (hY : φ (coordY W') = ψ (coordY W')) : φ = ψ := by
  have htest : (AdjoinRoot.of W'.toAffine.polynomial) Polynomial.X = coordX W' := by
    rw [coordX]; rfl
  have hofC : ∀ a : R, AdjoinRoot.of W'.toAffine.polynomial (Polynomial.C a)
      = algebraMap R W'.toAffine.CoordinateRing a := by
    intro a
    rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply]
  have key : ∀ r : Polynomial R, AdjoinRoot.of W'.toAffine.polynomial r
      = Polynomial.aeval (coordX W') r := by
    intro r
    induction r using Polynomial.induction_on with
    | C a => rw [Polynomial.aeval_C, hofC]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | monomial n a ih =>
        rw [map_mul, map_pow, map_mul, map_pow, htest, hofC, Polynomial.aeval_X,
          Polynomial.aeval_C]
  have hof : ∀ r : Polynomial R, φ (AdjoinRoot.of W'.toAffine.polynomial r)
      = ψ (AdjoinRoot.of W'.toAffine.polynomial r) := by
    intro r
    rw [key, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, hX]
  apply AlgHom.ext
  intro a
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  rw [WeierstrassCurve.Affine.CoordinateRing.smul,
    WeierstrassCurve.Affine.CoordinateRing.smul, mul_one, map_add, map_add, map_mul,
    map_mul,
    show Affine.CoordinateRing.mk W'.toAffine (Polynomial.C p)
      = AdjoinRoot.of W'.toAffine.polynomial p from rfl,
    show Affine.CoordinateRing.mk W'.toAffine (Polynomial.C q)
      = AdjoinRoot.of W'.toAffine.polynomial q from rfl,
    show Affine.CoordinateRing.mk W'.toAffine Polynomial.X = coordY W' from rfl,
    hof p, hof q, hY]

variable {R : Type u} [CommRing R]

/-- The `Γ`-map of the identity automorphism is the identity. -/
lemma pointedIsoΓ_refl_apply {W : WeierstrassCurve R}
    (hez' : projModelZero W ≫ (Iso.refl (projModel W)).hom = projModelZero W)
    (w : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) :
    pointedIsoΓ (Iso.refl (projModel W)) hez' w = w := rfl

/-- The coordinate equivalence of the identity automorphism is the identity. -/
lemma pointedIsoCoordEquiv_refl_apply {W : WeierstrassCurve R}
    (heπ' : (Iso.refl (projModel W)).hom ≫ projModelπ W = projModelπ W)
    (hez' : projModelZero W ≫ (Iso.refl (projModel W)).hom = projModelZero W)
    (x : W.toAffine.CoordinateRing) :
    pointedIsoCoordEquiv (Iso.refl (projModel W)) heπ' hez' x = x := by
  rw [pointedIsoCoordEquiv_apply, pointedIsoΓ_refl_apply, RingEquiv.symm_apply_apply]

/-- **([KVC-faith])** A pointed automorphism of the projective model whose induced
coordinate equivalence fixes the generators is the identity morphism — assembled from
the PROVEN T-W7.1b faithfulness chain (`pointedIsoΓ_eq_of_coordEquiv` +
`pointedIso_hom_eq_of_pointedIsoΓ`) applied against `Iso.refl`. -/
theorem pointedAuto_hom_eq_id_of_coordEquiv_fixes {W : WeierstrassCurve R}
    (e : projModel W ≅ projModel W)
    (heπ : e.hom ≫ projModelπ W = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W)
    (hX : pointedIsoCoordEquiv e heπ hez (coordX W) = coordX W)
    (hY : pointedIsoCoordEquiv e heπ hez (coordY W) = coordY W) :
    e.hom = 𝟙 (projModel W) := by
  have heπ' : (Iso.refl (projModel W)).hom ≫ projModelπ W = projModelπ W := by
    rw [Iso.refl_hom, Category.id_comp]
  have hez' : projModelZero W ≫ (Iso.refl (projModel W)).hom = projModelZero W := by
    rw [Iso.refl_hom, Category.comp_id]
  -- the refl coordinate equivalence fixes the generators
  have hXr : pointedIsoCoordEquiv (Iso.refl (projModel W)) heπ' hez' (coordX W)
      = coordX W := by
    rw [pointedIsoCoordEquiv_refl_apply]
  have hYr : pointedIsoCoordEquiv (Iso.refl (projModel W)) heπ' hez' (coordY W)
      = coordY W := by
    rw [pointedIsoCoordEquiv_refl_apply]
  -- the faithfulness chain
  have hcoord : pointedIsoCoordEquiv e heπ hez
      = pointedIsoCoordEquiv (Iso.refl (projModel W)) heπ' hez' := by
    refine AlgEquiv.ext fun x => ?_
    exact DFunLike.congr_fun (coordRingAlgHom_ext
      (pointedIsoCoordEquiv e heπ hez).toAlgHom
      (pointedIsoCoordEquiv (Iso.refl (projModel W)) heπ' hez').toAlgHom
      (hX.trans hXr.symm) (hY.trans hYr.symm)) x
  have hΓ : pointedIsoΓ e hez = pointedIsoΓ (Iso.refl (projModel W)) hez' :=
    pointedIsoΓ_eq_of_coordEquiv e (Iso.refl (projModel W)) heπ hez heπ' hez' hcoord
  have h := pointedIso_hom_eq_of_pointedIsoΓ e (Iso.refl (projModel W)) hez hez' hΓ
  rwa [Iso.refl_hom] at h

/-! ### [KVC-eval] — the evaluation bridge

A `k`-point `g : Spec k ⟶ projModel W` that is a section of `projModelπ` and whose range
lies in the `Z`-chart induces a `k`-algebra evaluation `ψC` of the affine coordinate ring
(the chart ring map of `g`, read through the fixed chart identification
`coordRingToZSection`). If moreover `g` is fixed by a pointed automorphism `e`
(`g ≫ e.hom = g`), then `ψC` is fixed by the induced coordinate equivalence:
`ψC ∘ pointedIsoCoordEquiv e heπ hez = ψC` (`zChartCoordEval_pointedIsoCoordEquiv`).
Finally `ψC` reads the points-dictionary coordinates: `ψC (coordX W)` / `ψC (coordY W)`
are the `Z`-chart solution values of `g` — the `x`/`y`-coordinates of the corresponding
affine point in the `projModelPointsEquiv(_some)` normal form
(`zChartCoordEval_coordX/_coordY`). -/

section KVCEval

open HomogeneousLocalization

/-- The `Z`-chart of the projective model is an affine open. -/
lemma isAffineOpen_zChart (W : WeierstrassCurve R) :
    IsAffineOpen (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :=
  Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos

/-- The canonical `fromSpec` of the `Z`-chart is `awayι` conjugated by `Spec` of the
`awayToSection` identification (the `X₂`-instance of `Proj_fromSpec_awayToSection_awayι`). -/
lemma zChart_fromSpec (W : WeierstrassCurve R) :
    (isAffineOpen_zChart W).fromSpec =
      Spec.map (Proj.awayToSection (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos :=
  Proj_fromSpec_awayToSection_awayι _ _ _ _

/-- The chart factorization of a point with range in the `Z`-chart: the lift of `g`
through the affine chart's `fromSpec` (an open immersion). -/
noncomputable def zChartLift (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W))) :
    Spec (CommRingCat.of k) ⟶
      Spec Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :=
  IsOpenImmersion.lift (isAffineOpen_zChart W).fromSpec g
    (by rw [(isAffineOpen_zChart W).range_fromSpec]; exact hmem)

@[reassoc]
lemma zChartLift_fromSpec (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W))) :
    zChartLift W g hmem ≫ (isAffineOpen_zChart W).fromSpec = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- **([KVC-eval] the Γ-evaluation)** The `Z`-chart section-ring evaluation of a chart
point: the ring map underlying `Spec.preimage` of the chart factorization. -/
noncomputable def zChartEval (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W))) :
    Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) →+* k :=
  (Spec.preimage (zChartLift W g hmem)).hom

lemma zChartEval_apply (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (w : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) :
    zChartEval W g hmem w = (Spec.preimage (zChartLift W g hmem)).hom w :=
  rfl

lemma Spec_map_zChartEval (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W))) :
    Spec.map (CommRingCat.ofHom (zChartEval W g hmem)) = zChartLift W g hmem :=
  Spec.map_preimage _

/-- A section of `projModelπ` is a `k`-point in the `SpecPoints` sense. -/
lemma section_comp_projModelπ_specMap (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ : g ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k))) :
    g ≫ projModelπ W = Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
  rw [hgπ, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- A section with range inside the `Z`-chart open factors through the `Z`-chart
(`InZChart`): the factoring morphism is the chart lift followed by `Spec` of
`awayToSection`. -/
lemma inZChart_of_range_subset (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ' : g ≫ projModelπ W = Spec.map (CommRingCat.ofHom (algebraMap k k)))
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W))) :
    InZChart W (⟨g, hgπ'⟩ : SpecPoints (projModel W) (projModelπ W) k) :=
  ⟨zChartLift W g hmem ≫ Spec.map (Proj.awayToSection (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))), by
    rw [Category.assoc, ← zChart_fromSpec, zChartLift_fromSpec]⟩

/-- Conversely, a point factoring through the `Z`-chart has range inside the `Z`-chart
open. -/
lemma range_subset_of_inZChart (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ' : g ≫ projModelπ W = Spec.map (CommRingCat.ofHom (algebraMap k k)))
    (hZ : InZChart W (⟨g, hgπ'⟩ : SpecPoints (projModel W) (projModelπ W) k)) :
    Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)) := by
  obtain ⟨h, hfac⟩ := hZ
  rintro _ ⟨p, rfl⟩
  have h1 : g.base p = (Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos).base (h.base p) := by
    have hc := congrArg (fun m => m p) hfac.symm
    rw [Scheme.Hom.comp_apply] at hc
    exact hc
  rw [h1]
  have h2 : (Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos).base (h.base p) ∈
      (Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).opensRange :=
    Scheme.Hom.mem_opensRange.mpr ⟨h.base p, rfl⟩
  rwa [Proj.opensRange_awayι] at h2

/-- **([KVC-eval] fix transport, Γ-level)** A pointed automorphism fixing the point `g`
fixes its `Z`-chart evaluation: `zChartEval g ∘ pointedIsoΓ e = zChartEval g`. Via the
`fromSpec` square `IsAffineOpen.SpecMap_appLE_fromSpec`, mono-ness of the chart open
immersion, `Spec`-faithfulness, and the appLE bridge `appLE_zChart_eq_pointedIsoΓ`. -/
lemma zChartEval_pointedIsoΓ (W : WeierstrassCurve k)
    (e : projModel W ≅ projModel W)
    (hez : projModelZero W ≫ e.hom = projModelZero W)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (hfix : g ≫ e.hom = g)
    (w : Γ(projModel W, Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) :
    zChartEval W g hmem (pointedIsoΓ e hez w) = zChartEval W g hmem w := by
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec e.hom (isAffineOpen_zChart W)
    (isAffineOpen_zChart W) (pointedIso_preimage_zChart e hez).ge
  have hlift : zChartLift W g hmem ≫ Spec.map (e.hom.appLE
      (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))
      (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))
      (pointedIso_preimage_zChart e hez).ge) = zChartLift W g hmem := by
    refine (cancel_mono (isAffineOpen_zChart W).fromSpec).mp ?_
    rw [Category.assoc, hsq, ← Category.assoc, zChartLift_fromSpec]
    exact hfix
  have h2 : e.hom.appLE
      (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))
      (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))
      (pointedIso_preimage_zChart e hez).ge ≫
      Spec.preimage (zChartLift W g hmem) = Spec.preimage (zChartLift W g hmem) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact hlift
  rw [appLE_zChart_eq_pointedIsoΓ e hez] at h2
  have h3 := congrArg (fun t => CommRingCat.Hom.hom t w) h2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h3
  exact h3

/-- **([KVC-eval] the structure readout)** The chart evaluation of a *section* returns the
scalar on the image of the structure ring map `k ⟶ Γ(Z-chart)`: from `hgπ` by
`Spec`-faithfulness against `awayι_projModelπ`. -/
lemma zChartEval_structure (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ : g ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (r : k) :
    zChartEval W g hmem ((Proj.awayToSection (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).hom
      ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
        (((gradeZeroRingEquiv W) : k →+* ↥(quotientGrading (projIdeal W) 0)) r))) = r := by
  have h1 : zChartLift W g hmem ≫ Spec.map (Proj.awayToSection (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) ≫
      Spec.map (CommRingCat.ofHom
        ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
        ((gradeZeroRingEquiv W) : k →+* ↥(quotientGrading (projIdeal W) 0)))) =
      𝟙 (Spec (CommRingCat.of k)) := by
    calc zChartLift W g hmem ≫ Spec.map (Proj.awayToSection (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) ≫
        Spec.map (CommRingCat.ofHom
          ((algebraMap (↥(quotientGrading (projIdeal W) 0))
            (Away (quotientGrading (projIdeal W))
              ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
          ((gradeZeroRingEquiv W) : k →+* ↥(quotientGrading (projIdeal W) 0))))
        = zChartLift W g hmem ≫ Spec.map (Proj.awayToSection (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) ≫
            (Proj.awayι (quotientGrading (projIdeal W))
              ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
              (mk_X_mem_quotientGrading_one W 2) one_pos ≫ projModelπ W) := by
          rw [awayι_projModelπ W 2]
      _ = (zChartLift W g hmem ≫ (isAffineOpen_zChart W).fromSpec) ≫ projModelπ W := by
          rw [zChart_fromSpec]
          simp only [Category.assoc]
      _ = g ≫ projModelπ W := by rw [zChartLift_fromSpec]
      _ = 𝟙 (Spec (CommRingCat.of k)) := hgπ
  have h2 : CommRingCat.ofHom
      ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
      ((gradeZeroRingEquiv W) : k →+* ↥(quotientGrading (projIdeal W) 0))) ≫
      Proj.awayToSection (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ≫
      Spec.preimage (zChartLift W g hmem) = 𝟙 (CommRingCat.of k) := by
    apply Spec.map_injective
    rw [Spec.map_id, Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    simpa only [Category.assoc] using h1
  have h3 := congrArg (fun t => CommRingCat.Hom.hom t r) h2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
    CommRingCat.hom_id, RingHom.id_apply] at h3
  exact h3

/-- The fixed chart identification `coordRingToZSection` in `awayToSection` form (pure
`rfl`-unfolding: the localization iso of the chart is `awayToSection`). -/
lemma coordRingToZSection_eq_awayToSection (W : WeierstrassCurve R)
    (f : W.toAffine.CoordinateRing) :
    coordRingToZSection W f =
      (Proj.awayToSection (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).hom
      ((chartZRingEquiv W).symm f) :=
  rfl

/-- **([KVC-eval] the coordinate-ring evaluation `ψC`)** The evaluation of the affine
coordinate ring induced by a `k`-point with range in the `Z`-chart: `zChartEval`
conjugated by the fixed chart identification `coordRingToZSection`. -/
noncomputable def zChartCoordEval (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W))) :
    W.toAffine.CoordinateRing →+* k :=
  (zChartEval W g hmem).comp (coordRingToZSection W).toRingHom

lemma zChartCoordEval_apply (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (f : W.toAffine.CoordinateRing) :
    zChartCoordEval W g hmem f = zChartEval W g hmem (coordRingToZSection W f) :=
  rfl

/-- **([KVC-eval] fix transport)** A pointed automorphism fixing the point `g` fixes the
induced coordinate-ring evaluation: `ψC ∘ pointedIsoCoordEquiv e heπ hez = ψC`. -/
theorem zChartCoordEval_pointedIsoCoordEquiv (W : WeierstrassCurve k)
    (e : projModel W ≅ projModel W)
    (heπ : e.hom ≫ projModelπ W = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (hfix : g ≫ e.hom = g) (f : W.toAffine.CoordinateRing) :
    zChartCoordEval W g hmem (pointedIsoCoordEquiv e heπ hez f) =
      zChartCoordEval W g hmem f := by
  rw [zChartCoordEval_apply, zChartCoordEval_apply, pointedIsoCoordEquiv_apply,
    RingEquiv.apply_symm_apply, zChartEval_pointedIsoΓ W e hez g hmem hfix]

/-- **([KVC-eval] `k`-linearity)** The coordinate-ring evaluation of a *section* is a
`k`-algebra map: it restricts to the identity on scalars. -/
theorem zChartCoordEval_algebraMap (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ : g ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (r : k) :
    zChartCoordEval W g hmem (algebraMap k W.toAffine.CoordinateRing r) = r := by
  have hsymm : (chartZRingEquiv W).symm (algebraMap k W.toAffine.CoordinateRing r) =
      (HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal W))
        (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
        ((algebraMapGradeZero (projIdeal W)) r) := by
    rw [← chartZRingEquiv_fromZero W r, RingEquiv.symm_apply_apply]
  rw [zChartCoordEval_apply, coordRingToZSection_eq_awayToSection, hsymm]
  exact zChartEval_structure W g hgπ hmem r

/-- **([KVC-eval] `ψC` packaged)** The coordinate-ring evaluation of a section as a
`k`-algebra homomorphism. -/
noncomputable def zChartCoordAlgEval (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ : g ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W))) :
    W.toAffine.CoordinateRing →ₐ[k] k :=
  { zChartCoordEval W g hmem with
    commutes' := fun r => zChartCoordEval_algebraMap W g hgπ hmem r }

lemma zChartCoordAlgEval_apply (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ : g ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (f : W.toAffine.CoordinateRing) :
    zChartCoordAlgEval W g hgπ hmem f = zChartCoordEval W g hmem f :=
  rfl

/-- `AlgHom` form of the fix transport. -/
theorem zChartCoordAlgEval_pointedIsoCoordEquiv (W : WeierstrassCurve k)
    (e : projModel W ≅ projModel W)
    (heπ : e.hom ≫ projModelπ W = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ : g ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (hfix : g ≫ e.hom = g) (f : W.toAffine.CoordinateRing) :
    zChartCoordAlgEval W g hgπ hmem (pointedIsoCoordEquiv e heπ hez f) =
      zChartCoordAlgEval W g hgπ hmem f :=
  zChartCoordEval_pointedIsoCoordEquiv W e heπ hez g hmem hfix f

/-- The chart ring hom of a section-with-range-in-the-`Z`-chart under `chartHomEquiv` is
exactly `zChartEval` composed with the `awayToSection` identification. This is the wire
between `ψC` and the points-dictionary chart data. -/
lemma chartHomEquiv_zChartEval (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ : g ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (hZ : InZChart W (⟨g, section_comp_projModelπ_specMap W g hgπ⟩ :
      SpecPoints (projModel W) (projModelπ W) k)) :
    (chartHomEquiv W 2 k ⟨⟨g, section_comp_projModelπ_specMap W g hgπ⟩, hZ⟩).1 =
      (zChartEval W g hmem).comp
        (Proj.awayToSection (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).hom := by
  have hcompat : ((zChartEval W g hmem).comp
      (Proj.awayToSection (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).hom).comp
      ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
      ((gradeZeroRingEquiv W) : k →+* ↥(quotientGrading (projIdeal W) 0))) =
      algebraMap k k :=
    RingHom.ext fun r => zChartEval_structure W g hgπ hmem r
  have hfac : Spec.map (CommRingCat.ofHom ((zChartEval W g hmem).comp
      (Proj.awayToSection (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).hom)) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos = g := by
    rw [show CommRingCat.ofHom ((zChartEval W g hmem).comp
        (Proj.awayToSection (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).hom) =
        Proj.awayToSection (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ≫
          Spec.preimage (zChartLift W g hmem) from rfl,
      Spec.map_comp, Spec.map_preimage, Category.assoc, ← zChart_fromSpec,
      zChartLift_fromSpec]
  exact congrArg Subtype.val (chartHomEquiv_eq_of_specMap W 2
    ⟨⟨g, section_comp_projModelπ_specMap W g hgπ⟩, hZ⟩
    ⟨(zChartEval W g hmem).comp
      (Proj.awayToSection (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).hom, hcompat⟩ hfac)

/-- **([KVC-eval] coordinate readout, `x`)** `ψC (coordX W)` is the `x`-coordinate of the
point in the points dictionary — the `Z`-chart solution value at index `0`, exactly the
`x` of `projModelPointsEquiv_some`. -/
theorem zChartCoordEval_coordX (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ : g ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (hZ : InZChart W (⟨g, section_comp_projModelπ_specMap W g hgπ⟩ :
      SpecPoints (projModel W) (projModelπ W) k)) :
    zChartCoordEval W g hmem (coordX W) =
      (chartSolutionsEquiv W 2 k (chartHomEquiv W 2 k
        ⟨⟨g, section_comp_projModelπ_specMap W g hgπ⟩, hZ⟩)).1 ⟨0, by decide⟩ := by
  have h0 : (chartSolutionsEquiv W 2 k (chartHomEquiv W 2 k
      ⟨⟨g, section_comp_projModelπ_specMap W g hgπ⟩, hZ⟩)).1 ⟨0, by decide⟩ =
      (chartHomEquiv W 2 k ⟨⟨g, section_comp_projModelπ_specMap W g hgπ⟩, hZ⟩).1
        (chartCoordEquiv W 2 (Ideal.Quotient.mk _
          (MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 2})))) :=
    rfl
  have h1 : chartCoordEquiv W 2 (Ideal.Quotient.mk _
      (MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 2}))) =
      HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0) :=
    chartCoordEquiv_mk_X W 2 ⟨0, by decide⟩
  have hX : (chartZRingEquiv W).symm (coordX W) =
      HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 0) := by
    rw [← chartZRingEquiv_x W, RingEquiv.symm_apply_apply]
  rw [h0, h1, chartHomEquiv_zChartEval W g hgπ hmem hZ, RingHom.comp_apply,
    zChartCoordEval_apply, coordRingToZSection_eq_awayToSection, hX]

/-- **([KVC-eval] coordinate readout, `y`)** `ψC (coordY W)` is the `y`-coordinate of the
point in the points dictionary — the `Z`-chart solution value at index `1`, exactly the
`y` of `projModelPointsEquiv_some`. -/
theorem zChartCoordEval_coordY (W : WeierstrassCurve k)
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ : g ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (hZ : InZChart W (⟨g, section_comp_projModelπ_specMap W g hgπ⟩ :
      SpecPoints (projModel W) (projModelπ W) k)) :
    zChartCoordEval W g hmem (coordY W) =
      (chartSolutionsEquiv W 2 k (chartHomEquiv W 2 k
        ⟨⟨g, section_comp_projModelπ_specMap W g hgπ⟩, hZ⟩)).1 ⟨1, by decide⟩ := by
  have h0 : (chartSolutionsEquiv W 2 k (chartHomEquiv W 2 k
      ⟨⟨g, section_comp_projModelπ_specMap W g hgπ⟩, hZ⟩)).1 ⟨1, by decide⟩ =
      (chartHomEquiv W 2 k ⟨⟨g, section_comp_projModelπ_specMap W g hgπ⟩, hZ⟩).1
        (chartCoordEquiv W 2 (Ideal.Quotient.mk _
          (MvPolynomial.X (⟨1, by decide⟩ : {j : Fin 3 // j ≠ 2})))) :=
    rfl
  have h1 : chartCoordEquiv W 2 (Ideal.Quotient.mk _
      (MvPolynomial.X (⟨1, by decide⟩ : {j : Fin 3 // j ≠ 2}))) =
      HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1) :=
    chartCoordEquiv_mk_X W 2 ⟨1, by decide⟩
  have hY : (chartZRingEquiv W).symm (coordY W) =
      HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W 1) := by
    rw [← chartZRingEquiv_y W, RingEquiv.symm_apply_apply]
  rw [h0, h1, chartHomEquiv_zChartEval W g hgπ hmem hZ, RingHom.comp_apply,
    zChartCoordEval_apply, coordRingToZSection_eq_awayToSection, hY]

/-! ### [KVC-master] — the master theorem -/

/-- **([KVC-master])** A pointed automorphism of the projective model over a field fixing
three `Z`-chart sections in the ±pair-plus-distinct-`x` configuration is the identity:
the coefficient extraction b3x/b3y + the algebraic collapse `[KVC-alg]` + the T-W7.1b
faithfulness chain `[KVC-faith]`, glued by the evaluation bridge `[KVC-eval]`. The point
conditions are stated in `ψC`-form (`zChartCoordEval`-values); the dictionary-coordinate
form follows via `zChartCoordEval_coordX/_coordY`. -/
theorem pointedAuto_hom_eq_id_of_fixes_points (W : WeierstrassCurve k)
    (e : projModel W ≅ projModel W)
    (heπ : e.hom ≫ projModelπ W = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W)
    (g₀ g₀' g₁ : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ₀ : g₀ ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (hgπ₀' : g₀' ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (hgπ₁ : g₁ ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (hmem₀ : Set.range ⇑g₀.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (hmem₀' : Set.range ⇑g₀'.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (hmem₁ : Set.range ⇑g₁.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)))
    (hfix₀ : g₀ ≫ e.hom = g₀) (hfix₀' : g₀' ≫ e.hom = g₀')
    (hfix₁ : g₁ ≫ e.hom = g₁)
    (hxpair : zChartCoordEval W g₀ hmem₀ (coordX W) =
      zChartCoordEval W g₀' hmem₀' (coordX W))
    (hypair : zChartCoordEval W g₀ hmem₀ (coordY W) ≠
      zChartCoordEval W g₀' hmem₀' (coordY W))
    (hxne : zChartCoordEval W g₀ hmem₀ (coordX W) ≠
      zChartCoordEval W g₁ hmem₁ (coordX W)) :
    e.hom = 𝟙 (projModel W) := by
  obtain ⟨α, β, hα, hΦx⟩ := pointedIsoCoordEquiv_coordX e heπ hez
  obtain ⟨γ, δ, ε, hγ, hΦy⟩ := pointedIsoCoordEquiv_coordY e heπ hez
  obtain ⟨hX, hY⟩ := coordEquiv_fixes_generators_of_fixed_points W
    (pointedIsoCoordEquiv e heπ hez) hα hγ hΦx hΦy
    (zChartCoordAlgEval W g₀ hgπ₀ hmem₀)
    (zChartCoordAlgEval W g₀' hgπ₀' hmem₀')
    (zChartCoordAlgEval W g₁ hgπ₁ hmem₁)
    (fun f => zChartCoordEval_pointedIsoCoordEquiv W e heπ hez g₀ hmem₀ hfix₀ f)
    (fun f => zChartCoordEval_pointedIsoCoordEquiv W e heπ hez g₀' hmem₀' hfix₀' f)
    (fun f => zChartCoordEval_pointedIsoCoordEquiv W e heπ hez g₁ hmem₁ hfix₁ f)
    hxpair hypair hxne
  exact pointedAuto_hom_eq_id_of_coordEquiv_fixes e heπ hez hX hY

end KVCEval

end ModularCurves
