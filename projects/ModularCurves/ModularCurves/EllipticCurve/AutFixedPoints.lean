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

end ModularCurves
