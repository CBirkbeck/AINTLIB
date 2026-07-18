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

open WeierstrassCurve

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

end ModularCurves
