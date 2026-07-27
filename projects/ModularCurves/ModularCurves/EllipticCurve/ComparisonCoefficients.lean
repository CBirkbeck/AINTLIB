/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.ModelVariableChange

/-!
# Coefficient extraction for the comparison theorem (T-W7.1b, second half)

Hypothesis-parameterized versions of the `b3x`/`b3y`/`main` leaves of T-W7.1b: given a pointed
isomorphism of projective Weierstrass models and the pole-filtration-preservation conclusion
`hfil` of the `b2` leaf (`pointedIsoCoordEquiv_filtration`), the induced coordinate-ring
`AlgEquiv` sends `x' ↦ αx + β` and `y' ↦ γy + δx + ε` with `α, γ` units, and the two Weierstrass
relations then force a variable change `C` with `C • W' = W`.

These are stated over an abstract `AlgEquiv Φ` (plus the filtration hypothesis) so they decouple
from the `b1`/`b2` construction; the wiring into `pointedIsoCoordEquiv_coordX` / `_coordY` /
`pointedIso_exists_variableChange` instantiates `Φ := pointedIsoCoordEquiv e heπ hez` and supplies
`hfil` from `pointedIsoCoordEquiv_filtration`.

AINTLIB ModularCurves T-W7.1b (lane P3-parallel, beastmode-P3b3).
-/

open WeierstrassCurve

namespace ModularCurves

universe u

variable {R : Type u} [CommRing R]

/-- Coefficient reading in the free module `⟨1, x, y⟩`: two `R`-linear combinations of `1`,
`coordX`, `coordY` are equal iff their coefficients agree. Needs `[Nontrivial R]` (otherwise
`1, x, y` collapse). -/
lemma coordXY_ext {W : WeierstrassCurve R} [Nontrivial R] {a b c a' b' c' : R}
    (h : algebraMap R W.toAffine.CoordinateRing a + algebraMap R _ b * coordX W
          + algebraMap R _ c * coordY W
        = algebraMap R _ a' + algebraMap R _ b' * coordX W + algebraMap R _ c' * coordY W) :
    a = a' ∧ b = b' ∧ c = c' := by
  have hli := Fintype.linearIndependent_iff.mp (linearIndependent_one_coordX_coordY W)
  have hzero : (a - a') • (1 : W.toAffine.CoordinateRing) + (b - b') • coordX W
      + (c - c') • coordY W = 0 := by
    have e1 : (a - a') • (1 : W.toAffine.CoordinateRing) = algebraMap R _ (a - a') := by
      rw [Algebra.algebraMap_eq_smul_one]
    have e2 : (b - b') • coordX W = algebraMap R _ (b - b') * coordX W := Algebra.smul_def _ _
    have e3 : (c - c') • coordY W = algebraMap R _ (c - c') * coordY W := Algebra.smul_def _ _
    rw [e1, e2, e3, map_sub, map_sub, map_sub]
    linear_combination h
  have key := hli ![a - a', b - b', c - c'] (by
    rw [Fin.sum_univ_three]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] using hzero)
  refine ⟨?_, ?_, ?_⟩
  · have := key 0; simpa [sub_eq_zero] using this
  · have := key 1; simpa [sub_eq_zero] using this
  · have := key 2; simpa [sub_eq_zero] using this

/-- **(T-W7.1b-b3x core)** From filtration preservation, the coordinate `x'` maps to
`αx + β` with `α` a unit. Abstract over the `AlgEquiv Φ`; instantiate `Φ := pointedIsoCoordEquiv`
for the wiring. Requires `[Nontrivial R]` (see the public version for the subsingleton case). -/
lemma exists_coordX_image {W W' : WeierstrassCurve R} [Nontrivial R]
    (Φ : W'.toAffine.CoordinateRing ≃ₐ[R] W.toAffine.CoordinateRing)
    (hfil : ∀ n, Submodule.map Φ.toLinearEquiv.toLinearMap (poleOrderFiltration W' n)
      = poleOrderFiltration W n) :
    ∃ α β : R, IsUnit α ∧
      Φ (coordX W') = algebraMap R _ α * coordX W + algebraMap R _ β := by
  have hx'mem : coordX W' ∈ poleOrderFiltration W' 2 := by
    rw [poleOrderFiltration_two]; exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have hΦx' : Φ (coordX W') ∈ poleOrderFiltration W 2 := by
    rw [← hfil 2]; exact Submodule.mem_map_of_mem hx'mem
  rw [poleOrderFiltration_two, Submodule.mem_span_pair] at hΦx'
  obtain ⟨c, d, hcd⟩ := hΦx'
  have hΦx'_eq : Φ (coordX W') = algebraMap R _ d * coordX W + algebraMap R _ c := by
    rw [← hcd, Algebra.smul_def, Algebra.smul_def, mul_one]; ring
  refine ⟨d, c, ?_, hΦx'_eq⟩
  -- unitness of `d` via the inverse: `Φ.symm x ∈ F₂ W' = span{1, x'}`
  have hxmem : coordX W ∈ poleOrderFiltration W 2 := by
    rw [poleOrderFiltration_two]; exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have hxinv : Φ.symm (coordX W) ∈ poleOrderFiltration W' 2 := by
    have hmem : coordX W ∈ Submodule.map Φ.toLinearEquiv.toLinearMap
      (poleOrderFiltration W' 2) := by
      rw [hfil 2]; exact hxmem
    obtain ⟨w, hw, hΦw⟩ := hmem
    have hΦw' : Φ w = coordX W := hΦw
    rw [← hΦw', Φ.symm_apply_apply]; exact hw
  rw [poleOrderFiltration_two, Submodule.mem_span_pair] at hxinv
  obtain ⟨c'', d'', hcd''⟩ := hxinv
  have hxinv_eq : Φ.symm (coordX W) = algebraMap R _ d'' * coordX W' + algebraMap R _ c'' := by
    rw [← hcd'', Algebra.smul_def, Algebra.smul_def, mul_one]; ring
  have hxback : algebraMap R _ (d'' * d) * coordX W + algebraMap R _ (d'' * c
    + c'') = coordX W := by
    have h1 : Φ (Φ.symm (coordX W)) = coordX W := Φ.apply_symm_apply _
    rw [hxinv_eq, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hΦx'_eq] at h1
    rw [map_mul, map_add, map_mul]; linear_combination h1
  have hpad : algebraMap R W.toAffine.CoordinateRing (0 : R) + algebraMap R _ (1 : R) * coordX W
        + algebraMap R _ (0 : R) * coordY W
      = algebraMap R _ (d'' * c + c'') + algebraMap R _ (d'' * d) * coordX W
        + algebraMap R _ (0 : R) * coordY W := by
    simp only [map_zero, map_one, zero_add, one_mul, zero_mul, add_zero]
    linear_combination -hxback
  obtain ⟨_, hdd, _⟩ := coordXY_ext hpad
  exact isUnit_iff_exists.mpr ⟨d'', (mul_comm d d'').trans hdd.symm, hdd.symm⟩

/-- **(T-W7.1b-b3y core)** From filtration preservation, the coordinate `y'` maps to
`γy + δx + ε` with `γ` a unit. Reuses the `x`-expansion (`exists_coordX_image`) inside the
inverse-image analysis. Requires `[Nontrivial R]`. -/
lemma exists_coordY_image {W W' : WeierstrassCurve R} [Nontrivial R]
    (Φ : W'.toAffine.CoordinateRing ≃ₐ[R] W.toAffine.CoordinateRing)
    (hfil : ∀ n, Submodule.map Φ.toLinearEquiv.toLinearMap (poleOrderFiltration W' n)
      = poleOrderFiltration W n) :
    ∃ γ δ ε : R, IsUnit γ ∧
      Φ (coordY W') = algebraMap R _ γ * coordY W + algebraMap R _ δ * coordX W
        + algebraMap R _ ε := by
  obtain ⟨α, β, _, hΦx'⟩ := exists_coordX_image Φ hfil
  have hy'mem : coordY W' ∈ poleOrderFiltration W' 3 := by
    rw [poleOrderFiltration_three]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hΦy' : Φ (coordY W') ∈ poleOrderFiltration W 3 := by
    rw [← hfil 3]; exact Submodule.mem_map_of_mem hy'mem
  rw [poleOrderFiltration_three, Submodule.mem_span_triple] at hΦy'
  obtain ⟨a, b, c, habc⟩ := hΦy'
  have hΦy'_eq : Φ (coordY W') = algebraMap R _ c * coordY W + algebraMap R _ b * coordX W
      + algebraMap R _ a := by
    rw [← habc, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_one]; ring
  refine ⟨c, b, a, ?_, hΦy'_eq⟩
  have hymem : coordY W ∈ poleOrderFiltration W 3 := by
    rw [poleOrderFiltration_three]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hyinv : Φ.symm (coordY W) ∈ poleOrderFiltration W' 3 := by
    have hmem : coordY W ∈ Submodule.map Φ.toLinearEquiv.toLinearMap
      (poleOrderFiltration W' 3) := by
      rw [hfil 3]; exact hymem
    obtain ⟨w, hw, hΦw⟩ := hmem
    have hΦw' : Φ w = coordY W := hΦw
    rw [← hΦw', Φ.symm_apply_apply]; exact hw
  rw [poleOrderFiltration_three, Submodule.mem_span_triple] at hyinv
  obtain ⟨a'', b'', c'', habc''⟩ := hyinv
  have hyinv_eq : Φ.symm (coordY W) = algebraMap R _ c'' * coordY W'
    + algebraMap R _ b'' * coordX W'
      + algebraMap R _ a'' := by
    rw [← habc'', Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_one]; ring
  have hyback : algebraMap R _ (c'' * c) * coordY W
      + algebraMap R _ (c'' * b + b'' * α) * coordX W
      + algebraMap R _ (c'' * a + b'' * β + a'') = coordY W := by
    have h1 : Φ (Φ.symm (coordY W)) = coordY W := Φ.apply_symm_apply _
    rw [hyinv_eq, map_add, map_add, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes,
      AlgEquiv.commutes, hΦy'_eq, hΦx'] at h1
    simp only [map_mul, map_add]
    linear_combination h1
  have hpad : algebraMap R W.toAffine.CoordinateRing (0 : R) + algebraMap R _ (0 : R) * coordX W
        + algebraMap R _ (1 : R) * coordY W
      = algebraMap R _ (c'' * a + b'' * β + a'') + algebraMap R _ (c'' * b + b'' * α) * coordX W
        + algebraMap R _ (c'' * c) * coordY W := by
    simp only [map_zero, map_one, zero_add, one_mul, zero_mul, add_zero]
    linear_combination -hyback
  obtain ⟨_, _, hcc⟩ := coordXY_ext hpad
  exact isUnit_iff_exists.mpr ⟨c'', (mul_comm c c'').trans hcc.symm, hcc.symm⟩

/-- Over a subsingleton base the coordinate ring is a subsingleton (its `0 = 1`). Used to
discharge the degenerate case of the coefficient-extraction lemmas without `[Nontrivial R]`. -/
lemma subsingleton_coordinateRing [Subsingleton R] (W : WeierstrassCurve R) :
    Subsingleton W.toAffine.CoordinateRing := by
  refine subsingleton_of_zero_eq_one ?_
  rw [← map_zero (algebraMap R _), ← map_one (algebraMap R _), Subsingleton.elim (0 : R) 1]

/-- **(T-W7.1b-b3x, general base)** The `x`-image extraction with the `[Nontrivial R]`
hypothesis discharged by a subsingleton case split; this is the form the wiring instantiates
at `Φ := pointedIsoCoordEquiv e heπ hez`. -/
lemma exists_coordX_image_of_filtration {W W' : WeierstrassCurve R}
    (Φ : W'.toAffine.CoordinateRing ≃ₐ[R] W.toAffine.CoordinateRing)
    (hfil : ∀ n, Submodule.map Φ.toLinearEquiv.toLinearMap (poleOrderFiltration W' n)
      = poleOrderFiltration W n) :
    ∃ α β : R, IsUnit α ∧
      Φ (coordX W') = algebraMap R _ α * coordX W + algebraMap R _ β := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · have : Subsingleton W.toAffine.CoordinateRing := subsingleton_coordinateRing W
    exact ⟨1, 0, isUnit_one, Subsingleton.elim _ _⟩
  · exact exists_coordX_image Φ hfil

/-- **(T-W7.1b-b3y, general base)** The `y`-image extraction with the `[Nontrivial R]`
hypothesis discharged by a subsingleton case split. -/
lemma exists_coordY_image_of_filtration {W W' : WeierstrassCurve R}
    (Φ : W'.toAffine.CoordinateRing ≃ₐ[R] W.toAffine.CoordinateRing)
    (hfil : ∀ n, Submodule.map Φ.toLinearEquiv.toLinearMap (poleOrderFiltration W' n)
      = poleOrderFiltration W n) :
    ∃ γ δ ε : R, IsUnit γ ∧
      Φ (coordY W') = algebraMap R _ γ * coordY W + algebraMap R _ δ * coordX W
        + algebraMap R _ ε := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · have : Subsingleton W.toAffine.CoordinateRing := subsingleton_coordinateRing W
    exact ⟨1, 0, 0, isUnit_one, Subsingleton.elim _ _⟩
  · exact exists_coordY_image Φ hfil

open Polynomial

private lemma hAX (W : WeierstrassCurve R) :
    algebraMap (R[X]) W.toAffine.CoordinateRing Polynomial.X = coordX W := rfl

private lemma hAC (W : WeierstrassCurve R) (a : R) :
    algebraMap (R[X]) W.toAffine.CoordinateRing (Polynomial.C a)
      = algebraMap R W.toAffine.CoordinateRing a := by
  rw [IsScalarTower.algebraMap_apply R (Polynomial R) W.toAffine.CoordinateRing,
    Polynomial.algebraMap_eq]

private lemma six_ext {W : WeierstrassCurve R} [Nontrivial R]
    {c₀ c₁ c₂ c₃ d₀ d₁ c₀' c₁' c₂' c₃' d₀' d₁' : R}
    (h : algebraMap R W.toAffine.CoordinateRing c₀ + algebraMap R _ c₁ * coordX W
          + algebraMap R _ c₂ * coordX W ^ 2 + algebraMap R _ c₃ * coordX W ^ 3
          + algebraMap R _ d₀ * coordY W + algebraMap R _ d₁ * (coordX W * coordY W)
        = algebraMap R _ c₀' + algebraMap R _ c₁' * coordX W
          + algebraMap R _ c₂' * coordX W ^ 2 + algebraMap R _ c₃' * coordX W ^ 3
          + algebraMap R _ d₀' * coordY W + algebraMap R _ d₁' * (coordX W * coordY W)) :
    c₀ = c₀' ∧ c₁ = c₁' ∧ c₂ = c₂' ∧ c₃ = c₃' ∧ d₀ = d₀' ∧ d₁ = d₁' := by
  have hzero : (Polynomial.C (c₀ - c₀') + Polynomial.C (c₁ - c₁') * Polynomial.X
        + Polynomial.C (c₂ - c₂') * Polynomial.X ^ 2 + Polynomial.C (c₃ - c₃') * Polynomial.X ^ 3)
        • (1 : W.toAffine.CoordinateRing)
      + (Polynomial.C (d₀ - d₀') + Polynomial.C (d₁ - d₁') * Polynomial.X) • coordY W = 0 := by
    simp only [Algebra.smul_def, map_add, map_mul, map_pow, hAX, hAC, map_sub, mul_one]
    linear_combination h
  obtain ⟨hp, hq⟩ := WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero
    (W' := W.toAffine) hzero
  have hp0 := congrArg (fun p => Polynomial.coeff p 0) hp
  have hp1 := congrArg (fun p => Polynomial.coeff p 1) hp
  have hp2 := congrArg (fun p => Polynomial.coeff p 2) hp
  have hp3 := congrArg (fun p => Polynomial.coeff p 3) hp
  have hq0 := congrArg (fun p => Polynomial.coeff p 0) hq
  have hq1 := congrArg (fun p => Polynomial.coeff p 1) hq
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_zero] at hp0 hp1 hp2 hp3 hq0 hq1
  norm_num at hp0 hp1 hp2 hp3 hq0 hq1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    [(rw [← sub_eq_zero]; exact hp0); (rw [← sub_eq_zero]; exact hp1);
     (rw [← sub_eq_zero]; exact hp2); (rw [← sub_eq_zero]; exact hp3);
     (rw [← sub_eq_zero]; exact hq0); (rw [← sub_eq_zero]; exact hq1)]

/-- The scaling unit of a Weierstrass variable change: if `α` and `γ` are units of a commutative
ring with `γ ^ 2 = α ^ 3`, then there is a unit `u` with `u ^ 2 = α` and `u ^ 3 = γ` (morally
`u = γ / α`). Packages the `u`-construction of `exists_variableChange_of_filtration`, where the
relation `γ ^ 2 = α ^ 3` comes from equating the `coordX ^ 3` coefficients of the two Weierstrass
relations. -/
private lemma exists_unit_sq_cube {α γ : R} (hα : IsUnit α) (hγ : IsUnit γ)
    (h : γ ^ 2 = α ^ 3) : ∃ u : Rˣ, (↑u : R) ^ 2 = α ∧ (↑u : R) ^ 3 = γ := by
  obtain ⟨uα, hαs⟩ := hα
  obtain ⟨uγ, hγs⟩ := hγ
  have hu_val : (↑(uγ * uα⁻¹) : R) = γ * (↑uα⁻¹ : R) := by rw [Units.val_mul, hγs]
  have hvα : α * (↑uα⁻¹ : R) = 1 := by rw [← hαs]; exact uα.mul_inv
  refine ⟨uγ * uα⁻¹, ?_, ?_⟩
  · rw [hu_val]
    linear_combination (↑uα⁻¹ : R) ^ 2 * h + α * (α * (↑uα⁻¹ : R) + 1) * hvα
  · rw [hu_val]
    linear_combination γ * (↑uα⁻¹ : R) ^ 3 * h
      + γ * ((α * (↑uα⁻¹ : R)) ^ 2 + α * (↑uα⁻¹ : R) + 1) * hvα

lemma exists_variableChange_of_filtration {W W' : WeierstrassCurve R}
    (Φ : W'.toAffine.CoordinateRing ≃ₐ[R] W.toAffine.CoordinateRing)
    (hfil : ∀ n, Submodule.map Φ.toLinearEquiv.toLinearMap (poleOrderFiltration W' n)
      = poleOrderFiltration W n) :
    ∃ C : VariableChange R, C • W' = W ∧
      Φ (coordX W') = algebraMap R _ ((↑C.u : R) ^ 2) * coordX W + algebraMap R _ C.r ∧
      Φ (coordY W') = algebraMap R _ ((↑C.u : R) ^ 3) * coordY W
        + algebraMap R _ (C.s * (↑C.u : R) ^ 2) * coordX W + algebraMap R _ C.t := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · refine ⟨1, ?_, ?_, ?_⟩
    · ext <;> exact Subsingleton.elim _ _
    · have := subsingleton_coordinateRing W; exact Subsingleton.elim _ _
    · have := subsingleton_coordinateRing W; exact Subsingleton.elim _ _
  · obtain ⟨α, β, hα, hx⟩ := exists_coordX_image Φ hfil
    obtain ⟨γ, δ, ε, hγ, hy⟩ := exists_coordY_image Φ hfil
    have hM := congrArg Φ (coordY_mul_coordY W')
    simp only [map_mul, map_add, map_sub, map_pow, AlgEquiv.commutes] at hM
    rw [hx, hy] at hM
    have hinput :
        algebraMap R W.toAffine.CoordinateRing (γ ^ 2 * W.toAffine.a₆ + ε ^ 2)
          + algebraMap R _ (γ ^ 2 * W.toAffine.a₄ + 2 * δ * ε) * coordX W
          + algebraMap R _ (γ ^ 2 * W.toAffine.a₂ + δ ^ 2) * coordX W ^ 2
          + algebraMap R _ (γ ^ 2) * coordX W ^ 3
          + algebraMap R _ (2 * γ * ε - γ ^ 2 * W.toAffine.a₃) * coordY W
          + algebraMap R _ (2 * γ * δ - γ ^ 2 * W.toAffine.a₁) * (coordX W * coordY W)
        = algebraMap R _ (β ^ 3 + W'.toAffine.a₂ * β ^ 2 + W'.toAffine.a₄ * β + W'.toAffine.a₆
              - W'.toAffine.a₁ * β * ε - W'.toAffine.a₃ * ε)
          + algebraMap R _ (3 * α * β ^ 2 + 2 * W'.toAffine.a₂ * α * β + W'.toAffine.a₄ * α
              - W'.toAffine.a₁ * (α * ε + β * δ) - W'.toAffine.a₃ * δ) * coordX W
          + algebraMap R _ (3 * α ^ 2 * β + W'.toAffine.a₂ * α ^ 2 - W'.toAffine.a₁ * α * δ)
              * coordX W ^ 2
          + algebraMap R _ (α ^ 3) * coordX W ^ 3
          + algebraMap R _ (-(W'.toAffine.a₁ * β * γ) - W'.toAffine.a₃ * γ) * coordY W
          + algebraMap R _ (-(W'.toAffine.a₁ * α * γ)) * (coordX W * coordY W) := by
      simp only [map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat]
      linear_combination hM
        - (algebraMap R W.toAffine.CoordinateRing γ) ^ 2 * coordY_mul_coordY W
    obtain ⟨e_x0, e_x1, e_x2, e_x3, e_y, e_xy⟩ := six_ext hinput
    obtain ⟨u, hu2, hu3⟩ := exists_unit_sq_cube hα hγ e_x3
    simp only [← hu2, ← hu3] at e_x0 e_x1 e_x2 e_y e_xy
    have h6 : IsUnit ((↑u : R) ^ 6) := by
      rw [← Units.val_pow_eq_pow_val]; exact (u ^ 6).isUnit
    refine ⟨⟨u, β, δ * (↑u⁻¹ : R) ^ 2, ε⟩, ?_, ?_, ?_⟩
    · ext
      · rw [variableChange_a₁]
        dsimp only
        refine h6.mul_right_inj.mp ?_
        linear_combination e_xy
          + (2*(↑u:R)^5*(↑u⁻¹:R)^2*δ + (↑u:R)^5*W'.toAffine.a₁ + 2*(↑u:R)^4*(↑u⁻¹:R)*δ
            + 2*(↑u:R)^3*δ) * u.mul_inv
      · rw [variableChange_a₂]
        dsimp only
        refine h6.mul_right_inj.mp ?_
        linear_combination -e_x2
          + (-(↑u:R)^5*(↑u⁻¹:R)^5*δ^2 - (↑u:R)^5*(↑u⁻¹:R)^3*W'.toAffine.a₁*δ
            + (↑u:R)^5*(↑u⁻¹:R)*W'.toAffine.a₂ + 3*(↑u:R)^5*(↑u⁻¹:R)*β - (↑u:R)^4*(↑u⁻¹:R)^4*δ^2
            - (↑u:R)^4*(↑u⁻¹:R)^2*W'.toAffine.a₁*δ + (↑u:R)^4*W'.toAffine.a₂ + 3*(↑u:R)^4*β
            - (↑u:R)^3*(↑u⁻¹:R)^3*δ^2 - (↑u:R)^3*(↑u⁻¹:R)*W'.toAffine.a₁*δ - (↑u:R)^2*(↑u⁻¹:R)^2*δ^2
            - (↑u:R)^2*W'.toAffine.a₁*δ - (↑u:R)*(↑u⁻¹:R)*δ^2 - δ^2) * u.mul_inv
      · rw [variableChange_a₃]
        dsimp only
        refine h6.mul_right_inj.mp ?_
        linear_combination e_y
          + ((↑u:R)^5*(↑u⁻¹:R)^2*W'.toAffine.a₁*β + (↑u:R)^5*(↑u⁻¹:R)^2*W'.toAffine.a₃
            + 2*(↑u:R)^5*(↑u⁻¹:R)^2*ε + (↑u:R)^4*(↑u⁻¹:R)*W'.toAffine.a₁*β
            + (↑u:R)^4*(↑u⁻¹:R)*W'.toAffine.a₃ + 2*(↑u:R)^4*(↑u⁻¹:R)*ε + (↑u:R)^3*W'.toAffine.a₁*β
            + (↑u:R)^3*W'.toAffine.a₃ + 2*(↑u:R)^3*ε) * u.mul_inv
      · rw [variableChange_a₄]
        dsimp only
        refine h6.mul_right_inj.mp ?_
        linear_combination -e_x1
          + (-(↑u:R)^5*(↑u⁻¹:R)^5*W'.toAffine.a₁*β*δ - (↑u:R)^5*(↑u⁻¹:R)^5*W'.toAffine.a₃*δ
            - 2*(↑u:R)^5*(↑u⁻¹:R)^5*δ*ε - (↑u:R)^5*(↑u⁻¹:R)^3*W'.toAffine.a₁*ε
            + 2*(↑u:R)^5*(↑u⁻¹:R)^3*W'.toAffine.a₂*β + (↑u:R)^5*(↑u⁻¹:R)^3*W'.toAffine.a₄
            + 3*(↑u:R)^5*(↑u⁻¹:R)^3*β^2 - (↑u:R)^4*(↑u⁻¹:R)^4*W'.toAffine.a₁*β*δ
            - (↑u:R)^4*(↑u⁻¹:R)^4*W'.toAffine.a₃*δ - 2*(↑u:R)^4*(↑u⁻¹:R)^4*δ*ε
            - (↑u:R)^4*(↑u⁻¹:R)^2*W'.toAffine.a₁*ε + 2*(↑u:R)^4*(↑u⁻¹:R)^2*W'.toAffine.a₂*β
            + (↑u:R)^4*(↑u⁻¹:R)^2*W'.toAffine.a₄ + 3*(↑u:R)^4*(↑u⁻¹:R)^2*β^2
            - (↑u:R)^3*(↑u⁻¹:R)^3*W'.toAffine.a₁*β*δ - (↑u:R)^3*(↑u⁻¹:R)^3*W'.toAffine.a₃*δ
            - 2*(↑u:R)^3*(↑u⁻¹:R)^3*δ*ε - (↑u:R)^3*(↑u⁻¹:R)*W'.toAffine.a₁*ε
            + 2*(↑u:R)^3*(↑u⁻¹:R)*W'.toAffine.a₂*β + (↑u:R)^3*(↑u⁻¹:R)*W'.toAffine.a₄
            + 3*(↑u:R)^3*(↑u⁻¹:R)*β^2 - (↑u:R)^2*(↑u⁻¹:R)^2*W'.toAffine.a₁*β*δ
            - (↑u:R)^2*(↑u⁻¹:R)^2*W'.toAffine.a₃*δ - 2*(↑u:R)^2*(↑u⁻¹:R)^2*δ*ε
            - (↑u:R)^2*W'.toAffine.a₁*ε + 2*(↑u:R)^2*W'.toAffine.a₂*β + (↑u:R)^2*W'.toAffine.a₄
            + 3*(↑u:R)^2*β^2 - (↑u:R)*(↑u⁻¹:R)*W'.toAffine.a₁*β*δ - (↑u:R)*(↑u⁻¹:R)*W'.toAffine.a₃*δ
            - 2*(↑u:R)*(↑u⁻¹:R)*δ*ε - W'.toAffine.a₁*β*δ - W'.toAffine.a₃*δ - 2*δ*ε) * u.mul_inv
      · rw [variableChange_a₆]
        dsimp only
        refine h6.mul_right_inj.mp ?_
        linear_combination -e_x0
          + (-(↑u:R)^5*(↑u⁻¹:R)^5*W'.toAffine.a₁*β*ε + (↑u:R)^5*(↑u⁻¹:R)^5*W'.toAffine.a₂*β^2
            - (↑u:R)^5*(↑u⁻¹:R)^5*W'.toAffine.a₃*ε + (↑u:R)^5*(↑u⁻¹:R)^5*W'.toAffine.a₄*β
            + (↑u:R)^5*(↑u⁻¹:R)^5*W'.toAffine.a₆ + (↑u:R)^5*(↑u⁻¹:R)^5*β^3 - (↑u:R)^5*(↑u⁻¹:R)^5*ε^2
            - (↑u:R)^4*(↑u⁻¹:R)^4*W'.toAffine.a₁*β*ε + (↑u:R)^4*(↑u⁻¹:R)^4*W'.toAffine.a₂*β^2
            - (↑u:R)^4*(↑u⁻¹:R)^4*W'.toAffine.a₃*ε + (↑u:R)^4*(↑u⁻¹:R)^4*W'.toAffine.a₄*β
            + (↑u:R)^4*(↑u⁻¹:R)^4*W'.toAffine.a₆ + (↑u:R)^4*(↑u⁻¹:R)^4*β^3 - (↑u:R)^4*(↑u⁻¹:R)^4*ε^2
            - (↑u:R)^3*(↑u⁻¹:R)^3*W'.toAffine.a₁*β*ε + (↑u:R)^3*(↑u⁻¹:R)^3*W'.toAffine.a₂*β^2
            - (↑u:R)^3*(↑u⁻¹:R)^3*W'.toAffine.a₃*ε + (↑u:R)^3*(↑u⁻¹:R)^3*W'.toAffine.a₄*β
            + (↑u:R)^3*(↑u⁻¹:R)^3*W'.toAffine.a₆ + (↑u:R)^3*(↑u⁻¹:R)^3*β^3 - (↑u:R)^3*(↑u⁻¹:R)^3*ε^2
            - (↑u:R)^2*(↑u⁻¹:R)^2*W'.toAffine.a₁*β*ε + (↑u:R)^2*(↑u⁻¹:R)^2*W'.toAffine.a₂*β^2
            - (↑u:R)^2*(↑u⁻¹:R)^2*W'.toAffine.a₃*ε + (↑u:R)^2*(↑u⁻¹:R)^2*W'.toAffine.a₄*β
            + (↑u:R)^2*(↑u⁻¹:R)^2*W'.toAffine.a₆ + (↑u:R)^2*(↑u⁻¹:R)^2*β^3 - (↑u:R)^2*(↑u⁻¹:R)^2*ε^2
            - (↑u:R)*(↑u⁻¹:R)*W'.toAffine.a₁*β*ε + (↑u:R)*(↑u⁻¹:R)*W'.toAffine.a₂*β^2
            - (↑u:R)*(↑u⁻¹:R)*W'.toAffine.a₃*ε + (↑u:R)*(↑u⁻¹:R)*W'.toAffine.a₄*β
            + (↑u:R)*(↑u⁻¹:R)*W'.toAffine.a₆ + (↑u:R)*(↑u⁻¹:R)*β^3 - (↑u:R)*(↑u⁻¹:R)*ε^2
            - W'.toAffine.a₁*β*ε + W'.toAffine.a₂*β^2 - W'.toAffine.a₃*ε + W'.toAffine.a₄*β
            + W'.toAffine.a₆ + β^3 - ε^2) * u.mul_inv
    · dsimp only
      rw [hx, hu2]
    · dsimp only
      rw [hy, hu3,
        show δ * (↑u⁻¹ : R) ^ 2 * (↑u : R) ^ 2 = δ from by
          rw [mul_assoc, pow_mul_pow_eq_one 2 u.inv_mul, mul_one]]

end ModularCurves
