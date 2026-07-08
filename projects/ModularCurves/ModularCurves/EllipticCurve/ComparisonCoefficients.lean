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
    have hmem : coordX W ∈ Submodule.map Φ.toLinearEquiv.toLinearMap (poleOrderFiltration W' 2) := by
      rw [hfil 2]; exact hxmem
    obtain ⟨w, hw, hΦw⟩ := hmem
    have hΦw' : Φ w = coordX W := hΦw
    rw [← hΦw', Φ.symm_apply_apply]; exact hw
  rw [poleOrderFiltration_two, Submodule.mem_span_pair] at hxinv
  obtain ⟨c'', d'', hcd''⟩ := hxinv
  have hxinv_eq : Φ.symm (coordX W) = algebraMap R _ d'' * coordX W' + algebraMap R _ c'' := by
    rw [← hcd'', Algebra.smul_def, Algebra.smul_def, mul_one]; ring
  have hxback : algebraMap R _ (d'' * d) * coordX W + algebraMap R _ (d'' * c + c'') = coordX W := by
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
    have hmem : coordY W ∈ Submodule.map Φ.toLinearEquiv.toLinearMap (poleOrderFiltration W' 3) := by
      rw [hfil 3]; exact hymem
    obtain ⟨w, hw, hΦw⟩ := hmem
    have hΦw' : Φ w = coordY W := hΦw
    rw [← hΦw', Φ.symm_apply_apply]; exact hw
  rw [poleOrderFiltration_three, Submodule.mem_span_triple] at hyinv
  obtain ⟨a'', b'', c'', habc''⟩ := hyinv
  have hyinv_eq : Φ.symm (coordY W) = algebraMap R _ c'' * coordY W' + algebraMap R _ b'' * coordX W'
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

end ModularCurves
