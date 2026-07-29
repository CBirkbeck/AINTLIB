/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleFiltration

/-!
# Exhaustivity of the Weierstrass pole filtration

Every regular function on the affine Weierstrass chart has some finite pole
order at the zero section.
-/

open AlgebraicGeometry

universe u

namespace ModularCurves

noncomputable section

/-- The pole-order filtration is increasing. -/
theorem poleOrderFiltration_mono
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {m n : ℕ} (hmn : m ≤ n) :
    poleOrderFiltration W m ≤ poleOrderFiltration W n := by
  unfold poleOrderFiltration
  apply Submodule.span_mono
  rintro g (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
  · exact Or.inl ⟨i, hi.trans hmn, rfl⟩
  · exact Or.inr ⟨i, hi.trans hmn, rfl⟩

private theorem exists_adjoinRoot_of_mem_poleOrderFiltration
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (p : Polynomial R) :
    ∃ n : ℕ, AdjoinRoot.of W.toAffine.polynomial p ∈
      poleOrderFiltration W n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨m, hm⟩ := hp
      obtain ⟨n, hn⟩ := hq
      refine ⟨max m n, ?_⟩
      rw [map_add]
      exact Submodule.add_mem _
        (poleOrderFiltration_mono W (le_max_left m n) hm)
        (poleOrderFiltration_mono W (le_max_right m n) hn)
  | monomial n a =>
      refine ⟨2 * n, ?_⟩
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      change algebraMap R W.toAffine.CoordinateRing a * coordX W ^ n ∈
        poleOrderFiltration W (2 * n)
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ a
        (Submodule.subset_span (Or.inl ⟨n, le_rfl, rfl⟩))

/-- The union of the finite pole-order stages is the whole affine Weierstrass
coordinate ring. -/
theorem exists_mem_poleOrderFiltration
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (f : W.toAffine.CoordinateRing) :
    ∃ n : ℕ, f ∈ poleOrderFiltration W n := by
  obtain ⟨p, q, rfl⟩ :=
    WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq f
  obtain ⟨m, hm⟩ := exists_adjoinRoot_of_mem_poleOrderFiltration W p
  obtain ⟨n, hn⟩ := exists_adjoinRoot_of_mem_poleOrderFiltration W q
  refine ⟨max m (n + 3), ?_⟩
  rw [WeierstrassCurve.Affine.CoordinateRing.smul,
    WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
  change AdjoinRoot.of W.toAffine.polynomial p +
      AdjoinRoot.of W.toAffine.polynomial q * coordY W ∈
    poleOrderFiltration W (max m (n + 3))
  apply Submodule.add_mem
  · exact poleOrderFiltration_mono W (le_max_left m (n + 3)) hm
  · apply poleOrderFiltration_mono W (le_max_right m (n + 3))
    apply poleOrderFiltration_mul_le W n 3
    apply Submodule.mul_mem_mul hn
    exact Submodule.subset_span
      (Or.inr ⟨0, by omega, by rw [pow_zero, one_mul]⟩)

end

end ModularCurves
