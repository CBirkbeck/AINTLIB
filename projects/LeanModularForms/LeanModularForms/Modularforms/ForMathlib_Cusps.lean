/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

@[expose] public section

/-!
# Cuspidal vanishing/boundedness from infinity-side hypotheses

Reduces vanishing/boundedness at an arbitrary cusp to vanishing/boundedness at the cusp
at infinity, by lifting along the `SL(2, ℤ)` action via
`OnePoint.isZeroAt_iff_forall_SL2Z` / `OnePoint.isBoundedAt_iff_forall_SL2Z`.
-/

open scoped MatrixGroups ModularForm UpperHalfPlane

/-- If `f ∣[k] A` is zero at imaginary infinity for every `A ∈ 𝒮ℒ`, then `f` is zero at every
cusp `c` of the arithmetic subgroup `𝒢`. -/
theorem zero_at_cusps_of_zero_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {k : ℤ}
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] (hc : IsCusp c 𝒢)
    (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsZeroAtImInfty (f ∣[k] A)) : c.IsZeroAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  exact (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun A _ ↦ hb A ⟨A, rfl⟩

