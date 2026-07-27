/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.FiniteType
import ModularCurves.EllipticCurve.PoleFiltrationMonomialSequence

/-!
# The ordered monomial basis of the model pole filtration

The existing model filtration basis is reindexed so that its vectors are
literally `1, x, y, x², xy, x³, ...`.
-/

open AlgebraicGeometry

universe u

namespace ModularCurves

private noncomputable def poleOrderMonomialEndomorphism
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {n : ℕ} (hn : 1 ≤ n) :
    poleOrderFiltration W n →ₗ[R] poleOrderFiltration W n :=
  (poleOrderFiltrationBasis W hn).constr R fun i =>
    ⟨poleOrderMonomialSequence W i,
      poleOrderMonomialSequence_mem W hn i⟩

private theorem poleOrderMonomialEndomorphism_surjective
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {n : ℕ} (hn : 1 ≤ n) :
    Function.Surjective (poleOrderMonomialEndomorphism W hn) := by
  rw [← LinearMap.range_eq_top,
    poleOrderMonomialEndomorphism,
    Module.Basis.constr_range]
  exact
    (Submodule.span_range_subtype_eq_top_iff
      (poleOrderFiltration W n)
      (fun i : Fin n => poleOrderMonomialSequence_mem W hn i)).2
      (span_poleOrderMonomialSequence W hn)

/-- The basis of `Fₙ` ordered by increasing pole order:
`1, x, y, x², xy, x³, ...`. -/
noncomputable def poleOrderFiltrationMonomialBasis
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {n : ℕ} (hn : 1 ≤ n) :
    Module.Basis (Fin n) R (poleOrderFiltration W n) := by
  let b := poleOrderFiltrationBasis W hn
  letI : Module.Finite R (poleOrderFiltration W n) :=
    Module.Finite.of_basis b
  exact b.map
    (LinearEquiv.ofBijective
      (poleOrderMonomialEndomorphism W hn)
      (OrzechProperty.bijective_of_surjective_endomorphism
        (poleOrderMonomialEndomorphism W hn)
        (poleOrderMonomialEndomorphism_surjective W hn)))

@[simp]
theorem poleOrderFiltrationMonomialBasis_apply
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    poleOrderFiltrationMonomialBasis W hn i =
      ⟨poleOrderMonomialSequence W i,
        poleOrderMonomialSequence_mem W hn i⟩ := by
  rw [poleOrderFiltrationMonomialBasis,
    Module.Basis.map_apply, LinearEquiv.ofBijective_apply,
    poleOrderMonomialEndomorphism,
    Module.Basis.constr_basis]

end ModularCurves
