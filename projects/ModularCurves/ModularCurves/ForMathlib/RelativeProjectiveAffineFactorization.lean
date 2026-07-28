/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.RelativeProjectiveAffineBase

/-!
# Relative projective factorizations over affine opens

A relative projective factorization becomes an ordinary projective-space factorization after
restriction to an affine base open.
-/

open CategoryTheory

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.IsRelativeProjectiveFactorization

/-- Restricting a relative projective factorization to an affine open gives an ordinary
projective-space factorization over the section ring of that open. -/
theorem isProjectiveFactorization_affineOpen
    {k : Type u} [CommRing k] {X S : Scheme.{u}}
    {s : S ⟶ Spec (.of k)} {f : X ⟶ S}
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    IsProjectiveFactorization
      (morphismRestrict f U ≫ hU.isoSpec.hom) := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  obtain ⟨d, j, hj, hjf⟩ := h.restrict U
  let i :
      (f ⁻¹ᵁ U).toScheme ⟶
        Proj
          (MvPolynomial.homogeneousSubmodule
            (Fin (d + 1)) Γ(S, U)) :=
    j ≫ (relativeProjectiveAffineIso s d U hU).hom
  have hi : IsClosedImmersion i := by
    dsimp only [i]
    letI : IsClosedImmersion j := hj
    infer_instance
  refine ⟨d, i, hi, ?_⟩
  dsimp only [i]
  rw [Category.assoc,
    relativeProjectiveAffineIso_hom_homogeneousProjπ]
  rw [← Category.assoc, hjf]

end AlgebraicGeometry.IsRelativeProjectiveFactorization
