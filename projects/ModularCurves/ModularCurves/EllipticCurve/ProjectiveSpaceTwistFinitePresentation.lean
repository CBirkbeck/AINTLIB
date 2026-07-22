/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwist

/-!
# Finite presentations by negative projective twists

This file reindexes the finite negative-twist quotient by a standard finite type.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every finite-type quasicoherent module on polynomial projective space is a quotient of a
`Fin`-indexed finite coproduct of powers of coordinate-hyperplane ideal modules. -/
theorem exists_fin_coordinateNegativeTwist_quotient [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ (r : ℕ) (j : Fin r → σ) (n : Fin r → ℕ)
        (f : (∐ fun i : Fin r ↦
          coordinateHyperplaneIdealModulePower (R := R) (j i) (n i)) ⟶ M),
      Epi f := by
  classical
  obtain ⟨I, hI, j, n, f, hf⟩ :=
    exists_finite_coordinateNegativeTwist_quotient M
  letI : Finite I := hI
  let e : Fin (Nat.card I) ≃ I := (Finite.equivFin I).symm
  let L : I → (Proj (homogeneousSubmodule σ R)).Modules := fun i ↦
    coordinateHyperplaneIdealModulePower (R := R) (j i) (n i)
  let g : (∐ fun k : Fin (Nat.card I) ↦ L (e k)) ⟶ M :=
    (Sigma.reindex e L).hom ≫ f
  refine ⟨Nat.card I, fun k ↦ j (e k), fun k ↦ n (e k), g, ?_⟩
  dsimp only [g]
  infer_instance

end

end MvPolynomial
