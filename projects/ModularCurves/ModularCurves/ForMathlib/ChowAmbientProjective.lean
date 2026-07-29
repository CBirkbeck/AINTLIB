/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.AffineProjectiveClosureFactorization
import ModularCurves.ForMathlib.FiniteProperClosureProjective
import ModularCurves.ForMathlib.NoetherianChowCover

/-!
# Projectivity of the Chow ambient scheme

The finite scheme-theoretic closure assembled from a nonempty finite affine cover has an explicit
projective factorization over the affine base.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FiniteAffineImageCover

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (xπ : X ⟶ Spec (.of R)) {ι : Type u} [Finite ι] [Nonempty ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
variable [IsNoetherian X] [LocallyOfFinitePresentation xπ]

/-- The ambient finite closure in the Chow construction is projective over the affine base. -/
lemma chowAmbientπ_isProjectiveFactorization :
    AlgebraicGeometry.IsProjectiveFactorization (chowAmbientπ xπ U hU) := by
  unfold chowAmbientπ
  apply FiniteProperClosure.π_isProjectiveFactorization
  exact projectiveπ_isProjectiveFactorization xπ U hU

end AlgebraicGeometry.Scheme.FiniteAffineImageCover
