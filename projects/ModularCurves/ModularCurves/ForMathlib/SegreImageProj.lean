/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's
`CoherentCohomologyFinite.SegreProductProjComparison`.
-/
import ModularCurves.ForMathlib.ProjMapClosedImmersion
import ModularCurves.ForMathlib.SegreImageGrading

/-!
# The Segre image in polynomial projective space

The canonical coordinate map onto the graded Segre image is surjective.
It therefore induces a closed immersion from the `Proj` of the image
grading into the ambient polynomial `Proj`.
-/

open AlgebraicGeometry
open HomogeneousIdeal

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard coordinate map onto the Segre image, as a graded ring homomorphism. -/
def segreImageGradedHom
    (R : Type u) [CommRing R] (m n : ℕ) :
    homogeneousSubmodule (Fin (segreDimension m n + 1)) R →+*ᵍ
      segreImageGrading R m n where
  __ := (segreRangeCoordinateHom R m n).toRingHom
  map_mem := segreRangeCoordinateHom_mem_imageGrading R m n

lemma segreImageGradedHom_surjective
    (R : Type u) [CommRing R] (m n : ℕ) :
    Function.Surjective (segreImageGradedHom R m n) :=
  segreRangeCoordinateHom_surjective R m n

/-- The coordinate map satisfies the irrelevant-ideal condition for `Proj.map`. -/
lemma segreImageIrrelevant_le
    (R : Type u) [CommRing R] (m n : ℕ) :
    (segreImageGrading R m n)₊ ≤
      (homogeneousSubmodule (Fin (segreDimension m n + 1)) R)₊.map
        (segreImageGradedHom R m n) :=
  irrelevant_le_map_of_surjective
    (segreImageGradedHom R m n)
    (segreImageGradedHom_surjective R m n)

/-- The canonical morphism from the Segre image `Proj` to polynomial projective space. -/
def segreImageProjι
    (R : Type u) [CommRing R] (m n : ℕ) :
    Proj (segreImageGrading R m n) ⟶
      Proj (homogeneousSubmodule (Fin (segreDimension m n + 1)) R) :=
  Proj.map (segreImageGradedHom R m n) (segreImageIrrelevant_le R m n)

/-- The canonical Segre image morphism is a closed immersion. -/
lemma segreImageProjι_isClosedImmersion
    (R : Type u) [CommRing R] (m n : ℕ) :
    IsClosedImmersion (segreImageProjι R m n) :=
  isClosedImmersion_projMap_of_surjective
    (segreImageGradedHom R m n)
    (segreImageIrrelevant_le R m n)
    (segreImageGradedHom_surjective R m n)

end MvPolynomial
