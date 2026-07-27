/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's
`CoherentCohomologyFinite.SegreProductChartTransitionGeometry`.
-/
import ModularCurves.ForMathlib.SegreProductChartTransitionAlgebra

/-!
# Geometry of transitions between product charts

The two affine charts in each projective factor induce the same map to projective space on their
common double homogeneous localization.
-/

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

noncomputable section

universe u v

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The first standard chart factors through its double-coordinate projective open. -/
@[reassoc]
lemma projectiveFirstChartToOverlapAway_toProj
    (R : Type u) [CommRing R] {σ : Type v} (i a : σ) :
    Spec.map
          (CommRingCat.ofHom
            (projectiveFirstChartToOverlapAway R i a)) ≫
        Proj.awayι
          (homogeneousSubmodule σ R)
          (X i)
          (X_mem_homogeneousSubmodule_one R i)
          Nat.zero_lt_one =
      Proj.awayι
        (homogeneousSubmodule σ R)
        (X i * X a)
        (SetLike.mul_mem_graded
          (X_mem_homogeneousSubmodule_one R i)
          (X_mem_homogeneousSubmodule_one R a))
        (by omega) := by
  exact Proj.SpecMap_awayMap_awayι
    (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R i)
    Nat.zero_lt_one
    (X_mem_homogeneousSubmodule_one R a)
    rfl

/-- The second standard chart factors through the same double-coordinate projective open. -/
@[reassoc]
lemma projectiveSecondChartToOverlapAway_toProj
    (R : Type u) [CommRing R] {σ : Type v} (i a : σ) :
    Spec.map
          (CommRingCat.ofHom
            (projectiveSecondChartToOverlapAway R i a)) ≫
        Proj.awayι
          (homogeneousSubmodule σ R)
          (X a)
          (X_mem_homogeneousSubmodule_one R a)
          Nat.zero_lt_one =
      Proj.awayι
        (homogeneousSubmodule σ R)
        (X i * X a)
        (SetLike.mul_mem_graded
          (X_mem_homogeneousSubmodule_one R i)
          (X_mem_homogeneousSubmodule_one R a))
        (by omega) := by
  exact Proj.SpecMap_awayMap_awayι
    (homogeneousSubmodule σ R)
    (X_mem_homogeneousSubmodule_one R a)
    Nat.zero_lt_one
    (X_mem_homogeneousSubmodule_one R i)
    (mul_comm (X i) (X a))

end MvPolynomial
