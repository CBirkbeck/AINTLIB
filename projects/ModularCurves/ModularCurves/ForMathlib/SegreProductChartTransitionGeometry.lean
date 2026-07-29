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

/-- The first and second affine charts in the first factor agree on the product overlap. -/
lemma segreProductOverlapLeftChartTransition_toProj
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec.map
          (CommRingCat.ofHom
            (segreProductOverlapLeftRingHom R m n i a j b)) ≫
        Proj.awayι
          (homogeneousSubmodule (Fin (m + 1)) R)
          (X i)
          (X_mem_homogeneousSubmodule_one R i)
          Nat.zero_lt_one =
      Spec.map
          (CommRingCat.ofHom
            (segreProductSecondLeftRingHom R m n i a j b)) ≫
        Proj.awayι
          (homogeneousSubmodule (Fin (m + 1)) R)
          (X a)
          (X_mem_homogeneousSubmodule_one R a)
          Nat.zero_lt_one := by
  let liftMap :=
    Spec.map
      (CommRingCat.ofHom
        (segreProductLeftOverlapLift R m n i a j b))
  calc
    _ = (liftMap ≫
          Spec.map
            (CommRingCat.ofHom
              (projectiveFirstChartToOverlapAway R i a))) ≫
          Proj.awayι
            (homogeneousSubmodule (Fin (m + 1)) R)
            (X i)
            (X_mem_homogeneousSubmodule_one R i)
            Nat.zero_lt_one := by
      rw [← Spec.map_comp]
      have hcat :
          CommRingCat.ofHom (projectiveFirstChartToOverlapAway R i a) ≫
              CommRingCat.ofHom
                (segreProductLeftOverlapLift R m n i a j b) =
            CommRingCat.ofHom
              (segreProductOverlapLeftRingHom R m n i a j b) := by
        ext x
        exact DFunLike.congr_fun
          (segreProductLeftOverlapLift_comp_first R m n i a j b) x
      rw [hcat]
    _ = liftMap ≫
          (Spec.map
              (CommRingCat.ofHom
                (projectiveFirstChartToOverlapAway R i a)) ≫
            Proj.awayι
              (homogeneousSubmodule (Fin (m + 1)) R)
              (X i)
              (X_mem_homogeneousSubmodule_one R i)
              Nat.zero_lt_one) := by
      rw [Category.assoc]
    _ = liftMap ≫
          Proj.awayι
            (homogeneousSubmodule (Fin (m + 1)) R)
            (X i * X a)
            (SetLike.mul_mem_graded
              (X_mem_homogeneousSubmodule_one R i)
              (X_mem_homogeneousSubmodule_one R a))
            (by omega) := by
      rw [projectiveFirstChartToOverlapAway_toProj]
    _ = liftMap ≫
          (Spec.map
              (CommRingCat.ofHom
                (projectiveSecondChartToOverlapAway R i a)) ≫
            Proj.awayι
              (homogeneousSubmodule (Fin (m + 1)) R)
              (X a)
              (X_mem_homogeneousSubmodule_one R a)
              Nat.zero_lt_one) := by
      rw [projectiveSecondChartToOverlapAway_toProj]
    _ = (liftMap ≫
          Spec.map
            (CommRingCat.ofHom
              (projectiveSecondChartToOverlapAway R i a))) ≫
          Proj.awayι
            (homogeneousSubmodule (Fin (m + 1)) R)
            (X a)
            (X_mem_homogeneousSubmodule_one R a)
            Nat.zero_lt_one := by
      rw [Category.assoc]
    _ = _ := by
      rw [← Spec.map_comp]
      rfl

/-- The first and second affine charts in the second factor agree on the product overlap. -/
lemma segreProductOverlapRightChartTransition_toProj
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec.map
          (CommRingCat.ofHom
            (segreProductOverlapRightRingHom R m n i a j b)) ≫
        Proj.awayι
          (homogeneousSubmodule (Fin (n + 1)) R)
          (X j)
          (X_mem_homogeneousSubmodule_one R j)
          Nat.zero_lt_one =
      Spec.map
          (CommRingCat.ofHom
            (segreProductSecondRightRingHom R m n i a j b)) ≫
        Proj.awayι
          (homogeneousSubmodule (Fin (n + 1)) R)
          (X b)
          (X_mem_homogeneousSubmodule_one R b)
          Nat.zero_lt_one := by
  let liftMap :=
    Spec.map
      (CommRingCat.ofHom
        (segreProductRightOverlapLift R m n i a j b))
  calc
    _ = (liftMap ≫
          Spec.map
            (CommRingCat.ofHom
              (projectiveFirstChartToOverlapAway R j b))) ≫
          Proj.awayι
            (homogeneousSubmodule (Fin (n + 1)) R)
            (X j)
            (X_mem_homogeneousSubmodule_one R j)
            Nat.zero_lt_one := by
      rw [← Spec.map_comp]
      have hcat :
          CommRingCat.ofHom (projectiveFirstChartToOverlapAway R j b) ≫
              CommRingCat.ofHom
                (segreProductRightOverlapLift R m n i a j b) =
            CommRingCat.ofHom
              (segreProductOverlapRightRingHom R m n i a j b) := by
        ext x
        exact DFunLike.congr_fun
          (segreProductRightOverlapLift_comp_first R m n i a j b) x
      rw [hcat]
    _ = liftMap ≫
          (Spec.map
              (CommRingCat.ofHom
                (projectiveFirstChartToOverlapAway R j b)) ≫
            Proj.awayι
              (homogeneousSubmodule (Fin (n + 1)) R)
              (X j)
              (X_mem_homogeneousSubmodule_one R j)
              Nat.zero_lt_one) := by
      rw [Category.assoc]
    _ = liftMap ≫
          Proj.awayι
            (homogeneousSubmodule (Fin (n + 1)) R)
            (X j * X b)
            (SetLike.mul_mem_graded
              (X_mem_homogeneousSubmodule_one R j)
              (X_mem_homogeneousSubmodule_one R b))
            (by omega) := by
      rw [projectiveFirstChartToOverlapAway_toProj]
    _ = liftMap ≫
          (Spec.map
              (CommRingCat.ofHom
                (projectiveSecondChartToOverlapAway R j b)) ≫
            Proj.awayι
              (homogeneousSubmodule (Fin (n + 1)) R)
              (X b)
              (X_mem_homogeneousSubmodule_one R b)
              Nat.zero_lt_one) := by
      rw [projectiveSecondChartToOverlapAway_toProj]
    _ = (liftMap ≫
          Spec.map
            (CommRingCat.ofHom
              (projectiveSecondChartToOverlapAway R j b))) ≫
          Proj.awayι
            (homogeneousSubmodule (Fin (n + 1)) R)
            (X b)
            (X_mem_homogeneousSubmodule_one R b)
            Nat.zero_lt_one := by
      rw [Category.assoc]
    _ = _ := by
      rw [← Spec.map_comp]
      rfl

end MvPolynomial
