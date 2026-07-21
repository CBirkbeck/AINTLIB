/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechWeightAssembly

/-!
# Degree-one exactness for nonnegative projective twists

This file assembles the fixed-weight contraction from
[Stacks Project, Lemma 30.8.1 (Tag 01XT)](https://stacks.math.columbia.edu/tag/01XT) to prove
degree-one exactness of the homogeneous Laurent presentation of the ordered Cech complex for a
nonnegative projective twist.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance : DecidableEq σ := Classical.decEq σ

/-- Every degree-one cocycle in the homogeneous Laurent presentation of the ordered Cech complex
for a nonnegative projective twist is a boundary. -/
theorem exists_preimage_coordinateHomogeneousLaurentOrderedCechDifferential_zero
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d)
    (s : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d 1)
    (hs : (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d 1).hom s = 0) :
    ∃ t : coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d 0,
      (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d 0).hom t = s := by
  classical
  have hcomponent_cycle (e : HomogeneousLaurentExponent σ d) :
      ModularCurves.orderedCechSupportDifferential
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.liftedNegativeSupport 1
          (coordinateHomogeneousLaurentWeightComponent (R := R) d e 1 s) = 0 := by
    rw [← coordinateHomogeneousLaurentWeightComponent_differential
      (R := R) (σ := σ) (d := d) (e := e) (n := 1), hs]
    exact map_zero (coordinateHomogeneousLaurentWeightComponent (R := R) d e 2)
  have hpreimage (e : HomogeneousLaurentExponent σ d) :
      ∃ t : ModularCurves.OrderedCechSupportCochain
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.liftedNegativeSupport 0,
        ModularCurves.orderedCechSupportDifferential
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            e.liftedNegativeSupport 0 t =
          coordinateHomogeneousLaurentWeightComponent (R := R) d e 1 s := by
    obtain ⟨i, hi⟩ := e.exists_not_mem_liftedNegativeSupport_of_nonneg j hd
    exact ModularCurves.exists_preimage_orderedCechSupportDifferential_zero
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.liftedNegativeSupport i hi
      (coordinateHomogeneousLaurentWeightComponent (R := R) d e 1 s)
      (hcomponent_cycle e)
  choose t ht using hpreimage
  refine ⟨∑ e ∈ coordinateHomogeneousLaurentActiveWeights d 1 s,
    coordinateHomogeneousLaurentWeightInclusion (R := R) d e 0 (t e), ?_⟩
  rw [map_sum]
  calc
    (∑ e ∈ coordinateHomogeneousLaurentActiveWeights d 1 s,
        (coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d 0).hom
          (coordinateHomogeneousLaurentWeightInclusion (R := R) d e 0 (t e))) =
      ∑ e ∈ coordinateHomogeneousLaurentActiveWeights d 1 s,
        coordinateHomogeneousLaurentWeightInclusion (R := R) d e 1
          (ModularCurves.orderedCechSupportDifferential
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            e.liftedNegativeSupport 0 (t e)) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [coordinateHomogeneousLaurentWeightInclusion_differential]
    _ = ∑ e ∈ coordinateHomogeneousLaurentActiveWeights d 1 s,
        coordinateHomogeneousLaurentWeightInclusion (R := R) d e 1
          (coordinateHomogeneousLaurentWeightComponent (R := R) d e 1 s) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [ht e]
    _ = s := coordinateHomogeneousLaurentActiveWeights_reconstruct d 1 s

end

end MvPolynomial
