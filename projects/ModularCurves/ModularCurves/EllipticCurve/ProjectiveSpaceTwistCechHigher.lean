/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechWeightAssembly
import ModularCurves.ForMathlib.OrderedCechSupportAlternating

/-!
# Higher exactness for nonnegative projective twists

This file assembles the all-degree support contraction from
[Stacks Project, Lemma 30.8.1 (Tag 01XT)](https://stacks.math.columbia.edu/tag/01XT) weight by
weight in the homogeneous Laurent presentation of the ordered Cech complex.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance : DecidableEq σ := Classical.decEq σ

/-- Every positive-degree cocycle in the homogeneous Laurent presentation of the ordered Cech
complex for a nonnegative projective twist is a boundary. -/
theorem exists_preimage_coordinateHomogeneousLaurentOrderedCechDifferential
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) (n : ℕ)
    (s : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d (n + 1))
    (hs : (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d (n + 1)).hom s = 0) :
    ∃ t : coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n,
      (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n).hom t = s := by
  classical
  have hcomponent_cycle (e : HomogeneousLaurentExponent σ d) :
      ModularCurves.orderedCechSupportDifferential
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.liftedNegativeSupport (n + 1)
          (coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s) = 0 := by
    rw [← coordinateHomogeneousLaurentWeightComponent_differential
      (R := R) (σ := σ) (d := d) (e := e) (n := n + 1), hs]
    exact map_zero
      (coordinateHomogeneousLaurentWeightComponent (R := R) d e (n + 2))
  have hpreimage (e : HomogeneousLaurentExponent σ d) :
      ∃ t : ModularCurves.OrderedCechSupportCochain
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.liftedNegativeSupport n,
        ModularCurves.orderedCechSupportDifferential
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            e.liftedNegativeSupport n t =
          coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s := by
    obtain ⟨i, hi⟩ := e.exists_not_mem_liftedNegativeSupport_of_nonneg j hd
    exact ModularCurves.exists_preimage_orderedCechSupportDifferential
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.liftedNegativeSupport i hi n
      (coordinateHomogeneousLaurentWeightComponent (R := R) d e (n + 1) s)
      (hcomponent_cycle e)
  choose t ht using hpreimage
  refine ⟨∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
    coordinateHomogeneousLaurentWeightInclusion (R := R) d e n (t e), ?_⟩
  rw [map_sum]
  calc
    (∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
        (coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom
          (coordinateHomogeneousLaurentWeightInclusion (R := R) d e n (t e))) =
      ∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
        coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (ModularCurves.orderedCechSupportDifferential
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            e.liftedNegativeSupport n (t e)) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [coordinateHomogeneousLaurentWeightInclusion_differential]
    _ = ∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
        coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [ht e]
    _ = s := coordinateHomogeneousLaurentActiveWeights_reconstruct d (n + 1) s

/-- Every positive-degree cocycle in the explicit standard-coordinate ordered Cech complex for a
nonnegative projective twist is a boundary. -/
theorem exists_preimage_coordinateHyperplaneTwistOrderedBaseCechDifferential
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) (n : ℕ)
    (s : Scheme.Modules.orderedBaseCechObject
      (homogeneousProjπ (R := R) (σ := σ))
      (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (coordinateOpenCover (R := R) (σ := σ)) (n + 1))
    (hs : (coordinateHyperplaneTwistOrderedBaseCechDifferential
      (R := R) (σ := σ) d (n + 1)).hom s = 0) :
    ∃ t : Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n,
      (coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d n).hom t = s := by
  have hs_weight :
      (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d (n + 1)).hom
          ((coordinateHomogeneousLaurentOrderedCechObjectIso
            (R := R) (σ := σ) d (n + 1)).hom.hom s) = 0 := by
    have h := congrArg (fun f => f.hom s)
      (coordinateHomogeneousLaurentOrderedCechDifferential_naturality
        (R := R) (σ := σ) d (n + 1))
    simpa [hs] using h
  obtain ⟨t, ht⟩ :=
    exists_preimage_coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) j d hd n
      ((coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d (n + 1)).hom.hom s) hs_weight
  refine ⟨(coordinateHomogeneousLaurentOrderedCechObjectIso
    (R := R) (σ := σ) d n).inv.hom t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (coordinateHomogeneousLaurentOrderedCechObjectIso
      (R := R) (σ := σ) d (n + 1)).hom).1
  have h := congrArg (fun f => f.hom
      ((coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d n).inv.hom t))
    (coordinateHomogeneousLaurentOrderedCechDifferential_naturality
      (R := R) (σ := σ) d n)
  have h' :
      (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n).hom
          ((coordinateHomogeneousLaurentOrderedCechObjectIso
            (R := R) (σ := σ) d n).hom.hom
            ((coordinateHomogeneousLaurentOrderedCechObjectIso
              (R := R) (σ := σ) d n).inv.hom t)) =
        (coordinateHomogeneousLaurentOrderedCechObjectIso
          (R := R) (σ := σ) d (n + 1)).hom.hom
          ((coordinateHyperplaneTwistOrderedBaseCechDifferential
            (R := R) (σ := σ) d n).hom
            ((coordinateHomogeneousLaurentOrderedCechObjectIso
              (R := R) (σ := σ) d n).inv.hom t)) := by
    simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] using h
  rw [← h']
  simpa using ht

/-- The explicit standard-coordinate ordered Cech complex for a nonnegative projective twist is
exact in every positive degree. -/
theorem coordinateHyperplaneTwistOrderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) (n : ℕ) :
    (coordinateHyperplaneTwistOrderedBaseCechComplex
      (R := R) j d).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) ((n + 1) + 1)
    (by simp) (by simp)]
  have hsc : (ShortComplex.mk
      (coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d n)
      (coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d (n + 1))
      (coordinateHyperplaneTwistOrderedBaseCechDifferential_comp
        (R := R) j d n)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro s hs
    exact exists_preimage_coordinateHyperplaneTwistOrderedBaseCechDifferential
      (R := R) (σ := σ) j d hd n s hs
  simpa only [HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor',
    coordinateHyperplaneTwistOrderedBaseCechComplex_X,
    coordinateHyperplaneTwistOrderedBaseCechComplex_d] using hsc

/-- The native ordered Cech complex of a nonnegative coordinate-hyperplane twist is exact in
every positive degree. -/
theorem coordinateHyperplaneTwist_orderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) (n : ℕ) :
    (Scheme.Modules.orderedBaseCechComplex
      (homogeneousProjπ (R := R) (σ := σ))
      (coordinateHyperplaneTwist (R := R) j d)
      (coordinateOpenCover (R := R) (σ := σ))).ExactAt (n + 1) := by
  exact (coordinateHyperplaneTwistOrderedBaseCechComplex_exactAt_succ
    (R := R) (σ := σ) j d hd n).of_iso
      (coordinateHyperplaneTwistOrderedBaseCechComplexIso
        (R := R) j d).symm

end

end MvPolynomial
