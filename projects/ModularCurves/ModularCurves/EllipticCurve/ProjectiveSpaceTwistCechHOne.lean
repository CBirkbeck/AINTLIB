/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechWeightAssembly
import ModularCurves.ForMathlib.SchemeModuleBaseCechHomology
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechHOne
import ModularCurves.Picard.InvertibleSheafLocallyFree

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

/-- Every degree-one cocycle in the explicit standard-coordinate ordered Cech complex for a
nonnegative projective twist is a boundary. -/
theorem exists_preimage_coordinateHyperplaneTwistOrderedBaseCechDifferential_zero
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d)
    (s : Scheme.Modules.orderedBaseCechObject
      (homogeneousProjπ (R := R) (σ := σ))
      (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (coordinateOpenCover (R := R) (σ := σ)) 1)
    (hs : (coordinateHyperplaneTwistOrderedBaseCechDifferential
      (R := R) (σ := σ) d 1).hom s = 0) :
    ∃ t : Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) 0,
      (coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d 0).hom t = s := by
  have hs_weight :
      (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d 1).hom
          ((coordinateHomogeneousLaurentOrderedCechObjectIso
            (R := R) (σ := σ) d 1).hom.hom s) = 0 := by
    have h := congrArg (fun f => f.hom s)
      (coordinateHomogeneousLaurentOrderedCechDifferential_naturality
        (R := R) (σ := σ) d 1)
    simpa [hs] using h
  obtain ⟨t, ht⟩ :=
    exists_preimage_coordinateHomogeneousLaurentOrderedCechDifferential_zero
      (R := R) (σ := σ) j d hd
      ((coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d 1).hom.hom s) hs_weight
  refine ⟨(coordinateHomogeneousLaurentOrderedCechObjectIso
    (R := R) (σ := σ) d 0).inv.hom t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (coordinateHomogeneousLaurentOrderedCechObjectIso
      (R := R) (σ := σ) d 1).hom).1
  have h := congrArg (fun f => f.hom
      ((coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d 0).inv.hom t))
    (coordinateHomogeneousLaurentOrderedCechDifferential_naturality
      (R := R) (σ := σ) d 0)
  have h' :
      (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d 0).hom
          ((coordinateHomogeneousLaurentOrderedCechObjectIso
            (R := R) (σ := σ) d 0).hom.hom
            ((coordinateHomogeneousLaurentOrderedCechObjectIso
              (R := R) (σ := σ) d 0).inv.hom t)) =
        (coordinateHomogeneousLaurentOrderedCechObjectIso
          (R := R) (σ := σ) d 1).hom.hom
          ((coordinateHyperplaneTwistOrderedBaseCechDifferential
            (R := R) (σ := σ) d 0).hom
            ((coordinateHomogeneousLaurentOrderedCechObjectIso
              (R := R) (σ := σ) d 0).inv.hom t)) := by
    simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] using h
  rw [← h']
  simpa using ht

/-- The explicit standard-coordinate ordered Cech complex for a nonnegative projective twist is
exact in degree one. -/
theorem coordinateHyperplaneTwistOrderedBaseCechComplex_exactAt_one
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) :
    (coordinateHyperplaneTwistOrderedBaseCechComplex
      (R := R) j d).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro s hs
  change (coordinateHyperplaneTwistOrderedBaseCechDifferential
    (R := R) (σ := σ) d 1).hom s = 0 at hs
  change ∃ t, (coordinateHyperplaneTwistOrderedBaseCechDifferential
    (R := R) (σ := σ) d 0).hom t = s
  exact exists_preimage_coordinateHyperplaneTwistOrderedBaseCechDifferential_zero
    (R := R) (σ := σ) j d hd s hs

/-- The native ordered Cech complex of a nonnegative coordinate-hyperplane twist is exact in
degree one. -/
theorem coordinateHyperplaneTwist_orderedBaseCechComplex_exactAt_one
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) :
    (Scheme.Modules.orderedBaseCechComplex
      (homogeneousProjπ (R := R) (σ := σ))
      (coordinateHyperplaneTwist (R := R) j d)
      (coordinateOpenCover (R := R) (σ := σ))).ExactAt 1 := by
  exact (coordinateHyperplaneTwistOrderedBaseCechComplex_exactAt_one
    (R := R) (σ := σ) j d hd).of_iso
      (coordinateHyperplaneTwistOrderedBaseCechComplexIso
        (R := R) j d).symm

/-- The native standard-coordinate Cech complex of a nonnegative coordinate-hyperplane twist is
exact in degree one. -/
theorem coordinateHyperplaneTwist_baseCechComplex_exactAt_one
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) :
    (Scheme.Modules.baseCechComplex
      (homogeneousProjπ (R := R) (σ := σ))
      (coordinateHyperplaneTwist (R := R) j d)
      (coordinateOpenCover (R := R) (σ := σ))).ExactAt 1 :=
  Scheme.Modules.baseCechComplex_exactAt_one_of_orderedBaseCechComplex_exactAt_one
    (homogeneousProjπ (R := R) (σ := σ))
    (coordinateHyperplaneTwist (R := R) j d)
    (coordinateOpenCover (R := R) (σ := σ))
    (coordinateHyperplaneTwist_orderedBaseCechComplex_exactAt_one
      (R := R) (σ := σ) j d hd)

/-- A nonnegative coordinate-hyperplane twist on polynomial projective space has vanishing first
sheaf cohomology. -/
theorem coordinateHyperplaneTwist_subsingleton_H_one
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) :
    Subsingleton (CategoryTheory.Sheaf.H
      (coordinateHyperplaneTwist (R := R) j d).sheaf 1) := by
  letI : (coordinateHyperplaneTwist (R := R) j d).IsQuasicoherent :=
    (coordinateHyperplaneTwist_isInvertible (R := R) j d).isQuasicoherent
  exact (Scheme.Modules.baseCechComplex_exactAt_one_iff_subsingleton_H
    (homogeneousProjπ (R := R) (σ := σ))
    (coordinateHyperplaneTwist (R := R) j d)
    (coordinateOpenCover (R := R) (σ := σ))
    (iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
    (coordinateOpenCover_isAffineOpen (R := R))).mp
      (coordinateHyperplaneTwist_baseCechComplex_exactAt_one
        (R := R) (σ := σ) j d hd)

end

end MvPolynomial
