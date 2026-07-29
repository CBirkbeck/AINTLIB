/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's `CoherentCohomologyFinite.SegreImageGrading`.
-/
import ModularCurves.ForMathlib.SegreCoordinatePresentation
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Subsemiring
import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-!
# The canonical grading on the Segre image algebra

The tensor product is graded by degree in its second factor. The Segre coordinate
map preserves this grading, so its image algebra inherits a canonical grading.
-/

open DirectSum
open scoped TensorProduct

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The tensor-product ring containing the Segre coordinate algebra. -/
abbrev SegreTensorRing
    (R : Type u) [CommRing R] (m n : ℕ) :=
  MvPolynomial (Fin (m + 1)) R ⊗[R] MvPolynomial (Fin (n + 1)) R

/-- Grade the tensor-product ring by polynomial degree in its second factor. -/
abbrev segreRightGrading
    (R : Type u) [CommRing R] (m n : ℕ) :
    ℕ → Submodule R (SegreTensorRing R m n) :=
  fun d =>
    ((homogeneousSubmodule (Fin (n + 1)) R d).baseChange
      (MvPolynomial (Fin (m + 1)) R)).restrictScalars R

instance segreRightGradingGradedRing
    (R : Type u) [CommRing R] (m n : ℕ) :
    GradedRing (segreRightGrading R m n) :=
  inferInstance

lemma segreStandardCoordinateValue_mem_degreeOne
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (segreDimension m n + 1)) :
    segreStandardCoordinateHom R m n (X i) ∈
      segreRightGrading R m n 1 := by
  rw [segreStandardCoordinateHom_X]
  exact Submodule.tmul_mem_baseChange_of_mem _
    (by
      rw [mem_homogeneousSubmodule]
      exact isHomogeneous_X R (segreIndexEquiv m n i).2)

lemma segreStandardCoordinateHom_eq_aeval
    (R : Type u) [CommRing R] (m n : ℕ) :
    segreStandardCoordinateHom R m n =
      MvPolynomial.aeval
        (fun i =>
          X (segreIndexEquiv m n i).1 ⊗ₜ[R]
            X (segreIndexEquiv m n i).2) := by
  ext i
  simp only [segreStandardCoordinateHom_X, aeval_X]

/-- The Segre coordinate map preserves standard degree. -/
lemma segreStandardCoordinateHom_mem_grading
    (R : Type u) [CommRing R] (m n : ℕ)
    {d : ℕ} {p : MvPolynomial (Fin (segreDimension m n + 1)) R}
    (hp : p ∈ homogeneousSubmodule (Fin (segreDimension m n + 1)) R d) :
    segreStandardCoordinateHom R m n p ∈ segreRightGrading R m n d := by
  rw [segreStandardCoordinateHom_eq_aeval]
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero =>
      exact (segreRightGrading R m n d).zero_mem
  | add p q hp hq ihp ihq =>
      simpa only [map_add] using (segreRightGrading R m n d).add_mem ihp ihq
  | monomial e r he =>
      rw [MvPolynomial.aeval_monomial]
      have hvariables :
          ∀ i ∈ e.support,
            (X (segreIndexEquiv m n i).1 ⊗ₜ[R]
                X (segreIndexEquiv m n i).2) ∈
              segreRightGrading R m n 1 := by
        intro i _
        simpa only [segreStandardCoordinateHom_X] using
          segreStandardCoordinateValue_mem_degreeOne R m n i
      have hproduct :
          e.prod
              (fun i exponent =>
                (X (segreIndexEquiv m n i).1 ⊗ₜ[R]
                  X (segreIndexEquiv m n i).2) ^ exponent) ∈
            segreRightGrading R m n (∑ i ∈ e.support, e i • 1) := by
        simpa only [Finsupp.prod] using
          (SetLike.prod_pow_mem_graded
            (segreRightGrading R m n)
            (fun _ => 1)
            (fun i =>
              X (segreIndexEquiv m n i).1 ⊗ₜ[R]
                X (segreIndexEquiv m n i).2)
            e hvariables)
      have hdegree : (∑ i ∈ e.support, e i • 1) = d := by
        change e.sum (fun _ c => c • 1) = d
        simpa only [Finsupp.weight_apply, Pi.one_apply,
          nsmul_eq_mul, mul_one] using he
      rw [hdegree] at hproduct
      have hcoeff :
          algebraMap R (SegreTensorRing R m n) r ∈
            segreRightGrading R m n 0 :=
        SetLike.algebraMap_mem_graded (segreRightGrading R m n) r
      simpa only [zero_add] using SetLike.mul_mem_graded hcoeff hproduct

/-- The coordinate map as a graded algebra homomorphism. -/
def segreStandardGradedHom
    (R : Type u) [CommRing R] (m n : ℕ) :
    homogeneousSubmodule (Fin (segreDimension m n + 1)) R →ₐᵍ[R]
      segreRightGrading R m n where
  __ := segreStandardCoordinateHom R m n
  map_mem := segreStandardCoordinateHom_mem_grading R m n

/-- The image algebra is homogeneous in the right-graded tensor product. -/
lemma segreCoordinateRing_isHomogeneous
    (R : Type u) [CommRing R] (m n : ℕ) :
    DirectSum.SetLike.IsHomogeneous
      (segreRightGrading R m n)
      (SegreCoordinateRing R m n : Subalgebra R (SegreTensorRing R m n)) := by
  intro d x hx
  obtain ⟨p, rfl⟩ := hx
  refine ⟨DirectSum.decompose
    (homogeneousSubmodule (Fin (segreDimension m n + 1)) R) p d, ?_⟩
  change
    segreStandardCoordinateHom R m n
        (DirectSum.decompose
          (homogeneousSubmodule (Fin (segreDimension m n + 1)) R) p d) =
      DirectSum.decompose
        (segreRightGrading R m n)
        (segreStandardCoordinateHom R m n p) d
  exact map_directSumDecompose
    (homogeneousSubmodule (Fin (segreDimension m n + 1)) R)
    (segreRightGrading R m n)
    (segreStandardGradedHom R m n).toGradedRingHom

/-- The degree-`d` piece of the Segre image algebra. -/
def segreImageGrading
    (R : Type u) [CommRing R] (m n d : ℕ) :
    Submodule R (SegreCoordinateRing R m n) :=
  (segreRightGrading R m n d).comap
    (Subalgebra.val (SegreCoordinateRing R m n)).toLinearMap

instance segreImageGradingGradedMonoid
    (R : Type u) [CommRing R] (m n : ℕ) :
    SetLike.GradedMonoid (segreImageGrading R m n) where
  one_mem := SetLike.one_mem_graded (segreRightGrading R m n)
  mul_mem i j x y hx hy := by
    change ((x * y : SegreCoordinateRing R m n) : SegreTensorRing R m n) ∈
      segreRightGrading R m n (i + j)
    change (x : SegreTensorRing R m n) ∈ segreRightGrading R m n i at hx
    change (y : SegreTensorRing R m n) ∈ segreRightGrading R m n j at hy
    exact SetLike.mul_mem_graded hx hy

lemma segreImageGrading_iSupIndep
    (R : Type u) [CommRing R] (m n : ℕ) :
    iSupIndep (segreImageGrading R m n) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  apply Subtype.ext
  have hambient :
      iSupIndep (segreRightGrading R m n) :=
    (DirectSum.Decomposition.isInternal
      (segreRightGrading R m n)).submodule_iSupIndep
  apply
    ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
      (segreRightGrading R m n)).mp hambient
        s
        (fun j => ((v j : SegreCoordinateRing R m n) : SegreTensorRing R m n))
        (fun j hj => hv j hj)
        ?_ i hi)
  calc
    ∑ j ∈ s, ((v j : SegreCoordinateRing R m n) : SegreTensorRing R m n) =
        ((∑ j ∈ s, v j : SegreCoordinateRing R m n) :
          SegreTensorRing R m n) := by
      exact (map_sum
        (Subalgebra.val (SegreCoordinateRing R m n))
        (fun j => v j) s).symm
    _ = 0 := by rw [hsum]; rfl

lemma iSup_segreImageGrading
    (R : Type u) [CommRing R] (m n : ℕ) :
    iSup (segreImageGrading R m n) = ⊤ := by
  classical
  apply top_unique
  intro x _
  obtain ⟨p, rfl⟩ := segreRangeCoordinateHom_surjective R m n x
  rw [← DirectSum.sum_support_decompose
    (homogeneousSubmodule (Fin (segreDimension m n + 1)) R) p,
    map_sum]
  apply Submodule.sum_mem
  intro d _
  apply le_iSup (segreImageGrading R m n) d
  change
    segreStandardCoordinateHom R m n
        (DirectSum.decompose
          (homogeneousSubmodule (Fin (segreDimension m n + 1)) R) p d) ∈
      segreRightGrading R m n d
  exact segreStandardCoordinateHom_mem_grading R m n
    (DirectSum.decompose
      (homogeneousSubmodule (Fin (segreDimension m n + 1)) R) p d).2

/-- The canonical grading of the Segre image algebra. -/
instance segreImageGradingGradedRing
    (R : Type u) [CommRing R] (m n : ℕ) :
    GradedRing (segreImageGrading R m n) where
  toGradedMonoid := segreImageGradingGradedMonoid R m n
  toDecomposition :=
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (segreImageGrading_iSupIndep R m n)
      (iSup_segreImageGrading R m n)).chooseDecomposition

lemma segreRangeCoordinateHom_mem_imageGrading
    (R : Type u) [CommRing R] (m n : ℕ)
    {d : ℕ} {p : MvPolynomial (Fin (segreDimension m n + 1)) R}
    (hp : p ∈ homogeneousSubmodule (Fin (segreDimension m n + 1)) R d) :
    segreRangeCoordinateHom R m n p ∈ segreImageGrading R m n d :=
  segreStandardCoordinateHom_mem_grading R m n hp

end MvPolynomial
