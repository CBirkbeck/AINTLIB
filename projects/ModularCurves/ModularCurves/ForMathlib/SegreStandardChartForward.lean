/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's
`CoherentCohomologyFinite.SegreStandardChartForward`.
-/
import ModularCurves.ForMathlib.ProjectiveCoordinateChartAlgebra
import ModularCurves.ForMathlib.SegreImageAffineCover

/-!
# The forward map on a standard Segre chart

On the chart where `XᵢYⱼ` is nonzero, the Segre coordinate `XₐY_b`
dehomogenizes to `(Xₐ / Xᵢ) ⊗ (Y_b / Yⱼ)`.
-/

open HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The canonical submodule instance, specialized so Lean can infer it through the range algebra. -/
instance segreCoordinateRingSubmoduleAddSubgroupClass
    (R : Type u) [CommRing R] (m n : ℕ) :
    AddSubgroupClass (Submodule R (SegreCoordinateRing R m n))
      (SegreCoordinateRing R m n) :=
  @Submodule.addSubgroupClass R (SegreCoordinateRing R m n) _ _ inferInstance

/-- The Segre target coordinate indexed by the pair `(i, j)`. -/
def segrePairIndex
    (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Fin (segreDimension m n + 1) :=
  (segreIndexEquiv m n).symm (i, j)

@[simp]
lemma segreIndexEquiv_segrePairIndex
    (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreIndexEquiv m n (segrePairIndex m n i j) = (i, j) :=
  (segreIndexEquiv m n).apply_symm_apply (i, j)

/-- The degree-zero coordinate ring of the standard Segre-image chart. -/
abbrev SegreImageChartRing
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :=
  Away
    (segreImageGrading R m n)
    (segreImageCoordinate R m n (segrePairIndex m n i j))

/-- The coefficient-ring map into a Segre-image chart ring. -/
noncomputable def segreImageAwayCoeffHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (f : SegreCoordinateRing R m n) :
    R →+* Away (segreImageGrading R m n) f :=
  (HomogeneousLocalization.fromZeroRingHom
      (segreImageGrading R m n) (Submonoid.powers f)).comp
    (algebraMap R (segreImageGrading R m n 0))

noncomputable instance segreImageAwayAlgebra
    (R : Type u) [CommRing R] (m n : ℕ)
    (f : SegreCoordinateRing R m n) :
    Algebra R (Away (segreImageGrading R m n) f) :=
  (segreImageAwayCoeffHom R m n f).toAlgebra

lemma segreImageAway_algebraMap_eq_mk
    (R : Type u) [CommRing R] (m n : ℕ)
    {d : ℕ} (f : SegreCoordinateRing R m n)
    (hf : f ∈ segreImageGrading R m n d) (r : R) :
    algebraMap R (Away (segreImageGrading R m n) f) r =
      Away.mk
        (segreImageGrading R m n)
        hf
        0
        (algebraMap R (SegreCoordinateRing R m n) r)
        (by simpa using
          SetLike.algebraMap_mem_graded (segreImageGrading R m n) r) := by
  apply HomogeneousLocalization.val_injective
  rfl

/-- The tensor product of the two standard projective chart rings. -/
abbrev SegreProductChartRing
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :=
  ProjectiveCoordinateAway R i ⊗[R] ProjectiveCoordinateAway R j

/-- Evaluate a Segre-image numerator on the product of the two standard affine charts. -/
def segreChartNumeratorHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreCoordinateRing R m n →ₐ[R] SegreProductChartRing R m n i j :=
  (Algebra.TensorProduct.map
      (projectiveCoordinateDehomogenization R i)
      (projectiveCoordinateDehomogenization R j)).comp
    (Subalgebra.val (SegreCoordinateRing R m n))

@[simp]
lemma segreChartNumeratorHom_coordinate
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (s : Fin (segreDimension m n + 1)) :
    segreChartNumeratorHom R m n i j (segreImageCoordinate R m n s) =
      projectiveCoordinateRatio R i (segreIndexEquiv m n s).1 ⊗ₜ[R]
        projectiveCoordinateRatio R j (segreIndexEquiv m n s).2 := by
  simp [segreChartNumeratorHom, segreImageCoordinate]

@[simp]
lemma segreChartNumeratorHom_anchor
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreChartNumeratorHom R m n i j
        (segreImageCoordinate R m n (segrePairIndex m n i j)) = 1 := by
  simp [Algebra.TensorProduct.one_def]

/-- Forget that the Segre chart localization is homogeneous. -/
def segreImageChartValRingHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreImageChartRing R m n i j →+*
      Localization.Away
        (segreImageCoordinate R m n (segrePairIndex m n i j)) where
  toFun := HomogeneousLocalization.val
  map_zero' := HomogeneousLocalization.val_zero
  map_one' := HomogeneousLocalization.val_one
  map_add' := HomogeneousLocalization.val_add
  map_mul' := HomogeneousLocalization.val_mul

@[simp]
lemma segreImageChartValRingHom_apply
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (x : SegreImageChartRing R m n i j) :
    segreImageChartValRingHom R m n i j x =
      HomogeneousLocalization.val x :=
  rfl

/-- The forward ring map on a standard Segre-image chart. -/
def segreChartForwardRingHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreImageChartRing R m n i j →+*
      SegreProductChartRing R m n i j :=
  (Localization.awayLift
      (segreChartNumeratorHom R m n i j).toRingHom
      (segreImageCoordinate R m n (segrePairIndex m n i j))
      (by
        change IsUnit
          (segreChartNumeratorHom R m n i j
            (segreImageCoordinate R m n (segrePairIndex m n i j)))
        rw [segreChartNumeratorHom_anchor]
        exact isUnit_one)).comp
    (segreImageChartValRingHom R m n i j)

/-- The forward chart map sends `p/(XᵢYⱼ)ⁿ` to the dehomogenized numerator. -/
lemma segreChartForwardRingHom_mk
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (q : ℕ) (p : SegreCoordinateRing R m n)
    (hp : p ∈ segreImageGrading R m n (q • 1)) :
    segreChartForwardRingHom R m n i j
        (Away.mk
          (segreImageGrading R m n)
          (segreImageCoordinate_mem_degreeOne R m n (segrePairIndex m n i j))
          q p hp) =
      segreChartNumeratorHom R m n i j p := by
  rw [segreChartForwardRingHom, RingHom.comp_apply,
    segreImageChartValRingHom_apply, HomogeneousLocalization.Away.val_mk]
  rw [Localization.awayLift_mk
    (segreChartNumeratorHom R m n i j).toRingHom
    (segreImageCoordinate R m n (segrePairIndex m n i j))
    p (1 : SegreProductChartRing R m n i j)
    (by simp [Algebra.TensorProduct.one_def]) q]
  simp

/-- The forward chart map as a coefficient-algebra map. -/
def segreChartForwardAlgHom
    (R : Type u) [CommRing R] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreImageChartRing R m n i j →ₐ[R]
      SegreProductChartRing R m n i j where
  __ := segreChartForwardRingHom R m n i j
  commutes' r := by
    rw [segreImageAway_algebraMap_eq_mk R m n
      (segreImageCoordinate R m n (segrePairIndex m n i j))
      (segreImageCoordinate_mem_degreeOne R m n (segrePairIndex m n i j)) r]
    change
      segreChartForwardRingHom R m n i j
          (Away.mk
            (segreImageGrading R m n)
            (segreImageCoordinate_mem_degreeOne R m n (segrePairIndex m n i j))
            0 (algebraMap R (SegreCoordinateRing R m n) r) _) =
        algebraMap R (SegreProductChartRing R m n i j) r
    rw [segreChartForwardRingHom_mk]
    exact (segreChartNumeratorHom R m n i j).commutes r

/-- The regular function `(XₐY_b)/(XᵢYⱼ)` on a standard Segre-image chart. -/
@[reducible]
def segreImageChartRatio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreImageChartRing R m n i j :=
  Away.mk
    (segreImageGrading R m n)
    (segreImageCoordinate_mem_degreeOne R m n (segrePairIndex m n i j))
    1
    (segreImageCoordinate R m n (segrePairIndex m n a b))
    (by simpa using
      segreImageCoordinate_mem_degreeOne R m n (segrePairIndex m n a b))

@[simp]
lemma segreChartForwardAlgHom_ratio
    (R : Type u) [CommRing R] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreChartForwardAlgHom R m n i j
        (segreImageChartRatio R m n i a j b) =
      projectiveCoordinateRatio R i a ⊗ₜ[R]
        projectiveCoordinateRatio R j b := by
  change
    segreChartForwardRingHom R m n i j
        (Away.mk
          (segreImageGrading R m n)
          (segreImageCoordinate_mem_degreeOne R m n (segrePairIndex m n i j))
          1
          (segreImageCoordinate R m n (segrePairIndex m n a b))
          _) = _
  rw [segreChartForwardRingHom_mk, segreChartNumeratorHom_coordinate]
  simp

end MvPolynomial
