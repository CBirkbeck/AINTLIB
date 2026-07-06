/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-A2d (step 4).
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The affine charts of projective space, ring-theoretically

The degree-zero part of the homogeneous localization of `R[X_j : j ∈ σ]` away from a
variable `X i` is a polynomial ring on the remaining variables:
`(R[X]_{X i})₀ ≃+* R[u_j : j ≠ i]`, by dehomogenisation `X_j/X_i ↦ u_j`.

This is the chart description underlying `ℙⁿ_R = Proj R[X₀,…,Xₙ]` and, through
quotient gradings, the affine charts of projective hypersurfaces.
-/

namespace HomogeneousLocalization

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι] [CommRing R] [CommRing A]
  [Algebra R A] {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜] (x : Submonoid A)

/-- `HomogeneousLocalization.val` as a ring homomorphism. -/
def valRingHom : HomogeneousLocalization 𝒜 x →+* Localization x where
  toFun := val
  map_one' := val_one
  map_mul' := val_mul
  map_zero' := val_zero
  map_add' := val_add

@[simp]
lemma valRingHom_apply (y : HomogeneousLocalization 𝒜 x) : valRingHom x y = y.val :=
  rfl

end HomogeneousLocalization

namespace MvPolynomial

open HomogeneousLocalization

variable (R : Type*) {σ : Type*} [CommRing R] [DecidableEq σ]

attribute [local instance] MvPolynomial.gradedAlgebra

lemma X_mem_homogeneousSubmodule_one (i : σ) :
    (X i : MvPolynomial σ R) ∈ homogeneousSubmodule σ R 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ _)

/-- The dehomogenising evaluation `R[X] → R[u_j : j ≠ i]`, `X_i ↦ 1`, `X_j ↦ u_j`. -/
noncomputable def dehomogenizeAux (i : σ) :
    MvPolynomial σ R →+* MvPolynomial {j : σ // j ≠ i} R :=
  eval₂Hom C fun j => if h : j = i then 1 else X ⟨j, h⟩

@[simp]
lemma dehomogenizeAux_C (i : σ) (r : R) : dehomogenizeAux R i (C r) = C r :=
  eval₂Hom_C _ _ _

@[simp]
lemma dehomogenizeAux_X_self (i : σ) : dehomogenizeAux R i (X i) = 1 := by
  simp [dehomogenizeAux]

@[simp]
lemma dehomogenizeAux_X_ne (i : σ) {j : σ} (h : j ≠ i) :
    dehomogenizeAux R i (X j) = X ⟨j, h⟩ := by
  simp [dehomogenizeAux, h]

/-- Dehomogenisation at the variable `X i`: the chart map
`(R[X]_{X i})₀ → R[u_j : j ≠ i]`. -/
noncomputable def dehomogenizeAt (i : σ) :
    Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) →+*
      MvPolynomial {j : σ // j ≠ i} R :=
  (Localization.awayLift (dehomogenizeAux R i) (X i)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)).comp (valRingHom _)

/-- The constants `R` inside the chart ring `(R[X]_{X i})₀`. -/
noncomputable def awayConst (i : σ) (r : R) :
    Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) :=
  Away.mk _ (X_mem_homogeneousSubmodule_one R i) 0 (C r)
    (by simpa using (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ _))

lemma val_awayConst' (i : σ) (r : R) :
    (awayConst R i r).val =
      Localization.mk (C r) (⟨(X i : MvPolynomial σ R) ^ 0, 0, rfl⟩ :
        Submonoid.powers (X i : MvPolynomial σ R)) := by
  rw [awayConst, Away.val_mk]

@[simp]
lemma val_awayConst (i : σ) (r : R) :
    (awayConst R i r).val = Localization.mk (C r) 1 := by
  rw [val_awayConst']
  exact congrArg _ (Subtype.ext (pow_zero _))

/-- The chart coordinate `X_j / X_i` in `(R[X]_{X i})₀`. -/
noncomputable def awayVar (i : σ) (j : {j : σ // j ≠ i}) :
    Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) :=
  Away.mk _ (X_mem_homogeneousSubmodule_one R i) 1 (X j.1)
    (by simpa using (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ _))

lemma val_awayVar' (i : σ) (j : {j : σ // j ≠ i}) :
    (awayVar R i j).val =
      Localization.mk (X j.1) (⟨(X i : MvPolynomial σ R) ^ 1, 1, rfl⟩ :
        Submonoid.powers (X i : MvPolynomial σ R)) := by
  rw [awayVar, Away.val_mk]

/-- The constants, as a ring homomorphism into the chart ring. -/
noncomputable def awayConstHom (i : σ) :
    R →+* Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) where
  toFun := awayConst R i
  map_one' := by
    apply val_injective
    rw [val_awayConst, val_one, map_one]
    exact Localization.mk_one
  map_mul' a b := by
    apply val_injective
    rw [val_mul, val_awayConst, val_awayConst, val_awayConst, Localization.mk_mul,
      map_mul, one_mul]
  map_zero' := by
    apply val_injective
    rw [val_awayConst, val_zero, map_zero]
    exact Localization.mk_zero _
  map_add' a b := by
    apply val_injective
    rw [val_add, val_awayConst, val_awayConst, val_awayConst,
      Localization.add_mk_self, map_add]

/-- Homogenisation into the chart at `X i`: `u_j ↦ X_j/X_i`. -/
noncomputable def homogenizeAt (i : σ) :
    MvPolynomial {j : σ // j ≠ i} R →+*
      Away (homogeneousSubmodule σ R) (X i : MvPolynomial σ R) :=
  eval₂Hom (awayConstHom R i) (awayVar R i)

private lemma dehomog_lift_mk_one (i : σ) (a : MvPolynomial σ R) :
    Localization.awayLift (dehomogenizeAux R i) (X i)
      (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩) (Localization.mk a 1) =
    dehomogenizeAux R i a := by
  rw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.Away.lift_eq _ _ _

/-- Dehomogenising after homogenising is the identity. -/
lemma dehomogenizeAt_comp_homogenizeAt (i : σ) :
    (dehomogenizeAt R i).comp (homogenizeAt R i) = RingHom.id _ := by
  apply ringHom_ext
  · intro r
    show dehomogenizeAt R i (homogenizeAt R i (C r)) = C r
    have hval : homogenizeAt R i (C r) = awayConst R i r := by
      rw [homogenizeAt, eval₂Hom_C]; rfl
    rw [hval]
    simp only [dehomogenizeAt, RingHom.comp_apply, valRingHom_apply, val_awayConst,
      dehomog_lift_mk_one, dehomogenizeAux_C]
  · intro j
    show dehomogenizeAt R i (homogenizeAt R i (X j)) = X j
    have hval : homogenizeAt R i (X j) = awayVar R i j := by
      rw [homogenizeAt, eval₂Hom_X']
    rw [hval]
    have hval2 : (awayVar R i j).val * Localization.mk (X i) 1 =
        Localization.mk (X j.1) 1 := by
      rw [val_awayVar', Localization.mk_mul, mul_one]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp [pow_one]; ring⟩
    have happ := congrArg (Localization.awayLift (dehomogenizeAux R i) (X i)
      (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)) hval2
    rw [map_mul, dehomog_lift_mk_one, dehomog_lift_mk_one] at happ
    simp only [dehomogenizeAux_X_self, mul_one, dehomogenizeAux_X_ne R i j.2] at happ
    show Localization.awayLift (dehomogenizeAux R i) (X i)
      (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩) (awayVar R i j).val = X j
    exact happ

end MvPolynomial
