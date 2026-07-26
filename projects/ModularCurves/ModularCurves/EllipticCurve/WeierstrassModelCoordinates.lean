/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.WeierstrassModel

/-!
# Homogeneous coordinates on a projective Weierstrass model

A triple satisfying the homogeneous Weierstrass equation induces an evaluation
map from the model's homogeneous coordinate ring. If one coordinate is a unit,
this map sends the irrelevant ideal onto the unit ideal, which is the algebraic
input required by `Proj.fromOfGlobalSections`.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace WeierstrassCurve.Projective

variable {R : Type u} [CommRing R]

/-- A generalized Weierstrass relation in a Cartier frame gives homogeneous
projective coordinates `[Xr:Y:r³]` on the corresponding cubic. -/
lemma equation_X_mul_r_Y_r_pow_three
    (W : WeierstrassCurve R) (X Y r : R)
    (h : Y ^ 2 + W.a₁ * X * Y * r + W.a₃ * Y * r ^ 3 =
      X ^ 3 + W.a₂ * X ^ 2 * r ^ 2 + W.a₄ * X * r ^ 4 + W.a₆ * r ^ 6) :
    W.toProjective.Equation ![X * r, Y, r ^ 3] := by
  rw [equation_iff]
  simp only [fin3_def_ext]
  linear_combination r ^ 3 * h

end WeierstrassCurve.Projective

namespace ModularCurves

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Evaluation of the projective Weierstrass coordinate ring at a triple
satisfying the homogeneous equation. -/
noncomputable def projModelEval
    (W : WeierstrassCurve R) (f : R →+* A) (P : Fin 3 → A)
    (hP : (W.map f).toProjective.Equation P) : projCoordRing W →+* A :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom f P) (by
    intro a ha
    rw [projIdeal_toIdeal, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul]
    have hF : MvPolynomial.eval₂ f P W.toProjective.polynomial = 0 := by
      rw [WeierstrassCurve.Projective.Equation,
        WeierstrassCurve.Projective.map_polynomial, MvPolynomial.eval_map] at hP
      exact hP
    change MvPolynomial.eval₂ f P W.toProjective.polynomial *
      MvPolynomial.eval₂ f P c = 0
    rw [hF, zero_mul])

@[simp]
lemma projModelEval_mk
    (W : WeierstrassCurve R) (f : R →+* A) (P : Fin 3 → A)
    (hP : (W.map f).toProjective.Equation P)
    (p : MvPolynomial (Fin 3) R) :
    projModelEval W f P hP
        (Ideal.Quotient.mk (projIdeal W).toIdeal p) =
      MvPolynomial.eval₂ f P p :=
  Ideal.Quotient.lift_mk _ _ _

@[simp]
lemma projModelEval_X
    (W : WeierstrassCurve R) (f : R →+* A) (P : Fin 3 → A)
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3) :
    projModelEval W f P hP
        (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i)) = P i := by
  rw [projModelEval_mk]
  simp only [MvPolynomial.eval₂_X]

/-- A unit homogeneous coordinate makes the image of the irrelevant ideal the
unit ideal. -/
lemma projModelEval_irrelevant_map_top_of_isUnit
    (W : WeierstrassCurve R) (f : R →+* A) (P : Fin 3 → A)
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3)
    (hi : IsUnit (P i)) :
    (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal.map
        (projModelEval W f P hP) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ ?_ hi
  rw [← projModelEval_X W f P hP i]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
      (mk_X_mem_quotientGrading_one W i))

/-- Two coprime homogeneous coordinates make the image of the irrelevant
ideal the unit ideal. -/
lemma projModelEval_irrelevant_map_top_of_isCoprime
    (W : WeierstrassCurve R) (f : R →+* A) (P : Fin 3 → A)
    (hP : (W.map f).toProjective.Equation P) (i j : Fin 3)
    (hij : IsCoprime (P i) (P j)) :
    (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal.map
        (projModelEval W f P hP) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  obtain ⟨a, b, hab⟩ := hij
  rw [← hab]
  apply Ideal.add_mem
  · apply Ideal.mul_mem_left
    rw [← projModelEval_X W f P hP i]
    exact Ideal.mem_map_of_mem _
      (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
        (mk_X_mem_quotientGrading_one W i))
  · apply Ideal.mul_mem_left
    rw [← projModelEval_X W f P hP j]
    exact Ideal.mem_map_of_mem _
      (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
        (mk_X_mem_quotientGrading_one W j))

@[simp]
lemma projModelEval_algebraMapGradeZero
    (W : WeierstrassCurve R) (f : R →+* A) (P : Fin 3 → A)
    (hP : (W.map f).toProjective.Equation P) (r : R) :
    projModelEval W f P hP
        (algebraMap (↥(quotientGrading (projIdeal W) 0))
          (projCoordRing W) (algebraMapGradeZero (projIdeal W) r)) = f r := by
  have hmk : algebraMap R (projCoordRing W) r =
      Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.C r) := by
    rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing W),
      RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
  rw [show (algebraMap (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W))
      (algebraMapGradeZero (projIdeal W) r) = algebraMap R (projCoordRing W) r from rfl,
    hmk, projModelEval_mk]
  simp only [MvPolynomial.eval₂_C]

/-- The morphism to the projective Weierstrass model defined by a homogeneous
coordinate triple with one unit coordinate. -/
noncomputable def projModelFromOfGlobalSections
    {X : Scheme.{u}} (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3)
    (hi : IsUnit (P i)) : X ⟶ projModel W :=
  Proj.fromOfGlobalSections _ (projModelEval W f P hP)
    (projModelEval_irrelevant_map_top_of_isUnit W f P hP i hi)

/-- The morphism defined by homogeneous coordinates lies over the base map
induced by its coefficient homomorphism. -/
@[reassoc]
theorem projModelFromOfGlobalSections_projModelπ
    {X : Scheme.{u}} (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3)
    (hi : IsUnit (P i)) :
    projModelFromOfGlobalSections W f P hP i hi ≫ projModelπ W =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) := by
  have key :
      ((projModelEval W f P hP).comp
        (algebraMap (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W))).comp
          (algebraMapGradeZero (projIdeal W)) = f := by
    ext r
    exact projModelEval_algebraMapGradeZero W f P hP r
  rw [projModelFromOfGlobalSections, projModelπ]
  simp only [Proj.fromOfGlobalSections_toSpecZero_assoc]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, key]

/-- The inverse image of a standard projective chart under the coordinate
morphism is the basic open of the corresponding coordinate. -/
lemma projModelFromOfGlobalSections_preimage_basicOpen
    {X : Scheme.{u}} (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3)
    (hi : IsUnit (P i)) (j : Fin 3) :
    projModelFromOfGlobalSections W f P hP i hi ⁻¹ᵁ
        Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)) =
      X.basicOpen (P j) := by
  rw [projModelFromOfGlobalSections,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos
      (mk_X_mem_quotientGrading_one W j)]
  exact congr_arg X.basicOpen (projModelEval_X W f P hP j)

/-- The morphism to the projective Weierstrass model defined by a homogeneous
coordinate triple with two coprime values. -/
noncomputable def projModelFromOfGlobalSectionsOfIsCoprime
    {X : Scheme.{u}} (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i j : Fin 3)
    (hij : IsCoprime (P i) (P j)) : X ⟶ projModel W :=
  Proj.fromOfGlobalSections _ (projModelEval W f P hP)
    (projModelEval_irrelevant_map_top_of_isCoprime W f P hP i j hij)

/-- The morphism defined by coprime homogeneous coordinates lies over the base
map induced by its coefficient homomorphism. -/
@[reassoc]
theorem projModelFromOfGlobalSectionsOfIsCoprime_projModelπ
    {X : Scheme.{u}} (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i j : Fin 3)
    (hij : IsCoprime (P i) (P j)) :
    projModelFromOfGlobalSectionsOfIsCoprime W f P hP i j hij ≫ projModelπ W =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) := by
  have key :
      ((projModelEval W f P hP).comp
        (algebraMap (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W))).comp
          (algebraMapGradeZero (projIdeal W)) = f := by
    ext r
    exact projModelEval_algebraMapGradeZero W f P hP r
  rw [projModelFromOfGlobalSectionsOfIsCoprime, projModelπ]
  simp only [Proj.fromOfGlobalSections_toSpecZero_assoc]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, key]

/-- The inverse image of a standard projective chart under the coprime
coordinate morphism is the basic open of the corresponding coordinate. -/
lemma projModelFromOfGlobalSectionsOfIsCoprime_preimage_basicOpen
    {X : Scheme.{u}} (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i j : Fin 3)
    (hij : IsCoprime (P i) (P j)) (k : Fin 3) :
    projModelFromOfGlobalSectionsOfIsCoprime W f P hP i j hij ⁻¹ᵁ
        Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X k)) =
      X.basicOpen (P k) := by
  rw [projModelFromOfGlobalSectionsOfIsCoprime,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos
      (mk_X_mem_quotientGrading_one W k)]
  exact congr_arg X.basicOpen (projModelEval_X W f P hP k)

/-- The inverse images of the two projective charts selected by the coprime
coordinates cover the source scheme. -/
lemma projModelFromOfGlobalSectionsOfIsCoprime_basicOpen_sup_eq_top
    {X : Scheme.{u}} (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i j : Fin 3)
    (hij : IsCoprime (P i) (P j)) :
    (projModelFromOfGlobalSectionsOfIsCoprime W f P hP i j hij ⁻¹ᵁ
        Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))) ⊔
      (projModelFromOfGlobalSectionsOfIsCoprime W f P hP i j hij ⁻¹ᵁ
        Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j))) = ⊤ := by
  rw [projModelFromOfGlobalSectionsOfIsCoprime_preimage_basicOpen,
    projModelFromOfGlobalSectionsOfIsCoprime_preimage_basicOpen]
  have hs : Ideal.span ({P i, P j} : Set Γ(X, (⊤ : X.Opens))) = ⊤ := by
    rw [Ideal.span_insert]
    exact (Ideal.sup_eq_top_iff_isCoprime (P i) (P j)).mpr hij
  have hcover := iSup_basicOpen_of_span_eq_top
    (X := X) (⊤ : X.Opens) ({P i, P j} : Set _) hs
  calc
    X.basicOpen (P i) ⊔ X.basicOpen (P j) =
        (⨆ r ∈ ({P i, P j} : Set Γ(X, (⊤ : X.Opens))), X.basicOpen r) := by
      apply le_antisymm
      · exact sup_le
          (le_iSup_of_le (P i) (le_iSup_of_le (by simp) le_rfl))
          (le_iSup_of_le (P j) (le_iSup_of_le (by simp) le_rfl))
      · refine iSup_le fun r => iSup_le fun hr => ?_
        rcases hr with hr | hr
        · subst r
          exact le_sup_left
        · have : r = P j := hr
          subst r
          exact le_sup_right
    _ = ⊤ := hcover

/-- Restriction of global sections to the top open of a basic-open
subscheme. -/
noncomputable def basicOpenTopRestriction
    (X : Scheme.{u}) (r : Γ(X, (⊤ : X.Opens))) :
    Γ(X, (⊤ : X.Opens)) →+*
      Γ((X.basicOpen r).toScheme, (⊤ : (X.basicOpen r).toScheme.Opens)) :=
  (X.basicOpen r).topIso.inv.hom.comp
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom

/-- The section defining a basic open becomes a unit after restriction to that
basic open. -/
lemma basicOpenTopRestriction_isUnit
    (X : Scheme.{u}) (r : Γ(X, (⊤ : X.Opens))) :
    IsUnit (basicOpenTopRestriction X r r) := by
  exact (AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen X.toRingedSpace r).map
    (X.basicOpen r).topIso.inv.hom

/-- Restrict homogeneous coordinates to the basic open of one coordinate and
use that unit coordinate to define a morphism to the projective model. -/
noncomputable def projModelFromBasicOpen
    (X : Scheme.{u}) (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3) :
    (X.basicOpen (P i)).toScheme ⟶ projModel W := by
  let ρ := basicOpenTopRestriction X (P i)
  have hP' : (W.map (ρ.comp f)).toProjective.Equation (ρ ∘ P) := by
    simpa only [WeierstrassCurve.map_map] using hP.map ρ
  exact projModelFromOfGlobalSections W (ρ.comp f) (ρ ∘ P) hP' i
    (basicOpenTopRestriction_isUnit X (P i))

/-- The basic-open coordinate morphism lies over the restricted coefficient
homomorphism. -/
@[reassoc]
theorem projModelFromBasicOpen_projModelπ
    (X : Scheme.{u}) (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3) :
    projModelFromBasicOpen X W f P hP i ≫ projModelπ W =
      (X.basicOpen (P i)).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom ((basicOpenTopRestriction X (P i)).comp f)) := by
  let ρ := basicOpenTopRestriction X (P i)
  have hP' : (W.map (ρ.comp f)).toProjective.Equation (ρ ∘ P) := by
    simpa only [WeierstrassCurve.map_map] using hP.map ρ
  have hbase := projModelFromOfGlobalSections_projModelπ W
    (ρ.comp f) (ρ ∘ P) hP' i
      (basicOpenTopRestriction_isUnit X (P i))
  rw [show projModelFromBasicOpen X W f P hP i =
    projModelFromOfGlobalSections W (ρ.comp f) (ρ ∘ P) hP' i
      (basicOpenTopRestriction_isUnit X (P i)) by
        rfl]
  exact hbase

/-- The image of the basic-open coordinate morphism lies in the corresponding
standard projective chart. -/
lemma projModelFromBasicOpen_preimage_basicOpen
    (X : Scheme.{u}) (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens))) (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P) (i : Fin 3) :
    projModelFromBasicOpen X W f P hP i ⁻¹ᵁ
        Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)) = ⊤ := by
  let ρ := basicOpenTopRestriction X (P i)
  have hP' : (W.map (ρ.comp f)).toProjective.Equation (ρ ∘ P) := by
    simpa only [WeierstrassCurve.map_map] using hP.map ρ
  have hpre := projModelFromOfGlobalSections_preimage_basicOpen
    W (ρ.comp f) (ρ ∘ P) hP' i
      (basicOpenTopRestriction_isUnit X (P i)) i
  rw [show projModelFromBasicOpen X W f P hP i =
    projModelFromOfGlobalSections W (ρ.comp f) (ρ ∘ P) hP' i
      (basicOpenTopRestriction_isUnit X (P i)) by
        rfl,
    hpre]
  exact Scheme.basicOpen_of_isUnit _
    (basicOpenTopRestriction_isUnit X (P i))

end ModularCurves
