/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AffinePointSection
import ModularCurves.EllipticCurve.MulByHomDegree

/-!
# Affine-point sections at field points ([T-E15-NORM] Stage B — the fibre evaluation)

The single funnel of the `hL`/`hArb` closes: evaluating the marked affine-point section
`[p : q : 1]` of the projective model at a field point `Spec K ⟶ Spec R` produces, under
the field-points dictionary `projModelPointsEquiv`, mathlib's affine point
`some (p̄, q̄)` of the base-changed curve. Together with the general-base additive
dictionary (`modelEllipticCurve_point_add_val` + `mulModelHom_specPoints`, both already
general-base) this reduces section-level group statements about the marked sections —
the `3`-torsion killing `[3]P = [3]Q = 0`, the fibrewise `E[3]`-generation, and the
`hArb` bridges — to the Stage-A field computations (`three_zsmul_some_origin`,
`three_zsmul_some_e3Q`), via the collision principle `hom_ext_of_forall_specPoint`
(Stage C supplies the reducedness of the universal base).

The chain: the affine section factors through the `Z`-chart as `Spec` of the evaluation
hom (`projModelAffineChart_eq_spec`), so its composite with a field point is
`Spec.map ((algebraMap R K).comp (affineChartHom W p q h)) ≫ awayι` — an explicit
`InZChart` witness; `chartHomEquiv_eq_of_specMap` reads the chart hom back off, and
`affineChartHom_mk` + `projModelAffineEval_mk` compute the two `Z`-chart coordinates to
`(p̄, q̄)`; `projModelPointsEquiv_some` closes.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdeal
open HomogeneousLocalization

universe u

namespace ModularCurves

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
  (K : Type u) [CommRing K] [Algebra R K]

/-- The evaluated affine-point section as a `K`-point of the projective model. -/
noncomputable def affineSectionSpecPoint (p q : R) (h : W.toAffine.Equation p q) :
    SpecPoints (projModel W) (projModelπ W) K :=
  ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelAffineSection W p q h, by
    rw [Category.assoc, projModelAffineSection_projModelπ, Category.comp_id]⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- **(Stage B-1)** The evaluated section is `Spec` of the composite evaluation hom,
followed by the `Z`-chart immersion — the explicit `InZChart` factorization. -/
theorem affineSectionSpecPoint_eq_spec (p q : R) (h : W.toAffine.Equation p q) :
    (affineSectionSpecPoint W K p q h).1 =
      Spec.map (CommRingCat.ofHom
          (((algebraMap R K).comp (affineChartHom W p q h)))) ≫
        Proj.awayι (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos := by
  show Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelAffineSection W p q h = _
  rw [← projModelAffineChart_fac W p q h, ← Category.assoc,
    projModelAffineChart_eq_spec, ← Spec.map_comp]
  rfl

/-- The evaluated section lies in the `Z`-chart. -/
theorem inZChart_affineSectionSpecPoint (p q : R) (h : W.toAffine.Equation p q) :
    InZChart W (affineSectionSpecPoint W K p q h) :=
  ⟨_, (affineSectionSpecPoint_eq_spec W K p q h).symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- **(Stage B-2, the value)** `affineChartHom` retracts the grade-zero `R`-structure. -/
theorem affineChartHom_gradeZero (p q : R) (h : W.toAffine.Equation p q) (r : R) :
    (affineChartHom W p q h)
        ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
          ((gradeZeroRingEquiv W : R →+* ↥(quotientGrading (projIdeal W) 0)) r)) = r := by
  have hmem : (quotientGradingHom (projIdeal W)) (MvPolynomial.C r) ∈
      quotientGrading (projIdeal W) (0 • 1) := by
    rw [zero_smul]
    exact mk_mem_quotientGrading _
      ((MvPolynomial.mem_homogeneousSubmodule 0 _).mpr
        (MvPolynomial.isHomogeneous_C _ r))
  have hform : (algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
        ((gradeZeroRingEquiv W : R →+* ↥(quotientGrading (projIdeal W) 0)) r) =
      HomogeneousLocalization.Away.mk _ (mk_X_mem_quotientGrading_one W 2) 0
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.C r)) hmem := by
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk, HomogeneousLocalization.algebraMap_eq,
      HomogeneousLocalization.fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, HomogeneousLocalization.val_mk]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    have hbridge : (((gradeZeroRingEquiv W : R →+* ↥(quotientGrading (projIdeal W) 0)) r :
          ↥(quotientGrading (projIdeal W) 0)) : projCoordRing W) =
        (quotientGradingHom (projIdeal W)) (MvPolynomial.C r) := by
      rw [show ((gradeZeroRingEquiv W : R →+* ↥(quotientGrading (projIdeal W) 0)) r)
          = algebraMapGradeZero (projIdeal W) r from rfl,
        coe_algebraMapGradeZero, quotientGradingHom_apply,
        IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing W),
        RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
    simp
    exact hbridge
  rw [hform, affineChartHom_mk]
  rw [show (quotientGradingHom (projIdeal W)) (MvPolynomial.C r)
      = Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.C r) from rfl,
    projModelAffineEval_mk]
  simp

/-- **(Stage B-2)** The composite evaluation hom is `R`-structure compatible. -/
theorem affineChartHom_comp_compat (p q : R) (h : W.toAffine.Equation p q) :
    (((algebraMap R K).comp (affineChartHom W p q h))).comp
        ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
          ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
      algebraMap R K := by
  ext r
  simp only [RingHom.comp_apply]
  rw [affineChartHom_gradeZero W p q h r]

/-- **(Stage B-3)** The chart hom of the evaluated section reads back as the composite
evaluation hom. -/
theorem chartHomEquiv_affineSectionSpecPoint (p q : R) (h : W.toAffine.Equation p q) :
    chartHomEquiv W 2 K ⟨affineSectionSpecPoint W K p q h,
        inZChart_affineSectionSpecPoint W K p q h⟩ =
      ⟨((algebraMap R K).comp (affineChartHom W p q h)),
        affineChartHom_comp_compat W K p q h⟩ :=
  chartHomEquiv_eq_of_specMap W 2 _ _ (affineSectionSpecPoint_eq_spec W K p q h).symm

end ModularCurves
