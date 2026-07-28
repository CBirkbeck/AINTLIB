/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AffinePointSection
import ModularCurves.EllipticCurve.MulByHomDegree
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.EllipticCurve.RecordGroupUnique
import ModularCurves.EllipticCurve.MulByHomFibres
import ModularCurves.LevelStructure.ExactOrder
import ModularCurves.ForMathlib.BaseChangeAlongCompat

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

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

set_option backward.isDefEq.respectTransparency false in
/-- **(Stage B-4)** `affineChartHom` on the `Z`-chart coordinates reads the marked
coordinates: `X_j/X_2 ↦ ![p, q, 1] j`. -/
theorem affineChartHom_coord (p q : R) (h : W.toAffine.Equation p q)
    (j : {j : Fin 3 // j ≠ 2}) :
    affineChartHom W p q h (chartCoordEquiv W 2 (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
        (MvPolynomial.X j))) = ![p, q, 1] j.1 := by
  rw [chartCoordEquiv_mk_X, HomogeneousLocalization.Away.isLocalizationElem,
    affineChartHom_mk]
  rw [show ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j.1)) ^ 1 =
      Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X j.1 ^ 1) from by
    rw [pow_one, pow_one]; rfl]
  rw [projModelAffineEval_mk]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **(Stage B-5)** The `Z`-chart coordinates of the evaluated section are the evaluated
marked coordinates. -/
theorem affineSectionSpecPoint_coord {K : Type u} [Field K] [Algebra R K]
    (p q : R) (h : W.toAffine.Equation p q)
    (j : {j : Fin 3 // j ≠ 2}) :
    (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨affineSectionSpecPoint W K p q h,
        inZChart_affineSectionSpecPoint W K p q h⟩)).1 j =
      algebraMap R K (![p, q, 1] j.1) := by
  rw [coord_val, chartHomEquiv_affineSectionSpecPoint]
  show ((algebraMap R K).comp (affineChartHom W p q h)) _ = _
  rw [RingHom.comp_apply, affineChartHom_coord]

set_option backward.isDefEq.respectTransparency false in
/-- **(Stage B ★★, the fibre evaluation)** Under the field-points dictionary, the
evaluated affine-point section is mathlib's affine point at the evaluated coordinates. -/
theorem projModelPointsEquiv_affineSectionSpecPoint {K : Type u} [Field K] [Algebra R K]
    [W.IsElliptic] (p q : R) (h : W.toAffine.Equation p q)
    (hns : (W.baseChange K).toAffine.Nonsingular
      (algebraMap R K p) (algebraMap R K q)) :
    projModelPointsEquiv W K (affineSectionSpecPoint W K p q h) =
      WeierstrassCurve.Affine.Point.some (algebraMap R K p) (algebraMap R K q) hns :=
  projModelPointsEquiv_some W K (affineSectionSpecPoint W K p q h)
    (inZChart_affineSectionSpecPoint W K p q h)
    (algebraMap R K p) (algebraMap R K q) hns
    (by rw [affineSectionSpecPoint_coord W p q h ⟨0, by decide⟩]; rfl)
    (by rw [affineSectionSpecPoint_coord W p q h ⟨1, by decide⟩]; rfl)

/-! ## The general-base additive dictionary

`projModelPointsEquiv` is additive on `K`-points of the model over **any ring base** —
the field-base restriction of `projModelPointsEquiv_add`/`projModelPointsAddEquiv`
(`MulByHomDegree.lean`) was incidental: both of its inputs
(`modelEllipticCurve_point_add_val` and `mulModelHom_specPoints`) are general-base. -/

section AddDict

variable [W.IsElliptic] {K' : Type u} [Field K'] [DecidableEq K'] [Algebra R K']

/-- **(Stage B-7)** The dictionary is additive over a general ring base. -/
theorem projModelPointsEquiv_point_add
    (P Q : (modelEllipticCurve W).Point
      (Spec.map (CommRingCat.ofHom (algebraMap R K')))) :
    projModelPointsEquiv W K' ⟨(P + Q).1, (P + Q).2⟩
      = projModelPointsEquiv W K' ⟨P.1, P.2⟩ + projModelPointsEquiv W K' ⟨Q.1, Q.2⟩ := by
  rw [← mulModelHom_specPoints W K' ⟨P.1, P.2⟩ ⟨Q.1, Q.2⟩]
  exact congrArg (projModelPointsEquiv W K')
    (Subtype.ext (modelEllipticCurve_point_add_val W P Q))

/-- **(Stage B-7)** The point group of the model over a general ring base, at a field
point, is additively equivalent to mathlib's affine point group of the fibre. -/
noncomputable def modelPointAddEquiv :
    (modelEllipticCurve W).Point (Spec.map (CommRingCat.ofHom (algebraMap R K')))
      ≃+ (W.baseChange K').toAffine.Point :=
  { Equiv.subtypeEquivProp rfl |>.trans (projModelPointsEquiv W K') with
    map_add' := projModelPointsEquiv_point_add W }

end AddDict

/-! ## The killing collision principle -/

section Collision

variable [W.IsElliptic]

/-- **(Stage B-8 ★★, the collision principle)** Over a reduced base, a section of the
model killed by `N` at every field point is killed by `N`: the two morphisms
`σ ≫ [N]` and the zero section agree on all field points, the model is separated
(mathlib's `Proj` instance) and the base reduced, so `hom_ext_of_forall_specPoint`
closes. The fibre hypothesis is the Stage-A/B computation. -/
theorem nsmul_section_eq_zero_of_forall_specPoint
    [IsReduced (Spec (CommRingCat.of R))] (N : ℕ)
    (σ : (modelEllipticCurve W).Section)
    (hfib : ∀ (K : Type u) [Field K]
      (pt : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      pt ≫ (σ.1 ≫ (modelEllipticCurve W).mulByHom (N : ℤ)) =
        pt ≫ (modelEllipticCurve W).zero) :
    (N : ℤ) • σ = 0 := by
  rw [EllipticCurve.smul_eq_zero_iff_comp_mulByHom (modelEllipticCurve W) (𝟙 _) N σ]
  rw [Category.id_comp]
  haveI : ((modelEllipticCurve W).E).IsSeparated :=
    inferInstanceAs ((projModel W).IsSeparated)
  exact hom_ext_of_forall_specPoint (fun K _ pt => hfib K pt)

end Collision


/-! ## Stage-D: killing transport along coefficient base change

The general-ring pointed group-object iso between the base-changed model and the model
of the mapped curve (the field restriction of `modelBaseChangeIsoAsOver` was incidental —
its pullback and zero-leg inputs are general; the monoid-compat comes from the
records-level canonicity `isMonHom_of_pointedIso_records`, which needs no noetherian
hypothesis), and through it: a marked affine-point section killed by `N` stays killed
after arbitrary coefficient base change. -/

section StageDTransport

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
  (W : WeierstrassCurve A) [W.IsElliptic]

/-- `asSection` sends the zero point to the zero section (local copy of
`Moduli/DrinfeldRepresentability.asSection_zero`, to keep this file light). -/
theorem asSection_zero' {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (g : T ⟶ S) : EllipticCurve.Point.asSection E g 0 = 0 := by
  have h := EllipticCurve.Point.asSection_zsmul E g 0 0
  simpa using h

open EllipticCurve in
/-- **(Stage D-3)** The base-changed model, as an `Over`-object, is isomorphic to the
model of the mapped curve via the pullback comparison. -/
noncomputable def modelBaseChangeIso :
    (((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A A')))).asOver) ≅
      ((modelEllipticCurve (W.map (algebraMap A A'))).asOver) := by
  haveI : (W.map (algebraMap A A')).IsElliptic := inferInstance
  refine Over.isoMk ((isPullback_projModelBaseChange (R' := A') W).isoPullback.symm) ?_
  show (isPullback_projModelBaseChange (R' := A') W).isoPullback.inv ≫
    projModelπ (W.map (algebraMap A A')) = _
  rw [Iso.inv_comp_eq]
  exact (isPullback_projModelBaseChange (R' := A') W).isoPullback_hom_snd.symm

theorem modelBaseChangeIso_hom_left :
    (modelBaseChangeIso (A' := A') W).hom.left =
      (isPullback_projModelBaseChange (R' := A') W).isoPullback.inv := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(Stage D-3)** The comparison is pointed: the base-changed zero section maps to the
mapped model's zero section. -/
theorem modelBaseChangeIso_zero :
    ((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A A')))).zero ≫
      (modelBaseChangeIso (A' := A') W).hom.left =
    (modelEllipticCurve (W.map (algebraMap A A'))).zero := by
  haveI : (W.map (algebraMap A A')).IsElliptic := inferInstance
  set b := isPullback_projModelBaseChange (R' := A') W
  have hfst : ((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A A')))).zero ≫
        pullback.fst (modelEllipticCurve W).π
          (Spec.map (CommRingCat.ofHom (algebraMap A A')))
      = Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ (modelEllipticCurve W).zero :=
    pullback.lift_fst _ _ _
  have hsnd : ((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A A')))).zero ≫
        pullback.snd (modelEllipticCurve W).π
          (Spec.map (CommRingCat.ofHom (algebraMap A A')))
      = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hz2 : projModelZero (W.map (algebraMap A A')) ≫ b.isoPullback.hom
      = ((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A A')))).zero := by
    refine pullback.hom_ext ?_ ?_
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (CategoryStruct.comp _) b.isoPullback_hom_fst).trans ?_
      exact (projModelZero_baseChange (R' := A') W).trans hfst.symm
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (CategoryStruct.comp _) b.isoPullback_hom_snd).trans ?_
      exact (projModelZero_projModelπ (W.map (algebraMap A A'))).trans hsnd.symm
  rw [modelBaseChangeIso_hom_left]
  show _ ≫ b.isoPullback.inv = projModelZero (W.map (algebraMap A A'))
  rw [Iso.comp_inv_eq]
  exact hz2.symm

set_option backward.isDefEq.respectTransparency false in
/-- **(Stage D-3)** The comparison is a pointed monoid-object hom — via the records-level
canonicity (`isMonHom_of_pointedIso_records`), with no noetherian hypothesis. -/
theorem isMonHom_modelBaseChangeIso :
    IsMonHom (modelBaseChangeIso (A' := A') W).hom := by
  haveI : (W.map (algebraMap A A')).IsElliptic := inferInstance
  have hη : (η[(((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A A')))).asOver)]) ≫
        (modelBaseChangeIso (A' := A') W).hom =
      η[((modelEllipticCurve (W.map (algebraMap A A'))).asOver)] := by
    ext1
    rw [Over.comp_left,
      (((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A A'))))).one_eq_zero,
      ((modelEllipticCurve (W.map (algebraMap A A')))).one_eq_zero]
    exact (Category.assoc _ _ _).trans
      (congrArg _ (modelBaseChangeIso_zero (A' := A') W))
  exact { one_hom := hη
          mul_hom := isMonHom_of_pointedIso_records _ _
            (modelBaseChangeIso (A' := A') W) hη }

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **(Stage D ★★, the killing transport)** A marked affine-point section killed by `N`
stays killed after arbitrary coefficient base change: pull + `asSection` transport the
killing to the base-changed model, and the pointed monoid iso carries it to the mapped
model, matching the mapped marked section by the pullback comparison against
`projModelAffineSection_baseChange`. -/
theorem nsmul_section_map_eq_zero_of_nsmul_eq_zero (N : ℕ)
    (p q : A) (h : W.toAffine.Equation p q)
    (h' : (W.map (algebraMap A A')).toAffine.Equation
      (algebraMap A A' p) (algebraMap A A' q))
    (hkill : (N : ℤ) • (⟨projModelAffineSection W p q h,
        projModelAffineSection_projModelπ W p q h⟩ :
      EllipticCurve.Section (modelEllipticCurve W)) = 0) :
    (N : ℤ) • (⟨projModelAffineSection (W.map (algebraMap A A'))
        (algebraMap A A' p) (algebraMap A A' q) h',
        projModelAffineSection_projModelπ _ _ _ h'⟩ :
      EllipticCurve.Section (modelEllipticCurve (W.map (algebraMap A A')))) = 0 := by
  haveI : (W.map (algebraMap A A')).IsElliptic := inferInstance
  set P₀ : EllipticCurve.Section (modelEllipticCurve W) :=
    ⟨projModelAffineSection W p q h, projModelAffineSection_projModelπ W p q h⟩ with hP₀
  -- the base-changed section is killed
  have hpull : (N : ℤ) • EllipticCurve.Point.pull (modelEllipticCurve W) (Spec.map (CommRingCat.ofHom (algebraMap A A'))) P₀ = 0 := by
    rw [← EllipticCurve.Point.pull_zsmul, hkill, EllipticCurve.Point.pull_zero]
  have hbc : (N : ℤ) • EllipticCurve.Point.asSection (modelEllipticCurve W) (Spec.map (CommRingCat.ofHom (algebraMap A A')))
      (EllipticCurve.Point.pull (modelEllipticCurve W) (Spec.map (CommRingCat.ofHom (algebraMap A A'))) P₀) = 0 := by
    rw [← EllipticCurve.Point.asSection_zsmul, hpull, asSection_zero']
  -- morphism-level killing on the base-changed model
  have hσbc := (EllipticCurve.smul_eq_zero_iff_comp_mulByHom
    ((modelEllipticCurve W).baseChange (Spec.map (CommRingCat.ofHom (algebraMap A A')))) (𝟙 _) N _).mp hbc
  rw [Category.id_comp] at hσbc
  -- the matched section on the mapped model
  haveI := isMonHom_modelBaseChangeIso (A' := A') W
  have hmatch : (EllipticCurve.Point.asSection (modelEllipticCurve W) (Spec.map (CommRingCat.ofHom (algebraMap A A')))
        (EllipticCurve.Point.pull (modelEllipticCurve W) (Spec.map (CommRingCat.ofHom (algebraMap A A'))) P₀)).1 ≫
        (modelBaseChangeIso (A' := A') W).hom.left =
      projModelAffineSection (W.map (algebraMap A A'))
        (algebraMap A A' p) (algebraMap A A' q) h' := by
    rw [modelBaseChangeIso_hom_left, Iso.comp_inv_eq]
    refine pullback.hom_ext ?_ ?_
    · refine ((EllipticCurve.Point.asSection_val_fst _ _ _).trans
        (projModelAffineSection_baseChange W p q h h').symm).trans ?_
      exact congrArg (fun m => projModelAffineSection (W.map (algebraMap A A'))
          (algebraMap A A' p) (algebraMap A A' q) h' ≫ m)
        (isPullback_projModelBaseChange (R' := A') W).isoPullback_hom_fst.symm
    · refine ((EllipticCurve.Point.asSection_val_snd _ _ _).trans
        (projModelAffineSection_projModelπ _ _ _ h').symm).trans ?_
      exact congrArg (fun m => projModelAffineSection (W.map (algebraMap A A'))
          (algebraMap A A' p) (algebraMap A A' q) h' ≫ m)
        (isPullback_projModelBaseChange (R' := A') W).isoPullback_hom_snd.symm
  -- transport the killing across the iso
  rw [EllipticCurve.smul_eq_zero_iff_comp_mulByHom
    (modelEllipticCurve (W.map (algebraMap A A'))) (𝟙 _) N _, Category.id_comp]
  show projModelAffineSection (W.map (algebraMap A A')) _ _ h' ≫ _ = _
  rw [← hmatch, Category.assoc,
    ← EllipticCurve.mulByHom_comp_left_of_isMonHom _ _
      (modelBaseChangeIso (A' := A') W).hom (N : ℤ),
    ← Category.assoc, hσbc]
  exact modelBaseChangeIso_zero (A' := A') W

end StageDTransport

end ModularCurves
