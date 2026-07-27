/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.WeierstrassModel

/-!
# Sections of the projective model through affine points (T-E14b-2)

**(STREAM-OMEGA 2026-07-14; board: T-E14 continuation.)** For an affine point
`(p, q)` on a Weierstrass curve `W/R` (i.e. satisfying the affine Weierstrass
equation), the section `[p : q : 1] : Spec R ⟶ projModel W` of the structure
morphism — the scheme-level "the section through `(p, q)`". Mirrors `projModelZero`
(the section `[0:1:0]` at infinity) verbatim, with the evaluation
`X ↦ p, Y ↦ q, Z ↦ 1` in place of `X ↦ 0, Y ↦ 1, Z ↦ 0`.

This is the vocabulary in which KM 4.6.2's Legendre `δ`-condition is stated: *"the
adapted `x` satisfies `x(P₂) = 0, x(Q₂) = 1`"* becomes "`P` is carried by the adapted
chart to `projModelAffineSection … 0 0 …` and `Q` to `projModelAffineSection … 1 0 …`"
(on `2`-torsion, `y = 0` is forced in char ≠ 2, so pinning `x` pins the point).
-/

-- v4.33 bump: opens/hom coercions are no longer transparent enough for the
-- `≫`-associativity and `comp_apply` rewrites below.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdeal
open HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- Evaluation of the homogeneous coordinate ring at an affine point `[p : q : 1]`
of the curve. -/
def projModelAffineEval (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) : projCoordRing W →+* R :=
  Ideal.Quotient.lift _ (MvPolynomial.eval ![p, q, 1]) (by
    intro a ha
    rw [projIdeal_toIdeal, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    have hF : MvPolynomial.eval ![p, q, 1] W.toProjective.polynomial = 0 := by
      rw [WeierstrassCurve.Projective.eval_polynomial]
      have he := (WeierstrassCurve.Affine.equation_iff (W := W.toAffine) p q).mp h
      show q ^ 2 * 1 + W.a₁ * p * q * 1 + W.a₃ * q * 1 ^ 2 -
        (p ^ 3 + W.a₂ * p ^ 2 * 1 + W.a₄ * p * 1 ^ 2 + W.a₆ * 1 ^ 3) = 0
      linear_combination he
    rw [map_mul, hF, zero_mul])

@[simp]
lemma projModelAffineEval_mk (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) (f : MvPolynomial (Fin 3) R) :
    projModelAffineEval W p q h (Ideal.Quotient.mk (projIdeal W).toIdeal f) =
      MvPolynomial.eval ![p, q, 1] f :=
  Ideal.Quotient.lift_mk _ _ _

/-- The class of `Z` lies in the irrelevant ideal of the quotient grading. -/
lemma mk_Z_mem_irrelevant (W : WeierstrassCurve R) :
    Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 2) ∈
      (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal := by
  show GradedRing.proj (quotientGrading (projIdeal W)) 0
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 2)) = 0
  rw [GradedRing.proj_apply,
    decompose_quotientGrading_mk (projIdeal W)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _)),
    DirectSum.coe_of_apply]
  simp

/-- The affine-point evaluation maps the irrelevant ideal onto the unit ideal. -/
lemma projModelAffineEval_irrelevant_map_top (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    (HomogeneousIdeal.irrelevant (quotientGrading (projIdeal W))).toIdeal.map
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
      (projModelAffineEval W p q h))
      (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 2)) = 1 := by
    rw [RingHom.comp_apply, projModelAffineEval_mk]
    rw [show MvPolynomial.eval ![p, q, 1] (MvPolynomial.X 2) = 1 from by simp]
    exact map_one _
  rw [← h1]
  exact Ideal.mem_map_of_mem _ (mk_Z_mem_irrelevant W)

/-- **(T-E14b-2)** The section `[p : q : 1]` of the projective Weierstrass model
through an affine point of the curve, via `Proj.fromOfGlobalSections` at the
evaluation `X ↦ p, Y ↦ q, Z ↦ 1`. -/
def projModelAffineSection (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) : Spec (.of R) ⟶ projModel W :=
  Proj.fromOfGlobalSections _
    ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h))
    (projModelAffineEval_irrelevant_map_top W p q h)

/-- Evaluation at `[p:q:1]` retracts the degree-zero inclusion. -/
@[simp]
lemma projModelAffineEval_algebraMapGradeZero (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) (r : R) :
    projModelAffineEval W p q h (algebraMap (↥(quotientGrading (projIdeal W) 0))
      (projCoordRing W) (algebraMapGradeZero (projIdeal W) r)) = r := by
  have hmk : algebraMap R (projCoordRing W) r =
      Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.C r) := by
    rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing W),
      RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
  rw [show (algebraMap (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W))
      (algebraMapGradeZero (projIdeal W) r) = algebraMap R (projCoordRing W) r from rfl,
    hmk, projModelAffineEval_mk]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14b-2)** The affine-point section is a section of the structure morphism. -/
@[reassoc (attr := simp)]
theorem projModelAffineSection_projModelπ (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    projModelAffineSection W p q h ≫ projModelπ W = 𝟙 _ := by
  have key : (((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
        (projModelAffineEval W p q h)).comp
          (algebraMap (↥(quotientGrading (projIdeal W) 0)) (projCoordRing W))).comp
      (algebraMapGradeZero (projIdeal W)) =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    ext r
    show (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (projModelAffineEval W p q h
        (algebraMap _ (projCoordRing W) (algebraMapGradeZero (projIdeal W) r))) = _
    rw [projModelAffineEval_algebraMapGradeZero]
  rw [projModelAffineSection, projModelπ]
  simp only [Proj.fromOfGlobalSections_toSpecZero_assoc]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, key, CommRingCat.ofHom_hom]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of R)

/-! ### The `Z`-chart factorisation and base-change naturality

Mirrors the `Y`-chart block of `WeierstrassModel.lean` (`projModelZeroChart` …
`projModelZero_baseChange`) with `X 1 ↦ X 2` and the affine evaluation in place of
the point-at-infinity evaluation: the section `[p : q : 1]` lands entirely in the
`Z`-chart. -/

open HomogeneousLocalization in
/-- The evaluation kills no power of `Z`: its value on the `Z`-class is `1`. -/
lemma projModelAffineEval_Z (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    projModelAffineEval W p q h ((quotientGradingHom (projIdeal W))
      (MvPolynomial.X 2)) = 1 := by
  show projModelAffineEval W p q h
    (Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X 2)) = 1
  rw [projModelAffineEval_mk]
  simp

/-- The affine section lands entirely in the `Z`-chart. -/
lemma projModelAffineSection_preimage_zChart (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    projModelAffineSection W p q h ⁻¹ᵁ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) = ⊤ := by
  unfold projModelAffineSection
  rw [Proj.fromOfGlobalSections_preimage_basicOpen (hn := one_pos)
    (hr := mk_X_mem_quotientGrading_one W 2)]
  rw [show ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
      (projModelAffineEval W p q h)) ((quotientGradingHom (projIdeal W))
        (MvPolynomial.X 2)) = 1 from by
    rw [RingHom.comp_apply, projModelAffineEval_Z, map_one]]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The chart factorisation of the affine section through the `Z`-chart. -/
noncomputable def projModelAffineChart (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    Spec (.of R) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) := by
  have hrange : Set.range ⇑(projModelAffineSection W p q h) ⊆
      Set.range ⇑(Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos) := by
    rw [show Set.range ⇑(Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos) =
        (Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) :
          Set (Proj (quotientGrading (projIdeal W)))) from by
      rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ (projModelAffineSection W p q h ⁻¹ᵁ (Proj.basicOpen
        (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) := by
      rw [projModelAffineSection_preimage_zChart]
      trivial
    exact hx
  exact IsOpenImmersion.lift _ _ hrange

@[reassoc]
lemma projModelAffineChart_fac (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    projModelAffineChart W p q h ≫ Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos =
      projModelAffineSection W p q h :=
  IsOpenImmersion.lift_fac _ _ _

open HomogeneousLocalization in
/-- Evaluation of the `Z`-chart at the affine point `[p : q : 1]`. -/
noncomputable def affineChartHom (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+* R :=
  (Localization.awayLift (projModelAffineEval W p q h)
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
    (isUnit_iff_exists_inv.mpr ⟨1, by
      rw [projModelAffineEval_Z, one_mul]⟩)).comp
    (HomogeneousLocalization.valRingHom _)

open HomogeneousLocalization in
lemma affineChartHom_mk (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) {i : ℕ}
    (hs : (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2) ∈
      quotientGrading (projIdeal W) i) (n : ℕ) (a : projCoordRing W)
    (ha : a ∈ quotientGrading (projIdeal W) (n • i)) :
    affineChartHom W p q h (HomogeneousLocalization.Away.mk _ hs n a ha) =
      projModelAffineEval W p q h a := by
  rw [affineChartHom, RingHom.comp_apply,
    HomogeneousLocalization.valRingHom_apply, Away.val_mk]
  rw [Localization.awayLift_mk (hv := by rw [projModelAffineEval_Z, one_mul])]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The piece-level comparison for the glue step. -/
private lemma glue_pieceZ (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    (Proj.openCoverOfMapIrrelevantEqTop (quotientGrading (projIdeal W))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h))
      (projModelAffineEval_irrelevant_map_top W p q h)).f
      ⟨1, (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2),
        one_pos, mk_X_mem_quotientGrading_one W 2⟩ ≫
      Spec.map (CommRingCat.ofHom (affineChartHom W p q h)) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos =
    Proj.toBasicOpenOfGlobalSections (quotientGrading (projIdeal W))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h)) rfl
      one_pos (mk_X_mem_quotientGrading_one W 2) ≫
      (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).ι := by
  rw [show Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos =
      (Proj.basicOpenIsoSpec (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).inv ≫
      (Proj.basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).ι from
    (Proj.basicOpenIsoSpec_inv_ι _ _ _ _).symm]
  rw [Proj.toBasicOpenOfGlobalSections]
  rw [← Category.assoc, ← Category.assoc]
  refine congrArg (· ≫ (Proj.basicOpen (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).ι) ?_
  rw [Iso.cancel_iso_inv_right]
  rw [show (Proj.openCoverOfMapIrrelevantEqTop (quotientGrading (projIdeal W))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h))
      (projModelAffineEval_irrelevant_map_top W p q h)).f
      ⟨1, (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2),
        one_pos, mk_X_mem_quotientGrading_one W 2⟩ =
    Scheme.Opens.ι ((Spec (CommRingCat.of R)).basicOpen
      (((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) from rfl]
  rw [Iso.eq_inv_comp, Scheme.isoOfEq_hom_ι_assoc]
  have hζ : Spec.map (CommRingCat.ofHom (affineChartHom W p q h)) =
      (Spec (CommRingCat.of R)).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (affineChartHom W p q h) ≫
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv) := by
    rw [Spec.map_comp, toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]
  rw [hζ, ← morphismRestrict_ι_assoc]
  congr 1
  rw [← basicOpenIsoSpecAway_hom_SpecMap_assoc, Iso.cancel_iso_hom_left, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  have hval : (HomogeneousLocalization.valRingHom
      (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :
        Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+*
        Localization.Away ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) =
      algebraMap _ _ :=
    RingHom.ext fun y => rfl
  rw [affineChartHom, hval, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  apply IsLocalization.ringHom_ext
    (M := Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))
  rw [IsLocalization.map_comp, RingHom.comp_assoc, IsLocalization.Away.lift_comp,
    RingHom.comp_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The `Spec` of the chart evaluation composed with the chart inclusion is the
affine section (the glue step). -/
lemma spec_affineChartHom_awayι (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    Spec.map (CommRingCat.ofHom (affineChartHom W p q h)) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos =
      projModelAffineSection W p q h := by
  have hone : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp
      (projModelAffineEval W p q h)) ((quotientGradingHom (projIdeal W))
        (MvPolynomial.X 2)) = 1 := by
    rw [RingHom.comp_apply, projModelAffineEval_Z, map_one]
  have htop : (Spec (.of R)).basicOpen
      (((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) = ⊤ := by
    rw [hone]
    simp
  haveI : IsIso ((Spec (.of R)).basicOpen
      (((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).ι := by
    rw [htop]
    exact ⟨(Spec (.of R)).topIso.inv, (Spec (.of R)).topIso.hom_inv_id,
      (Spec (.of R)).topIso.inv_hom_id⟩
  rw [← cancel_epi (((Spec (.of R)).basicOpen
      (((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).ι)]
  show (Proj.openCoverOfMapIrrelevantEqTop (quotientGrading (projIdeal W))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h))
      (projModelAffineEval_irrelevant_map_top W p q h)).f
      ⟨1, (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2),
        one_pos, mk_X_mem_quotientGrading_one W 2⟩ ≫
      Spec.map (CommRingCat.ofHom (affineChartHom W p q h)) ≫
      Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos =
    (Proj.openCoverOfMapIrrelevantEqTop (quotientGrading (projIdeal W))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp (projModelAffineEval W p q h))
      (projModelAffineEval_irrelevant_map_top W p q h)).f
      ⟨1, (quotientGradingHom (projIdeal W)) (MvPolynomial.X 2),
        one_pos, mk_X_mem_quotientGrading_one W 2⟩ ≫
        projModelAffineSection W p q h
  conv_rhs => rw [projModelAffineSection, Proj.fromOfGlobalSections]
  rw [Scheme.Cover.ι_glueMorphisms]
  exact glue_pieceZ W p q h

set_option backward.isDefEq.respectTransparency false in
/-- The `Z`-chart factorisation of the affine section is `Spec` of the evaluation. -/
lemma projModelAffineChart_eq_spec (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    projModelAffineChart W p q h =
      Spec.map (CommRingCat.ofHom (affineChartHom W p q h)) := by
  rw [← cancel_mono (Proj.awayι (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
    (mk_X_mem_quotientGrading_one W 2) one_pos),
    projModelAffineChart_fac, spec_affineChartHom_awayι]

/-- The affine-point evaluation is natural in the base ring. -/
lemma projModelAffineEval_baseChangeGradedHom {R' : Type u} [CommRing R']
    [Algebra R R'] (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q)
    (h' : (W.map (algebraMap R R')).toAffine.Equation
      (algebraMap R R' p) (algebraMap R R' q)) (x : projCoordRing W) :
    projModelAffineEval (W.map (algebraMap R R')) (algebraMap R R' p)
      (algebraMap R R' q) h' ((baseChangeGradedHom (algebraMap R R') W) x) =
      algebraMap R R' (projModelAffineEval W p q h x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [show ((baseChangeGradedHom (algebraMap R R') W)
      (Ideal.Quotient.mk (projIdeal W).toIdeal f)) =
      Ideal.Quotient.mk (projIdeal (W.map (algebraMap R R'))).toIdeal
        (MvPolynomial.map (algebraMap R R') f) from
    quotientGradingMap_mk _ _ _ _ f]
  rw [projModelAffineEval_mk, projModelAffineEval_mk, MvPolynomial.eval_map]
  have h2 := MvPolynomial.eval₂_comp_left (algebraMap R R') (RingHom.id R)
    ![p, q, 1] f
  rw [MvPolynomial.eval₂_id, RingHom.comp_id] at h2
  rw [h2]
  congr 1
  funext i
  fin_cases i <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14b-2 ★)** Naturality of the affine-point section under base change:
`[σp : σq : 1]` of the base-changed curve, pushed along the model base change, is the
base change of `[p : q : 1]`. -/
lemma projModelAffineSection_baseChange {R' : Type u} [CommRing R'] [Algebra R R']
    (W : WeierstrassCurve R) (p q : R) (h : W.toAffine.Equation p q)
    (h' : (W.map (algebraMap R R')).toAffine.Equation
      (algebraMap R R' p) (algebraMap R R' q)) :
    projModelAffineSection (W.map (algebraMap R R')) (algebraMap R R' p)
        (algebraMap R R' q) h' ≫ projModelBaseChange (algebraMap R R') W =
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫
        projModelAffineSection W p q h := by
  rw [← projModelAffineChart_fac (W.map (algebraMap R R')) _ _ h', Category.assoc]
  rw [show projModelBaseChange (algebraMap R R') W =
    Proj.map (baseChangeGradedHom (algebraMap R R') W)
      (baseChangeGradedHom_irrelevant_le (algebraMap R R') W) from rfl]
  rw [← awayι_awayCongr (W.map (algebraMap R R'))
    (baseChangeGradedHom_mk_X (R' := R') W 2)
    ((baseChangeGradedHom (algebraMap R R') W).2
      (mk_X_mem_quotientGrading_one W 2))]
  rw [Category.assoc]
  rw [Proj.awayι_comp_map (baseChangeGradedHom (algebraMap R R') W)
    (baseChangeGradedHom_irrelevant_le (algebraMap R R') W) one_pos _
    (mk_X_mem_quotientGrading_one W 2)]
  rw [← projModelAffineChart_fac W p q h, ← Category.assoc, ← Category.assoc,
    ← Category.assoc]
  refine congrArg (· ≫ Proj.awayι (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
    (mk_X_mem_quotientGrading_one W 2) one_pos) ?_
  rw [projModelAffineChart_eq_spec, projModelAffineChart_eq_spec,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  refine congrArg Spec.map ?_
  ext x
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2)
    (x : HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
    Function.comp_apply]
  simp only [RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom, RingHom.coe_coe]
  rw [HomogeneousLocalization.Away.map_mk, awayCongr_mk, affineChartHom_mk,
    affineChartHom_mk, projModelAffineEval_baseChangeGradedHom W p q h h']

end ModularCurves
