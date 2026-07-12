/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.ComparisonCoefficients

/-!
# Coordinate action of the projective variable-change isomorphism (T-W7.1b bridge)

The geometric bridge for the T-W7.1b comparison theorem: an explicit computation of the induced
coordinate-ring automorphism `pointedIsoCoordEquiv (projModelVCIso C W)` of the scheme isomorphism
attached to a `VariableChange C`. It sends `x ↦ u²·x' + r` and `y ↦ u³·y' + s·u²·x' + t`
(`bridge_coordX` / `bridge_coordY`), matching the affine variable change.

The proof routes through `pointedIsoCoordEquiv_sections`: `pointedIsoΓ (projModelVCIso C W)` is the
section-level action of `Proj.map (vcGradedHom C W)`, which on the `Z`-chart is the homogeneous
localization map `HomogeneousLocalization.Away.map (vcGradedHom C W)` (via `Proj.awayι_comp_map`);
`chartZRingEquiv_x`/`_y` then land the generators on `coordX`/`coordY`.

These feed the `main`/`b5` leaves: `bridge_coordX`/`_coordY` instantiate the bridge hypotheses of
`projModelVCIso_injective` and provide the coordinate action for `pointedIso_exists_variableChange`.

AINTLIB ModularCurves T-W7.1b (lane P3-parallel, beastmode-P3b3).
-/

open WeierstrassCurve CategoryTheory
namespace ModularCurves
open AlgebraicGeometry HomogeneousLocalization HomogeneousIdeal
universe u
variable {R : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Aux A: image of `X j` class under `vcGradedHom`. -/
lemma vcGradedHom_mk_X (C : VariableChange R) (W : WeierstrassCurve R) (j : Fin 3) :
    (vcGradedHom C W) ((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)) =
      (quotientGradingHom (projIdeal (C • W))) (vcMvSubst C j) := by
  show quotientGradingMap (vcMvGraded C) _ _ _ (Ideal.Quotient.mk _ _) = _
  rw [quotientGradingMap_mk]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval (vcMvSubst C) (MvPolynomial.X j)) = _
  rw [MvPolynomial.aeval_X]
  rfl

/-- Aux A2: `vcGradedHom` fixes the `X 2` class. -/
lemma vcGradedHom_mk_X2 (C : VariableChange R) (W : WeierstrassCurve R) :
    (vcGradedHom C W) ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) =
      (quotientGradingHom (projIdeal (C • W))) (MvPolynomial.X 2) := by
  rw [vcGradedHom_mk_X]; rfl

/-- Aux B core (decomposition): the `Away.mk` of a linear numerator `a·X0 + b·X2` over `X2`. -/
lemma away_mk_linear_decomp (V : WeierstrassCurve R) (a b : R)
    (hmem : (quotientGradingHom (projIdeal V)) (a • MvPolynomial.X 0 + b • MvPolynomial.X 2)
      ∈ quotientGrading (projIdeal V) (1 • 1)) :
    HomogeneousLocalization.Away.mk (quotientGrading (projIdeal V))
        (mk_X_mem_quotientGrading_one V 2) 1
        ((quotientGradingHom (projIdeal V)) (a • MvPolynomial.X 0 + b • MvPolynomial.X 2)) hmem
      = HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal V))
          (Submonoid.powers ((quotientGradingHom (projIdeal V)) (MvPolynomial.X 2)))
          ((algebraMapGradeZero (projIdeal V)) a)
        * HomogeneousLocalization.Away.isLocalizationElem
            (mk_X_mem_quotientGrading_one V 2) (mk_X_mem_quotientGrading_one V 0)
      + HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal V))
          (Submonoid.powers ((quotientGradingHom (projIdeal V)) (MvPolynomial.X 2)))
          ((algebraMapGradeZero (projIdeal V)) b) := by
  have hC : ∀ r : R, (Ideal.Quotient.mk (projIdeal V).toIdeal (MvPolynomial.C r) :
      projCoordRing V) = algebraMap R (projCoordRing V) r := fun r => by
    rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing V),
      RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
  have hnum : (quotientGradingHom (projIdeal V))
      (a • MvPolynomial.X 0 + b • MvPolynomial.X 2) =
      algebraMap R (projCoordRing V) a *
        (quotientGradingHom (projIdeal V)) (MvPolynomial.X 0)
      + algebraMap R (projCoordRing V) b *
        (quotientGradingHom (projIdeal V)) (MvPolynomial.X 2) := by
    simp only [quotientGradingHom_apply, MvPolynomial.smul_eq_C_mul, map_add, map_mul]
    rw [hC, hC]
  have hfz : ∀ g : ↥(quotientGrading (projIdeal V) 0),
      (HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal V))
        (Submonoid.powers ((quotientGradingHom (projIdeal V)) (MvPolynomial.X 2))) g).val
      = Localization.mk (↑g) 1 := fun g => rfl
  apply val_injective
  rw [HomogeneousLocalization.val_add, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    hfz, hfz, Localization.mk_mul, Localization.add_mk, coe_algebraMapGradeZero,
    coe_algebraMapGradeZero, hnum]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, pow_one, one_mul, mul_one]
  ring

/-- Aux B (landing): `chartZRingEquiv` of the linear `Away.mk`. -/
lemma away_mk_linear (V : WeierstrassCurve R) (a b : R)
    (hmem : (quotientGradingHom (projIdeal V)) (a • MvPolynomial.X 0 + b • MvPolynomial.X 2)
      ∈ quotientGrading (projIdeal V) (1 • 1)) :
    chartZRingEquiv V (HomogeneousLocalization.Away.mk (quotientGrading (projIdeal V))
        (mk_X_mem_quotientGrading_one V 2) 1
        ((quotientGradingHom (projIdeal V)) (a • MvPolynomial.X 0 + b • MvPolynomial.X 2)) hmem)
      = algebraMap R _ a * coordX V + algebraMap R _ b := by
  rw [away_mk_linear_decomp, map_add, map_mul, chartZRingEquiv_fromZero, chartZRingEquiv_x,
    chartZRingEquiv_fromZero]

/-- Aux T: `awayToSection` is natural under `awayCongr` and the presheaf `eqToHom` transport. -/
lemma awayToSection_presheaf_awayCongr {V : WeierstrassCurve R}
    {s t : projCoordRing V} (heq : s = t)
    (z : HomogeneousLocalization.Away (quotientGrading (projIdeal V)) s) :
    ((projModel V).presheaf.map (eqToHom
        (show Proj.basicOpen (quotientGrading (projIdeal V)) t
            = Proj.basicOpen (quotientGrading (projIdeal V)) s by rw [heq])).op).hom
        ((Proj.awayToSection (quotientGrading (projIdeal V)) s).hom z)
      = (Proj.awayToSection (quotientGrading (projIdeal V)) t).hom (awayCongr heq z) := by
  subst heq
  rw [awayCongr_rfl, eqToHom_refl, CategoryTheory.op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Aux C (naturality): `pointedIsoΓ` of the variable-change iso, on the image of a `Z`-chart
`Away` element under `awayToSection`, equals `awayToSection` of the transported `Away.map`. -/
lemma auxC (C : VariableChange R) (W : WeierstrassCurve R)
    (w : HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :
    pointedIsoΓ (projModelVCIso C W) (projModelVCIso_zero C W)
        ((Proj.awayToSection (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))).hom w)
      = (Proj.awayToSection (quotientGrading (projIdeal (C • W)))
          ((quotientGradingHom (projIdeal (C • W))) (MvPolynomial.X 2))).hom
          (awayCongr (vcGradedHom_mk_X2 C W)
            (HomogeneousLocalization.Away.map (vcGradedHom C W)
              ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) w)) := by
  have hcomp := Proj.awayToSection_comp_appLE (vcGradedHom C W) (vcGradedHom_irrelevant_le C W)
      (mk_X_mem_quotientGrading_one W 2)
  have hel := congrArg (fun φ => CommRingCat.Hom.hom φ w) hcomp
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appLE,
    CommRingCat.hom_ofHom] at hel
  rw [← awayToSection_presheaf_awayCongr (vcGradedHom_mk_X2 C W)
    (HomogeneousLocalization.Away.map (vcGradedHom C W)
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) w)]
  rw [← hel]
  show ((projModel (C • W)).presheaf.map (eqToHom
      (pointedIso_preimage_zChart (projModelVCIso C W) (projModelVCIso_zero C W)).symm).op).hom _
    = _
  rw [← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
  congr 1

/-- H1: `(chartZSectionsRingEquiv V).symm ∘ chartZRingEquiv V = awayToSection`. -/
lemma chartZSectionsRingEquiv_symm_chartZRingEquiv (V : WeierstrassCurve R)
    (w : HomogeneousLocalization.Away (quotientGrading (projIdeal V))
      ((quotientGradingHom (projIdeal V)) (MvPolynomial.X 2))) :
    (chartZSectionsRingEquiv V).symm (chartZRingEquiv V w) =
      (Proj.awayToSection (quotientGrading (projIdeal V))
        ((quotientGradingHom (projIdeal V)) (MvPolynomial.X 2))).hom w := by
  rw [chartZSectionsRingEquiv, RingEquiv.symm_trans_apply, RingEquiv.symm_symm,
    RingEquiv.symm_apply_apply]
  rfl

/-- H2: `chartZSectionsRingEquiv V ∘ awayToSection = chartZRingEquiv V`. -/
lemma chartZSectionsRingEquiv_awayToSection (V : WeierstrassCurve R)
    (z : HomogeneousLocalization.Away (quotientGrading (projIdeal V))
      ((quotientGradingHom (projIdeal V)) (MvPolynomial.X 2))) :
    chartZSectionsRingEquiv V ((Proj.awayToSection (quotientGrading (projIdeal V))
        ((quotientGradingHom (projIdeal V)) (MvPolynomial.X 2))).hom z) =
      chartZRingEquiv V z := by
  rw [chartZSectionsRingEquiv, RingEquiv.trans_apply]
  congr 1
  rw [RingEquiv.symm_apply_eq]
  rfl

/-- Master lemma (steps 1-4): the coordinate equivalence of the variable-change iso, on a
`Z`-chart element, equals `chartZRingEquiv` of the transported graded `Away.map`. -/
lemma pointedIsoCoordEquiv_vc_chartZRingEquiv (C : VariableChange R) (W : WeierstrassCurve R)
    (w : HomogeneousLocalization.Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :
    pointedIsoCoordEquiv (projModelVCIso C W) (projModelVCIso_π C W) (projModelVCIso_zero C W)
        (chartZRingEquiv W w)
      = chartZRingEquiv (C • W)
          (awayCongr (vcGradedHom_mk_X2 C W)
            (HomogeneousLocalization.Away.map (vcGradedHom C W)
              ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) w)) := by
  have hsec := pointedIsoCoordEquiv_sections (projModelVCIso C W) (projModelVCIso_π C W)
    (projModelVCIso_zero C W) (chartZRingEquiv W w)
  rw [chartZSectionsRingEquiv_symm_chartZRingEquiv, auxC] at hsec
  have h2 := congrArg (chartZSectionsRingEquiv (C • W)) hsec
  rw [RingEquiv.apply_symm_apply, chartZSectionsRingEquiv_awayToSection] at h2
  exact h2

/-- Trilinear decomposition: `Away.mk` of `a·X1 + b·X0 + c·X2` over `X2`. -/
lemma away_mk_trilinear_decomp (V : WeierstrassCurve R) (a b c : R)
    (hmem : (quotientGradingHom (projIdeal V))
        (a • MvPolynomial.X 1 + b • MvPolynomial.X 0 + c • MvPolynomial.X 2)
      ∈ quotientGrading (projIdeal V) (1 • 1)) :
    HomogeneousLocalization.Away.mk (quotientGrading (projIdeal V))
        (mk_X_mem_quotientGrading_one V 2) 1
        ((quotientGradingHom (projIdeal V))
          (a • MvPolynomial.X 1 + b • MvPolynomial.X 0 + c • MvPolynomial.X 2)) hmem
      = HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal V))
          (Submonoid.powers ((quotientGradingHom (projIdeal V)) (MvPolynomial.X 2)))
          ((algebraMapGradeZero (projIdeal V)) a)
        * HomogeneousLocalization.Away.isLocalizationElem
            (mk_X_mem_quotientGrading_one V 2) (mk_X_mem_quotientGrading_one V 1)
      + HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal V))
          (Submonoid.powers ((quotientGradingHom (projIdeal V)) (MvPolynomial.X 2)))
          ((algebraMapGradeZero (projIdeal V)) b)
        * HomogeneousLocalization.Away.isLocalizationElem
            (mk_X_mem_quotientGrading_one V 2) (mk_X_mem_quotientGrading_one V 0)
      + HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal V))
          (Submonoid.powers ((quotientGradingHom (projIdeal V)) (MvPolynomial.X 2)))
          ((algebraMapGradeZero (projIdeal V)) c) := by
  have hC : ∀ r : R, (Ideal.Quotient.mk (projIdeal V).toIdeal (MvPolynomial.C r) :
      projCoordRing V) = algebraMap R (projCoordRing V) r := fun r => by
    rw [IsScalarTower.algebraMap_eq R (MvPolynomial (Fin 3) R) (projCoordRing V),
      RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
  have hnum : (quotientGradingHom (projIdeal V))
      (a • MvPolynomial.X 1 + b • MvPolynomial.X 0 + c • MvPolynomial.X 2) =
      algebraMap R (projCoordRing V) a *
        (quotientGradingHom (projIdeal V)) (MvPolynomial.X 1)
      + algebraMap R (projCoordRing V) b *
        (quotientGradingHom (projIdeal V)) (MvPolynomial.X 0)
      + algebraMap R (projCoordRing V) c *
        (quotientGradingHom (projIdeal V)) (MvPolynomial.X 2) := by
    simp only [quotientGradingHom_apply, MvPolynomial.smul_eq_C_mul, map_add, map_mul]
    rw [hC, hC, hC]
  have hfz : ∀ g : ↥(quotientGrading (projIdeal V) 0),
      (HomogeneousLocalization.fromZeroRingHom (quotientGrading (projIdeal V))
        (Submonoid.powers ((quotientGradingHom (projIdeal V)) (MvPolynomial.X 2))) g).val
      = Localization.mk (↑g) 1 := fun g => rfl
  apply val_injective
  rw [HomogeneousLocalization.val_add, HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, hfz, hfz, hfz]
  rw [coe_algebraMapGradeZero, coe_algebraMapGradeZero, coe_algebraMapGradeZero, hnum]
  rw [Localization.mk_mul, Localization.mk_mul]
  rw [Localization.add_mk, Localization.add_mk]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, pow_one, one_mul, mul_one]
  ring

/-- Trilinear landing: `chartZRingEquiv` of the trilinear `Away.mk`. -/
lemma away_mk_trilinear (V : WeierstrassCurve R) (a b c : R)
    (hmem : (quotientGradingHom (projIdeal V))
        (a • MvPolynomial.X 1 + b • MvPolynomial.X 0 + c • MvPolynomial.X 2)
      ∈ quotientGrading (projIdeal V) (1 • 1)) :
    chartZRingEquiv V (HomogeneousLocalization.Away.mk (quotientGrading (projIdeal V))
        (mk_X_mem_quotientGrading_one V 2) 1
        ((quotientGradingHom (projIdeal V))
          (a • MvPolynomial.X 1 + b • MvPolynomial.X 0 + c • MvPolynomial.X 2)) hmem)
      = algebraMap R _ a * coordY V + algebraMap R _ b * coordX V + algebraMap R _ c := by
  rw [away_mk_trilinear_decomp, map_add, map_add, map_mul, map_mul, chartZRingEquiv_fromZero,
    chartZRingEquiv_y, chartZRingEquiv_fromZero, chartZRingEquiv_x, chartZRingEquiv_fromZero]

/-- P3: the transported graded `Away.map` of the `X0`/`X1`-over-`X2` generator is the `Away.mk`
of the substituted numerator `vcMvSubst C j`. -/
lemma awayCongr_map_isLoc (C : VariableChange R) (W : WeierstrassCurve R) (j : Fin 3)
    (hmem : (quotientGradingHom (projIdeal (C • W))) (vcMvSubst C j)
      ∈ quotientGrading (projIdeal (C • W)) (1 • 1)) :
    awayCongr (vcGradedHom_mk_X2 C W)
        (HomogeneousLocalization.Away.map (vcGradedHom C W)
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (HomogeneousLocalization.Away.isLocalizationElem
            (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W j)))
      = HomogeneousLocalization.Away.mk (quotientGrading (projIdeal (C • W)))
          (mk_X_mem_quotientGrading_one (C • W) 2) 1
          ((quotientGradingHom (projIdeal (C • W))) (vcMvSubst C j)) hmem := by
  rw [show HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W j)
      = HomogeneousLocalization.Away.mk (quotientGrading (projIdeal W))
          (mk_X_mem_quotientGrading_one W 2) 1
          (((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)) ^ 1)
          (by rw [pow_one]; exact mk_X_mem_quotientGrading_one W j) from rfl]
  rw [HomogeneousLocalization.Away.map_mk, awayCongr_mk]
  apply val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  rw [map_pow, vcGradedHom_mk_X, pow_one]

/-- **BRIDGE (coordX)**: the coordinate iso of a variable change sends `x` to `u²·x' + r`. -/
lemma bridge_coordX (C : VariableChange R) (W : WeierstrassCurve R) :
    pointedIsoCoordEquiv (projModelVCIso C W) (projModelVCIso_π C W) (projModelVCIso_zero C W)
        (coordX W)
      = algebraMap R _ ((↑C.u : R) ^ 2) * coordX (C • W) + algebraMap R _ C.r := by
  have hmem : (quotientGradingHom (projIdeal (C • W))) (vcMvSubst C 0)
      ∈ quotientGrading (projIdeal (C • W)) (1 • 1) := by
    rw [smul_eq_mul, mul_one]
    exact mk_mem_quotientGrading _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (vcMvSubst_isHomogeneous C 0))
  rw [← chartZRingEquiv_x W, pointedIsoCoordEquiv_vc_chartZRingEquiv,
    awayCongr_map_isLoc C W 0 hmem]
  exact away_mk_linear (C • W) ((↑C.u : R) ^ 2) C.r hmem

/-- **BRIDGE (coordY)**: the coordinate iso sends `y` to `u³·y' + s·u²·x' + t`. -/
lemma bridge_coordY (C : VariableChange R) (W : WeierstrassCurve R) :
    pointedIsoCoordEquiv (projModelVCIso C W) (projModelVCIso_π C W) (projModelVCIso_zero C W)
        (coordY W)
      = algebraMap R _ ((↑C.u : R) ^ 3) * coordY (C • W)
        + algebraMap R _ (C.s * (↑C.u : R) ^ 2) * coordX (C • W) + algebraMap R _ C.t := by
  have hmem : (quotientGradingHom (projIdeal (C • W))) (vcMvSubst C 1)
      ∈ quotientGrading (projIdeal (C • W)) (1 • 1) := by
    rw [smul_eq_mul, mul_one]
    exact mk_mem_quotientGrading _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (vcMvSubst_isHomogeneous C 1))
  rw [← chartZRingEquiv_y W, pointedIsoCoordEquiv_vc_chartZRingEquiv,
    awayCongr_map_isLoc C W 1 hmem]
  exact away_mk_trilinear (C • W) ((↑C.u : R) ^ 3) (C.s * (↑C.u : R) ^ 2) C.t hmem

end ModularCurves
