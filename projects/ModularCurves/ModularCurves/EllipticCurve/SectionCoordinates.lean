/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AffinePointSection

/-!
# Reading affine coordinates off a model section ([hArb-1] core)

**(STREAM-OMEGA 2026-07-17.)** The converse of `projModelAffineSection`: a section of
the projective Weierstrass model over `Spec R` that factors through the `Z`-chart IS
the affine-point section of a (unique) solution `(p, q)` of the Weierstrass equation —
`eq_affineSection_of_zChart_factor`. The engine is `chartHomEquiv` (chart-factoring
`Spec`-points ≃ `R`-compatible ring maps out of the chart ring, over an ARBITRARY
`R`-algebra — here `K := R` itself) together with `chartCoordEquiv` (the chart ring is
the plane coordinate ring mod the dehomogenised cubic): the ring map's values on the
two chart coordinates are the affine coordinates, the dehomogenised cubic relation is
the Weierstrass equation, and `chartHomEquiv`'s injectivity identifies the section with
`projModelAffineSection`.

This is the coordinate-reading step of the `IsE3Datum` cover assembly (hArb,
`Moduli/Bootstrap.lean:95`): level sections avoid the zero section fibrewise, hence
land in the `Z`-chart locally on the base, hence are marked at honest coordinates.
-/

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization

variable {R : Type u} [CommRing R]

/-- The `R`-structure compatibility of the affine-chart evaluation: transporting
`projModelAffineSection ≫ projModelπ = 𝟙` through `Spec`. -/
theorem affineChartHom_comp_algebraMap (W : WeierstrassCurve R) (p q : R)
    (heq : W.toAffine.Equation p q) :
    (affineChartHom W p q heq).comp
      ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
      algebraMap R R := by
  have h2 : Spec.map (CommRingCat.ofHom ((affineChartHom W p q heq).comp
      ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))))) =
      Spec.map (CommRingCat.ofHom (algebraMap R R)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← awayι_projModelπ W 2,
      ← Category.assoc, spec_affineChartHom_awayι, projModelAffineSection_projModelπ,
      Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have h3 := Spec.map_injective h2
  exact congrArg CommRingCat.Hom.hom h3

/-- The `Z`-chart ring presented by the plane coordinate ring, evaluated on the coordinate
`X j`, reads off the affine coordinates of the affine-point evaluation. -/
private lemma affineChartHom_chartCoordEquiv_X (W : WeierstrassCurve R) (a b : R)
    (ha : W.toAffine.Equation a b) (j : {j : Fin 3 // j ≠ 2}) :
    (affineChartHom W a b ha)
        (chartCoordEquiv W 2 (Ideal.Quotient.mk
          (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
          (MvPolynomial.X j))) =
      MvPolynomial.eval ![a, b, 1] (MvPolynomial.X j.1) := by
  rw [chartCoordEquiv_mk_X]
  rw [show Away.isLocalizationElem (mk_X_mem_quotientGrading_one W 2)
      (mk_X_mem_quotientGrading_one W j.1) =
    Away.mk (quotientGrading (projIdeal W))
      (mk_X_mem_quotientGrading_one W 2) 1
      (((quotientGradingHom (projIdeal W)) (MvPolynomial.X j.1)) ^ 1)
      (by
        simpa using SetLike.pow_mem_graded 1
          (mk_X_mem_quotientGrading_one W j.1)) from rfl]
  rw [affineChartHom_mk, map_pow, pow_one]
  rw [show (quotientGradingHom (projIdeal W)) (MvPolynomial.X j.1) =
    Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X j.1) from rfl]
  rw [projModelAffineEval_mk]

/-- The values of an `R`-compatible `Z`-chart hom on the two chart coordinates solve the
Weierstrass equation, because the dehomogenised cubic vanishes in the chart ring. -/
private lemma chartHom_coord_equation (W : WeierstrassCurve R)
    (φ : Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+* R)
    (hφ : φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
      algebraMap R R)
    {p q : R}
    (hp : φ (chartCoordEquiv W 2 (Ideal.Quotient.mk
      (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
      (MvPolynomial.X ⟨0, by decide⟩))) = p)
    (hq : φ (chartCoordEquiv W 2 (Ideal.Quotient.mk
      (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
      (MvPolynomial.X ⟨1, by decide⟩))) = q) :
    W.toAffine.Equation p q := by
  have hcubic0 : φ (chartCoordEquiv W 2 (Ideal.Quotient.mk
      (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
      (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial))) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
      map_zero, map_zero]
  have haev := chart_hom_aeval W 2 φ hφ
    (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial)
  rw [hcubic0] at haev
  have hpoly : MvPolynomial.aeval (fun j : {j : Fin 3 // j ≠ 2} =>
      φ (chartCoordEquiv W 2 (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
        (MvPolynomial.X j))))
      (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial) =
      q ^ 2 + W.a₁ * p * q + W.a₃ * q
        - (p ^ 3 + W.a₂ * p ^ 2 + W.a₄ * p + W.a₆) := by
    subst hp
    subst hq
    simp only [WeierstrassCurve.Projective.polynomial]
    simp only [map_sub, map_add, map_mul, map_pow, MvPolynomial.dehomogenizeAux_C,
      MvPolynomial.dehomogenizeAux_X_self,
      MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 2 by decide),
      MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 2 by decide),
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, mul_one, one_pow]
    rfl
  rw [WeierstrassCurve.Affine.equation_iff]
  linear_combination hpoly.symm.trans haev.symm

/-- An `R`-compatible `Z`-chart hom is determined by its values on the two chart
coordinates: it is the affine-chart evaluation at those coordinates. -/
private lemma eq_affineChartHom_of_coord_values (W : WeierstrassCurve R)
    (φ : Away (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+* R)
    (hφ : φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
        (Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
      algebraMap R R)
    {p q : R} (heq : W.toAffine.Equation p q)
    (hp : φ (chartCoordEquiv W 2 (Ideal.Quotient.mk
      (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
      (MvPolynomial.X ⟨0, by decide⟩))) = p)
    (hq : φ (chartCoordEquiv W 2 (Ideal.Quotient.mk
      (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
      (MvPolynomial.X ⟨1, by decide⟩))) = q) :
    φ = affineChartHom W p q heq := by
  have hext : φ.comp (((chartCoordEquiv W 2 : _ ≃+* _) :
        MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial} →+*
        Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) =
      (affineChartHom W p q heq).comp (((chartCoordEquiv W 2 : _ ≃+* _) :
        MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸
          Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial} →+*
        Away (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) := by
    refine Ideal.Quotient.ringHom_ext
      (MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_))
    · show φ (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.C r))) =
        (affineChartHom W p q heq)
          (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.C r)))
      rw [chartCoordEquiv_mk_C]
      exact (RingHom.congr_fun hφ r).trans
        (RingHom.congr_fun (affineChartHom_comp_algebraMap W p q heq) r).symm
    · show φ (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.X j))) =
        (affineChartHom W p q heq)
          (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.X j)))
      rw [affineChartHom_chartCoordEquiv_X W p q heq j]
      rcases j with ⟨j, hj⟩
      fin_cases j
      · exact hp.trans (by simp)
      · exact hq.trans (by simp)
      · simp at hj
  refine RingHom.ext fun a => ?_
  obtain ⟨b, rfl⟩ := (chartCoordEquiv W 2).surjective a
  exact RingHom.congr_fun hext b

/-- **([hArb-1] the coordinate reading)** A section of the projective model over
`Spec R` factoring through the `Z`-chart is the affine-point section of a solution of
the Weierstrass equation. -/
theorem eq_affineSection_of_zChart_factor (W : WeierstrassCurve R)
    (τ : Spec (CommRingCat.of R) ⟶ projModel W)
    (hπ : τ ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of R)))
    (h₀ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of
      (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))))
    (hfac : h₀ ≫ Proj.awayι (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos = τ) :
    ∃ (p q : R) (heq : W.toAffine.Equation p q),
      τ = projModelAffineSection W p q heq := by
  have hπ' : τ ≫ projModelπ W = Spec.map (CommRingCat.ofHom (algebraMap R R)) := by
    rw [hπ, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  obtain ⟨⟨φ, hφ⟩, hgc⟩ :
      ∃ ψ, chartHomEquiv W 2 R ⟨⟨τ, hπ'⟩, h₀, hfac⟩ = ψ := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : R, φ (chartCoordEquiv W 2 (Ideal.Quotient.mk
    (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
    (MvPolynomial.X ⟨0, by decide⟩))) = p := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : R, φ (chartCoordEquiv W 2 (Ideal.Quotient.mk
    (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
    (MvPolynomial.X ⟨1, by decide⟩))) = q := ⟨_, rfl⟩
  have heq : W.toAffine.Equation p q := chartHom_coord_equation W φ hφ hp hq
  have hπaff : projModelAffineSection W p q heq ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom (algebraMap R R)) := by
    rw [projModelAffineSection_projModelπ, Algebra.algebraMap_self,
      CommRingCat.ofHom_id, Spec.map_id]
  refine ⟨p, q, heq, congrArg (fun z => z.1.1) ((chartHomEquiv W 2 R).injective
    (hgc.trans (Subtype.ext (eq_affineChartHom_of_coord_values W φ hφ heq hp hq)) |>.trans
      (chartHomEquiv_eq_of_specMap W 2
        ⟨⟨projModelAffineSection W p q heq, hπaff⟩,
          projModelAffineChart W p q heq, projModelAffineChart_fac W p q heq⟩
        ⟨affineChartHom W p q heq, affineChartHom_comp_algebraMap W p q heq⟩
        (spec_affineChartHom_awayι W p q heq)).symm))⟩

set_option backward.isDefEq.respectTransparency false in
/-- **([hArb-1] companion: coordinate uniqueness)** The affine-point section determines
its coordinates: compose with the chart factorisation and read the two chart
coordinates off the evaluation homs. -/
theorem projModelAffineSection_injective (W : WeierstrassCurve R) {p q p' q' : R}
    {h : W.toAffine.Equation p q} {h' : W.toAffine.Equation p' q'}
    (heq : projModelAffineSection W p q h = projModelAffineSection W p' q' h') :
    p = p' ∧ q = q' := by
  -- the chart evaluations agree
  have hch : affineChartHom W p q h = affineChartHom W p' q' h' := by
    have h1 : Spec.map (CommRingCat.ofHom (affineChartHom W p q h)) =
        Spec.map (CommRingCat.ofHom (affineChartHom W p' q' h')) := by
      have := spec_affineChartHom_awayι W p q h
      rw [heq, ← spec_affineChartHom_awayι W p' q' h'] at this
      exact (cancel_mono (Proj.awayι (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos)).mp this
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  constructor
  · have h0 := congrArg (fun (ψ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+* R) =>
      ψ (chartCoordEquiv W 2 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 2}))))) hch
    simp only [affineChartHom_chartCoordEquiv_X] at h0
    simpa using h0
  · have h0 := congrArg (fun (ψ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+* R) =>
      ψ (chartCoordEquiv W 2 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨1, by decide⟩ : {j : Fin 3 // j ≠ 2}))))) hch
    simp only [affineChartHom_chartCoordEquiv_X] at h0
    simpa using h0

end ModularCurves
