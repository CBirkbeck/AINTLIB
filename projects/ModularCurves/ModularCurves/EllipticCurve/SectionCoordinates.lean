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

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
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
  set gc : { g : SpecPoints (projModel W) (projModelπ W) R //
      ∃ h : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))),
        h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos = g.1 } :=
    ⟨⟨τ, hπ'⟩, h₀, hfac⟩ with hgc
  set φ := chartHomEquiv W 2 R gc with hφdef
  -- the coordinates: the chart hom's values on `X/Z` and `Y/Z`
  set p : R := φ.1 (chartCoordEquiv W 2 (Ideal.Quotient.mk
    (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
    (MvPolynomial.X ⟨0, by decide⟩))) with hp
  set q : R := φ.1 (chartCoordEquiv W 2 (Ideal.Quotient.mk
    (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
    (MvPolynomial.X ⟨1, by decide⟩))) with hq
  -- the Weierstrass equation, from the dehomogenised cubic relation
  have hcubic0 : φ.1 (chartCoordEquiv W 2 (Ideal.Quotient.mk
      (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
      (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial))) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
      map_zero, map_zero]
  have haev := chart_hom_aeval W 2 φ.1 φ.2
    (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial)
  rw [hcubic0] at haev
  have hpoly : MvPolynomial.aeval (fun j : {j : Fin 3 // j ≠ 2} =>
      φ.1 (chartCoordEquiv W 2 (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial})
        (MvPolynomial.X j))))
      (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial) =
      q ^ 2 + W.a₁ * p * q + W.a₃ * q
        - (p ^ 3 + W.a₂ * p ^ 2 + W.a₄ * p + W.a₆) := by
    simp only [WeierstrassCurve.Projective.polynomial]
    simp only [map_sub, map_add, map_mul, map_pow, MvPolynomial.dehomogenizeAux_C,
      MvPolynomial.dehomogenizeAux_X_self,
      MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 2 by decide),
      MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 2 by decide),
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, mul_one, one_pow]
    rfl
  have heq : W.toAffine.Equation p q := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have hval : q ^ 2 + W.a₁ * p * q + W.a₃ * q
        - (p ^ 3 + W.a₂ * p ^ 2 + W.a₄ * p + W.a₆) = 0 :=
      hpoly.symm.trans haev.symm
    linear_combination hval
  refine ⟨p, q, heq, ?_⟩
  -- the affine section as a chart-factoring point
  have hπaff : projModelAffineSection W p q heq ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom (algebraMap R R)) := by
    rw [projModelAffineSection_projModelπ, Algebra.algebraMap_self,
      CommRingCat.ofHom_id, Spec.map_id]
  set gaff : { g : SpecPoints (projModel W) (projModelπ W) R //
      ∃ h : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))),
        h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
          (mk_X_mem_quotientGrading_one W 2) one_pos = g.1 } :=
    ⟨⟨projModelAffineSection W p q heq, hπaff⟩,
      projModelAffineChart W p q heq, projModelAffineChart_fac W p q heq⟩ with hgaff
  -- the chart hom of the affine section is the affine-chart evaluation
  have h1 : chartHomEquiv W 2 R gaff =
      ⟨affineChartHom W p q heq, affineChartHom_comp_algebraMap W p q heq⟩ :=
    chartHomEquiv_eq_of_specMap W 2 gaff
      ⟨affineChartHom W p q heq, affineChartHom_comp_algebraMap W p q heq⟩
      (spec_affineChartHom_awayι W p q heq)
  -- the two chart homs agree (values on constants and the two coordinates)
  have hhom : φ.1 = affineChartHom W p q heq := by
    have hext : φ.1.comp (((chartCoordEquiv W 2 :
          MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸
            Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial} ≃+*
          Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :
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
      · -- constants: both sides are the `R`-structure
        show φ.1 (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.C r))) =
          (affineChartHom W p q heq)
            (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.C r)))
        rw [chartCoordEquiv_mk_C]
        exact (RingHom.congr_fun φ.2 r).trans
          (RingHom.congr_fun (affineChartHom_comp_algebraMap W p q heq) r).symm
      · -- coordinates: `X/Z ↦ p`, `Y/Z ↦ q`
        show φ.1 (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.X j))) =
          (affineChartHom W p q heq)
            (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.X j)))
        have hval : (affineChartHom W p q heq)
            (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.X j))) =
            MvPolynomial.eval ![p, q, 1] (MvPolynomial.X j.1) := by
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
        rw [hval]
        rcases j with ⟨j, hj⟩
        fin_cases j
        · exact hp.symm.trans (by simp)
        · exact hq.symm.trans (by simp)
        · simp at hj
    refine RingHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := (chartCoordEquiv W 2).surjective a
    exact RingHom.congr_fun hext b
  -- injectivity of the chart-point correspondence
  have hgceq : gc = gaff := by
    refine (chartHomEquiv W 2 R).injective ?_
    rw [h1, ← hφdef]
    exact Subtype.ext hhom
  have := congrArg (fun z => z.1.1) hgceq
  simpa [hgc, hgaff] using this

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
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
  -- read the coordinates
  have hval : ∀ (j : {j : Fin 3 // j ≠ 2}) (a b : R) (ha : W.toAffine.Equation a b),
      (affineChartHom W a b ha)
        (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.X j))) =
        MvPolynomial.eval ![a, b, 1] (MvPolynomial.X j.1) := by
    intro j a b ha
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
  constructor
  · have h0 := congrArg (fun (ψ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+* R) =>
      ψ (chartCoordEquiv W 2 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 2}))))) hch
    simp only [hval] at h0
    simpa using h0
  · have h0 := congrArg (fun (ψ : Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) →+* R) =>
      ψ (chartCoordEquiv W 2 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨1, by decide⟩ : {j : Fin 3 // j ≠ 2}))))) hch
    simp only [hval] at h0
    simpa using h0

end ModularCurves
