/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionChartRing

/-!
# The chart-product ladder (T-W7.0c-c5β, β2b)

`biChartRing W i j ≃ₐ[R] affineChartRing (W ⊗ affineChartRing W j) i` — the `(i,j)`
chart-product ring of `E ×_R E` is the chart-`i` ring of the base-changed curve over the
chart-`j` ring. Consequences:

* `IsDomain`/`IsReduced` for chart-products reduce to the *single-chart* statement over a
  larger base (the remaining β2b leaf);
* `IsJacobsonRing (biChartRing W i j)` is already automatic (`MvPolynomial.isJacobsonRing`
  for finite variable sets + the quotient instance) — no code needed;
* β1's `Spec`-identification can consume the same ladder.

The proof is a three-step quotient transport: reorder and split the two relations
(`DoubleQuot.quotQuotEquivQuotSupₐ`), push the right-factor relation through `sumAlgEquiv`
(where `rename Sum.inr` becomes a coefficient constant — `sumAlgEquiv_comp_rename_inr`),
and absorb it into the coefficients (`quotientEquivQuotientMvPolynomial`).
-/

open MvPolynomial

namespace WeierstrassCurve.Projective

section QuotientMvPolynomialLemma

variable {S : Type*} [CommRing S] {σ : Type*}

/-- The inverse of `quotientEquivQuotientMvPolynomial` sends the class of a polynomial to
the polynomial of classes. -/
lemma quotientEquivQuotientMvPolynomial_symm_mk (I : Ideal S) (q : MvPolynomial σ S) :
    (MvPolynomial.quotientEquivQuotientMvPolynomial I (σ := σ)).symm
        (Ideal.Quotient.mk _ q) =
      MvPolynomial.map (Ideal.Quotient.mk I) q := by
  apply (MvPolynomial.quotientEquivQuotientMvPolynomial I (σ := σ)).injective
  rw [AlgEquiv.apply_symm_apply]
  show Ideal.Quotient.mk _ q = eval₂Hom _ _ (MvPolynomial.map (Ideal.Quotient.mk I) q)
  rw [coe_eval₂Hom, eval₂_map, Ideal.Quotient.lift_comp_mk]
  have h3 : (Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ S)))
      (eval₂ C X q) = Ideal.Quotient.mk _ q := by rw [eval₂_eta]
  exact (h3.symm.trans (eval₂_comp_left
    (Ideal.Quotient.mk (Ideal.map C I : Ideal (MvPolynomial σ S))) C X q))

end QuotientMvPolynomialLemma

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i j : Fin 3)

/-- Left-factor relation of the chart product. -/
private noncomputable abbrev gL : MvPolynomial ({k : Fin 3 // k ≠ i} ⊕ {k : Fin 3 // k ≠ j}) R :=
  rename Sum.inl (dehomogenizeAux R i W.toProjective.polynomial)

/-- Right-factor relation of the chart product. -/
private noncomputable abbrev gR : MvPolynomial ({k : Fin 3 // k ≠ i} ⊕ {k : Fin 3 // k ≠ j}) R :=
  rename Sum.inr (dehomogenizeAux R j W.toProjective.polynomial)

/-- The dehomogenised cubic of a base-changed curve is the coefficient-map image of the
original one. -/
lemma dehomogenizeAux_map_polynomial {S : Type*} [CommRing S] (φ : R →+* S) :
    dehomogenizeAux S i (W.map φ).toProjective.polynomial =
      MvPolynomial.map φ (dehomogenizeAux R i W.toProjective.polynomial) := by
  rw [map_polynomial, dehomogenizeAux_map]

/-- Absorb the right-factor relation into the coefficients: the quotient of the four-variable
ring by `gR` is the two-variable ring over the chart-`j` ring. -/
private noncomputable def innerEquiv :
    (MvPolynomial ({k : Fin 3 // k ≠ i} ⊕ {k : Fin 3 // k ≠ j}) R ⧸
        Ideal.span {gR W i j}) ≃ₐ[R]
      MvPolynomial {k : Fin 3 // k ≠ i} (affineChartRing W j) :=
  (Ideal.quotientEquivAlg _
      (Ideal.span {(C (dehomogenizeAux R j W.toProjective.polynomial) :
        MvPolynomial {k : Fin 3 // k ≠ i} (MvPolynomial {k : Fin 3 // k ≠ j} R))})
      (sumAlgEquiv R _ _) (by
        rw [Ideal.map_span, Set.image_singleton]
        have hE : (sumAlgEquiv R {k : Fin 3 // k ≠ i} {k : Fin 3 // k ≠ j}) (gR W i j) =
            C (dehomogenizeAux R j W.toProjective.polynomial) :=
          AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr
            (R := R) (S₁ := {k : Fin 3 // k ≠ i}) (S₂ := {k : Fin 3 // k ≠ j})) _
        exact congrArg (fun x => Ideal.span {x}) hE.symm)).trans <|
    (Ideal.quotientEquivAlgOfEq R (by rw [Ideal.map_span, Set.image_singleton])).trans
      ((MvPolynomial.quotientEquivQuotientMvPolynomial
        (Ideal.span {dehomogenizeAux R j W.toProjective.polynomial})).restrictScalars R).symm

/-- The image of the left-factor relation under `innerEquiv`. -/
private lemma innerEquiv_mk_gL :
    innerEquiv W i j (Ideal.Quotient.mk _ (gL W i j)) =
      MvPolynomial.map (algebraMap R (affineChartRing W j))
        (dehomogenizeAux R i W.toProjective.polynomial) := by
  rw [innerEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, Ideal.quotientEquivAlg_mk,
    Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.symm_restrictScalars,
    AlgEquiv.restrictScalars_apply]
  have hkey : ((sumAlgEquiv R {k : Fin 3 // k ≠ i}
        {k : Fin 3 // k ≠ j}).toAlgHom.toRingHom).comp
      ((rename (Sum.inl : {k : Fin 3 // k ≠ i} →
        {k : Fin 3 // k ≠ i} ⊕ {k : Fin 3 // k ≠ j})).toRingHom) =
      (MvPolynomial.map (algebraMap R (MvPolynomial {k : Fin 3 // k ≠ j} R))) := by
    refine ringHom_ext (fun r => ?_) (fun k => ?_)
    · show (sumAlgEquiv R _ _) ((rename Sum.inl) (C r)) = _
      simp only [rename_C, map_C, sumAlgEquiv_C_inl, MvPolynomial.algebraMap_eq]
    · show (sumAlgEquiv R _ _) ((rename Sum.inl) (X k)) = _
      simp only [rename_X, map_X, sumAlgEquiv_X_inl]
  have hgl : (sumAlgEquiv R {k : Fin 3 // k ≠ i} {k : Fin 3 // k ≠ j}) (gL W i j) =
      MvPolynomial.map (algebraMap R (MvPolynomial {k : Fin 3 // k ≠ j} R))
        (dehomogenizeAux R i W.toProjective.polynomial) :=
    RingHom.congr_fun hkey _
  rw [hgl, quotientEquivQuotientMvPolynomial_symm_mk, MvPolynomial.map_map]
  rfl

/-- **The ladder**: the `(i,j)` chart-product ring of `E ×_R E` is the chart-`i` ring of the
curve base-changed to the chart-`j` ring. -/
noncomputable def biChartRingEquiv :
    biChartRing W i j ≃ₐ[R]
      affineChartRing (W.map (algebraMap R (affineChartRing W j))) i :=
  (Ideal.quotientEquivAlgOfEq R (by rw [Ideal.span_insert, sup_comm])).trans <|
    (DoubleQuot.quotQuotEquivQuotSupₐ R (Ideal.span {gR W i j})
      (Ideal.span {gL W i j})).symm.trans <|
    (Ideal.quotientEquivAlg _ _ (innerEquiv W i j) rfl).trans <|
    Ideal.quotientEquivAlgOfEq R (by
      rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton,
        dehomogenizeAux_map_polynomial]
      congr 1
      show {innerEquiv W i j (Ideal.Quotient.mkₐ R _ (gL W i j))} = _
      rw [Ideal.Quotient.mkₐ_eq_mk, innerEquiv_mk_gL])

/-- Domain-ness of a chart-product reduces to the single-chart statement over the chart
base. -/
theorem isDomain_biChartRing
    [IsDomain (affineChartRing (W.map (algebraMap R (affineChartRing W j))) i)] :
    IsDomain (biChartRing W i j) :=
  (biChartRingEquiv W i j).toRingEquiv.isDomain _

end WeierstrassCurve.Projective
