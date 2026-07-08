import ModularCurves.EllipticCurve.AdditionChartRing

/-!
# The chart-product ladder (T-W7.0c-c5β, β2b)

`biChartRing W i j ≃ₐ[R] affineChartRing (W ⊗ affineChartRing W j) i` — the `(i,j)`
chart-product of `E ×_R E` is the chart-`i` ring of the base-changed curve over the
chart-`j` ring. Consequences:

* `IsDomain`/`IsReduced` for the chart-product reduce to the *single-chart* statement over
  a larger base (the remaining β2b leaf);
* `IsJacobsonRing (biChartRing W i j)` is already automatic (`MvPolynomial.isJacobsonRing`
  for finite variable sets + the quotient instance) — no code needed;
* β1's `Spec`-identification can consume the same ladder.

The proof is a standard three-step quotient transport: split the two relations
(`quotQuotEquivQuotSupₐ`), push the inner one through `sumAlgEquiv` (where
`rename Sum.inr` becomes a constant — `sumAlgEquiv_comp_rename_inr`), and absorb it into
the coefficients (`quotientEquivQuotientMvPolynomial`).
-/

open MvPolynomial

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i j : Fin 3)

private abbrev σ₁ (i : Fin 3) := {k : Fin 3 // k ≠ i}

/-- The inner relation: the right factor's dehomogenised cubic. -/
private noncomputable abbrev gInner : MvPolynomial (σ₁ i ⊕ σ₁ j) R :=
  rename Sum.inl (dehomogenizeAux R i W.toProjective.polynomial)

private noncomputable abbrev gOuter : MvPolynomial (σ₁ i ⊕ σ₁ j) R :=
  rename Sum.inr (dehomogenizeAux R j W.toProjective.polynomial)

/-- The dehomogenised cubic of the base-changed curve is the coefficient-map image of the
original one. -/
lemma dehomogenizeAux_map_polynomial {S : Type*} [CommRing S] (φ : R →+* S) :
    dehomogenizeAux S i (W.map φ).toProjective.polynomial =
      MvPolynomial.map φ (dehomogenizeAux R i W.toProjective.polynomial) := by
  rw [map_polynomial, dehomogenizeAux_map]

/-- **The ladder**: the `(i,j)` chart-product ring of `E ×_R E` is the chart-`i` ring of the
curve base-changed to the chart-`j` ring. -/
noncomputable def biChartRingEquiv :
    biChartRing W i j ≃ₐ[R]
      affineChartRing (W.map (algebraMap R (affineChartRing W j))) i := by
  refine AlgEquiv.trans (Ideal.quotientEquivAlgOfEq R ?_ :
      biChartRing W i j ≃ₐ[R] _ ⧸ (Ideal.span {gOuter W i j} ⊔ Ideal.span {gInner W i j}))
    (AlgEquiv.trans (Ideal.quotQuotEquivQuotSupₐ R _ _).symm ?_)
  · rw [Ideal.span_insert, sup_comm]
  -- transport the outer quotient along the inner-quotient equivalence
  refine AlgEquiv.trans (Ideal.quotientEquivAlg _ _ ?e ?hmap) (Ideal.quotientEquivAlgOfEq R ?_)
  case e =>
    -- (P ⧸ ⟨gOuter⟩) ≃ MvPolynomial (σ₁ i) (affineChartRing W j)
    refine AlgEquiv.trans (Ideal.quotientEquivAlg _
      (Ideal.span {(C (dehomogenizeAux R j W.toProjective.polynomial) :
        MvPolynomial (σ₁ i) (MvPolynomial (σ₁ j) R))})
      (sumAlgEquiv R (σ₁ i) (σ₁ j)) ?_) ?_
    · rw [Ideal.map_span, Set.image_singleton]
      congr 1
      exact (AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr (R := R)) _)
    · refine AlgEquiv.trans (Ideal.quotientEquivAlgOfEq R ?_)
        ((MvPolynomial.quotientEquivQuotientMvPolynomial _).restrictScalars R).symm
      rw [Ideal.map_span, Set.image_singleton]
  case hmap => rfl
  · -- identify the transported outer ideal with the target relation
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton,
      dehomogenizeAux_map_polynomial]
    rfl

end WeierstrassCurve.Projective
