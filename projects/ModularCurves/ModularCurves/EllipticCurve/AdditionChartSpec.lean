import ModularCurves.EllipticCurve.AdditionChartTensor
import ModularCurves.EllipticCurve.WeierstrassModel

/-!
# `Spec` of the chart-product ring is the chart-product open (T-W7.0c-c5β, β1 scheme half)

The geometric half of β1. The `(i,j)` piece of the natural cover of `E ×_R E` is
`pullback (awayι i ≫ π) (awayι j ≫ π)`; we identify it with `Spec (biChartRing W i j)`:

1. `awayι_projModelπ` writes each leg as `Spec.map` of a ring map `R → chartAway`, whose source
   is the **degree-zero part** of the graded coordinate ring identified with `R`
   (`gradeZeroRingEquiv`). That composite is not a global `Algebra R` instance, so we install it
   as `chartAwayAlgebra` — after which `pullbackSpecIso` applies verbatim.
2. `chartCoordAlgEquiv` upgrades the repo's `chartCoordEquiv` (a bare `RingEquiv`) to an
   `R`-algebra equivalence; the required `commutes'` is exactly `chartCoordEquiv_mk_C`. β3
   consumes this too, so it is built once here.
3. `Algebra.TensorProduct.congr` + `biChartRingTensorEquiv` (β1's algebra half) then turn
   `Spec (chartAway i ⊗[R] chartAway j)` into `Spec (biChartRing W i j)`.

The upshot, `chartPieceIso`, is what lets the addition-law triples — which live in
`biChartRing` and are known to lie on the curve there (`equation_lawTwoTriple_of_isDomain`) —
be read as functions on an honest open subscheme of `E ×_R E`, which is what `addOnZ`/`addOnY`
need (β3).
-/

open MvPolynomial ModularCurves HomogeneousIdeal HomogeneousLocalization
open AlgebraicGeometry CategoryTheory Limits TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.Projective

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (i j : Fin 3)

/-- The chart ring of the projective model in its `Away` presentation. -/
noncomputable abbrev chartAway : Type :=
  HomogeneousLocalization.Away (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))

/-- The chart immersion `Spec (chartAway W i) ⟶ projModel W`. -/
noncomputable abbrev chartι : Spec (CommRingCat.of (chartAway W i)) ⟶ projModel W :=
  Proj.awayι (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i))
    (mk_X_mem_quotientGrading_one W i) one_pos

/-- **(obstacle 1)** The `R`-algebra structure on a chart ring: the structure morphism of the
model factors through the degree-zero part of the graded coordinate ring, which is `R`. This is
not a global instance, so it is installed here (and it is *the* structure used by
`awayι_projModelπ`). -/
noncomputable instance chartAwayAlgebra : Algebra R (chartAway W i) :=
  ((algebraMap (↥(quotientGrading (projIdeal W) 0)) (chartAway W i)).comp
    ((gradeZeroRingEquiv W : R ≃+* _) : R →+* _)).toAlgebra

lemma chartAway_algebraMap_apply (r : R) :
    algebraMap R (chartAway W i) r =
      (algebraMap (↥(quotientGrading (projIdeal W) 0)) (chartAway W i))
        ((gradeZeroRingEquiv W) r) :=
  rfl

/-- **(obstacle 2)** `chartCoordEquiv` upgraded to an `R`-algebra equivalence: the constants
match by `chartCoordEquiv_mk_C`. -/
noncomputable def chartCoordAlgEquiv : affineChartRing W i ≃ₐ[R] chartAway W i :=
  AlgEquiv.ofRingEquiv (f := chartCoordEquiv W i) fun r => by
    have hconst : (algebraMap R (affineChartRing W i)) r =
        Ideal.Quotient.mk (Ideal.span
          {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial}) (MvPolynomial.C r) := by
      simp [IsScalarTower.algebraMap_apply R (MvPolynomial {j : Fin 3 // j ≠ i} R)
        (affineChartRing W i), MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq]
    rw [hconst, chartCoordEquiv_mk_C, chartAway_algebraMap_apply]

/-- The structure morphism of the model, restricted to a chart, is `Spec` of the chart's
`R`-algebra structure map — the form `pullbackSpecIso` consumes. -/
lemma chartι_projModelπ :
    chartι W i ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom (algebraMap R (chartAway W i))) := by
  rw [awayι_projModelπ]

/-- The `(i,j)` chart-product piece of `E ×_R E`, as `Spec` of a tensor product. -/
noncomputable def chartPieceTensorIso :
    pullback (chartι W i ≫ projModelπ W) (chartι W j ≫ projModelπ W) ≅
      Spec (CommRingCat.of (chartAway W i ⊗[R] chartAway W j)) := by
  rw [chartι_projModelπ, chartι_projModelπ]
  exact pullbackSpecIso R (chartAway W i) (chartAway W j)

/-- The chart-product ring presents the tensor product of the two `Away` chart rings. -/
noncomputable def biChartRingAwayTensorEquiv :
    biChartRing W i j ≃ₐ[R] chartAway W i ⊗[R] chartAway W j :=
  (biChartRingTensorEquiv W i j).trans
    (Algebra.TensorProduct.congr (chartCoordAlgEquiv W i) (chartCoordAlgEquiv W j))

/-- **(β1)** The `(i,j)` chart-product piece of `E ×_R E` is `Spec` of the chart-product ring.

This is the identification that lets `lawOneTriple`/`lawTwoTriple` — elements of
`biChartRing W i j`, proven to satisfy the curve equation there (`equation_lawTwoTriple_of_isDomain`)
— be read as regular functions on an open subscheme of `E ×_R E`, which is what the `addOnZ` /
`addOnY` chart morphisms consume (β3). -/
noncomputable def chartPieceIso :
    pullback (chartι W i ≫ projModelπ W) (chartι W j ≫ projModelπ W) ≅
      Spec (CommRingCat.of (biChartRing W i j)) :=
  (chartPieceTensorIso W i j).trans
    (Scheme.Spec.mapIso
      ((biChartRingAwayTensorEquiv W i j).toRingEquiv.toCommRingCatIso).op)

/-- The pieces `chartPieceIso` identifies are an open cover of `E ×_R E`: they are the
left-right cover induced by the model's chart cover on each factor. -/
noncomputable def chartProductCover :
    (pullback (projModelπ W) (projModelπ W)).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (modelChartCover W).openCover
    (modelChartCover W).openCover (projModelπ W) (projModelπ W)

end WeierstrassCurve.Projective
