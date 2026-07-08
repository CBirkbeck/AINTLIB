import ModularCurves.EllipticCurve.AdditionChartHom

/-!
# Cross-index chart compatibility (T-W7.0c-c5β, c4.2 — the last crux)

The one statement standing between β4(b) and the glued `addOnY` / `addOnZ`.

β4(b) (`AdditionChartGlue.lean`) showed the *two laws* agree wherever both are regular — and
`isUnit_of_minor` showed they are then regular at the SAME index, so no cross-index comparison
between the laws is needed. What remains is cross-index compatibility for a SINGLE triple: on
`D(t k) ⊓ D(t l)` the chart morphisms built at index `k` and at index `l` land in *different*
chart rings (`chartAway W k` vs `chartAway W l`), so the ratio argument of β4(b) does not apply.
Geometrically this is nothing but the statement that a projective triple defines a morphism to
`Proj` — the original plan's `toProjOfBihomTriple`.

## Route (recorded; mathlib gap identified)

Mathlib supplies the chart-compatibility square
`AlgebraicGeometry.Proj.SpecMap_awayMap_awayι` (ProjectiveSpectrum/Basic.lean:248):

  `Spec.map (awayMap 𝒜 g_deg hx) ≫ awayι 𝒜 f = awayι 𝒜 (f * g)`.

So both sides of the goal factor through `awayι` at `X k * X l` once the two chart morphisms are
shown to come from a COMMON ring map `Away 𝒜 (X k * X l) → S`; the `X l * X k` versus `X k * X l`
mismatch is the repo's `ForMathlib/AwayCongr.lean` (`awayCongr`).

The common map exists because `D₊(X k) ⊓ D₊(X l)` is the basic open of `D₊(X k)` at the function
`X l / X k`, whose image `t l * u` is a unit in `S`; i.e. `Away 𝒜 (X k * X l)` should be the
localization of `Away 𝒜 (X k)` at that element, and the map is `IsLocalization.Away.lift`.

**Mathlib HAS this** (an earlier note in this file claimed a gap; that claim was wrong and is
retracted): `HomogeneousLocalization.Away.isLocalization_mul` (HomogeneousLocalization.lean:883)
states that, along `awayMap`, `Away 𝒜 (f * g)` IS the localization of `Away 𝒜 f` at
`Away.isLocalizationElem hf hg` (`= g / f` in degree 1). The repo's `chartCoordEquiv_mk_X`
(WeierstrassModel.lean:791) already identifies that element with the chart variable `X l`.

So the assembly is: the chart morphism sends `isLocalizationElem` to `t l * u`
(`chartAwayHomOfTriple_isLocalizationElem`), a unit when the triple is regular at both indices
(`isUnit_chartAwayHomOfTriple_isLocalizationElem`); `IsLocalization.Away.lift` then produces the
common map `ψ : Away 𝒜 (X k * X l) → S` with `ψ ∘ awayMap = hom_k` by `IsLocalization.lift_comp`,
and the same on the `l` side; `Proj.SpecMap_awayMap_awayι` pushes both composites through `awayι`
at `X k * X l`, with `awayCongr` absorbing `X l * X k = X k * X l`.
-/

open MvPolynomial ModularCurves AlgebraicGeometry CategoryTheory

namespace WeierstrassCurve.Projective

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
variable {S : Type} [CommRing S] [Algebra R S]

/-- The chart morphism of a triple, evaluated at the transition element `X l / X k` of
`Away.isLocalization_mul`, is the ratio `t l / t k`. This is the value that must be a unit for
`IsLocalization.Away.lift` to produce the common map on `D₊(X k) ⊓ D₊(X l)`. -/
lemma chartAwayHomOfTriple_isLocalizationElem (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S) (u : S)
    (hu : t k * u = 1) (ht : (W.map (algebraMap R S)).toProjective.Equation t) :
    chartAwayHomOfTriple W k t u hu ht
        (HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W l)) =
      t l * u := by
  have hsymm : (chartCoordAlgEquiv W k).symm
      (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W l)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (⟨l, hkl⟩ : {m : Fin 3 // m ≠ k})) := by
    apply (chartCoordAlgEquiv W k).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (chartCoordEquiv_mk_X W k ⟨l, hkl⟩).symm
  show chartHomOfTriple W k t u hu ht ((chartCoordAlgEquiv W k).symm _) = _
  rw [hsymm, chartHomOfTriple_coord]

/-- The transition element's image is a unit whenever the triple is regular at both indices —
the hypothesis `IsLocalization.Away.lift` consumes. -/
lemma isUnit_chartAwayHomOfTriple_isLocalizationElem (k l : Fin 3) (hkl : l ≠ k)
    (t : Fin 3 → S) (u v : S) (hu : t k * u = 1) (hv : t l * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t) :
    IsUnit (chartAwayHomOfTriple W k t u hu ht
      (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W l))) := by
  rw [chartAwayHomOfTriple_isLocalizationElem W k l hkl t u hu ht]
  exact (IsUnit.of_mul_eq_one _ hv).mul (IsUnit.of_mul_eq_one_right _ hu)

/-- **(c4.2, the last crux of c5β)** A projective triple on the curve, regular at two indices,
defines the same morphism to the model through either chart. Equivalently: the triple defines a
morphism to `Proj`, independent of the chart used to read it off.

Route (mathlib HAS the localization statement — see the module docstring):
`HomogeneousLocalization.Away.isLocalization_mul` presents `Away 𝒜 (X k * X l)` as the
localization of `Away 𝒜 (X k)` at `Away.isLocalizationElem`, whose image under the chart morphism
is the unit `t l * u` (the two lemmas above). `IsLocalization.Away.lift` then produces the common
map `ψ`, and `Proj.SpecMap_awayMap_awayι` pushes both sides through `awayι` at `X k * X l`
(`awayCongr` for the `X l * X k` mismatch). Sub-ticket: `T-W7.0c-c5β-projglue`. -/
theorem chartι_comp_specMap_chartAwayHom_eq (k l : Fin 3) (t : Fin 3 → S) (u v : S)
    (hu : t k * u = 1) (hv : t l * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t) :
    Spec.map (CommRingCat.ofHom (chartAwayHomOfTriple W k t u hu ht).toRingHom) ≫ chartι W k =
      Spec.map (CommRingCat.ofHom (chartAwayHomOfTriple W l t v hv ht).toRingHom) ≫
        chartι W l := by
  sorry

end WeierstrassCurve.Projective
