/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
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

open MvPolynomial ModularCurves HomogeneousIdeal HomogeneousLocalization
open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.Projective

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {S : Type u} [CommRing S] [Algebra R S]

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

open HomogeneousLocalization in
/-- The `k`-side factorization: the chart morphism of a triple factors through the overlap chart
`Away 𝒜 (X k * X l)`, via `IsLocalization.Away.lift` on the presentation supplied by
`Away.isLocalization_mul`. -/
noncomputable def projGlueLift (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S) (u v : S)
    (hu : t k * u = 1) (hv : t l * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (x : projCoordRing W)
    (hx : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X k) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X l)) :
    letI : Algebra (chartAway W k) (Away (quotientGrading (projIdeal W)) x) :=
      (awayMap (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W l) hx).toAlgebra
    Away (quotientGrading (projIdeal W)) x →+* S := by
  letI : Algebra (chartAway W k) (Away (quotientGrading (projIdeal W)) x) :=
    (awayMap (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W l) hx).toAlgebra
  haveI := Away.isLocalization_mul (𝒜 := quotientGrading (projIdeal W))
    (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W l)
    hx one_ne_zero
  exact IsLocalization.Away.lift
    (Away.isLocalizationElem (mk_X_mem_quotientGrading_one W k)
      (mk_X_mem_quotientGrading_one W l))
    (g := (chartAwayHomOfTriple W k t u hu ht).toRingHom)
    (isUnit_chartAwayHomOfTriple_isLocalizationElem W k l hkl t u v hu hv ht)

open HomogeneousLocalization in
/-- **The lift factors the chart morphism.** `ψ ∘ awayMap = hom_k`, the defining property of the
`IsLocalization.Away.lift` used to build `projGlueLift`: composing the overlap-chart lift with the
transition map `awayMap` back to chart `k` recovers the chart morphism `chartAwayHomOfTriple` of the
triple. This is `IsLocalization.Away.lift_comp` on the presentation supplied by
`Away.isLocalization_mul`, packaged once and shared by both `specMap_projGlueLift_awayι` and
`projGlueLift_eq`. -/
lemma projGlueLift_comp_awayMap (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S) (u v : S)
    (hu : t k * u = 1) (hv : t l * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (x : projCoordRing W)
    (hx : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X k) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X l)) :
    (projGlueLift W k l hkl t u v hu hv ht x hx).comp
        (awayMap (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W l) hx) =
      (chartAwayHomOfTriple W k t u hu ht).toRingHom := by
  letI : Algebra (chartAway W k) (Away (quotientGrading (projIdeal W)) x) :=
    (awayMap (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W l) hx).toAlgebra
  haveI := Away.isLocalization_mul (𝒜 := quotientGrading (projIdeal W))
    (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W l) hx one_ne_zero
  exact IsLocalization.Away.lift_comp _ _

open HomogeneousLocalization in
/-- **The `k`-side factorization.** `ψ ∘ awayMap = hom_k` (`IsLocalization.Away.lift_comp`), so the
`k`-chart composite equals `Spec ψ` followed by the overlap chart `awayι` at `X k * X l`. -/
lemma specMap_projGlueLift_awayι (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S) (u v : S)
    (hu : t k * u = 1) (hv : t l * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (x : projCoordRing W)
    (hx : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X k) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X l))
    (hxdeg : x ∈ quotientGrading (projIdeal W) 2) :
    Spec.map (CommRingCat.ofHom (projGlueLift W k l hkl t u v hu hv ht x hx)) ≫
        Proj.awayι (quotientGrading (projIdeal W)) x hxdeg (by omega) =
      Spec.map (CommRingCat.ofHom (chartAwayHomOfTriple W k t u hu ht).toRingHom) ≫
        chartι W k := by
  letI : Algebra (chartAway W k) (Away (quotientGrading (projIdeal W)) x) :=
    (awayMap (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W l) hx).toAlgebra
  haveI := Away.isLocalization_mul (𝒜 := quotientGrading (projIdeal W))
    (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W l)
    hx one_ne_zero
  have hcomp := projGlueLift_comp_awayMap W k l hkl t u v hu hv ht x hx
  have hsq := Proj.SpecMap_awayMap_awayι (𝒜 := quotientGrading (projIdeal W))
    (g_deg := mk_X_mem_quotientGrading_one W l) (hx := hx)
    (f_deg := mk_X_mem_quotientGrading_one W k) (hm := one_pos) (m' := 1)
  rw [chartι, ← hsq, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]

open HomogeneousLocalization in
/-- **(final sub-leaf)** The chart morphism of a triple, on an `Away.mk` element: the fraction
`b / (X k)^n` (with `b` homogeneous of degree `n`) is sent to `b(t) * u^n`, where `b(t)` is the
evaluation of `b` at the triple. This is the computation both `projGlueLift_eq` and any future
`toProjOfTriple` need; it is the ring-level content of "the chart morphism is evaluation at `t`,
normalized by the invertible coordinate".

Sub-ticket `T-W7.0c-c5β-projglue`, leaf 1. Route: `chartCoordEquiv_mk` (WeierstrassModel.lean:574)
computes `chartCoordEquiv` on `Ideal.Quotient.mk p` as `Away.map … (homogenizeAt R k p)`; take
`p := dehomogenizeAux R k b` and use `aeval_dehomogenizeAux_of_apply_eq_one` (AdditionChartHom) to
identify the evaluation. -/
lemma chartAwayHomOfTriple_awayMk (k : Fin 3) (t : Fin 3 → S) (u : S) (hu : t k * u = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t) (n : ℕ)
    (b : MvPolynomial (Fin 3) R) (hb : b ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R n) :
    chartAwayHomOfTriple W k t u hu ht
        (Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W k) n
          ((quotientGradingHom (projIdeal W)) b)
          (by simp only [smul_eq_mul, mul_one]; exact mk_mem_quotientGrading (projIdeal W) hb)) =
      MvPolynomial.aeval t b * u ^ n := by
  have hmem : b ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R (n • 1) := by simpa using hb
  have hsymm : (chartCoordAlgEquiv W k).symm
      (Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W k) n
        ((quotientGradingHom (projIdeal W)) b)
        (by simp only [smul_eq_mul, mul_one]; exact mk_mem_quotientGrading (projIdeal W) hb)) =
      Ideal.Quotient.mk _ (MvPolynomial.dehomogenizeAux R k b) := by
    apply (chartCoordAlgEquiv W k).injective
    rw [AlgEquiv.apply_symm_apply]
    symm
    show chartCoordEquiv W k (Ideal.Quotient.mk _ (MvPolynomial.dehomogenizeAux R k b)) = _
    rw [chartCoordEquiv_mk, MvPolynomial.homogenizeAt_dehomogenizeAux R k hmem, Away.map_mk]
  show chartHomOfTriple W k t u hu ht ((chartCoordAlgEquiv W k).symm _) = _
  rw [hsymm, chartHomOfTriple_mk]
  have hw : (fun m : Fin 3 => u * t m) k = 1 := by
    show u * t k = 1
    rw [mul_comm]
    exact hu
  have hstep := aeval_dehomogenizeAux_of_apply_eq_one (S := S) k (fun m : Fin 3 => u * t m) hw b
  have hscale := ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hb).aeval_mul_left (S := S) t u
  have hfun : (fun m : {m : Fin 3 // m ≠ k} => t (m : Fin 3) * u) =
      (fun m : {m : Fin 3 // m ≠ k} => (fun p : Fin 3 => u * t p) (m : Fin 3)) :=
    funext fun m => mul_comm _ _
  rw [hfun, hstep, hscale, mul_comm]

open HomogeneousLocalization in
/-- **The change-of-chart ring identity in the overlap `Away 𝒜 (X k * X l)`.** The image of the
chart-`k` fraction `c / (X k) ^ n` under the transition map to the overlap, times the `n`-th power of
the transition element `X l / X k`, equals the image of the chart-`l` fraction `c / (X l) ^ n` under
the transition map from the other side. Purely a graded-localization computation
(`HomogeneousLocalization.val_injective` reducing to `Localization.mk` equality, then `ring`); it is
the ring-level content behind the agreement of the two chart lifts in `projGlueLift_eq`. -/
lemma awayMap_mk_mul_awayMap_isLocalizationElem_pow (k l : Fin 3) (x : projCoordRing W)
    (hx : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X k) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X l))
    (hx' : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X l) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X k))
    (n : ℕ) (c : projCoordRing W) (hc : c ∈ quotientGrading (projIdeal W) (n • 1)) :
    (awayMap (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W l) hx)
          (Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W k) n c hc) *
        ((awayMap (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W k) hx')
          (Away.isLocalizationElem (mk_X_mem_quotientGrading_one W l)
            (mk_X_mem_quotientGrading_one W k))) ^ n =
      (awayMap (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W k) hx')
        (Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W l) n c hc) := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, val_pow, awayMap_mk, awayMap_mk, awayMap_mk,
    Away.val_mk, Away.val_mk, Away.val_mk, Localization.mk_pow, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  subst hx
  push_cast
  ring

open HomogeneousLocalization in
/-- **The last ring-level step.** The two lifts — built from the `k`-chart and the `l`-chart of the
same triple — coincide as ring maps out of the overlap chart `Away 𝒜 (X k * X l)`.

By `IsLocalization.lift_unique` (against the `k`-side algebra structure) this is equivalent to
`ψ_l ∘ awayMap_k = hom_k`, i.e. to computing `chartAwayHomOfTriple` on `Away.mk` elements: both
sides send `b / (X k)^n` to `b(t) * u^n`. Sub-ticket `T-W7.0c-c5β-projglue`, final leaf. -/
lemma projGlueLift_eq (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S) (u v : S)
    (hu : t k * u = 1) (hv : t l * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (x : projCoordRing W)
    (hx : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X k) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X l))
    (hx' : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X l) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X k)) :
    projGlueLift W k l hkl t u v hu hv ht x hx =
      projGlueLift W l k (Ne.symm hkl) t v u hv hu ht x hx' := by
  letI : Algebra (chartAway W k) (Away (quotientGrading (projIdeal W)) x) :=
    (awayMap (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W l) hx).toAlgebra
  haveI := Away.isLocalization_mul (𝒜 := quotientGrading (projIdeal W))
    (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W l) hx one_ne_zero
  refine IsLocalization.lift_unique _ fun a => ?_
  -- write `a = c / (X k)^n` with `c` the class of a degree-`n` homogeneous `b`
  obtain ⟨n, c, hc, rfl⟩ := Away.mk_surjective (quotientGrading (projIdeal W))
    (mk_X_mem_quotientGrading_one W k) a
  obtain ⟨b, hb, hbc⟩ := Submodule.mem_map.mp hc
  have hbc' : (quotientGradingHom (projIdeal W)) b = c := hbc
  -- the ring identity in `Away 𝒜 x` : (c / X k ^ n) * (X k ^ 2 / x) ^ n = c / X l ^ n
  have hid := awayMap_mk_mul_awayMap_isLocalizationElem_pow W k l x hx hx' n c hc
  letI : Algebra (chartAway W l) (Away (quotientGrading (projIdeal W)) x) :=
    (awayMap (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W k) hx').toAlgebra
  haveI := Away.isLocalization_mul (𝒜 := quotientGrading (projIdeal W))
    (mk_X_mem_quotientGrading_one W l) (mk_X_mem_quotientGrading_one W k) hx' one_ne_zero
  have hb' : b ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R n := by simpa using hb
  have hinv : (t k * v) * (u * t l) = 1 := by
    have : (t k * v) * (u * t l) = (t k * u) * (t l * v) := by ring
    rw [this, hu, hv, one_mul]
  -- apply ψ_l to the ring identity
  have hpsi := congrArg (projGlueLift W l k (Ne.symm hkl) t v u hv hu ht x hx') hid
  rw [map_mul, map_pow] at hpsi
  have hliftl : ∀ z, (projGlueLift W l k (Ne.symm hkl) t v u hv hu ht x hx')
      ((awayMap (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W k) hx') z) =
      chartAwayHomOfTriple W l t v hv ht z := fun z =>
    RingHom.congr_fun (projGlueLift_comp_awayMap W l k (Ne.symm hkl) t v u hv hu ht x hx') z
  have hvalmk : chartAwayHomOfTriple W l t v hv ht
      (Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W l) n c hc) =
      MvPolynomial.aeval t b * v ^ n :=
    hbc' ▸ chartAwayHomOfTriple_awayMk W l t v hv ht n b hb'
  rw [hliftl, hliftl, hvalmk,
    chartAwayHomOfTriple_isLocalizationElem W l k (Ne.symm hkl) t v hv ht] at hpsi
  rw [RingHom.algebraMap_toAlgebra]
  have hvalk : chartAwayHomOfTriple W k t u hu ht
      (Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W k) n c hc) =
      MvPolynomial.aeval t b * u ^ n :=
    hbc' ▸ chartAwayHomOfTriple_awayMk W k t u hu ht n b hb'
  show _ = chartAwayHomOfTriple W k t u hu ht _
  rw [hvalk]
  have h1 : _ * (u * t l) ^ n = _ * (u * t l) ^ n :=
    congrArg (fun z : S => z * (u * t l) ^ n) hpsi
  rw [mul_assoc, ← mul_pow, hinv, one_pow, mul_one] at h1
  rw [h1]
  have h2 : MvPolynomial.aeval t b * v ^ n * (u * t l) ^ n =
      MvPolynomial.aeval t b * u ^ n * (t l * v) ^ n := by rw [mul_pow]; ring
  rw [h2, hv, one_pow, mul_one]

open HomogeneousLocalization in
/-- **(c4.2, the last crux of c5β)** A projective triple on the curve, regular at two indices,
defines the same morphism to the model through either chart. Equivalently: the triple defines a
morphism to `Proj`, independent of the chart used to read it off.

Both chart composites factor through the overlap chart `awayι` at `X k * X l`
(`specMap_projGlueLift_awayι`, proven), so the statement reduces to the equality of the two lifts
(`projGlueLift_eq`). -/
theorem chartι_comp_specMap_chartAwayHom_eq (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S) (u v : S)
    (hu : t k * u = 1) (hv : t l * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t) :
    Spec.map (CommRingCat.ofHom (chartAwayHomOfTriple W k t u hu ht).toRingHom) ≫ chartι W k =
      Spec.map (CommRingCat.ofHom (chartAwayHomOfTriple W l t v hv ht).toRingHom) ≫
        chartι W l := by
  set x : projCoordRing W := (quotientGradingHom (projIdeal W)) (MvPolynomial.X k) *
    (quotientGradingHom (projIdeal W)) (MvPolynomial.X l) with hxdef
  have hxdeg : x ∈ quotientGrading (projIdeal W) 2 :=
    SetLike.mul_mem_graded (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W l)
  have hx' : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X l) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X k) := by
    rw [hxdef, mul_comm]
  rw [← specMap_projGlueLift_awayι W k l hkl t u v hu hv ht x hxdef hxdeg,
    ← specMap_projGlueLift_awayι W l k (Ne.symm hkl) t v u hv hu ht x hx' hxdeg,
    projGlueLift_eq W k l hkl t u v hu hv ht x hxdef hx']

end WeierstrassCurve.Projective
