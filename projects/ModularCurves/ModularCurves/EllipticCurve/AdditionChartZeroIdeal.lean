/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.PoleFiltration
import ModularCurves.EllipticCurve.AdditionChartProj

/-!
# The zero ideal in the projective `Y`-chart

This file computes the two generators of the zero-section ideal under a projective chart map.
For the normalized pole-coordinate triple `[x * r, y, r ^ 3]`, with `x` and `y` invertible,
the image of the model ideal `(s, t)` is the principal ideal `(r)`.
-/

open MvPolynomial ModularCurves HomogeneousIdeal HomogeneousLocalization
open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.Projective

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {S : Type u} [CommRing S] [Algebra R S]

/-- The first coordinate on the `Y`-chart evaluates to `P 0 / P 1`. -/
lemma chartAwayHomOfTriple_chartYRoot
    (P : Fin 3 → S) (u : S) (hu : P 1 * u = 1)
    (hP : (W.map (algebraMap R S)).toProjective.Equation P) :
    chartAwayHomOfTriple W 1 P u hu hP
        ((chartYRingEquiv W).symm
          (AdjoinRoot.root (infChartCubic W))) =
      P 0 * u := by
  have hroot :
      (chartYRingEquiv W).symm
          (AdjoinRoot.root (infChartCubic W)) =
        HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W 1)
          (mk_X_mem_quotientGrading_one W 0) := by
    apply (chartYRingEquiv W).injective
    rw [RingEquiv.apply_symm_apply, chartYRingEquiv_sElem]
  rw [hroot]
  exact chartAwayHomOfTriple_isLocalizationElem W 1 0 (by decide)
    P u hu hP

/-- The second coordinate on the `Y`-chart evaluates to `P 2 / P 1`. -/
lemma chartAwayHomOfTriple_chartYTel
    (P : Fin 3 → S) (u : S) (hu : P 1 * u = 1)
    (hP : (W.map (algebraMap R S)).toProjective.Equation P) :
    chartAwayHomOfTriple W 1 P u hu hP
        ((chartYRingEquiv W).symm (infChartTElem W)) =
      P 2 * u := by
  have htel :
      (chartYRingEquiv W).symm (infChartTElem W) =
        HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W 1)
          (mk_X_mem_quotientGrading_one W 2) := by
    apply (chartYRingEquiv W).injective
    rw [RingEquiv.apply_symm_apply, chartYRingEquiv_isLocalizationElem]
  rw [htel]
  exact chartAwayHomOfTriple_isLocalizationElem W 1 2 (by decide)
    P u hu hP

/-- For a normalized triple `[x * r, P 1, r ^ 3]` in the `Y`-chart, with `x` invertible,
the image of the zero-section ideal `(s, t)` is the principal ideal `(r)`. -/
lemma chartAwayHomOfTriple_map_chartYZeroIdeal
    (P : Fin 3 → S) (u : S) (hu : P 1 * u = 1)
    (hP : (W.map (algebraMap R S)).toProjective.Equation P)
    (r x : S) (hP0 : P 0 = x * r) (hP2 : P 2 = r ^ 3)
    (hx : IsUnit x) :
    Ideal.map
        (chartAwayHomOfTriple W 1 P u hu hP).toRingHom
        (Ideal.span {
          (chartYRingEquiv W).symm
            (AdjoinRoot.root (infChartCubic W)),
          (chartYRingEquiv W).symm (infChartTElem W)}) =
      Ideal.span {r} := by
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change Ideal.span {
      chartAwayHomOfTriple W 1 P u hu hP
        ((chartYRingEquiv W).symm
          (AdjoinRoot.root (infChartCubic W))),
      chartAwayHomOfTriple W 1 P u hu hP
        ((chartYRingEquiv W).symm (infChartTElem W))} =
    Ideal.span {r}
  rw [chartAwayHomOfTriple_chartYRoot,
    chartAwayHomOfTriple_chartYTel, hP0, hP2]
  have hu' : IsUnit u := IsUnit.of_mul_eq_one_right _ hu
  have hxu : IsUnit (x * u) := hx.mul hu'
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro a (rfl | rfl)
    · change x * r * u ∈ Ideal.span {r}
      rw [show x * r * u = (x * u) * r by ring]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self r)
    · change r ^ 3 * u ∈ Ideal.span {r}
      rw [show r ^ 3 * u = (r ^ 2 * u) * r by ring]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self r)
  · let I : Ideal S := Ideal.span {x * r * u, r ^ 3 * u}
    change Ideal.span {r} ≤ I
    refine Ideal.span_le.mpr ?_
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hxu
    have hgen : x * r * u ∈ I := by
      change x * r * u ∈ Ideal.span {x * r * u, r ^ 3 * u}
      exact Ideal.subset_span (Set.mem_insert _ _)
    have hvr : v * (x * r * u) ∈ I :=
      Ideal.mul_mem_left _ _ hgen
    have hvr_eq : v * (x * r * u) = r := by
      calc
        v * (x * r * u) = (x * u) * v * r := by ring
        _ = r := by rw [hv, one_mul]
    exact (congrArg (fun q : S => q ∈ I) hvr_eq).mp hvr

end WeierstrassCurve.Projective
