/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.AdditionChartSpec
import ModularCurves.ForMathlib.HomogeneousEval

/-!
# A projective triple on the curve gives a chart morphism (T-W7.0c-c5β, β3 ring core)

The universal property behind `addOnZ` / `addOnY`. Let `t : Fin 3 → S` be a triple in an
`R`-algebra `S` with

* `t k` invertible (witness `u`, `t k * u = 1`), and
* `t` on the curve: `(W.map (algebraMap R S)).Equation t`.

Then the ratios `t m / t k` solve the dehomogenised cubic of chart `k`, so they define an
`R`-algebra map `affineChartRing W k →ₐ[R] S` (`chartHomOfTriple`) — equivalently, by
`chartCoordAlgEquiv`, a map out of the chart ring of the model, i.e. a morphism
`Spec S ⟶ chart k ↪ projModel W`.

Applied with `S := Localization.Away (lawTwoTriple W i j k)` over `biChartRing W i j`, whose
on-curve hypothesis is `equation_lawTwoTriple_of_isDomain`, this is exactly the `k`-th piece of
`addOnY` on the `(i,j)` chart-product (β1's `chartPieceIso` turns `Spec (biChartRing W i j)`
into that chart-product open). Same for `lawOneTriple` and `addOnZ`.

The two computational inputs:

* `aeval_dehomogenizeAux_of_apply_eq_one` — evaluating a dehomogenised polynomial at a vector
  whose `k`-th entry is `1` is the same as evaluating the original polynomial there;
* `MvPolynomial.IsHomogeneous.eval₂_mul_left` (ForMathlib) — rescaling a homogeneous polynomial's
  argument multiplies the value by `c ^ deg`.

Together: the rescaled vector `(t · * u)` has `k`-th entry `1`, so evaluating the dehomogenised
cubic there is evaluating the cubic at `(t · * u)`, which is `u ^ 3 * (curve equation at t) = 0`.
-/

open MvPolynomial ModularCurves

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

section Dehomogenize

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Evaluating the dehomogenisation of `p` at `k` on a vector whose `k`-th entry is `1` agrees
with evaluating `p` itself on that vector. -/
lemma aeval_dehomogenizeAux_of_apply_eq_one (k : Fin 3) (w : Fin 3 → S) (hw : w k = 1)
    (p : MvPolynomial (Fin 3) R) :
    aeval (fun m : {m : Fin 3 // m ≠ k} => w m) (dehomogenizeAux R k p) = aeval w p := by
  have h : (aeval (fun m : {m : Fin 3 // m ≠ k} => w m) :
        MvPolynomial {m : Fin 3 // m ≠ k} R →ₐ[R] S).toRingHom.comp (dehomogenizeAux R k) =
      (aeval w : MvPolynomial (Fin 3) R →ₐ[R] S).toRingHom := by
    refine ringHom_ext (fun r => ?_) (fun n => ?_)
    · simp
    · by_cases hn : n = k
      · subst hn
        simp [dehomogenizeAux_X_self, hw]
      · simp [dehomogenizeAux_X_ne _ _ hn]
  exact RingHom.congr_fun h p

/-- **(β3, the key identity)** A projective triple on the curve, with an invertible `k`-th
coordinate, solves the dehomogenised cubic of chart `k` after dividing by that coordinate. -/
theorem aeval_dehomogenizeAux_eq_zero (k : Fin 3) (t : Fin 3 → S) (u : S) (hu : t k * u = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t) :
    aeval (fun m : {m : Fin 3 // m ≠ k} => t m * u)
      (dehomogenizeAux R k W.toProjective.polynomial) = 0 := by
  have hcurve : aeval t W.toProjective.polynomial = 0 := by
    rw [Equation, map_polynomial, eval_map] at ht
    exact ht
  have hw : (fun n : Fin 3 => u * t n) k = 1 := by
    show u * t k = 1
    rw [mul_comm]
    exact hu
  have hstep := aeval_dehomogenizeAux_of_apply_eq_one (S := S) k (fun n : Fin 3 => u * t n) hw
    W.toProjective.polynomial
  have hscale := (projective_polynomial_isHomogeneous W).aeval_mul_left (S := S) t u
  have hfun : (fun m : {m : Fin 3 // m ≠ k} => t (m : Fin 3) * u) =
      (fun m : {m : Fin 3 // m ≠ k} => (fun n : Fin 3 => u * t n) (m : Fin 3)) :=
    funext fun m => mul_comm _ _
  rw [hfun, hstep, hscale, hcurve, mul_zero]

/-- **(β3)** The chart morphism attached to an on-curve triple with invertible `k`-th coordinate:
the `R`-algebra map `affineChartRing W k →ₐ[R] S` sending the chart coordinate `X m / X k` to
`t m * u`. Compose with `chartCoordAlgEquiv` (β1) to land in the model's chart ring. -/
noncomputable def chartHomOfTriple (k : Fin 3) (t : Fin 3 → S) (u : S) (hu : t k * u = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t) :
    affineChartRing W k →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aeval (fun m : {m : Fin 3 // m ≠ k} => t m * u)) <| by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, aeval_dehomogenizeAux_eq_zero W k t u hu ht, zero_mul]

@[simp]
lemma chartHomOfTriple_mk (k : Fin 3) (t : Fin 3 → S) (u : S) (hu : t k * u = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (p : MvPolynomial {m : Fin 3 // m ≠ k} R) :
    chartHomOfTriple W k t u hu ht (Ideal.Quotient.mk _ p) =
      aeval (fun m : {m : Fin 3 // m ≠ k} => t m * u) p :=
  rfl

/-- The chart coordinates go to the ratios, as designed. -/
@[simp]
lemma chartHomOfTriple_coord (k : Fin 3) (t : Fin 3 → S) (u : S) (hu : t k * u = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t) (m : {m : Fin 3 // m ≠ k}) :
    chartHomOfTriple W k t u hu ht (Ideal.Quotient.mk _ (X m)) = t m * u := by
  rw [chartHomOfTriple_mk, aeval_X]

/-- The same morphism, landing in the model's `Away` chart ring presentation (β1's
`chartCoordAlgEquiv`), which is what `Proj.awayι` consumes. -/
noncomputable def chartAwayHomOfTriple (k : Fin 3) (t : Fin 3 → S) (u : S) (hu : t k * u = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t) :
    chartAway W k →ₐ[R] S :=
  (chartHomOfTriple W k t u hu ht).comp (chartCoordAlgEquiv W k).symm.toAlgHom

/-- **(naturality of the chart hom in the target ring)** The chart morphism of a triple commutes
with base change of the target: pushing the triple along `φ : S →+* S'` and taking the chart hom
is the same as taking the chart hom and post-composing with `φ`.

This is what identifies the restriction of a piece morphism to a smaller basic open with the chart
hom of the same triple over the smaller localization (c4.2c). -/
lemma chartHomOfTriple_naturality {S' : Type*} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S')
    (k : Fin 3) (t : Fin 3 → S) (u : S) (hu : t k * u = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (hu' : φ (t k) * φ u = 1)
    (ht' : (W.map (algebraMap R S')).toProjective.Equation (fun m => φ (t m))) :
    (chartHomOfTriple W k (fun m => φ (t m)) (φ u) hu' ht' : affineChartRing W k →ₐ[R] S') =
      (φ.comp (chartHomOfTriple W k t u hu ht)) := by
  refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun m => ?_)
  show chartHomOfTriple W k (fun m => φ (t m)) (φ u) hu' ht' (Ideal.Quotient.mk _ (X m)) =
    φ (chartHomOfTriple W k t u hu ht (Ideal.Quotient.mk _ (X m)))
  rw [chartHomOfTriple_coord, chartHomOfTriple_coord, map_mul]

end Dehomogenize

end WeierstrassCurve.Projective
