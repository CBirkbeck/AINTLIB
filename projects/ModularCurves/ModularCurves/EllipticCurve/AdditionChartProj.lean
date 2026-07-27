/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionChartHom

/-!
# Compatibility of projective charts

This file proves that a projective triple regular in two coordinates defines the same morphism
through either affine chart of a Weierstrass curve.

## Main definitions

* `projGlueLift`: the lift of a chart map to the overlap of two projective charts.

## Main results

* `chartι_comp_specMap_chartAwayHom_eq`: a projective triple gives the same morphism through either
  chart on which it is regular.
-/

open MvPolynomial ModularCurves HomogeneousIdeal HomogeneousLocalization
open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.Projective

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {S : Type u} [CommRing S] [Algebra R S]

/-- The chart map sends the transition element `X l / X k` to `t l / t k`. -/
lemma chartAwayHomOfTriple_isLocalizationElem (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S)
    (u : S) (hu : t k * u = 1) (ht : (W.map (algebraMap R S)).toProjective.Equation t) :
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

/-- The transition element maps to a unit when both coordinates are invertible. -/
lemma isUnit_chartAwayHomOfTriple_isLocalizationElem (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S)
    (u v : S) (hu : t k * u = 1) (hv : t l * v = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t) :
    IsUnit (chartAwayHomOfTriple W k t u hu ht
      (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W l))) := by
  rw [chartAwayHomOfTriple_isLocalizationElem W k l hkl t u hu ht]
  exact (IsUnit.of_mul_eq_one _ hv).mul (IsUnit.of_mul_eq_one_right _ hu)

open HomogeneousLocalization in
/-- The lift of a chart map to the overlap of the `k`-th and `l`-th projective charts. -/
noncomputable def projGlueLift (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S) (u v : S)
    (hu : t k * u = 1) (hv : t l * v = 1) (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (x : projCoordRing W) (hx : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X k) *
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
/-- Composing `projGlueLift` with the transition map recovers the original chart map. -/
lemma projGlueLift_comp_awayMap (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S) (u v : S)
    (hu : t k * u = 1) (hv : t l * v = 1) (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (x : projCoordRing W) (hx : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X k) *
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
/-- The map through the `k`-th chart factors through the overlap chart. -/
lemma specMap_projGlueLift_awayι (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S) (u v : S)
    (hu : t k * u = 1) (hv : t l * v = 1) (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (x : projCoordRing W) (hx : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X k) *
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
/-- The chart map sends the homogeneous fraction `b / (X k) ^ n` to `b(t) * u ^ n`. -/
lemma chartAwayHomOfTriple_awayMk (k : Fin 3) (t : Fin 3 → S) (u : S) (hu : t k * u = 1)
    (ht : (W.map (algebraMap R S)).toProjective.Equation t) (n : ℕ)
    (b : MvPolynomial (Fin 3) R) (hb : b ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R n) :
    chartAwayHomOfTriple W k t u hu ht
        (Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W k) n
          ((quotientGradingHom (projIdeal W)) b)
          (by
            simp only [smul_eq_mul, mul_one]
            exact mk_mem_quotientGrading (projIdeal W) hb)) =
      MvPolynomial.aeval t b * u ^ n := by
  have hmem : b ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R (n • 1) := by simpa using hb
  have hsymm : (chartCoordAlgEquiv W k).symm
      (Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W k) n
        ((quotientGradingHom (projIdeal W)) b)
        (by
          simp only [smul_eq_mul, mul_one]
          exact mk_mem_quotientGrading (projIdeal W) hb)) =
      Ideal.Quotient.mk _ (MvPolynomial.dehomogenizeAux R k b) := by
    apply (chartCoordAlgEquiv W k).injective
    rw [AlgEquiv.apply_symm_apply]
    symm
    show chartCoordEquiv W k (Ideal.Quotient.mk _ (MvPolynomial.dehomogenizeAux R k b)) = _
    rw [chartCoordEquiv_mk, MvPolynomial.homogenizeAt_dehomogenizeAux R k hmem, Away.map_mk]
  show chartHomOfTriple W k t u hu ht ((chartCoordAlgEquiv W k).symm _) = _
  rw [hsymm, chartHomOfTriple_mk]
  have hw : (fun m : Fin 3 => u * t m) k = 1 := by simpa [mul_comm] using hu
  have hstep := aeval_dehomogenizeAux_of_apply_eq_one (S := S) k (fun m : Fin 3 => u * t m) hw b
  have hscale := ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hb).aeval_mul_left (S := S) t u
  have hfun : (fun m : {m : Fin 3 // m ≠ k} => t (m : Fin 3) * u) =
      (fun m : {m : Fin 3 // m ≠ k} => (fun p : Fin 3 => u * t p) (m : Fin 3)) :=
    funext fun m => mul_comm _ _
  rw [hfun, hstep, hscale, mul_comm]

open HomogeneousLocalization in
/-- The chart transition maps satisfy the homogeneous fraction change-of-chart identity. -/
lemma awayMap_mk_mul_awayMap_isLocalizationElem_pow (k l : Fin 3) (x : projCoordRing W)
    (hx : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X k) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X l))
    (hx' : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X l) *
      (quotientGradingHom (projIdeal W)) (MvPolynomial.X k)) (n : ℕ) (c : projCoordRing W)
    (hc : c ∈ quotientGrading (projIdeal W) (n • 1)) :
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
/-- The overlap lifts constructed from two regular coordinates are equal. -/
lemma projGlueLift_eq (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S) (u v : S) (hu : t k * u = 1)
    (hv : t l * v = 1) (ht : (W.map (algebraMap R S)).toProjective.Equation t)
    (x : projCoordRing W) (hx : x = (quotientGradingHom (projIdeal W)) (MvPolynomial.X k) *
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
  obtain ⟨n, c, hc, rfl⟩ := Away.mk_surjective (quotientGrading (projIdeal W))
    (mk_X_mem_quotientGrading_one W k) a
  obtain ⟨b, hb, hbc⟩ := Submodule.mem_map.mp hc
  have hbc' : (quotientGradingHom (projIdeal W)) b = c := hbc
  have hid := awayMap_mk_mul_awayMap_isLocalizationElem_pow W k l x hx hx' n c hc
  letI : Algebra (chartAway W l) (Away (quotientGrading (projIdeal W)) x) :=
    (awayMap (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W k) hx').toAlgebra
  haveI := Away.isLocalization_mul (𝒜 := quotientGrading (projIdeal W))
    (mk_X_mem_quotientGrading_one W l) (mk_X_mem_quotientGrading_one W k) hx' one_ne_zero
  have hb' : b ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R n := by simpa using hb
  have hinv : (t k * v) * (u * t l) = 1 := by
    have : (t k * v) * (u * t l) = (t k * u) * (t l * v) := by ring
    rw [this, hu, hv, one_mul]
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
      MvPolynomial.aeval t b * u ^ n * (t l * v) ^ n := by
    rw [mul_pow]
    ring
  rw [h2, hv, one_pow, mul_one]

open HomogeneousLocalization in
/-- A projective triple regular in two coordinates defines the same morphism through either
chart. -/
theorem chartι_comp_specMap_chartAwayHom_eq (k l : Fin 3) (hkl : l ≠ k) (t : Fin 3 → S)
    (u v : S) (hu : t k * u = 1) (hv : t l * v = 1)
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
