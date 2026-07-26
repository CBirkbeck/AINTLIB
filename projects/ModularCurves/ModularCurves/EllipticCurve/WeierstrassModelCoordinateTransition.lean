/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionChartOverlap
import ModularCurves.EllipticCurve.WeierstrassModelCoordinates

/-!
# Coordinate transitions for projective Weierstrass models

A homogeneous coordinate morphism with a unit coordinate factors through the
corresponding affine chart. This identifies the `Proj.fromOfGlobalSections`
construction with the chart morphism obtained from coordinate ratios.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open WeierstrassCurve.Projective

namespace ModularCurves

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R]

/-- A homogeneous coordinate morphism with a unit coordinate is the morphism
defined by the corresponding affine-chart coordinate ratios. -/
theorem projModelFromOfGlobalSections_eq_chart
    {X : Scheme.{u}} (W : WeierstrassCurve R)
    [Algebra R Γ(X, (⊤ : X.Opens))]
    (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map (algebraMap R Γ(X, (⊤ : X.Opens)))).toProjective.Equation P)
    (i : Fin 3) (hi : IsUnit (P i)) :
    projModelFromOfGlobalSections W
        (algebraMap R Γ(X, (⊤ : X.Opens))) P hP i hi =
      X.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          (chartAwayHomOfTriple W i P
            (↑hi.unit⁻¹) hi.mul_val_inv hP).toRingHom) ≫
        chartι W i := by
  let q : projCoordRing W :=
    (quotientGradingHom (projIdeal W)) (MvPolynomial.X i)
  let D : (projModel W).Opens :=
    Proj.basicOpen (quotientGrading (projIdeal W)) q
  let φ : projCoordRing W →+* Γ(X, (⊤ : X.Opens)) :=
    projModelEval W (algebraMap R Γ(X, (⊤ : X.Opens))) P hP
  let E : X.Opens := X.basicOpen (φ q)
  let F : X ⟶ projModel W :=
    projModelFromOfGlobalSections W
      (algebraMap R Γ(X, (⊤ : X.Opens))) P hP i hi
  have hpre : F ⁻¹ᵁ D = E := by
    simpa only [F, D, E, q, φ, projModelFromOfGlobalSections] using
      Proj.fromOfGlobalSections_preimage_basicOpen
        (quotientGrading (projIdeal W))
        (projModelEval W
          (algebraMap R Γ(X, (⊤ : X.Opens))) P hP)
        (projModelEval_irrelevant_map_top_of_isUnit
          W (algebraMap R Γ(X, (⊤ : X.Opens))) P hP i hi)
        one_pos (mk_X_mem_quotientGrading_one W i)
  have hφq : φ q = P i := by
    exact projModelEval_X W
      (algebraMap R Γ(X, (⊤ : X.Opens))) P hP i
  have hφqUnit : IsUnit (φ q) := hφq.symm ▸ hi
  have htop : E = ⊤ := Scheme.basicOpen_of_isUnit X hφqUnit
  haveI : IsIso E.ι := by
    rw [htop, ← Scheme.topIso_hom]
    infer_instance
  let ψ : Localization.Away (φ q) →+* Γ(X, (⊤ : X.Opens)) :=
    IsLocalization.Away.lift (φ q) (g := RingHom.id _) hφqUnit
  have hψ : ψ.comp (algebraMap _ (Localization.Away (φ q))) =
      RingHom.id _ := by
    simpa only [ψ] using
      IsLocalization.Away.lift_comp
        (S := Localization.Away (φ q))
        (g := RingHom.id Γ(X, (⊤ : X.Opens)))
        (x := φ q) hφqUnit
  have hmap :
      Submonoid.powers q ≤ (Submonoid.powers (φ q)).comap φ := by
    rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
  let μ : Localization.Away q →+* Localization.Away (φ q) :=
    IsLocalization.map (Localization.Away (φ q)) φ hmap
  let χ : Localization.Away q →+* Γ(X, (⊤ : X.Opens)) :=
    Localization.awayLift φ q hφqUnit
  have hψμ : ψ.comp μ = χ := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers q)
    rw [RingHom.comp_assoc]
    simp only [μ, IsLocalization.map_comp]
    rw [← RingHom.comp_assoc, hψ, RingHom.id_comp]
    exact (IsLocalization.Away.lift_comp
      (S := Localization.Away q) (g := φ) (x := q) hφqUnit).symm
  have hqi : φ q * (↑hi.unit⁻¹ : Γ(X, (⊤ : X.Opens))) = 1 := by
    rw [hφq]
    exact hi.mul_val_inv
  have hring :
      ψ.comp (μ.comp
          (algebraMap (chartAway W i) (Localization.Away q))) =
        (chartAwayHomOfTriple W i P
          (↑hi.unit⁻¹) hi.mul_val_inv hP).toRingHom := by
    rw [← RingHom.comp_assoc, hψμ]
    apply RingHom.ext
    intro y
    obtain ⟨n, c, hc, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective
        (quotientGrading (projIdeal W))
        (mk_X_mem_quotientGrading_one W i) y
    obtain ⟨b, hb, hbc⟩ := Submodule.mem_map.mp hc
    have hb' : b ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R n := by
      simpa only [smul_eq_mul, mul_one] using hb
    have hbc' :
        (quotientGradingHom (projIdeal W)) b = c := hbc
    simp only [χ, RingHom.comp_apply]
    have hval :
        (algebraMap (chartAway W i) (Localization.Away q))
            (HomogeneousLocalization.Away.mk
              (quotientGrading (projIdeal W))
              (mk_X_mem_quotientGrading_one W i) n c hc) =
          Localization.mk c ⟨q ^ n, by exact ⟨n, rfl⟩⟩ := by
      change HomogeneousLocalization.val
        (HomogeneousLocalization.Away.mk
          (quotientGrading (projIdeal W))
          (mk_X_mem_quotientGrading_one W i) n c hc) = _
      exact HomogeneousLocalization.Away.val_mk
        (quotientGrading (projIdeal W)) n
        (mk_X_mem_quotientGrading_one W i) c hc
    rw [hval]
    rw [Localization.awayLift_mk φ q c
      (↑hi.unit⁻¹) hqi n]
    have hchart :
        (chartAwayHomOfTriple W i P
            (↑hi.unit⁻¹) hi.mul_val_inv hP).toRingHom
            (HomogeneousLocalization.Away.mk
              (quotientGrading (projIdeal W))
              (mk_X_mem_quotientGrading_one W i) n c hc) =
          MvPolynomial.aeval P b * (↑hi.unit⁻¹) ^ n :=
      hbc' ▸ chartAwayHomOfTriple_awayMk W i P
          (↑hi.unit⁻¹) hi.mul_val_inv hP n b hb'
    rw [hchart, ← hbc']
    simp only [φ, quotientGradingHom_apply, projModelEval_mk,
      MvPolynomial.aeval_def]
  have hbasic :
      (X.isoOfEq (X.toSpecΓ_preimage_basicOpen (φ q))).inv ≫
          X.toSpecΓ ∣_ PrimeSpectrum.basicOpen (φ q) ≫
          (basicOpenIsoSpecAway (φ q)).hom =
        E.ι ≫ X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) := by
    rw [← cancel_mono
      (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, (⊤ : X.Opens))
          (Localization.Away (φ q)))))]
    slice_lhs 3 4 => rw [basicOpenIsoSpecAway_hom_SpecMap]
    slice_lhs 2 3 =>
      rw [morphismRestrict_ι X.toSpecΓ
        (PrimeSpectrum.basicOpen (φ q) :
          (Spec (CommRingCat.of Γ(X, (⊤ : X.Opens)))).Opens)]
    slice_lhs 1 2 => rw [Scheme.isoOfEq_inv_ι]
    slice_rhs 3 4 =>
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
      simp only [CommRingCat.ofHom_id, Spec.map_id]
    rfl
  rw [show projModelFromOfGlobalSections W
      (algebraMap R Γ(X, (⊤ : X.Opens))) P hP i hi = F by rfl]
  rw [← cancel_epi E.ι]
  calc
    E.ι ≫ F =
        F.resLE D E hpre.ge ≫ D.ι := by
          exact (Scheme.Hom.resLE_comp_ι F hpre.ge).symm
    _ = Proj.toBasicOpenOfGlobalSections
          (quotientGrading (projIdeal W))
          φ rfl one_pos (mk_X_mem_quotientGrading_one W i) ≫ D.ι := by
          congr 1
          simpa only [F, D, E, q, φ,
            projModelFromOfGlobalSections] using
            Proj.fromOfGlobalSections_resLE
              (quotientGrading (projIdeal W))
              (projModelEval W
                (algebraMap R Γ(X, (⊤ : X.Opens))) P hP)
              (projModelEval_irrelevant_map_top_of_isUnit
                W (algebraMap R Γ(X, (⊤ : X.Opens)))
                P hP i hi)
              one_pos (mk_X_mem_quotientGrading_one W i)
    _ = E.ι ≫ X.toSpecΓ ≫
          Spec.map (CommRingCat.ofHom
            (chartAwayHomOfTriple W i P
              (↑hi.unit⁻¹) hi.mul_val_inv hP).toRingHom) ≫
          chartι W i := by
          rw [Proj.toBasicOpenOfGlobalSections]
          rw [reassoc_of% hbasic]
          have hring' :
              ψ.comp
                  ((IsLocalization.map
                    (Localization.Away (φ q)) φ hmap).comp
                    (algebraMap (chartAway W i)
                      (Localization.Away q))) =
                (chartAwayHomOfTriple W i P
                  (↑hi.unit⁻¹) hi.mul_val_inv hP).toRingHom := by
            simpa only [μ] using hring
          slice_lhs 3 4 =>
            rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hring']
          dsimp only [D, q]
          slice_lhs 4 5 => rw [Proj.basicOpenIsoSpec_inv_ι]

end ModularCurves
