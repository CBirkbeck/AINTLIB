/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.Curves.Divisor.MillerAllChar
import HasseWeil.Foundation.EC.SeparableKernelTorsor
import HasseWeil.HasseBound.WeilPairing.DivisorPullback
import HasseWeil.HasseBound.WeilPairing.Pairing
import HasseWeil.HasseBound.WeilPairing.PairingProps
import HasseWeil.HasseBound.WeilPairing.TorsionCardEll

/-!
# Nondegeneracy of the Weil pairing

This file proves that the finite-level Weil pairing over an algebraically closed field is
nondegenerate in its second argument. The proof uses surjectivity of multiplication on curve
points, injectivity of divisor pullback, the Galois fixed-field description, and Abel--Jacobi.

## Main results

* `weilPairing_nondegenerate`: the Weil pairing is nondegenerate in its second argument.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.3.3, III.4.10b, and III.8.1c.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric HasseWeil.WeilPairing.DivisorPullback

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

local notation "KE" => W.toAffine.FunctionField

section Nondeg

variable [IsAlgClosed F]

omit [DecidableEq F]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
private theorem exists_mulByInt_preimage_x (ℓ : ℤ) (hℓ0 : ℓ ≠ 0) (x_Q : F) :
    ∃ x₀ : F, (W.Φ ℓ).eval x₀ = x_Q * (W.ΨSq ℓ).eval x₀ ∧
      (W.ΨSq ℓ).eval x₀ ≠ 0 := by
  set g : Polynomial F := W.Φ ℓ - Polynomial.C x_Q * W.ΨSq ℓ with hg_def
  have hΦ_monic : (W.Φ ℓ).Monic := W.leadingCoeff_Φ ℓ
  have hΦ_natDeg : (W.Φ ℓ).natDegree = ℓ.natAbs ^ 2 := W.natDegree_Φ ℓ
  have hℓ2_pos : 0 < ℓ.natAbs ^ 2 := pow_pos (Int.natAbs_pos.mpr hℓ0) 2
  have hsub_natDeg_le : (Polynomial.C x_Q * W.ΨSq ℓ).natDegree ≤ ℓ.natAbs ^ 2 - 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (W.natDegree_ΨSq_le ℓ)
  have hg_monic : g.Monic := by
    refine hΦ_monic.sub_of_left ?_
    rw [Polynomial.degree_eq_natDegree hΦ_monic.ne_zero, hΦ_natDeg]
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact_mod_cast lt_of_le_of_lt hsub_natDeg_le (Nat.sub_lt hℓ2_pos Nat.one_pos)
  have hg_natDeg : g.natDegree = ℓ.natAbs ^ 2 := by
    rw [hg_def]
    refine (Polynomial.natDegree_sub_eq_left_of_natDegree_lt ?_).trans hΦ_natDeg
    rw [hΦ_natDeg]; exact lt_of_le_of_lt hsub_natDeg_le (Nat.sub_lt hℓ2_pos Nat.one_pos)
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root g (by
    rw [Polynomial.degree_eq_natDegree hg_monic.ne_zero, hg_natDeg]
    exact_mod_cast hℓ2_pos.ne')
  have hroot : (W.Φ ℓ).eval x₀ = x_Q * (W.ΨSq ℓ).eval x₀ := by
    simpa only [Polynomial.IsRoot.def, hg_def, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, sub_eq_zero] using hx₀
  refine ⟨x₀, hroot, ?_⟩
  intro hΨ0
  have hor : (W.Φ ℓ).eval x₀ ≠ 0 ∨ (W.ΨSq ℓ).eval x₀ ≠ 0 := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      Polynomial.aeval_ne_zero_of_isCoprime
        (isCoprime_Φ_ΨSq W (W.coe_Δ' ▸ W.Δ'.ne_zero) hℓ0) x₀
  rcases hor with hΦne | hΨne
  · rw [hroot, hΨ0, mul_zero] at hΦne; exact hΦne rfl
  · exact hΨne hΨ0

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
private theorem exists_mulByInt_preimage_point (ℓ : ℤ) (hℓ0 : ℓ ≠ 0)
    (x_Q y_Q : F) (hQns : W.toAffine.Nonsingular x_Q y_Q) :
    ∃ P : W.toAffine.Point, ℓ • P = Affine.Point.some x_Q y_Q hQns := by
  obtain ⟨x₀, hroot, hΨSq_ne⟩ := exists_mulByInt_preimage_x W ℓ hℓ0 x_Q
  obtain ⟨y₀, hy₀eq⟩ := exists_point_on_curve W x₀
  have hns₀ : W.toAffine.Nonsingular x₀ y₀ :=
    (W.toAffine.equation_iff_nonsingular_of_Δ_ne_zero (W.coe_Δ' ▸ W.Δ'.ne_zero)).mp hy₀eq
  have hψ_ne : (W.ψ ℓ).evalEval x₀ y₀ ≠ 0 := by
    intro hψ0
    apply hΨSq_ne
    rw [ΨSq_eval_eq_psi_sq W hy₀eq ℓ, hψ0, zero_pow (by norm_num)]
  obtain ⟨hns', hsmul⟩ := zsmul_affine_point_eq_gen W ℓ hns₀ hψ_ne
  have hx_eq : (W.φ ℓ).evalEval x₀ y₀ / (W.ψ ℓ).evalEval x₀ y₀ ^ 2 = x_Q := by
    rw [evalEval_φ_eq_Φ W hy₀eq ℓ,
      show (W.ψ ℓ).evalEval x₀ y₀ ^ 2 = (W.ΨSq ℓ).eval x₀ from
        (ΨSq_eval_eq_psi_sq W hy₀eq ℓ).symm,
      hroot, mul_div_assoc, div_self hΨSq_ne, mul_one]
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq (Affine.equation_iff_nonsingular.mpr hns')
      (Affine.equation_iff_nonsingular.mpr hQns) hx_eq with hyy | hyy
  · refine ⟨Affine.Point.some x₀ y₀ hns₀, ?_⟩
    rw [hsmul]
    exact (Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hx_eq, hyy⟩
  · refine ⟨-(Affine.Point.some x₀ y₀ hns₀), ?_⟩
    rw [zsmul_neg, hsmul, Affine.Point.neg_some]
    refine (Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hx_eq, ?_⟩
    rw [hx_eq, hyy, WeierstrassCurve.Affine.negY_negY]

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- Multiplication by a nonzero integer is surjective on points over an algebraically closed
field. -/
theorem mulByInt_point_surjective (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
    Function.Surjective (mulByInt W.toAffine ℓ).toAddMonoidHom := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; norm_num at hℓ
  intro Q
  simp only [mulByInt_apply]
  rcases Q with _ | ⟨x_Q, y_Q, hQns⟩
  · exact ⟨0, zsmul_zero ℓ⟩
  · exact exists_mulByInt_preimage_point W ℓ hℓ0 x_Q y_Q hQns

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- Pullback of divisors by multiplication is injective over an algebraically closed field. -/
theorem pullbackDivisor_injective (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    [hker : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker] :
    Function.Injective
      (pullbackDivisor (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker) := by
  intro D₁ D₂ hD
  refine Finsupp.ext fun v ↦ ?_
  obtain ⟨P, hP⟩ := mulByInt_point_surjective W ℓ hℓ v.toAffinePoint
  set w : ProjectiveSmoothPoint (⟨W.toAffine⟩ : SmoothPlaneCurve F) :=
    P.toProjectiveSmoothPoint with hw
  have hwaff : (mulByInt W.toAffine ℓ).toAddMonoidHom w.toAffinePoint = v.toAffinePoint := by
    rw [hw, Affine.Point.toProjectiveSmoothPoint_toAffinePoint]; exact hP
  have h1 := congrFun (congrArg DFunLike.coe hD) w
  rw [pullbackDivisor_apply (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker D₁ w,
    pullbackDivisor_apply (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker D₂ w,
    hwaff, Affine.Point.toAffinePoint_toProjectiveSmoothPoint] at h1
  exact h1

/-- A point is zero if its difference from zero defines a principal divisor. -/
theorem eq_zero_of_kappaDivisor_principal {T : W.toAffine.Point}
    (hT : (⟨W.toAffine⟩ : SmoothPlaneCurve F).ProjIsPrincipal
      (Curves.kappaDivisor W.toAffine T)) :
    T = 0 := by
  simpa [Curves.projectiveDivisorSum_kappaDivisor] using
    (afInputs_allChar W.toAffine).h_van
      (fun _ hD ↦ SmoothPlaneCurve.principal_mem_degZero (C := ⟨W.toAffine⟩) hD)
      (Curves.kappaDivisor W.toAffine T) hT

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- Every automorphism over a multiplication pullback is translation by a torsion point. -/
theorem aut_eq_translate (ℓ : ℤ) (hℓ0 : ℓ ≠ 0)
    (σ : @AlgEquiv KE KE KE _ _ _
      (mulByInt W.toAffine ℓ).toAlgebra (mulByInt W.toAffine ℓ).toAlgebra) :
    ∃ k : W.toAffine.Point, ℓ • k = 0 ∧
      ∀ z : KE, σ z = translateAlgEquivOfPoint W k z := by
  letI := (mulByInt W.toAffine ℓ).toAlgebra
  have hcov := hcov_mulByInt_of_xy W ℓ hℓ0 (hxy_mulByInt W ℓ hℓ0)
  set forward := kernelTranslateForwardAut W (mulByInt W.toAffine ℓ) hcov with hfwd_def
  obtain ⟨k, hk_mem, hk_lift⟩ := hdesc_mulByInt W ℓ hℓ0 σ
  have hk0 : ℓ • k = 0 := by
    rw [← mulByInt_apply]; exact (HasseWeil.Isogeny.mem_kernel_iff _ k).mp hk_mem
  refine ⟨k, hk0, ?_⟩
  have hact : genericPointAct W (mulByInt W.toAffine ℓ) (forward ⟨k, hk_mem⟩) =
      genericPointAct W (mulByInt W.toAffine ℓ) σ := by
    rw [hfwd_def,
      genericPointAct_kernelTranslateForwardAut W (mulByInt W.toAffine ℓ) hcov ⟨k, hk_mem⟩]
    rw [hk_lift, add_comm, sub_add_cancel]
  rw [genericPointAct_eq_some W (mulByInt W.toAffine ℓ) (forward ⟨k, hk_mem⟩),
    genericPointAct_eq_some W (mulByInt W.toAffine ℓ) σ] at hact
  have hcoords := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hact
  have hσx : σ (x_gen W) = translateAlgEquivOfPoint W k (x_gen W) := hcoords.1.symm
  have hσy : σ (y_gen W) = translateAlgEquivOfPoint W k (y_gen W) := hcoords.2.symm
  have hcoeq : (σ.toAlgHom.restrictScalars F) = (translateAlgEquivOfPoint W k).toAlgHom :=
    algHom_ext_x_y_gen W hσx hσy
  intro z
  exact DFunLike.congr_fun hcoeq z

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- A function fixed by all torsion translations lies in the multiplication pullback range. -/
theorem mem_pullback_range_of_translate_fixed (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    {g : KE} (hg : ∀ S : W.toAffine.Point, ℓ • S = 0 →
      translateAlgEquivOfPoint W S g = g) :
    ∃ h : KE, (mulByInt W.toAffine ℓ).pullback h = g := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; norm_num at hℓ
  letI := (mulByInt W.toAffine ℓ).toAlgebra
  haveI hfin : @FiniteDimensional KE KE _ _ (mulByInt W.toAffine ℓ).toAlgebra.toModule :=
    isogeny_finiteDimensional W (mulByInt W.toAffine ℓ)
  haveI hgal : @IsGalois KE _ KE _ (mulByInt W.toAffine ℓ).toAlgebra :=
    Isogeny.isGalois_of_isSeparable_and_normal (mulByInt W.toAffine ℓ)
      (mulByInt_isSeparable W ℓ hℓ) (h_normal_mulByInt W ℓ hℓ0)
  have hfix : ∀ σ : @AlgEquiv KE KE KE _ _ _
      (mulByInt W.toAffine ℓ).toAlgebra (mulByInt W.toAffine ℓ).toAlgebra, σ g = g := by
    intro σ
    obtain ⟨k, hk0, hσ⟩ := aut_eq_translate W ℓ hℓ0 σ
    rw [hσ g]; exact hg k hk0
  have hbot : g ∈ (⊥ : IntermediateField KE KE) :=
    (IsGalois.mem_bot_iff_fixed g).mpr hfix
  rwa [IntermediateField.mem_bot] at hbot

omit [IsAlgClosed F] [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- Pullback sends the divisor of a point relative to zero to the corresponding fibre difference. -/
theorem pullbackDivisor_kappaDivisor (ℓ : ℤ)
    [hker : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker] (T : W.toAffine.Point) :
    pullbackDivisor (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker
        (Curves.kappaDivisor W.toAffine T) =
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker T -
        pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker 0 := by
  rw [Curves.kappaDivisor, ← pullbackDivisorHom_apply, map_sub, pullbackDivisorHom_apply,
    pullbackDivisorHom_apply, pullbackDivisor_single, pullbackDivisor_single, one_smul, one_smul,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
    ProjectiveSmoothPoint.toAffinePoint_infinity]

/-- The Weil pairing is nondegenerate in its second argument. -/
theorem weilPairing_nondegenerate (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (T : W.toAffine.Point) (hT : ℓ • T = 0)
    (h_deg : ∀ S : W.toAffine.Point, (hS : ℓ • S = 0) →
      weilPairing W ℓ hℓ S T hS hT = 1) :
    T = 0 := by
  haveI hker : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker := mulByInt_ker_finite W ℓ hℓ
  obtain ⟨h, hh⟩ := mem_pullback_range_of_translate_fixed W ℓ hℓ (fun S hS ↦ by
    rw [weilPairing_translate W ℓ hℓ S T hS hT, h_deg S hS, map_one, one_mul])
  apply eq_zero_of_kappaDivisor_principal W
  refine ⟨h, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hh
    exact weilFunction_ne_zero W ℓ hℓ T hT hh.symm
  · apply pullbackDivisor_injective W ℓ hℓ
    rw [← projectiveDivisorOf_pullback_eq_pullbackDivisor (W := W.toAffine)
      (projOrdTransport_mulByInt ℓ hℓ) h]
    change (W_smooth W).projectiveDivisorOf ((mulByInt W.toAffine ℓ).pullback h) = _
    rw [hh, weilFunction_divisor W ℓ hℓ T hT, pullbackDivisor_kappaDivisor W ℓ T]

end Nondeg

end HasseWeil.WeilPairing
