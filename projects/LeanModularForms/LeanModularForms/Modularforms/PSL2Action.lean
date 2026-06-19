/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.NumberTheory.Modular
import LeanModularForms.Modularforms.PeterssonInnerProduct

/-!
# PSL₂(ℤ) action on the upper half-plane

The **projective special linear group** `PSL(2, ℤ) = SL(2, ℤ) / {±I}` acts
faithfully on the upper half-plane `ℍ`. The center `{±I}` of `SL(2, ℤ)` acts
trivially (since `(-I) • τ = τ` for all `τ ∈ ℍ`), so the action descends to
the quotient.

## Main results

* `center_SL2Z_smul_eq` — the center of `SL(2, ℤ)` acts trivially on `ℍ`.
* `instMulActionPSL` — `MulAction PSL(2, ℤ) ℍ`.
* `isFundamentalDomain_fdo_PSL` — `𝒟ᵒ` is a fundamental domain for `PSL(2, ℤ)`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.4
* [Shi] Shimura, *Arithmetic Theory of Automorphic Functions*, §1.5
-/

noncomputable section

open scoped MatrixGroups ModularForm Pointwise
open ModularGroup UpperHalfPlane Matrix.SpecialLinearGroup MeasureTheory

/-- The center of `SL(2, ℤ)` consists of `{I, -I}`. Every center element
acts trivially on `ℍ` because it is a scalar matrix `ζI` with `ζ = ±1`,
and `(ζτ + 0)/(0τ + ζ) = τ`. -/
theorem center_SL2Z_smul_eq (c : SL(2, ℤ)) (hc : c ∈ Subgroup.center SL(2, ℤ)) (τ : ℍ) :
    c • τ = τ := by
  rw [mem_center_iff] at hc
  obtain ⟨ζ, hζ, hζ_eq⟩ := hc
  simp only [Fintype.card_fin] at hζ
  have hζ_cases : ζ = 1 ∨ ζ = -1 := by
    rcases mul_eq_zero.mp (by nlinarith [hζ] : (ζ - 1) * (ζ + 1) = 0) with h | h <;> lia
  rcases hζ_cases with rfl | rfl
  · have : c = 1 := by
      ext i j
      simpa [Matrix.scalar] using (congr_fun (congr_fun hζ_eq i) j).symm
    rw [this, one_smul]
  · have : c = -1 := by
      ext i j
      simpa [Matrix.scalar, coe_neg] using (congr_fun (congr_fun hζ_eq i) j).symm
    rw [this]
    simp

private def pslSmul : PSL(2, ℤ) → ℍ → ℍ :=
  Quotient.lift (fun (a : SL(2, ℤ)) (τ : ℍ) ↦ a • τ) (by
    intro a b hab
    funext τ
    rw [show b = a * (a⁻¹ * b) by group, mul_smul,
      center_SL2Z_smul_eq _ (QuotientGroup.leftRel_apply.mp hab)])

@[simp] private theorem pslSmul_coe (a : SL(2, ℤ)) (τ : ℍ) :
    pslSmul (↑a) τ = a • τ := rfl

/-- The action of `PSL(2, ℤ) = SL(2, ℤ)/{±I}` on `ℍ`, descending from the
`SL(2, ℤ)` action since the center acts trivially. -/
instance instMulActionPSL : MulAction PSL(2, ℤ) ℍ where
  smul g τ := pslSmul g τ
  one_smul τ := by
    change pslSmul (↑(1 : SL(2, ℤ))) τ = τ
    rw [pslSmul_coe, one_smul]
  mul_smul g₁ g₂ τ := by
    induction g₁ using Quotient.inductionOn with | h a => ?_
    induction g₂ using Quotient.inductionOn with | h b => ?_
    change pslSmul ((↑a : PSL(2, ℤ)) * ↑b) τ = pslSmul ↑a (pslSmul ↑b τ)
    rw [← QuotientGroup.mk_mul, pslSmul_coe, pslSmul_coe, pslSmul_coe, mul_smul]

/-- The `PSL(2, ℤ)` action is compatible with the `SL(2, ℤ)` action:
`(↑g) • τ = g • τ` for `g : SL(2, ℤ)`. -/
@[simp]
theorem PSL_smul_coe (g : SL(2, ℤ)) (τ : ℍ) :
    (↑g : PSL(2, ℤ)) • τ = g • τ := rfl

instance : Countable PSL(2, ℤ) := Quotient.countable

instance : MeasurableSpace UpperHalfPlane := borel UpperHalfPlane
instance : BorelSpace UpperHalfPlane := ⟨rfl⟩

instance : MeasurableConstSMul PSL(2, ℤ) ℍ where
  measurable_const_smul g := by
    induction g using Quotient.inductionOn with | h a => ?_
    change Measurable (fun τ ↦ (↑a : PSL(2, ℤ)) • τ)
    simp only [PSL_smul_coe]
    exact (continuous_const_smul (mapGL ℝ a)).measurable

private lemma mapGL_det_abs_eq_one (g : SL(2, ℤ)) :
    |(Matrix.GeneralLinearGroup.det (mapGL ℝ g)).val| = 1 := by
  simp [mapGL]

/-- The density identity from [Miyake] (1.4.3)+(1.1.7): for `g ∈ SL₂(ℤ)` and `τ ∈ ℍ`,
`Im(τ)⁻² = Im(gτ)⁻² · normSq(denom g τ)⁻²`. The `normSq` from `Im(gτ)⁻²` exactly cancels
the Jacobian `normSq(denom)⁻²` of the Möbius transform. -/
theorem density_jacobian_identity (g : SL(2, ℤ)) (τ : ℍ) :
    τ.im ^ (-2 : ℤ) = (g • τ).im ^ (-2 : ℤ) *
      Complex.normSq (UpperHalfPlane.denom (mapGL ℝ g) τ) ^ (-2 : ℤ) := by
  set g' := mapGL ℝ g
  suffices him : (g • τ).im = τ.im / Complex.normSq (UpperHalfPlane.denom g' τ) by
    rw [him, div_zpow]
    exact (div_mul_cancel₀ _ (zpow_ne_zero _ <| ne_of_gt <|
      Complex.normSq_pos.mpr (UpperHalfPlane.denom_ne_zero g' τ))).symm
  have h := UpperHalfPlane.im_smul_eq_div_normSq g' τ
  rwa [(rfl : g' • τ = g • τ), mapGL_det_abs_eq_one, one_mul] at h

private def moeb (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (((g.1 0 0 : ℤ) : ℂ) * z + (g.1 0 1 : ℤ)) / ((g.1 1 0 : ℤ) * z + (g.1 1 1 : ℤ))

private lemma moeb_denom_ne_zero (g : SL(2, ℤ)) (z : ℂ) (hz : 0 < z.im) :
    ((g.1 1 0 : ℤ) : ℂ) * z + (g.1 1 1 : ℤ) ≠ 0 :=
  UpperHalfPlane.denom_ne_zero (mapGL ℝ g) (⟨z, hz⟩ : ℍ)

private lemma moeb_hasDerivAt (g : SL(2, ℤ)) (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (moeb g) (1 / ((g.1 1 0 : ℤ) * z + (g.1 1 1 : ℤ) : ℂ) ^ 2) z := by
  set a := ((g.1 0 0 : ℤ) : ℂ)
  set b := ((g.1 0 1 : ℤ) : ℂ)
  set c := ((g.1 1 0 : ℤ) : ℂ)
  set d := ((g.1 1 1 : ℤ) : ℂ)
  have hd := moeb_denom_ne_zero g z hz
  change HasDerivAt (fun w ↦ (a * w + b) / (c * w + d)) (1 / (c * z + d) ^ 2) z
  have hn : DifferentiableAt ℂ (fun w ↦ a * w + b) z :=
    (differentiableAt_id.const_mul a).add (differentiableAt_const b)
  have hdn : DifferentiableAt ℂ (fun w ↦ c * w + d) z :=
    (differentiableAt_id.const_mul c).add (differentiableAt_const d)
  suffices h : deriv (fun w ↦ (a * w + b) / (c * w + d)) z = 1 / (c * z + d) ^ 2 by
    rw [← h]
    exact (hn.div hdn hd).hasDerivAt
  rw [← Pi.div_def, deriv_div hn hdn hd, deriv_add_const, deriv_const_mul_field,
    deriv_add_const, deriv_const_mul_field]
  simp only [deriv_id'', mul_one]
  have hdet : a * d - b * c = 1 := by
    simp only [a, b, c, d]
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  congr 1
  linear_combination hdet

private lemma det_complexSmul (w : ℂ) : (w • (1 : ℂ →L[ℝ] ℂ)).det = Complex.normSq w := by
  rw [show w • (1 : ℂ →L[ℝ] ℂ) =
      (ContinuousLinearMap.toSpanSingleton ℂ w).restrictScalars ℝ by
    ext z; simp [ContinuousLinearMap.toSpanSingleton, mul_comm]]
  change ((ContinuousLinearMap.toSpanSingleton ℂ w).restrictScalars ℝ).toLinearMap.det = _
  rw [show ((ContinuousLinearMap.toSpanSingleton ℂ w).restrictScalars ℝ).toLinearMap =
      (Algebra.lmul ℝ ℂ) w by ext z; simp [ContinuousLinearMap.toSpanSingleton, mul_comm],
    ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.basisOneI, Module.Basis.ofEquivFun_repr_apply,
    Complex.normSq_apply, mul_comm, Algebra.lmul, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk]
  simp [Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]

private lemma moeb_coe (g : SL(2, ℤ)) (τ : ℍ) : moeb g (↑τ) = ↑(g • τ) := by
  simp only [moeb, UpperHalfPlane.coe_specialLinearGroup_apply, algebraMap_int_eq,
    Int.coe_castRingHom]
  push_cast
  rfl

private lemma moeb_image_eq (g : SL(2, ℤ)) (s : Set ℍ) :
    moeb g '' (UpperHalfPlane.coe '' ((g • ·) ⁻¹' s)) = UpperHalfPlane.coe '' s := by
  ext z
  constructor
  · rintro ⟨w, ⟨τ, hτ, rfl⟩, rfl⟩
    exact ⟨g • τ, hτ, (moeb_coe g τ).symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨↑(g⁻¹ • σ), ⟨g⁻¹ • σ, by simpa, rfl⟩, ?_⟩
    rw [moeb_coe, smul_inv_smul]

private lemma setLIntegral_comap_coe (t : Set ℍ) (ht : MeasurableSet t) (f : ℂ → ENNReal) :
    ∫⁻ τ in t, f (UpperHalfPlane.coe τ) ∂(Measure.comap UpperHalfPlane.coe (volume : Measure ℂ)) =
    ∫⁻ z in UpperHalfPlane.coe '' t, f z ∂(volume : Measure ℂ) := by
  have me := isOpenEmbedding_coe.measurableEmbedding
  rw [(⟨me.measurable, me.map_comap volume⟩ :
      MeasurePreserving UpperHalfPlane.coe _ _).setLIntegral_comp_emb me f t,
    Measure.restrict_restrict (me.measurableSet_image.mpr ht),
    Set.inter_eq_left.mpr (Set.image_subset_range _ _)]

instance instSMulInvMeasure_SL : SMulInvariantMeasure SL(2, ℤ) ℍ μ_hyp where
  measure_preimage_smul g s hs := by
    have hs' : MeasurableSet ((g • ·) ⁻¹' s) := (measurable_const_smul g) hs
    simp_rw [hyperbolicMeasure, ← UpperHalfPlane.coe_im]
    rw [withDensity_apply _ hs', withDensity_apply _ hs,
      setLIntegral_comap_coe _ hs' (fun z ↦ ENNReal.ofReal (z.im ^ (-2 : ℤ))),
      setLIntegral_comap_coe _ hs (fun z ↦ ENNReal.ofReal (z.im ^ (-2 : ℤ)))]
    set A := UpperHalfPlane.coe '' ((g • ·) ⁻¹' s)
    rw [show UpperHalfPlane.coe '' s = moeb g '' A from (moeb_image_eq g s).symm,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
        (isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hs')
        (fun z hz ↦ (moeb_hasDerivAt g z (by
          obtain ⟨τ, _, rfl⟩ := hz
          exact τ.coe_im_pos)).complexToReal_fderiv.hasFDerivWithinAt)
        (fun z₁ hz₁ z₂ hz₂ h ↦ by
          obtain ⟨τ₁, _, rfl⟩ := hz₁
          obtain ⟨τ₂, _, rfl⟩ := hz₂
          rw [moeb_coe, moeb_coe] at h
          exact congrArg _ (MulAction.injective g (UpperHalfPlane.ext h)))]
    refine setLIntegral_congr_fun
      (isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hs') fun z hz ↦ ?_
    obtain ⟨τ, _, rfl⟩ := hz
    simp only [det_complexSmul]
    rw [abs_of_nonneg (Complex.normSq_nonneg _),
      ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
      moeb_coe, UpperHalfPlane.coe_im]
    congr 1
    have hdenom : Complex.normSq (1 / ((↑(g.1 1 0 : ℤ) : ℂ) * ↑τ + ↑(g.1 1 1 : ℤ)) ^ 2) =
        Complex.normSq (UpperHalfPlane.denom (mapGL ℝ g) ↑τ) ^ (-2 : ℤ) := by
      simp only [UpperHalfPlane.denom, mapGL, MonoidHom.comp_apply, one_div,
        Complex.normSq_inv, zpow_neg]
      congr 3
      all_goals (first | rfl | simp [Matrix.SpecialLinearGroup.map, algebraMap_int_eq,
        Int.coe_castRingHom, Matrix.SpecialLinearGroup.toGL])
      all_goals exact Eq.refl _
    rw [hdenom, ← UpperHalfPlane.coe_im, mul_comm]
    exact density_jacobian_identity g τ

instance instSMulInvMeasure_PSL : SMulInvariantMeasure PSL(2, ℤ) ℍ μ_hyp where
  measure_preimage_smul g s hs := by
    induction g using Quotient.inductionOn with | h a => ?_
    change μ_hyp ((fun τ ↦ (↑a : PSL(2, ℤ)) • τ) ⁻¹' s) = μ_hyp s
    simpa only [PSL_smul_coe] using
      (measurePreserving_smul a μ_hyp).measure_preimage hs.nullMeasurableSet

private theorem center_SL2Z_smul_eq_of_forall (g : SL(2, ℤ))
    (htriv : ∀ z : ℍ, g • z = z)
    (hc : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    g ∈ Subgroup.center SL(2, ℤ) := by
  have hdet : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 *
      (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two, hc, mul_zero, sub_zero] at this
  set z₀ : ℍ := ⟨⟨0, 2⟩, by norm_num⟩
  have z₀_fdo : z₀ ∈ fdo :=
    ⟨by norm_num [Complex.normSq_apply], by
      change |z₀.re| < 1 / 2
      simp [UpperHalfPlane.re, z₀]⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · have hg : g = T ^ ((↑g : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
      ext i j
      simp only [coe_T_zpow]
      fin_cases i <;> fin_cases j <;> simp_all
    have hb := eq_zero_of_mem_fdo_of_T_zpow_mem_fdo z₀_fdo (hg ▸ htriv z₀ ▸ z₀_fdo)
    rw [hg, hb, zpow_zero]
    exact one_mem _
  · have hng : -g = T ^ (-((↑g : Matrix (Fin 2) (Fin 2) ℤ) 0 1)) := by
      ext i j
      simp only [coe_T_zpow, coe_neg]
      fin_cases i <;> fin_cases j <;> simp_all
    have hb : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by
      have h2 : (-g) • z₀ = z₀ := by
        rw [SL_neg_smul]
        exact htriv z₀
      rw [hng] at h2
      have := eq_zero_of_mem_fdo_of_T_zpow_mem_fdo z₀_fdo (h2 ▸ z₀_fdo)
      lia
    have : g = -1 := neg_eq_iff_eq_neg.mp (by rw [hng, hb, neg_zero, zpow_zero])
    rw [this]
    refine Subgroup.mem_center_iff.mpr fun x ↦ ?_
    ext i j
    simp [coe_neg, neg_mul, mul_neg]

private theorem fdo_PSL_pairwise_disjoint :
    Pairwise fun (g₁ g₂ : PSL(2, ℤ)) ↦ Disjoint (g₁ • (fdo : Set ℍ)) (g₂ • fdo) := by
  intro g₁ g₂ hne
  rw [Set.disjoint_left]
  intro τ h1 h2
  obtain ⟨σ₁, hσ₁, rfl⟩ := h1
  obtain ⟨σ₂, hσ₂, h_eq⟩ := h2
  induction g₁ using Quotient.inductionOn with | h a => ?_
  induction g₂ using Quotient.inductionOn with | h b => ?_
  simp only [PSL_smul_coe] at h_eq
  have hba : (b⁻¹ * a) • σ₁ = σ₂ := by rw [mul_smul, ← h_eq, inv_smul_smul]
  exfalso
  apply hne
  have hc := c_eq_zero hσ₁ (hba ▸ hσ₂)
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
  have hn0 := eq_zero_of_mem_fdo_of_T_zpow_mem_fdo hσ₁ (hn σ₁ ▸ (hba ▸ hσ₂))
  have htriv : ∀ z : ℍ, (b⁻¹ * a) • z = z := fun z ↦ by
    rw [hn z, hn0, zpow_zero, one_smul]
  rw [Quotient.eq, QuotientGroup.leftRel_apply, show a⁻¹ * b = (b⁻¹ * a)⁻¹ by group]
  exact (Subgroup.center _).inv_mem (center_SL2Z_smul_eq_of_forall _ htriv hc)

private lemma measurableSet_fd_diff_fdo : MeasurableSet (fd \ fdo : Set ℍ) :=
  MeasurableSet.diff
    ((isClosed_le continuous_const (Complex.continuous_normSq.comp continuous_coe)).inter
      (isClosed_le (continuous_abs.comp continuous_re) continuous_const)).measurableSet
    UpperHalfPlane.isOpen_fdo.measurableSet

/-- The open fundamental domain `𝒟ᵒ` is a fundamental domain for `PSL(2, ℤ)`
acting on `ℍ` with respect to the hyperbolic measure `μ_hyp`. -/
theorem isFundamentalDomain_fdo_PSL :
    IsFundamentalDomain PSL(2, ℤ) (fdo : Set ℍ) μ_hyp where
  nullMeasurableSet := UpperHalfPlane.isOpen_fdo.measurableSet.nullMeasurableSet
  ae_covers := by
    rw [ae_iff]
    apply measure_mono_null (show {x | ¬∃ g : PSL(2, ℤ), g • x ∈ fdo} ⊆
        ⋃ g : SL(2, ℤ), (g • ·) ⁻¹' (fd \ fdo) by
      intro τ hτ
      push Not at hτ
      obtain ⟨g, hg⟩ := exists_smul_mem_fd τ
      exact Set.mem_iUnion.mpr ⟨g, Set.mem_preimage.mpr ⟨hg, hτ ↑g⟩⟩)
    exact measure_iUnion_null fun g ↦
      (measurePreserving_smul g μ_hyp).measure_preimage
        (measurableSet_fd_diff_fdo.nullMeasurableSet) ▸ hyperbolicMeasure_fd_boundary
  aedisjoint := fun _ _ hne ↦
    (fdo_PSL_pairwise_disjoint hne).aedisjoint

end

noncomputable section GLPos_invariance

open scoped MatrixGroups ModularForm
open UpperHalfPlane MeasureTheory

local notation "GL₂⁺" => GL(2, ℝ)⁺

private def moebGL (g : GL₂⁺) (z : ℂ) : ℂ :=
  let M : Matrix (Fin 2) (Fin 2) ℝ := ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  (↑(M 0 0) * z + ↑(M 0 1)) / (↑(M 1 0) * z + ↑(M 1 1))

private lemma moebGL_denom_ne_zero (g : GL₂⁺) (z : ℂ) (hz : 0 < z.im) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    (↑(M 1 0) * z + ↑(M 1 1) : ℂ) ≠ 0 :=
  denom_ne_zero_of_im (g : GL (Fin 2) ℝ) (ne_of_gt hz)

private lemma moebGL_hasDerivAt (g : GL₂⁺) (z : ℂ) (hz : 0 < z.im) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    HasDerivAt (moebGL g)
      ((↑(M.det : ℝ) : ℂ) / (↑(M 1 0) * z + ↑(M 1 1)) ^ 2) z := by
  set M : Matrix (Fin 2) (Fin 2) ℝ := ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  set a : ℂ := ↑(M 0 0 : ℝ)
  set b : ℂ := ↑(M 0 1 : ℝ)
  set c : ℂ := ↑(M 1 0 : ℝ)
  set d : ℂ := ↑(M 1 1 : ℝ)
  have hd := moebGL_denom_ne_zero g z hz
  change HasDerivAt (fun w ↦ (a * w + b) / (c * w + d)) (↑(M.det : ℝ) / (c * z + d) ^ 2) z
  have hn : DifferentiableAt ℂ (fun w ↦ a * w + b) z :=
    (differentiableAt_id.const_mul a).add (differentiableAt_const b)
  have hdn : DifferentiableAt ℂ (fun w ↦ c * w + d) z :=
    (differentiableAt_id.const_mul c).add (differentiableAt_const d)
  suffices h : deriv (fun w ↦ (a * w + b) / (c * w + d)) z =
      ↑(M.det : ℝ) / (c * z + d) ^ 2 by
    rw [← h]
    exact (hn.div hdn hd).hasDerivAt
  rw [← Pi.div_def, deriv_div hn hdn hd, deriv_add_const, deriv_const_mul_field,
    deriv_add_const, deriv_const_mul_field]
  simp only [deriv_id'', mul_one]
  have hdet : a * d - b * c = ↑(M.det : ℝ) := by
    simp only [a, b, c, d, Matrix.det_fin_two]
    push_cast
    ring
  congr 1
  linear_combination hdet

private lemma moebGL_coe (g : GL₂⁺) (τ : ℍ) : moebGL g (↑τ) = ↑((g : GL (Fin 2) ℝ) • τ) := by
  rw [coe_smul_of_det_pos g.2]
  rfl

private lemma moebGL_image_eq (g : GL₂⁺) (s : Set ℍ) :
    moebGL g '' (UpperHalfPlane.coe '' (((g : GL (Fin 2) ℝ) • ·) ⁻¹' s)) =
      UpperHalfPlane.coe '' s := by
  ext z
  constructor
  · rintro ⟨w, ⟨τ, hτ, rfl⟩, rfl⟩
    exact ⟨(g : GL (Fin 2) ℝ) • τ, hτ, (moebGL_coe g τ).symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨↑((g : GL (Fin 2) ℝ)⁻¹ • σ),
      ⟨(g : GL (Fin 2) ℝ)⁻¹ • σ, by simpa, rfl⟩, ?_⟩
    rw [moebGL_coe, smul_inv_smul]

/-- The density-Jacobian identity for GL₂⁺(ℝ):
`Im(τ)⁻² = normSq(det(g)/(denom g τ)²) · Im(g•τ)⁻²`. The `|det|²` from the Jacobian
cancels the `|det|²` in `Im(g•τ)⁻²`, leaving `Im(τ)⁻²`. -/
theorem density_jacobian_identity_GLpos (g : GL₂⁺) (τ : ℍ) :
    τ.im ^ (-2 : ℤ) =
      Complex.normSq ((↑((↑g : GL (Fin 2) ℝ).det : ℝ) : ℂ) /
        (denom (↑g : GL (Fin 2) ℝ) ↑τ) ^ 2) *
      ((↑g : GL (Fin 2) ℝ) • τ).im ^ (-2 : ℤ) := by
  set g' := (g : GL (Fin 2) ℝ)
  set D := denom g' (↑τ : ℂ)
  have hnsD : (0 : ℝ) < Complex.normSq D := Complex.normSq_pos.mpr (denom_ne_zero g' τ)
  have hdet_pos : (0 : ℝ) < g'.det.val := g.2
  have him := im_smul_eq_div_normSq g' τ
  rw [abs_of_pos hdet_pos] at him
  have hns_frac : Complex.normSq ((↑(g'.det.val : ℝ) : ℂ) / D ^ 2) =
      g'.det.val ^ 2 / Complex.normSq D ^ 2 := by
    rw [Complex.normSq_div, map_pow, Complex.normSq_ofReal]
    ring
  rw [hns_frac, him, div_zpow, mul_comm, mul_zpow]
  field_simp
  ring

/-- `MeasurableConstSMul` for `GL(2,ℝ)⁺` acting on `ℍ`, inherited from `GL(Fin 2, ℝ)`. -/
instance : MeasurableConstSMul GL(2, ℝ)⁺ ℍ where
  measurable_const_smul g := (continuous_const_smul (g : GL (Fin 2) ℝ)).measurable

/-- The hyperbolic measure `μ_hyp` is invariant under the action of `GL(2,ℝ)⁺` on `ℍ`.
This generalizes `instSMulInvMeasure_SL` from `SL(2,ℤ)` to the full group `GL(2,ℝ)⁺`. -/
instance instSMulInvMeasure_GLpos : SMulInvariantMeasure GL(2, ℝ)⁺ ℍ μ_hyp where
  measure_preimage_smul g s hs := by
    set g' := (g : GL (Fin 2) ℝ)
    have hs' : MeasurableSet ((g' • ·) ⁻¹' s) := (measurable_const_smul g') hs
    simp_rw [hyperbolicMeasure, ← UpperHalfPlane.coe_im]
    rw [show (fun τ ↦ (g : GL₂⁺) • τ) ⁻¹' s = (g' • ·) ⁻¹' s from rfl,
      withDensity_apply _ hs', withDensity_apply _ hs,
      setLIntegral_comap_coe _ hs' (fun z ↦ ENNReal.ofReal (z.im ^ (-2 : ℤ))),
      setLIntegral_comap_coe _ hs (fun z ↦ ENNReal.ofReal (z.im ^ (-2 : ℤ)))]
    set A := UpperHalfPlane.coe '' ((g' • ·) ⁻¹' s)
    rw [show UpperHalfPlane.coe '' s = moebGL g '' A from (moebGL_image_eq g s).symm,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
        (isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hs')
        (fun z hz ↦ (moebGL_hasDerivAt g z (by
          obtain ⟨τ, _, rfl⟩ := hz
          exact τ.coe_im_pos)).complexToReal_fderiv.hasFDerivWithinAt)
        (fun z₁ hz₁ z₂ hz₂ h ↦ by
          obtain ⟨τ₁, _, rfl⟩ := hz₁
          obtain ⟨τ₂, _, rfl⟩ := hz₂
          rw [moebGL_coe, moebGL_coe] at h
          exact congrArg _ (MulAction.injective g' (UpperHalfPlane.ext h)))]
    refine setLIntegral_congr_fun
      (isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hs') fun z hz ↦ ?_
    obtain ⟨τ, _, rfl⟩ := hz
    simp only [det_complexSmul]
    rw [abs_of_nonneg (Complex.normSq_nonneg _),
      ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
      moebGL_coe]
    congr 1
    rw [coe_im τ, coe_im ((↑g : GL (Fin 2) ℝ) • τ)]
    exact density_jacobian_identity_GLpos g τ

end GLPos_invariance

noncomputable section PSL_R_action

open scoped MatrixGroups ModularForm Pointwise
open UpperHalfPlane Matrix.SpecialLinearGroup MeasureTheory

/-- The center of `SL(2, ℝ)` consists of `{I, -I}`. Every central element acts
trivially on `ℍ` because it is a scalar matrix `ζI` with `ζ² = 1`, and the Möbius
formula `(ζτ + 0)/(0τ + ζ) = τ` is invariant under the sign of `ζ`. -/
theorem center_SL2R_smul_eq (c : SL(2, ℝ)) (hc : c ∈ Subgroup.center SL(2, ℝ)) (τ : ℍ) :
    c • τ = τ := by
  rw [mem_center_iff] at hc
  obtain ⟨ζ, hζ, hζ_eq⟩ := hc
  simp only [Fintype.card_fin] at hζ
  have hζ_cases : ζ = 1 ∨ ζ = -1 := by
    rcases mul_eq_zero.mp (by nlinarith [hζ] : (ζ - 1) * (ζ + 1) = 0) with h | h
    · exact .inl (by linarith)
    · exact .inr (by linarith)
  have hζ_ne : ζ ≠ 0 := by rcases hζ_cases with rfl | rfl <;> norm_num
  have h00 : ((c : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 = ζ := by
    simpa [Matrix.scalar_apply, Matrix.diagonal] using (congr_fun (congr_fun hζ_eq 0) 0).symm
  have h11 : ((c : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 = ζ := by
    simpa [Matrix.scalar_apply, Matrix.diagonal] using (congr_fun (congr_fun hζ_eq 1) 1).symm
  have h01 : ((c : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 = 0 := by
    simpa [Matrix.scalar_apply, Matrix.diagonal] using (congr_fun (congr_fun hζ_eq 0) 1).symm
  have h10 : ((c : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 = 0 := by
    simpa [Matrix.scalar_apply, Matrix.diagonal] using (congr_fun (congr_fun hζ_eq 1) 0).symm
  have hζ_ne_C : (ζ : ℂ) ≠ 0 := by exact_mod_cast hζ_ne
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply, h00, h11, h01, h10]
  simp only [Algebra.algebraMap_self_apply, Complex.ofReal_zero,
    zero_mul, zero_add, add_zero]
  field_simp

private def pslSmul_R : PSL(2, ℝ) → ℍ → ℍ :=
  Quotient.lift (fun (a : SL(2, ℝ)) (τ : ℍ) ↦ a • τ) (by
    intro a b hab
    funext τ
    rw [show b = a * (a⁻¹ * b) by group, mul_smul,
      center_SL2R_smul_eq _ (QuotientGroup.leftRel_apply.mp hab)])

@[simp] private theorem pslSmul_R_coe (a : SL(2, ℝ)) (τ : ℍ) :
    pslSmul_R (↑a) τ = a • τ := rfl

/-- The action of `PSL(2, ℝ) = SL(2, ℝ)/{±I}` on `ℍ`, descending from the
`SL(2, ℝ)` action since the center acts trivially. -/
instance instMulActionPSL_R : MulAction PSL(2, ℝ) ℍ where
  smul g τ := pslSmul_R g τ
  one_smul τ := by
    change pslSmul_R (↑(1 : SL(2, ℝ))) τ = τ
    rw [pslSmul_R_coe, one_smul]
  mul_smul g₁ g₂ τ := by
    induction g₁ using Quotient.inductionOn with | h a => ?_
    induction g₂ using Quotient.inductionOn with | h b => ?_
    change pslSmul_R ((↑a : PSL(2, ℝ)) * ↑b) τ = pslSmul_R ↑a (pslSmul_R ↑b τ)
    rw [← QuotientGroup.mk_mul, pslSmul_R_coe, pslSmul_R_coe, pslSmul_R_coe, mul_smul]

/-- Compatibility: the `PSL(2, ℝ)` action of a representative coincides with
the underlying `SL(2, ℝ)` action.  Mirror of `PSL_smul_coe` for `PSL(2, ℤ)`. -/
@[simp]
theorem PSL_R_smul_coe (g : SL(2, ℝ)) (τ : ℍ) :
    (↑g : PSL(2, ℝ)) • τ = g • τ := rfl

instance : MeasurableConstSMul PSL(2, ℝ) ℍ where
  measurable_const_smul g := by
    induction g using Quotient.inductionOn with | h a => ?_
    change Measurable (fun τ ↦ (↑a : PSL(2, ℝ)) • τ)
    simp only [PSL_R_smul_coe]
    exact (continuous_const_smul (mapGL ℝ a)).measurable

instance instSMulInvMeasure_PSL_R : SMulInvariantMeasure PSL(2, ℝ) ℍ μ_hyp where
  measure_preimage_smul g s hs := by
    induction g using Quotient.inductionOn with | h a => ?_
    change μ_hyp ((fun τ ↦ (↑a : PSL(2, ℝ)) • τ) ⁻¹' s) = μ_hyp s
    simp only [PSL_R_smul_coe]
    let g_GLPos : GL(2, ℝ)⁺ := ⟨mapGL ℝ a, by simp [mapGL]⟩
    exact (measurePreserving_smul g_GLPos μ_hyp).measure_preimage hs.nullMeasurableSet

/-- The lift `SL(2, ℤ) →* PSL(2, ℝ)`: cast `SL(2, ℤ)` entries to `ℝ` via
`SpecialLinearGroup.map (Int.castRingHom ℝ)`, then project to the `±I`-quotient. -/
def SL2Z_to_PSL2R : SL(2, ℤ) →* PSL(2, ℝ) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))

@[simp] theorem SL2Z_to_PSL2R_apply (g : SL(2, ℤ)) :
    SL2Z_to_PSL2R g =
      (↑(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) : PSL(2, ℝ)) := rfl

/-- Representative-action compatibility: the `PSL(2, ℝ)`-image of an integer `SL`
element acts on `ℍ` exactly as the underlying `SL(2, ℤ)`-element does (under the
`SL(2, ℤ) → SL(2, ℝ)` embedding via `Int.castRingHom`). -/
@[simp]
theorem SL2Z_to_PSL2R_smul (g : SL(2, ℤ)) (τ : ℍ) :
    SL2Z_to_PSL2R g • τ =
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) • τ :=
  rfl

private lemma map_intCast_entry (g : SL(2, ℤ)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ) i j =
    (((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℝ) := rfl

private lemma g_mem_center_of_map_intCast_mem_center (g : SL(2, ℤ))
    (hmem : (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g : SL(2, ℝ)) ∈
      Subgroup.center SL(2, ℝ)) : g ∈ Subgroup.center SL(2, ℤ) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hmem ⊢
  obtain ⟨r, hr_pow, hr_scalar⟩ := hmem
  have h_entry_R : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) =
      (Matrix.scalar (Fin 2) r) i j := fun i j ↦ by
    have h_ij := congr_fun (congr_fun hr_scalar i) j
    rw [map_intCast_entry] at h_ij
    exact h_ij.symm
  set z : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  have hr_z : (z : ℝ) = r := by
    have := h_entry_R 0 0
    rwa [show (Matrix.scalar (Fin 2) r) 0 0 = r by simp [Matrix.scalar_apply]] at this
  have h_diag : ∀ i, (g : Matrix (Fin 2) (Fin 2) ℤ) i i = z := fun i ↦ by
    have h_iR : (((g : Matrix _ _ ℤ) i i : ℤ) : ℝ) = (z : ℝ) := by
      have := h_entry_R i i
      rw [show (Matrix.scalar (Fin 2) r) i i = r by simp [Matrix.scalar_apply]] at this
      rw [this, ← hr_z]
    exact_mod_cast h_iR
  have h_off : ∀ i j, i ≠ j → (g : Matrix (Fin 2) (Fin 2) ℤ) i j = 0 := fun i j hij ↦ by
    have h_R : (((g : Matrix _ _ ℤ) i j : ℤ) : ℝ) = 0 := by
      have := h_entry_R i j
      rw [show (Matrix.scalar (Fin 2) r) i j = 0 by simp [Matrix.scalar_apply, hij]] at this
      exact this
    exact_mod_cast h_R
  have hz_sq : z ^ 2 = 1 := by
    have hz_sq_R : (z : ℝ) ^ 2 = 1 := by
      rw [hr_z]
      simpa [Fintype.card_fin] using hr_pow
    exact_mod_cast hz_sq_R
  refine ⟨z, by simpa [Fintype.card_fin] using hz_sq, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, h_diag]
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, h_off i j hij]

private lemma map_intCast_mem_center_of_g_mem_center (g : SL(2, ℤ))
    (hmem : g ∈ Subgroup.center SL(2, ℤ)) :
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g : SL(2, ℝ)) ∈
      Subgroup.center SL(2, ℝ) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hmem ⊢
  obtain ⟨z, hz_pow, hz_scalar⟩ := hmem
  refine ⟨(z : ℝ), by exact_mod_cast hz_pow, ?_⟩
  ext i j
  have h_ij := congr_fun (congr_fun hz_scalar i) j
  rw [map_intCast_entry]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h_ij ⊢
    exact_mod_cast h_ij
  · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] at h_ij ⊢
    exact_mod_cast h_ij

/-- The kernel of `SL2Z_to_PSL2R` is the center of `SL(2, ℤ)`: an integer matrix
casts to a real scalar matrix iff it is itself a scalar matrix. -/
theorem ker_SL2Z_to_PSL2R : SL2Z_to_PSL2R.ker = Subgroup.center SL(2, ℤ) := by
  ext g
  simp only [MonoidHom.mem_ker, SL2Z_to_PSL2R_apply, QuotientGroup.eq_one_iff]
  exact ⟨g_mem_center_of_map_intCast_mem_center g, map_intCast_mem_center_of_g_mem_center g⟩

/-- The descended hom `PSL(2, ℤ) →* PSL(2, ℝ)`. `SL2Z_to_PSL2R` factors through
`PSL(2, ℤ) = SL(2, ℤ) ⧸ center SL(2, ℤ)` since integer scalar matrices map into
`center SL(2, ℝ)`. -/
def PSL2Z_to_PSL2R : PSL(2, ℤ) →* PSL(2, ℝ) :=
  QuotientGroup.lift (Subgroup.center SL(2, ℤ)) SL2Z_to_PSL2R fun x hx ↦ by
    rwa [ker_SL2Z_to_PSL2R]

@[simp] theorem PSL2Z_to_PSL2R_mk (g : SL(2, ℤ)) :
    PSL2Z_to_PSL2R (↑g : PSL(2, ℤ)) = SL2Z_to_PSL2R g :=
  QuotientGroup.lift_mk' _ _ g

/-- Action compatibility for `PSL2Z_to_PSL2R` (representative form): the descended
hom sends `[g] : PSL(2, ℤ)` to a `PSL(2, ℝ)`-element acting on `ℍ` exactly as the
underlying `SL(2, ℤ)`-action does. -/
@[simp]
theorem PSL2Z_to_PSL2R_smul (g : SL(2, ℤ)) (τ : ℍ) :
    PSL2Z_to_PSL2R (↑g : PSL(2, ℤ)) • τ = g • τ :=
  rfl

/-- Action compatibility for `PSL2Z_to_PSL2R` (generic form): for any
`p : PSL(2, ℤ)`, the descended hom's image acts on `ℍ` exactly as `p` does. -/
@[simp]
theorem PSL2Z_to_PSL2R_smul_eq (p : PSL(2, ℤ)) (τ : ℍ) :
    PSL2Z_to_PSL2R p • τ = p • τ := by
  induction p using Quotient.inductionOn with | h g => ?_
  exact (PSL2Z_to_PSL2R_smul g τ).trans (PSL_smul_coe g τ).symm

/-- `PSL2Z_to_PSL2R` is injective: its kernel is the image of
`SL2Z_to_PSL2R.ker = center SL(2, ℤ)` under the `PSL(2, ℤ)`-projection, which is `⊥`. -/
theorem PSL2Z_to_PSL2R_injective : Function.Injective PSL2Z_to_PSL2R := by
  rw [← MonoidHom.ker_eq_bot_iff]
  change (QuotientGroup.lift (Subgroup.center SL(2, ℤ)) SL2Z_to_PSL2R _).ker = ⊥
  rw [QuotientGroup.ker_lift, ker_SL2Z_to_PSL2R, QuotientGroup.map_mk'_self]

/-- Positive-scalar action invariance for `GL (Fin 2) ℝ`: if `h` has matrix obtained
by scaling `g`'s matrix by a positive scalar `c`, and `g` has positive determinant,
then `h` and `g` act identically on `ℍ`. -/
lemma GL_smul_pos_eq
    {g h : GL (Fin 2) ℝ} {c : ℝ} (hc : 0 < c)
    (hg_det : 0 < g.det.val)
    (h_eq : ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      c • ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    (τ : ℍ) :
    h • τ = g • τ := by
  have hc_C : (c : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  have hh_det : 0 < h.det.val := by
    have h_det_eq : h.det.val = c ^ 2 * g.det.val := by
      change ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
        c ^ 2 * ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det
      rw [h_eq, Matrix.det_smul]
      simp [Fintype.card_fin]
    rw [h_det_eq]
    positivity
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos hh_det, coe_smul_of_det_pos hg_det]
  have h_entry : ∀ i j,
      ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
        c * ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j := fun i j ↦ by
    rw [h_eq]
    simp [Matrix.smul_apply, smul_eq_mul]
  have h_num : num h τ = (c : ℂ) * num g τ := by
    change ((h 0 0 : ℝ) : ℂ) * τ + ((h 0 1 : ℝ) : ℂ) =
      (c : ℂ) * (((g 0 0 : ℝ) : ℂ) * τ + ((g 0 1 : ℝ) : ℂ))
    push_cast [h_entry 0 0, h_entry 0 1]
    ring
  have h_denom : denom h τ = (c : ℂ) * denom g τ := by
    change ((h 1 0 : ℝ) : ℂ) * τ + ((h 1 1 : ℝ) : ℂ) =
      (c : ℂ) * (((g 1 0 : ℝ) : ℂ) * τ + ((g 1 1 : ℝ) : ℂ))
    push_cast [h_entry 1 0, h_entry 1 1]
    ring
  rw [h_num, h_denom, mul_div_mul_left _ _ hc_C]

/-- The det-normalized `SL(2, ℝ)` representative of a `GL(2, ℝ)⁺` element: the matrix
`(Real.sqrt g.det.val)⁻¹ • g.val.val` has determinant `1`. -/
noncomputable def GLPos_to_SLR (g : GL(2, ℝ)⁺) : SL(2, ℝ) :=
  ⟨(Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
      ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ),
    by
      have hg_pos : 0 < ((g : GL (Fin 2) ℝ).det.val : ℝ) := g.property
      change ((Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
          ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).det = 1
      rw [Matrix.det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt hg_pos.le]
      exact inv_mul_cancel₀ (ne_of_gt hg_pos)⟩

/-- The projective representative of a `GL(2, ℝ)⁺` element: the `PSL(2, ℝ)`-image of
`GLPos_to_SLR g`. This is a function, not a group hom, since the determinant
normalization does not commute with matrix multiplication. -/
noncomputable def GLPos_to_PSL_R_term (g : GL(2, ℝ)⁺) : PSL(2, ℝ) :=
  (GLPos_to_SLR g : PSL(2, ℝ))

/-- Action equivariance: the projective representative `GLPos_to_PSL_R_term g` acts on
`ℍ` exactly as `g` does, even though `det g` need not be `1`. -/
theorem GLPos_to_PSL_R_term_smul (g : GL(2, ℝ)⁺) (τ : ℍ) :
    GLPos_to_PSL_R_term g • τ = g • τ := by
  have hg_pos : 0 < ((g : GL (Fin 2) ℝ).det.val : ℝ) := g.property
  have h_sqrt_pos : 0 < (Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ := by
    rw [inv_pos]
    exact Real.sqrt_pos.mpr hg_pos
  change ((GLPos_to_SLR g : SL(2, ℝ)) : PSL(2, ℝ)) • τ = g • τ
  rw [PSL_R_smul_coe]
  change (mapGL ℝ (GLPos_to_SLR g) : GL (Fin 2) ℝ) • τ = (g : GL (Fin 2) ℝ) • τ
  refine GL_smul_pos_eq h_sqrt_pos hg_pos ?_ τ
  change ((mapGL ℝ (GLPos_to_SLR g) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    (Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
      ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  ext i j
  simp [GLPos_to_SLR, Matrix.smul_apply]

/-- Set-level action compatibility: the set-level analogue of
`GLPos_to_PSL_R_term_smul`, lifting pointwise action-equality on `ℍ` to set-image
equality. -/
@[simp]
theorem GLPos_to_PSL_R_term_smul_set (α' : GL(2, ℝ)⁺) (S : Set ℍ) :
    (GLPos_to_PSL_R_term α' • S : Set ℍ) = ((α' : GL(2, ℝ)⁺) • S : Set ℍ) := by
  ext τ
  simp [Set.mem_smul_set, GLPos_to_PSL_R_term_smul]

end PSL_R_action

