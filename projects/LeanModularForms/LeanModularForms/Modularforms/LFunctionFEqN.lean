/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.Modularforms.LFunctionFEq

/-!
# Functional equation and analytic continuation at level `N` via the Fricke involution

For a weight-`k` cusp form `f` on a width-`1` arithmetic group that the Fricke matrix
`W_N = [[0,-1],[N,0]]` normalizes (e.g. `Γ₁(N)` or `Γ₀(N)`), Hecke's theorem at level `N`
(Diamond–Shurman Thm 5.10.2, Shimura §3.6) reads
`Λ_N(k - s, f) = iᵏ · Λ_N(s, g)`, where `g = f ∣[k] W_N` (Petersson-normalized, see below) and
`Λ_N(s, f) = N^{s/2} · (2π)^{-s} · Γ(s) · L(s, f)` is the **level-`N` completed L-function**.

This generalizes `LFunctionFEq.lean` (the level-`1` `S`-involution case `N = 1`,
`W_1 = S`, `g = f`).

## The Fricke imaginary-axis slash

The single genuinely new analytic input is the behaviour of the imaginary-axis restriction under
the slash by `W_N`.  With the **scaled restriction** `F̃(t) := f(i·t/√N)`
(`fun t ↦ (f : ℍ → ℂ).resToImagAxis (t / √N)`):

* `frickeImagAxisSlash`: for `t > 0`,
  `(f ∣[k] W_N).resToImagAxis (t/√N) = (√N)^{k-2} · i^{-k} · t^{-k} · F̃(1/t)`.

Computation: `denom(W_N, z) = N z`; at `z = it/√N`, `N z = i t √N`, so
`(denom)^{-k} = i^{-k} t^{-k} N^{-k/2}`; `(det W_N)^{k-1} = N^{k-1}`; and
`W_N • (it/√N) = i·(1/t)/√N`.  Hence the constant is `N^{k-1} · N^{-k/2} = N^{k/2-1} = (√N)^{k-2}`.

## Normalization

We use the **Petersson-normalized** Fricke companion `g = N^{1-k/2} • (f ∣[k] W_N)`
(equivalently `(√N)^{2-k} • (f ∣[k] W_N)`).  With this normalization the relation between the
scaled restrictions becomes `F̃(1/t) = (iᵏ · t^k) • G̃(t)`, so the root number is exactly
`ε = iᵏ` and the classical statement `Λ_N(k - s, f) = iᵏ · Λ_N(s, g)` holds verbatim.

## The big reuse

The Mellin bridge `ModularForms.mellin_resToImagAxis_eq` is *level-agnostic* (needs only width `1`,
cusp, `0 < k`, `k/2+1 < Re s`).  The `√N` scaling factors out cleanly via mathlib's
`mellin_comp_mul_right`:
`mellin F̃ s = (√N)^s · mellin (resToImagAxis f) s = N^{s/2} · (2π)^{-s} · Γ(s) · L(s, f)`.
So we reuse `mellin_resToImagAxis_eq` for **both** `f` and `g`, multiplying only by the scaling
factor.  The rapid decay, local integrability, and continuation assembly all reuse the
level-`1` machinery in `LFunctionFEq.lean`.

## Main results

* `ModularForms.frickeImagAxisSlash`: the Fricke imaginary-axis slash lemma (the new crux).
* `ModularForms.lcompletedN_functional_equation`: Hecke's functional equation at level `N`,
  `Λ_N(k - s, f) = iᵏ · Λ_N(s, g)`.
* `ModularForms.lSeriesN_hasEntireExtension`: analytic continuation of `L(·, f)` (for any width-`1`
  arithmetic cusp form), to an entire function on `ℂ`.

## References

* Hecke, *Über die Bestimmung Dirichletscher Reihen durch ihre Funktionalgleichung*.
* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.10 (Thm 5.10.2).
* [Shi] Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.6.
* [Miy] Miyake, *Modular Forms*, Thm 4.3.5.
-/

open Filter Topology Asymptotics Set MeasureTheory Complex UpperHalfPlane
open scoped Real ModularForm MatrixGroups

namespace ModularForms

/-! ### The Fricke matrix `W_N` in `GL₂(ℝ)` -/

/-- The Fricke matrix `W_N = [[0,-1],[N,0]] ∈ GL₂(ℝ)` (determinant `N`).  Acting on `ℍ` by
`z ↦ -1/(N z)`.  This is the level-`N` analogue of `S = [[0,-1],[1,0]]` (the case `N = 1`). -/
noncomputable def frickeR (N : ℕ) [NeZero N] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simpa using (NeZero.ne (N : ℝ)))

@[simp] lemma frickeR_coe (N : ℕ) [NeZero N] :
    (↑(frickeR N) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (N : ℝ), 0] := rfl

lemma frickeR_det_val (N : ℕ) [NeZero N] : (frickeR N).det.val = N := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, frickeR_coe, Matrix.det_fin_two_of]; ring

lemma frickeR_det_pos (N : ℕ) [NeZero N] : 0 < (frickeR N).det.val := by
  rw [frickeR_det_val]; exact_mod_cast NeZero.pos N

/-! ### The scaled imaginary-axis lift and the Fricke smul identity -/

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- `√N > 0`, the positivity of the scaling factor.  Used throughout to justify `t ↦ t / √N`. -/
private lemma sqrt_natCast_pos : 0 < Real.sqrt N :=
  Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos N)

/-- The point `i · t / √N ∈ ℍ`, for `t > 0`. -/
private noncomputable def scaledImLift {t : ℝ} (ht : 0 < t) : ℍ :=
  ⟨Complex.I * (t / Real.sqrt N : ℝ), by
    have hN : 0 < Real.sqrt N := sqrt_natCast_pos
    simp only [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im,
      one_mul, zero_mul]
    positivity⟩

private lemma scaledImLift_coe {t : ℝ} (ht : 0 < t) :
    ((scaledImLift (N := N) ht : ℍ) : ℂ) = Complex.I * (t / Real.sqrt N : ℝ) := rfl

/-- `F.resToImagAxis (t / √N) = F (i·t/√N)` for `t > 0` (raw-function form). -/
private lemma resToImagAxisScaled_eq (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    F.resToImagAxis (t / Real.sqrt N) = F (scaledImLift (N := N) ht) := by
  have hN : 0 < Real.sqrt N := sqrt_natCast_pos
  have htN : 0 < t / Real.sqrt N := by positivity
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htN, ↓reduceDIte]
  congr 1

/-- **The Fricke smul identity on the scaled imaginary axis.**  For `t > 0`,
`W_N • (i·t/√N) = i·(1/t)/√N`. -/
private lemma frickeR_smul_scaledImLift {t : ℝ} (ht : 0 < t) :
    frickeR N • scaledImLift (N := N) ht = scaledImLift (N := N) (one_div_pos.mpr ht) := by
  have hN : 0 < Real.sqrt N := sqrt_natCast_pos
  have hNc : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hsqN : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]; norm_cast
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (frickeR_det_pos N)]
  rw [UpperHalfPlane.num, UpperHalfPlane.denom, frickeR_coe, scaledImLift_coe, scaledImLift_coe]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  -- `(0 * (I·t/√N) + (-1)) / ((N) * (I·t/√N) + 0) = I · ((1/t)/√N)`
  push_cast
  rw [div_eq_iff (by
    -- denominator `N * (I * (t / √N))` is nonzero
    have : (N : ℂ) * (Complex.I * (↑t / ↑(Real.sqrt N))) ≠ 0 := by
      refine mul_ne_zero (by exact_mod_cast (NeZero.ne N)) (mul_ne_zero Complex.I_ne_zero ?_)
      exact div_ne_zero htc hNc
    simpa using this)]
  rw [← hsqN]; field_simp; ring_nf; rw [Complex.I_sq]; ring

/-! ### The Fricke imaginary-axis slash lemma (the crux) -/

open ModularForm in
/-- **The Fricke imaginary-axis slash.**  For any `F : ℍ → ℂ` and `t > 0`, the scaled
imaginary-axis restriction of the Fricke slash `F ∣[k] W_N` is
`(F ∣[k] W_N).resToImagAxis (t/√N) = (√N)^{k-2} · i^{-k} · t^{-k} · F.resToImagAxis ((1/t)/√N)`.

This is the level-`N` analogue of `ResToImagAxis.SlashActionS`; the constant `(√N)^{k-2}`
absorbs the `N^{k-1}` from `(det W_N)^{k-1}` and the `N^{-k/2}` from `denom(W_N)^{-k}`. -/
theorem frickeImagAxisSlash (F : ℍ → ℂ) {t : ℝ} (ht : 0 < t) :
    (F ∣[k] frickeR N).resToImagAxis (t / Real.sqrt N) =
      (Real.sqrt N : ℂ) ^ (k - 2) * Complex.I ^ (-k) * (t : ℂ) ^ (-k) *
        F.resToImagAxis (1 / t / Real.sqrt N) := by
  have hN : 0 < Real.sqrt N := sqrt_natCast_pos
  have hNc : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hsqN : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]; norm_cast
  -- Rewrite both restrictions in terms of `F` evaluated at the lift points.
  rw [resToImagAxisScaled_eq (F ∣[k] frickeR N) ht, resToImagAxisScaled_eq F (one_div_pos.mpr ht)]
  -- Unfold the slash at the lift point, using `det W_N > 0` (so `σ = id`) and `|det| = N`.
  rw [ModularForm.slash_apply, frickeR_smul_scaledImLift ht]
  have hσ : ∀ w : ℂ, UpperHalfPlane.σ (frickeR N) w = w := fun w ↦ by
    rw [UpperHalfPlane.σ, if_pos (frickeR_det_pos N)]; rfl
  rw [hσ]
  have hdet : |(frickeR N).det.val| = (N : ℝ) := by
    rw [frickeR_det_val]; exact abs_of_nonneg (Nat.cast_nonneg N)
  rw [hdet]
  -- Compute `denom (W_N) (i·t/√N) = √N · i · t`.
  have hdenom : UpperHalfPlane.denom (frickeR N) (scaledImLift (N := N) ht) =
      (Real.sqrt N : ℂ) * Complex.I * (t : ℂ) := by
    rw [UpperHalfPlane.denom, frickeR_coe, scaledImLift_coe]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    rw [show (N : ℂ) = (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) from hsqN.symm]
    field_simp
    ring
  rw [hdenom]
  -- Collapse the scalar: `N^{k-1} · (√N · i · t)^{-k} = (√N)^{k-2} · i^{-k} · t^{-k}`.
  have hN2 : ((N : ℝ) : ℂ) ^ (k - 1) = (Real.sqrt N : ℂ) ^ (2 * (k - 1)) := by
    rw [show ((N : ℝ) : ℂ) = (Real.sqrt N : ℂ) ^ (2 : ℤ) by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq]; exact hsqN.symm, ← zpow_mul]
  have hsplit : ((Real.sqrt N : ℂ) * Complex.I * (t : ℂ)) ^ (-k) =
      (Real.sqrt N : ℂ) ^ (-k) * Complex.I ^ (-k) * (t : ℂ) ^ (-k) := by
    rw [mul_zpow, mul_zpow]
  have hscalar : ((N : ℝ) : ℂ) ^ (k - 1) * ((Real.sqrt N : ℂ) * Complex.I * (t : ℂ)) ^ (-k) =
      (Real.sqrt N : ℂ) ^ (k - 2) * Complex.I ^ (-k) * (t : ℂ) ^ (-k) := by
    rw [hN2, hsplit]
    rw [show (Real.sqrt N : ℂ) ^ (2 * (k - 1))
          * ((Real.sqrt N : ℂ) ^ (-k) * Complex.I ^ (-k) * (t : ℂ) ^ (-k))
        = ((Real.sqrt N : ℂ) ^ (2 * (k - 1)) * (Real.sqrt N : ℂ) ^ (-k))
          * (Complex.I ^ (-k) * (t : ℂ) ^ (-k)) by ring]
    rw [← zpow_add₀ hNc, show 2 * (k - 1) + -k = k - 2 by ring]
    ring
  rw [mul_assoc, hscalar]
  ring

/-! ### The level-`N` completed L-function and the scaled Mellin bridge -/

omit [NeZero N] k in
/-- `√N` as a complex number, raised to the power `s`, equals `N^{s/2}`. -/
private lemma sqrt_cpow_eq (s : ℂ) :
    (Real.sqrt N : ℂ) ^ s = (N : ℂ) ^ (s / 2) := by
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; ring,
    show s / 2 = ((1 / 2 : ℝ) : ℂ) * s by push_cast; ring,
    Complex.cpow_mul_ofReal_nonneg hNR, ← Real.sqrt_eq_rpow]

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ]

/-- The **level-`N` completed L-function** (naive Dirichlet product):
`Λ_N(s, f) = N^{s/2} · (2π)^{-s} · Γ(s) · L(s, f)`. -/
noncomputable def lcompletedSeriesN (N : ℕ) [ModularFormClass F Γ k] (f : F) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * lcompletedSeries f s

@[simp]
lemma lcompletedSeriesN_apply (N : ℕ) [ModularFormClass F Γ k] (f : F) (s : ℂ) :
    lcompletedSeriesN N f s = (N : ℂ) ^ (s / 2) * lcompletedSeries f s := rfl

/-- **The scaled Mellin bridge.**  For a weight-`k` cusp form `f` of strict width `1` at `∞` on an
arithmetic subgroup, with `0 < k`, the Mellin transform of the **scaled** imaginary-axis
restriction `t ↦ f(i·t/√N)` on the half-plane `k/2 + 1 < Re s` equals the level-`N` completed
L-function `N^{s/2} · (2π)^{-s} · Γ(s) · L(s, f)`. -/
theorem mellin_resToImagAxisScaled_eq [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F)
    (hw : Γ.strictWidthInfty = 1) (hk : 0 < k) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    mellin (fun t : ℝ ↦ (f : ℍ → ℂ).resToImagAxis (t / Real.sqrt N)) s =
      lcompletedSeriesN N f s := by
  have hN : 0 < Real.sqrt N := sqrt_natCast_pos
  have hNinv : 0 < (Real.sqrt N)⁻¹ := inv_pos.mpr hN
  -- write the scaled restriction as a multiplicative shift `t ↦ g(t · (√N)⁻¹)`
  have heq : (fun t : ℝ ↦ (f : ℍ → ℂ).resToImagAxis (t / Real.sqrt N)) =
      (fun t : ℝ ↦ (f : ℍ → ℂ).resToImagAxis (t * (Real.sqrt N)⁻¹)) := by
    funext t; rw [div_eq_mul_inv]
  rw [heq, mellin_comp_mul_right _ s hNinv, mellin_resToImagAxis_eq f hw hk hs]
  -- `((√N)⁻¹)^(-s) = (√N)^s = N^{s/2}`
  have harg : (Real.sqrt N : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (Real.sqrt_nonneg _)]; exact Real.pi_ne_zero.symm
  rw [lcompletedSeriesN_apply, smul_eq_mul, Complex.ofReal_inv,
    Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv, sqrt_cpow_eq]

/-! ### Rapid decay and local integrability of the scaled restriction -/

/-- The scaled imaginary-axis lift `t ↦ ofComplex (i·t/√N) : ℝ → ℍ`. -/
private noncomputable def scaledImAxisLift (t : ℝ) : ℍ :=
  UpperHalfPlane.ofComplex (Complex.I * (t / Real.sqrt N : ℝ))

private lemma scaledImAxisLift_coe {t : ℝ} (ht : 0 < t) :
    ((scaledImAxisLift (N := N) t : ℍ) : ℂ) = Complex.I * (t / Real.sqrt N : ℝ) := by
  have hN : 0 < Real.sqrt N := sqrt_natCast_pos
  rw [scaledImAxisLift, UpperHalfPlane.ofComplex_apply_of_im_pos
    (z := Complex.I * (t / Real.sqrt N : ℝ)) (by
      simp only [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im,
        one_mul, zero_mul]
      positivity)]

private lemma scaledImAxisLift_im_of_pos {t : ℝ} (ht : 0 < t) :
    (scaledImAxisLift (N := N) t).im = t / Real.sqrt N := by
  rw [← UpperHalfPlane.coe_im, scaledImAxisLift_coe ht, Complex.mul_im, Complex.I_im, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma resToImagAxisScaled_eq_comp [ModularFormClass F Γ k] (f : F) {t : ℝ} (ht : 0 < t) :
    (f : ℍ → ℂ).resToImagAxis (t / Real.sqrt N) = f (scaledImAxisLift (N := N) t) := by
  rw [resToImagAxisScaled_eq (f : ℍ → ℂ) ht]
  congr 1
  apply UpperHalfPlane.ext
  rw [scaledImAxisLift_coe ht, scaledImLift_coe]

/-- The scaled lift tends to `atImInfty` as `t → ∞` (since `t/√N → ∞`). -/
private lemma tendsto_scaledImAxisLift : Tendsto (scaledImAxisLift (N := N)) atTop atImInfty := by
  have hN : 0 < Real.sqrt N := sqrt_natCast_pos
  refine UpperHalfPlane.tendsto_comap_im_ofComplex.comp ?_
  rw [tendsto_comap_iff]
  have htend : Tendsto (fun t : ℝ ↦ t / Real.sqrt N) atTop atTop :=
    Filter.Tendsto.atTop_div_const hN tendsto_id
  refine htend.congr fun t ↦ ?_
  simp [Function.comp_apply, Complex.mul_im]

/-- **Exponential decay of the scaled restriction.**  For a weight-`k` cusp form of strict
width `1` at `∞`, `t ↦ f(i·t/√N) =O[atTop] (fun t => exp(-2π t/√N))`. -/
private lemma isBigO_resToImagAxisScaled_exp [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F)
    (hw : Γ.strictWidthInfty = 1) :
    (fun t : ℝ ↦ (f : ℍ → ℂ).resToImagAxis (t / Real.sqrt N)) =O[atTop]
      fun t : ℝ ↦ Real.exp (-2 * π * (t / Real.sqrt N)) := by
  have hΓper : (1 : ℝ) ∈ Γ.strictPeriods := hw ▸ Γ.strictWidthInfty_mem_strictPeriods
  have hdecay : (⇑f) =O[atImInfty] fun τ : ℍ ↦ Real.exp (-2 * π * τ.im / 1) :=
    CuspFormClass.exp_decay_atImInfty (h := 1) f one_pos hΓper
  have hcomp := hdecay.comp_tendsto (tendsto_scaledImAxisLift (N := N))
  refine (hcomp.congr' ?_ ?_)
  · filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Function.comp_apply, ← resToImagAxisScaled_eq_comp f ht]
  · filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Function.comp_apply, scaledImAxisLift_im_of_pos ht]
    norm_num

/-- **Rapid decay of the scaled restriction.**  For a weight-`k` cusp form of strict width `1`,
`t ↦ f(i·t/√N) =O[atTop] (·^r)` for every real exponent `r`.  This is the `hf_top`/`hg_top` field
of a `StrongFEPair`. -/
private lemma isBigO_resToImagAxisScaled_rpow [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F)
    (hw : Γ.strictWidthInfty = 1) (r : ℝ) :
    (fun t : ℝ ↦ (f : ℍ → ℂ).resToImagAxis (t / Real.sqrt N)) =O[atTop] fun t : ℝ ↦ t ^ r := by
  have hN : 0 < Real.sqrt N := sqrt_natCast_pos
  refine (isBigO_resToImagAxisScaled_exp f hw).trans ?_
  -- `exp(-2π t/√N) = exp(-(2π/√N)·t)` is `o(t^r)` (decays faster than any power)
  have hlit : (fun t : ℝ ↦ Real.exp (-(2 * π / Real.sqrt N) * t)) =o[atTop] fun t : ℝ ↦ t ^ r :=
    isLittleO_exp_neg_mul_rpow_atTop (by positivity) r
  refine (hlit.isBigO).congr_left (fun t ↦ ?_)
  congr 1
  field_simp

/-- The scaled restriction is locally integrable on `Ioi 0` (continuous there). -/
private lemma locallyIntegrableOn_resToImagAxisScaled [ModularFormClass F Γ k] (f : F) :
    LocallyIntegrableOn (fun t : ℝ ↦ (f : ℍ → ℂ).resToImagAxis (t / Real.sqrt N)) (Ioi 0) := by
  have hN : 0 < Real.sqrt N := sqrt_natCast_pos
  refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
  refine fun t (ht : 0 < t) ↦ ?_
  -- `t ↦ res(t/√N)` is differentiable at `t > 0` (chain rule on the linear scaling)
  have hdiff : DifferentiableAt ℝ (fun t : ℝ ↦ (f : ℍ → ℂ).resToImagAxis (t / Real.sqrt N)) t := by
    have htN : 0 < t / Real.sqrt N := by positivity
    have h1 := ResToImagAxis.Differentiable (f : ℍ → ℂ) (ModularFormClass.holo f)
      (t / Real.sqrt N) htN
    exact (h1.comp t (differentiableAt_id.div_const _))
  exact hdiff.continuousAt.continuousWithinAt

/-! ### The level-`N` functional-equation pair -/

omit [NeZero N] k in
/-- Scaling the function commutes with the scaled restriction:
`(c • F).resToImagAxis (t/√N) = c • (F.resToImagAxis (t/√N))`. -/
private lemma resToImagAxisScaled_smul (c : ℂ) (F : ℍ → ℂ) (t : ℝ) :
    (c • F).resToImagAxis (t / Real.sqrt N) = c • (F.resToImagAxis (t / Real.sqrt N)) := by
  simp only [Function.resToImagAxis_apply, ResToImagAxis, Pi.smul_apply]
  split_ifs <;> simp

open ModularForm in
/-- **The level-`N` self-duality functional equation** (Petersson-normalized).  For raw functions
`F G : ℍ → ℂ` with `G = (√N)^{2-k} • (F ∣[k] W_N)`, the scaled restrictions
`F̃(t) := F(i·t/√N)`, `G̃(t) := G(i·t/√N)` satisfy
`F̃(1/t) = (iᵏ · t^k) · G̃(t)` for `t > 0`.  This is the `h_feq` field of the `StrongFEPair`,
with FE-weight `k` and root number `ε = iᵏ`. -/
private lemma resToImagAxisScaled_feq (F G : ℍ → ℂ)
    (hG : G = (Real.sqrt N : ℂ) ^ (2 - k) • (F ∣[k] frickeR N)) {t : ℝ} (ht : 0 < t) :
    F.resToImagAxis (1 / t / Real.sqrt N) =
      (Complex.I ^ k * ((t ^ (k : ℝ) : ℝ) : ℂ)) • G.resToImagAxis (t / Real.sqrt N) := by
  have hN : 0 < Real.sqrt N := sqrt_natCast_pos
  have hNc : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  -- `G̃(t) = (√N)^{2-k} · (F∣W_N).resToImagAxis(t/√N) = I^{-k} · t^{-k} · F̃(1/t)`.
  rw [hG, resToImagAxisScaled_smul, frickeImagAxisSlash F ht]
  rw [smul_eq_mul, smul_eq_mul,
    show ((t ^ (k : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ k by rw [← Complex.ofReal_zpow, Real.rpow_intCast]]
  -- `F̃(1/t) = I^k · t^k · ((√N)^{2-k} · (√N)^{k-2} · I^{-k} · t^{-k} · F̃(1/t))`.
  have hsqcancel : (Real.sqrt N : ℂ) ^ (2 - k) * (Real.sqrt N : ℂ) ^ (k - 2) = 1 := by
    rw [← zpow_add₀ hNc, show (2 - k) + (k - 2) = 0 by ring, zpow_zero]
  rw [show (Real.sqrt N : ℂ) ^ (2 - k) *
        ((Real.sqrt N : ℂ) ^ (k - 2) * Complex.I ^ (-k) * (t : ℂ) ^ (-k) *
          F.resToImagAxis (1 / t / Real.sqrt N))
      = ((Real.sqrt N : ℂ) ^ (2 - k) * (Real.sqrt N : ℂ) ^ (k - 2)) *
        (Complex.I ^ (-k) * (t : ℂ) ^ (-k)) * F.resToImagAxis (1 / t / Real.sqrt N) by ring,
    hsqcancel, one_mul]
  rw [show Complex.I ^ k * (t : ℂ) ^ k *
        (Complex.I ^ (-k) * (t : ℂ) ^ (-k) * F.resToImagAxis (1 / t / Real.sqrt N))
      = (Complex.I ^ k * Complex.I ^ (-k)) * ((t : ℂ) ^ k * (t : ℂ) ^ (-k)) *
        F.resToImagAxis (1 / t / Real.sqrt N) by ring,
    ← zpow_add₀ Complex.I_ne_zero, ← zpow_add₀ htc, add_neg_cancel, zpow_zero,
    zpow_zero, one_mul, one_mul]

open ModularForm in
/-- The `StrongFEPair` attached to a level-`N` weight-`k` cusp form `F` and its Petersson-normalized
Fricke companion `G = (√N)^{2-k} • (F ∣[k] W_N)` (both width-`1` arithmetic cusp forms, possibly on
different carriers `Γ_F`, `Γ_G`).  The two functions are the **scaled** restrictions
`F̃(t) = F(i·t/√N)`, `G̃(t) = G(i·t/√N)`; the FE-weight is `k`; the root number is `ε = iᵏ`. -/
noncomputable def feqPairN
    {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {F₁ F₂ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ]
    [Γ₁.IsArithmetic] [CuspFormClass F₁ Γ₁ k] [Γ₂.IsArithmetic] [CuspFormClass F₂ Γ₂ k]
    (f : F₁) (g : F₂) (hw₁ : Γ₁.strictWidthInfty = 1) (hw₂ : Γ₂.strictWidthInfty = 1) (hk : 0 < k)
    (hg : (g : ℍ → ℂ) = (Real.sqrt N : ℂ) ^ (2 - k) • ((f : ℍ → ℂ) ∣[k] frickeR N)) :
    WeakFEPair ℂ where
  f := fun t : ℝ ↦ (f : ℍ → ℂ).resToImagAxis (t / Real.sqrt N)
  g := fun t : ℝ ↦ (g : ℍ → ℂ).resToImagAxis (t / Real.sqrt N)
  k := (k : ℝ)
  ε := Complex.I ^ k
  f₀ := 0
  g₀ := 0
  hf_int := locallyIntegrableOn_resToImagAxisScaled f
  hg_int := locallyIntegrableOn_resToImagAxisScaled g
  hk := by exact_mod_cast hk
  hε := zpow_ne_zero _ Complex.I_ne_zero
  h_feq := fun x hx ↦ resToImagAxisScaled_feq (f : ℍ → ℂ) (g : ℍ → ℂ) hg (mem_Ioi.mp hx)
  hf_top := fun r ↦ by simpa using isBigO_resToImagAxisScaled_rpow f hw₁ r
  hg_top := fun r ↦ by simpa using isBigO_resToImagAxisScaled_rpow g hw₂ r

/-- The level-`N` `feqPairN` is a strong FE-pair: its constant terms vanish. -/
theorem isStrongFEPairN
    {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {F₁ F₂ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ]
    [Γ₁.IsArithmetic] [CuspFormClass F₁ Γ₁ k] [Γ₂.IsArithmetic] [CuspFormClass F₂ Γ₂ k]
    (f : F₁) (g : F₂) (hw₁ : Γ₁.strictWidthInfty = 1) (hw₂ : Γ₂.strictWidthInfty = 1) (hk : 0 < k)
    (hg : (g : ℍ → ℂ) = (Real.sqrt N : ℂ) ^ (2 - k) • ((f : ℍ → ℂ) ∣[k] frickeR N)) :
    IsStrongFEPair (feqPairN f g hw₁ hw₂ hk hg) where
  hf₀ := rfl
  hg₀ := rfl

/-! ### The level-`N` completed L-function, its functional equation and entirety -/

/-- The **level-`N` completed L-function** of a weight-`k` cusp form `f`: the entire function
`Λ_N(s, f) = mellin (t ↦ f(i·t/√N)) s`. -/
noncomputable def lcompletedΛN (N : ℕ) [NeZero N] {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*}
    [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) (s : ℂ) : ℂ :=
  mellin (fun t : ℝ ↦ (f : ℍ → ℂ).resToImagAxis (t / Real.sqrt N)) s

lemma lcompletedΛN_apply (N : ℕ) [NeZero N] {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*}
    [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) (s : ℂ) :
    lcompletedΛN N f s = mellin (fun t : ℝ ↦ (f : ℍ → ℂ).resToImagAxis (t / Real.sqrt N)) s := rfl

/-- On the half-plane `k/2 + 1 < Re s`, the level-`N` completed L-function equals the naive
completed Dirichlet product `N^{s/2} · (2π)^{-s} · Γ(s) · L(s, f)`. -/
theorem lcompletedΛN_eq_lcompletedSeriesN {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ]
    [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F) (hw : Γ.strictWidthInfty = 1) (hk : 0 < k)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    lcompletedΛN N f s = lcompletedSeriesN N f s :=
  mellin_resToImagAxisScaled_eq f hw hk hs

open ModularForm in
/-- **Hecke's functional equation at level `N`** (the headline, maximally general).  For width-`1`
arithmetic weight-`k` (`k > 0`) cusp forms `F`, `G` on (possibly different) carriers, with `G` the
**Petersson-normalized Fricke companion** `G = (√N)^{2-k} • (F ∣[k] W_N)`, the level-`N` completed
L-functions satisfy
`Λ_N(k - s, F) = iᵏ · Λ_N(s, G)` for all `s : ℂ`. -/
theorem lcompletedN_functional_equation
    {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {F₁ F₂ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ]
    [Γ₁.IsArithmetic] [CuspFormClass F₁ Γ₁ k] [Γ₂.IsArithmetic] [CuspFormClass F₂ Γ₂ k]
    (f : F₁) (g : F₂) (hw₁ : Γ₁.strictWidthInfty = 1) (hw₂ : Γ₂.strictWidthInfty = 1) (hk : 0 < k)
    (hg : (g : ℍ → ℂ) = (Real.sqrt N : ℂ) ^ (2 - k) • ((f : ℍ → ℂ) ∣[k] frickeR N)) (s : ℂ) :
    lcompletedΛN N f ((k : ℂ) - s) = Complex.I ^ k * lcompletedΛN N g s := by
  have hP := isStrongFEPairN f g hw₁ hw₂ hk hg
  set P := feqPairN f g hw₁ hw₂ hk hg with hP_def
  have hfe := P.functional_equation s
  -- `P.Λ (k - s) = ε • P.symm.Λ s`; here `ε = I^k`, `P.Λ = lcompletedΛN N f`,
  -- `P.symm.Λ = lcompletedΛN N g`.
  rw [smul_eq_mul] at hfe
  have hΛf : ∀ t, lcompletedΛN N f t = P.Λ t := fun t ↦ (hP.hasMellin t).2
  have hΛg : ∀ t, lcompletedΛN N g t = P.symm.Λ t := fun t ↦ (hP.symm.hasMellin t).2
  have hPk : (P.k : ℂ) = (k : ℂ) := by
    have hk_eq : P.k = (k : ℝ) := by rw [hP_def]; rfl
    rw [hk_eq]; push_cast; ring
  rw [hΛf ((k : ℂ) - s), show ((k : ℂ) - s) = (↑P.k - s) from by rw [hPk], hfe, ← hΛg s]
  rfl

open ModularForm in
/-- **The level-`N` completed L-function is entire.**  For a width-`1` arithmetic weight-`k`
(`k > 0`) cusp form `f` whose Petersson-normalized Fricke companion `g = (√N)^{2-k} • (f ∣[k] W_N)`
is again a (width-`1` arithmetic) cusp form, `Λ_N(·, f)` is entire. -/
theorem differentiable_lcompletedΛN
    {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {F₁ F₂ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ]
    [Γ₁.IsArithmetic] [CuspFormClass F₁ Γ₁ k] [Γ₂.IsArithmetic] [CuspFormClass F₂ Γ₂ k]
    (f : F₁) (g : F₂) (hw₁ : Γ₁.strictWidthInfty = 1) (hw₂ : Γ₂.strictWidthInfty = 1) (hk : 0 < k)
    (hg : (g : ℍ → ℂ) = (Real.sqrt N : ℂ) ^ (2 - k) • ((f : ℍ → ℂ) ∣[k] frickeR N)) :
    Differentiable ℂ (lcompletedΛN N f) := by
  have hP := isStrongFEPairN f g hw₁ hw₂ hk hg
  have hΛ : lcompletedΛN N f = (feqPairN f g hw₁ hw₂ hk hg).Λ :=
    funext fun s ↦ (hP.hasMellin s).2
  rw [hΛ]
  exact hP.differentiable_Λ

/-! ### Analytic continuation of `L(·, f)` at level `N` -/

open ModularForm in
/-- The entire witness for the continuation of `L(·, f)` at level `N`:
`s ↦ (2π)^s · Λ_N(s, f) / (N^{s/2} · Γ(s))`. -/
private noncomputable def lSeriesExtensionN
    {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (s : ℂ) : ℂ :=
  (2 * ↑π) ^ s * lcompletedΛN N f s * ((N : ℂ) ^ (s / 2))⁻¹ * (Complex.Gamma s)⁻¹

open ModularForm in
/-- The witness is entire: `(2π)^s`, `Λ_N`, `(N^{s/2})⁻¹` and `1/Γ` are all entire. -/
private lemma differentiable_lSeriesExtensionN
    {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {F₁ F₂ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ]
    [Γ₁.IsArithmetic] [CuspFormClass F₁ Γ₁ k] [Γ₂.IsArithmetic] [CuspFormClass F₂ Γ₂ k]
    (f : F₁) (g : F₂) (hw₁ : Γ₁.strictWidthInfty = 1) (hw₂ : Γ₂.strictWidthInfty = 1) (hk : 0 < k)
    (hg : (g : ℍ → ℂ) = (Real.sqrt N : ℂ) ^ (2 - k) • ((f : ℍ → ℂ) ∣[k] frickeR N)) :
    Differentiable ℂ (lSeriesExtensionN (N := N) f) := by
  have hpi : NeZero (2 * (↑π : ℂ)) := ⟨by simp [Real.pi_ne_zero]⟩
  have hNz : NeZero (N : ℂ) := ⟨by exact_mod_cast NeZero.ne N⟩
  -- `s ↦ (N^{s/2})⁻¹` is entire (a nonvanishing complex power, composed with `s ↦ s/2`).
  have hNpow : Differentiable ℂ (fun s : ℂ ↦ ((N : ℂ) ^ (s / 2))⁻¹) := by
    have h1 : Differentiable ℂ (fun s : ℂ ↦ (N : ℂ) ^ (s / 2)) :=
      (differentiable_const_cpow_of_neZero (N : ℂ)).comp
        ((differentiable_id).div_const 2)
    refine h1.inv (fun s ↦ ?_)
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (NeZero.ne (N : ℂ)))
  refine (((((differentiable_const_cpow_of_neZero (2 * (↑π : ℂ))).mul
    (differentiable_lcompletedΛN f g hw₁ hw₂ hk hg)).mul hNpow)).mul
    Complex.differentiable_one_div_Gamma)

open ModularForm in
/-- On the half-plane `k/2 + 1 < Re s`, the witness equals `L(s, f)`. -/
private lemma lSeriesExtensionN_eq_of_re_gt [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F)
    (hw : Γ.strictWidthInfty = 1)
    (hk : 0 < k) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    lSeriesExtensionN (N := N) f s = LSeries (lCoeff f) s := by
  have hs0re : 0 < s.re := lt_trans (by positivity) hs
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (fun m ↦ by
    intro h; rw [h] at hs0re; simp at hs0re; nlinarith [hs0re, Nat.cast_nonneg (α := ℝ) m])
  have hpi : (2 * (↑π : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hNpow : (N : ℂ) ^ (s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hNz)
  rw [lSeriesExtensionN, lcompletedΛN_eq_lcompletedSeriesN f hw hk hs, lcompletedSeriesN_apply,
    lcompletedSeries_apply, lSeries_apply]
  rw [show (2 * (↑π : ℂ)) ^ s *
        ((N : ℂ) ^ (s / 2) * ((2 * ↑π) ^ (-s) * Complex.Gamma s * LSeries (lCoeff f) s))
        * ((N : ℂ) ^ (s / 2))⁻¹ * (Complex.Gamma s)⁻¹
      = ((2 * ↑π) ^ s * (2 * ↑π) ^ (-s)) * ((N : ℂ) ^ (s / 2) * ((N : ℂ) ^ (s / 2))⁻¹) *
        (Complex.Gamma s * (Complex.Gamma s)⁻¹) * LSeries (lCoeff f) s from by ring]
  rw [← Complex.cpow_add _ _ hpi, add_neg_cancel, Complex.cpow_zero, mul_inv_cancel₀ hNpow,
    mul_inv_cancel₀ hΓ, one_mul, one_mul, one_mul]

open ModularForm in
/-- **Analytic continuation of the L-function at level `N`.**  For a width-`1` arithmetic weight-`k`
(`k > 0`) cusp form `f` whose Petersson-normalized Fricke companion `g = (√N)^{2-k} • (f ∣[k] W_N)`
is again a (width-`1` arithmetic) cusp form, the L-function `L(·, f)` extends to an entire function
on `ℂ`, namely `s ↦ (2π)^s · Λ_N(s, f) / (N^{s/2} · Γ(s))`. -/
theorem lSeriesN_hasEntireExtension
    {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} {F₁ F₂ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ]
    [Γ₁.IsArithmetic] [CuspFormClass F₁ Γ₁ k] [Γ₂.IsArithmetic] [CuspFormClass F₂ Γ₂ k]
    (f : F₁) (g : F₂) (hw₁ : Γ₁.strictWidthInfty = 1) (hw₂ : Γ₂.strictWidthInfty = 1) (hk : 0 < k)
    (hg : (g : ℍ → ℂ) = (Real.sqrt N : ℂ) ^ (2 - k) • ((f : ℍ → ℂ) ∣[k] frickeR N)) :
    LSeries.HasEntireExtension (lCoeff f) := by
  refine ⟨lSeriesExtensionN (N := N) f,
    differentiable_lSeriesExtensionN f g hw₁ hw₂ hk hg, ?_⟩
  -- agreement on the convergence half-plane via the identity theorem
  set U : Set ℂ := {z : ℂ | LSeries.abscissaOfAbsConv (lCoeff f) < (z.re : EReal)} with hU
  have hGan : AnalyticOnNhd ℂ (lSeriesExtensionN (N := N) f) U :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (differentiable_lSeriesExtensionN f g hw₁ hw₂ hk hg)).mono (Set.subset_univ _)
  have hLan : AnalyticOnNhd ℂ (LSeries (lCoeff f)) U := LSeries_analyticOnNhd (lCoeff f)
  set z₀ : ℂ := (((k : ℝ) / 2 + 2 : ℝ) : ℂ) with hz₀
  have habs : LSeries.abscissaOfAbsConv (lCoeff f) ≤ (((k : ℝ) / 2 : ℝ) : EReal) + 1 :=
    abscissaOfAbsConv_lCoeff_le_cuspForm f
  have hz₀U : z₀ ∈ U := by
    rw [hU, Set.mem_setOf_eq, hz₀, Complex.ofReal_re]
    refine lt_of_le_of_lt habs ?_
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) from rfl, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    linarith
  have hnhd : lSeriesExtensionN (N := N) f =ᶠ[𝓝 z₀] LSeries (lCoeff f) := by
    have hopen : IsOpen {z : ℂ | (k : ℝ) / 2 + 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hz₀mem : z₀ ∈ {z : ℂ | (k : ℝ) / 2 + 1 < z.re} := by
      rw [Set.mem_setOf_eq, hz₀, Complex.ofReal_re]; linarith
    filter_upwards [hopen.mem_nhds hz₀mem] with z hz
    exact lSeriesExtensionN_eq_of_re_gt f hw₁ hk hz
  intro s hs
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hGan hLan
    (isPreconnected_re_gt_EReal _) hz₀U hnhd hs

/-! ### Level-`1` subsumption

At `N = 1`, the Fricke matrix `W_1 = [[0,-1],[1,0]]` is `S`, `√1 = 1`, the level-`1` completed
function `Λ_1(·, f) = mellin(t ↦ f(it))` is exactly `LFunctionFEq.lean`'s `lcompleted f`, and the
Petersson factor `(√1)^{2-k} = 1` is trivial.  Hence this file subsumes the level-`1` result. -/

section Level1Subsumption

/-- At level `1`, the level-`N` completed L-function is the level-`1` completed L-function of
`LFunctionFEq.lean`: `Λ_1(·, f) = mellin(t ↦ f(it)) = lcompleted f`. -/
theorem lcompletedΛN_one_eq_lcompleted {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) :
    lcompletedΛN 1 f = lcompleted f := by
  funext s
  rw [lcompletedΛN_apply, lcompleted_apply]
  simp only [Nat.cast_one, Real.sqrt_one, div_one]

/-- At level `1`, the Petersson-normalized Fricke companion is `f ∣[k] S`. -/
theorem frickeR_one_slash_eq_S_slash (F : ℍ → ℂ) :
    (Real.sqrt (1 : ℕ) : ℂ) ^ (2 - k) • (F ∣[k] frickeR 1) = F ∣[k] ModularGroup.S := by
  have hWS : frickeR 1 = (ModularGroup.S : GL (Fin 2) ℝ) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [frickeR_coe]
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_S]
  rw [hWS, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, one_zpow, one_smul,
    ModularForm.SL_slash]

end Level1Subsumption

/-! ### Specialisation to the concrete `Γ₁(N)` carrier

For cusp forms on `Γ := (Γ₁(N)).map (mapGL ℝ)`, the strict width at `∞` is automatically `1`
(`strictWidthInfty_Gamma1_mapGL`), so Hecke's functional equation and the analytic continuation
hold without the explicit width hypotheses.  The Fricke matrix `W_N` normalizes `Γ₁(N)`, so the
companion `g = (√N)^{2-k} • (f ∣[k] W_N)` is again a cusp form on `Γ₁(N)`; wiring this companion to
a *bundled* `CuspForm` requires the Fricke-operator cusp-preservation of
`HeckeRIngs/GL2/Fricke.lean` (`frickeOperatorCusp`) and is left as future work to keep this file's
import surface light.  We record here the `Γ₁(N)`-carrier form where the bundled companion `g` is
supplied by the caller. -/

section Gamma1

open CongruenceSubgroup Matrix.SpecialLinearGroup

variable {N : ℕ} [NeZero N] {k : ℤ}
variable {F₁ F₂ : Type*} [FunLike F₁ ℍ ℂ] [FunLike F₂ ℍ ℂ]
  [CuspFormClass F₁ ((Gamma1 N).map (mapGL ℝ)) k] [CuspFormClass F₂ ((Gamma1 N).map (mapGL ℝ)) k]

/-- **Hecke's functional equation at level `N`, on the `Γ₁(N)` carrier.**  For weight-`k` (`k > 0`)
cusp forms `f`, `g` on `Γ₁(N)` with `g = (√N)^{2-k} • (f ∣[k] W_N)` the Petersson-normalized Fricke
companion, `Λ_N(k - s, f) = iᵏ · Λ_N(s, g)`. -/
theorem lcompletedN_functional_equation_Gamma1 (f : F₁) (g : F₂) (hk : 0 < k)
    (hg : (g : ℍ → ℂ) = (Real.sqrt N : ℂ) ^ (2 - k) • ((f : ℍ → ℂ) ∣[k] frickeR N)) (s : ℂ) :
    lcompletedΛN N f ((k : ℂ) - s) = Complex.I ^ k * lcompletedΛN N g s :=
  lcompletedN_functional_equation f g (strictWidthInfty_Gamma1_mapGL N)
    (strictWidthInfty_Gamma1_mapGL N) hk hg s

/-- **The level-`N` completed L-function of a `Γ₁(N)` cusp form is entire.** -/
theorem differentiable_lcompletedΛN_Gamma1 (f : F₁) (g : F₂) (hk : 0 < k)
    (hg : (g : ℍ → ℂ) = (Real.sqrt N : ℂ) ^ (2 - k) • ((f : ℍ → ℂ) ∣[k] frickeR N)) :
    Differentiable ℂ (lcompletedΛN N f) :=
  differentiable_lcompletedΛN f g (strictWidthInfty_Gamma1_mapGL N)
    (strictWidthInfty_Gamma1_mapGL N) hk hg

/-- **Analytic continuation at level `N`, on the `Γ₁(N)` carrier.**  The L-function of a weight-`k`
(`k > 0`) cusp form on `Γ₁(N)` whose Fricke companion is again a `Γ₁(N)` cusp form extends to an
entire function on `ℂ`. -/
theorem lSeriesN_hasEntireExtension_Gamma1 (f : F₁) (g : F₂) (hk : 0 < k)
    (hg : (g : ℍ → ℂ) = (Real.sqrt N : ℂ) ^ (2 - k) • ((f : ℍ → ℂ) ∣[k] frickeR N)) :
    LSeries.HasEntireExtension (lCoeff f) :=
  lSeriesN_hasEntireExtension f g (strictWidthInfty_Gamma1_mapGL N)
    (strictWidthInfty_Gamma1_mapGL N) hk hg

end Gamma1

end ModularForms
