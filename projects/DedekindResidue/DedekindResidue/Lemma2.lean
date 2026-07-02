module

public import Mathlib
public import DedekindResidue.AuxiliaryFunction
public import DedekindResidue.CompletedZeta.Normalisation

/-!
# Lemma 2: the Fourier transform of the auxiliary function  (T003)

Belabas–Friedman Lemma 2 (eq. 8): the paper-convention Fourier transform (eq. 2,
`F̂(γ) = ∫ F(t)e^{itγ}dt`) of the test function `F_{s,X}` in closed form. This file builds
it bottom-up: the evenness reduction to a cosine transform, the plateau contribution
`2 sin(γT)/γ`, the exponential-tail integration by parts (paper eq. 7), and the assembly.

The main statement is for `γ ≠ 0`; the `sin(γT)/γ` term forces a separate `γ = 0`
companion (the pointwise limit), faithful to the paper's implicit convention.
-/

namespace DedekindResidue

@[expose] public section

open MeasureTheory
open scoped Real


/-- The paper Fourier transform of an even function reduces to a cosine transform on the
positive ray. -/
theorem paperFourierIntegral_even (F : ℝ → ℂ) (hF : ∀ t, F (-t) = F t) (γ : ℝ)
    (hInt : Integrable (fun t : ℝ => F t * Complex.exp (Complex.I * t * γ))) :
    paperFourierIntegral F γ
      = 2 * ∫ t in Set.Ioi (0:ℝ), F t * ((Real.cos (t * γ) : ℝ) : ℂ) := by
  rw [paperFourierIntegral]
  rw [← integral_add_compl (measurableSet_Iic (a := (0:ℝ))) hInt, Set.compl_Iic]
  have hneg : (∫ t in Set.Iic (0:ℝ), F t * Complex.exp (Complex.I * t * γ))
      = ∫ t in Set.Ioi (0:ℝ), F t * Complex.exp (-(Complex.I * t * γ)) := by
    rw [show Set.Iic (0:ℝ) = Set.Iic (-(0:ℝ)) by norm_num]
    rw [← integral_comp_neg_Ioi (f := fun t : ℝ => F t * Complex.exp (Complex.I * t * γ))]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [hF]
    push_cast
    ring_nf
  have hInt' : Integrable (fun t : ℝ => F t * Complex.exp (-(Complex.I * t * γ))) := by
    have h1 := hInt.comp_neg
    refine h1.congr (Filter.Eventually.of_forall (fun t => ?_))
    show F (-t) * Complex.exp (Complex.I * (-t : ℝ) * γ)
      = F t * Complex.exp (-(Complex.I * t * γ))
    rw [hF]
    push_cast
    ring_nf
  rw [hneg, ← integral_add hInt'.integrableOn hInt.integrableOn]
  · rw [show (2 : ℂ) * (∫ t in Set.Ioi (0:ℝ), F t * ((Real.cos (t * γ) : ℝ) : ℂ))
      = ∫ t in Set.Ioi (0:ℝ), 2 * (F t * ((Real.cos (t * γ) : ℝ) : ℂ)) from
      (integral_const_mul 2 _).symm]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf

open scoped Real in
/-- The plateau contribution: `∫_0^T cos(tγ) dt = sin(Tγ)/γ` (`γ ≠ 0`, `T ≥ 0`). -/
theorem integral_plateau_cos {T γ : ℝ} (hT : 0 ≤ T) (hγ : γ ≠ 0) :
    (∫ t in Set.Ioc (0:ℝ) T, ((Real.cos (t * γ) : ℝ) : ℂ))
      = ((Real.sin (T * γ) / γ : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_of_le hT, intervalIntegral.integral_ofReal]
  congr 1
  rw [intervalIntegral.integral_comp_mul_right (fun t => Real.cos t) hγ]
  rw [integral_cos]
  simp [div_eq_inv_mul]

/-- The global exponential bound on the auxiliary function:
`‖F_{s,X}(t)‖ ≤ e^{h_r T}·e^{-h_r|t|}` with `h_r = Re s − 1/2 ≥ 0`, `T = log X ≥ 0`. -/
theorem norm_auxF_le (s : ℂ) {X : ℝ} (hX : 1 ≤ X) (hs : 1/2 ≤ s.re) (t : ℝ) :
    ‖auxF s X t‖ ≤ Real.exp ((s.re - 1/2) * Real.log X)
      * Real.exp (-(s.re - 1/2) * |t|) := by
  have hT : 0 ≤ Real.log X := Real.log_nonneg hX
  have hr : 0 ≤ s.re - 1/2 := by linarith
  rw [auxF]
  split_ifs with h
  · -- plateau: ‖1‖ = 1 ≤ e^{h_r(T − |t|)}
    rw [norm_one, ← Real.exp_add]
    refine Real.one_le_exp ?_
    have : (s.re - 1/2) * Real.log X + -(s.re - 1/2) * |t|
        = (s.re - 1/2) * (Real.log X - |t|) := by ring
    rw [this]
    exact mul_nonneg hr (by linarith)
  · -- tail: (T/|t|)·e^{-h_r(|t|−T)} ≤ e^{h_r T}e^{-h_r|t|}
    push Not at h
    have ht0 : (0:ℝ) < |t| := lt_of_le_of_lt hT h
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    have hre : (-(s - 1/2) * Complex.ofReal (|t| - Real.log X)).re
        = -(s.re - 1/2) * (|t| - Real.log X) := by
      simp [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre]
    have habs : |Real.log X / (abs t)| = Real.log X / (abs t) :=
      abs_of_nonneg (div_nonneg hT ht0.le)
    rw [Real.norm_eq_abs, habs, ← Real.exp_add]
    have hdivle : Real.log X / |t| ≤ 1 := by
      rw [div_le_one ht0]
      exact h.le
    calc Real.log X / |t| * Real.exp (-(s.re - 1/2) * (|t| - Real.log X))
        ≤ 1 * Real.exp (-(s.re - 1/2) * (|t| - Real.log X)) :=
          mul_le_mul_of_nonneg_right hdivle (Real.exp_pos _).le
      _ = Real.exp (-(s.re - 1/2) * (|t| - Real.log X)) := one_mul _
      _ = Real.exp ((s.re - 1/2) * Real.log X + -(s.re - 1/2) * |t|) := by
          congr 1
          ring

/-- Two-sided exponential decay is integrable on the line. -/
theorem integrable_exp_neg_mul_abs {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * |t|)) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hb).congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [abs_of_pos ht]
  have h1' : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr h1
  have hmap : Measure.map (MeasurableEquiv.neg ℝ) (volume.restrict (Set.Ici (0:ℝ)))
      = volume.restrict (Set.Iic 0) := by
    rw [show Set.Ici (0:ℝ) = (MeasurableEquiv.neg ℝ) ⁻¹' (Set.Iic 0) by
      ext t
      simp [MeasurableEquiv.neg_apply]]
    rw [← Measure.restrict_map (MeasurableEquiv.neg ℝ).measurable measurableSet_Iic]
    congr 1
    exact Measure.map_neg_eq_self (volume : Measure ℝ)
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-b * |t|)) (Set.Iic 0) := by
    rw [IntegrableOn, ← hmap, integrable_map_equiv]
    refine h1'.congr (Filter.Eventually.of_forall (fun t => ?_))
    show Real.exp (-b * |t|) = Real.exp (-b * |(-t : ℝ)|)
    rw [abs_neg]
  have hunion := h2.union h1
  rw [Set.Iic_union_Ioi] at hunion
  rwa [← integrableOn_univ]

/-- The paper Fourier kernel against `F_{s,X}` is integrable on the line
(`Re s > 1/2`, `X ≥ 1`). -/
theorem integrable_auxF_kernel (s : ℂ) {X : ℝ} (hX : 1 ≤ X) (hs : 1/2 < s.re) (γ : ℝ) :
    Integrable (fun t : ℝ => auxF s X t * Complex.exp (Complex.I * t * γ)) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs (b := s.re - 1/2) (by linarith)).const_mul
      (Real.exp ((s.re - 1/2) * Real.log X)))
    (((measurable_auxF s X).mul (by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun t => ?_))
  rw [norm_mul]
  have hker : ‖Complex.exp (Complex.I * t * γ)‖ = 1 := by
    rw [Complex.norm_exp]
    have : (Complex.I * t * γ).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [this, Real.exp_zero]
  rw [hker, mul_one]
  exact norm_auxF_le s hX (le_of_lt hs) t

end

end DedekindResidue
