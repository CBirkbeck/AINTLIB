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

/-- Belabas–Friedman eq. (7), first derivative: on `t > 0`,
`d/dt [e^{-ht}/t] = -(h + 1/t)·e^{-ht}/t`. -/
theorem hasDerivAt_gAux_core (h : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => Complex.exp (-h * u) / u)
      (-(h + 1/t) * (Complex.exp (-h * t) / t)) t := by
  have hden_ne : ((t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ht.ne'
  have hnum : HasDerivAt (fun w : ℂ => Complex.exp (-h * w))
      (Complex.exp (-h * (t : ℂ)) * (-h)) (t : ℂ) := by
    have hlin : HasDerivAt (fun w : ℂ => -h * w) (-h) (t : ℂ) := by
      simpa using (hasDerivAt_id ((t : ℝ) : ℂ)).const_mul (-h)
    exact hlin.cexp
  have hdiv := hnum.div (hasDerivAt_id ((t : ℝ) : ℂ)) hden_ne
  have hcomp := hdiv.comp_ofReal
  refine hcomp.congr_deriv ?_
  simp only [id_eq]
  field_simp
  ring

/-- Belabas–Friedman eq. (7), second derivative: on `t > 0`, the derivative of
`-(h+1/t)·e^{-ht}/t` is `(h² + (2ht+2)/t²)·e^{-ht}/t`. -/
theorem hasDerivAt_gAux_deriv (h : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => -(h + 1/u) * (Complex.exp (-h * u) / u))
      ((h^2 + (2*h*t + 2)/t^2) * (Complex.exp (-h * t) / t)) t := by
  have hden_ne : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  -- all-ℂ computation, then compose with ofReal
  have hfac : HasDerivAt (fun w : ℂ => -(h + 1/w)) (1/(t:ℂ)^2) (t : ℂ) := by
    have hinv : HasDerivAt (fun w : ℂ => w⁻¹) (-((t:ℂ)^2)⁻¹) (t : ℂ) :=
      hasDerivAt_inv hden_ne
    have h2 := (hinv.const_add h).neg
    rw [show (-fun w : ℂ => h + w⁻¹) = (fun w : ℂ => -(h + 1/w)) from
      funext (fun w => by simp [one_div])] at h2
    simpa [neg_neg] using h2
  have hnum : HasDerivAt (fun w : ℂ => Complex.exp (-h * w))
      (Complex.exp (-h * (t : ℂ)) * (-h)) (t : ℂ) := by
    have hlin : HasDerivAt (fun w : ℂ => -h * w) (-h) (t : ℂ) := by
      simpa using (hasDerivAt_id ((t : ℝ) : ℂ)).const_mul (-h)
    exact hlin.cexp
  have hg := hnum.div (hasDerivAt_id ((t : ℝ) : ℂ)) hden_ne
  have hprod := hfac.mul hg
  have hcomp := hprod.comp_ofReal
  refine hcomp.congr_deriv ?_
  simp only [Pi.div_apply, id_eq]
  field_simp
  ring

/-- Master decay bound: a continuous multiplier `φ` bounded on `(T, ∞)` times the
kernel `e^{-ht}/t` (with `Re h > 0`, `T > 0`) is integrable on `(T, ∞)`, by comparison
with `(C/T)·e^{-Re h · t}`. -/
theorem integrableOn_bounded_mul_exp_div {h : ℂ} (hh : 0 < h.re) {T : ℝ} (hT : 0 < T)
    {φ : ℝ → ℂ} (hφc : ContinuousOn φ (Set.Ioi T)) {C : ℝ}
    (hφb : ∀ t ∈ Set.Ioi T, ‖φ t‖ ≤ C) :
    IntegrableOn (fun t : ℝ => φ t * (Complex.exp (-h * t) / t)) (Set.Ioi T) := by
  have hg : ContinuousOn (fun t : ℝ => Complex.exp (-h * t) / (t : ℂ)) (Set.Ioi T) := by
    refine ContinuousOn.div ?_ Complex.continuous_ofReal.continuousOn ?_
    · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
    · intro t ht
      exact_mod_cast (hT.trans ht).ne'
  refine Integrable.mono' (g := fun t : ℝ => C / T * Real.exp (-h.re * t))
    ((exp_neg_integrableOn_Ioi T hh).const_mul _)
    ((hφc.mul hg).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htpos : 0 < t := hT.trans ht
  have hnorm : ‖φ t * (Complex.exp (-h * t) / t)‖
      = ‖φ t‖ * (Real.exp (-h.re * t) / t) := by
    rw [norm_mul, norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos]
    congr 2
    simp [Complex.mul_re]
  rw [hnorm]
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hφb t ht)
  have hle : Real.exp (-h.re * t) / t ≤ Real.exp (-h.re * t) / T :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le hT (le_of_lt ht)
  calc ‖φ t‖ * (Real.exp (-h.re * t) / t)
      ≤ C * (Real.exp (-h.re * t) / T) :=
        mul_le_mul (hφb t ht) hle (by positivity) hC0
    _ = C / T * Real.exp (-h.re * t) := by ring

/-- The kernel `e^{-ht}/t` times an eventually-bounded multiplier tends to `0` at `∞`. -/
theorem tendsto_exp_div_mul_atTop {h : ℂ} (hh : 0 < h.re) {v : ℝ → ℂ} {C : ℝ}
    (hv : ∀ᶠ t : ℝ in Filter.atTop, ‖v t‖ ≤ C) :
    Filter.Tendsto (fun t : ℝ => Complex.exp (-h * t) / t * v t) Filter.atTop (nhds 0) := by
  have hexp : Filter.Tendsto (fun t : ℝ => C * Real.exp (-(h.re * t))) Filter.atTop
      (nhds (C * 0)) := by
    refine Filter.Tendsto.const_mul C (Real.tendsto_exp_atBot.comp ?_)
    exact Filter.tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hh Filter.tendsto_id)
  rw [mul_zero] at hexp
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hv] with t ht hvt
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have hnorm : ‖Complex.exp (-h * t) / t * v t‖
      = Real.exp (-h.re * t) / t * ‖v t‖ := by
    rw [norm_mul, norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos]
    congr 2
    simp [Complex.mul_re]
  rw [hnorm, neg_mul]
  have h1 : Real.exp (-(h.re * t)) / t ≤ Real.exp (-(h.re * t)) :=
    div_le_self (Real.exp_pos _).le ht
  have hv0 : 0 ≤ ‖v t‖ := norm_nonneg _
  calc Real.exp (-(h.re * t)) / t * ‖v t‖
      ≤ Real.exp (-(h.re * t)) * C := by
        exact mul_le_mul h1 hvt hv0 (Real.exp_pos _).le
    _ = C * Real.exp (-(h.re * t)) := by ring

/-- First integration by parts for the Fourier tail (Belabas–Friedman, proof of Lemma 2):
with `g(t) = e^{-ht}/t`, `∫_T^∞ (g′(t)·sin(tγ)/γ + g(t)·cos(tγ)) dt = -g(T)·sin(Tγ)/γ`. -/
theorem integral_Ioi_gAux_ibp₁ (h : ℂ) (hh : 0 < h.re) {T γ : ℝ} (hT : 0 < T) (hγ : γ ≠ 0) :
    (∫ t in Set.Ioi T,
        (-(h + 1/t) * (Complex.exp (-h * t) / t) * ((Real.sin (t * γ) / γ : ℝ) : ℂ)
          + Complex.exp (-h * t) / t * ((Real.cos (t * γ) : ℝ) : ℂ)))
      = -(Complex.exp (-h * T) / T * ((Real.sin (T * γ) / γ : ℝ) : ℂ)) := by
  have key := integral_Ioi_deriv_mul_eq_sub
    (u := fun t : ℝ => Complex.exp (-h * t) / t)
    (u' := fun t : ℝ => -(h + 1/t) * (Complex.exp (-h * t) / t))
    (v := fun t : ℝ => ((Real.sin (t * γ) / γ : ℝ) : ℂ))
    (v' := fun t : ℝ => ((Real.cos (t * γ) : ℝ) : ℂ))
    (a := T) (a' := Complex.exp (-h * T) / T * ((Real.sin (T * γ) / γ : ℝ) : ℂ)) (b' := 0)
    (fun t ht => hasDerivAt_gAux_core h (hT.trans ht))
    (fun t _ => by
      have hs : HasDerivAt (fun t : ℝ => Real.sin (t * γ) / γ) (Real.cos (t * γ)) t := by
        have := (((hasDerivAt_id t).mul_const γ).sin).div_const γ
        simpa [mul_div_assoc, mul_div_cancel_right₀ _ hγ] using this
      exact hs.ofReal_comp)
    ?_ ?_ ?_
  · rw [key, zero_sub]
  · -- integrability of u'·v + u·v'
    have h₁ : IntegrableOn
        (fun t : ℝ => (-(h + 1/t) * ((Real.sin (t * γ) / γ : ℝ) : ℂ))
          * (Complex.exp (-h * t) / t)) (Set.Ioi T) := by
      refine integrableOn_bounded_mul_exp_div hh hT ?_
        (C := (‖h‖ + 1/T) * (1/|γ|)) ?_
      · refine ContinuousOn.mul (ContinuousOn.neg ?_)
          (Complex.continuous_ofReal.comp
            (by fun_prop : Continuous fun t : ℝ => Real.sin (t * γ) / γ)).continuousOn
        exact continuousOn_const.add (continuousOn_const.div
          Complex.continuous_ofReal.continuousOn
          (fun t ht => by exact_mod_cast (hT.trans ht).ne'))
      · intro t ht
        rw [norm_mul, norm_neg]
        refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
        · refine le_trans (norm_add_le _ _) ?_
          have : ‖(1 : ℂ)/(t : ℂ)‖ ≤ 1/T := by
            rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (hT.trans ht)]
            gcongr
            exact le_of_lt ht
          linarith
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
          gcongr
          exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have h₂ : IntegrableOn
        (fun t : ℝ => ((Real.cos (t * γ) : ℝ) : ℂ) * (Complex.exp (-h * t) / t))
        (Set.Ioi T) := by
      refine integrableOn_bounded_mul_exp_div hh hT
        (Complex.continuous_ofReal.comp
          (by fun_prop : Continuous fun t : ℝ => Real.cos (t * γ))).continuousOn
        (C := 1) ?_
      intro t _
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have h₁' : IntegrableOn (fun t : ℝ =>
        -(h + 1/t) * (Complex.exp (-h * t) / t) * ((Real.sin (t * γ) / γ : ℝ) : ℂ))
        (Set.Ioi T) := h₁.congr_fun (fun t _ => by ring) measurableSet_Ioi
    have h₂' : IntegrableOn (fun t : ℝ =>
        Complex.exp (-h * t) / t * ((Real.cos (t * γ) : ℝ) : ℂ)) (Set.Ioi T) :=
      h₂.congr_fun (fun t _ => by ring) measurableSet_Ioi
    exact h₁'.add h₂'
  · -- boundary at T
    have hc : ContinuousAt (fun t : ℝ =>
        Complex.exp (-h * t) / t * ((Real.sin (t * γ) / γ : ℝ) : ℂ)) T := by
      have hT0 : ((T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
      fun_prop (disch := intros; exact hT0)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  · -- vanishing at ∞
    refine tendsto_exp_div_mul_atTop hh (C := 1/|γ|) ?_
    filter_upwards with t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
    gcongr
    exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

end

end DedekindResidue
