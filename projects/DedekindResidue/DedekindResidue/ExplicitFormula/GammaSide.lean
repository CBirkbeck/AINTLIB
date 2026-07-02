module

public import DedekindResidue.ExplicitFormula.FourierJordan

/-!
# The archimedean side: digamma integrals (SP2-Γψ)

Poitou's computation of the archimedean part of the explicit formula (Poitou, *Sur les
petits discriminants*, exposé 6, pp. 6-03–6-06) rests on **Gauss's integral formula**
(his eq. (5))

`ψ(z) = -∫₀^∞ (e^{-xz}/(1-e^{-x}) - e^{-x}/x) dx`,   `Re z > 0`,

and its consequences for `Re ψ` on vertical lines. Mathlib defines `Complex.digamma`
(as `logDeriv Gamma`) but has no integral representation (explicit TODO in
`Mathlib.Analysis.SpecialFunctions.Gamma.Digamma`), so this file builds it from the
Euler integral: `Γ'(z) = ∫₀^∞ t^{z-1}e^{-t} log t dt` (mathlib's
`hasDerivAt_GammaIntegral`), the Frullani representation of `log`, and Fubini — the
classical Gauss derivation.

## Main results

- `integral_frullani_log` : `∫₀^∞ (e^{-x} - e^{-tx})/x dx = log t` for `t > 0`.
- `integrableOn_rpow_mul_exp_neg_mul_abs_log` : the log-weighted Euler integrand is
  integrable.
- `abs_frullani_kernel_le` : exponential domination of the Frullani kernel.
- `integral_gauss_inner` : the inner evaluation
  `∫₀^∞ t^{z-1}e^{-t}(e^{-x}-e^{-tx})/x dt = Γ(z)(e^{-x} - (1+x)^{-z})/x`.
- `digamma_eq_integral_gauss_one` : **Gauss's first form**
  `ψ(z) = ∫₀^∞ (e^{-x} - (1+x)^{-z})/x dx` for `Re z > 0`.
- `integrableOn_gauss_one_integrand` : integrability of that integrand.
- `digamma_sub_digamma_eq_integral` : **Poitou's difference form**
  `ψ(w) - ψ(σ) = ∫₀^∞ (e^{-σu} - e^{-wu})/(1-e^{-u}) du` (`x = e^u - 1`), the form his
  eq. (5) is used in — both counterterms cancel in the difference.
-/

@[expose] public section


namespace DedekindResidue

open MeasureTheory Complex intervalIntegral Real Filter SchwartzMap
open scoped FourierTransform ContDiff ComplexConjugate InnerProductSpace ENNReal

/-- **Frullani integral for the logarithm** (Γψ-c1): for `t > 0`,
`∫₀^∞ (e^{-x} - e^{-tx})/x dx = log t`. The kernel is `∫_1^t e^{-sx} ds`; Fubini and
`∫₀^∞ e^{-sx} dx = 1/s` reduce it to `∫_1^t ds/s`. -/
theorem integral_frullani_log {t : ℝ} (ht : 0 < t) :
    ∫ x in Set.Ioi (0:ℝ), (Real.exp (-x) - Real.exp (-(t*x))) / x = Real.log t := by
  -- the kernel identity: for x > 0
  have hker : ∀ x : ℝ, 0 < x →
      (Real.exp (-x) - Real.exp (-(t*x))) / x = ∫ s in (1:ℝ)..t, Real.exp (-(s*x)) := by
    intro x hx
    have hprim : ∀ s : ℝ, HasDerivAt (fun s' : ℝ => -Real.exp (-(s'*x)) / x)
        (Real.exp (-(s*x))) s := by
      intro s
      have h0 : HasDerivAt (fun s' : ℝ => s' * x) x s := by
        simpa using (hasDerivAt_id s).mul_const x
      have h1 : HasDerivAt (fun s' : ℝ => -(s' * x)) (-x) s := h0.neg
      have h2 := h1.exp
      have h3 : HasDerivAt (fun s' : ℝ => -Real.exp (-(s'*x)))
          (-(Real.exp (-(s*x)) * -x)) s := h2.neg
      have h4 := h3.div_const x
      have hval : -(Real.exp (-(s*x)) * -x) / x = Real.exp (-(s*x)) := by
        rw [div_eq_iff hx.ne']
        ring
      rw [hval] at h4
      exact h4
    have hint : IntervalIntegrable (fun s : ℝ => Real.exp (-(s*x))) volume 1 t := by
      refine ContinuousOn.intervalIntegrable ?_
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hprim s) hint]
    field_simp
    ring
  -- Fubini on a positive window: ∫_x ∫_{s ∈ Ioc a b} e^{-sx} = ∫_{Ioc a b} 1/s
  have haux : ∀ a b : ℝ, 0 < a → a ≤ b →
      (∫ x in Set.Ioi (0:ℝ), ∫ s in Set.Ioc a b, Real.exp (-(s*x)))
        = ∫ s in Set.Ioc a b, 1/s := by
    intro a b ha hab
    have hmeasp : AEStronglyMeasurable (Function.uncurry fun x s : ℝ => Real.exp (-(s*x)))
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioc a b))) := by
      refine Continuous.aestronglyMeasurable ?_
      have : (Function.uncurry fun x s : ℝ => Real.exp (-(s*x)))
          = fun p : ℝ × ℝ => Real.exp (-(p.2 * p.1)) := by
        funext p
        rw [Function.uncurry]
      rw [this]
      fun_prop
    have hprod : Integrable (Function.uncurry fun x s : ℝ => Real.exp (-(s*x)))
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioc a b))) := by
      have hdom : Integrable (fun p : ℝ × ℝ => Real.exp (-(a * p.1)) * 1)
          ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioc a b))) := by
        refine MeasureTheory.Integrable.mul_prod
          (f := fun x : ℝ => Real.exp (-(a*x))) (g := fun _ : ℝ => (1:ℝ)) ?_ ?_
        · have := exp_neg_integrableOn_Ioi (0:ℝ) ha
          refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
          show Real.exp (-a * x) = Real.exp (-(a*x))
          rw [show -a * x = -(a*x) by ring]
        · exact MeasureTheory.integrableOn_const (by
            rw [Real.volume_Ioc]
            exact ENNReal.ofReal_ne_top)
      refine hdom.mono' hmeasp ?_
      rw [Measure.prod_restrict]
      refine (MeasureTheory.ae_restrict_iff'
        (measurableSet_Ioi.prod measurableSet_Ioc)).mpr ?_
      refine Filter.Eventually.of_forall (fun p hp => ?_)
      have hx : 0 < p.1 := hp.1
      have hs : a ≤ p.2 := hp.2.1.le
      show ‖Real.exp (-(p.2 * p.1))‖ ≤ Real.exp (-(a * p.1)) * 1
      rw [Real.norm_eq_abs, Real.abs_exp, mul_one]
      refine Real.exp_le_exp.mpr ?_
      rw [neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_right hs hx.le
    have hswap := MeasureTheory.integral_integral_swap hprod
    rw [hswap]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    have hspos : 0 < s := lt_trans ha hs.1
    exact integral_exp_neg_mul_Ioi hspos
  rcases le_or_gt 1 t with h1t | h1t
  · have h0 : (∫ x in Set.Ioi (0:ℝ), (Real.exp (-x) - Real.exp (-(t*x))) / x)
        = ∫ x in Set.Ioi (0:ℝ), ∫ s in Set.Ioc (1:ℝ) t, Real.exp (-(s*x)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [Set.mem_Ioi] at hx
      rw [hker x hx, intervalIntegral.integral_of_le h1t]
    rw [h0, haux 1 t one_pos h1t]
    have h2 : (∫ s in Set.Ioc (1:ℝ) t, 1/s) = ∫ s in (1:ℝ)..t, 1/s := by
      rw [intervalIntegral.integral_of_le h1t]
    rw [h2, integral_one_div (by
      intro h
      rw [Set.mem_uIcc] at h
      rcases h with ⟨h', _⟩ | ⟨_, h'⟩ <;> linarith), div_one]
  · have h0 : (∫ x in Set.Ioi (0:ℝ), (Real.exp (-x) - Real.exp (-(t*x))) / x)
        = ∫ x in Set.Ioi (0:ℝ), -∫ s in Set.Ioc t 1, Real.exp (-(s*x)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [Set.mem_Ioi] at hx
      rw [hker x hx, intervalIntegral.integral_symm,
        intervalIntegral.integral_of_le h1t.le]
    rw [h0, MeasureTheory.integral_neg, haux t 1 ht h1t.le]
    have h2 : (∫ s in Set.Ioc t (1:ℝ), 1/s) = ∫ s in t..(1:ℝ), 1/s := by
      rw [intervalIntegral.integral_of_le h1t.le]
    rw [h2, integral_one_div (by
      intro h
      rw [Set.mem_uIcc] at h
      rcases h with ⟨h', _⟩ | ⟨_, h'⟩ <;> linarith)]
    rw [one_div, Real.log_inv, neg_neg]

/-- The log-weighted Gamma integrand is integrable: `∫₀^∞ t^{a-1} e^{-t} |log t| dt < ∞`
for `a > 0` (Γψ-c2b). Near `0` the log loses to `t^{a/2}`; at infinity `log t ≤ t`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_abs_log {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (a-1) * Real.exp (-t) * |Real.log t|)
      (Set.Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => t ^ (a-1) * Real.exp (-t) * |Real.log t|)
      (volume.restrict (Set.Ioi 0)) := by
    refine Measurable.aestronglyMeasurable ?_ |>.restrict
    fun_prop
  refine MeasureTheory.Integrable.mono'
    (g := fun t => (2/a) * (Real.exp (-t) * t ^ (a/2 - 1))
      + Real.exp (-t) * t ^ ((a+1) - 1))
    (((Real.GammaIntegral_convergent (by positivity : (0:ℝ) < a/2)).const_mul
        (2/a)).add
      (Real.GammaIntegral_convergent (by positivity : (0:ℝ) < a+1)))
    hmeas ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  rw [Set.mem_Ioi] at ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases le_or_gt t 1 with h1 | h1
  · -- near 0: |log t| = -log t ≤ (2/a) t^{-a/2}
    have hlog : |Real.log t| ≤ (2/a) * t ^ (-(a/2)) := by
      rw [abs_of_nonpos (Real.log_nonpos ht.le h1)]
      have h2 : Real.log (t ^ (-(a/2))) ≤ t ^ (-(a/2)) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_rpow ht] at h2
      have h3 : -Real.log t = (2/a) * (-(a/2) * Real.log t) := by
        field_simp
      rw [h3]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith [Real.rpow_nonneg ht.le (-(a/2))]
    calc t ^ (a-1) * Real.exp (-t) * |Real.log t|
        ≤ t ^ (a-1) * Real.exp (-t) * ((2/a) * t ^ (-(a/2))) := by
          refine mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (2/a) * (Real.exp (-t) * (t ^ (a-1) * t ^ (-(a/2)))) := by ring
      _ = (2/a) * (Real.exp (-t) * t ^ (a/2 - 1)) := by
          rw [← Real.rpow_add ht]
          ring_nf
      _ ≤ (2/a) * (Real.exp (-t) * t ^ (a/2 - 1))
          + Real.exp (-t) * t ^ ((a+1) - 1) := by
          have : (0:ℝ) ≤ Real.exp (-t) * t ^ ((a+1) - 1) := by positivity
          linarith
  · -- tail: |log t| = log t ≤ t
    have hlog : |Real.log t| ≤ t := by
      rw [abs_of_nonneg (Real.log_nonneg h1.le)]
      have := Real.log_le_sub_one_of_pos ht
      linarith
    calc t ^ (a-1) * Real.exp (-t) * |Real.log t|
        ≤ t ^ (a-1) * Real.exp (-t) * t := by
          refine mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = Real.exp (-t) * (t ^ (a-1) * t ^ (1:ℝ)) := by
          rw [Real.rpow_one]
          ring
      _ = Real.exp (-t) * t ^ ((a+1) - 1) := by
          rw [← Real.rpow_add ht]
          ring_nf
      _ ≤ (2/a) * (Real.exp (-t) * t ^ (a/2 - 1))
          + Real.exp (-t) * t ^ ((a+1) - 1) := by
          have : (0:ℝ) ≤ (2/a) * (Real.exp (-t) * t ^ (a/2 - 1)) := by positivity
          linarith

/-- The Frullani kernel is dominated exponentially: `|(e^{-x} - e^{-tx})/x| ≤ |t-1| e^{-mx}`
with `m = min 1 t`, hence integrable on `(0, ∞)` for each `t > 0` (Γψ-c2 slice bound). -/
theorem abs_frullani_kernel_le (t : ℝ) {x : ℝ} (hx : 0 < x) :
    |(Real.exp (-x) - Real.exp (-(t*x))) / x| ≤ |t - 1| * Real.exp (-(min 1 t * x)) := by
  have hker : (Real.exp (-x) - Real.exp (-(t*x))) / x = ∫ s in (1:ℝ)..t, Real.exp (-(s*x)) := by
    have hprim : ∀ s : ℝ, HasDerivAt (fun s' : ℝ => -Real.exp (-(s'*x)) / x)
        (Real.exp (-(s*x))) s := by
      intro s
      have h0 : HasDerivAt (fun s' : ℝ => s' * x) x s := by
        simpa using (hasDerivAt_id s).mul_const x
      have h1 : HasDerivAt (fun s' : ℝ => -(s' * x)) (-x) s := h0.neg
      have h2 := h1.exp
      have h3 : HasDerivAt (fun s' : ℝ => -Real.exp (-(s'*x)))
          (-(Real.exp (-(s*x)) * -x)) s := h2.neg
      have h4 := h3.div_const x
      have hval : -(Real.exp (-(s*x)) * -x) / x = Real.exp (-(s*x)) := by
        rw [div_eq_iff hx.ne']
        ring
      rw [hval] at h4
      exact h4
    have hint : IntervalIntegrable (fun s : ℝ => Real.exp (-(s*x))) volume 1 t := by
      refine ContinuousOn.intervalIntegrable ?_
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hprim s) hint]
    field_simp
    ring
  rw [hker]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Real.exp (-(min 1 t * x))) (a := (1:ℝ)) (b := t)
    (f := fun s : ℝ => Real.exp (-(s*x)))
    (fun s hs => by
      rw [Real.norm_eq_abs, Real.abs_exp]
      refine Real.exp_le_exp.mpr ?_
      rw [neg_le_neg_iff]
      refine mul_le_mul_of_nonneg_right ?_ hx.le
      rw [Set.mem_uIoc] at hs
      rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact le_trans (min_le_left _ _) h1.le
      · exact le_trans (min_le_right _ _) h1.le)
  rw [Real.norm_eq_abs] at hbound
  calc |∫ s in (1:ℝ)..t, Real.exp (-(s*x))|
      ≤ Real.exp (-(min 1 t * x)) * |t - 1| := hbound
    _ = |t - 1| * Real.exp (-(min 1 t * x)) := mul_comm _ _

/-- Inner evaluation of the Gauss double integral (Γψ-c2, fixed `x > 0`):
`∫₀^∞ t^{z-1} e^{-t} (e^{-x} - e^{-tx})/x dt = Γ(z)·(e^{-x} - (1+x)^{-z})/x`. -/
theorem integral_gauss_inner {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1)
        * ((Real.exp (-t) * ((Real.exp (-x) - Real.exp (-(t*x))) / x) : ℝ) : ℂ))
      = Complex.Gamma z * ((((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)) / (x:ℂ)) := by
  -- the two Gamma-type integrals
  have hint1 : IntegrableOn (fun t : ℝ => (t:ℂ) ^ (z-1) * ((Real.exp (-t) : ℝ) : ℂ))
      (Set.Ioi 0) := by
    have h0 := Complex.GammaIntegral_convergent hz
    refine h0.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [mul_comm]
  have hcont_cpow : ContinuousOn (fun t : ℝ => (t:ℂ) ^ (z-1)) (Set.Ioi 0) := by
    refine continuousOn_of_forall_continuousAt (fun t ht => ?_)
    have h0 : ContinuousAt (fun w : ℂ => w ^ (z - 1)) (t:ℂ) :=
      continuousAt_cpow_const <| Complex.ofReal_mem_slitPlane.2 ht
    exact ContinuousAt.comp h0 Complex.continuous_ofReal.continuousAt
  have hint2 : IntegrableOn
      (fun t : ℝ => (t:ℂ) ^ (z-1) * ((Real.exp (-((1+x)*t)) : ℝ) : ℂ)) (Set.Ioi 0) := by
    have h0 := Complex.GammaIntegral_convergent hz
    refine MeasureTheory.Integrable.mono' (h0.norm) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.mul hcont_cpow ?_
      exact (Complex.continuous_ofReal.comp (by fun_prop)).continuousOn
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [Set.mem_Ioi] at ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
      calc ‖(t:ℂ) ^ (z-1)‖ * Real.exp (-((1+x)*t))
          ≤ ‖(t:ℂ) ^ (z-1)‖ * Real.exp (-t) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine Real.exp_le_exp.mpr ?_
            nlinarith
        _ = Real.exp (-t) * ‖(t:ℂ) ^ (z-1)‖ := mul_comm _ _
  -- expand the kernel and split
  have hsplit : (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1)
      * ((Real.exp (-t) * ((Real.exp (-x) - Real.exp (-(t*x))) / x) : ℝ) : ℂ))
      = (((Real.exp (-x) : ℝ) : ℂ) / (x:ℂ))
          * (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1) * ((Real.exp (-t) : ℝ) : ℂ))
        - ((1:ℂ) / (x:ℂ))
          * ∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1) * ((Real.exp (-((1+x)*t)) : ℝ) : ℂ) := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_sub ((hint1.const_mul _)) ((hint2.const_mul _))]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [Set.mem_Ioi] at ht
    have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    push_cast
    rw [show -((1+(x:ℂ))*(t:ℂ)) = -(t:ℂ) + -((t:ℂ)*(x:ℂ)) by ring, Complex.exp_add]
    field_simp
  rw [hsplit]
  -- evaluate both integrals
  have hval1 : (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1) * ((Real.exp (-t) : ℝ) : ℂ))
      = Complex.Gamma z := by
    rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [mul_comm]
  have hval2 : (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1) * ((Real.exp (-((1+x)*t)) : ℝ) : ℂ))
      = ((1+x : ℝ) : ℂ) ^ (-z) * Complex.Gamma z := by
    have h0 := Complex.integral_cpow_mul_exp_neg_mul_Ioi hz (by linarith : (0:ℝ) < 1+x)
    have h1 : (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1) * ((Real.exp (-((1+x)*t)) : ℝ) : ℂ))
        = ∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z-1) * Complex.exp (-(((1+x:ℝ):ℂ) * (t:ℂ))) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      congr 1
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [h1, h0]
    have harg : ((1+x : ℝ) : ℂ).arg ≠ π := by
      rw [Complex.arg_ofReal_of_nonneg (by linarith)]
      exact Real.pi_ne_zero.symm
    rw [one_div, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  rw [hval1, hval2]
  ring

/-- **Gauss's first integral for the digamma function** (Γψ-c2): for `Re z > 0`,
`ψ(z) = ∫₀^∞ (e^{-x} - (1+x)^{-z})/x dx`. Obtained from `Γ'(z) = ∫ t^{z-1}e^{-t} log t dt`
by writing `log t` as a Frullani integral and applying Fubini. -/
theorem digamma_eq_integral_gauss_one {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z = ∫ x in Set.Ioi (0:ℝ),
      (((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)) / (x:ℂ) := by
  -- Γ' as the log-weighted Euler integral
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : Complex.Gamma =ᶠ[nhds z] Complex.GammaIntegral := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact Complex.Gamma_eq_integral hw
  have hd : HasDerivAt Complex.Gamma
      (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z - 1)
        * (((Real.log t : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))) z :=
    (Complex.hasDerivAt_GammaIntegral hz).congr_of_eventuallyEq hev
  -- continuity of the double integrand on the open quadrant
  have hcont_cpow : ContinuousOn (fun t : ℝ => (t:ℂ) ^ (z-1)) (Set.Ioi 0) := by
    refine continuousOn_of_forall_continuousAt (fun t ht => ?_)
    have h0 : ContinuousAt (fun w : ℂ => w ^ (z - 1)) (t:ℂ) :=
      continuousAt_cpow_const <| Complex.ofReal_mem_slitPlane.2 ht
    exact ContinuousAt.comp h0 Complex.continuous_ofReal.continuousAt
  set F : ℝ × ℝ → ℂ := fun p => (p.1:ℂ) ^ (z-1)
      * ((Real.exp (-p.1) * ((Real.exp (-p.2) - Real.exp (-(p.1*p.2))) / p.2) : ℝ) : ℂ)
    with hF
  have hcontF : ContinuousOn F ((Set.Ioi 0) ×ˢ (Set.Ioi 0)) := by
    refine ContinuousOn.mul ?_ ?_
    · exact hcont_cpow.comp continuous_fst.continuousOn (fun p hp => hp.1)
    · refine Complex.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.mul (by fun_prop) ?_
      refine ContinuousOn.div (by fun_prop) continuous_snd.continuousOn ?_
      exact fun p hp => (hp.2 : (0:ℝ) < p.2).ne'
  have hmeasF : AEStronglyMeasurable (Function.uncurry fun t x : ℝ => F (t, x))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    rw [Measure.prod_restrict]
    have huncurry : (Function.uncurry fun t x : ℝ => F (t, x)) = F := by
      funext p
      rw [Function.uncurry]
    rw [huncurry]
    exact hcontF.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  -- pointwise |K|-integral: exactly |log t|
  have hKabs : ∀ t : ℝ, 0 < t →
      (∫ x in Set.Ioi (0:ℝ), |(Real.exp (-x) - Real.exp (-(t*x))) / x|)
        = |Real.log t| := by
    intro t ht
    rcases le_or_gt 1 t with h1t | h1t
    · have hpos : ∀ x ∈ Set.Ioi (0:ℝ),
          |(Real.exp (-x) - Real.exp (-(t*x))) / x|
            = (Real.exp (-x) - Real.exp (-(t*x))) / x := by
        intro x hx
        rw [Set.mem_Ioi] at hx
        refine abs_of_nonneg ?_
        refine div_nonneg ?_ hx.le
        have : t * x ≥ x := by nlinarith
        have := Real.exp_le_exp.mpr (neg_le_neg this)
        linarith
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpos,
        integral_frullani_log ht, abs_of_nonneg (Real.log_nonneg h1t)]
    · have hneg : ∀ x ∈ Set.Ioi (0:ℝ),
          |(Real.exp (-x) - Real.exp (-(t*x))) / x|
            = -((Real.exp (-x) - Real.exp (-(t*x))) / x) := by
        intro x hx
        rw [Set.mem_Ioi] at hx
        refine abs_of_nonpos ?_
        refine div_nonpos_of_nonpos_of_nonneg ?_ hx.le
        have : t * x ≤ x := by nlinarith
        have := Real.exp_le_exp.mpr (neg_le_neg this)
        linarith
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hneg,
        MeasureTheory.integral_neg, integral_frullani_log ht,
        abs_of_nonpos (Real.log_nonpos ht.le h1t.le)]
  -- product integrability
  have hprodF : Integrable (Function.uncurry fun t x : ℝ => F (t, x))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    refine (MeasureTheory.integrable_prod_iff hmeasF).mpr ⟨?_, ?_⟩
    · -- slices in x, for a.e. t
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [Set.mem_Ioi] at ht
      simp only [Function.uncurry_apply_pair]
      have hm : 0 < min 1 t := lt_min one_pos ht
      refine MeasureTheory.Integrable.mono'
        (g := fun x => ‖(t:ℂ) ^ (z-1)‖ * Real.exp (-t)
          * (|t - 1| * Real.exp (-(min 1 t * x)))) ?_ ?_ ?_
      · have h0 : IntegrableOn (fun x : ℝ => Real.exp (-(min 1 t * x))) (Set.Ioi 0) := by
          have := exp_neg_integrableOn_Ioi (0:ℝ) hm
          refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
          show Real.exp (-(min 1 t) * x) = Real.exp (-(min 1 t * x))
          rw [show -(min 1 t) * x = -(min 1 t * x) by ring]
        have h1 := (h0.const_mul (|t - 1|)).const_mul (‖(t:ℂ) ^ (z-1)‖ * Real.exp (-t))
        refine h1.congr (Filter.Eventually.of_forall (fun x => ?_))
        ring
      · have hFy : (fun y => F (t, y))
            = fun y => ((t:ℂ)^(z-1))
              * ((Real.exp (-t) * ((Real.exp (-y) - Real.exp (-(t*y))) / y) : ℝ) : ℂ) := by
          funext y
          rw [hF]
        rw [hFy]
        refine (Measurable.aestronglyMeasurable ?_).restrict
        exact (Complex.measurable_ofReal.comp (by fun_prop)).const_mul _
      · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        rw [Set.mem_Ioi] at hx
        rw [hF]
        simp only
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp]
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact abs_frullani_kernel_le t hx
    · -- the norm-outer function equals t^{a-1} e^{-t} |log t|
      have hcongr : ∀ t ∈ Set.Ioi (0:ℝ),
          (∫ x, ‖(Function.uncurry fun t x : ℝ => F (t, x)) (t, x)‖
            ∂(volume.restrict (Set.Ioi 0)))
          = t ^ (z.re - 1) * Real.exp (-t) * |Real.log t| := by
        intro t ht
        rw [Set.mem_Ioi] at ht
        have h0 : ∀ x ∈ Set.Ioi (0:ℝ),
            ‖(Function.uncurry fun t x : ℝ => F (t, x)) (t, x)‖
              = (t ^ (z.re - 1) * Real.exp (-t))
                * |(Real.exp (-x) - Real.exp (-(t*x))) / x| := by
          intro x hx
          simp only [Function.uncurry_apply_pair]
          rw [hF]
          simp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Real.abs_exp,
            Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
          ring
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h0,
          MeasureTheory.integral_const_mul, hKabs t ht]
      have hbase := integrableOn_rpow_mul_exp_neg_mul_abs_log (a := z.re) hz
      refine hbase.congr ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      exact (hcongr t ht).symm
  -- Γ' as the double integral
  have hlog_inner : ∀ t ∈ Set.Ioi (0:ℝ),
      (t:ℂ) ^ (z - 1) * (((Real.log t : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ))
        = ∫ x in Set.Ioi (0:ℝ), F (t, x) := by
    intro t ht
    rw [Set.mem_Ioi] at ht
    rw [← integral_frullani_log ht]
    rw [show ((∫ x in Set.Ioi (0:ℝ), (Real.exp (-x) - Real.exp (-(t*x))) / x : ℝ) : ℂ)
        = ∫ x in Set.Ioi (0:ℝ), (((Real.exp (-x) - Real.exp (-(t*x))) / x : ℝ) : ℂ) from
      integral_complex_ofReal.symm]
    rw [show (t:ℂ) ^ (z - 1)
        * ((∫ x in Set.Ioi (0:ℝ), (((Real.exp (-x) - Real.exp (-(t*x))) / x : ℝ) : ℂ))
          * ((Real.exp (-t) : ℝ) : ℂ))
        = ((t:ℂ) ^ (z - 1) * ((Real.exp (-t) : ℝ) : ℂ))
          * ∫ x in Set.Ioi (0:ℝ), (((Real.exp (-x) - Real.exp (-(t*x))) / x : ℝ) : ℂ)
      from by ring]
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [hF]
    simp only
    push_cast
    ring
  have hΓ' : (∫ t : ℝ in Set.Ioi 0, (t:ℂ) ^ (z - 1)
      * (((Real.log t : ℝ) : ℂ) * ((Real.exp (-t) : ℝ) : ℂ)))
      = ∫ t in Set.Ioi (0:ℝ), ∫ x in Set.Ioi (0:ℝ), F (t, x) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hlog_inner
  have hswap := MeasureTheory.integral_integral_swap hprodF
  have hswap' : (∫ t in Set.Ioi (0:ℝ), ∫ x in Set.Ioi (0:ℝ), F (t, x))
      = ∫ x in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ), F (t, x) := hswap
  -- inner evaluation
  have hinner_eval : ∀ x ∈ Set.Ioi (0:ℝ), (∫ t in Set.Ioi (0:ℝ), F (t, x))
      = Complex.Gamma z
        * ((((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)) / (x:ℂ)) := by
    intro x hx
    rw [Set.mem_Ioi] at hx
    rw [← integral_gauss_inner hz hx]
  have hΓne : Complex.Gamma z ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun m => ?_)
    intro h
    rw [h] at hz
    simp only [Complex.neg_re, Complex.natCast_re] at hz
    have h2 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [Complex.digamma_def, logDeriv_apply, hd.deriv, hΓ', hswap',
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hinner_eval,
    MeasureTheory.integral_const_mul, mul_comm, mul_div_assoc, div_self hΓne, mul_one]

/-- The Gauss integrand `(e^{-x} - (1+x)^{-z})/x` is integrable on `(0, ∞)` for
`Re z > 0`: bounded near `0` (the singularities cancel to first order) and dominated by
`e^{-x}/x₀ + x^{-(1+Re z)}` in the tail. -/
theorem integrableOn_gauss_one_integrand {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn
      (fun x : ℝ => (((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)) / (x:ℂ))
      (Set.Ioi 0) := by
  set x₀ : ℝ := min 1 (1/(‖z‖+1)) with hx₀
  have hx₀pos : 0 < x₀ := lt_min one_pos (by positivity)
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)) / (x:ℂ))
      (volume.restrict (Set.Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div ?_ (Complex.continuous_ofReal.continuousOn) ?_
    · refine ContinuousOn.sub ?_ ?_
      · exact (Complex.continuous_ofReal.comp (by fun_prop)).continuousOn
      · refine continuousOn_of_forall_continuousAt (fun x hx => ?_)
        rw [Set.mem_Ioi] at hx
        have h0 : ContinuousAt (fun w : ℂ => w ^ (-z)) ((1+x : ℝ):ℂ) :=
          continuousAt_cpow_const <| Complex.ofReal_mem_slitPlane.2 (by linarith)
        have hinner : ContinuousAt (fun x : ℝ => ((1+x : ℝ) : ℂ)) x := by fun_prop
        exact ContinuousAt.comp (x := x) h0 hinner
    · intro x hx
      rw [Set.mem_Ioi] at hx
      exact_mod_cast hx.ne'
  rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 x₀ ∪ Set.Ioi x₀ by
    rw [Set.Ioc_union_Ioi_eq_Ioi hx₀pos.le], MeasureTheory.integrableOn_union]
  constructor
  · -- near 0: bounded by 1 + 2‖z‖
    refine MeasureTheory.Integrable.mono'
      (g := fun _ => 1 + 2*‖z‖)
      (MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top))
      (hmeas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl)) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    obtain ⟨hx0, hxle⟩ := hx
    have hlog_le : Real.log (1+x) ≤ x := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1+x)
      linarith
    have hlog_nonneg : 0 ≤ Real.log (1+x) := Real.log_nonneg (by linarith)
    have hznorm : ‖-z * (Real.log (1+x) : ℂ)‖ ≤ 1 := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hlog_nonneg]
      have h1 : Real.log (1+x) ≤ 1/(‖z‖+1) := by
        calc Real.log (1+x) ≤ x := hlog_le
          _ ≤ x₀ := hxle
          _ ≤ 1/(‖z‖+1) := min_le_right _ _
      calc ‖z‖ * Real.log (1+x) ≤ ‖z‖ * (1/(‖z‖+1)) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]
            linarith
    have hcpow_exp : ((1+x : ℝ) : ℂ) ^ (-z)
        = Complex.exp (-z * (Real.log (1+x) : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (by
        exact_mod_cast (by linarith : (0:ℝ) < 1+x).ne'),
        ← Complex.ofReal_log (by linarith : (0:ℝ) ≤ 1+x)]
      ring_nf
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    rw [div_le_iff₀ hx0]
    have htri : ‖((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖
        ≤ ‖((Real.exp (-x) : ℝ) : ℂ) - 1‖ + ‖(1:ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖ := by
      calc ‖((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖
          = ‖(((Real.exp (-x) : ℝ) : ℂ) - 1) + ((1:ℂ) - ((1+x : ℝ) : ℂ) ^ (-z))‖ := by
            ring_nf
        _ ≤ _ := norm_add_le _ _
    have h1 : ‖((Real.exp (-x) : ℝ) : ℂ) - 1‖ ≤ x := by
      rw [show ((Real.exp (-x) : ℝ) : ℂ) - 1 = ((Real.exp (-x) - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by
          have := Real.exp_le_one_iff.mpr (by linarith : -x ≤ 0)
          linarith)]
      have := Real.add_one_le_exp (-x)
      linarith
    have h2 : ‖(1:ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖ ≤ 2*‖z‖*x := by
      rw [hcpow_exp, ← norm_neg]
      have h3 := Complex.norm_exp_sub_one_le hznorm
      calc ‖-(1 - Complex.exp (-z * (Real.log (1+x) : ℂ)))‖
          = ‖Complex.exp (-z * (Real.log (1+x) : ℂ)) - 1‖ := by
            rw [neg_sub]
        _ ≤ 2 * ‖-z * (Real.log (1+x) : ℂ)‖ := h3
        _ = 2 * (‖z‖ * Real.log (1+x)) := by
            rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hlog_nonneg]
        _ ≤ 2*‖z‖*x := by
            have := mul_le_mul_of_nonneg_left hlog_le (norm_nonneg z)
            nlinarith [norm_nonneg z]
    calc ‖((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖
        ≤ x + 2*‖z‖*x := by
          have := htri
          linarith
      _ = (1 + 2*‖z‖) * x := by ring
  · -- tail: dominated by e^{-x}/x₀ + x^{-(1+Re z)}
    refine MeasureTheory.Integrable.mono'
      (g := fun x => (1/x₀) * Real.exp (-x) + x ^ (-(1 + z.re)))
      (MeasureTheory.Integrable.add ?_ ?_)
      (hmeas.mono_measure (Measure.restrict_mono (Set.Ioi_subset_Ioi hx₀pos.le) le_rfl)) ?_
    · have h0 := exp_neg_integrableOn_Ioi x₀ (one_pos)
      have h1 : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi x₀) := by
        refine h0.congr_fun (fun x _ => ?_) measurableSet_Ioi
        show Real.exp (-1 * x) = Real.exp (-x)
        rw [neg_one_mul]
      exact h1.const_mul _
    · refine integrableOn_Ioi_rpow_of_lt (by linarith) hx₀pos
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.mem_Ioi] at hx
      have hx0 : 0 < x := lt_trans hx₀pos hx
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      rw [div_le_iff₀ hx0]
      have hnorm_sub : ‖((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖
          ≤ Real.exp (-x) + (1+x) ^ (-z.re) := by
        calc ‖((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖
            ≤ ‖((Real.exp (-x) : ℝ) : ℂ)‖ + ‖((1+x : ℝ) : ℂ) ^ (-z)‖ := norm_sub_le _ _
          _ = Real.exp (-x) + (1+x) ^ (-z.re) := by
              rw [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
                Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0:ℝ) < 1+x),
                Complex.neg_re]
      calc ‖((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-z)‖
          ≤ Real.exp (-x) + (1+x) ^ (-z.re) := hnorm_sub
        _ ≤ (1/x₀) * Real.exp (-x) * x + x ^ (-(1 + z.re)) * x := by
            have hp1 : Real.exp (-x) ≤ (1/x₀) * Real.exp (-x) * x := by
              have h5 : (1:ℝ) ≤ x/x₀ := (one_le_div hx₀pos).mpr hx.le
              calc Real.exp (-x) = Real.exp (-x) * 1 := (mul_one _).symm
                _ ≤ Real.exp (-x) * (x/x₀) :=
                    mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
                _ = (1/x₀) * Real.exp (-x) * x := by ring
            have hp2 : (1+x) ^ (-z.re) ≤ x ^ (-(1 + z.re)) * x := by
              have h4 : (1+x) ^ (-z.re) ≤ x ^ (-z.re) := by
                refine Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)
              calc (1+x) ^ (-z.re) ≤ x ^ (-z.re) := h4
                _ = x ^ (-(1 + z.re)) * x := by
                    rw [show x ^ (-(1 + z.re)) * x
                        = x ^ (-(1 + z.re)) * x ^ (1:ℝ) by rw [Real.rpow_one],
                      ← Real.rpow_add hx0]
                    ring_nf
            linarith
        _ = ((1/x₀) * Real.exp (-x) + x ^ (-(1 + z.re))) * x := by ring

/-- **Poitou's difference form of Gauss's formula** (p. 6-03, eq. (5), applied to a
difference so that both counterterms cancel): for `σ > 0` real and `Re w > 0`,

`ψ(w) - ψ(σ) = ∫₀^∞ (e^{-σu} - e^{-wu})/(1 - e^{-u}) du`.

Change of variables `x = e^u - 1` in the difference of two Gauss first-form integrals. -/
theorem digamma_sub_digamma_eq_integral {σ : ℝ} (hσ : 0 < σ) {w : ℂ} (hw : 0 < w.re) :
    Complex.digamma w - Complex.digamma (σ:ℂ)
      = ∫ u in Set.Ioi (0:ℝ),
          (Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ)))
            / (1 - Complex.exp (-(u:ℂ))) := by
  have hσ' : 0 < ((σ:ℂ)).re := by simpa using hσ
  rw [digamma_eq_integral_gauss_one hw, digamma_eq_integral_gauss_one hσ',
    ← MeasureTheory.integral_sub (integrableOn_gauss_one_integrand hw)
      (integrableOn_gauss_one_integrand hσ')]
  -- the e^{-x}/x counterterms cancel
  have hstep1 : (∫ x in Set.Ioi (0:ℝ),
      ((((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-w)) / (x:ℂ)
        - (((Real.exp (-x) : ℝ) : ℂ) - ((1+x : ℝ) : ℂ) ^ (-(σ:ℂ))) / (x:ℂ)))
      = ∫ x in Set.Ioi (0:ℝ),
          (((1+x : ℝ) : ℂ) ^ (-(σ:ℂ)) - ((1+x : ℝ) : ℂ) ^ (-w)) / (x:ℂ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    ring
  rw [hstep1]
  -- change of variables x = e^u - 1
  set g : ℝ → ℝ := fun u => Real.exp u - 1 with hg
  have himg : g '' Set.Ioi 0 = Set.Ioi (0:ℝ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hg]
      simp only
      have := Real.exp_lt_exp.mpr hu
      rw [Real.exp_zero] at this
      linarith
    · intro hx
      refine ⟨Real.log (1+x), ?_, ?_⟩
      · refine Real.log_pos ?_
        linarith
      · rw [hg]
        simp only
        rw [Real.exp_log (by linarith)]
        ring
  have hderiv : ∀ u ∈ Set.Ioi (0:ℝ), HasDerivWithinAt g (Real.exp u) (Set.Ioi 0) u := by
    intro u _
    exact ((Real.hasDerivAt_exp u).sub_const 1).hasDerivWithinAt
  have hinj : Set.InjOn g (Set.Ioi 0) := by
    have hmono : StrictMono g := by
      intro a b hab
      rw [hg]
      simp only
      have := Real.exp_lt_exp.mpr hab
      linarith
    exact (hmono.injective).injOn
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv hinj
    (fun x : ℝ => (((1+x : ℝ) : ℂ) ^ (-(σ:ℂ)) - ((1+x : ℝ) : ℂ) ^ (-w)) / (x:ℂ))
  rw [himg] at hcov
  rw [hcov]
  -- pointwise identification with the exponential kernel
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  rw [Set.mem_Ioi] at hu
  have hexp1 : (0:ℝ) < Real.exp u - 1 := by
    have := Real.exp_lt_exp.mpr hu
    rw [Real.exp_zero] at this
    linarith
  have hbase : (1 + (g u) : ℝ) = Real.exp u := by
    rw [hg]
    ring
  -- (e^u)^{-z} = exp(-zu) for both exponents
  have hcpow : ∀ z : ℂ, ((1 + (g u) : ℝ) : ℂ) ^ (-z) = Complex.exp (-z * (u:ℂ)) := by
    intro z
    rw [hbase, Complex.cpow_def_of_ne_zero (by
      exact_mod_cast (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp]
    ring_nf
  rw [show |Real.exp u| = Real.exp u from abs_of_pos (Real.exp_pos u)]
  rw [Complex.real_smul, hcpow, hcpow]
  have hgu : ((g u : ℝ) : ℂ) = ((Real.exp u - 1 : ℝ) : ℂ) := by
    rw [hg]
  rw [hgu]
  have hne1 : ((Real.exp u - 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hexp1.ne'
  have hne2 : (1 : ℂ) - Complex.exp (-(u:ℂ)) ≠ 0 := by
    have h2 : Complex.exp (-(u:ℂ)) = ((Real.exp (-u) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      push_cast
      ring_nf
    rw [h2]
    have h3 : Real.exp (-u) < 1 := by
      have := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
      rwa [Real.exp_zero] at this
    intro h
    have h4 := sub_eq_zero.mp h
    have h5 : (1:ℝ) = Real.exp (-u) := by exact_mod_cast h4
    linarith
  rw [← mul_div_assoc, div_eq_div_iff hne1 hne2]
  have hkey : ((Real.exp u : ℝ) : ℂ) * (1 - Complex.exp (-(u:ℂ)))
      = ((Real.exp u - 1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    rw [mul_sub, mul_one, ← Complex.exp_add]
    simp
  linear_combination (Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ))) * hkey

/-- The exponential difference kernel of `digamma_sub_digamma_eq_integral` is integrable
on `(0, ∞)`: near `0` the numerator vanishes to first order, and the tail decays
exponentially. -/
theorem integrableOn_digamma_diff_kernel {σ : ℝ} (hσ : 0 < σ) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun u : ℝ =>
      (Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ)))
        / (1 - Complex.exp (-(u:ℂ)))) (Set.Ioi 0) := by
  set u₀ : ℝ := min 1 (1/(‖w - (σ:ℂ)‖+1)) with hu₀
  have hu₀pos : 0 < u₀ := lt_min one_pos (by positivity)
  have hu₀le1 : u₀ ≤ 1 := min_le_left _ _
  have hden_pos : ∀ u : ℝ, 0 < u → 0 < 1 - Real.exp (-u) := by
    intro u hu
    have := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hden_real : ∀ u : ℝ, (1:ℂ) - Complex.exp (-(u:ℂ))
      = ((1 - Real.exp (-u) : ℝ) : ℂ) := by
    intro u
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hne : ∀ u : ℝ, 0 < u → (1:ℂ) - Complex.exp (-(u:ℂ)) ≠ 0 := by
    intro u hu
    rw [hden_real u]
    exact_mod_cast (hden_pos u hu).ne'
  have hmeas : AEStronglyMeasurable (fun u : ℝ =>
      (Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ)))
        / (1 - Complex.exp (-(u:ℂ)))) (volume.restrict (Set.Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro u hu
    rw [Set.mem_Ioi] at hu
    exact hne u hu
  have hden_lower : ∀ u : ℝ, 0 < u → u / Real.exp u ≤ 1 - Real.exp (-u) := by
    intro u hu
    have h1 := Real.add_one_le_exp u
    rw [Real.exp_neg u, div_le_iff₀ (Real.exp_pos u), sub_mul, one_mul,
      inv_mul_cancel₀ (Real.exp_pos u).ne']
    linarith
  have hnum_re : ∀ u : ℝ, (-(σ:ℂ) * (u:ℂ)).re = -(σ * u) := by
    intro u
    simp [Complex.mul_re]
  rw [show Set.Ioi (0:ℝ) = Set.Ioc 0 u₀ ∪ Set.Ioi u₀ by
    rw [Set.Ioc_union_Ioi_eq_Ioi hu₀pos.le], MeasureTheory.integrableOn_union]
  constructor
  · -- near 0: bounded
    refine MeasureTheory.Integrable.mono'
      (g := fun _ => 2 * ‖w - (σ:ℂ)‖ * Real.exp 1)
      (MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top))
      (hmeas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl)) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    obtain ⟨hu0, huu₀⟩ := hu
    have hu1 : u ≤ 1 := le_trans huu₀ hu₀le1
    have hnum : Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ))
        = Complex.exp (-(σ:ℂ) * (u:ℂ)) * (1 - Complex.exp (-(w - (σ:ℂ)) * (u:ℂ))) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      ring_nf
    have hv : ‖(-(w - (σ:ℂ)) * (u:ℂ))‖ = ‖w - (σ:ℂ)‖ * u := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
    have hsmall : ‖(-(w - (σ:ℂ)) * (u:ℂ))‖ ≤ 1 := by
      rw [hv]
      have h1 : u ≤ 1/(‖w - (σ:ℂ)‖+1) := le_trans huu₀ (min_le_right _ _)
      calc ‖w - (σ:ℂ)‖ * u ≤ ‖w - (σ:ℂ)‖ * (1/(‖w - (σ:ℂ)‖+1)) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ 1 := by
            rw [mul_one_div, div_le_one (by positivity)]
            linarith
    rw [hnum, norm_div, norm_mul]
    have h1 : ‖Complex.exp (-(σ:ℂ) * (u:ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp, hnum_re u]
      refine Real.exp_le_one_iff.mpr ?_
      have := mul_pos hσ hu0
      linarith
    have h3 : ‖(1:ℂ) - Complex.exp (-(w - (σ:ℂ)) * (u:ℂ))‖ ≤ 2 * (‖w - (σ:ℂ)‖ * u) := by
      rw [← norm_neg, neg_sub]
      calc ‖Complex.exp (-(w - (σ:ℂ)) * (u:ℂ)) - 1‖
          ≤ 2 * ‖(-(w - (σ:ℂ)) * (u:ℂ))‖ := Complex.norm_exp_sub_one_le hsmall
        _ = 2 * (‖w - (σ:ℂ)‖ * u) := by rw [hv]
    rw [hden_real u, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hden_pos u hu0), div_le_iff₀ (hden_pos u hu0)]
    have h5 := hden_lower u hu0
    calc ‖Complex.exp (-(σ:ℂ) * (u:ℂ))‖
          * ‖(1:ℂ) - Complex.exp (-(w - (σ:ℂ)) * (u:ℂ))‖
        ≤ 1 * (2 * (‖w - (σ:ℂ)‖ * u)) :=
          mul_le_mul h1 h3 (norm_nonneg _) zero_le_one
      _ = 2 * ‖w - (σ:ℂ)‖ * u := by ring
      _ ≤ 2 * ‖w - (σ:ℂ)‖ * Real.exp 1 * (u / Real.exp u) := by
          rw [show 2 * ‖w - (σ:ℂ)‖ * Real.exp 1 * (u / Real.exp u)
              = 2 * ‖w - (σ:ℂ)‖ * u * (Real.exp 1 / Real.exp u) by ring]
          have h7 : (1:ℝ) ≤ Real.exp 1 / Real.exp u := by
            rw [le_div_iff₀ (Real.exp_pos u), one_mul]
            exact Real.exp_le_exp.mpr hu1
          have hc : (0:ℝ) ≤ 2 * ‖w - (σ:ℂ)‖ * u := by positivity
          nlinarith [mul_nonneg hc (by linarith : (0:ℝ) ≤ Real.exp 1 / Real.exp u - 1)]
      _ ≤ 2 * ‖w - (σ:ℂ)‖ * Real.exp 1 * (1 - Real.exp (-u)) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
  · -- tail: exponential decay over a bounded-below denominator
    set a := min σ w.re with ha
    have hapos : 0 < a := lt_min hσ hw
    refine MeasureTheory.Integrable.mono'
      (g := fun u => (2 / (1 - Real.exp (-u₀))) * Real.exp (-(a * u)))
      (Integrable.const_mul ?_ _)
      (hmeas.mono_measure (Measure.restrict_mono (Set.Ioi_subset_Ioi hu₀pos.le) le_rfl)) ?_
    · have h0 := exp_neg_integrableOn_Ioi u₀ hapos
      refine h0.congr_fun (fun u _ => ?_) measurableSet_Ioi
      show Real.exp (-a * u) = Real.exp (-(a * u))
      rw [neg_mul]
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      rw [Set.mem_Ioi] at hu
      have hu0 : 0 < u := lt_trans hu₀pos hu
      rw [norm_div, hden_real u, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hden_pos u hu0), div_le_iff₀ (hden_pos u hu0)]
      have hmono : 1 - Real.exp (-u₀) ≤ 1 - Real.exp (-u) := by
        have := Real.exp_le_exp.mpr (show -u ≤ -u₀ by linarith)
        linarith
      have hnum_bound : ‖Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ))‖
          ≤ 2 * Real.exp (-(a * u)) := by
        calc ‖Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ))‖
            ≤ ‖Complex.exp (-(σ:ℂ) * (u:ℂ))‖ + ‖Complex.exp (-w * (u:ℂ))‖ :=
              norm_sub_le _ _
          _ = Real.exp (-(σ * u)) + Real.exp (-(w.re * u)) := by
              rw [Complex.norm_exp, Complex.norm_exp, hnum_re u]
              congr 2
              simp [Complex.mul_re]
          _ ≤ Real.exp (-(a * u)) + Real.exp (-(a * u)) := by
              have h1 : a ≤ σ := min_le_left _ _
              have h2 : a ≤ w.re := min_le_right _ _
              have h3 : Real.exp (-(σ * u)) ≤ Real.exp (-(a * u)) := by
                refine Real.exp_le_exp.mpr ?_
                nlinarith
              have h4 : Real.exp (-(w.re * u)) ≤ Real.exp (-(a * u)) := by
                refine Real.exp_le_exp.mpr ?_
                nlinarith
              linarith
          _ = 2 * Real.exp (-(a * u)) := by ring
      calc ‖Complex.exp (-(σ:ℂ) * (u:ℂ)) - Complex.exp (-w * (u:ℂ))‖
          ≤ 2 * Real.exp (-(a * u)) := hnum_bound
        _ = (2 / (1 - Real.exp (-u₀))) * Real.exp (-(a * u)) * (1 - Real.exp (-u₀)) := by
            field_simp
            exact (div_self (hden_pos u₀ hu₀pos).ne').symm
        _ ≤ (2 / (1 - Real.exp (-u₀))) * Real.exp (-(a * u)) * (1 - Real.exp (-u)) := by
            refine mul_le_mul_of_nonneg_left hmono ?_
            have := hden_pos u₀ hu₀pos
            positivity

/-- **Poitou's cosine-kernel identity** (p. 6-04): for `σ > 0`,
`Re(ψ(σ+it) - ψ(σ)) = ∫₀^∞ e^{-σu}(1 - cos(tu))/(1-e^{-u}) du`. -/
theorem re_digamma_sub_eq_integral {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (Complex.digamma ((σ:ℂ) + (t:ℂ)*Complex.I) - Complex.digamma (σ:ℂ)).re
      = ∫ u in Set.Ioi (0:ℝ),
          Real.exp (-(σ*u)) * (1 - Real.cos (t*u)) / (1 - Real.exp (-u)) := by
  have hw : 0 < ((σ:ℂ) + (t:ℂ)*Complex.I).re := by simp [hσ]
  rw [digamma_sub_digamma_eq_integral hσ hw]
  have hint := integrableOn_digamma_diff_kernel hσ hw
  have h0 := integral_re hint
  simp only [RCLike.re_to_complex] at h0
  rw [← h0]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  rw [Set.mem_Ioi] at hu
  have hden_pos : 0 < 1 - Real.exp (-u) := by
    have := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hden_real : (1:ℂ) - Complex.exp (-(u:ℂ)) = ((1 - Real.exp (-u) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_exp]
    push_cast
    ring_nf
  show ((Complex.exp (-(σ:ℂ) * (u:ℂ))
      - Complex.exp (-((σ:ℂ) + (t:ℂ)*Complex.I) * (u:ℂ)))
        / (1 - Complex.exp (-(u:ℂ)))).re = _
  rw [hden_real, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hre1 : (Complex.exp (-(σ:ℂ) * (u:ℂ))).re = Real.exp (-(σ*u)) := by
    rw [Complex.exp_re]
    have h1 : (-(σ:ℂ) * (u:ℂ)).re = -(σ*u) := by
      simp [Complex.mul_re]
    have h2 : (-(σ:ℂ) * (u:ℂ)).im = 0 := by
      simp [Complex.mul_im]
    rw [h1, h2, Real.cos_zero, mul_one]
  have hre2 : (Complex.exp (-((σ:ℂ) + (t:ℂ)*Complex.I) * (u:ℂ))).re
      = Real.exp (-(σ*u)) * Real.cos (t*u) := by
    rw [Complex.exp_re]
    have h1 : (-((σ:ℂ) + (t:ℂ)*Complex.I) * (u:ℂ)).re = -(σ*u) := by
      simp [Complex.mul_re, Complex.add_re, Complex.add_im]
    have h2 : (-((σ:ℂ) + (t:ℂ)*Complex.I) * (u:ℂ)).im = -(t*u) := by
      simp [Complex.mul_im, Complex.add_re, Complex.add_im]
    rw [h1, h2, Real.cos_neg]
  rw [Complex.sub_re, hre1, hre2]
  field_simp

/-- The `σ = 1/2` kernel is the hyperbolic-sine kernel (Poitou p. 6-04, first display):
`e^{-u/2}/(1 - e^{-u}) = 1/(2 sinh(u/2))`. -/
theorem exp_half_div_one_sub_exp_neg {u : ℝ} (hu : 0 < u) :
    Real.exp (-(u/2)) / (1 - Real.exp (-u)) = 1/(2 * Real.sinh (u/2)) := by
  have hsh : 2 * Real.sinh (u/2) = Real.exp (u/2) - Real.exp (-(u/2)) := by
    rw [Real.sinh_eq]
    ring
  have hden_pos : 0 < 1 - Real.exp (-u) := by
    have := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hsh_pos : 0 < Real.exp (u/2) - Real.exp (-(u/2)) := by
    have := Real.exp_lt_exp.mpr (show -(u/2) < u/2 by linarith)
    linarith
  rw [hsh, div_eq_div_iff hden_pos.ne' (by linarith)]
  rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
  ring_nf
  rw [Real.exp_zero]

/-- **The elementary cosh integral** (Poitou p. 6-04): `∫₀^∞ du/(2 cosh(u/2)) = π/2`.
Substituting `v = e^{u/2}` gives `2∫₁^∞ dv/(1+v²) = 2(π/2 - π/4)`. -/
theorem integral_inv_two_cosh_half :
    ∫ u in Set.Ioi (0:ℝ), 1/(2 * Real.cosh (u/2)) = π/2 := by
  set g : ℝ → ℝ := fun u => Real.exp (u/2) with hg
  have himg : g '' Set.Ioi 0 = Set.Ioi (1:ℝ) := by
    ext v
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hg]
      simp only
      have := Real.exp_lt_exp.mpr (show (0:ℝ) < u/2 by linarith)
      rwa [Real.exp_zero] at this
    · intro hv
      refine ⟨2 * Real.log v, ?_, ?_⟩
      · have := Real.log_pos hv
        linarith
      · rw [hg]
        simp only
        rw [show 2 * Real.log v / 2 = Real.log v by ring, Real.exp_log (by linarith)]
  have hderiv : ∀ u ∈ Set.Ioi (0:ℝ),
      HasDerivWithinAt g (Real.exp (u/2) * (1/2)) (Set.Ioi 0) u := by
    intro u _
    have h0 : HasDerivAt (fun u : ℝ => u/2) (1/2) u := by
      simpa using (hasDerivAt_id u).div_const 2
    exact (h0.exp).hasDerivWithinAt
  have hinj : Set.InjOn g (Set.Ioi 0) := by
    have hmono : StrictMono g := by
      intro a b hab
      rw [hg]
      simp only
      exact Real.exp_lt_exp.mpr (by linarith)
    exact hmono.injective.injOn
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv hinj (fun v : ℝ => 2/(1+v^2))
  rw [himg] at hcov
  -- evaluate the v-side
  have hval : (∫ v in Set.Ioi (1:ℝ), 2/(1+v^2)) = π/2 := by
    have h0 : (∫ v in Set.Ioi (1:ℝ), 2/(1+v^2))
        = 2 * ∫ v in Set.Ioi (1:ℝ), (1+v^2)⁻¹ := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
      rw [div_eq_mul_inv]
    rw [h0, integral_Ioi_inv_one_add_sq, Real.arctan_one]
    ring
  have hpt : (∫ u in Set.Ioi (0:ℝ), 1/(2 * Real.cosh (u/2)))
      = ∫ u in Set.Ioi (0:ℝ), |Real.exp (u/2) * (1/2)| • (2/(1 + (g u)^2)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    rw [Set.mem_Ioi] at hu
    rw [hg]
    simp only
    rw [abs_of_pos (by positivity : (0:ℝ) < Real.exp (u/2) * (1/2)), smul_eq_mul]
    have hcosh : 2 * Real.cosh (u/2) = Real.exp (u/2) + Real.exp (-(u/2)) := by
      rw [Real.cosh_eq]
      ring
    rw [hcosh]
    have h2 : Real.exp (u/2) + Real.exp (-(u/2)) > 0 := by positivity
    have h3 : Real.exp (-(u/2)) * Real.exp (u/2) = 1 := by
      rw [← Real.exp_add]
      simp
    have h4 : (0:ℝ) < 1 + Real.exp (u/2)^2 := by positivity
    field_simp
    nlinarith [h3, Real.exp_pos (u/2)]
  rw [hpt, ← hcov, hval]

/-- The real cosine kernel of `re_digamma_sub_eq_integral` is integrable on `(0, ∞)`. -/
theorem integrableOn_re_diff_kernel {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    IntegrableOn
      (fun u : ℝ => Real.exp (-(σ*u)) * (1 - Real.cos (t*u)) / (1 - Real.exp (-u)))
      (Set.Ioi 0) := by
  have hw : 0 < ((σ:ℂ) + (t:ℂ)*Complex.I).re := by simp [hσ]
  have h0 := (integrableOn_digamma_diff_kernel hσ hw).re
  simp only [RCLike.re_to_complex] at h0
  refine h0.congr ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
  refine Filter.Eventually.of_forall (fun u hu => ?_)
  rw [Set.mem_Ioi] at hu
  have hden_pos : 0 < 1 - Real.exp (-u) := by
    have := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hden_real : (1:ℂ) - Complex.exp (-(u:ℂ)) = ((1 - Real.exp (-u) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_exp]
    push_cast
    ring_nf
  show ((Complex.exp (-(σ:ℂ) * (u:ℂ))
      - Complex.exp (-((σ:ℂ) + (t:ℂ)*Complex.I) * (u:ℂ)))
        / (1 - Complex.exp (-(u:ℂ)))).re = _
  rw [hden_real, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hre1 : (Complex.exp (-(σ:ℂ) * (u:ℂ))).re = Real.exp (-(σ*u)) := by
    rw [Complex.exp_re]
    have h1 : (-(σ:ℂ) * (u:ℂ)).re = -(σ*u) := by
      simp [Complex.mul_re]
    have h2 : (-(σ:ℂ) * (u:ℂ)).im = 0 := by
      simp [Complex.mul_im]
    rw [h1, h2, Real.cos_zero, mul_one]
  have hre2 : (Complex.exp (-((σ:ℂ) + (t:ℂ)*Complex.I) * (u:ℂ))).re
      = Real.exp (-(σ*u)) * Real.cos (t*u) := by
    rw [Complex.exp_re]
    have h1 : (-((σ:ℂ) + (t:ℂ)*Complex.I) * (u:ℂ)).re = -(σ*u) := by
      simp [Complex.mul_re, Complex.add_re, Complex.add_im]
    have h2 : (-((σ:ℂ) + (t:ℂ)*Complex.I) * (u:ℂ)).im = -(t*u) := by
      simp [Complex.mul_im, Complex.add_re, Complex.add_im]
    rw [h1, h2, Real.cos_neg]
  rw [Complex.sub_re, hre1, hre2]
  field_simp

/-- **The quarter–half cosh combination** (Poitou p. 6-04, third display): the halved
`σ = 1/4` kernel minus the `σ = 1/2` kernel is the hyperbolic-cosine kernel:

`[Re ψ(1/4 + it/2) - ψ(1/4)-part] - [Re ψ(1/2 + it) - ψ(1/2)-part]
   = ∫₀^∞ (1 - cos(tx))/(2 cosh(x/2)) dx`. -/
theorem re_digamma_quarter_sub_half_eq_integral (t : ℝ) :
    (Complex.digamma (((1/4 : ℝ):ℂ) + ((t/2 : ℝ):ℂ)*Complex.I)
        - Complex.digamma ((1/4 : ℝ):ℂ)).re
      - (Complex.digamma (((1/2 : ℝ):ℂ) + ((t : ℝ):ℂ)*Complex.I)
        - Complex.digamma ((1/2 : ℝ):ℂ)).re
      = ∫ x in Set.Ioi (0:ℝ), (1 - Real.cos (t*x)) / (2 * Real.cosh (x/2)) := by
  rw [re_digamma_sub_eq_integral (by norm_num : (0:ℝ) < 1/4) (t/2),
    re_digamma_sub_eq_integral (by norm_num : (0:ℝ) < 1/2) t]
  -- substitute u = 2x in the σ = 1/4 integral
  set g : ℝ → ℝ := fun x => 2*x with hg
  have himg : g '' Set.Ioi 0 = Set.Ioi (0:ℝ) := by
    ext v
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hg]
      simp only
      linarith
    · intro hv
      exact ⟨v/2, by linarith, by rw [hg]; simp only; ring⟩
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivWithinAt g 2 (Set.Ioi 0) x := by
    intro x _
    have h0 : HasDerivAt (fun x : ℝ => 2*x) 2 x := by
      simpa using (hasDerivAt_id x).const_mul 2
    exact h0.hasDerivWithinAt
  have hinj : Set.InjOn g (Set.Ioi 0) := by
    have hmono : StrictMono g := fun a b hab => by
      rw [hg]
      simp only
      linarith
    exact hmono.injective.injOn
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv hinj
    (fun u : ℝ => Real.exp (-(1/4*u)) * (1 - Real.cos (t/2*u)) / (1 - Real.exp (-u)))
  rw [himg] at hcov
  rw [hcov]
  -- integrable pieces for the subtraction
  have hint2 := integrableOn_re_diff_kernel (by norm_num : (0:ℝ) < 1/2) t
  have hint1 : IntegrableOn
      (fun x : ℝ => |(2:ℝ)| • (Real.exp (-(1/4*(g x))) * (1 - Real.cos (t/2*(g x)))
        / (1 - Real.exp (-(g x))))) (Set.Ioi 0) := by
    have h0 := (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hderiv hinj
      (fun u : ℝ => Real.exp (-(1/4*u)) * (1 - Real.cos (t/2*u))
        / (1 - Real.exp (-u)))).mp ?_
    · exact h0
    · rw [himg]
      exact integrableOn_re_diff_kernel (by norm_num : (0:ℝ) < 1/4) (t/2)
  rw [← MeasureTheory.integral_sub hint1 hint2]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [Set.mem_Ioi] at hx
  rw [hg]
  simp only
  rw [abs_of_pos (by norm_num : (0:ℝ) < 2), smul_eq_mul]
  -- kernel identity: 2e^{-x/2}/(1-e^{-2x}) - e^{-x/2}/(1-e^{-x}) = 1/(2cosh(x/2))
  have hd1 : 0 < 1 - Real.exp (-(2*x)) := by
    have := Real.exp_lt_exp.mpr (show -(2*x) < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hd2 : 0 < 1 - Real.exp (-x) := by
    have := Real.exp_lt_exp.mpr (show -x < 0 by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hfactor : 1 - Real.exp (-(2*x)) = (1 - Real.exp (-x)) * (1 + Real.exp (-x)) := by
    have h0 : Real.exp (-(2*x)) = Real.exp (-x) * Real.exp (-x) := by
      rw [← Real.exp_add]
      ring_nf
    rw [h0]
    ring
  have hcosh : 2 * Real.cosh (x/2) = Real.exp (x/2) + Real.exp (-(x/2)) := by
    rw [Real.cosh_eq]
    ring
  have hcosh_pos : (0:ℝ) < 2 * Real.cosh (x/2) := by
    rw [hcosh]
    positivity
  -- arguments align: 1/4*(2x) = x/2, t/2*(2x) = t*x, 1/2*x = x/2
  rw [show (1:ℝ)/4*(2*x) = x/2 by ring, show t/2*(2*x) = t*x by ring,
    show (-(1/2*x) : ℝ) = -(x/2) by ring]
  have hbr : 2/(1 - Real.exp (-(2*x))) - 1/(1 - Real.exp (-x)) = 1/(1 + Real.exp (-x)) := by
    rw [hfactor]
    have h1 : 0 < 1 + Real.exp (-x) := by positivity
    field_simp
    ring
  have hker : Real.exp (-(x/2)) / (1 + Real.exp (-x)) = 1/(2*Real.cosh (x/2)) := by
    rw [hcosh, div_eq_div_iff (by positivity) (by positivity)]
    rw [mul_add, ← Real.exp_add, ← Real.exp_add]
    ring_nf
    rw [Real.exp_zero]
  calc 2 * (Real.exp (-(x/2)) * (1 - Real.cos (t*x)) / (1 - Real.exp (-(2*x))))
        - Real.exp (-(x/2)) * (1 - Real.cos (t*x)) / (1 - Real.exp (-x))
      = (Real.exp (-(x/2)) * (1 - Real.cos (t*x)))
          * (2/(1 - Real.exp (-(2*x))) - 1/(1 - Real.exp (-x))) := by ring
    _ = (Real.exp (-(x/2)) * (1 - Real.cos (t*x))) * (1/(1 + Real.exp (-x))) := by
        rw [hbr]
    _ = (1 - Real.cos (t*x)) * (Real.exp (-(x/2)) / (1 + Real.exp (-x))) := by ring
    _ = (1 - Real.cos (t*x)) * (1/(2*Real.cosh (x/2))) := by rw [hker]
    _ = (1 - Real.cos (t*x)) / (2 * Real.cosh (x/2)) := by ring

/-- The sine-integral tail `∫_t^∞ sin u/u du`, defined through the Dirichlet integral as
`π/2 - ∫_0^t sin u/u du` (Poitou p. 6-05, the `γ₁ + γ₃` term). -/
noncomputable def sincTail (t : ℝ) : ℝ := π/2 - ∫ u in (0:ℝ)..t, Real.sin u / u

/-- The truncated tail integrals converge to `sincTail`. -/
theorem tendsto_integral_sinc_window (t : ℝ) :
    Tendsto (fun X : ℝ => ∫ u in t..X, Real.sin u / u) atTop (nhds (sincTail t)) := by
  have h0 : ∀ X : ℝ, (∫ u in t..X, Real.sin u / u)
      = (∫ u in (0:ℝ)..X, Real.sin u / u) - ∫ u in (0:ℝ)..t, Real.sin u / u := by
    intro X
    rw [eq_sub_iff_add_eq]
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_sinc 0 t) (intervalIntegrable_sinc t X)
  simp only [h0]
  rw [sincTail]
  exact (tendsto_integral_sinc_atTop).sub_const _

/-- `sincTail` vanishes at infinity. -/
theorem tendsto_sincTail_atTop : Tendsto sincTail atTop (nhds 0) := by
  have h0 := tendsto_integral_sinc_atTop.const_sub (π/2)
  simp only [sub_self] at h0
  exact h0

/-- `sincTail` is differentiable away from `0`, with derivative `-sin t/t`. -/
theorem hasDerivAt_sincTail {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt sincTail (-(Real.sin t / t)) t := by
  have h0 : HasDerivAt (fun t : ℝ => ∫ u in (0:ℝ)..t, Real.sin u / u)
      (Real.sin t / t) t := by
    refine intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_sinc 0 t) ?_ ?_
    · refine (Measurable.stronglyMeasurable ?_).stronglyMeasurableAtFilter
      fun_prop
    · have : ContinuousAt (fun u : ℝ => Real.sin u / u) t := by
        refine ContinuousAt.div (by fun_prop) (by fun_prop) ht
      exact this
  have h1 : HasDerivAt (fun t : ℝ => π/2 - ∫ u in (0:ℝ)..t, Real.sin u / u)
      (0 - Real.sin t / t) t := (hasDerivAt_const t (π/2)).sub h0
  have h2 : sincTail = fun t : ℝ => π/2 - ∫ u in (0:ℝ)..t, Real.sin u / u := rfl
  rw [h2]
  simpa using h1

/-- The symmetric exponential tails equal the sinc tail: for `t > 0`,
`∫_1^X (e^{itx} - e^{-itx})/x dx → 2i·sincTail t` (Poitou p. 6-05, `γ₁ + γ₃`). -/
theorem tendsto_integral_cexp_sub_div_window {t : ℝ} (ht : 0 < t) :
    Tendsto (fun X : ℝ => ∫ x in (1:ℝ)..X,
        (Complex.exp ((t*x : ℝ) * Complex.I) - Complex.exp (-((t*x : ℝ)) * Complex.I))
          / (x:ℂ))
      atTop (nhds (2 * Complex.I * ((sincTail t : ℝ) : ℂ))) := by
  -- pointwise: the integrand is 2i·sin(tx)/x
  have hpt : ∀ x : ℝ,
      (Complex.exp ((t*x : ℝ) * Complex.I) - Complex.exp (-((t*x : ℝ)) * Complex.I))
        / (x:ℂ)
      = 2 * Complex.I * ((Real.sin (t*x) / x : ℝ) : ℂ) := by
    intro x
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
    · rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      push_cast
      field_simp
      ring
  have h0 : ∀ X : ℝ, (∫ x in (1:ℝ)..X,
      (Complex.exp ((t*x : ℝ) * Complex.I) - Complex.exp (-((t*x : ℝ)) * Complex.I))
        / (x:ℂ))
      = 2 * Complex.I * ((∫ x in (1:ℝ)..X, Real.sin (t*x) / x : ℝ) : ℂ) := by
    intro X
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun x _ => hpt x)
  simp only [h0]
  -- ∫_1^X sin(tx)/x = ∫_t^{tX} sinc → sincTail t
  have h1 : ∀ X : ℝ, (∫ x in (1:ℝ)..X, Real.sin (t*x) / x)
      = ∫ u in t..(t*X), Real.sin u / u := by
    intro X
    have := integral_sin_mul_div_eq t 1 X ht
    rw [mul_one] at this
    exact this
  simp only [h1]
  have h2 : Tendsto (fun X : ℝ => t * X) atTop atTop :=
    Filter.Tendsto.const_mul_atTop ht Filter.tendsto_id
  have h3 := (tendsto_integral_sinc_window t).comp h2
  have h4 : Tendsto (fun X : ℝ => ((∫ u in t..(t*X), Real.sin u / u : ℝ) : ℂ))
      atTop (nhds ((sincTail t : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp h3
  exact h4.const_mul _

/-- **Differentiation of a Fourier-type set integral** (Lemme 1 engine, Poitou p. 6-05):
if `G` and `x·G(x)` are integrable on `s`, then `t ↦ ∫_s G(x) e^{itx} dx` is
differentiable with derivative `∫_s i·x·G(x) e^{itx} dx`. -/
theorem hasDerivAt_integral_mul_cexp {G : ℝ → ℂ} {s : Set ℝ}
    (hG : IntegrableOn G s) (hxG : IntegrableOn (fun x : ℝ => (x:ℂ) * G x) s) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ x in s, G x * Complex.exp ((τ * x : ℝ) * Complex.I))
      (∫ x in s, Complex.I * (x:ℂ) * G x * Complex.exp ((t * x : ℝ) * Complex.I)) t := by
  have hexp_meas : ∀ τ : ℝ, AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((τ * x : ℝ) * Complex.I)) (volume.restrict s) := by
    intro τ
    refine (Continuous.aestronglyMeasurable ?_).restrict
    fun_prop
  have hexp_norm : ∀ τ x : ℝ, ‖Complex.exp ((τ * x : ℝ) * Complex.I)‖ = 1 := by
    intro τ x
    rw [Complex.norm_exp]
    simp
  have h := _root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ : ℝ => fun x : ℝ => G x * Complex.exp ((τ * x : ℝ) * Complex.I))
    (F' := fun τ : ℝ => fun x : ℝ =>
      Complex.I * (x:ℂ) * G x * Complex.exp ((τ * x : ℝ) * Complex.I))
    (bound := fun x => ‖(x:ℂ) * G x‖)
    (μ := volume.restrict s) (x₀ := t) (s := Metric.ball t 1)
    (Metric.ball_mem_nhds t one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact h.2
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    exact (hG.aestronglyMeasurable.mul (hexp_meas τ))
  · refine hG.mul_bdd (c := 1) (hexp_meas t) ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hexp_norm t x]
  · have h5 : AEStronglyMeasurable (fun x : ℝ => Complex.I * (x:ℂ))
        (volume.restrict s) := (Continuous.aestronglyMeasurable (by fun_prop)).restrict
    exact (h5.mul hG.aestronglyMeasurable).mul (hexp_meas t)
  · refine Filter.Eventually.of_forall (fun x => ?_)
    intro τ _
    rw [norm_mul, hexp_norm τ x, mul_one, norm_mul]
    rw [show ‖Complex.I * (x:ℂ)‖ = ‖(x:ℂ)‖ by
      rw [norm_mul, Complex.norm_I, one_mul]]
    rw [← norm_mul]
  · exact hxG.norm
  · refine Filter.Eventually.of_forall (fun x => ?_)
    intro τ _
    have h0 : HasDerivAt (fun τ : ℝ => τ * x) x τ := by
      simpa using (hasDerivAt_id τ).mul_const x
    have h1 : HasDerivAt (fun τ : ℝ => ((τ * x : ℝ) : ℂ)) ((x:ℝ):ℂ) τ :=
      h0.ofReal_comp
    have h2 : HasDerivAt (fun τ : ℝ => ((τ * x : ℝ) : ℂ) * Complex.I)
        ((x:ℂ) * Complex.I) τ := h1.mul_const Complex.I
    have h3 := h2.cexp
    have h4 := h3.const_mul (G x)
    have hval : G x * (Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((x:ℂ) * Complex.I))
        = Complex.I * (x:ℂ) * G x * Complex.exp ((τ * x : ℝ) * Complex.I) := by
      ring
    rw [hval] at h4
    exact h4

/-- **Poitou's `γ`** (p. 6-05): the Fourier transform of `(F(0) - F(x))/x`, the
non-summable `F(0)`-tails taken as improper sinc-tail limits. Defined for all `t`
(the value at `t = 0` is junk). -/
noncomputable def gammaFT (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  (∫ x in Set.Ioc (-1:ℝ) 1, (F 0 - F x)/(x:ℂ) * Complex.exp ((t*x : ℝ) * Complex.I))
  + F 0 * (2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ))
  - ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, F x/(x:ℂ) * Complex.exp ((t*x : ℝ) * Complex.I)

/-- **Lemme 1** (Poitou p. 6-04/6-05): away from `t = 0`, Poitou's `γ` is differentiable
with `γ'(t) = -i·φ(t)`, `φ` the Fourier transform of `F`. -/
theorem hasDerivAt_gammaFT {F : ℝ → ℂ} (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (gammaFT F)
      (-Complex.I * ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)) t := by
  -- P1: the near-zero piece
  have hxG₀ : IntegrableOn (fun x : ℝ => (x:ℂ) * ((F 0 - F x)/(x:ℂ)))
      (Set.Ioc (-1) 1) := by
    have h0 : IntegrableOn (fun x : ℝ => F 0 - F x) (Set.Ioc (-1:ℝ) 1) := by
      refine (MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top)).sub hF.integrableOn
    refine h0.congr ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    filter_upwards [MeasureTheory.ae_iff.mpr (by
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
      exact MeasureTheory.measure_singleton (0:ℝ) : volume {x : ℝ | ¬ x ≠ 0} = 0)]
      with x hx _
    have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    exact (mul_div_cancel₀ _ hxne).symm
  have hP1 := hasDerivAt_integral_mul_cexp hFdiv hxG₀ t
  -- P3: the tail piece
  have hGtail : IntegrableOn (fun x : ℝ => F x/(x:ℂ)) (Set.Ioc (-1:ℝ) 1)ᶜ := by
    refine MeasureTheory.Integrable.mono' (hF.integrableOn.norm) ?_ ?_
    · refine ((hF.aestronglyMeasurable.restrict.mul
        ((Complex.measurable_ofReal.inv).aestronglyMeasurable.restrict)).congr ?_)
      exact Filter.Eventually.of_forall (fun x => (div_eq_mul_inv (F x) _).symm)
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc.compl).mpr ?_
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.mem_compl_iff, Set.mem_Ioc] at hx
      push Not at hx
      have hx1 : 1 ≤ |x| := by
        rcases le_or_gt x (-1) with h | h
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · have := hx h
          rw [abs_of_pos (by linarith)]
          linarith
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_self (norm_nonneg _) hx1
  have hxGtail : IntegrableOn (fun x : ℝ => (x:ℂ) * (F x/(x:ℂ)))
      (Set.Ioc (-1:ℝ) 1)ᶜ := by
    refine hF.integrableOn.congr ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc.compl).mpr ?_
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.mem_compl_iff, Set.mem_Ioc] at hx
    push Not at hx
    have hxne : x ≠ 0 := by
      rcases le_or_gt x (-1) with h | h
      · linarith
      · have := hx h
        nlinarith
    have hxne' : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxne
    field_simp
  have hP3 := hasDerivAt_integral_mul_cexp hGtail hxGtail t
  -- P2: the sinc-tail piece, locally sign-constant
  have hP2 : HasDerivAt (fun τ : ℝ =>
      F 0 * (2 * Complex.I * ((Real.sign τ * sincTail |τ| : ℝ) : ℂ)))
      (F 0 * (2 * Complex.I * ((-(Real.sin t / t) : ℝ) : ℂ))) t := by
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · -- t < 0 : locally sign = -1, |τ| = -τ
      have hev : (fun τ : ℝ => F 0 * (2 * Complex.I
          * ((Real.sign τ * sincTail |τ| : ℝ) : ℂ)))
          =ᶠ[nhds t] (fun τ : ℝ => F 0 * (2 * Complex.I
          * ((-(sincTail (-τ)) : ℝ) : ℂ))) := by
        filter_upwards [eventually_lt_nhds hneg] with τ hτ
        rw [Real.sign_of_neg hτ, abs_of_neg hτ]
        norm_num
      have h0 : HasDerivAt (fun τ : ℝ => sincTail (-τ)) (Real.sin t / t) t := by
        have h1 := (hasDerivAt_sincTail (show -t ≠ 0 by simpa using ht)).comp t
          ((hasDerivAt_id t).neg)
        have h2 : -(Real.sin (-t) / (-t)) * -1 = Real.sin t / t := by
          rw [Real.sin_neg]
          field_simp
        rw [h2] at h1
        exact h1
      have h3 : HasDerivAt (fun τ : ℝ => F 0 * (2 * Complex.I
          * ((-(sincTail (-τ)) : ℝ) : ℂ)))
          (F 0 * (2 * Complex.I * ((-(Real.sin t / t) : ℝ) : ℂ))) t := by
        have h4 : HasDerivAt (fun τ : ℝ => ((-(sincTail (-τ)) : ℝ) : ℂ))
            ((-(Real.sin t / t) : ℝ) : ℂ) t := by
          have h5 : HasDerivAt (fun τ : ℝ => -(sincTail (-τ))) (-(Real.sin t / t)) t :=
            h0.neg
          exact h5.ofReal_comp
        have h6 := h4.const_mul (F 0 * (2 * Complex.I))
        have h7 : (fun τ : ℝ => F 0 * (2 * Complex.I) * ((-(sincTail (-τ)) : ℝ) : ℂ))
            = fun τ : ℝ => F 0 * (2 * Complex.I * ((-(sincTail (-τ)) : ℝ) : ℂ)) := by
          funext τ
          ring
        rw [h7] at h6
        have h8 : F 0 * (2 * Complex.I) * ((-(Real.sin t / t) : ℝ) : ℂ)
            = F 0 * (2 * Complex.I * ((-(Real.sin t / t) : ℝ) : ℂ)) := by ring
        rw [h8] at h6
        exact h6
      exact h3.congr_of_eventuallyEq hev
    · -- t > 0 : locally sign = 1, |τ| = τ
      have hev : (fun τ : ℝ => F 0 * (2 * Complex.I
          * ((Real.sign τ * sincTail |τ| : ℝ) : ℂ)))
          =ᶠ[nhds t] (fun τ : ℝ => F 0 * (2 * Complex.I
          * ((sincTail τ : ℝ) : ℂ))) := by
        filter_upwards [eventually_gt_nhds hpos] with τ hτ
        rw [Real.sign_of_pos hτ, abs_of_pos hτ, one_mul]
      have h3 : HasDerivAt (fun τ : ℝ => F 0 * (2 * Complex.I
          * ((sincTail τ : ℝ) : ℂ)))
          (F 0 * (2 * Complex.I * ((-(Real.sin t / t) : ℝ) : ℂ))) t := by
        have h4 : HasDerivAt (fun τ : ℝ => ((sincTail τ : ℝ) : ℂ))
            ((-(Real.sin t / t) : ℝ) : ℂ) t :=
          (hasDerivAt_sincTail ht).ofReal_comp
        have h6 := h4.const_mul (F 0 * (2 * Complex.I))
        have h7 : (fun τ : ℝ => F 0 * (2 * Complex.I) * ((sincTail τ : ℝ) : ℂ))
            = fun τ : ℝ => F 0 * (2 * Complex.I * ((sincTail τ : ℝ) : ℂ)) := by
          funext τ
          ring
        rw [h7] at h6
        have h8 : F 0 * (2 * Complex.I) * ((-(Real.sin t / t) : ℝ) : ℂ)
            = F 0 * (2 * Complex.I * ((-(Real.sin t / t) : ℝ) : ℂ)) := by ring
        rw [h8] at h6
        exact h6
      exact h3.congr_of_eventuallyEq hev
  -- assemble
  have hsum := (hP1.add hP2).sub hP3
  have hfun : (((fun τ : ℝ => ∫ x in Set.Ioc (-1:ℝ) 1, (F 0 - F x)/(x:ℂ)
          * Complex.exp ((τ*x : ℝ) * Complex.I))
        + fun τ : ℝ => F 0 * (2 * Complex.I * ((Real.sign τ * sincTail |τ| : ℝ) : ℂ)))
      - fun τ : ℝ => ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, F x/(x:ℂ)
          * Complex.exp ((τ*x : ℝ) * Complex.I))
      = gammaFT F := by
    funext τ
    rfl
  rw [hfun] at hsum
  -- integrable building blocks on the window
  have hexp_meas : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I))
      (volume.restrict (Set.Ioc (-1:ℝ) 1)) := by
    refine (Continuous.aestronglyMeasurable ?_).restrict
    fun_prop
  have hexp_int : IntegrableOn (fun x : ℝ => Complex.exp ((t*x : ℝ) * Complex.I))
      (Set.Ioc (-1:ℝ) 1) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun _ => (1:ℝ))
      (MeasureTheory.integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top)) hexp_meas ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Complex.norm_exp]
    simp
  have hFe_Ioc : IntegrableOn
      (fun x : ℝ => F x * Complex.exp ((t*x : ℝ) * Complex.I)) (Set.Ioc (-1:ℝ) 1) := by
    refine hF.integrableOn.mul_bdd (c := 1) hexp_meas ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Complex.norm_exp]
    simp
  have hFe_compl : IntegrableOn
      (fun x : ℝ => F x * Complex.exp ((t*x : ℝ) * Complex.I)) (Set.Ioc (-1:ℝ) 1)ᶜ := by
    refine hF.integrableOn.mul_bdd (c := 1) ?_ ?_
    · refine (Continuous.aestronglyMeasurable ?_).restrict
      fun_prop
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Complex.norm_exp]
      simp
  -- V2: the window value
  have hV2 : (∫ x in Set.Ioc (-1:ℝ) 1, Complex.exp ((t*x : ℝ) * Complex.I))
      = ((2 * Real.sin t / t : ℝ) : ℂ) := by
    have h0 := integral_cexp_window ht (1:ℝ)
    rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)] at h0
    rw [one_mul] at h0
    rw [← h0]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
    congr 1
    push_cast
    ring
  -- V1: split the near-zero derivative integral
  have hV1 : (∫ x in Set.Ioc (-1:ℝ) 1, Complex.I * (x:ℂ) * ((F 0 - F x)/(x:ℂ))
      * Complex.exp ((t*x : ℝ) * Complex.I))
      = Complex.I * F 0 * ((2 * Real.sin t / t : ℝ) : ℂ)
        - Complex.I * ∫ x in Set.Ioc (-1:ℝ) 1,
            F x * Complex.exp ((t*x : ℝ) * Complex.I) := by
    have h0 : (∫ x in Set.Ioc (-1:ℝ) 1, Complex.I * (x:ℂ) * ((F 0 - F x)/(x:ℂ))
        * Complex.exp ((t*x : ℝ) * Complex.I))
        = ∫ x in Set.Ioc (-1:ℝ) 1,
            (Complex.I * F 0 * Complex.exp ((t*x : ℝ) * Complex.I)
              - Complex.I * (F x * Complex.exp ((t*x : ℝ) * Complex.I))) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_)
      filter_upwards [MeasureTheory.ae_iff.mpr (by
        simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
        exact MeasureTheory.measure_singleton (0:ℝ) : volume {x : ℝ | ¬ x ≠ 0} = 0)]
        with x hx _
      have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      field_simp
    rw [h0, MeasureTheory.integral_sub ((hexp_int.const_mul _)) (hFe_Ioc.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hV2]
  -- V3: the tail derivative integral
  have hV3 : (∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, Complex.I * (x:ℂ) * (F x/(x:ℂ))
      * Complex.exp ((t*x : ℝ) * Complex.I))
      = Complex.I * ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ,
          F x * Complex.exp ((t*x : ℝ) * Complex.I) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc.compl (fun x hx => ?_)
    rw [Set.mem_compl_iff, Set.mem_Ioc] at hx
    push Not at hx
    have hxne : x ≠ 0 := by
      rcases le_or_gt x (-1) with h | h
      · linarith
      · have := hx h
        nlinarith
    have hxne' : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxne
    field_simp
  -- V5: recombine the full line
  have hV5 : (∫ x in Set.Ioc (-1:ℝ) 1, F x * Complex.exp ((t*x : ℝ) * Complex.I))
      + ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, F x * Complex.exp ((t*x : ℝ) * Complex.I)
      = ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I) :=
    MeasureTheory.integral_add_compl measurableSet_Ioc (by
      refine hF.mul_bdd (c := 1) ?_ ?_
      · refine Continuous.aestronglyMeasurable ?_
        fun_prop
      · refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Complex.norm_exp]
        simp)
  have hval : ((∫ x in Set.Ioc (-1:ℝ) 1, Complex.I * (x:ℂ) * ((F 0 - F x)/(x:ℂ))
        * Complex.exp ((t*x : ℝ) * Complex.I))
      + F 0 * (2 * Complex.I * ((-(Real.sin t / t) : ℝ) : ℂ)))
      - ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, Complex.I * (x:ℂ) * (F x/(x:ℂ))
          * Complex.exp ((t*x : ℝ) * Complex.I)
      = -Complex.I * ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I) := by
    rw [hV1, hV3, ← hV5]
    push_cast
    ring
  rw [hval] at hsum
  exact hsum

/-- Chord bound: `‖e^{iθ} - 1‖ ≤ |θ|` (via `‖e^{iθ}-1‖ = 2|sin(θ/2)|`). -/
theorem norm_cexp_mul_I_sub_one_le (θ : ℝ) :
    ‖Complex.exp ((θ:ℂ) * Complex.I) - 1‖ ≤ |θ| := by
  have h0 : Complex.exp ((θ:ℂ) * Complex.I) - 1
      = ⟨Real.cos θ - 1, Real.sin θ⟩ := by
    rw [Complex.exp_mul_I]
    apply Complex.ext
    · simp [Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    · simp [Complex.add_im, Complex.mul_im, Complex.sin_ofReal_re]
  rw [h0]
  rw [Complex.norm_def, Complex.normSq_mk]
  have h1 : (Real.cos θ - 1) * (Real.cos θ - 1) + Real.sin θ * Real.sin θ
      = 4 * Real.sin (θ/2)^2 := by
    have h2 : Real.cos θ = 1 - 2 * Real.sin (θ/2)^2 := by
      have h5 := Real.cos_two_mul (θ/2)
      have h6 : 2 * (θ/2) = θ := by ring
      rw [h6] at h5
      have h7 := Real.sin_sq_add_cos_sq (θ/2)
      nlinarith
    have h3 := Real.sin_sq_add_cos_sq θ
    nlinarith
  rw [h1]
  have h4 : Real.sqrt (4 * Real.sin (θ/2)^2) = 2 * |Real.sin (θ/2)| := by
    rw [show (4 : ℝ) * Real.sin (θ/2)^2 = (2 * |Real.sin (θ/2)|)^2 by
      rw [mul_pow, sq_abs]
      ring]
    exact Real.sqrt_sq (by positivity)
  rw [h4]
  calc 2 * |Real.sin (θ/2)| ≤ 2 * |θ/2| := by
        have := Real.abs_sin_le_abs (x := θ/2)
        linarith
    _ = |θ| := by
        rw [abs_div, abs_two]
        ring

/-- **Poitou's `ρ`** (Lemme 2, p. 6-05): `ρ(t) = ∫ k(x)(1 - e^{itx})/x dx`. -/
noncomputable def rhoFT (k : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, k x * ((1 - Complex.exp ((t*x : ℝ) * Complex.I))/(x:ℂ))

@[simp]
theorem rhoFT_zero (k : ℝ → ℂ) : rhoFT k 0 = 0 := by
  rw [rhoFT]
  simp

/-- The `ρ` integrand is integrable for integrable `k` (chord bound `≤ |t|·‖k‖`). -/
theorem integrable_rhoFT_integrand {k : ℝ → ℂ} (hk : Integrable k) (t : ℝ) :
    Integrable (fun x : ℝ => k x * ((1 - Complex.exp ((t*x : ℝ) * Complex.I))/(x:ℂ))) := by
  refine MeasureTheory.Integrable.mono' (g := fun x => |t| * ‖k x‖)
    (hk.norm.const_mul _) ?_ ?_
  · refine hk.aestronglyMeasurable.mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      fun_prop
    · exact ((Complex.measurable_ofReal.inv).aestronglyMeasurable)
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
      positivity
    · rw [norm_mul, mul_comm (|t|) _]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      rw [div_le_iff₀ (abs_pos.mpr hx)]
      have h0 : ‖(1:ℂ) - Complex.exp ((t*x : ℝ) * Complex.I)‖
          = ‖Complex.exp ((t*x : ℝ) * Complex.I) - 1‖ := by
        rw [← norm_neg, neg_sub]
      rw [h0]
      calc ‖Complex.exp ((t*x : ℝ) * Complex.I) - 1‖ ≤ |t*x| :=
            norm_cexp_mul_I_sub_one_le (t*x)
        _ = |t| * |x| := abs_mul t x

/-- **Lemme 2, derivative of `ρ`** (Poitou p. 6-06): `ρ'(t) = -i·μ(t)` with
`μ(t) = ∫ k(x) e^{itx} dx`. -/
theorem hasDerivAt_rhoFT {k : ℝ → ℂ} (hk : Integrable k) (t : ℝ) :
    HasDerivAt (rhoFT k)
      (-Complex.I * ∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) t := by
  have hexp_meas : ∀ τ : ℝ, AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((τ * x : ℝ) * Complex.I)) volume := by
    intro τ
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have h := _root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ : ℝ => fun x : ℝ =>
      k x * ((1 - Complex.exp ((τ * x : ℝ) * Complex.I))/(x:ℂ)))
    (F' := fun τ : ℝ => fun x : ℝ =>
      -Complex.I * (k x * Complex.exp ((τ * x : ℝ) * Complex.I)))
    (bound := fun x => ‖k x‖)
    (μ := volume) (x₀ := t) (s := Metric.ball t 1)
    (Metric.ball_mem_nhds t one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · have h2 := h.2
    have h3 : (fun τ : ℝ => ∫ x : ℝ,
        k x * ((1 - Complex.exp ((τ * x : ℝ) * Complex.I))/(x:ℂ))) = rhoFT k := by
      funext τ
      rw [rhoFT]
    rw [h3] at h2
    rw [← MeasureTheory.integral_const_mul]
    exact h2
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    exact (integrable_rhoFT_integrand hk τ).aestronglyMeasurable
  · exact integrable_rhoFT_integrand hk t
  · refine AEStronglyMeasurable.const_mul ?_ _
    exact hk.aestronglyMeasurable.mul (hexp_meas t)
  · refine Filter.Eventually.of_forall (fun x => ?_)
    intro τ _
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, norm_mul, Complex.norm_exp]
    have h0 : (((τ * x : ℝ) : ℂ) * Complex.I).re = 0 := by
      simp
    rw [h0, Real.exp_zero, mul_one]
  · exact hk.norm
  · filter_upwards [MeasureTheory.ae_iff.mpr (by
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
      exact MeasureTheory.measure_singleton (0:ℝ) : volume {x : ℝ | ¬ x ≠ 0} = 0)]
      with x hx
    intro τ _
    · have h0 : HasDerivAt (fun τ : ℝ => τ * x) x τ := by
        simpa using (hasDerivAt_id τ).mul_const x
      have h1 : HasDerivAt (fun τ : ℝ => ((τ * x : ℝ) : ℂ)) ((x:ℝ):ℂ) τ :=
        h0.ofReal_comp
      have h2 : HasDerivAt (fun τ : ℝ => ((τ * x : ℝ) : ℂ) * Complex.I)
          ((x:ℂ) * Complex.I) τ := h1.mul_const Complex.I
      have h3 := h2.cexp
      have h4' : HasDerivAt (fun τ : ℝ => (1 : ℂ)
          - Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I))
          (0 - Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((x:ℂ) * Complex.I)) τ :=
        (hasDerivAt_const τ (1:ℂ)).sub h3
      have h4 : HasDerivAt (fun τ : ℝ => (1 : ℂ)
          - Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I))
          (-(Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((x:ℂ) * Complex.I))) τ := by
        have h9 : (0 : ℂ) - Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((x:ℂ) * Complex.I)
            = -(Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * ((x:ℂ) * Complex.I)) := by
          ring
        rw [h9] at h4'
        exact h4'
      have h5 := (h4.div_const ((x:ℂ))).const_mul (k x)
      have hval : k x * (-(Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I)
          * ((x:ℂ) * Complex.I)) / (x:ℂ))
          = -Complex.I * (k x * Complex.exp ((τ * x : ℝ) * Complex.I)) := by
        have hxne : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
        field_simp
      rw [hval] at h5
      exact h5

/-- `μ(t) = ∫ k(x)e^{itx} dx` is bounded by `‖k‖₁`. -/
theorem norm_muFT_le (k : ℝ → ℂ) (t : ℝ) :
    ‖∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)‖ ≤ ∫ x : ℝ, ‖k x‖ := by
  calc ‖∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)‖
      ≤ ∫ x : ℝ, ‖k x * Complex.exp ((t*x : ℝ) * Complex.I)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖k x‖ := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        show ‖k x * Complex.exp ((t*x : ℝ) * Complex.I)‖ = ‖k x‖
        rw [norm_mul, Complex.norm_exp]
        have h0 : (((t * x : ℝ) : ℂ) * Complex.I).re = 0 := by simp
        rw [h0, Real.exp_zero, mul_one]

/-- `μ` is continuous (dominated convergence). -/
theorem continuous_muFT {k : ℝ → ℂ} (hk : Integrable k) :
    Continuous (fun t : ℝ => ∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  refine MeasureTheory.continuousAt_of_dominated ?_ ?_ hk.norm ?_
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    refine hk.aestronglyMeasurable.mul ?_
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [norm_mul, Complex.norm_exp]
    have h0 : (((τ * x : ℝ) : ℂ) * Complex.I).re = 0 := by simp
    rw [h0, Real.exp_zero, mul_one]
  · refine Filter.Eventually.of_forall (fun x => ?_)
    refine Continuous.continuousAt ?_
    have h1 : Continuous (fun τ : ℝ => Complex.exp ((τ * x : ℝ) * Complex.I)) := by
      fun_prop
    exact h1.const_mul _

/-- `ρ` is continuous (it is differentiable everywhere). -/
theorem continuous_rhoFT {k : ℝ → ℂ} (hk : Integrable k) :
    Continuous (rhoFT k) := by
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  exact (hasDerivAt_rhoFT hk t).continuousAt

/-- The sinc tail is globally bounded. -/
theorem exists_bound_sincTail : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |sincTail t| ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := exists_bound_primitive_sinc
  refine ⟨π/2 + C, by positivity, fun t => ?_⟩
  rw [sincTail]
  have h0 : |∫ u in (0:ℝ)..t, Real.sin u / u| ≤ C := by
    rcases le_or_gt 0 t with h | h
    · exact hC t h
    · have h2 := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := -t)
        (f := fun u : ℝ => Real.sin u / u)
      have h3 : (∫ x in (0:ℝ)..(-t), Real.sin (-x) / (-x))
          = ∫ x in (0:ℝ)..(-t), Real.sin x / x := by
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        rw [Real.sin_neg, neg_div_neg_eq]
      rw [h3] at h2
      simp only [neg_neg, neg_zero] at h2
      -- h2 : ∫ x in 0..(-t), sin x/x = ∫ x in t..0, sin x/x
      have h4 : (∫ u in (0:ℝ)..t, Real.sin u / u)
          = -∫ x in (0:ℝ)..(-t), Real.sin x / x := by
        rw [h2, intervalIntegral.integral_symm]
      rw [h4, abs_neg]
      exact hC (-t) (by linarith)
  calc |π/2 - ∫ u in (0:ℝ)..t, Real.sin u / u|
      ≤ |π/2| + |∫ u in (0:ℝ)..t, Real.sin u / u| := abs_sub _ _
    _ ≤ π/2 + C := by
        rw [abs_of_pos (by positivity : (0:ℝ) < π/2)]
        linarith

/-- Continuity in `t` of Fourier-type set integrals (dominated convergence). -/
theorem continuous_integral_mul_cexp {G : ℝ → ℂ} {s : Set ℝ} (hG : IntegrableOn G s) :
    Continuous (fun t : ℝ => ∫ x in s, G x * Complex.exp ((t*x : ℝ) * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  refine MeasureTheory.continuousAt_of_dominated ?_ ?_ hG.norm ?_
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    refine hG.aestronglyMeasurable.mul ?_
    refine (Continuous.aestronglyMeasurable ?_).restrict
    fun_prop
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [norm_mul, Complex.norm_exp]
    have h0 : (((τ * x : ℝ) : ℂ) * Complex.I).re = 0 := by simp
    rw [h0, Real.exp_zero, mul_one]
  · refine Filter.Eventually.of_forall (fun x => ?_)
    refine Continuous.continuousAt ?_
    have h1 : Continuous (fun τ : ℝ => Complex.exp ((τ * x : ℝ) * Complex.I)) := by
      fun_prop
    exact h1.const_mul _

/-- `γ` is continuous away from `0` (it is differentiable there). -/
theorem continuousAt_gammaFT {F : ℝ → ℂ} (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    {t : ℝ} (ht : t ≠ 0) : ContinuousAt (gammaFT F) t :=
  (hasDerivAt_gammaFT hF hFdiv ht).continuousAt

/-- `γ` is globally bounded on any compact window: the continuous pieces are bounded on
compacts and the sinc-tail jump term is globally bounded. -/
theorem exists_bound_gammaFT {F : ℝ → ℂ} (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Set.Icc a b, ‖gammaFT F t‖ ≤ C := by
  have hGtail : IntegrableOn (fun x : ℝ => F x/(x:ℂ)) (Set.Ioc (-1:ℝ) 1)ᶜ := by
    refine MeasureTheory.Integrable.mono' (hF.integrableOn.norm) ?_ ?_
    · refine ((hF.aestronglyMeasurable.restrict.mul
        ((Complex.measurable_ofReal.inv).aestronglyMeasurable.restrict)).congr ?_)
      exact Filter.Eventually.of_forall (fun x => (div_eq_mul_inv (F x) _).symm)
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc.compl).mpr ?_
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.mem_compl_iff, Set.mem_Ioc] at hx
      push Not at hx
      have hx1 : 1 ≤ |x| := by
        rcases le_or_gt x (-1) with h | h
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · have := hx h
          rw [abs_of_pos (by linarith)]
          linarith
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_self (norm_nonneg _) hx1
  obtain ⟨Cs, hCspos, hCs⟩ := exists_bound_sincTail
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    ((continuous_integral_mul_cexp hFdiv).continuousOn)
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    ((continuous_integral_mul_cexp hGtail).continuousOn)
  refine ⟨(|C₀| + 1) + ‖F 0‖ * (2 * Cs) + (|C₁| + 1), by positivity, fun t htmem => ?_⟩
  rw [gammaFT]
  set A : ℂ := ∫ x in Set.Ioc (-1:ℝ) 1, (F 0 - F x)/(x:ℂ)
      * Complex.exp ((t*x : ℝ) * Complex.I) with hA
  set B : ℂ := F 0 * (2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ)) with hB
  set D : ℂ := ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, F x/(x:ℂ)
      * Complex.exp ((t*x : ℝ) * Complex.I) with hD
  have h1 : ‖A + B - D‖ ≤ ‖A‖ + ‖B‖ + ‖D‖ := by
    have t1 : ‖A + B - D‖ ≤ ‖A + B‖ + ‖D‖ := norm_sub_le _ _
    have t2 : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    linarith
  refine le_trans h1 ?_
  have h2 : ‖B‖ ≤ ‖F 0‖ * (2 * Cs) := by
    rw [hB, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_mul]
    have hsign : |Real.sign t| ≤ 1 := by
      rcases lt_trichotomy t 0 with h | h | h
      · rw [Real.sign_of_neg h]
        norm_num
      · rw [h, Real.sign_zero]
        norm_num
      · rw [Real.sign_of_pos h]
        norm_num
    calc ‖(2:ℂ)‖ * (|Real.sign t| * abs (sincTail |t|))
        ≤ ‖(2:ℂ)‖ * (1 * Cs) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine mul_le_mul hsign (hCs (|t|)) (abs_nonneg _) zero_le_one
      _ = 2 * Cs := by
          rw [Complex.norm_ofNat]
          ring
  have h3 : ‖A‖ ≤ |C₀| + 1 := by
    rw [hA]
    refine le_trans (hC₀ t htmem) ?_
    calc C₀ ≤ |C₀| := le_abs_self _
      _ ≤ |C₀| + 1 := by linarith
  have h4 : ‖D‖ ≤ |C₁| + 1 := by
    rw [hD]
    refine le_trans (hC₁ t htmem) ?_
    calc C₁ ≤ |C₁| := le_abs_self _
      _ ≤ |C₁| + 1 := by linarith
  linarith

/-- **Integration by parts off zero** (Lemme 2, p. 6-06): on an interval avoiding `0`,
`∫_c^d ρφ = i(ρ(d)γ(d) - ρ(c)γ(c)) - ∫_c^d μγ`. -/
theorem integral_rhoFT_mul_phi_eq {k F : ℝ → ℂ} (hk : Integrable k) (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    {c d : ℝ} (h0 : (0:ℝ) ∉ Set.uIcc c d) :
    (∫ t in c..d, rhoFT k t * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      = Complex.I * (rhoFT k d * gammaFT F d - rhoFT k c * gammaFT F c)
        - ∫ t in c..d, (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t := by
  have hu : ∀ t ∈ Set.uIcc c d, HasDerivAt (rhoFT k)
      (-Complex.I * ∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) t :=
    fun t _ => hasDerivAt_rhoFT hk t
  have hv : ∀ t ∈ Set.uIcc c d, HasDerivAt (gammaFT F)
      (-Complex.I * ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)) t := by
    intro t ht
    refine hasDerivAt_gammaFT hF hFdiv ?_
    intro heq
    rw [heq] at ht
    exact h0 ht
  have hu' : IntervalIntegrable (fun t : ℝ =>
      -Complex.I * ∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) volume c d := by
    refine Continuous.intervalIntegrable ?_ c d
    exact (continuous_muFT hk).const_mul _
  have hv' : IntervalIntegrable (fun t : ℝ =>
      -Complex.I * ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)) volume c d := by
    refine Continuous.intervalIntegrable ?_ c d
    exact (continuous_muFT hF).const_mul _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  -- hibp : ∫ ρ·(-iφ) = ρ d γ d - ρ c γ c - ∫ (-iμ)·γ
  have h1 : (∫ t in c..d, rhoFT k t
      * (-Complex.I * ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      = -Complex.I * ∫ t in c..d,
          rhoFT k t * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  have h2 : (∫ t in c..d,
      (-Complex.I * ∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t)
      = -Complex.I * ∫ t in c..d,
          (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  rw [h1, h2] at hibp
  -- solve for ∫ρφ
  have hA : ∀ A : ℂ, Complex.I * (-Complex.I * A) = A := fun A => by
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  have h3 := congrArg (fun z => Complex.I * z) hibp
  rw [hA] at h3
  rw [mul_sub, hA] at h3
  exact h3

/-- **The fixed-`T` boundary identity** (Lemme 2, p. 6-06): letting `ε → 0` in the
integration by parts on `[-T, -ε]` and `[ε, T]`, the `ρ(±ε)γ(±ε)` boundary terms vanish
(`ρ(0) = 0`, `γ` bounded near `0`), leaving
`∫_{-T}^T ρφ = i(ρ(T)γ(T) - ρ(-T)γ(-T)) - ∫_{-T}^T μγ`. -/
theorem integral_rhoFT_mul_phi_symm {k F : ℝ → ℂ} (hk : Integrable k) (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hμγ : Integrable (fun t : ℝ =>
      (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t))
    {T : ℝ} (hT : 0 < T) :
    (∫ t in (-T)..T, rhoFT k t * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      = Complex.I * (rhoFT k T * gammaFT F T - rhoFT k (-T) * gammaFT F (-T))
        - ∫ t in (-T)..T,
            (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t := by
  set ρ := rhoFT k with hρ
  set γ := gammaFT F with hγ
  set μ : ℝ → ℂ := fun t => ∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I) with hμ
  set φ : ℝ → ℂ := fun t => ∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I) with hφ
  have hρφ_cont : Continuous (fun t => ρ t * φ t) :=
    (continuous_rhoFT hk).mul (continuous_muFT hF)
  have hμγ_ii : ∀ a b : ℝ, IntervalIntegrable (fun t => μ t * γ t) volume a b :=
    fun a b => hμγ.intervalIntegrable
  obtain ⟨Cγ, hCγpos, hCγ⟩ := exists_bound_gammaFT hF hFdiv (-1) 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hρφ_cont.continuousOn)
  -- the ε-parameterized decomposition
  have hEq : ∀ ε : ℝ, 0 < ε → ε < T →
      (∫ t in (-T)..T, ρ t * φ t)
      = (Complex.I * (ρ (-ε) * γ (-ε) - ρ (-T) * γ (-T)) - ∫ t in (-T)..(-ε), μ t * γ t)
        + (∫ t in (-ε)..ε, ρ t * φ t)
        + (Complex.I * (ρ T * γ T - ρ ε * γ ε) - ∫ t in ε..T, μ t * γ t) := by
    intro ε hε hεT
    have hsplit : (∫ t in (-T)..T, ρ t * φ t)
        = (∫ t in (-T)..(-ε), ρ t * φ t) + (∫ t in (-ε)..ε, ρ t * φ t)
          + ∫ t in ε..T, ρ t * φ t := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hρφ_cont.intervalIntegrable _ _) (hρφ_cont.intervalIntegrable _ _),
        intervalIntegral.integral_add_adjacent_intervals
        (hρφ_cont.intervalIntegrable _ _) (hρφ_cont.intervalIntegrable _ _)]
    rw [hsplit]
    rw [integral_rhoFT_mul_phi_eq hk hF hFdiv (c := -T) (d := -ε) (by
      rw [Set.uIcc_of_le (by linarith), Set.mem_Icc]
      push Not
      intro h
      linarith)]
    rw [integral_rhoFT_mul_phi_eq hk hF hFdiv (c := ε) (d := T) (by
      rw [Set.uIcc_of_le (by linarith), Set.mem_Icc]
      push Not
      intro h
      linarith)]
  -- limits of each ε-piece along 𝓝[>] 0
  have hρ0 : Tendsto (fun ε : ℝ => ρ ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 := (continuous_rhoFT hk).tendsto 0
    rw [show rhoFT k 0 = 0 from rhoFT_zero k] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hρ0' : Tendsto (fun ε : ℝ => ρ (-ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 := (continuous_rhoFT hk).tendsto 0
    rw [show rhoFT k 0 = 0 from rhoFT_zero k] at h0
    have h1 : Tendsto (fun ε : ℝ => -ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := (continuous_neg.tendsto (0:ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    exact h0.comp h1
  have hbd1 : Tendsto (fun ε : ℝ => ρ ε * γ ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hb : Tendsto (fun ε : ℝ => Cγ * ‖ρ ε‖) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using (hρ0.norm.const_mul Cγ)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
    rw [norm_mul]
    calc ‖ρ ε‖ * ‖γ ε‖ ≤ ‖ρ ε‖ * Cγ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact hCγ ε ⟨by linarith [hε.1], hε.2.le⟩
      _ = Cγ * ‖ρ ε‖ := mul_comm _ _
  have hbd2 : Tendsto (fun ε : ℝ => ρ (-ε) * γ (-ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hb : Tendsto (fun ε : ℝ => Cγ * ‖ρ (-ε)‖) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using (hρ0'.norm.const_mul Cγ)
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
    rw [norm_mul]
    calc ‖ρ (-ε)‖ * ‖γ (-ε)‖ ≤ ‖ρ (-ε)‖ * Cγ := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine hCγ (-ε) ⟨by linarith [hε.2], by linarith [hε.1]⟩
      _ = Cγ * ‖ρ (-ε)‖ := mul_comm _ _
  have hmid : Tendsto (fun ε : ℝ => ∫ t in (-ε)..ε, ρ t * φ t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hb : Tendsto (fun ε : ℝ => (2 * (|M| + 1)) * ε)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h0 : Tendsto (fun ε : ℝ => (2 * (|M| + 1)) * ε) (nhds 0) (nhds 0) := by
        have h1 : Tendsto (fun ε : ℝ => ε) (nhds (0:ℝ)) (nhds 0) := tendsto_id
        simpa using h1.const_mul (2 * (|M| + 1))
      exact h0.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hb
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
      have h0 := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := |M| + 1) (a := -ε) (b := ε) (f := fun t => ρ t * φ t) (fun t htmem => by
          rw [Set.uIoc_of_le (by linarith [hε.1] : -ε ≤ ε), Set.mem_Ioc] at htmem
          calc ‖ρ t * φ t‖ ≤ M := hM t ⟨by linarith [htmem.1, hε.2], by
                linarith [htmem.2, hε.2]⟩
            _ ≤ |M| + 1 := by
                have := le_abs_self M
                linarith)
      calc ‖∫ t in (-ε)..ε, ρ t * φ t‖ ≤ (|M| + 1) * |ε - (-ε)| := h0
        _ = (2 * (|M| + 1)) * ε := by
            rw [abs_of_pos (by linarith [hε.1] : (0:ℝ) < ε - (-ε))]
            ring
  have htail_pos : Tendsto (fun ε : ℝ => ∫ t in ε..T, μ t * γ t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t in (0:ℝ)..T, μ t * γ t)) := by
    have h0 : ∀ ε : ℝ, (∫ t in ε..T, μ t * γ t)
        = (∫ t in (0:ℝ)..T, μ t * γ t) - ∫ t in (0:ℝ)..ε, μ t * γ t := by
      intro ε
      rw [eq_sub_iff_add_eq, add_comm]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hμγ_ii 0 ε) (hμγ_ii ε T)
    refine Tendsto.congr (fun ε => (h0 ε).symm) ?_
    have h1 : Tendsto (fun ε : ℝ => ∫ t in (0:ℝ)..ε, μ t * γ t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h2 : Tendsto (fun ε : ℝ => ∫ t in Set.Ioc (0:ℝ) ε, μ t * γ t)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        refine hμγ.tendsto_setIntegral_nhds_zero ?_
        have h3 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          rw [show (0 : ENNReal) = ENNReal.ofReal 0 by simp]
          exact (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
        refine h3.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [Function.comp_apply, Real.volume_Ioc, sub_zero]
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [Set.mem_Ioi] at hε
      rw [intervalIntegral.integral_of_le hε.le]
    have h4 : Tendsto (fun ε : ℝ => (∫ t in (0:ℝ)..T, μ t * γ t)
        - ∫ t in (0:ℝ)..ε, μ t * γ t) (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((∫ t in (0:ℝ)..T, μ t * γ t) - 0)) := tendsto_const_nhds.sub h1
    simpa using h4
  have htail_neg : Tendsto (fun ε : ℝ => ∫ t in (-T)..(-ε), μ t * γ t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t in (-T)..(0:ℝ), μ t * γ t)) := by
    have h0 : ∀ ε : ℝ, (∫ t in (-T)..(-ε), μ t * γ t)
        = (∫ t in (-T)..(0:ℝ), μ t * γ t) - ∫ t in (-ε)..(0:ℝ), μ t * γ t := by
      intro ε
      rw [eq_sub_iff_add_eq]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hμγ_ii (-T) (-ε)) (hμγ_ii (-ε) 0)
    refine Tendsto.congr (fun ε => (h0 ε).symm) ?_
    have h1 : Tendsto (fun ε : ℝ => ∫ t in (-ε)..(0:ℝ), μ t * γ t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h2 : Tendsto (fun ε : ℝ => ∫ t in Set.Ioc (-ε) (0:ℝ), μ t * γ t)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        refine hμγ.tendsto_setIntegral_nhds_zero ?_
        have h3 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          rw [show (0 : ENNReal) = ENNReal.ofReal 0 by simp]
          exact (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
        refine h3.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [Function.comp_apply, Real.volume_Ioc, sub_neg_eq_add, zero_add]
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [Set.mem_Ioi] at hε
      rw [intervalIntegral.integral_of_le (by linarith : -ε ≤ 0)]
    have h4 : Tendsto (fun ε : ℝ => (∫ t in (-T)..(0:ℝ), μ t * γ t)
        - ∫ t in (-ε)..(0:ℝ), μ t * γ t) (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((∫ t in (-T)..(0:ℝ), μ t * γ t) - 0)) := tendsto_const_nhds.sub h1
    simpa using h4
  -- assemble the ε-limit of the right-hand side
  have hRHS : Tendsto (fun ε : ℝ =>
      (Complex.I * (ρ (-ε) * γ (-ε) - ρ (-T) * γ (-T)) - ∫ t in (-T)..(-ε), μ t * γ t)
        + (∫ t in (-ε)..ε, ρ t * φ t)
        + (Complex.I * (ρ T * γ T - ρ ε * γ ε) - ∫ t in ε..T, μ t * γ t))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((Complex.I * ((0:ℂ) - ρ (-T) * γ (-T)) - ∫ t in (-T)..(0:ℝ), μ t * γ t)
        + (0:ℂ)
        + (Complex.I * (ρ T * γ T - 0) - ∫ t in (0:ℝ)..T, μ t * γ t))) := by
    refine Filter.Tendsto.add (Filter.Tendsto.add ?_ hmid) ?_
    · refine Filter.Tendsto.sub ?_ htail_neg
      refine Filter.Tendsto.const_mul _ ?_
      exact (hbd2.sub_const _)
    · refine Filter.Tendsto.sub ?_ htail_pos
      refine Filter.Tendsto.const_mul _ ?_
      exact (tendsto_const_nhds.sub hbd1)
  -- the left side is constant; conclude by uniqueness of limits
  have hLHS : Tendsto (fun _ : ℝ => ∫ t in (-T)..T, ρ t * φ t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((Complex.I * ((0:ℂ) - ρ (-T) * γ (-T)) - ∫ t in (-T)..(0:ℝ), μ t * γ t)
        + (0:ℂ)
        + (Complex.I * (ρ T * γ T - 0) - ∫ t in (0:ℝ)..T, μ t * γ t))) := by
    refine hRHS.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hT] with ε hε
    exact (hEq ε hε.1 hε.2).symm
  have huniq := tendsto_nhds_unique tendsto_const_nhds hLHS
  have hadj : (∫ t in (-T)..(0:ℝ), μ t * γ t) + ∫ t in (0:ℝ)..T, μ t * γ t
      = ∫ t in (-T)..T, μ t * γ t :=
    intervalIntegral.integral_add_adjacent_intervals (hμγ_ii (-T) 0) (hμγ_ii 0 T)
  linear_combination huniq - hadj

/-- **Lemme 2** (Poitou p. 6-06): with the boundary decay `ργ → 0` at `±∞` and `μγ`
integrable, the symmetric truncations `∫_{-T}^{T} ρ(t)φ(t) dt` converge as `T → ∞`,
with value `-∫_ℝ μ(t)γ(t) dt`. -/
theorem tendsto_integral_rhoFT_mul_phi {k F : ℝ → ℂ}
    (hk : Integrable k) (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hμγ : Integrable (fun t : ℝ =>
      (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t))
    (htop : Tendsto (fun t : ℝ => rhoFT k t * gammaFT F t) atTop (nhds 0))
    (hbot : Tendsto (fun t : ℝ => rhoFT k t * gammaFT F t) atBot (nhds 0)) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
        rhoFT k t * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      atTop (nhds (-∫ t : ℝ,
        (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t)) := by
  have hev : (fun T : ℝ => ∫ t in (-T)..T,
      rhoFT k t * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      =ᶠ[atTop] (fun T : ℝ =>
        Complex.I * (rhoFT k T * gammaFT F T - rhoFT k (-T) * gammaFT F (-T))
        - ∫ t in (-T)..T,
            (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with T hT
    exact integral_rhoFT_mul_phi_symm hk hF hFdiv hμγ hT
  rw [Filter.tendsto_congr' hev]
  have hneg : Tendsto (fun T : ℝ => -T) atTop atBot :=
    Filter.tendsto_neg_atBot_iff.mpr Filter.tendsto_id
  have hb1 : Tendsto (fun T : ℝ => rhoFT k T * gammaFT F T) atTop (nhds 0) := htop
  have hb2 : Tendsto (fun T : ℝ => rhoFT k (-T) * gammaFT F (-T)) atTop (nhds 0) :=
    hbot.comp hneg
  have hboundary : Tendsto (fun T : ℝ =>
      Complex.I * (rhoFT k T * gammaFT F T - rhoFT k (-T) * gammaFT F (-T)))
      atTop (nhds 0) := by
    have h0 := (hb1.sub hb2).const_mul Complex.I
    simpa using h0
  have hint : Tendsto (fun T : ℝ => ∫ t in (-T)..T,
      (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t)
      atTop (nhds (∫ t : ℝ,
        (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral hμγ hneg Filter.tendsto_id
  have h1 := hboundary.sub hint
  simpa using h1

/-- **Convention bridge** (P-b): the kernel transform `μ(t) = ∫ k(x)e^{itx} dx` is the
mathlib Fourier integral at `-t/(2π)`. -/
theorem muFT_eq_fourierIntegral (k : ℝ → ℂ) (t : ℝ) :
    (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I))
      = 𝓕 k (-t/(2*π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show k x * Complex.exp ((t*x : ℝ) * Complex.I)
      = Complex.exp (((-2 * π * x * (-t/(2*π)) : ℝ) : ℂ) * Complex.I) • k x
  rw [smul_eq_mul]
  rw [show (-2 * π * x * (-t/(2*π)) : ℝ) = t * x by
    field_simp]
  ring

/-- **Multiplication formula against Schwartz functions** (Pa-1): for integrable `f`,
`∫ 𝓕Φ(x) • f(x) dx = ∫ Φ(ξ) • 𝓕f(ξ) dξ`. -/
theorem integral_fourier_schwartz_smul {f : ℝ → ℂ} (hf : Integrable f)
    (Φ : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, (𝓕 (Φ : ℝ → ℂ)) x • f x = ∫ ξ : ℝ, (Φ : ℝ → ℂ) ξ • (𝓕 f) ξ := by
  have h0 := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := innerₗ ℝ) (f := (Φ : ℝ → ℂ)) (g := f)
    (by fun_prop) (by fun_prop) (Φ.integrable) hf
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    exact real_inner_comm a b
  rw [hflip] at h0
  exact h0

/-- **The `L¹ ∩ L²` compatibility of the Fourier transform** (Pa-2): for `f` both
integrable and square-integrable, the abstract `L²` Fourier transform (extended from
Schwartz functions) agrees a.e. with the pointwise Fourier integral. Both sides define
the same tempered distribution, and locally integrable functions are a.e.-determined by
their distributional action. -/
theorem coeFn_fourier_toLp_two {f : ℝ → ℂ} (hf1 : Integrable f)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  set A : ℝ → ℂ := ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) with hA
  have hB_cont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous (by fun_prop) (by fun_prop) hf1
  have hsub_li : LocallyIntegrable (fun x => A x - 𝓕 f x) volume := by
    refine LocallyIntegrable.sub ?_ ?_
    · exact (Lp.memLp _).locallyIntegrable (by norm_num)
    · exact hB_cont.locallyIntegrable
  have h0 : ∀ᵐ x ∂(volume : Measure ℝ), A x - 𝓕 f x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hsub_li ?_
    intro g g_smooth g_cpt
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    set Φg := hg₁.toSchwartzMap hg₂ with hΦg
    have hΦg_coe : ∀ x : ℝ, Φg x = ((g x : ℝ) : ℂ) := fun x => rfl
    have hΦg_cont : Continuous (fun x : ℝ => Φg x) := Φg.continuous
    have hΦg_supp : HasCompactSupport (fun x : ℝ => Φg x) := hg₁
    have hΦg2 : MemLp (fun x : ℝ => Φg x) 2 (volume : Measure ℝ) :=
      hΦg_cont.memLp_of_hasCompactSupport (p := 2) hΦg_supp
    -- integrability of the two test pairings
    have hgA : Integrable (fun x => g x • A x) volume := by
      have h1 : Integrable ((fun x : ℝ => Φg x) * A) volume :=
        MemLp.integrable_mul hΦg2 (Lp.memLp _)
      refine h1.congr (Filter.Eventually.of_forall (fun x => ?_))
      show Φg x * A x = g x • A x
      rw [hΦg_coe x]
      exact Complex.real_smul.symm
    have hgB : Integrable (fun x => g x • 𝓕 f x) volume := by
      have h1 : Integrable (fun x : ℝ => Φg x * 𝓕 f x) volume := by
        refine Integrable.mul_bdd (c := ∫ y : ℝ, ‖f y‖)
          (hΦg_cont.integrable_of_hasCompactSupport hΦg_supp) ?_ ?_
        · exact hB_cont.aestronglyMeasurable
        · refine Filter.Eventually.of_forall (fun ξ => ?_)
          exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
      refine h1.congr (Filter.Eventually.of_forall (fun x => ?_))
      show Φg x * 𝓕 f x = g x • 𝓕 f x
      rw [hΦg_coe x]
      exact Complex.real_smul.symm
    -- the distributional chain
    have hchain : (∫ x, g x • A x) = ∫ x, g x • 𝓕 f x := by
      have c1 : (∫ x, g x • A x) = Lp.toTemperedDistribution (𝓕 (hf2.toLp f)) Φg := by
        rw [Lp.toTemperedDistribution_apply]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        show g x • A x = Φg x • A x
        rw [hΦg_coe x, Complex.real_smul, smul_eq_mul]
      have c2 : Lp.toTemperedDistribution (𝓕 (hf2.toLp f)) Φg
          = 𝓕 (Lp.toTemperedDistribution (hf2.toLp f)) Φg := by
        rw [Lp.fourier_toTemperedDistribution_eq]
      have c3 : 𝓕 (Lp.toTemperedDistribution (hf2.toLp f)) Φg
          = Lp.toTemperedDistribution (hf2.toLp f) (𝓕 Φg) := rfl
      have c4 : Lp.toTemperedDistribution (hf2.toLp f) (𝓕 Φg)
          = ∫ x, (𝓕 Φg) x • ((hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x :=
        Lp.toTemperedDistribution_apply _ _
      have c5 : (∫ x, (𝓕 Φg) x • ((hf2.toLp f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)
          = ∫ x, (𝓕 (fun y : ℝ => Φg y)) x • f x := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [hf2.coeFn_toLp] with x hx
        rw [hx]
        congr 1
      have c6 : (∫ x, (𝓕 (fun y : ℝ => Φg y)) x • f x)
          = ∫ ξ, (fun y : ℝ => Φg y) ξ • 𝓕 f ξ :=
        integral_fourier_schwartz_smul hf1 Φg
      have c7 : (∫ ξ, (fun y : ℝ => Φg y) ξ • 𝓕 f ξ) = ∫ ξ, g ξ • 𝓕 f ξ := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
        show Φg ξ • 𝓕 f ξ = g ξ • 𝓕 f ξ
        rw [hΦg_coe ξ, Complex.real_smul, smul_eq_mul]
      rw [c1, c2, c3, c4, c5, c6, c7]
    calc (∫ x, g x • (A x - 𝓕 f x))
        = (∫ x, g x • A x) - ∫ x, g x • 𝓕 f x := by
          rw [← MeasureTheory.integral_sub hgA hgB]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          show g x • (A x - 𝓕 f x) = g x • A x - g x • 𝓕 f x
          exact smul_sub _ _ _
      _ = 0 := by rw [hchain, sub_self]
  filter_upwards [h0] with x hx
  exact sub_eq_zero.mp hx

/-- The Fourier transform of the conjugate reflection is the conjugate transform:
`𝓕(conj ∘ k ∘ neg) = conj ∘ 𝓕k`. -/
theorem fourier_conj_neg (k : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => conj (k (-x))) ξ = conj (𝓕 k ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_conj]
  have h0 : (fun v : ℝ => conj (Complex.exp ((-2 * π * v * ξ : ℝ) * Complex.I) • k v))
      = fun v : ℝ => Complex.exp ((-2 * π * (-v) * ξ : ℝ) * Complex.I) • conj (k v) := by
    funext v
    rw [smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj]
    congr 2
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [h0]
  have h1 := integral_comp_neg_real
    (fun v : ℝ => Complex.exp ((-2 * π * (-v) * ξ : ℝ) * Complex.I) • conj (k v))
  rw [← h1]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  show Complex.exp ((-2 * π * v * ξ : ℝ) * Complex.I) • conj (k (-v))
      = Complex.exp ((-2 * π * (-(-v)) * ξ : ℝ) * Complex.I) • conj (k (-v))
  rw [neg_neg]

/-- **The Plancherel pairing** (Poitou p. 6-06): for `k, h ∈ L¹ ∩ L²`,
`∫ 𝓕k(ξ)·𝓕h(ξ) dξ = ∫ k(-x)·h(x) dx`. -/
theorem integral_fourier_mul_fourier {k h : ℝ → ℂ}
    (hk1 : Integrable k) (hk2 : MemLp k 2 (volume : Measure ℝ))
    (hh1 : Integrable h) (hh2 : MemLp h 2 (volume : Measure ℝ)) :
    ∫ ξ : ℝ, 𝓕 k ξ * 𝓕 h ξ = ∫ x : ℝ, k (-x) * h x := by
  classical
  set kstar : ℝ → ℂ := fun x => conj (k (-x)) with hkstar
  have hMP : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg _
  have hks1 : Integrable kstar := by
    have h0 : Integrable (fun x : ℝ => k (-x)) :=
      hMP.integrable_comp_of_integrable hk1
    exact memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr h0).star)
  have hks2 : MemLp kstar 2 (volume : Measure ℝ) := by
    have h0 : MemLp (fun x : ℝ => k (-x)) 2 (volume : Measure ℝ) :=
      hk2.comp_measurePreserving hMP
    exact h0.star
  -- the L² pairing
  have hpair := MeasureTheory.Lp.inner_fourier_eq
    (hks2.toLp kstar) (hh2.toLp h)
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at hpair
  -- identify the left side with ∫ 𝓕k·𝓕h
  have hL : (∫ a : ℝ, ⟪(𝓕 (hks2.toLp kstar) : Lp ℂ 2 (volume : Measure ℝ)) a,
        (𝓕 (hh2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) a⟫_ℂ)
      = ∫ ξ : ℝ, 𝓕 k ξ * 𝓕 h ξ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [coeFn_fourier_toLp_two hks1 hks2, coeFn_fourier_toLp_two hh1 hh2]
      with ξ h1 h2
    rw [RCLike.inner_apply, h1, h2, fourier_conj_neg, starRingEnd_self_apply]
    exact mul_comm _ _
  -- identify the right side with ∫ k(-x)·h(x)
  have hR : (∫ a : ℝ, ⟪(hks2.toLp kstar : Lp ℂ 2 (volume : Measure ℝ)) a,
        (hh2.toLp h : Lp ℂ 2 (volume : Measure ℝ)) a⟫_ℂ)
      = ∫ x : ℝ, k (-x) * h x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hks2.coeFn_toLp, hh2.coeFn_toLp] with x h1 h2
    rw [RCLike.inner_apply, h1, h2]
    rw [hkstar]
    simp only [starRingEnd_self_apply]
    exact mul_comm _ _
  rw [hL, hR] at hpair
  exact hpair

/-- **The mixed Plancherel pairing**: for `k ∈ L¹ ∩ L²` and `h ∈ L²` (not necessarily
integrable), `∫ 𝓕k(ξ)·(𝓕₂h)(ξ) dξ = ∫ k(-x)·h(x) dx`, where `𝓕₂h` is (a representative
of) the `L²` Fourier transform. -/
theorem integral_fourier_mul_fourierL2 {k h : ℝ → ℂ}
    (hk1 : Integrable k) (hk2 : MemLp k 2 (volume : Measure ℝ))
    (hh2 : MemLp h 2 (volume : Measure ℝ)) :
    (∫ ξ : ℝ, 𝓕 k ξ * ((𝓕 (hh2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ)
      = ∫ x : ℝ, k (-x) * h x := by
  classical
  set kstar : ℝ → ℂ := fun x => conj (k (-x)) with hkstar
  have hMP : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg _
  have hks1 : Integrable kstar := by
    have h0 : Integrable (fun x : ℝ => k (-x)) :=
      hMP.integrable_comp_of_integrable hk1
    exact memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr h0).star)
  have hks2 : MemLp kstar 2 (volume : Measure ℝ) := by
    have h0 : MemLp (fun x : ℝ => k (-x)) 2 (volume : Measure ℝ) :=
      hk2.comp_measurePreserving hMP
    exact h0.star
  have hpair := MeasureTheory.Lp.inner_fourier_eq
    (hks2.toLp kstar) (hh2.toLp h)
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at hpair
  have hL : (∫ a : ℝ, ⟪(𝓕 (hks2.toLp kstar) : Lp ℂ 2 (volume : Measure ℝ)) a,
        (𝓕 (hh2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) a⟫_ℂ)
      = ∫ ξ : ℝ, 𝓕 k ξ * ((𝓕 (hh2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [coeFn_fourier_toLp_two hks1 hks2] with ξ h1
    rw [RCLike.inner_apply, h1, fourier_conj_neg, starRingEnd_self_apply]
    exact mul_comm _ _
  have hR : (∫ a : ℝ, ⟪(hks2.toLp kstar : Lp ℂ 2 (volume : Measure ℝ)) a,
        (hh2.toLp h : Lp ℂ 2 (volume : Measure ℝ)) a⟫_ℂ)
      = ∫ x : ℝ, k (-x) * h x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hks2.coeFn_toLp, hh2.coeFn_toLp] with x h1 h2
    rw [RCLike.inner_apply, h1, h2]
    rw [hkstar]
    simp only [starRingEnd_self_apply]
    exact mul_comm _ _
  rw [hL, hR] at hpair
  exact hpair

/-- Two-sided version of the symmetric-tail limit: for `t ≠ 0`,
`∫_1^X (e^{itx} - e^{-itx})/x dx → 2i·sign(t)·sincTail|t|`. -/
theorem tendsto_integral_cexp_sub_div_window' {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun X : ℝ => ∫ x in (1:ℝ)..X,
        (Complex.exp ((t*x : ℝ) * Complex.I) - Complex.exp (-((t*x : ℝ)) * Complex.I))
          / (x:ℂ))
      atTop (nhds (2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ))) := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · -- t < 0: flip signs and use the positive case at |t| = -t
    have h0 := tendsto_integral_cexp_sub_div_window (t := -t) (by linarith)
    have h1 : (fun X : ℝ => ∫ x in (1:ℝ)..X,
        (Complex.exp ((t*x : ℝ) * Complex.I) - Complex.exp (-((t*x : ℝ)) * Complex.I))
          / (x:ℂ))
        = fun X : ℝ => -∫ x in (1:ℝ)..X,
          (Complex.exp ((-t*x : ℝ) * Complex.I) - Complex.exp (-((-t*x : ℝ)) * Complex.I))
            / (x:ℂ) := by
      funext X
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [show ((-t*x : ℝ) : ℂ) = -((t*x : ℝ) : ℂ) by push_cast; ring]
      rw [show (-(-((t*x : ℝ) : ℂ))) = ((t*x : ℝ) : ℂ) by ring]
      ring
    rw [h1]
    have h2 := h0.neg
    have h3 : -(2 * Complex.I * ((sincTail (-t) : ℝ) : ℂ))
        = 2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ) := by
      rw [Real.sign_of_neg hneg, abs_of_neg hneg]
      push_cast
      ring
    rw [h3] at h2
    exact h2
  · have h0 := tendsto_integral_cexp_sub_div_window hpos
    have h3 : 2 * Complex.I * ((sincTail t : ℝ) : ℂ)
        = 2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ) := by
      rw [Real.sign_of_pos hpos, abs_of_pos hpos, one_mul]
    rw [h3] at h0
    exact h0

/-- **Pointwise convergence of truncated Fourier integrals to Poitou's `γ`** (P-c, step 1):
for `t ≠ 0`, `∫_{-n}^{n} (F(0)-F(x))/x · e^{itx} dx → gammaFT F t`. -/
theorem tendsto_truncated_fourier_gammaFT {F : ℝ → ℂ} (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => ∫ x in Set.Ioc (-(n:ℝ)) (n:ℝ),
        ((F 0 - F x)/(x:ℂ)) * Complex.exp ((t*x : ℝ) * Complex.I))
      atTop (nhds (gammaFT F t)) := by
  set h : ℝ → ℂ := fun x => (F 0 - F x)/(x:ℂ) with hh
  set e : ℝ → ℂ := fun x => Complex.exp ((t*x : ℝ) * Complex.I) with he
  have he_bd : ∀ x : ℝ, ‖e x‖ = 1 := by
    intro x
    rw [he]
    simp only
    rw [Complex.norm_exp]
    simp
  have he_meas : AEStronglyMeasurable e volume := by
    refine Continuous.aestronglyMeasurable ?_
    rw [he]
    fun_prop
  -- integrabilities
  have hFe_int : Integrable (fun x : ℝ => (F x/(x:ℂ)) * e x) volume → True := fun _ => trivial
  have hFx_tail : IntegrableOn (fun x : ℝ => F x/(x:ℂ)) (Set.Ioc (-1:ℝ) 1)ᶜ := by
    refine MeasureTheory.Integrable.mono' (hF.integrableOn.norm) ?_ ?_
    · refine ((hF.aestronglyMeasurable.restrict.mul
        ((Complex.measurable_ofReal.inv).aestronglyMeasurable.restrict)).congr ?_)
      exact Filter.Eventually.of_forall (fun x => (div_eq_mul_inv (F x) _).symm)
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc.compl).mpr ?_
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Set.mem_compl_iff, Set.mem_Ioc] at hx
      push Not at hx
      have hx1 : 1 ≤ |x| := by
        rcases le_or_gt x (-1) with h' | h'
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · have := hx h'
          rw [abs_of_pos (by linarith)]
          linarith
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_self (norm_nonneg _) hx1
  -- eventually-n decomposition
  have hEq : ∀ n : ℕ, 1 ≤ n →
      (∫ x in Set.Ioc (-(n:ℝ)) (n:ℝ), h x * e x)
      = (∫ x in Set.Ioc (-1:ℝ) 1, h x * e x)
        + (F 0 * ∫ x in (1:ℝ)..(n:ℝ),
            (Complex.exp ((t*x : ℝ) * Complex.I)
              - Complex.exp (-((t*x : ℝ)) * Complex.I)) / (x:ℂ))
        - ∫ x in (Set.Ioc (-(n:ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) (n:ℝ)), (F x/(x:ℂ)) * e x := by
    intro n hn
    have hn' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hsplit : Set.Ioc (-(n:ℝ)) (n:ℝ)
        = Set.Ioc (-(n:ℝ)) (-1:ℝ) ∪ Set.Ioc (-1:ℝ) 1 ∪ Set.Ioc (1:ℝ) (n:ℝ) := by
      rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
        Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]
    -- integrability of h·e on the three pieces
    have hmid : IntegrableOn (fun x => h x * e x) (Set.Ioc (-1:ℝ) 1) := by
      refine hFdiv.mul_bdd (c := 1) (he_meas.restrict) ?_
      exact Filter.Eventually.of_forall (fun x => by rw [he_bd x])
    have hF0_int : ∀ a b : ℝ, Set.Ioc a b ⊆ (Set.Ioc (-1:ℝ) 1)ᶜ →
        IntegrableOn (fun x : ℝ => F 0/(x:ℂ) * e x) (Set.Ioc a b) := by
      intro a b hsub
      refine MeasureTheory.Integrable.mono'
        (g := fun _ => ‖F 0‖)
        (MeasureTheory.integrableOn_const (by
          rw [Real.volume_Ioc]
          exact ENNReal.ofReal_ne_top)) ?_ ?_
      · refine AEStronglyMeasurable.mul ?_ (he_meas.restrict)
        exact ((Complex.measurable_ofReal.inv).aestronglyMeasurable.const_mul
          (F 0)).congr (Filter.Eventually.of_forall (fun x =>
            (div_eq_mul_inv (F 0) ((x:ℝ):ℂ)).symm)) |>.restrict
      · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        have hx1 : 1 ≤ |x| := by
          have := hsub hx
          rw [Set.mem_compl_iff, Set.mem_Ioc] at this
          push Not at this
          rcases le_or_gt x (-1) with h' | h'
          · rw [abs_of_nonpos (by linarith)]
            linarith
          · have := this h'
            rw [abs_of_pos (by linarith)]
            linarith
        rw [norm_mul, he_bd x, mul_one, norm_div, Complex.norm_real,
          Real.norm_eq_abs]
        exact div_le_self (norm_nonneg _) hx1
    have hFx_int : ∀ a b : ℝ, Set.Ioc a b ⊆ (Set.Ioc (-1:ℝ) 1)ᶜ →
        IntegrableOn (fun x => (F x/(x:ℂ)) * e x) (Set.Ioc a b) := by
      intro a b hsub
      refine ((hFx_tail.mono_set hsub).mul_bdd (c := 1) (he_meas.restrict) ?_)
      exact Filter.Eventually.of_forall (fun x => by rw [he_bd x])
    have htail_int : ∀ a b : ℝ, Set.Ioc a b ⊆ (Set.Ioc (-1:ℝ) 1)ᶜ →
        IntegrableOn (fun x => h x * e x) (Set.Ioc a b) := by
      intro a b hsub
      refine ((hF0_int a b hsub).sub (hFx_int a b hsub)).congr ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
      refine Filter.Eventually.of_forall (fun x _ => ?_)
      show F 0/(x:ℂ) * e x - (F x/(x:ℂ)) * e x = h x * e x
      rw [hh]
      simp only
      ring
    have hneg_sub : Set.Ioc (-(n:ℝ)) (-1:ℝ) ⊆ (Set.Ioc (-1:ℝ) 1)ᶜ := by
      intro x hx
      rw [Set.mem_Ioc] at hx
      rw [Set.mem_compl_iff, Set.mem_Ioc]
      push Not
      intro h'
      linarith [hx.2]
    have hpos_sub : Set.Ioc (1:ℝ) (n:ℝ) ⊆ (Set.Ioc (-1:ℝ) 1)ᶜ := by
      intro x hx
      rw [Set.mem_Ioc] at hx
      rw [Set.mem_compl_iff, Set.mem_Ioc]
      push Not
      intro h'
      linarith [hx.1]
    -- split the integral
    have hdisj1 : Disjoint (Set.Ioc (-(n:ℝ)) (-1:ℝ)) (Set.Ioc (-1:ℝ) 1) := by
      refine Set.disjoint_left.mpr (fun x hx hx' => ?_)
      rw [Set.mem_Ioc] at hx hx'
      linarith [hx.2, hx'.1]
    have hdisj2 : Disjoint (Set.Ioc (-(n:ℝ)) (-1:ℝ) ∪ Set.Ioc (-1:ℝ) 1)
        (Set.Ioc (1:ℝ) (n:ℝ)) := by
      refine Set.disjoint_left.mpr (fun x hx hx' => ?_)
      rw [Set.mem_Ioc] at hx'
      rcases hx with hx | hx <;> rw [Set.mem_Ioc] at hx
      · linarith [hx.2, hx'.1]
      · linarith [hx.2, hx'.1]
    rw [hsplit, MeasureTheory.setIntegral_union hdisj2 measurableSet_Ioc
      (MeasureTheory.IntegrableOn.union (htail_int _ _ hneg_sub) hmid)
      (htail_int _ _ hpos_sub),
      MeasureTheory.setIntegral_union hdisj1 measurableSet_Ioc
      (htail_int _ _ hneg_sub) hmid]
    -- tail algebra
    have htail_eq : ∀ a b : ℝ, Set.Ioc a b ⊆ (Set.Ioc (-1:ℝ) 1)ᶜ →
        (∫ x in Set.Ioc a b, h x * e x)
        = (∫ x : ℝ in Set.Ioc a b, F 0/(x:ℂ) * e x)
          - ∫ x in Set.Ioc a b, (F x/(x:ℂ)) * e x := by
      intro a b hsub
      rw [← MeasureTheory.integral_sub (hF0_int a b hsub) (hFx_int a b hsub)]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
      show h x * e x = F 0/(x:ℂ) * e x - (F x/(x:ℂ)) * e x
      rw [hh]
      simp only
      ring
    rw [htail_eq _ _ hneg_sub, htail_eq _ _ hpos_sub]
    -- pull out F 0 and reflect the negative window
    have hF0pull : ∀ a b : ℝ, (∫ x : ℝ in Set.Ioc a b, F 0/(x:ℂ) * e x)
        = F 0 * ∫ x in Set.Ioc a b, e x / (x:ℂ) := by
      intro a b
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
      ring
    rw [hF0pull, hF0pull]
    have hIoc_int : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => e x / (x:ℂ)) volume a b
        → True := fun _ _ _ => trivial
    have hnegint : (∫ x in Set.Ioc (-(n:ℝ)) (-1:ℝ), e x / (x:ℂ))
        = -∫ x in (1:ℝ)..(n:ℝ), Complex.exp (-((t*x : ℝ)) * Complex.I) / (x:ℂ) := by
      rw [← intervalIntegral.integral_of_le (by linarith : -(n:ℝ) ≤ -1)]
      have h0 := intervalIntegral.integral_comp_neg (a := (1:ℝ)) (b := (n:ℝ))
        (f := fun y : ℝ => e y / (y:ℂ))
      -- h0 : ∫ x in 1..n, e(-x)/(-x) = ∫ x in -n..-1, e x/x
      rw [← h0, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      show e (-x) / ((-x : ℝ):ℂ) = -(Complex.exp (-((t*x : ℝ)) * Complex.I) / (x:ℂ))
      rw [he]
      simp only
      rw [show ((t*(-x) : ℝ) : ℂ) = -((t*x : ℝ) : ℂ) by push_cast; ring]
      push_cast
      rw [div_neg]
    have hposint : (∫ x in Set.Ioc (1:ℝ) (n:ℝ), e x / (x:ℂ))
        = ∫ x in (1:ℝ)..(n:ℝ), Complex.exp ((t*x : ℝ) * Complex.I) / (x:ℂ) := by
      rw [← intervalIntegral.integral_of_le hn']
    rw [hnegint, hposint]
    -- recombine the interval integrals
    have hcont1 : IntervalIntegrable
        (fun x : ℝ => Complex.exp ((t*x : ℝ) * Complex.I) / (x:ℂ)) volume 1 (n:ℝ) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
      intro x hx
      rw [Set.uIcc_of_le hn', Set.mem_Icc] at hx
      exact_mod_cast (by linarith : x ≠ 0)
    have hcont2 : IntervalIntegrable
        (fun x : ℝ => Complex.exp (-((t*x : ℝ)) * Complex.I) / (x:ℂ)) volume 1 (n:ℝ) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
      intro x hx
      rw [Set.uIcc_of_le hn', Set.mem_Icc] at hx
      exact_mod_cast (by linarith : x ≠ 0)
    have hwindow : (F 0 * ∫ x in (1:ℝ)..(n:ℝ),
          Complex.exp ((t*x : ℝ) * Complex.I) / (x:ℂ))
        + F 0 * -∫ x in (1:ℝ)..(n:ℝ), Complex.exp (-((t*x : ℝ)) * Complex.I) / (x:ℂ)
        = F 0 * ∫ x in (1:ℝ)..(n:ℝ),
            (Complex.exp ((t*x : ℝ) * Complex.I)
              - Complex.exp (-((t*x : ℝ)) * Complex.I)) / (x:ℂ) := by
      have hcont2' : IntervalIntegrable
          (fun x : ℝ => -(Complex.exp (-((t*x : ℝ)) * Complex.I) / (x:ℂ)))
          volume 1 (n:ℝ) := hcont2.neg
      rw [← mul_add, ← intervalIntegral.integral_neg,
        ← intervalIntegral.integral_add hcont1 hcont2']
      congr 1
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      ring
    -- recombine the F-tail set integrals
    have hFtails : (∫ x in Set.Ioc (-(n:ℝ)) (-1:ℝ), (F x/(x:ℂ)) * e x)
        + ∫ x in Set.Ioc (1:ℝ) (n:ℝ), (F x/(x:ℂ)) * e x
        = ∫ x in (Set.Ioc (-(n:ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) (n:ℝ)), (F x/(x:ℂ)) * e x := by
      rw [MeasureTheory.setIntegral_union ?_ measurableSet_Ioc
        (hFx_int _ _ hneg_sub) (hFx_int _ _ hpos_sub)]
      refine Set.disjoint_left.mpr (fun x hx hx' => ?_)
      rw [Set.mem_Ioc] at hx hx'
      linarith [hx.2, hx'.1]
    linear_combination hwindow - hFtails
  -- assemble the limit
  have hlim : Tendsto (fun n : ℕ =>
      (∫ x in Set.Ioc (-1:ℝ) 1, h x * e x)
        + (F 0 * ∫ x in (1:ℝ)..((n:ℕ):ℝ),
            (Complex.exp ((t*x : ℝ) * Complex.I)
              - Complex.exp (-((t*x : ℝ)) * Complex.I)) / (x:ℂ))
        - ∫ x in (Set.Ioc (-((n:ℕ):ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) ((n:ℕ):ℝ)),
            (F x/(x:ℂ)) * e x)
      atTop (nhds (gammaFT F t)) := by
    -- window limit
    have hT2 : Tendsto (fun n : ℕ => F 0 * ∫ x in (1:ℝ)..((n:ℕ):ℝ),
        (Complex.exp ((t*x : ℝ) * Complex.I)
          - Complex.exp (-((t*x : ℝ)) * Complex.I)) / (x:ℂ))
        atTop (nhds (F 0 * (2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ)))) := by
      refine Filter.Tendsto.const_mul _ ?_
      exact (tendsto_integral_cexp_sub_div_window' ht).comp
        tendsto_natCast_atTop_atTop
    -- tail limit: the union is exactly the complement
    have hUnion : (⋃ n : ℕ, (Set.Ioc (-((n:ℕ):ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) ((n:ℕ):ℝ)))
        = (Set.Ioc (-1:ℝ) 1)ᶜ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union, Set.mem_Ioc, Set.mem_compl_iff]
      constructor
      · rintro ⟨n, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · push Not
          intro h'
          linarith
        · push Not
          intro h'
          linarith
      · intro hx
        push Not at hx
        rcases le_or_gt x (-1) with h' | h'
        · obtain ⟨n, hn⟩ := exists_nat_gt (-x)
          exact ⟨n, Or.inl ⟨by linarith, h'⟩⟩
        · have h'' := hx h'
          obtain ⟨n, hn⟩ := exists_nat_gt x
          exact ⟨n, Or.inr ⟨h'', hn.le⟩⟩
    have hmono : Monotone (fun n : ℕ =>
        Set.Ioc (-((n:ℕ):ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) ((n:ℕ):ℝ)) := by
      intro m n hmn
      have hmn' : ((m:ℕ):ℝ) ≤ ((n:ℕ):ℝ) := by exact_mod_cast hmn
      refine Set.union_subset_union ?_ ?_
      · exact Set.Ioc_subset_Ioc_left (by linarith)
      · exact Set.Ioc_subset_Ioc_right hmn'
    have hint_union : IntegrableOn (fun x => (F x/(x:ℂ)) * e x)
        (⋃ n : ℕ, (Set.Ioc (-((n:ℕ):ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) ((n:ℕ):ℝ))) := by
      rw [hUnion]
      refine hFx_tail.mul_bdd (c := 1) (he_meas.restrict) ?_
      exact Filter.Eventually.of_forall (fun x => by rw [he_bd x])
    have hT3 : Tendsto (fun n : ℕ =>
        ∫ x in (Set.Ioc (-((n:ℕ):ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) ((n:ℕ):ℝ)),
          (F x/(x:ℂ)) * e x)
        atTop (nhds (∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, (F x/(x:ℂ)) * e x)) := by
      have h0 := MeasureTheory.tendsto_setIntegral_of_monotone₀
        (s := fun n : ℕ => Set.Ioc (-((n:ℕ):ℝ)) (-1:ℝ) ∪ Set.Ioc (1:ℝ) ((n:ℕ):ℝ))
        (fun n => (measurableSet_Ioc.union measurableSet_Ioc).nullMeasurableSet)
        hmono hint_union
      rw [hUnion] at h0
      exact h0
    have hT1 : Tendsto (fun _ : ℕ => ∫ x in Set.Ioc (-1:ℝ) 1, h x * e x)
        atTop (nhds (∫ x in Set.Ioc (-1:ℝ) 1, h x * e x)) := tendsto_const_nhds
    have hfinal := (hT1.add hT2).sub hT3
    have hval : (∫ x in Set.Ioc (-1:ℝ) 1, h x * e x)
        + F 0 * (2 * Complex.I * ((Real.sign t * sincTail |t| : ℝ) : ℂ))
        - ∫ x in (Set.Ioc (-1:ℝ) 1)ᶜ, (F x/(x:ℂ)) * e x = gammaFT F t := by
      rw [gammaFT]
    rw [hval] at hfinal
    exact hfinal
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (hEq n hn).symm

/-- **L² convergence of truncations**: for `g ∈ L²`,
`eLpNorm (1_{(-n,n]}·g - g) 2 → 0`. -/
theorem tendsto_eLpNorm_indicator_truncation {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    Tendsto (fun n : ℕ => eLpNorm
        ((Set.Ioc (-(n:ℝ)) (n:ℝ)).indicator g - g) 2 (volume : Measure ℝ))
      atTop (nhds 0) := by
  have hkey : ∀ n : ℕ, eLpNorm ((Set.Ioc (-(n:ℝ)) (n:ℝ)).indicator g - g) 2 volume
      = (∫⁻ x, ((Set.Ioc (-(n:ℝ)) (n:ℝ))ᶜ.indicator (fun y => ‖g y‖ₑ ^ (2:ℝ)) x))
        ^ (1/(2:ℝ)) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    rw [show ((2:ℝ≥0∞).toReal) = (2:ℝ) by norm_num]
    congr 1
    refine lintegral_congr (fun x => ?_)
    rw [Pi.sub_apply]
    rcases (em (x ∈ Set.Ioc (-(n:ℝ)) (n:ℝ))) with hx | hx
    · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx)]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (by simpa using hx)]
      simp [enorm_neg]
  simp only [hkey]
  -- dominated convergence for the inner lintegral
  have hdom : Tendsto (fun n : ℕ => ∫⁻ x,
      ((Set.Ioc (-(n:ℝ)) (n:ℝ))ᶜ.indicator (fun y => ‖g y‖ₑ ^ (2:ℝ)) x))
      atTop (nhds 0) := by
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume : Measure ℝ) := by simp
    rw [h0]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun x => ‖g x‖ₑ ^ (2:ℝ)) ?_ ?_ ?_ ?_
    · intro n
      refine AEMeasurable.indicator ?_ (measurableSet_Ioc.compl)
      exact (hg.aestronglyMeasurable.enorm.pow_const _)
    · intro n
      refine Filter.Eventually.of_forall (fun x => ?_)
      rcases (em (x ∈ (Set.Ioc (-(n:ℝ)) (n:ℝ))ᶜ)) with hx | hx
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact bot_le
    · have := hg.eLpNorm_lt_top
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
        show ((2:ℝ≥0∞).toReal) = (2:ℝ) by norm_num] at this
      have h1 : (∫⁻ x, ‖g x‖ₑ ^ (2:ℝ)) < ⊤ := by
        by_contra hcon
        push Not at hcon
        rw [top_le_iff.mp hcon] at this
        simp at this
      exact h1.ne
    · refine Filter.Eventually.of_forall (fun x => ?_)
      obtain ⟨N, hN⟩ := exists_nat_gt |x|
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hx : x ∈ Set.Ioc (-(n:ℝ)) (n:ℝ) := by
        rw [Set.mem_Ioc]
        have h2 : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        constructor
        · nlinarith [abs_nonneg x, neg_abs_le x]
        · nlinarith [le_abs_self x]
      rw [Set.indicator_of_notMem (by simpa using hx)]
  -- continuity of `· ^ (1/2)` at 0
  have hcont : Tendsto (fun z : ℝ≥0∞ => z ^ (1/(2:ℝ))) (nhds 0) (nhds 0) := by
    have h0 := (ENNReal.continuous_rpow_const (y := 1/(2:ℝ))).tendsto 0
    rw [show (0:ℝ≥0∞) ^ (1/(2:ℝ)) = 0 by
      rw [ENNReal.zero_rpow_of_pos (by norm_num)]] at h0
    exact h0
  exact hcont.comp hdom

/-- **Poitou's `γ` is the `L²` Fourier transform** (P-c): for `F` integrable with
`(F(0)-F(x))/x` locally integrable at `0` and square-integrable, `gammaFT F` agrees a.e.
with a representative of the `L²` Fourier transform of `(F(0)-F(x))/x`, reflected and
rescaled to the `e^{itx}` convention. -/
theorem gammaFT_ae_eq_fourierL2 {F : ℝ → ℂ} (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ)) :
    (fun t : ℝ => gammaFT F t) =ᵐ[volume]
      (fun t : ℝ => ((𝓕 (hFdiv2.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        (-t/(2*π))) := by
  classical
  set h : ℝ → ℂ := fun x => (F 0 - F x)/(x:ℂ) with hh
  set hn : ℕ → ℝ → ℂ := fun n => (Set.Ioc (-(n:ℝ)) (n:ℝ)).indicator h with hhn
  -- truncations are L¹ ∩ L²
  have hIntOn : ∀ n : ℕ, IntegrableOn h (Set.Ioc (-(n:ℝ)) (n:ℝ)) := by
    intro n
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (-(n:ℝ)) (n:ℝ))) := by
      constructor
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    have h1 : MemLp h 2 (volume.restrict (Set.Ioc (-(n:ℝ)) (n:ℝ))) :=
      hFdiv2.restrict _
    have h2 : MemLp (fun _ : ℝ => (1:ℂ)) 2
        (volume.restrict (Set.Ioc (-(n:ℝ)) (n:ℝ))) := memLp_const _
    have h3 := MemLp.integrable_mul h1 h2
    refine h3.congr (Filter.Eventually.of_forall (fun x => ?_))
    show h x * 1 = h x
    rw [mul_one]
  have hn1 : ∀ n : ℕ, Integrable (hn n) := by
    intro n
    rw [hhn]
    exact (integrable_indicator_iff measurableSet_Ioc).mpr (hIntOn n)
  have hn2 : ∀ n : ℕ, MemLp (hn n) 2 (volume : Measure ℝ) := by
    intro n
    rw [hhn]
    exact hFdiv2.indicator measurableSet_Ioc
  -- the eLpNorm of the transform difference equals the eLpNorm of the truncation error
  have hbr : ∀ u : Lp ℂ 2 (volume : Measure ℝ),
      (𝓕 u : Lp ℂ 2 (volume : Measure ℝ))
        = MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ u := fun _ => rfl
  have hLp_eLp : ∀ c : Lp ℂ 2 (volume : Measure ℝ),
      eLpNorm (⇑(𝓕 c : Lp ℂ 2 (volume : Measure ℝ))) 2 volume = eLpNorm (⇑c) 2 volume := by
    intro c
    have e1 : eLpNorm (⇑(𝓕 c : Lp ℂ 2 (volume : Measure ℝ))) 2 volume
        = ENNReal.ofReal ‖(𝓕 c : Lp ℂ 2 (volume : Measure ℝ))‖ := by
      rw [MeasureTheory.Lp.norm_def,
        ENNReal.ofReal_toReal (MeasureTheory.Lp.eLpNorm_ne_top _)]
    have e2 : eLpNorm (⇑c) 2 volume = ENNReal.ofReal ‖c‖ := by
      rw [MeasureTheory.Lp.norm_def,
        ENNReal.ofReal_toReal (MeasureTheory.Lp.eLpNorm_ne_top _)]
    rw [e1, e2, MeasureTheory.Lp.norm_fourier_eq]
  have hstep : ∀ n : ℕ,
      eLpNorm ((𝓕 (fun x : ℝ => hn n x))
        - ((𝓕 (hFdiv2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) 2 volume
      = eLpNorm (hn n - h) 2 volume := by
    intro n
    have h1 : (𝓕 (fun x : ℝ => hn n x))
        =ᵐ[volume] ((𝓕 ((hn2 n).toLp (hn n)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
      (coeFn_fourier_toLp_two (hn1 n) (hn2 n)).symm
    rw [eLpNorm_congr_ae (Filter.EventuallyEq.sub h1 (Filter.EventuallyEq.refl _ _))]
    have h2 : (((𝓕 ((hn2 n).toLp (hn n)) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        - ((𝓕 (hFdiv2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ))
        =ᵐ[volume] ((𝓕 ((hn2 n).toLp (hn n)) - 𝓕 (hFdiv2.toLp h)
          : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
      (MeasureTheory.Lp.coeFn_sub _ _).symm
    rw [eLpNorm_congr_ae h2]
    have h3 : (𝓕 ((hn2 n).toLp (hn n)) - 𝓕 (hFdiv2.toLp h)
        : Lp ℂ 2 (volume : Measure ℝ))
        = (𝓕 ((hn2 n).toLp (hn n) - hFdiv2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) := by
      rw [hbr, hbr, hbr, ← map_sub]
    rw [h3, hLp_eLp]
    refine eLpNorm_congr_ae ?_
    filter_upwards [MeasureTheory.Lp.coeFn_sub ((hn2 n).toLp (hn n)) (hFdiv2.toLp h),
      (hn2 n).coeFn_toLp, hFdiv2.coeFn_toLp] with x hx1 hx2 hx3
    rw [hx1, Pi.sub_apply, hx2, hx3]
    rfl
  have heLp : Tendsto (fun n : ℕ =>
      eLpNorm ((𝓕 (fun x : ℝ => hn n x))
        - ((𝓕 (hFdiv2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) 2 volume)
      atTop (nhds 0) := by
    simp only [hstep]
    exact tendsto_eLpNorm_indicator_truncation hFdiv2
  -- convergence in measure and an a.e.-convergent subsequence
  have hmeas : TendstoInMeasure volume (fun n : ℕ => 𝓕 (fun x : ℝ => hn n x)) atTop
      ((𝓕 (hFdiv2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_ ?_ heLp
    · intro n
      refine Continuous.aestronglyMeasurable ?_
      exact VectorFourier.fourierIntegral_continuous (by fun_prop) (by fun_prop) (hn1 n)
    · exact (MeasureTheory.Lp.memLp _).aestronglyMeasurable
  obtain ⟨ns, hns_mono, hns_ae⟩ := hmeas.exists_seq_tendsto_ae
  -- pull the a.e. statement back through ξ = -t/(2π)
  have hqmp : Measure.QuasiMeasurePreserving (fun t : ℝ => -t/(2*π))
      volume volume := by
    have h0 : (fun t : ℝ => -t/(2*π)) = fun t : ℝ => (-(2*π))⁻¹ * t := by
      funext t
      field_simp
    rw [h0]
    refine ⟨by fun_prop, ?_⟩
    have hne0 : ((-(2*π))⁻¹ : ℝ) ≠ 0 := by
      refine inv_ne_zero ?_
      refine neg_ne_zero.mpr ?_
      positivity
    rw [Real.map_volume_mul_left hne0]
    exact Measure.smul_absolutelyContinuous
  have hae_t := hqmp.ae hns_ae
  -- combine with the pointwise truncated convergence
  have hne : ∀ᵐ t : ℝ, t ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact MeasureTheory.measure_singleton 0
  filter_upwards [hae_t, hne] with t hlim ht
  have hpt : Tendsto (fun i : ℕ => 𝓕 (fun x : ℝ => hn (ns i) x) (-t/(2*π)))
      atTop (nhds (gammaFT F t)) := by
    have h0 : ∀ n : ℕ, 𝓕 (fun x : ℝ => hn n x) (-t/(2*π))
        = ∫ x in Set.Ioc (-(n:ℝ)) (n:ℝ), h x * Complex.exp ((t*x : ℝ) * Complex.I) := by
      intro n
      rw [← muFT_eq_fourierIntegral (fun x : ℝ => hn n x) t]
      rw [hhn]
      rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      show (Set.Ioc (-(n:ℝ)) (n:ℝ)).indicator h x * Complex.exp ((t*x : ℝ) * Complex.I)
          = (Set.Ioc (-(n:ℝ)) (n:ℝ)).indicator
              (fun y => h y * Complex.exp ((t*y : ℝ) * Complex.I)) x
      simp only [Set.indicator_apply]
      split_ifs with hx
      · rfl
      · rw [zero_mul]
    simp only [h0]
    exact (tendsto_truncated_fourier_gammaFT hF hFdiv ht).comp
      (hns_mono.tendsto_atTop)
  exact tendsto_nhds_unique hpt hlim

/-- **`μγ` is integrable** (P-d prerequisite): the product of the two transforms is
integrable, being a.e. a product of two `L²` representatives after rescaling. -/
theorem integrable_muFT_mul_gammaFT {k F : ℝ → ℂ}
    (hk1 : Integrable k) (hk2 : MemLp k 2 (volume : Measure ℝ))
    (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ)) :
    Integrable (fun t : ℝ =>
      (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t) := by
  set repk : ℝ → ℂ := ((𝓕 (hk2.toLp k) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) with hrepk
  set reph : ℝ → ℂ := ((𝓕 (hFdiv2.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
    with hreph
  -- integrable product of the scaled reps
  have hprod : Integrable (fun t : ℝ => repk (-t/(2*π)) * reph (-t/(2*π))) := by
    have h0 : Integrable (fun s : ℝ => repk s * reph s) :=
      MemLp.integrable_mul (MeasureTheory.Lp.memLp _) (MeasureTheory.Lp.memLp _)
    have h1 : Integrable (fun t : ℝ => (fun s : ℝ => repk s * reph s) ((-(2*π))⁻¹ * t)) := by
      rw [MeasureTheory.integrable_comp_mul_left_iff
        (fun s : ℝ => repk s * reph s)
        (inv_ne_zero (neg_ne_zero.mpr (by positivity : (2*π : ℝ) ≠ 0)))]
      exact h0
    refine h1.congr (Filter.Eventually.of_forall (fun t => ?_))
    congr 2 <;> · field_simp
  -- transfer along a.e. equality
  have hμeq : ∀ t : ℝ, (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I))
      = 𝓕 k (-t/(2*π)) := fun t => muFT_eq_fourierIntegral k t
  have hkae : (fun t : ℝ => 𝓕 k (-t/(2*π))) =ᵐ[volume]
      (fun t : ℝ => repk (-t/(2*π))) := by
    have h0 : (𝓕 k) =ᵐ[volume] repk := (coeFn_fourier_toLp_two hk1 hk2).symm
    have hqmp : Measure.QuasiMeasurePreserving (fun t : ℝ => -t/(2*π))
        (volume : Measure ℝ) (volume : Measure ℝ) := by
      have h1 : (fun t : ℝ => -t/(2*π)) = fun t : ℝ => (-(2*π))⁻¹ * t := by
        funext t
        field_simp
      rw [h1]
      refine ⟨by fun_prop, ?_⟩
      rw [Real.map_volume_mul_left (inv_ne_zero (neg_ne_zero.mpr
        (by positivity : (2*π : ℝ) ≠ 0)))]
      exact Measure.smul_absolutelyContinuous
    exact hqmp.ae h0
  have hγae : (fun t : ℝ => gammaFT F t) =ᵐ[volume]
      (fun t : ℝ => reph (-t/(2*π))) := gammaFT_ae_eq_fourierL2 hF hFdiv hFdiv2
  refine hprod.congr ?_
  filter_upwards [hkae, hγae] with t h1 h2
  rw [hμeq t, h1, h2]

/-- **The Plancherel evaluation of `∫μγ`** (P-d, Poitou p. 6-06): for `k ∈ L¹∩L²` and
admissible `F`,
`∫ μ(t)γ(t) dt = 2π ∫ k(-x)·(F(0)-F(x))/x dx`. -/
theorem integral_muFT_mul_gammaFT {k F : ℝ → ℂ}
    (hk1 : Integrable k) (hk2 : MemLp k 2 (volume : Measure ℝ))
    (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ)) :
    (∫ t : ℝ, (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t)
      = ((2*π : ℝ) : ℂ) * ∫ x : ℝ, k (-x) * ((F 0 - F x)/(x:ℂ)) := by
  set repk : ℝ → ℂ := ((𝓕 (hk2.toLp k) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) with hrepk
  set reph : ℝ → ℂ := ((𝓕 (hFdiv2.toLp _) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
    with hreph
  have hμeq : ∀ t : ℝ, (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I))
      = 𝓕 k (-t/(2*π)) := fun t => muFT_eq_fourierIntegral k t
  have hkae : (fun t : ℝ => 𝓕 k (-t/(2*π))) =ᵐ[volume]
      (fun t : ℝ => repk (-t/(2*π))) := by
    have h0 : (𝓕 k) =ᵐ[volume] repk := (coeFn_fourier_toLp_two hk1 hk2).symm
    have hqmp : Measure.QuasiMeasurePreserving (fun t : ℝ => -t/(2*π))
        (volume : Measure ℝ) (volume : Measure ℝ) := by
      have h1 : (fun t : ℝ => -t/(2*π)) = fun t : ℝ => (-(2*π))⁻¹ * t := by
        funext t
        field_simp
      rw [h1]
      refine ⟨by fun_prop, ?_⟩
      rw [Real.map_volume_mul_left (inv_ne_zero (neg_ne_zero.mpr
        (by positivity : (2*π : ℝ) ≠ 0)))]
      exact Measure.smul_absolutelyContinuous
    exact hqmp.ae h0
  have hγae : (fun t : ℝ => gammaFT F t) =ᵐ[volume]
      (fun t : ℝ => reph (-t/(2*π))) := gammaFT_ae_eq_fourierL2 hF hFdiv hFdiv2
  -- replace by the scaled representatives
  have h1 : (∫ t : ℝ, (∫ x : ℝ, k x * Complex.exp ((t*x : ℝ) * Complex.I)) * gammaFT F t)
      = ∫ t : ℝ, repk (-t/(2*π)) * reph (-t/(2*π)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hkae, hγae] with t hk' hγ'
    rw [hμeq t, hk', hγ']
  rw [h1]
  -- rescale
  have h2 : (∫ t : ℝ, repk (-t/(2*π)) * reph (-t/(2*π)))
      = |((-(2*π))⁻¹)⁻¹| • ∫ s : ℝ, repk s * reph s := by
    rw [← MeasureTheory.Measure.integral_comp_mul_left
      (fun s : ℝ => repk s * reph s) ((-(2*π))⁻¹)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    congr 2 <;> · field_simp
  rw [h2]
  have h3 : |((-(2*π))⁻¹)⁻¹| = (2*π : ℝ) := by
    rw [inv_inv, abs_neg, abs_of_pos (by positivity)]
  rw [h3]
  -- evaluate via the mixed Plancherel pairing
  have h4 : (∫ s : ℝ, repk s * reph s)
      = ∫ x : ℝ, k (-x) * ((F 0 - F x)/(x:ℂ)) := by
    have h5 : (∫ s : ℝ, repk s * reph s) = ∫ s : ℝ, 𝓕 k s * reph s := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [(coeFn_fourier_toLp_two hk1 hk2)] with s hs
      rw [hrepk]
      show ((𝓕 (hk2.toLp k) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) s * reph s
          = 𝓕 k s * reph s
      rw [hs]
    rw [h5, hreph]
    exact integral_fourier_mul_fourierL2 hk1 hk2 hFdiv2
  rw [h4, Complex.real_smul]

/-- **Proposition 3, abstract form** (Poitou p. 6-04/6-06): for `k ∈ L¹∩L²` and
admissible `F` with the boundary decay `ρ(t)γ(t) → 0`, the symmetric truncations of
`∫ρφ` converge:

`lim_{T→∞} ∫_{-T}^T ρ(t)·φ(t) dt = -2π ∫ k(-x)·(F(0)-F(x))/x dx`.

For odd `k` the right side is `+2π ∫ k(x)·(F(0)-F(x))/x dx`. -/
theorem tendsto_integral_rhoFT_mul_phi_eq_plancherel {k F : ℝ → ℂ}
    (hk1 : Integrable k) (hk2 : MemLp k 2 (volume : Measure ℝ))
    (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ))
    (htop : Tendsto (fun t : ℝ => rhoFT k t * gammaFT F t) atTop (nhds 0))
    (hbot : Tendsto (fun t : ℝ => rhoFT k t * gammaFT F t) atBot (nhds 0)) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
        rhoFT k t * (∫ x : ℝ, F x * Complex.exp ((t*x : ℝ) * Complex.I)))
      atTop (nhds (-(((2*π : ℝ) : ℂ) * ∫ x : ℝ, k (-x) * ((F 0 - F x)/(x:ℂ))))) := by
  have h0 := tendsto_integral_rhoFT_mul_phi hk1 hF hFdiv
    (integrable_muFT_mul_gammaFT hk1 hk2 hF hFdiv hFdiv2) htop hbot
  rw [integral_muFT_mul_gammaFT hk1 hk2 hF hFdiv hFdiv2] at h0
  exact h0

/-- **Poitou's odd kernel** (p. 6-06): the odd extension of
`x ↦ x e^{-σx}/(1-e^{-x})` from `x > 0`. -/
noncomputable def poitouKernel (σ : ℝ) (x : ℝ) : ℝ :=
  Real.sign x * (|x| * Real.exp (-(σ*|x|)) / (1 - Real.exp (-|x|)))

theorem poitouKernel_neg (σ x : ℝ) : poitouKernel σ (-x) = -poitouKernel σ x := by
  rw [poitouKernel, poitouKernel, Real.sign_neg, abs_neg]
  ring

theorem poitouKernel_of_pos {σ x : ℝ} (hx : 0 < x) :
    poitouKernel σ x = x * Real.exp (-(σ*x)) / (1 - Real.exp (-x)) := by
  rw [poitouKernel, Real.sign_of_pos hx, abs_of_pos hx, one_mul]

/-- The kernel profile bound: `|poitouKernel σ x| ≤ (1+|x|)e^{-σ|x|}` (from
`y/(1-e^{-y}) ≤ 1+y`, i.e. `(1+y)e^{-y} ≤ 1`). -/
theorem abs_poitouKernel_le (σ : ℝ) (x : ℝ) :
    |poitouKernel σ x| ≤ (1 + |x|) * Real.exp (-(σ*|x|)) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [poitouKernel, Real.sign_of_neg hx, abs_mul, abs_neg, abs_one, one_mul]
    have hax : 0 < |x| := abs_pos.mpr hx.ne
    have hden : 0 < 1 - Real.exp (-|x|) := by
      have := Real.exp_lt_exp.mpr (show -|x| < 0 by linarith)
      rw [Real.exp_zero] at this
      linarith
    rw [abs_div, abs_mul, abs_abs, Real.abs_exp, abs_of_pos hden,
      div_le_iff₀ hden]
    have hkey : (1 + |x|) * Real.exp (-|x|) ≤ 1 := by
      have h0 := Real.add_one_le_exp |x|
      rw [Real.exp_neg]
      rw [mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    nlinarith [Real.exp_pos (-(σ*|x|)), Real.exp_pos (-|x|), abs_nonneg x,
      mul_pos (Real.exp_pos (-(σ*|x|))) hden]
  · rw [hx]
    simp [poitouKernel]
  · rw [poitouKernel, Real.sign_of_pos hx, one_mul]
    have hax : 0 < |x| := abs_pos.mpr hx.ne'
    have hden : 0 < 1 - Real.exp (-|x|) := by
      have := Real.exp_lt_exp.mpr (show -|x| < 0 by linarith)
      rw [Real.exp_zero] at this
      linarith
    rw [abs_div, abs_mul, abs_abs, Real.abs_exp, abs_of_pos hden,
      div_le_iff₀ hden]
    have hkey : (1 + |x|) * Real.exp (-|x|) ≤ 1 := by
      have h0 := Real.add_one_le_exp |x|
      rw [Real.exp_neg]
      rw [mul_inv_le_iff₀ (Real.exp_pos _)]
      linarith
    nlinarith [Real.exp_pos (-(σ*|x|)), Real.exp_pos (-|x|), abs_nonneg x,
      mul_pos (Real.exp_pos (-(σ*|x|))) hden]

/-- The two-sided exponential `e^{-a|x|}` is integrable. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-(a*|x|))) := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).restrict (Set.Iio (0:ℝ))
      = Measure.map (fun x : ℝ => -x) ((volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))) := by
    rw [show Set.Ioi (0:ℝ) = (fun x : ℝ => -x) ⁻¹' (Set.Iio 0) by ext x; simp,
      ← Measure.restrict_map A.measurable measurableSet_Iio,
      Measure.map_neg_eq_self (volume : Measure ℝ)]
  have hIoi : IntegrableOn (fun x : ℝ => Real.exp (-(a*|x|))) (Set.Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi (0:ℝ) ha).congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [Set.mem_Ioi] at hx
    rw [abs_of_pos hx]
    ring_nf
  have hIio : IntegrableOn (fun x : ℝ => Real.exp (-(a*|x|))) (Set.Iio 0) := by
    rw [IntegrableOn, hmap, A.integrable_map_iff]
    refine hIoi.congr ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    show Real.exp (-(a*|x|)) = Real.exp (-(a*|(-x)|))
    rw [abs_neg]
  rw [← MeasureTheory.integrableOn_univ,
    show (Set.univ : Set ℝ) = Set.Iio 0 ∪ Set.Ici 0 by rw [Set.Iio_union_Ici],
    MeasureTheory.integrableOn_union]
  constructor
  · exact hIio
  · have h8 : IntegrableOn (fun x : ℝ => Real.exp (-(a*|x|))) {(0:ℝ)} := by
      rw [IntegrableOn, Measure.restrict_eq_zero.mpr (measure_singleton 0)]
      exact integrable_zero_measure
    have h9 : Set.Ici (0:ℝ) = {(0:ℝ)} ∪ Set.Ioi 0 := by
      ext x
      simp only [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi]
      constructor
      · intro h'
        rcases eq_or_lt_of_le h' with h'' | h''
        · exact Or.inl h''.symm
        · exact Or.inr h''
      · rintro (h' | h')
        · exact h'.ge
        · exact h'.le
    rw [h9]
    exact MeasureTheory.IntegrableOn.union h8 hIoi

/-- The exponential-polynomial majorant bound: `(1+|x|)e^{-a|x|} ≤ (1+2/a)e^{-a|x|/2}`. -/
theorem one_add_abs_mul_exp_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (1 + |x|) * Real.exp (-(a*|x|)) ≤ (1 + 2/a) * Real.exp (-(a*|x|/2)) := by
  have h1 : |x| * Real.exp (-(a*|x|)) ≤ (2/a) * Real.exp (-(a*|x|/2)) := by
    have h2 : a*|x|/2 + 1 ≤ Real.exp (a*|x|/2) := Real.add_one_le_exp _
    have h3 : |x| ≤ (2/a) * Real.exp (a*|x|/2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      nlinarith [abs_nonneg x]
    calc |x| * Real.exp (-(a*|x|))
        ≤ ((2/a) * Real.exp (a*|x|/2)) * Real.exp (-(a*|x|)) := by
          refine mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = (2/a) * Real.exp (-(a*|x|/2)) := by
          rw [mul_assoc, ← Real.exp_add]
          ring_nf
  have h4 : Real.exp (-(a*|x|)) ≤ Real.exp (-(a*|x|/2)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [abs_nonneg x]
  nlinarith [Real.exp_pos (-(a*|x|/2))]

/-- The exponential-polynomial majorant is integrable on the whole line. -/
theorem integrable_one_add_abs_mul_exp {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => (1 + |x|) * Real.exp (-(a*|x|))) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (1 + |x|) * Real.exp (-(a*|x|)))
      (volume : Measure ℝ) := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  refine MeasureTheory.Integrable.mono'
    (g := fun x => (1 + 2/a) * Real.exp (-(a*|x|/2)))
    (((integrable_exp_neg_mul_abs (show (0:ℝ) < a/2 by positivity)).congr
      (Filter.Eventually.of_forall (fun x => by
        show Real.exp (-(a/2*|x|)) = Real.exp (-(a*|x|/2))
        ring_nf))).const_mul _) hmeas ?_
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact one_add_abs_mul_exp_le ha x)

/-- Total form of the Poitou kernel: `sign x·|x| = x` collapses the piecewise
definition. -/
theorem poitouKernel_eq (σ x : ℝ) :
    poitouKernel σ x = x * Real.exp (-(σ*|x|)) / (1 - Real.exp (-|x|)) := by
  have hs : Real.sign x * |x| = x := by
    rcases lt_trichotomy x 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]
      ring
    · rw [h, Real.sign_zero, abs_zero, mul_zero]
    · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]
  rw [poitouKernel, show Real.sign x * (|x| * Real.exp (-(σ*|x|)) / (1 - Real.exp (-|x|)))
      = (Real.sign x * |x|) * Real.exp (-(σ*|x|)) / (1 - Real.exp (-|x|)) from by ring,
    hs]

/-- The Poitou kernel is measurable. -/
theorem measurable_poitouKernel (σ : ℝ) : Measurable (poitouKernel σ) := by
  have h0 : poitouKernel σ = fun x => x * Real.exp (-(σ*|x|)) / (1 - Real.exp (-|x|)) :=
    funext (poitouKernel_eq σ)
  rw [h0]
  fun_prop

/-- The (complexified) Poitou kernel is integrable (K3). -/
theorem integrable_poitouKernel {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun x : ℝ => ((poitouKernel σ x : ℝ) : ℂ)) := by
  refine MeasureTheory.Integrable.mono' (integrable_one_add_abs_mul_exp hσ) ?_ ?_
  · exact (Complex.measurable_ofReal.comp (measurable_poitouKernel σ)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_poitouKernel_le σ x

/-- The (complexified) Poitou kernel is square-integrable (K4). -/
theorem memLp_two_poitouKernel {σ : ℝ} (hσ : 0 < σ) :
    MemLp (fun x : ℝ => ((poitouKernel σ x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  have hmaj : MemLp (fun x : ℝ => (1 + |x|) * Real.exp (-(σ*|x|))) 2
      (volume : Measure ℝ) := by
    rw [memLp_two_iff_integrable_sq (by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop)]
    have h0 : ∀ x : ℝ, ((1 + |x|) * Real.exp (-(σ*|x|)))^2
        ≤ (1 + 2/σ)^2 * Real.exp (-(σ*|x|)) := by
      intro x
      have h1 := one_add_abs_mul_exp_le hσ x
      have h2 : ((1 + |x|) * Real.exp (-(σ*|x|)))^2
          ≤ ((1 + 2/σ) * Real.exp (-(σ*|x|/2)))^2 := by
        refine pow_le_pow_left₀ (by positivity) h1 2
      refine le_trans h2 (le_of_eq ?_)
      rw [mul_pow]
      congr 1
      rw [sq, ← Real.exp_add]
      ring_nf
    refine MeasureTheory.Integrable.mono'
      (((integrable_exp_neg_mul_abs hσ).const_mul ((1 + 2/σ)^2))) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      fun_prop
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact h0 x
  refine MemLp.of_le hmaj ?_ ?_
  · exact (Complex.measurable_ofReal.comp (measurable_poitouKernel σ)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    refine le_trans (abs_poitouKernel_le σ x) (le_abs_self _)

end DedekindResidue
