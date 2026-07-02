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

open MeasureTheory Complex intervalIntegral Real Filter

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

end DedekindResidue
