module

public import DedekindResidue.ExplicitFormula.PrimeSide

/-!
# Fourier–Jordan inversion: the Dirichlet integral (SP2-FJ-c)

The classical Dirichlet integral `∫₀^∞ (sin x)/x dx = π/2`, phrased as convergence of the
truncated integrals `∫₀^b (sin x)/x dx → π/2` as `b → ∞`. This is the analytic engine of
Jordan's pointwise Fourier-inversion criterion for functions of bounded variation, used in
Poitou's proof of the explicit formula (Poitou, *Sur les petits discriminants*, Séminaire
DPP 1976/77, exposé 6, p. 6-03) to invert the transform `Φ` on the prime side.

Not available in mathlib. We follow the Frullani/Fubini route:
`1/x = ∫₀^∞ e^{-xy} dy`, so
`∫₀^b (sin x)/x dx = ∫₀^∞ (1 - e^{-yb}(cos y + y sin b))/(1+y²) dy`
by Fubini and the closed form of the damped sine integral; dominated convergence then gives
the limit `∫₀^∞ dy/(1+y²) = π/2`.

## Main results

- `hasDerivAt_exp_sin_primitive`, `integral_exp_neg_mul_sin`: closed form of
  `∫₀^b e^{-yx} sin x dx`.
- `integral_exp_neg_mul_Ioi`: `∫₀^∞ e^{-xy} dy = 1/x`.
- `integral_sinc_eq`: the Fubini identity for the truncated Dirichlet integral.
- `tendsto_integral_sinc_atTop`: `∫₀^b (sin x)/x dx → π/2`.
-/

@[expose] public section


namespace DedekindResidue

open MeasureTheory Complex intervalIntegral Real Filter

/-- Antiderivative for the damped sine: `d/dt [-e^{-yt}(cos t + y sin t)/(1+y²)]
= e^{-yt} sin t`. -/
theorem hasDerivAt_exp_sin_primitive (y x : ℝ) :
    HasDerivAt (fun t : ℝ =>
      -(Real.exp (-(y*t)) * (Real.cos t + y * Real.sin t)) / (1 + y^2))
      (Real.exp (-(y*x)) * Real.sin x) x := by
  have h0 : HasDerivAt (fun t : ℝ => y*t) y x := by
    simpa using (hasDerivAt_id x).const_mul y
  have h1 : HasDerivAt (fun t : ℝ => -(y*t)) (-y) x := h0.neg
  have hexp := h1.exp
  have htrig : HasDerivAt (fun t : ℝ => Real.cos t + y * Real.sin t)
      (-Real.sin x + y * Real.cos x) x :=
    (Real.hasDerivAt_cos x).add ((Real.hasDerivAt_sin x).const_mul y)
  have hmul := hexp.mul htrig
  have hfull := (hmul.neg).div_const (1 + y^2)
  have hy2 : (1 + y^2) ≠ 0 := by positivity
  have hval : -(Real.exp (-(y*x)) * -y * (Real.cos x + y * Real.sin x)
      + Real.exp (-(y*x)) * (-Real.sin x + y * Real.cos x)) / (1 + y^2)
      = Real.exp (-(y*x)) * Real.sin x := by
    rw [div_eq_iff hy2]
    ring
  rw [hval] at hfull
  exact hfull

/-- Closed form of the damped sine integral. -/
theorem integral_exp_neg_mul_sin (y b : ℝ) :
    ∫ x in (0:ℝ)..b, Real.exp (-(y*x)) * Real.sin x
      = (1 - Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b)) / (1 + y^2) := by
  have hint : IntervalIntegrable (fun x : ℝ => Real.exp (-(y*x)) * Real.sin x)
      volume 0 b := by
    refine ContinuousOn.intervalIntegrable ?_
    fun_prop
  have := integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -(Real.exp (-(y*t)) * (Real.cos t + y * Real.sin t)) / (1 + y^2))
    (fun x _ => hasDerivAt_exp_sin_primitive y x) hint
  rw [this]
  simp only [mul_zero, neg_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero,
    add_zero, mul_one]
  ring

/-- The inner exponential integral: `∫_{y>0} e^{-xy} dy = 1/x` for `x > 0`. -/
theorem integral_exp_neg_mul_Ioi {x : ℝ} (hx : 0 < x) :
    ∫ y in Set.Ioi (0:ℝ), Real.exp (-(x*y)) = 1/x := by
  have hderiv : ∀ t ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun y : ℝ => -Real.exp (-(x*y)) / x) (Real.exp (-(x*t))) t := by
    intro t _
    have h0 : HasDerivAt (fun y : ℝ => x*y) x t := by
      simpa using (hasDerivAt_id t).const_mul x
    have h1 : HasDerivAt (fun y : ℝ => -(x*y)) (-x) t := h0.neg
    have h2 := (h1.exp.neg).div_const x
    have hval : -(Real.exp (-(x*t)) * -x) / x = Real.exp (-(x*t)) := by
      rw [div_eq_iff hx.ne']
      ring
    rw [hval] at h2
    exact h2
  have hint : IntegrableOn (fun y : ℝ => Real.exp (-(x*y))) (Set.Ioi 0) := by
    have := exp_neg_integrableOn_Ioi (0:ℝ) hx
    refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
    ring_nf
  have htend : Tendsto (fun y : ℝ => -Real.exp (-(x*y)) / x) atTop (nhds 0) := by
    have h1 : Tendsto (fun y : ℝ => -(x*y)) atTop atBot := by
      refine Filter.tendsto_neg_atBot_iff.mpr ?_
      exact Tendsto.const_mul_atTop hx tendsto_id
    have h2 := (Real.tendsto_exp_atBot.comp h1).neg
    have h3 := h2.div_const x
    simpa using h3
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [this, mul_zero, neg_zero, Real.exp_zero]
  rw [zero_sub, neg_div, neg_neg, one_div]



/-- **The Fubini step of the Dirichlet integral**: for `b > 0`,
`∫₀^b sin x/x dx = ∫_{y>0} (1 − e^{-yb}(cos b + y sin b))/(1+y²) dy`. -/
theorem integral_sinc_eq {b : ℝ} (hb : 0 < b) :
    (∫ x in (0:ℝ)..b, Real.sin x / x)
      = ∫ y in Set.Ioi (0:ℝ),
          (1 - Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b)) / (1 + y^2) := by
  -- joint integrability on Ioc 0 b × Ioi 0
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun x y => Real.sin x * Real.exp (-(x*y)))
      ((volume.restrict (Set.Ioc (0:ℝ) b)).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have hint_slice : ∀ x ∈ Set.Ioc (0:ℝ) b,
      Integrable (fun y => Real.sin x * Real.exp (-(x*y)))
        (volume.restrict (Set.Ioi (0:ℝ))) := by
    intro x hx
    refine Integrable.const_mul ?_ _
    have := exp_neg_integrableOn_Ioi (0:ℝ) hx.1
    refine (this.congr_fun (fun y _ => ?_) measurableSet_Ioi)
    simp only
    rw [show -x * y = -(x*y) by ring]
  have hnorm_int : ∀ x ∈ Set.Ioc (0:ℝ) b,
      (∫ y in Set.Ioi (0:ℝ), ‖Real.sin x * Real.exp (-(x*y))‖) ≤ 1 := by
    intro x hx
    have hval : (∫ y in Set.Ioi (0:ℝ), ‖Real.sin x * Real.exp (-(x*y))‖)
        = |Real.sin x| * (1/x) := by
      rw [show (fun y => ‖Real.sin x * Real.exp (-(x*y))‖)
          = fun y => |Real.sin x| * Real.exp (-(x*y)) from funext (fun y => by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp])]
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi hx.1]
    rw [hval]
    have h1 : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
    rw [abs_of_pos hx.1] at h1
    rw [mul_one_div]
    rw [div_le_one hx.1]
    exact h1
  have hprod : Integrable (Function.uncurry fun x y => Real.sin x * Real.exp (-(x*y)))
      ((volume.restrict (Set.Ioc (0:ℝ) b)).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    rw [MeasureTheory.integrable_prod_iff hmeas]
    constructor
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
      exact Filter.Eventually.of_forall (fun x hx => hint_slice x hx)
    · refine MeasureTheory.Integrable.mono'
        (g := fun _ => (1:ℝ))
        (MeasureTheory.integrableOn_const (C := (1:ℝ)) (by
          rw [Real.volume_Ioc]
          exact ENNReal.ofReal_ne_top))
        ((hmeas.norm).integral_prod_right') ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
      refine Filter.Eventually.of_forall (fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hnorm_int x hx
  -- pointwise kernel identity and the swap
  have hswap := MeasureTheory.integral_integral_swap hprod
  rw [intervalIntegral.integral_of_le hb.le]
  calc (∫ x in Set.Ioc (0:ℝ) b, Real.sin x / x)
      = ∫ x in Set.Ioc (0:ℝ) b,
          (∫ y in Set.Ioi (0:ℝ), Real.sin x * Real.exp (-(x*y))) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
        rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi hx.1, mul_one_div]
    _ = ∫ y in Set.Ioi (0:ℝ),
          (∫ x in Set.Ioc (0:ℝ) b, Real.sin x * Real.exp (-(x*y))) := hswap
    _ = ∫ y in Set.Ioi (0:ℝ),
          (1 - Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b)) / (1 + y^2) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
        rw [← intervalIntegral.integral_of_le hb.le]
        rw [show (fun x => Real.sin x * Real.exp (-(x*y)))
            = fun x => Real.exp (-(y*x)) * Real.sin x from funext (fun x => by
              rw [mul_comm x y]; ring)]
        exact integral_exp_neg_mul_sin y b

/-- **The Dirichlet integral** (SP2-FJ-c): `∫₀^∞ sin x/x dx = π/2`, as a limit of the
truncated integrals. Fubini against `1/x = ∫ e^{-xy} dy` plus dominated convergence. -/
theorem tendsto_integral_sinc_atTop :
    Filter.Tendsto (fun b : ℝ => ∫ x in (0:ℝ)..b, Real.sin x / x)
      atTop (nhds (π/2)) := by
  have hval : (π/2 : ℝ) = ∫ y in Set.Ioi (0:ℝ), (1 + y^2)⁻¹ := by
    rw [integral_Ioi_inv_one_add_sq]
    simp
  rw [hval]
  have hev : (fun b : ℝ => ∫ x in (0:ℝ)..b, Real.sin x / x)
      =ᶠ[atTop] (fun b => ∫ y in Set.Ioi (0:ℝ),
        (1 - Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b)) / (1 + y^2)) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with b hb
    exact integral_sinc_eq hb
  rw [Filter.tendsto_congr' hev]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun y => (1 + (1+y) * Real.exp (-y)) / (1 + y^2)) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall (fun b => ?_)
    refine Continuous.aestronglyMeasurable ?_
    have h2 : ∀ y : ℝ, (1 + y^2) ≠ 0 := fun y => by positivity
    fun_prop (disch := exact h2)
  · filter_upwards [Filter.eventually_ge_atTop 1] with b hb
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [Set.mem_Ioi] at hy
    have hy2 : (0:ℝ) < 1 + y^2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hy2]
    refine div_le_div_of_nonneg_right ?_ hy2.le
    have htrig : |Real.cos b + y * Real.sin b| ≤ 1 + y := by
      calc |Real.cos b + y * Real.sin b|
          ≤ |Real.cos b| + |y * Real.sin b| := abs_add_le _ _
        _ ≤ 1 + y := by
            have h1 := Real.abs_cos_le_one b
            have h2 := Real.abs_sin_le_one b
            rw [abs_mul, abs_of_pos hy]
            nlinarith [abs_nonneg (Real.sin b)]
    have hexp : Real.exp (-(y*b)) ≤ Real.exp (-y) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    calc |1 - Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b)|
        ≤ 1 + Real.exp (-(y*b)) * |Real.cos b + y * Real.sin b| := by
          have h0 := norm_sub_le (1:ℝ)
            (Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b))
          simp only [Real.norm_eq_abs, abs_one] at h0
          rw [abs_mul, Real.abs_exp] at h0
          exact h0
      _ ≤ 1 + (1+y) * Real.exp (-y) := by
          have h1 : Real.exp (-(y*b)) * |Real.cos b + y * Real.sin b|
              ≤ Real.exp (-y) * (1+y) := by
            refine mul_le_mul hexp htrig (abs_nonneg _) (Real.exp_pos _).le
          linarith
  · -- the dominating function is integrable
    have hint1 : IntegrableOn (fun y : ℝ => (1+y^2)⁻¹) (Set.Ioi 0) :=
      integrable_inv_one_add_sq.integrableOn
    have hint2 : IntegrableOn (fun y : ℝ => Real.exp (-y)) (Set.Ioi 0) := by
      have := exp_neg_integrableOn_Ioi (0:ℝ) (by norm_num : (0:ℝ) < 1)
      refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
      show Real.exp (-1 * y) = Real.exp (-y)
      rw [neg_one_mul]
    have hint3 : IntegrableOn (fun y : ℝ => 2 * Real.exp (-(y/2))) (Set.Ioi 0) := by
      have h0 := exp_neg_integrableOn_Ioi (0:ℝ) (by norm_num : (0:ℝ) < 1/2)
      have h1 : IntegrableOn (fun y : ℝ => Real.exp (-(y/2))) (Set.Ioi 0) := by
        refine h0.congr_fun (fun y _ => ?_) measurableSet_Ioi
        show Real.exp (-(1/2) * y) = Real.exp (-(y/2))
        rw [show (-(1/2) * y : ℝ) = -(y/2) by ring]
      exact h1.const_mul 2
    refine MeasureTheory.Integrable.mono' ((hint1.add hint2).add hint3) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      have h2 : ∀ y : ℝ, (1 + y^2) ≠ 0 := fun y => by positivity
      fun_prop (disch := exact h2)
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      rw [Set.mem_Ioi] at hy
      have hy2 : (0:ℝ) < 1 + y^2 := by positivity
      have hy21 : (1:ℝ) ≤ 1 + y^2 := by nlinarith
      have hnn : (0:ℝ) ≤ (1 + (1+y) * Real.exp (-y)) / (1 + y^2) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hsplit : (1 + (1+y) * Real.exp (-y)) / (1 + y^2)
          = (1+y^2)⁻¹ + ((1+y) * Real.exp (-y)) / (1+y^2) := by
        rw [add_div, one_div]
      rw [hsplit]
      have hexp_bd : ((1+y) * Real.exp (-y)) / (1+y^2) ≤ (1+y) * Real.exp (-y) := by
        rw [div_le_iff₀ hy2]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1+y) (Real.exp_pos (-y)).le]
      have hy_exp : y * Real.exp (-y) ≤ 2 * Real.exp (-(y/2)) := by
        have h1 : y/2 + 1 ≤ Real.exp (y/2) := Real.add_one_le_exp (y/2)
        have h2 : y ≤ 2 * Real.exp (y/2) := by linarith
        calc y * Real.exp (-y) ≤ (2 * Real.exp (y/2)) * Real.exp (-y) :=
              mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
          _ = 2 * Real.exp (-(y/2)) := by
              rw [mul_assoc, ← Real.exp_add]
              ring_nf
      have hfinal : (1+y) * Real.exp (-y) ≤ Real.exp (-y) + 2 * Real.exp (-(y/2)) := by
        have : (1+y) * Real.exp (-y) = Real.exp (-y) + y * Real.exp (-y) := by ring
        rw [this]
        linarith
      calc (1+y^2)⁻¹ + ((1+y) * Real.exp (-y)) / (1+y^2)
          ≤ (1+y^2)⁻¹ + (1+y) * Real.exp (-y) := by linarith
        _ ≤ (1+y^2)⁻¹ + (Real.exp (-y) + 2 * Real.exp (-(y/2))) := by linarith
        _ = (fun y : ℝ => (1+y^2)⁻¹) y + (fun y : ℝ => Real.exp (-y)) y
            + (fun y : ℝ => 2 * Real.exp (-(y/2))) y := by
            simp only
            ring
  · -- pointwise limits
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [Set.mem_Ioi] at hy
    have h0 : Filter.Tendsto
        (fun b : ℝ => Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b))
        atTop (nhds 0) := by
      refine squeeze_zero_norm (a := fun b => (1+y) * Real.exp (-(y*b))) (fun b => ?_) ?_
      · rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
        have htrig : |Real.cos b + y * Real.sin b| ≤ 1 + y := by
          calc |Real.cos b + y * Real.sin b|
              ≤ |Real.cos b| + |y * Real.sin b| := abs_add_le _ _
            _ ≤ 1 + y := by
                have h1 := Real.abs_cos_le_one b
                have h2 := Real.abs_sin_le_one b
                rw [abs_mul, abs_of_pos hy]
                nlinarith [abs_nonneg (Real.sin b)]
        calc Real.exp (-(y*b)) * |Real.cos b + y * Real.sin b|
            ≤ Real.exp (-(y*b)) * (1+y) :=
              mul_le_mul_of_nonneg_left htrig (Real.exp_pos _).le
          _ = (1+y) * Real.exp (-(y*b)) := by ring
      · have h1 : Filter.Tendsto (fun b : ℝ => -(y*b)) atTop atBot := by
          refine Filter.tendsto_neg_atBot_iff.mpr ?_
          exact Filter.Tendsto.const_mul_atTop hy Filter.tendsto_id
        have h2 := Real.tendsto_exp_atBot.comp h1
        have h3 := h2.const_mul (1+y)
        simpa using h3
    have h1 : Filter.Tendsto
        (fun b : ℝ => (1 - Real.exp (-(y*b)) * (Real.cos b + y * Real.sin b)) / (1 + y^2))
        atTop (nhds ((1 - 0) / (1 + y^2))) :=
      (Filter.Tendsto.const_sub 1 h0).div_const _
    simpa using h1

/-- The sinc function is interval integrable on every interval (it is measurable and
bounded by `1`). -/
theorem intervalIntegrable_sinc (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.sin x / x) volume a b := by
  refine intervalIntegrable_iff.mpr ?_
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.sin x / x)
      (volume.restrict (Set.uIoc a b)) :=
    (Real.measurable_sin.div measurable_id).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono'
    (g := fun _ => (1:ℝ))
    (MeasureTheory.integrableOn_const (C := (1:ℝ)) (by
      rw [Real.volume_uIoc]
      exact ENNReal.ofReal_ne_top))
    hmeas ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs]
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  · rw [abs_div]
    exact div_le_one_of_le₀ Real.abs_sin_le_abs (abs_nonneg _)

/-- The sinc primitive is uniformly bounded on `[0, ∞)`: continuity on compacts plus
the limit `π/2` at infinity. This is the constant `C_sinc` of Poitou's Fourier–Jordan
argument (p. 6-03). -/
theorem exists_bound_primitive_sinc :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℝ, 0 ≤ b → |∫ x in (0:ℝ)..b, Real.sin x / x| ≤ C := by
  set g : ℝ → ℝ := fun b => ∫ x in (0:ℝ)..b, Real.sin x / x with hg
  have hgc : Continuous g :=
    intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_sinc a b) 0
  -- eventually within 1 of π/2
  have htail := tendsto_integral_sinc_atTop.eventually
    (Metric.closedBall_mem_nhds (π/2) one_pos)
  rw [Filter.eventually_atTop] at htail
  obtain ⟨b₀, hb₀⟩ := htail
  -- bound on the compact initial segment [0, max b₀ 0]
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := max b₀ 0)).exists_bound_of_continuousOn
    hgc.continuousOn
  refine ⟨max C₀ (|π/2| + 1) + 1, by positivity, fun b hb => ?_⟩
  rcases le_or_gt b (max b₀ 0) with hble | hbgt
  · have := hC₀ b ⟨hb, hble⟩
    rw [Real.norm_eq_abs] at this
    calc |g b| ≤ C₀ := this
      _ ≤ max C₀ (|π/2| + 1) := le_max_left _ _
      _ ≤ max C₀ (|π/2| + 1) + 1 := le_add_of_nonneg_right zero_le_one
  · have hb' : b₀ ≤ b := le_trans (le_max_left _ _) hbgt.le
    have := hb₀ b hb'
    rw [Real.dist_eq] at this
    calc |g b| = |(g b - π/2) + π/2| := by ring_nf
      _ ≤ |g b - π/2| + |π/2| := abs_add_le _ _
      _ ≤ 1 + |π/2| := by gcongr
      _ = |π/2| + 1 := add_comm _ _
      _ ≤ max C₀ (|π/2| + 1) := le_max_right _ _
      _ ≤ max C₀ (|π/2| + 1) + 1 := le_add_of_nonneg_right zero_le_one

/-- **Uniform sinc-window bound `C_sinc`** (FJ-c tail corollary): a single constant
bounds `|∫_A^B sin x/x dx|` over all nonnegative windows. Used to control the
variation part of the Fourier–Jordan near-zero estimate. -/
theorem exists_bound_integral_sinc :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      |∫ x in A..B, Real.sin x / x| ≤ C := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_bound_primitive_sinc
  refine ⟨2 * C₀, by positivity, fun A B hA hB => ?_⟩
  have hsub : (∫ x in (0:ℝ)..B, Real.sin x / x) - ∫ x in (0:ℝ)..A, Real.sin x / x
      = ∫ x in A..B, Real.sin x / x :=
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_sinc 0 B) (intervalIntegrable_sinc 0 A)
  rw [← hsub]
  calc |(∫ x in (0:ℝ)..B, Real.sin x / x) - ∫ x in (0:ℝ)..A, Real.sin x / x|
      ≤ |∫ x in (0:ℝ)..B, Real.sin x / x| + |∫ x in (0:ℝ)..A, Real.sin x / x| :=
        abs_sub _ _
    _ ≤ C₀ + C₀ := add_le_add (hC₀ B hB) (hC₀ A hA)
    _ = 2 * C₀ := by ring

end DedekindResidue
