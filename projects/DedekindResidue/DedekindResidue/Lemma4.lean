/-
DedekindResidue: Belabas–Friedman Lemma 4 — the two-cutoff difference estimates.

Applying Lemma 3 at the two cutoffs `X` and `X' = X/e^a` and subtracting kills the
`T`-independent terms (`Φ(0)+Φ(1)`, `log Δ_K`, the Γ-constant), and the paper's four
estimates bound what remains: the sine difference by the mean value theorem
(`|sin(Tγ) − sin(T'γ)| ≤ a|γ|`, losing no `log X`), the cosine terms trivially, the
tail integrals by the exact antiderivative of the kernel, and the archimedean
integrals by monotonicity and the mean value theorem (the `β`-bound). Everything is
carried at real `σ > 1` with `h = σ − 1/2` explicit; the `σ → 1⁺` limit is taken in
the final inequality (never by analytic continuation of the identity), which
reproduces the paper's Lemma 4 (`Mostways`, eq. (Explicit2)) at `k = ℚ`.

Source: B–F 1305.0035, §3 (TeX lines 409–519); route: decomposition-t011.md.
-/
module

public import Mathlib
public import DedekindResidue.Lemma3

@[expose] public section

namespace DedekindResidue

open Complex NumberField Filter Real

variable (K : Type*) [Field K] [NumberField K]

/-! ### The sine-difference estimate (paper lines 446–456)

The mean value theorem gives `|sin(γT) − sin(γT')| ≤ |γ|(T − T')`, so the difference
of the sine series at two cutoffs loses the `1/γ` and is bounded by
`(T−T')·2h²·Σ_ρ m_ρ/(h²+γ_ρ²)` — no `log X` loss. -/

/-- Pointwise: `‖zeroSinTerm at X − zeroSinTerm at X'‖ ≤ 2h²(T−T')/(h²+γ²)`. -/
theorem norm_zeroSinTerm_sub_le {σ : ℝ} (hσ : 1/2 < σ) {X X' : ℝ} (hX' : 1 < X')
    (hXX : X' ≤ X) (γ : ℝ) :
    ‖zeroSinTerm (σ:ℂ) X γ - zeroSinTerm (σ:ℂ) X' γ‖
      ≤ 2*(σ - 1/2)^2 * (Real.log X - Real.log X') / ((σ - 1/2)^2 + γ^2) := by
  have hh : (0:ℝ) < σ - 1/2 := by linarith
  have hh2 : (0:ℝ) < (σ - 1/2)^2 := pow_pos hh 2
  have hT'0 : 0 < Real.log X' := Real.log_pos hX'
  have hTT : Real.log X' ≤ Real.log X := Real.log_le_log (by linarith) hXX
  have hD : (0:ℝ) < (σ - 1/2)^2 + γ^2 := by positivity
  by_cases hγ : γ = 0
  · -- plateau: the difference of the plateau values is `2(T − T')`
    subst hγ
    rw [zeroSinTerm, zeroSinTerm, if_pos rfl, if_pos rfl]
    have h1 : (2 * (Real.log X : ℂ)) - 2 * (Real.log X' : ℂ)
        = ((2*(Real.log X - Real.log X') : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [show (0:ℝ)^2 = 0 by norm_num, add_zero]
    rw [div_eq_mul_inv, show 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
        * ((σ - 1/2)^2)⁻¹ = 2*(Real.log X - Real.log X')
          * ((σ - 1/2)^2 * ((σ - 1/2)^2)⁻¹) by ring,
      mul_inv_cancel₀ hh2.ne', mul_one]
  · -- `γ ≠ 0`: MVT via `LipschitzWith 1 sin`
    have h1 : zeroSinTerm (σ:ℂ) X γ - zeroSinTerm (σ:ℂ) X' γ
        = ((2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*γ)
            * (Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ)) : ℝ) : ℂ) := by
      rw [zeroSinTerm, zeroSinTerm, if_neg hγ, if_neg hγ]
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    have hsin : |Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ)|
        ≤ (Real.log X - Real.log X') * |γ| := by
      have h2 := Real.lipschitzWith_sin.dist_le_mul (Real.log X * γ) (Real.log X' * γ)
      rw [Real.dist_eq, Real.dist_eq] at h2
      calc |Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ)|
          ≤ 1 * |Real.log X * γ - Real.log X' * γ| := by exact_mod_cast h2
        _ = |(Real.log X - Real.log X')| * |γ| := by
            rw [one_mul, show Real.log X * γ - Real.log X' * γ
              = (Real.log X - Real.log X') * γ by ring, abs_mul]
        _ = (Real.log X - Real.log X') * |γ| := by
            rw [abs_of_nonneg (by linarith)]
    have hγpos : (0:ℝ) < |γ| := abs_pos.mpr hγ
    calc |2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*γ)
          * (Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ))|
        = 2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*|γ|)
          * |Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ)| := by
          rw [abs_mul, abs_div, abs_mul, abs_two, abs_of_pos hh2, abs_mul,
            abs_of_pos hD]
      _ ≤ 2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*|γ|)
          * ((Real.log X - Real.log X') * |γ|) := by
          gcongr
      _ = 2*(σ - 1/2)^2 * (Real.log X - Real.log X') / ((σ - 1/2)^2 + γ^2) := by
          field_simp

/-- **The sine-difference estimate**: the two-cutoff difference of the sine series is
bounded by `2h²(T−T')·Σ_ρ m_ρ/(h²+γ_ρ²)`. -/
theorem norm_tsum_zeroSinTerm_sub_le {σ : ℝ} (hσ : 1/2 < σ) {X X' : ℝ} (hX' : 1 < X')
    (hXX : X' ≤ X) :
    ‖(∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im)
      - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im‖
      ≤ 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
          * ∑' ρ : ZetaZeros K,
              (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2) := by
  have hX : 1 < X := lt_of_lt_of_le hX' hXX
  have hsum : Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im) :=
    summable_zetaZeros_mul_of_norm_le K hσ (fun γ => norm_zeroSinTerm_le hσ hX γ)
  have hsum' : Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im) :=
    summable_zetaZeros_mul_of_norm_le K hσ (fun γ => norm_zeroSinTerm_le hσ hX' γ)
  rw [← Summable.tsum_sub hsum hsum']
  have hmaj : Summable (fun ρ : ZetaZeros K =>
      2*(σ - 1/2)^2 * (Real.log X - Real.log X')
        * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2))) :=
    (summable_zetaZeros_inv_sq K (σ - 1/2) (by linarith)).mul_left _
  have hpt : ∀ ρ : ZetaZeros K,
      ‖(zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im
        - (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im‖
      ≤ 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
          * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by
    intro ρ
    have hdnn : (0:ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
      exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
    rw [show (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im
        - (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im
        = (zetaZeroDivisor K ρ.1 : ℂ)
          * (zeroSinTerm (σ:ℂ) X ρ.1.im - zeroSinTerm (σ:ℂ) X' ρ.1.im) by ring,
      norm_mul, Complex.norm_intCast, abs_of_nonneg hdnn]
    calc (zetaZeroDivisor K ρ.1 : ℝ)
          * ‖zeroSinTerm (σ:ℂ) X ρ.1.im - zeroSinTerm (σ:ℂ) X' ρ.1.im‖
        ≤ (zetaZeroDivisor K ρ.1 : ℝ)
          * (2*(σ - 1/2)^2 * (Real.log X - Real.log X')
              / ((σ - 1/2)^2 + ρ.1.im^2)) :=
          mul_le_mul_of_nonneg_left (norm_zeroSinTerm_sub_le hσ hX' hXX _) hdnn
      _ = 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
            * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by ring
  rw [← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm ?_).trans
    (Summable.tsum_le_tsum (fun ρ => hpt ρ) ?_ hmaj)
  · exact hmaj.of_nonneg_of_le (fun ρ => norm_nonneg _) hpt
  · exact (hsum.sub hsum').norm

/-! ### The cosine and tail-integral estimates (paper lines 457–467)

The cosine terms are bounded trivially (`|cos| ≤ 1`) at each cutoff; the tail
integral is evaluated exactly by the kernel antiderivative
`d/dt(−e^{−ht}/t) = (h + 1/t)e^{−ht}/t`, giving the clean `1/T` bound with no
constants lost. -/

/-- Generic norm bound: a `c/(h²+γ²)`-bounded test function has divisor-weighted
series bounded by `c·Σ_ρ m_ρ/(h²+γ_ρ²)`. -/
theorem norm_tsum_zetaZeros_mul_le {σ : ℝ} (hσ : 1/2 < σ) {f : ℝ → ℂ} {c : ℝ}
    (hf : ∀ γ : ℝ, ‖f γ‖ ≤ c / ((σ - 1/2)^2 + γ^2)) :
    ‖∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * f ρ.1.im‖
      ≤ c * ∑' ρ : ZetaZeros K,
          (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2) := by
  have hmaj : Summable (fun ρ : ZetaZeros K =>
      c * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2))) :=
    (summable_zetaZeros_inv_sq K (σ - 1/2) (by linarith)).mul_left c
  have hpt : ∀ ρ : ZetaZeros K,
      ‖(zetaZeroDivisor K ρ.1 : ℂ) * f ρ.1.im‖
        ≤ c * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by
    intro ρ
    have hdnn : (0:ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
      exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hdnn]
    calc (zetaZeroDivisor K ρ.1 : ℝ) * ‖f ρ.1.im‖
        ≤ (zetaZeroDivisor K ρ.1 : ℝ) * (c / ((σ - 1/2)^2 + ρ.1.im^2)) :=
          mul_le_mul_of_nonneg_left (hf _) hdnn
      _ = c * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by ring
  rw [← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm ?_).trans
    (Summable.tsum_le_tsum (fun ρ => hpt ρ) ?_ hmaj)
  · exact hmaj.of_nonneg_of_le (fun ρ => norm_nonneg _) hpt
  · exact (summable_zetaZeros_mul_of_norm_le K hσ hf).norm

/-- **The cosine-terms estimate**: the two-cutoff difference of the cosine series is
bounded by `(2(h+1/T) + 2(h+1/T'))·Σ_ρ m_ρ/(h²+γ_ρ²)` (triangle inequality, `|cos|≤1`
at each cutoff). -/
theorem norm_tsum_zeroCosTerm_sub_le {σ : ℝ} (hσ : 1/2 < σ) {X X' : ℝ} (hX' : 1 < X')
    (hXX : X' ≤ X) :
    ‖(∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X ρ.1.im)
      - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroCosTerm (σ:ℂ) X' ρ.1.im‖
      ≤ (2*((σ - 1/2) + 1/Real.log X) + 2*((σ - 1/2) + 1/Real.log X'))
          * ∑' ρ : ZetaZeros K,
              (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2) := by
  have hX : 1 < X := lt_of_lt_of_le hX' hXX
  refine (norm_sub_le _ _).trans ?_
  rw [add_mul]
  gcongr
  · exact norm_tsum_zetaZeros_mul_le K hσ (fun γ => norm_zeroCosTerm_le hσ hX γ)
  · exact norm_tsum_zetaZeros_mul_le K hσ (fun γ => norm_zeroCosTerm_le hσ hX' γ)

/-- The kernel `(h + 1/t)e^{−ht}/t` is integrable on `(T, ∞)`. -/
theorem integrableOn_kernel {h T : ℝ} (hh : 0 < h) (hT : 0 < T) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (h + 1/t) * Real.exp (-h*t) / t) (Set.Ioi T) := by
  refine MeasureTheory.Integrable.mono'
    (g := fun t : ℝ => (h + 1/T) / T * Real.exp (-h*t))
    ((exp_neg_integrableOn_Ioi T hh).const_mul _) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div ?_ continuousOn_id (fun t ht => (hT.trans ht).ne')
    refine ContinuousOn.mul ?_
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    exact continuousOn_const.add (continuousOn_const.div continuousOn_id
      (fun t ht => (hT.trans ht).ne'))
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := hT.trans ht
    have hTt : T ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (h + 1/t) * Real.exp (-h*t) / t
        ≤ (h + 1/T) * Real.exp (-h*t) / T := by
          gcongr
      _ = (h + 1/T) / T * Real.exp (-h*t) := by ring

/-- **The exact kernel integral** (paper eq:diffeq consequence, lines 460–467):
`∫_T^∞ (h + 1/t)·e^{−ht}/t · dt = e^{−hT}/T` — the antiderivative is `−e^{−ht}/t`. -/
theorem integral_Ioi_kernel_eval {h T : ℝ} (hh : 0 < h) (hT : 0 < T) :
    ∫ t in Set.Ioi T, (h + 1/t) * Real.exp (-h*t) / t = Real.exp (-h*T) / T := by
  have hderiv : ∀ t ∈ Set.Ioi T, HasDerivAt (fun u : ℝ => -(Real.exp (-h*u) / u))
      ((h + 1/t) * Real.exp (-h*t) / t) t := by
    intro t ht
    have ht0 : (0:ℝ) < t := hT.trans ht
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-h*u))
        (Real.exp (-h*t) * (-h * 1)) t :=
      ((hasDerivAt_id t).const_mul (-h)).exp
    have h2 := (h1.div (hasDerivAt_id t) ht0.ne').neg
    have h3 : (h + 1/t) * Real.exp (-h*t) / t
        = -((Real.exp (-h*t) * (-h*1) * t - Real.exp (-h*t) * 1) / t^2) := by
      field_simp
      ring
    exact h3 ▸ h2
  have hint := integrableOn_kernel hh hT
  have hlim : Tendsto (fun t : ℝ => -(Real.exp (-h*t) / t)) atTop (nhds 0) := by
    rw [show (0:ℝ) = -0 by norm_num]
    exact Tendsto.neg (Tendsto.div_atTop
      (Real.tendsto_exp_atBot.comp
        (Tendsto.const_mul_atTop_of_neg (by linarith : (-h:ℝ) < 0) tendsto_id))
      tendsto_id)
  have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun u : ℝ => -(Real.exp (-h*u) / u))
    (f' := fun t : ℝ => (h + 1/t) * Real.exp (-h*t) / t)
    (by
      refine ContinuousWithinAt.neg ?_
      refine ContinuousWithinAt.div ?_ continuousWithinAt_id hT.ne'
      exact (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).continuousWithinAt)
    hderiv hint hlim
  rw [hkey]
  ring

/-- **The refined integral-piece bound**: `‖zeroIntTerm‖ ≤ 4/(T·(h²+γ²))` — the
tail integral is at most `1/T` by the exact kernel antiderivative (no opaque
constant). -/
theorem norm_zeroIntTerm_le_refined {σ : ℝ} (hσ : 1/2 < σ) {X : ℝ} (hX : 1 < X)
    (γ : ℝ) :
    ‖zeroIntTerm (σ:ℂ) X γ‖
      ≤ 4 / (Real.log X * ((σ - 1/2)^2 + γ^2)) := by
  have hh : (0:ℝ) < σ - 1/2 := by linarith
  have hT0 : 0 < Real.log X := Real.log_pos hX
  have hD : (0:ℝ) < (σ - 1/2)^2 + γ^2 := by positivity
  have hDc : ((σ:ℂ) - 1/2)^2 + (γ:ℂ)^2 = (((σ - 1/2)^2 + γ^2 : ℝ) : ℂ) := by
    push_cast
    ring
  set T : ℝ := Real.log X with hT_def
  -- the tail integral is bounded by `1/T`
  have hIle : ‖∫ t in Set.Ioi T,
      ((Real.cos (t * γ) : ℝ) : ℂ) * auxF (σ:ℂ) X t * ((((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2)‖
      ≤ 1 / T := by
    have hmajint : MeasureTheory.IntegrableOn (fun t : ℝ =>
        Real.exp ((σ - 1/2)*T) * ((σ - 1/2 + 1/t) * Real.exp (-(σ - 1/2)*t) / t))
        (Set.Ioi T) := (integrableOn_kernel hh hT0).const_mul _
    have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi T)),
        ‖((Real.cos (t * γ) : ℝ) : ℂ) * auxF (σ:ℂ) X t
          * ((((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2)‖
        ≤ Real.exp ((σ - 1/2)*T) * ((σ - 1/2 + 1/t) * Real.exp (-(σ - 1/2)*t) / t) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := hT0.trans ht
      have hTt : T ≤ t := le_of_lt ht
      have habs : |t| = t := abs_of_pos ht0
      have hauxval : auxF (σ:ℂ) X t
          = ((T/t * Real.exp (-(σ - 1/2)*(t - T)) : ℝ) : ℂ) := by
        rw [auxF_ofReal, habs,
          if_neg (by simp only [← hT_def]; exact not_le.mpr ht), ← hT_def]
      have hqval : ((((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2)
          = ((((σ - 1/2)*t + 1)/t^2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hauxval, hqval, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      have h2 : |T/t * Real.exp (-(σ - 1/2)*(t - T))|
          = T/t * Real.exp (-(σ - 1/2)*(t - T)) := abs_of_nonneg (by positivity)
      have h3 : |((σ - 1/2)*t + 1)/t^2| = ((σ - 1/2)*t + 1)/t^2 :=
        abs_of_nonneg (by positivity)
      rw [h2, h3]
      calc |Real.cos (t*γ)| * (T/t * Real.exp (-(σ - 1/2)*(t - T)))
            * (((σ - 1/2)*t + 1)/t^2)
          ≤ 1 * (T/t * Real.exp (-(σ - 1/2)*(t - T))) * (((σ - 1/2)*t + 1)/t^2) := by
            gcongr
            · exact abs_cos_le_one _
        _ = Real.exp ((σ - 1/2)*T)
              * (Real.exp (-(σ - 1/2)*t) * (((σ - 1/2)*t + 1) * (T/t^3))) := by
            rw [show -(σ - 1/2)*(t - T) = -(σ - 1/2)*t + (σ - 1/2)*T by ring,
              Real.exp_add]
            field_simp
        _ ≤ Real.exp ((σ - 1/2)*T)
              * (Real.exp (-(σ - 1/2)*t) * (((σ - 1/2)*t + 1) * (1/t^2))) := by
            have h4 : T/t^3 ≤ 1/t^2 := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith
            gcongr
        _ = Real.exp ((σ - 1/2)*T) * ((σ - 1/2 + 1/t) * Real.exp (-(σ - 1/2)*t) / t) := by
            field_simp
    refine (MeasureTheory.norm_integral_le_of_norm_le hmajint hbound).trans ?_
    rw [MeasureTheory.integral_const_mul, integral_Ioi_kernel_eval hh hT0,
      ← mul_div_assoc, ← Real.exp_add,
      show (σ - 1/2)*T + -(σ - 1/2)*T = 0 by ring, Real.exp_zero]
  -- assemble
  rw [zeroIntTerm, norm_mul, norm_div, hDc, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hD, show ‖(4:ℂ)‖ = 4 by norm_num]
  calc 4 / ((σ - 1/2)^2 + γ^2) * ‖∫ t in Set.Ioi (Real.log X),
        ((Real.cos (t * γ) : ℝ) : ℂ) * auxF (σ:ℂ) X t
          * ((((σ:ℂ) - 1/2)*t + 1)/(t:ℂ)^2)‖
      ≤ 4 / ((σ - 1/2)^2 + γ^2) * (1 / Real.log X) := by
        gcongr
    _ = 4 / (Real.log X * ((σ - 1/2)^2 + γ^2)) := by
        field_simp

/-- **The integral-terms estimate**: the two-cutoff difference of the tail-integral
series is bounded by `(4/T + 4/T')·Σ_ρ m_ρ/(h²+γ_ρ²)`. -/
theorem norm_tsum_zeroIntTerm_sub_le {σ : ℝ} (hσ : 1/2 < σ) {X X' : ℝ} (hX' : 1 < X')
    (hXX : X' ≤ X) :
    ‖(∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X ρ.1.im)
      - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroIntTerm (σ:ℂ) X' ρ.1.im‖
      ≤ (4 / Real.log X + 4 / Real.log X')
          * ∑' ρ : ZetaZeros K,
              (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2) := by
  have hX : 1 < X := lt_of_lt_of_le hX' hXX
  refine (norm_sub_le _ _).trans ?_
  rw [add_mul]
  gcongr
  · refine norm_tsum_zetaZeros_mul_le K hσ (fun γ => ?_)
    have h1 := norm_zeroIntTerm_le_refined hσ hX γ
    rwa [show (4:ℝ) / (Real.log X * ((σ - 1/2)^2 + γ^2))
      = 4 / Real.log X / ((σ - 1/2)^2 + γ^2) by rw [div_div]] at h1
  · refine norm_tsum_zetaZeros_mul_le K hσ (fun γ => ?_)
    have h1 := norm_zeroIntTerm_le_refined hσ hX' γ
    rwa [show (4:ℝ) / (Real.log X' * ((σ - 1/2)^2 + γ^2))
      = 4 / Real.log X' / ((σ - 1/2)^2 + γ^2) by rw [div_div]] at h1

/-! ### The archimedean estimate: the `β`-kernel (paper lines 476–518)

The combined `sinh + cosh` archimedean kernel is
`L(U) = log((1+e^{−U})/(1−e^{−U})) = 2 artanh(e^{−U})`; the paper's `β`-bound rests
on `e^{U/2}·L(U)` being decreasing, which follows from `L(U) ≤ 1/sinh U`
(via `log(1+x) ≤ x` and `−log(1−x) ≤ x/(1−x)`). -/

/-- The combined archimedean log-kernel `L(U) = log(1+e^{−U}) − log(1−e^{−U})`. -/
noncomputable def archKernelL (U : ℝ) : ℝ :=
  Real.log (1 + Real.exp (-U)) - Real.log (1 - Real.exp (-U))

theorem exp_neg_lt_one {U : ℝ} (hU : 0 < U) : Real.exp (-U) < 1 := by
  have h1 : Real.exp (-U) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
  simpa using h1

theorem archKernelL_pos {U : ℝ} (hU : 0 < U) : 0 < archKernelL U := by
  have he1 : Real.exp (-U) < 1 := exp_neg_lt_one hU
  have he0 : 0 < Real.exp (-U) := Real.exp_pos _
  have h1 : Real.log (1 - Real.exp (-U)) < 0 :=
    Real.log_neg (by linarith) (by linarith)
  have h2 : 0 < Real.log (1 + Real.exp (-U)) :=
    Real.log_pos (by linarith)
  rw [archKernelL]
  linarith

/-- `sinh U = (1 − x²)/(2x)` for `x = e^{−U}`. -/
theorem sinh_eq_exp_neg {U : ℝ} :
    Real.sinh U = (1 - Real.exp (-U)^2) / (2*Real.exp (-U)) := by
  have hxU : Real.exp U = (Real.exp (-U))⁻¹ := by
    rw [← Real.exp_neg, neg_neg]
  rw [Real.sinh_eq, hxU]
  have hne : Real.exp (-U) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- **(A)** `L(U) ≤ 2/sinh U` (crude log bounds suffice for the factor 2). -/
theorem archKernelL_le_two_inv_sinh {U : ℝ} (hU : 0 < U) :
    archKernelL U ≤ 2 / Real.sinh U := by
  set x : ℝ := Real.exp (-U) with hx_def
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x < 1 := exp_neg_lt_one hU
  have hx2 : (0:ℝ) < 1 - x^2 := by nlinarith
  rw [sinh_eq_exp_neg, ← hx_def, div_div_eq_mul_div]
  have hlog1 : Real.log (1 + x) ≤ x := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + x)
    linarith
  have hlog2 : -Real.log (1 - x) ≤ x / (1 - x) := by
    have h1 : Real.log (1 - x) = -Real.log (1/(1-x)) := by
      rw [Real.log_div one_ne_zero (by linarith : (1:ℝ) - x ≠ 0), Real.log_one]
      ring
    rw [h1, neg_neg]
    have h2 := Real.log_le_sub_one_of_pos
      (by positivity : (0:ℝ) < 1/(1-x))
    have h3 : 1/(1-x) - 1 = x/(1-x) := by
      rw [eq_div_iff (by linarith : (1:ℝ) - x ≠ 0), sub_mul, one_mul,
        div_mul_cancel₀ _ (by linarith : (1:ℝ) - x ≠ 0)]
      ring
    linarith
  rw [archKernelL, ← hx_def]
  have hL : x + x/(1-x) = x*(2-x)/(1-x) := by
    have hne : (1:ℝ) - x ≠ 0 := by linarith
    rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
    ring
  have hxx : x + x/(1-x) ≤ 2*(2*x)/(1-x^2) := by
    rw [hL, div_le_div_iff₀ (by linarith) hx2]
    nlinarith [mul_pos hx0 (by linarith : (0:ℝ) < 1 - x), sq_nonneg x,
      mul_pos (mul_pos hx0 hx0) (by linarith : (0:ℝ) < 1 - x)]
  linarith

/-- The derivative of the weighted kernel:
`d/dU (e^{U/2}·L(U)) = e^{U/2}·(L(U)/2 − 1/sinh U)`. -/
theorem hasDerivAt_exp_half_mul_archKernelL {U : ℝ} (hU : 0 < U) :
    HasDerivAt (fun U : ℝ => Real.exp (U/2) * archKernelL U)
      (Real.exp (U/2) * (archKernelL U / 2 - 1 / Real.sinh U)) U := by
  have he0 : 0 < Real.exp (-U) := Real.exp_pos _
  have he1 : Real.exp (-U) < 1 := exp_neg_lt_one hU
  have h1 : HasDerivAt (fun U : ℝ => Real.exp (U/2)) (Real.exp (U/2) * (1/2)) U := by
    have h0 := ((hasDerivAt_id U).div_const (2:ℝ)).exp
    simpa using h0
  have hexpneg : HasDerivAt (fun U : ℝ => Real.exp (-U)) (-Real.exp (-U)) U := by
    have h0 := ((hasDerivAt_id U).neg).exp
    simpa using h0
  have h2a : HasDerivAt (fun U : ℝ => Real.log (1 + Real.exp (-U)))
      (-Real.exp (-U)/(1 + Real.exp (-U))) U := by
    have h0 := ((hasDerivAt_const U (1:ℝ)).add hexpneg).log
      (by linarith : (1:ℝ) + Real.exp (-U) ≠ 0)
    simpa using h0
  have h2b : HasDerivAt (fun U : ℝ => Real.log (1 - Real.exp (-U)))
      (Real.exp (-U)/(1 - Real.exp (-U))) U := by
    have h0 := ((hasDerivAt_const U (1:ℝ)).sub hexpneg).log
      (by linarith : (1:ℝ) - Real.exp (-U) ≠ 0)
    rw [show Real.exp (-U)/(1 - Real.exp (-U))
      = (0 - -Real.exp (-U))/(1 - Real.exp (-U)) by ring]
    exact h0
  have h2 : HasDerivAt (fun U : ℝ =>
      Real.log (1 + Real.exp (-U)) - Real.log (1 - Real.exp (-U)))
      (-Real.exp (-U)/(1 + Real.exp (-U)) - Real.exp (-U)/(1 - Real.exp (-U))) U :=
    h2a.sub h2b
  have h3 := h1.mul h2
  have hLder : -Real.exp (-U)/(1 + Real.exp (-U)) - Real.exp (-U)/(1 - Real.exp (-U))
      = -(1 / Real.sinh U) := by
    rw [sinh_eq_exp_neg]
    have hx2 : (0:ℝ) < 1 - Real.exp (-U)^2 := by nlinarith
    have hne1 : (1:ℝ) + Real.exp (-U) ≠ 0 := by linarith
    have hne2 : (1:ℝ) - Real.exp (-U) ≠ 0 := by linarith
    have hne3 : (1:ℝ) - Real.exp (-U)^2 ≠ 0 := hx2.ne'
    field_simp
    ring
  have hval : Real.exp (U/2) * (archKernelL U / 2 - 1 / Real.sinh U)
      = Real.exp (U/2) * (1/2)
        * (Real.log (1 + Real.exp (-U)) - Real.log (1 - Real.exp (-U)))
        + Real.exp (U/2)
          * (-Real.exp (-U)/(1 + Real.exp (-U)) - Real.exp (-U)/(1 - Real.exp (-U))) := by
    rw [hLder]
    unfold archKernelL
    ring
  exact hval ▸ h3

/-- **(B)** `e^{U/2}·L(U)` is antitone on `(0, ∞)`. -/
theorem antitoneOn_exp_half_mul_archKernelL :
    AntitoneOn (fun U : ℝ => Real.exp (U/2) * archKernelL U) (Set.Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
  · intro U hU
    exact ((hasDerivAt_exp_half_mul_archKernelL hU).continuousAt).continuousWithinAt
  · rw [interior_Ioi]
    intro U hU
    exact ((hasDerivAt_exp_half_mul_archKernelL hU).differentiableAt).differentiableWithinAt
  · rw [interior_Ioi]
    intro U hU
    rw [(hasDerivAt_exp_half_mul_archKernelL hU).deriv]
    have hL := archKernelL_le_two_inv_sinh hU
    have hs : 0 < Real.sinh U := Real.sinh_pos_iff.mpr hU
    have h1 : archKernelL U / 2 - 1 / Real.sinh U ≤ 0 := by
      have h2 : (0:ℝ) < 1 / Real.sinh U := by positivity
      have h3 : archKernelL U ≤ 2 * (1 / Real.sinh U) := by
        rw [show (2:ℝ) * (1 / Real.sinh U) = 2 / Real.sinh U by ring]
        exact hL
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h1

/-! ### The cutoff-derivative representation (c4-C1)

For fixed `y > 0` the map `U ↦ F_{σ,e^U}(y)` is the plateau `1` for `U ≥ y` and the
smooth tail `(U/y)e^{−h(y−U)}` for `U ≤ y` (both branches agree at `U = y`), so the
two-cutoff difference is the interval integral of the `U`-derivative
`((1+hU)/y)e^{−h(y−U)}` cut off at `U = y`. -/

/-- The real auxiliary-function family in the log-cutoff `U`: `F_{σ,e^U}(y)` for
`y > 0`. -/
noncomputable def auxFCut (σ U y : ℝ) : ℝ :=
  if y ≤ U then 1 else U/y * Real.exp (-(σ - 1/2)*(y - U))

/-- On the real ray, `auxF` at cutoff `X` is the coercion of `auxFCut σ (log X)`. -/
theorem auxF_eq_auxFCut (σ : ℝ) (X : ℝ) {y : ℝ} (hy : 0 < y) :
    auxF (σ:ℂ) X y = ((auxFCut σ (Real.log X) y : ℝ) : ℂ) := by
  rw [auxF_ofReal, auxFCut, abs_of_pos hy]

/-- The tail branch extends continuously through the kink: for `U ≤ y`,
`auxFCut σ U y = (U/y)e^{−h(y−U)}`. -/
theorem auxFCut_eq_tail {σ U y : ℝ} (hy : 0 < y) (hU : U ≤ y) :
    auxFCut σ U y = U/y * Real.exp (-(σ - 1/2)*(y - U)) := by
  rw [auxFCut]
  by_cases hcase : y ≤ U
  · have hUy : U = y := le_antisymm hU hcase
    subst hUy
    rw [if_pos le_rfl, sub_self, mul_zero, Real.exp_zero,
      div_self hy.ne', one_mul]
  · rw [if_neg hcase]

/-- The `U`-derivative of the tail branch. -/
theorem hasDerivAt_auxFCut_tail {σ y : ℝ} (U : ℝ) :
    HasDerivAt (fun U : ℝ => U/y * Real.exp (-(σ - 1/2)*(y - U)))
      ((1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U))) U := by
  have h1 : HasDerivAt (fun U : ℝ => U/y) (1/y) U := (hasDerivAt_id U).div_const y
  have h2 : HasDerivAt (fun U : ℝ => Real.exp (-(σ - 1/2)*(y - U)))
      (Real.exp (-(σ - 1/2)*(y - U)) * (σ - 1/2)) U := by
    have h3 : HasDerivAt (fun U : ℝ => -(σ - 1/2)*(y - U)) (σ - 1/2) U := by
      have h4 := ((hasDerivAt_id U).const_sub y).const_mul (-(σ - 1/2))
      simpa using h4
    simpa using h3.exp
  have h5 := h1.mul h2
  have hval : (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U))
      = 1/y * Real.exp (-(σ - 1/2)*(y - U))
        + U/y * (Real.exp (-(σ - 1/2)*(y - U)) * (σ - 1/2)) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div,
      ← add_div]
    congr 1
    ring
  exact hval ▸ h5

/-- The cutoff-difference integrand: the `U`-derivative, cut off at `U = y`. -/
noncomputable def cutKernel (σ y U : ℝ) : ℝ :=
  if U < y then (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U)) else 0

theorem cutKernel_nonneg {σ y U : ℝ} (hσ : 1/2 < σ) (hy : 0 < y) (hU : 0 ≤ U) :
    0 ≤ cutKernel σ y U := by
  rw [cutKernel]
  by_cases hcase : U < y
  · rw [if_pos hcase]
    have h1 : (0:ℝ) ≤ 1 + (σ - 1/2)*U := by nlinarith
    positivity
  · rw [if_neg hcase]

theorem measurable_cutKernel (σ y : ℝ) : Measurable (cutKernel σ y) := by
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) ?_
    measurable_const
  fun_prop

theorem intervalIntegrable_cutKernel {σ y : ℝ} (hσ : 1/2 < σ) (hy : 0 < y)
    {T' T : ℝ} (hT' : 0 < T') (hTT : T' ≤ T) :
    IntervalIntegrable (cutKernel σ y) MeasureTheory.volume T' T := by
  refine IntervalIntegrable.mono_fun'
    (g := fun _ : ℝ => (1 + (σ - 1/2)*T)/y)
    (intervalIntegrable_const) ?_ ?_
  · exact (measurable_cutKernel σ y).aestronglyMeasurable
  · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun U hU => ?_)
    rw [Set.uIoc_of_le hTT] at hU
    have hU0 : 0 < U := hT'.trans hU.1
    rw [Real.norm_eq_abs, abs_of_nonneg (cutKernel_nonneg hσ hy hU0.le), cutKernel]
    by_cases hcase : U < y
    · rw [if_pos hcase]
      have he : Real.exp (-(σ - 1/2)*(y - U)) ≤ 1 := by
        have h0 : (0:ℝ) ≤ (σ - 1/2)*(y - U) :=
          mul_nonneg (by linarith) (by linarith)
        calc Real.exp (-(σ - 1/2)*(y - U)) ≤ Real.exp 0 :=
              Real.exp_le_exp.mpr (by nlinarith [h0])
          _ = 1 := Real.exp_zero
      have h1 : (0:ℝ) ≤ 1 + (σ - 1/2)*U := by nlinarith
      calc (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U))
          ≤ (1 + (σ - 1/2)*U)/y * 1 :=
            mul_le_mul_of_nonneg_left he (by positivity)
        _ ≤ (1 + (σ - 1/2)*T)/y := by
            rw [mul_one]
            have h2 : (σ - 1/2)*U ≤ (σ - 1/2)*T :=
              mul_le_mul_of_nonneg_left hU.2 (by linarith)
            gcongr
    · rw [if_neg hcase]
      have h1 : (0:ℝ) ≤ 1 + (σ - 1/2)*T := by nlinarith
      positivity

/-- Almost every `U` differs from `y`. -/
theorem ae_ne_singleton (y : ℝ) : ∀ᵐ U : ℝ, U ≠ y := by
  refine MeasureTheory.ae_iff.mpr ?_
  simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
  exact MeasureTheory.measure_singleton y

/-- **(C1) The cutoff-difference representation**: for `0 < T' ≤ T` and `y > 0`,
`F_{σ,e^T}(y) − F_{σ,e^{T'}}(y) = ∫_{T'}^T cutKernel σ y U dU`. -/
theorem auxFCut_sub_eq_integral {σ : ℝ} (hσ : 1/2 < σ) {T' T y : ℝ} (hT' : 0 < T')
    (hTT : T' ≤ T) (hy : 0 < y) :
    auxFCut σ T y - auxFCut σ T' y = ∫ U in T'..T, cutKernel σ y U := by
  have hcont : Continuous (fun U : ℝ =>
      (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U))) := by fun_prop
  by_cases hyT' : y ≤ T'
  · -- plateau at both cutoffs; the kernel vanishes on `[T', T]`
    have h1 : auxFCut σ T y = 1 := by rw [auxFCut, if_pos (le_trans hyT' hTT)]
    have h2 : auxFCut σ T' y = 1 := by rw [auxFCut, if_pos hyT']
    rw [h1, h2, sub_self,
      intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun U hU => ?_),
      intervalIntegral.integral_zero]
    rw [Set.uIcc_of_le hTT] at hU
    rw [cutKernel, if_neg (not_lt.mpr (le_trans hyT' hU.1))]
  · rw [not_le] at hyT'
    by_cases hyT : T ≤ y
    · -- tail at both cutoffs: pure FTC on `[T', T] ⊆ (0, y]`
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun U : ℝ => U/y * Real.exp (-(σ - 1/2)*(y - U)))
        (f' := fun U : ℝ => (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U)))
        (fun U _ => hasDerivAt_auxFCut_tail U)
        (hcont.intervalIntegrable T' T)
      rw [auxFCut_eq_tail hy hyT, auxFCut_eq_tail hy (le_trans hTT hyT), ← hftc]
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [ae_ne_singleton y] with U hUy hUIoc
      rw [Set.uIoc_of_le hTT] at hUIoc
      have hUlt : U < y := lt_of_le_of_ne (le_trans hUIoc.2 hyT) hUy
      rw [cutKernel, if_pos hUlt]
    · -- straddling case `T' < y < T`: split at `y`
      rw [not_le] at hyT
      have hint1 := intervalIntegrable_cutKernel (T' := T') (T := y) hσ hy hT'
        (le_of_lt hyT')
      have hint2 := intervalIntegrable_cutKernel (T' := y) (T := T) hσ hy hy
        (le_of_lt hyT)
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
      -- the `[y, T]` piece vanishes pointwise
      have hzero : (∫ U in y..T, cutKernel σ y U) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun U hU => ?_),
          intervalIntegral.integral_zero]
        rw [Set.uIcc_of_le (le_of_lt hyT)] at hU
        rw [cutKernel, if_neg (not_lt.mpr hU.1)]
      rw [hzero, add_zero]
      -- the `[T', y]` piece: FTC ending exactly at the kink
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun U : ℝ => U/y * Real.exp (-(σ - 1/2)*(y - U)))
        (f' := fun U : ℝ => (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U)))
        (fun U _ => hasDerivAt_auxFCut_tail U)
        (hcont.intervalIntegrable T' y)
      have hplateau : auxFCut σ T y = 1 := by
        rw [auxFCut, if_pos (le_of_lt hyT)]
      have htailT' : auxFCut σ T' y
          = T'/y * Real.exp (-(σ - 1/2)*(y - T')) :=
        auxFCut_eq_tail hy (le_of_lt hyT')
      rw [hplateau, htailT']
      rw [show (∫ U in T'..y, cutKernel σ y U)
          = ∫ U in T'..y, (1 + (σ - 1/2)*U)/y * Real.exp (-(σ - 1/2)*(y - U)) from ?_,
        hftc, sub_self, mul_zero, Real.exp_zero, mul_one, div_self hy.ne']
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [ae_ne_singleton y] with U hUy hUIoc
      rw [Set.uIoc_of_le (le_of_lt hyT')] at hUIoc
      have hUlt : U < y := lt_of_le_of_ne hUIoc.2 hUy
      rw [cutKernel, if_pos hUlt]


/-! ### The closed-form archimedean tail integrals (c4-C2)

`∫_U^∞ dy/(e^y−1) = −log(1−e^{−U})` and `∫_U^∞ dy/(e^y+1) = log(1+e^{−U})` — the two
halves of the `archKernelL` closed form. -/

theorem integrableOn_inv_exp_sub_one {U : ℝ} (hU : 0 < U) :
    MeasureTheory.IntegrableOn (fun y : ℝ => 1/(Real.exp y - 1)) (Set.Ioi U) := by
  have hbound : ∀ y ∈ Set.Ioi U, ‖1/(Real.exp y - 1)‖
      ≤ (1 - Real.exp (-U))⁻¹ * Real.exp (-y) := by
    intro y hy
    have hyU : U < y := hy
    have he1 : Real.exp (-U) < 1 := exp_neg_lt_one hU
    have hey : 0 < Real.exp y := Real.exp_pos _
    have hgt : 1 < Real.exp y := by
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp y := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1/(Real.exp y - 1))]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.exp y - 1)]
    have hkey : Real.exp (-y) * (Real.exp y - 1) = 1 - Real.exp (-y) := by
      rw [mul_sub, ← Real.exp_add, mul_one]
      norm_num
    calc (1:ℝ) = (1 - Real.exp (-U))⁻¹ * (1 - Real.exp (-U)) := by
          rw [inv_mul_cancel₀ (by linarith : (1:ℝ) - Real.exp (-U) ≠ 0)]
      _ ≤ (1 - Real.exp (-U))⁻¹ * (1 - Real.exp (-y)) := by
          gcongr
      _ = (1 - Real.exp (-U))⁻¹ * Real.exp (-y) * (Real.exp y - 1) := by
          rw [mul_assoc, hkey]
  refine MeasureTheory.Integrable.mono'
    ((exp_neg_integrableOn_Ioi U one_pos).const_mul ((1 - Real.exp (-U))⁻¹)) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_exp.continuousOn.sub continuousOn_const) ?_
    intro y hy
    have hgt : 1 < Real.exp y := by
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp y := Real.exp_lt_exp.mpr (by linarith [hU.trans hy])
    linarith
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
    have h1 := hbound y hy
    calc ‖1/(Real.exp y - 1)‖ ≤ (1 - Real.exp (-U))⁻¹ * Real.exp (-y) := h1
      _ = (1 - Real.exp (-U))⁻¹ * Real.exp (-1*y) := by norm_num

theorem integral_Ioi_inv_exp_sub_one {U : ℝ} (hU : 0 < U) :
    ∫ y in Set.Ioi U, 1/(Real.exp y - 1) = -Real.log (1 - Real.exp (-U)) := by
  have hderiv : ∀ y ∈ Set.Ioi U, HasDerivAt (fun y : ℝ => Real.log (1 - Real.exp (-y)))
      (1/(Real.exp y - 1)) y := by
    intro y hy
    have hyU : U < y := hy
    have hy0 : 0 < y := hU.trans hyU
    have he1 : Real.exp (-y) < 1 := exp_neg_lt_one hy0
    have hexpneg : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
      have h0 := ((hasDerivAt_id y).neg).exp
      simpa using h0
    have h1 := ((hasDerivAt_const y (1:ℝ)).sub hexpneg).log
      (by linarith : (1:ℝ) - Real.exp (-y) ≠ 0)
    have hval : (0 - -Real.exp (-y))/(1 - Real.exp (-y)) = 1/(Real.exp y - 1) := by
      rw [zero_sub, neg_neg]
      rw [div_eq_div_iff (by linarith : (1:ℝ) - Real.exp (-y) ≠ 0)
        (by
          have hgt : 1 < Real.exp y := by
            calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
              _ < Real.exp y := Real.exp_lt_exp.mpr (by linarith)
          linarith : (Real.exp y - 1) ≠ 0)]
      rw [mul_sub, ← Real.exp_add, mul_one, neg_add_cancel, Real.exp_zero, one_mul]
    exact hval ▸ h1
  have hlim : Tendsto (fun y : ℝ => Real.log (1 - Real.exp (-y))) atTop (nhds 0) := by
    rw [show (0:ℝ) = Real.log (1 - 0) by norm_num]
    refine Tendsto.log ?_ (by norm_num)
    exact tendsto_const_nhds.sub
      (Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg
        (by norm_num : (-1:ℝ) < 0) tendsto_id) |>.congr (fun y => by norm_num))
  have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun y : ℝ => Real.log (1 - Real.exp (-y)))
    (f' := fun y : ℝ => 1/(Real.exp y - 1))
    (by
      have he1 : Real.exp (-U) < 1 := exp_neg_lt_one hU
      refine ContinuousWithinAt.log ?_ (by linarith)
      exact (continuous_const.sub (Real.continuous_exp.comp
        continuous_neg)).continuousWithinAt)
    hderiv (integrableOn_inv_exp_sub_one hU) hlim
  rw [hkey]
  ring

theorem integrableOn_inv_exp_add_one {U : ℝ} (hU : 0 < U) :
    MeasureTheory.IntegrableOn (fun y : ℝ => 1/(Real.exp y + 1)) (Set.Ioi U) := by
  refine (integrableOn_inv_exp_sub_one hU).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.div continuousOn_const
      (Real.continuous_exp.continuousOn.add continuousOn_const) ?_
    intro y _
    positivity
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
    have hgt : 1 < Real.exp y := by
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ < Real.exp y := Real.exp_lt_exp.mpr (by linarith [hU.trans hy])
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1/(Real.exp y + 1))]
    have h1 : (0:ℝ) < Real.exp y - 1 := by linarith
    have h2 : Real.exp y - 1 ≤ Real.exp y + 1 := by linarith
    exact one_div_le_one_div_of_le h1 h2

theorem integral_Ioi_inv_exp_add_one {U : ℝ} (hU : 0 < U) :
    ∫ y in Set.Ioi U, 1/(Real.exp y + 1) = Real.log (1 + Real.exp (-U)) := by
  have hderiv : ∀ y ∈ Set.Ioi U, HasDerivAt (fun y : ℝ => -Real.log (1 + Real.exp (-y)))
      (1/(Real.exp y + 1)) y := by
    intro y hy
    have hy0 : 0 < y := hU.trans hy
    have he0 : 0 < Real.exp (-y) := Real.exp_pos _
    have hexpneg : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-y)) y := by
      have h0 := ((hasDerivAt_id y).neg).exp
      simpa using h0
    have h1 := (((hasDerivAt_const y (1:ℝ)).add hexpneg).log
      (by linarith : (1:ℝ) + Real.exp (-y) ≠ 0)).neg
    have hval : -((0 + -Real.exp (-y))/(1 + Real.exp (-y))) = 1/(Real.exp y + 1) := by
      rw [zero_add]
      rw [neg_div, neg_neg]
      rw [div_eq_div_iff (by linarith : (1:ℝ) + Real.exp (-y) ≠ 0)
        (by positivity : (Real.exp y + 1) ≠ 0)]
      rw [mul_add, ← Real.exp_add, mul_one, neg_add_cancel, Real.exp_zero, one_mul]
    exact hval ▸ h1
  have hlim : Tendsto (fun y : ℝ => -Real.log (1 + Real.exp (-y))) atTop (nhds 0) := by
    rw [show (0:ℝ) = -Real.log (1 + 0) by norm_num]
    refine Tendsto.neg (Tendsto.log ?_ (by norm_num))
    exact tendsto_const_nhds.add
      (Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg
        (by norm_num : (-1:ℝ) < 0) tendsto_id) |>.congr (fun y => by norm_num))
  have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun y : ℝ => -Real.log (1 + Real.exp (-y)))
    (f' := fun y : ℝ => 1/(Real.exp y + 1))
    (by
      refine ContinuousWithinAt.neg ?_
      refine ContinuousWithinAt.log ?_ (by positivity)
      exact (continuous_const.add (Real.continuous_exp.comp
        continuous_neg)).continuousWithinAt)
    hderiv (integrableOn_inv_exp_add_one hU) hlim
  rw [hkey]
  ring


end DedekindResidue

end
