/-
DedekindResidue: assembly of Weil's explicit formula (Poitou's formula (6)).

This file combines the zero-capture contour (Prop 1, `ZeroCapture.lean`), the
prime side (Prop 2, `PrimeSide.lean`/`FourierJordan.lean`) and the Γ-side
(Prop 3 + I_G, `GammaSide.lean`) into Poitou's explicit formula, following
"Sur les petits discriminants" (Séminaire DPP 1976/77, exposé 6).
-/
module

public import Mathlib
public import DedekindResidue.ExplicitFormula.ZeroCapture
public import DedekindResidue.ExplicitFormula.GammaSide

@[expose] public section

namespace DedekindResidue

open MeasureTheory Complex intervalIntegral Real Filter NumberField
open scoped ENNReal NNReal

variable (K : Type*) [Field K] [NumberField K]

/-- **The right-edge split of `Λ_ent'/Λ_ent`** (Poitou p. 6-01/6-02): on `Re s > 1`,

`logDeriv Λ_ent(s) = 1/s + 1/(s-1) + (1/2)log|d| + γ_K'/γ_K(s) + ζ_K'/ζ_K(s)`. -/
theorem logDeriv_completedDedekindZetaEntire_split {s : ℂ} (hs : 1 < s.re) :
    logDeriv (completedDedekindZetaEntire K) s
      = 1/s + 1/(s-1) + ((Real.log |NumberField.discr K| : ℝ) : ℂ)/2
        + logDeriv (gammaFactor K) s
        + logDeriv (NumberField.dedekindZeta K) s := by
  have hUo : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hs
    linarith
  have hs1 : s ≠ 1 := by
    intro h0
    rw [h0, Complex.one_re] at hs
    linarith
  have hspos : 0 < s.re := by linarith
  have hdiscr0 : (0:ℝ) < (|NumberField.discr K| : ℝ) := by
    have h0 : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
    have h1 : 0 < |NumberField.discr K| := abs_pos.mpr h0
    exact_mod_cast h1
  have hdiscrC : (((|NumberField.discr K| : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hdiscr0.ne'
  -- the eventual product form
  have hev : completedDedekindZetaEntire K =ᶠ[nhds s]
      fun z => z * (z - 1) * (((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2)
        * (gammaFactor K z * NumberField.dedekindZeta K z)) := by
    filter_upwards [hUo.mem_nhds hs] with z hz
    have hz1 : (1:ℝ) < z.re := hz
    have hz0' : z ≠ 0 := by
      intro h0
      rw [h0, Complex.zero_re] at hz1
      linarith
    have hz1' : z ≠ 1 := by
      intro h0
      rw [h0, Complex.one_re] at hz1
      linarith
    rw [completedDedekindZetaEntire_eq K hz0' hz1',
      completedDedekindZeta_eq_of_one_lt_re K hz1, completedZetaPrefactor]
    ring
  have hld : logDeriv (completedDedekindZetaEntire K) s
      = logDeriv (fun z : ℂ => z * (z - 1) * (((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2)
        * (gammaFactor K z * NumberField.dedekindZeta K z))) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hld]
  -- nonvanishing and differentiability of the factors
  have hγne : gammaFactor K s ≠ 0 := gammaFactor_ne_zero_of_re_pos K hspos
  have hζne : NumberField.dedekindZeta K s ≠ 0 := dedekindZeta_ne_zero_of_one_lt_re K hs
  have hγd : DifferentiableAt ℂ (gammaFactor K) s :=
    ((differentiableAt_Gammaℝ_of_re_pos hspos).pow _).mul
      ((differentiableAt_Gammaℂ_of_re_pos hspos).pow _)
  have hcpow_d : DifferentiableAt ℂ
      (fun z : ℂ => ((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2)) s := by
    have h0 : HasDerivAt (fun w : ℂ => w / 2) (1/2) s := by
      have h1 := (hasDerivAt_id s).div_const (2:ℂ)
      have h3 : (1:ℂ)/2 = 1/2 := by norm_num
      rw [h3] at h1
      exact h1
    exact (h0.const_cpow (Or.inl hdiscrC)).differentiableAt
  have hcpow_ne : ((|NumberField.discr K| : ℝ) : ℂ) ^ (s/2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hdiscrC
  have hζd : DifferentiableAt ℂ (NumberField.dedekindZeta K) s := by
    have hev2 : NumberField.dedekindZeta K =ᶠ[nhds s]
        fun z => completedDedekindZetaEntire K z
          / (z * (z - 1) * (((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2)
              * gammaFactor K z)) := by
      filter_upwards [hUo.mem_nhds hs] with z hz
      have hz1 : (1:ℝ) < z.re := hz
      have hzpos : 0 < z.re := by linarith
      have hz0' : z ≠ 0 := by
        intro h0
        rw [h0, Complex.zero_re] at hz1
        linarith
      have hz1' : z ≠ 1 := by
        intro h0
        rw [h0, Complex.one_re] at hz1
        linarith
      have hcne : ((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2) ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
        exact Or.inl hdiscrC
      have hγnez : gammaFactor K z ≠ 0 := gammaFactor_ne_zero_of_re_pos K hzpos
      rw [completedDedekindZetaEntire_eq K hz0' hz1',
        completedDedekindZeta_eq_of_one_lt_re K hz1, completedZetaPrefactor]
      field_simp
    rw [hev2.differentiableAt_iff]
    refine DifferentiableAt.div ((differentiable_completedDedekindZetaEntire K) s) ?_ ?_
    · exact (differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
        (hcpow_d.mul hγd)
    · refine mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) ?_
      exact mul_ne_zero hcpow_ne (gammaFactor_ne_zero_of_re_pos K hspos)
  have hγζne : gammaFactor K s * NumberField.dedekindZeta K s ≠ 0 := mul_ne_zero hγne hζne
  have hγζd : DifferentiableAt ℂ
      (fun z => gammaFactor K z * NumberField.dedekindZeta K z) s := hγd.mul hζd
  have hpre_ne : ((|NumberField.discr K| : ℝ) : ℂ) ^ (s/2)
      * (gammaFactor K s * NumberField.dedekindZeta K s) ≠ 0 := by
    refine mul_ne_zero ?_ hγζne
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hdiscrC
  have hpre_d : DifferentiableAt ℂ
      (fun z : ℂ => ((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2)
        * (gammaFactor K z * NumberField.dedekindZeta K z)) s :=
    hcpow_d.mul hγζd
  have hid_ne : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  have hid_d : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1)) s :=
    differentiableAt_id.mul (differentiableAt_id.sub_const 1)
  -- peel the factors
  rw [logDeriv_mul (f := fun z : ℂ => z * (z - 1))
      (g := fun z : ℂ => ((|NumberField.discr K| : ℝ) : ℂ) ^ (z/2)
        * (gammaFactor K z * NumberField.dedekindZeta K z)) s hid_ne hpre_ne hid_d hpre_d]
  rw [logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1) s hs0
      (sub_ne_zero.mpr hs1) differentiableAt_id (differentiableAt_id.sub_const 1)]
  rw [logDeriv_cpow_half_mul (f := fun z : ℂ => gammaFactor K z
      * NumberField.dedekindZeta K z) hdiscrC hγζne hγζd]
  rw [logDeriv_mul (f := gammaFactor K) (g := NumberField.dedekindZeta K) s hγne hζne
      hγd hζd]
  have h1 : logDeriv (fun z : ℂ => z) s = 1/s := by
    rw [logDeriv_apply, deriv_id'']
  have h2 : logDeriv (fun z : ℂ => z - 1) s = 1/(s-1) := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  have h3 : Complex.log (((|NumberField.discr K| : ℝ)) : ℂ)
      = ((Real.log |NumberField.discr K| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hdiscr0.le]
  rw [h1, h2, h3]
  ring

/-- The complex exponential tail integral: for `Re z > 0`,
`∫₀^∞ e^{-zv} dv = 1/z`. -/
theorem integral_cexp_neg_mul_Ioi {z : ℂ} (hz : 0 < z.re) :
    ∫ v in Set.Ioi (0:ℝ), Complex.exp (-(z * (v:ℂ))) = z⁻¹ := by
  have hzne : z ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hz
    exact lt_irrefl _ hz
  have hderiv : ∀ v ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun v : ℝ => -Complex.exp (-(z * (v:ℂ))) / z)
        (Complex.exp (-(z * (v:ℂ)))) v := by
    intro v _
    have h0 : HasDerivAt (fun v : ℝ => ((v:ℝ):ℂ)) 1 v := by
      simpa using (hasDerivAt_id v).ofReal_comp
    have h1 : HasDerivAt (fun v : ℝ => -(z * (v:ℂ))) (-z) v := by
      have h2 := (h0.const_mul z).neg
      have h3 : -(z * (1:ℂ)) = -z := by ring
      rw [h3] at h2
      exact h2
    have h3 := (h1.cexp.neg).div_const z
    have hval : -(Complex.exp (-(z * (v:ℂ))) * -z) / z = Complex.exp (-(z * (v:ℂ))) := by
      rw [div_eq_iff hzne]
      ring
    rw [hval] at h3
    exact h3
  have hint : IntegrableOn (fun v : ℝ => Complex.exp (-(z * (v:ℂ)))) (Set.Ioi 0) := by
    refine Integrable.mono' (g := fun v : ℝ => Real.exp (-(z.re * v))) ?_ ?_ ?_
    · have := exp_neg_integrableOn_Ioi (0:ℝ) hz
      refine this.congr_fun (fun v _ => ?_) measurableSet_Ioi
      show Real.exp (-z.re * v) = Real.exp (-(z.re * v))
      rw [show -z.re * v = -(z.re * v) by ring]
    · refine (Continuous.aestronglyMeasurable ?_).restrict
      exact Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).neg)
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall (fun v _ => ?_))
      rw [Complex.norm_exp]
      rw [show (-(z * (v:ℂ))).re = -(z.re * v) from by
        rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring]
  have htend : Tendsto (fun v : ℝ => -Complex.exp (-(z * (v:ℂ))) / z) atTop (nhds 0) := by
    rw [show (0:ℂ) = -0/z by ring]
    refine Tendsto.div_const (Tendsto.neg ?_) z
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : (fun v : ℝ => ‖Complex.exp (-(z * (v:ℂ)))‖)
        = fun v : ℝ => Real.exp (-(z.re * v)) := by
      funext v
      rw [Complex.norm_exp]
      congr 1
      rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h1]
    have h2 : Tendsto (fun v : ℝ => -(z.re * v)) atTop atBot := by
      refine Filter.tendsto_neg_atBot_iff.mpr ?_
      exact Tendsto.const_mul_atTop hz tendsto_id
    exact Real.tendsto_exp_atBot.comp h2
  have h0 := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [h0]
  rw [show ((0:ℝ):ℂ) = (0:ℂ) from rfl, mul_zero, neg_zero, Complex.exp_zero]
  rw [zero_sub, neg_div, neg_neg, one_div]

/-- The complex exponential head integral: for `Re z > 0`,
`∫_{-∞}^{w} e^{zu} du = e^{zw}/z`. -/
theorem integral_cexp_mul_Iio {z : ℂ} (hz : 0 < z.re) (w : ℝ) :
    ∫ u in Set.Iio w, Complex.exp (z * (u:ℂ)) = Complex.exp (z * (w:ℂ)) / z := by
  -- reflect to the tail integral via u = w - v
  have A : MeasurableEmbedding (fun v : ℝ => w - v) :=
    (Homeomorph.subLeft w).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).restrict (Set.Iio w)
      = Measure.map (fun v : ℝ => w - v) ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    rw [show Set.Ioi (0:ℝ) = (fun v : ℝ => w - v) ⁻¹' (Set.Iio w) by
        ext v
        simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]
        constructor <;> intro h <;> linarith,
      ← Measure.restrict_map A.measurable measurableSet_Iio]
    congr 1
    -- map (w - ·) volume = volume
    have h1 : (fun v : ℝ => w - v) = (fun v : ℝ => w + v) ∘ (fun v : ℝ => -v) := by
      funext v
      simp [sub_eq_add_neg]
    rw [h1, ← Measure.map_map (measurable_const_add w) measurable_neg,
      Measure.map_neg_eq_self, map_add_left_eq_self]
  rw [show (∫ u in Set.Iio w, Complex.exp (z * (u:ℂ)))
      = ∫ u, Complex.exp (z * (u:ℂ)) ∂((volume : Measure ℝ).restrict (Set.Iio w)) from rfl,
    hmap, A.integral_map]
  have h2 : (∫ v in Set.Ioi (0:ℝ), Complex.exp (z * ((w - v : ℝ):ℂ)))
      = ∫ v in Set.Ioi (0:ℝ), Complex.exp (z * (w:ℂ)) * Complex.exp (-(z * (v:ℂ))) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h2, MeasureTheory.integral_const_mul, integral_cexp_neg_mul_Ioi hz,
    div_eq_mul_inv]

/-- Left rays as reflected right rays. -/
theorem restrict_Iio_eq_map_sub (w : ℝ) :
    (volume : Measure ℝ).restrict (Set.Iio w)
      = Measure.map (fun v : ℝ => w - v) ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
  have A : MeasurableEmbedding (fun v : ℝ => w - v) :=
    (Homeomorph.subLeft w).isClosedEmbedding.measurableEmbedding
  rw [show Set.Ioi (0:ℝ) = (fun v : ℝ => w - v) ⁻¹' (Set.Iio w) by
      ext v
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]
      constructor <;> intro h <;> linarith,
    ← Measure.restrict_map A.measurable measurableSet_Iio]
  congr 1
  have h1 : (fun v : ℝ => w - v) = (fun v : ℝ => w + v) ∘ (fun v : ℝ => -v) := by
    funext v
    simp [sub_eq_add_neg]
  rw [h1, ← Measure.map_map (measurable_const_add w) measurable_neg,
    Measure.map_neg_eq_self, map_add_left_eq_self]

/-- `e^{cu}` is integrable on left rays for `c > 0`. -/
theorem integrableOn_exp_mul_Iio {c : ℝ} (hc : 0 < c) (w : ℝ) :
    IntegrableOn (fun u : ℝ => Real.exp (c*u)) (Set.Iio w) := by
  rw [IntegrableOn, restrict_Iio_eq_map_sub w]
  have A : MeasurableEmbedding (fun v : ℝ => w - v) :=
    (Homeomorph.subLeft w).isClosedEmbedding.measurableEmbedding
  rw [A.integrable_map_iff]
  have h0 : IntegrableOn (fun v : ℝ => Real.exp (c*w) * Real.exp (-(c*v)))
      (Set.Ioi 0) := by
    refine Integrable.const_mul ?_ _
    have := exp_neg_integrableOn_Ioi (0:ℝ) hc
    refine this.congr_fun (fun v _ => ?_) measurableSet_Ioi
    show Real.exp (-c * v) = Real.exp (-(c * v))
    rw [show -c * v = -(c*v) by ring]
  refine h0.congr (Filter.Eventually.of_forall (fun v => ?_))
  show Real.exp (c*w) * Real.exp (-(c*v)) = Real.exp (c*(w - v))
  rw [← Real.exp_add]
  congr 1
  ring

/-- `∫_{-∞}^w e^{cu} du = e^{cw}/c` for `c > 0`. -/
theorem integral_exp_mul_Iio {c : ℝ} (hc : 0 < c) (w : ℝ) :
    ∫ u in Set.Iio w, Real.exp (c*u) = Real.exp (c*w)/c := by
  have A : MeasurableEmbedding (fun v : ℝ => w - v) :=
    (Homeomorph.subLeft w).isClosedEmbedding.measurableEmbedding
  rw [show (∫ u in Set.Iio w, Real.exp (c*u))
      = ∫ u, Real.exp (c*u) ∂((volume : Measure ℝ).restrict (Set.Iio w)) from rfl,
    restrict_Iio_eq_map_sub w, A.integral_map]
  have h2 : (∫ v in Set.Ioi (0:ℝ), Real.exp (c * (w - v)))
      = ∫ v in Set.Ioi (0:ℝ), Real.exp (c*w) * Real.exp (-(c*v)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h2, MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi hc]
  ring

variable {c : ℝ} {G : ℝ → ℂ}

/-- **The pole-piece window function** (Poitou's residue terms as a Fourier window):
`E_c(u) = 2 e^{cu} ∫_u^∞ G(w) e^{-cw} dw`. Paired against `e^{itu}` it produces
`2·(∫G e^{itx})/(c+it)`, the `1/s`- and `1/(s-1)`-terms of the edge integrand. -/
noncomputable def poleWindow (c : ℝ) (G : ℝ → ℂ) (u : ℝ) : ℂ :=
  2 * ((Real.exp (c*u) : ℝ) : ℂ)
    * ∫ w in Set.Ioi u, G w * ((Real.exp (-(c*w)) : ℝ) : ℂ)

/-- The tail kernel is integrable on each right ray. -/
theorem integrableOn_poleWindow_kernel (hc : 0 < c) (hG : Integrable G) (u : ℝ) :
    IntegrableOn (fun w : ℝ => G w * ((Real.exp (-(c*w)) : ℝ) : ℂ)) (Set.Ioi u) := by
  refine (hG.restrict).mul_bdd (c := Real.exp (-(c*u))) ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_).restrict
    exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).neg))
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun w hw => ?_))
    rw [Set.mem_Ioi] at hw
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith)

/-- The global tail formula: `∫_{Ioi u} = ∫_{Ioi 0} - ∫_0^u`. -/
theorem tail_integral_eq (hc : 0 < c) (hG : Integrable G) (u : ℝ) :
    (∫ w in Set.Ioi u, G w * ((Real.exp (-(c*w)) : ℝ) : ℂ))
      = (∫ w in Set.Ioi (0:ℝ), G w * ((Real.exp (-(c*w)) : ℝ) : ℂ))
        - ∫ x in (0:ℝ)..u, G x * ((Real.exp (-(c*x)) : ℝ) : ℂ) := by
  set Kf : ℝ → ℂ := fun w => G w * ((Real.exp (-(c*w)) : ℝ) : ℂ) with hKf
  rcases le_or_gt 0 u with hu | hu
  · -- u ≥ 0 : Ioi 0 = Ioc 0 u ∪ Ioi u
    have hsplit : (∫ w in Set.Ioi (0:ℝ), Kf w)
        = (∫ w in Set.Ioc 0 u, Kf w) + ∫ w in Set.Ioi u, Kf w := by
      rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi ((integrableOn_poleWindow_kernel hc hG 0).mono_set
          (fun w hw => hw.1)) (integrableOn_poleWindow_kernel hc hG u),
        Set.Ioc_union_Ioi_eq_Ioi hu]
    rw [intervalIntegral.integral_of_le hu]
    rw [hsplit]
    ring
  · -- u < 0 : Ioi u = Ioc u 0 ∪ Ioi 0
    have hsplit : (∫ w in Set.Ioi u, Kf w)
        = (∫ w in Set.Ioc u 0, Kf w) + ∫ w in Set.Ioi (0:ℝ), Kf w := by
      rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi ((integrableOn_poleWindow_kernel hc hG u).mono_set
          (fun w hw => hw.1)) (integrableOn_poleWindow_kernel hc hG 0),
        Set.Ioc_union_Ioi_eq_Ioi hu.le]
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hu.le]
    rw [hsplit]
    ring

/-- `poleWindow` is continuous. -/
theorem continuous_poleWindow (hc : 0 < c) (hG : Integrable G) :
    Continuous (poleWindow c G) := by
  have hK_ii : ∀ a b : ℝ, IntervalIntegrable
      (fun w : ℝ => G w * ((Real.exp (-(c*w)) : ℝ) : ℂ)) volume a b := by
    intro a b
    rw [intervalIntegrable_iff]
    exact (integrableOn_poleWindow_kernel hc hG (min a b)).mono_set
      (fun w hw => hw.1)
  have hτ : Continuous (fun u : ℝ =>
      ∫ w in Set.Ioi u, G w * ((Real.exp (-(c*w)) : ℝ) : ℂ)) := by
    have h0 : (fun u : ℝ => ∫ w in Set.Ioi u, G w * ((Real.exp (-(c*w)) : ℝ) : ℂ))
        = fun u : ℝ => (∫ w in Set.Ioi (0:ℝ), G w * ((Real.exp (-(c*w)) : ℝ) : ℂ))
          - ∫ x in (0:ℝ)..u, G x * ((Real.exp (-(c*x)) : ℝ) : ℂ) :=
      funext (fun u => tail_integral_eq hc hG u)
    rw [h0]
    exact continuous_const.sub (continuous_primitive hK_ii 0)
  refine Continuous.mul ?_ hτ
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)))

/-- Value at the origin. -/
theorem poleWindow_zero :
    poleWindow c G 0 = 2 * ∫ w in Set.Ioi (0:ℝ), G w * ((Real.exp (-(c*w)) : ℝ) : ℂ) := by
  rw [poleWindow, mul_zero, Real.exp_zero]
  norm_num

/-- The half-plane indicator product function behind `poleWindow` is integrable. -/
theorem integrable_poleWindow_pair (hc : 0 < c) (hG : Integrable G) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ => ({q : ℝ × ℝ | q.1 < q.2}).indicator
      (fun q => (2 * ((Real.exp (c*q.1) : ℝ):ℂ) * Complex.exp ((t*q.1 : ℝ) * Complex.I))
        * (G q.2 * ((Real.exp (-(c*q.2)) : ℝ):ℂ))) p)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hKm : AEStronglyMeasurable (fun w : ℝ => G w * ((Real.exp (-(c*w)) : ℝ):ℂ))
      (volume : Measure ℝ) := by
    refine hG.1.mul ?_
    refine Continuous.aestronglyMeasurable ?_
    exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).neg))
  have hcoeffc : Continuous (fun u : ℝ =>
      2 * ((Real.exp (c*u) : ℝ):ℂ) * Complex.exp ((t*u : ℝ) * Complex.I)) := by
    refine Continuous.mul ?_ ?_
    · exact continuous_const.mul (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
    · exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
          continuous_const)
  have hPmeas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ({q : ℝ × ℝ | q.1 < q.2}).indicator
        (fun q => (2 * ((Real.exp (c*q.1) : ℝ):ℂ)
            * Complex.exp ((t*q.1 : ℝ) * Complex.I))
          * (G q.2 * ((Real.exp (-(c*q.2)) : ℝ):ℂ))) p)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    refine AEStronglyMeasurable.indicator ?_
      (measurableSet_lt measurable_fst measurable_snd)
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hcoeffc.comp continuous_fst).aestronglyMeasurable
    · exact hKm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  refine (MeasureTheory.integrable_prod_iff' hPmeas).mpr ⟨?_, ?_⟩
  · -- u-slices for a.e. w
    refine Filter.Eventually.of_forall (fun w => ?_)
    have hsec : (fun u : ℝ => ({q : ℝ × ℝ | q.1 < q.2}).indicator
        (fun q => (2 * ((Real.exp (c*q.1) : ℝ):ℂ)
            * Complex.exp ((t*q.1 : ℝ) * Complex.I))
          * (G q.2 * ((Real.exp (-(c*q.2)) : ℝ):ℂ))) (u, w))
        = (Set.Iio w).indicator (fun u =>
            (2 * ((Real.exp (c*u) : ℝ):ℂ) * Complex.exp ((t*u : ℝ) * Complex.I))
              * (G w * ((Real.exp (-(c*w)) : ℝ):ℂ))) := by
      funext u
      by_cases h : u < w
      · rw [Set.indicator_of_mem (by exact h : (u, w) ∈ {q : ℝ × ℝ | q.1 < q.2}),
          Set.indicator_of_mem (Set.mem_Iio.mpr h)]
      · rw [Set.indicator_of_notMem (by exact h : (u, w) ∉ {q : ℝ × ℝ | q.1 < q.2}),
          Set.indicator_of_notMem (fun hm => h (Set.mem_Iio.mp hm))]
    rw [hsec]
    rw [integrable_indicator_iff measurableSet_Iio]
    refine Integrable.mul_const ?_ _
    refine Integrable.mono' (g := fun u : ℝ => 2 * Real.exp (c*u))
      (((integrableOn_exp_mul_Iio hc w).const_mul 2)) ?_ ?_
    · exact (hcoeffc.aestronglyMeasurable).restrict
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Iio).mpr
        (Filter.Eventually.of_forall (fun u _ => ?_))
      rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [show ‖(2:ℂ)‖ = 2 by norm_num]
  · -- the norm marginals
    have hval : ∀ w : ℝ, (∫ u : ℝ, ‖({q : ℝ × ℝ | q.1 < q.2}).indicator
        (fun q => (2 * ((Real.exp (c*q.1) : ℝ):ℂ)
            * Complex.exp ((t*q.1 : ℝ) * Complex.I))
          * (G q.2 * ((Real.exp (-(c*q.2)) : ℝ):ℂ))) (u, w)‖)
        = (2/c) * ‖G w‖ := by
      intro w
      have hsec : ∀ u : ℝ, ‖({q : ℝ × ℝ | q.1 < q.2}).indicator
          (fun q => (2 * ((Real.exp (c*q.1) : ℝ):ℂ)
              * Complex.exp ((t*q.1 : ℝ) * Complex.I))
            * (G q.2 * ((Real.exp (-(c*q.2)) : ℝ):ℂ))) (u, w)‖
          = (Set.Iio w).indicator
              (fun u => 2 * Real.exp (c*u) * (‖G w‖ * Real.exp (-(c*w)))) u := by
        intro u
        by_cases h : u < w
        · rw [Set.indicator_of_mem (by exact h : (u, w) ∈ {q : ℝ × ℝ | q.1 < q.2}),
            Set.indicator_of_mem (Set.mem_Iio.mpr h)]
          simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs, Real.abs_exp, Complex.norm_ofNat]
        · rw [Set.indicator_of_notMem (by exact h : (u, w) ∉ {q : ℝ × ℝ | q.1 < q.2}),
            Set.indicator_of_notMem (fun hm => h (Set.mem_Iio.mp hm)), norm_zero]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsec)]
      rw [MeasureTheory.integral_indicator measurableSet_Iio]
      rw [show (fun u : ℝ => 2 * Real.exp (c*u) * (‖G w‖ * Real.exp (-(c*w))))
          = fun u : ℝ => (2 * (‖G w‖ * Real.exp (-(c*w)))) * Real.exp (c*u) from by
        funext u
        ring]
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Iio hc w]
      have hee : Real.exp (-(c*w)) * Real.exp (c*w) = 1 := by
        rw [← Real.exp_add, show -(c*w) + c*w = 0 by ring, Real.exp_zero]
      calc 2 * (‖G w‖ * Real.exp (-(c*w))) * (Real.exp (c*w)/c)
          = (2/c) * ‖G w‖ * (Real.exp (-(c*w)) * Real.exp (c*w)) := by ring
        _ = 2/c * ‖G w‖ := by rw [hee, mul_one]
    refine Integrable.congr ((hG.norm.const_mul (2/c))) ?_
    exact Filter.Eventually.of_forall (fun w => (hval w).symm)

/-- **The fixed-`t` pole-piece identity**: `∫ E_c(u) e^{itu} du = 2·(∫ G e^{itx})/(c+it)`. -/
theorem integral_poleWindow_cexp (hc : 0 < c) (hG : Integrable G) (t : ℝ) :
    ∫ u : ℝ, poleWindow c G u * Complex.exp ((t*u : ℝ) * Complex.I)
      = 2 * (∫ x : ℝ, G x * Complex.exp ((t*x : ℝ) * Complex.I))
          * ((c:ℂ) + (t:ℂ)*Complex.I)⁻¹ := by
  set z : ℂ := (c:ℂ) + (t:ℂ)*Complex.I with hz_def
  have hzre : z.re = c := by
    rw [hz_def]
    simp
  have hzpos : 0 < z.re := by
    rw [hzre]
    exact hc
  set P : ℝ × ℝ → ℂ := fun p => ({q : ℝ × ℝ | q.1 < q.2}).indicator
    (fun q => (2 * ((Real.exp (c*q.1) : ℝ):ℂ) * Complex.exp ((t*q.1 : ℝ) * Complex.I))
      * (G q.2 * ((Real.exp (-(c*q.2)) : ℝ):ℂ))) p with hP_def
  have hprod : Integrable P ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    integrable_poleWindow_pair hc hG t
  -- identify the u-marginal with the left-hand integrand
  have hIdent1 : ∀ u : ℝ, poleWindow c G u * Complex.exp ((t*u : ℝ) * Complex.I)
      = ∫ w : ℝ, P (u, w) := by
    intro u
    have hsec : (fun w : ℝ => P (u, w))
        = (Set.Ioi u).indicator (fun w =>
            (2 * ((Real.exp (c*u) : ℝ):ℂ) * Complex.exp ((t*u : ℝ) * Complex.I))
              * (G w * ((Real.exp (-(c*w)) : ℝ):ℂ))) := by
      funext w
      rw [hP_def]
      beta_reduce
      by_cases h : u < w
      · rw [Set.indicator_of_mem (by exact h : (u, w) ∈ {q : ℝ × ℝ | q.1 < q.2}),
          Set.indicator_of_mem (Set.mem_Ioi.mpr h)]
      · rw [Set.indicator_of_notMem (by exact h : (u, w) ∉ {q : ℝ × ℝ | q.1 < q.2}),
          Set.indicator_of_notMem (fun hm => h (Set.mem_Ioi.mp hm))]
    rw [hsec, MeasureTheory.integral_indicator measurableSet_Ioi,
      MeasureTheory.integral_const_mul, poleWindow]
    ring
  -- identify the w-marginal
  have hIdent2 : ∀ w : ℝ, (∫ u : ℝ, P (u, w))
      = (G w * Complex.exp ((t*w : ℝ) * Complex.I)) * (2 * z⁻¹) := by
    intro w
    have hsec : (fun u : ℝ => P (u, w))
        = (Set.Iio w).indicator (fun u =>
            (2 * ((Real.exp (c*u) : ℝ):ℂ) * Complex.exp ((t*u : ℝ) * Complex.I))
              * (G w * ((Real.exp (-(c*w)) : ℝ):ℂ))) := by
      funext u
      rw [hP_def]
      beta_reduce
      by_cases h : u < w
      · rw [Set.indicator_of_mem (by exact h : (u, w) ∈ {q : ℝ × ℝ | q.1 < q.2}),
          Set.indicator_of_mem (Set.mem_Iio.mpr h)]
      · rw [Set.indicator_of_notMem (by exact h : (u, w) ∉ {q : ℝ × ℝ | q.1 < q.2}),
          Set.indicator_of_notMem (fun hm => h (Set.mem_Iio.mp hm))]
    rw [hsec, MeasureTheory.integral_indicator measurableSet_Iio]
    have hpt : ∀ u : ℝ, (2 * ((Real.exp (c*u) : ℝ):ℂ)
        * Complex.exp ((t*u : ℝ) * Complex.I))
          * (G w * ((Real.exp (-(c*w)) : ℝ):ℂ))
        = (2 * (G w * ((Real.exp (-(c*w)) : ℝ):ℂ))) * Complex.exp (z * (u:ℂ)) := by
      intro u
      have hexp : Complex.exp (z * (u:ℂ))
          = ((Real.exp (c*u) : ℝ):ℂ) * Complex.exp ((t*u : ℝ) * Complex.I) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        rw [hz_def]
        push_cast
        ring
      rw [hexp]
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iio (fun u _ => hpt u),
      MeasureTheory.integral_const_mul, integral_cexp_mul_Iio hzpos w]
    have hcollapse : ((Real.exp (-(c*w)) : ℝ):ℂ) * Complex.exp (z * (w:ℂ))
        = Complex.exp ((t*w : ℝ) * Complex.I) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      rw [hz_def]
      push_cast
      ring
    linear_combination (2 * G w / z) * hcollapse
  -- swap and conclude
  have hswap := MeasureTheory.integral_integral_swap
    (f := fun u w : ℝ => P (u, w)) (by exact hprod)
  calc ∫ u : ℝ, poleWindow c G u * Complex.exp ((t*u : ℝ) * Complex.I)
      = ∫ u : ℝ, ∫ w : ℝ, P (u, w) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hIdent1)
    _ = ∫ w : ℝ, ∫ u : ℝ, P (u, w) := hswap
    _ = ∫ w : ℝ, (G w * Complex.exp ((t*w : ℝ) * Complex.I)) * (2 * z⁻¹) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hIdent2)
    _ = (∫ w : ℝ, G w * Complex.exp ((t*w : ℝ) * Complex.I)) * (2 * z⁻¹) :=
        MeasureTheory.integral_mul_const _ _
    _ = 2 * (∫ x : ℝ, G x * Complex.exp ((t*x : ℝ) * Complex.I)) * z⁻¹ := by
        ring

/-- `poleWindow` is integrable. -/
theorem integrable_poleWindow (hc : 0 < c) (hG : Integrable G) :
    Integrable (poleWindow c G) (volume : Measure ℝ) := by
  have h0 := (integrable_poleWindow_pair hc hG 0).integral_prod_left
  refine h0.congr (Filter.Eventually.of_forall (fun u => ?_))
  have h1 : poleWindow c G u * Complex.exp ((0*u : ℝ) * Complex.I) = poleWindow c G u := by
    rw [show ((0*u : ℝ) : ℂ) = 0 by push_cast; ring, zero_mul, Complex.exp_zero, mul_one]
  calc (∫ w : ℝ, ({q : ℝ × ℝ | q.1 < q.2}).indicator
        (fun q => (2 * ((Real.exp (c*q.1) : ℝ):ℂ)
            * Complex.exp ((0*q.1 : ℝ) * Complex.I))
          * (G q.2 * ((Real.exp (-(c*q.2)) : ℝ):ℂ))) (u, w))
      = poleWindow c G u * Complex.exp ((0*u : ℝ) * Complex.I) := by
        have h2 : ∀ w : ℝ, ({q : ℝ × ℝ | q.1 < q.2}).indicator
            (fun q => (2 * ((Real.exp (c*q.1) : ℝ):ℂ)
                * Complex.exp ((0*q.1 : ℝ) * Complex.I))
              * (G q.2 * ((Real.exp (-(c*q.2)) : ℝ):ℂ))) (u, w)
            = (Set.Ioi u).indicator (fun w =>
                (2 * ((Real.exp (c*u) : ℝ):ℂ)
                  * Complex.exp ((0*u : ℝ) * Complex.I))
                  * (G w * ((Real.exp (-(c*w)) : ℝ):ℂ))) w := by
          intro w
          by_cases h : u < w
          · rw [Set.indicator_of_mem (by exact h : (u, w) ∈ {q : ℝ × ℝ | q.1 < q.2}),
              Set.indicator_of_mem (Set.mem_Ioi.mpr h)]
          · rw [Set.indicator_of_notMem (by exact h : (u, w) ∉ {q : ℝ × ℝ | q.1 < q.2}),
              Set.indicator_of_notMem (fun hm => h (Set.mem_Ioi.mp hm))]
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h2),
          MeasureTheory.integral_indicator measurableSet_Ioi,
          MeasureTheory.integral_const_mul, poleWindow]
        ring
    _ = poleWindow c G u := h1

variable {a : ℝ} {F : ℝ → ℂ}

/-- `Φ` on the edge `Re s = 1+a` is the Fourier integral of the weighted function. -/
theorem paperPhi_edge (a : ℝ) (F : ℝ → ℂ) (t : ℝ) :
    paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
      = ∫ x : ℝ, (F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ))
          * Complex.exp ((t*x : ℝ) * Complex.I) := by
  rw [paperPhi]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show F x * Complex.exp (((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1/2) * x)
      = F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ) * Complex.exp ((t*x : ℝ) * Complex.I)
  rw [show ((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1/2) * x
      = (((1/2+a) * x : ℝ) : ℂ) + ((t*x : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  rw [Complex.exp_add, Complex.ofReal_exp]
  ring

/-- The weighted function `F(x)e^{bx}`, `|b| ≤ 1/2`, is integrable for even `F`
with `F·e^{(1/2+a)x} ∈ L¹`. -/
theorem integrable_F_mul_exp_half (ha : 0 < a) (hF : Integrable F)
    (hFeven : ∀ x : ℝ, F (-x) = F x)
    (hFa : Integrable (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)))
    {b : ℝ} (hb : |b| ≤ 1/2) :
    Integrable (fun x : ℝ => F x * ((Real.exp (b * x) : ℝ) : ℂ)) := by
  have hGneg : Integrable (fun x : ℝ =>
      ‖F (-x) * ((Real.exp ((1/2+a) * (-x)) : ℝ) : ℂ)‖) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable
      hFa.norm
  refine Integrable.mono'
    (g := fun x => ‖F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)‖
      + ‖F (-x) * ((Real.exp ((1/2+a) * (-x)) : ℝ) : ℂ)‖)
    (hFa.norm.add hGneg) ?_ ?_
  · refine hF.1.mul ?_
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      Complex.norm_real, Real.norm_eq_abs, Real.abs_exp, hFeven x]
    rcases le_or_gt 0 x with hx | hx
    · have h1 : Real.exp (b*x) ≤ Real.exp ((1/2+a)*x) := by
        refine Real.exp_le_exp.mpr ?_
        have hble : b ≤ 1/2 := le_trans (le_abs_self b) hb
        nlinarith
      nlinarith [norm_nonneg (F x), Real.exp_pos ((1/2+a)*(-x)),
        mul_nonneg (norm_nonneg (F x)) (Real.exp_pos ((1/2+a)*(-x))).le]
    · have h1 : Real.exp (b*x) ≤ Real.exp ((1/2+a)*(-x)) := by
        refine Real.exp_le_exp.mpr ?_
        have hble : -b ≤ 1/2 := le_trans (neg_le_abs b) hb
        nlinarith
      nlinarith [norm_nonneg (F x), Real.exp_pos ((1/2+a)*x),
        mul_nonneg (norm_nonneg (F x)) (Real.exp_pos ((1/2+a)*x)).le]

/-- **The value identification** (Poitou p. 6-07, Remarque): for even `F`,
`E_a(0) + E_{1+a}(0) = Φ(0) + Φ(1)`. -/
theorem poleWindow_zero_add_eq (ha : 0 < a) (hF : Integrable F)
    (hFeven : ∀ x : ℝ, F (-x) = F x)
    (hFa : Integrable (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ))) :
    poleWindow a (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) 0
        + poleWindow (1+a) (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) 0
      = paperPhi F 0 + paperPhi F 1 := by
  -- the two tail kernels collapse
  have hker1 : ∀ w : ℝ, (F w * ((Real.exp ((1/2+a) * w) : ℝ) : ℂ))
      * ((Real.exp (-(a*w)) : ℝ) : ℂ) = F w * ((Real.exp ((1/2) * w) : ℝ) : ℂ) := by
    intro w
    rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  have hker2 : ∀ w : ℝ, (F w * ((Real.exp ((1/2+a) * w) : ℝ) : ℂ))
      * ((Real.exp (-((1+a)*w)) : ℝ) : ℂ) = F w * ((Real.exp (-(1/2) * w) : ℝ) : ℂ) := by
    intro w
    rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  -- Φ-values as weighted integrals
  have hΦ1 : paperPhi F 1 = ∫ x : ℝ, F x * ((Real.exp ((1/2) * x) : ℝ) : ℂ) := by
    rw [paperPhi]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show F x * Complex.exp (((1:ℂ) - 1/2) * x) = F x * ((Real.exp ((1/2) * x) : ℝ) : ℂ)
    rw [show ((1:ℂ) - 1/2) * x = (((1/2) * x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
  have hΦ0 : paperPhi F 0 = ∫ x : ℝ, F x * ((Real.exp (-(1/2) * x) : ℝ) : ℂ) := by
    rw [paperPhi]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show F x * Complex.exp (((0:ℂ) - 1/2) * x) = F x * ((Real.exp (-(1/2) * x) : ℝ) : ℂ)
    rw [show ((0:ℂ) - 1/2) * x = ((-(1/2) * x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp]
  -- fold the full-line integrals onto the half line
  have hfold : ∀ b : ℝ, |b| ≤ 1/2 →
      (∫ x : ℝ, F x * ((Real.exp (b * x) : ℝ) : ℂ))
        = (∫ w in Set.Ioi (0:ℝ), F w * ((Real.exp (b * w) : ℝ) : ℂ))
          + ∫ w in Set.Ioi (0:ℝ), F w * ((Real.exp (-b * w) : ℝ) : ℂ) := by
    intro b hb
    have hint := integrable_F_mul_exp_half ha hF hFeven hFa hb
    have hsplit := (MeasureTheory.integral_add_compl (measurableSet_Iio (a := (0:ℝ)))
      hint).symm
    have hcomplIio : (Set.Iio (0:ℝ))ᶜ = Set.Ici (0:ℝ) := by
      ext x
      simp
    rw [hcomplIio] at hsplit
    have hIci : (∫ x in Set.Ici (0:ℝ), F x * ((Real.exp (b * x) : ℝ) : ℂ))
        = ∫ x in Set.Ioi (0:ℝ), F x * ((Real.exp (b * x) : ℝ) : ℂ) :=
      (MeasureTheory.setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0:ℝ)))).symm
    have A : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    have hmap : (volume : Measure ℝ).restrict (Set.Iio (0:ℝ))
        = Measure.map (fun x : ℝ => -x) ((volume : Measure ℝ).restrict (Set.Ioi (0:ℝ))) := by
      rw [show Set.Ioi (0:ℝ) = (fun x : ℝ => -x) ⁻¹' (Set.Iio 0) by ext x; simp,
        ← Measure.restrict_map A.measurable measurableSet_Iio,
        Measure.map_neg_eq_self (volume : Measure ℝ)]
    have hIio : (∫ x in Set.Iio (0:ℝ), F x * ((Real.exp (b * x) : ℝ) : ℂ))
        = ∫ w in Set.Ioi (0:ℝ), F w * ((Real.exp (-b * w) : ℝ) : ℂ) := by
      rw [show (∫ x in Set.Iio (0:ℝ), F x * ((Real.exp (b * x) : ℝ) : ℂ))
          = ∫ x, F x * ((Real.exp (b * x) : ℝ) : ℂ)
              ∂((volume : Measure ℝ).restrict (Set.Iio 0)) from rfl,
        hmap, A.integral_map]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
      show F (-w) * ((Real.exp (b * -w) : ℝ) : ℂ) = F w * ((Real.exp (-b * w) : ℝ) : ℂ)
      rw [hFeven w, show b * -w = -b * w by ring]
    rw [hsplit, hIci, hIio]
    ring
  rw [poleWindow_zero, poleWindow_zero,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun w _ => hker1 w),
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun w _ => hker2 w),
    hΦ0, hΦ1, hfold (1/2) (by rw [abs_of_pos]; norm_num),
    hfold (-(1/2)) (by rw [abs_neg, abs_of_pos]; norm_num)]
  rw [show -(-(1/2)) = (1/2 : ℝ) by ring]
  ring

/-- **The pole-piece limit** (Poitou p. 6-01/6-07): the `1/s + 1/(s-1)` part of the
edge integral converges to `2π(Φ(0) + Φ(1))`. -/
theorem tendsto_pole_piece (ha : 0 < a) (hF : Integrable F)
    (hFeven : ∀ x : ℝ, F (-x) = F x)
    (hFa : Integrable (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)))
    (hEre : LocallyBoundedVariationOn (fun u : ℝ =>
      ((poleWindow a (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u
        + poleWindow (1+a) (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u)).re)
      Set.univ)
    (hEim : LocallyBoundedVariationOn (fun u : ℝ =>
      ((poleWindow a (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u
        + poleWindow (1+a) (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u)).im)
      Set.univ) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
        (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
          * (1/(((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
            + 1/((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1)))
      atTop (nhds (((2*π : ℝ):ℂ) * (paperPhi F 0 + paperPhi F 1))) := by
  set G : ℝ → ℂ := fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ) with hG_def
  set E : ℝ → ℂ := fun u => poleWindow a G u + poleWindow (1+a) G u with hE_def
  have h1a : (0:ℝ) < 1+a := by linarith
  have hEint : Integrable E :=
    (integrable_poleWindow ha hFa).add (integrable_poleWindow h1a hFa)
  have hEcont : Continuous E :=
    (continuous_poleWindow ha hFa).add (continuous_poleWindow h1a hFa)
  have hEp : Tendsto E (nhdsWithin 0 (Set.Ioi 0)) (nhds (E 0)) :=
    (hEcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hEm : Tendsto E (nhdsWithin 0 (Set.Iio 0)) (nhds (E 0)) :=
    (hEcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hW := tendsto_fourier_window_jordan hEint hEre hEim hEp hEm
  -- fixed-T function identity
  have hfun : ∀ T : ℝ, (∫ t in (-T)..T,
      (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
        + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
        * (1/(((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + 1/((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1)))
      = ∫ t in (-T)..T, ∫ u : ℝ, E u * Complex.exp ((t:ℂ)*(u:ℂ)*Complex.I) := by
    intro T
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [paperPhi_one_sub hFeven]
    -- the E-integral splits into the two pole windows
    have hpc : ∀ c : ℝ, 0 < c → Integrable (fun u : ℝ =>
        poleWindow c G u * Complex.exp ((t*u : ℝ) * Complex.I)) := by
      intro c hc
      refine (integrable_poleWindow hc hFa).mul_bdd (c := 1) ?_ ?_
      · refine Continuous.aestronglyMeasurable ?_
        exact Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
            continuous_const)
      · refine Filter.Eventually.of_forall (fun u => ?_)
        rw [Complex.norm_exp_ofReal_mul_I]
    have hsplit : (∫ u : ℝ, E u * Complex.exp ((t*u : ℝ) * Complex.I))
        = (∫ u : ℝ, poleWindow a G u * Complex.exp ((t*u : ℝ) * Complex.I))
          + ∫ u : ℝ, poleWindow (1+a) G u * Complex.exp ((t*u : ℝ) * Complex.I) := by
      rw [← MeasureTheory.integral_add (hpc a ha) (hpc (1+a) h1a)]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      show E u * Complex.exp ((t*u : ℝ) * Complex.I) = _
      rw [hE_def]
      ring
    have hcast1 : ((a:ℝ):ℂ) + (t:ℂ)*Complex.I
        = (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1 := by
      push_cast
      ring
    have hcast2 : (((1+a:ℝ)):ℂ) + (t:ℂ)*Complex.I
        = ((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I := rfl
    have hkey : (2 * paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
        * (1/(((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + 1/((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1))
        = ∫ u : ℝ, E u * Complex.exp ((t*u : ℝ) * Complex.I) := by
      have hφG : paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          = ∫ x : ℝ, G x * Complex.exp ((t*x : ℝ) * Complex.I) := paperPhi_edge a F t
      rw [hsplit, integral_poleWindow_cexp ha hFa t, integral_poleWindow_cexp h1a hFa t,
        hφG, hcast1, one_div, one_div]
      ring
    calc (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
          * (1/(((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
            + 1/((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1))
        = (2 * paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
          * (1/(((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
            + 1/((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1)) := by ring
      _ = ∫ u : ℝ, E u * Complex.exp ((t*u : ℝ) * Complex.I) := hkey
      _ = ∫ u : ℝ, E u * Complex.exp ((t:ℂ)*(u:ℂ)*Complex.I) := by
          refine MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun u => ?_))
          show E u * Complex.exp (((t*u : ℝ):ℂ) * Complex.I)
              = E u * Complex.exp ((t:ℂ)*(u:ℂ)*Complex.I)
          rw [Complex.ofReal_mul]
  refine Tendsto.congr (fun T => (hfun T).symm) ?_
  have hlim : ((π : ℝ):ℂ) * (E 0 + E 0) = ((2*π : ℝ):ℂ) * (paperPhi F 0 + paperPhi F 1) := by
    have h0 : E 0 = paperPhi F 0 + paperPhi F 1 := by
      rw [hE_def]
      exact poleWindow_zero_add_eq ha hF hFeven hFa
    rw [h0]
    push_cast
    ring
  rw [← hlim]
  exact hW

/-- **The discriminant piece**: the constant `(1/2)log|d|` against the paired window
converges to `2π F(0)·log|d|` (after the two edges double it). Stated for a general
real constant `κ`: `lim ∫ (Φ(s)+Φ(1-s))·κ dt = 4π κ F(0)`. -/
theorem tendsto_const_piece (hFeven : ∀ x : ℝ, F (-x) = F x)
    (hFa : Integrable (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)))
    (hGre : LocallyBoundedVariationOn (fun x : ℝ =>
      ((F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ))).re) Set.univ)
    (hGim : LocallyBoundedVariationOn (fun x : ℝ =>
      ((F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ))).im) Set.univ)
    {Fp Fm : ℂ}
    (hFp : Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds Fp))
    (hFm : Tendsto F (nhdsWithin 0 (Set.Iio 0)) (nhds Fm))
    (κ : ℝ) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
        (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))) * ((κ : ℝ) : ℂ))
      atTop (nhds (((2*π : ℝ):ℂ) * ((κ : ℝ) : ℂ) * (Fp + Fm))) := by
  set G : ℝ → ℂ := fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ) with hG_def
  -- one-sided limits of G at 0 are those of F
  have hGlim : ∀ (l : Filter ℝ) (L : ℂ), l ≤ nhds 0 → Tendsto F l (nhds L) →
      Tendsto G l (nhds L) := by
    intro l L hl hFl
    have hexp : Tendsto (fun x : ℝ => ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) l (nhds 1) := by
      have h0 : Continuous (fun x : ℝ => ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp (Real.continuous_exp.comp
          (continuous_const.mul continuous_id))
      have h1 := (h0.tendsto 0).mono_left hl
      rw [show ((Real.exp ((1/2+a) * 0) : ℝ) : ℂ) = 1 by norm_num] at h1
      exact h1
    have h2 := hFl.mul hexp
    rw [mul_one] at h2
    exact h2
  have hGp : Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds Fp) :=
    hGlim _ _ nhdsWithin_le_nhds hFp
  have hGm : Tendsto G (nhdsWithin 0 (Set.Iio 0)) (nhds Fm) :=
    hGlim _ _ nhdsWithin_le_nhds hFm
  have hW := tendsto_fourier_window_jordan hFa hGre hGim hGp hGm
  -- fixed-T identity
  have hfun : ∀ T : ℝ, (∫ t in (-T)..T,
      (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
        + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))) * ((κ : ℝ) : ℂ))
      = 2 * ((κ : ℝ) : ℂ) * ∫ t in (-T)..T,
          ∫ u : ℝ, G u * Complex.exp ((t:ℂ)*(u:ℂ)*Complex.I) := by
    intro T
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [paperPhi_one_sub hFeven]
    have hφG : paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
        = ∫ x : ℝ, G x * Complex.exp ((t*x : ℝ) * Complex.I) := paperPhi_edge a F t
    rw [hφG]
    have hcongr : (∫ x : ℝ, G x * Complex.exp ((t*x : ℝ) * Complex.I))
        = ∫ u : ℝ, G u * Complex.exp ((t:ℂ)*(u:ℂ)*Complex.I) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      show G u * Complex.exp (((t*u : ℝ):ℂ) * Complex.I)
          = G u * Complex.exp ((t:ℂ)*(u:ℂ)*Complex.I)
      rw [Complex.ofReal_mul]
    rw [hcongr]
    ring
  refine Tendsto.congr (fun T => (hfun T).symm) ?_
  have h9 := hW.const_mul (2 * ((κ : ℝ) : ℂ))
  have hlim : 2 * ((κ : ℝ) : ℂ) * (((π : ℝ) : ℂ) * (Fp + Fm))
      = ((2*π : ℝ):ℂ) * ((κ : ℝ) : ℂ) * (Fp + Fm) := by
    push_cast
    ring
  rw [hlim] at h9
  exact h9

/-- `Φ` on the critical line is the Fourier integral, in the window normal form. -/
theorem paperPhi_half_line (F : ℝ → ℂ) (y : ℝ) :
    paperPhi F (((1/2 : ℝ):ℂ) + (y:ℂ)*Complex.I)
      = ∫ x : ℝ, F x * Complex.exp ((y*x : ℝ) * Complex.I) := by
  have h0 : (((1/2 : ℝ):ℂ) + (y:ℂ)*Complex.I) = 1/2 + (y:ℂ)*Complex.I := by
    push_cast
    ring
  rw [h0, paperPhi_half_add_mul_I, paperFourierIntegral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  push_cast
  ring_nf

/-- **The Γ-edge limit** (Poitou p. 6-03, "Calcul de la partie archimédienne"):
shift to the critical line, fold to the real part, and evaluate by `I_G`. -/
theorem tendsto_gamma_edge (ha : 0 < a) (ha' : a ≤ 1/4)
    (hF : Integrable F)
    (hre : LocallyBoundedVariationOn (fun u : ℝ => (F u).re) Set.univ)
    (him : LocallyBoundedVariationOn (fun u : ℝ => (F u).im) Set.univ)
    (hF0 : Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds (F 0)))
    (hFeven : ∀ x : ℝ, F (-x) = F x)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ))
    (htop2 : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/2) x : ℝ) : ℂ)) t * gammaFT F t) atTop (nhds 0))
    (hbot2 : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/2) x : ℝ) : ℂ)) t * gammaFT F t) atBot (nhds 0))
    (htop4 : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/4) x : ℝ) : ℂ)) t
        * gammaFT (fun x : ℝ => F (x/2) / 2) t) atTop (nhds 0))
    (hbot4 : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/4) x : ℝ) : ℂ)) t
        * gammaFT (fun x : ℝ => F (x/2) / 2) t) atBot (nhds 0))
    (hΦd : Differentiable ℂ (paperPhi F))
    {B : ℝ → ℝ}
    (hB : ∀ σ t : ℝ, -a ≤ σ → σ ≤ 1+a →
      ‖paperPhi F ((σ:ℂ) + (t:ℂ)*Complex.I)‖ ≤ B |t|)
    (hBlog : Tendsto (fun T : ℝ => B T * Real.log (2+T)) atTop (nhds 0)) :
    Tendsto (fun T : ℝ => ∫ y in (-T)..T,
        (paperPhi F (((1+a : ℝ):ℂ) + (y:ℂ)*Complex.I)
          + paperPhi F (1 - (((1+a : ℝ):ℂ) + (y:ℂ)*Complex.I)))
          * logDeriv (gammaFactor K) (((1+a : ℝ):ℂ) + (y:ℂ)*Complex.I))
      atTop (nhds (((2*π : ℝ) : ℂ) *
        ((((-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
              + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
                * (Real.eulerMascheroniConstant + Real.log (8*π))
              + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)) : ℝ)) : ℂ) * F 0
          + (((NumberField.InfinitePlace.nrRealPlaces K
              + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ)
              * (∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
          + ((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ)
              * ∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (F 0 - F y)))) := by
  -- the vertical integrals over ±T can be shifted to the critical line
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_norm_logDeriv_gammaFactor_le K
  have hgb : ∀ σ t : ℝ, 1/2 ≤ σ → σ ≤ 1+a → 4 ≤ |t| →
      ‖logDeriv (gammaFactor K) ((σ:ℂ) + (t:ℂ)*Complex.I)‖
        ≤ (fun r : ℝ => C₀ * Real.log (2+r)) |t| := by
    intro σ t h1 h2 h3
    exact hC₀ σ t (by linarith) (by linarith) h3
  have hlim' : Tendsto (fun T : ℝ => B T * ((fun r : ℝ => C₀ * Real.log (2+r)) T))
      atTop (nhds 0) := by
    have h0 := hBlog.const_mul C₀
    rw [mul_zero] at h0
    refine h0.congr (fun T => ?_)
    show C₀ * (B T * Real.log (2+T)) = B T * (C₀ * Real.log (2+T))
    ring
  have hshift := tendsto_shift_vertical_sub ha hΦd
    (fun s hs => differentiableAt_logDeriv_gammaFactor K hs) hB hgb hlim'
  -- the critical-line integral is the I_G integrand
  have hIG := tendsto_IG_gammaFactor K hF hre him hF0 hFeven hFdiv hFdiv2
    htop2 hbot2 htop4 hbot4
  have hhalf : Tendsto (fun T : ℝ => ∫ y in (-T)..T,
      (paperPhi F (((1/2 : ℝ):ℂ) + (y:ℂ)*Complex.I)
        + paperPhi F (1 - (((1/2 : ℝ):ℂ) + (y:ℂ)*Complex.I)))
        * logDeriv (gammaFactor K) (((1/2 : ℝ):ℂ) + (y:ℂ)*Complex.I))
      atTop (nhds (((2*π : ℝ) : ℂ) *
        ((((-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
              + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
                * (Real.eulerMascheroniConstant + Real.log (8*π))
              + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)) : ℝ)) : ℂ) * F 0
          + (((NumberField.InfinitePlace.nrRealPlaces K
              + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ)
              * (∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
          + ((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ)
              * ∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (F 0 - F y)))) := by
    refine hIG.congr (fun T => ?_)
    rw [← integral_half_line_fold K hF hFeven (fun y => paperPhi_half_line F y) T]
  -- assemble: edge = (edge - half) + half
  have hcomb := hshift.add hhalf
  rw [zero_add] at hcomb
  refine hcomb.congr (fun T => ?_)
  ring

/-- Continuity in `t` of `Λ_ent'/Λ_ent(1+a+it)`. -/
theorem continuous_logDeriv_completedDedekindZetaEntire_edge (ha : 0 < a) :
    Continuous (fun t : ℝ =>
      logDeriv (completedDedekindZetaEntire K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)) := by
  have han : AnalyticOnNhd ℂ (completedDedekindZetaEntire K) Set.univ :=
    (differentiable_completedDedekindZetaEntire K).differentiableOn.analyticOnNhd
      isOpen_univ
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  have hs : 1 < ((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)).re := by
    rw [show ((((1+a : ℝ)):ℂ) + (t:ℂ)*Complex.I).re = 1+a from by simp]
    linarith
  refine ContinuousAt.comp ?_
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt)
  have hd : ContinuousAt (deriv (completedDedekindZetaEntire K))
      (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) :=
    ((han _ (Set.mem_univ _)).deriv).differentiableAt.continuousAt
  have hv : ContinuousAt (completedDedekindZetaEntire K)
      (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) :=
    (differentiable_completedDedekindZetaEntire K).continuous.continuousAt
  have hne : completedDedekindZetaEntire K (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) ≠ 0 :=
    completedDedekindZetaEntire_ne_zero_of_one_lt_re K hs
  exact ContinuousAt.div hd hv hne

/-- Continuity in `t` of `γ_K'/γ_K(1+a+it)`. -/
theorem continuous_logDeriv_gammaFactor_edge (ha : 0 < a) :
    Continuous (fun t : ℝ =>
      logDeriv (gammaFactor K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)) := by
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  refine ContinuousAt.comp ?_
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt)
  refine (differentiableAt_logDeriv_gammaFactor K ?_).continuousAt
  rw [show ((((1+a : ℝ)):ℂ) + (t:ℂ)*Complex.I).re = 1+a from by simp]
  linarith

/-- **The full edge-integral limit** — all four pieces of
`∫ (Φ(s)+Φ(1-s))·Λ_ent'/Λ_ent(s)` on `Re s = 1+a` converge (Poitou (1) → (6)). -/
theorem tendsto_edge_integral (ha : 0 < a) (ha' : a ≤ 1/4)
    (hF : Integrable F)
    (hre : LocallyBoundedVariationOn (fun u : ℝ => (F u).re) Set.univ)
    (him : LocallyBoundedVariationOn (fun u : ℝ => (F u).im) Set.univ)
    (hF0 : Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds (F 0)))
    (hFeven : ∀ x : ℝ, F (-x) = F x)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    (hFdiv2 : MemLp (fun x : ℝ => (F 0 - F x)/(x:ℂ)) 2 (volume : Measure ℝ))
    (htop2 : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/2) x : ℝ) : ℂ)) t * gammaFT F t) atTop (nhds 0))
    (hbot2 : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/2) x : ℝ) : ℂ)) t * gammaFT F t) atBot (nhds 0))
    (htop4 : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/4) x : ℝ) : ℂ)) t
        * gammaFT (fun x : ℝ => F (x/2) / 2) t) atTop (nhds 0))
    (hbot4 : Tendsto (fun t : ℝ =>
      rhoFT (fun x => ((poitouKernel (1/4) x : ℝ) : ℂ)) t
        * gammaFT (fun x : ℝ => F (x/2) / 2) t) atBot (nhds 0))
    (hΦd : Differentiable ℂ (paperPhi F))
    {B : ℝ → ℝ}
    (hB : ∀ σ t : ℝ, -a ≤ σ → σ ≤ 1+a →
      ‖paperPhi F ((σ:ℂ) + (t:ℂ)*Complex.I)‖ ≤ B |t|)
    (hBlog : Tendsto (fun T : ℝ => B T * Real.log (2+T)) atTop (nhds 0))
    (hFa : Integrable (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)))
    (hGre : LocallyBoundedVariationOn (fun x : ℝ =>
      ((F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ))).re) Set.univ)
    (hGim : LocallyBoundedVariationOn (fun x : ℝ =>
      ((F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ))).im) Set.univ)
    (hEre : LocallyBoundedVariationOn (fun u : ℝ =>
      ((poleWindow a (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u
        + poleWindow (1+a) (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u)).re)
      Set.univ)
    (hEim : LocallyBoundedVariationOn (fun u : ℝ =>
      ((poleWindow a (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u
        + poleWindow (1+a) (fun x : ℝ => F x * ((Real.exp ((1/2+a) * x) : ℝ) : ℂ)) u)).im)
      Set.univ)
    (hHre : LocallyBoundedVariationOn (fun u : ℝ => (primeSideH K a F u).re) Set.univ)
    (hHim : LocallyBoundedVariationOn (fun u : ℝ => (primeSideH K a F u).im) Set.univ)
    {Hp Hm : ℂ}
    (hHp : Tendsto (primeSideH K a F) (nhdsWithin 0 (Set.Ioi 0)) (nhds Hp))
    (hHm : Tendsto (primeSideH K a F) (nhdsWithin 0 (Set.Iio 0)) (nhds Hm)) :
    Tendsto (fun T : ℝ => ∫ t in (-T)..T,
        (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
          * logDeriv (completedDedekindZetaEntire K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
      atTop (nhds
        (((2*π : ℝ):ℂ) * (paperPhi F 0 + paperPhi F 1)
          + ((2*π : ℝ):ℂ) * ((Real.log |NumberField.discr K| / 2 : ℝ) : ℂ) * (F 0 + F 0)
          + ((2*π : ℝ) : ℂ) *
            ((((-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
                + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
                  * (Real.eulerMascheroniConstant + Real.log (8*π))
                + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)) : ℝ)) : ℂ) * F 0
            + (((NumberField.InfinitePlace.nrRealPlaces K
                + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ)
                * (∫ y in Set.Ioi (0:ℝ),
                  ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
            + ((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ)
                * ∫ y in Set.Ioi (0:ℝ),
                  ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
          - 2 * ((π : ℝ) : ℂ) * (Hp + Hm))) := by
  -- the left one-sided limit of F from evenness
  have hmneg : Tendsto (fun x : ℝ => -x) (nhdsWithin 0 (Set.Iio 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h2 := (continuous_neg.tendsto (0:ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio 0))
      rw [neg_zero] at h2
      exact h2
    · filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Set.mem_Iio] at hx
      exact Set.mem_Ioi.mpr (by linarith)
  have hFm : Tendsto F (nhdsWithin 0 (Set.Iio 0)) (nhds (F 0)) :=
    (hF0.comp hmneg).congr (fun x => hFeven x)
  -- the four piece limits
  have hpole := tendsto_pole_piece ha hF hFeven hFa hEre hEim
  have hdisc := tendsto_const_piece hFeven hFa hGre hGim hF0 hFm
    (Real.log |NumberField.discr K| / 2)
  have hγ := tendsto_gamma_edge K ha ha' hF hre him hF0 hFeven hFdiv hFdiv2
    htop2 hbot2 htop4 hbot4 hΦd hB hBlog
  have hζ := (tendsto_prime_side K ha hFeven hFa hHre hHim hHp hHm).neg
  -- continuity facts for the fixed-T splitting
  have hΦc : Continuous (fun t : ℝ => paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)) := by
    refine (continuous_muFT hFa).congr (fun t => ?_)
    exact (paperPhi_edge a F t).symm
  have hΦpairc : Continuous (fun t : ℝ =>
      paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
        + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))) := by
    refine (hΦc.add hΦc).congr (fun t => ?_)
    show paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
        + paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
      = paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
        + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
    rw [paperPhi_one_sub hFeven]
  have hs_ne : ∀ t : ℝ, (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) ≠ 0 := by
    intro t h0
    have h1 := congrArg Complex.re h0
    rw [show ((((1+a : ℝ)):ℂ) + (t:ℂ)*Complex.I).re = 1+a from by simp,
      Complex.zero_re] at h1
    linarith
  have hs1_ne : ∀ t : ℝ, (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1 ≠ 0 := by
    intro t h0
    have h1 := congrArg Complex.re h0
    rw [Complex.sub_re, Complex.one_re,
      show ((((1+a : ℝ)):ℂ) + (t:ℂ)*Complex.I).re = 1+a from by simp,
      Complex.zero_re] at h1
    linarith
  have hsc : Continuous (fun t : ℝ => (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hpolec : Continuous (fun t : ℝ =>
      1/(((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
        + 1/((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1)) :=
    (continuous_const.div hsc hs_ne).add
      (continuous_const.div (hsc.sub continuous_const) hs1_ne)
  have hγc := continuous_logDeriv_gammaFactor_edge K ha
  have hΛc := continuous_logDeriv_completedDedekindZetaEntire_edge K ha
  -- fixed-T splitting into the four pieces
  have hfun : ∀ T : ℝ, (∫ t in (-T)..T,
      (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
        + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
        * logDeriv (completedDedekindZetaEntire K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
      = (∫ t in (-T)..T,
          (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
            + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
            * (1/(((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
              + 1/((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1)))
        + ((∫ t in (-T)..T,
            (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
              + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
              * ((Real.log |NumberField.discr K| / 2 : ℝ) : ℂ))
          + ((∫ y in (-T)..T,
              (paperPhi F (((1+a : ℝ):ℂ) + (y:ℂ)*Complex.I)
                + paperPhi F (1 - (((1+a : ℝ):ℂ) + (y:ℂ)*Complex.I)))
                * logDeriv (gammaFactor K) (((1+a : ℝ):ℂ) + (y:ℂ)*Complex.I))
            + -(∫ t in (-T)..T,
              (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
                + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
                * (-(logDeriv (NumberField.dedekindZeta K)
                    (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))))) := by
    intro T
    have ii1 : IntervalIntegrable (fun t : ℝ =>
        (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
          * (1/(((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
            + 1/((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1)))
        MeasureTheory.volume (-T) T := (hΦpairc.mul hpolec).intervalIntegrable _ _
    have ii2 : IntervalIntegrable (fun t : ℝ =>
        (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
          * ((Real.log |NumberField.discr K| / 2 : ℝ) : ℂ))
        MeasureTheory.volume (-T) T := (hΦpairc.mul continuous_const).intervalIntegrable _ _
    have ii3 : IntervalIntegrable (fun t : ℝ =>
        (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
          * logDeriv (gammaFactor K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
        MeasureTheory.volume (-T) T := (hΦpairc.mul hγc).intervalIntegrable _ _
    have ii4 : IntervalIntegrable (fun t : ℝ =>
        (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
          * logDeriv (NumberField.dedekindZeta K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
        MeasureTheory.volume (-T) T := by
      have hfull : IntervalIntegrable (fun t : ℝ =>
          (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
            + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
            * logDeriv (completedDedekindZetaEntire K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
          MeasureTheory.volume (-T) T := (hΦpairc.mul hΛc).intervalIntegrable _ _
      have hζeq : (fun t : ℝ =>
          (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
            + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
            * logDeriv (NumberField.dedekindZeta K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
          = fun t : ℝ =>
            ((paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
              + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
              * logDeriv (completedDedekindZetaEntire K)
                  (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
            - (((paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
              + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
              * (1/(((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
                + 1/((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1)))
              + (((paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
                + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
                * ((Real.log |NumberField.discr K| / 2 : ℝ) : ℂ))
                + ((paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
                  + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
                  * logDeriv (gammaFactor K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))) := by
        funext t
        have hsre : 1 < ((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)).re := by
          rw [show ((((1+a : ℝ)):ℂ) + (t:ℂ)*Complex.I).re = 1+a from by simp]
          linarith
        have hsplit := logDeriv_completedDedekindZetaEntire_split K hsre
        rw [hsplit]
        rw [show (((Real.log |NumberField.discr K| : ℝ) : ℂ))/2
            = ((Real.log |NumberField.discr K| / 2 : ℝ) : ℂ) by push_cast; ring]
        ring
      rw [hζeq]
      exact (hfull.sub (ii1.add (ii2.add ii3)))
    -- pointwise split of the full integrand
    have hpt : ∀ t : ℝ,
        (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
          * logDeriv (completedDedekindZetaEntire K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
        = (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
            + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
            * (1/(((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
              + 1/((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I) - 1))
          + ((paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
              + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
              * ((Real.log |NumberField.discr K| / 2 : ℝ) : ℂ)
            + ((paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
                + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
                * logDeriv (gammaFactor K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
              + (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
                + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
                * logDeriv (NumberField.dedekindZeta K)
                    (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))) := by
      intro t
      have hsre : 1 < ((((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)).re := by
        rw [show ((((1+a : ℝ)):ℂ) + (t:ℂ)*Complex.I).re = 1+a from by simp]
        linarith
      rw [logDeriv_completedDedekindZetaEntire_split K hsre]
      rw [show (((Real.log |NumberField.discr K| : ℝ) : ℂ))/2
          = ((Real.log |NumberField.discr K| / 2 : ℝ) : ℂ) by push_cast; ring]
      ring
    have h4 : (∫ t in (-T)..T,
        (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
          + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
          * logDeriv (NumberField.dedekindZeta K) (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I))
        = -(∫ t in (-T)..T,
          (paperPhi F (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)
            + paperPhi F (1 - (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))
            * (-(logDeriv (NumberField.dedekindZeta K)
                (((1+a : ℝ):ℂ) + (t:ℂ)*Complex.I)))) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      ring
    rw [intervalIntegral.integral_congr (fun t _ => hpt t),
      intervalIntegral.integral_add ii1 (ii2.add (ii3.add ii4)),
      intervalIntegral.integral_add ii2 (ii3.add ii4),
      intervalIntegral.integral_add ii3 ii4, h4]
  refine Tendsto.congr (fun T => (hfun T).symm) ?_
  have hfinal := hpole.add (hdisc.add (hγ.add hζ))
  convert hfinal using 2
  ring

end DedekindResidue
