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

end DedekindResidue
