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
public import DedekindResidue.ExplicitFormula.AuxAdmissible

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

/-- **Weil's explicit formula** (Poitou's (6), Théorème p. 6-06/6-07): there is a
sequence of contour heights `T n → ∞` along which the zero-capture sums of
`Φ` over the zeros of `Λ_K` in `(-a, 1+a) × (-T n, T n)` converge, with limit

`Φ(0) + Φ(1) + log|d|·F(0) + I_G-terms − (H(0+) + H(0-))`,

the right side of formula (6) before the prime-side unfolding of `H(0±)`. -/
theorem weil_explicit_formula (ha : 0 < a) (ha' : a ≤ 1/4)
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
    (hBlog2 : Tendsto (fun T : ℝ => B T * (Real.log (2+T))^2) atTop (nhds 0))
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
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      Tendsto (fun n : ℕ => ∑ᶠ ρ, (((MeromorphicOn.divisor (completedDedekindZetaEntire K)
          (Set.Ioo (-a) (1+a) ×ℂ Set.Ioo (-(T n)) (T n))) ρ : ℂ)) * paperPhi F ρ)
        atTop (nhds
          ((paperPhi F 0 + paperPhi F 1)
            + ((Real.log |NumberField.discr K| : ℝ) : ℂ) * F 0
            + (((-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
                + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
                  * (Real.eulerMascheroniConstant + Real.log (8*π))
                + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)) : ℝ)) : ℂ) * F 0
            + (((NumberField.InfinitePlace.nrRealPlaces K
                + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ)
                * (∫ y in Set.Ioi (0:ℝ),
                  ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
            + ((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ)
                * (∫ y in Set.Ioi (0:ℝ),
                  ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
            - (Hp + Hm))) := by
  -- weaker single-log decay for the Γ-shift
  have hBnn : ∀ᶠ T in atTop, 0 ≤ B T := by
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with T hT
    have h0 := hB (1/2) T (by linarith) (by linarith)
    rw [abs_of_nonneg hT] at h0
    exact le_trans (norm_nonneg _) h0
  have hlog1 : ∀ᶠ T in atTop, (1:ℝ) ≤ Real.log (2+T) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with T hT
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2+T) := Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hBlog : Tendsto (fun T : ℝ => B T * Real.log (2+T)) atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hBlog2
    · filter_upwards [hBnn, hlog1] with T h1 h2
      exact mul_nonneg h1 (by linarith)
    · filter_upwards [hBnn, hlog1] with T h1 h2
      have h3 : Real.log (2+T) ≤ (Real.log (2+T))^2 := by nlinarith
      exact mul_le_mul_of_nonneg_left h3 h1
  have hedge := tendsto_edge_integral K ha ha' hF hre him hF0 hFeven hFdiv hFdiv2
    htop2 hbot2 htop4 hbot4 hΦd hB hBlog hFa hGre hGim hEre hEim hHre hHim hHp hHm
  -- good heights
  obtain ⟨A, hA2, c, C, hc, hc1, hC, hgood⟩ := exists_contour_height K
  have hchoice : ∀ n : ℕ, ∃ T ∈ Set.Icc (A + 5 + n) (A + 5 + n + 1),
      (∀ ρ : ℂ, completedDedekindZetaEntire K ρ = 0 →
        c / Real.log (2 + (A + 5 + n)) ≤ |T - ρ.im|
          ∧ c / Real.log (2 + (A + 5 + n)) ≤ |T + ρ.im|)
      ∧ (∀ σ : ℝ, -(1/4) ≤ σ → σ ≤ 5/4 →
          completedDedekindZetaEntire K ((σ:ℂ) + (T:ℂ) * Complex.I) ≠ 0
          ∧ ‖logDeriv (completedDedekindZetaEntire K) ((σ:ℂ) + (T:ℂ) * Complex.I)‖
            ≤ C * (Real.log (2 + (A + 5 + n)))^2)
      ∧ ∀ σ : ℝ, -(1/4) ≤ σ → σ ≤ 5/4 →
          completedDedekindZetaEntire K ((σ:ℂ) + ((-T:ℝ):ℂ) * Complex.I) ≠ 0
          ∧ ‖logDeriv (completedDedekindZetaEntire K) ((σ:ℂ) + ((-T:ℝ):ℂ) * Complex.I)‖
            ≤ C * (Real.log (2 + (A + 5 + n)))^2 := by
    intro n
    have h0 : A + 5 ≤ A + 5 + n := by
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact hgood (A + 5 + n) h0
  choose T hTmem hTsep hTtop hTbot using hchoice
  have hTge : ∀ n : ℕ, A + 5 + n ≤ T n := fun n => (hTmem n).1
  have hTtend : Tendsto T atTop atTop := by
    refine tendsto_atTop_atTop.mpr (fun b => ?_)
    obtain ⟨n₀, hn₀⟩ := exists_nat_ge (b - A - 5)
    refine ⟨n₀, fun n hn => ?_⟩
    have h1 := hTge n
    have h2 : (n₀ : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith
  have hTpos : ∀ n : ℕ, 0 < T n := by
    intro n
    have h0 := hTge n
    have h1 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  refine ⟨T, hTtend, ?_⟩
  -- the zero-capture bound at each good height
  have hcap : ∀ n : ℕ, ‖2 * Real.pi * Complex.I
      * (∑ᶠ ρ, (((MeromorphicOn.divisor (completedDedekindZetaEntire K)
          (Set.Ioo (-a) (1+a) ×ℂ Set.Ioo (-(T n)) (T n))) ρ : ℂ)) * paperPhi F ρ)
      - Complex.I • ∫ y : ℝ in (-(T n))..(T n),
          (paperPhi F (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)
            + paperPhi F (1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)))
            * logDeriv (completedDedekindZetaEntire K)
                (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)‖
      ≤ 2 * (1 + 2*a) * (B (T n) * (C * (Real.log (2 + (A + 5 + n)))^2)) := by
    intro n
    refine zero_capture_edge_form K ha ha' (hTpos n)
      (fun ζ _ => hΦd.differentiableAt) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro σ h1 h2
      exact (hTtop n σ (by linarith) (by linarith)).1
    · intro σ h1 h2
      exact (hTbot n σ (by linarith) (by linarith)).1
    · -- 0 ≤ CΦ
      have h0 := hB (1/2) (T n) (by linarith) (by linarith)
      rw [abs_of_pos (hTpos n)] at h0
      exact le_trans (norm_nonneg _) h0
    · intro x hx
      rw [Set.uIcc_of_le (by linarith : -a ≤ 1+a), Set.mem_Icc] at hx
      have h0 := hB x (T n) hx.1 hx.2
      rw [abs_of_pos (hTpos n)] at h0
      exact h0
    · intro x hx
      rw [Set.uIcc_of_le (by linarith : -a ≤ 1+a), Set.mem_Icc] at hx
      have h0 := hB x (-(T n)) hx.1 hx.2
      rw [abs_neg, abs_of_pos (hTpos n)] at h0
      exact h0
    · intro x hx
      rw [Set.uIcc_of_le (by linarith : -a ≤ 1+a), Set.mem_Icc] at hx
      exact (hTtop n x (by linarith [hx.1]) (by linarith [hx.2])).2
    · intro x hx
      rw [Set.uIcc_of_le (by linarith : -a ≤ 1+a), Set.mem_Icc] at hx
      exact (hTbot n x (by linarith [hx.1]) (by linarith [hx.2])).2
  -- the error tends to zero
  have herr : Tendsto (fun n : ℕ =>
      2 * (1 + 2*a) * (B (T n) * (C * (Real.log (2 + (A + 5 + n)))^2))) atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => B (T n) * (Real.log (2 + T n))^2) atTop (nhds 0) :=
      hBlog2.comp hTtend
    have h1 : Tendsto (fun n : ℕ =>
        2 * (1 + 2*a) * C * (B (T n) * (Real.log (2 + T n))^2)) atTop (nhds 0) := by
      have h2 := h0.const_mul (2 * (1 + 2*a) * C)
      rw [mul_zero] at h2
      exact h2
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [] with n
    have hBnn' : 0 ≤ B (T n) := by
      have h0' := hB (1/2) (T n) (by linarith) (by linarith)
      rw [abs_of_pos (hTpos n)] at h0'
      exact le_trans (norm_nonneg _) h0'
    have hAn : (0:ℝ) ≤ A + 5 + n := by
      have h9 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hlogle : Real.log (2 + (A + 5 + n)) ≤ Real.log (2 + T n) :=
      Real.log_le_log (by linarith) (by linarith [hTge n])
    have hlognn : 0 ≤ Real.log (2 + (A + 5 + n)) :=
      Real.log_nonneg (by linarith)
    have hsq : (Real.log (2 + (A + 5 + n)))^2 ≤ (Real.log (2 + T n))^2 := by nlinarith
    have h4 : B (T n) * (Real.log (2 + (A + 5 + n)))^2
        ≤ B (T n) * (Real.log (2 + T n))^2 := mul_le_mul_of_nonneg_left hsq hBnn'
    have hval_nn : 0 ≤ 2 * (1 + 2*a) * (B (T n) * (C * (Real.log (2 + (A + 5 + n)))^2)) :=
      mul_le_mul_of_nonneg_left (mul_nonneg hBnn' (mul_nonneg hC.le (sq_nonneg _)))
        (by linarith) |>.trans_eq' (by ring)
    rw [Real.norm_eq_abs, abs_of_nonneg hval_nn]
    calc 2 * (1 + 2*a) * (B (T n) * (C * (Real.log (2 + (A + 5 + n)))^2))
        = 2 * (1 + 2*a) * (C * (B (T n) * (Real.log (2 + (A + 5 + n)))^2)) := by ring
      _ ≤ 2 * (1 + 2*a) * (C * (B (T n) * (Real.log (2 + T n))^2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact mul_le_mul_of_nonneg_left h4 hC.le
      _ = 2 * (1 + 2*a) * C * (B (T n) * (Real.log (2 + T n))^2) := by ring
  -- 2πi S_n − i E_n → 0
  have hdiff : Tendsto (fun n : ℕ => 2 * Real.pi * Complex.I
      * (∑ᶠ ρ, (((MeromorphicOn.divisor (completedDedekindZetaEntire K)
          (Set.Ioo (-a) (1+a) ×ℂ Set.Ioo (-(T n)) (T n))) ρ : ℂ)) * paperPhi F ρ)
      - Complex.I • ∫ y : ℝ in (-(T n))..(T n),
          (paperPhi F (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)
            + paperPhi F (1 - (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)))
            * logDeriv (completedDedekindZetaEntire K)
                (((1+a:ℝ):ℂ) + (y:ℂ) * Complex.I)) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ herr
    filter_upwards [] with n
    exact hcap n
  -- hence 2πi S_n → i · L
  have hSn : Tendsto (fun n : ℕ => 2 * Real.pi * Complex.I
      * (∑ᶠ ρ, (((MeromorphicOn.divisor (completedDedekindZetaEntire K)
          (Set.Ioo (-a) (1+a) ×ℂ Set.Ioo (-(T n)) (T n))) ρ : ℂ)) * paperPhi F ρ))
      atTop (nhds (0 + Complex.I • (((2*π : ℝ):ℂ) * (paperPhi F 0 + paperPhi F 1)
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
        - 2 * ((π : ℝ) : ℂ) * (Hp + Hm)))) := by
    have h0 := hdiff.add ((hedge.comp hTtend).const_smul Complex.I)
    refine h0.congr (fun n => ?_)
    exact sub_add_cancel _ _
  -- divide by 2πi
  have h2πi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hfin := hSn.const_mul ((2 * Real.pi * Complex.I : ℂ))⁻¹
  have hlim_eq : ((2 * Real.pi * Complex.I : ℂ))⁻¹ * (0 + Complex.I • (((2*π : ℝ):ℂ)
        * (paperPhi F 0 + paperPhi F 1)
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
      - 2 * ((π : ℝ) : ℂ) * (Hp + Hm)))
      = ((paperPhi F 0 + paperPhi F 1)
        + ((Real.log |NumberField.discr K| : ℝ) : ℂ) * F 0
        + (((-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
            + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
              * (Real.eulerMascheroniConstant + Real.log (8*π))
            + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)) : ℝ)) : ℂ) * F 0
        + (((NumberField.InfinitePlace.nrRealPlaces K
            + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ)
            * (∫ y in Set.Ioi (0:ℝ),
              ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
        + ((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ)
            * (∫ y in Set.Ioi (0:ℝ),
              ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (F 0 - F y))
        - (Hp + Hm)) := by
    rw [zero_add, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ h2πi]
    push_cast
    ring
  rw [hlim_eq] at hfin
  refine hfin.congr (fun n => ?_)
  rw [← mul_assoc, inv_mul_cancel₀ h2πi, one_mul]

/-- **Quadratic Fourier decay of the auxiliary function** (readable from the
Belabas–Friedman closed form, Lemma 2 eq. (8)): `‖F̂_{s,X}(γ)‖ = O(1/γ²)`. -/
theorem exists_norm_fourier_auxF_le (s : ℂ) {X : ℝ} (hX : 1 < X) (hs : 1/2 < s.re) :
    ∃ C γ₀ : ℝ, 0 < C ∧ 1 ≤ γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ |γ| →
      ‖paperFourierIntegral (auxF s X) γ‖ ≤ C / γ^2 := by
  set h : ℂ := s - 1/2 with hh_def
  have hhre : 0 < h.re := by
    rw [hh_def, show (s - 1/2 : ℂ).re = s.re - 1/2 by simp [Complex.sub_re]]
    linarith
  have hT0 : 0 < Real.log X := Real.log_pos hX
  -- the tail-integral constant
  set K₀ : ℝ := ‖h‖/Real.log X + 1/(Real.log X)^2 with hK₀_def
  set M : ℝ := ∫ t in Set.Ioi (Real.log X),
    K₀ * (Real.exp ((s.re - 1/2) * Real.log X) * Real.exp (-(s.re - 1/2) * t)) with hM_def
  have hmaj_int : IntegrableOn (fun t : ℝ =>
      K₀ * (Real.exp ((s.re - 1/2) * Real.log X) * Real.exp (-(s.re - 1/2) * t)))
      (Set.Ioi (Real.log X)) := by
    refine Integrable.const_mul (Integrable.const_mul ?_ _) _
    exact exp_neg_integrableOn_Ioi _ (by linarith)
  have hMnn : 0 ≤ M := by
    rw [hM_def]
    refine MeasureTheory.integral_nonneg (fun t => ?_)
    have hK₀nn : 0 ≤ K₀ := by
      rw [hK₀_def]
      positivity
    positivity
  -- the tail integral in the closed form is bounded by M, for every γ
  have htail_bound : ∀ γ : ℝ, ‖∫ t in Set.Ioi (Real.log X),
      ((Real.cos (t * γ) : ℝ) : ℂ) * auxF s X t * ((h*t + 1)/(t:ℂ)^2)‖ ≤ M := by
    intro γ
    refine le_trans (norm_integral_le_integral_norm _) ?_
    rw [hM_def]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hmaj_int ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun t ht => ?_))
    rw [Set.mem_Ioi] at ht
    have ht0 : 0 < t := lt_trans hT0 ht
    show ‖((Real.cos (t * γ) : ℝ) : ℂ) * auxF s X t * ((h*t + 1)/(t:ℂ)^2)‖
        ≤ K₀ * (Real.exp ((s.re - 1/2) * Real.log X) * Real.exp (-(s.re - 1/2) * t))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb1 : |Real.cos (t * γ)| ≤ 1 := Real.abs_cos_le_one _
    have hb2 : ‖auxF s X t‖ ≤ Real.exp ((s.re - 1/2) * Real.log X)
        * Real.exp (-(s.re - 1/2) * t) := by
      have h0 := norm_auxF_le s hX.le hs.le t
      rw [abs_of_pos ht0] at h0
      exact h0
    have hb3 : ‖(h*(t:ℂ) + 1)/(t:ℂ)^2‖ ≤ K₀ := by
      rw [norm_div]
      have hden : ‖((t:ℂ))^2‖ = t^2 := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      rw [hden, div_le_iff₀ (by positivity)]
      have hnum : ‖h*(t:ℂ) + 1‖ ≤ ‖h‖*t + 1 := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, norm_one]
      refine le_trans hnum ?_
      rw [hK₀_def]
      have e2 : t ≤ t^2/Real.log X := by
        rw [le_div_iff₀ hT0]
        nlinarith
      have e3 : (1:ℝ) ≤ t^2/(Real.log X)^2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have e4 : ‖h‖ * t ≤ ‖h‖ * (t^2/Real.log X) :=
        mul_le_mul_of_nonneg_left e2 (norm_nonneg h)
      have e5 : (‖h‖/Real.log X + 1/(Real.log X)^2) * t^2
          = ‖h‖ * (t^2/Real.log X) + t^2/(Real.log X)^2 := by
        ring
      rw [e5]
      have e6 : (1:ℝ) * 1 ≤ t^2/(Real.log X)^2 := by
        rw [one_mul]
        exact e3
      linarith
    calc |Real.cos (t * γ)| * ‖auxF s X t‖ * ‖(h*(t:ℂ) + 1)/(t:ℂ)^2‖
        ≤ 1 * (Real.exp ((s.re - 1/2) * Real.log X)
            * Real.exp (-(s.re - 1/2) * t)) * K₀ := by
          have hK₀nn : 0 ≤ K₀ := by
            rw [hK₀_def]
            positivity
          refine mul_le_mul (mul_le_mul hb1 hb2 (norm_nonneg _) (by norm_num)) hb3
            (norm_nonneg _) (by positivity)
      _ = K₀ * (Real.exp ((s.re - 1/2) * Real.log X) * Real.exp (-(s.re - 1/2) * t)) := by
          ring
  -- the denominator lower bound
  set γ₀ : ℝ := 1 + Real.sqrt 2 * ‖h‖ with hγ₀_def
  have hγ₀1 : 1 ≤ γ₀ := by
    rw [hγ₀_def]
    have h1 : 0 ≤ Real.sqrt 2 * ‖h‖ := by positivity
    linarith
  refine ⟨4*‖h‖^2 + 4*‖h + 1/((Real.log X : ℝ):ℂ)‖ + 8*M + 1, γ₀, ?_, hγ₀1,
    fun γ hγ => ?_⟩
  · have hn1 := sq_nonneg ‖h‖
    have hn2 := norm_nonneg (h + 1/((Real.log X : ℝ):ℂ))
    linarith
  have hγ1 : 1 ≤ |γ| := le_trans hγ₀1 hγ
  have hγne : γ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hγ1
    linarith
  have hγ2 : (0:ℝ) < γ^2 := by positivity
  have hd : γ^2/2 ≤ ‖h^2 + ((γ:ℝ):ℂ)^2‖ := by
    have h1 : Real.sqrt 2 * ‖h‖ ≤ |γ| := by
      rw [hγ₀_def] at hγ
      linarith
    have h2 : 2 * ‖h‖^2 ≤ γ^2 := by
      have h3 : (Real.sqrt 2 * ‖h‖)^2 ≤ |γ|^2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h3
      rw [← sq_abs γ]
      linarith
    have h4 : (h^2 + ((γ:ℝ):ℂ)^2).re ≤ ‖h^2 + ((γ:ℝ):ℂ)^2‖ := Complex.re_le_norm _
    have h5 : (h^2 + ((γ:ℝ):ℂ)^2).re = (h^2).re + γ^2 := by
      rw [Complex.add_re, show (((γ:ℝ):ℂ))^2 = (((γ^2 : ℝ)):ℂ) by push_cast; ring,
        Complex.ofReal_re]
    have h6 : -(‖h‖^2) ≤ (h^2).re := by
      have h7 := Complex.abs_re_le_norm (h^2)
      rw [norm_pow] at h7
      have h10 := abs_le.mp h7
      linarith [h10.1]
    linarith
  -- the generic division bound
  have hkey : ∀ z : ℂ, ‖z / (h^2 + ((γ:ℝ):ℂ)^2)‖ ≤ ‖z‖ * (2/γ^2) := by
    intro z
    rw [norm_div]
    have hdpos : 0 < ‖h^2 + ((γ:ℝ):ℂ)^2‖ := lt_of_lt_of_le (by positivity) hd
    rw [div_le_iff₀ hdpos]
    have h1 : 1 ≤ (2/γ^2) * ‖h^2 + ((γ:ℝ):ℂ)^2‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hγ2]
      linarith
    nlinarith [norm_nonneg z]
  rw [fourier_auxF s hX hs hγne]
  -- rewrite the three terms as single divisions
  have e1 : 2 * h^2 / ((h^2 + ((γ:ℝ):ℂ)^2) * γ)
        * ((Real.sin (Real.log X * γ) : ℝ) : ℂ)
      = (2 * h^2 * ((Real.sin (Real.log X * γ) : ℝ) : ℂ) / γ)
          / (h^2 + ((γ:ℝ):ℂ)^2) := by
    rw [div_mul_eq_mul_div, div_mul_eq_div_div_swap]
  have e2 : 2 * (h + 1/((Real.log X : ℝ):ℂ)) / (h^2 + ((γ:ℝ):ℂ)^2)
        * ((Real.cos (Real.log X * γ) : ℝ) : ℂ)
      = (2 * (h + 1/((Real.log X : ℝ):ℂ)) * ((Real.cos (Real.log X * γ) : ℝ) : ℂ))
          / (h^2 + ((γ:ℝ):ℂ)^2) := by
    rw [div_mul_eq_mul_div]
  have e3 : 4 / (h^2 + ((γ:ℝ):ℂ)^2) * (∫ t in Set.Ioi (Real.log X),
        ((Real.cos (t * γ) : ℝ) : ℂ) * auxF s X t * ((h*t + 1)/(t:ℂ)^2))
      = (4 * ∫ t in Set.Ioi (Real.log X),
          ((Real.cos (t * γ) : ℝ) : ℂ) * auxF s X t * ((h*t + 1)/(t:ℂ)^2))
          / (h^2 + ((γ:ℝ):ℂ)^2) := by
    rw [div_mul_eq_mul_div]
  rw [e1, e2, e3]
  -- numerator bounds
  have n1 : ‖2 * h^2 * ((Real.sin (Real.log X * γ) : ℝ) : ℂ) / γ‖ ≤ 2*‖h‖^2 := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, show ‖(2:ℂ)‖ = 2 by norm_num]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < |γ|)]
    have hs1 : |Real.sin (Real.log X * γ)| ≤ 1 := Real.abs_sin_le_one _
    nlinarith [norm_nonneg h, sq_nonneg ‖h‖, abs_nonneg (Real.sin (Real.log X * γ))]
  have n2 : ‖2 * (h + 1/((Real.log X : ℝ):ℂ)) * ((Real.cos (Real.log X * γ) : ℝ) : ℂ)‖
      ≤ 2*‖h + 1/((Real.log X : ℝ):ℂ)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show ‖(2:ℂ)‖ = 2 by norm_num]
    have hc1 : |Real.cos (Real.log X * γ)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [norm_nonneg (h + 1/((Real.log X : ℝ):ℂ))]
  have n3 : ‖4 * ∫ t in Set.Ioi (Real.log X),
      ((Real.cos (t * γ) : ℝ) : ℂ) * auxF s X t * ((h*t + 1)/(t:ℂ)^2)‖ ≤ 4*M := by
    rw [norm_mul, show ‖(4:ℂ)‖ = 4 by norm_num]
    have := htail_bound γ
    linarith
  -- assemble
  calc ‖(2 * h^2 * ((Real.sin (Real.log X * γ) : ℝ) : ℂ) / γ) / (h^2 + ((γ:ℝ):ℂ)^2)
        + (2 * (h + 1/((Real.log X : ℝ):ℂ)) * ((Real.cos (Real.log X * γ) : ℝ) : ℂ))
            / (h^2 + ((γ:ℝ):ℂ)^2)
        - (4 * ∫ t in Set.Ioi (Real.log X),
            ((Real.cos (t * γ) : ℝ) : ℂ) * auxF s X t * ((h*t + 1)/(t:ℂ)^2))
            / (h^2 + ((γ:ℝ):ℂ)^2)‖
      ≤ ‖(2 * h^2 * ((Real.sin (Real.log X * γ) : ℝ) : ℂ) / γ) / (h^2 + ((γ:ℝ):ℂ)^2)‖
        + ‖(2 * (h + 1/((Real.log X : ℝ):ℂ)) * ((Real.cos (Real.log X * γ) : ℝ) : ℂ))
            / (h^2 + ((γ:ℝ):ℂ)^2)‖
        + ‖(4 * ∫ t in Set.Ioi (Real.log X),
            ((Real.cos (t * γ) : ℝ) : ℂ) * auxF s X t * ((h*t + 1)/(t:ℂ)^2))
            / (h^2 + ((γ:ℝ):ℂ)^2)‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        have := norm_add_le
          ((2 * h^2 * ((Real.sin (Real.log X * γ) : ℝ) : ℂ) / γ) / (h^2 + ((γ:ℝ):ℂ)^2))
          ((2 * (h + 1/((Real.log X : ℝ):ℂ)) * ((Real.cos (Real.log X * γ) : ℝ) : ℂ))
            / (h^2 + ((γ:ℝ):ℂ)^2))
        linarith
    _ ≤ (2*‖h‖^2) * (2/γ^2) + (2*‖h + 1/((Real.log X : ℝ):ℂ)‖) * (2/γ^2)
        + (4*M) * (2/γ^2) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact le_trans (hkey _) (mul_le_mul_of_nonneg_right n1 (by positivity))
        · exact le_trans (hkey _) (mul_le_mul_of_nonneg_right n2 (by positivity))
        · exact le_trans (hkey _) (mul_le_mul_of_nonneg_right n3 (by positivity))
    _ ≤ (4*‖h‖^2 + 4*‖h + 1/((Real.log X : ℝ):ℂ)‖ + 8*M + 1) / γ^2 := by
        have hfin : (2*‖h‖^2)*(2/γ^2) + (2*‖h + 1/((Real.log X : ℝ):ℂ)‖)*(2/γ^2)
            + (4*M)*(2/γ^2)
            = (4*‖h‖^2 + 4*‖h + 1/((Real.log X : ℝ):ℂ)‖ + 8*M)/γ^2 := by
          field_simp
          ring
        rw [hfin, div_le_div_iff_of_pos_right hγ2]
        linarith

/-- Set-restricted Riemann–Lebesgue, `e^{+ixt}` kernel, `t → +∞`. -/
theorem tendsto_setIntegral_mul_cexp_atTop (q : ℝ → ℂ) (s : Set ℝ)
    (hs : MeasurableSet s) :
    Tendsto (fun t : ℝ => ∫ x in s, q x * Complex.exp ((t*x : ℝ) * Complex.I))
      atTop (nhds 0) := by
  have h0 := tendsto_integral_mul_cexp_pos_atTop (s.indicator q)
  refine h0.congr (fun t => ?_)
  rw [← MeasureTheory.integral_indicator hs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show s.indicator q x * Complex.exp ((x:ℂ) * (t:ℂ) * Complex.I)
      = s.indicator (fun x => q x * Complex.exp ((t*x : ℝ) * Complex.I)) x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    congr 1
    push_cast
    ring_nf
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

/-- Set-restricted Riemann–Lebesgue, `e^{+ixt}` kernel, `t → -∞`. -/
theorem tendsto_setIntegral_mul_cexp_atBot (q : ℝ → ℂ) (s : Set ℝ)
    (hs : MeasurableSet s) :
    Tendsto (fun t : ℝ => ∫ x in s, q x * Complex.exp ((t*x : ℝ) * Complex.I))
      atBot (nhds 0) := by
  have h0 := tendsto_integral_mul_cexp_neg_atTop (s.indicator q)
  have h2 := h0.comp tendsto_neg_atBot_atTop
  refine h2.congr (fun t => ?_)
  simp only [Function.comp_apply]
  rw [← MeasureTheory.integral_indicator hs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show s.indicator q x * Complex.exp (-((x:ℂ) * ((-t:ℝ):ℂ)) * Complex.I)
      = s.indicator (fun x => q x * Complex.exp ((t*x : ℝ) * Complex.I)) x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    congr 1
    push_cast
    ring_nf
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

/-- The plateau piece of `gammaFT` vanishes at `±∞`. -/
theorem tendsto_gammaFT_plateau (F : ℝ → ℂ) (l : Filter ℝ)
    (habs : Tendsto (fun t : ℝ => |t|) l atTop) :
    Tendsto (fun t : ℝ =>
      F 0 * (2 * Complex.I * ((Real.sign t * sincTail (|t|) : ℝ) : ℂ))) l (nhds 0) := by
  have h1 : Tendsto (fun t : ℝ => sincTail (|t|)) l (nhds 0) :=
    tendsto_sincTail_atTop.comp habs
  have h2 : Tendsto (fun t : ℝ => 2 * ‖F 0‖ * |sincTail (|t|)|) l (nhds 0) := by
    have h3 := (h1.abs).const_mul (2 * ‖F 0‖)
    rw [abs_zero, mul_zero] at h3
    exact h3
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [] with t
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, show ‖(2:ℂ)‖ = 2 by norm_num]
  have hsign : |Real.sign t| ≤ 1 := by
    rcases lt_trichotomy t 0 with h | h | h
    · rw [Real.sign_of_neg h]
      norm_num
    · rw [h, Real.sign_zero]
      norm_num
    · rw [Real.sign_of_pos h]
      norm_num
  have hnn := abs_nonneg (sincTail (|t|))
  have hstep : |Real.sign t| * |sincTail (|t|)| ≤ |sincTail (|t|)| := by
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hstep (norm_nonneg (F 0)), norm_nonneg (F 0)]

/-- **Poitou's `γ` vanishes at `+∞`** — unconditionally: Riemann–Lebesgue on both
integral pieces, `sincTail → 0` on the plateau piece. -/
theorem tendsto_gammaFT_atTop (F : ℝ → ℂ) :
    Tendsto (gammaFT F) atTop (nhds 0) := by
  have hW := tendsto_setIntegral_mul_cexp_atTop (fun x : ℝ => (F 0 - F x)/(x:ℂ))
    (Set.Ioc (-1) 1) measurableSet_Ioc
  have hT := tendsto_setIntegral_mul_cexp_atTop (fun x : ℝ => F x/(x:ℂ))
    ((Set.Ioc (-1) 1)ᶜ) measurableSet_Ioc.compl
  have hS := tendsto_gammaFT_plateau F atTop (tendsto_abs_atTop_atTop)
  have h0 := (hW.add hS).sub hT
  rw [show ((0:ℂ) + 0 - 0 : ℂ) = 0 by ring] at h0
  exact h0

/-- **Poitou's `γ` vanishes at `-∞`** — unconditionally. -/
theorem tendsto_gammaFT_atBot (F : ℝ → ℂ) :
    Tendsto (gammaFT F) atBot (nhds 0) := by
  have hW := tendsto_setIntegral_mul_cexp_atBot (fun x : ℝ => (F 0 - F x)/(x:ℂ))
    (Set.Ioc (-1) 1) measurableSet_Ioc
  have hT := tendsto_setIntegral_mul_cexp_atBot (fun x : ℝ => F x/(x:ℂ))
    ((Set.Ioc (-1) 1)ᶜ) measurableSet_Ioc.compl
  have hS := tendsto_gammaFT_plateau F atBot ?_
  · have h0 := (hW.add hS).sub hT
    rw [show ((0:ℂ) + 0 - 0 : ℂ) = 0 by ring] at h0
    exact h0
  · have h1 : Tendsto (fun t : ℝ => -t) atBot atTop := tendsto_neg_atBot_atTop
    refine (tendsto_abs_atTop_atTop.comp h1).congr (fun t => ?_)
    simp only [Function.comp_apply]
    rw [abs_neg]

/-- **The `γ = O(1/t)` bound from quadratic Fourier decay** (Poitou's Lemme 1 made
quantitative): if the Fourier transform of `F` is `O(1/γ²)` beyond `γ₀`, then
`‖γ_F(t)‖ ≤ C/|t|` there, via `γ' = -iφ` and the fundamental theorem of calculus
against the vanishing at infinity. -/
theorem norm_gammaFT_le_of_fourier_decay {F : ℝ → ℂ} (hF : Integrable F)
    (hFdiv : IntegrableOn (fun x : ℝ => (F 0 - F x)/(x:ℂ)) (Set.Ioc (-1) 1))
    {C γ₀ : ℝ} (hγ₀ : 1 ≤ γ₀)
    (hφ : ∀ γ : ℝ, γ₀ ≤ |γ| →
      ‖∫ x : ℝ, F x * Complex.exp ((γ*x : ℝ) * Complex.I)‖ ≤ C/γ^2) :
    ∀ t : ℝ, γ₀ ≤ |t| → ‖gammaFT F t‖ ≤ C/|t| := by
  have hrpow : ∀ τ : ℝ, 0 < τ → ∀ u : ℝ, τ < u → u^(-2 : ℝ) = 1/u^2 := by
    intro τ hτ u hu
    have hu0 : 0 < u := lt_trans hτ hu
    rw [Real.rpow_neg hu0.le, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num,
      Real.rpow_natCast, one_div]
  have hval : ∀ τ : ℝ, 0 < τ → (∫ u in Set.Ioi τ, C * u^(-2 : ℝ)) = C/τ := by
    intro τ hτ
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hτ,
      show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  -- the one-sided tail bound, stated for the positive ray after reflection bookkeeping
  have hmain : ∀ (g : ℝ → ℂ) (ψ : ℝ → ℂ) (τ : ℝ), γ₀ ≤ τ →
      (∀ u ∈ Set.Ici τ, HasDerivAt g (ψ u) u) →
      (∀ u : ℝ, τ < u → ‖ψ u‖ ≤ C/u^2) →
      AEStronglyMeasurable ψ ((volume : Measure ℝ).restrict (Set.Ioi τ)) →
      Tendsto g atTop (nhds 0) →
      ‖g τ‖ ≤ C/τ := by
    intro g ψ τ hτ hderiv hψb hψm htend
    have hτ0 : 0 < τ := lt_of_lt_of_le one_pos (le_trans hγ₀ hτ)
    have hint : IntegrableOn ψ (Set.Ioi τ) := by
      refine Integrable.mono' (g := fun u : ℝ => C * u^(-2 : ℝ))
        ((integrableOn_Ioi_rpow_of_lt (by norm_num) hτ0).const_mul C) hψm ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall (fun u hu => ?_))
      rw [Set.mem_Ioi] at hu
      show ‖ψ u‖ ≤ C * u^(-2 : ℝ)
      rw [hrpow τ hτ0 u hu]
      refine le_trans (hψb u hu) (le_of_eq ?_)
      rw [one_div, div_eq_mul_inv]
    have hkey := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
    rw [zero_sub] at hkey
    have hg : g τ = -∫ u in Set.Ioi τ, ψ u := by
      rw [hkey, neg_neg]
    rw [hg, norm_neg]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    rw [← hval τ hτ0]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun u => norm_nonneg _))
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) hτ0).const_mul C) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun u hu => ?_))
    rw [Set.mem_Ioi] at hu
    show ‖ψ u‖ ≤ C * u^(-2 : ℝ)
    rw [hrpow τ hτ0 u hu]
    refine le_trans (hψb u hu) (le_of_eq ?_)
    rw [one_div, div_eq_mul_inv]
  have hφc : Continuous (fun γ : ℝ => ∫ x : ℝ, F x * Complex.exp ((γ*x : ℝ) * Complex.I)) :=
    continuous_muFT hF
  intro t ht
  rcases le_or_gt γ₀ t with htpos | htneg
  · -- positive side
    have habs : |t| = t := abs_of_pos (lt_of_lt_of_le one_pos (le_trans hγ₀ htpos))
    rw [habs]
    refine hmain (gammaFT F) (fun u => -Complex.I
      * ∫ x : ℝ, F x * Complex.exp ((u*x : ℝ) * Complex.I)) t htpos ?_ ?_ ?_
      (tendsto_gammaFT_atTop F)
    · intro u hu
      rw [Set.mem_Ici] at hu
      refine hasDerivAt_gammaFT hF hFdiv ?_
      have : (0:ℝ) < u := lt_of_lt_of_le one_pos (le_trans hγ₀ (le_trans htpos hu))
      linarith
    · intro u hu
      have hu0 : γ₀ ≤ |u| := by
        rw [abs_of_pos (lt_trans (lt_of_lt_of_le one_pos (le_trans hγ₀ htpos)) hu)]
        linarith
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      exact hφ u hu0
    · exact ((continuous_const.mul hφc).aestronglyMeasurable).restrict
  · -- negative side: reflect
    have htneg' : t ≤ -γ₀ := by
      rcases abs_cases t with ⟨h1, _⟩ | ⟨h1, h2⟩
      · rw [h1] at ht
        linarith
      · rw [h1] at ht
        linarith
    have hτ : γ₀ ≤ -t := by linarith
    have habs : |t| = -t := abs_of_neg (by linarith)
    rw [habs]
    have hgval : gammaFT F t = (fun u : ℝ => gammaFT F (-u)) (-t) := by
      simp only [neg_neg]
    rw [show ‖gammaFT F t‖ = ‖(fun u : ℝ => gammaFT F (-u)) (-t)‖ by rw [← hgval]]
    refine hmain (fun u : ℝ => gammaFT F (-u))
      (fun u => Complex.I * ∫ x : ℝ, F x * Complex.exp (((-u)*x : ℝ) * Complex.I))
      (-t) hτ ?_ ?_ ?_ ?_
    · intro u hu
      rw [Set.mem_Ici] at hu
      have hu0 : 0 < u := lt_of_lt_of_le one_pos (le_trans hγ₀ (le_trans hτ hu))
      have hd := hasDerivAt_gammaFT hF hFdiv (t := -u) (by linarith : (-u : ℝ) ≠ 0)
      have hneg : HasDerivAt (fun v : ℝ => -v) (-(1:ℝ)) u := (hasDerivAt_id u).neg
      have hcomp := hd.scomp u hneg
      have hval2 : ((-1 : ℝ)) • (-Complex.I
          * ∫ x : ℝ, F x * Complex.exp (((-u)*x : ℝ) * Complex.I))
          = Complex.I * ∫ x : ℝ, F x * Complex.exp (((-u)*x : ℝ) * Complex.I) := by
        rw [Complex.real_smul]
        push_cast
        ring
      rw [hval2] at hcomp
      exact hcomp
    · intro u hu
      have hu0 : 0 < u := lt_trans (lt_of_lt_of_le one_pos (le_trans hγ₀ hτ)) hu
      have habs2 : γ₀ ≤ |(-u : ℝ)| := by
        rw [abs_neg, abs_of_pos hu0]
        linarith
      rw [norm_mul, Complex.norm_I, one_mul]
      refine le_trans (hφ (-u) habs2) (le_of_eq ?_)
      rw [neg_pow]
      norm_num
    · refine ((continuous_const.mul ?_).aestronglyMeasurable).restrict
      exact hφc.comp continuous_neg
    · exact (tendsto_gammaFT_atBot F).comp tendsto_neg_atTop_atBot

/-- The auxiliary function is integrable on the line (exponential decay). -/
theorem integrable_auxF (s : ℂ) {X : ℝ} (hX : 1 < X) (hs : 1/2 < s.re) :
    Integrable (auxF s X) := by
  refine Integrable.mono'
    (g := fun t : ℝ => Real.exp ((s.re - 1/2) * Real.log X)
      * Real.exp (-(s.re - 1/2) * |t|)) ?_ ?_ ?_
  · refine Integrable.const_mul ?_ _
    have h0 := integrable_exp_neg_mul_abs (b := s.re - 1/2) (by linarith)
    exact h0
  · exact (continuous_auxF s hX).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => norm_auxF_le s hX.le hs.le t)

/-- The divided difference `(F(0) - F(x))/x` of the auxiliary function is integrable
on the unit window: it vanishes on the plateau `|x| ≤ min 1 (log X)` and is bounded
by a constant on the remainder. -/
theorem integrableOn_auxF_diffQuot_window (s : ℂ) {X : ℝ} (hX : 1 < X)
    (hs : 1/2 < s.re) :
    IntegrableOn (fun x : ℝ => (auxF s X 0 - auxF s X x)/(x:ℂ)) (Set.Ioc (-1) 1) := by
  set δ : ℝ := min 1 (Real.log X) with hδ_def
  have hδ0 : 0 < δ := lt_min one_pos (Real.log_pos hX)
  set B : ℝ := (1 + Real.exp ((s.re - 1/2) * Real.log X)) / δ with hB_def
  have hbound : ∀ x : ℝ, ‖(auxF s X 0 - auxF s X x)/(x:ℂ)‖ ≤ B := by
    intro x
    rcases le_or_gt |x| δ with hx | hx
    · -- plateau: the numerator vanishes
      have h1 : auxF s X x = 1 := by
        rw [auxF, if_pos]
        exact le_trans hx (min_le_right _ _)
      rw [auxF_zero s hX.le, h1, sub_self, zero_div, norm_zero, hB_def]
      positivity
    · have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at hx
        linarith
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      have hnum : ‖auxF s X 0 - auxF s X x‖
          ≤ 1 + Real.exp ((s.re - 1/2) * Real.log X) := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [auxF_zero s hX.le, norm_one]
        have h2 := norm_auxF_le s hX.le hs.le x
        have h3 : Real.exp (-(s.re - 1/2) * |x|) ≤ 1 := by
          refine Real.exp_le_one_iff.mpr ?_
          have := abs_nonneg x
          nlinarith
        nlinarith [Real.exp_pos ((s.re - 1/2) * Real.log X),
          norm_nonneg (auxF s X x), Real.exp_pos (-(s.re - 1/2) * |x|)]
      rw [hB_def]
      calc ‖auxF s X 0 - auxF s X x‖ / |x|
          ≤ (1 + Real.exp ((s.re - 1/2) * Real.log X)) / |x| := by
            rw [div_le_div_iff_of_pos_right (by positivity)]
            exact hnum
        _ ≤ (1 + Real.exp ((s.re - 1/2) * Real.log X)) / δ := by
            refine div_le_div_of_nonneg_left ?_ hδ0 hx.le
            positivity
  refine Integrable.mono' (g := fun _ : ℝ => B)
    (MeasureTheory.integrableOn_const (by exact (measure_Ioc_lt_top).ne)) ?_
    (Filter.Eventually.of_forall (fun x => hbound x))
  refine AEStronglyMeasurable.congr
    (f := fun x : ℝ => (auxF s X 0 - auxF s X x) * ((x:ℂ))⁻¹) ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((aestronglyMeasurable_const.sub
        (continuous_auxF s hX).aestronglyMeasurable)).restrict
    · exact ((Complex.measurable_ofReal.inv).aestronglyMeasurable).restrict
  · refine Filter.Eventually.of_forall (fun x => ?_)
    show (auxF s X 0 - auxF s X x) * ((x:ℂ))⁻¹ = (auxF s X 0 - auxF s X x)/(x:ℂ)
    rw [div_eq_mul_inv]

/-- Convention bridge: the paper Fourier integral in window normal form. -/
theorem paperFourierIntegral_eq_muFT (F : ℝ → ℂ) (γ : ℝ) :
    paperFourierIntegral F γ = ∫ x : ℝ, F x * Complex.exp ((γ*x : ℝ) * Complex.I) := by
  rw [paperFourierIntegral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  push_cast
  ring_nf

/-- `log(2+|t|)/|t| → 0` along any filter where `|t| → ∞`. -/
theorem tendsto_log_two_add_abs_div_abs (l : Filter ℝ)
    (habs : Tendsto (fun t : ℝ => |t|) l atTop) :
    Tendsto (fun t : ℝ => Real.log (2 + |t|) / |t|) l (nhds 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    have := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    refine this.congr (fun x => ?_)
    rfl
  have h1 : Tendsto (fun r : ℝ => Real.log (2 + r) / (2 + r)) atTop (nhds 0) := by
    have h2 : Tendsto (fun r : ℝ => 2 + r) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_id
    exact h0.comp h2
  have h3 : Tendsto (fun r : ℝ => (2 + r) / r) atTop (nhds 1) := by
    have h4 : Tendsto (fun r : ℝ => 2/r + 1) atTop (nhds (0 + 1)) := by
      refine Tendsto.add ?_ tendsto_const_nhds
      exact tendsto_const_nhds.div_atTop tendsto_id
    rw [zero_add] at h4
    refine h4.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with r hr
    field_simp
  have h5 : Tendsto (fun r : ℝ => Real.log (2 + r) / r) atTop (nhds 0) := by
    have h6 := h1.mul h3
    rw [zero_mul] at h6
    refine h6.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with r hr
    have h7 : (2 + r) ≠ 0 := by linarith
    field_simp
  exact h5.comp habs

/-- **The boundary decay `ρ·γ → 0`** from the `O(log)`-kernel and an `O(1/t)`
bound on `γ`. -/
theorem tendsto_rhoFT_mul_gammaFT_of_decay {F : ℝ → ℂ} {σ : ℝ}
    (hσ : 0 < σ) (hσl : -1 ≤ σ) (hσr : σ ≤ 2)
    {C γ₀ : ℝ}
    (hγb : ∀ t : ℝ, γ₀ ≤ |t| → ‖gammaFT F t‖ ≤ C/|t|)
    (l : Filter ℝ) (habs : Tendsto (fun t : ℝ => |t|) l atTop) :
    Tendsto (fun t : ℝ => rhoFT (fun x => ((poitouKernel σ x : ℝ) : ℂ)) t
      * gammaFT F t) l (nhds 0) := by
  obtain ⟨Cρ, hCρ, hρb⟩ := exists_norm_rhoFT_poitouKernel_le hσ hσl hσr
  have hlog := tendsto_log_two_add_abs_div_abs l habs
  have hlim : Tendsto (fun t : ℝ => Cρ * C * (Real.log (2 + |t|) / |t|)) l (nhds 0) := by
    have h0 := hlog.const_mul (Cρ * C)
    rw [mul_zero] at h0
    exact h0
  refine squeeze_zero_norm' ?_ hlim
  have hev : ∀ᶠ t : ℝ in l, max 2 γ₀ ≤ |t| :=
    habs.eventually (Filter.eventually_ge_atTop (max 2 γ₀))
  filter_upwards [hev] with t ht
  have ht2 : 2 ≤ |t| := le_trans (le_max_left _ _) ht
  have htγ : γ₀ ≤ |t| := le_trans (le_max_right _ _) ht
  have ht0 : 0 < |t| := lt_of_lt_of_le two_pos ht2
  rw [norm_mul]
  calc ‖rhoFT (fun x => ((poitouKernel σ x : ℝ) : ℂ)) t‖ * ‖gammaFT F t‖
      ≤ (Cρ * Real.log (2 + |t|)) * (C/|t|) := by
        refine mul_le_mul (hρb t ht2) (hγb t htγ) (norm_nonneg _) ?_
        have hlognn : 0 ≤ Real.log (2 + |t|) :=
          Real.log_nonneg (by linarith [abs_nonneg t])
        positivity
    _ = Cρ * C * (Real.log (2 + |t|) / |t|) := by
        field_simp

/-- **Boundary discharge at the auxiliary function**: `ρ_σ·γ_{F_{s,X}} → 0` along
any `|t| → ∞` filter — the `htop2`/`hbot2` hypotheses of the Weil assembly. -/
theorem tendsto_boundary_auxF (s : ℂ) {X : ℝ} (hX : 1 < X) (hs : 1/2 < s.re)
    {σ : ℝ} (hσ : 0 < σ) (hσl : -1 ≤ σ) (hσr : σ ≤ 2) (l : Filter ℝ)
    (habs : Tendsto (fun t : ℝ => |t|) l atTop) :
    Tendsto (fun t : ℝ => rhoFT (fun x => ((poitouKernel σ x : ℝ) : ℂ)) t
      * gammaFT (auxF s X) t) l (nhds 0) := by
  obtain ⟨C, γ₀, hC, hγ₀, hφ⟩ := exists_norm_fourier_auxF_le s hX hs
  refine tendsto_rhoFT_mul_gammaFT_of_decay (C := C) (γ₀ := γ₀) hσ hσl hσr ?_ l habs
  refine norm_gammaFT_le_of_fourier_decay (integrable_auxF s hX hs)
    (integrableOn_auxF_diffQuot_window s hX hs) hγ₀ ?_
  intro γ hγ
  rw [← paperFourierIntegral_eq_muFT]
  exact hφ γ hγ

/-- **Boundary discharge at the half-scaled auxiliary function**: the
`htop4`/`hbot4` hypotheses of the Weil assembly. -/
theorem tendsto_boundary_auxF_half (s : ℂ) {X : ℝ} (hX : 1 < X) (hs : 1/2 < s.re)
    {σ : ℝ} (hσ : 0 < σ) (hσl : -1 ≤ σ) (hσr : σ ≤ 2) (l : Filter ℝ)
    (habs : Tendsto (fun t : ℝ => |t|) l atTop) :
    Tendsto (fun t : ℝ => rhoFT (fun x => ((poitouKernel σ x : ℝ) : ℂ)) t
      * gammaFT (fun x : ℝ => auxF s X (x/2) / 2) t) l (nhds 0) := by
  obtain ⟨C, γ₀, hC, hγ₀, hφ⟩ := exists_norm_fourier_auxF_le s hX hs
  refine tendsto_rhoFT_mul_gammaFT_of_decay (C := C) (γ₀ := γ₀) hσ hσl hσr ?_ l habs
  have hFh : Integrable (fun x : ℝ => auxF s X (x/2) / 2) :=
    integrable_halfScale (integrable_auxF s hX hs)
  have hFhdiv : IntegrableOn (fun x : ℝ =>
      ((fun x : ℝ => auxF s X (x/2) / 2) 0 - (fun x : ℝ => auxF s X (x/2) / 2) x)/(x:ℂ))
      (Set.Ioc (-1) 1) := by
    refine (integrableOn_halfScale_div (integrableOn_auxF_diffQuot_window s hX hs)).congr
      (Filter.Eventually.of_forall (fun x => ?_))
    show (auxF s X 0/2 - auxF s X (x/2)/2)/(x:ℂ)
        = (auxF s X (0/2) / 2 - auxF s X (x/2) / 2)/(x:ℂ)
    norm_num
  refine norm_gammaFT_le_of_fourier_decay hFh hFhdiv hγ₀ ?_
  intro u hu
  -- the Fourier transform of the half-scale is the transform at 2u
  have hFour : (∫ x : ℝ, (auxF s X (x/2) / 2) * Complex.exp ((u*x : ℝ) * Complex.I))
      = ∫ x : ℝ, auxF s X x * Complex.exp (((2*u)*x : ℝ) * Complex.I) := by
    set g : ℝ → ℂ := fun w => auxF s X w * Complex.exp (((2*u)*w : ℝ) * Complex.I)
      with hg
    have h1 : (∫ x : ℝ, g ((2:ℝ)⁻¹ * x)) = |(((2:ℝ)⁻¹))⁻¹| • ∫ x : ℝ, g x :=
      MeasureTheory.Measure.integral_comp_mul_left g ((2:ℝ)⁻¹)
    have h2 : (fun x : ℝ => (auxF s X (x/2) / 2) * Complex.exp ((u*x : ℝ) * Complex.I))
        = fun x : ℝ => (1/2 : ℂ) * g ((2:ℝ)⁻¹ * x) := by
      funext x
      show (auxF s X (x/2) / 2) * Complex.exp ((u*x : ℝ) * Complex.I)
          = (1/2 : ℂ) * g ((2:ℝ)⁻¹ * x)
      rw [hg]
      show (auxF s X (x/2) / 2) * Complex.exp ((u*x : ℝ) * Complex.I)
          = (1/2 : ℂ) * (auxF s X ((2:ℝ)⁻¹ * x)
            * Complex.exp (((2*u)*((2:ℝ)⁻¹ * x) : ℝ) * Complex.I))
      rw [show (2:ℝ)⁻¹ * x = x/2 by ring]
      rw [show ((2*u)*(x/2) : ℝ) = (u*x : ℝ) by ring]
      ring
    rw [h2, MeasureTheory.integral_const_mul, h1,
      show |(((2:ℝ)⁻¹))⁻¹| = (2:ℝ) by norm_num, Complex.real_smul,
      Complex.ofReal_ofNat]
    ring
  show ‖∫ x : ℝ, (auxF s X (x/2) / 2) * Complex.exp ((u*x : ℝ) * Complex.I)‖ ≤ C/u^2
  rw [hFour, ← paperFourierIntegral_eq_muFT]
  have h2u : γ₀ ≤ |2*u| := by
    rw [abs_mul, abs_two]
    have h0 := abs_nonneg u
    linarith
  refine le_trans (hφ (2*u) h2u) ?_
  have hu0 : (0:ℝ) < u^2 := by
    have h0 : u ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hu
      linarith
    positivity
  rw [mul_pow]
  rw [show (2:ℝ)^2 * u^2 = 4 * u^2 by ring]
  refine div_le_div_of_nonneg_left hC.le hu0 ?_
  linarith

end DedekindResidue
