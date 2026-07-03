/-
DedekindResidue: B–F Lemma 5 (Landau–Stark) — the zero-sum estimate
`Σ_ρ 1/(¼+γ_ρ²) ≤ (2σ−1)(log Δ_K + 2/(σ−1) − d_{K,σ})`.

Route (B–F lines 523–562 + the footnote at 549–553): apply the Weil–Poitou explicit
formula to the **Landau–Stark test function** `F_h(x) = e^{−h|x|}` (`h = σ − 1/2`),
whose transform is the exact rational `Φ(z) = 1/(h−(z−1/2)) + 1/(h+(z−1/2))`.
The zero side is `Σ_ρ m_ρ·2h/(h²+γ_ρ²)`, the prime side collapses to the Dirichlet
series of `−ζ'_K/ζ_K(σ)`, and the archimedean side evaluates in digamma values.
This file: the admissibility suite for `F_h` (every hypothesis of
`weil_explicit_formula`), its packaged instance, and the eq:Stark display.
-/
module

public import Mathlib
public import DedekindResidue.Lemma4

@[expose] public section

namespace DedekindResidue

open Complex NumberField Filter MeasureTheory

variable (K : Type*) [Field K] [NumberField K]

/-! ### The Landau–Stark test function `F_h(x) = e^{−h|x|}` -/

/-- **The Landau–Stark test function** `F_h(x) = e^{−h|x|}` (B–F footnote, line 551):
the two-sided exponential whose Poitou transform is `2h/(h² − (z−1/2)²)`. -/
noncomputable def expTest (h : ℝ) (x : ℝ) : ℂ := ((Real.exp (-h * |x|) : ℝ) : ℂ)

theorem expTest_neg (h x : ℝ) : expTest h (-x) = expTest h x := by
  unfold expTest
  rw [abs_neg]

theorem expTest_zero (h : ℝ) : expTest h 0 = 1 := by
  unfold expTest
  simp

theorem continuous_expTest (h : ℝ) : Continuous (expTest h) := by
  unfold expTest
  fun_prop

theorem norm_expTest (h x : ℝ) : ‖expTest h x‖ = Real.exp (-h * |x|) := by
  unfold expTest
  rw [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]

theorem norm_expTest_le_one {h : ℝ} (hh : 0 ≤ h) (x : ℝ) : ‖expTest h x‖ ≤ 1 := by
  rw [norm_expTest]
  refine Real.exp_le_one_iff.mpr ?_
  have h0 := abs_nonneg x
  nlinarith [hh, h0]

/-- **`hF` at the Landau–Stark function.** -/
theorem integrable_expTest {h : ℝ} (hh : 0 < h) : Integrable (expTest h) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-h * |x|)) :=
    integrable_exp_neg_mul_abs hh
  exact h1.ofReal

/-- **`hFa` at the Landau–Stark function**: the `c`-weighted function is integrable
for `|c| < h`. -/
theorem integrable_expTest_mul_exp {h : ℝ} {c : ℝ} (hc : |c| < h) :
    Integrable (fun x : ℝ => expTest h x * ((Real.exp (c * x) : ℝ) : ℂ)) := by
  refine Integrable.mono'
    (g := fun x : ℝ => Real.exp (-(h - |c|) * |x|))
    (integrable_exp_neg_mul_abs (by linarith)) ?_ ?_
  · exact ((continuous_expTest h).mul
      (Complex.continuous_ofReal.comp (by fun_prop))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [norm_mul, norm_expTest, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : c * x ≤ |c| * |x| := by
      calc c * x ≤ |c * x| := le_abs_self _
        _ = |c| * |x| := abs_mul c x
    nlinarith [abs_nonneg x]

/-! ### Bounded variation of the weighted Landau–Stark function -/

/-- On the positive ray, `F_h·e^{cx} = e^{(c−h)x}` has an integrable derivative,
hence bounded variation. -/
theorem expTest_mul_exp_bv_Ici {h : ℝ} {c : ℝ} (hc : c < h) :
    BoundedVariationOn (fun x : ℝ => expTest h x * ((Real.exp (c * x) : ℝ) : ℂ))
      (Set.Ici 0) := by
  refine boundedVariationOn_of_deriv_integrable
    (f' := fun x : ℝ => (((c - h) * Real.exp ((c - h) * x) : ℝ) : ℂ))
    Set.ordConnected_Ici
    (Continuous.continuousOn ((continuous_expTest h).mul
      (Complex.continuous_ofReal.comp (by fun_prop)))) ?_ ?_
  · rw [interior_Ici]
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    have hev : (fun y : ℝ => expTest h y * ((Real.exp (c * y) : ℝ) : ℂ))
        =ᶠ[nhds x] fun y : ℝ => ((Real.exp ((c - h) * y) : ℝ) : ℂ) := by
      filter_upwards [eventually_gt_nhds hx0] with y hy
      unfold expTest
      rw [abs_of_pos hy, ← Complex.ofReal_mul, ← Real.exp_add,
        show -h * y + c * y = (c - h) * y by ring]
    have hbase : HasDerivAt (fun y : ℝ => ((Real.exp ((c - h) * y) : ℝ) : ℂ))
        (((c - h) * Real.exp ((c - h) * x) : ℝ) : ℂ) x := by
      have h1 := (((hasDerivAt_id x).const_mul (c - h)).exp).ofReal_comp
      refine h1.congr_deriv ?_
      simp only [id_eq]
      push_cast
      ring
    exact hbase.congr_of_eventuallyEq hev
  · have h1 : IntegrableOn (fun x : ℝ => Real.exp ((c - h) * x)) (Set.Ici 0) := by
      have h2 := exp_neg_integrableOn_Ioi (0:ℝ) (show 0 < -(c - h) by linarith)
      have h3 : IntegrableOn (fun x : ℝ => Real.exp ((c - h) * x)) (Set.Ioi 0) := by
        refine h2.congr_fun (fun x _ => ?_) measurableSet_Ioi
        simp only [neg_neg]
      exact h3.congr_set_ae (Ioi_ae_eq_Ici (a := (0:ℝ))).symm
    have h4 : IntegrableOn
        (fun x : ℝ => (((c - h) * Real.exp ((c - h) * x) : ℝ) : ℂ)) (Set.Ici 0) :=
      (h1.const_mul (c - h)).ofReal
    exact h4

/-- **BV of the weighted Landau–Stark function on the line** for `|c| < h`. -/
theorem boundedVariationOn_expTest_mul_exp {h : ℝ} {c : ℝ}
    (hcl : -h < c) (hcr : c < h) :
    BoundedVariationOn (fun x : ℝ => expTest h x * ((Real.exp (c * x) : ℝ) : ℂ))
      Set.univ := by
  have hpos := expTest_mul_exp_bv_Ici hcr
  have hneg' := expTest_mul_exp_bv_Ici (h := h) (c := -c) (by linarith)
  have hcomp : (fun x : ℝ => expTest h x * ((Real.exp (c * x) : ℝ) : ℂ))
      = (fun x : ℝ => expTest h x * ((Real.exp ((-c) * x) : ℝ) : ℂ))
        ∘ (fun x : ℝ => -x) := by
    funext x
    show expTest h x * ((Real.exp (c * x) : ℝ) : ℂ)
        = expTest h (-x) * ((Real.exp ((-c) * (-x)) : ℝ) : ℂ)
    rw [expTest_neg, neg_mul_neg]
  have hIic : eVariationOn
      (fun x : ℝ => expTest h x * ((Real.exp (c * x) : ℝ) : ℂ)) (Set.Iic 0) ≠ ⊤ := by
    rw [hcomp]
    refine ne_top_of_le_ne_top hneg' (eVariationOn.comp_le_of_antitoneOn _ _ ?_ ?_)
    · exact fun x _ y _ hxy => neg_le_neg hxy
    · exact fun x hx => Set.mem_Ici.mpr (neg_nonneg.mpr hx)
  unfold BoundedVariationOn at hpos ⊢
  rw [show (Set.univ : Set ℝ) = Set.Iic 0 ∪ Set.Ici 0 from
      (Set.Iic_union_Ici (a := (0:ℝ))).symm,
    eVariationOn.union _ ⟨Set.self_mem_Iic, fun x hx => hx⟩
      ⟨Set.self_mem_Ici, fun x hx => hx⟩]
  exact ENNReal.add_ne_top.mpr ⟨hIic, hpos⟩

/-- **`hre` at the Landau–Stark function.** -/
theorem locallyBoundedVariationOn_expTest_re {h : ℝ} (hh : 0 < h) :
    LocallyBoundedVariationOn (fun u : ℝ => (expTest h u).re) Set.univ := by
  have h1 := boundedVariationOn_expTest_mul_exp (h := h) (c := 0) (by linarith) hh
  have h2 : (fun x : ℝ => expTest h x * ((Real.exp (0 * x) : ℝ) : ℂ)) = expTest h := by
    funext x
    rw [zero_mul, Real.exp_zero, Complex.ofReal_one, mul_one]
  rw [h2] at h1
  exact (lipschitzWith_complex_re.comp_boundedVariationOn h1).locallyBoundedVariationOn

/-- **`him` at the Landau–Stark function.** -/
theorem locallyBoundedVariationOn_expTest_im {h : ℝ} (hh : 0 < h) :
    LocallyBoundedVariationOn (fun u : ℝ => (expTest h u).im) Set.univ := by
  have h1 := boundedVariationOn_expTest_mul_exp (h := h) (c := 0) (by linarith) hh
  have h2 : (fun x : ℝ => expTest h x * ((Real.exp (0 * x) : ℝ) : ℂ)) = expTest h := by
    funext x
    rw [zero_mul, Real.exp_zero, Complex.ofReal_one, mul_one]
  rw [h2] at h1
  exact (lipschitzWith_complex_im.comp_boundedVariationOn h1).locallyBoundedVariationOn

/-- **`hGre` at the Landau–Stark function** (`c = 1/2+a < h`). -/
theorem locallyBoundedVariationOn_expTest_mul_exp_re {h : ℝ} {a : ℝ}
    (ha : 0 < a) (hah : 1/2 + a < h) :
    LocallyBoundedVariationOn (fun x : ℝ =>
      ((expTest h x * ((Real.exp ((1/2 + a) * x) : ℝ) : ℂ))).re) Set.univ :=
  (lipschitzWith_complex_re.comp_boundedVariationOn
    (boundedVariationOn_expTest_mul_exp (by linarith) hah)).locallyBoundedVariationOn

/-- **`hGim` at the Landau–Stark function.** -/
theorem locallyBoundedVariationOn_expTest_mul_exp_im {h : ℝ} {a : ℝ}
    (ha : 0 < a) (hah : 1/2 + a < h) :
    LocallyBoundedVariationOn (fun x : ℝ =>
      ((expTest h x * ((Real.exp ((1/2 + a) * x) : ℝ) : ℂ))).im) Set.univ :=
  (lipschitzWith_complex_im.comp_boundedVariationOn
    (boundedVariationOn_expTest_mul_exp (by linarith) hah)).locallyBoundedVariationOn

/-! ### The divided difference `(F_h(0) − F_h(x))/x` -/

/-- The divided difference of the Landau–Stark function is bounded by `h`
(mean value bound `1 − e^{−t} ≤ t`). -/
theorem norm_expTest_diffQuot_le {h : ℝ} (hh : 0 < h) (x : ℝ) :
    ‖(expTest h 0 - expTest h x)/(x:ℂ)‖ ≤ h := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Complex.ofReal_zero, div_zero, norm_zero]
    linarith
  · rw [expTest_zero, norm_div, Complex.norm_real, Real.norm_eq_abs]
    unfold expTest
    rw [show (1 : ℂ) - ((Real.exp (-h * |x|) : ℝ) : ℂ)
        = (((1 - Real.exp (-h * |x|)) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    have hexple : Real.exp (-h * |x|) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have h0 := abs_pos.mpr hx
      nlinarith
    rw [abs_of_nonneg (by linarith)]
    rw [div_le_iff₀ (abs_pos.mpr hx)]
    have h2 := Real.add_one_le_exp (-(h * |x|))
    have h3 : -h * |x| = -(h * |x|) := by ring
    rw [h3]
    linarith

/-- **`hFdiv` at the Landau–Stark function**: the divided difference is integrable
on the window. -/
theorem integrableOn_expTest_diffQuot_window {h : ℝ} (hh : 0 < h) :
    IntegrableOn (fun x : ℝ => (expTest h 0 - expTest h x)/(x:ℂ))
      (Set.Ioc (-1) 1) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (expTest h 0 - expTest h x)/(x:ℂ))
      (volume : Measure ℝ) := by
    refine AEStronglyMeasurable.congr
      (f := fun x : ℝ => (expTest h 0 - expTest h x) * ((x:ℂ))⁻¹) ?_ ?_
    · exact (aestronglyMeasurable_const.sub
        (continuous_expTest h).aestronglyMeasurable).mul
        ((Complex.measurable_ofReal.inv).aestronglyMeasurable)
    · refine Filter.Eventually.of_forall (fun x => ?_)
      show (expTest h 0 - expTest h x) * ((x:ℂ))⁻¹ = (expTest h 0 - expTest h x)/(x:ℂ)
      rw [div_eq_mul_inv]
  refine Integrable.mono' (g := fun _ : ℝ => h) ?_ hmeas.restrict ?_
  · exact integrableOn_const (by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top.ne)
  · exact Filter.Eventually.of_forall (fun x => norm_expTest_diffQuot_le hh x)

/-- **`hFdiv2` at the Landau–Stark function**: the divided difference is
square-integrable on the line (`≤ h` near `0`, `O(1/|x|)` beyond). -/
theorem memLp_two_expTest_diffQuot {h : ℝ} (hh : 0 < h) :
    MemLp (fun x : ℝ => (expTest h 0 - expTest h x)/(x:ℂ)) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (expTest h 0 - expTest h x)/(x:ℂ))
      (volume : Measure ℝ) := by
    refine AEStronglyMeasurable.congr
      (f := fun x : ℝ => (expTest h 0 - expTest h x) * ((x:ℂ))⁻¹) ?_ ?_
    · exact (aestronglyMeasurable_const.sub
        (continuous_expTest h).aestronglyMeasurable).mul
        ((Complex.measurable_ofReal.inv).aestronglyMeasurable)
    · refine Filter.Eventually.of_forall (fun x => ?_)
      show (expTest h 0 - expTest h x) * ((x:ℂ))⁻¹ = (expTest h 0 - expTest h x)/(x:ℂ)
      rw [div_eq_mul_inv]
  have hfar : ∀ x : ℝ, x ≠ 0 → ‖(expTest h 0 - expTest h x)/(x:ℂ)‖ ≤ 1/|x| := by
    intro x hx
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_div_iff_of_pos_right (abs_pos.mpr hx)]
    have h1 : Real.exp (-h * |x|) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have h0 := abs_nonneg x
      nlinarith [hh, h0]
    have h2 := Real.exp_pos (-h * |x|)
    rw [expTest_zero]
    unfold expTest
    rw [show (1 : ℂ) - ((Real.exp (-h * |x|) : ℝ) : ℂ)
        = (((1 - Real.exp (-h * |x|)) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hraypos : IntegrableOn
      (fun x : ℝ => ‖(expTest h 0 - expTest h x)/(x:ℂ)‖^2) (Set.Ioi 1) := by
    refine Integrable.mono' (g := fun x : ℝ => x^(-2 : ℝ))
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos) ?_ ?_
    · exact ((hmeas.norm.pow 2).restrict)
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall (fun x hx => ?_))
      rw [Set.mem_Ioi] at hx
      have hx0 : (0:ℝ) < x := lt_trans one_pos hx
      have h1 := hfar x hx0.ne'
      rw [abs_of_pos hx0] at h1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg hx0.le,
        show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      calc ‖(expTest h 0 - expTest h x)/(x:ℂ)‖^2 ≤ (1/x)^2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = (x^2)⁻¹ := by
            rw [div_pow, one_pow, one_div]
  have hwindow : IntegrableOn
      (fun x : ℝ => ‖(expTest h 0 - expTest h x)/(x:ℂ)‖^2) (Set.Ioc (-1) 1) := by
    refine Integrable.mono' (g := fun _ : ℝ => h^2) ?_
      ((hmeas.norm.pow 2).restrict) ?_
    · exact integrableOn_const (by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top.ne)
    · refine Filter.Eventually.of_forall (fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_expTest_diffQuot_le hh x) 2
  have hrayneg : IntegrableOn
      (fun x : ℝ => ‖(expTest h 0 - expTest h x)/(x:ℂ)‖^2) (Set.Iic (-1)) := by
    have A : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
    have hmap : (volume : Measure ℝ).restrict (Set.Iic (-1))
        = Measure.map (fun x : ℝ => -x)
            ((volume : Measure ℝ).restrict (Set.Ici 1)) := by
      rw [show Set.Ici (1:ℝ) = (fun x : ℝ => -x) ⁻¹' (Set.Iic (-1)) by
          ext x
          simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]
          constructor <;> intro hy <;> linarith,
        ← Measure.restrict_map A.measurable measurableSet_Iic,
        Measure.map_neg_eq_self (volume : Measure ℝ)]
    rw [IntegrableOn, hmap, A.integrable_map_iff]
    have hIci : IntegrableOn
        (fun x : ℝ => ‖(expTest h 0 - expTest h x)/(x:ℂ)‖^2) (Set.Ici 1) :=
      hraypos.congr_set_ae (Ioi_ae_eq_Ici (a := (1:ℝ))).symm
    refine hIci.congr (Filter.Eventually.of_forall (fun x => ?_))
    show ‖(expTest h 0 - expTest h x)/(x:ℂ)‖^2
        = ‖(expTest h 0 - expTest h (-x))/((-x : ℝ):ℂ)‖^2
    rw [expTest_neg]
    have hnorm : ‖(expTest h 0 - expTest h x)/(x:ℂ)‖
        = ‖(expTest h 0 - expTest h x)/((-x : ℝ):ℂ)‖ := by
      rw [norm_div, norm_div]
      congr 1
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_neg]
    rw [hnorm]
  have hcover : (Set.univ : Set ℝ) = Set.Iic (-1) ∪ (Set.Ioc (-1) 1 ∪ Set.Ioi 1) := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioc, Set.mem_Ioi,
      true_iff]
    rcases le_or_gt x (-1) with h1 | h1
    · exact Or.inl h1
    · rcases le_or_gt x 1 with h2 | h2
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inr h2)
  rw [← MeasureTheory.integrableOn_univ, hcover]
  exact hrayneg.union (hwindow.union hraypos)

/-! ### The closed form of the transform: `Φ_{F_h}(z) = 1/(h−(z−1/2)) + 1/(h+(z−1/2))` -/

/-- The complex exponential is integrable on the right ray when its rate has
positive real part. -/
theorem integrableOn_Ioi_cexp_neg {c : ℂ} (hc : 0 < c.re) :
    MeasureTheory.IntegrableOn (fun x : ℝ => Complex.exp (-(c * x)))
      (Set.Ioi (0:ℝ)) := by
  refine Integrable.mono' (g := fun x : ℝ => Real.exp (-c.re * x))
    (exp_neg_integrableOn_Ioi 0 hc) ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).restrict
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr (le_of_eq ?_)
    simp [Complex.mul_re]

/-- `∫_0^∞ e^{−cx} dx = 1/c` for `Re c > 0`. -/
theorem integral_Ioi_cexp_neg {c : ℂ} (hc : 0 < c.re) :
    ∫ x in Set.Ioi (0:ℝ), Complex.exp (-(c * x)) = 1/c := by
  have hc0 : c ≠ 0 := fun hc0 => by
    rw [hc0] at hc
    simp at hc
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun y : ℝ => -Complex.exp (-(c * y))/c)
        (Complex.exp (-(c * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => ((y:ℝ):ℂ)) (((1:ℝ)):ℂ) x :=
      (hasDerivAt_id x).ofReal_comp
    have h2 : HasDerivAt (fun y : ℝ => -(c * ((y:ℝ):ℂ))) (-c) x := by
      have h2a := h1.const_mul (-c)
      have h2b : HasDerivAt (fun y : ℝ => (-c) * ((y:ℝ):ℂ)) (-c) x := by
        simpa using h2a
      exact h2b.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => by ring))
    have h3 : HasDerivAt (fun y : ℝ => Complex.exp (-(c * y)))
        (Complex.exp (-(c * x)) * -c) x := h2.cexp
    have h4 := (h3.neg).div_const c
    refine h4.congr_deriv ?_
    field_simp
  have hlim : Filter.Tendsto (fun y : ℝ => -Complex.exp (-(c * y))/c) atTop
      (nhds 0) := by
    refine squeeze_zero_norm (a := fun y : ℝ => Real.exp (-c.re * y) / ‖c‖)
      (fun y => le_of_eq ?_) ?_
    · rw [norm_div, norm_neg, Complex.norm_exp]
      simp [Complex.mul_re]
    · have h5 : Filter.Tendsto (fun y : ℝ => Real.exp (-c.re * y)) atTop
          (nhds 0) :=
        Real.tendsto_exp_atBot.comp
          (Tendsto.const_mul_atTop_of_neg (by linarith : -c.re < 0) tendsto_id)
      have h6 := h5.div_const ‖c‖
      rw [zero_div] at h6
      exact h6
  have hcont : ContinuousWithinAt (fun y : ℝ => -Complex.exp (-(c * y))/c)
      (Set.Ici 0) 0 := by
    refine Continuous.continuousWithinAt ?_
    fun_prop
  have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    hcont hderiv (integrableOn_Ioi_cexp_neg hc) hlim
  rw [hkey]
  push_cast
  rw [mul_zero, neg_zero, Complex.exp_zero]
  field_simp
  ring

/-- Reflecting a left-ray integral. -/
theorem integral_Iio_comp_neg (G : ℝ → ℂ) :
    ∫ x in Set.Iio (0:ℝ), G x = ∫ x in Set.Ioi (0:ℝ), G (-x) := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).restrict (Set.Iio (0:ℝ))
      = Measure.map (fun x : ℝ => -x) ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    rw [show Set.Ioi (0:ℝ) = (fun x : ℝ => -x) ⁻¹' (Set.Iio 0) by ext x; simp,
      ← Measure.restrict_map A.measurable measurableSet_Iio,
      Measure.map_neg_eq_self (volume : Measure ℝ)]
  rw [show (∫ x in Set.Iio (0:ℝ), G x)
      = ∫ x, G x ∂((volume : Measure ℝ).restrict (Set.Iio 0)) from rfl,
    hmap, A.integral_map]

/-- The weighted Landau–Stark kernel matches the pure exponential on the right
ray. -/
theorem expTest_kernel_eq_Ici {h : ℝ} (z : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    expTest h x * Complex.exp ((z - 1/2) * x)
      = Complex.exp (-(((h:ℂ) - (z - 1/2)) * x)) := by
  unfold expTest
  rw [abs_of_nonneg hx, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The closed form of the Poitou transform of `F_h`** on the convergence strip
`|Re z − 1/2| < h`:
`Φ_{F_h}(z) = 1/(h − (z−1/2)) + 1/(h + (z−1/2))`. -/
theorem paperPhi_expTest {h : ℝ} {z : ℂ} (hz : |z.re - 1/2| < h) :
    paperPhi (expTest h) z
      = 1/((h:ℂ) - (z - 1/2)) + 1/((h:ℂ) + (z - 1/2)) := by
  have habs := abs_lt.mp hz
  have hre1 : 0 < ((h:ℂ) - (z - 1/2)).re := by
    have he : (h:ℂ) - (z - 1/2) = ((h + 1/2 : ℝ) : ℂ) - z := by push_cast; ring
    rw [he, Complex.sub_re, Complex.ofReal_re]
    linarith [habs.2]
  have hre2 : 0 < ((h:ℂ) + (z - 1/2)).re := by
    have he : (h:ℂ) + (z - 1/2) = ((h - 1/2 : ℝ) : ℂ) + z := by push_cast; ring
    rw [he, Complex.add_re, Complex.ofReal_re]
    linarith [habs.1]
  have hEqIoi : ∀ x ∈ Set.Ioi (0:ℝ),
      expTest h x * Complex.exp ((z - 1/2) * x)
        = Complex.exp (-(((h:ℂ) - (z - 1/2)) * x)) :=
    fun x hx => expTest_kernel_eq_Ici z (le_of_lt hx)
  have hEqIoi' : ∀ x ∈ Set.Ioi (0:ℝ),
      expTest h (-x) * Complex.exp ((z - 1/2) * ((-x : ℝ) : ℂ))
        = Complex.exp (-(((h:ℂ) + (z - 1/2)) * x)) := by
    intro x hx
    rw [expTest_neg]
    unfold expTest
    rw [abs_of_nonneg (le_of_lt hx), Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hIci_int : MeasureTheory.IntegrableOn
      (fun x : ℝ => expTest h x * Complex.exp ((z - 1/2) * x)) (Set.Ici 0) :=
    ((integrableOn_Ioi_cexp_neg hre1).congr_fun
      (fun x hx => (hEqIoi x hx).symm) measurableSet_Ioi).congr_set_ae
      (Ioi_ae_eq_Ici (a := (0:ℝ))).symm
  have hIio_int : MeasureTheory.IntegrableOn
      (fun x : ℝ => expTest h x * Complex.exp ((z - 1/2) * x)) (Set.Iio 0) := by
    rw [integrableOn_Iio_comp_neg_iff]
    exact (integrableOn_Ioi_cexp_neg hre2).congr_fun
      (fun x hx => (hEqIoi' x hx).symm) measurableSet_Ioi
  have hIci_val : (∫ x in Set.Ici (0:ℝ), expTest h x * Complex.exp ((z - 1/2) * x))
      = 1/((h:ℂ) - (z - 1/2)) := by
    rw [← MeasureTheory.setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0:ℝ))),
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEqIoi]
    have h1 := integral_Ioi_cexp_neg hre1
    rw [h1, one_div]
  have hIio_val : (∫ x in Set.Iio (0:ℝ), expTest h x * Complex.exp ((z - 1/2) * x))
      = 1/((h:ℂ) + (z - 1/2)) := by
    rw [integral_Iio_comp_neg,
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEqIoi']
    have h1 := integral_Ioi_cexp_neg hre2
    rw [h1, one_div]
  rw [paperPhi, ← MeasureTheory.setIntegral_univ,
    show (Set.univ : Set ℝ) = Set.Iio 0 ∪ Set.Ici 0 from
      (Set.Iio_union_Ici (a := (0:ℝ))).symm,
    MeasureTheory.setIntegral_union (Set.Iio_disjoint_Ici le_rfl)
      measurableSet_Ici hIio_int hIci_int, hIci_val, hIio_val]
  ring

/-- **The Fourier decay of `F̂_h`**: the transform is the rational
`2h/(h²+γ²) ≤ 2h/γ²`. -/
theorem exists_norm_fourier_expTest_le {h : ℝ} (hh : 0 < h) :
    ∃ C γ₀ : ℝ, 0 < C ∧ 1 ≤ γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ |γ| →
      ‖paperFourierIntegral (expTest h) γ‖ ≤ C / γ^2 := by
  refine ⟨2*h, 1, by linarith [hh], le_refl 1, fun γ hγ => ?_⟩
  have hγ0 : γ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hγ
    linarith
  have h1 : paperFourierIntegral (expTest h) γ
      = paperPhi (expTest h) (1/2 + (γ : ℂ) * Complex.I) :=
    (paperPhi_half_add_mul_I (expTest h) γ).symm
  have hre : ((1:ℂ)/2 + (γ:ℂ)*Complex.I).re = 1/2 := by simp
  have h2 := paperPhi_expTest
    (z := 1/2 + (γ:ℂ)*Complex.I) (h := h) (by rw [hre]; simpa using hh)
  have hzero1 : ((h:ℂ) - ((1/2 + (γ:ℂ)*Complex.I) - 1/2))
      = (h:ℂ) - (γ:ℂ)*Complex.I := by ring
  have hzero2 : ((h:ℂ) + ((1/2 + (γ:ℂ)*Complex.I) - 1/2))
      = (h:ℂ) + (γ:ℂ)*Complex.I := by ring
  have hd3 : (((h^2 + γ^2 : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hd1 : ((h:ℂ) - (γ:ℂ)*Complex.I) ≠ 0 := by
    intro h0
    have h1' := congrArg Complex.re h0
    simp at h1'
    linarith
  have hd2 : ((h:ℂ) + (γ:ℂ)*Complex.I) ≠ 0 := by
    intro h0
    have h1' := congrArg Complex.re h0
    simp at h1'
    linarith
  have hprod : ((h:ℂ) - (γ:ℂ)*Complex.I) * ((h:ℂ) + (γ:ℂ)*Complex.I)
      = (((h^2 + γ^2 : ℝ)) : ℂ) := by
    have h2 : ((h:ℂ) - (γ:ℂ)*Complex.I) * ((h:ℂ) + (γ:ℂ)*Complex.I)
        = (h:ℂ)^2 - ((γ:ℂ)*Complex.I)^2 := by ring
    rw [h2, mul_pow, Complex.I_sq]
    push_cast
    ring
  have hcomb : 1/((h:ℂ) - (γ:ℂ)*Complex.I) + 1/((h:ℂ) + (γ:ℂ)*Complex.I)
      = ((2*h : ℝ) : ℂ) / (((h^2 + γ^2 : ℝ)) : ℂ) := by
    rw [div_add_div _ _ hd1 hd2, hprod]
    congr 1
    push_cast
    ring
  rw [h1, h2, hzero1, hzero2, hcomb]
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_pos (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg γ, sq_nonneg h]

/-- **`hB` at the Landau–Stark function**: the band bound `M/max(|t|,1)` with
`M = 2/δ + 2`, `δ = h − (1/2+a)`, straight from the closed form. -/
theorem exists_band_bound_paperPhi_expTest {h : ℝ} (hh : 0 < h) {a : ℝ}
    (ha : 0 < a) (hah : 1/2 + a < h) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ t : ℝ, -a ≤ σ → σ ≤ 1+a →
      ‖paperPhi (expTest h) ((σ:ℂ) + (t:ℂ)*Complex.I)‖ ≤ M / max |t| 1 := by
  set δ : ℝ := h - (1/2 + a) with hδ_def
  have hδ0 : 0 < δ := by rw [hδ_def]; linarith
  refine ⟨2/δ + 2, by positivity, fun σ t hσl hσr => ?_⟩
  have hre : ((σ:ℂ) + (t:ℂ)*Complex.I).re = σ := by simp
  have hband : |((σ:ℂ) + (t:ℂ)*Complex.I).re - 1/2| < h := by
    rw [hre, abs_lt]
    constructor <;> linarith
  rw [paperPhi_expTest hband]
  have hkey : ∀ w : ℂ, δ ≤ |w.re| → |t| ≤ |w.im| → w ≠ 0 →
      ‖1/w‖ ≤ (1/δ + 1) / max |t| 1 := by
    intro w hwre hwim hw0
    rw [norm_div, norm_one]
    have h1 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have h2 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    have hw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    rcases le_total |t| 1 with ht | ht
    · rw [max_eq_right ht, div_one]
      rw [div_add' _ _ _ hδ0.ne', div_le_div_iff₀ hw hδ0]
      have h3 : δ ≤ ‖w‖ := le_trans hwre h1
      nlinarith
    · rw [max_eq_left ht]
      rw [div_le_div_iff₀ hw (by linarith : (0:ℝ) < |t|)]
      have h3 : |t| ≤ ‖w‖ := le_trans hwim h2
      have h4 : (0:ℝ) ≤ 1/δ := by positivity
      nlinarith
  have hb1 : ‖1/((h:ℂ) - (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))‖
      ≤ (1/δ + 1) / max |t| 1 := by
    refine hkey _ ?_ ?_ ?_
    · rw [show (((h:ℂ) - (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))).re
          = h - (σ - 1/2) by simp]
      rw [abs_of_pos (by linarith)]
      rw [hδ_def]
      linarith
    · rw [show (((h:ℂ) - (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))).im = -t by simp,
        abs_neg]
    · intro h0
      have h1' := congrArg Complex.re h0
      rw [show (((h:ℂ) - (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))).re
          = h - (σ - 1/2) by simp] at h1'
      simp at h1'
      linarith
  have hb2 : ‖1/((h:ℂ) + (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))‖
      ≤ (1/δ + 1) / max |t| 1 := by
    refine hkey _ ?_ ?_ ?_
    · rw [show (((h:ℂ) + (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))).re
          = h + (σ - 1/2) by simp]
      rw [abs_of_pos (by linarith)]
      rw [hδ_def]
      linarith
    · rw [show (((h:ℂ) + (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))).im = t by simp]
    · intro h0
      have h1' := congrArg Complex.re h0
      rw [show (((h:ℂ) + (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))).re
          = h + (σ - 1/2) by simp] at h1'
      simp at h1'
      linarith
  refine le_trans (norm_add_le _ _) ?_
  have hmax : (0:ℝ) < max |t| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  calc ‖1/((h:ℂ) - (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))‖
        + ‖1/((h:ℂ) + (((σ:ℂ) + (t:ℂ)*Complex.I) - 1/2))‖
      ≤ (1/δ + 1) / max |t| 1 + (1/δ + 1) / max |t| 1 := add_le_add hb1 hb2
    _ = (2/δ + 2) / max |t| 1 := by
        field_simp
        ring

/-- **`hΦd` at the Landau–Stark function**: the transform is differentiable on the
closed band (which sits strictly inside the convergence strip). -/
theorem differentiableAt_paperPhi_expTest {h : ℝ} {a : ℝ}
    (_ha : 0 < a) (hah : 1/2 + a < h) :
    ∀ ζ : ℂ, -a ≤ ζ.re → ζ.re ≤ 1+a →
      DifferentiableAt ℂ (paperPhi (expTest h)) ζ := by
  intro ζ hζl hζr
  set U : Set ℂ := {z : ℂ | |z.re - 1/2| < h} with hU_def
  have hUopen : IsOpen U := by
    have h1 : U = (fun z : ℂ => |z.re - 1/2|) ⁻¹' (Set.Iio h) := rfl
    rw [h1]
    exact (Continuous.abs (by fun_prop)).isOpen_preimage _ isOpen_Iio
  have hζU : ζ ∈ U := by
    rw [hU_def, Set.mem_setOf_eq, abs_lt]
    constructor <;> linarith
  have hrat : DifferentiableAt ℂ
      (fun z : ℂ => 1/((h:ℂ) - (z - 1/2)) + 1/((h:ℂ) + (z - 1/2))) ζ := by
    have habs : |ζ.re - 1/2| < h := hζU
    have habs' := abs_lt.mp habs
    have hd1 : ((h:ℂ) - (ζ - 1/2)) ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      have h2 : ((h:ℂ) - (ζ - 1/2)) = ((h + 1/2 : ℝ) : ℂ) - ζ := by push_cast; ring
      rw [h2, Complex.sub_re, Complex.ofReal_re] at h1
      simp at h1
      linarith
    have hd2 : ((h:ℂ) + (ζ - 1/2)) ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      have h2 : ((h:ℂ) + (ζ - 1/2)) = ((h - 1/2 : ℝ) : ℂ) + ζ := by push_cast; ring
      rw [h2, Complex.add_re, Complex.ofReal_re] at h1
      simp at h1
      linarith
    refine DifferentiableAt.add ?_ ?_
    · exact (differentiableAt_const _).div
        ((differentiableAt_const _).sub
          ((differentiableAt_id).sub (differentiableAt_const _))) hd1
    · exact (differentiableAt_const _).div
        ((differentiableAt_const _).add
          ((differentiableAt_id).sub (differentiableAt_const _))) hd2
  refine hrat.congr_of_eventuallyEq ?_
  filter_upwards [hUopen.mem_nhds hζU] with z hz
  exact paperPhi_expTest hz

end DedekindResidue

end
