module

public import Mathlib
public import DedekindResidue.ExplicitFormula.PhiTransform

/-!
# Rectangle contour integrals and the rectangle Cauchy formula  (SP2-RECT R-c)

The explicit-formula contour is Poitou's rectangle `[-a, 1+a] × [-T, T]` (p. 6-01).
Mathlib provides Cauchy–Goursat on rectangles (`integral_boundary_rect_eq_zero_…`) but
no winding/Cauchy *formula*; this file supplies it:

* `rectangleIntegral f z w` — the counterclockwise boundary combination
  bottom − top + i·right − i·left used by mathlib's Goursat theorem;
* `rectangleIntegral_eq_zero` — the Goursat wrapper (countable exceptional set);
* `rectangleIntegral_inv_sub` — the winding integral `∮ (ζ−ρ)⁻¹ dζ = 2πi` for `ρ`
  inside, by explicit `log`-antiderivatives on the four sides (the left side through
  the reflected branch `log(−(ζ−ρ))`) and the jump identities
  `log(−u) = log u ∓ πi` (`log_neg_of_im_pos`/`log_neg_of_im_neg`);
* `rectangleIntegral_cauchy` — the Cauchy formula
  `∮ Φ(ζ)·(ζ−ρ)⁻¹ dζ = 2πi·Φ(ρ)`, by peeling `dslope Φ ρ` (continuous on the closed
  rectangle, differentiable off `ρ` — Goursat kills it) from `Φ(ρ)·(ζ−ρ)⁻¹`.

Route: `.mathlib-quality/decomposition-sp2.md`, leaf SP2-RECT (R-b, R-c).
-/

@[expose] public section

namespace DedekindResidue

open MeasureTheory Complex intervalIntegral

/-- The (counterclockwise) boundary integral over the axis-parallel rectangle with
corners `z` (bottom-left) and `w` (top-right), in the combination used by mathlib's
rectangle Cauchy–Goursat theorem: bottom − top + i·right − i·left. -/
noncomputable def rectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I))
    - (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I))
    + Complex.I • (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I))
    - Complex.I • (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I))

/-- `log(-u) = log u - πi` in the upper half-plane. -/
theorem log_neg_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    Complex.log (-u) = Complex.log u - Real.pi * Complex.I := by
  have hne : u ≠ 0 := by
    intro h0
    rw [h0] at hu
    simp at hu
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hu]
  push_cast
  ring

/-- `log(-u) = log u + πi` in the lower half-plane. -/
theorem log_neg_of_im_neg {u : ℂ} (hu : u.im < 0) :
    Complex.log (-u) = Complex.log u + Real.pi * Complex.I := by
  have hne : u ≠ 0 := by
    intro h0
    rw [h0] at hu
    simp at hu
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hu]
  push_cast
  ring

/-- FTC on a horizontal segment staying in the slit plane:
`∫_{a}^{b} (x + ci − ρ)⁻¹ dx = log(b + ci − ρ) − log(a + ci − ρ)`. -/
theorem integral_horizontal_inv_sub {a b c : ℝ} {ρ : ℂ}
    (h : ∀ x ∈ Set.uIcc a b, ((x:ℂ) + (c:ℂ) * Complex.I - ρ) ∈ Complex.slitPlane) :
    ∫ x : ℝ in a..b, ((x:ℂ) + (c:ℂ) * Complex.I - ρ)⁻¹
      = Complex.log ((b:ℂ) + (c:ℂ) * Complex.I - ρ)
        - Complex.log ((a:ℂ) + (c:ℂ) * Complex.I - ρ) := by
  have hne : ∀ x ∈ Set.uIcc a b, ((x:ℂ) + (c:ℂ) * Complex.I - ρ) ≠ 0 :=
    fun x hx => Complex.slitPlane_ne_zero (h x hx)
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => Complex.log ((t:ℂ) + (c:ℂ) * Complex.I - ρ))
        (((x:ℂ) + (c:ℂ) * Complex.I - ρ)⁻¹) x := by
    intro x hx
    have hlin : HasDerivAt (fun t : ℝ => (t:ℂ) + (c:ℂ) * Complex.I - ρ) 1 x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const
        ((c:ℂ) * Complex.I)).sub_const ρ
    have := hlin.clog_real (h x hx)
    simpa using this
  have hcont : IntervalIntegrable
      (fun x : ℝ => ((x:ℂ) + (c:ℂ) * Complex.I - ρ)⁻¹) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ ?_ hne
    fun_prop
  exact integral_eq_sub_of_hasDerivAt hderiv hcont

/-- FTC on a vertical segment staying in the slit plane:
`i·∫_{c}^{d} (b + yi − ρ)⁻¹ dy = log(b + di − ρ) − log(b + ci − ρ)`. -/
theorem smul_integral_vertical_inv_sub {b c d : ℝ} {ρ : ℂ}
    (h : ∀ y ∈ Set.uIcc c d, ((b:ℂ) + (y:ℂ) * Complex.I - ρ) ∈ Complex.slitPlane) :
    Complex.I • (∫ y : ℝ in c..d, ((b:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹)
      = Complex.log ((b:ℂ) + (d:ℂ) * Complex.I - ρ)
        - Complex.log ((b:ℂ) + (c:ℂ) * Complex.I - ρ) := by
  have hne : ∀ y ∈ Set.uIcc c d, ((b:ℂ) + (y:ℂ) * Complex.I - ρ) ≠ 0 :=
    fun y hy => Complex.slitPlane_ne_zero (h y hy)
  have hderiv : ∀ y ∈ Set.uIcc c d,
      HasDerivAt (fun t : ℝ => Complex.log ((b:ℂ) + (t:ℂ) * Complex.I - ρ))
        (Complex.I * ((b:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹) y := by
    intro y hy
    have hlin : HasDerivAt (fun t : ℝ => (b:ℂ) + (t:ℂ) * Complex.I - ρ) Complex.I y := by
      have h1 : HasDerivAt (fun t : ℝ => (t:ℂ) * Complex.I) Complex.I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I
      simpa using (h1.const_add ((b:ℂ))).sub_const ρ
    have := hlin.clog_real (h y hy)
    rw [div_eq_mul_inv] at this
    simpa [mul_comm] using this
  have hcont : IntervalIntegrable
      (fun y : ℝ => Complex.I * ((b:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹) volume c d := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inv₀ ?_ hne
    fun_prop
  have hint := integral_eq_sub_of_hasDerivAt hderiv hcont
  rw [intervalIntegral.integral_const_mul] at hint
  rw [smul_eq_mul]
  exact hint

/-- **The rectangle winding integral** (SP2-RECT R-c core): for `ρ` in the open
rectangle with corners `z` (bottom-left) and `w` (top-right),
`∮_{∂R} (ζ − ρ)⁻¹ dζ = 2πi`. -/
theorem rectangleIntegral_inv_sub {z w ρ : ℂ}
    (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
    rectangleIntegral (fun ζ => (ζ - ρ)⁻¹) z w = 2 * Real.pi * Complex.I := by
  rw [rectangleIntegral]
  -- the four segments
  have hbot : ∀ x ∈ Set.uIcc z.re w.re,
      ((x:ℂ) + (z.im:ℂ) * Complex.I - ρ) ∈ Complex.slitPlane := by
    intro x _
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    have him : ((x:ℂ) + (z.im:ℂ) * Complex.I - ρ).im = z.im - ρ.im := by simp
    rw [him]
    exact ne_of_lt (by linarith)
  have htop : ∀ x ∈ Set.uIcc z.re w.re,
      ((x:ℂ) + (w.im:ℂ) * Complex.I - ρ) ∈ Complex.slitPlane := by
    intro x _
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    have him : ((x:ℂ) + (w.im:ℂ) * Complex.I - ρ).im = w.im - ρ.im := by simp
    rw [him]
    exact ne_of_gt (by linarith)
  have hright : ∀ y ∈ Set.uIcc z.im w.im,
      ((w.re:ℂ) + (y:ℂ) * Complex.I - ρ) ∈ Complex.slitPlane := by
    intro y _
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hre : ((w.re:ℂ) + (y:ℂ) * Complex.I - ρ).re = w.re - ρ.re := by simp
    rw [hre]
    linarith
  -- rewrite the four integrals; the left segment needs the reflected branch
  have hB := integral_horizontal_inv_sub (a := z.re) (b := w.re) (c := z.im) (ρ := ρ) hbot
  have hT := integral_horizontal_inv_sub (a := z.re) (b := w.re) (c := w.im) (ρ := ρ) htop
  have hR := smul_integral_vertical_inv_sub (b := w.re) (c := z.im) (d := w.im) (ρ := ρ) hright
  -- left segment: reflect through -(ζ - ρ), which has positive real part
  have hleftpt : ∀ y ∈ Set.uIcc z.im w.im,
      (-((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)) ∈ Complex.slitPlane := by
    intro y _
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have hre : (-((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)).re = ρ.re - z.re := by simp
    rw [hre]
    linarith
  have hLderiv : ∀ y ∈ Set.uIcc z.im w.im,
      HasDerivAt (fun t : ℝ => Complex.log (-((z.re:ℂ) + (t:ℂ) * Complex.I - ρ)))
        (Complex.I * ((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹) y := by
    intro y hy
    have hlin : HasDerivAt (fun t : ℝ => -((z.re:ℂ) + (t:ℂ) * Complex.I - ρ))
        (-Complex.I) y := by
      have h1 : HasDerivAt (fun t : ℝ => (t:ℂ) * Complex.I) Complex.I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I
      exact ((h1.const_add ((z.re:ℂ))).sub_const ρ).neg
    have := hlin.clog_real (hleftpt y hy)
    have hne : ((z.re:ℂ) + (y:ℂ) * Complex.I - ρ) ≠ 0 := by
      intro h0
      have := hleftpt y hy
      rw [h0] at this
      simp [Complex.slitPlane] at this
    rw [show -Complex.I / -((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)
        = Complex.I * ((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹ by
      field_simp] at this
    exact this
  have hLcont : IntervalIntegrable
      (fun y : ℝ => Complex.I * ((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹)
      volume z.im w.im := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.inv₀ ?_ ?_
    · fun_prop
    · intro y hy h0
      have := hleftpt y hy
      rw [h0] at this
      simp [Complex.slitPlane] at this
  have hL0 := integral_eq_sub_of_hasDerivAt hLderiv hLcont
  rw [intervalIntegral.integral_const_mul] at hL0
  -- assemble: name the four corner values
  set u₁ : ℂ := (z.re:ℂ) + (z.im:ℂ) * Complex.I - ρ with hu₁
  set u₂ : ℂ := (w.re:ℂ) + (z.im:ℂ) * Complex.I - ρ with hu₂
  set u₃ : ℂ := (w.re:ℂ) + (w.im:ℂ) * Complex.I - ρ with hu₃
  set u₄ : ℂ := (z.re:ℂ) + (w.im:ℂ) * Complex.I - ρ with hu₄
  -- the left integral in terms of the reflected logs
  have hL : Complex.I • (∫ y : ℝ in z.im..w.im, ((z.re:ℂ) + (y:ℂ) * Complex.I - ρ)⁻¹)
      = Complex.log (-u₄) - Complex.log (-u₁) := by
    rw [smul_eq_mul, hL0]
  -- the corner half-plane facts
  have hu₁im : u₁.im < 0 := by
    rw [hu₁]
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re]
    simp
    linarith
  have hu₄im : 0 < u₄.im := by
    rw [hu₄]
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re]
    simp
    linarith
  rw [hB, hT, hR, hL]
  rw [log_neg_of_im_pos hu₄im, log_neg_of_im_neg hu₁im]
  ring



/-- **Rectangle Cauchy–Goursat** (wrapper of mathlib's off-countable version in the
`rectangleIntegral` packaging): the boundary integral of a function continuous on the
closed rectangle and differentiable off a countable set vanishes. -/
theorem rectangleIntegral_eq_zero {f : ℂ → ℂ} {z w : ℂ} {s : Set ℂ} (hs : s.Countable)
    (Hc : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (Hd : ∀ x ∈ (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
      Set.Ioo (min z.im w.im) (max z.im w.im)) \ s, DifferentiableAt ℂ f x) :
    rectangleIntegral f z w = 0 := by
  rw [rectangleIntegral]
  exact Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f z w s hs Hc Hd

/-- Horizontal-segment split of `Φ(ζ)(ζ-ρ)⁻¹` into `dslope + Φ(ρ)·(ζ-ρ)⁻¹`. -/
theorem integral_horizontal_split {Φ : ℂ → ℂ} {ρ : ℂ} {a b c : ℝ} {R : Set ℂ}
    (hcont : ContinuousOn (dslope Φ ρ) R)
    (hseg : ∀ x ∈ Set.uIcc a b, ((x:ℂ) + (c:ℂ) * Complex.I) ∈ R)
    (hne : ∀ x ∈ Set.uIcc a b, ((x:ℂ) + (c:ℂ) * Complex.I) ≠ ρ) :
    ∫ x : ℝ in a..b, Φ ((x:ℂ) + (c:ℂ) * Complex.I) * (((x:ℂ) + (c:ℂ) * Complex.I) - ρ)⁻¹
      = (∫ x : ℝ in a..b, dslope Φ ρ ((x:ℂ) + (c:ℂ) * Complex.I))
        + Φ ρ * ∫ x : ℝ in a..b, (((x:ℂ) + (c:ℂ) * Complex.I) - ρ)⁻¹ := by
  have hpath : ContinuousOn (fun x : ℝ => (x:ℂ) + (c:ℂ) * Complex.I) (Set.uIcc a b) := by
    fun_prop
  have hds_int : IntervalIntegrable
      (fun x : ℝ => dslope Φ ρ ((x:ℂ) + (c:ℂ) * Complex.I)) volume a b :=
    (hcont.comp hpath hseg).intervalIntegrable
  have hinv_int : IntervalIntegrable
      (fun x : ℝ => (((x:ℂ) + (c:ℂ) * Complex.I) - ρ)⁻¹) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro x hx
    exact sub_ne_zero_of_ne (hne x hx)
  have hsplit : ∀ x ∈ Set.uIcc a b,
      Φ ((x:ℂ) + (c:ℂ) * Complex.I) * (((x:ℂ) + (c:ℂ) * Complex.I) - ρ)⁻¹
        = dslope Φ ρ ((x:ℂ) + (c:ℂ) * Complex.I)
          + Φ ρ * (((x:ℂ) + (c:ℂ) * Complex.I) - ρ)⁻¹ := by
    intro x hx
    rw [dslope_of_ne Φ (hne x hx), slope_def_field, div_eq_mul_inv]
    ring
  rw [intervalIntegral.integral_congr hsplit, intervalIntegral.integral_add hds_int
    (hinv_int.const_mul (Φ ρ)), intervalIntegral.integral_const_mul]

/-- Vertical-segment split of `Φ(ζ)(ζ-ρ)⁻¹` into `dslope + Φ(ρ)·(ζ-ρ)⁻¹`. -/
theorem integral_vertical_split {Φ : ℂ → ℂ} {ρ : ℂ} {b c d : ℝ} {R : Set ℂ}
    (hcont : ContinuousOn (dslope Φ ρ) R)
    (hseg : ∀ y ∈ Set.uIcc c d, ((b:ℂ) + (y:ℂ) * Complex.I) ∈ R)
    (hne : ∀ y ∈ Set.uIcc c d, ((b:ℂ) + (y:ℂ) * Complex.I) ≠ ρ) :
    ∫ y : ℝ in c..d, Φ ((b:ℂ) + (y:ℂ) * Complex.I) * (((b:ℂ) + (y:ℂ) * Complex.I) - ρ)⁻¹
      = (∫ y : ℝ in c..d, dslope Φ ρ ((b:ℂ) + (y:ℂ) * Complex.I))
        + Φ ρ * ∫ y : ℝ in c..d, (((b:ℂ) + (y:ℂ) * Complex.I) - ρ)⁻¹ := by
  have hpath : ContinuousOn (fun y : ℝ => (b:ℂ) + (y:ℂ) * Complex.I) (Set.uIcc c d) := by
    fun_prop
  have hds_int : IntervalIntegrable
      (fun y : ℝ => dslope Φ ρ ((b:ℂ) + (y:ℂ) * Complex.I)) volume c d :=
    (hcont.comp hpath hseg).intervalIntegrable
  have hinv_int : IntervalIntegrable
      (fun y : ℝ => (((b:ℂ) + (y:ℂ) * Complex.I) - ρ)⁻¹) volume c d := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (by fun_prop) ?_
    intro y hy
    exact sub_ne_zero_of_ne (hne y hy)
  have hsplit : ∀ y ∈ Set.uIcc c d,
      Φ ((b:ℂ) + (y:ℂ) * Complex.I) * (((b:ℂ) + (y:ℂ) * Complex.I) - ρ)⁻¹
        = dslope Φ ρ ((b:ℂ) + (y:ℂ) * Complex.I)
          + Φ ρ * (((b:ℂ) + (y:ℂ) * Complex.I) - ρ)⁻¹ := by
    intro y hy
    rw [dslope_of_ne Φ (hne y hy), slope_def_field, div_eq_mul_inv]
    ring
  rw [intervalIntegral.integral_congr hsplit, intervalIntegral.integral_add hds_int
    (hinv_int.const_mul (Φ ρ)), intervalIntegral.integral_const_mul]

/-- **The rectangle Cauchy integral formula** (SP2-RECT R-c): for `Φ` differentiable
on (a neighbourhood of each point of) the closed rectangle and `ρ` in the open
rectangle, `∮_{∂R} Φ(ζ)(ζ − ρ)⁻¹ dζ = 2πi·Φ(ρ)`. -/
theorem rectangleIntegral_cauchy {Φ : ℂ → ℂ} {z w ρ : ℂ}
    (hΦ : ∀ ζ ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im, DifferentiableAt ℂ Φ ζ)
    (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
    rectangleIntegral (fun ζ => Φ ζ * (ζ - ρ)⁻¹) z w
      = 2 * Real.pi * Complex.I * Φ ρ := by
  set R : Set ℂ := Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im with hR
  -- ρ is interior to the closed rectangle
  have hρR : R ∈ nhds ρ := by
    rw [← mem_interior_iff_mem_nhds, hR, Complex.interior_reProdIm]
    rw [Set.uIcc_of_le (by linarith : z.re ≤ w.re), Set.uIcc_of_le (by linarith : z.im ≤ w.im),
      interior_Icc, interior_Icc]
    rw [Complex.mem_reProdIm]
    exact ⟨Set.mem_Ioo.mpr ⟨h1, h2⟩, Set.mem_Ioo.mpr ⟨h3, h4⟩⟩
  -- the dslope is continuous on the rectangle, differentiable off ρ
  have hcont : ContinuousOn (dslope Φ ρ) R :=
    (continuousOn_dslope hρR).mpr
      ⟨fun ζ hζ => (hΦ ζ hζ).continuousAt.continuousWithinAt,
        hΦ ρ (mem_of_mem_nhds hρR)⟩
  have hzero : rectangleIntegral (dslope Φ ρ) z w = 0 := by
    refine rectangleIntegral_eq_zero (Set.countable_singleton ρ) hcont ?_
    intro x hx
    obtain ⟨hxmem, hxne⟩ := hx
    rw [Set.mem_singleton_iff] at hxne
    refine (differentiableAt_dslope_of_ne hxne).mpr ?_
    refine hΦ x ?_
    rw [hR]
    rw [Complex.mem_reProdIm] at hxmem ⊢
    rw [Set.uIcc_of_le (by linarith : z.re ≤ w.re), Set.uIcc_of_le (by linarith : z.im ≤ w.im)]
    obtain ⟨hx1, hx2⟩ := hxmem
    rw [min_eq_left (by linarith : z.re ≤ w.re), max_eq_right (by linarith : z.re ≤ w.re)]
      at hx1
    rw [min_eq_left (by linarith : z.im ≤ w.im), max_eq_right (by linarith : z.im ≤ w.im)]
      at hx2
    exact ⟨Set.Ioo_subset_Icc_self hx1, Set.Ioo_subset_Icc_self hx2⟩
  -- segment membership and non-hitting facts
  have hsegB : ∀ x ∈ Set.uIcc z.re w.re, ((x:ℂ) + (z.im:ℂ) * Complex.I) ∈ R := by
    intro x hx
    rw [hR, Complex.mem_reProdIm]
    constructor
    · simpa using hx
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
      simp
  have hsegT : ∀ x ∈ Set.uIcc z.re w.re, ((x:ℂ) + (w.im:ℂ) * Complex.I) ∈ R := by
    intro x hx
    rw [hR, Complex.mem_reProdIm]
    constructor
    · simpa using hx
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re]
      simp
  have hsegR : ∀ y ∈ Set.uIcc z.im w.im, ((w.re:ℂ) + (y:ℂ) * Complex.I) ∈ R := by
    intro y hy
    rw [hR, Complex.mem_reProdIm]
    constructor
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      simp
    · simpa using hy
  have hsegL : ∀ y ∈ Set.uIcc z.im w.im, ((z.re:ℂ) + (y:ℂ) * Complex.I) ∈ R := by
    intro y hy
    rw [hR, Complex.mem_reProdIm]
    constructor
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      simp
    · simpa using hy
  have hneB : ∀ x ∈ Set.uIcc z.re w.re, ((x:ℂ) + (z.im:ℂ) * Complex.I) ≠ ρ := by
    intro x _ h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hneT : ∀ x ∈ Set.uIcc z.re w.re, ((x:ℂ) + (w.im:ℂ) * Complex.I) ≠ ρ := by
    intro x _ h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hneR : ∀ y ∈ Set.uIcc z.im w.im, ((w.re:ℂ) + (y:ℂ) * Complex.I) ≠ ρ := by
    intro y _ h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hneL : ∀ y ∈ Set.uIcc z.im w.im, ((z.re:ℂ) + (y:ℂ) * Complex.I) ≠ ρ := by
    intro y _ h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  -- split all four segments
  have hB := integral_horizontal_split (a := z.re) (b := w.re) (c := z.im) hcont hsegB hneB
  have hT := integral_horizontal_split (a := z.re) (b := w.re) (c := w.im) hcont hsegT hneT
  have hRt := integral_vertical_split (b := w.re) (c := z.im) (d := w.im) hcont hsegR hneR
  have hLt := integral_vertical_split (b := z.re) (c := z.im) (d := w.im) hcont hsegL hneL
  -- assemble
  have hwind := rectangleIntegral_inv_sub h1 h2 h3 h4
  rw [rectangleIntegral] at hzero hwind ⊢
  rw [hB, hT, hRt, hLt]
  rw [smul_eq_mul, smul_eq_mul] at hzero hwind ⊢
  linear_combination hzero + Φ ρ * hwind

end DedekindResidue

end
