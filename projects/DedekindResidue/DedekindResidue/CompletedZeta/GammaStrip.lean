module

public import Mathlib

/-!
# Vertical behaviour of the Gamma function  (SP1-AC leaf A1)

Two-sided control of `‖Γ(σ+it)‖` on vertical strips, built WITHOUT Stirling asymptotics:
the moduli on the lines `Re = 1/2` and `Re = 1` are **exact** by the reflection formula,

* `norm_Gamma_half_add_mul_I_sq : ‖Γ(1/2+it)‖² = π / cosh(πt)`,
* `norm_Gamma_one_add_mul_I_sq  : ‖Γ(1+it)‖²  = πt / sinh(πt)`  (`t ≠ 0`),

and the strip bounds in between/beyond follow from these by the Hadamard three-lines
theorem, the recurrence `Γ(s+1) = sΓ(s)`, and `1/Γ(z) = Γ(1-z)·sin(πz)/π` (upcoming in
this file). These feed the convexity bounds for `ζ_K` (AC-A3) and the Jensen zero
counting (AC-A4); see `.mathlib-quality/decomposition-sp1ac.md`.
-/

namespace DedekindResidue

@[expose] public section

open Complex MeasureTheory
open scoped Real

/-- Exact modulus of `Γ` on the critical line `Re = 1/2`:
`‖Γ(1/2+it)‖² = π/cosh(πt)`. -/
theorem norm_Gamma_half_add_mul_I_sq (t : ℝ) :
    ‖Complex.Gamma (1/2 + t * Complex.I)‖^2 = π / Real.cosh (π * t) := by
  have key := Complex.Gamma_mul_Gamma_one_sub (1/2 + t * Complex.I)
  have hconj : (1 : ℂ) - (1/2 + t * Complex.I)
      = (starRingEnd ℂ) (1/2 + t * Complex.I) := by
    apply Complex.ext <;> simp
    norm_num
  rw [hconj, Complex.Gamma_conj, Complex.mul_conj] at key
  have hsin : Complex.sin (π * (1/2 + t * Complex.I))
      = ((Real.cosh (π * t) : ℝ) : ℂ) := by
    rw [show (π : ℂ) * (1/2 + t * Complex.I)
        = π/2 + ((π * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two,
      Complex.cos_mul_I]
    push_cast [Complex.ofReal_cosh]
    ring
  rw [hsin] at key
  -- key : ↑(normSq Γz) = ↑π / ↑cosh(πt); cast down
  have hcosh : Real.cosh (π * t) ≠ 0 := (Real.cosh_pos _).ne'
  have : ((Complex.normSq (Complex.Gamma (1/2 + t * Complex.I)) : ℝ) : ℂ)
      = ((π / Real.cosh (π * t) : ℝ) : ℂ) := by
    rw [key]
    push_cast
    ring
  have hreal := Complex.ofReal_injective this
  rw [← hreal, Complex.normSq_eq_norm_sq]

/-- Exact modulus of `Γ` on the line `Re = 1`: `‖Γ(1+it)‖² = πt/sinh(πt)` (`t ≠ 0`). -/
theorem norm_Gamma_one_add_mul_I_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 + t * Complex.I)‖^2 = π * t / Real.sinh (π * t) := by
  have htI : (t : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.ext_iff, ht]
  have key := Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * Complex.I)
  -- Γ(1+it) = it·Γ(it)
  have hrec : Complex.Gamma (1 + t * Complex.I)
      = (t : ℂ) * Complex.I * Complex.Gamma ((t : ℂ) * Complex.I) := by
    rw [add_comm, Complex.Gamma_add_one _ htI]
  have hconj : (1 : ℂ) - (t : ℂ) * Complex.I
      = (starRingEnd ℂ) (1 + t * Complex.I) := by
    apply Complex.ext <;> simp
  have hsin : Complex.sin (π * ((t : ℂ) * Complex.I))
      = ((Real.sinh (π * t) : ℝ) : ℂ) * Complex.I := by
    rw [show (π : ℂ) * ((t : ℂ) * Complex.I) = ((π * t : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.sin_mul_I]
    push_cast [Complex.ofReal_sinh]
    ring
  rw [hconj, Complex.Gamma_conj, hsin] at key
  -- key : Γ(it) · conj Γ(1+it) = π/(sinh(πt)·I)
  have hsinh : Real.sinh (π * t) ≠ 0 := by
    rw [ne_eq, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero ht
  have key2 : ((Complex.normSq (Complex.Gamma (1 + t * Complex.I)) : ℝ) : ℂ)
      = ((π * t / Real.sinh (π * t) : ℝ) : ℂ) := by
    calc ((Complex.normSq (Complex.Gamma (1 + t * Complex.I)) : ℝ) : ℂ)
        = Complex.Gamma (1 + t * Complex.I)
          * (starRingEnd ℂ) (Complex.Gamma (1 + t * Complex.I)) :=
          (Complex.mul_conj _).symm
      _ = ((t : ℂ) * Complex.I) * (Complex.Gamma ((t : ℂ) * Complex.I)
          * (starRingEnd ℂ) (Complex.Gamma (1 + t * Complex.I))) := by
          rw [hrec]; ring
      _ = ((t : ℂ) * Complex.I)
          * ((π : ℂ) / (((Real.sinh (π * t) : ℝ) : ℂ) * Complex.I)) := by rw [key]
      _ = ((π * t / Real.sinh (π * t) : ℝ) : ℂ) := by
          have hsc : ((Real.sinh (π * t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsinh
          push_cast
          field_simp
  have hreal := Complex.ofReal_injective key2
  rw [← hreal, Complex.normSq_eq_norm_sq]

/-- Triangle inequality for the Gamma integral: `‖Γ(z)‖ ≤ Γ(Re z)` on `Re z > 0`. -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz, Complex.GammaIntegral]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re]

/-- `‖sin(x+iy)‖² = sin²x + sinh²y`. -/
theorem norm_sin_add_mul_I_sq (x y : ℝ) :
    ‖Complex.sin (x + y * Complex.I)‖^2 = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.sin_add, Complex.cos_mul_I, Complex.sin_mul_I]
  rw [show Complex.sin x * Complex.cosh y + Complex.cos x * (Complex.sinh y * Complex.I)
      = ((Real.sin x * Real.cosh y : ℝ) : ℂ)
        + ((Real.cos x * Real.sinh y : ℝ) : ℂ) * Complex.I by
    push_cast [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh]
    ring]
  rw [Complex.norm_add_mul_I]
  rw [Real.sq_sqrt (by positivity)]
  have h1 := Real.sin_sq_add_cos_sq x
  have h2 := Real.cosh_sq y
  nlinarith [Real.sinh_sq y]

/-- On `[1/2, 3/2]`, `Γ` is at most `max Γ(1/2) Γ(3/2)` (convexity). -/
theorem Gamma_le_max_of_mem_Icc {σ : ℝ} (hσ : σ ∈ Set.Icc (1/2 : ℝ) (3/2)) :
    Real.Gamma σ ≤ max (Real.Gamma (1/2)) (Real.Gamma (3/2)) := by
  have hseg : σ ∈ segment ℝ (1/2 : ℝ) (3/2) := by
    rw [segment_eq_Icc (by norm_num : (1/2 : ℝ) ≤ 3/2)]
    exact hσ
  exact Real.convexOn_Gamma.le_max_of_mem_segment (by norm_num) (by norm_num) hseg

/-- The Phragmén–Lindelöf comparator bound: `‖Γ(z)²·sin(πz)/z²‖ ≤ 4π` on the closed
strip `1/2 ≤ Re z ≤ 3/2`. -/
theorem norm_Gamma_sq_mul_sin_div_le {z : ℂ} (h1 : 1/2 ≤ z.re) (h2 : z.re ≤ 3/2) :
    ‖Complex.Gamma z ^ 2 * Complex.sin (π * z) / z ^ 2‖ ≤ 4 * π := by
  set f : ℂ → ℂ := fun w => Complex.Gamma w ^ 2 * Complex.sin (π * w) / w ^ 2 with hf
  -- nonvanishing of w on the closed strip
  have hne : ∀ w : ℂ, 1/2 ≤ w.re → w ≠ 0 := by
    intro w hw h0
    rw [h0] at hw
    norm_num at hw
  -- differentiable on Re > 0, hence DiffContOnCl on the open strip
  have hdiff : ∀ w : ℂ, 1/2 ≤ w.re → DifferentiableAt ℂ f w := by
    intro w hw
    have hG : DifferentiableAt ℂ Complex.Gamma w := by
      refine Complex.differentiableAt_Gamma w (fun m => ?_)
      intro h0
      have : w.re = -(m : ℝ) := by rw [h0]; simp
      rw [this] at hw
      have : (0:ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact ((hG.pow 2).mul ((Complex.differentiable_sin.comp
      ((differentiable_const _).mul differentiable_id)).differentiableAt)).div
      (differentiableAt_pow 2) (pow_ne_zero 2 (hne w hw))
  -- Γ bounded on the closed strip
  have hM : ∀ w : ℂ, 1/2 ≤ w.re → w.re ≤ 3/2 →
      ‖Complex.Gamma w‖ ≤ max (Real.Gamma (1/2)) (Real.Gamma (3/2)) :=
    fun w hw1 hw2 => le_trans (norm_Gamma_le_Gamma_re (by linarith))
      (Gamma_le_max_of_mem_Icc ⟨hw1, hw2⟩)
  -- |sin(πw)| ≤ cosh(π·Im w) ≤ exp(π·|Im w|)
  have hsin_le : ∀ w : ℂ, ‖Complex.sin (π * w)‖ ≤ Real.exp (π * |w.im|) := by
    intro w
    have hdecomp : (π : ℂ) * w = ((π * w.re : ℝ) : ℂ) + ((π * w.im : ℝ) : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im w]
      push_cast
      ring
    have hsq := norm_sin_add_mul_I_sq (π * w.re) (π * w.im)
    rw [← hdecomp] at hsq
    have hcosh : ‖Complex.sin (π * w)‖^2 ≤ Real.cosh (π * w.im) ^ 2 := by
      rw [hsq, Real.cosh_sq]
      nlinarith [Real.sin_sq_add_cos_sq (π * w.re), sq_nonneg (Real.sin (π * w.re))]
    have h1 : ‖Complex.sin (π * w)‖ ≤ Real.cosh (π * w.im) := by
      nlinarith [norm_nonneg (Complex.sin (π * w)), Real.cosh_pos (π * w.im)]
    refine h1.trans ?_
    rw [show π * |w.im| = |π * w.im| by rw [abs_mul, abs_of_pos Real.pi_pos]]
    rw [Real.cosh_eq]
    have e1 : Real.exp (π * w.im) ≤ Real.exp |π * w.im| :=
      Real.exp_le_exp.mpr (le_abs_self _)
    have e2 : Real.exp (-(π * w.im)) ≤ Real.exp |π * w.im| :=
      Real.exp_le_exp.mpr (neg_le_abs _)
    linarith
  -- norm of sin on the two boundary lines is exactly cosh(π·Im)
  have hsin_line : ∀ w : ℂ, Real.sin (π * w.re) ^ 2 = 1 →
      ‖Complex.sin (π * w)‖ = Real.cosh (π * w.im) := by
    intro w hw
    have hdecomp : (π : ℂ) * w
        = ((π * w.re : ℝ) : ℂ) + ((π * w.im : ℝ) : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im w]
      push_cast
      ring
    have hsq := norm_sin_add_mul_I_sq (π * w.re) (π * w.im)
    rw [← hdecomp] at hsq
    rw [hw] at hsq
    rw [← Real.sqrt_sq (norm_nonneg _), hsq,
      show 1 + Real.sinh (π * w.im) ^ 2 = Real.cosh (π * w.im) ^ 2 by
        rw [Real.cosh_sq]; ring,
      Real.sqrt_sq (Real.cosh_pos _).le]
  -- the exact boundary bounds
  have hbdry_a : ∀ w : ℂ, w.re = 1/2 → ‖f w‖ ≤ 4 * π := by
    intro w hw
    have hweq : w = (1/2 : ℂ) + (w.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hw]
    have hΓ : ‖Complex.Gamma w‖^2 = π / Real.cosh (π * w.im) := by
      conv_lhs => rw [hweq]
      exact norm_Gamma_half_add_mul_I_sq w.im
    have hsin : ‖Complex.sin (π * w)‖ = Real.cosh (π * w.im) := by
      refine hsin_line w ?_
      rw [hw, show π * (1/2 : ℝ) = π/2 by ring, Real.sin_pi_div_two]
      norm_num
    have hwn : (1/2 : ℝ) ≤ ‖w‖ := by
      calc (1/2 : ℝ) = |w.re| := by rw [hw]; norm_num
        _ ≤ ‖w‖ := Complex.abs_re_le_norm w
    have hcosh0 : Real.cosh (π * w.im) ≠ 0 := (Real.cosh_pos _).ne'
    have hw2 : (1/4 : ℝ) ≤ ‖w‖^2 := by nlinarith
    have hw2pos : (0:ℝ) < ‖w‖^2 := lt_of_lt_of_le (by norm_num) hw2
    rw [hf]
    rw [norm_div, norm_mul, norm_pow, norm_pow, hΓ, hsin,
      div_mul_cancel₀ _ hcosh0, div_le_iff₀ hw2pos]
    nlinarith [Real.pi_pos]
  have hbdry_b : ∀ w : ℂ, w.re = 3/2 → ‖f w‖ ≤ 4 * π := by
    intro w hw
    have hwm : w - 1 = (1/2 : ℂ) + (w.im : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [hw]
        norm_num
      · simp
    have hne1 : w - 1 ≠ 0 := by
      intro h0
      rw [h0] at hwm
      have := congrArg Complex.re hwm.symm
      simp at this
    have hrec : Complex.Gamma w = (w - 1) * Complex.Gamma (w - 1) := by
      have := Complex.Gamma_add_one (w - 1) hne1
      rw [sub_add_cancel] at this
      rw [this]
    have hΓ : ‖Complex.Gamma w‖^2
        = ‖w - 1‖^2 * (π / Real.cosh (π * w.im)) := by
      rw [hrec, norm_mul, mul_pow]
      congr 1
      rw [show w - 1 = (1/2 : ℂ) + (w.im : ℂ) * Complex.I from hwm]
      have : ((1/2 : ℂ) + (w.im : ℂ) * Complex.I).im = w.im := by simp
      rw [show ((1/2 : ℂ) + (w.im : ℂ) * Complex.I) = (1/2 : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I from rfl]
      exact norm_Gamma_half_add_mul_I_sq w.im
    have hsin : ‖Complex.sin (π * w)‖ = Real.cosh (π * w.im) := by
      refine hsin_line w ?_
      rw [hw]
      rw [show π * (3/2 : ℝ) = π + π/2 by ring, Real.sin_add]
      simp
    have hcosh0 : Real.cosh (π * w.im) ≠ 0 := (Real.cosh_pos _).ne'
    have hle : ‖w - 1‖^2 ≤ ‖w‖^2 := by
      have h1 : ‖w - 1‖^2 = (1/2)^2 + w.im^2 := by
        rw [hwm]
        rw [show ((1/2 : ℂ) + (w.im : ℂ) * Complex.I) = ((1/2 : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I by push_cast; ring]
        rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
      have h2 : ‖w‖^2 = (3/2)^2 + w.im^2 := by
        have hwe : w = ((3/2 : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [hw]
        conv_lhs => rw [hwe]
        rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
      rw [h1, h2]
      nlinarith
    have hwn : (3/2 : ℝ) ≤ ‖w‖ := by
      calc (3/2 : ℝ) = |w.re| := by rw [hw]; norm_num
        _ ≤ ‖w‖ := Complex.abs_re_le_norm w
    have hw2pos : (0:ℝ) < ‖w‖^2 := by nlinarith
    rw [hf]
    rw [norm_div, norm_mul, norm_pow, norm_pow, hΓ, hsin]
    rw [mul_assoc, div_mul_cancel₀ _ hcosh0, div_le_iff₀ hw2pos]
    nlinarith [Real.pi_pos, sq_nonneg ‖w - 1‖]
  -- differentiability up to the boundary
  have hcl : closure (Complex.re ⁻¹' Set.Ioo (1/2 : ℝ) (3/2))
      ⊆ Complex.re ⁻¹' Set.Icc (1/2 : ℝ) (3/2) :=
    closure_minimal (fun w hw => ⟨le_of_lt hw.1, le_of_lt hw.2⟩)
      (IsClosed.preimage Complex.continuous_re isClosed_Icc)
  have hfd : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo (1/2 : ℝ) (3/2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    intro w hw
    exact (hdiff w (hcl hw).1).differentiableWithinAt
  -- sub-double-exponential growth on the strip
  have hgrow : ∃ c < π / ((3/2 : ℝ) - 1/2), ∃ B,
      f =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop
          ⊓ Filter.principal (Complex.re ⁻¹' Set.Ioo (1/2 : ℝ) (3/2))]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1, ?_, π, ?_⟩
    · rw [show (3/2 : ℝ) - 1/2 = 1 by norm_num, div_one]
      linarith [Real.pi_gt_three]
    refine Asymptotics.IsBigO.of_bound
      (4 * (max (Real.Gamma (1/2)) (Real.Gamma (3/2)))^2) ?_
    rw [Filter.eventually_inf_principal]
    refine Filter.Eventually.of_forall (fun w hw => ?_)
    have hw1 : 1/2 ≤ w.re := le_of_lt hw.1
    have hw2' : w.re ≤ 3/2 := le_of_lt hw.2
    have hΓb := hM w hw1 hw2'
    have hsinb := hsin_le w
    have hwn : (1/2 : ℝ) ≤ ‖w‖ :=
      le_trans (le_trans hw1 (le_abs_self _)) (Complex.abs_re_le_norm w)
    have hw2sq : (1/4 : ℝ) ≤ ‖w‖^2 := by nlinarith
    have hnorm : ‖f w‖ = ‖Complex.Gamma w‖^2 * ‖Complex.sin (π * w)‖ / ‖w‖^2 := by
      rw [hf, norm_div, norm_mul, norm_pow, norm_pow]
    have hexp1 : Real.exp (π * |w.im|) ≤ Real.exp (π * Real.exp |w.im|) := by
      rw [Real.exp_le_exp]
      have : |w.im| ≤ Real.exp |w.im| := by
        linarith [Real.add_one_le_exp |w.im|]
      nlinarith [Real.pi_pos]
    calc ‖f w‖ = ‖Complex.Gamma w‖^2 * ‖Complex.sin (π * w)‖ / ‖w‖^2 := hnorm
      _ ≤ ‖Complex.Gamma w‖^2 * ‖Complex.sin (π * w)‖ / (1/4) := by
          gcongr
      _ = 4 * (‖Complex.Gamma w‖^2 * ‖Complex.sin (π * w)‖) := by ring
      _ ≤ 4 * ((max (Real.Gamma (1/2)) (Real.Gamma (3/2)))^2
            * Real.exp (π * |w.im|)) := by
          gcongr
      _ = 4 * (max (Real.Gamma (1/2)) (Real.Gamma (3/2)))^2
            * Real.exp (π * |w.im|) := by ring
      _ ≤ 4 * (max (Real.Gamma (1/2)) (Real.Gamma (3/2)))^2
            * Real.exp (π * Real.exp (1 * |w.im|)) := by
          rw [one_mul]
          have h4M : (0:ℝ) ≤ 4 * (max (Real.Gamma (1/2)) (Real.Gamma (3/2)))^2 := by
            positivity
          nlinarith [hexp1, Real.exp_pos (π * |w.im|)]
      _ = 4 * (max (Real.Gamma (1/2)) (Real.Gamma (3/2)))^2
            * ‖Real.exp (π * Real.exp (1 * |w.im|))‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  -- Phragmén–Lindelöf
  show ‖f z‖ ≤ 4 * π
  exact PhragmenLindelof.vertical_strip hfd hgrow hbdry_a hbdry_b h1 h2

/-- **Decaying Γ-upper on the base strip** (AC-A1-iii payoff): for `1/2 ≤ σ ≤ 3/2` and
`1 ≤ |t|`, `‖Γ(σ+it)‖ ≤ √(12π)·‖σ+it‖·e^{-π|t|/2}`. -/
theorem norm_Gamma_le_mul_exp {σ t : ℝ} (h1 : 1/2 ≤ σ) (h2 : σ ≤ 3/2) (ht : 1 ≤ |t|) :
    ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.sqrt (12 * π) * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖
        * Real.exp (-(π * |t|) / 2) := by
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz
  have hzre : z.re = σ := by simp [hz]
  have hzim : z.im = t := by simp [hz]
  have hcomp := norm_Gamma_sq_mul_sin_div_le (z := z) (by rw [hzre]; exact h1)
    (by rw [hzre]; exact h2)
  have hzne : z ≠ 0 := by
    intro h0
    rw [h0] at hzim
    simp at hzim
    rw [← hzim] at ht
    norm_num at ht
  -- lower bound for |sin(πz)|
  have hsinh_lower : Real.sinh (π * |t|) ≤ ‖Complex.sin (π * z)‖ := by
    have hdecomp : (π : ℂ) * z
        = ((π * σ : ℝ) : ℂ) + ((π * t : ℝ) : ℂ) * Complex.I := by
      rw [hz]; push_cast; ring
    have hsq := norm_sin_add_mul_I_sq (π * σ) (π * t)
    rw [← hdecomp] at hsq
    have h1' : Real.sinh (π * |t|) = |Real.sinh (π * t)| := by
      rw [show π * |t| = |π * t| by rw [abs_mul, abs_of_pos Real.pi_pos], ← Real.abs_sinh]
    rw [h1']
    have : |Real.sinh (π * t)|^2 ≤ ‖Complex.sin (π * z)‖^2 := by
      rw [hsq, sq_abs]
      nlinarith [sq_nonneg (Real.sin (π * σ))]
    nlinarith [abs_nonneg (Real.sinh (π * t)), norm_nonneg (Complex.sin (π * z))]
  -- sinh(π|t|) ≥ e^{π|t|}/3 for |t| ≥ 1
  have hsinh_exp : Real.exp (π * |t|) / 3 ≤ Real.sinh (π * |t|) := by
    rw [Real.sinh_eq]
    have hx : (3 : ℝ) ≤ Real.exp (π * |t|) := by
      have h4 : (4 : ℝ) ≤ 1 + π * |t| := by nlinarith [Real.pi_gt_three]
      have := Real.add_one_le_exp (π * |t|)
      linarith
    have hpos : 0 < Real.exp (π * |t|) := Real.exp_pos _
    have hinv : Real.exp (-(π * |t|)) = (Real.exp (π * |t|))⁻¹ := by
      rw [Real.exp_neg]
    rw [hinv]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3)] at *
    have hinvle : (Real.exp (π * |t|))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      linarith
    nlinarith [inv_pos.mpr hpos]
  -- assemble: ‖Γ z‖² ≤ 12π‖z‖²e^{-π|t|}
  have hsin_pos : (0:ℝ) < ‖Complex.sin (π * z)‖ := by
    have h3 : (0:ℝ) < Real.sinh (π * |t|) := by
      apply Real.sinh_pos_iff.mpr
      have htpos : (0:ℝ) < |t| := lt_of_lt_of_le one_pos ht
      positivity
    linarith
  have hkey : ‖Complex.Gamma z‖^2
      ≤ 12 * π * ‖z‖^2 * Real.exp (-(π * |t|)) := by
    have hexp : ‖Complex.Gamma z‖^2 * ‖Complex.sin (π * z)‖ / ‖z‖^2 ≤ 4 * π := by
      have hnorm : ‖Complex.Gamma z ^ 2 * Complex.sin (π * z) / z ^ 2‖
          = ‖Complex.Gamma z‖^2 * ‖Complex.sin (π * z)‖ / ‖z‖^2 := by
        rw [norm_div, norm_mul, norm_pow, norm_pow]
      rw [← hnorm]
      exact hcomp
    have hz2 : (0:ℝ) < ‖z‖^2 := by positivity
    rw [div_le_iff₀ hz2] at hexp
    -- ‖Γ‖²·‖sin‖ ≤ 4π‖z‖², and ‖sin‖ ≥ e^{π|t|}/3
    have hchain : Real.exp (π * |t|) / 3 ≤ ‖Complex.sin (π * z)‖ :=
      le_trans hsinh_exp hsinh_lower
    have hΓ2 : (0:ℝ) ≤ ‖Complex.Gamma z‖^2 := by positivity
    have hstep : ‖Complex.Gamma z‖^2 * (Real.exp (π * |t|) / 3) ≤ 4 * π * ‖z‖^2 :=
      le_trans (by nlinarith) hexp
    have hepos : (0:ℝ) < Real.exp (π * |t|) := Real.exp_pos _
    calc ‖Complex.Gamma z‖^2
        = (‖Complex.Gamma z‖^2 * (Real.exp (π * |t|) / 3)) * (3 / Real.exp (π * |t|)) := by
          field_simp
      _ ≤ (4 * π * ‖z‖^2) * (3 / Real.exp (π * |t|)) := by
          have h3e : (0:ℝ) ≤ 3 / Real.exp (π * |t|) := by positivity
          exact mul_le_mul_of_nonneg_right hstep h3e
      _ = 12 * π * ‖z‖^2 * Real.exp (-(π * |t|)) := by
          rw [Real.exp_neg]
          field_simp
          ring
  -- take square roots
  have hRHS : (Real.sqrt (12 * π) * ‖z‖ * Real.exp (-(π * |t|) / 2))^2
      = 12 * π * ‖z‖^2 * Real.exp (-(π * |t|)) := by
    have hsq : Real.sqrt (12 * π)^2 = 12 * π := Real.sq_sqrt (by positivity)
    have hexp2 : Real.exp (-(π * |t|) / 2)^2 = Real.exp (-(π * |t|)) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [mul_pow, mul_pow, hsq, hexp2]
  calc ‖Complex.Gamma z‖ = Real.sqrt (‖Complex.Gamma z‖^2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt ((Real.sqrt (12 * π) * ‖z‖ * Real.exp (-(π * |t|) / 2))^2) := by
        apply Real.sqrt_le_sqrt
        rw [hRHS]
        exact hkey
    _ = Real.sqrt (12 * π) * ‖z‖ * Real.exp (-(π * |t|) / 2) := by
        rw [Real.sqrt_sq (by positivity)]

end

end DedekindResidue
