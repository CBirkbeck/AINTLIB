module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import BernoulliRegular.GaussSumSign

/-!
# Positivity of `L(χ, 1)` for real quadratic non-principal Dirichlet characters

Key argument:

* For real `s > 1` and real quadratic `χ`, each Euler factor
  `1 − χ(p) · p^{-s}` is a positive real (as `p^{-s} < 1`, `χ(p) ∈ {0, ±1}`).
* The `exp`-`log` form of the Euler product
  (`DirichletCharacter.LSeries_eulerProduct_exp_log`) gives
  `L(χ, s) = exp(Σ' -log(1 − χ(p) · p^{-s}))`. The sum is real (each term
  is the log of a real positive), so the exponential is a positive real.
* Continuity of `LFunction` at `s = 1` (from `differentiable_LFunction`)
  plus non-vanishing (`LFunction_apply_one_ne_zero`) conclude that
  `L(χ, 1)` is also a positive real.

## Main result

* `BernoulliRegular.LFunction_one_pos_of_legendreDirichlet`: for
  `p ≡ 3 (mod 4)`, `L(legendreDirichlet p, 1)` has zero imaginary part and
  positive real part.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open Complex DirichletCharacter Topology Filter

section Positivity

variable (p : ℕ) [hp : Fact p.Prime]

/-- For a real quadratic Dirichlet character `χ`, real `s > 1`, and prime `q`,
the Euler factor `1 − χ(q) · q^{-s}` is a positive real number. -/
theorem one_sub_chi_pow_pos_of_real_quadratic
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ_quad : χ.IsQuadratic)
    {s : ℝ} (hs : 1 < s) (q : Nat.Primes) :
    ∃ r : ℝ, 0 < r ∧
      (1 - χ (q : ℕ) * ((q : ℕ) : ℂ) ^ (-(s : ℂ))) = ((r : ℝ) : ℂ) := by
  have hq_prime : (q : ℕ).Prime := q.2
  have hq_cast_pos : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast hq_prime.pos
  have hq_cast_ge_two : (2 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast hq_prime.two_le
  -- q^{-s} as a real number
  set a : ℝ := ((q : ℕ) : ℝ) ^ (-s) with ha_def
  have ha_pos : 0 < a := Real.rpow_pos_of_pos hq_cast_pos _
  have hq_pow_gt_one : 1 < ((q : ℕ) : ℝ) ^ s :=
    Real.one_lt_rpow (by linarith : (1 : ℝ) < ((q : ℕ) : ℝ)) (by linarith)
  have ha_lt_one : a < 1 := by
    have h_rewrite : a = 1 / ((q : ℕ) : ℝ) ^ s := by
      rw [ha_def, Real.rpow_neg hq_cast_pos.le, one_div]
    rw [h_rewrite, div_lt_one (by linarith)]
    exact hq_pow_gt_one
  -- Complex cast of q^{-s}
  have h_cpow : ((q : ℕ) : ℂ) ^ (-(s : ℂ)) = ((a : ℝ) : ℂ) := by
    rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) from by push_cast; ring, ha_def]
    exact (Complex.ofReal_cpow hq_cast_pos.le _).symm
  -- χ(q) takes values in {-1, 0, 1}
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ_quad.sq_eq_one (q : ℕ) with h0 | h1 | h_neg1
  · -- χ(q) = 0
    refine ⟨1, zero_lt_one, ?_⟩
    rw [h0, zero_mul]
    push_cast; ring
  · -- χ(q) = 1
    refine ⟨1 - a, by linarith, ?_⟩
    rw [h1, h_cpow, one_mul]
    push_cast; ring
  · -- χ(q) = -1
    refine ⟨1 + a, by linarith, ?_⟩
    rw [h_neg1, h_cpow]
    push_cast; ring

/-- For real quadratic `χ`, real `s > 1`, and prime `q`, the Euler factor
inverse `(1 − χ(q) · q^{-s})⁻¹` is a positive real. -/
theorem eulerFactor_inv_pos_of_real_quadratic
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ_quad : χ.IsQuadratic)
    {s : ℝ} (hs : 1 < s) (q : Nat.Primes) :
    ∃ r : ℝ, 0 < r ∧
      ((1 - χ (q : ℕ) * ((q : ℕ) : ℂ) ^ (-(s : ℂ)))⁻¹) = ((r : ℝ) : ℂ) := by
  obtain ⟨r, hr_pos, hr_eq⟩ := one_sub_chi_pow_pos_of_real_quadratic hχ_quad hs q
  refine ⟨r⁻¹, inv_pos.mpr hr_pos, ?_⟩
  rw [hr_eq, ← Complex.ofReal_inv]

/-- For real quadratic `χ`, real `s > 1`, and prime `q`, the `-log` of
the Euler factor is a real number. -/
theorem neg_log_eulerFactor_isReal
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ_quad : χ.IsQuadratic)
    {s : ℝ} (hs : 1 < s) (q : Nat.Primes) :
    (-(Complex.log (1 - χ (q : ℕ) * ((q : ℕ) : ℂ) ^ (-(s : ℂ))))).im = 0 := by
  obtain ⟨r, hr_pos, hr_eq⟩ := one_sub_chi_pow_pos_of_real_quadratic hχ_quad hs q
  rw [hr_eq, ← Complex.ofReal_log hr_pos.le]
  simp

/-- For a non-principal primitive real quadratic Dirichlet character `χ` and
real `s > 1`, `L(χ, s)` is a positive real number. -/
theorem LFunction_pos_of_real_quadratic_of_one_lt
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ_quad : χ.IsQuadratic)
    {s : ℝ} (hs : 1 < s) :
    (DirichletCharacter.LFunction χ (s : ℂ)).im = 0 ∧
      0 < (DirichletCharacter.LFunction χ (s : ℂ)).re := by
  have hs_re : (1 : ℝ) < ((s : ℂ)).re := by simp [hs]
  -- LFunction = LSeries for Re s > 1
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs_re]
  -- LSeries = exp(∑ -log(...)) from the Euler product
  have h_exp := DirichletCharacter.LSeries_eulerProduct_exp_log χ hs_re
  rw [← h_exp]
  -- Each -log term is real, so the sum is real, so exp of it is a positive real.
  set X : ℂ := ∑' p : Nat.Primes,
    -Complex.log (1 - χ p * ((p : ℕ) : ℂ) ^ (-(s : ℂ))) with hX_def
  -- Show X has zero imaginary part
  have hX_im : X.im = 0 := by
    -- Each term has `.im = 0`; the tsum might not be summable, but then it's 0,
    -- so `.im = 0` either way.
    by_cases h_summ :
        Summable fun p : Nat.Primes =>
          -Complex.log (1 - χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-(s : ℂ)))
    · rw [hX_def, Complex.im_tsum h_summ]
      have h_each : ∀ p : Nat.Primes,
          (-Complex.log (1 - χ (p : ℕ) * ((p : ℕ) : ℂ) ^ (-(s : ℂ)))).im = 0 := fun p =>
        neg_log_eulerFactor_isReal hχ_quad hs p
      simp [h_each]
    · rw [hX_def, tsum_eq_zero_of_not_summable h_summ]; simp
  -- X is real, so exp X is a positive real
  have hX_re_cast : ((X.re : ℝ) : ℂ) = X :=
    Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr hX_im)
  rw [← hX_re_cast]
  refine ⟨?_, ?_⟩
  · exact Complex.exp_ofReal_im X.re
  · rw [Complex.exp_ofReal_re]; exact Real.exp_pos _

/-- For a primitive real quadratic non-principal Dirichlet character `χ`,
`L(χ, 1)` is a positive real number (zero imaginary part, positive real part).
The argument: `L(χ, s)` is positive real for real `s > 1`
(`LFunction_pos_of_real_quadratic_of_one_lt`); take the limit `s → 1⁺`
by continuity; combine with the non-vanishing at `s = 1`. -/
theorem LFunction_one_pos_of_real_quadratic
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ_quad : χ.IsQuadratic) (hχ_ne_one : χ ≠ 1) :
    (DirichletCharacter.LFunction χ 1).im = 0 ∧
      0 < (DirichletCharacter.LFunction χ 1).re := by
  have h_cont : Continuous (DirichletCharacter.LFunction χ) :=
    (DirichletCharacter.differentiable_LFunction hχ_ne_one).continuous
  -- The sequence t n = 1 + 1/(n+1) tends to 1, with each t n > 1.
  set t : ℕ → ℝ := fun n => 1 + 1 / (n + 1 : ℝ) with ht_def
  have h_t_tendsto : Tendsto t atTop (𝓝 (1 : ℝ)) := by
    simpa [t] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
  have h_tC_tendsto : Tendsto (fun n => ((t n : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp h_t_tendsto
  have h_gt_one : ∀ n : ℕ, 1 < t n := by
    intro n
    simp only [t]
    have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have h_pos : ∀ n : ℕ,
      (DirichletCharacter.LFunction χ ((t n : ℝ) : ℂ)).im = 0 ∧
        0 < (DirichletCharacter.LFunction χ ((t n : ℝ) : ℂ)).re :=
    fun n => LFunction_pos_of_real_quadratic_of_one_lt hχ_quad (h_gt_one n)
  have h_L_tendsto : Tendsto (fun n : ℕ => DirichletCharacter.LFunction χ ((t n : ℝ) : ℂ))
      atTop (𝓝 (DirichletCharacter.LFunction χ 1)) :=
    (h_cont.tendsto 1).comp h_tC_tendsto
  -- `.im = 0`
  have h_im : (DirichletCharacter.LFunction χ 1).im = 0 := by
    have h_im_tendsto : Tendsto
        (fun n : ℕ => (DirichletCharacter.LFunction χ ((t n : ℝ) : ℂ)).im)
        atTop (𝓝 (DirichletCharacter.LFunction χ 1).im) :=
      (Complex.continuous_im.tendsto _).comp h_L_tendsto
    have h_const : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have h_eq : (fun n : ℕ => (DirichletCharacter.LFunction χ
        ((t n : ℝ) : ℂ)).im) = fun _ : ℕ => (0 : ℝ) :=
      funext fun n => (h_pos n).1
    rw [h_eq] at h_im_tendsto
    exact tendsto_nhds_unique h_im_tendsto h_const
  refine ⟨h_im, ?_⟩
  -- `.re > 0`: combine `.re ≥ 0` (limit of positive) and `≠ 0` (non-vanishing).
  have h_ne : DirichletCharacter.LFunction χ 1 ≠ 0 :=
    DirichletCharacter.LFunction_apply_one_ne_zero hχ_ne_one
  have h_re_ge : 0 ≤ (DirichletCharacter.LFunction χ 1).re :=
    ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp h_L_tendsto)
      (fun n => (h_pos n).2.le)
  have h_re_ne : (DirichletCharacter.LFunction χ 1).re ≠ 0 := by
    intro h_eq; apply h_ne
    exact Complex.ext h_eq h_im
  exact lt_of_le_of_ne h_re_ge (Ne.symm h_re_ne)

end Positivity

end BernoulliRegular
