module

public import BernoulliRegular.LValueAtOne.Defs

/-!
# Trigonometric and Abel-summation lemmas for `LValueAtOne`

This file collects the residue-class rewrites and complex logarithm boundary
identities shared by the odd and even `L(1, χ)` formulas.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace BernoulliRegular

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

/-- The standard real representative of `a : ZMod p` lies in the closed unit
interval after dividing by `p`. -/
lemma zmod_val_div_prime_mem_Icc (a : ZMod p) :
    (a.val / p : ℝ) ∈ Set.Icc 0 1 := by
  have hp_pos : 0 < p := hp.out.pos
  refine Set.mem_Icc.mpr ⟨by positivity, ?_⟩
  exact (div_le_one (Nat.cast_pos.mpr hp_pos)).mpr <| Nat.cast_le.mpr (ZMod.val_lt a).le

/-- For a nonzero residue `a : ZMod p`, the standard real representative lies
strictly between `0` and `1` after dividing by `p`. -/
lemma zmod_val_div_prime_mem_Ioo {a : ZMod p} (ha : a ≠ 0) :
    (a.val / p : ℝ) ∈ Set.Ioo 0 1 := by
  have hp_pos : 0 < p := hp.out.pos
  have hval_pos : 0 < a.val := by
    by_contra h
    have hval_zero : a.val = 0 := Nat.eq_zero_of_not_pos h
    exact ha <| (ZMod.val_eq_zero a).mp hval_zero
  refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
  · exact div_pos (Nat.cast_pos.mpr hval_pos) (Nat.cast_pos.mpr hp_pos)
  · exact (div_lt_one (Nat.cast_pos.mpr hp_pos)).2 <| Nat.cast_lt.mpr (ZMod.val_lt a)

/-- A nonzero residue class gives a nonzero point of `UnitAddCircle`. -/
lemma zmod_toAddCircle_ne_zero {a : ZMod p} (ha : a ≠ 0) :
    ZMod.toAddCircle a ≠ 0 := by
  simpa [ZMod.toAddCircle_eq_zero] using ha

/-- Rewrite `hurwitzZetaOdd` at `ZMod.toAddCircle a` using the standard real
representative `a.val / p`. -/
lemma hurwitzZetaOdd_toAddCircle_eq_val_div_prime (a : ZMod p) (s : ℂ) :
    HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle a) s =
      HurwitzZeta.hurwitzZetaOdd (a.val / p : ℝ) s := by
  rw [ZMod.toAddCircle_apply]

/-- Rewrite `sinZeta` at `ZMod.toAddCircle a` using the standard real
representative `a.val / p`. -/
lemma sinZeta_toAddCircle_eq_val_div_prime (a : ZMod p) (s : ℂ) :
    HurwitzZeta.sinZeta (ZMod.toAddCircle a) s = HurwitzZeta.sinZeta (a.val / p : ℝ) s := by
  rw [ZMod.toAddCircle_apply]

/-- Rewriting `1 - e^{it}` in polar form on the upper unit semicircle. -/
lemma one_sub_exp_ofReal_mul_I (t : ℝ) :
    (1 : ℂ) - Complex.exp (t * Complex.I) =
      (2 * Real.sin (t / 2) : ℝ) *
        (Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I) := by
  calc
    (1 : ℂ) - Complex.exp (t * Complex.I)
        = ((1 - Real.cos t : ℝ) : ℂ) + (-Real.sin t : ℝ) * Complex.I := by
            rw [Complex.exp_ofReal_mul_I]
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = ((2 * Real.sin (t / 2) ^ 2 : ℝ) : ℂ) +
          (-(2 * Real.sin (t / 2) * Real.cos (t / 2)) : ℝ) * Complex.I := by
            rw [show t = 2 * (t / 2) by ring, Real.cos_two_mul, Real.sin_two_mul]
            have hsq : 1 - (2 * Real.cos (t / 2) ^ 2 - 1) = 2 * Real.sin (t / 2) ^ 2 := by
              nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
            rw [hsq]
            ring_nf
    _ = (2 * Real.sin (t / 2) : ℝ) *
          (Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I) := by
            simp [Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, sq]
            ring

/-- The principal argument of `1 - e^{it}` for `0 < t < 2π`. -/
lemma arg_one_sub_exp_ofReal_mul_I {t : ℝ} (ht₀ : 0 < t) (ht₂π : t < 2 * Real.pi) :
    Complex.arg ((1 : ℂ) - Complex.exp (t * Complex.I)) = t / 2 - Real.pi / 2 := by
  have hs : 0 < 2 * Real.sin (t / 2) := by
    have hhalf : 0 < t / 2 ∧ t / 2 < Real.pi := by
      constructor <;> nlinarith [ht₀, ht₂π, Real.pi_pos]
    have hsin : 0 < Real.sin (t / 2) := Real.sin_pos_of_mem_Ioo hhalf
    positivity
  have hθ : t / 2 - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · nlinarith [ht₀, Real.pi_pos]
    · nlinarith [ht₂π]
  rw [one_sub_exp_ofReal_mul_I]
  simpa using (Complex.arg_mul_cos_add_sin_mul_I hs hθ)

/-- The logarithm in the Abel sum formula has the expected boundary imaginary part. -/
lemma neg_log_one_sub_exp_ofReal_mul_I_im {t : ℝ} (ht₀ : 0 < t) (ht₂π : t < 2 * Real.pi) :
    (-Complex.log ((1 : ℂ) - Complex.exp (t * Complex.I))).im = Real.pi / 2 - t / 2 := by
  rw [show (-Complex.log ((1 : ℂ) - Complex.exp (t * Complex.I))).im =
      -(Complex.log ((1 : ℂ) - Complex.exp (t * Complex.I))).im by simp]
  rw [Complex.log_im, arg_one_sub_exp_ofReal_mul_I ht₀ ht₂π]
  ring

/-- Abel summation identity for the damped sine series attached to `sinZeta` at `s = 1`. -/
lemma hasSum_mul_rpow_sin (x r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    HasSum (fun n : ℕ ↦ (r ^ n / n) * Real.sin (2 * Real.pi * x * n))
      (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im := by
  let z : ℂ := (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz : ‖z‖ < 1 := by
    have hexp : ‖Complex.exp (2 * Real.pi * x * Complex.I)‖ = 1 := by
      simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
    have hz' : ‖z‖ = r := by
      calc
        ‖z‖ = ‖(r : ℂ)‖ * ‖Complex.exp (2 * Real.pi * x * Complex.I)‖ := by
          simp [z]
        _ = r * 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hr₀, hexp]
        _ = r := by ring
    rw [hz']
    exact hr₁
  refine (Complex.hasSum_im (Complex.hasSum_taylorSeries_neg_log hz)).congr_fun ?_
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [z]
  · rw [show z = (r : ℂ) * Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) by simp [z]]
    rw [Complex.div_natCast_im, mul_pow, Complex.mul_im, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, ← Complex.exp_nat_mul]
    rw [show (n : ℂ) * ((2 * Real.pi * x : ℝ) * Complex.I) =
        ((2 * Real.pi * x * n : ℝ) : ℂ) * Complex.I by
          norm_num
          ring]
    rw [Complex.exp_ofReal_mul_I_im]
    ring

/-- Abel summation identity for the damped cosine series attached to `cosZeta` at `s = 1`. -/
lemma hasSum_mul_rpow_cos (x r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    HasSum (fun n : ℕ ↦ (r ^ n / n) * Real.cos (2 * Real.pi * x * n))
      (-Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖) := by
  let z : ℂ := (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz : ‖z‖ < 1 := by
    have hexp : ‖Complex.exp (2 * Real.pi * x * Complex.I)‖ = 1 := by
      simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
    have hz' : ‖z‖ = r := by
      calc
        ‖z‖ = ‖(r : ℂ)‖ * ‖Complex.exp (2 * Real.pi * x * Complex.I)‖ := by
          simp [z]
        _ = r * 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hr₀, hexp]
        _ = r := by ring
    rw [hz']
    exact hr₁
  have hsum :
      HasSum (fun n : ℕ ↦ (z ^ n / n).re) (-Complex.log ((1 : ℂ) - z)).re :=
    (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz))
  have hsum' :
      HasSum (fun n : ℕ ↦ (r ^ n / n) * Real.cos (2 * Real.pi * x * n))
        (-Complex.log ((1 : ℂ) - z)).re := by
    refine hsum.congr_fun ?_
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [z]
    · rw [show z = (r : ℂ) * Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) by simp [z]]
      rw [Complex.div_natCast_re, mul_pow, Complex.mul_re, ← Complex.ofReal_pow,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, ← Complex.exp_nat_mul]
      rw [show (n : ℂ) * ((2 * Real.pi * x : ℝ) * Complex.I) =
          ((2 * Real.pi * x * n : ℝ) : ℂ) * Complex.I by
            norm_num
            ring]
      rw [Complex.exp_ofReal_mul_I_re]
      ring
  have hvalue : (-Complex.log ((1 : ℂ) - z)).re = -Real.log ‖(1 : ℂ) - z‖ := by
    simpa using congrArg Neg.neg (Complex.log_re ((1 : ℂ) - z))
  simpa [hvalue, z] using hsum'

/-- The norm of `1 - e^{it}` on the upper unit semicircle. -/
lemma norm_one_sub_exp_ofReal_mul_I {t : ℝ} (ht₀ : 0 < t) (ht₂π : t < 2 * Real.pi) :
    ‖(1 : ℂ) - Complex.exp (t * Complex.I)‖ = 2 * Real.sin (t / 2) := by
  have hs : 0 < 2 * Real.sin (t / 2) := by
    have hhalf : 0 < t / 2 ∧ t / 2 < Real.pi := by
      constructor <;> nlinarith [ht₀, ht₂π, Real.pi_pos]
    have hsin : 0 < Real.sin (t / 2) := Real.sin_pos_of_mem_Ioo hhalf
    positivity
  calc
    ‖(1 : ℂ) - Complex.exp (t * Complex.I)‖
        = ‖((2 * Real.sin (t / 2) : ℝ) : ℂ)‖ *
            ‖Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I‖ := by
              rw [one_sub_exp_ofReal_mul_I, Complex.norm_mul]
    _ = |2 * Real.sin (t / 2)| * 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          have hunit :
              ‖Real.cos (t / 2 - Real.pi / 2) +
                  Real.sin (t / 2 - Real.pi / 2) * Complex.I‖ = 1 := by
            simpa using Complex.norm_cos_add_sin_mul_I (t / 2 - Real.pi / 2)
          rw [hunit]
    _ = 2 * Real.sin (t / 2) := by rw [abs_of_pos hs, mul_one]

end LValueAtOne

end BernoulliRegular
