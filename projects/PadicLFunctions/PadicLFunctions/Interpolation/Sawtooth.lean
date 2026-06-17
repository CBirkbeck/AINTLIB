/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The sawtooth boundary value and `hurwitzZeta` at `s = 0`

The classical conditionally-convergent evaluation `∑_{n≥1} sin(2πnx)/n =
π(1/2 − x)` for `x ∈ (0,1)` (Abel limit + Dirichlet's test), packaged as
`sinZeta_one_eq_boundary`, and its consequence through the functional
equation: the value `hurwitzZeta x 0 = −B₁(x)` for `x ∈ (0,1)`
(`hurwitzZeta_neg_nat_of_mem_Ioo` extends mathlib's `hurwitzZeta_neg_nat`
to `k = 0`, closing the TODO recorded there, for interior `x`).

This is the missing ingredient for the `k = 0` case of the complex bridge
`L(χ, −k) = −B_{k+1,χ}/(k+1)` (`GenBernoulliComplex.lean`). Ported from the
author's `flt-regular-bernoulli` project (`BernoulliRegular/LValueAtOne/
{DirichletBounds, ComplexBounds, Sine}.lean`), generalised away from the
prime-modulus wrappers; provenance recorded in `.mathlib-quality/plan.md`
(survey addendum).
-/

noncomputable section

open Filter
open scoped Topology

namespace PadicLFunctions

/-! ### Dirichlet-test partial-sum bounds -/

/-- Summation by parts bound for a weighted series with bounded partial sums. -/
lemma norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℕ → ℝ} {z : ℕ → E} {B : ℝ}
    (ha : Antitone a) (ha_nonneg : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, a i • z i‖ ≤ B * a 0 := by
  have hB : 0 ≤ B := by
    simpa using hbound 0
  rcases n.eq_zero_or_pos with rfl | hn
  · have : 0 ≤ B * a 0 := mul_nonneg hB (ha_nonneg 0)
    simpa using this
  · rw [Finset.sum_range_by_parts (f := a) (g := z) (n := n)]
    have hsum_le :
        ‖∑ i ∈ Finset.range (n - 1),
            (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖ ≤
          B * (a 0 - a (n - 1)) := by
      calc
        ‖∑ i ∈ Finset.range (n - 1),
            (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖
            ≤ ∑ i ∈ Finset.range (n - 1),
                ‖(a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖ := by
              simpa using norm_sum_le (Finset.range (n - 1))
                (fun i => (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j)
        _ ≤ ∑ i ∈ Finset.range (n - 1), B * (a i - a (i + 1)) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hdiff_nonpos : a (i + 1) - a i ≤ 0 := sub_nonpos.mpr (ha (Nat.le_succ i))
              calc
                ‖(a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖
                    = |a (i + 1) - a i| * ‖∑ j ∈ Finset.range (i + 1), z j‖ := by
                        rw [norm_smul, Real.norm_eq_abs]
                _ = (a i - a (i + 1)) * ‖∑ j ∈ Finset.range (i + 1), z j‖ := by
                      rw [abs_of_nonpos hdiff_nonpos]
                      ring
                _ ≤ (a i - a (i + 1)) * B := by
                      gcongr
                      · exact sub_nonneg.mpr (ha (Nat.le_succ i))
                      · exact hbound (i + 1)
                _ = B * (a i - a (i + 1)) := by ring
        _ = B * (a 0 - a (n - 1)) := by
              rw [← Finset.mul_sum]
              have htel : ∑ i ∈ Finset.range (n - 1), (a i - a (i + 1)) = a 0 - a (n - 1) := by
                have htel' := Finset.sum_range_sub (f := a) (n := n - 1)
                calc
                  ∑ i ∈ Finset.range (n - 1), (a i - a (i + 1))
                      = ∑ i ∈ Finset.range (n - 1), -((a (i + 1) - a i)) := by
                          refine Finset.sum_congr rfl fun i hi => by ring
                  _ = -∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) := by
                        rw [Finset.sum_neg_distrib]
                  _ = a 0 - a (n - 1) := by linarith
              rw [htel]
    have hfirst : ‖a (n - 1) • ∑ i ∈ Finset.range n, z i‖ ≤ B * a (n - 1) := by
      calc
        ‖a (n - 1) • ∑ i ∈ Finset.range n, z i‖
            = |a (n - 1)| * ‖∑ i ∈ Finset.range n, z i‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ = a (n - 1) * ‖∑ i ∈ Finset.range n, z i‖ := by
          rw [abs_of_nonneg (ha_nonneg _)]
        _ ≤ a (n - 1) * B := by
          gcongr
          · exact ha_nonneg _
          · exact hbound n
        _ = B * a (n - 1) := by ring
    calc
      ‖a (n - 1) • ∑ i ∈ Finset.range n, z i -
          ∑ i ∈ Finset.range (n - 1),
            (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖
          ≤ ‖a (n - 1) • ∑ i ∈ Finset.range n, z i‖ +
              ‖∑ i ∈ Finset.range (n - 1),
                  (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖ := by
              simpa [sub_eq_add_neg] using
                (norm_sub_le (a (n - 1) • ∑ i ∈ Finset.range n, z i)
                  (∑ i ∈ Finset.range (n - 1),
                    (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j))
      _ ≤ B * a (n - 1) + B * (a 0 - a (n - 1)) := add_le_add hfirst hsum_le
      _ = B * a 0 := by ring

/-- Partial sums over a shifted sequence are controlled by the same bound up to a factor `2`. -/
lemma norm_sum_range_shift_le_of_bounded
    {E : Type*} [NormedAddCommGroup E]
    {z : ℕ → E} {B : ℝ}
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (m n : ℕ) :
    ‖∑ i ∈ Finset.range n, z (m + i)‖ ≤ 2 * B := by
  have hshift :
      ∑ i ∈ Finset.range n, z (m + i) =
        ∑ i ∈ Finset.range (m + n), z i - ∑ i ∈ Finset.range m, z i := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm, add_left_comm, add_assoc] using (Finset.sum_range_add z m n).symm
  rw [hshift]
  calc
    ‖∑ i ∈ Finset.range (m + n), z i - ∑ i ∈ Finset.range m, z i‖
        ≤ ‖∑ i ∈ Finset.range (m + n), z i‖ + ‖∑ i ∈ Finset.range m, z i‖ := by
            simpa [sub_eq_add_neg] using
              (norm_sub_le (∑ i ∈ Finset.range (m + n), z i) (∑ i ∈ Finset.range m, z i))
    _ ≤ B + B := add_le_add (hbound _) (hbound _)
    _ = 2 * B := by ring

/-- Tail sums of a weighted series inherit the same summation-by-parts bound. -/
lemma norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℕ → ℝ} {z : ℕ → E} {B : ℝ}
    (ha : Antitone a) (ha_nonneg : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (m n : ℕ) :
    ‖∑ i ∈ Finset.range n, a (m + i) • z (m + i)‖ ≤ (2 * B) * a m := by
  simpa [two_mul, add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_comm, mul_left_comm,
    mul_assoc] using
    (norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded
      (a := fun k => a (m + k)) (z := fun k => z (m + k)) (B := 2 * B)
      (ha := fun i j hij => ha (Nat.add_le_add_left hij m))
      (ha_nonneg := fun k => ha_nonneg (m + k))
      (hbound := fun k => norm_sum_range_shift_le_of_bounded (z := z) (B := B) hbound m k) n)

/-! ### Polar bounds for `1 − e^{it}` and the Abel sums -/

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
    HasSum (fun n : ℕ => (r ^ n / n) * Real.sin (2 * Real.pi * x * n))
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

/-! ### The sine boundary chain -/

/-- Partial sums of the sine kernel stay uniformly bounded away from the endpoints. -/
lemma norm_sum_range_sin_le {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * i)‖ ≤
      2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
  let z : ℂ := Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz_ne_one : z ≠ 1 := by
    intro hz
    have hexp : Complex.exp ((2 * Real.pi * x) * Complex.I) = 1 := by simpa [z] using hz
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
    have him : 2 * Real.pi * x = (m : ℝ) * (2 * Real.pi) := by
      simpa using congrArg Complex.im hm
    have hm_pos : (0 : ℝ) < m := by nlinarith [Real.pi_pos, hx₀, him]
    have hm_lt_one : (m : ℝ) < 1 := by nlinarith [Real.pi_pos, hx₁, him]
    have hm_pos_int : 0 < m := by exact_mod_cast hm_pos
    have hm_lt_one_int : m < 1 := by exact_mod_cast hm_lt_one
    omega
  have him :
      ((∑ i ∈ Finset.range n, z ^ i).im : ℝ) =
        ∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * i) := by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show z ^ i = Complex.exp (((2 * Real.pi * x * i : ℝ) : ℂ) * Complex.I) by
      rw [← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring, Complex.exp_ofReal_mul_I_im]
  have hgeom :
      ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ 2 / ‖z - 1‖ := by
    calc
      ‖∑ i ∈ Finset.range n, z ^ i‖ = ‖(z ^ n - 1) / (z - 1)‖ := by
        rw [geom_sum_eq hz_ne_one]
      _ = ‖z ^ n - 1‖ / ‖z - 1‖ := by rw [Complex.norm_div]
      _ ≤ 2 / ‖z - 1‖ := by
        have hden : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne_one)
        have hnum : ‖z ^ n - 1‖ ≤ 2 := by
          calc
            ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 1 + 1 := by
              rw [norm_pow]
              have hz_norm : ‖z‖ = 1 := by
                simpa [z] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
              rw [hz_norm]
              simp
            _ = 2 := by norm_num
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
  calc
    ‖∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * i)‖
      = ‖((∑ i ∈ Finset.range n, z ^ i).im : ℝ)‖ := by rw [him]
    _ ≤ ‖∑ i ∈ Finset.range n, z ^ i‖ := by
      simpa using (RCLike.norm_im_le_norm (∑ i ∈ Finset.range n, z ^ i))
    _ ≤ 2 / ‖z - 1‖ := hgeom
    _ = 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
      simp [z, norm_sub_rev]

/-- Continuity in the exponent of a single shifted sine term. -/
lemma continuous_shiftedSinTerm (x : ℝ) (i : ℕ) :
    Continuous fun s : ℝ =>
      Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)) := by
  refine Continuous.div continuous_const ?_ ?_
  · exact Continuous.const_cpow Complex.continuous_ofReal (Or.inl (Nat.cast_add_one_ne_zero i))
  · intro s h
    exact (Nat.cast_add_one_ne_zero i) ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- Repackage `hasSum_nat_sinZeta` with the harmless zero term removed. -/
lemma hasSum_shifted_sinZeta (x s : ℝ) (hs : 1 < s) :
    HasSum (fun n : ℕ => Real.sin (2 * Real.pi * x * (n + 1)) / ((n + 1 : ℂ) ^ (s : ℂ)))
      (HurwitzZeta.sinZeta x s) := by
  let f : ℕ → ℂ := fun n => Real.sin (2 * Real.pi * x * n) / ((n : ℂ) ^ (s : ℂ))
  have hfull : HasSum f (HurwitzZeta.sinZeta x s) := by
    simpa [f] using HurwitzZeta.hasSum_nat_sinZeta x (show 1 < ((s : ℂ)).re by simpa)
  have hshift : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ, f (n + 1)) :=
    ((summable_nat_add_iff 1).2 hfull.summable).hasSum
  have hfull' : HasSum f (f 0 + ∑' n : ℕ, f (n + 1)) := hshift.zero_add
  have hvalue : (∑' n : ℕ, f (n + 1)) = HurwitzZeta.sinZeta x s := by
    have := tendsto_nhds_unique hfull'.tendsto_sum_nat hfull.tendsto_sum_nat
    simpa [f, hs.ne'] using this
  exact hvalue ▸ hshift.congr_fun (fun n => by simp [f])

/-- Uniform tail bound for the shifted sine Dirichlet series on the half-line `s ≥ 1`. -/
lemma norm_sum_range_shifted_sin_term_le {x s : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (hs : 1 ≤ s)
    (m n : ℕ) :
    ‖∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (m + i + 1)) / (((m + i + 1 : ℕ) : ℂ) ^ (s : ℂ))‖ ≤
      (4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) *
        (1 / (m + 1 : ℝ) ^ s) := by
  let a : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ) ^ s
  let z : ℕ → ℂ := fun k => Real.sin (2 * Real.pi * x * (k + 1))
  have ha : Antitone a := by
    intro i j hij
    have hij' : (i + 1 : ℝ) ≤ j + 1 := by exact_mod_cast Nat.succ_le_succ hij
    have hi_pos : 0 < (i + 1 : ℝ) := by positivity
    have hs_nonneg : 0 ≤ s := le_trans zero_lt_one.le hs
    have hpow : (i + 1 : ℝ) ^ s ≤ (j + 1 : ℝ) ^ s :=
      Real.rpow_le_rpow hi_pos.le hij' hs_nonneg
    simpa [a, one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hi_pos _) hpow
  have ha_nonneg : ∀ k, 0 ≤ a k := by
    intro k
    positivity
  have hzbound :
      ∀ k, ‖∑ i ∈ Finset.range k, z i‖ ≤
        2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
    intro k
    have hsum :
        ∑ i ∈ Finset.range k, Real.sin (2 * Real.pi * x * (i + 1)) =
          ∑ i ∈ Finset.range (k + 1), Real.sin (2 * Real.pi * x * i) := by
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
        (Finset.sum_range_add (fun i => Real.sin (2 * Real.pi * x * i)) 1 k).symm
    rw [show (∑ i ∈ Finset.range k, z i) =
        ((∑ i ∈ Finset.range k, Real.sin (2 * Real.pi * x * (i + 1)) : ℝ) : ℂ) by
          simp [z, Complex.ofReal_sum]]
    rw [Complex.norm_real, hsum]
    exact norm_sum_range_sin_le hx₀ hx₁ (k + 1)
  calc
    ‖∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (m + i + 1)) / (((m + i + 1 : ℕ) : ℂ) ^ (s : ℂ))‖
        = ‖∑ i ∈ Finset.range n, a (m + i) • z (m + i)‖ := by
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            have hcpow :
                (((m + i + 1 : ℕ) : ℂ) ^ (s : ℂ)) =
                  ((((m + i + 1 : ℕ) : ℝ) ^ s : ℝ) : ℂ) := by
              simpa using
                (Complex.ofReal_cpow (x := (m + i + 1 : ℝ)) (by positivity) (y := s)).symm
            rw [hcpow]
            simp [a, z, div_eq_mul_inv, mul_comm, mul_left_comm]
    _ ≤ (2 * (2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) * a m :=
          norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded ha ha_nonneg hzbound m n
    _ = (4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
          * (1 / (m + 1 : ℝ) ^ s) := by
          have hcoef :
              (2 * (2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) =
                4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
            ring
          rw [hcoef]

/-- The endpoint sine series converges on `(0, 1)` by Dirichlet's test. -/
lemma exists_tendsto_sum_range_sin_div_nat {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    ∃ l : ℝ,
      Tendsto
        (fun n ↦ ∑ i ∈ Finset.range n,
          if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i)
        atTop (𝓝 l) := by
  let f : ℕ → ℝ := fun n => if n = 0 then 1 else 1 / n
  let z : ℕ → ℝ := fun n => if n = 0 then 0 else Real.sin (2 * Real.pi * x * n)
  have hf : Antitone f := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp [f]
      · simp [f, hb.ne']
        have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast Nat.succ_le_of_lt hb
        simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hb1
    · have hb : 0 < b := lt_of_lt_of_le ha hab
      simp [f, ha.ne', (Nat.ne_of_gt hb)]
      have ha' : (0 : ℝ) < a := by exact_mod_cast ha
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      simpa [one_div] using one_div_le_one_div_of_le ha' hab'
  have hf0 : Tendsto f atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa [f]
      using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0))
  have hpartial :
      ∀ n, ∑ i ∈ Finset.range n, z i
        = ∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * i) := by
    intro n
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [z]
    · simp [z, hi.ne']
  have hbound :
      ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤
        2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
    intro n
    rw [hpartial]
    exact norm_sum_range_sin_le hx₀ hx₁ n
  have hcauchy := hf.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hbound
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨l, ?_⟩
  have hseries :
      (fun n ↦ ∑ i ∈ Finset.range n, f i • z i) =
        fun n ↦ ∑ i ∈ Finset.range n,
          if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i := by
    funext n
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [f, z]
    · simp [f, z, hi.ne', smul_eq_mul, div_eq_mul_inv, mul_comm]
  exact hseries ▸ hl

/-- The endpoint sine series converges to the classical boundary value
`π * (1 / 2 - x)` on `(0, 1)`. -/
lemma tendsto_sum_range_sin_div_nat {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i)
      atTop (𝓝 (Real.pi * (1 / 2 - x))) := by
  obtain ⟨l, hl⟩ := exists_tendsto_sum_range_sin_div_nat hx₀ hx₁
  let coeff : ℕ → ℝ := fun n =>
    if n = 0 then 0 else Real.sin (2 * Real.pi * x * n) / n
  have habel :
      Tendsto (fun r : ℝ => ∑' n, coeff n * r ^ n) (𝓝[<] 1) (𝓝 l) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hcoeff :
      Set.EqOn
        (fun r : ℝ => ∑' n, coeff n * r ^ n)
        (fun r : ℝ =>
          (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
        (Set.Ioo 0 1) := by
    intro r hr
    have hr₀ : 0 ≤ r := hr.1.le
    have hr₁ : r < 1 := hr.2
    calc
      ∑' n : ℕ, coeff n * r ^ n
          = ∑' n : ℕ, (r ^ n / n) * Real.sin (2 * Real.pi * x * n) := by
              refine tsum_congr fun n : ℕ => ?_
              rcases n.eq_zero_or_pos with rfl | hn
              · simp [coeff]
              · simp [coeff, hn.ne', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im :=
            (hasSum_mul_rpow_sin x r hr₀ hr₁).tsum_eq
  have habel' :
      Tendsto
        (fun r : ℝ =>
          (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
        (𝓝[<] 1) (𝓝 l) :=
    Tendsto.congr' (hcoeff.eventuallyEq_of_mem (Ioo_mem_nhdsLT zero_lt_one)) habel
  have hslit :
      ((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have hre :
        (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)).re : ℝ) =
          2 * Real.sin (Real.pi * x) ^ 2 := by
      have hExp :
          (Complex.exp ((2 * Real.pi * x) * Complex.I)).re = Real.cos (2 * Real.pi * x) := by
        simpa using (Complex.exp_ofReal_mul_I_re (2 * Real.pi * x))
      rw [Complex.sub_re, Complex.one_re, hExp]
      have hsq : 1 - Real.cos (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) ^ 2 := by
        rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.cos_two_mul]
        nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
      exact hsq
    rw [hre]
    have hxπ : Real.pi * x ∈ Set.Ioo 0 Real.pi := by
      constructor <;> nlinarith [hx₀, hx₁, Real.pi_pos]
    have hsin : 0 < Real.sin (Real.pi * x) := Real.sin_pos_of_mem_Ioo hxπ
    positivity
  have hcont :
      Tendsto
        (fun r : ℝ =>
          (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
        (𝓝[<] 1) (𝓝 (Real.pi * (1 / 2 - x))) := by
    have hz :
        Tendsto
          (fun r : ℝ => (1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))
          (𝓝[<] 1)
          (𝓝 ((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I))) := by
      have hcont :
          Continuous fun r : ℝ =>
            (1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I) := by
        continuity
      have hcont1 :
          ContinuousAt
            (fun r : ℝ => (1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))
            1 :=
        hcont.continuousAt
      convert tendsto_nhdsWithin_of_tendsto_nhds hcont1.tendsto using 1
      · simp
    have hlog :
        Tendsto
          (fun r : ℝ =>
            Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)))
          (𝓝[<] 1)
          (𝓝 (Complex.log ((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))) :=
      hz.clog hslit
    have him0 :
        Tendsto
          (fun r : ℝ =>
            (Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
          (𝓝[<] 1)
          (𝓝 ((Complex.log (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im)) :=
      Complex.continuous_im.continuousAt.tendsto.comp hlog
    have hnegim :
        Tendsto
          (fun r : ℝ =>
            -((Complex.log
                ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im))
          (𝓝[<] 1)
          (𝓝 (-((Complex.log
            (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im))) :=
      him0.neg
    have ht₀ : 0 < 2 * Real.pi * x := by nlinarith [hx₀, Real.pi_pos]
    have ht₂π : 2 * Real.pi * x < 2 * Real.pi := by nlinarith [hx₁, Real.pi_pos]
    have hvalue := neg_log_one_sub_exp_ofReal_mul_I_im ht₀ ht₂π
    have hvalue' :
        -((Complex.log (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im) =
          Real.pi * (1 / 2 - x) := by
      calc
        -((Complex.log (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im) =
            Real.pi / 2 - (2 * Real.pi * x) / 2 := by
              simpa using hvalue
        _ = Real.pi * (1 / 2 - x) := by ring
    simpa [hvalue'] using hnegim
  have hl_eq : l = Real.pi * (1 / 2 - x) := tendsto_nhds_unique habel' hcont
  simpa [hl_eq] using hl

/-- The shifted endpoint sine series converges to the same boundary value. -/
lemma tendsto_sum_range_shifted_sin_one {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (1 : ℂ)))
      atTop (nhds (Real.pi * (1 / 2 - x) : ℂ)) := by
  let F : ℕ → ℂ := fun n =>
    ((∑ i ∈ Finset.range n,
      if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i : ℝ) : ℂ)
  have hbase : Tendsto F atTop (nhds (Real.pi * (1 / 2 - x) : ℂ)) := by
    simpa [F] using (tendsto_sum_range_sin_div_nat hx₀ hx₁).ofReal
  have hshifted : Tendsto (fun n : ℕ => F (n + 1)) atTop (nhds (Real.pi * (1 / 2 - x) : ℂ)) :=
    (tendsto_add_atTop_iff_nat 1).2 hbase
  refine hshifted.congr' <| Filter.Eventually.of_forall fun n => ?_
  have hsum :=
    Finset.sum_range_add
      (fun i : ℕ => (((if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i : ℝ)) : ℂ)) 1 n
  simpa [F, add_comm, add_left_comm, add_assoc] using hsum

/-- The shifted sine Dirichlet partial sums are uniformly Cauchy on the half-line `s ≥ 1`. -/
lemma uniformCauchySeqOn_shiftedSinPartialSums {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    UniformCauchySeqOn
      (fun n (s : ℝ) => ∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)))
      atTop (Set.Ici 1) := by
  rw [Metric.uniformCauchySeqOn_iff]
  let B : ℝ :=
    4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖
  have hxπ : Real.pi * x ∈ Set.Ioo 0 Real.pi := by
    constructor <;> nlinarith [hx₀, hx₁, Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * x) := Real.sin_pos_of_mem_Ioo hxπ
  have hdenom : 0 < ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
    have htwo : 0 < 2 * Real.sin (Real.pi * x) := by positivity
    have hunit_ne :
        Real.cos (Real.pi * x - Real.pi / 2) +
            Real.sin (Real.pi * x - Real.pi / 2) * Complex.I ≠ 0 := by
      have hunit_pos :
          0 < ‖Real.cos (Real.pi * x - Real.pi / 2) +
              Real.sin (Real.pi * x - Real.pi / 2) * Complex.I‖ := by
        have hunit_pos' :
            0 < ‖Complex.cos ((Real.pi * x - Real.pi / 2 : ℝ) : ℂ) +
                Complex.sin ((Real.pi * x - Real.pi / 2 : ℝ) : ℂ) * Complex.I‖ := by
          rw [Complex.norm_cos_add_sin_mul_I]
          norm_num
        simpa [Complex.ofReal_cos, Complex.ofReal_sin] using hunit_pos'
      exact norm_pos_iff.mp hunit_pos
    have hfac_ne : ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast htwo.ne'
    have hzero : (1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 0 := by
      have hrewrite :
          (1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) =
            (2 * Real.sin ((2 * Real.pi * x) / 2) : ℝ) *
              (Real.cos ((2 * Real.pi * x) / 2 - Real.pi / 2) +
                Real.sin ((2 * Real.pi * x) / 2 - Real.pi / 2) * Complex.I) := by
        simpa [mul_assoc] using one_sub_exp_ofReal_mul_I (2 * Real.pi * x)
      rw [hrewrite]
      simpa [show (2 * Real.pi * x) / 2 = Real.pi * x by ring] using mul_ne_zero hfac_ne hunit_ne
    exact norm_pos_iff.mpr hzero
  have hB_pos : 0 < B := by
    positivity
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (div_pos hε hB_pos)
  refine ⟨N, ?_⟩
  have htail_bound :
      ∀ ⦃m n : ℕ⦄, N ≤ m → m ≤ n → ∀ s ∈ Set.Ici (1 : ℝ),
        dist
            (∑ i ∈ Finset.range m,
              Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)))
            (∑ i ∈ Finset.range n,
              Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)))
          < ε := by
    intro m n hm hmn s hs
    let term : ℕ → ℂ := fun k =>
      Real.sin (2 * Real.pi * x * (k + 1)) / ((k + 1 : ℂ) ^ (s : ℂ))
    have hsplit :
        ∑ i ∈ Finset.range n, term i =
          ∑ i ∈ Finset.range m, term i + ∑ i ∈ Finset.range (n - m), term (m + i) := by
      simpa [term, Nat.add_sub_of_le hmn] using Finset.sum_range_add term m (n - m)
    have hs' : 1 ≤ s := hs
    rw [dist_eq_norm, norm_sub_rev]
    calc
      ‖∑ i ∈ Finset.range n, term i - ∑ i ∈ Finset.range m, term i‖
          = ‖∑ i ∈ Finset.range (n - m), term (m + i)‖ := by
              rw [hsplit]
              ring_nf
      _ ≤ B * (1 / (m + 1 : ℝ) ^ s) := by
            simpa [B, term, add_assoc, add_comm, add_left_comm] using
              norm_sum_range_shifted_sin_term_le (x := x) hx₀ hx₁ hs' m (n - m)
      _ ≤ B * (1 / (m + 1 : ℝ)) := by
            have hm1 : 1 ≤ (m + 1 : ℝ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
            have hpow : (m + 1 : ℝ) ^ (1 : ℝ) ≤ (m + 1 : ℝ) ^ s := by
              simpa using Real.rpow_le_rpow_of_exponent_le hm1 hs'
            have hpow_inv : 1 / (m + 1 : ℝ) ^ s ≤ 1 / (m + 1 : ℝ) := by
              simpa [Real.rpow_one] using
                (one_div_le_one_div_of_le (show 0 < (m + 1 : ℝ) ^ (1 : ℝ) by positivity) hpow)
            exact mul_le_mul_of_nonneg_left hpow_inv hB_pos.le
      _ ≤ B * (1 / (N + 1 : ℝ)) := by
            have hm_inv : 1 / (m + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
              one_div_le_one_div_of_le (show 0 < (N + 1 : ℝ) by positivity)
                (by exact_mod_cast Nat.succ_le_succ hm)
            exact mul_le_mul_of_nonneg_left hm_inv hB_pos.le
      _ < B * (ε / B) :=
            mul_lt_mul_of_pos_left hN hB_pos
      _ = ε := by
            field_simp [hB_pos.ne']
  intro m hm n hn s hs
  rcases le_total m n with hmn | hnm
  · exact htail_bound hm hmn s hs
  · simpa [dist_comm] using htail_bound hn hnm s hs

/-- The sine zeta function takes the classical boundary value at `s = 1` for `x ∈ (0, 1)`:
`sinZeta x 1 = π(1/2 − x)`. -/
theorem sinZeta_one_eq_boundary {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    HurwitzZeta.sinZeta x 1 = (Real.pi * (1 / 2 - x) : ℂ) := by
  let boundary : ℂ := (Real.pi * (1 / 2 - x) : ℂ)
  let S : ℕ → ℝ → ℂ := fun n s =>
    ∑ i ∈ Finset.range n,
      Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ))
  let G : ℝ → ℂ := fun s => if hs : s = 1 then boundary else HurwitzZeta.sinZeta x s
  have hCauchy : UniformCauchySeqOn S atTop (Set.Ici 1) := by
    simpa [S] using uniformCauchySeqOn_shiftedSinPartialSums (x := x) hx₀ hx₁
  have hpoint : ∀ s ∈ Set.Ici (1 : ℝ), Tendsto (fun n => S n s) atTop (𝓝 (G s)) := by
    intro s hs
    by_cases hs1 : s = 1
    · simpa [S, G, hs1, boundary] using tendsto_sum_range_shifted_sin_one (x := x) hx₀ hx₁
    · simpa [S, G, hs1] using (hasSum_shifted_sinZeta (x := x) s
        (lt_of_le_of_ne hs (by simpa [eq_comm] using hs1))).tendsto_sum_nat
  have hcont : ContinuousOn G (Set.Ici (1 : ℝ)) := by
    apply (hCauchy.tendstoUniformlyOn_of_tendsto hpoint).continuousOn
    refine Frequently.of_forall fun n => ?_
    classical
    dsimp [S]
    exact Continuous.continuousOn <|
      continuous_finsetSum _ fun i _ => continuous_shiftedSinTerm x i
  have hG_right : Tendsto G (𝓝[Set.Ioi 1] 1) (𝓝 boundary) :=
    ((by simpa [G, boundary] using (hcont 1 (by simp)).tendsto :
        Tendsto G (𝓝[Set.Ici 1] 1) (𝓝 boundary))).mono_left
      (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hsin_right : Tendsto (fun s : ℝ => HurwitzZeta.sinZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 boundary) :=
    hG_right.congr' <| by
      filter_upwards [eventually_mem_nhdsWithin] with s hs
      simp [G, ne_of_gt (show 1 < s by simpa using hs)]
  have hsin_cont : Tendsto (fun s : ℝ => HurwitzZeta.sinZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 (HurwitzZeta.sinZeta x 1)) :=
    ((HurwitzZeta.differentiableAt_sinZeta x 1).continuousAt.tendsto.comp
      Complex.continuous_ofReal.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  simpa [boundary] using (tendsto_nhds_unique hsin_right hsin_cont).symm

/-! ### `hurwitzZeta` at `s = 0` on the open interval -/

/-- A real number in `(0,1)` is nonzero on the unit circle `ℝ/ℤ`. -/
lemma unitAddCircle_coe_ne_zero {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    (↑x : UnitAddCircle) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
  rw [zsmul_eq_mul, mul_one] at hn
  have h0 : (0 : ℝ) < n := hn ▸ hx₀
  have h1 : (n : ℝ) < 1 := hn ▸ hx₁
  have h0' : 0 < n := by exact_mod_cast h0
  have h1' : n < 1 := by exact_mod_cast h1
  omega

/-- The odd Hurwitz zeta function at `s = 0`: `ζ_O(x, 0) = 1/2 − x` for
`x ∈ (0,1)`, via the functional equation `hurwitzZetaOdd_one_sub` at `s = 1`
and the sawtooth boundary value. -/
theorem hurwitzZetaOdd_apply_zero_of_mem_Ioo {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    HurwitzZeta.hurwitzZetaOdd x 0 = ((1 / 2 - x : ℝ) : ℂ) := by
  have h1 : ∀ n : ℕ, (1 : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have := congrArg Complex.re h
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at this
    have hn : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg
    linarith
  have h := HurwitzZeta.hurwitzZetaOdd_one_sub (↑x : UnitAddCircle) (s := 1) h1
  rw [sub_self, sinZeta_one_eq_boundary hx₀ hx₁] at h
  rw [h, Complex.Gamma_one, Complex.cpow_neg_one]
  have hsin : Complex.sin (↑Real.pi * 1 / 2) = 1 := by
    rw [mul_one, show (↑Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one]
  rw [hsin]
  have hpi : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  push_cast
  ring

/-- mathlib's `hurwitzZeta_neg_nat`, extended to `k = 0` for `x` in the open
interval (the `k = 0` case is the TODO recorded at `hurwitzZeta_neg_nat`;
boundary `x` genuinely fails it: `hurwitzZeta 0 0 = ζ(0) = −1/2 ≠ −B₁(0)`). -/
theorem hurwitzZeta_neg_nat_of_mem_Ioo (k : ℕ) {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    HurwitzZeta.hurwitzZeta x (-(k : ℂ)) =
      -1 / (k + 1) *
        ((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.cast_zero, neg_zero, HurwitzZeta.hurwitzZeta,
      HurwitzZeta.hurwitzZetaEven_apply_zero,
      if_neg (unitAddCircle_coe_ne_zero hx₀ hx₁), zero_add,
      hurwitzZetaOdd_apply_zero_of_mem_Ioo hx₀ hx₁, zero_add,
      Polynomial.bernoulli_one]
    push_cast
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [map_inv₀, map_ofNat]
    ring
  · exact_mod_cast HurwitzZeta.hurwitzZeta_neg_nat hk.ne' ⟨hx₀.le, hx₁.le⟩

end PadicLFunctions
