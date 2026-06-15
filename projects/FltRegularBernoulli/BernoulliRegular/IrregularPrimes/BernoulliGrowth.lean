import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic

/-!
# Bernoulli growth along even indices

This file proves the analytic growth input used in Diekmann's proof that
there are infinitely many irregular primes.  The source is mathlib's exact
zeta-value formula `hasSum_zeta_nat`.
-/

open Filter
open scoped Nat Real Topology

namespace BernoulliRegular

noncomputable section

/-- The real zeta series at a positive even integer. -/
abbrev zetaEvenSeries (k : ℕ) : ℝ :=
  ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * k)

/-- The zeta series at `2 * k`, `k ≠ 0`, is at least its `n = 1` term. -/
theorem one_le_zetaEvenSeries {k : ℕ} (hk : k ≠ 0) :
    1 ≤ zetaEvenSeries k := by
  have hsummable : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 * k)) :=
    (hasSum_zeta_nat hk).summable
  have hnonneg : ∀ n : ℕ, 0 ≤ (1 : ℝ) / (n : ℝ) ^ (2 * k) := by
    intro n
    positivity
  have hle := hsummable.sum_le_tsum ({1} : Finset ℕ) (fun n _ => hnonneg n)
  simpa [zetaEvenSeries] using hle

/-- A one-sided lower bound for `|B_{2k}|` extracted from the zeta-value
formula. -/
theorem bernoulli_even_abs_lower_bound {k : ℕ} (hk : k ≠ 0) :
    ((2 * k)! : ℝ) / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)) ≤
      |((bernoulli (2 * k) : ℚ) : ℝ)| := by
  have hsum_eq := (hasSum_zeta_nat hk).tsum_eq
  have hone : (1 : ℝ) ≤ zetaEvenSeries k := one_le_zetaEvenSeries hk
  rw [zetaEvenSeries, hsum_eq] at hone
  set C : ℝ := (2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k) with hC
  set F : ℝ := ((2 * k)! : ℝ) with hF
  set B : ℝ := ((bernoulli (2 * k) : ℚ) : ℝ) with hB
  have hone' : (1 : ℝ) ≤ (-1 : ℝ) ^ (k + 1) * C * B / F := by
    simpa [hC, hF, hB, mul_assoc] using hone
  have hC_pos : 0 < C := by
    rw [hC]
    positivity
  have hF_pos : 0 < F := by
    rw [hF]
    positivity
  have hF_nonneg : 0 ≤ F := hF_pos.le
  have habs_ge : 1 ≤ |((-1 : ℝ) ^ (k + 1) * C * B / F)| :=
    le_trans hone' (le_abs_self _)
  have hcalc : |((-1 : ℝ) ^ (k + 1) * C * B / F)| = C * |B| / F := by
    rw [abs_div, abs_mul, abs_mul]
    have hsign : |(-1 : ℝ) ^ (k + 1)| = 1 := by
      rw [abs_pow, abs_neg, abs_one, one_pow]
    rw [hsign, one_mul, abs_of_pos hC_pos, abs_of_pos hF_pos]
  rw [hcalc] at habs_ge
  have hmul : F ≤ C * |B| := by
    have := mul_le_mul_of_nonneg_right habs_ge hF_nonneg
    rwa [one_mul, div_mul_cancel₀ _ hF_pos.ne'] at this
  have hdiv : F / C ≤ |B| := by
    rw [div_le_iff₀ hC_pos]
    simpa [mul_comm] using hmul
  simpa [hC, hF, hB] using hdiv

/-- The corresponding lower bound for `|B_{2k} / (2k)|`. -/
theorem bernoulli_div_self_abs_lower_bound {k : ℕ} (hk : k ≠ 0) :
    (Nat.factorial (2 * k - 1) : ℝ) /
        ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)) ≤
      |(((bernoulli (2 * k) : ℚ) / (2 * k : ℚ) : ℚ) : ℝ)| := by
  have hB := bernoulli_even_abs_lower_bound (k := k) hk
  have hn_pos : 0 < (2 * k : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right hB hn_pos.le
  have hleft : (((2 * k)! : ℝ) / ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k))) /
        (2 * k : ℝ) =
      (Nat.factorial (2 * k - 1) : ℝ) /
        ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)) := by
    have hn_ne : 2 * k ≠ 0 := by omega
    have hn_ne_real : (2 * k : ℝ) ≠ 0 := by positivity
    rw [show ((2 * k)! : ℝ) = (2 * k : ℝ) * (Nat.factorial (2 * k - 1) : ℝ) by
      exact_mod_cast (Nat.mul_factorial_pred hn_ne).symm]
    field_simp [hn_ne_real]
  have hright : |((bernoulli (2 * k) : ℚ) : ℝ)| / (2 * k : ℝ) =
      |(((bernoulli (2 * k) : ℚ) / (2 * k : ℚ) : ℚ) : ℝ)| := by
    have hn_pos_rat_real : 0 < (((2 * k : ℚ) : ℝ)) := by
      exact_mod_cast (by omega : 0 < 2 * k)
    rw [Rat.cast_div]
    rw [abs_div, abs_of_pos hn_pos_rat_real]
    norm_num
  rw [hleft] at hdiv
  rwa [hright] at hdiv

/-- Factorials dominate any fixed exponential, even after replacing `n!` by
`(n - 1)!`. -/
theorem tendsto_factorial_pred_div_const_pow_atTop {A : ℝ} (hA : 0 < A) :
    Tendsto (fun n : ℕ => (Nat.factorial (n - 1) : ℝ) / A ^ n) atTop atTop := by
  have hzero : Tendsto
      (fun n : ℕ => (1 : ℝ) * A ^ n / (Nat.factorial (n - 1) : ℝ)) atTop (𝓝 0) :=
    FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop 1 A 1
  have hzero' : Tendsto
      (fun n : ℕ => A ^ n / (Nat.factorial (n - 1) : ℝ)) atTop (𝓝 0) := by
    simpa using hzero
  have hpos : ∀ n : ℕ, 0 < A ^ n / (Nat.factorial (n - 1) : ℝ) := by
    intro n
    positivity
  have hgt : Tendsto
      (fun n : ℕ => A ^ n / (Nat.factorial (n - 1) : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzero', Eventually.of_forall hpos⟩
  have hinv := hgt.inv_tendsto_nhdsGT_zero
  convert hinv using 1
  ext n
  rw [Pi.inv_apply]
  field_simp [pow_ne_zero n hA.ne', Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - 1))]

/-- The map `k ↦ 2 * k` tends to infinity. -/
theorem tendsto_two_mul_atTop : Tendsto (fun k : ℕ => 2 * k) atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone
  · intro a b hab
    exact Nat.mul_le_mul_left 2 hab
  · intro n
    exact ⟨n, by omega⟩

/-- The lower bound for `|B_{2k}/(2k)|` tends to infinity. -/
theorem tendsto_bernoulli_lower_bound_atTop :
    Tendsto
      (fun k : ℕ => (Nat.factorial (2 * k - 1) : ℝ) /
        ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)))
      atTop atTop := by
  have hA : 0 < (2 : ℝ) * Real.pi := by positivity
  have hbase := tendsto_factorial_pred_div_const_pow_atTop hA
  have hcomp := hbase.comp tendsto_two_mul_atTop
  have hmul := Tendsto.const_mul_atTop (show (0 : ℝ) < 2 by norm_num) hcomp
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hpow : ((2 : ℝ) * Real.pi) ^ (2 * k) =
      (2 : ℝ) ^ (2 * k) * Real.pi ^ (2 * k) := by
    rw [mul_pow]
  calc
    (2 : ℝ) * ((Nat.factorial (2 * k - 1) : ℝ) / (((2 : ℝ) * Real.pi) ^ (2 * k)))
        = (Nat.factorial (2 * k - 1) : ℝ) /
          ((2 : ℝ) ^ (2 * k - 1) * Real.pi ^ (2 * k)) := by
      rw [hpow]
      have h2pow : (2 : ℝ) ^ (2 * k) = 2 * (2 : ℝ) ^ (2 * k - 1) := by
        have hs : (2 * k - 1) + 1 = 2 * k := by omega
        nth_rewrite 1 [← hs]
        rw [pow_succ]
        ring
      rw [h2pow]
      field_simp [show (2 : ℝ) ≠ 0 by norm_num]

/-- Diekmann's growth input: `|B_{2n}/(2n)|` tends to infinity. -/
theorem tendsto_abs_bernoulli_div_self_even :
    Tendsto
      (fun n : ℕ => |(((bernoulli (2 * n) : ℚ) / (2 * n : ℚ) : ℚ) : ℝ)|)
      atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_bernoulli_lower_bound_atTop
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact bernoulli_div_self_abs_lower_bound (k := k) (by omega)

/-- For every positive even `C`, some even multiple `C * 2^t` has
`|B_m/m| > 1`. -/
theorem exists_large_even_multiple_abs_bernoulli_div_self_gt_one
    {C : ℕ} (hC_pos : 0 < C) (hC_even : Even C) :
    ∃ t : ℕ,
      1 < |(((bernoulli (C * 2 ^ t) : ℚ) / (C * 2 ^ t : ℚ) : ℚ) : ℝ)| := by
  let c := C / 2
  have hc_pos : 0 < c := by
    obtain ⟨d, hd⟩ := hC_even
    dsimp [c]
    rw [hd]
    omega
  have hpow : Tendsto (fun t : ℕ => 2 ^ t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))
  have hc_tendsto : Tendsto (fun t : ℕ => c * 2 ^ t) atTop atTop := by
    refine tendsto_atTop_mono (fun t => ?_) hpow
    exact Nat.le_mul_of_pos_left (2 ^ t) hc_pos
  have hcomp := tendsto_abs_bernoulli_div_self_even.comp hc_tendsto
  have hevent := hcomp.eventually (eventually_gt_atTop 1)
  obtain ⟨t, ht⟩ := hevent.exists
  refine ⟨t, ?_⟩
  have hC_eq : 2 * c = C := by
    dsimp [c]
    exact Nat.two_mul_div_two_of_even hC_even
  have hidx : 2 * (c * 2 ^ t) = C * 2 ^ t := by
    rw [← Nat.mul_assoc, hC_eq]
  have hdenR : (2 : ℝ) * ((c : ℝ) * (2 : ℝ) ^ t) = (C : ℝ) * (2 : ℝ) ^ t := by
    exact_mod_cast hidx
  simpa [hidx, hdenR, Nat.cast_mul, Nat.cast_pow, mul_assoc] using ht

end

end BernoulliRegular
