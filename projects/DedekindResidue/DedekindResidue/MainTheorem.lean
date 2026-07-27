/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import DedekindResidue.Theorem1

/-!
# Theorem 1 (Belabas–Friedman) — the main effective bound

The statement of the paper's main result: under GRH, `log κ_K` is approximated by the
computable quantity `f_K(X)` with an explicit error `O(log Δ_K / (√X log X))`, where
`κ_K = Res_{s=1} ζ_K(s)` is mathlib's `NumberField.dedekindZeta_residue K`.

`bSum` / `fK` (Belabas–Friedman's `B_K(X)` / `f_K(X)`, p. 2) live in
`DedekindResidue.Theorem1` together with the endgame bridges. The proof combines the explicit
zero-sum and archimedean estimates there with `step1`.
-/

namespace DedekindResidue

@[expose] public section

open NumberField Real

private lemma key_algebra {s : ℝ} (hs0 : 0 < s) :
    (2 * (1 + 1 / s) - 1) * (s ^ 2 + 2 / ((1 + 1 / s) - 1)) = (s + 2) ^ 2 := by
  have h1 : (1 : ℝ) + 1 / s - 1 = 1 / s := by ring
  rw [h1]
  field_simp
  ring

private lemma one_le_log_abs_discr {K : Type*} [Field K] [NumberField K]
    (hn : 1 < Module.finrank ℚ K) : (1 : ℝ) ≤ Real.log (|discr K| : ℝ) := by
  have hd2 : (2 : ℤ) < |discr K| := NumberField.abs_discr_gt_two hn
  have hd3' : (3 : ℤ) ≤ |discr K| := by lia
  have hd3 : (3 : ℝ) ≤ (|discr K| : ℝ) := by exact_mod_cast hd3'
  have hd0 : (0 : ℝ) < (|discr K| : ℝ) := by linarith
  rw [Real.le_log_iff_exp_le hd0]
  exact Real.exp_one_lt_d9.le.trans (by linarith)

private lemma zero_sum_le_sq {K : Type*} [Field K] [NumberField K]
    (hn : 1 < Module.finrank ℚ K) (hGRH : GeneralizedRiemannHypothesis K)
    (hRH : RiemannHypothesis) : zeroSumSigma K 1 + zeroSumSigma ℚ 1
      ≤ (Real.sqrt (Real.log (|discr K| : ℝ)) + 2) ^ 2 := by
  have hl3gt := Real.log_three_gt_d9
  have hl2gt := Real.log_two_gt_d9
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlπ : Real.log 3 ≤ Real.log π :=
    Real.log_le_log (by norm_num) Real.pi_gt_three.le
  have hlogd1 := one_le_log_abs_discr hn
  set L : ℝ := Real.log (|discr K| : ℝ) with hL_def
  have hL0 : (0 : ℝ) < L := by linarith
  set s : ℝ := Real.sqrt L with hs_def
  have hs1 : (1 : ℝ) ≤ s := by
    rw [hs_def, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hlogd1
  have hs0 : (0 : ℝ) < s := by linarith
  have hs2 : s ^ 2 = L := Real.sq_sqrt hL0.le
  set σ : ℝ := 1 + 1 / s with hσ_def
  have hσ1 : (1 : ℝ) < σ := by
    rw [hσ_def]
    have : (0 : ℝ) < 1 / s := by positivity
    linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσ_def]
    have : 1 / s ≤ 1 := by
      rw [div_le_one hs0]
      exact hs1
    linarith
  have hdLow0 : (0 : ℝ) ≤ 2 * Real.eulerMascheroniConstant + 2 * Real.log (2 * π) - 3 := by
    have h2π : Real.log (2 * π) = Real.log 2 + Real.log π :=
      Real.log_mul two_ne_zero Real.pi_ne_zero
    rw [h2π]
    linarith
  have hkey : (2 * σ - 1) * (L + 2 / (σ - 1)) = (s + 2) ^ 2 := by
    rw [hσ_def, ← hs2]
    exact key_algebra hs0
  have hσ10 : (0 : ℝ) < σ - 1 := by linarith
  have h2σ1 : (1 : ℝ) ≤ 2 * σ - 1 := by linarith
  have hmono : (2 * σ - 1) * (L + 2 / (σ - 1) - dSigma K σ)
      ≤ (2 * σ - 1) * (L + 2 / (σ - 1))
        - (2 * σ - 1) *
          (2 * Real.eulerMascheroniConstant + 2 * Real.log (2 * π) - 3) := by
    have := mul_le_mul_of_nonneg_left (dSigma_ge K hn hσ1 hσ2)
      (by linarith : (0 : ℝ) ≤ 2 * σ - 1)
    nlinarith
  have habsorb : 2 * Real.eulerMascheroniConstant + 2 * Real.log (2 * π) - 3
      ≤ (2 * σ - 1) *
        (2 * Real.eulerMascheroniConstant + 2 * Real.log (2 * π) - 3) := by
    nlinarith
  calc zeroSumSigma K 1 + zeroSumSigma ℚ 1
      ≤ (2 * σ - 1) * (L + 2 / (σ - 1) - dSigma K σ)
        + (2 * Real.eulerMascheroniConstant + 2 * Real.log (2 * π) - 3) := by
        exact add_le_add (landau_stark_estimate K hGRH hσ1) (zeroSumSigma_rat_le hRH)
    _ ≤ (2 * σ - 1) * (L + 2 / (σ - 1)) := by linarith
    _ = (s + 2) ^ 2 := hkey

private lemma beta_piece_le {X : ℝ} (hX : 69 ≤ X) :
    (1 / 2 + 1 / Real.log (X / 9)) * Real.exp (Real.log (X / 9) / 2)
      * archKernelL (Real.log (X / 9)) ≤ 6 / Real.sqrt X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hsX : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hthresh : Real.log (23 / 3) ≤ Real.log (X / 9) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hexpT : Real.exp (Real.log (X / 9) / 2) = Real.sqrt (X / 9) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith : (0 : ℝ) < X / 9)]
    congr 1
    ring
  have hsqrt9 : Real.sqrt (X / 9) = Real.sqrt X / 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_div' X (by norm_num),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  refine (beta_bound_half hthresh).trans (le_of_eq ?_)
  rw [Real.exp_neg, hexpT, hsqrt9, inv_div]
  field_simp
  ring

private lemma zero_sum_coefficient_le {X : ℝ} (hX : 69 ≤ X) :
    2 * (1 / 2 : ℝ) ^ 2 * (Real.log X - Real.log (X / 9))
        + (2 * ((1 / 2 : ℝ) + 1 / Real.log X)
          + 2 * ((1 / 2 : ℝ) + 1 / Real.log (X / 9)))
        + (4 / Real.log X + 4 / Real.log (X / 9))
      ≤ (4 / 3) * 2.324 * (1 + 3.88 * (1 / Real.log (X / 9))) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hT'0 : (0 : ℝ) < Real.log (X / 9) := Real.log_pos (by linarith)
  have hT'X : Real.log (X / 9) ≤ Real.log X :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog9diff : Real.log X - Real.log (X / 9) = Real.log 9 := by
    rw [Real.log_div hX0.ne' (by norm_num)]
    ring
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hl3lt := Real.log_three_lt_d9
  have hl3gt := Real.log_three_gt_d9
  have h4X : (4 : ℝ) / Real.log X = 4 * (1 / Real.log X) := by ring
  have h4T : (4 : ℝ) / Real.log (X / 9) = 4 * (1 / Real.log (X / 9)) := by ring
  have h6X : 1 / Real.log X ≤ 1 / Real.log (X / 9) :=
    div_le_div_of_nonneg_left (by norm_num) hT'0 hT'X
  have hT'inv0 : (0 : ℝ) < 1 / Real.log (X / 9) := by positivity
  rw [hlog9diff, hlog9, h4X, h4T]
  linarith

private lemma zero_sum_term_le {K : Type*} [Field K] [NumberField K] {X s : ℝ}
    (hX : 69 ≤ X) (hZS : zeroSumSigma K 1 + zeroSumSigma ℚ 1 ≤ (s + 2) ^ 2) :
    (2 * (1 / 2 : ℝ) ^ 2 * (Real.log X - Real.log (X / 9))
          + (2 * ((1 / 2 : ℝ) + 1 / Real.log X)
            + 2 * ((1 / 2 : ℝ) + 1 / Real.log (X / 9)))
          + (4 / Real.log X + 4 / Real.log (X / 9)))
        * (zeroSumSigma K 1 + zeroSumSigma ℚ 1)
      ≤ ((4 / 3) * 2.324 * (1 + 3.88 * (1 / Real.log (X / 9)))) * (s + 2) ^ 2 := by
  have hT'0 : (0 : ℝ) < Real.log (X / 9) := Real.log_pos (by linarith)
  have hZS0 : (0 : ℝ) ≤ zeroSumSigma K 1 + zeroSumSigma ℚ 1 :=
    add_nonneg (zeroSumSigma_nonneg K 1) (zeroSumSigma_nonneg ℚ 1)
  refine mul_le_mul (zero_sum_coefficient_le hX) hZS hZS0 ?_
  positivity

private lemma archimedean_term_le {X nR : ℝ} (hX : 69 ≤ X) (hnR : 2 ≤ nR) :
    (nR - 1) * ((Real.log X - Real.log (X / 9))
        * ((1 / 2 + 1 / Real.log (X / 9)) * Real.exp (Real.log (X / 9) / 2)
          * archKernelL (Real.log (X / 9))))
      ≤ (4 / 3) * 2.324 * 4.26 * (nR - 1) / Real.sqrt X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hsX : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hlog9diff : Real.log X - Real.log (X / 9) = Real.log 9 := by
    rw [Real.log_div hX0.ne' (by norm_num)]
    ring
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlog9nn : (0 : ℝ) ≤ Real.log 9 := by
    rw [hlog9]
    linarith [Real.log_three_gt_d9]
  have harch : (nR - 1) * ((Real.log X - Real.log (X / 9))
        * ((1 / 2 + 1 / Real.log (X / 9)) * Real.exp (Real.log (X / 9) / 2)
          * archKernelL (Real.log (X / 9))))
      ≤ (nR - 1) * (Real.log 9 * (6 / Real.sqrt X)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [hlog9diff]
    exact mul_le_mul_of_nonneg_left (beta_piece_le hX) hlog9nn
  refine harch.trans ?_
  rw [show (nR - 1) * (Real.log 9 * (6 / Real.sqrt X))
      = (6 * Real.log 9) * ((nR - 1) / Real.sqrt X) by ring,
    show (4 / 3) * 2.324 * 4.26 * (nR - 1) / Real.sqrt X
      = ((4 / 3) * 2.324 * 4.26) * ((nR - 1) / Real.sqrt X) by ring]
  refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (by linarith) hsX.le)
  rw [hlog9]
  linarith [Real.log_three_lt_d9]

private lemma rhs_expand {X s nR : ℝ} (hs0 : 0 < s)
    (hsX : (0 : ℝ) < Real.sqrt X) (hl3X : (0 : ℝ) < Real.log (3 * X))
    (hT'0 : (0 : ℝ) < Real.log (X / 9)) : (4 / 3) * Real.sqrt X * Real.log (3 * X)
        * (2.324 * s ^ 2 / (Real.sqrt X * Real.log (3 * X))
          * ((1 + 3.88 / Real.log (X / 9)) * (1 + 2 / s) ^ 2
            + 4.26 * (nR - 1) / (Real.sqrt X * s ^ 2)))
      = (4 / 3) * 2.324 * (1 + 3.88 * (1 / Real.log (X / 9))) * (s + 2) ^ 2
        + (4 / 3) * 2.324 * 4.26 * (nR - 1) / Real.sqrt X := by
  have hsXne : Real.sqrt X ≠ 0 := hsX.ne'
  have hl3Xne : Real.log (3 * X) ≠ 0 := hl3X.ne'
  have hsne : s ≠ 0 := hs0.ne'
  have hT'ne : Real.log (X / 9) ≠ 0 := hT'0.ne'
  field_simp

private lemma scaled_error_le {K : Type*} [Field K] [NumberField K]
    (hn : 1 < Module.finrank ℚ K) (hGRH : GeneralizedRiemannHypothesis K)
    (hRH : RiemannHypothesis) {X : ℝ} (hX : 69 ≤ X) : (4 / 3) * Real.sqrt X * Real.log (3 * X)
        * |Real.log (dedekindZeta_residue K) - fK K X|
      ≤ (4 / 3) * Real.sqrt X * Real.log (3 * X)
        * (2.324 * Real.log (|discr K| : ℝ) / (Real.sqrt X * Real.log (3 * X))
          * ((1 + 3.88 / Real.log (X / 9))
              * (1 + 2 / Real.sqrt (Real.log (|discr K| : ℝ))) ^ 2
            + 4.26 * ((Module.finrank ℚ K : ℝ) - 1)
                / (Real.sqrt X * Real.log (|discr K| : ℝ)))) := by
  have hX9 : (9 : ℝ) < X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hsX : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hT'0 : (0 : ℝ) < Real.log (X / 9) := Real.log_pos (by linarith)
  have hl3X : (0 : ℝ) < Real.log (3 * X) := Real.log_pos (by linarith)
  have hlogd1 := one_le_log_abs_discr hn
  set s : ℝ := Real.sqrt (Real.log (|discr K| : ℝ)) with hs_def
  have hs1 : (1 : ℝ) ≤ s := by
    rw [hs_def, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hlogd1
  have hs0 : (0 : ℝ) < s := by linarith
  have hs2 : s ^ 2 = Real.log (|discr K| : ℝ) := by
    rw [hs_def]
    exact Real.sq_sqrt (by linarith)
  have hZS : zeroSumSigma K 1 + zeroSumSigma ℚ 1 ≤ (s + 2) ^ 2 := by
    rw [hs_def]
    exact zero_sum_le_sq hn hGRH hRH
  set nR : ℝ := (Module.finrank ℚ K : ℝ) with hnR_def
  have hnR2 : (2 : ℝ) ≤ nR := by
    rw [hnR_def]
    exact_mod_cast hn
  have hRHSexpand : (4 / 3) * Real.sqrt X * Real.log (3 * X)
      * (2.324 * Real.log (|discr K| : ℝ) / (Real.sqrt X * Real.log (3 * X))
        * ((1 + 3.88 / Real.log (X / 9))
            * (1 + 2 / Real.sqrt (Real.log (|discr K| : ℝ))) ^ 2
          + 4.26 * (nR - 1) / (Real.sqrt X * Real.log (|discr K| : ℝ))))
    = (4 / 3) * 2.324 * (1 + 3.88 * (1 / Real.log (X / 9))) * (s + 2) ^ 2
      + (4 / 3) * 2.324 * 4.26 * (nR - 1) / Real.sqrt X := by
    rw [← hs2, Real.sqrt_sq hs0.le]
    exact rhs_expand hs0 hsX hl3X hT'0
  calc
    (4 / 3) * Real.sqrt X * Real.log (3 * X)
          * |Real.log (dedekindZeta_residue K) - fK K X|
        ≤ (nR - 1) * ((Real.log X - Real.log (X / 9))
            * ((1 / 2 + 1 / Real.log (X / 9)) * Real.exp (Real.log (X / 9) / 2)
              * archKernelL (Real.log (X / 9))))
          + (2 * (1 / 2 : ℝ) ^ 2 * (Real.log X - Real.log (X / 9))
              + (2 * ((1 / 2 : ℝ) + 1 / Real.log X)
                + 2 * ((1 / 2 : ℝ) + 1 / Real.log (X / 9)))
              + (4 / Real.log X + 4 / Real.log (X / 9)))
            * (zeroSumSigma K 1 + zeroSumSigma ℚ 1) := step1 K hGRH hRH hn hX9
    _ ≤ (4 / 3) * 2.324 * 4.26 * (nR - 1) / Real.sqrt X
          + ((4 / 3) * 2.324 * (1 + 3.88 * (1 / Real.log (X / 9)))) * (s + 2) ^ 2 :=
      add_le_add (archimedean_term_le hX hnR2) (zero_sum_term_le hX hZS)
    _ = (4 / 3) * 2.324 * (1 + 3.88 * (1 / Real.log (X / 9))) * (s + 2) ^ 2
          + (4 / 3) * 2.324 * 4.26 * (nR - 1) / Real.sqrt X := add_comm _ _
    _ = (4 / 3) * Real.sqrt X * Real.log (3 * X)
        * (2.324 * Real.log (|discr K| : ℝ) / (Real.sqrt X * Real.log (3 * X))
          * ((1 + 3.88 / Real.log (X / 9))
              * (1 + 2 / Real.sqrt (Real.log (|discr K| : ℝ))) ^ 2
            + 4.26 * ((Module.finrank ℚ K : ℝ) - 1)
                / (Real.sqrt X * Real.log (|discr K| : ℝ)))) := hRHSexpand.symm

/-- **Theorem 1** (Belabas–Friedman, arXiv:1305.0035, p. 2). Let `K` be a number field of
degree `n > 1`. Under GRH for `ζ_K` and RH for `ζ_ℚ`, for `X ≥ 69`,
`|log κ_K − f_K(X)| ≤ (2.324 log Δ_K / (√X log 3X)) ·
((1 + 3.88/log(X/9))·(1 + 2/√(log Δ_K))² + 4.26(n−1)/(√X log Δ_K))`, where
`κ_K = dedekindZeta_residue K` and `Δ_K = |disc K|`. -/
theorem belabas_friedman_bound {K : Type*} [Field K] [NumberField K] (hn : 1 < Module.finrank ℚ K)
    (hGRH : GeneralizedRiemannHypothesis K) (hRH : RiemannHypothesis) {X : ℝ} (hX : 69 ≤ X) :
    |Real.log (dedekindZeta_residue K) - fK K X|
      ≤ 2.324 * Real.log (|discr K| : ℝ) / (Real.sqrt X * Real.log (3 * X)) *
          ((1 + 3.88 / Real.log (X / 9)) *
              (1 + 2 / Real.sqrt (Real.log (|discr K| : ℝ))) ^ 2
            + 4.26 * ((Module.finrank ℚ K : ℝ) - 1) /
                (Real.sqrt X * Real.log (|discr K| : ℝ))) := by
  have hsX : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr (by linarith)
  have hl3X : (0 : ℝ) < Real.log (3 * X) := Real.log_pos (by linarith)
  have hc0 : (0 : ℝ) < (4 / 3) * Real.sqrt X * Real.log (3 * X) := by positivity
  exact le_of_mul_le_mul_left (scaled_error_le hn hGRH hRH hX) hc0

end

end DedekindResidue
