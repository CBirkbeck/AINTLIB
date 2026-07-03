module

public import DedekindResidue.Theorem1

/-!
# Theorem 1 (Belabas–Friedman) — the main effective bound

The statement of the paper's main result: under GRH, `log κ_K` is approximated by the
computable quantity `f_K(X)` with an explicit error `O(log Δ_K / (√X log X))`, where
`κ_K = Res_{s=1} ζ_K(s)` is mathlib's `NumberField.dedekindZeta_residue K`.

`bSum` / `fK` (Belabas–Friedman's `B_K(X)` / `f_K(X)`, p. 2) live in
`DedekindResidue.Theorem1` together with the endgame bridges. The proof of
`belabas_friedman_thm1` is the whole SP1→SP2→SP3→Tier 3 development.
-/

namespace DedekindResidue

@[expose] public section

open NumberField Real

/-- **Theorem 1** (Belabas–Friedman, arXiv:1305.0035, p. 2). Let `K` be a number field of
degree `n > 1`. Under GRH for `ζ_K` and RH for `ζ_ℚ`, for `X ≥ 69`,
`|log κ_K − f_K(X)| ≤ (2.324 log Δ_K / (√X log 3X)) · ((1 + 3.88/log(X/9))·(1 + 2/√(log Δ_K))²
+ 4.26(n−1)/(√X log Δ_K))`, where `κ_K = dedekindZeta_residue K` and `Δ_K = |disc K|`.
**Proof: the SP1→SP2→SP3→Tier 3 development.** -/
theorem belabas_friedman_thm1 {K : Type*} [Field K] [NumberField K]
    (hn : 1 < Module.finrank ℚ K)
    (hGRH : GeneralizedRiemannHypothesis K) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 69 ≤ X) :
    |Real.log (dedekindZeta_residue K) - fK K X|
      ≤ 2.324 * Real.log (|discr K| : ℝ) / (Real.sqrt X * Real.log (3 * X)) *
          ((1 + 3.88 / Real.log (X / 9)) *
              (1 + 2 / Real.sqrt (Real.log (|discr K| : ℝ))) ^ 2
            + 4.26 * ((Module.finrank ℚ K : ℝ) - 1) /
                (Real.sqrt X * Real.log (|discr K| : ℝ))) := by
  -- ### X-side facts
  have hX9 : (9:ℝ) < X := by linarith
  have hX0 : (0:ℝ) < X := by linarith
  have hX9' : (1:ℝ) < X/9 := by linarith
  have hsX : (0:ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hT'0 : (0:ℝ) < Real.log (X/9) := Real.log_pos hX9'
  have hTX0 : (0:ℝ) < Real.log X := Real.log_pos (by linarith)
  have hT'X : Real.log (X/9) ≤ Real.log X :=
    Real.log_le_log (by linarith) (by linarith)
  have hl3X : (0:ℝ) < Real.log (3*X) := Real.log_pos (by linarith)
  have hlog9diff : Real.log X - Real.log (X/9) = Real.log 9 := by
    rw [Real.log_div hX0.ne' (by norm_num)]
    ring
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9:ℝ) = 3^2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hl3lt := Real.log_three_lt_d9
  have hl3gt := Real.log_three_gt_d9
  have hl2gt := Real.log_two_gt_d9
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlπ : Real.log 3 ≤ Real.log π :=
    Real.log_le_log (by norm_num) Real.pi_gt_three.le
  -- ### discriminant-side facts
  have hd2 : (2:ℤ) < |discr K| := NumberField.abs_discr_gt_two hn
  have hd3' : (3:ℤ) ≤ |discr K| := by omega
  have hd3 : (3:ℝ) ≤ (|discr K| : ℝ) := by exact_mod_cast hd3'
  have hd0 : (0:ℝ) < (|discr K| : ℝ) := by linarith
  have hlogd1 : (1:ℝ) ≤ Real.log (|discr K| : ℝ) := by
    rw [Real.le_log_iff_exp_le hd0]
    calc Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
      _ ≤ (|discr K| : ℝ) := by linarith
  set L : ℝ := Real.log (|discr K| : ℝ) with hL_def
  have hL0 : (0:ℝ) < L := by linarith
  set s : ℝ := Real.sqrt L with hs_def
  have hs1 : (1:ℝ) ≤ s := by
    rw [hs_def, show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hlogd1
  have hs0 : (0:ℝ) < s := by linarith
  have hs2 : s^2 = L := Real.sq_sqrt hL0.le
  -- ### the σ-instantiation of the Landau–Stark estimate
  set σ : ℝ := 1 + 1/s with hσ_def
  have hσ1 : (1:ℝ) < σ := by
    rw [hσ_def]
    have : (0:ℝ) < 1/s := by positivity
    linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσ_def]
    have : 1/s ≤ 1 := by
      rw [div_le_one hs0]
      exact hs1
    linarith
  have hK := landau_stark_estimate K hGRH hσ1
  have hdS := dSigma_ge K hn hσ1 hσ2
  have hQ := zeroSumSigma_rat_le hRH
  have hdLow0 : (0:ℝ) ≤ 2 * Real.eulerMascheroniConstant + 2 * Real.log (2*π) - 3 := by
    have h2π : Real.log (2*π) = Real.log 2 + Real.log π :=
      Real.log_mul two_ne_zero Real.pi_ne_zero
    rw [h2π]
    linarith
  -- the zero sums are bounded by `(s+2)²`
  have hkey : (2*σ - 1) * (L + 2/(σ - 1)) = (s+2)^2 := by
    rw [hσ_def, ← hs2]
    have h1 : (1:ℝ) + 1/s - 1 = 1/s := by ring
    rw [h1]
    field_simp
    ring
  have hZS : zeroSumSigma K 1 + zeroSumSigma ℚ 1 ≤ (s+2)^2 := by
    have hσ10 : (0:ℝ) < σ - 1 := by linarith
    have h2σ1 : (1:ℝ) ≤ 2*σ - 1 := by linarith
    have hmono : (2*σ - 1) * (L + 2/(σ - 1) - dSigma K σ)
        ≤ (2*σ - 1) * (L + 2/(σ - 1))
          - (2*σ - 1) * (2 * Real.eulerMascheroniConstant + 2 * Real.log (2*π) - 3) := by
      have := mul_le_mul_of_nonneg_left hdS (by linarith : (0:ℝ) ≤ 2*σ - 1)
      nlinarith
    have habsorb : (2*σ - 1)
          * (2 * Real.eulerMascheroniConstant + 2 * Real.log (2*π) - 3)
        ≥ 2 * Real.eulerMascheroniConstant + 2 * Real.log (2*π) - 3 := by
      nlinarith
    calc zeroSumSigma K 1 + zeroSumSigma ℚ 1
        ≤ (2*σ - 1) * (L + 2/(σ - 1) - dSigma K σ)
          + (2 * Real.eulerMascheroniConstant + 2 * Real.log (2*π) - 3) := by
          exact add_le_add hK hQ
      _ ≤ (2*σ - 1) * (L + 2/(σ - 1)) := by linarith
      _ = (s+2)^2 := hkey
  -- ### the β-piece: `(1/2 + 1/T')·e^{T'/2}·L(T') ≤ 6/√X`
  have hthresh : Real.log (23/3) ≤ Real.log (X/9) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hβ := beta_bound_half hthresh
  have hexpT : Real.exp (Real.log (X/9)/2) = Real.sqrt (X/9) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith : (0:ℝ) < X/9)]
    congr 1
    ring
  have hsqrt9 : Real.sqrt (X/9) = Real.sqrt X / 3 := by
    rw [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_div' X (by norm_num),
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
  have hβ6 : (1/2 + 1/Real.log (X/9)) * Real.exp (Real.log (X/9)/2)
      * archKernelL (Real.log (X/9)) ≤ 6 / Real.sqrt X := by
    refine le_trans hβ (le_of_eq ?_)
    rw [Real.exp_neg, hexpT, hsqrt9, inv_div]
    field_simp
    ring
  -- ### the coefficient bound
  have h4X : (4:ℝ)/Real.log X = 4*(1/Real.log X) := by ring
  have h4T : (4:ℝ)/Real.log (X/9) = 4*(1/Real.log (X/9)) := by ring
  have h6X : 1/Real.log X ≤ 1/Real.log (X/9) :=
    div_le_div_of_nonneg_left (by norm_num) hT'0 hT'X
  have hT'inv0 : (0:ℝ) < 1/Real.log (X/9) := by positivity
  have hCOEFF_le : 2*(1/2:ℝ)^2 * (Real.log X - Real.log (X/9))
      + (2*((1/2:ℝ) + 1/Real.log X) + 2*((1/2:ℝ) + 1/Real.log (X/9)))
      + (4 / Real.log X + 4 / Real.log (X/9))
      ≤ (4/3) * 2.324 * (1 + 3.88 * (1/Real.log (X/9))) := by
    rw [hlog9diff, hlog9, h4X, h4T]
    linarith
  -- ### assemble the two bounds against step1
  have hstep := step1 K hGRH hRH hn hX9
  set nR : ℝ := (Module.finrank ℚ K : ℝ) with hnR_def
  have hnR2 : (2:ℝ) ≤ nR := by
    rw [hnR_def]
    exact_mod_cast hn
  have hlog9nn : (0:ℝ) ≤ Real.log 9 := by
    rw [hlog9]
    linarith
  have harch : (nR - 1) * ((Real.log X - Real.log (X/9))
      * ((1/2 + 1/Real.log (X/9)) * Real.exp (Real.log (X/9)/2)
        * archKernelL (Real.log (X/9))))
      ≤ (nR - 1) * (Real.log 9 * (6/Real.sqrt X)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [hlog9diff]
    exact mul_le_mul_of_nonneg_left hβ6 hlog9nn
  have hZS0 : (0:ℝ) ≤ zeroSumSigma K 1 + zeroSumSigma ℚ 1 :=
    add_nonneg (zeroSumSigma_nonneg K 1) (zeroSumSigma_nonneg ℚ 1)
  have hcoefmul : (2*(1/2:ℝ)^2 * (Real.log X - Real.log (X/9))
      + (2*((1/2:ℝ) + 1/Real.log X) + 2*((1/2:ℝ) + 1/Real.log (X/9)))
      + (4 / Real.log X + 4 / Real.log (X/9)))
        * (zeroSumSigma K 1 + zeroSumSigma ℚ 1)
      ≤ ((4/3) * 2.324 * (1 + 3.88 * (1/Real.log (X/9)))) * (s+2)^2 := by
    refine mul_le_mul hCOEFF_le hZS hZS0 ?_
    have : (0:ℝ) < (4/3) * 2.324 * (1 + 3.88 * (1/Real.log (X/9))) := by positivity
    linarith
  -- ### the archimedean constant `6·log 9 ≤ (4/3)·2.324·4.26`
  have harch2 : (nR - 1) * (Real.log 9 * (6/Real.sqrt X))
      ≤ (4/3) * 2.324 * 4.26 * (nR - 1) / Real.sqrt X := by
    have heq1 : (nR - 1) * (Real.log 9 * (6/Real.sqrt X))
        = (6 * Real.log 9) * ((nR - 1) / Real.sqrt X) := by ring
    have heq2 : (4/3) * 2.324 * 4.26 * (nR - 1) / Real.sqrt X
        = ((4/3) * 2.324 * 4.26) * ((nR - 1) / Real.sqrt X) := by ring
    rw [heq1, heq2]
    refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (by linarith) hsX.le)
    rw [hlog9]
    linarith
  -- ### the right-hand side, expanded (`L = s²` substituted)
  have hRHSexpand : (4/3) * Real.sqrt X * Real.log (3*X)
      * (2.324 * L / (Real.sqrt X * Real.log (3 * X))
        * ((1 + 3.88 / Real.log (X / 9)) * (1 + 2 / s) ^ 2
          + 4.26 * (nR - 1) / (Real.sqrt X * L)))
      = (4/3) * 2.324 * (1 + 3.88 * (1/Real.log (X/9))) * (s+2)^2
        + (4/3) * 2.324 * 4.26 * (nR - 1) / Real.sqrt X := by
    rw [← hs2]
    have hsXne : Real.sqrt X ≠ 0 := hsX.ne'
    have hl3Xne : Real.log (3*X) ≠ 0 := hl3X.ne'
    have hsne : s ≠ 0 := hs0.ne'
    have hT'ne : Real.log (X/9) ≠ 0 := hT'0.ne'
    field_simp
  -- ### chain and cancel
  have hchain : (4/3) * Real.sqrt X * Real.log (3*X)
      * |Real.log (dedekindZeta_residue K) - fK K X|
      ≤ (4/3) * Real.sqrt X * Real.log (3*X)
        * (2.324 * L / (Real.sqrt X * Real.log (3 * X))
          * ((1 + 3.88 / Real.log (X / 9)) * (1 + 2 / s) ^ 2
            + 4.26 * (nR - 1) / (Real.sqrt X * L))) := by
    rw [hRHSexpand]
    calc (4/3) * Real.sqrt X * Real.log (3*X)
        * |Real.log (dedekindZeta_residue K) - fK K X|
        ≤ (nR - 1) * ((Real.log X - Real.log (X/9))
            * ((1/2 + 1/Real.log (X/9)) * Real.exp (Real.log (X/9)/2)
              * archKernelL (Real.log (X/9))))
          + (2*(1/2:ℝ)^2 * (Real.log X - Real.log (X/9))
            + (2*((1/2:ℝ) + 1/Real.log X) + 2*((1/2:ℝ) + 1/Real.log (X/9)))
            + (4 / Real.log X + 4 / Real.log (X/9)))
            * (zeroSumSigma K 1 + zeroSumSigma ℚ 1) := hstep
      _ ≤ (nR - 1) * (Real.log 9 * (6/Real.sqrt X))
          + ((4/3) * 2.324 * (1 + 3.88 * (1/Real.log (X/9)))) * (s+2)^2 :=
          add_le_add harch hcoefmul
      _ ≤ (4/3) * 2.324 * (1 + 3.88 * (1/Real.log (X/9))) * (s+2)^2
          + (4/3) * 2.324 * 4.26 * (nR - 1) / Real.sqrt X := by
          linarith [harch2]
  have hc0 : (0:ℝ) < (4/3) * Real.sqrt X * Real.log (3*X) := by positivity
  exact le_of_mul_le_mul_left hchain hc0

end

end DedekindResidue
