/-
DedekindResidue: the Theorem-1 endgame (B–F §3, lines 564–631).

`bSum`/`bSumRel`/`fK` are Belabas–Friedman's `B_K(X)`/`f_K(X)` (p. 2). This file
bridges them to the machinery: `B_K(X) = −P_K(1, X)` (the σ = 1 plateau sum of
Lemma 3/4 is exactly minus the paper's sum), evaluates the cutoff-weight difference
`eq:Diff`, and assembles `Step1` from `lemma4_explicit2` + `landau_stark_estimate`.
-/
module

public import Mathlib
public import DedekindResidue.Lemma5

@[expose] public section

namespace DedekindResidue

open Complex NumberField Filter MeasureTheory Real

variable (K : Type*) [Field K] [NumberField K]

/-- The single-field prime-power sum
`Σ_{𝔭^m, N𝔭^m < X} (log N𝔭 / N𝔭^{m/2})·(√X·log X / (N𝔭^{m/2}·log N𝔭^m) − 1)`
over nonzero prime ideals `𝔭 ⊆ 𝓞_K` and exponents `m = k+1 ≥ 1` with `N𝔭^m < X`
(`N𝔭 = Ideal.absNorm 𝔭`, real powers). **Design note**: indexed over
`{𝔭 prime} × ℕ` with `m = k+1`, the same index as `plateauSum`, so the σ = 1
plateau bridge `bSum_eq_neg_plateauSum` is a termwise identity.

This is the `K`-part of Belabas–Friedman's `B_K(X)`; the paper's `B_K` itself is
the **relative** sum `∑^{K−ℚ}` — see `bSumRel`. -/
noncomputable def bSum (K : Type*) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  ∑' pk : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ,
    if (Ideal.absNorm pk.1.1 : ℝ) ^ ((((pk.2+1 : ℕ)) : ℝ)) < X then
      (Real.log (Ideal.absNorm pk.1.1)
          / (Ideal.absNorm pk.1.1 : ℝ) ^ ((((pk.2+1 : ℕ)) : ℝ) / 2))
        * (Real.sqrt X * Real.log X
            / ((Ideal.absNorm pk.1.1 : ℝ) ^ ((((pk.2+1 : ℕ)) : ℝ) / 2)
              * Real.log ((Ideal.absNorm pk.1.1 : ℝ) ^ ((((pk.2+1 : ℕ)) : ℝ))))
          - 1)
    else 0

/-- **`B_K(X)`** of Belabas–Friedman (p. 2, verbatim):
`B_K(X) := ∑^{K−ℚ}_{𝔭,m : N𝔭^m < X} (log N𝔭/N𝔭^{m/2})·(√X·log X/(N𝔭^{m/2}·log N𝔭^m) − 1)`,
where "the notation `∑^{K−k}` means that the sum for `k` is subtracted from the
corresponding sum for `K`" — so the rational-prime sum is subtracted from the
`K`-sum. -/
noncomputable def bSumRel (K : Type*) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  bSum K X - bSum ℚ X

/-- `f_K(X) = 3·(B_K(X) − B_K(X/9)) / (2·√X·log(3X))` — Belabas–Friedman, p. 2
(with `B_K` the **relative** `∑^{K−ℚ}` sum `bSumRel`): the computable approximation
to `log κ_K` bounded in Theorem 1. -/
noncomputable def fK (K : Type*) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  3 * (bSumRel K X - bSumRel K (X / 9)) / (2 * Real.sqrt X * Real.log (3 * X))

/-! ### The plateau bridge: `B_K(X) = −P_K(1, X)` -/

/-- **The plateau bridge (T12-a-i)**: the paper's `B_K`-sum is exactly minus the
`σ = 1` plateau sum of the explicit-formula display. At `σ = 1` the plateau tail
`e^{−(σ−1/2)(m log N𝔭 − log X)}` is `√X/N𝔭^{m/2}`, and the boundary term
`N𝔭^m = X` vanishes on both sides (which reconciles the strict/non-strict
cutoffs). -/
theorem bSum_eq_neg_plateauSum {X : ℝ} (hX : 1 < X) :
    bSum K X = -plateauSum K 1 X := by
  rw [bSum, plateauSum, ← tsum_neg]
  refine tsum_congr (fun pk => ?_)
  have hN2 : (2:ℝ) ≤ (Ideal.absNorm pk.1.1 : ℝ) := by
    have hne0 : Ideal.absNorm pk.1.1 ≠ 0 :=
      fun h0 => pk.1.2.2 (Ideal.absNorm_eq_zero_iff.mp h0)
    have hne1 : Ideal.absNorm pk.1.1 ≠ 1 :=
      fun h0 => pk.1.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h0)
    have h2 : 2 ≤ Ideal.absNorm pk.1.1 := by omega
    exact_mod_cast h2
  have hN0 : (0:ℝ) < (Ideal.absNorm pk.1.1 : ℝ) := by linarith
  have hX0 : (0:ℝ) < X := by linarith
  have hlogN : (0:ℝ) < Real.log (Ideal.absNorm pk.1.1) :=
    Real.log_pos (by linarith)
  have hm : (0:ℝ) < (((pk.2+1 : ℕ)) : ℝ) := by positivity
  have hmlogN : (0:ℝ) < (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) :=
    mul_pos hm hlogN
  -- the condition bridge: `N^m < X ↔ m·log N < log X`
  have hcond : (Ideal.absNorm pk.1.1 : ℝ) ^ ((((pk.2+1 : ℕ)) : ℝ)) < X
      ↔ (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) < Real.log X := by
    rw [← Real.log_rpow hN0]
    exact (Real.log_lt_log_iff (Real.rpow_pos_of_pos hN0 _) hX0).symm
  -- the rpow denominators
  have hNh : (0:ℝ) < (Ideal.absNorm pk.1.1 : ℝ) ^ ((((pk.2+1 : ℕ)) : ℝ) / 2) :=
    Real.rpow_pos_of_pos hN0 _
  -- log of the power
  have hlogpow : Real.log ((Ideal.absNorm pk.1.1 : ℝ) ^ ((((pk.2+1 : ℕ)) : ℝ)))
      = (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) :=
    Real.log_rpow hN0 _
  -- the σ = 1 exponential is `√X/N^{m/2}`
  have hexp : Real.exp (-((1:ℝ) - 1/2)
        * ((((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) - Real.log X))
      = Real.sqrt X / (Ideal.absNorm pk.1.1 : ℝ) ^ ((((pk.2+1 : ℕ)) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0, Real.rpow_def_of_pos hN0,
      ← Real.exp_sub]
    congr 1
    ring
  -- the negated-rpow form
  have hnegpow : (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) / 2)
      = ((Ideal.absNorm pk.1.1 : ℝ) ^ ((((pk.2+1 : ℕ)) : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg hN0.le]
    congr 1
    ring
  by_cases hlt : (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) < Real.log X
  · -- interior: both branches active, terms negate
    rw [if_pos (hcond.mpr hlt), if_pos hlt.le, hlogpow, hexp, hnegpow]
    field_simp
    ring
  · by_cases heq : (((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) = Real.log X
    · -- boundary: the paper's term is excluded, the plateau term vanishes
      rw [if_neg (by rw [hcond]; exact hlt), if_pos heq.le, hexp]
      have hlogX0 : Real.log X ≠ 0 := by
        rw [← heq]
        exact hmlogN.ne'
      rw [show Real.sqrt X = Real.exp (Real.log X / 2) by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0]
        congr 1
        ring]
      rw [show (Ideal.absNorm pk.1.1 : ℝ) ^ ((((pk.2+1 : ℕ)) : ℝ) / 2)
          = Real.exp ((((pk.2+1 : ℕ)) : ℝ) * Real.log (Ideal.absNorm pk.1.1) / 2) by
        rw [Real.rpow_def_of_pos hN0]
        congr 1
        ring]
      rw [heq, div_self (Real.exp_pos _).ne', div_self hlogX0]
      norm_num
    · -- exterior: both vanish
      rw [if_neg (by rw [hcond]; intro h1; exact hlt (lt_of_le_of_ne h1.le heq)),
        if_neg (by intro h1; exact hlt (lt_of_le_of_ne h1 heq))]
      norm_num

/-- The relative-sum bridge: `B_{K/ℚ}(X) = −(P_K(1,X) − P_ℚ(1,X))`. -/
theorem bSumRel_eq_neg_plateau_diff {X : ℝ} (hX : 1 < X) :
    bSumRel K X = -(plateauSum K 1 X - plateauSum ℚ 1 X) := by
  rw [bSumRel, bSum_eq_neg_plateauSum K hX, bSum_eq_neg_plateauSum ℚ hX]
  ring

/-! ### eq:Diff and Step1 (T12-a-ii/iii) -/

/-- **eq:Diff** (B–F line 568): the cutoff-weight difference at `a = log 9`:
`√X·log X − √(X/9)·log(X/9) = (2/3)·√X·log(3X)`. -/
theorem cutoff_weight_diff {X : ℝ} (hX9 : 9 < X) :
    Real.log X * Real.sqrt X - Real.log (X/9) * Real.sqrt (X/9)
      = (2/3) * Real.sqrt X * Real.log (3*X) := by
  have hX0 : (0:ℝ) < X := by linarith
  have hsqrt9 : Real.sqrt (X/9) = Real.sqrt X / 3 := by
    rw [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_div' X (by norm_num),
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
  have hlogdiv : Real.log (X/9) = Real.log X - Real.log 9 :=
    Real.log_div hX0.ne' (by norm_num)
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9:ℝ) = 3^2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlog3X : Real.log (3*X) = Real.log 3 + Real.log X :=
    Real.log_mul (by norm_num) hX0.ne'
  rw [hsqrt9, hlogdiv, hlog9, hlog3X]
  ring

/-- **Step1** (B–F line 575, ×2 normalisation): under GRH + RH, `n ≥ 2`, `X > 9`,
`(4/3)·√X·log(3X)·|log κ_K − f_K(X)|` is at most the archimedean bound plus the
`c`-coefficient times the two zero sums, at cutoffs `X` and `X/9`. -/
theorem step1 (hGRH : GeneralizedRiemannHypothesis K) (hRH : RiemannHypothesis)
    (hn : 1 < Module.finrank ℚ K) {X : ℝ} (hX9 : 9 < X) :
    (4/3) * Real.sqrt X * Real.log (3*X)
        * |Real.log (NumberField.dedekindZeta_residue K) - fK K X|
      ≤ ((Module.finrank ℚ K : ℝ) - 1)
          * ((Real.log X - Real.log (X/9))
            * ((1/2 + 1/Real.log (X/9)) * Real.exp (Real.log (X/9)/2)
              * archKernelL (Real.log (X/9))))
        + (2*(1/2:ℝ)^2 * (Real.log X - Real.log (X/9))
            + (2*((1/2:ℝ) + 1/Real.log X) + 2*((1/2:ℝ) + 1/Real.log (X/9)))
            + (4 / Real.log X + 4 / Real.log (X/9)))
          * (zeroSumSigma K 1 + zeroSumSigma ℚ 1) := by
  have hX' : 1 < X/9 := by linarith
  have hXX : X/9 ≤ X := by linarith
  have hX1 : 1 < X := by linarith
  have hkey := lemma4_explicit2 K hGRH hRH hn hX' hXX
  rw [dedekindZeta_residue_rat_eq_one, Real.log_one] at hkey
  have hfacnn : (0:ℝ) ≤ (4/3) * Real.sqrt X * Real.log (3*X) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg X))
      (Real.log_nonneg (by linarith))
  have hfacpos : (0:ℝ) < 2 * Real.sqrt X * Real.log (3*X) := by
    have h1 : 0 < Real.sqrt X := Real.sqrt_pos.mpr (by linarith)
    have h2 : 0 < Real.log (3*X) := Real.log_pos (by linarith)
    positivity
  have hD : bSumRel K X - bSumRel K (X/9)
      = fK K X * (2 * Real.sqrt X * Real.log (3*X)) / 3 := by
    rw [fK, div_mul_cancel₀ _ hfacpos.ne',
      mul_div_cancel_left₀ _ (by norm_num : (3:ℝ) ≠ 0)]
  have hP := bSumRel_eq_neg_plateau_diff K hX1
  have hP' := bSumRel_eq_neg_plateau_diff K hX'
  have hdiff := cutoff_weight_diff hX9
  have habs_eq : 2 * (Real.log X * Real.sqrt X
        * (Real.log (NumberField.dedekindZeta_residue K) - 0))
      - 2 * (Real.log (X/9) * Real.sqrt (X/9)
        * (Real.log (NumberField.dedekindZeta_residue K) - 0))
      + 2 * (plateauSum K 1 X - plateauSum K 1 (X/9))
      - 2 * (plateauSum ℚ 1 X - plateauSum ℚ 1 (X/9))
      = (4/3) * Real.sqrt X * Real.log (3*X)
          * (Real.log (NumberField.dedekindZeta_residue K) - fK K X) := by
    linear_combination 2 * (Real.log (NumberField.dedekindZeta_residue K)) * hdiff
      + 2 * hP - 2 * hP' - 2 * hD
  rw [habs_eq, abs_mul, abs_of_nonneg hfacnn] at hkey
  exact hkey

end DedekindResidue

end
