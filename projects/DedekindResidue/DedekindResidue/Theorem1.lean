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


/-- The exponential weight is at most one for nonnegative arguments. -/
theorem exp_weight_le_one {σ y : ℝ} (hσ : 1/2 < σ) (hy : 0 ≤ y) :
    Real.exp (-(σ - 1/2) * y) ≤ 1 := by
  refine Real.exp_le_one_iff.mpr ?_
  have h1 := mul_nonneg (show (0:ℝ) ≤ σ - 1/2 by linarith) hy
  nlinarith

/-! ### The archimedean integrals, elementarily (T12-b, no digamma) -/

/-- The sinh-weighted exponential integrand is integrable: bounded by `σ−1/2` on
`(0,1]` (since `sinh x ≥ x`), exponentially small beyond. -/
theorem integrableOn_sinh_weight_exp {σ : ℝ} (hσ : 1/2 < σ) :
    MeasureTheory.IntegrableOn
      (fun y : ℝ => 1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y)))
      (Set.Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => 1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y)))
      ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    refine AEStronglyMeasurable.mul ?_ (by fun_prop)
    exact ((measurable_const.div (by fun_prop)).aestronglyMeasurable)
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine MeasureTheory.IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (g := fun _ : ℝ => σ - 1/2)
      (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top.ne))
      (hmeas.mono_set (by rw [hsplit]; exact Set.subset_union_left)) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall (fun y hy => ?_))
    have hy0 : 0 < y := hy.1
    have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
    have hsy : y/2 ≤ Real.sinh (y/2) := Real.self_le_sinh_iff.mpr (by linarith)
    have hexp : 1 - Real.exp (-(σ - 1/2) * y) ≤ (σ - 1/2) * y := by
      have h1 := Real.add_one_le_exp (-((σ - 1/2) * y))
      have h2 : -(σ - 1/2) * y = -((σ - 1/2) * y) := by ring
      rw [h2]
      linarith
    have hexp0 : 0 ≤ 1 - Real.exp (-(σ - 1/2) * y) := by
      linarith [exp_weight_le_one hσ hy0.le]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hexp0)]
    calc 1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y))
        ≤ 1/(2 * (y/2)) * ((σ - 1/2) * y) := by
          refine mul_le_mul ?_ hexp hexp0 (by positivity)
          exact one_div_le_one_div_of_le (by linarith) (by linarith)
      _ = σ - 1/2 := by
          rw [show 2 * (y/2) = y by ring]
          field_simp
  · refine Integrable.mono' (g := fun y : ℝ =>
      (1 - Real.exp (-1))⁻¹ * Real.exp (-(1/2) * y))
      ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0:ℝ) < 1/2)).const_mul _)
      (hmeas.mono_set (by rw [hsplit]; exact Set.subset_union_right)) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun y hy => ?_))
    have hy1 : (1:ℝ) < y := hy
    have hy0 : (0:ℝ) < y := by linarith
    have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
    have hexp0 : 0 ≤ 1 - Real.exp (-(σ - 1/2) * y) := by
      linarith [exp_weight_le_one hσ hy0.le]
    have hexp1 : 1 - Real.exp (-(σ - 1/2) * y) ≤ 1 := by
      have := Real.exp_pos (-(σ - 1/2) * y)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hexp0)]
    have hpos1 : (0:ℝ) < 1 - Real.exp (-1) := by
      have := Real.exp_lt_one_iff.mpr (show (-1:ℝ) < 0 by norm_num)
      linarith
    have hfrac : 1/(2 * Real.sinh (y/2))
        ≤ (1 - Real.exp (-1))⁻¹ * Real.exp (-(1/2) * y) := by
      have hsinh : (1 - Real.exp (-1)) * Real.exp (y/2) ≤ 2 * Real.sinh (y/2) := by
        rw [two_sinh_half_eq']
        have h1 : Real.exp (-y) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
        have h2 := Real.exp_pos (y/2)
        nlinarith
      have h2s : (0:ℝ) < 2 * Real.sinh (y/2) := by positivity
      rw [div_le_iff₀ h2s]
      have h3 : Real.exp (-(1/2) * y) * Real.exp (y/2) = 1 := by
        rw [← Real.exp_add, show -(1/2) * y + y/2 = 0 by ring, Real.exp_zero]
      calc (1:ℝ) = ((1 - Real.exp (-1))⁻¹ * (1 - Real.exp (-1)))
            * (Real.exp (-(1/2) * y) * Real.exp (y/2)) := by
            rw [inv_mul_cancel₀ hpos1.ne', h3, mul_one]
        _ = (1 - Real.exp (-1))⁻¹ * Real.exp (-(1/2) * y)
            * ((1 - Real.exp (-1)) * Real.exp (y/2)) := by ring
        _ ≤ (1 - Real.exp (-1))⁻¹ * Real.exp (-(1/2) * y) * (2 * Real.sinh (y/2)) :=
            mul_le_mul_of_nonneg_left hsinh (by positivity)
    calc 1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y))
        ≤ 1/(2 * Real.sinh (y/2)) * 1 := mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ = 1/(2 * Real.sinh (y/2)) := mul_one _
      _ ≤ (1 - Real.exp (-1))⁻¹ * Real.exp (-(1/2) * y) := hfrac

/-- **The sinh-integral recurrence** `I(σ+1) = I(σ) + 1/σ`: the difference
integrand collapses to `e^{−σy}` (the `sinh` cancels). -/
theorem sinh_int_rec {σ : ℝ} (hσ : 1/2 < σ) :
    (∫ y in Set.Ioi (0:ℝ),
        1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-((σ+1) - 1/2) * y)))
      = (∫ y in Set.Ioi (0:ℝ),
          1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y))) + 1/σ := by
  have hσ0 : (0:ℝ) < σ := by linarith
  have hdiff : (∫ y in Set.Ioi (0:ℝ),
        1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-((σ+1) - 1/2) * y)))
      - (∫ y in Set.Ioi (0:ℝ),
          1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y))) = 1/σ := by
    rw [← MeasureTheory.integral_sub (integrableOn_sinh_weight_exp (by linarith))
      (integrableOn_sinh_weight_exp hσ)]
    have hcongr : ∀ y ∈ Set.Ioi (0:ℝ),
        1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-((σ+1) - 1/2) * y))
          - 1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y))
        = Real.exp (-(σ * y)) := by
      intro y hy
      have hy0 : (0:ℝ) < y := hy
      have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
      have h2s : (0:ℝ) < 2 * Real.sinh (y/2) := by positivity
      have hkey : Real.exp (-(σ - 1/2) * y) - Real.exp (-((σ+1) - 1/2) * y)
          = Real.exp (-(σ * y)) * (2 * Real.sinh (y/2)) := by
        rw [Real.sinh_eq,
          show -(σ - 1/2) * y = -(σ * y) + y/2 by ring,
          show -((σ+1) - 1/2) * y = -(σ * y) + -(y/2) by ring,
          Real.exp_add, Real.exp_add]
        ring
      have hgoal : 1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-((σ+1) - 1/2) * y))
          - 1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y))
          = (Real.exp (-(σ - 1/2) * y) - Real.exp (-((σ+1) - 1/2) * y))
            / (2 * Real.sinh (y/2)) := by
        ring
      rw [hgoal, hkey, mul_div_assoc, div_self h2s.ne', mul_one]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
      integral_exp_neg_mul_Ioi hσ0]
  linarith

/-- **Monotonicity of the sinh integral in `σ`.** -/
theorem sinh_int_mono {σ σ' : ℝ} (hσ : 1/2 < σ) (hσσ' : σ ≤ σ') :
    (∫ y in Set.Ioi (0:ℝ),
        1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y)))
      ≤ ∫ y in Set.Ioi (0:ℝ),
          1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ' - 1/2) * y)) := by
  refine MeasureTheory.setIntegral_mono_on (integrableOn_sinh_weight_exp hσ)
    (integrableOn_sinh_weight_exp (by linarith)) measurableSet_Ioi
    (fun y hy => ?_)
  have hy0 : (0:ℝ) < y := hy
  have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : Real.exp (-(σ' - 1/2) * y) ≤ Real.exp (-(σ - 1/2) * y) :=
    Real.exp_le_exp.mpr (by nlinarith)
  linarith

/-- **`I(1) = 2 log 2`** by the fundamental theorem of calculus: the integrand is
`e^{−y/2}/(1+e^{−y/2})`, the derivative of `−2·log(1+e^{−y/2})`. -/
theorem sinh_int_one :
    (∫ y in Set.Ioi (0:ℝ),
        1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-((1:ℝ) - 1/2) * y)))
      = 2 * Real.log 2 := by
  have hderiv : ∀ y ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun y : ℝ => -2 * Real.log (1 + Real.exp (-(y/2))))
        (1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-((1:ℝ) - 1/2) * y))) y := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
    have hpos : (0:ℝ) < 1 + Real.exp (-(y/2)) := by positivity
    have h1 : HasDerivAt (fun y : ℝ => -(y/2)) (-(1/2)) y := by
      have h1a := (hasDerivAt_id y).const_mul (-(1/2) : ℝ)
      simp only [id_eq, mul_one] at h1a
      exact h1a.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun x => by ring))
    have h2 := ((h1.exp).const_add 1).log hpos.ne'
    have h3 := h2.const_mul (-2)
    refine h3.congr_deriv ?_
    have hem : Real.exp (-(y/2)) * Real.exp (-(y/2)) = Real.exp (-y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hform : Real.exp (-((1:ℝ) - 1/2) * y) = Real.exp (-(y/2)) := by
      congr 1
      ring
    rw [hform, two_sinh_half_eq']
    have hene : (0:ℝ) < 1 - Real.exp (-y) := by
      have h4 : Real.exp (-y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have hey : Real.exp (-(y/2)) * Real.exp (y/2) = 1 := by
      rw [← Real.exp_add]
      norm_num
    field_simp
    nlinarith [hem, hey, Real.exp_pos (y/2), Real.exp_pos (-(y/2))]
  have hlim : Filter.Tendsto (fun y : ℝ => -2 * Real.log (1 + Real.exp (-(y/2))))
      atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun y : ℝ => Real.exp (-(y/2))) atTop (nhds 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      have h1 := Tendsto.const_mul_atTop_of_neg
        (show (-(1/2) : ℝ) < 0 by norm_num) (tendsto_id (α := ℝ))
      refine h1.congr (fun y => ?_)
      simp only [id_eq]
      ring
    have h3 : Filter.Tendsto (fun y : ℝ => 1 + Real.exp (-(y/2))) atTop (nhds 1) := by
      have h4 := (tendsto_const_nhds (x := (1:ℝ)) (f := atTop)).add h2
      rw [add_zero] at h4
      exact h4
    have h5 := ((Real.continuousAt_log one_ne_zero).tendsto).comp h3
    rw [Real.log_one] at h5
    have h6 := h5.const_mul (-2)
    simpa using h6
  have hcont : ContinuousWithinAt (fun y : ℝ => -2 * Real.log (1 + Real.exp (-(y/2))))
      (Set.Ici 0) 0 := by
    refine Continuous.continuousWithinAt ?_
    refine continuous_const.mul (Continuous.log (by fun_prop) (fun y => ?_))
    positivity
  have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    (integrableOn_sinh_weight_exp (by norm_num)) hlim
  rw [hkey]
  norm_num

/-- The cosh integrand is integrable (dominated by the pure cosh kernel). -/
theorem integrableOn_cosh_weight_exp {σ : ℝ} (hσ : 1/2 < σ) :
    MeasureTheory.IntegrableOn
      (fun y : ℝ => 1/(2 * Real.cosh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y)))
      (Set.Ioi 0) := by
  refine (integrableOn_sinh_weight_exp hσ).mono' ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ (by fun_prop)
    exact ((measurable_const.div (by fun_prop)).aestronglyMeasurable)
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun y hy => ?_))
    have hy0 : (0:ℝ) < y := hy
    have hs : 0 < Real.sinh (y/2) := Real.sinh_pos_iff.mpr (by linarith)
    have hc : (0:ℝ) < Real.cosh (y/2) := Real.cosh_pos _
    have hsc : Real.sinh (y/2) < Real.cosh (y/2) := Real.sinh_lt_cosh _
    have h1 : Real.exp (-(σ - 1/2) * y) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith
    have h2 : (0:ℝ) ≤ 1 - Real.exp (-(σ - 1/2) * y) := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ h2
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- The pure `1/(2 * cosh (y/2))` kernel is integrable on `Set.Ioi 0`, dominated by
`e^(-y/2)`. Shared by `cosh_int_le` and `cosh_int_two`. -/
theorem integrableOn_inv_two_cosh_half :
    MeasureTheory.IntegrableOn
      (fun y : ℝ => 1/(2 * Real.cosh (y/2))) (Set.Ioi 0) := by
  refine Integrable.mono' (g := fun y : ℝ => Real.exp (-(1/2) * y))
    (exp_neg_integrableOn_Ioi 0 (by norm_num)) ?_ ?_
  · exact ((measurable_const.div (by fun_prop)).aestronglyMeasurable)
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall (fun y _ => ?_))
    have hc : (0:ℝ) < Real.cosh (y/2) := Real.cosh_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hch : Real.exp (y/2) ≤ 2 * Real.cosh (y/2) := by
      rw [Real.cosh_eq]
      have := Real.exp_pos (-(y/2))
      linarith
    have hde : Real.exp (-(1/2) * y) * Real.exp (y/2) = 1 := by
      rw [← Real.exp_add, show -(1/2) * y + y/2 = 0 by ring, Real.exp_zero]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.exp_pos (-(1/2) * y), Real.exp_pos (y/2)]

/-- **The cosh integral is at most `π/2`.** -/
theorem cosh_int_le {σ : ℝ} (hσ : 1/2 < σ) :
    (∫ y in Set.Ioi (0:ℝ),
        1/(2 * Real.cosh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y))) ≤ π/2 := by
  rw [← integral_inv_two_cosh_half]
  have hcoshint := integrableOn_inv_two_cosh_half
  refine MeasureTheory.setIntegral_mono_on (integrableOn_cosh_weight_exp hσ)
    hcoshint measurableSet_Ioi (fun y hy => ?_)
  have hy0 : (0:ℝ) < y := hy
  have hc : (0:ℝ) < Real.cosh (y/2) := Real.cosh_pos _
  have h1 : (0:ℝ) < Real.exp (-(σ - 1/2) * y) := Real.exp_pos _
  nlinarith [mul_pos (show (0:ℝ) < 1/(2 * Real.cosh (y/2)) by positivity) h1]

/-- **`I_cosh(2) = π/2 − (1 − log 2)`** by FTC: the tail integrand
`e^{−3y/2}/(2cosh(y/2)) = e^{−2y}/(1+e^{−y})` is the derivative of
`log(1+e^{−y}) − e^{−y}`. -/
theorem cosh_int_two :
    (∫ y in Set.Ioi (0:ℝ),
        1/(2 * Real.cosh (y/2)) * (1 - Real.exp (-((2:ℝ) - 1/2) * y)))
      = π/2 - (1 - Real.log 2) := by
  have hJint : MeasureTheory.IntegrableOn
      (fun y : ℝ => 1/(2 * Real.cosh (y/2)) * Real.exp (-((2:ℝ) - 1/2) * y))
      (Set.Ioi 0) := by
    refine Integrable.mono' (g := fun y : ℝ => Real.exp (-(3/2) * y))
      (exp_neg_integrableOn_Ioi 0 (by norm_num)) ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ (by fun_prop)
      exact ((measurable_const.div (by fun_prop)).aestronglyMeasurable)
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall (fun y _ => ?_))
      have hc : (0:ℝ) < Real.cosh (y/2) := Real.cosh_pos _
      have hc1 : (1:ℝ) ≤ Real.cosh (y/2) := Real.one_le_cosh _
      have he := Real.exp_pos (-((2:ℝ) - 1/2) * y)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hform : Real.exp (-((2:ℝ) - 1/2) * y) = Real.exp (-(3/2) * y) := by
        congr 1
        ring
      rw [hform]
      have h1 : 1/(2 * Real.cosh (y/2)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      nlinarith [Real.exp_pos (-(3/2) * y)]
  have hcoshint := integrableOn_inv_two_cosh_half
  have hsplit : (∫ y in Set.Ioi (0:ℝ),
      1/(2 * Real.cosh (y/2)) * (1 - Real.exp (-((2:ℝ) - 1/2) * y)))
      = (∫ y in Set.Ioi (0:ℝ), 1/(2 * Real.cosh (y/2)))
        - ∫ y in Set.Ioi (0:ℝ), 1/(2 * Real.cosh (y/2))
            * Real.exp (-((2:ℝ) - 1/2) * y) := by
    rw [← MeasureTheory.integral_sub hcoshint hJint]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    ring
  have hJ : (∫ y in Set.Ioi (0:ℝ),
      1/(2 * Real.cosh (y/2)) * Real.exp (-((2:ℝ) - 1/2) * y)) = 1 - Real.log 2 := by
    have hderiv : ∀ y ∈ Set.Ioi (0:ℝ),
        HasDerivAt (fun y : ℝ => Real.log (1 + Real.exp (-y)) - Real.exp (-y))
          (1/(2 * Real.cosh (y/2)) * Real.exp (-((2:ℝ) - 1/2) * y)) y := by
      intro y _
      have hpos : (0:ℝ) < 1 + Real.exp (-y) := by positivity
      have h1 : HasDerivAt (fun y : ℝ => -y) (-1) y := by
        have h1a := (hasDerivAt_id y).const_mul (-1 : ℝ)
        simp only [id_eq, mul_one] at h1a
        exact h1a.congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun x => by ring))
      have h2 := ((h1.exp).const_add 1).log hpos.ne'
      have h3 := h2.sub h1.exp
      refine h3.congr_deriv ?_
      have hc : (0:ℝ) < Real.cosh (y/2) := Real.cosh_pos _
      have hch : 2 * Real.cosh (y/2) = Real.exp (y/2) * (1 + Real.exp (-y)) := by
        rw [Real.cosh_eq, mul_add, mul_one, ← Real.exp_add,
          show y/2 + -y = -(y/2) by ring]
        ring
      have hform : Real.exp (-((2:ℝ) - 1/2) * y)
          = Real.exp (-y) * Real.exp (-y) * Real.exp (y/2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hform, hch]
      have he := Real.exp_pos (-y)
      have hey := Real.exp_pos (y/2)
      field_simp
      ring
    have hlim : Filter.Tendsto
        (fun y : ℝ => Real.log (1 + Real.exp (-y)) - Real.exp (-y)) atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun y : ℝ => Real.exp (-y)) atTop (nhds 0) := by
        refine Real.tendsto_exp_atBot.comp ?_
        exact tendsto_neg_atTop_atBot
      have h3 : Filter.Tendsto (fun y : ℝ => 1 + Real.exp (-y)) atTop (nhds 1) := by
        have h4 := (tendsto_const_nhds (x := (1:ℝ)) (f := atTop)).add h2
        rw [add_zero] at h4
        exact h4
      have h5 := ((Real.continuousAt_log one_ne_zero).tendsto).comp h3
      rw [Real.log_one] at h5
      have h6 := h5.sub h2
      rw [sub_zero] at h6
      exact h6
    have hcont : ContinuousWithinAt
        (fun y : ℝ => Real.log (1 + Real.exp (-y)) - Real.exp (-y)) (Set.Ici 0) 0 := by
      refine Continuous.continuousWithinAt ?_
      refine Continuous.sub (Continuous.log (by fun_prop) (fun y => ?_)) (by fun_prop)
      positivity
    have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
      hJint hlim
    rw [hkey]
    norm_num
  rw [hsplit, integral_inv_two_cosh_half, hJ]

/-! ### The `d_{K,σ}` numerics (T12-b N3) -/

/-- `ℚ` has exactly one real place. -/
theorem nrRealPlaces_rat : NumberField.InfinitePlace.nrRealPlaces ℚ = 1 :=
  NumberField.InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ)

/-- `ℚ` has no complex places. -/
theorem nrComplexPlaces_rat : NumberField.InfinitePlace.nrComplexPlaces ℚ = 0 := by
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank ℚ
  rw [nrRealPlaces_rat, Module.finrank_self] at h
  omega

/-- **`I_sinh(2) = 1 + 2 log 2`** from the recurrence and `I_sinh(1) = 2 log 2`. -/
theorem sinh_int_two :
    (∫ y in Set.Ioi (0:ℝ),
        1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-((2:ℝ) - 1/2) * y)))
      = 1 + 2 * Real.log 2 := by
  have h := sinh_int_rec (σ := 1) (by norm_num)
  rw [sinh_int_one] at h
  rw [show ((2:ℝ) - 1/2) = ((1:ℝ)+1) - 1/2 by norm_num, h]
  ring

/-- The von Mangoldt Dirichlet sum is nonnegative. -/
theorem vonMangoldtSum_nonneg (σ : ℝ) : 0 ≤ vonMangoldtSum K σ :=
  tsum_nonneg fun _ => mul_nonneg (Real.log_natCast_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- `log (8 * π) = 3 * log 2 + log π`, the Γ-constant that appears in the `dSigma`
numerics (`dSigma_rat_two_eq`, `dSigma_ge`). -/
theorem log_eight_mul_pi_eq : Real.log (8 * π) = 3 * Real.log 2 + Real.log π := by
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero,
    show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
  push_cast
  ring

/-- **`d_{ℚ,2} = 2W + γ + log π − 1`**, `W = vonMangoldtSum ℚ 2` (B–F lines 603–612 at
`k = ℚ`, `σ = 2`): with `n = r₁ = 1`, `I_sinh(2) = 1 + 2 log 2`,
`I_cosh(2) = π/2 − (1 − log 2)` and `log 8π = 3 log 2 + log π`, the Γ-constant and the
archimedean integrals collapse elementarily. -/
theorem dSigma_rat_two_eq :
    dSigma ℚ 2 = 2 * vonMangoldtSum ℚ 2
      + Real.eulerMascheroniConstant + Real.log π - 1 := by
  have hlog8π := log_eight_mul_pi_eq
  rw [dSigma, nrRealPlaces_rat, nrComplexPlaces_rat, sinh_int_two, cosh_int_two, hlog8π]
  push_cast
  ring

/-- **The lower bound `d_{K,σ} ≥ 2γ + 2 log 2π − 3`** for `1 < σ ≤ 2`, `n ≥ 2`
(B–F lines 603–612): drop `W ≥ 0` and `r₁·(π/2 − I_cosh) ≥ 0`, bound
`n·(γ + log 8π − I_sinh(σ)) ≥ 2·(…)` (the bracket is nonnegative since
`I_sinh(σ) ≤ I_sinh(2) = 1 + 2log2 < γ + log 8π`), and use
`I_sinh(σ) + 1/σ = I_sinh(σ+1) ≤ I_sinh(3) = 3/2 + 2 log 2`. -/
theorem dSigma_ge (hn : 1 < Module.finrank ℚ K) {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    2 * Real.eulerMascheroniConstant + 2 * Real.log (2*π) - 3 ≤ dSigma K σ := by
  have hσh : (1:ℝ)/2 < σ := by linarith
  -- the sinh integral at σ, bounded via the recurrence and monotonicity
  have hrec := sinh_int_rec hσh
  have hmono := sinh_int_mono (σ := σ + 1) (σ' := 3) (by linarith) (by linarith)
  have h3 : (∫ y in Set.Ioi (0:ℝ),
      1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-((3:ℝ) - 1/2) * y)))
      = 3/2 + 2 * Real.log 2 := by
    have h := sinh_int_rec (σ := 2) (by norm_num)
    rw [sinh_int_two] at h
    rw [show ((3:ℝ) - 1/2) = ((2:ℝ)+1) - 1/2 by norm_num, h]
    ring
  have hIs_le : (∫ y in Set.Ioi (0:ℝ),
      1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y)))
      ≤ 3/2 + 2 * Real.log 2 - 1/σ := by
    rw [h3] at hmono
    linarith
  -- the cosh integral is at most π/2
  have hIc_le := cosh_int_le hσh
  -- numeric certificates for the bracket
  have hγ : (1:ℝ)/2 < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl3 : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
  have hlπ : Real.log 3 ≤ Real.log π :=
    Real.log_le_log (by norm_num) Real.pi_gt_three.le
  have hlog8π := log_eight_mul_pi_eq
  have hlog2π : Real.log (2*π) = Real.log 2 + Real.log π :=
    Real.log_mul (by norm_num) Real.pi_ne_zero
  have hσ0 : (0:ℝ) < σ := by linarith
  have hinvσ : (1:ℝ)/2 ≤ 1/σ := by
    rw [div_le_div_iff₀ (by norm_num) hσ0]
    linarith
  -- the bracket `γ + log 8π − I_sinh(σ) ≥ 0` (in `3log2 + logπ` form)
  have hbr : 0 ≤ Real.eulerMascheroniConstant + (3 * Real.log 2 + Real.log π)
      - (∫ y in Set.Ioi (0:ℝ),
          1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y))) := by
    linarith
  -- place counts
  have hW := vonMangoldtSum_nonneg K σ
  have hcard := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcardR : (NumberField.InfinitePlace.nrRealPlaces K : ℝ)
      + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ)
      = (Module.finrank ℚ K : ℝ) := by
    rw [← hcard]
    push_cast
    ring
  have hsumcast : ((NumberField.InfinitePlace.nrRealPlaces K
      + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ) : ℝ)
      = (NumberField.InfinitePlace.nrRealPlaces K : ℝ)
        + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ) := by
    push_cast
    ring
  have hn2R : (2:ℝ) ≤ (NumberField.InfinitePlace.nrRealPlaces K : ℝ)
      + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ) := by
    rw [hcardR]
    have : (2:ℕ) ≤ Module.finrank ℚ K := hn
    exact_mod_cast this
  have hr1nn : (0:ℝ) ≤ (NumberField.InfinitePlace.nrRealPlaces K : ℝ) :=
    Nat.cast_nonneg _
  -- assemble, over opaque atoms
  rw [dSigma, hsumcast, hlog8π, hlog2π]
  generalize hISg : (∫ y in Set.Ioi (0:ℝ),
      1/(2 * Real.sinh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y))) = IS at hIs_le hbr ⊢
  generalize hICg : (∫ y in Set.Ioi (0:ℝ),
      1/(2 * Real.cosh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y))) = IC at hIc_le ⊢
  generalize hR1g : (NumberField.InfinitePlace.nrRealPlaces K : ℝ) = R1 at hn2R hr1nn ⊢
  generalize hR2g : (NumberField.InfinitePlace.nrComplexPlaces K : ℝ) = R2 at hn2R ⊢
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ R1 + 2*R2 - 2) hbr,
    mul_nonneg hr1nn (by linarith : (0:ℝ) ≤ π/2 - IC), hW, hIs_le,
    (by ring : (2:ℝ)/σ = 2*(1/σ))]

/-! ### The ℚ-side von Mangoldt certificate (T12-b N4) -/

/-- The natural number `p` is a prime element of `𝓞 ℚ` when it is a prime
(transport along `𝓞 ℚ ≃+* ℤ`). -/
theorem prime_natCast_ringOfIntegers_rat {p : ℕ} (hp : p.Prime) :
    Prime ((p : 𝓞 ℚ)) := by
  have h : Prime (Rat.ringOfIntegersEquiv ((p : 𝓞 ℚ))) := by
    rw [map_natCast]
    exact Nat.prime_iff_prime_int.mp hp
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv).mp h

/-- The rational prime `p` as a nonzero prime ideal of `𝓞 ℚ`. -/
noncomputable def ratPrimeIdeal (p : ℕ) (hp : p.Prime) :
    {𝔭 : Ideal (𝓞 ℚ) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
  ⟨Ideal.span {(p : 𝓞 ℚ)},
    (Ideal.span_singleton_prime (prime_natCast_ringOfIntegers_rat hp).ne_zero).mpr
      (prime_natCast_ringOfIntegers_rat hp),
    fun hbot => (prime_natCast_ringOfIntegers_rat hp).ne_zero
      (Ideal.span_singleton_eq_bot.mp hbot)⟩

/-- The ideal `ratPrimeIdeal p` has absolute norm `p` (the norm of `p : 𝓞 ℚ`
is `p^1` since `𝓞 ℚ` has `ℤ`-rank one). -/
theorem absNorm_ratPrimeIdeal (p : ℕ) (hp : p.Prime) :
    Ideal.absNorm (ratPrimeIdeal p hp).1 = p := by
  show Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) = p
  rw [Ideal.absNorm_span_singleton,
    show ((p : 𝓞 ℚ)) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) from (map_natCast _ p).symm,
    Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self,
    pow_one, Int.natAbs_natCast]

/-- The von Mangoldt term at `(ratPrimeIdeal p, m)` and `σ = 2` is
`log p / p^(2(m+1))`. -/
theorem vonMangoldt_term_ratPrimeIdeal (p : ℕ) (hp : p.Prime) (m : ℕ) :
    Real.log (Ideal.absNorm (ratPrimeIdeal p hp).1)
      * (Ideal.absNorm (ratPrimeIdeal p hp).1 : ℝ) ^ (-(((m+1 : ℕ)) : ℝ) * 2)
    = Real.log p * ((p:ℝ) ^ (2*(m+1)))⁻¹ := by
  rw [absNorm_ratPrimeIdeal,
    show (-(((m+1 : ℕ)) : ℝ) * 2) = -((2*(m+1) : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg (Nat.cast_nonneg p), Real.rpow_natCast]

/-- The nine sample indices `(2,1),(2,2),(2,3),(3,1),(3,2),(5,1),(7,1),(11,1),(13,1)`
(prime, exponent) for the `σ = 2` von Mangoldt certificate. -/
noncomputable def vmIndex : Fin 9 → {𝔭 : Ideal (𝓞 ℚ) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ :=
  ![(ratPrimeIdeal 2 (by norm_num), 0), (ratPrimeIdeal 2 (by norm_num), 1),
    (ratPrimeIdeal 2 (by norm_num), 2), (ratPrimeIdeal 3 (by norm_num), 0),
    (ratPrimeIdeal 3 (by norm_num), 1), (ratPrimeIdeal 5 (by norm_num), 0),
    (ratPrimeIdeal 7 (by norm_num), 0), (ratPrimeIdeal 11 (by norm_num), 0),
    (ratPrimeIdeal 13 (by norm_num), 0)]

/-- The nine sample indices are pairwise distinct (separated by the invariant
`(absNorm, exponent)`). -/
theorem vmIndex_injective : Function.Injective vmIndex := by
  have hkey : ∀ i, (Ideal.absNorm (vmIndex i).1.1, (vmIndex i).2)
      = ![(2,0),(2,1),(2,2),(3,0),(3,1),(5,0),(7,0),(11,0),(13,0)] i := by
    intro i
    fin_cases i <;>
      simp [vmIndex, absNorm_ratPrimeIdeal]
  have htable : Function.Injective
      (![(2,0),(2,1),(2,2),(3,0),(3,1),(5,0),(7,0),(11,0),(13,0)] : Fin 9 → ℕ × ℕ) := by
    decide
  intro i j hij
  refine htable ?_
  rw [← hkey i, ← hkey j, hij]

/-- **The nine-term von Mangoldt certificate at `σ = 2`** (T12-b N4):
`W = Σ_{𝔭,m} log N𝔭·N𝔭^{−2m} ≥ (21/64)·log 2 + (10/81)·log 3 + log 5/25 + log 7/49
+ log 11/121 + log 13/169` (the terms `2^1,2^2,2^3,3^1,3^2,5,7,11,13`). -/
theorem vonMangoldtSum_rat_two_ge :
    Real.log 2 * (21/64) + Real.log 3 * (10/81) + Real.log 5 * (1/25)
      + Real.log 7 * (1/49) + Real.log 11 * (1/121) + Real.log 13 * (1/169)
      ≤ vonMangoldtSum ℚ 2 := by
  classical
  have hsum := summable_primeIdeal_pow_log_rpow (K := ℚ) (by norm_num : (1:ℝ) < 2)
  have hle := Summable.sum_le_tsum (f := fun pk :
        {𝔭 : Ideal (𝓞 ℚ) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} × ℕ =>
      Real.log (Ideal.absNorm pk.1.1)
        * (Ideal.absNorm pk.1.1 : ℝ) ^ (-(((pk.2+1 : ℕ)) : ℝ) * 2))
    (Finset.univ.map ⟨vmIndex, vmIndex_injective⟩)
    (fun _ _ => mul_nonneg (Real.log_natCast_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hsum
  rw [Finset.sum_map] at hle
  refine le_trans (le_of_eq ?_) hle
  simp only [Function.Embedding.coeFn_mk, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, vmIndex]
  simp only [vonMangoldt_term_ratPrimeIdeal]
  push_cast
  norm_num
  ring

/-- From `2 ^ a ≤ p ^ b` in `ℕ` (with `2 ≤ p`), deduce `a * log 2 ≤ b * log p` by
taking logs of the cast inequality. The `hl7`/`hl11`/`hl13` power comparisons in
`zeroSumSigma_rat_le` are instances. -/
theorem mul_log_two_le_mul_log_of_pow_le {a b p : ℕ} (_hp : 2 ≤ p) (h : 2 ^ a ≤ p ^ b) :
    (a : ℝ) * Real.log 2 ≤ (b : ℝ) * Real.log p := by
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < 2 ^ a)
    (by exact_mod_cast h : ((2:ℝ)) ^ a ≤ (p:ℝ) ^ b)
  rwa [Real.log_pow, Real.log_pow] at hlog

/-- **The ℚ-zero-sum master certificate** (T12-b N4, replacing B–F's `0.023095`):
under RH, `Σ_ρ m_ρ/(¼+γ_ρ²) ≤ 2γ_E + 2 log 2π − 3` — the ℚ-zero sum is at most the
`d_{K,σ}` lower bound. Via `landau_stark_estimate` at `ℚ`, `σ = 2` (`log Δ_ℚ = 0`),
`d_{ℚ,2} = 2W + γ_E + log π − 1`, and the nine-term `W`-certificate, the inequality
reduces to `12 ≤ 6W + 5γ_E + 5 log π + 2 log 2`, which holds with margin `0.38`. -/
theorem zeroSumSigma_rat_le (hRH : RiemannHypothesis) :
    zeroSumSigma ℚ 1 ≤ 2 * Real.eulerMascheroniConstant + 2 * Real.log (2*π) - 3 := by
  have h1 := landau_stark_estimate ℚ (generalizedRiemannHypothesis_rat hRH)
    (σ := 2) (by norm_num)
  rw [Rat.numberField_discr] at h1
  norm_num [Real.log_one] at h1
  rw [dSigma_rat_two_eq] at h1
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hl2 := Real.log_two_gt_d9
  have hl3 := Real.log_three_gt_d9
  have hl5 := Real.log_five_gt_d9
  have hlπ : Real.log 3 ≤ Real.log π :=
    Real.log_le_log (by norm_num) Real.pi_gt_three.le
  have hl7 : 14 * Real.log 2 ≤ 5 * Real.log 7 := by
    exact_mod_cast mul_log_two_le_mul_log_of_pow_le (a := 14) (b := 5) (p := 7)
      (by norm_num) (by norm_num)
  have hl11 : 10 * Real.log 2 ≤ 3 * Real.log 11 := by
    exact_mod_cast mul_log_two_le_mul_log_of_pow_le (a := 10) (b := 3) (p := 11)
      (by norm_num) (by norm_num)
  have hl13 : 11 * Real.log 2 ≤ 3 * Real.log 13 := by
    exact_mod_cast mul_log_two_le_mul_log_of_pow_le (a := 11) (b := 3) (p := 13)
      (by norm_num) (by norm_num)
  have hW := vonMangoldtSum_rat_two_ge
  have hlog2π : Real.log (2*π) = Real.log 2 + Real.log π :=
    Real.log_mul two_ne_zero Real.pi_ne_zero
  rw [hlog2π]
  linarith

/-! ### The β-bound (T12-b N5) -/

/-- The quintic Mercator upper bound `log(1+u) ≤ u − u²/2 + u³/3 − u⁴/4 + u⁵/5` for
`u ≥ 0`: the deficit has derivative `u⁵/(1+u) ≥ 0` and vanishes at `0`. -/
theorem log_one_add_le_quintic {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ u - u^2/2 + u^3/3 - u^4/4 + u^5/5 := by
  have hderiv : ∀ x ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun v : ℝ => v - v^2/2 + v^3/3 - v^4/4 + v^5/5 - Real.log (1 + v))
        (1 - x + x^2 - x^3 + x^4 - 1/(1+x)) x := by
    intro x hx
    have hx0 : (0:ℝ) ≤ x := hx
    have h1x : (0:ℝ) < 1 + x := by linarith
    have hp : HasDerivAt (fun v : ℝ => v - v^2/2 + v^3/3 - v^4/4 + v^5/5)
        (1 - x + x^2 - x^3 + x^4) x := by
      have h1 : HasDerivAt (fun v : ℝ => v) 1 x := hasDerivAt_id' x
      have h2 := (hasDerivAt_pow 2 x).div_const 2
      have h3 := (hasDerivAt_pow 3 x).div_const 3
      have h4 := (hasDerivAt_pow 4 x).div_const 4
      have h5 := (hasDerivAt_pow 5 x).div_const 5
      have h := (((h1.sub h2).add h3).sub h4).add h5
      refine h.congr_deriv ?_
      norm_num
    have hl : HasDerivAt (fun v : ℝ => Real.log (1 + v)) (1/(1+x)) x := by
      have h := ((hasDerivAt_id x).const_add (1:ℝ)).log h1x.ne'
      simpa using h
    exact hp.sub hl
  have hmono : MonotoneOn
      (fun v : ℝ => v - v^2/2 + v^3/3 - v^4/4 + v^5/5 - Real.log (1 + v))
      (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · intro x hx
      exact ((hderiv x hx).continuousAt).continuousWithinAt
    · rw [interior_Ici]
      intro x hx
      exact ((hderiv x
        (Set.mem_Ici.mpr (Set.mem_Ioi.mp hx).le)).differentiableAt).differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      rw [(hderiv x (Set.mem_Ici.mpr (Set.mem_Ioi.mp hx).le)).deriv]
      have hx0 : (0:ℝ) < x := hx
      have h1x : (0:ℝ) < 1 + x := by linarith
      rw [sub_nonneg, div_le_iff₀ h1x]
      nlinarith [pow_nonneg hx0.le 5]
  have h0 := hmono Set.self_mem_Ici (a := (0:ℝ)) (Set.mem_Ici.mpr hu) hu
  norm_num at h0
  linarith

/-- `L(t) = log(1 + 2/(e^t − 1))` for `t > 0`: the two log-halves of the archimedean
kernel combine over the common denominator `e^t − 1`. -/
theorem archKernelL_eq_log_one_add {t : ℝ} (ht : 0 < t) :
    archKernelL t = Real.log (1 + 2/(Real.exp t - 1)) := by
  have hE1 : (1:ℝ) < Real.exp t := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr ht
  have hE0 : (0:ℝ) < Real.exp t := Real.exp_pos t
  have he1 : Real.exp (-t) < 1 := exp_neg_lt_one ht
  have he0 : (0:ℝ) < Real.exp (-t) := Real.exp_pos _
  rw [archKernelL, ← Real.log_div (by linarith) (by linarith)]
  congr 1
  rw [Real.exp_neg]
  have hE1' : Real.exp t - 1 ≠ 0 := by linarith
  have hEne : Real.exp t ≠ 0 := hE0.ne'
  field_simp
  ring

/-- Small-argument exponential upper bound `e^x ≤ 1/(1−x)` for `x < 1`. -/
theorem exp_le_one_div_one_sub {x : ℝ} (hx : x < 1) :
    Real.exp x ≤ 1/(1-x) := by
  have h1 : (0:ℝ) < 1 - x := by linarith
  have h2 : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have h3 : Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) :=
    mul_le_mul_of_nonneg_left h2 (Real.exp_pos x).le
  rw [← Real.exp_add] at h3
  norm_num at h3
  rw [le_div_iff₀ h1]
  linarith

/-- The threshold certificate `log(23/3) ≥ 2.0246` (via `e² < 7.3890561` and
`e^{0.0246} ≤ 1/(1 − 0.0246)`). -/
theorem log_twentyThree_thirds_ge : (2.0246:ℝ) ≤ Real.log (23/3) := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 23/3)]
  have he2 : Real.exp 2 ≤ 2.7182818286^2 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have h := Real.exp_one_lt_d9.le
    nlinarith [Real.exp_pos 1]
  have he00 : Real.exp 0.0246 ≤ 1/(1 - 0.0246) :=
    exp_le_one_div_one_sub (by norm_num)
  calc Real.exp 2.0246 = Real.exp 2 * Real.exp 0.0246 := by
        rw [← Real.exp_add]
        norm_num
    _ ≤ 2.7182818286^2 * (1/(1 - 0.0246)) :=
        mul_le_mul he2 he00 (Real.exp_pos _).le (by positivity)
    _ ≤ 23/3 := by norm_num

/-- **The β-bound** (T12-b N5, B–F line 594): `(1/2 + 1/t)·e^t·L(t) ≤ 2` for
`t ≥ log(23/3)` (i.e. `t = log(X/9)`, `X ≥ 69`). Via the quintic Mercator bound at
`u = 2/(e^t−1) ≤ 3/10`: `e^t·L ≤ (2+u)(1−u/2+u²/3−u³/4+u⁴/5)
= 2 + u²(1−u)/6 + (3/20)u⁴ + u⁵/5 ≤ 2.012201`, and `(1/2+1/t) ≤ 1/2+1/2.0246`. -/
theorem beta_bound_core {t : ℝ} (ht : Real.log (23/3) ≤ t) :
    (1/2 + 1/t) * (Real.exp t * archKernelL t) ≤ 2 := by
  have ht' : (2.0246:ℝ) ≤ t := le_trans log_twentyThree_thirds_ge ht
  have ht0 : (0:ℝ) < t := by linarith
  have hE : (23/3 : ℝ) ≤ Real.exp t := by
    calc (23/3 : ℝ) = Real.exp (Real.log (23/3)) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr ht
  have hE1 : (0:ℝ) < Real.exp t - 1 := by linarith
  set u : ℝ := 2/(Real.exp t - 1) with hu_def
  have hu0 : 0 < u := by positivity
  have hu3 : u ≤ 3/10 := by
    rw [hu_def, div_le_iff₀ hE1]
    linarith
  have hL : archKernelL t = Real.log (1 + u) := archKernelL_eq_log_one_add ht0
  have hEu : Real.exp t * u = 2 + u := by
    rw [hu_def]
    field_simp
    ring
  have hEL : Real.exp t * archKernelL t
      ≤ 2 + u^2*(1-u)/6 + (3/20)*u^4 + u^5/5 := by
    rw [hL]
    calc Real.exp t * Real.log (1 + u)
        ≤ Real.exp t * (u - u^2/2 + u^3/3 - u^4/4 + u^5/5) :=
          mul_le_mul_of_nonneg_left (log_one_add_le_quintic hu0.le) (Real.exp_pos t).le
      _ = 2 + u^2*(1-u)/6 + (3/20)*u^4 + u^5/5 := by
          linear_combination (1 - u/2 + u^2/3 - u^3/4 + u^4/5) * hEu
  have hP : 2 + u^2*(1-u)/6 + (3/20)*u^4 + u^5/5 ≤ 2012201/1000000 := by
    have hfac : (0:ℝ) ≤ 21/100 + (7/10)*u - u^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hu3 hu0.le]
    have hcube : u^2*(1-u) ≤ 63/1000 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu3) hfac]
    have h4 : u^4 ≤ (3/10:ℝ)^4 := pow_le_pow_left₀ hu0.le hu3 4
    have h5 : u^5 ≤ (3/10:ℝ)^5 := pow_le_pow_left₀ hu0.le hu3 5
    nlinarith
  have hfrac : 1/2 + 1/t ≤ 1/2 + 1/2.0246 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2.0246) ht'
    linarith
  have hELpos : 0 ≤ Real.exp t * archKernelL t :=
    mul_nonneg (Real.exp_pos t).le (archKernelL_pos ht0).le
  calc (1/2 + 1/t) * (Real.exp t * archKernelL t)
      ≤ (1/2 + 1/2.0246) * (2012201/1000000) :=
        mul_le_mul hfrac (le_trans hEL hP) hELpos (by norm_num)
    _ ≤ 2 := by norm_num

/-- The β-bound in the halved-exponential form used by `step1`'s archimedean term:
`(1/2 + 1/t)·e^{t/2}·L(t) ≤ 2·e^{−t/2}`. -/
theorem beta_bound_half {t : ℝ} (ht : Real.log (23/3) ≤ t) :
    (1/2 + 1/t) * Real.exp (t/2) * archKernelL t ≤ 2 * Real.exp (-(t/2)) := by
  have hcore := beta_bound_core ht
  have hkey : (1/2 + 1/t) * Real.exp (t/2) * archKernelL t
      = ((1/2 + 1/t) * (Real.exp t * archKernelL t)) * Real.exp (-(t/2)) := by
    rw [show Real.exp t = Real.exp (t/2) * Real.exp (t/2) by
      rw [← Real.exp_add]; congr 1; ring]
    have hne : Real.exp (t/2) ≠ 0 := (Real.exp_pos _).ne'
    rw [Real.exp_neg]
    field_simp
  rw [hkey]
  exact mul_le_mul_of_nonneg_right hcore (Real.exp_pos _).le

end DedekindResidue

end
