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

/-- The cosh-weighted exponential integral is trapped in `[0, π/2]`. -/
theorem cosh_int_nonneg {σ : ℝ} (hσ : 1/2 < σ) :
    0 ≤ ∫ y in Set.Ioi (0:ℝ),
        1/(2 * Real.cosh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y)) := by
  refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun y hy => ?_)
  have hy0 : (0:ℝ) < y := hy
  have hc : (0:ℝ) < Real.cosh (y/2) := Real.cosh_pos _
  have h1 : Real.exp (-(σ - 1/2) * y) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    nlinarith
  have h2 : (0:ℝ) ≤ 1 - Real.exp (-(σ - 1/2) * y) := by linarith
  positivity

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

/-- **The cosh integral is at most `π/2`.** -/
theorem cosh_int_le {σ : ℝ} (hσ : 1/2 < σ) :
    (∫ y in Set.Ioi (0:ℝ),
        1/(2 * Real.cosh (y/2)) * (1 - Real.exp (-(σ - 1/2) * y))) ≤ π/2 := by
  rw [← integral_inv_two_cosh_half]
  have hcoshint : MeasureTheory.IntegrableOn
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
  have hcoshint : MeasureTheory.IntegrableOn
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

end DedekindResidue

end
