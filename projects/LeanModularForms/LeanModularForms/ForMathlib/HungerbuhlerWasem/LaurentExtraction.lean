/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.FlatnessConditions
import LeanModularForms.ForMathlib.HungerbuhlerWasem
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Laurent extraction for HungerbuhlerWasem (T-LE-01)

For the Hungerbühler–Wasem residue theorem in its full crossing form, we need
to extract a Laurent decomposition `f = polarPart + holomorphicRemainder` at
each pole `s ∈ S`. Condition (B) (`SatisfiesConditionB.laurent_compatible`)
already carries this data via `∃ N a g, ...`.

This file extracts that data into named functions (using `Classical.choose`)
and builds a `PolarPartDecomposition` from a `SatisfiesConditionB` hypothesis.

## Main definitions

* `HungerbuhlerWasem.PolarPartDecomposition.ofMeromorphicWithCondB` — the
  constructor consuming `MeromorphicAt` data and `SatisfiesConditionB γ f S`
  to build a `PolarPartDecomposition` (handles both crossed and uncrossed poles).

## Strategy

We use `Classical.choose` on `hCondB.laurent_compatible` to extract the data
`(N, a, g)` for each crossed pole. For uncrossed poles, we use a default
`order = 0` (empty polar part) and the analytic remainder is `f` locally.
This adds no axioms beyond the existing `Classical.choice`.
-/

open Filter Topology Set Complex MeasureTheory Metric

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

private lemma circleIntegral_higherOrder_eq_zero
    {s : ℂ} {r : ℝ} {n : ℕ} (hn : 2 ≤ n) (c : ℂ) :
    ∮ z in C(s, r), c / (z - s) ^ n = 0 := by
  have h_eq : (fun z ↦ c / (z - s) ^ n) = fun z ↦ c * (z - s) ^ (-(n : ℤ)) := by
    funext z
    rw [div_eq_mul_inv, zpow_neg, zpow_natCast]
  rw [h_eq, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_zpow_of_ne (by omega) s s r, mul_zero]

private lemma circleIntegrable_higherOrder_term {s : ℂ} {r : ℝ}
    (hs_notin : s ∉ sphere s |r|) {N : ℕ} (a : Fin N → ℂ) (k : Fin N) :
    CircleIntegrable
      (fun z ↦ if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) s r := by
  by_cases hk : k.val ≥ 1
  · simp only [hk, ↓reduceIte]
    rw [show (fun z ↦ a k / (z - s) ^ (k.val + 1)) =
        fun z ↦ a k * (z - s) ^ (-((k.val + 1 : ℕ) : ℤ)) by
      funext z; rw [div_eq_mul_inv, zpow_neg, zpow_natCast]]
    refine CircleIntegrable.const_smul ?_
    show CircleIntegrable (fun z ↦ (z - s) ^ (-((k.val + 1 : ℕ) : ℤ))) s r
    rw [circleIntegrable_sub_zpow_iff]
    exact Or.inr (Or.inr hs_notin)
  · simp only [hk, ↓reduceIte]; exact circleIntegrable_const _ _ _

private lemma circleIntegral_higherOrder_sum_eq_zero
    {s : ℂ} {r : ℝ} (hr : 0 < r) {N : ℕ} (a : Fin N → ℂ) :
    ∮ z in C(s, r),
      (∑ k : Fin N, if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) = 0 := by
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hs_notin : s ∉ sphere s |r| := by
    rw [mem_sphere, dist_self, abs_of_pos hr]
    exact hr_ne.symm
  have h_each_int : ∀ k : Fin N, CircleIntegrable
      (fun z ↦ if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) s r :=
    fun k ↦ circleIntegrable_higherOrder_term hs_notin a k
  rw [circleIntegral.integral_fun_sum (s := Finset.univ) (fun k _ ↦ h_each_int k)]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hk : k.val ≥ 1
  · simp only [hk, ↓reduceIte]
    exact circleIntegral_higherOrder_eq_zero (by omega) (a k)
  · simp only [hk, ↓reduceIte]
    simp [circleIntegral]

/-- **Residue computation from Laurent data.** For a function `f` with the
Laurent expansion `f z = g z + ∑ k : Fin N, a k / (z - s)^(k+1)` near `s`
(where `g` is analytic at `s`), the residue equals `a 0` (or `0` if `N = 0`).

This is the higher-order generalization of `residue_eq_of_simple_pole_decomp`:
the analytic part contributes zero, the order-0 Laurent term `a_0/(z-s)`
contributes `a_0`, and higher-order terms `a_k/(z-s)^(k+1)` for `k ≥ 1` all
have circle integral zero. -/
theorem residue_of_laurent_expansion {f g : ℂ → ℂ} {s : ℂ} (N : ℕ) (a : Fin N → ℂ)
    (hg : AnalyticAt ℂ g s)
    (hf_eq : ∀ᶠ z in 𝓝[≠] s,
      f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) :
    residue f s = if h : 0 < N then a ⟨0, h⟩ else 0 := by
  by_cases hN_pos : 0 < N
  · rw [dif_pos hN_pos]
    set rest : ℂ → ℂ := fun z ↦
      g z + ∑ k : Fin N, if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0
        with hrest_def
    have hf_eq' : ∀ᶠ z in 𝓝[≠] s, f z = a ⟨0, hN_pos⟩ / (z - s) + rest z := by
      filter_upwards [hf_eq] with z hz
      rw [hz, hrest_def]
      have hsplit : ∑ k : Fin N, a k / (z - s) ^ (k.val + 1) =
          a ⟨0, hN_pos⟩ / (z - s) +
            ∑ k : Fin N, if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0 := by
        rw [show (∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) =
            ∑ k : Fin N, ((if k.val = 0 then a ⟨0, hN_pos⟩ / (z - s) else 0) +
              (if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0)) from ?_,
          Finset.sum_add_distrib]
        · congr 1
          rw [Finset.sum_eq_single ⟨0, hN_pos⟩]
          · simp
          · intro k _ hk
            have hk0 : k.val ≠ 0 := fun h_eq ↦ hk (Fin.ext h_eq)
            simp [hk0]
          · simp
        · refine Finset.sum_congr rfl fun k _ ↦ ?_
          by_cases hk : k.val = 0
          · simp [show k = ⟨0, hN_pos⟩ from Fin.ext hk]
          · simp [hk, show k.val ≥ 1 by omega]
      rw [hsplit]; ring
    unfold residue
    apply Filter.Tendsto.limUnder_eq
    apply tendsto_nhds_of_eventually_eq
    obtain ⟨rg, hrg_pos, hg_ball⟩ := hg.exists_ball_analyticOnNhd
    rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hf_eq'
    obtain ⟨rf, hrf_pos, hrf_eq⟩ := hf_eq'
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (lt_min hrg_pos hrf_pos)] with r hr_lt hr_pos
    simp only [mem_Ioi, mem_Iio] at hr_pos hr_lt
    have hr_lt_rg : r < rg := hr_lt.trans_le (min_le_left _ _)
    have hr_lt_rf : r < rf := hr_lt.trans_le (min_le_right _ _)
    have hr_ne : r ≠ 0 := ne_of_gt hr_pos
    have hs_notin : s ∉ sphere s |r| := by
      rw [mem_sphere, dist_self, abs_of_pos hr_pos]; exact hr_ne.symm
    have h_eq_on : EqOn f (fun z ↦ a ⟨0, hN_pos⟩ * (z - s)⁻¹ + rest z) (sphere s r) := by
      intro z hz
      have h_ne : z ≠ s := fun heq ↦ by
        rw [heq, mem_sphere, dist_self] at hz; linarith
      have := hrf_eq ⟨by rw [mem_ball, mem_sphere.mp hz]; exact hr_lt_rf,
        mem_compl_singleton_iff.mpr h_ne⟩
      simp only [mem_setOf_eq] at this
      rw [this, div_eq_mul_inv]
    have h_ci_g : CircleIntegrable g s r :=
      ((hg_ball.continuousOn.mono (closedBall_subset_ball hr_lt_rg)).mono
        sphere_subset_closedBall).circleIntegrable hr_pos.le
    have h_ci_higher_each : ∀ k : Fin N, CircleIntegrable
        (fun z ↦ if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) s r :=
      fun k ↦ circleIntegrable_higherOrder_term hs_notin a k
    have h_ci_higher_sum : CircleIntegrable
        (fun z ↦ ∑ k : Fin N, if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0)
        s r := by
      rw [show (fun z ↦ ∑ k : Fin N,
          (if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0 : ℂ)) =
          ∑ k ∈ (Finset.univ : Finset (Fin N)),
            fun z ↦ if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0 by
        funext z; rw [Finset.sum_apply]]
      exact CircleIntegrable.sum _ (fun k _ ↦ h_ci_higher_each k)
    have h_ci_rest : CircleIntegrable rest s r := h_ci_g.add h_ci_higher_sum
    have h_ci_a0_inv : CircleIntegrable (fun z ↦ a ⟨0, hN_pos⟩ * (z - s)⁻¹) s r :=
      (circleIntegrable_sub_inv_iff.mpr (Or.inr hs_notin)).const_fun_smul
    rw [circleIntegral.integral_congr hr_pos.le h_eq_on,
      circleIntegral.integral_add h_ci_a0_inv h_ci_rest,
      circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_center_inv s hr_ne]
    have h_int_g : ∮ z in C(s, r), g z = 0 := by
      refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr_pos.le
        countable_empty
        (hg_ball.continuousOn.mono (closedBall_subset_ball hr_lt_rg))
        (fun z ⟨hz, _⟩ ↦ ?_)
      exact (hg_ball z (ball_subset_ball hr_lt_rg.le hz)).differentiableAt
    have h_int_rest : ∮ z in C(s, r), rest z = 0 := by
      rw [show rest = fun z ↦ g z + _ from rfl,
        circleIntegral.integral_add h_ci_g h_ci_higher_sum, h_int_g, zero_add]
      exact circleIntegral_higherOrder_sum_eq_zero hr_pos a
    rw [h_int_rest, add_zero]; field_simp
  · obtain rfl : N = 0 := by omega
    rw [dif_neg (by omega)]
    have hf_eq_g : ∀ᶠ z in 𝓝[≠] s, f z = g z := by
      filter_upwards [hf_eq] with z hz; rw [hz]; simp
    rw [residue_congr hf_eq_g]
    exact residue_eq_zero_of_analyticAt hg

private lemma analyticAt_peel_one {g : ℂ → ℂ} {s : ℂ} (hg : AnalyticAt ℂ g s) :
    ∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ s ∧
      ∀ᶠ z in 𝓝 s, g z = g s + (z - s) * g₁ z := by
  have h_diff : AnalyticAt ℂ (fun z ↦ g z - g s) s := hg.sub analyticAt_const
  have h_value : (fun z ↦ g z - g s) s = 0 := by simp
  have h_ord_ne : analyticOrderAt (fun z ↦ g z - g s) s ≠ 0 := fun h_eq ↦
    (h_diff.analyticOrderAt_eq_zero).mp h_eq h_value
  have h_ge : (1 : ℕ∞) ≤ analyticOrderAt (fun z ↦ g z - g s) s :=
    Order.one_le_iff_ne_zero.mpr h_ord_ne
  obtain ⟨g₁, hg₁_an, hg₁_eq⟩ :=
    (natCast_le_analyticOrderAt h_diff).mp (by exact_mod_cast h_ge)
  refine ⟨g₁, hg₁_an, ?_⟩
  filter_upwards [hg₁_eq] with z hz
  have heq : g z - g s = (z - s) * g₁ z := by simpa using hz
  linear_combination heq

private lemma analyticAt_taylor_decomp {g : ℂ → ℂ} {s : ℂ}
    (hg : AnalyticAt ℂ g s) (k : ℕ) :
    ∃ (c : Fin k → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R s ∧
      ∀ᶠ z in 𝓝 s, g z = (∑ j : Fin k, c j * (z - s) ^ j.val) + (z - s) ^ k * R z := by
  induction k with
  | zero =>
      refine ⟨Fin.elim0, g, hg, ?_⟩
      filter_upwards with z
      simp
  | succ k ih =>
      obtain ⟨c, R, hR_an, hR_eq⟩ := ih
      obtain ⟨R', hR'_an, hR'_eq⟩ := analyticAt_peel_one hR_an
      refine ⟨Fin.snoc c (R s), R', hR'_an, ?_⟩
      filter_upwards [hR_eq, hR'_eq] with z hR_eq_z hR'_eq_z
      rw [hR_eq_z, hR'_eq_z, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last,
        Fin.val_castSucc]
      ring

private lemma pow_div_pow_neg {w : ℂ} (hw : w ≠ 0) {k j : ℕ} (hjk : j < k) :
    w ^ j * (w ^ k)⁻¹ = (w ^ (k - j))⁻¹ := by
  have h_exp : (k - j) + j = k := by omega
  rw [show (w ^ k)⁻¹ = (w ^ ((k - j) + j))⁻¹ by rw [h_exp], pow_add]
  field_simp

private lemma reindex_sum_fin_neg {k : ℕ} (_hk : 0 < k) (c : Fin k → ℂ) (w : ℂ) :
    (∑ j : Fin k, c j / w ^ (k - j.val)) =
      ∑ i : Fin k,
        c ⟨k - 1 - i.val, by have := i.isLt; omega⟩ / w ^ (i.val + 1) := by
  let σ : Fin k → Fin k := fun j ↦ ⟨k - 1 - j.val, by have := j.isLt; omega⟩
  have hσ_invol : Function.Involutive σ := fun j ↦ by
    ext
    have := j.isLt
    simp [σ]
    omega
  have h_sum_eq : (∑ i : Fin k, c (σ i) / w ^ (k - (σ i).val)) =
      ∑ j : Fin k, c j / w ^ (k - j.val) := by
    apply (Equiv.sum_comp ⟨σ, σ, hσ_invol.leftInverse, hσ_invol.rightInverse⟩
      (fun j ↦ c j / w ^ (k - j.val)))
  rw [← h_sum_eq]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 2
  simp only [σ]
  omega

/-- **Generic Laurent data extraction from `MeromorphicAt`.** For any meromorphic
function `f` at `s`, there exist `(N, a, g)` such that `g` is analytic at `s` and
`f =ᶠ[𝓝[≠] s] g + ∑ k : Fin N, a k / (z - s)^(k+1)`. -/
theorem mero_laurent_data_exists {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) :
    ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1) := by
  classical
  obtain ⟨n, g₀, hg₀_an, hg₀_eq⟩ :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mp hMero
  by_cases hn_neg : n < 0
  · set k : ℕ := (-n).toNat with hk_def
    have hk_pos : 0 < k := by rw [hk_def]; omega
    have hn_eq : n = -(k : ℤ) := by omega
    obtain ⟨c, R, hR_an, hR_eq⟩ := analyticAt_taylor_decomp hg₀_an k
    refine ⟨k, fun i : Fin k ↦ c ⟨k - 1 - i.val, by have := i.isLt; omega⟩, R, hR_an, ?_⟩
    have hR_eq_nbhd : ∀ᶠ z in 𝓝[≠] s, g₀ z =
        (∑ j : Fin k, c j * (z - s) ^ j.val) + (z - s) ^ k * R z :=
      nhdsWithin_le_nhds hR_eq
    have hg₀_eq' : ∀ᶠ z in 𝓝[≠] s, f z = (z - s) ^ (-(k : ℤ)) • g₀ z := by
      filter_upwards [hg₀_eq] with z hz
      rw [hz, hn_eq]
    filter_upwards [hg₀_eq', hR_eq_nbhd, self_mem_nhdsWithin] with z hf_eq hR_eq_z hz_ne
    have hz_sub : (z - s) ≠ 0 := sub_ne_zero.mpr hz_ne
    rw [hf_eq, hR_eq_z, smul_eq_mul, zpow_neg, zpow_natCast, mul_add]
    have h1 : ((z - s) ^ k)⁻¹ * ((z - s) ^ k * R z) = R z := by field_simp
    rw [h1, add_comm]
    congr 1
    rw [Finset.mul_sum, show ∑ j : Fin k, ((z - s) ^ k)⁻¹ * (c j * (z - s) ^ j.val) =
        ∑ j : Fin k, c j / (z - s) ^ (k - j.val) from
      Finset.sum_congr rfl fun j _ ↦ by
        rw [div_eq_mul_inv, show ((z - s) ^ k)⁻¹ * (c j * (z - s) ^ j.val) =
            c j * ((z - s) ^ j.val * ((z - s) ^ k)⁻¹) by ring,
          pow_div_pow_neg hz_sub j.isLt]]
    exact reindex_sum_fin_neg hk_pos c (z - s)
  · set m : ℕ := n.toNat
    refine ⟨0, Fin.elim0, fun z ↦ (z - s) ^ m * g₀ z, ?_, ?_⟩
    · exact ((analyticAt_id.sub analyticAt_const).pow m).mul hg₀_an
    · filter_upwards [hg₀_eq] with z hf_eq
      simp only [Finset.sum_empty, Finset.univ_eq_empty, add_zero]
      rw [hf_eq, smul_eq_mul, show n = (m : ℤ) by omega, zpow_natCast]

/-- Local polar part at pole `s` from a `MeromorphicAt` hypothesis: extracted
via `Classical.choose` on `mero_laurent_data_exists`. -/
noncomputable def meroPolarPartAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s)
    (z : ℂ) : ℂ :=
  ∑ k : Fin (mero_laurent_data_exists hMero).choose,
    (mero_laurent_data_exists hMero).choose_spec.choose k /
      (z - s) ^ (k.val + 1)

/-- Order of the local polar part at `s` from a `MeromorphicAt` hypothesis. -/
noncomputable def meroPolarOrderAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) :
    ℕ :=
  (mero_laurent_data_exists hMero).choose

/-- Laurent coefficient `a_k` at `s` from a `MeromorphicAt` hypothesis. -/
noncomputable def meroPolarCoeffAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s)
    (k : Fin (meroPolarOrderAt hMero)) : ℂ :=
  (mero_laurent_data_exists hMero).choose_spec.choose
    (Fin.cast (by simp [meroPolarOrderAt]) k)

/-- The analytic remainder `g` at `s` from a `MeromorphicAt` hypothesis. -/
noncomputable def meroAnalyticPartAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) : ℂ → ℂ :=
  (mero_laurent_data_exists hMero).choose_spec.choose_spec.choose

/-- The analytic part is `AnalyticAt ℂ` at `s`. -/
theorem meroAnalyticPartAt_analyticAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) : AnalyticAt ℂ (meroAnalyticPartAt hMero) s :=
  (mero_laurent_data_exists hMero).choose_spec.choose_spec.choose_spec.1

/-- **Local Laurent decomposition** from `MeromorphicAt`: near `s`,
`f = analyticPart + polarPart` (in the punctured neighborhood). -/
theorem mero_f_eq_analyticPart_plus_polarPart_eventually {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) :
    ∀ᶠ z in 𝓝[≠] s, f z = meroAnalyticPartAt hMero z + meroPolarPartAt hMero z := by
  filter_upwards
    [(mero_laurent_data_exists hMero).choose_spec.choose_spec.choose_spec.2]
    with z hz
  rw [hz]
  rfl

/-- `meroPolarPartAt s` is differentiable at any point `z ≠ s`. -/
theorem meroPolarPartAt_differentiableAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {z : ℂ} (hz : z ≠ s) :
    DifferentiableAt ℂ (meroPolarPartAt hMero) z := by
  unfold meroPolarPartAt
  refine DifferentiableAt.fun_sum fun k _ ↦ ?_
  exact (differentiableAt_const _).div
    ((differentiableAt_id.sub (differentiableAt_const _)).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hz))

/-- `meroPolarPartAt s` is `AnalyticAt ℂ` at any point `w ≠ s`. -/
theorem meroPolarPartAt_analyticAt_off {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {w : ℂ} (hw : w ≠ s) :
    AnalyticAt ℂ (meroPolarPartAt hMero) w := by
  unfold meroPolarPartAt
  refine Finset.analyticAt_fun_sum _ fun k _ ↦ ?_
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hw))

/-- Polar part written as the explicit Laurent sum using order/coeff. -/
theorem meroPolarPartAt_eq_sum {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (z : ℂ) :
    meroPolarPartAt hMero z =
      ∑ k : Fin (meroPolarOrderAt hMero),
        meroPolarCoeffAt hMero k / (z - s) ^ (k.val + 1) := by
  unfold meroPolarPartAt meroPolarCoeffAt meroPolarOrderAt
  rfl

/-- The leading Laurent coefficient `a_0` equals the residue of `f` at `s`. -/
theorem meroPolarCoeffAt_zero_eq_residue {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (h_pos : 0 < meroPolarOrderAt hMero) :
    meroPolarCoeffAt hMero ⟨0, h_pos⟩ = residue f s := by
  have h_data := mero_laurent_data_exists hMero
  set N := h_data.choose
  set a := h_data.choose_spec.choose
  set g := h_data.choose_spec.choose_spec.choose
  have hg_an : AnalyticAt ℂ g s := h_data.choose_spec.choose_spec.choose_spec.1
  have hf_eq : ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1) :=
    h_data.choose_spec.choose_spec.choose_spec.2
  have hN_pos : 0 < N := h_pos
  have hres := residue_of_laurent_expansion N a hg_an hf_eq
  rw [dif_pos hN_pos] at hres
  unfold meroPolarCoeffAt
  rw [hres]
  rfl

/-- The total polar part across all poles, using `MeromorphicAt` data
(uniform across crossed and uncrossed poles). -/
noncomputable def meroPolarPartTotal {S : Finset ℂ} {f : ℂ → ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) (z : ℂ) : ℂ :=
  ∑ s ∈ S.attach, meroPolarPartAt (hMero s.1 s.2) z

private theorem mero_otherPolar_analyticAt {S : Finset ℂ} {f : ℂ → ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) {s : ℂ} (_hs : s ∈ S) :
    AnalyticAt ℂ (fun z ↦ ∑ s' ∈ S.attach.filter (fun s' ↦ s'.1 ≠ s),
      meroPolarPartAt (hMero s'.1 s'.2) z) s := by
  refine Finset.analyticAt_fun_sum _ fun s' hs' ↦ ?_
  have h_ne : s'.1 ≠ s := (Finset.mem_filter.mp hs').2
  exact meroPolarPartAt_analyticAt_off (hMero s'.1 s'.2) h_ne.symm

private theorem mero_f_minus_total_eventuallyEq_analytic {S : Finset ℂ} {f : ℂ → ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) {s : ℂ} (hs : s ∈ S) :
    ∃ g_s : ℂ → ℂ, AnalyticAt ℂ g_s s ∧
      ∀ᶠ z in 𝓝[≠] s, f z - meroPolarPartTotal hMero z = g_s z := by
  set g_s : ℂ → ℂ := fun z ↦
    meroAnalyticPartAt (hMero s hs) z -
      ∑ s' ∈ S.attach.filter (fun s' ↦ s'.1 ≠ s),
        meroPolarPartAt (hMero s'.1 s'.2) z with hg_s_def
  refine ⟨g_s, (meroAnalyticPartAt_analyticAt (hMero s hs)).sub
    (mero_otherPolar_analyticAt hMero hs), ?_⟩
  filter_upwards [mero_f_eq_analyticPart_plus_polarPart_eventually (hMero s hs)] with z hz
  rw [hg_s_def, hz]
  suffices h_total : meroPolarPartTotal hMero z =
      meroPolarPartAt (hMero s hs) z +
        ∑ s' ∈ S.attach.filter (fun s' ↦ s'.1 ≠ s),
          meroPolarPartAt (hMero s'.1 s'.2) z by
    rw [h_total]
    ring
  unfold meroPolarPartTotal
  rw [show (∑ s' ∈ S.attach, meroPolarPartAt (hMero s'.1 s'.2) z) =
      (∑ s' ∈ S.attach.filter (fun s' ↦ s'.1 = s),
        meroPolarPartAt (hMero s'.1 s'.2) z) +
      (∑ s' ∈ S.attach.filter (fun s' ↦ ¬ s'.1 = s),
        meroPolarPartAt (hMero s'.1 s'.2) z) from
    (Finset.sum_filter_add_sum_filter_not S.attach _ _).symm]
  have h_singleton : S.attach.filter (fun s' ↦ s'.1 = s) = {⟨s, hs⟩} := by
    ext s'
    simp only [Finset.mem_filter, Finset.mem_attach, true_and, Finset.mem_singleton]
    refine ⟨fun h_eq ↦ ?_, fun h_eq ↦ ?_⟩
    · ext
      exact h_eq
    · rw [h_eq]
  rw [h_singleton, Finset.sum_singleton]

/-- **The constructor: `PolarPartDecomposition.ofMeromorphicWithCondB`.**

Given:
- `U` open in `ℂ`, `S ⊆ U` finite,
- `f : ℂ → ℂ` differentiable on `U \ S`,
- `hMero : ∀ s ∈ S, MeromorphicAt f s` — meromorphicity at each pole,
- A piecewise-`C¹` immersion `γ` with `SatisfiesConditionB γ f S`,

we build a `PolarPartDecomposition f S U`. This constructor handles **both
crossed and uncrossed** poles uniformly (no `hAllCrossed` hypothesis), since
for each pole `s` we extract Laurent data from the `MeromorphicAt` hypothesis
directly via `meromorphicOrderAt_ne_top_iff`.

The `hCondB` parameter is kept in the signature for use downstream (e.g. by
per-pole CPV dischargers that need the angle compatibility data); it is not
required by this constructor's body. -/
noncomputable def PolarPartDecomposition.ofMeromorphicWithCondB
    {U : Set ℂ} (hU_open : IsOpen U)
    {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U \ ↑S))
    {γ : PwC1Immersion x x}
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (_hCondB : SatisfiesConditionB γ f S) :
    PolarPartDecomposition f S U := by
  let polarPart : ℂ → ℂ → ℂ := fun s z ↦
    if h_mem : s ∈ S then meroPolarPartAt (hMero s h_mem) z else 0
  let order : ℂ → ℕ := fun s ↦
    if h_mem : s ∈ S then meroPolarOrderAt (hMero s h_mem) else 0
  let coeff : (s : ℂ) → Fin (order s) → ℂ := fun s k ↦
    if h_mem : s ∈ S then
      meroPolarCoeffAt (hMero s h_mem) (Fin.cast (by simp [order, h_mem]) k)
    else by
      have h0 : order s = 0 := by simp [order, h_mem]
      exact absurd k.isLt (by omega)
  set rem : ℂ → ℂ := fun z ↦ f z - meroPolarPartTotal hMero z with hrem_def
  set correction : ℂ → ℂ := fun z ↦
    if z ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] z) rem else rem z with hcorr_def
  refine
    { polarPart := polarPart
      order := order
      coeff := coeff
      polarPart_eq := ?_
      residue_eq := ?_
      analyticRemainder := correction
      analyticRemainder_diff := ?_
      decomp := ?_ }
  · intro s hs z _hz
    have h_pp : polarPart s z = meroPolarPartAt (hMero s hs) z := by
      simp only [polarPart, hs, ↓reduceDIte]
    have h_order : order s = meroPolarOrderAt (hMero s hs) := by
      simp only [order, hs, ↓reduceDIte]
    rw [h_pp, meroPolarPartAt_eq_sum (hMero s hs) z, ← Fin.sum_congr'
      (fun k : Fin (meroPolarOrderAt (hMero s hs)) ↦
        meroPolarCoeffAt (hMero s hs) k / (z - s) ^ (k.val + 1)) h_order]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    congr 1
    simp only [coeff, hs, ↓reduceDIte]
  · intro s hs
    have h_order : order s = meroPolarOrderAt (hMero s hs) := by
      simp only [order, hs, ↓reduceDIte]
    by_cases h_pos : 0 < order s
    · rw [dif_pos h_pos]
      have h_pos' : 0 < meroPolarOrderAt (hMero s hs) := h_order ▸ h_pos
      rw [← meroPolarCoeffAt_zero_eq_residue (hMero s hs) h_pos']
      change meroPolarCoeffAt (hMero s hs) ⟨0, h_pos'⟩ = coeff s ⟨0, h_pos⟩
      simp only [coeff, hs, ↓reduceDIte]
      rfl
    · rw [dif_neg h_pos]
      have h_zero : meroPolarOrderAt (hMero s hs) = 0 := by rw [← h_order]; omega
      have h_data := mero_laurent_data_exists (hMero s hs)
      set N := h_data.choose
      set a := h_data.choose_spec.choose
      set g := h_data.choose_spec.choose_spec.choose
      have hg_an : AnalyticAt ℂ g s := h_data.choose_spec.choose_spec.choose_spec.1
      have hf_eq : ∀ᶠ z in 𝓝[≠] s,
          f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1) :=
        h_data.choose_spec.choose_spec.choose_spec.2
      have hN_zero : N = 0 := h_zero
      have hres := residue_of_laurent_expansion N a hg_an hf_eq
      rw [dif_neg (by omega)] at hres
      exact hres
  · intro z hzU
    by_cases hzS : z ∈ (↑S : Set ℂ)
    · have hzS' := Finset.mem_coe.mp hzS
      obtain ⟨g_z, hg_z_an, hg_z_eq⟩ :=
        mero_f_minus_total_eventuallyEq_analytic hMero hzS'
      have h_corr_eq : (fun w ↦ correction w) =ᶠ[𝓝 z] g_z := by
        have h_lim_eq : limUnder (𝓝[≠] z) rem = g_z z :=
          (hg_z_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            |>.congr' (hg_z_eq.mono fun _ h ↦ h.symm)).limUnder_eq
        have h_at_z : correction z = g_z z := by
          change (if z ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] z) rem else rem z) = g_z z
          rw [if_pos hzS, h_lim_eq]
        have hz_not_erase : z ∉ (↑(S.erase z) : Set ℂ) := fun hmem ↦
          (Finset.mem_erase.mp (Finset.mem_coe.mp hmem)).1 rfl
        obtain ⟨V, hV_open, hz_V, hV_eq⟩ := mem_nhdsWithin.mp hg_z_eq
        have h_erase_away : (↑(S.erase z) : Set ℂ)ᶜ ∈ 𝓝 z :=
          (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds hz_not_erase
        apply Filter.mem_of_superset (Filter.inter_mem (hV_open.mem_nhds hz_V) h_erase_away)
        intro w ⟨hw_V, hw_erase⟩
        change correction w = g_z w
        by_cases hwz : w = z
        · rw [hwz, h_at_z]
        · have hw_not_S : w ∉ (↑S : Set ℂ) := fun hmem ↦ hw_erase
            (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hwz, Finset.mem_coe.mp hmem⟩))
          change (if w ∈ (↑S : Set ℂ) then _ else rem w) = g_z w
          rw [if_neg hw_not_S]
          exact hV_eq ⟨hw_V, hwz⟩
      exact (hg_z_an.differentiableAt.congr_of_eventuallyEq h_corr_eq).differentiableWithinAt
    · have h_U_minus_S := hU_open.sdiff S.finite_toSet.isClosed
      have hzU_S : z ∈ U \ (↑S : Set ℂ) := ⟨hzU, hzS⟩
      have h_f_diff : DifferentiableAt ℂ f z :=
        (hf z hzU_S).differentiableAt (h_U_minus_S.mem_nhds hzU_S)
      have h_total_diff : DifferentiableAt ℂ (meroPolarPartTotal hMero) z := by
        unfold meroPolarPartTotal
        refine DifferentiableAt.fun_sum fun s' _ ↦ ?_
        refine meroPolarPartAt_differentiableAt (hMero s'.1 s'.2) fun h_eq ↦ ?_
        exact hzS (h_eq ▸ Finset.mem_coe.mpr s'.2)
      have h_corr_eq : (fun w ↦ correction w) =ᶠ[𝓝 z] rem := by
        apply Filter.mem_of_superset (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS)
        intro w hw
        change (if w ∈ (↑S : Set ℂ) then _ else rem w) = rem w
        rw [if_neg hw]
      exact ((h_f_diff.sub h_total_diff).congr_of_eventuallyEq h_corr_eq).differentiableWithinAt
  · intro z ⟨_, hzS⟩
    have h_corr : correction z = rem z := by simp only [hcorr_def, hzS, ↓reduceIte]
    have h_rem : rem z = f z - meroPolarPartTotal hMero z := by simp only [hrem_def]
    have h_total : meroPolarPartTotal hMero z = ∑ s ∈ S, polarPart s z := by
      unfold meroPolarPartTotal
      rw [show ∑ s ∈ S, polarPart s z = ∑ s' ∈ S.attach, polarPart s'.1 z from
        (Finset.sum_attach S _).symm]
      refine Finset.sum_congr rfl fun s' _ ↦ ?_
      simp only [polarPart, s'.2, ↓reduceDIte]
    change f z = correction z + ∑ s ∈ S, polarPart s z
    rw [h_corr, h_rem, h_total]
    ring

end HungerbuhlerWasem

end
