/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem

/-!
# Multi-pole DCT lift for the polar-part Cauchy principal value (T-BR-Y5)

When `γ` crosses **multiple** poles in `S`, a singleton-CPV
`HasCauchyPV (decomp.polarPart s) γ s L` at one pole `s ∈ S` can be lifted to
the multi-point form `HasCauchyPVOn S (decomp.polarPart s) γ L`
**without** requiring `γ` to avoid the other poles in `S \ {s}`.

This eliminates the `h_avoid_others_per_pole` restriction in
`residueTheorem_crossing_*`.

## Strategy

The integrand `cpvIntegrandOn S f γ ε t` differs from the singleton-form
`cpvIntegrand f γ s ε t` exactly on the set

  `D(ε) := { t : (∃ s' ∈ S \ {s}, ‖γ(t) - s'‖ ≤ ε) ∧ ε < ‖γ(t) - s‖ }`

For `f = decomp.polarPart s`:
- the Laurent expression of `f` is bounded uniformly by some `M_polar` on
  `D(ε)` (when ε is small enough);
- `‖γ'(t)‖ ≤ K` (the Lipschitz constant);
- `vol(D(ε)) ≤ vol(badSet for S \ {s})(ε) → 0` as ε → 0+ (immersion → preimage
  of finite set has measure zero).

## Main results

* `MultiPoleDCT.badSet_volume_tendsto_zero` — `vol(badSet γ T ε) → 0` as
  `ε → 0+` when `γ` is an immersion and `T` is finite.
* `MultiPoleDCT.cpvIntegrand_polarPart_intervalIntegrable` — singleton
  cutoff integrand for the polar part is interval-integrable.
* `MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole` — the
  singleton-to-multipole CPV lift (the headline T-BR-Y5 result).

-/

open Set Filter Topology Complex MeasureTheory Metric
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

namespace MultiPoleDCT

variable {x : ℂ}

/-- The "bad set" for a finite set `T` of pole candidates: parameters `t ∈ [0,1]`
where `γ(t)` is within `ε` of some `s' ∈ T`. As `ε → 0+`, the bad sets shrink
to `γ⁻¹(T) ∩ [0,1]`. -/
def badSetIcc (γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) : Set ℝ :=
  {t ∈ Icc (0 : ℝ) 1 | ∃ s' ∈ T, ‖γP.toPath.extend t - s'‖ ≤ ε}

theorem badSetIcc_measurableSet (γP : PiecewiseC1Path x x) (T : Finset ℂ)
    (ε : ℝ) : MeasurableSet (badSetIcc γP T ε) := by
  classical
  have h_eq : badSetIcc γP T ε =
      Icc (0 : ℝ) 1 ∩ ⋃ s' ∈ T, {t : ℝ | ‖γP.toPath.extend t - s'‖ ≤ ε} := by
    ext t; simp only [badSetIcc, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion]; tauto
  rw [h_eq]
  refine measurableSet_Icc.inter (MeasurableSet.biUnion T.countable_toSet fun s' _ ↦ ?_)
  exact (isClosed_le ((γP.toPath.continuous_extend.sub continuous_const).norm)
    continuous_const).measurableSet

theorem badSetIcc_mono (γP : PiecewiseC1Path x x) (T : Finset ℂ) :
    Monotone (badSetIcc γP T) :=
  fun _ _ hε _ ⟨ht_Icc, s', hs'T, h_le⟩ ↦ ⟨ht_Icc, s', hs'T, h_le.trans hε⟩

theorem badSetIcc_subset_Icc (γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) :
    badSetIcc γP T ε ⊆ Icc (0 : ℝ) 1 := fun _ ht ↦ ht.1

theorem badSetIcc_volume_ne_top (γP : PiecewiseC1Path x x) (T : Finset ℂ) (ε : ℝ) :
    volume (badSetIcc γP T ε) ≠ ⊤ :=
  ((measure_mono (badSetIcc_subset_Icc γP T ε)).trans_lt measure_Icc_lt_top).ne

/-- Intersection of all bad sets (over ε > 0) equals the preimage of `T` in `[0,1]`. -/
theorem badSetIcc_iInter_pos (γP : PiecewiseC1Path x x) (T : Finset ℂ) :
    (⋂ ε ∈ Set.Ioi (0 : ℝ), badSetIcc γP T ε) =
      {t ∈ Icc (0 : ℝ) 1 | γP.toPath.extend t ∈ (↑T : Set ℂ)} := by
  classical
  ext t
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_Ioi]
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨(h 1 zero_lt_one).1, ?_⟩
    by_contra h_notin
    by_cases hT_ne : T.Nonempty
    · have h_pos : ∀ s' ∈ T, 0 < ‖γP.toPath.extend t - s'‖ := fun s' hs' ↦
        norm_pos_iff.mpr (sub_ne_zero.mpr fun heq ↦
          h_notin (heq ▸ Finset.mem_coe.mpr hs'))
      obtain ⟨s_min, hs_min_mem, hs_min⟩ := Finset.exists_min_image T
        (fun s' ↦ ‖γP.toPath.extend t - s'‖) hT_ne
      have h_min_pos := h_pos s_min hs_min_mem
      obtain ⟨_, s', hs'T, h_close⟩ :=
        h (‖γP.toPath.extend t - s_min‖ / 2) (by linarith)
      linarith [hs_min s' hs'T, h_close]
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hT_ne
      exact absurd (h 1 zero_lt_one).2.choose_spec.1 (Finset.notMem_empty _)
  · intro ⟨ht_Icc, ht_in_T⟩ ε hε_pos
    refine ⟨ht_Icc, _, Finset.mem_coe.mp ht_in_T, ?_⟩
    rw [sub_self, norm_zero]
    exact hε_pos.le

/-- The volume of the bad set tends to zero as `ε → 0+` for a closed piecewise-`C¹`
immersion `γ`. -/
theorem badSet_volume_tendsto_zero (γ : ClosedPwC1Immersion x) (T : Finset ℂ) :
    Tendsto (fun ε : ℝ ↦ volume (badSetIcc γ.toPwC1Immersion.toPiecewiseC1Path T ε))
      (𝓝[>] 0) (𝓝 0) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_lim := MeasureTheory.tendsto_measure_biInter_gt
    (μ := MeasureTheory.volume) (s := badSetIcc γP T) (a := (0 : ℝ))
    (fun r _ ↦ (badSetIcc_measurableSet γP T r).nullMeasurableSet)
    (fun _ _ _ hij ↦ badSetIcc_mono γP T hij)
    ⟨1, zero_lt_one, badSetIcc_volume_ne_top γP T 1⟩
  have h_iInter_eq : volume (⋂ r, ⋂ (_ : r > (0 : ℝ)), badSetIcc γP T r) = 0 := by
    rw [show (⋂ r, ⋂ (_ : r > (0 : ℝ)), badSetIcc γP T r) =
        {t ∈ Icc (0 : ℝ) 1 | γP.toPath.extend t ∈ (↑T : Set ℂ)}
      from badSetIcc_iInter_pos γP T]
    exact volume_preimage_finset_in_Icc01_zero γ T
  rwa [h_iInter_eq] at h_lim

/-- The singleton-CPV cutoff integrand for the polar part `decomp.polarPart s`
is interval-integrable on `[0, 1]` for every `ε > 0`. Mirrors
`cpvIntegrandOn_polarPart_intervalIntegrable` but for the singleton form. -/
theorem cpvIntegrand_polarPart_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {U : Set ℂ} {S : Finset ℂ}
    {f : ℂ → ℂ} (decomp : PolarPartDecomposition f S U) {s : ℂ} (hs : s ∈ S)
    {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable
      (fun t ↦ cpvIntegrand (decomp.polarPart s)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t)
      MeasureTheory.volume 0 1 := by
  classical
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set N : ℕ := decomp.order s
  set a : Fin N → ℂ := decomp.coeff s
  set laurentSum : ℂ → ℂ := fun z ↦ ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
  set h_curve : ℝ → ℂ := fun t ↦
    laurentSum (γP.toPath.extend t) * deriv γP.toPath.extend t
  have h_indicator_eq :
      (fun t ↦ cpvIntegrand (decomp.polarPart s) γP.toPath.extend s ε t) =
      {t : ℝ | ε < ‖γP.toPath.extend t - s‖}.indicator h_curve := by
    funext t
    unfold cpvIntegrand
    by_cases h : ε < ‖γP.toPath.extend t - s‖
    · have h_ne : γP.toPath.extend t ≠ s := fun heq ↦ by
        rw [heq, sub_self, norm_zero] at h; linarith
      rw [if_pos h, Set.indicator_of_mem (a := t) h]
      change decomp.polarPart s (γP.toPath.extend t) * deriv γP.toPath.extend t =
        laurentSum (γP.toPath.extend t) * deriv γP.toPath.extend t
      rw [decomp.polarPart_eq s hs _ h_ne]
    · rw [if_neg h, Set.indicator_of_notMem (a := t) h]
  have h_meas_set : MeasurableSet {t : ℝ | ε < ‖γP.toPath.extend t - s‖} :=
    (isOpen_lt continuous_const
      (γP.toPath.continuous_extend.sub continuous_const).norm).measurableSet
  set M_polar : ℝ := ∑ k : Fin N, ‖a k‖ / ε ^ (k.val + 1)
  set M : ℝ := M_polar * K
  have h_M_polar_nonneg : 0 ≤ M_polar :=
    Finset.sum_nonneg fun k _ ↦ div_nonneg (norm_nonneg _) (pow_nonneg hε.le _)
  have h_M_nonneg : 0 ≤ M := mul_nonneg h_M_polar_nonneg K.coe_nonneg
  have h_bound_on_set : ∀ t ∈ {t : ℝ | ε < ‖γP.toPath.extend t - s‖},
      ‖h_curve t‖ ≤ M := fun t h_far_s ↦ by
    rw [show ‖h_curve t‖ = ‖laurentSum (γP.toPath.extend t)‖ * ‖deriv γP.toPath.extend t‖
      from norm_mul _ _]
    exact mul_le_mul ((norm_sum_le _ _).trans <| Finset.sum_le_sum fun k _ ↦ by
        rw [norm_div, norm_pow]
        exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hε _)
          (pow_le_pow_left₀ hε.le h_far_s.le _))
      (norm_deriv_le_of_lipschitz hLip) (norm_nonneg _) h_M_polar_nonneg
  have h_curve_meas : Measurable h_curve :=
    (Finset.measurable_sum _ fun k _ ↦
      (((γP.toPath.continuous_extend.measurable.sub_const s).pow_const _).const_div _)).mul
      (measurable_deriv _)
  rw [intervalIntegrable_iff, h_indicator_eq]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
    (h_curve_meas.aestronglyMeasurable.indicator h_meas_set) M ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t _
  by_cases ht_in : t ∈ {t : ℝ | ε < ‖γP.toPath.extend t - s‖}
  · rw [Set.indicator_of_mem ht_in]; exact h_bound_on_set t ht_in
  · rw [Set.indicator_of_notMem ht_in, norm_zero]; exact h_M_nonneg

variable {U : Set ℂ}

/-- **T-BR-Y5 — Multi-pole DCT lift for the polar part.**

Given `decomp : PolarPartDecomposition f S U`, a closed piecewise-`C¹`
immersion `γ`, `s ∈ S`, and a singleton CPV
`HasCauchyPV (decomp.polarPart s) γ s L`, the multi-point CPV
`HasCauchyPVOn S (decomp.polarPart s) γ L` follows **without** requiring
γ to avoid the other poles in `S \ {s}`. -/
theorem hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole
    {S : Finset ℂ} {f : ℂ → ℂ} (hS_in_U : ↑S ⊆ U)
    (decomp : PolarPartDecomposition f S U)
    (γ : ClosedPwC1Immersion x) {s : ℂ} (hs : s ∈ S) {L : ℂ}
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (h : HasCauchyPV (decomp.polarPart s)
      γ.toPwC1Immersion.toPiecewiseC1Path s L) :
    HasCauchyPVOn S (decomp.polarPart s)
      γ.toPwC1Immersion.toPiecewiseC1Path L := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set T : Finset ℂ := S.erase s
  set N : ℕ := decomp.order s
  set a : Fin N → ℂ := decomp.coeff s
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  have h_deriv_le : ∀ t, ‖deriv γP.toPath.extend t‖ ≤ K := fun _ ↦
    norm_deriv_le_of_lipschitz hLip
  by_cases hT_ne : T.Nonempty
  swap
  · have hT_empty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT_ne
    have hS_eq : S = {s} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hs, fun s' hs' ↦ by
      by_contra h_ne
      exact (Finset.eq_empty_iff_forall_notMem.mp hT_empty) _
        (Finset.mem_erase.mpr ⟨h_ne, hs'⟩)⟩
    simp only [HasCauchyPVOn, HasCauchyPV] at h ⊢
    refine h.congr fun ε ↦ intervalIntegral.integral_congr fun t _ ↦ ?_
    unfold cpvIntegrand cpvIntegrandOn
    by_cases h_far : ε < ‖γP.toPath.extend t - s‖
    · rw [if_pos h_far, if_neg fun ⟨s', hs', h_le⟩ ↦ by
        rw [hS_eq, Finset.mem_singleton] at hs'
        exact absurd h_far (not_lt.mpr (hs' ▸ h_le))]
    · rw [if_neg h_far, if_pos ⟨s, by rw [hS_eq, Finset.mem_singleton], not_lt.mp h_far⟩]
  obtain ⟨s'_min, hs'_min_mem, hs'_min⟩ := Finset.exists_min_image T
    (fun s' ↦ ‖s - s'‖) hT_ne
  have h_pos_min : 0 < ‖s - s'_min‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr fun heq ↦
      Finset.ne_of_mem_erase hs'_min_mem heq.symm)
  set R : ℝ := ‖s - s'_min‖ / 4
  have hR_pos : 0 < R := by positivity
  have h_3R_pos : 0 < 3 * R := by linarith
  have h_dist_ge : ∀ s' ∈ T, 4 * R ≤ ‖s - s'‖ := fun s' hs'_mem ↦ by
    have : (4 : ℝ) * R = ‖s - s'_min‖ := by simp [R]; ring
    linarith [hs'_min s' hs'_mem]
  set M_polar : ℝ := ∑ k : Fin N, ‖a k‖ / (3 * R) ^ (k.val + 1)
  set M : ℝ := M_polar * K
  have hM_polar_nonneg : 0 ≤ M_polar :=
    Finset.sum_nonneg fun k _ ↦ div_nonneg (norm_nonneg _)
      (pow_nonneg h_3R_pos.le _)
  have hM_nonneg : 0 ≤ M := mul_nonneg hM_polar_nonneg K.coe_nonneg
  have h_diff_pt : ∀ ε > (0 : ℝ), ∀ t,
      cpvIntegrand (decomp.polarPart s) γP.toPath.extend s ε t -
        cpvIntegrandOn S (decomp.polarPart s) γP.toPath.extend ε t =
      if (∃ s' ∈ T, ‖γP.toPath.extend t - s'‖ ≤ ε) ∧
          ε < ‖γP.toPath.extend t - s‖
        then decomp.polarPart s (γP.toPath.extend t) * deriv γP.toPath.extend t
        else 0 := by
    intro ε _hε t
    unfold cpvIntegrand cpvIntegrandOn
    by_cases h_far_s : ε < ‖γP.toPath.extend t - s‖
    · by_cases h_S : ∃ s'' ∈ S, ‖γP.toPath.extend t - s''‖ ≤ ε
      · obtain ⟨s'', hs''_mem, h_close⟩ := h_S
        have hs''_ne_s : s'' ≠ s := fun heq ↦ by rw [heq] at h_close; linarith
        have hs''_in_T : s'' ∈ T := Finset.mem_erase.mpr ⟨hs''_ne_s, hs''_mem⟩
        rw [if_pos h_far_s, if_pos ⟨s'', hs''_mem, h_close⟩,
          if_pos ⟨⟨s'', hs''_in_T, h_close⟩, h_far_s⟩]
        ring
      · rw [if_pos h_far_s, if_neg h_S, if_neg (fun ⟨⟨s', hs'_mem, h_close⟩, _⟩ ↦
          h_S ⟨s', Finset.mem_of_mem_erase hs'_mem, h_close⟩)]
        ring
    · rw [if_neg h_far_s, if_pos ⟨s, hs, not_lt.mp h_far_s⟩,
        if_neg (fun ⟨_, hh⟩ ↦ h_far_s hh)]
      ring
  have h_diff_norm_bound_on_Icc : ∀ ε ∈ Set.Ioo (0 : ℝ) R, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖cpvIntegrand (decomp.polarPart s) γP.toPath.extend s ε t -
        cpvIntegrandOn S (decomp.polarPart s) γP.toPath.extend ε t‖ ≤
      (badSetIcc γP T ε).indicator (fun _ : ℝ ↦ M) t := by
    intro ε ⟨hε_pos, hε_lt_R⟩ t ht_Icc
    rw [h_diff_pt ε hε_pos t]
    by_cases h_cond : (∃ s' ∈ T, ‖γP.toPath.extend t - s'‖ ≤ ε) ∧
        ε < ‖γP.toPath.extend t - s‖
    · rw [if_pos h_cond]
      obtain ⟨⟨s', hs'_mem, h_close_s'⟩, h_far_s⟩ := h_cond
      have h_dist_far : 3 * R ≤ ‖γP.toPath.extend t - s‖ := by
        have h_tri : ‖s - s'‖ ≤ ‖γP.toPath.extend t - s‖ + ‖γP.toPath.extend t - s'‖ := by
          have := norm_sub_le (γP.toPath.extend t - s') (γP.toPath.extend t - s)
          have heq : (γP.toPath.extend t - s') - (γP.toPath.extend t - s) = s - s' := by ring
          rw [heq] at this; linarith
        linarith [h_dist_ge s' hs'_mem, h_close_s'.trans hε_lt_R.le]
      have h_polarPart_eq : decomp.polarPart s (γP.toPath.extend t) =
          ∑ k : Fin N, a k / (γP.toPath.extend t - s) ^ (k.val + 1) :=
        decomp.polarPart_eq s hs _ fun heq ↦ by
          rw [heq, sub_self, norm_zero] at h_far_s; linarith
      rw [h_polarPart_eq, Set.indicator_of_mem (show t ∈ badSetIcc γP T ε from
        ⟨ht_Icc, s', hs'_mem, h_close_s'⟩), norm_mul]
      refine mul_le_mul ?_ (h_deriv_le t) (norm_nonneg _) hM_polar_nonneg
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
      rw [norm_div, norm_pow]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos h_3R_pos _)
        (pow_le_pow_left₀ h_3R_pos.le h_dist_far _)
    · rw [if_neg h_cond, norm_zero]
      exact Set.indicator_nonneg (fun _ _ ↦ hM_nonneg) t
  have h_int_bound : ∀ ε ∈ Set.Ioo (0 : ℝ) R,
      ‖(∫ t in (0 : ℝ)..1, cpvIntegrand (decomp.polarPart s)
          γP.toPath.extend s ε t) -
        (∫ t in (0 : ℝ)..1, cpvIntegrandOn S (decomp.polarPart s)
          γP.toPath.extend ε t)‖ ≤
      M * (volume (badSetIcc γP T ε)).toReal := by
    rintro ε ⟨hε_pos, hε_lt_R⟩
    have h_int_cpv : IntervalIntegrable
        (fun t ↦ cpvIntegrand (decomp.polarPart s) γP.toPath.extend s ε t)
        MeasureTheory.volume 0 1 :=
      cpvIntegrand_polarPart_intervalIntegrable γ decomp hs hε_pos
    have h_int_cpvOn : IntervalIntegrable
        (fun t ↦ cpvIntegrandOn S (decomp.polarPart s) γP.toPath.extend ε t)
        MeasureTheory.volume 0 1 :=
      cpvIntegrandOn_polarPart_intervalIntegrable γ hS_in_U decomp hs h_null hε_pos
    rw [← intervalIntegral.integral_sub h_int_cpv h_int_cpvOn]
    have h_bound_aux :
        ‖∫ t in (0 : ℝ)..1, (cpvIntegrand (decomp.polarPart s)
              γP.toPath.extend s ε t -
            cpvIntegrandOn S (decomp.polarPart s) γP.toPath.extend ε t)‖ ≤
        ∫ t in (0 : ℝ)..1,
          (badSetIcc γP T ε).indicator (fun _ : ℝ ↦ M) t := by
      refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ ?_
      · refine MeasureTheory.ae_of_all _ fun t ht ↦ ?_
        exact h_diff_norm_bound_on_Icc ε ⟨hε_pos, hε_lt_R⟩ t ⟨ht.1.le, ht.2⟩
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
        refine (MeasureTheory.integrable_indicator_iff
          (badSetIcc_measurableSet γP T ε)).mpr ?_
        refine MeasureTheory.integrableOn_const (μ := volume.restrict (Set.Ioc 0 1))
          (s := badSetIcc γP T ε) (C := M) ?_
        rw [MeasureTheory.Measure.restrict_apply (badSetIcc_measurableSet γP T ε)]
        exact ((measure_mono (Set.inter_subset_right :
          badSetIcc γP T ε ∩ Set.Ioc 0 1 ⊆ Set.Ioc 0 1)).trans_lt measure_Ioc_lt_top).ne
    have h_ind_int :
        ∫ t in (0 : ℝ)..1, (badSetIcc γP T ε).indicator (fun _ : ℝ ↦ M) t =
          M * (volume (badSetIcc γP T ε ∩ Set.Ioc 0 1)).toReal := by
      rw [intervalIntegral.integral_of_le zero_le_one,
          MeasureTheory.integral_indicator (badSetIcc_measurableSet γP T ε),
          MeasureTheory.setIntegral_const, MeasureTheory.Measure.real,
          MeasureTheory.Measure.restrict_apply (badSetIcc_measurableSet γP T ε),
          smul_eq_mul, mul_comm]
    rw [h_ind_int] at h_bound_aux
    exact h_bound_aux.trans (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (badSetIcc_volume_ne_top γP T ε)
        (measure_mono Set.inter_subset_left)) hM_nonneg)
  have h_vol_lim : Tendsto (fun ε ↦ (volume (badSetIcc γP T ε)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    have := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp
      (badSet_volume_tendsto_zero γ T)
    simpa only [Function.comp_def, ENNReal.toReal_zero] using this
  have h_bound_tendsto : Tendsto (fun ε ↦ M * (volume (badSetIcc γP T ε)).toReal)
      (𝓝[>] 0) (𝓝 0) := by simpa using h_vol_lim.const_mul M
  have h_diff_tendsto :
      Tendsto (fun ε ↦ (∫ t in (0 : ℝ)..1, cpvIntegrand (decomp.polarPart s)
          γP.toPath.extend s ε t) -
        (∫ t in (0 : ℝ)..1, cpvIntegrandOn S (decomp.polarPart s)
          γP.toPath.extend ε t)) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h_bound_tendsto
    filter_upwards [Ioo_mem_nhdsGT hR_pos] with ε hε
    exact h_int_bound ε hε
  unfold HasCauchyPVOn
  unfold HasCauchyPV at h
  simpa [sub_sub_self] using (h.sub h_diff_tendsto)

end MultiPoleDCT

end HungerbuhlerWasem

end
