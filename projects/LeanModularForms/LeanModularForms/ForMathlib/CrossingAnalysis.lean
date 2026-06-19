/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.CurveUtilities
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Compactness.Compact

/-!
# Crossing Analysis — Proposition 2.2

For a `PwC1Immersion` γ : [0,1] → E, the set of parameter values where γ
passes through a given point z₀ is finite. This is Proposition 2.2 from
Hungerbühler–Wasem.

## Main definitions

* `PwC1Immersion.crossingSet` — the set `{t ∈ Icc 0 1 | γ t = z₀}`

## Main results

* `PwC1Immersion.crossingSet_isClosed` — the crossing set is closed
* `PwC1Immersion.crossing_isolated_smooth` — crossings at smooth points are isolated
* `PwC1Immersion.crossing_isolated_left` — crossings at partition points are
  isolated from the left
* `PwC1Immersion.crossing_isolated_right` — crossings at partition points are
  isolated from the right
* `PwC1Immersion.crossing_isolated` — every crossing in `(0,1)` is isolated
* `PwC1Immersion.crossingSet_finite` — **Proposition 2.2**: the crossing set is finite

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x y : E}

namespace PwC1Immersion

/-- The crossing set: parameter values in `[0, 1]` where the path passes through `z₀`. -/
def crossingSet (γ : PwC1Immersion x y) (z₀ : E) : Set ℝ :=
  {t ∈ Icc (0 : ℝ) 1 | (γ : ℝ → E) t = z₀}

theorem crossingSet_subset_Icc (γ : PwC1Immersion x y) (z₀ : E) :
    γ.crossingSet z₀ ⊆ Icc (0 : ℝ) 1 :=
  fun _ ht ↦ ht.1

/-- The crossing set is closed. -/
theorem crossingSet_isClosed (γ : PwC1Immersion x y) (z₀ : E) :
    _root_.IsClosed (γ.crossingSet z₀) := by
  have : γ.crossingSet z₀ = Icc (0 : ℝ) 1 ∩ (γ : ℝ → E) ⁻¹' {z₀} := by
    ext t
    simp only [crossingSet, mem_sep_iff, mem_inter_iff, mem_preimage, mem_singleton_iff]
  rw [this]
  exact isClosed_Icc.inter (isClosed_singleton.preimage γ.toPiecewiseC1Path.continuous)

/-- Near `p` from the left, points are eventually not in the partition. -/
private theorem eventually_not_in_partition_left
    (γ : PwC1Immersion x y) (p : ℝ) :
    ∀ᶠ t in 𝓝[<] p, t ∉ γ.toPiecewiseC1Path.partition := by
  have hcl : _root_.IsClosed ((↑γ.toPiecewiseC1Path.partition \ {p} : Set ℝ)) :=
    (γ.toPiecewiseC1Path.partition.finite_toSet.subset diff_subset).isClosed
  have hmem : p ∉ (↑γ.toPiecewiseC1Path.partition \ {p} : Set ℝ) := by simp
  have h1 : ∀ᶠ t in 𝓝[<] p, t ∈ (↑γ.toPiecewiseC1Path.partition \ {p} : Set ℝ)ᶜ :=
    eventually_nhdsWithin_of_eventually_nhds (hcl.isOpen_compl.mem_nhds hmem)
  have h2 : ∀ᶠ t in 𝓝[<] p, t < p := eventually_nhdsWithin_of_forall fun t ht ↦ ht
  exact (h1.and h2).mono fun t ⟨ht_compl, ht_lt⟩ ht_part ↦
    ht_compl ⟨ht_part, ne_of_lt ht_lt⟩

/-- Near `p` from the right, points are eventually not in the partition. -/
private theorem eventually_not_in_partition_right
    (γ : PwC1Immersion x y) (p : ℝ) :
    ∀ᶠ t in 𝓝[>] p, t ∉ γ.toPiecewiseC1Path.partition := by
  have hcl : _root_.IsClosed ((↑γ.toPiecewiseC1Path.partition \ {p} : Set ℝ)) :=
    (γ.toPiecewiseC1Path.partition.finite_toSet.subset diff_subset).isClosed
  have hmem : p ∉ (↑γ.toPiecewiseC1Path.partition \ {p} : Set ℝ) := by simp
  have h1 : ∀ᶠ t in 𝓝[>] p, t ∈ (↑γ.toPiecewiseC1Path.partition \ {p} : Set ℝ)ᶜ :=
    eventually_nhdsWithin_of_eventually_nhds (hcl.isOpen_compl.mem_nhds hmem)
  have h2 : ∀ᶠ t in 𝓝[>] p, p < t := eventually_nhdsWithin_of_forall fun t ht ↦ ht
  exact (h1.and h2).mono fun t ⟨ht_compl, ht_gt⟩ ht_part ↦
    ht_compl ⟨ht_part, ne_of_gt ht_gt⟩

/-- `Ioo q p ⊆ Ioo 0 1` implies `Icc q p ⊆ Icc 0 1` by taking closures. -/
private theorem Icc_subset_of_Ioo_subset {q p : ℝ} (hqp : q < p)
    (h : Ioo q p ⊆ Ioo (0 : ℝ) 1) : Icc q p ⊆ Icc (0 : ℝ) 1 := by
  have := closure_mono h
  rwa [closure_Ioo (ne_of_lt hqp), closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at this

/-- At a smooth point where `γ(t₀) = z₀`, there is a punctured neighborhood in which
`γ(t) ≠ z₀`. -/
theorem crossing_isolated_smooth (γ : PwC1Immersion x y) (z₀ : E) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hcross : (γ : ℝ → E) t₀ = z₀)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) :
    ∀ᶠ t in 𝓝[≠] t₀, (γ : ℝ → E) t ≠ z₀ := by
  rw [← hcross]
  exact (γ.toPiecewiseC1Path.differentiable_off_extend t₀ ht₀ hsmooth).hasDerivAt.eventually_ne
    (γ.deriv_ne_zero t₀ ht₀ hsmooth)

/-- At a partition point `p` with `0 < p`, `γ(t) ≠ γ(p)` for `t` sufficiently close
to `p` from the left. -/
theorem crossing_isolated_left (γ : PwC1Immersion x y) (z₀ : E) (p : ℝ)
    (hp_part : p ∈ γ.toPiecewiseC1Path.partition) (hp_pos : 0 < p)
    (hcross : (γ : ℝ → E) p = z₀) :
    ∀ᶠ t in 𝓝[<] p, (γ : ℝ → E) t ≠ z₀ := by
  obtain ⟨L, hL_ne, hL_tendsto⟩ := γ.left_deriv_limit p hp_part
  obtain ⟨f, _, hf_L⟩ := exists_dual_vector ℝ L (norm_ne_zero_iff.mpr hL_ne)
  have hfL_pos : (0 : ℝ) < f L := by
    rw [hf_L]
    exact_mod_cast norm_pos_iff.mpr hL_ne
  set h : ℝ → ℝ := fun t ↦ f ((γ : ℝ → E) t - z₀) with hh_def
  have hh_p : h p = 0 := by simp only [hh_def, hcross, sub_self, map_zero]
  have hp_Ioo := γ.toPiecewiseC1Path.partition_subset hp_part
  have h_ev_smooth := eventually_not_in_partition_left γ p
  have h_ev_Ioo : ∀ᶠ t in 𝓝[<] p, t ∈ Ioo (0 : ℝ) 1 :=
    (eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hp_pos) |>.and
      (eventually_nhdsWithin_of_forall fun _ ht ↦ ht)).mono
      fun _ ⟨h0t, htp⟩ ↦ ⟨h0t, lt_trans htp hp_Ioo.2⟩
  have h_ev_deriv_pos : ∀ᶠ t in 𝓝[<] p, f (deriv (γ : ℝ → E) t) > 0 :=
    (f.continuous.continuousAt.tendsto.comp hL_tendsto).eventually (Ioi_mem_nhds hfL_pos)
  have h_all : ∀ᶠ t in 𝓝[<] p,
      t ∉ γ.toPiecewiseC1Path.partition ∧ t ∈ Ioo (0 : ℝ) 1 ∧
      f (deriv (γ : ℝ → E) t) > 0 :=
    h_ev_smooth.and (h_ev_Ioo.and h_ev_deriv_pos)
  rw [Filter.Eventually, mem_nhdsLT_iff_exists_Ioo_subset' hp_pos] at h_all
  obtain ⟨q, hq_lt_p, hq_cond⟩ := h_all
  have hqp_sub : Icc q p ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_of_Ioo_subset hq_lt_p (fun t ht ↦ (hq_cond ht).2.1)
  have hh_cont_qp : ContinuousOn h (Icc q p) :=
    f.continuous.comp_continuousOn
      ((γ.toPiecewiseC1Path.continuous.continuousOn.mono hqp_sub).sub continuousOn_const)
  have hh_deriv_pos : ∀ s ∈ interior (Icc q p), 0 < deriv h s := by
    rw [interior_Icc]
    intro s hs
    obtain ⟨hs_smooth, hs_Ioo, hs_dpos⟩ := hq_cond hs
    have h_sub : HasDerivAt (fun t ↦ (γ : ℝ → E) t - z₀) (deriv (γ : ℝ → E) s - 0) s :=
      (γ.toPiecewiseC1Path.differentiable_off_extend s hs_Ioo hs_smooth).hasDerivAt.sub
        (hasDerivAt_const s z₀)
    simp only [sub_zero] at h_sub
    exact (f.hasFDerivAt.comp_hasDerivAt s h_sub).deriv ▸ hs_dpos
  have hh_mono := strictMonoOn_of_deriv_pos (convex_Icc q p) hh_cont_qp hh_deriv_pos
  rw [Filter.Eventually, mem_nhdsLT_iff_exists_Ioo_subset' hp_pos]
  exact ⟨q, hq_lt_p, fun t ht hγt ↦ by
    have hht : h t = 0 := by simp only [hh_def, hγt, sub_self, map_zero]
    have : h t < h p := hh_mono (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr hq_lt_p.le) ht.2
    linarith⟩

/-- At a partition point `p` with `p < 1`, `γ(t) ≠ γ(p)` for `t` sufficiently close
to `p` from the right. -/
theorem crossing_isolated_right (γ : PwC1Immersion x y) (z₀ : E) (p : ℝ)
    (hp_part : p ∈ γ.toPiecewiseC1Path.partition) (hp_lt_one : p < 1)
    (hcross : (γ : ℝ → E) p = z₀) :
    ∀ᶠ t in 𝓝[>] p, (γ : ℝ → E) t ≠ z₀ := by
  obtain ⟨L, hL_ne, hL_tendsto⟩ := γ.right_deriv_limit p hp_part
  obtain ⟨f, _, hf_L⟩ := exists_dual_vector ℝ L (norm_ne_zero_iff.mpr hL_ne)
  have hfL_pos : (0 : ℝ) < f L := by
    rw [hf_L]
    exact_mod_cast norm_pos_iff.mpr hL_ne
  set h : ℝ → ℝ := fun t ↦ f ((γ : ℝ → E) t - z₀) with hh_def
  have hh_p : h p = 0 := by simp only [hh_def, hcross, sub_self, map_zero]
  have hp_Ioo := γ.toPiecewiseC1Path.partition_subset hp_part
  have h_ev_smooth := eventually_not_in_partition_right γ p
  have h_ev_Ioo : ∀ᶠ t in 𝓝[>] p, t ∈ Ioo (0 : ℝ) 1 :=
    (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hp_lt_one) |>.and
      (eventually_nhdsWithin_of_forall fun _ ht ↦ ht)).mono
      fun _ ⟨ht1, htp⟩ ↦ ⟨lt_trans hp_Ioo.1 htp, ht1⟩
  have h_ev_deriv_pos : ∀ᶠ t in 𝓝[>] p, f (deriv (γ : ℝ → E) t) > 0 :=
    (f.continuous.continuousAt.tendsto.comp hL_tendsto).eventually (Ioi_mem_nhds hfL_pos)
  have h_all : ∀ᶠ t in 𝓝[>] p,
      t ∉ γ.toPiecewiseC1Path.partition ∧ t ∈ Ioo (0 : ℝ) 1 ∧
      f (deriv (γ : ℝ → E) t) > 0 :=
    h_ev_smooth.and (h_ev_Ioo.and h_ev_deriv_pos)
  rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset' hp_lt_one] at h_all
  obtain ⟨r, hr_gt_p, hr_cond⟩ := h_all
  have hpr_sub : Icc p r ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_of_Ioo_subset hr_gt_p (fun t ht ↦ (hr_cond ht).2.1)
  have hh_cont_pr : ContinuousOn h (Icc p r) :=
    f.continuous.comp_continuousOn
      ((γ.toPiecewiseC1Path.continuous.continuousOn.mono hpr_sub).sub continuousOn_const)
  have hh_deriv_pos : ∀ s ∈ interior (Icc p r), 0 < deriv h s := by
    rw [interior_Icc]
    intro s hs
    obtain ⟨hs_smooth, hs_Ioo, hs_dpos⟩ := hr_cond hs
    have h_sub : HasDerivAt (fun t ↦ (γ : ℝ → E) t - z₀) (deriv (γ : ℝ → E) s - 0) s :=
      (γ.toPiecewiseC1Path.differentiable_off_extend s hs_Ioo hs_smooth).hasDerivAt.sub
        (hasDerivAt_const s z₀)
    simp only [sub_zero] at h_sub
    exact (f.hasFDerivAt.comp_hasDerivAt s h_sub).deriv ▸ hs_dpos
  have hh_mono := strictMonoOn_of_deriv_pos (convex_Icc p r) hh_cont_pr hh_deriv_pos
  rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset' hp_lt_one]
  exact ⟨r, hr_gt_p, fun t ht hγt ↦ by
    have hht : h t = 0 := by simp only [hh_def, hγt, sub_self, map_zero]
    have : h p < h t := hh_mono (left_mem_Icc.mpr hr_gt_p.le) (Ioo_subset_Icc_self ht) ht.1
    linarith⟩

/-- At any crossing `t₀ ∈ (0, 1)`, there is a punctured neighborhood with no other
crossings in `[0, 1]`. Combines the smooth-point and partition-point cases. -/
theorem crossing_isolated (γ : PwC1Immersion x y) (z₀ : E) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hcross : (γ : ℝ → E) t₀ = z₀) :
    ∀ᶠ t in 𝓝[≠] t₀, (γ : ℝ → E) t ≠ z₀ ∨ t ∉ Icc (0 : ℝ) 1 := by
  by_cases hpart : t₀ ∈ γ.toPiecewiseC1Path.partition
  · rw [punctured_nhds_eq_nhdsWithin_sup_nhdsWithin, Filter.eventually_sup]
    exact ⟨(crossing_isolated_left γ z₀ t₀ hpart ht₀.1 hcross).mono fun t ht ↦ Or.inl ht,
           (crossing_isolated_right γ z₀ t₀ hpart ht₀.2 hcross).mono fun t ht ↦ Or.inl ht⟩
  · exact (crossing_isolated_smooth γ z₀ t₀ ht₀ hcross hpart).mono fun t ht ↦ Or.inl ht

/-- No point of the crossing set in `(0, 1)` is an accumulation point. -/
theorem crossing_not_accPt (γ : PwC1Immersion x y) (z₀ : E) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hcross : (γ : ℝ → E) t₀ = z₀) :
    ¬AccPt t₀ (𝓟 (γ.crossingSet z₀)) := by
  rw [accPt_iff_frequently_nhdsNE, Filter.not_frequently]
  exact (crossing_isolated γ z₀ t₀ ht₀ hcross).mono fun t ht ht_mem ↦ by
    simp only [crossingSet, mem_sep_iff] at ht_mem
    exact ht.elim (fun h ↦ h ht_mem.2) (fun h ↦ h ht_mem.1)

/-- **Proposition 2.2** (Hungerbühler–Wasem): The crossing set of a piecewise C¹
immersion is finite, provided the endpoints avoid `z₀`. -/
theorem crossingSet_finite (γ : PwC1Immersion x y) (z₀ : E)
    (h0 : (γ : ℝ → E) 0 ≠ z₀) (h1 : (γ : ℝ → E) 1 ≠ z₀) :
    Set.Finite (γ.crossingSet z₀) := by
  by_contra hS_inf
  obtain ⟨a, _, ha_acc⟩ := (Set.not_finite.mp hS_inf).exists_accPt_of_subset_isCompact
    isCompact_Icc (crossingSet_subset_Icc γ z₀)
  have ha_S : a ∈ γ.crossingSet z₀ :=
    (γ.crossingSet_isClosed z₀).closure_eq ▸ mem_closure_iff_clusterPt.mpr ha_acc.clusterPt
  have ha_Ioo : a ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ha_S.1.1 (Ne.symm (fun h ↦ h0 (h ▸ ha_S.2))),
     lt_of_le_of_ne ha_S.1.2 (fun h ↦ h1 (h ▸ ha_S.2))⟩
  exact γ.crossing_not_accPt z₀ a ha_Ioo ha_S.2 ha_acc

end PwC1Immersion

end
