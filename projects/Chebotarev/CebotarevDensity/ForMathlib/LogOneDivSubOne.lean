module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Limit lemmas for `log (1 / (s - 1))` near `s = 1`

Purely analytic limit facts about the function `s ↦ log (1 / (s - 1))` on a
right neighbourhood of `1`, together with the divergent-denominator squeeze
that drives them.

## Main results

* `tendsto_log_one_div_sub_one_atTop` — `log (1 / (s - 1))` diverges to `+∞`
  as `s ↓ 1`.
* `tendsto_ratio_one_of_div_atTop_pm_bounded` — a generic squeeze: if `g → +∞`
  and `f` agrees with `g` up to a two-sided additive bounded error, then
  `f s / g s → 1`.
* `tendsto_ratio_one_of_log_pm_bounded` — the `g = log (1 / (s - 1))`, `s ↓ 1`
  specialisation of the squeeze.

None of these mention number fields or Dirichlet density; they live in the
root namespace as candidates for upstreaming to mathlib.

## Implementation notes

The squeeze is stated in the elementary `∃ C, ∀ᶠ _ ≤ _` form rather than via
`Asymptotics.IsEquivalent`; it builds directly on
`tendsto_bdd_div_atTop_nhds_zero`. The same fact can be assembled from the
`IsEquivalent` API (`isLittleO_one_left_iff`, `IsLittleO.isEquivalent`,
`isEquivalent_iff_tendsto_one`); the elementary route keeps the hypotheses in
the shape Dirichlet-density callers already produce.
-/

@[expose] public section

noncomputable section

open Filter Topology

/-- `log(1/(s-1)) → +∞` as `s ↓ 1` — the divergence driving the density
asymptotics. -/
theorem tendsto_log_one_div_sub_one_atTop :
    Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
  refine Real.tendsto_log_atTop.comp ?_
  have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by
        simp only [Set.mem_Ioi] at hs ⊢
        linarith)
  simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero

/-- Generic squeeze over an arbitrary divergent denominator: if `g → +∞`
along a filter `l` and `f` agrees with `g` up to a two-sided additive
bounded error (eventually along `l`), then `f s / g s → 1`. The additive
bounded term washes out because the denominator blows up; no property of
the denominator beyond divergence is used. -/
theorem tendsto_ratio_one_of_div_atTop_pm_bounded
    {l : Filter ℝ} {g f : ℝ → ℝ} (hg : Tendsto g l atTop)
    (h_le : ∃ C : ℝ, ∀ᶠ s in l, f s ≤ g s + C)
    (h_lower : ∃ C : ℝ, ∀ᶠ s in l, g s - C ≤ f s) :
    Tendsto (fun s : ℝ ↦ f s / g s) l (𝓝 1) := by
  obtain ⟨C₁, hle⟩ := h_le
  obtain ⟨C₂, hlower⟩ := h_lower
  have h0 : Tendsto (fun s ↦ (f s - g s) / g s) l (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero (b := -C₂) (B := C₁)
      (hlower.mono fun s h ↦ by linarith) (hle.mono fun s h ↦ by linarith) hg
  refine (add_zero (1 : ℝ) ▸ h0.const_add 1).congr' ?_
  filter_upwards [hg.eventually_gt_atTop 0] with s h
  rw [add_div_eq_mul_add_div _ _ h.ne', one_mul, add_sub_cancel]

/-- Generic squeeze: if `f(s) = log(1/(s-1)) + bounded` on a right
neighbourhood of `1`, then `f(s) / log(1/(s-1)) → 1` as `s ↓ 1`. The
analytic content is just that `log(1/(s-1)) → ∞`, so the additive
bounded term washes out under division. The log-free statement is
`tendsto_ratio_one_of_div_atTop_pm_bounded`. -/
theorem tendsto_ratio_one_of_log_pm_bounded (f : ℝ → ℝ)
    (h_le : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), f s ≤ Real.log (1 / (s - 1)) + C)
    (h_lower : ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), Real.log (1 / (s - 1)) - C ≤ f s) :
    Tendsto (fun s : ℝ ↦ f s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_div_atTop_pm_bounded tendsto_log_one_div_sub_one_atTop h_le h_lower
