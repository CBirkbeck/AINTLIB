# Inventory — `ForMathlib/LogOneDivSubOne.lean`

Path: `projects/Chebotarev/CebotarevDensity/ForMathlib/LogOneDivSubOne.lean`
File-level: `module`; `public import` of `Mathlib.Analysis.SpecialFunctions.Log.Basic` and `Mathlib.Topology.Algebra.Order.Field`; `@[expose] public section`; `noncomputable section`; `open Filter Topology`. All three declarations live in the **root namespace** (no project namespace) — author-earmarked for upstreaming to mathlib.

---

### `theorem tendsto_log_one_div_sub_one_atTop`
- **Type**: `Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop`
- **What**: The real function `s ↦ log(1/(s−1))` diverges to `+∞` as `s` approaches `1` from the right (the right-neighbourhood filter `𝓝[>] 1`).
- **How**: Composes `Real.tendsto_log_atTop` (log → +∞ at +∞) with the fact that `1/(s−1) → +∞`. The inner limit is built by first showing `s − 1 → 0⁺` as a map `𝓝[>] 1 → 𝓝[>] 0` (via `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` from continuity of subtraction plus an `Ioi` membership `linarith`), then applying `Tendsto.inv_tendsto_nhdsGT_zero` to get the reciprocal diverging, rewriting `(s-1)⁻¹` to `1/(s-1)` with `one_div`.
- **Hypotheses**: none (closed statement).
- **Uses from project**: `[]`
- **Used by**: `tendsto_ratio_one_of_log_pm_bounded`
- **Visibility**: public
- **Lines**: 42–53 (proof ≈ 8 lines)
- **Notes**: none. (Uses `simpa ... using!` with bang variant; no `sorry`/`set_option`/`TODO`.)

---

### `theorem tendsto_ratio_one_of_div_atTop_pm_bounded`
- **Type**: `{l : Filter ℝ} {g f : ℝ → ℝ} (hg : Tendsto g l atTop) (h_le : ∃ C, ∀ᶠ s in l, f s ≤ g s + C) (h_lower : ∃ C, ∀ᶠ s in l, g s - C ≤ f s) : Tendsto (fun s ↦ f s / g s) l (𝓝 1)`
- **What**: Generic additive-perturbation squeeze: along any filter `l`, if `g → +∞` and `f` is sandwiched between `g − C` and `g + C` (two-sided additive bounded error, possibly different constants), then the ratio `f/g → 1`.
- **How**: Unpacks the two constants, then shows `(f−g)/g → 0` via `tendsto_bdd_div_atTop_nhds_zero` (numerator `f − g` is bounded in `[−C₂, C₁]`, denominator `g → +∞`), so `1 + (f−g)/g → 1`. Finishes by `congr'`-rewriting `1 + (f−g)/g` to `f/g` eventually where `g > 0` (from `hg.eventually_gt_atTop 0`), using `add_div_eq_mul_add_div` and `add_sub_cancel`.
- **Hypotheses**: `g` tends to `+∞` along `l`; `f ≤ g + C₁` eventually; `g − C₂ ≤ f` eventually.
- **Uses from project**: `[]`
- **Used by**: `tendsto_ratio_one_of_log_pm_bounded`
- **Visibility**: public
- **Lines**: 60–72 (proof ≈ 9 lines)
- **Notes**: none.

---

### `theorem tendsto_ratio_one_of_log_pm_bounded`
- **Type**: `(f : ℝ → ℝ) (h_le : ∃ C, ∀ᶠ s in 𝓝[>] (1:ℝ), f s ≤ Real.log (1/(s-1)) + C) (h_lower : ∃ C, ∀ᶠ s in 𝓝[>] (1:ℝ), Real.log (1/(s-1)) - C ≤ f s) : Tendsto (fun s ↦ f s / Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 1)`
- **What**: The `g = log(1/(s−1))`, `s ↓ 1` specialisation of the squeeze: if `f` equals `log(1/(s−1))` up to a two-sided additive bounded error on a right neighbourhood of `1`, then `f(s) / log(1/(s−1)) → 1` as `s ↓ 1`.
- **How**: One-line application of `tendsto_ratio_one_of_div_atTop_pm_bounded` with the divergence witness `tendsto_log_one_div_sub_one_atTop`; the two bound hypotheses are passed straight through.
- **Hypotheses**: `f ≤ log(1/(s−1)) + C` and `log(1/(s−1)) − C ≤ f`, each eventually on `𝓝[>] 1`.
- **Uses from project**: `tendsto_ratio_one_of_div_atTop_pm_bounded`, `tendsto_log_one_div_sub_one_atTop`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 79–83 (proof = 1 line, term-mode)
- **Notes**: none.

---

## File Summary

- **Total declarations**: 3 (defs: 0 / lemmas+theorems: 3 / instances: 0).
- **Key API (used by ≥3 in-file)**: none — file has only 3 decls; the most-reused is `tendsto_log_one_div_sub_one_atTop` and `tendsto_ratio_one_of_div_atTop_pm_bounded` (each used once internally).
- **Unused decls (in file)**: `tendsto_ratio_one_of_log_pm_bounded` (the intended public entry point for Dirichlet-density callers; "unused" only means no other decl in *this* file calls it).
- **Decls with `sorry`**: none.
- **Decls with `set_option`**: none.
- **Proofs >50 lines (decompose-needed)**: none.
- **Proofs 30–50 lines**: none. (All three proofs are ≤ 9 lines.)
- **ForMathlib mathlib-overlap flags** (name/statement may already exist upstream):
  - `tendsto_log_one_div_sub_one_atTop` — very specific (`log(1/(s-1))` at `1⁺`); unlikely verbatim in mathlib, but its two ingredients (`Real.tendsto_log_atTop`, `Tendsto.inv_tendsto_nhdsGT_zero`) already exist, so it is a thin composite — worth a mathlib search before upstreaming.
  - `tendsto_ratio_one_of_div_atTop_pm_bounded` — generic additive-perturbation ratio limit. **Strong candidate for pre-existing mathlib coverage**: closely related to `Asymptotics.IsEquivalent` API (the file's own docstring cites `isLittleO_one_left_iff`, `IsLittleO.isEquivalent`, `isEquivalent_iff_tendsto_one`) and builds on `tendsto_bdd_div_atTop_nhds_zero`. Check whether an `IsEquivalent`/`IsBigO`-flavoured form already gives `f/g → 1`.
  - `tendsto_ratio_one_of_log_pm_bounded` — trivial specialisation of the above; would not be added independently to mathlib.
- **General notes**: docstrings explicitly state these "live in the root namespace as candidates for upstreaming to mathlib" and explain the deliberate choice of the elementary `∃ C, ∀ᶠ` squeeze form over the `IsEquivalent` API to match caller-produced hypothesis shapes — relevant to any generalisation/mathlibable assessment.
