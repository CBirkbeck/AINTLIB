# Inventory — `ForMathlib/LatticePointCount.lean`

File: `projects/Chebotarev/CebotarevDensity/ForMathlib/LatticePointCount.lean`
Namespace: `Chebotarev`. Whole file is `@[expose] public section` (so the default visibility of every non-`private` decl is **public**).
Topic: effective lattice-point count with a Lipschitz-boundary `O(nᵈ⁻¹)` error term — author-earmarked for mathlib.

---

### `lemma ceil_natCast_mul_le_ceil_natCast_mul_add`
- **Type**: `(n : ℕ) {a b r : ℝ} (h : a ≤ b + r) : (⌈(n : ℝ) * a⌉ : ℤ) ≤ ⌈(n : ℝ) * b⌉ + ⌈(n : ℝ) * r⌉`
- **What**: A subadditivity-style bound on integer ceilings: if `a ≤ b + r`, then `⌈n·a⌉ ≤ ⌈n·b⌉ + ⌈n·r⌉`.
- **How**: Two-step `calc`: monotonicity `Int.ceil_le_ceil` (using `n·a ≤ n·b + n·r` from `Nat.cast_nonneg` and `nlinarith`), then the mathlib ceiling subadditivity `Int.ceil_add_le`.
- **Hypotheses**: `n : ℕ`; reals `a, b, r` with `a ≤ b + r`.
- **Uses from project**: `[]`
- **Used by**: `ncard_index_image_le_of_diam_le`.
- **Visibility**: private
- **Lines**: 59–64 (proof ~5 lines).
- **Notes**: none.

### `lemma abs_sub_le_one_div_of_ceil_natCast_mul_eq`
- **Type**: `{n : ℕ} (hn : 0 < (n : ℝ)) {a b : ℝ} (h : ⌈(n : ℝ) * a⌉ = ⌈(n : ℝ) * b⌉) : |a - b| ≤ 1 / n`
- **What**: If `n·a` and `n·b` have the same ceiling, then `a` and `b` are within `1/n` of each other (cells of the `1/n` grid have diameter `1/n`).
- **How**: Rewrites `a - b = (n·a - n·b)/n`, reduces via `abs_div` / `div_le_div_iff_of_pos_right` to `|n·a − n·b| ≤ 1`, then closes both bounds with `nlinarith` fed `Int.le_ceil` and `Int.ceil_lt_add_one` at `n·a` and `n·b` plus the equality of ceilings.
- **Hypotheses**: `0 < (n:ℝ)`; equality of the two ceilings `⌈n·a⌉ = ⌈n·b⌉`.
- **Uses from project**: `[]`
- **Used by**: `ncard_index_image_chart_le`.
- **Visibility**: private
- **Lines**: 66–73 (proof ~7 lines).
- **Notes**: none.

### `theorem setFinite_index_image_of_isBounded`
- **Type**: `(n : ℕ) {T : Set (ι → ℝ)} (hbdd : Bornology.IsBounded T) : (index n '' T).Finite`
- **What**: Only finitely many cells of the `n⁻¹ℤ^ι` grid meet a bounded set; i.e. the `index n`-image of a bounded `T` is finite.
- **How**: `IsBounded.subset_closedBall` gives a radius `R`; the index-image is shown `⊆` the explicit finite product `Fintype.piFinset` of integer intervals `Icc (⌈-(n·R)⌉-1) (⌈n·R⌉-1)`, using `dist_le_pi_dist` to bound each coordinate and `Int.ceil_le_ceil` on the index. Closed by `Set.Finite.subset`.
- **Hypotheses**: `T` bounded in the sup metric on `ι → ℝ` (`Fintype ι`).
- **Uses from project**: `[]` (uses mathlib `index`/`index_apply` from `BoxIntegral.unitPartition`).
- **Used by**: `ncard_index_image_chart_le`, `ncard_index_image_frontier_le`, `abs_card_inter_sub_volume_mul_pow_le`.
- **Visibility**: public
- **Lines**: 80–97 (proof ~16 lines).
- **Notes**: carries `set_option linter.unusedFintypeInType false` (false positive — `Fintype ι` needed for sup-metric). Statement is a candidate mathlib-flavoured fact; see file summary.

### `theorem ncard_index_image_le_of_diam_le`
- **Type**: `(n : ℕ) [NeZero n] {T : Set (ι → ℝ)} {r : ℝ} (hr : 0 ≤ r) (hdiam : Metric.diam T ≤ r) (hbdd : Bornology.IsBounded T) : (index n '' T).ncard ≤ (2 * ⌈(n:ℝ) * r⌉₊ + 1) ^ Fintype.card ι`
- **What**: Bounded-diameter cell incidence — a set of diameter `≤ r` meets at most `(2⌈n·r⌉₊+1)ᵈ` grid cells (`d = #ι`).
- **How**: Empty case `simp`. Otherwise pick `x₀ ∈ T`; bound the index-image inside the box `Fintype.piFinset (Icc (cᵢ−K) (cᵢ+K))` with `c = index n x₀`, `K = ⌈n·r⌉₊`, using `dist_le_pi_dist` + `Metric.dist_le_diam_of_mem` for the per-coordinate bound and `ceil_natCast_mul_le_ceil_natCast_mul_add` (project) for the index bound. Cardinality via `Int.card_Icc`, `Finset.prod_const`, `Finset.card_univ`.
- **Hypotheses**: `n ≠ 0`; `0 ≤ r`; `diam T ≤ r`; `T` bounded.
- **Uses from project**: `ceil_natCast_mul_le_ceil_natCast_mul_add`.
- **Used by**: `ncard_index_image_chart_le`.
- **Visibility**: public
- **Lines**: 99–133 (proof ~29 lines).
- **Notes**: long (30–50) — borderline at ~29; treat as substantial. No sorry/set_option.

### `theorem ncard_index_image_chart_le`
- **Type**: `{M : ℝ≥0} {φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)} (hφ : LipschitzWith M φ) {n : ℕ} (hn : 1 ≤ n) : (index n '' (φ '' Set.Icc 0 1)).ncard ≤ (2 * ⌈(M:ℝ)⌉₊ + 1) ^ Fintype.card ι * (n + 1) ^ (Fintype.card ι - 1)`
- **What**: Single-chart cell count — for one `M`-Lipschitz `φ` from `[0,1]ᵈ⁻¹`, the number of grid cells meeting `φ '' [0,1]ᵈ⁻¹` is `≤ (2⌈M⌉₊+1)ᵈ·(n+1)ᵈ⁻¹ = O(nᵈ⁻¹)`.
- **How**: Partition `[0,1]ᵈ⁻¹` by the coordinatewise ceiling map `q y k = ⌈n·yₖ⌉`, indexed by the finite box `T = Icc 0 (fun _ ↦ n)`. Each piece `Icc 0 1 ∩ q⁻¹{v}` has diameter `≤ 1/n` (`abs_sub_le_one_div_of_ceil_natCast_mul_eq`, project), so its φ-image has diameter `≤ M/n`, and `ncard_index_image_le_of_diam_le` (project) bounds its cells by `(2⌈M⌉₊+1)ᵈ` (after `n·(M·(1/n)) = M`). Sum over `T` via `Finset.set_ncard_biUnion_le` + `Finset.sum_le_sum`; `#T = (n+1)ᵈ⁻¹` via `Pi.card_Icc`/`Int.card_Icc`.
- **Hypotheses**: `φ` is `M`-Lipschitz; `1 ≤ n`.
- **Uses from project**: `abs_sub_le_one_div_of_ceil_natCast_mul_eq`, `ncard_index_image_le_of_diam_le`, `setFinite_index_image_of_isBounded`.
- **Used by**: `ncard_index_image_frontier_le`.
- **Visibility**: public
- **Lines**: 135–198 (proof ~56 lines).
- **Notes**: **OVER-50 — needs further /decompose-proof pass** (~56-line proof; natural helpers: the diameter-of-piece bound `hdiam`, the cover `hcover`, the per-piece bound `hpiece`). No sorry/set_option.

### `theorem ncard_index_image_frontier_le`
- **Type**: `{s : Set (ι → ℝ)} {m : ℕ} {M : ℝ≥0} {φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)} (hφ : ∀ j, LipschitzWith M (φ j)) (hcov : frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1) {n : ℕ} (hn : 1 ≤ n) : (index n '' frontier s).ncard ≤ (m * (2 * ⌈(M:ℝ)⌉₊ + 1) ^ Fintype.card ι * 2 ^ (Fintype.card ι - 1)) * n ^ (Fintype.card ι - 1)`
- **What**: Boundary-cell count — if `∂s` is covered by `m` images of `M`-Lipschitz charts, the number of grid cells meeting `∂s` is `O(nᵈ⁻¹)` with explicit constant `m·(2⌈M⌉₊+1)ᵈ·2ᵈ⁻¹`.
- **How**: `index n '' ∂s ⊆ ⋃ j, index n '' (φ j '' [0,1])` via `Set.image_iUnion` + `Set.image_mono hcov`; then `Set.ncard_iUnion_le_of_fintype` + `Finset.sum_le_sum` with the per-chart bound `ncard_index_image_chart_le` (project); finally replace `(n+1)ᵈ⁻¹ ≤ 2ᵈ⁻¹·nᵈ⁻¹` (`Nat.pow_le_pow_left`) and a `gcongr`/`ring` `calc`.
- **Hypotheses**: all `φ j` are `M`-Lipschitz; `∂s ⊆ ⋃ⱼ φ j '' [0,1]ᵈ⁻¹`; `1 ≤ n`.
- **Uses from project**: `ncard_index_image_chart_le`, `setFinite_index_image_of_isBounded`.
- **Used by**: `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`.
- **Visibility**: public
- **Lines**: 200–232 (proof ~23 lines).
- **Notes**: none (no sorry/set_option).

### `lemma index_mem_image_frontier_of_box_meet_not_subset`
- **Type**: `{n : ℕ} [NeZero n] {s : Set (ι → ℝ)} {ν : ι → ℤ} (hmeet : ((box n ν : Set (ι → ℝ)) ∩ s).Nonempty) (hnsub : ¬ (box n ν : Set (ι → ℝ)) ⊆ s) : ν ∈ index n '' frontier s`
- **What**: If a grid box meets `s` but is not contained in `s`, then its index `ν` is the index of some boundary point — the cell straddles `∂s`.
- **How**: The box is preconnected (`Box.coe_eq_pi` + `convex_pi`/`convex_Ioc`). Assuming (for contradiction) the box misses `∂s`, it splits into `interior s ∪ (closure s)ᶜ`; preconnectedness (`IsPreconnected.subset_or_subset` with `isOpen_interior`, `isClosed_closure.isOpen_compl`, disjointness) forces the whole box into one side, contradicting either a chosen point of `box ∩ sᶜ` or the meeting point.
- **Hypotheses**: `n ≠ 0`; box `ν` meets `s`; box `ν` not `⊆ s`. (`Fintype ι` is `omit`-ted.)
- **Uses from project**: `[]` (uses mathlib `box`, `mem_box_iff_index` from `unitPartition`).
- **Used by**: `abs_card_inter_sub_volume_mul_pow_le`.
- **Visibility**: private
- **Lines**: 234–259 (proof ~25 lines).
- **Notes**: long (30–50) — ~25-line proof, watch in decompose pass. `omit [Fintype ι]`. No sorry.

### `lemma measureReal_biUnion_box`
- **Type**: `(n : ℕ) [NeZero n] (t : Finset (ι → ℤ)) : volume.real (⋃ ν ∈ t, (box n ν : Set (ι → ℝ))) = t.card / (n : ℝ) ^ Fintype.card ι`
- **What**: The real volume of a finite disjoint union of grid boxes is `#t / nᵈ` (each box has volume `1/nᵈ`).
- **How**: Each box volume is `1/nᵈ` (`measureReal_def`, mathlib `volume_box`); the boxes are pairwise disjoint and measurable with finite measure, so `measureReal_biUnion_finset` applies, then `Finset.sum_const`/`nsmul_eq_mul`/`ring`.
- **Hypotheses**: `n ≠ 0`; `t` a finite set of integer indices.
- **Uses from project**: `[]` (mathlib `box`, `volume_box`, `disjoint` from `unitPartition`).
- **Used by**: `abs_card_inter_sub_volume_mul_pow_le`.
- **Visibility**: private
- **Lines**: 261–272 (proof ~11 lines).
- **Notes**: none.

### `theorem abs_card_inter_sub_volume_mul_pow_le`
- **Type**: `{s : Set (ι → ℝ)} (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s) {n : ℕ} (hn : 1 ≤ n) : |(Nat.card ↑(s ∩ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ) - volume.real s * (n:ℝ) ^ Fintype.card ι| ≤ (index n '' frontier s).ncard`
- **What**: Count↔volume bridge — the number of points of `n⁻¹ℤ^ι` in a bounded measurable `s` differs from `vol(s)·nᵈ` by at most the number of grid cells meeting `∂s` (effective sandwich behind `tendsto_card_div_pow_atTop_volume`).
- **How**: Sets up `Inside ⊆ Tag ⊆ Meet ⊆ Inside ∪ Bd` where `Inside = {ν : box⊆s}`, `Meet = {ν : box meets s}`, `Bd = index n '' ∂s`, `Tag = {ν : tag n ν ∈ s}`. Identifies the lattice count with `Tag.ncard` via `tag_index_eq_self_of_mem_smul_span` / `tag_mem_smul_span` / `index_tag` and injectivity `eq_of_mem_smul_span_of_index_eq_index`; the `Meet ⊆ Inside ∪ Bd` step uses `index_mem_image_frontier_of_box_meet_not_subset` (project). Volume is sandwiched: `Inside.ncard ≤ V ≤ Meet.ncard` from `measureReal_mono` on `⋃ box` together with `measureReal_biUnion_box` (project); finiteness from `setFinite_index_image_of_isBounded` and mathlib `setFinite_index`. Combined by `abs_le` + `linarith`.
- **Hypotheses**: `s` bounded, measurable; `1 ≤ n`.
- **Uses from project**: `setFinite_index_image_of_isBounded`, `index_mem_image_frontier_of_box_meet_not_subset`, `measureReal_biUnion_box`.
- **Used by**: `exists_card_inter_smul_lattice_sub_volume_mul_pow_le`.
- **Visibility**: public
- **Lines**: 277–355 (proof ~72 lines).
- **Notes**: **OVER-50 — needs further /decompose-proof pass** (~72-line proof; natural helpers: the `Tag.ncard` identification `hNeq`, the chain inclusions, and the two volume bounds `hvol_lower`/`hvol_upper`). No sorry/set_option.

### `theorem exists_card_inter_smul_lattice_sub_volume_mul_pow_le`
- **Type**: `{ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) (hbdd : Bornology.IsBounded s) (hmeas : MeasurableSet s) (hlip : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧ frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1) : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → |(Nat.card ↑(s ∩ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ) - volume.real s * (n:ℝ) ^ Fintype.card ι| ≤ C * (n:ℝ) ^ (Fintype.card ι - 1)`
- **What**: Terminal export — for a bounded measurable `s` whose frontier is covered by finitely many Lipschitz images of `[0,1]ᵈ⁻¹`, the lattice-point count equals `vol(s)·nᵈ` up to `O(nᵈ⁻¹)`; the effective form of `tendsto_card_div_pow_atTop_volume`.
- **How**: Destructure the Lipschitz cover; take `C = m·(2⌈M⌉₊+1)ᵈ·2ᵈ⁻¹` (cast from ℕ); chain `abs_card_inter_sub_volume_mul_pow_le` (project) then `ncard_index_image_frontier_le` (project, cast via `Nat.cast_le`), closing with `push_cast; ring`.
- **Hypotheses**: `s` bounded, measurable; frontier covered by finitely many common-Lipschitz-constant charts from the `(d−1)`-cube.
- **Uses from project**: `abs_card_inter_sub_volume_mul_pow_le`, `ncard_index_image_frontier_le`.
- **Used by**: unused in file (terminal export; the file's `Main results`).
- **Visibility**: public
- **Lines**: 359–380 (proof ~6 lines).
- **Notes**: none.

---

## File Summary

**Total declarations: 9** — defs: 0 / lemmas+theorems: 9 (4 `private` lemmas + 5 `public` theorems) / instances: 0 / structures/classes/abbrevs/inductives: 0.

**Key API (used by ≥3 in-file):**
- `setFinite_index_image_of_isBounded` — used by 3 (`ncard_index_image_chart_le`, `ncard_index_image_frontier_le`, `abs_card_inter_sub_volume_mul_pow_le`).
- (Next-most-reused: `ncard_index_image_le_of_diam_le`, `ncard_index_image_chart_le`, each used by 1; the dependency spine is otherwise a clean linear chain → terminal export.)

**Unused-in-file decls:** `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (intended terminal export — consumed by other Chebotarev files, e.g. the unit-grid ideal-congruence count).

**Decls with `sorry`:** none.

**Decls with `set_option`:** `setFinite_index_image_of_isBounded` (`set_option linter.unusedFintypeInType false in` — documented false positive).

**Proofs >50 lines (decompose-needed):**
- `abs_card_inter_sub_volume_mul_pow_le` — ~72 lines (lines 277–355).
- `ncard_index_image_chart_le` — ~56 lines (lines 135–198).

**Proofs 30–50 lines:** none strictly in `[30,50]`; two are borderline-substantial just under 30 and worth noting:
- `ncard_index_image_le_of_diam_le` — ~29 lines (99–133).
- `index_mem_image_frontier_of_box_meet_not_subset` — ~25 lines (234–259).

**ForMathlib — names/statements that may already exist (or near-collide with) mathlib:**
- `ceil_natCast_mul_le_ceil_natCast_mul_add` — a ceiling subadditivity bound; mathlib already has `Int.ceil_add_le` (used inside). Check for a packaged `⌈n·a⌉ ≤ ⌈n·b⌉ + ⌈n·r⌉` form before contributing; likely too specialised to exist, but verify.
- `abs_sub_le_one_div_of_ceil_natCast_mul_eq` — "same scaled ceiling ⇒ within 1/n"; plausibly derivable from existing `Int.ceil`/`Int.fract` lemmas; check mathlib for an equivalent.
- `setFinite_index_image_of_isBounded` / `ncard_index_image_le_of_diam_le` — these are about `BoxIntegral.unitPartition.index`; mathlib's `UnitPartition` API already proves `setFinite_index` (used here) and `tendsto_card_div_pow_atTop_volume`. The effective/diameter-counting refinements look genuinely new, but they belong directly beside the existing `index` API — confirm no overlap with `setFinite_index` / `ncard`-of-index lemmas.
- `measureReal_biUnion_box` — real-volume of a finite disjoint union of `box n ν`; mathlib has `volume_box` and `measureReal_biUnion_finset`; this is a thin specialisation, may be inlineable rather than contributed.
- `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` / `abs_card_inter_sub_volume_mul_pow_le` — explicitly framed as the *effective* strengthening of mathlib's `tendsto_card_div_pow_atTop_volume`; the headline new results, no direct mathlib equivalent expected.

**General/naming note (ForMathlib):** decls are stated for `ι : Type*` with `[Fintype ι]` over the sup-metric `ι → ℝ` and the standard lattice `span ℤ (range (Pi.basisFun ℝ ι))` — appropriately general for a mathlib `UnitPartition`-adjacent contribution. Names follow mathlib conventions (`setFinite_…`, `ncard_…_le`, `abs_…_le`, `exists_…_le`). The `Chebotarev` namespace would need stripping/relocating on contribution.
