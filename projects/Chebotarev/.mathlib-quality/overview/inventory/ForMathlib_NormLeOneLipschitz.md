# Inventory: `ForMathlib/NormLeOneLipschitz.lean`

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean`
Namespace: `Chebotarev`. File-level `@[expose] public section`, `noncomputable section`. Imports only `Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne`.

**NOTE (ForMathlib):** decls are author-earmarked for mathlib; generality/naming flags collected in the File Summary.

---

### `def clampUnit`
- **Type**: `(ι : Type*) (c : ι → ℝ) : ι → ℝ`, `fun i ↦ (Set.projIcc 0 1 zero_le_one (c i) : ℝ)`
- **What**: The coordinatewise retraction of a function `ι → ℝ` onto the unit cube `Icc 0 1`, applying `Set.projIcc` to each coordinate.
- **How**: Direct definition via `Set.projIcc 0 1` in each coordinate slot (no proof).
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `clampUnit_mem_Icc`, `clampUnit_eq_self`, `lipschitzWith_clampUnit`, `exists_lipschitzWith_comp_clampUnit`, `frontierCoverFamily`, and (transitively) the cover theorems.
- **Visibility**: public
- **Lines**: 86–88 (def body 1 line)
- **Notes**: none

### `theorem clampUnit_mem_Icc`
- **Type**: `(ι : Type*) (c : ι → ℝ) : clampUnit ι c ∈ Icc (0 : ι → ℝ) 1`
- **What**: The clamp always lands inside the unit cube.
- **How**: Coordinatewise, each `Set.projIcc 0 1 _ _` carries a subtype membership proof `.2.1`/`.2.2` giving the lower/upper bound.
- **Hypotheses**: none.
- **Uses from project**: `clampUnit`
- **Used by**: `exists_lipschitzWith_comp_clampUnit`, `exists_bound_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 90–92 (proof 2 lines)
- **Notes**: none

### `theorem clampUnit_eq_self`
- **Type**: `{ι : Type*} {c : ι → ℝ} (hc : c ∈ Icc (0 : ι → ℝ) 1) : clampUnit ι c = c`
- **What**: On the unit cube the clamp is the identity.
- **How**: `funext` + `Set.projIcc_of_mem` (projection fixes points already in the interval).
- **Hypotheses**: `c` lies in the unit cube `Icc 0 1`.
- **Uses from project**: `clampUnit`
- **Used by**: `frontier_subset_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 94–96 (proof 1 line)
- **Notes**: none

### `private theorem lipschitzWith_one_of_edist_apply_le`
- **Type**: `{α κ : Type*} {β : κ → Type*} [PseudoEMetricSpace α] [∀ j, PseudoEMetricSpace (β j)] [Fintype κ] {F : α → ∀ j, β j} (h : ∀ c d j, edist (F c j) (F d j) ≤ edist c d) : LipschitzWith 1 F`
- **What**: A map into a finite pi-type is `1`-Lipschitz if every output coordinate's `edist` is bounded by the input `edist`; the pi-codomain companion of `LipschitzWith.eval`.
- **How**: `LipschitzWith.of_edist_le`, then `edist_pi_def` rewrites the pi-`edist` as a finite `Finset.sup`, discharged by `Finset.sup_le` from the hypothesis.
- **Hypotheses**: every coordinate of `F` is `edist`-nonexpansive in the input; `κ` finite.
- **Uses from project**: `[]`
- **Used by**: `lipschitzWith_clampUnit`, `lipschitzWith_cubeRelabel`
- **Visibility**: private
- **Lines**: 98–105 (proof 3 lines)
- **Notes**: generic metric lemma — flag for mathlib pi/Lipschitz API (see Summary).

### `theorem lipschitzWith_clampUnit`
- **Type**: `(ι : Type*) [Fintype ι] : LipschitzWith 1 (clampUnit ι)`
- **What**: The cube clamp is globally `1`-Lipschitz.
- **How**: `lipschitzWith_one_of_edist_apply_le`, reducing each coordinate to `LipschitzWith.projIcc` (the `1`-Lipschitz interval projection) combined with `edist_le_pi_edist`.
- **Hypotheses**: `ι` finite.
- **Uses from project**: `lipschitzWith_one_of_edist_apply_le`, `clampUnit`
- **Used by**: `exists_lipschitzWith_comp_clampUnit`
- **Visibility**: public
- **Lines**: 107–110 (proof 4 lines)
- **Notes**: none

### `theorem exists_lipschitzWith_comp_clampUnit`
- **Type**: `{ι κ : Type*} [Fintype ι] [Fintype κ] {f : (ι → ℝ) → κ → ℝ} (hf : ContDiff ℝ 1 f) : ∃ M : ℝ≥0, LipschitzWith M (f ∘ clampUnit ι)`
- **What**: A globally `C¹` map `(ι→ℝ)→(κ→ℝ)` pre-composed with the cube clamp is globally Lipschitz (without changing its image of the unit cube).
- **How**: `ContDiff.locallyLipschitz` → `locallyLipschitzOn` on `Icc 0 1`, then `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact` (compactness of the cube, `isCompact_Icc`) yields a constant `M` on the cube; compose with `lipschitzWith_clampUnit` (1-Lipschitz, lands in cube) via `gcongr`.
- **Hypotheses**: `f` is `C¹`; `ι`, `κ` finite.
- **Uses from project**: `clampUnit_mem_Icc`, `lipschitzWith_clampUnit`, `clampUnit`
- **Used by**: `exists_lipschitzWith_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 112–122 (proof 6 lines)
- **Notes**: none

### `theorem contDiff_expMapBasis`
- **Type**: `ContDiff ℝ 1 (⇑(expMapBasis (K := K)))` (with `variable (K : Type*) [Field K] [NumberField K]`)
- **What**: Mathlib's `expMapBasis` map (on `realSpace K`) is continuously differentiable.
- **How**: Rewrites `expMapBasis` to the explicit product form via mathlib's `expMapBasis_apply'` (`Real.exp (x w₀) • ∏ ... ^ x i`), then `fun_prop` with a discharger proving each base `w (fundSystem …)` is positive (`InfinitePlace.pos_iff`), hence `rpow` is differentiable.
- **Hypotheses**: `K` a number field.
- **Uses from project**: `[]` (uses mathlib `expMapBasis`, `w₀`, `fundSystem`, `equivFinRank`)
- **Used by**: `contDiff_faceMapZero`, `contDiff_faceMapSide`
- **Visibility**: public
- **Lines**: 126–132 (proof 6 lines)
- **Notes**: none. `classical` used.

### `def faceMapZero`
- **Type**: `(c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K`, `= expMapBasis fun w ↦ if hw : w = w₀ then 0 else c ⟨w, hw⟩`
- **What**: Parametrization of the `expMapBasis`-image of the `w₀`-face `{x | x w₀ = 0}` of `paramSet K`: plug `0` in the `w₀`-slot, the cube coordinates elsewhere.
- **How**: Definition: `expMapBasis` precomposed with the slot-filling pi-map (no proof).
- **Hypotheses**: none (K a number field, in scope).
- **Uses from project**: `[]` (mathlib `expMapBasis`, `w₀`)
- **Used by**: `contDiff_faceMapZero`, `image_boundary_subset_faces`, `frontierCoverFamily`, `frontier_subset_frontierCoverFamily`, `exists_lipschitzWith_frontierCoverFamily`, `exists_bound_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 134–138 (def 2 lines). `open scoped Classical`.
- **Notes**: none

### `def faceMapSide`
- **Type**: `(i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ) (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K`, `= c i • expMapBasis fun w ↦ if hw : w = w₀ then 0 else if ⟨w,hw⟩ = i then a else c ⟨w,hw⟩`
- **What**: Parametrization of the `expMapBasis`-image of a side face `{x | x i = a}` (`i ≠ w₀`, `a∈{0,1}`); the unbounded `w₀`-direction is linearized by the substitution `t = exp(x w₀) ∈ (0,1]` which becomes the cube slot `c i` freed by pinning `x i = a`.
- **How**: Definition: scalar `c i •` of `expMapBasis` applied to the pinned/filled pi-map (no proof).
- **Hypotheses**: none.
- **Uses from project**: `[]` (mathlib `expMapBasis`, `w₀`)
- **Used by**: `contDiff_faceMapSide`, `expMapBasis_mem_iUnion_faceMapSide`, `image_boundary_subset_faces`, `frontierCoverFamily`, `frontier_subset_frontierCoverFamily`, `exists_lipschitzWith_frontierCoverFamily`, `exists_bound_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 140–149 (def 4 lines). `open scoped Classical`.
- **Notes**: none

### `theorem contDiff_faceMapZero`
- **Type**: `ContDiff ℝ 1 (faceMapZero K)`
- **What**: The `w₀`-face parametrization is `C¹`.
- **How**: `contDiff_expMapBasis` composed (`ContDiff.comp`) with the slot-map, shown `C¹` coordinatewise by `contDiff_pi` + case split (`contDiff_const` on `w₀`, `contDiff_apply` elsewhere).
- **Hypotheses**: K a number field.
- **Uses from project**: `contDiff_expMapBasis`, `faceMapZero`
- **Used by**: `exists_lipschitzWith_frontierCoverFamily`, `exists_bound_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 151–156 (proof 4 lines). `open scoped Classical`.
- **Notes**: none

### `theorem contDiff_faceMapSide`
- **Type**: `(i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ) : ContDiff ℝ 1 (faceMapSide K i a)`
- **What**: Each side-face parametrization is `C¹`.
- **How**: `(contDiff_apply i).smul` of (`contDiff_expMapBasis ∘` slot-map), the slot-map `C¹` coordinatewise via `contDiff_pi` and a nested case split (`w₀` / pinned-`i` give `contDiff_const`, else `contDiff_apply`).
- **Hypotheses**: K a number field.
- **Uses from project**: `contDiff_expMapBasis`, `faceMapSide`
- **Used by**: `exists_lipschitzWith_frontierCoverFamily`, `exists_bound_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 158–167 (proof 8 lines). `open scoped Classical`.
- **Notes**: none

### `theorem frontier_image_paramSet_subset`
- **Type**: `frontier (expMapBasis '' paramSet K) ⊆ expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ∪ {0}`
- **What**: Topological reduction — the frontier of the `expMapBasis`-image of `paramSet K` is contained in the image of the box boundary together with `{0}` (the escape to norm `0` as `w₀ → −∞`).
- **How**: Closure of the image sits in `compactSet K` (via `expMapBasis_closure_subset_compactSet`, `isCompact_compactSet`); interior of the image contains `expMapBasis '' interior` (via `expMapBasis.isOpen_image_of_subset_source`, `expMapBasis_source`); then `Set.diff_subset_diff`, `compactSet_eq_union`, and `Set.image_diff (injective_expMapBasis K)` finish.
- **Hypotheses**: K a number field.
- **Uses from project**: `[]` (all mathlib: `paramSet`, `compactSet`, `expMapBasis`, `expMapBasis_closure_subset_compactSet`, `isCompact_compactSet`, `compactSet_eq_union`, `injective_expMapBasis`, `expMapBasis_source`)
- **Used by**: `frontier_subset_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 169–186 (proof 10 lines)
- **Notes**: none. Hinges on mathlib `expMapBasis_closure_subset_compactSet`, `compactSet_eq_union`, `injective_expMapBasis`.

### `private theorem expMapBasis_mem_iUnion_faceMapSide`
- **Type**: `{y : realSpace K} {w : InfinitePlace K} (hwe : w ≠ w₀) (hw₀ : y w₀ ≤ 0) (hIcc : ∀ v ≠ w₀, y v ∈ Icc 0 1) (ha : y w = 0 ∨ y w = 1) : (expMapBasis y) ∈ ⋃ i, ⋃ a ∈ {0,1}, faceMapSide K i a '' Icc 0 1`
- **What**: If `y` satisfies the box-boundary constraints with `y w ∈ {0,1}` at some `w ≠ w₀`, then `expMapBasis y` lies in some side-face cube image.
- **How**: Constructs cube point `c j = if j=i then exp(y w₀) else y j` (in cube by `Real.exp_nonneg`/`exp_le_one_iff`), proves `faceMapSide K i (y w) c = expMapBasis y` via mathlib's `expMapBasis_apply''` (factoring out `exp(x w₀)`) and a `funext` matching the pinned slot map; concludes by `mem_iUnion`.
- **Hypotheses**: `w ≠ w₀`; `y w₀ ≤ 0`; all non-`w₀` coords in `[0,1]`; `y w ∈ {0,1}`.
- **Uses from project**: `faceMapSide`
- **Used by**: `image_boundary_subset_faces`
- **Visibility**: private
- **Lines**: 188–219 (proof ~31 lines). `open scoped Classical`.
- **Notes**: long (30–50). Hinges on mathlib `expMapBasis_apply''`.

### `theorem image_boundary_subset_faces`
- **Type**: `expMapBasis '' (closure (paramSet K) \ interior (paramSet K)) ⊆ faceMapZero K '' Icc 0 1 ∪ ⋃ i, ⋃ a ∈ {0,1}, faceMapSide K i a '' Icc 0 1`
- **What**: Face covering — every box-boundary image point lies in the `w₀`-face cube image or some side-face cube image.
- **How**: Unfold `closure_paramSet`/`interior_paramSet` (mathlib) to coordinate constraints; a boundary point fails an interior coordinate constraint at some `w`; case `w = w₀` gives `y w₀ = 0` (→ `faceMapZero`), else `y w ∈ {0,1}` (→ `expMapBasis_mem_iUnion_faceMapSide`).
- **Hypotheses**: K a number field.
- **Uses from project**: `faceMapZero`, `faceMapSide`, `expMapBasis_mem_iUnion_faceMapSide`
- **Used by**: `frontier_subset_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 221–256 (proof ~25 lines)
- **Notes**: long (30–50)? proof is ~25 lines → none (under 30). Hinges on mathlib `closure_paramSet`, `interior_paramSet`.

### `def cubeRelabel`
- **Type**: `(c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) : {w : InfinitePlace K // w ≠ w₀} → ℝ`, `fun j ↦ c (equivFinRank.symm j)`
- **What**: Relabels cube coordinates `Fin(#InfinitePlace K − 1) → ℝ` to functions on the non-distinguished places `{w ≠ w₀}` via mathlib's `equivFinRank`.
- **How**: Definition by precomposition with `equivFinRank.symm` (no proof).
- **Hypotheses**: none.
- **Uses from project**: `[]` (mathlib `equivFinRank`, `w₀`)
- **Used by**: `lipschitzWith_cubeRelabel`, `cubeRelabel_mem_Icc`, `exists_cubeRelabel_eq`, `frontierCoverFamily`, `exists_bound_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 258–262 (def 1 line)
- **Notes**: none

### `theorem lipschitzWith_cubeRelabel`
- **Type**: `LipschitzWith 1 (cubeRelabel K)`
- **What**: The coordinate relabelling is `1`-Lipschitz.
- **How**: `lipschitzWith_one_of_edist_apply_le`, each coordinate bounded via `edist_le_pi_edist` at `equivFinRank.symm j`.
- **Hypotheses**: K a number field.
- **Uses from project**: `lipschitzWith_one_of_edist_apply_le`, `cubeRelabel`
- **Used by**: `exists_lipschitzWith_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 264–267 (proof 2 lines). `open scoped Classical`.
- **Notes**: none

### `theorem cubeRelabel_mem_Icc`
- **Type**: `{c : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ} (hc : c ∈ Icc 0 1) : cubeRelabel K c ∈ Icc 0 1`
- **What**: Relabelling sends the unit cube into the unit cube.
- **How**: Coordinatewise pull-back of the bounds from `hc` (no real work).
- **Hypotheses**: `c` in the unit cube.
- **Uses from project**: `cubeRelabel`
- **Used by**: `frontier_subset_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 269–272 (proof 1 line)
- **Notes**: none

### `theorem exists_cubeRelabel_eq`
- **Type**: `{c' : {w : InfinitePlace K // w ≠ w₀} → ℝ} (hc' : c' ∈ Icc 0 1) : ∃ c ∈ Icc 0 1, cubeRelabel K c = c'`
- **What**: Every unit-cube point in the `{w ≠ w₀}` coordinates is the relabelling of a unit-cube point in `Fin(r−1)` coordinates (surjectivity onto the cube).
- **How**: Take `c j = c' (equivFinRank j)`; bounds inherited; equality by `funext` + `simp [cubeRelabel]` (using `equivFinRank.symm ∘ equivFinRank = id`).
- **Hypotheses**: `c'` in the unit cube.
- **Uses from project**: `cubeRelabel`
- **Used by**: `frontier_subset_frontierCoverFamily`
- **Visibility**: public
- **Lines**: 274–278 (proof 3 lines)
- **Notes**: none

### `def frontierCoverFamily`
- **Type**: `(Unit ⊕ Unit ⊕ ({w : InfinitePlace K // w ≠ w₀} × Bool)) → (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K`
- **What**: The finite family covering the frontier: the zero map (`inl ()`), the `w₀`-face map (`inr (inl ())`), and the side-face maps `faceMapSide i a` (`inr (inr (i,b))`, `a = if b then 1 else 0`), each post-clamped to the cube and relabelled through `cubeRelabel`.
- **How**: `Sum.elim` assembling the three branches (no proof).
- **Hypotheses**: none.
- **Uses from project**: `faceMapZero`, `clampUnit`, `cubeRelabel`, `faceMapSide`
- **Used by**: `exists_lipschitzWith_frontierCoverFamily`, `frontier_subset_frontierCoverFamily`, `normLeOne_frontier_lipschitz_cover`, `exists_bound_frontierCoverFamily`, `frontier_normLeOne_subset_iUnion_image_liftToMixed_aux`, `normLeOne_frontier_lipschitz_cover_mixedSpace`
- **Visibility**: public
- **Lines**: 280–289 (def 3 lines)
- **Notes**: none

### `theorem exists_lipschitzWith_frontierCoverFamily`
- **Type**: `∃ M : ℝ≥0, ∀ s, LipschitzWith M (frontierCoverFamily K s)`
- **What**: All members of `frontierCoverFamily` are `M`-Lipschitz for one common constant `M`.
- **How**: `exists_lipschitzWith_comp_clampUnit` for the `w₀`-face and (via `choose`) each side face; precompose with `lipschitzWith_cubeRelabel` (1-Lipschitz); take `M = M₀ ⊔ Finset.univ.sup Ms`; weaken each branch (zero map is `LipschitzWith.const`).
- **Hypotheses**: K a number field.
- **Uses from project**: `exists_lipschitzWith_comp_clampUnit`, `contDiff_faceMapZero`, `contDiff_faceMapSide`, `lipschitzWith_cubeRelabel`, `frontierCoverFamily`
- **Used by**: `frontier_subset_frontierCoverFamily`, `normLeOne_frontier_lipschitz_cover`, `normLeOne_frontier_lipschitz_cover_mixedSpace`
- **Visibility**: public
- **Lines**: 291–306 (proof 9 lines)
- **Notes**: none. `classical`.

### `theorem frontier_subset_frontierCoverFamily`
- **Type**: `frontier (normAtAllPlaces '' normLeOne K) ⊆ ⋃ s, frontierCoverFamily K s '' Icc 0 1`
- **What**: The frontier of the `realSpace` image of `normLeOne K` is covered by the cube images of `frontierCoverFamily`.
- **How**: Rewrite via mathlib `normAtAllPlaces_normLeOne_eq_image`; chain `frontier_image_paramSet_subset` → `image_boundary_subset_faces`; identify each face image with a family member by undoing `cubeRelabel` (`exists_cubeRelabel_eq`) and the clamp (`clampUnit_eq_self`); `{0}` is the zero map's value.
- **Hypotheses**: K a number field.
- **Uses from project**: `frontier_image_paramSet_subset`, `image_boundary_subset_faces`, `exists_cubeRelabel_eq`, `cubeRelabel_mem_Icc`, `clampUnit_eq_self`, `faceMapZero`, `faceMapSide`, `clampUnit`, `cubeRelabel`, `frontierCoverFamily`
- **Used by**: `normLeOne_frontier_lipschitz_cover`, `frontier_normLeOne_subset_iUnion_image_liftToMixed_aux`
- **Visibility**: public
- **Lines**: 308–341 (proof ~24 lines)
- **Notes**: none (under 30). `classical`. Hinges on mathlib `normAtAllPlaces_normLeOne_eq_image`.

### `theorem normLeOne_frontier_lipschitz_cover`
- **Type**: `∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K), (∀ j, LipschitzWith M (φ j)) ∧ frontier (normAtAllPlaces '' normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1`
- **What**: **Main result (realSpace).** The frontier of `normAtAllPlaces '' normLeOne K` is covered by finitely many `M`-Lipschitz images of `[0,1]^{r−1}` (`r = #InfinitePlace K`) — the `hlip` hypothesis of the effective lattice-point count.
- **How**: Reindex `frontierCoverFamily` along `Fintype.equivFin` of the sum index type; Lipschitz from `exists_lipschitzWith_frontierCoverFamily`; cover from `frontier_subset_frontierCoverFamily` via `Equiv.symm.surjective.iUnion_comp`.
- **Hypotheses**: K a number field.
- **Uses from project**: `exists_lipschitzWith_frontierCoverFamily`, `frontierCoverFamily`, `frontier_subset_frontierCoverFamily`
- **Used by**: unused in file (terminal `realSpace` API; mathematically referenced by `_mixedSpace` doc only)
- **Visibility**: public
- **Lines**: 343–358 (proof 5 lines)
- **Notes**: none. `classical`.

### `theorem dist_mul_le_norm_mul_dist`
- **Type**: `{α : Type*} [NormedField α] (a b u v : α) : dist (a * u) (b * v) ≤ ‖a‖ * dist u v + ‖v‖ * dist a b`
- **What**: Product distance estimate in a normed field, from splitting `a·u − b·v = a·(u−v) + (a−b)·v`.
- **How**: Rewrite all `dist` as norms, algebraic split (`ring`), `norm_add_le`, `norm_mul`.
- **Hypotheses**: `α` a normed field.
- **Uses from project**: `[]`
- **Used by**: `dist_mul_exp_phase_le`
- **Visibility**: public
- **Lines**: 360–367 (proof 4 lines)
- **Notes**: none. **Generic normed-field lemma — flag for mathlib (see Summary).**

### `theorem lipschitzWith_exp_ofReal_mul_I`
- **Type**: `LipschitzWith 1 (fun t : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I))`
- **What**: The unit-circle exponential `t ↦ exp(t·i)` is globally `1`-Lipschitz.
- **How**: Identify it with `circleMap 0 1` (`funext` + `simp [circleMap]`), then mathlib `lipschitzWith_circleMap 0 1` gives `|R|=1`-Lipschitz.
- **Hypotheses**: none.
- **Uses from project**: `[]` (mathlib `circleMap`, `lipschitzWith_circleMap`)
- **Used by**: `lipschitzWith_phase`
- **Visibility**: public
- **Lines**: 369–375 (proof 3 lines)
- **Notes**: none. **Possibly in/near mathlib (circleMap API) — flag (see Summary).**

### `theorem lipschitzWith_phase`
- **Type**: `LipschitzWith (2 * Real.pi).toNNReal (fun t : ℝ ↦ Complex.exp ((2 * (Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ)) * Complex.I))`
- **What**: The phase reparametrization `θ ↦ exp((2πθ − π)i)` is `2π`-Lipschitz.
- **How**: Decompose as unit-circle exp ∘ affine `θ ↦ 2πθ − π`; affine map `2π`-Lipschitz via `LipschitzWith.of_dist_le_mul` + `abs_mul`; compose with `lipschitzWith_exp_ofReal_mul_I` (rewriting `1 * (2π) = 2π`).
- **Hypotheses**: none.
- **Uses from project**: `lipschitzWith_exp_ofReal_mul_I`
- **Used by**: `dist_mul_exp_phase_le`
- **Visibility**: public
- **Lines**: 377–398 (proof ~16 lines)
- **Notes**: none (under 30).

### `theorem dist_mul_exp_phase_le`
- **Type**: `(a b θc θd : ℝ) : dist ((a:ℂ) * exp((2πθc−π)i)) ((b:ℂ) * exp((2πθd−π)i)) ≤ ‖(a:ℂ)‖ * (2π * dist θc θd) + dist (a:ℂ) (b:ℂ)`
- **What**: Per-place phase-modulus distance bound, using `‖exp((2πθd−π)i)‖ = 1` and the `2π`-Lipschitz phase.
- **How**: `dist_mul_le_norm_mul_dist`, then `‖ud‖ = 1` (`Complex.norm_exp` with zero real part) and the phase bound `lipschitzWith_phase.dist_le_mul`; `gcongr`.
- **Hypotheses**: none.
- **Uses from project**: `dist_mul_le_norm_mul_dist`, `lipschitzWith_phase`
- **Used by**: `lipschitzWith_liftToMixed`
- **Visibility**: public
- **Lines**: 400–417 (proof ~11 lines)
- **Notes**: none.

### `theorem exists_phase_mem_Icc_mul_exp`
- **Type**: `(z : ℂ) : ∃ θ : ℝ, θ ∈ Icc (0:ℝ) 1 ∧ (‖z‖:ℂ) * Complex.exp ((2*Real.pi*θ − Real.pi) * Complex.I) = z`
- **What**: Polar parametrization — every `z` equals `‖z‖ · exp((2πθ − π)i)` for some `θ ∈ [0,1]` (`θ = (arg z + π)/(2π)`).
- **How**: Take `θ = (z.arg + π)/(2π)`; membership from `Complex.neg_pi_lt_arg`/`arg_le_pi`; equality by reducing the phase to `z.arg` (`field_simp`/`ring`) and mathlib `Complex.norm_mul_exp_arg_mul_I`.
- **Hypotheses**: none.
- **Uses from project**: `[]` (mathlib `Complex.arg`, `neg_pi_lt_arg`, `arg_le_pi`, `norm_mul_exp_arg_mul_I`)
- **Used by**: `mem_iUnion_image_liftToMixed_of_eq`
- **Visibility**: public
- **Lines**: 419–436 (proof ~12 lines)
- **Notes**: none. Hinges on mathlib `Complex.norm_mul_exp_arg_mul_I`.

### `def mixedCubeEquiv`
- **Type**: `Fin (Module.finrank ℚ K - 1) ≃ Fin (Fintype.card (InfinitePlace K) - 1) ⊕ {w : InfinitePlace K // IsComplex w}` (noncomputable)
- **What**: Splits the `d−1` cube coordinates into `r−1` modulus coordinates and `r₂` phase coordinates (one per complex place); the cardinalities match.
- **How**: `Fintype.equivOfCardEq`; card equality from `card_eq_nrRealPlaces_add_nrComplexPlaces`, `card_add_two_mul_card_eq_rank` (i.e. `r₁ + 2r₂ = d`), `Fintype.card_pos` (`r ≥ 1`), closed by `lia`.
- **Hypotheses**: K a number field.
- **Uses from project**: `[]` (mathlib `nrRealPlaces`, `nrComplexPlaces`, `card_eq_nrRealPlaces_add_nrComplexPlaces`, `card_add_two_mul_card_eq_rank`)
- **Used by**: `liftToMixed`, `mem_iUnion_image_liftToMixed_of_eq`
- **Visibility**: public (noncomputable)
- **Lines**: 438–454 (proof ~9 lines)
- **Notes**: none.

### `def liftToMixed`
- **Type**: `(ψ : (Fin (Fintype.card (InfinitePlace K) - 1) → ℝ) → realSpace K) (ε : {w // IsReal w} → Bool) (c : Fin (Module.finrank ℚ K - 1) → ℝ) : mixedSpace K` (noncomputable)
- **What**: Lifts a `realSpace`-valued cover map `ψ` to a `mixedSpace`-valued map: real places get `± ψ(...)` (sign from `ε`), complex places get `ψ(...) · exp((2πθ_w − π)i)`; the first `r−1` cube coordinates feed `ψ`, the last `r₂` are the complex phases.
- **How**: Definition: a `Prod` of the real-coordinate function and complex-coordinate function, using `mixedCubeEquiv.symm` to read the modulus/phase slots (no proof).
- **Hypotheses**: none beyond K a number field.
- **Uses from project**: `mixedCubeEquiv`
- **Used by**: `lipschitzWith_liftToMixed`, `mem_iUnion_image_liftToMixed_of_eq`, `frontier_normLeOne_subset_iUnion_image_liftToMixed_aux`, `normLeOne_frontier_lipschitz_cover_mixedSpace`
- **Visibility**: public (noncomputable)
- **Lines**: 456–471 (def ~6 lines)
- **Notes**: none.

### `theorem lipschitzWith_liftToMixed`
- **Type**: `{ψ : ...→ realSpace K} {M₀ : ℝ≥0} {B : ℝ} (hψ : LipschitzWith M₀ ψ) (hB : ∀ c, ‖ψ c‖ ≤ B) (ε : {w // IsReal w} → Bool) : LipschitzWith (M₀ + (B * (2 * Real.pi)).toNNReal) (liftToMixed K ψ ε)`
- **What**: If `ψ` is `M₀`-Lipschitz and bounded by `B`, its lift `liftToMixed K ψ ε` is globally Lipschitz with constant `M₀ + (B·2π).toNNReal`.
- **How**: `LipschitzWith.of_dist_le_mul`; modulus bound `dist yc yd ≤ M₀ dist c d` from `hψ` + `dist_pi`; split on `Prod.dist_eq`/`max_le`; real coords isometric to `ψ`-coords (sign cancels via `abs_mul`); complex coords bounded by `dist_mul_exp_phase_le` then a `calc` collecting `B·2π` (phase) and `M₀` (modulus).
- **Hypotheses**: `ψ` is `M₀`-Lipschitz; `ψ` uniformly bounded by `B` (so `B ≥ 0`); sign pattern `ε`.
- **Uses from project**: `dist_mul_exp_phase_le`, `liftToMixed`, `mixedCubeEquiv` (via `liftToMixed`)
- **Used by**: `normLeOne_frontier_lipschitz_cover_mixedSpace`
- **Visibility**: public
- **Lines**: 473–524 (proof ~42 lines). `open scoped Classical`.
- **Notes**: **long (30–50)** (~42 lines). Hinges on `dist_mul_exp_phase_le` and mathlib `normAtPlace`/pi-dist API.

### `theorem exists_bound_frontierCoverFamily`
- **Type**: `∃ B : ℝ, ∀ s c, ‖frontierCoverFamily K s c‖ ≤ B`
- **What**: Every member of `frontierCoverFamily` is globally bounded by a single constant `B` (each face map is continuous, only ever evaluated on the compact cube via the clamp).
- **How**: Helper: a continuous `g` on `Icc 0 1` has bounded range (`IsCompact.image`, `isBounded.subset_closedBall`); apply to `faceMapZero`/each `faceMapSide` (continuity from `contDiff_*.continuous`); take `B` as the sup of `toNNReal`s.
- **Hypotheses**: K a number field.
- **Uses from project**: `clampUnit_mem_Icc`, `cubeRelabel`, `clampUnit`, `frontierCoverFamily`, `contDiff_faceMapZero`, `contDiff_faceMapSide`
- **Used by**: `normLeOne_frontier_lipschitz_cover_mixedSpace`
- **Visibility**: public
- **Lines**: 526–551 (proof ~21 lines)
- **Notes**: none (under 30). `classical`.

### `theorem mem_iUnion_image_liftToMixed_of_eq`
- **Type**: `{ψ : ...} {c' : Fin (Fintype.card (InfinitePlace K) - 1) → ℝ} (hc' : c' ∈ Icc 0 1) {x : mixedSpace K} (hx : normAtAllPlaces x = ψ c') : x ∈ ⋃ ε, liftToMixed K ψ ε '' Icc 0 1`
- **What**: Fibre covering — if a frontier-cover point `y = normAtAllPlaces x` equals `ψ c'`, then `x` lies in the cube image of `liftToMixed K ψ ε` for the sign pattern `ε` reading off the signs of `x`'s real coordinates.
- **How**: `choose` phases via `exists_phase_mem_Icc_mul_exp` on each complex coordinate; set `ε w = decide (0 ≤ x.1 w)` and assemble `c = Sum.elim c' θ ∘ mixedCubeEquiv`; check modulus equalities `ψ c' w = |x.1 w|`/`= ‖x.2 w‖` (via mathlib `normAtAllPlaces_apply`, `normAtPlace_apply_of_isReal/isComplex`); reconcile signs (`abs_of_nonneg`/`abs_of_neg`) and phases.
- **Hypotheses**: `c'` in the unit cube; `normAtAllPlaces x = ψ c'`.
- **Uses from project**: `exists_phase_mem_Icc_mul_exp`, `mixedCubeEquiv`, `liftToMixed`
- **Used by**: `frontier_normLeOne_subset_iUnion_image_liftToMixed_aux`
- **Visibility**: public
- **Lines**: 553–591 (proof ~28 lines)
- **Notes**: none (under 30). Hinges on mathlib `normAtPlace_apply_of_isReal/isComplex`, `normAtAllPlaces_apply`.

### `theorem frontier_normLeOne_subset_preimage`
- **Type**: `frontier (normLeOne K) ⊆ normAtAllPlaces ⁻¹' frontier (normAtAllPlaces '' normLeOne K)`
- **What**: The `mixedSpace` frontier of `normLeOne K` sits inside the `normAtAllPlaces`-preimage of the frontier of its `realSpace` image.
- **How**: `normLeOne K = normAtAllPlaces ⁻¹' (image)` via mathlib `normLeOne_eq_preimage_image`; then `Continuous.frontier_preimage_subset` with `continuous_normAtAllPlaces`.
- **Hypotheses**: K a number field.
- **Uses from project**: `[]` (mathlib `normLeOne_eq_preimage_image`, `continuous_normAtAllPlaces`, `Continuous.frontier_preimage_subset`)
- **Used by**: `frontier_normLeOne_subset_iUnion_image_liftToMixed_aux`
- **Visibility**: public
- **Lines**: 593–601 (proof 2 lines)
- **Notes**: none.

### `private theorem frontier_normLeOne_subset_iUnion_image_liftToMixed_aux`
- **Type**: `frontier (normLeOne K) ⊆ ⋃ p : (Unit ⊕ Unit ⊕ (...×Bool)) × ({w // IsReal w} → Bool), liftToMixed K (frontierCoverFamily K p.1) p.2 '' Icc 0 1`
- **What**: Auxiliary — the `mixedSpace` frontier is covered by the lifts of every `frontierCoverFamily` member over every sign pattern.
- **How**: Chain `frontier_normLeOne_subset_preimage` → preimage of `frontier_subset_frontierCoverFamily` (`Set.preimage_mono`, `preimage_iUnion`); for each `s` and `x` with `normAtAllPlaces x = frontierCoverFamily K s c'`, apply `mem_iUnion_image_liftToMixed_of_eq` to get the sign `ε`, repackage into the product index.
- **Hypotheses**: K a number field.
- **Uses from project**: `frontier_normLeOne_subset_preimage`, `frontier_subset_frontierCoverFamily`, `mem_iUnion_image_liftToMixed_of_eq`, `liftToMixed`, `frontierCoverFamily`
- **Used by**: `normLeOne_frontier_lipschitz_cover_mixedSpace`
- **Visibility**: private
- **Lines**: 603–617 (proof ~12 lines). `open scoped Classical`.
- **Notes**: none.

### `theorem normLeOne_frontier_lipschitz_cover_mixedSpace`
- **Type**: `∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Module.finrank ℚ K - 1) → ℝ) → mixedSpace K), (∀ j, LipschitzWith M (φ j)) ∧ frontier (normLeOne K) ⊆ ⋃ j, φ j '' Icc 0 1`
- **What**: **Main result (mixedSpace).** The frontier of `normLeOne K` in `mixedSpace K` is covered by finitely many `M`-Lipschitz images of `[0,1]^{d−1}`, `d = finrank ℚ K`.
- **How**: Lipschitz constant/bound from `exists_lipschitzWith_frontierCoverFamily` + `exists_bound_frontierCoverFamily`; the family `Φ p = liftToMixed K (frontierCoverFamily K p.1) p.2` is Lipschitz by `lipschitzWith_liftToMixed`; reindex over `Fintype.equivFin S`; cover from `frontier_normLeOne_subset_iUnion_image_liftToMixed_aux` via `iUnion_comp`.
- **Hypotheses**: K a number field.
- **Uses from project**: `exists_lipschitzWith_frontierCoverFamily`, `exists_bound_frontierCoverFamily`, `liftToMixed`, `frontierCoverFamily`, `lipschitzWith_liftToMixed`, `frontier_normLeOne_subset_iUnion_image_liftToMixed_aux`
- **Used by**: `normLeOne_frontier_lipschitz_cover_index`
- **Visibility**: public
- **Lines**: 619–641 (proof ~12 lines). `open scoped Classical`.
- **Notes**: none.

### `theorem normLeOne_frontier_lipschitz_cover_index`
- **Type**: `∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card (index K) - 1) → ℝ) → (index K → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧ frontier ((mixedEmbedding.stdBasis K).equivFunL '' (normLeOne K)) ⊆ ⋃ j, φ j '' Icc 0 1`
- **What**: **Main result (index coordinates).** The frontier of the `stdBasis`-coordinate image `Φ '' normLeOne K` (`Φ = (stdBasis K).equivFunL`) in `index K → ℝ` is covered by finitely many Lipschitz cube images — the exact `hlip` hypothesis of `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` with `ι = index K`.
- **How**: Take the `mixedSpace` cover, post-compose charts with the continuous-linear `Φ` (Lipschitz `Φ.lipschitz`, frontier-preserving as homeomorphism `Φ.toHomeomorph.image_frontier`); relabel cube dimension via `finCongr` using `Fintype.card (index K) − 1 = finrank ℚ K − 1` (from `Module.finrank_eq_card_basis (stdBasis K)`, `mixedEmbedding.finrank`); the `IsometryEquiv.piCongrLeft'` chart is isometric.
- **Hypotheses**: K a number field.
- **Uses from project**: `normLeOne_frontier_lipschitz_cover_mixedSpace`
- **Used by**: unused in file (terminal `index`-coordinate API)
- **Visibility**: public
- **Lines**: 643–671 (proof ~15 lines). `open scoped Classical`.
- **Notes**: none. Hinges on mathlib `mixedEmbedding.stdBasis`, `mixedEmbedding.finrank`, `index`.

---

## File Summary

**Total declarations: 31** documented.
- **defs: 7** — `clampUnit`, `faceMapZero`, `faceMapSide`, `cubeRelabel`, `frontierCoverFamily`, `mixedCubeEquiv` (noncomputable), `liftToMixed` (noncomputable).
- **lemmas/theorems: 24** — incl. 3 main results (`normLeOne_frontier_lipschitz_cover`, `..._mixedSpace`, `..._index`).
- **instances: 0**, structures/classes/abbrevs/inductives: 0.

**Key API (used by ≥3 in-file):**
- `clampUnit` (def) — used by ≥5.
- `faceMapZero`, `faceMapSide` (defs) — used by ≥6 each.
- `cubeRelabel` (def) — used by ≥5.
- `frontierCoverFamily` (def) — used by 6.
- `liftToMixed` (def) — used by 4.
- `exists_lipschitzWith_frontierCoverFamily` (thm) — used by 3.
- `contDiff_expMapBasis` (thm, 2), `contDiff_faceMapZero`/`contDiff_faceMapSide` (each used by 2), `lipschitzWith_one_of_edist_apply_le` (used by 2).

**Unused decls (no in-file consumer):** `normLeOne_frontier_lipschitz_cover` (terminal realSpace export), `normLeOne_frontier_lipschitz_cover_index` (terminal index export). Both are intentional public exports / API endpoints, not dead code.

**Decls with `sorry`:** none.

**Decls with `set_option`:** none. (Several use `open scoped Classical in` or a `classical` tactic; no `set_option`.)

**Proofs >50 lines (decompose-needed):** none.

**Proofs 30–50 lines (long):**
- `lipschitzWith_liftToMixed` — ~42 lines (lines 473–524). Candidate for `/decompose-proof` (split real-coord vs complex-coord bounds into helpers).
- `expMapBasis_mem_iUnion_faceMapSide` (private) — ~31 lines (lines 188–219).

(Borderline near 30, under: `frontier_subset_frontierCoverFamily` ~24, `image_boundary_subset_faces` ~25, `mem_iUnion_image_liftToMixed_of_eq` ~28, `exists_bound_frontierCoverFamily` ~21.)

**ForMathlib — names/statements that may already exist in mathlib (generality/dup check needed):**
1. `dist_mul_le_norm_mul_dist` — fully generic `NormedField` product-distance estimate; very plausibly already in mathlib or trivially derivable from `norm_add_le`/`dist_eq_norm`. **Check before PR.**
2. `lipschitzWith_one_of_edist_apply_le` (private) — generic "1-Lipschitz into finite pi from coordinatewise edist bound"; likely expressible via existing `LipschitzWith.pi` / `LipschitzWith.eval` API. **Check.**
3. `lipschitzWith_exp_ofReal_mul_I` — `t ↦ exp(t·i)` is `1`-Lipschitz; it's literally `circleMap 0 1` and mathlib has `lipschitzWith_circleMap`; a named form may already exist or be one line. **Check.**
4. `exists_phase_mem_Icc_mul_exp` — polar form `z = ‖z‖·exp((2πθ−π)i)`, `θ∈[0,1]`; the affine-normalized-arg packaging looks Chebotarev-specific (the `[0,1]` normalization), but the core is mathlib `Complex.norm_mul_exp_arg_mul_I`. Likely keep, but generality of the interval-normalization is worth a look.
5. `lipschitzWith_clampUnit` / `clampUnit` — coordinatewise `projIcc` retraction; mathlib has `LipschitzWith.projIcc`; a packaged pi-version `clampUnit` may be a reasonable small addition but check for an existing "project onto box / pi-Icc" def.

All of `faceMap*`, `frontierCoverFamily`, `liftToMixed`, `mixedCubeEquiv`, and the three `normLeOne_frontier_lipschitz_cover*` results are genuinely number-field/`expMapBasis`-specific (heavy use of `paramSet`, `compactSet`, `normAtAllPlaces`, `mixedEmbedding.stdBasis`) and are the real contribution.

**Naming note (ForMathlib):** `mixedCubeEquiv`, `liftToMixed`, `frontierCoverFamily`, `cubeRelabel`, `clampUnit`, `faceMapZero/Side` are unnamespaced-leaf names under `Chebotarev`; for a mathlib PR they'd want a `NumberField.mixedEmbedding`-style namespace and the project-flavored `frontierCoverFamily`/`faceMap*` names reconsidered for generality.
