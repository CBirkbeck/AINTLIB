# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/IntervalRing.lean`

1844 lines. Namespace `FarguesFontaine`, `noncomputable section`, `universe u`.
Imports: `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`, `«Adic spaces».FarguesFontaine.Groebner`.
Opens: `TopologicalRing ValuationSpectrum WittVector NNReal`.

Section variables (implicit in every signature below):
`(p : ℕ) [Fact p.Prime]`, `(F : Type u)` a perfectoid field of char `p` with a topological/uniform/nonarchimedean
structure, `(ϖ : PseudoUniformizer F)`.

Subject: Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, Definition 4.2 / Lemma 4.4 /
Corollary 4.5 — the interval rings `B^I` for `I = [s,r]`, realized (decision AD-7) as the closure of
the diagonal image of `Bloc` inside `hatK ρ₁ × hatK ρ₂`.

---

### `def BIProd`
- **Type**: `{ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) : Bloc p F ϖ →+* hatK p F hρ₁0 hρ₁1 × hatK p F hρ₂0 hρ₂1`
- **What**: The diagonal ring map sending `x ∈ Bloc` to the pair of its images in the two completed fraction fields attached to the interval endpoints `ρ₁, ρ₂`.
- **How**: `RingHom.prod` of the two endpoint maps `BlocToHatK`.
- **Hypotheses**: both radii in the open interval `(0,1)`.
- **Uses from project**: `Bloc`, `hatK`, `BlocToHatK`
- **Used by**: `BISub`, `BIProd_fst`, `BIProd_snd`, `BIProd_mem_BISub`, `wI_BIProd`, `BISub_fst_mem`, `BISub_snd_mem`, `exists_BIProd_wI_le`, `BIProd_injective`, `valued_BlocToHatK_le_wI`, `valued_BlocToHatK_sub_le_wI`, `neBot_comap_of_mem_BISub`, `eventually_pair_wI_le`, `tendsto_resI`, `resI_BIProd`, `map_add_comap_le`, `map_mul_comap_le`, `resI_add`, `resI_mul`, `resI_pair_mem`, `resIHom`, `wI_p_image`, `isUnit_p_BIProd`, `tendsto_wI_p_pow`, `wI_le_of_approx`, `valued_resI_le_wI`, `pImage`, `pInvImage`
- **Visibility**: public
- **Lines**: 55–58 (definition, 1 line of term)
- **Notes**: —

### `theorem BIProd_fst`
- **Type**: `… (x : Bloc p F ϖ) : (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x).1 = BlocToHatK p F ϖ hρ₁0 hρ₁1 x`
- **What**: The first coordinate of the diagonal image is the endpoint map at `ρ₁`.
- **How**: Definitional (`rfl`) — `RingHom.prod` projects to its factors.
- **Hypotheses**: none beyond the radius bounds.
- **Uses from project**: `BIProd`, `BlocToHatK`, `Bloc`
- **Used by**: `valued_pImage_fst`, `valued_pInvImage_fst`
- **Visibility**: public, `@[simp]`
- **Lines**: 60–63 (`rfl`)
- **Notes**: —

### `theorem BIProd_snd`
- **Type**: `… (x : Bloc p F ϖ) : (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 x).2 = BlocToHatK p F ϖ hρ₂0 hρ₂1 x`
- **What**: The second coordinate of the diagonal image is the endpoint map at `ρ₂`.
- **How**: Definitional (`rfl`).
- **Hypotheses**: none beyond the radius bounds.
- **Uses from project**: `BIProd`, `BlocToHatK`, `Bloc`
- **Used by**: `valued_pImage_snd`, `valued_pInvImage_snd`
- **Visibility**: public, `@[simp]`
- **Lines**: 65–68 (`rfl`)
- **Notes**: —

### `def BISub`
- **Type**: `… : Subring (hatK p F hρ₁0 hρ₁1 × hatK p F hρ₂0 hρ₂1)`
- **What**: The interval ring `B^I` (Kedlaya Def. 4.2): the topological closure of the range of the diagonal map inside the product of the two endpoint completions.
- **How**: `Subring.topologicalClosure` applied to `(BIProd …).range`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIProd`, `hatK`
- **Used by**: essentially every later result (≈80 sites), notably `isClosed_BISub`, `BIProd_mem_BISub`, `exists_BIProd_wI_le`, `isComplete_BISub`, `BIPlus`, `resI`, `resIHom`, `BIPlusIn`, `pIdeal`, `BIPairOfDefinition`, `isHuberRing_BISub`, `isTateRing_BISub`
- **Visibility**: public
- **Lines**: 72–75 (1-line term)
- **Notes**: this is the file's central object.

### `theorem isClosed_BISub`
- **Type**: `… : IsClosed (BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 : Set (hatK … × hatK …))`
- **What**: `B^I` is a closed subset of the product of the two completions.
- **How**: The carrier is definitionally `closure (range …)`, so `isClosed_closure` applies after an `rfl` rewrite.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BISub`, `BIProd`, `hatK`
- **Used by**: `isComplete_BISub`, `isClosed_BIPlus`
- **Visibility**: public
- **Lines**: 78–87 (6-line proof)
- **Notes**: —

### `theorem BIProd_mem_BISub`
- **Type**: `… (x : Bloc p F ϖ) : BIProd p F ϖ … x ∈ BISub p F ϖ …`
- **What**: The diagonal image of `Bloc` is contained in `B^I`.
- **How**: `Subring.le_topologicalClosure` applied to the range membership witness `⟨x, rfl⟩`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIProd`, `BISub`, `Bloc`
- **Used by**: `resI_BIProd`, `pInvImage_mem_BISub`, `pEltB_mem_BIPlusIn`
- **Visibility**: public
- **Lines**: 90–93 (1-line term)
- **Notes**: —

### `def wI`
- **Type**: `… (z : hatK p F hρ₁0 hρ₁1 × hatK p F hρ₂0 hρ₂1) : NNReal`
- **What**: The interval norm `λ_I = max{λ_{ρ₁}, λ_{ρ₂}}` (Kedlaya Def. 4.2), computed as the max of the two coordinatewise valuations.
- **How**: `max (Valued.v z.1) (Valued.v z.2)`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `hatK`
- **Used by**: ~90 downstream sites — the norm-theory lemmas (`wI_*`), `BIPlus`, `BIPlusIn`, the `resI` continuity chain, the Huber/Tate endgame
- **Visibility**: public
- **Lines**: 96–98 (1-line term)
- **Notes**: —

### `theorem wI_zero`
- **Type**: `… : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 0 = 0`
- **What**: The interval norm of `0` is `0`.
- **How**: Unfold `wI` and simplify the two valuations of `0`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `wI`
- **Used by**: `wI_eq_zero_iff`, `BIPlus`, `mem_BIPlusIn_iff`(via `BIPlusIn`)
- **Visibility**: public, `@[simp]`
- **Lines**: 100–105 (2 lines)
- **Notes**: —

### `theorem wI_one`
- **Type**: `… : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 1 = 1`
- **What**: The interval norm of `1` is `1`.
- **How**: Unfold `wI`; both coordinate valuations of `1` are `1`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `wI`
- **Used by**: `BIPlus` (one-membership), `wI_pow_le_one`, `BIPlusIn`
- **Visibility**: public, `@[simp]`
- **Lines**: 107–112 (2 lines)
- **Notes**: —

### `theorem wI_add_le`
- **Type**: `… (z w : …) : wI … (z + w) ≤ max (wI … z) (wI … w)`
- **What**: The interval norm is ultrametric (strong triangle inequality).
- **How**: `max_le` reduces to the two coordinates; each uses `Valuation.map_add` and `le_max_of_le_left/right`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `wI`, `hatK`
- **Used by**: `BIPlus` (closure under `+`), `eventually_pair_wI_le`, `wI_le_of_approx`, `BIPlusIn`
- **Visibility**: public
- **Lines**: 115–126 (8-line proof)
- **Notes**: —

### `theorem wI_mul_le`
- **Type**: `… (z w : …) : wI … (z * w) ≤ wI … z * wI … w`
- **What**: The interval norm is submultiplicative (each coordinate valuation is in fact multiplicative).
- **How**: `max_le`, then `Valuation.map_mul` in each coordinate and `mul_le_mul` against the max bounds.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `wI`, `hatK`
- **Used by**: `BIPlus`, `wI_pow_le_one`, `wI_p_pow_mul_le`, `BIPlusIn`
- **Visibility**: public
- **Lines**: 129–137 (5-line proof)
- **Notes**: —

### `theorem wI_neg`
- **Type**: `… (z : …) : wI … (-z) = wI … z`
- **What**: The interval norm is invariant under negation.
- **How**: Coordinatewise `Valuation.map_neg` on `(-z).1 = -z.1` and `(-z).2 = -z.2`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `wI`, `hatK`
- **Used by**: `exists_BI_series_limit`, `BIPlus`, `eventually_pair_wI_le`, `BIPlusIn`
- **Visibility**: public, `@[simp]`
- **Lines**: 139–149 (6-line proof)
- **Notes**: —

### `theorem wI_eq_zero_iff`
- **Type**: `… (z : …) : wI … z = 0 ↔ z = 0`
- **What**: The interval norm is a genuine norm: it vanishes exactly at `0`.
- **How**: Forward: the max being `0` forces each `Valued.v zᵢ = 0` by `le_max_left/right`, then `Valuation.zero_iff` and `Prod.ext`. Backward: `wI_zero`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `wI`, `wI_zero`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 152–167 (12-line proof)
- **Notes**: unused in file.

### `theorem wI_BIProd`
- **Type**: `… (x : Bloc p F ϖ) : wI … (BIProd … x) = max (Valued.v (BlocToHatK … hρ₁0 hρ₁1 x)) (Valued.v (BlocToHatK … hρ₂0 hρ₂1 x))`
- **What**: On the diagonal image of `Bloc`, the interval norm is the max of the two Gauss values.
- **How**: Definitional (`rfl`).
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `wI`, `BIProd`, `BlocToHatK`, `Bloc`
- **Used by**: `valued_BlocToHatK_le_wI`, `wI_p_image`
- **Visibility**: public
- **Lines**: 170–174 (`rfl`)
- **Notes**: —

### `theorem BISub_fst_mem`
- **Type**: `… (hz : z ∈ BISub p F ϖ …) : z.1 ∈ BrSub p F ϖ hρ₁0 hρ₁1`
- **What**: The first coordinate of an element of the interval ring lies in the endpoint ring `B^{ρ₁}`.
- **How**: `image_closure_subset_closure_image continuous_fst` pushes the closure through `Prod.fst`, then `closure_mono` against the inclusion of `Prod.fst '' range(BIProd)` into `range(BlocToHatK)`.
- **Hypotheses**: `z ∈ BISub`; radii in `(0,1)`.
- **Uses from project**: `BISub`, `BIProd`, `BrSub`, `BlocToHatK`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 177–197 (16-line proof)
- **Notes**: unused in file; exported API tying `B^I` to the one-radius rings.

### `theorem BISub_snd_mem`
- **Type**: `… (hz : z ∈ BISub p F ϖ …) : z.2 ∈ BrSub p F ϖ hρ₂0 hρ₂1`
- **What**: The second coordinate of an element of the interval ring lies in the endpoint ring `B^{ρ₂}`.
- **How**: Same argument as `BISub_fst_mem` with `continuous_snd` and `image_closure_subset_closure_image`.
- **Hypotheses**: `z ∈ BISub`; radii in `(0,1)`.
- **Uses from project**: `BISub`, `BIProd`, `BrSub`, `BlocToHatK`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 200–217 (13-line proof)
- **Notes**: unused in file.

### `theorem valued_ball_mem_nhds`
- **Type**: `… (z : hatK p F hρ0 hρ1) {ε : NNReal} (hε : 0 < ε) : {w | Valued.v (w - z) ≤ ε} ∈ nhds z`
- **What**: In a completed endpoint field, closed valuation balls centred at any point are neighbourhoods of that point.
- **How**: Translate by `z`: `w ↦ w - z` is continuous at `z` with value `0`, and `valued_ball_mem_nhds_zero` gives the ball at the origin; pull back along `ContinuousAt`.
- **Hypotheses**: `0 < ε`; `ρ ∈ (0,1)`.
- **Uses from project**: `hatK`, `valued_ball_mem_nhds_zero`
- **Used by**: `exists_BIProd_wI_le`, `eventually_pair_wI_le`, `wI_ball_mem_nhds`
- **Visibility**: public
- **Lines**: 220–229 (7-line proof)
- **Notes**: —

### `theorem exists_BIProd_wI_le`
- **Type**: `… (hz : z ∈ BISub …) {ε : NNReal} (hε : 0 < ε) : ∃ x : Bloc p F ϖ, wI … (BIProd … x - z) ≤ ε`
- **What**: Quantitative density: every element of `B^I` is `wI`-approximated to within `ε` by the image of an element of `Bloc`.
- **How**: The `wI`-ball around `z` is a neighbourhood (intersection of the two coordinate balls from `valued_ball_mem_nhds`, pulled back by `continuous_fst`/`continuous_snd`), so `mem_closure_iff_nhds` produces a range point inside it.
- **Hypotheses**: `z ∈ BISub`, `0 < ε`.
- **Uses from project**: `BISub`, `BIProd`, `wI`, `valued_ball_mem_nhds`, `Bloc`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 233–256 (20-line proof)
- **Notes**: unused in file; the file's other density arguments go through `eventually_pair_wI_le` instead.

### `theorem gaussTerm_rpow_interpolate`
- **Type**: `{ρ₁ ρ₂ : NNReal} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x : Ainf p F) (n : ℕ) : gaussTerm p F (ρ₁ ^ θ * ρ₂ ^ (1-θ)) x n = (gaussTerm p F ρ₁ x n) ^ θ * (gaussTerm p F ρ₂ x n) ^ (1-θ)`
- **What**: Three circles, termwise (Kedlaya Lemma 4.4): the `n`-th Gauss term at the geometrically interpolated radius `ρ₁^θ ρ₂^{1-θ}` equals the corresponding interpolation of the endpoint terms — an exact equality, not just a bound.
- **How**: Unfold `gaussTerm` and split on whether the Teichmüller coefficient's `perfectoidValuation` is `0`; in the nonzero case use `NNReal.rpow_add` to write `v = v^θ · v^{1-θ}` and `NNReal.rpow_natCast`/`rpow_mul` to interpolate `ρ^n`, then `ring`.
- **Hypotheses**: `0 ≤ θ ≤ 1`.
- **Uses from project**: `gaussTerm`, `Ainf`, `perfectoidValuation`, `teichCoeff`, `OF`
- **Used by**: `gaussValue_rpow_interpolate`
- **Visibility**: public
- **Lines**: 258–295 (33-line proof)
- **Notes**: >30 lines; heavy `NNReal.rpow` bookkeeping with a `calc` finish.

### `theorem gaussValue_rpow_interpolate`
- **Type**: `(hρ₁1 : ρ₁ ≤ 1) (hρ₂1 : ρ₂ ≤ 1) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x : Ainf p F) : gaussValue p F (ρ₁ ^ θ * ρ₂ ^ (1-θ)) x ≤ (gaussValue p F ρ₁ x) ^ θ * (gaussValue p F ρ₂ x) ^ (1-θ)`
- **What**: Three circles (Kedlaya Lemma 4.4): the Gauss value (a supremum of terms) at an interpolated radius is bounded by the interpolated product of the endpoint Gauss values.
- **How**: `ciSup_le` reduces to a single term; apply `gaussTerm_rpow_interpolate` and then bound each factor by `gaussTerm_le_gaussValue` under `NNReal.rpow_le_rpow`.
- **Hypotheses**: `ρ₁, ρ₂ ≤ 1`, `0 ≤ θ ≤ 1` (the `≤ 1` bounds make the interpolated radius `≤ 1`, needed for the sup to be well-behaved).
- **Uses from project**: `gaussValue`, `gaussTerm_rpow_interpolate`, `gaussTerm_le_gaussValue`, `Ainf`
- **Used by**: `wLoc_rpow_interpolate`
- **Visibility**: public
- **Lines**: 297–316 (14-line proof)
- **Notes**: —

### `theorem rpow_interpolate_lt_one`
- **Type**: `(hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : 0 < ρ₁ ^ θ * ρ₂ ^ (1-θ) ∧ ρ₁ ^ θ * ρ₂ ^ (1-θ) < 1`
- **What**: The geometric interpolation of two admissible radii is again an admissible radius: it lies strictly between `0` and `1`.
- **How**: Positivity from `NNReal.rpow_pos`; for `< 1`, split on `θ = 0` (giving `ρ₂`) versus `θ > 0` (`NNReal.rpow_lt_rpow` gives `ρ₁^θ < 1`, and `ρ₂^{1-θ} ≤ 1`).
- **Hypotheses**: both radii in `(0,1)`, `0 ≤ θ ≤ 1`.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 318–336 (15-line proof)
- **Notes**: unused in file; the admissibility side-conditions are supplied by hand as `hmid0/hmid1` at the call sites.

### `theorem wLoc_rpow_interpolate`
- **Type**: `{θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hmid0 : 0 < ρ₁^θ * ρ₂^(1-θ)) (hmid1 : ρ₁^θ * ρ₂^(1-θ) < 1) (x : Bloc p F ϖ) : wLoc p F ϖ hmid0 hmid1 x ≤ (wLoc p F ϖ hρ₁0 hρ₁1 x) ^ θ * (wLoc p F ϖ hρ₂0 hρ₂1 x) ^ (1-θ)`
- **What**: Three circles on the localization `Bloc` (Kedlaya Lemma 4.4): the extended Gauss valuation at an interpolated radius is bounded by the interpolation of the endpoint valuations.
- **How**: Write `x = a/y` with `y = (p·[ϖ])^k` via `IsLocalization.surj`; the denominator's Gauss value is `(σ·c)^k` (using `gaussValue_p_teichPi` and `map_pow` of `gaussVal`), which interpolates *exactly*; then cancel it and apply `gaussValue_rpow_interpolate` to the numerator `a`.
- **Hypotheses**: `0 ≤ θ ≤ 1`; the interpolated radius admissible; all four endpoint radius bounds.
- **Uses from project**: `wLoc`, `Bloc`, `Ainf`, `teichPi`, `gaussValue`, `gaussVal`, `gaussValue_p_teichPi`, `gaussValue_rpow_interpolate`, `wLoc_algebraMap`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `OF`
- **Used by**: `wLoc_le_max_of_interpolate`
- **Visibility**: public
- **Lines**: 338–404 (59-line proof)
- **Notes**: >30 lines; the file's longest analytic argument, structured as `hden`/`hval`/`hdenint` + a four-step `calc`.

### `theorem wLoc_le_max_of_interpolate`
- **Type**: `… (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hmid0 …) (hmid1 …) (x : Bloc p F ϖ) : wLoc p F ϖ hmid0 hmid1 x ≤ max (wLoc p F ϖ hρ₁0 hρ₁1 x) (wLoc p F ϖ hρ₂0 hρ₂1 x)`
- **What**: Kedlaya Corollary 4.5 in usable form: the interval norm (the max over the two endpoints) dominates the valuation at every intermediate radius.
- **How**: Chain `wLoc_rpow_interpolate` with the elementary bound `M^θ · M^{1-θ} = M` for `M` the max, obtained from `NNReal.rpow_add` (with a separate `M = 0` branch).
- **Hypotheses**: `0 ≤ θ ≤ 1`; the interpolated radius admissible.
- **Uses from project**: `wLoc`, `wLoc_rpow_interpolate`, `Bloc`
- **Used by**: `valued_BlocToHatK_le_wI` (line 656)
- **Visibility**: public
- **Lines**: 406–428 (16-line proof)
- **Notes**: —

### `theorem isComplete_BISub`
- **Type**: `… : IsComplete (BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 : Set (hatK … × hatK …))`
- **What**: `B^I` is complete — it is a closed subset of the (complete) product of two complete valued fields.
- **How**: `IsClosed.isComplete` applied to `isClosed_BISub`.
- **Hypotheses**: radii in `(0,1)`; completeness of the ambient `hatK` factors.
- **Uses from project**: `BISub`, `isClosed_BISub`, `hatK`
- **Used by**: `exists_BI_series_limit`
- **Visibility**: public
- **Lines**: 430–435 (1-line term)
- **Notes**: —

### `theorem cauchySeq_of_wI_le`
- **Type**: `(s : ℕ → hatK … × hatK …) (h : ∀ ε > 0, ∃ N₀, ∀ m n ≥ N₀, wI … (s m - s n) ≤ ε) : CauchySeq s`
- **What**: A `wI`-Cauchy criterion: uniform smallness of `wI (s m - s n)` implies the sequence is Cauchy in the product uniformity.
- **How**: Each coordinate is Cauchy by `cauchySeq_of_valued_le` (bounding the coordinate valuation by the max), then `CauchySeq.prodMk`.
- **Hypotheses**: the `ε`-`N₀` estimate; radii in `(0,1)`.
- **Uses from project**: `wI`, `hatK`, `cauchySeq_of_valued_le`
- **Used by**: `exists_BI_series_limit`
- **Visibility**: public
- **Lines**: 437–454 (12-line proof)
- **Notes**: —

### `theorem exists_BI_series_limit`
- **Type**: `(hu : ∀ l, u l ∈ BISub …) {C : ℕ → NNReal} (hC : ∀ l, wI … (u l) ≤ C l) (hC0 : Tendsto C atTop (nhds 0)) : ∃ S ∈ BISub …, Tendsto (fun n => ∑ l ∈ Finset.range n, u l) atTop (nhds S)`
- **What**: Series convergence in `B^I`: if the terms lie in `B^I` and their interval norms are dominated by a null sequence, the partial sums converge to an element of `B^I`.
- **How**: Partial sums lie in `B^I` by `Subring.sum_mem`; the tail difference is an `Ico`-sum bounded via `Valuation.map_sum_le` in each coordinate, giving Cauchy through `cauchySeq_of_wI_le`; conclude with `cauchySeq_tendsto_of_isComplete` and `isComplete_BISub`.
- **Hypotheses**: termwise membership, a dominating null sequence `C`.
- **Uses from project**: `BISub`, `wI`, `wI_neg`, `cauchySeq_of_wI_le`, `isComplete_BISub`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 456–508 (42-line proof)
- **Notes**: >30 lines; unused in file (exported for downstream Gröbner/Noetherian arguments).

### `theorem wLoc_ne_zero`
- **Type**: `{ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {x : Bloc p F ϖ} (hx : x ≠ 0) : wLoc p F ϖ hρ0 hρ1 x ≠ 0`
- **What**: The extended Gauss valuation on the localization `Bloc` is nonzero on nonzero elements — i.e. it is a genuine valuation with trivial kernel.
- **How**: Write `x·y = a` with `y ∈ powers (p·[ϖ])` via `IsLocalization.surj`; `wLoc x = 0` forces `gaussValue ρ a = 0`, hence `a = 0` by `gaussValue_pos_of_ne_zero`; since `y`'s image is a unit (`isUnit_p_teichPi_image`), `x = 0`, contradiction.
- **Hypotheses**: `x ≠ 0`; `ρ ∈ (0,1)`.
- **Uses from project**: `wLoc`, `Bloc`, `Ainf`, `teichPi`, `gaussValue`, `wLoc_algebraMap`, `gaussValue_pos_of_ne_zero`, `isUnit_p_teichPi_image`
- **Used by**: `BlocToHatK_injective`
- **Visibility**: public
- **Lines**: 510–537 (25-line proof)
- **Notes**: —

### `theorem valued_BlocToHatK`
- **Type**: `{ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} (x : Bloc p F ϖ) : Valued.v (BlocToHatK p F ϖ hρ0 hρ1 x) = wLoc p F ϖ hρ0 hρ1 x`
- **What**: The valuation of the completed field `hatK ρ` restricts along the endpoint map to the extended Gauss valuation `wLoc` on `Bloc`.
- **How**: Both sides satisfy the same equation after clearing the localization denominator `y`: `IsLocalization.lift_eq` identifies `BlocToHatK ∘ algebraMap` with `toHatK`, `valued_toHatK` computes the numerator/denominator values, and `mul_right_cancel₀` (with `gaussValue ρ y ≠ 0` from `gaussValue_p_teichPi_ne_zero`) finishes.
- **Hypotheses**: `ρ ∈ (0,1)`.
- **Uses from project**: `BlocToHatK`, `wLoc`, `Bloc`, `Ainf`, `teichPi`, `gaussValue`, `gaussVal`, `toHatK`, `valued_toHatK`, `wLoc_algebraMap`, `gaussValue_p_teichPi_ne_zero`
- **Used by**: `BlocToHatK_injective`, `valued_BlocToHatK_le_wI`, `wI_p_image`, `valued_pImage_fst`, `valued_pImage_snd`, `valued_pInvImage_fst`, `valued_pInvImage_snd` (7 sites)
- **Visibility**: public
- **Lines**: 539–570 (28-line proof)
- **Notes**: key API — used by 3+ consumers.

### `theorem BlocToHatK_injective`
- **Type**: `{ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} : Function.Injective (BlocToHatK p F ϖ hρ0 hρ1)`
- **What**: The endpoint map `Bloc → hatK ρ` is injective (the engine behind Kedlaya Corollary 4.6).
- **How**: `injective_iff_map_eq_zero`; if `x ≠ 0` mapped to `0` then `valued_BlocToHatK` would force `wLoc x = 0`, contradicting `wLoc_ne_zero`.
- **Hypotheses**: `ρ ∈ (0,1)`.
- **Uses from project**: `BlocToHatK`, `valued_BlocToHatK`, `wLoc_ne_zero`
- **Used by**: `BIProd_injective`
- **Visibility**: public
- **Lines**: 572–579 (5-line proof)
- **Notes**: —

### `theorem BIProd_injective`
- **Type**: `… : Function.Injective (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: The diagonal map into the product of the two completions is injective.
- **How**: Injectivity of the first component already suffices: apply `BlocToHatK_injective` to `congrArg Prod.fst`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIProd`, `BlocToHatK_injective`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 581–586 (2-line proof)
- **Notes**: unused in file.

### `def BIPlus`
- **Type**: `… : Subring (hatK p F hρ₁0 hρ₁1 × hatK p F hρ₂0 hρ₂1)`
- **What**: The integral interval ring `B^{I,+}` (Kedlaya Def. 4.2): the elements of `B^I` whose interval norm is at most `1`.
- **How**: Subring structure built by hand — `zero_mem'`/`one_mem'` from `wI_zero`/`wI_one`, `add_mem'` from the ultrametric `wI_add_le`, `neg_mem'` from `wI_neg`, `mul_mem'` from `wI_mul_le` plus `1·1 = 1`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BISub`, `wI`, `wI_zero`, `wI_one`, `wI_add_le`, `wI_neg`, `wI_mul_le`, `hatK`
- **Used by**: `mem_BIPlus_iff`, `BIPlus_le_BISub`, `isClosed_BIPlus`, `isComplete_BIPlus`
- **Visibility**: public
- **Lines**: 588–614 (25-line structure instance)
- **Notes**: five field proofs inline.

### `theorem mem_BIPlus_iff`
- **Type**: `… : z ∈ BIPlus p F ϖ … ↔ z ∈ BISub p F ϖ … ∧ wI … z ≤ 1`
- **What**: Membership in `B^{I,+}` is exactly membership in `B^I` together with the norm bound.
- **How**: `Iff.rfl` — the carrier was defined by that conjunction.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIPlus`, `BISub`, `wI`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 616–622 (`Iff.rfl`)
- **Notes**: unused in file.

### `theorem BIPlus_le_BISub`
- **Type**: `… : BIPlus p F ϖ … ≤ BISub p F ϖ …`
- **What**: `B^{I,+}` is a subring of `B^I`.
- **How**: Project the first conjunct of membership.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIPlus`, `BISub`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 624–628 (1-line term)
- **Notes**: unused in file.

### `theorem wI_pow_le_one`
- **Type**: `(hz : wI … z ≤ 1) (n : ℕ) : wI … (z ^ n) ≤ 1`
- **What**: Power-boundedness: elements of interval norm `≤ 1` have all powers of norm `≤ 1`.
- **How**: Induction on `n`, base from `wI_one`, step from `wI_mul_le` and `1·1 = 1`.
- **Hypotheses**: `wI z ≤ 1`.
- **Uses from project**: `wI`, `wI_one`, `wI_mul_le`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 630–644 (9-line proof)
- **Notes**: unused in file.

### `theorem valued_BlocToHatK_le_wI`
- **Type**: `(hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hmid0 …) (hmid1 …) (x : Bloc p F ϖ) : Valued.v (BlocToHatK p F ϖ hmid0 hmid1 x) ≤ wI … (BIProd … x)`
- **What**: Kedlaya Corollary 4.5 in the form the restriction maps consume: at any interpolated radius, the endpoint value of a `Bloc`-element is bounded by its interval norm.
- **How**: Rewrite all three valuations into `wLoc` via `valued_BlocToHatK` and `wI_BIProd`, then apply `wLoc_le_max_of_interpolate`.
- **Hypotheses**: `0 ≤ θ ≤ 1`; interpolated radius admissible.
- **Uses from project**: `BlocToHatK`, `BIProd`, `wI`, `valued_BlocToHatK`, `wI_BIProd`, `wLoc_le_max_of_interpolate`, `Bloc`
- **Used by**: `valued_BlocToHatK_sub_le_wI`, `valued_resI_le_wI` (line 1260)
- **Visibility**: public
- **Lines**: 646–657 (3-line proof)
- **Notes**: —

### `theorem valued_BlocToHatK_sub_le_wI`
- **Type**: `… (x y : Bloc p F ϖ) : Valued.v (BlocToHatK … x - BlocToHatK … y) ≤ wI … (BIProd … x - BIProd … y)`
- **What**: The intermediate endpoint map is `wI`-Lipschitz on differences, hence uniformly continuous for the interval uniformity — the estimate that lets `resI` be defined by a limit.
- **How**: Both differences are images of `x - y` (by `map_sub`), so the statement reduces to `valued_BlocToHatK_le_wI` at `x - y`.
- **Hypotheses**: `0 ≤ θ ≤ 1`; interpolated radius admissible.
- **Uses from project**: `BlocToHatK`, `BIProd`, `wI`, `valued_BlocToHatK_le_wI`, `Bloc`
- **Used by**: `tendsto_resI` (805), `map_add_comap_le` (858)
- **Visibility**: public
- **Lines**: 659–675 (8-line proof)
- **Notes**: —

### `theorem neBot_comap_of_mem_BISub`
- **Type**: `(hz : z ∈ BISub …) : (Filter.comap (BIProd …) (nhds z)).NeBot`
- **What**: For a point of `B^I`, the filter of `Bloc`-approximants (the pullback of the neighbourhood filter along the diagonal map) is nontrivial.
- **How**: `Filter.comap_neBot_iff` reduces to: every neighbourhood of `z` meets `range (BIProd …)`, which is exactly `mem_closure_iff_nhds` applied to the definition of `BISub` as a closure.
- **Hypotheses**: `z ∈ BISub`.
- **Uses from project**: `BISub`, `BIProd`, `hatK`
- **Used by**: `tendsto_resI`, `resI_BIProd`, `resI_add`, `resI_mul`, `resI_pair_mem`, `valued_resI_le_wI` (8 sites)
- **Visibility**: public
- **Lines**: 677–688 (6-line proof)
- **Notes**: key API — used by 3+ consumers; the nontriviality that makes the `lim`-based `resI` meaningful.

### `theorem eventually_pair_wI_le`
- **Type**: `(z : …) {ε : NNReal} (hε : 0 < ε) : ∀ᶠ q in (comap (BIProd …) (nhds z)) ×ˢ (comap (BIProd …) (nhds z)), wI … (BIProd … q.2 - BIProd … q.1) ≤ ε`
- **What**: Two approximants of the same point of the product are eventually `wI`-close: the approximant filter is Cauchy for the interval norm.
- **How**: Both coordinates are eventually within `ε/2` of `z` (using `valued_ball_mem_nhds` in each factor and `Filter.eventually_comap`), then the ultrametric `wI_add_le` together with `wI_neg` combines the two halves.
- **Hypotheses**: `0 < ε`.
- **Uses from project**: `BIProd`, `wI`, `wI_add_le`, `wI_neg`, `valued_ball_mem_nhds`, `hatK`
- **Used by**: `tendsto_resI` (797)
- **Visibility**: public
- **Lines**: 690–738 (41-line proof)
- **Notes**: >30 lines.

### `theorem exists_nnreal_lt_gamma`
- **Type**: `{ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} (γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass Valued.v))ˣ) : ∃ ε : NNReal, 0 < ε ∧ ∀ w, Valued.v w ≤ ε → (Valued.v).restrict w < γ.1`
- **What**: Every unit `γ` of the value group of `hatK ρ` dominates a positive `NNReal` valuation threshold — a translation device between `NNReal`-valued bounds and abstract value-group entourages.
- **How**: The embedding of `γ` into `NNReal` is positive (by injectivity of `ValueGroup₀.embedding_strictMono` and `map_zero`), so `exists_pow_lt_of_lt_one` gives `ρ^N` below it; take `ε = ρ^{N+1}` and transport the inequality back through `embedding_strictMono` and `Valuation.embedding_restrict`.
- **Hypotheses**: `ρ ∈ (0,1)`; `γ` a unit of the value group.
- **Uses from project**: `hatK`
- **Used by**: `tendsto_resI` (796), `wI_ball_mem_nhds` (851)
- **Visibility**: public
- **Lines**: 740–765 (20-line proof)
- **Notes**: bridges `NNReal` estimates and `Valued`'s uniformity basis.

### `def resI`
- **Type**: `… (hσ0 : 0 < σ) (hσ1 : σ < 1) (z : hatK p F hρ₁0 hρ₁1 × hatK p F hρ₂0 hρ₂1) : hatK p F hσ0 hσ1`
- **What**: The restriction map of `B^I` to an intermediate radius `σ`, defined as the `limUnder` of the endpoint maps `BlocToHatK … hσ0 hσ1` along the filter of `Bloc`-approximants of `z`.
- **How**: `Filter.limUnder (comap (BIProd …) (nhds z)) (BlocToHatK … hσ0 hσ1)`.
- **Hypotheses**: `σ ∈ (0,1)` (no relation to the interval is required for the *definition*; the lemmas add the interpolation hypotheses).
- **Uses from project**: `BIProd`, `BlocToHatK`, `hatK`, `Bloc`
- **Used by**: `tendsto_resI`, `resI_BIProd`, `resI_add`, `resI_mul`, `resI_pair_mem`, `resIHom`, `valued_resI_le_wI` (~24 sites)
- **Visibility**: public
- **Lines**: 767–773 (2-line term)
- **Notes**: key API — used by 3+ consumers; a `Classical.choice`-flavoured `limUnder`, so all content lives in `tendsto_resI`.

### `theorem tendsto_resI`
- **Type**: `(hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hmid0 …) (hmid1 …) (hz : z ∈ BISub …) : Tendsto (BlocToHatK p F ϖ hmid0 hmid1) (comap (BIProd …) (nhds z)) (nhds (resI … z))`
- **What**: Kedlaya Cor. 4.5 made into a map: for `z ∈ B^I` and an intermediate radius, the endpoint images of the approximants really do converge, and their limit is `resI z`.
- **How**: The pushed-forward approximant filter is Cauchy — `neBot_comap_of_mem_BISub` gives `NeBot`, `Valued.hasBasis_uniformity` plus `exists_nnreal_lt_gamma` turns an entourage into an `ε`, and `eventually_pair_wI_le` combined with `valued_BlocToHatK_sub_le_wI` supplies the estimate; completeness of `hatK` then produces a limit, which `Tendsto.limUnder_eq` identifies with `resI z`.
- **Hypotheses**: `z ∈ BISub`; `0 ≤ θ ≤ 1`; interpolated radius admissible.
- **Uses from project**: `resI`, `BIProd`, `BISub`, `BlocToHatK`, `Bloc`, `hatK`, `neBot_comap_of_mem_BISub`, `exists_nnreal_lt_gamma`, `eventually_pair_wI_le`, `valued_BlocToHatK_sub_le_wI`
- **Used by**: `resI_BIProd`, `resI_add`, `resI_mul`, `resI_pair_mem`, `valued_resI_le_wI` (10 sites)
- **Visibility**: public
- **Lines**: 775–811 (26-line proof)
- **Notes**: key API — used by 3+ consumers; the central convergence theorem of the `resI` block.

### `theorem wI_ball_mem_nhds`
- **Type**: `(z : …) {ε : NNReal} (hε : 0 < ε) : {w | wI … (w - z) ≤ ε} ∈ nhds z`
- **What**: Interval-norm balls in the product are neighbourhoods of their centre.
- **How**: Intersect the two coordinate balls (each a neighbourhood by `valued_ball_mem_nhds` pulled back along `continuous_fst`/`continuous_snd`) and bound the max.
- **Hypotheses**: `0 < ε`.
- **Uses from project**: `wI`, `valued_ball_mem_nhds`, `hatK`
- **Used by**: `resI_BIProd` (853), `wI_le_of_approx` (1245)
- **Visibility**: public
- **Lines**: 813–829 (11-line proof)
- **Notes**: —

### `theorem resI_BIProd`
- **Type**: `… (x : Bloc p F ϖ) : resI … hmid0 hmid1 (BIProd … x) = BlocToHatK p F ϖ hmid0 hmid1 x`
- **What**: The restriction map extends the endpoint map: on the diagonal image of `Bloc` it is just `BlocToHatK` at the intermediate radius.
- **How**: Two `Tendsto` statements with the same filter — `tendsto_resI` at `BIProd x`, and a direct convergence of `BlocToHatK … y` to `BlocToHatK … x` built from `wI_ball_mem_nhds`, `exists_nnreal_lt_gamma` and `valued_BlocToHatK_sub_le_wI` — are identified by `tendsto_nhds_unique`.
- **Hypotheses**: `0 ≤ θ ≤ 1`; interpolated radius admissible.
- **Uses from project**: `resI`, `BIProd`, `BISub`, `BlocToHatK`, `BIProd_mem_BISub`, `neBot_comap_of_mem_BISub`, `tendsto_resI`, `exists_nnreal_lt_gamma`, `wI_ball_mem_nhds`, `valued_BlocToHatK_sub_le_wI`, `Bloc`, `hatK`
- **Used by**: `resIHom` (map_one'/map_zero' fields, 4 sites)
- **Visibility**: public
- **Lines**: 831–860 (21-line proof)
- **Notes**: —

### `theorem map_add_comap_le`
- **Type**: `(z z' : …) : map (fun q => q.1 + q.2) ((comap (BIProd …) (nhds z)) ×ˢ (comap (BIProd …) (nhds z'))) ≤ comap (BIProd …) (nhds (z + z'))`
- **What**: Filter form of "approximants of a sum are sums of approximants": adding approximants of `z` and `z'` gives approximants of `z + z'`.
- **How**: `Filter.map_le_iff_le_comap`, then `Filter.tendsto_comap.comp tendsto_fst/snd` gives convergence in each slot, `Tendsto.add` combines them, and `map_add` of the ring hom `BIProd` rewrites the composite.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIProd`, `Bloc`, `hatK`
- **Used by**: `resI_add` (938)
- **Visibility**: public
- **Lines**: 862–890 (21-line proof)
- **Notes**: —

### `theorem map_mul_comap_le`
- **Type**: `(z z' : …) : map (fun q => q.1 * q.2) (… ×ˢ …) ≤ comap (BIProd …) (nhds (z * z'))`
- **What**: Filter form of "approximants of a product are products of approximants".
- **How**: Identical to `map_add_comap_le` with `Tendsto.mul` and `map_mul` in place of the additive versions.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIProd`, `Bloc`, `hatK`
- **Used by**: `resI_mul` (964)
- **Visibility**: public
- **Lines**: 892–920 (21-line proof)
- **Notes**: near-duplicate of `map_add_comap_le` (candidate for a shared `map_binop_comap_le`).

### `theorem resI_add`
- **Type**: `… (hz : z ∈ BISub …) (hz' : z' ∈ BISub …) : resI … (z + z') = resI … z + resI … z'`
- **What**: The restriction map is additive on `B^I`.
- **How**: `tendsto_resI` at `z`, `z'` and `z + z'`; the sum of the first two composed with the projections and the third composed with `map_add_comap_le` are two limits of the same filter, so `tendsto_nhds_unique` applies.
- **Hypotheses**: both points in `BISub`; `0 ≤ θ ≤ 1`; interpolated radius admissible.
- **Uses from project**: `resI`, `BISub`, `BlocToHatK`, `neBot_comap_of_mem_BISub`, `tendsto_resI`, `map_add_comap_le`, `Bloc`, `hatK`
- **Used by**: `resIHom` (`map_add'`)
- **Visibility**: public
- **Lines**: 922–946 (15-line proof)
- **Notes**: —

### `theorem resI_mul`
- **Type**: `… (hz : z ∈ BISub …) (hz' : z' ∈ BISub …) : resI … (z * z') = resI … z * resI … z'`
- **What**: The restriction map is multiplicative on `B^I`.
- **How**: Same double-limit argument as `resI_add`, using `map_mul_comap_le`, `Tendsto.mul` and `tendsto_nhds_unique`.
- **Hypotheses**: both points in `BISub`; `0 ≤ θ ≤ 1`; interpolated radius admissible.
- **Uses from project**: `resI`, `BISub`, `BlocToHatK`, `neBot_comap_of_mem_BISub`, `tendsto_resI`, `map_mul_comap_le`, `Bloc`, `hatK`
- **Used by**: `resIHom` (`map_mul'`)
- **Visibility**: public
- **Lines**: 948–972 (15-line proof)
- **Notes**: —

### `theorem resI_pair_mem`
- **Type**: `(hθ0 …) (hθ1 …) (hη0 …) (hη1 …) (hσ₁0 …) (hσ₁1 …) (hσ₂0 …) (hσ₂1 …) (hz : z ∈ BISub …) : (resI … hσ₁0 hσ₁1 z, resI … hσ₂0 hσ₂1 z) ∈ BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1`
- **What**: For two intermediate radii `σ₁, σ₂` inside `I`, the pair of restrictions of `z ∈ B^I` lies in the smaller interval ring `B^{I'}` — the statement that makes `resIHom` well-defined.
- **How**: `Filter.Tendsto.prodMk_nhds` of the two `tendsto_resI` limits gives convergence of the paired approximants, which lie in `range (BIProd …)` always; `mem_closure_of_tendsto` puts the limit in the closure, i.e. in `BISub`.
- **Hypotheses**: `z ∈ BISub`; both `θ, η ∈ [0,1]`; both interpolated radii admissible.
- **Uses from project**: `resI`, `BISub`, `BIProd`, `BlocToHatK`, `neBot_comap_of_mem_BISub`, `tendsto_resI`, `hatK`
- **Used by**: `resIHom` (`toFun`)
- **Visibility**: public
- **Lines**: 974–1000 (14-line proof)
- **Notes**: —

### `def resIHom`
- **Type**: `(hθ0 hθ1 hη0 hη1) (hσ₁0 hσ₁1 hσ₂0 hσ₂1) : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)`
- **What**: The restriction ring homomorphism `B^I → B^{I'}` (Kedlaya Corollary 4.6) for a subinterval `I' = [σ₁, σ₂] ⊆ I`, given by the pair of `resI`'s.
- **How**: `toFun` uses `resI_pair_mem` for well-definedness; the four ring-hom fields come from `resI_add`, `resI_mul` and — for `0`/`1` — from `resI_BIProd` applied to `BIProd 0`/`BIProd 1`, wrapped in `Subtype.ext` and `Prod.ext`.
- **Hypotheses**: both `θ, η ∈ [0,1]`; both interpolated endpoints admissible.
- **Uses from project**: `BISub`, `BIProd`, `resI`, `resI_pair_mem`, `resI_add`, `resI_mul`, `resI_BIProd`, `hatK`
- **Used by**: unused in file (headline export, cited in the module docstring)
- **Visibility**: public
- **Lines**: 1002–1056 (53-line structure instance)
- **Notes**: >30 lines; the file's headline construction. Unused in file but the point of the whole `resI` block.

### `theorem wI_pow`
- **Type**: `(z : …) (n : ℕ) : wI … (z ^ n) = (wI … z) ^ n`
- **What**: The interval norm is power-multiplicative — a max of two multiplicative valuations commutes with taking powers.
- **How**: `Valuation.map_pow` in each coordinate, then case split on which coordinate valuation is larger, using monotonicity `pow_le_pow_left₀` to see the max is preserved.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `wI`, `hatK`
- **Used by**: `wI_pow_eq_one_iff`, `tendsto_wI_p_pow`, `wI_p_pow_mul_le`
- **Visibility**: public
- **Lines**: 1058–1069 (7-line proof)
- **Notes**: key API — used by 3+ consumers.

### `theorem wI_pow_eq_one_iff`
- **Type**: `(z : …) {n : ℕ} (hn : n ≠ 0) : wI … (z ^ n) ≤ 1 ↔ wI … z ≤ 1`
- **What**: For `n ≠ 0`, a power has interval norm `≤ 1` iff the element does — the norm bound is detected by any nonzero power.
- **How**: Rewrite by `wI_pow`; forward by contradiction using `pow_lt_pow_left₀` on `1 < wI z`, backward by `pow_le_pow_left₀` and `one_pow`.
- **Hypotheses**: `n ≠ 0`.
- **Uses from project**: `wI`, `wI_pow`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1071–1091 (14-line proof)
- **Notes**: unused in file; uses the `push Not` tactic.

### `theorem gaussValue_p`
- **Type**: `{ρ : NNReal} (hρ1 : ρ ≤ 1) : gaussValue p F ρ ((p : Ainf p F)) = ρ`
- **What**: The Gauss value of the prime `p` (as an element of `A_inf`) at radius `ρ` is `ρ` itself.
- **How**: Write `p = p · 1` and apply `gaussValue_p_mul` together with `gaussValue_one`.
- **Hypotheses**: `ρ ≤ 1`.
- **Uses from project**: `gaussValue`, `Ainf`, `gaussValue_p_mul`, `gaussValue_one`
- **Used by**: `wI_p_image`, `valued_pImage_fst`, `valued_pImage_snd`
- **Visibility**: public
- **Lines**: 1093–1099 (4-line `calc`)
- **Notes**: key API — used by 3+ consumers.

### `theorem wI_p_image`
- **Type**: `… : wI … (BIProd … (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F))) = max ρ₁ ρ₂`
- **What**: The interval norm of the image of `p` is the larger of the two endpoint radii.
- **How**: Rewrite via `wI_BIProd`, `valued_BlocToHatK` and `wLoc_algebraMap` into two Gauss values, then apply `gaussValue_p` at each radius.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `wI`, `BIProd`, `wI_BIProd`, `valued_BlocToHatK`, `wLoc_algebraMap`, `gaussValue_p`, `Ainf`, `Bloc`
- **Used by**: `tendsto_wI_p_pow`, `wI_p_pow_mul_le`, `pEltB_mem_BIPlusIn` (1542)
- **Visibility**: public
- **Lines**: 1101–1108 (2-line proof)
- **Notes**: key API — used by 3+ consumers; this is what makes `max ρ₁ ρ₂ < 1` the topological nilpotence rate.

### `theorem isUnit_p_BIProd`
- **Type**: `… : IsUnit (BIProd … (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F)))`
- **What**: `p` is a unit in the interval ring (it is already inverted in `Bloc`).
- **How**: Push `isUnit_p_image` forward along the ring hom `BIProd`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIProd`, `isUnit_p_image`, `Ainf`, `Bloc`
- **Used by**: `exists_eq_p_pow_mul` (1308)
- **Visibility**: public
- **Lines**: 1110–1115 (1-line term)
- **Notes**: —

### `theorem tendsto_wI_p_pow`
- **Type**: `… : Tendsto (fun n : ℕ => wI … ((BIProd … (algebraMap … (p : Ainf p F))) ^ n)) atTop (nhds 0)`
- **What**: `p` is topologically nilpotent in the interval ring: the interval norms of its powers tend to `0`.
- **How**: `wI_pow` and `wI_p_image` compute the `n`-th norm as `(max ρ₁ ρ₂)^n`, and `max ρ₁ ρ₂ < 1`, so `tendsto_pow_atTop_nhds_zero_of_lt_one` applies.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `wI`, `BIProd`, `wI_pow`, `wI_p_image`, `Ainf`, `Bloc`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1117–1133 (9-line proof)
- **Notes**: unused in file; the Tate-ring property is instead derived through `pUnit`/`BIPairOfDefinition`.

### `theorem isClosed_valued_ball`
- **Type**: `{ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1} {c : NNReal} (hc : 0 < c) : IsClosed {w : hatK p F hρ0 hρ1 | Valued.v w ≤ c}`
- **What**: Closed valuation balls in a completed endpoint field are topologically closed.
- **How**: The ball is an additive subgroup (ultrametric `Valuation.map_add` gives `add_mem`); it is open since it is a neighbourhood of `0` (`valued_ball_mem_nhds_zero`) and `AddSubgroup.isOpen_of_mem_nhds`; open subgroups are closed by `AddSubgroup.isClosed_of_isOpen`.
- **Hypotheses**: `0 < c`.
- **Uses from project**: `hatK`, `valued_ball_mem_nhds_zero`
- **Used by**: `isClosed_wI_ball` (twice), `valued_resI_le_wI`
- **Visibility**: public
- **Lines**: 1135–1153 (16-line proof)
- **Notes**: key API — used by 3+ consumer sites.

### `theorem isClosed_wI_ball`
- **Type**: `{c : NNReal} (hc : 0 < c) : IsClosed {z | wI … z ≤ c}`
- **What**: Interval-norm balls in the product are closed.
- **How**: Prove the ball is the intersection of the two coordinate balls (via `le_max_left/right` and `max_le`), then `IsClosed.inter` of two preimages of `isClosed_valued_ball` under `continuous_fst`/`continuous_snd`.
- **Hypotheses**: `0 < c`.
- **Uses from project**: `wI`, `isClosed_valued_ball`, `hatK`
- **Used by**: `wI_le_of_approx`, `isClosed_BIPlus`
- **Visibility**: public
- **Lines**: 1155–1182 (24-line proof)
- **Notes**: —

### `theorem wI_le_of_approx`
- **Type**: `(hz : z ∈ BISub …) {c : NNReal} (hc : 0 < c) (hall : ∀ x : Bloc p F ϖ, wI … (BIProd … x) ≤ c) : wI … z ≤ c`
- **What**: Interval-norm bounds pass to limits: if every `Bloc`-image has norm `≤ c`, so does every element of `B^I`.
- **How**: `range (BIProd …)` is inside the ball, so `closure_mono` puts `z` in the ball's closure, which equals the ball by `isClosed_wI_ball`.
- **Hypotheses**: `z ∈ BISub`, `0 < c`, the uniform bound on `Bloc`-images.
- **Uses from project**: `BISub`, `BIProd`, `wI`, `isClosed_wI_ball`, `Bloc`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1184–1200 (8-line proof)
- **Notes**: unused in file.

### `theorem isClosed_BIPlus`
- **Type**: `… : IsClosed (BIPlus p F ϖ … : Set (hatK … × hatK …))`
- **What**: The integral interval ring `B^{I,+}` is closed in the product.
- **How**: Its carrier is definitionally `BISub ∩ {wI ≤ 1}`; both are closed (`isClosed_BISub`, `isClosed_wI_ball` at `c = 1`), so `IsClosed.inter` applies.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIPlus`, `BISub`, `wI`, `isClosed_BISub`, `isClosed_wI_ball`, `hatK`
- **Used by**: `isComplete_BIPlus`
- **Visibility**: public
- **Lines**: 1202–1213 (7-line proof)
- **Notes**: —

### `theorem isComplete_BIPlus`
- **Type**: `… : IsComplete (BIPlus p F ϖ … : Set (hatK … × hatK …))`
- **What**: `B^{I,+}` is complete.
- **How**: `IsClosed.isComplete` on `isClosed_BIPlus`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIPlus`, `isClosed_BIPlus`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1215–1220 (1-line term)
- **Notes**: unused in file.

### `theorem valued_resI_le_wI`
- **Type**: `(hθ0 hθ1 hmid0 hmid1) (hz : z ∈ BISub …) : Valued.v (resI … hmid0 hmid1 z) ≤ wI … z`
- **What**: The restriction map is norm-nonincreasing (Kedlaya Cor. 4.5 at the level of the completion): the value at an intermediate radius never exceeds the interval norm.
- **How**: For each `ε > 0` the approximants eventually satisfy `wI (BIProd x - z) ≤ ε`, so by the ultrametric `wI_add_le` their norms are `≤ max(wI z, ε)`, and `valued_BlocToHatK_le_wI` transfers this to the intermediate values; `isClosed_valued_ball.mem_of_tendsto` with `tendsto_resI` passes the bound to the limit, and `exists_between` removes the `ε` slack.
- **Hypotheses**: `z ∈ BISub`; `0 ≤ θ ≤ 1`; interpolated radius admissible.
- **Uses from project**: `resI`, `wI`, `BISub`, `BIProd`, `neBot_comap_of_mem_BISub`, `tendsto_resI`, `isClosed_valued_ball`, `wI_ball_mem_nhds`, `wI_add_le`, `valued_BlocToHatK_le_wI`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1222–1268 (38-line proof)
- **Notes**: >30 lines; unused in file (exported bound). Uses the `push Not` tactic.

### `def pImage`
- **Type**: `… : hatK p F hρ₁0 hρ₁1 × hatK p F hρ₂0 hρ₂1`
- **What**: The image of the prime `p` in the product, as a single element (rather than an application of `BIProd`).
- **How**: `BIProd … (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F))`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIProd`, `Ainf`, `Bloc`, `hatK`
- **Used by**: `valued_pImage_fst/snd`, `wI_p_pow_mul_le`, `exists_eq_p_pow_mul`, `p_pow_smul_ball_eq`, `pImage_mul_pInvImage`, `pEltB`, `coe_mul_pEltPlus_pow`, `mul_pEltPlus_pow_eq`, `mem_pIdeal_pow_iff`, `isOpen_coord_ball` (~30 sites)
- **Visibility**: public
- **Lines**: 1270–1274 (2-line term)
- **Notes**: key API — used by 3+ consumers.

### `theorem valued_pImage_fst`
- **Type**: `… : Valued.v (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).1 = ρ₁`
- **What**: The first coordinate of the image of `p` has valuation exactly `ρ₁`.
- **How**: Unfold through `BIProd_fst`, `valued_BlocToHatK` and `wLoc_algebraMap` to a Gauss value, then `gaussValue_p`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pImage`, `BIProd_fst`, `valued_BlocToHatK`, `wLoc_algebraMap`, `gaussValue_p`
- **Used by**: `exists_eq_p_pow_mul`, `p_pow_smul_ball_eq`, `isOpen_coord_ball`
- **Visibility**: public
- **Lines**: 1276–1281 (2-line proof)
- **Notes**: key API — used by 3+ consumers.

### `theorem valued_pImage_snd`
- **Type**: `… : Valued.v (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).2 = ρ₂`
- **What**: The second coordinate of the image of `p` has valuation exactly `ρ₂`.
- **How**: Same chain as `valued_pImage_fst` through `BIProd_snd` and `gaussValue_p` at `ρ₂`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pImage`, `BIProd_snd`, `valued_BlocToHatK`, `wLoc_algebraMap`, `gaussValue_p`
- **Used by**: `exists_eq_p_pow_mul`, `p_pow_smul_ball_eq`, `isOpen_coord_ball`
- **Visibility**: public
- **Lines**: 1283–1287 (2-line proof)
- **Notes**: key API — used by 3+ consumers; no docstring of its own (shares the one above).

### `theorem wI_p_pow_mul_le`
- **Type**: `(n : ℕ) (z : …) : wI … ((pImage …) ^ n * z) ≤ (max ρ₁ ρ₂) ^ n * wI … z`
- **What**: Scaling up: multiplying by `pⁿ` shrinks the interval norm by at least the factor `(max ρ₁ ρ₂)ⁿ` — one half of the adic sandwich.
- **How**: Submultiplicativity `wI_mul_le`, then compute `wI (pImage ^ n)` by `wI_pow` and `wI_p_image`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `wI`, `pImage`, `wI_mul_le`, `wI_pow`, `wI_p_image`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1289–1297 (3-line proof)
- **Notes**: unused in file (`pIdeal_pow_subset_ball` re-derives the estimate through the coordinates).

### `theorem exists_eq_p_pow_mul`
- **Type**: `(n : ℕ) (hz1 : Valued.v z.1 ≤ ρ₁ ^ n) (hz2 : Valued.v z.2 ≤ ρ₂ ^ n) : ∃ w, wI … w ≤ 1 ∧ z = (pImage …) ^ n * w`
- **What**: Scaling down: any element whose coordinates are bounded by `ρᵢⁿ` is `pⁿ` times an element of the unit ball — the converse half of the adic sandwich.
- **How**: `isUnit_p_BIProd` makes `pImage ^ n` a unit with inverse `W`; `valued_pImage_fst/snd` and `Valuation.map_pow` compute `v(W.i) = (ρᵢⁿ)⁻¹`, so `w = W · z` has both coordinate valuations `≤ 1` by `inv_mul_le_iff₀`, and `z = pImage^n · w` follows from `mul_assoc`.
- **Hypotheses**: the two coordinate bounds.
- **Uses from project**: `pImage`, `wI`, `isUnit_p_BIProd`, `valued_pImage_fst`, `valued_pImage_snd`, `hatK`
- **Used by**: `p_pow_smul_ball_eq` (1424)
- **Visibility**: public
- **Lines**: 1299–1350 (44-line proof)
- **Notes**: >30 lines.

### `theorem isOpen_valued_ball`
- **Type**: `{c : NNReal} (hc : 0 < c) : IsOpen {w : hatK p F hρ0 hρ1 | Valued.v w ≤ c}`
- **What**: Closed valuation balls in a completed endpoint field are also open (being additive subgroups containing a neighbourhood of `0`).
- **How**: Same `AddSubgroup` construction as `isClosed_valued_ball`, stopping at `AddSubgroup.isOpen_of_mem_nhds` with `valued_ball_mem_nhds_zero`.
- **Hypotheses**: `0 < c`.
- **Uses from project**: `hatK`, `valued_ball_mem_nhds_zero`
- **Used by**: `isOpen_wI_ball` (twice), `isOpen_coord_ball` (twice)
- **Visibility**: public
- **Lines**: 1352–1369 (14-line proof)
- **Notes**: key API — used by 3+ consumer sites; the `AddSubgroup` term duplicates `isClosed_valued_ball` (dedup candidate).

### `theorem isOpen_wI_ball`
- **Type**: `{c : NNReal} (hc : 0 < c) : IsOpen {z | wI … z ≤ c}`
- **What**: Interval-norm balls in the product are open.
- **How**: Same set decomposition as `isClosed_wI_ball` (intersection of two coordinate preimages), then `IsOpen.inter` of `isOpen_valued_ball` pullbacks.
- **Hypotheses**: `0 < c`.
- **Uses from project**: `wI`, `isOpen_valued_ball`, `hatK`
- **Used by**: `isOpen_BIPlusIn` (1496)
- **Visibility**: public
- **Lines**: 1371–1394 (21-line proof)
- **Notes**: near-duplicate of `isClosed_wI_ball` (dedup candidate).

### `theorem p_pow_smul_ball_eq`
- **Type**: `(n : ℕ) : {z | ∃ w, wI … w ≤ 1 ∧ z = (pImage …) ^ n * w} = {z | Valued.v z.1 ≤ ρ₁ ^ n ∧ Valued.v z.2 ≤ ρ₂ ^ n}`
- **What**: The set-level heart of the adic sandwich: `pⁿ` times the unit ball is exactly the two-coordinate ball of radii `ρ₁ⁿ, ρ₂ⁿ`.
- **How**: Forward by `Valuation.map_mul`/`map_pow` plus `valued_pImage_fst/snd`; backward is exactly `exists_eq_p_pow_mul`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `wI`, `pImage`, `valued_pImage_fst`, `valued_pImage_snd`, `exists_eq_p_pow_mul`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1396–1424 (20-line proof)
- **Notes**: unused in file; the adic endgame instead works with `pIdeal` powers directly.

### `def BIPlusIn`
- **Type**: `… : Subring ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: `B^{I,+}` viewed as a subring *of* `B^I` (rather than of the ambient product) — the ring of definition for the Huber structure.
- **How**: Carrier `{z | wI ↑z ≤ 1}`; the six subring fields come from `wI_zero`, `wI_one`, `wI_add_le`, `wI_neg`, `wI_mul_le` together with the `Subring` coercion lemmas (`ZeroMemClass.coe_zero`, `AddMemClass.coe_add`, …).
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BISub`, `wI`, `wI_zero`, `wI_one`, `wI_add_le`, `wI_neg`, `wI_mul_le`, `hatK`
- **Used by**: `mem_BIPlusIn_iff`, `isOpen_BIPlusIn`, `pEltB_mem_BIPlusIn`, `pEltPlus`, `pIdeal`, the whole adic endgame, `BIPairOfDefinition` (~31 sites)
- **Visibility**: public
- **Lines**: 1426–1475 (48-line structure instance)
- **Notes**: >30 lines; the `↥`-relative twin of `BIPlus` (dedup candidate — the two differ only in the ambient ring).

### `theorem mem_BIPlusIn_iff`
- **Type**: `{z : ↥(BISub …)} : z ∈ BIPlusIn p F ϖ … ↔ wI … (z : …) ≤ 1`
- **What**: Membership in the ring of definition is exactly the norm bound on the underlying pair.
- **How**: `Iff.rfl`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIPlusIn`, `BISub`, `wI`, `hatK`
- **Used by**: `isOpen_BIPlusIn`, `pEltB_mem_BIPlusIn`, `mem_pIdeal_pow_iff` (1612, 1615), `isOpen_coord_ball` (1662)
- **Visibility**: public
- **Lines**: 1477–1481 (`Iff.rfl`)
- **Notes**: key API — used by 3+ consumers; no docstring.

### `theorem isOpen_BIPlusIn`
- **Type**: `… : IsOpen (BIPlusIn p F ϖ … : Set ↥(BISub …))`
- **What**: The ring of definition is open in `B^I` — it is the unit ball of the interval norm.
- **How**: Rewrite the carrier as a preimage under `Subtype.val` using `mem_BIPlusIn_iff`, then pull back `isOpen_wI_ball` at `c = 1` along `continuous_subtype_val`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIPlusIn`, `BISub`, `wI`, `mem_BIPlusIn_iff`, `isOpen_wI_ball`, `hatK`
- **Used by**: `isHuberRing_BISub` (1813)
- **Visibility**: public
- **Lines**: 1483–1496 (9-line proof)
- **Notes**: —

### `def pInvImage`
- **Type**: `… : hatK p F hρ₁0 hρ₁1 × hatK p F hρ₂0 hρ₂1`
- **What**: The inverse of `p` in the interval ring, as an element of the product.
- **How**: `BIProd` applied to the inverse of the unit `(isUnit_p_image p F ϖ).unit`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIProd`, `isUnit_p_image`, `hatK`
- **Used by**: `pImage_mul_pInvImage`, `valued_pInvImage_fst/snd`, `pInvImage_mem_BISub`, `mem_pIdeal_pow_iff`, `isOpen_coord_ball`, `pUnit` (~16 sites)
- **Visibility**: public
- **Lines**: 1498–1501 (1-line term)
- **Notes**: key API — used by 3+ consumers.

### `theorem pImage_mul_pInvImage`
- **Type**: `… : pImage p F ϖ … * pInvImage p F ϖ … = 1`
- **What**: `pImage` and `pInvImage` are mutually inverse in the product ring.
- **How**: Both are `BIProd`-images, so `map_mul` reduces to `x · x⁻¹ = 1` in `Bloc`, supplied by `Units.mul_inv` and `IsUnit.unit_spec` for `isUnit_p_image`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pImage`, `pInvImage`, `isUnit_p_image`, `Ainf`, `Bloc`
- **Used by**: `isOpen_coord_ball` (1667), `pUnit` (1828, 1831)
- **Visibility**: public
- **Lines**: 1503–1512 (6-line proof)
- **Notes**: —

### `theorem valued_pInvImage_fst`
- **Type**: `… : Valued.v (pInvImage p F ϖ …).1 = ρ₁⁻¹`
- **What**: The first coordinate of `p⁻¹` has valuation `ρ₁⁻¹`.
- **How**: `BIProd_fst` and `valued_BlocToHatK` reduce to the project lemma `wLoc_p_inv`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pInvImage`, `BIProd_fst`, `valued_BlocToHatK`, `wLoc_p_inv`
- **Used by**: `mem_pIdeal_pow_iff` (1641)
- **Visibility**: public
- **Lines**: 1514–1518 (2-line proof)
- **Notes**: no docstring.

### `theorem valued_pInvImage_snd`
- **Type**: `… : Valued.v (pInvImage p F ϖ …).2 = ρ₂⁻¹`
- **What**: The second coordinate of `p⁻¹` has valuation `ρ₂⁻¹`.
- **How**: Same as `valued_pInvImage_fst` through `BIProd_snd` and `wLoc_p_inv` at `ρ₂`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pInvImage`, `BIProd_snd`, `valued_BlocToHatK`, `wLoc_p_inv`
- **Used by**: `mem_pIdeal_pow_iff` (1651)
- **Visibility**: public
- **Lines**: 1520–1524 (2-line proof)
- **Notes**: no docstring.

### `theorem pInvImage_mem_BISub`
- **Type**: `… : pInvImage p F ϖ … ∈ BISub p F ϖ …`
- **What**: `p⁻¹` lies in the interval ring.
- **How**: It is a `BIProd`-image, so `BIProd_mem_BISub` applies.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pInvImage`, `BISub`, `BIProd_mem_BISub`
- **Used by**: `mem_pIdeal_pow_iff` (1635), `pUnit` (1827)
- **Visibility**: public
- **Lines**: 1526–1529 (1-line term)
- **Notes**: no docstring.

### `def pEltB`
- **Type**: `… : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: The element `p` of the interval ring `B^I` (as a bundled subtype element).
- **How**: `⟨pImage …, BIProd_mem_BISub …⟩`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pImage`, `BISub`, `BIProd_mem_BISub`
- **Used by**: `pEltB_mem_BIPlusIn`, `pEltPlus`, `pUnit` (1826)
- **Visibility**: public
- **Lines**: 1532–1535 (1-line term)
- **Notes**: —

### `theorem pEltB_mem_BIPlusIn`
- **Type**: `… : pEltB p F ϖ … ∈ BIPlusIn p F ϖ …`
- **What**: `p` lies in the ring of definition, i.e. its interval norm is at most `1`.
- **How**: `mem_BIPlusIn_iff` reduces to `wI (pImage) ≤ 1`, which is `max ρ₁ ρ₂ ≤ 1` by `wI_p_image` and `hρᵢ1.le`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pEltB`, `BIPlusIn`, `mem_BIPlusIn_iff`, `wI`, `pImage`, `wI_p_image`
- **Used by**: `pEltPlus`
- **Visibility**: public
- **Lines**: 1537–1543 (4-line proof)
- **Notes**: no docstring.

### `def pEltPlus`
- **Type**: `… : ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: `p` as an element of the ring of definition `B^{I,+}`.
- **How**: `⟨pEltB …, pEltB_mem_BIPlusIn …⟩`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIPlusIn`, `pEltB`, `pEltB_mem_BIPlusIn`
- **Used by**: `pIdeal`, `pIdeal_fg`, `pIdeal_pow_eq_span`, `coe_mul_pEltPlus_pow`, `mul_pEltPlus_pow_eq`, `isTateRing_BISub` (1840)
- **Visibility**: public
- **Lines**: 1545–1548 (1-line term)
- **Notes**: key API — used by 3+ consumers.

### `def pIdeal`
- **Type**: `… : Ideal ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: The ideal of definition `(p) ⊆ B^{I,+}`.
- **How**: `Ideal.span {pEltPlus …}`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIPlusIn`, `pEltPlus`
- **Used by**: `pIdeal_fg`, `pIdeal_pow_eq_span`, `mem_pIdeal_pow_iff`, `isOpen_pIdeal_pow`, `pIdeal_pow_subset_ball`, `exists_pIdeal_pow_subset_of_ball`, `isAdic_pIdeal`, `BIPairOfDefinition` (11 sites)
- **Visibility**: public
- **Lines**: 1550–1553 (1-line term)
- **Notes**: key API — used by 3+ consumers.

### `theorem pIdeal_fg`
- **Type**: `… : (pIdeal p F ϖ …).FG`
- **What**: The ideal of definition is finitely generated (indeed principal).
- **How**: Exhibit the singleton `{pEltPlus …}` as generating set; `Finset.coe_singleton` matches it with the `Ideal.span`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pIdeal`, `pEltPlus`
- **Used by**: `BIPairOfDefinition` (1814)
- **Visibility**: public
- **Lines**: 1555–1558 (1-line term)
- **Notes**: no docstring.

### `theorem pIdeal_pow_eq_span`
- **Type**: `(n : ℕ) : (pIdeal p F ϖ …) ^ n = Ideal.span {pEltPlus p F ϖ … ^ n}`
- **What**: The `n`-th power of the principal ideal `(p)` is generated by `pⁿ`.
- **How**: `Ideal.span_singleton_pow`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pIdeal`, `pEltPlus`, `BIPlusIn`
- **Used by**: `mem_pIdeal_pow_iff` (1607)
- **Visibility**: public
- **Lines**: 1560–1566 (1-line term)
- **Notes**: —

### `theorem coe_mul_pEltPlus_pow`
- **Type**: `(n : ℕ) (b : ↥(BIPlusIn …)) : ((b * pEltPlus … ^ n : ↥(BIPlusIn …)) : hatK × hatK) = (b : hatK × hatK) * (pImage …) ^ n`
- **What**: Computes the ambient (product-level) value of a `B^{I,+}`-multiple of `pⁿ`, unwinding two layers of subtype coercion.
- **How**: `push_cast` then `rfl`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIPlusIn`, `BISub`, `pEltPlus`, `pImage`, `hatK`
- **Used by**: `mul_pEltPlus_pow_eq` (1593), `mem_pIdeal_pow_iff` (1616)
- **Visibility**: public
- **Lines**: 1568–1580 (2-line proof)
- **Notes**: —

### `theorem mul_pEltPlus_pow_eq`
- **Type**: `(n : ℕ) (w y : ↥(BIPlusIn …)) (h : (w : hatK × hatK) * (pImage …) ^ n = (y : hatK × hatK)) : w * pEltPlus … ^ n = y`
- **What**: Converse bookkeeping lemma: an ambient equation `w · pⁿ = y` at the level of the product lifts to the two-level subtype `B^{I,+}`.
- **How**: Two nested `Subtype.ext` applications, rewriting the coercion with `coe_mul_pEltPlus_pow`.
- **Hypotheses**: the ambient equation `h`.
- **Uses from project**: `BIPlusIn`, `BISub`, `pEltPlus`, `pImage`, `coe_mul_pEltPlus_pow`, `hatK`
- **Used by**: `mem_pIdeal_pow_iff` (1664)
- **Visibility**: public
- **Lines**: 1582–1593 (1-line term)
- **Notes**: exists precisely to isolate the two-level subtype unfolding (per its docstring).

### `theorem mem_pIdeal_pow_iff`
- **Type**: `(n : ℕ) (y : ↥(BIPlusIn …)) : y ∈ (pIdeal … ^ n) ↔ Valued.v (y : hatK × hatK).1 ≤ ρ₁ ^ n ∧ Valued.v (y : hatK × hatK).2 ≤ ρ₂ ^ n`
- **What**: The powers of the ideal of definition are exactly the two-coordinate balls — this identifies the `p`-adic topology on `B^{I,+}` with its subspace topology, the crux of the Huber-ring proof.
- **How**: `pIdeal_pow_eq_span` + `Ideal.mem_span_singleton'`. Forward: `coe_mul_pEltPlus_pow` and `valued_pImage_fst/snd` give `v(b·pⁿ)ᵢ ≤ ρᵢⁿ`. Backward: multiply by `pInvImage ^ n`, whose coordinate valuations `ρᵢ⁻ⁿ` (`valued_pInvImage_fst/snd`) make the result lie in `BIPlusIn` (`mem_BIPlusIn_iff`), and `mul_pEltPlus_pow_eq` with `pImage_mul_pInvImage` recovers `y`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pIdeal`, `pIdeal_pow_eq_span`, `BIPlusIn`, `BISub`, `mem_BIPlusIn_iff`, `coe_mul_pEltPlus_pow`, `mul_pEltPlus_pow_eq`, `pImage`, `pInvImage`, `valued_pImage_fst`, `valued_pImage_snd`, `valued_pInvImage_fst`, `valued_pInvImage_snd`, `pInvImage_mem_BISub`, `pImage_mul_pInvImage`, `hatK`
- **Used by**: `isOpen_pIdeal_pow` (1739), `pIdeal_pow_subset_ball` (1777)
- **Visibility**: public
- **Lines**: 1595–1674 (68-line proof)
- **Notes**: >30 lines; the longest proof in the adic endgame and the technical heart of `isAdic_pIdeal`.

### `theorem exists_wI_ball_subset`
- **Type**: `(hs : s ∈ nhds (0 : hatK × hatK)) : ∃ ε : NNReal, 0 < ε ∧ {z | wI … z ≤ ε} ⊆ s`
- **What**: Interval-norm balls form a neighbourhood basis at `0` in the product.
- **How**: `nhds_prod_eq` and `Filter.mem_prod_iff` split `s` into two coordinate neighbourhoods; `exists_valued_ball_subset` gives a ball inside each, and `min ε₁ ε₂` works for the max-norm.
- **Hypotheses**: `s` a neighbourhood of `0`.
- **Uses from project**: `wI`, `hatK`, `exists_valued_ball_subset`
- **Used by**: `exists_ball_subset_of_mem_nhds_BIPlusIn` (1756)
- **Visibility**: public
- **Lines**: 1676–1692 (10-line proof)
- **Notes**: —

### `theorem isOpen_coord_ball`
- **Type**: `{c₁ c₂ : NNReal} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) : IsOpen {z | Valued.v z.1 ≤ c₁ ∧ Valued.v z.2 ≤ c₂}`
- **What**: The two-coordinate closed ball (with independent radii) is open in the product.
- **How**: The set is *definitionally* an intersection of two coordinate preimages, so `IsOpen.inter` of two `isOpen_valued_ball` pullbacks along `continuous_fst`/`continuous_snd` finishes.
- **Hypotheses**: both radii positive.
- **Uses from project**: `hatK`, `isOpen_valued_ball`
- **Used by**: `isOpen_pIdeal_pow` (1741)
- **Visibility**: public
- **Lines**: 1694–1707 (7-line proof)
- **Notes**: generalises `isOpen_wI_ball` to unequal radii — needed because `(p)ⁿ` is the ball of radii `(ρ₁ⁿ, ρ₂ⁿ)`.

### `instance instIsTopologicalRingBIPlusIn`
- **Type**: `… : IsTopologicalRing ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: The ring of definition is a topological ring for its subspace topology.
- **How**: `inferInstance` — recorded once so later instance searches do not re-derive it through two subring layers.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BIPlusIn`
- **Used by**: unused explicitly in file (consumed by typeclass inference in `isAdic_pIdeal` / `BIPairOfDefinition`)
- **Visibility**: public instance
- **Lines**: 1709–1714 (1-line term)
- **Notes**: performance shortcut instance.

### `theorem isAdic_of_isOpen_pow_of_subset`
- **Type**: `{R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {J : Ideal R} (h1 : ∀ n, IsOpen ((J ^ n : Ideal R) : Set R)) (h2 : ∀ s ∈ nhds (0 : R), ∃ n, ((J ^ n : Ideal R) : Set R) ⊆ s) : IsAdic J`
- **What**: A general criterion for a topology to be `J`-adic: powers of `J` are open and form a neighbourhood basis at `0`.
- **How**: `isAdic_iff.mpr`.
- **Hypotheses**: `R` a topological commutative ring; the two conditions.
- **Uses from project**: `[]`
- **Used by**: `isAdic_pIdeal` (1802)
- **Visibility**: public
- **Lines**: 1716–1723 (1-line term)
- **Notes**: fully generic (no `p`/`F`/`ϖ` dependence) — a `ForMathlib`-style helper stated here to avoid unfolding the subring-of-a-subring topology twice.

### `theorem isOpen_pIdeal_pow`
- **Type**: `(n : ℕ) : IsOpen ((pIdeal p F ϖ … ^ n : Ideal ↥(BIPlusIn …)) : Set ↥(BIPlusIn …))`
- **What**: Every power of the ideal of definition is open in `B^{I,+}`.
- **How**: `mem_pIdeal_pow_iff` identifies `(p)ⁿ` with the preimage of the coordinate ball of radii `(ρ₁ⁿ, ρ₂ⁿ)`, which is open by `isOpen_coord_ball`; pull back along the double `continuous_subtype_val`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pIdeal`, `BIPlusIn`, `BISub`, `mem_pIdeal_pow_iff`, `isOpen_coord_ball`, `hatK`
- **Used by**: `isAdic_pIdeal` (1802)
- **Visibility**: public
- **Lines**: 1725–1742 (12-line proof)
- **Notes**: —

### `theorem exists_ball_subset_of_mem_nhds_BIPlusIn`
- **Type**: `(hs : s ∈ nhds (0 : ↥(BIPlusIn …))) : ∃ ε : NNReal, 0 < ε ∧ {y | wI … (y : hatK × hatK) ≤ ε} ⊆ s`
- **What**: Interval-norm balls form a neighbourhood basis at `0` in the ring of definition too.
- **How**: Unfold the two subtype topologies with `nhds_subtype_eq_comap` and `Filter.mem_comap`, then apply `exists_wI_ball_subset` in the ambient product and push the ball back through both inclusions.
- **Hypotheses**: `s` a neighbourhood of `0` in `B^{I,+}`.
- **Uses from project**: `BIPlusIn`, `BISub`, `wI`, `exists_wI_ball_subset`, `hatK`
- **Used by**: `isAdic_pIdeal` (1804)
- **Visibility**: public
- **Lines**: 1744–1762 (11-line proof)
- **Notes**: —

### `theorem pIdeal_pow_subset_ball`
- **Type**: `{N : ℕ} {ε : NNReal} (hN : (max ρ₁ ρ₂) ^ N ≤ ε) : ((pIdeal … ^ N : Ideal ↥(BIPlusIn …)) : Set _) ⊆ {y | wI … (y : hatK × hatK) ≤ ε}`
- **What**: If `(max ρ₁ ρ₂)^N ≤ ε` then the `N`-th power of the ideal of definition is contained in the `ε`-ball for the interval norm.
- **How**: `mem_pIdeal_pow_iff` gives the two coordinate bounds `ρᵢ^N`; each is `≤ (max ρ₁ ρ₂)^N ≤ ε` by `pow_le_pow_left₀`, and `max_le` assembles the `wI` bound.
- **Hypotheses**: `(max ρ₁ ρ₂)^N ≤ ε`.
- **Uses from project**: `pIdeal`, `BIPlusIn`, `BISub`, `wI`, `mem_pIdeal_pow_iff`, `hatK`
- **Used by**: `exists_pIdeal_pow_subset_of_ball` (1795)
- **Visibility**: public
- **Lines**: 1764–1782 (9-line proof)
- **Notes**: —

### `theorem exists_pIdeal_pow_subset_of_ball`
- **Type**: `{ε : NNReal} (hε : 0 < ε) (hsub : {y | wI … (y : hatK × hatK) ≤ ε} ⊆ s) : ∃ n : ℕ, ((pIdeal … ^ n : Ideal ↥(BIPlusIn …)) : Set _) ⊆ s`
- **What**: Any set containing an interval-norm ball contains a power of the ideal of definition — the converse inclusion of the adic sandwich.
- **How**: Since `max ρ₁ ρ₂ < 1`, `exists_pow_lt_of_lt_one` produces `N` with `(max ρ₁ ρ₂)^N < ε`, and `pIdeal_pow_subset_ball` puts `(p)^N` inside the ball, hence inside `s`.
- **Hypotheses**: `0 < ε`; the ball is inside `s`.
- **Uses from project**: `pIdeal`, `BIPlusIn`, `BISub`, `wI`, `pIdeal_pow_subset_ball`, `hatK`
- **Used by**: `isAdic_pIdeal` (1805)
- **Visibility**: public
- **Lines**: 1784–1795 (2-line `match` term)
- **Notes**: —

### `theorem isAdic_pIdeal`
- **Type**: `… : IsAdic (pIdeal p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: The subspace topology on `B^{I,+}` is exactly the `p`-adic topology — the defining property of the pair `(B^{I,+}, (p))`.
- **How**: `isAdic_of_isOpen_pow_of_subset` fed with `isOpen_pIdeal_pow` for openness and with `exists_ball_subset_of_mem_nhds_BIPlusIn` composed with `exists_pIdeal_pow_subset_of_ball` for the basis condition.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `pIdeal`, `isAdic_of_isOpen_pow_of_subset`, `isOpen_pIdeal_pow`, `exists_ball_subset_of_mem_nhds_BIPlusIn`, `exists_pIdeal_pow_subset_of_ball`
- **Used by**: `BIPairOfDefinition` (1815)
- **Visibility**: public
- **Lines**: 1797–1805 (4-line term)
- **Notes**: —

### `def BIPairOfDefinition`
- **Type**: `… : PairOfDefinition ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: The pair of definition `(B^{I,+}, (p))` for the interval ring `B^I` (Kedlaya Def. 4.2 / Lemma 4.4).
- **How**: Bundles `BIPlusIn` and `pIdeal` with the three required facts: `isOpen_BIPlusIn`, `pIdeal_fg`, `isAdic_pIdeal`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BISub`, `BIPlusIn`, `pIdeal`, `isOpen_BIPlusIn`, `pIdeal_fg`, `isAdic_pIdeal`, `PairOfDefinition`
- **Used by**: `isHuberRing_BISub` (1821), `isTateRing_BISub` (1839)
- **Visibility**: public
- **Lines**: 1807–1815 (5-field structure)
- **Notes**: —

### `instance isHuberRing_BISub`
- **Type**: `… : IsHuberRing ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: The interval ring `B^I` is a Huber ring.
- **How**: Supply `BIPairOfDefinition` as the required pair of definition.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BISub`, `BIPairOfDefinition`, `IsHuberRing`
- **Used by**: unused in file (headline instance)
- **Visibility**: public instance
- **Lines**: 1817–1821 (1 field)
- **Notes**: one of the file's two headline results.

### `def pUnit`
- **Type**: `… : (↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))ˣ`
- **What**: `p` packaged as a unit of `B^I`.
- **How**: `val := pEltB`, `inv := ⟨pInvImage, pInvImage_mem_BISub⟩`; both unit equations reduce by `Subtype.ext` to `pImage_mul_pInvImage` (the second after `mul_comm`).
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BISub`, `pEltB`, `pInvImage`, `pInvImage_mem_BISub`, `pImage_mul_pInvImage`
- **Used by**: `isTateRing_BISub` (1838)
- **Visibility**: public
- **Lines**: 1823–1831 (4-field structure)
- **Notes**: —

### `instance isTateRing_BISub`
- **Type**: `… : IsTateRing ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: The interval ring `B^I` is a Tate ring: `p` is a topologically nilpotent unit.
- **How**: Take `pUnit` as the unit; its topological nilpotence comes from `PairOfDefinition.isTopologicallyNilpotent_of_mem` applied to `pEltPlus`, which lies in `(p)` by `Ideal.mem_span_singleton_self`.
- **Hypotheses**: radii in `(0,1)`.
- **Uses from project**: `BISub`, `pUnit`, `BIPairOfDefinition`, `pEltPlus`, `IsTateRing`
- **Used by**: unused in file (headline instance)
- **Visibility**: public instance
- **Lines**: 1833–1840 (4-line proof)
- **Notes**: the file's second headline result.

---

### File Summary

**Totals** — 99 declarations: **14 defs** (`BIProd`, `BISub`, `wI`, `BIPlus`, `resI`, `resIHom`, `pImage`, `BIPlusIn`, `pInvImage`, `pEltB`, `pEltPlus`, `pIdeal`, `BIPairOfDefinition`, `pUnit`), **82 theorems/lemmas**, **3 instances** (`instIsTopologicalRingBIPlusIn`, `isHuberRing_BISub`, `isTateRing_BISub`). No structures, classes or abbrevs; everything is public (no `private`/`scoped`/`protected`).

**Key API used by 3+ others (in-file consumer counts)**
| declaration | in-file consumers |
|---|---|
| `wI` | ~90 sites — the interval norm, threaded through everything |
| `BISub` | ~80 sites — the interval ring itself |
| `BIProd` | ~28 consumers — the diagonal map |
| `BIPlusIn` | ~31 sites — the ring of definition |
| `pImage` | ~30 sites |
| `resI` | ~24 sites |
| `pInvImage` | ~16 sites |
| `pIdeal` | 11 sites |
| `neBot_comap_of_mem_BISub` | 8 (`tendsto_resI`, `resI_BIProd`, `resI_add`, `resI_mul`, `resI_pair_mem`, `valued_resI_le_wI`) |
| `valued_BlocToHatK` | 7 (`BlocToHatK_injective`, `valued_BlocToHatK_le_wI`, `wI_p_image`, `valued_pImage_fst/snd`, `valued_pInvImage_fst/snd`) |
| `tendsto_resI` | 10 sites across 5 consumers |
| `pEltPlus` | 6 consumers |
| `mem_BIPlusIn_iff` | 5 consumers |
| `wI_add_le`, `wI_mul_le`, `wI_one`, `wI_neg` | 4 each (`BIPlus`, `BIPlusIn`, plus norm lemmas) |
| `wI_pow` | 3 (`wI_pow_eq_one_iff`, `tendsto_wI_p_pow`, `wI_p_pow_mul_le`) |
| `wI_p_image` | 3 (`tendsto_wI_p_pow`, `wI_p_pow_mul_le`, `pEltB_mem_BIPlusIn`) |
| `gaussValue_p` | 3 (`wI_p_image`, `valued_pImage_fst/snd`) |
| `isOpen_valued_ball` | 4 sites (`isOpen_wI_ball` ×2, `isOpen_coord_ball` ×2) |
| `isClosed_valued_ball` | 3 sites (`isClosed_wI_ball` ×2, `valued_resI_le_wI`) |
| `valued_ball_mem_nhds` | 3 consumers (`exists_BIProd_wI_le`, `eventually_pair_wI_le`, `wI_ball_mem_nhds`) |
| `valued_pImage_fst` / `valued_pImage_snd` | 3 each |
| `BIProd_mem_BISub` | 3 |

**Unused in file (24)** — exported API, several of them the file's actual headline results:
`wI_eq_zero_iff`, `BISub_fst_mem`, `BISub_snd_mem`, `exists_BIProd_wI_le`, `rpow_interpolate_lt_one`, `exists_BI_series_limit`, `BIProd_injective`, `mem_BIPlus_iff`, `BIPlus_le_BISub`, `wI_pow_le_one`, **`resIHom`**, `wI_pow_eq_one_iff`, `tendsto_wI_p_pow`, `wI_le_of_approx`, `isComplete_BIPlus`, `valued_resI_le_wI`, `wI_p_pow_mul_le`, `p_pow_smul_ball_eq`, `instIsTopologicalRingBIPlusIn` (used only by instance search), **`isHuberRing_BISub`**, **`isTateRing_BISub`**, plus `BIPlus`-block leaves. `resIHom`, `isHuberRing_BISub` and `isTateRing_BISub` are the intended downstream exports.

**Declarations with `sorry`** — none. The file is sorry-free.

**Declarations with `set_option`** — none. No `maxHeartbeats`/`maxRecDepth` bumps anywhere in the file.

**Proofs > 30 lines** (8, longest first)
| declaration | lines | proof length |
|---|---|---|
| `mem_pIdeal_pow_iff` | 1595–1674 | 68 |
| `wLoc_rpow_interpolate` | 338–404 | 59 |
| `resIHom` | 1002–1056 | 53 (structure with 4 field proofs) |
| `BIPlusIn` | 1426–1475 | 48 (structure with 6 field proofs) |
| `exists_eq_p_pow_mul` | 1299–1350 | 44 |
| `exists_BI_series_limit` | 456–508 | 42 |
| `eventually_pair_wI_le` | 690–738 | 41 |
| `valued_resI_le_wI` | 1222–1268 | 38 |
| `gaussTerm_rpow_interpolate` | 258–295 | 33 |

(Just under the bar, for completeness: `valued_BlocToHatK` 28, `tendsto_resI` 26, `BIPlus` 25, `wLoc_ne_zero` 25, `isClosed_wI_ball` 24.)

**Other observations**
- Near-duplicate pairs, all dedup candidates: `isClosed_valued_ball` / `isOpen_valued_ball` (identical `AddSubgroup` construction), `isClosed_wI_ball` / `isOpen_wI_ball` (identical set decomposition), `map_add_comap_le` / `map_mul_comap_le`, `BIPlus` / `BIPlusIn` (same conditions, different ambient ring), `BISub_fst_mem` / `BISub_snd_mem`.
- `isAdic_of_isOpen_pow_of_subset` is fully generic in `R` and `J` — a `ForMathlib`-style helper living in this file.
- `wI_pow_eq_one_iff` and `valued_resI_le_wI` use the `push Not` tactic; `coe_mul_pEltPlus_pow` uses `push_cast`.
- Missing docstrings: `valued_pImage_snd`, `mem_BIPlusIn_iff`, `valued_pInvImage_fst`, `valued_pInvImage_snd`, `pInvImage_mem_BISub`, `pEltB_mem_BIPlusIn`, `pIdeal_fg`.
