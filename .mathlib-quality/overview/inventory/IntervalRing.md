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
