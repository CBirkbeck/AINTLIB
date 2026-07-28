# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/IntervalSplitting.lean`

**Namespace:** `FarguesFontaine`  •  **Lines:** 1029  •  **Imports:** `«Adic spaces».FarguesFontaine.UniformizerEquivariance`, `Mathlib.RingTheory.WittVector.InitTail`
**Opens:** `TopologicalRing ValuationSpectrum WittVector NNReal`  •  entire file inside `noncomputable section`

**Ambient variables** (used by every declaration): `(p : ℕ) [Fact p.Prime]`, `(F : Type*)` a topological/uniform field with `[NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]`, and `(ϖ : PseudoUniformizer F)`. From line 849 onward there are additional implicit radius variables `{ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}`.

---

### `theorem teichCoeff_tail`
- **Type**: `(x : Ainf p F) (k n : ℕ) : teichCoeff p F (WittVector.tail k x) n = if k ≤ n then teichCoeff p F x n else 0`
- **What**: The `n`-th Teichmüller (Witt) coordinate of the `k`-tail truncation of `x ∈ A_inf` is `x`'s own `n`-th coordinate when `n ≥ k`, and `0` otherwise. It says exactly that `tail k` kills the first `k` Witt coordinates and leaves the rest alone.
- **How**: Case split `by_cases hn : k ≤ n`, then `simp` unfolding `teichCoeff`, `WittVector.tail`, `WittVector.select`: mathlib's `tail k` is `select (k ≤ ·)`, so the coefficient is either `x.coeff n` or `0` according to the selecting predicate.
- **Hypotheses**: none beyond the ambient perfectoid-field setup (`p` prime, `F` char-`p` perfectoid) needed for `Ainf`/`teichCoeff` to typecheck.
- **Uses from project**: `Ainf`, `teichCoeff`
- **Used by**: `pow_mul_gaussValue_tail_le`
- **Visibility**: public
- **Lines**: 43–48 (proof 2 lines)
- **Notes**: none

### `theorem teichCoeff_init`
- **Type**: `(x : Ainf p F) (k n : ℕ) : teichCoeff p F (WittVector.init k x) n = if n < k then teichCoeff p F x n else 0`
- **What**: Mirror of the previous lemma for the initial truncation: `init k x` keeps the Witt coordinates below index `k` and zeroes all the others.
- **How**: `by_cases hn : n < k` then `simp [teichCoeff, WittVector.init, WittVector.select, hn]` — `init k` is `select (· < k)`, so the selecting predicate directly produces the `if`.
- **Hypotheses**: none beyond the ambient setup.
- **Uses from project**: `Ainf`, `teichCoeff`
- **Used by**: `pow_mul_gaussValue_init_le`
- **Visibility**: public
- **Lines**: 50–55 (proof 2 lines)
- **Notes**: none

### `theorem pow_mul_gaussValue_tail_le`
- **Type**: `{σ τ : NNReal} (hστ : σ ≤ τ) (hτ1 : τ ≤ 1) (x : Ainf p F) (k : ℕ) : τ ^ k * gaussValue p F σ (WittVector.tail k x) ≤ σ ^ k * gaussValue p F τ x`
- **What**: **The tail bound** (positive part of the Mittag-Leffler estimate). For radii `σ ≤ τ ≤ 1`, the `σ`-Gauss norm of the `k`-tail of `x` is bounded by the `τ`-Gauss norm of `x` up to the radius-ratio factor `(σ/τ)^k`, written multiplicatively to avoid division.
- **How**: Unfold `gaussValue` as a supremum of `gaussTerm`s, push the scalar inside with `NNReal.mul_iSup`, and bound each term via `ciSup_le`. For `n ≥ k`, `teichCoeff_tail` shows the term is `σ^n · |x_n|`; the core inequality `τ^k σ^n ≤ σ^k τ^n` comes from writing `σ^n = σ^k σ^{n-k}`, `τ^n = τ^k τ^{n-k}` (`pow_add` + `omega`) and applying `pow_le_pow_left' hστ`; the resulting `σ^k · gaussTerm τ x n` is then dominated by `σ^k · gaussValue τ x` using `le_ciSup (bddAbove_range_gaussTerm p F hτ1 x)`. For `n < k` the coefficient vanishes and the term is `0`.
- **Hypotheses**: `σ ≤ τ` (the small radius is the one where the tail is measured) and `τ ≤ 1` (needed so that the family of Gauss terms at radius `τ` is bounded above, i.e. so the sup exists).
- **Uses from project**: `Ainf`, `teichCoeff`, `teichCoeff_tail`, `gaussValue`, `gaussTerm`, `perfectoidValuation`, `bddAbove_range_gaussTerm`
- **Used by**: `exists_wLoc_split`
- **Visibility**: public
- **Lines**: 57–96 (proof 33 lines)
- **Notes**: proof > 30 lines; no `set_option`, no `sorry`

### `theorem pow_mul_gaussValue_init_le`
- **Type**: `{σ τ : NNReal} (hτσ : τ ≤ σ) (hσ1 : σ ≤ 1) (hτ1 : τ ≤ 1) (x : Ainf p F) (k : ℕ) : τ ^ k * gaussValue p F σ (WittVector.init k x) ≤ σ ^ k * gaussValue p F τ x`
- **What**: **The initial bound** (principal part of the Mittag-Leffler estimate). Dual to the previous lemma: for `τ ≤ σ ≤ 1`, the `σ`-Gauss norm of the `k`-initial part of `x` is controlled by the `τ`-Gauss norm of `x`.
- **How**: Same supremum-by-supremum scheme (`NNReal.mul_iSup`, `ciSup_le`). For `n < k`, `teichCoeff_init` identifies the term as `σ^n · |x_n|`; the core inequality `τ^k σ^n ≤ σ^k τ^n` is now proven by splitting the *larger* exponent, `σ^k = σ^n σ^{k-n}` and `τ^k = τ^n τ^{k-n}`, and applying `pow_le_pow_left' hτσ`. The bound then closes with `le_ciSup (bddAbove_range_gaussTerm p F hτ1 x)`; for `n ≥ k` the term is `0` by `teichCoeff_init`.
- **Hypotheses**: `τ ≤ σ` (radius ordering reversed relative to the tail bound), `σ ≤ 1` (unused numerically but kept for symmetry of the API), `τ ≤ 1` (boundedness of the Gauss-term family at `τ`).
- **Uses from project**: `Ainf`, `teichCoeff`, `teichCoeff_init`, `gaussValue`, `gaussTerm`, `perfectoidValuation`, `bddAbove_range_gaussTerm`
- **Used by**: `exists_wLoc_split`
- **Visibility**: public
- **Lines**: 98–137 (proof 33 lines)
- **Notes**: proof > 30 lines; hypothesis `hσ1` is not consumed in the body (symmetry/API-shape only)

### `theorem exists_wLoc_split`
- **Type**: `{τ : NNReal} (hτ0 : 0 < τ) (hτ1 : τ < 1) (z : Bloc p F ϖ) : ∃ zP zM : Bloc p F ϖ, z = zP + zM ∧ (∀ σ hσ0 hσ1, σ ≤ τ → wLoc p F ϖ hσ0 hσ1 zP ≤ wLoc p F ϖ hτ0 hτ1 z) ∧ (∀ σ hσ0 hσ1, τ ≤ σ → wLoc p F ϖ hσ0 hσ1 zM ≤ wLoc p F ϖ hτ0 hτ1 z)`
- **What**: **The Mittag-Leffler splitting of `Bloc`.** Every element `z` of the localized Robba-type ring splits at a threshold radius `τ` into a "tail"/positive part `zP` whose norm at every radius `σ ≤ τ` is bounded by `z`'s `τ`-norm, plus a "principal" part `zM` with the same bound at every radius `σ ≥ τ`. This is the analytic engine behind gluing of interval rings.
- **How**: Present `z` as a fraction `x/y` with `y = (p·[ϖ])^k` using `IsLocalization.surj` over `Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)` and `IsLocalization.eq_mk'_iff_mul_eq`. Compute the denominator's Gauss value once and for all as `(σ·|ϖ|)^k` via `gaussVal_apply`, `Valuation.map_pow` and `gaussValue_p_teichPi` (nonvanishing by `gaussValue_p_teichPi_ne_zero`). Then set `zP := mk' (tail k x) y`, `zM := mk' (init k x) y`; the sum identity is `IsLocalization.mk'_add` plus `WittVector.init_add_tail` and `IsLocalization.mk'_cancel`. Each norm bound reduces via `wLoc_mk'` and `div_le_div_iff₀` (denominators nonzero) to exactly `pow_mul_gaussValue_tail_le` / `pow_mul_gaussValue_init_le` after cancelling the common factor `|ϖ|^k` with `ring`.
- **Hypotheses**: `0 < τ < 1` (a legitimate radius); `F` perfectoid of char `p` and `ϖ` a pseudo-uniformizer, so `p·[ϖ]` is the element inverted in `Bloc` and its Gauss value is computable and nonzero.
- **Uses from project**: `Bloc`, `Ainf`, `teichPi`, `wLoc`, `wLoc_mk'`, `gaussValue`, `gaussVal`, `gaussVal_apply`, `gaussValue_p_teichPi`, `gaussValue_p_teichPi_ne_zero`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`, `pow_mul_gaussValue_tail_le`, `pow_mul_gaussValue_init_le`
- **Used by**: `exists_blocApprox_pair`
- **Visibility**: public
- **Lines**: 139–233 (proof 83 lines)
- **Notes**: proof > 30 lines; the two bound-proofs are near-verbatim mirrors of each other (a decomposition candidate)

### `def biFstQ`
- **Type**: `(q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂) →+* hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)`
- **What**: **The left-endpoint projection** of the rational-exponent interval ring: sends an element of `B^{[q₁,q₂]}` to its component in the completed field at radius `|ϖ|^{q₁}`.
- **How**: `BIQ` is by construction a subring of the product of the two completed endpoint fields, so the map is literally `Prod.fst ∘ Subtype.val`; all four ring-hom axioms (`map_one'`, `map_mul'`, `map_zero'`, `map_add'`) are `rfl` because subring/product operations are componentwise.
- **Hypotheses**: `0 < q₁`, `0 < q₂` — needed so that `vpiQ_lt_one` applies and both radii lie in `(0,1)`.
- **Uses from project**: `BIQ`, `hatK`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biFstQ_continuous`, `biFstQ_blocToBI`, `biFstQ_biResQ'_left`, `biSndQ_biResQ'_middle`, `biResQ'_split_injective`, `exists_blocApprox_pair`, `biResQ'_eq_left_of_tendsto`, `biResQ'_eq_right_of_tendsto`, `glueSeq`, `glueSeq_specL`, `glueSeq_specR`, `glueSeq_valued_le`, `biGlue`, `biGlue_coe`, `biGlue_fst`, `biGlue_snd`, `tendsto_glueSeq_biGlue`, `biResQ'_biGlue_left`, `biResQ'_biGlue_right`, `biResQ'_split_surjective`
- **Visibility**: public (`noncomputable`)
- **Lines**: 235–245 (structure-instance body, 6 lines)
- **Notes**: none

### `def biSndQ`
- **Type**: `(q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂) →+* hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)`
- **What**: **The right-endpoint projection**: the component of an element of `B^{[q₁,q₂]}` in the completed field at radius `|ϖ|^{q₂}`.
- **How**: Same as `biFstQ` but taking `Prod.snd` of the underlying pair; the ring-hom fields are `rfl` since the product ring structure is componentwise.
- **Hypotheses**: `0 < q₁`, `0 < q₂` (so both radii are admissible).
- **Uses from project**: `BIQ`, `hatK`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biSndQ_continuous`, `biSndQ_blocToBI`, `biSndQ_biResQ'_right`, `biSndQ_biResQ'_middle`, `biResQ'_split_injective`, `exists_blocApprox_pair`, `biResQ'_eq_left_of_tendsto`, `biResQ'_eq_right_of_tendsto`, `glueSeq`, `glueSeq_specL`, `glueSeq_specR`, `glueSeq_valued_le`, `biGlue`, `biGlue_coe`, `biGlue_fst`, `biGlue_snd`, `tendsto_glueSeq_biGlue`, `biResQ'_biGlue_left`, `biResQ'_biGlue_right`, `biResQ'_split_surjective`
- **Visibility**: public (`noncomputable`)
- **Lines**: 247–256 (structure-instance body, 6 lines)
- **Notes**: none

### `theorem biFstQ_continuous`
- **Type**: `(q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) : Continuous (biFstQ p F ϖ q₁ q₂ h₁ h₂)`
- **What**: The left-endpoint projection is continuous for the subspace topology on `B^{[q₁,q₂]}` and the product topology on the endpoint fields.
- **How**: One-liner: the map is `Prod.fst ∘ Subtype.val`, so `continuous_fst.comp continuous_subtype_val`.
- **Hypotheses**: `0 < q₁`, `0 < q₂` (only to make `biFstQ` typecheck).
- **Uses from project**: `biFstQ`
- **Used by**: `biFstQ_biResQ'_left`, `biSndQ_biResQ'_middle`, `biResQ'_eq_right_of_tendsto`
- **Visibility**: public
- **Lines**: 258–260 (proof 1 line, term mode)
- **Notes**: none

### `theorem biSndQ_continuous`
- **Type**: `(q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) : Continuous (biSndQ p F ϖ q₁ q₂ h₁ h₂)`
- **What**: The right-endpoint projection is continuous.
- **How**: `continuous_snd.comp continuous_subtype_val` — same composition-of-projections argument as for `biFstQ_continuous`.
- **Hypotheses**: `0 < q₁`, `0 < q₂`.
- **Uses from project**: `biSndQ`
- **Used by**: `biSndQ_biResQ'_right`, `biSndQ_biResQ'_middle`, `biResQ'_eq_left_of_tendsto`
- **Visibility**: public
- **Lines**: 262–264 (proof 1 line, term mode)
- **Notes**: none

### `theorem biFstQ_blocToBI`
- **Type**: `(q₁ q₂ : ℚ) (h₁ h₂) (z : Bloc p F ϖ) : biFstQ p F ϖ q₁ q₂ h₁ h₂ (blocToBI p F ϖ … z) = BlocToHatK p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁) z`
- **What**: On the dense layer `Bloc ⊆ B^I`, the left-endpoint projection is just the completion map `Bloc → \hat K_{|ϖ|^{q₁}}`.
- **How**: `blocToBI` is `BIProd` corestricted to the closure, so `show` re-expresses the goal as `(BIProd … z).1 = _`, and `BIProd_fst` closes it.
- **Hypotheses**: `0 < q₁`, `0 < q₂`.
- **Uses from project**: `biFstQ`, `blocToBI`, `BIProd`, `BIProd_fst`, `BlocToHatK`, `Bloc`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biFstQ_biResQ'_left`, `biSndQ_biResQ'_middle`, `biResQ'_eq_right_of_tendsto`
- **Visibility**: public
- **Lines**: 266–275 (proof 4 lines)
- **Notes**: none

### `theorem biSndQ_blocToBI`
- **Type**: `(q₁ q₂ : ℚ) (h₁ h₂) (z : Bloc p F ϖ) : biSndQ p F ϖ q₁ q₂ h₁ h₂ (blocToBI p F ϖ … z) = BlocToHatK p F ϖ (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z`
- **What**: Dual dense-layer identity: the right-endpoint projection restricted to `Bloc` is the completion map at radius `|ϖ|^{q₂}`.
- **How**: `show` unfolds the coercion to `(BIProd … z).2 = _` and `BIProd_snd` finishes.
- **Hypotheses**: `0 < q₁`, `0 < q₂`.
- **Uses from project**: `biSndQ`, `blocToBI`, `BIProd`, `BIProd_snd`, `BlocToHatK`, `Bloc`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biSndQ_biResQ'_right`, `biSndQ_biResQ'_middle`, `biResQ'_eq_left_of_tendsto`
- **Visibility**: public
- **Lines**: 277–286 (proof 4 lines)
- **Notes**: none

### `theorem biFstQ_biResQ'_left`
- **Type**: `(q₁ q₂ r : ℚ) (h₁ h₂ hr) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) : (biFstQ p F ϖ q₁ r h₁ hr).comp (biResQ' p F ϖ q₁ q₂ q₁ r … ) = biFstQ p F ϖ q₁ q₂ h₁ h₂`
- **What**: **Shared-left-endpoint law**: restricting from `[q₁,q₂]` to the left half `[q₁,r]` and then projecting to the `q₁`-endpoint gives back the original `q₁`-endpoint projection. Stated as an equality of ring homs.
- **How**: Both composites are continuous (`biFstQ_continuous`, `biResQ'_continuous`), so `DenseRange.equalizer` applied to `denseRange_blocToBI` reduces the claim to the dense `Bloc`-layer; there `biResQ'_blocToBI` turns the restriction into `blocToBI` at the new radii and two applications of `biFstQ_blocToBI` make both sides `BlocToHatK` at radius `|ϖ|^{q₁}`. Finally `RingHom.ext` upgrades the function equality to a ring-hom equality.
- **Hypotheses**: all three exponents positive; `q₂ < q₁` (nondegenerate interval, decreasing-radius orientation); `q₂ ≤ r ≤ q₁` (the split point lies inside).
- **Uses from project**: `biFstQ`, `biResQ'`, `biFstQ_continuous`, `biResQ'_continuous`, `denseRange_blocToBI`, `biResQ'_blocToBI`, `biFstQ_blocToBI`, `blocToBI`, `BIQ`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biResQ'_split_injective`, `biResQ'_eq_left_of_tendsto`
- **Visibility**: public
- **Lines**: 288–310 (proof 16 lines)
- **Notes**: none

### `theorem biSndQ_biResQ'_right`
- **Type**: `(q₁ q₂ r : ℚ) (h₁ h₂ hr) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) : (biSndQ p F ϖ r q₂ hr h₂).comp (biResQ' p F ϖ q₁ q₂ r q₂ … ) = biSndQ p F ϖ q₁ q₂ h₁ h₂`
- **What**: **Shared-right-endpoint law**: restricting to the right half `[r,q₂]` and projecting to the `q₂`-endpoint reproduces the original `q₂`-endpoint projection.
- **How**: The same dense-range equalizer argument: `denseRange_blocToBI.equalizer` with continuity from `biSndQ_continuous` and `biResQ'_continuous`, and on the dense layer `biResQ'_blocToBI` followed by two uses of `biSndQ_blocToBI` collapses both sides to `BlocToHatK` at `|ϖ|^{q₂}`; `RingHom.ext` finishes.
- **Hypotheses**: exponents positive; `q₂ < q₁`; `q₂ ≤ r ≤ q₁`.
- **Uses from project**: `biSndQ`, `biResQ'`, `biSndQ_continuous`, `biResQ'_continuous`, `denseRange_blocToBI`, `biResQ'_blocToBI`, `biSndQ_blocToBI`, `blocToBI`, `BIQ`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biResQ'_split_injective`, `biResQ'_eq_right_of_tendsto`
- **Visibility**: public
- **Lines**: 312–334 (proof 16 lines)
- **Notes**: none

### `theorem biSndQ_biResQ'_middle`
- **Type**: `(q₁ q₂ r : ℚ) (h₁ h₂ hr) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) : (biSndQ p F ϖ q₁ r h₁ hr).comp (biResQ' … q₁ r …) = (biFstQ p F ϖ r q₂ hr h₂).comp (biResQ' … r q₂ …)`
- **What**: **Middle-component match**: the `r`-endpoint of the restriction to the left half `[q₁,r]` agrees with the `r`-endpoint of the restriction to the right half `[r,q₂]`. This is precisely the cocycle/compatibility condition that makes the pair of restrictions land in the fiber product over `\hat K_{|ϖ|^r}`.
- **How**: Again `denseRange_blocToBI.equalizer` (both composites continuous by `biSndQ_continuous`/`biFstQ_continuous` composed with `biResQ'_continuous`); on the dense layer two applications of `biResQ'_blocToBI` plus `biSndQ_blocToBI` and `biFstQ_blocToBI` reduce both sides to `BlocToHatK` at radius `|ϖ|^r`; `RingHom.ext` concludes.
- **Hypotheses**: exponents positive; `q₂ < q₁`; `q₂ ≤ r ≤ q₁`.
- **Uses from project**: `biSndQ`, `biFstQ`, `biResQ'`, `biSndQ_continuous`, `biFstQ_continuous`, `biResQ'_continuous`, `denseRange_blocToBI`, `biResQ'_blocToBI`, `biSndQ_blocToBI`, `biFstQ_blocToBI`, `blocToBI`, `BIQ`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: unused in file (exported; consumed by `FarguesFontaine/YPresheaf.lean`)
- **Visibility**: public
- **Lines**: 336–365 (proof 22 lines)
- **Notes**: none

### `theorem biResQ'_split_injective`
- **Type**: `(q₁ q₂ r : ℚ) (h₁ h₂ hr) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) {x y : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)} (hL : …left restrictions agree…) (hR : …right restrictions agree…) : x = y`
- **What**: **Separation half of the sheaf axiom**: an element of `B^{[q₁,q₂]}` is uniquely determined by its restrictions to the two halves `[q₁,r]` and `[r,q₂]`.
- **How**: `RingHom.congr_fun` applied to `biFstQ_biResQ'_left` rewrites `biFstQ x` as `biFstQ (res_left x)`, so `hL` forces the `q₁`-components of `x` and `y` to agree; symmetrically `biSndQ_biResQ'_right` with `hR` forces the `q₂`-components to agree. Since `BIQ` is a subring of a *product of two fields*, `Subtype.ext (Prod.ext hfst hsnd)` gives `x = y`.
- **Hypotheses**: exponents positive; `q₂ < q₁`; `q₂ ≤ r ≤ q₁`; the two restriction-equality hypotheses `hL`, `hR`.
- **Uses from project**: `biFstQ`, `biSndQ`, `biResQ'`, `biFstQ_biResQ'_left`, `biSndQ_biResQ'_right`, `BIQ`
- **Used by**: unused in file (exported; consumed by `FarguesFontaine/YPresheaf.lean`)
- **Visibility**: public
- **Lines**: 367–390 (proof 13 lines)
- **Notes**: none

### `theorem exists_blocApprox_pair`
- **Type**: `(q₁ q₂ r : ℚ) (h₁ h₂ hr) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁) (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂)) (hmatch : biSndQ … g₁ = biFstQ … g₂) {ε : NNReal} (hε : 0 < ε) : ∃ h : Bloc p F ϖ, wI … (g₁ - BIProd … h) ≤ ε ∧ wI … (g₂ - BIProd … h) ≤ ε`
- **What**: **The joint approximation step**: a *matching* pair of half-interval elements can be approximated to accuracy `ε` by a *single* element of the dense layer `Bloc`, simultaneously in both halves. This is where the Mittag-Leffler splitting is actually used.
- **How**: Each `gᵢ` lies in the topological closure of the `BIProd`-range (that is the definition of `BISub`/`BIQ`), so `mem_closure_iff_nhds` together with `wI_ball_mem_nhds` produces `z₁, z₂ ∈ Bloc` with `wI (BIProd zᵢ - gᵢ) ≤ ε`. Their difference at the split radius is small: through `hmatch` the ultrametric triangle inequality `Valuation.map_add` bounds `v(BlocToHatK_r z₁ - BlocToHatK_r z₂)` by `max` of the two `ε`-bounds, giving `wLoc_{|ϖ|^r}(z₁ - z₂) ≤ ε` after `valued_BlocToHatK`. Now `exists_wLoc_split` splits `z₁ - z₂ = dP + dM` at `τ = vpiQ r`, and `h := z₁ - dP` works: on the left half, `wI_add_le` splits off the correction, `wI_BIProd` + `valued_BlocToHatK` turn it into two `wLoc` values, and the `τ`-control of `dP` at radii `≤ |ϖ|^r` (using `vpiQ_antitone hrq₁`) bounds them by `ε`; on the right half `z₁ - dP = z₂ + dM` and the `τ`-control of `dM` at radii `≥ |ϖ|^r` (using `vpiQ_antitone hq₂r`) does the same, with `wI_neg` handling signs.
- **Hypotheses**: `0 < q₁, q₂, r`; `q₂ ≤ r ≤ q₁` (split point inside the interval, with the radius-decreasing orientation); the matching condition `hmatch` at the split radius; `0 < ε`.
- **Uses from project**: `BIQ`, `BISub`, `BIProd`, `hatK`, `wI`, `wI_ball_mem_nhds`, `wI_add_le`, `wI_neg`, `wI_BIProd`, `biSndQ`, `biFstQ`, `BlocToHatK`, `valued_BlocToHatK`, `wLoc`, `exists_wLoc_split`, `vpiQ_pos`, `vpiQ_lt_one`, `vpiQ_antitone`, `Bloc`
- **Used by**: `glueSeq`, `glueSeq_specL`, `glueSeq_specR`
- **Visibility**: public
- **Lines**: 392–540 (proof 128 lines)
- **Notes**: proof > 30 lines — by far the longest analytic argument in the file; the left-half and right-half blocks are structurally parallel (decomposition candidate)

### `theorem tendsto_hatK_of_valued_le`
- **Type**: `{ρ : NNReal} {hρ0 hρ1} {u : ℕ → hatK p F hρ0 hρ1} {L : hatK p F hρ0 hρ1} {ε : ℕ → NNReal} (hb : ∀ n, Valued.v (u n - L) ≤ ε n) (hε : Tendsto ε atTop (nhds 0)) : Tendsto u atTop (nhds L)`
- **What**: Convergence criterion in a completed endpoint field: termwise valuation bounds by a null sequence force convergence to `L`.
- **How**: `Filter.tendsto_def` reduces to preimages of neighbourhoods; `Valued.mem_nhds` presents any `U ∈ 𝓝 L` as containing a valuation ball of radius `γ` in the value group, and the project lemma `exists_nnreal_lt_gamma` converts `γ` into a positive `NNReal` threshold `δ`. Then `hε.eventually_lt_const hδ0` makes `ε n < δ` eventually, and `(hb n).trans hn.le` puts `u n` inside the ball.
- **Hypotheses**: a termwise bound `v(u n - L) ≤ ε n` and `ε → 0` in `NNReal`; the radius `ρ ∈ (0,1)` so that `hatK` is the intended completed field.
- **Uses from project**: `hatK`, `exists_nnreal_lt_gamma`
- **Used by**: `tendsto_BIProd_of_valued_le`, `biResQ'_biGlue_left`, `biResQ'_biGlue_right`
- **Visibility**: public
- **Lines**: 542–555 (proof 8 lines)
- **Notes**: none

### `theorem tendsto_BIProd_of_valued_le`
- **Type**: `{ρ₁ ρ₂} {hρ₁0 hρ₁1 hρ₂0 hρ₂1} {h : ℕ → Bloc p F ϖ} {a : hatK p F hρ₁0 hρ₁1} {b : hatK p F hρ₂0 hρ₂1} {ε : ℕ → NNReal} (h1 : ∀ n, v (BlocToHatK … (h n) - a) ≤ ε n) (h2 : ∀ n, v (BlocToHatK … (h n) - b) ≤ ε n) (hε : Tendsto ε atTop (nhds 0)) : Tendsto (fun n => BIProd … (h n)) atTop (nhds (a, b))`
- **What**: If the two endpoint images of a sequence of `Bloc` elements are termwise controlled by a common null sequence, then the diagonal images converge to `(a,b)` in the product of the two completed fields.
- **How**: Apply `tendsto_hatK_of_valued_le` separately in each coordinate and combine with `Filter.Tendsto.prodMk_nhds`, which is exactly convergence in the product topology.
- **Hypotheses**: the two termwise bounds by the same `ε`, and `ε → 0`; both radii in `(0,1)`.
- **Uses from project**: `tendsto_hatK_of_valued_le`, `hatK`, `Bloc`, `BlocToHatK`, `BIProd`
- **Used by**: `biGlue`, `tendsto_glueSeq_biGlue`
- **Visibility**: public
- **Lines**: 557–569 (proof 3 lines)
- **Notes**: none

### `theorem biResQ'_eq_left_of_tendsto`
- **Type**: `(q₁ q₂ r : ℚ) (h₁ h₂ hr) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (f : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)) (h : ℕ → Bloc p F ϖ) (hfst : biFstQ … f = biFstQ … g₁) (htof : blocToBI (h n) → f) (hmid : BlocToHatK_{|ϖ|^r} (h n) → biSndQ … g₁) : biResQ' … f = g₁`
- **What**: **Recognition criterion for the left half**: if `f` already has the right outer (`q₁`) component and some `Bloc` sequence converges to `f` in `B^{[q₁,q₂]}` while its `r`-endpoint converges to `g₁`'s `r`-component, then the left restriction of `f` really is `g₁`.
- **How**: Transport the approximating sequence through the restriction map: `Filter.Tendsto.congr` with `biResQ'_blocToBI` (restriction of a `Bloc` element is again `blocToBI`) plus continuity `biResQ'_continuous` gives `blocToBI (h n) → biResQ' f` inside `B^{[q₁,r]}`. Then compare the two components of the subtype element: the `q₁`-component by `RingHom.congr_fun (biFstQ_biResQ'_left …)` together with `hfst`; the `r`-component by `tendsto_nhds_unique` between `hmid` and the limit obtained from `biSndQ_blocToBI` + `biSndQ_continuous` applied to the transported sequence. `Subtype.ext (Prod.ext …)` assembles them.
- **Hypotheses**: exponents positive; `q₂ < q₁`; `q₂ ≤ r ≤ q₁`; the outer-component equality `hfst` and the two convergence hypotheses; Hausdorffness of the endpoint field (used implicitly by `tendsto_nhds_unique`).
- **Uses from project**: `BIQ`, `Bloc`, `biFstQ`, `biSndQ`, `biResQ'`, `biResQ'_blocToBI`, `biResQ'_continuous`, `biFstQ_biResQ'_left`, `biSndQ_blocToBI`, `biSndQ_continuous`, `blocToBI`, `BlocToHatK`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biResQ'_biGlue_left`
- **Visibility**: public
- **Lines**: 571–611 (proof 25 lines)
- **Notes**: none

### `theorem biResQ'_eq_right_of_tendsto`
- **Type**: mirror of the above with `g₂ : ↥(BIQ p F ϖ r q₂ hr h₂)`, hypothesis `hsnd : biSndQ … f = biSndQ … g₂`, `hmid` converging to `biFstQ … g₂`, conclusion `biResQ' … r q₂ … f = g₂`
- **What**: **Recognition criterion for the right half**: matching outer (`q₂`) component plus joint convergence identifies the right restriction of `f` as `g₂`.
- **How**: Same scheme mirrored: `Filter.Tendsto.congr` with `biResQ'_blocToBI` and `biResQ'_continuous` transports the sequence into `B^{[r,q₂]}`; the `r`-component is pinned by `tendsto_nhds_unique` against the limit given by `biFstQ_blocToBI` + `biFstQ_continuous`, and the `q₂`-component by `RingHom.congr_fun (biSndQ_biResQ'_right …)` with `hsnd`; `Subtype.ext (Prod.ext …)` concludes.
- **Hypotheses**: exponents positive; `q₂ < q₁`; `q₂ ≤ r ≤ q₁`; `hsnd` and the two convergence hypotheses.
- **Uses from project**: `BIQ`, `Bloc`, `biFstQ`, `biSndQ`, `biResQ'`, `biResQ'_blocToBI`, `biResQ'_continuous`, `biSndQ_biResQ'_right`, `biFstQ_blocToBI`, `biFstQ_continuous`, `blocToBI`, `BlocToHatK`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biResQ'_biGlue_right`
- **Visibility**: public
- **Lines**: 613–650 (proof 25 lines)
- **Notes**: none

### `def glueSeq`
- **Type**: `(q₁ q₂ r : ℚ) (h₁ h₂ hr) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁) (g₁ …) (g₂ …) (hmatch …) : ℕ → Bloc p F ϖ`
- **What**: **The joint approximating sequence** for a matching pair: for each `n`, an element of `Bloc` that approximates both `g₁` and `g₂` to accuracy `2⁻ⁿ`.
- **How**: `Exists.choose` on `exists_blocApprox_pair` instantiated at `ε = (2⁻¹ : NNReal)^n`, whose positivity is `pow_pos (by norm_num)`.
- **Hypotheses**: `q₂ ≤ r ≤ q₁` with all exponents positive, and the matching condition `hmatch` — precisely the hypotheses of `exists_blocApprox_pair`.
- **Uses from project**: `exists_blocApprox_pair`, `Bloc`, `BIQ`, `biFstQ`, `biSndQ`
- **Used by**: `glueSeq_specL`, `glueSeq_specR`, `glueSeq_valued_le`, `biGlue`, `tendsto_glueSeq_biGlue`
- **Visibility**: public (`noncomputable`)
- **Lines**: 652–660 (body 3 lines)
- **Notes**: choice-based definition; its properties are only accessible through `glueSeq_specL`/`glueSeq_specR`

### `theorem glueSeq_specL`
- **Type**: `… (n : ℕ) : wI p F … (g₁ - BIProd … (glueSeq … n)) ≤ 2⁻¹ ^ n`
- **What**: The defining left-half property of `glueSeq`: at stage `n` the sequence approximates `g₁` in `B^{[q₁,r]}` to within `2⁻ⁿ` in the interval max-norm.
- **How**: Term-mode projection `(exists_blocApprox_pair … (pow_pos … n)).choose_spec.1` — the first conjunct of the specification of the chosen witness, with the same `ε` instantiation used in `glueSeq`.
- **Hypotheses**: same as `glueSeq` (`q₂ ≤ r ≤ q₁`, positivity, `hmatch`).
- **Uses from project**: `glueSeq`, `exists_blocApprox_pair`, `wI`, `BIProd`, `BIQ`, `hatK`, `biFstQ`, `biSndQ`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `glueSeq_valued_le`
- **Visibility**: public
- **Lines**: 662–676 (proof 2 lines, term mode)
- **Notes**: none

### `theorem glueSeq_specR`
- **Type**: `… (n : ℕ) : wI p F … (g₂ - BIProd … (glueSeq … n)) ≤ 2⁻¹ ^ n`
- **What**: The defining right-half property of `glueSeq`: the same sequence approximates `g₂` in `B^{[r,q₂]}` to within `2⁻ⁿ`.
- **How**: Term-mode `(exists_blocApprox_pair … ).choose_spec.2` — the second conjunct of the chosen witness's specification.
- **Hypotheses**: same as `glueSeq`.
- **Uses from project**: `glueSeq`, `exists_blocApprox_pair`, `wI`, `BIProd`, `BIQ`, `hatK`, `biFstQ`, `biSndQ`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `glueSeq_valued_le`
- **Visibility**: public
- **Lines**: 678–692 (proof 2 lines, term mode)
- **Notes**: none

### `theorem glueSeq_valued_le`
- **Type**: `… (n : ℕ) : v(BlocToHatK_{q₁}(glueSeq n) - biFstQ g₁) ≤ 2⁻¹^n ∧ v(BlocToHatK_{r}(glueSeq n) - biSndQ g₁) ≤ 2⁻¹^n ∧ v(BlocToHatK_{r}(glueSeq n) - biFstQ g₂) ≤ 2⁻¹^n ∧ v(BlocToHatK_{q₂}(glueSeq n) - biSndQ g₂) ≤ 2⁻¹^n`
- **What**: The per-coordinate (four-fold) form of the two max-norm approximation bounds: each of the four endpoint components — `q₁` and `r` from the left half, `r` and `q₂` from the right half — is within `2⁻ⁿ`.
- **How**: Unfold `wI` into a `max` in both `glueSeq_specL` and `glueSeq_specR`, flip the direction of each difference with `Valuation.map_sub_swap`, then read off the four bounds by `le_max_left`/`le_max_right` composed with `le_trans`.
- **Hypotheses**: same as `glueSeq`; plus the ultrametric structure making `wI` a max of two valuations.
- **Uses from project**: `glueSeq`, `glueSeq_specL`, `glueSeq_specR`, `wI`, `BlocToHatK`, `biFstQ`, `biSndQ`, `BIQ`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biGlue`, `tendsto_glueSeq_biGlue`, `biResQ'_biGlue_left`, `biResQ'_biGlue_right`
- **Visibility**: public
- **Lines**: 694–723 (proof 12 lines)
- **Notes**: the four conjuncts are addressed downstream as `.1`, `.2.1`, `.2.2.1`, `.2.2.2`

### `theorem glueSeq_eps_tendsto`
- **Type**: `Filter.Tendsto (fun n : ℕ => (2⁻¹ : NNReal) ^ n) Filter.atTop (nhds 0)`
- **What**: The chosen accuracy sequence `2⁻ⁿ` tends to `0` in `NNReal` — the null-sequence input required by the convergence criteria.
- **How**: `tendsto_pow_atTop_nhds_zero_of_lt_one` with `2⁻¹ < 1` discharged by `norm_num`.
- **Hypotheses**: none (the ambient variables are not even used).
- **Uses from project**: []
- **Used by**: `biGlue`, `tendsto_glueSeq_biGlue`, `biResQ'_biGlue_left`, `biResQ'_biGlue_right`
- **Visibility**: public
- **Lines**: 725–728 (proof 1 line, term mode)
- **Notes**: statement carries the section variables `p F ϖ` although they are unused

### `def biGlue`
- **Type**: `(q₁ q₂ r : ℚ) (h₁ h₂ hr) (hq₂r : q₂ ≤ r) (hrq₁ : r ≤ q₁) (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂)) (hmatch : biSndQ … g₁ = biFstQ … g₂) : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)`
- **What**: **The glued element** of a matching pair: the element of `B^{[q₁,q₂]}` whose two endpoint components are the two *outer* components `(biFstQ g₁, biSndQ g₂)`.
- **How**: Supply the pair together with a proof that it lies in the topological closure of the `BIProd`-range (which is the carrier of `BIQ`): `mem_closure_of_tendsto` applied to `tendsto_BIProd_of_valued_le` fed with the `q₁`- and `q₂`-bounds `(glueSeq_valued_le …).1` and `.2.2.2`, the null sequence `glueSeq_eps_tendsto`, and the trivial eventual-membership `Filter.Eventually.of_forall fun n => ⟨glueSeq … n, rfl⟩`.
- **Hypotheses**: `q₂ ≤ r ≤ q₁` with all exponents positive; the matching condition `hmatch` (needed to build `glueSeq` in the first place).
- **Uses from project**: `BIQ`, `hatK`, `biFstQ`, `biSndQ`, `glueSeq`, `glueSeq_valued_le`, `glueSeq_eps_tendsto`, `tendsto_BIProd_of_valued_le`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biGlue_coe`, `biGlue_fst`, `biGlue_snd`, `tendsto_glueSeq_biGlue`, `biResQ'_biGlue_left`, `biResQ'_biGlue_right`, `biResQ'_split_surjective`
- **Visibility**: public (`noncomputable`)
- **Lines**: 730–746 (body 10 lines)
- **Notes**: the membership proof is where the analytic work (`glueSeq`) enters the definition

### `theorem biGlue_coe`
- **Type**: `… : (biGlue … : hatK … × hatK …) = (biFstQ p F ϖ q₁ r h₁ hr g₁, biSndQ p F ϖ r q₂ hr h₂ g₂)`
- **What**: Unfolds the glued element to its underlying pair in the product of the two completed endpoint fields.
- **How**: `rfl` — `biGlue` is defined as a `Subtype.mk` on exactly this pair, so the coercion is definitional.
- **Hypotheses**: those of `biGlue` (`q₂ ≤ r ≤ q₁`, positivity, `hmatch`).
- **Uses from project**: `biGlue`, `biFstQ`, `biSndQ`, `hatK`, `BIQ`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biGlue_fst`, `biGlue_snd`
- **Visibility**: public
- **Lines**: 748–756 (proof `rfl`)
- **Notes**: none

### `theorem biGlue_fst`
- **Type**: `… : biFstQ p F ϖ q₁ q₂ h₁ h₂ (biGlue …) = biFstQ p F ϖ q₁ r h₁ hr g₁`
- **What**: The outer-left (`q₁`) component of the glued element is the outer-left component of `g₁`.
- **How**: `show` re-expresses `biFstQ` as `.1` of the underlying pair (definitional), then `rw [biGlue_coe]` replaces the pair by `(biFstQ g₁, biSndQ g₂)`.
- **Hypotheses**: those of `biGlue`.
- **Uses from project**: `biFstQ`, `biGlue`, `biGlue_coe`, `hatK`, `BIQ`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biResQ'_biGlue_left`
- **Visibility**: public
- **Lines**: 758–769 (proof 4 lines)
- **Notes**: none

### `theorem biGlue_snd`
- **Type**: `… : biSndQ p F ϖ q₁ q₂ h₁ h₂ (biGlue …) = biSndQ p F ϖ r q₂ hr h₂ g₂`
- **What**: The outer-right (`q₂`) component of the glued element is the outer-right component of `g₂`.
- **How**: `show` turns `biSndQ` into `.2` of the underlying pair and `rw [biGlue_coe]` finishes.
- **Hypotheses**: those of `biGlue`.
- **Uses from project**: `biSndQ`, `biGlue`, `biGlue_coe`, `hatK`, `BIQ`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biResQ'_biGlue_right`
- **Visibility**: public
- **Lines**: 771–782 (proof 4 lines)
- **Notes**: none

### `theorem tendsto_glueSeq_biGlue`
- **Type**: `… : Filter.Tendsto (fun n => blocToBI p F ϖ … (glueSeq … n)) Filter.atTop (nhds (biGlue …))`
- **What**: The approximating sequence, viewed inside `B^{[q₁,q₂]}`, actually converges to the glued element.
- **How**: `tendsto_subtype_rng.mpr` reduces convergence in the subtype `BIQ` to convergence of the underlying pairs in the product; that is supplied by `tendsto_BIProd_of_valued_le` with the `q₁`- and `q₂`-bounds `(glueSeq_valued_le …).1` / `.2.2.2` and the null sequence `glueSeq_eps_tendsto`.
- **Hypotheses**: those of `biGlue`.
- **Uses from project**: `blocToBI`, `glueSeq`, `glueSeq_valued_le`, `glueSeq_eps_tendsto`, `tendsto_BIProd_of_valued_le`, `biGlue`, `BIQ`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biResQ'_biGlue_left`, `biResQ'_biGlue_right`
- **Visibility**: public
- **Lines**: 784–799 (proof 6 lines, term mode)
- **Notes**: none

### `theorem biResQ'_biGlue_left`
- **Type**: `(q₁ q₂ r : ℚ) (h₁ h₂ hr) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) (g₁ g₂ hmatch) : biResQ' p F ϖ q₁ q₂ q₁ r … (biGlue …) = g₁`
- **What**: **The left restriction of the glued element is `g₁`** — half of the gluing statement.
- **How**: Apply the recognition criterion `biResQ'_eq_left_of_tendsto` with `f := biGlue` and `h := glueSeq`: its outer-component hypothesis is exactly `biGlue_fst`, its joint-convergence hypothesis is `tendsto_glueSeq_biGlue`, and its middle-convergence hypothesis follows from `tendsto_hatK_of_valued_le` applied to the second bound `(glueSeq_valued_le …).2.1` together with `glueSeq_eps_tendsto`.
- **Hypotheses**: exponents positive, `q₂ < q₁`, `q₂ ≤ r ≤ q₁` (destructured as `hrm.1`, `hrm.2` when feeding `biGlue`), and `hmatch`.
- **Uses from project**: `biResQ'`, `biResQ'_eq_left_of_tendsto`, `biGlue`, `biGlue_fst`, `tendsto_glueSeq_biGlue`, `tendsto_hatK_of_valued_le`, `glueSeq_valued_le`, `glueSeq_eps_tendsto`, `BIQ`, `biFstQ`, `biSndQ`
- **Used by**: `biResQ'_split_surjective`
- **Visibility**: public
- **Lines**: 801–814 (proof 7 lines, term mode)
- **Notes**: none

### `theorem biResQ'_biGlue_right`
- **Type**: `… : biResQ' p F ϖ q₁ q₂ r q₂ … (biGlue …) = g₂`
- **What**: **The right restriction of the glued element is `g₂`** — the other half of the gluing statement.
- **How**: Mirror of the previous lemma: `biResQ'_eq_right_of_tendsto` fed with `biGlue_snd` for the outer component, `tendsto_glueSeq_biGlue` for joint convergence, and `tendsto_hatK_of_valued_le` on the third bound `(glueSeq_valued_le …).2.2.1` with `glueSeq_eps_tendsto` for the middle component.
- **Hypotheses**: exponents positive, `q₂ < q₁`, `q₂ ≤ r ≤ q₁`, and `hmatch`.
- **Uses from project**: `biResQ'`, `biResQ'_eq_right_of_tendsto`, `biGlue`, `biGlue_snd`, `tendsto_glueSeq_biGlue`, `tendsto_hatK_of_valued_le`, `glueSeq_valued_le`, `glueSeq_eps_tendsto`, `BIQ`, `biFstQ`, `biSndQ`
- **Used by**: `biResQ'_split_surjective`
- **Visibility**: public
- **Lines**: 816–829 (proof 7 lines, term mode)
- **Notes**: none

### `theorem biResQ'_split_surjective`
- **Type**: `(q₁ q₂ r : ℚ) (h₁ h₂ hr) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) (g₁ g₂) (hmatch : biSndQ … g₁ = biFstQ … g₂) : ∃ f : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂), biResQ' … q₁ r … f = g₁ ∧ biResQ' … r q₂ … f = g₂`
- **What**: **Gluing (existence) half of the sheaf axiom**: every matching pair of half-interval elements arises as the pair of restrictions of a single element of `B^{[q₁,q₂]}`. Together with `biResQ'_split_injective` this is the split fiber-product theorem `B^{[q₁,q₂]} ≅ B^{[q₁,r]} ×_{\hat K_{|ϖ|^r}} B^{[r,q₂]}`.
- **How**: Anonymous constructor providing the witness `biGlue … g₁ g₂ hmatch` and the two identities `biResQ'_biGlue_left` and `biResQ'_biGlue_right`.
- **Hypotheses**: exponents positive; `q₂ < q₁`; `q₂ ≤ r ≤ q₁`; the matching condition `hmatch` at the split radius.
- **Uses from project**: `biGlue`, `biResQ'_biGlue_left`, `biResQ'_biGlue_right`, `biResQ'`, `BIQ`, `biFstQ`, `biSndQ`
- **Used by**: unused in file (exported; consumed by `FarguesFontaine/YPresheaf.lean`)
- **Visibility**: public
- **Lines**: 831–843 (proof 3 lines, term mode)
- **Notes**: none

### `theorem wI_coe_pow`
- **Type**: `(z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) (n : ℕ) : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 ((z ^ n : ↥(BISub …)) : hatK … × hatK …) = wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (z : hatK … × hatK …) ^ n`
- **What**: The interval norm `wI = max(v₁, v₂)` is **multiplicative on powers**: `wI(zⁿ) = (wI z)ⁿ` for `z` in the interval ring.
- **How**: Push the subring coercion through the power with `SubmonoidClass.coe_pow`, unfold `wI` to `max (v z.1 ^ n) (v z.2 ^ n)` using `map_pow` on each valuation, then split on which coordinate is larger via `le_total`; in each branch `max_eq_left`/`max_eq_right` identifies `wI z`, and `pow_le_pow_left'` shows the same coordinate still realizes the max after raising to the `n`-th power.
- **Hypotheses**: `0 < ρᵢ < 1` for both radii (ambient section variables); `z` an element of the interval ring `BISub`.
- **Uses from project**: `wI`, `BISub`, `hatK`
- **Used by**: `isPowerBounded_iff_wI_le_one`
- **Visibility**: public
- **Lines**: 852–879 (proof 21 lines)
- **Notes**: sits under the section-variable block introduced at line 849 (`{ρ₁ ρ₂ : NNReal} …`)

### `theorem isPowerBounded_iff_wI_le_one`
- **Type**: `(z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : TopologicalRing.IsPowerBounded z ↔ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 ((z : hatK p F hρ₁0 hρ₁1 × hatK p F hρ₂0 hρ₂1)) ≤ 1`
- **What**: **Power-boundedness in the interval ring is exactly the unit ball**: an element of `B^I` is power-bounded (its set of powers is bounded in the topological-ring sense) iff its interval norm is `≤ 1`, i.e. iff it lies in `BIPlusIn`. This is the substrate for identifying `B^{I,+}` with `(B^I)°`.
- **How**: (⇐) Given `wI z ≤ 1` and a neighbourhood `U` of `0` in the subtype, pull back to the product (`nhds_subtype_eq_comap`) and extract a `wI`-ball inside it with `exists_wI_ball_subset`; take that same ball as the bounding neighbourhood `V`, using submultiplicativity `wI_mul_le` and `wI_coe_pow` + `pow_le_one₀` to get `wI(zⁿ·v) ≤ 1·ε = ε`. (⇒) Contrapositive. If `wI z > 1`, then by `max_cases` one coordinate has valuation `> 1`. Boundedness against the unit-ball neighbourhood (built from `wI_ball_mem_nhds` pulled back by `continuous_subtype_val`) yields a neighbourhood `V` of `0`, and `NNReal.exists_pow_lt_of_lt_one` (with `max ρ₁ ρ₂ < 1`) gives `m` with `(max ρ₁ ρ₂)^m < ε`, so `y := pEltB^m ∈ V` — its coordinate values being `ρᵢ^m` by `valued_pImage_fst`/`valued_pImage_snd`. Then `pow_unbounded_of_one_lt` produces `n` with `v(z_i)^n > (ρᵢ^m)⁻¹`, forcing `v((zⁿ·y)_i) > 1` and contradicting `zⁿ·y` lying in the unit ball.
- **Hypotheses**: both radii `ρ₁, ρ₂ ∈ (0,1)` — positivity is used for `pow_ne_zero … hρᵢ0.ne'` in the blow-up step, and `ρᵢ < 1` for `NNReal.exists_pow_lt_of_lt_one` to find arbitrarily small `pEltB^m`; `z` in the interval ring.
- **Uses from project**: `BISub`, `hatK`, `wI`, `wI_coe_pow`, `wI_mul_le`, `wI_ball_mem_nhds`, `exists_wI_ball_subset`, `pEltB`, `pImage`, `valued_pImage_fst`, `valued_pImage_snd`, `TopologicalRing.IsPowerBounded` (`Adic spaces/Bounded.lean`)
- **Used by**: unused in file (exported; consumed by `FarguesFontaine/ChartVObj.lean`)
- **Visibility**: public
- **Lines**: 881–1025 (proof 137 lines)
- **Notes**: proof > 30 lines — the longest proof in the file; the two coordinate branches of the forward direction are structurally identical (decomposition candidate). Docstring mentions `BIPlusIn` although the statement is phrased as `wI ≤ 1` (the carrier condition of `BIPlusIn`).

---

### File Summary

- **Total declarations: 35** (4 defs — `biFstQ`, `biSndQ`, `glueSeq`, `biGlue`; 31 lemmas/theorems; 0 instances, 0 structures/classes/abbrevs)
- **Key API (used by 3+ others)**:
  - `biFstQ`, `biSndQ` (the two endpoint projections — appear in the statement of essentially everything after line 235)
  - `biFstQ_continuous`, `biSndQ_continuous` (3 uses each)
  - `biFstQ_blocToBI`, `biSndQ_blocToBI` (3 uses each — the dense-layer identities)
  - `exists_blocApprox_pair` (3 uses: `glueSeq`, `glueSeq_specL`, `glueSeq_specR`)
  - `tendsto_hatK_of_valued_le` (3 uses)
  - `glueSeq` (5 uses), `glueSeq_valued_le` (4), `glueSeq_eps_tendsto` (4)
  - `biGlue` (7 uses)
- **Unused declarations** (within this file — all four are the file's exported interface): `biSndQ_biResQ'_middle`, `biResQ'_split_injective`, `biResQ'_split_surjective` (all consumed by `Adic spaces/FarguesFontaine/YPresheaf.lean`), `isPowerBounded_iff_wI_le_one` (consumed by `Adic spaces/FarguesFontaine/ChartVObj.lean`)
- **Declarations with sorry**: none — the file is sorry-free
- **Declarations with set_option**: none — no heartbeat or recursion-depth bumps anywhere in the file
- **Proofs > 30 lines**:
  - `isPowerBounded_iff_wI_le_one` — 137 lines (881–1025)
  - `exists_blocApprox_pair` — 128 lines (392–540)
  - `exists_wLoc_split` — 83 lines (139–233)
  - `pow_mul_gaussValue_tail_le` — 33 lines (57–96)
  - `pow_mul_gaussValue_init_le` — 33 lines (98–137)
