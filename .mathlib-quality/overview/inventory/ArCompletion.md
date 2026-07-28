# Inventory: `projects/AdicSpaces/Adic spaces/FarguesFontaine/ArCompletion.lean`

File: 1787 lines. Namespace `FarguesFontaine`, `noncomputable section`, `universe u`.
Global variables: `(p : ℕ) [Fact p.Prime]`, `(F : Type u)` a perfectoid field of char `p` with
topological/uniform/nonarchimedean structure, and `(ϖ : PseudoUniformizer F)`.
Opens: `TopologicalRing ValuationSpectrum WittVector`.

---

### `theorem gaussVal_nonZeroDivisors_le_primeCompl`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : nonZeroDivisors (Ainf p F) ≤ (gaussVal p F hρ0 hρ1).supp.primeCompl`
- **What**: Every nonzerodivisor of `A_inf` lies outside the support of the Gauss valuation, i.e. the Gauss valuation is nonzero on nonzerodivisors.
- **How**: A nonzerodivisor is nonzero (`nonZeroDivisors.ne_zero`); membership in the support means the valuation vanishes (`Valuation.mem_supp_iff`), which contradicts strict positivity of `gaussValue` off zero (`gaussValue_pos_of_ne_zero`).
- **Hypotheses**: `0 < ρ < 1`; `A_inf` is a domain-like ring where `gaussValue` is positive off `0`.
- **Uses from project**: `gaussVal`, `gaussValue_pos_of_ne_zero`, `Ainf`
- **Used by**: `wK`
- **Visibility**: public
- **Lines**: 45–55 (proof ~8 lines)
- **Notes**: none

### `def wK`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Valuation (FractionRing (Ainf p F)) NNReal`
- **What**: The Gauss valuation `w_ρ` extended from `A_inf` to its fraction field `K = Frac(A_inf)`.
- **How**: `Valuation.extendToLocalization` applied to `gaussVal`, using `gaussVal_nonZeroDivisors_le_primeCompl` to see the localizing monoid avoids the support.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `gaussVal`, `gaussVal_nonZeroDivisors_le_primeCompl`, `Ainf`
- **Used by**: `wK_algebraMap`, `hatK`, `toHatK`, `valued_toHatK`
- **Visibility**: public
- **Lines**: 57–61
- **Notes**: none

### `theorem wK_algebraMap`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : Ainf p F) : wK p F hρ0 hρ1 (algebraMap (Ainf p F) (FractionRing (Ainf p F)) x) = gaussValue p F ρ x`
- **What**: The extended valuation `wK` agrees with `gaussValue` on the image of `A_inf`.
- **How**: Direct term-mode application of mathlib's `Valuation.extendToLocalization_apply_map_apply`.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `wK`, `gaussValue`, `Ainf`
- **Used by**: `valued_toHatK`
- **Visibility**: public
- **Lines**: 63–67
- **Notes**: `@[simp]`

### `abbrev hatK`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Type u`
- **What**: The ambient completed Gauss-valued field `K̂_ρ`, i.e. mathlib's valued-field completion of `(Frac(A_inf), wK)`.
- **How**: `(wK p F hρ0 hρ1).Completion` — mathlib's `Valuation.Completion` on the `WithVal` type synonym.
- **Hypotheses**: `0 < ρ < 1`; `wK` has trivial support so the completion is a field.
- **Uses from project**: `wK`
- **Used by**: `toHatK`, `AlocToHatK`, `ArSub`, `BlocToHatK`, `BrSub`, and essentially every subsequent declaration
- **Visibility**: public
- **Lines**: 69–71
- **Notes**: `abbrev` (reducible), so the `Valued` instance transfers automatically

### `def toHatK`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Ainf p F →+* hatK p F hρ0 hρ1`
- **What**: The canonical ring map `A_inf → K̂_ρ` factoring through `Frac(A_inf)`.
- **How**: Composition of `algebraMap (Ainf) (FractionRing …)`, the `WithVal.equiv` type-synonym transport, and `UniformSpace.Completion.coeRingHom`.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `hatK`, `wK`, `Ainf`
- **Used by**: `valued_toHatK`, `AlocToHatK`, `BlocToHatK`, `valued_AlocToHatK`
- **Visibility**: public
- **Lines**: 73–78
- **Notes**: none

### `theorem valued_toHatK`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : Ainf p F) : Valued.v (toHatK p F hρ0 hρ1 x) = gaussValue p F ρ x`
- **What**: The completion's valuation on the image of `x ∈ A_inf` is the Gauss value of `x`.
- **How**: Unfold `toHatK`, rewrite the composite as a literal `WithVal`-coercion into the completion so that `Valued.valuedCompletion_apply` (valuation on coerced elements) applies, then finish with `wK_algebraMap`.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `toHatK`, `wK`, `wK_algebraMap`, `gaussValue`, `Ainf`
- **Used by**: `AlocToHatK`, `BlocToHatK`, `valued_AlocToHatK`
- **Visibility**: public
- **Lines**: 80–93 (proof ~10 lines)
- **Notes**: `@[simp]`; uses a `show … from rfl` to force the coercion shape

### `abbrev Aloc`
- **Type**: `(p F ϖ) : Type u` — `Localization.Away (teichPi p F ϖ)`
- **What**: Kedlaya's `A_{L,E} = A_inf[1/[ϖ]]`, the localization of `A_inf` at the Teichmüller lift of a pseudo-uniformizer (decision AD-1).
- **How**: `Localization.Away (teichPi p F ϖ)`.
- **Hypotheses**: `ϖ` a pseudo-uniformizer of `F`.
- **Uses from project**: `teichPi`, `Ainf`
- **Used by**: nearly every subsequent declaration (`AlocToHatK`, `alocToWittF`, `wAloc`, `ArSub`, …)
- **Visibility**: public
- **Lines**: 97–98
- **Notes**: `abbrev`

### `def AlocToHatK`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Aloc p F ϖ →+* hatK p F hρ0 hρ1`
- **What**: The ring map realizing `A_inf[1/[ϖ]]` inside the completed field `K̂_ρ`.
- **How**: `IsLocalization.lift` of `toHatK`; the required invertibility is `isUnit_iff_ne_zero` in the field `hatK`, and nonvanishing of `Valued.v` on powers of `[ϖ]` follows from `valued_toHatK` plus `gaussValue_teichmuller` and `PseudoUniformizer.toOF_ne_zero`.
- **Hypotheses**: `0 < ρ < 1`; `hatK` is a field; `[ϖ]` has nonzero Gauss value.
- **Uses from project**: `Aloc`, `hatK`, `toHatK`, `valued_toHatK`, `gaussValue`, `gaussVal`, `teichPi`, `gaussValue_teichmuller`, `PseudoUniformizer.toOF_ne_zero`, `perfectoidValuation`
- **Used by**: `ArSub`, `valued_AlocToHatK`, and every later result about `A^r`
- **Visibility**: public
- **Lines**: 100–119 (proof-obligation ~15 lines)
- **Notes**: none

### `def ArSub`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Subring (hatK p F hρ0 hρ1)`
- **What**: `A^r` as a subring of the ambient completed field: the topological closure of the image of `Aloc` (Kedlaya Def 2.4, per the AD-3 refinement).
- **How**: `(AlocToHatK …).range.topologicalClosure`.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `AlocToHatK`, `hatK`
- **Used by**: `approxFilter`-based results, `gaussTermFhat_le_of_mem_ArSub`, `PhiHat_mem_ArSub`, `wAr`, `exists_gaussValueHat_eq_gaussTermFhat`, etc.
- **Visibility**: public
- **Lines**: 121–124
- **Notes**: none

### `def BlocToHatK`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Bloc p F ϖ →+* hatK p F hρ0 hρ1`
- **What**: The ring map realizing `Bloc = A_inf[1/(p·[ϖ])]` inside `K̂_ρ`.
- **How**: Same `IsLocalization.lift` pattern as `AlocToHatK`, with the nonvanishing supplied by `gaussValue_p_teichPi_ne_zero` and `pow_ne_zero`.
- **Hypotheses**: `0 < ρ < 1`; `p·[ϖ]` has nonzero Gauss value.
- **Uses from project**: `Bloc`, `hatK`, `toHatK`, `valued_toHatK`, `gaussValue`, `gaussVal`, `teichPi`, `gaussValue_p_teichPi_ne_zero`, `Ainf`
- **Used by**: `BrSub`
- **Visibility**: public
- **Lines**: 126–144 (proof-obligation ~13 lines)
- **Notes**: none

### `def BrSub`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Subring (hatK p F hρ0 hρ1)`
- **What**: `B^r` as a subring of `hatK`: the topological closure of the `Bloc`-image.
- **How**: `(BlocToHatK …).range.topologicalClosure`.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `BlocToHatK`, `hatK`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 146–148
- **Notes**: none

### `theorem isUnit_map_teichPi`
- **Type**: `IsUnit (WittVector.map ((powerBoundedSubring.toSubring F).subtype) (teichPi p F ϖ))`
- **What**: The image of `[ϖ]` in `W(F)` under the coefficientwise map `W(O_F) → W(F)` is a unit.
- **How**: Exhibit the explicit inverse `[ϖ⁻¹]`: `WittVector.map_teichmuller` turns the image into `teichmuller p ϖ`, then multiplicativity of `teichmuller` (`← map_mul`) plus `mul_inv_cancel₀` on the nonzero field element `ϖ` gives `= 1`; conclude with `Units.mkOfMulEqOne`.
- **Hypotheses**: `F` a field (so `ϖ ≠ 0` is invertible); `ϖ` a pseudo-uniformizer with nonzero image.
- **Uses from project**: `teichPi`, `PseudoUniformizer.toOF`, `powerBoundedSubring`, `OF`
- **Used by**: `alocToWittF`
- **Visibility**: public
- **Lines**: 150–165 (proof ~14 lines)
- **Notes**: none

### `def alocToWittF`
- **Type**: `Aloc p F ϖ →+* WittVector p F`
- **What**: The concrete embedding `A_{L,E} = A_inf[1/[ϖ]] → W(F)` (Kedlaya's `A_{L,E} ⊆ W(L)_E`, Def 2.2/2.4).
- **How**: `IsLocalization.lift` of the coefficientwise inclusion `WittVector.map (powerBoundedSubring.toSubring F).subtype`, using `isUnit_map_teichPi` (raised to the `k`-th power) to invert the powers of `[ϖ]`.
- **Hypotheses**: `[ϖ]` maps to a unit in `W(F)` (i.e. `isUnit_map_teichPi`).
- **Uses from project**: `Aloc`, `isUnit_map_teichPi`, `teichPi`, `powerBoundedSubring`
- **Used by**: `alocToWittF_algebraMap`, `gaussTermF_alocToWittF_le`, `gaussValueF_alocToWittF`, `alocTeich_wittF`, `gaussTermF_alocToWittF_decay`, and all coordinate arguments
- **Visibility**: public
- **Lines**: 167–177
- **Notes**: none

### `theorem alocToWittF_algebraMap`
- **Type**: `(x : Ainf p F) : alocToWittF p F ϖ (algebraMap (Ainf p F) (Aloc p F ϖ) x) = WittVector.map ((powerBoundedSubring.toSubring F).subtype) x`
- **What**: `alocToWittF` restricted to `A_inf` is the coefficientwise inclusion `W(O_F) → W(F)`.
- **How**: `IsLocalization.lift_eq`.
- **Hypotheses**: none beyond the ambient setup.
- **Uses from project**: `alocToWittF`, `Aloc`, `Ainf`, `powerBoundedSubring`
- **Used by**: `gaussTermF_alocToWittF_le`, `gaussValueF_alocToWittF`, `alocTeich_wittF`, `gaussTermF_alocToWittF_decay`
- **Visibility**: public
- **Lines**: 179–183
- **Notes**: `@[simp]`

### `theorem gaussVal_powers_teichPi_le_primeCompl`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Submonoid.powers (teichPi p F ϖ) ≤ (gaussVal p F hρ0 hρ1).supp.primeCompl`
- **What**: All powers `[ϖ]^k` avoid the support of the Gauss valuation.
- **How**: `map_pow` reduces to `gaussValue [ϖ] ≠ 0`, which is `gaussValue_teichmuller` plus `PseudoUniformizer.toOF_ne_zero` and `Valuation.zero_iff` for `perfectoidValuation`.
- **Hypotheses**: `0 < ρ < 1`; `ϖ ≠ 0`.
- **Uses from project**: `gaussVal`, `gaussValue`, `teichPi`, `gaussValue_teichmuller`, `PseudoUniformizer.toOF_ne_zero`, `perfectoidValuation`
- **Used by**: `wAloc`
- **Visibility**: public
- **Lines**: 185–197 (proof ~9 lines)
- **Notes**: none

### `def wAloc`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Valuation (Aloc p F ϖ) NNReal`
- **What**: The Gauss valuation extended from `A_inf` to `Aloc = A_inf[1/[ϖ]]` (the mirror of `wLoc`).
- **How**: `Valuation.extendToLocalization` of `gaussVal` along `gaussVal_powers_teichPi_le_primeCompl`.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `gaussVal`, `gaussVal_powers_teichPi_le_primeCompl`, `Aloc`
- **Used by**: essentially all dense-layer estimates: `wAloc_algebraMap`, `gaussTermF_alocToWittF_le`, `gaussValueF_alocToWittF`, `valued_AlocToHatK`, `approx*`, `exists_finite_teichmuller_sum_close`, `alocPrefix_*`, `wAloc_p_smul`, …
- **Visibility**: public
- **Lines**: 199–202
- **Notes**: none

### `theorem wAloc_algebraMap`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : Ainf p F) : wAloc p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Aloc p F ϖ) x) = gaussValue p F ρ x`
- **What**: `wAloc` agrees with `gaussValue` on the image of `A_inf`.
- **How**: `Valuation.extendToLocalization_apply_map_apply`.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `wAloc`, `gaussValue`, `Aloc`, `Ainf`
- **Used by**: `gaussTermF_alocToWittF_le`, `gaussValueF_alocToWittF`, `valued_AlocToHatK`, `alocTeich_value`, `alocPrefix_value`, `wAloc_p_smul`, and more
- **Visibility**: public
- **Lines**: 204–208
- **Notes**: `@[simp]`

### `theorem gaussTermF_alocToWittF_le`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : Aloc p F ϖ) (n : ℕ) : gaussTermF p F ρ (alocToWittF p F ϖ u) n ≤ wAloc p F ϖ hρ0 hρ1 u`
- **What**: Each Gauss term `|u_n|·ρ^n` of the `W(F)`-realization of `u ∈ Aloc` is bounded by the extended Gauss valuation of `u` (half of Kedlaya (2.2.1) on the dense layer).
- **How**: Write `u·[ϖ]^k = a` with `a ∈ A_inf` via `IsLocalization.surj`; the Teichmüller-multiplication formula `gaussTermF_teichmuller_mul` shows terms scale by `c^k` (where `c = |ϖ|`), and `wAloc` scales the same way, so the `A_inf`-bound `gaussTerm_le_gaussValue` transfers after cancelling `c^k > 0` (`le_of_mul_le_mul_right`).
- **Hypotheses**: `0 < ρ < 1`; `ϖ ≠ 0` so `c > 0`; `gaussTerm ≤ gaussValue` on `A_inf`.
- **Uses from project**: `gaussTermF`, `alocToWittF`, `alocToWittF_algebraMap`, `wAloc`, `wAloc_algebraMap`, `gaussValue`, `gaussVal`, `gaussTerm`, `gaussTerm_le_gaussValue`, `gaussValue_teichmuller`, `gaussTermF_teichmuller_mul`, `gaussTermF_map`, `teichPi`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `perfectoidValuation`, `Aloc`, `Ainf`, `powerBoundedSubring`, `OF`
- **Used by**: `bddAbove_gaussTermF_alocToWittF`, `gaussValueF_alocToWittF`
- **Visibility**: public
- **Lines**: 210–263 (proof ~50 lines)
- **Notes**: proof >30 lines — decompose candidate (shares the `u·[ϖ]^k = a` setup with `gaussValueF_alocToWittF`)

### `theorem bddAbove_gaussTermF_alocToWittF`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : Aloc p F ϖ) : BddAbove (Set.range (gaussTermF p F ρ (alocToWittF p F ϖ u)))`
- **What**: The Gauss-term sequence of an `Aloc`-image in `W(F)` is bounded above (so its `⨆` is meaningful).
- **How**: Take `wAloc u` as the explicit bound, supplied termwise by `gaussTermF_alocToWittF_le`.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `gaussTermF`, `alocToWittF`, `wAloc`, `gaussTermF_alocToWittF_le`, `Aloc`
- **Used by**: `gaussValueF_alocToWittF`
- **Visibility**: public
- **Lines**: 265–271
- **Notes**: none

### `theorem gaussValueF_alocToWittF`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : Aloc p F ϖ) : gaussValueF p F ρ (alocToWittF p F ϖ u) = wAloc p F ϖ hρ0 hρ1 u`
- **What**: The `W(F)`-Gauss value (sup of terms) of an `Aloc`-image equals the extended Gauss valuation `wAloc u` — the realization equality on the dense layer, including attainment of the sup.
- **How**: `≤` is `ciSup_le` of `gaussTermF_alocToWittF_le`. For `≥`, again write `u·[ϖ]^k = a`; if `wAloc u = 0` it's trivial, else `a ≠ 0` so `exists_gaussValue_eq_gaussTerm` attains the `A_inf`-sup at some `n₀`; transferring by the `c^k`-scaling (`gaussTermF_teichmuller_mul`, `mul_right_cancel₀`) gives `wAloc u = gaussTermF … n₀`, and `le_ciSup` (with `bddAbove_gaussTermF_alocToWittF`) closes it.
- **Hypotheses**: `0 < ρ < 1`; sup attainment on `A_inf` (`exists_gaussValue_eq_gaussTerm`); `c = |ϖ| > 0`.
- **Uses from project**: `gaussValueF`, `alocToWittF`, `alocToWittF_algebraMap`, `wAloc`, `wAloc_algebraMap`, `gaussTermF_alocToWittF_le`, `bddAbove_gaussTermF_alocToWittF`, `exists_gaussValue_eq_gaussTerm`, `gaussValue`, `gaussVal`, `gaussValue_zero`, `gaussValue_teichmuller`, `gaussTerm`, `gaussTermF`, `gaussTermF_teichmuller_mul`, `gaussTermF_map`, `teichPi`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `perfectoidValuation`, `Aloc`, `Ainf`, `powerBoundedSubring`, `OF`
- **Used by**: `alocTeich_value`, `alocPrefix_value`, `wAloc_p_smul`, `gaussTermF_alocToWittF_decay`
- **Visibility**: public
- **Lines**: 273–341 (proof ~63 lines)
- **Notes**: proof >30 lines — decompose candidate; duplicates the surjectivity/scaling preamble of `gaussTermF_alocToWittF_le`

### `theorem valued_AlocToHatK`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : Aloc p F ϖ) : Valued.v (AlocToHatK p F ϖ hρ0 hρ1 u) = wAloc p F ϖ hρ0 hρ1 u`
- **What**: The valuation of the completed Gauss-valued field `hatK` restricts along `AlocToHatK` to the extended Gauss valuation `wAloc` on `Aloc = A_inf[1/[ϖ]]`.
- **How**: Write `u·y = a` with `a ∈ A_inf`, `y` a power of `[ϖ]` (`IsLocalization.surj`); `gaussValue y ≠ 0` because `gaussValue_teichmuller` and `PseudoUniformizer.toOF_ne_zero` make it a nonzero power. Both sides multiplied by `gaussValue y` equal `gaussValue a` (via `IsLocalization.lift_eq`, `valued_toHatK`, `wAloc_algebraMap`), so `mul_right_cancel₀` concludes.
- **Hypotheses**: `0 < ρ < 1`; `ϖ` a pseudo-uniformizer so `[ϖ]` has nonzero Gauss value.
- **Uses from project**: `AlocToHatK`, `wAloc`, `wAloc_algebraMap`, `toHatK`, `valued_toHatK`, `gaussValue`, `gaussVal`, `gaussValue_teichmuller`, `teichPi`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `perfectoidValuation`, `Aloc`, `Ainf`
- **Used by**: `eventually_pair_wAloc_le`, `eventually_wAloc_eq`, `cauchySeq_prefix_image`, `valued_PhiHatK`, `tendsto_gaussTerm_teichCoeffAr`, `PhiHatK_teichCoeffAr`
- **Visibility**: public
- **Lines**: 344–374 (proof ~29 lines)
- **Notes**: none

### `def teichCoeffAr`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : hatK p F hρ0 hρ1) (n : ℕ) : F`
- **What**: The `n`-th Teichmüller coordinate of a point of the completion, defined as the limit of the coordinates `teichCoeffF (alocToWittF u) n` along the filter of `Aloc`-approximants of `x`. Junk value off the closure `ArSub`.
- **How**: Definition — `Filter.limUnder` of the coordinate function along `Filter.comap (AlocToHatK …) (nhds x)`.
- **Hypotheses**: `0 < ρ < 1`; meaningful only when the comap filter is `NeBot` and the coordinate function converges (see `tendsto_teichCoeffAr`).
- **Uses from project**: `hatK`, `AlocToHatK`, `alocToWittF`, `teichCoeffF`, `Aloc`
- **Used by**: `tendsto_teichCoeffAr`, `gaussTerm_teichCoeffAr_le`, `PhiHatK_teichCoeffAr`, `valued_eq_iSup_teichCoeffAr`, `wAr`, `teichCoeffAr_PhiHatK`, `teichCoeffAr_zero`, and more
- **Visibility**: public
- **Lines**: 378–381
- **Notes**: noncomputable (whole file `noncomputable section`); uses `Classical` choice implicitly through `limUnder`

### `theorem ball_mem_nhds_zero`
- **Type**: `(m : ℕ) : {z : F | perfectoidValuation p F z ≤ (perfectoidValuation p F ↑(PseudoUniformizer.toOF F ϖ)) ^ m} ∈ nhds (0 : F)`
- **What**: In the perfectoid field `F`, the closed valuation ball of radius `c^m` (with `c = |ϖ|`) is a neighbourhood of `0`.
- **How**: The set `ϖ^m · O_F` is open, since multiplication by the unit `ϖ^m` is an open map (`IsUnit.isOpenMap_smul`) and `O_F = powerBoundedSubring F` is open in a Huber ring (`IsHuberRing.exists_pairOfDefinition`, `PairOfDefinition.isOpen_powerBoundedSubring`); it contains `0` and lands inside the ball because `perfectoidValuation_le_one` bounds power-bounded elements by `1`.
- **Hypotheses**: `F` a perfectoid (hence Huber) field; `ϖ` a pseudo-uniformizer (a unit of `F`).
- **Uses from project**: `perfectoidValuation`, `perfectoidValuation_le_one`, `PseudoUniformizer.toOF`, `powerBoundedSubring`, `isPowerBounded_zero`, `IsHuberRing.exists_pairOfDefinition`, `OF`
- **Used by**: `isClosed_ball`, `PhiHatK_teichCoeffAr`
- **Visibility**: public
- **Lines**: 385–405 (proof ~19 lines)
- **Notes**: none

### `theorem exists_ball_subset_nhds`
- **Type**: `{V : Set F} (hV : V ∈ nhds (0 : F)) : ∃ m : ℕ, {z | perfectoidValuation p F z ≤ (perfectoidValuation p F ↑(PseudoUniformizer.toOF F ϖ)) ^ m} ⊆ V`
- **What**: Converse of `ball_mem_nhds_zero`: every neighbourhood of `0` in `F` contains a closed valuation ball `{|z| ≤ c^m}`. Together the two say the valuation balls are a neighbourhood basis at `0`.
- **How**: Shrink `V` to an open subgroup `G` (`NonarchimedeanAddGroup.is_nonarchimedean`); boundedness of the power-bounded subring in a uniform ring (`IsUniform.isBounded_powerBounded`) gives `W` with `W·O_F ⊆ G`, and topological nilpotence of `ϖ` (`PseudoUniformizer.isTopologicallyNilpotent`) puts `ϖ^N ∈ W`. Then `|z| ≤ c^N` forces `z·ϖ^{-N} ∈ O_F` by `Valuation.Integers.exists_of_le_one`, so `z = (z·ϖ^{-N})·ϖ^N ∈ O_F·W ⊆ G ⊆ V`.
- **Hypotheses**: `F` perfectoid, uniform, nonarchimedean; `ϖ` a topologically nilpotent unit.
- **Uses from project**: `perfectoidValuation`, `perfectoidValuation_integers`, `PseudoUniformizer.toOF`, `PseudoUniformizer.isTopologicallyNilpotent`, `IsPerfectoidRing.uniform`, `IsUniform.isBounded_powerBounded`, `powerBoundedSubring`, `OF`
- **Used by**: `tendsto_teichCoeffAr`
- **Visibility**: public
- **Lines**: 409–437 (proof ~27 lines)
- **Notes**: none

### `theorem neBot_comap_of_mem_ArSub`
- **Type**: `{ρ} {hρ0 hρ1} {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) : (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x)).NeBot`
- **What**: For `x` in the closed subring `A^r` (the closure of the image of `Aloc`), the filter of `Aloc`-approximants of `x` is nontrivial, so limits along it are meaningful.
- **How**: `Filter.comap_neBot_iff` reduces to meeting every neighbourhood of `x`; since `ArSub` is by definition the topological closure of `Set.range (AlocToHatK …)`, `mem_closure_iff_nhds` produces a point of the range in each such neighbourhood.
- **Hypotheses**: `x ∈ ArSub` (i.e. `x` lies in the closure of the `Aloc`-image).
- **Uses from project**: `ArSub`, `AlocToHatK`, `hatK`
- **Used by**: `exists_eventually_wAloc_le`, `tendsto_teichCoeffAr`, `gaussTerm_teichCoeffAr_le`, `tendsto_gaussTerm_teichCoeffAr`, `PhiHatK_teichCoeffAr`
- **Visibility**: public
- **Lines**: 440–454 (proof ~13 lines)
- **Notes**: none

### `theorem eventually_pair_wAloc_le`
- **Type**: `{ρ} {hρ0 hρ1} (x : hatK p F hρ0 hρ1) {ε : NNReal} (hε : 0 < ε) : ∀ᶠ q in (comap (AlocToHatK …) (nhds x)) ×ˢ (comap (AlocToHatK …) (nhds x)), wAloc p F ϖ hρ0 hρ1 (q.2 - q.1) ≤ ε`
- **What**: Any two approximants of a point `x ∈ hatK` are eventually within `ε` of each other for `wAloc` — the Cauchy property of the approximant filter, expressed in the ground valuation rather than in the completion's value group.
- **How**: Pick `N` with `ρ^N < ε` (`exists_pow_lt_of_lt_one`) and use the test element `z₀ = toHatK (p^N)`, whose value is `ρ^N` by `gaussValue_p_mul`/`gaussValue_one`. The uniformity basis `Valued.hasBasis_uniformity` at the unit `γ = Units.mk0 ((Valued.v).restrict z₀)` plus `cauchy_nhds` gives eventual `restrict`-smallness of differences; `Valuation.restrict_lt_iff` converts it to `Valued.v (…) < Valued.v z₀`, and `valued_AlocToHatK` transports it to `wAloc (u' - u) < ρ^N ≤ ε`.
- **Hypotheses**: `0 < ρ < 1` (so `ρ^N → 0`); `0 < ε`; nothing about `x` beyond membership in the completion.
- **Uses from project**: `AlocToHatK`, `valued_AlocToHatK`, `toHatK`, `valued_toHatK`, `wAloc`, `gaussValue`, `gaussVal`, `gaussValue_p_mul`, `gaussValue_one`, `hatK`, `Ainf`, `Aloc`
- **Used by**: `exists_eventually_wAloc_le`, `tendsto_teichCoeffAr`
- **Visibility**: public
- **Lines**: 459–523 (proof ~59 lines)
- **Notes**: proof >30 lines — decompose candidate (the `γ`/`restrict` value-group plumbing is separable from the `ρ^N < ε` bookkeeping)

### `theorem exists_eventually_wAloc_le`
- **Type**: `{ρ} {hρ0 hρ1} {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) : ∃ B : NNReal, ∀ᶠ u in comap (AlocToHatK …) (nhds x), wAloc p F ϖ hρ0 hρ1 u ≤ B`
- **What**: The approximants of a point of `A^r` eventually have uniformly bounded Gauss value — the value scale needed before any coordinatewise estimate.
- **How**: Apply `eventually_pair_wAloc_le` with `ε = 1` and split the product-eventually into two one-sided sets (`Filter.eventually_prod_iff`); fix one witness `u₀` from the nonempty filter (`neBot_comap_of_mem_ArSub`), then the ultrametric inequality `Valuation.map_add` on `u = (u - u₀) + u₀` bounds every later `u` by `max (wAloc u₀) 1`.
- **Hypotheses**: `x ∈ ArSub` (so the approximant filter is `NeBot`); `0 < ρ < 1`.
- **Uses from project**: `neBot_comap_of_mem_ArSub`, `eventually_pair_wAloc_le`, `wAloc`, `AlocToHatK`, `ArSub`, `hatK`, `Aloc`
- **Used by**: `tendsto_teichCoeffAr`
- **Visibility**: public
- **Lines**: 526–549 (proof ~22 lines)
- **Notes**: none

### `theorem tendsto_teichCoeffAr`
- **Type**: `{ρ} {hρ0 hρ1} {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (n : ℕ) : Tendsto (fun u => teichCoeffF p F (alocToWittF p F ϖ u) n) (comap (AlocToHatK …) (nhds x)) (nhds (teichCoeffAr p F ϖ hρ0 hρ1 x n))`
- **What**: For `x ∈ A^r` the `n`-th Teichmüller coordinate of the approximants actually converges in `F`, and its limit is the value assigned by `teichCoeffAr` — so the junk-value definition is genuinely a coordinate function on `A^r`.
- **How**: Show the pushed-forward coordinate filter is Cauchy and use completeness of `F` (`IsPerfectoidRing.complete`, `T0Space`), then `Tendsto.limUnder_eq` identifies the limit with `teichCoeffAr`. Cauchyness: fix a ball `{|z| ≤ c^m}` inside a given entourage (`exists_ball_subset_nhds`, `uniformity_eq_comap_nhds_zero`), get the modulus `δ` from `exists_delta_teichCoeffF_sub` at the value scale `B ≤ c^{-M}` (from `exists_eventually_wAloc_le`), and feed it pairs supplied by `eventually_pair_wAloc_le` at `ε = δ`, converting `wAloc` bounds into `gaussValueF` bounds by `gaussValueF_alocToWittF` and `bddAbove_gaussTermF_alocToWittF`.
- **Hypotheses**: `x ∈ ArSub`; `F` complete, `T0`, uniform additive group, perfectoid; `0 < ρ < 1`.
- **Uses from project**: `teichCoeffAr`, `teichCoeffF`, `alocToWittF`, `AlocToHatK`, `ArSub`, `neBot_comap_of_mem_ArSub`, `exists_eventually_wAloc_le`, `eventually_pair_wAloc_le`, `exists_ball_subset_nhds`, `exists_delta_teichCoeffF_sub`, `gaussValueF_alocToWittF`, `bddAbove_gaussTermF_alocToWittF`, `wAloc`, `perfectoidValuation`, `perfectoidValuation_toOF_lt_one`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `IsPerfectoidRing.complete`, `IsPerfectoidRing.t0`, `IsPerfectoidRing.uniformAddGroup`, `IsPerfectoidRing.topologyEq`, `OF`, `Aloc`, `hatK`
- **Used by**: `gaussTerm_teichCoeffAr_le`, `PhiHatK_teichCoeffAr`, `teichCoeffAr_PhiHatK`, `tendsto_gaussTerm_teichCoeffAr`
- **Visibility**: public
- **Lines**: 554–632 (proof ~74 lines)
- **Notes**: proof >30 lines — decompose candidate (the `B ≤ c⁻¹^M` scale extraction and the Cauchy argument are independent blocks)

### `theorem eventually_wAloc_eq`
- **Type**: `{ρ} {hρ0 hρ1} {x : hatK p F hρ0 hρ1} (hx : Valued.v x ≠ 0) : ∀ᶠ u in comap (AlocToHatK …) (nhds x), wAloc p F ϖ hρ0 hρ1 u = Valued.v x`
- **What**: For a nonzero-valued point of the completion, the approximants eventually have value exactly `Valued.v x` — ultrametric constancy of the valuation on small balls.
- **How**: The ball `{z | (Valued.v).restrict (z - x) < γ}` with `γ = Units.mk0 ((Valued.v).restrict x)` is a neighbourhood of `x` (`Valued.mem_nhds`); on it `Valuation.restrict_lt_iff` gives `v(z - x) < v x`, and two applications of the ultrametric `Valuation.map_add` (to `z = (z-x)+x` and `x = (x-z)+z`, using `Valuation.map_neg`) force `v z = v x`. Transport to `wAloc` by `valued_AlocToHatK`.
- **Hypotheses**: `Valued.v x ≠ 0`; `0 < ρ < 1`.
- **Uses from project**: `valued_AlocToHatK`, `AlocToHatK`, `wAloc`, `hatK`, `Aloc`
- **Used by**: `gaussTerm_teichCoeffAr_le`
- **Visibility**: public
- **Lines**: 637–679 (proof ~40 lines)
- **Notes**: proof >30 lines — decompose candidate; shares the `γ = Units.mk0 (restrict …)` preamble with `eventually_pair_wAloc_le`. Contains `push Not` (line 666)

### `theorem isClosed_ball`
- **Type**: `{r : NNReal} (hr : 0 < r) : IsClosed {y : F | perfectoidValuation p F y ≤ r}`
- **What**: Closed valuation balls of positive radius in the perfectoid field `F` are topologically closed (in fact clopen).
- **How**: The ball is an additive subgroup (ultrametric `Valuation.map_add` plus `Valuation.map_neg`); it is open because it contains the ball of radius `c^m` for `c^m < r` (`exists_pow_lt_of_lt_one`, `ball_mem_nhds_zero`), so `AddSubgroup.isOpen_of_mem_nhds` applies, and an open subgroup of a topological group is closed (`AddSubgroup.isClosed_of_isOpen`).
- **Hypotheses**: `0 < r`; `ϖ` a pseudo-uniformizer (`include ϖ`), used only to produce a small radius `c^m`.
- **Uses from project**: `perfectoidValuation`, `perfectoidValuation_toOF_lt_one`, `ball_mem_nhds_zero`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `OF`
- **Used by**: `gaussTerm_teichCoeffAr_le`, `tendsto_gaussTerm_teichCoeffAr`
- **Visibility**: public
- **Lines**: 684–708 (proof ~23 lines); `include ϖ` on line 681
- **Notes**: none

### `theorem gaussTerm_teichCoeffAr_le`
- **Type**: `{ρ} {hρ0 hρ1} {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : Valued.v x ≠ 0) (n : ℕ) : ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n) ≤ Valued.v x`
- **What**: Kedlaya's term bound (2.2.1) transferred to the completion `A^r`: each Gauss term `ρ^n·|x_n|` of the limit coordinates is at most the completed-field value of `x`.
- **How**: Set `r = v(x)·(ρ^n)⁻¹`. By `eventually_wAloc_eq` the approximants eventually have `wAloc u = v x`, and `gaussTermF_alocToWittF_le` then puts each approximant coordinate inside the ball `{s ≤ r}`; that ball is closed (`isClosed_ball`), so `IsClosed.mem_of_tendsto` with `tendsto_teichCoeffAr` passes the bound to the limit coordinate, and multiplying back by `ρ^n` gives the claim.
- **Hypotheses**: `x ∈ ArSub` and `Valued.v x ≠ 0` (the latter to make `r` positive and `eventually_wAloc_eq` applicable); `0 < ρ < 1`.
- **Uses from project**: `teichCoeffAr`, `tendsto_teichCoeffAr`, `eventually_wAloc_eq`, `gaussTermF_alocToWittF_le`, `gaussTermF`, `isClosed_ball`, `neBot_comap_of_mem_ArSub`, `teichCoeffF`, `alocToWittF`, `AlocToHatK`, `ArSub`, `perfectoidValuation`, `hatK`
- **Used by**: unused in file (exported term bound; the value formula reaches the same statement via `valued_PhiHatK`)
- **Visibility**: public
- **Lines**: 712–742 (proof ~29 lines)
- **Notes**: none

### `def alocTeich`
- **Type**: `(c : F) : Aloc p F ϖ`
- **What**: The Teichmüller lift of an arbitrary element `c ∈ F` (not just of `O_F`) into `Aloc = A_inf[1/[ϖ]]`, obtained by absorbing `c` into `O_F` with a power of `ϖ` and dividing back.
- **How**: Definition — `IsLocalization.mk'` of `teichmuller p (c·ϖ^k)` over the denominator `[ϖ]^k ∈ Submonoid.powers (teichPi p F ϖ)`, where `k` is the Tate-absorption exponent supplied by `exists_mul_pow_isPowerBounded`.
- **Hypotheses**: `ϖ` a pseudo-uniformizer of the perfectoid field `F`; uses `Exists.choose` on `exists_mul_pow_isPowerBounded`.
- **Uses from project**: `Aloc`, `teichPi`, `exists_mul_pow_isPowerBounded`, `OF`, `powerBoundedSubring`
- **Used by**: `alocToWittF_alocTeich`, `wAloc_alocTeich`, `exists_finite_teichmuller_sum_close`, `prefixAloc`
- **Visibility**: public
- **Lines**: 746–753
- **Notes**: noncomputable; the exponent is a `choose`, so only `alocToWittF_alocTeich` / `wAloc_alocTeich` should be used downstream, never the definition

### `theorem alocToWittF_alocTeich`
- **Type**: `(c : F) : alocToWittF p F ϖ (alocTeich p F ϖ c) = WittVector.teichmuller p c`
- **What**: `alocTeich c` really is the Teichmüller lift of `c`: its image in `W(F)` is `[c]`.
- **How**: Multiply by the denominator (`IsLocalization.mk'_spec`) and push through `alocToWittF` using `alocToWittF_algebraMap`; `WittVector.map_teichmuller` rewrites both sides as Teichmüller lifts, and since `[ϖ^k]` is a unit in `W(F)` (its inverse is `[(ϖ^k)⁻¹]`, `F` a field) `IsUnit.mul_right_cancel` removes it.
- **Hypotheses**: `F` a field so `ϖ^k ≠ 0` is invertible; `ϖ` a pseudo-uniformizer.
- **Uses from project**: `alocTeich`, `alocToWittF`, `alocToWittF_algebraMap`, `teichPi`, `PseudoUniformizer.toOF`, `exists_mul_pow_isPowerBounded`, `powerBoundedSubring`, `Ainf`, `Aloc`, `OF`
- **Used by**: `alocToWittF_prefixAloc`, `exists_finite_teichmuller_sum_close`
- **Visibility**: public
- **Lines**: 756–798 (proof ~41 lines)
- **Notes**: proof >30 lines — decompose candidate (the `hyW`/`haW` `WittVector.map`-of-Teichmüller computations are reusable helpers); shares its `k`/`a`/`y` preamble with `wAloc_alocTeich`

### `theorem wAloc_alocTeich`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (c : F) : wAloc p F ϖ hρ0 hρ1 (alocTeich p F ϖ c) = perfectoidValuation p F c`
- **What**: The Gauss value of the generalized Teichmüller lift `alocTeich c` is exactly `|c|` — Teichmüller lifts are isometric for `wAloc`.
- **How**: Same `IsLocalization.mk'_spec` multiplication as `alocToWittF_alocTeich`, but evaluated with `wAloc_algebraMap`; `gaussValue_teichmuller` computes both `gaussValue [ϖ]^k = c_ϖ^k` and `gaussValue [c·ϖ^k] = |c|·c_ϖ^k`, and `mul_right_cancel₀` with `c_ϖ^k > 0` gives the result.
- **Hypotheses**: `0 < ρ < 1`; `ϖ ≠ 0` so `c_ϖ = |ϖ| > 0`.
- **Uses from project**: `alocTeich`, `wAloc`, `wAloc_algebraMap`, `gaussValue`, `gaussVal`, `gaussValue_teichmuller`, `teichPi`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `perfectoidValuation`, `exists_mul_pow_isPowerBounded`, `Ainf`, `Aloc`, `OF`
- **Used by**: unused in file (exported isometry statement for Teichmüller lifts)
- **Visibility**: public
- **Lines**: 801–832 (proof ~30 lines)
- **Notes**: shares the `k`/`a`/`y`/`mk'_spec` preamble with `alocToWittF_alocTeich` — joint decompose candidate

### `theorem exists_finite_teichmuller_sum_close`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : Aloc p F ϖ) {ε : NNReal} (hε : 0 < ε) : ∃ (N : ℕ) (b : ℕ → F), wAloc p F ϖ hρ0 hρ1 (u - ∑ n ∈ Finset.range N, (p : Aloc p F ϖ) ^ n * alocTeich p F ϖ (b n)) ≤ ε`
- **What**: **Density of finite Teichmüller sums in `Aloc`**: every `u ∈ A_inf[1/[ϖ]]` is approximated to within `ε` in the Gauss valuation by a finite sum `Σ_{n<N} pⁿ·[bₙ]` with `bₙ ∈ F`. This is the statement that makes `A^r` the completion of the span of the `pⁿ[b]`.
- **How**: Four stages. (i) Write `u·[ϖ]^k = A` with `A ∈ A_inf` (`IsLocalization.surj` plus `Submonoid.powers`), and choose `N` with `ρ^N < ε·c_ϖ^k` (`exists_pow_lt_of_lt_one`); define `bₙ = teichCoeff A n / ϖ^k`, so the denominator is absorbed into the coefficients. (ii) Compute the `W(F)`-image of `u` and of the finite sum `t` after multiplying by `[ϖ^k]`: `himgu` uses `alocToWittF_algebraMap` + `WittVector.map_teichmuller`, and `himgt` uses `alocToWittF_alocTeich` termwise. (iii) Subtract: `exists_eq_sum_teichCoeff_add` splits `A` as its length-`N` Teichmüller prefix plus `p^N·z` with `z ∈ A_inf`, so `alocToWittF (u - t)·[ϖ^k] = p^N · map z`. (iv) Value the identity: `gaussValueF_teichmuller_mul` extracts the factor `c_ϖ^k`, and an induction on the exponent (using `gaussValueF_p_mul` and `bddAbove_gaussTermF_p_mul`, based at `gaussValue_le_one`/`gaussTerm_le_one`) shows `gaussValueF (p^N · map z) ≤ ρ^N`; `gaussValueF_alocToWittF` returns this to `wAloc`, and `le_of_mul_le_mul_right` cancels `c_ϖ^k > 0`.
- **Hypotheses**: `0 < ρ < 1` (so `ρ^N → 0`); `0 < ε`; `ϖ ≠ 0` so `c_ϖ = |ϖ| > 0`; `F` a field so `ϖ^k` is invertible (used to define `b`).
- **Uses from project**: `wAloc`, `alocTeich`, `alocToWittF`, `alocToWittF_algebraMap`, `alocToWittF_alocTeich`, `teichCoeff`, `exists_eq_sum_teichCoeff_add`, `gaussValueF`, `gaussValueF_alocToWittF`, `gaussValueF_teichmuller_mul`, `gaussValueF_p_mul`, `gaussValueF_map`, `gaussTermF`, `gaussTermF_map`, `gaussTerm_le_one`, `gaussValue_le_one`, `bddAbove_gaussTermF_p_mul`, `teichPi`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `perfectoidValuation`, `powerBoundedSubring`, `Ainf`, `Aloc`, `OF`
- **Used by**: unused in file (density input consumed downstream / by later files)
- **Visibility**: public
- **Lines**: 837–964 (proof ~124 lines)
- **Notes**: **decompose-proof candidate** — four separable blocks: the `u·[ϖ]^k = A` localization preamble, `himgu`/`himgt` (the two `W(F)`-image computations, shared with `alocToWittF_alocTeich`), the `hdiffW` tail identity, and the `h2gen` induction `gaussValueF (p^M·x) ≤ ρ^M` which is a standalone lemma about `gaussValueF`

### `def prefixAloc`
- **Type**: `(b : ℕ → F) (N : ℕ) : Aloc p F ϖ`
- **What**: The finite Teichmüller prefix sum `Σ_{n<N} pⁿ·alocTeich(bₙ)` in `Aloc` — the building block of the `c₀`-style construction of elements of `A^r` from coefficient sequences.
- **How**: Definition — `Finset.sum` over `Finset.range N`.
- **Hypotheses**: none beyond the ambient perfectoid data.
- **Uses from project**: `Aloc`, `alocTeich`
- **Used by**: `alocToWittF_prefixAloc`, `teichCoeffF_prefixAloc`, `wAloc_prefixAloc`, `prefixAloc_sub`, `cauchySeq_prefix_image`, `PhiHatK`, `tendsto_PhiHatK`, and more
- **Visibility**: public
- **Lines**: 967–968
- **Notes**: noncomputable

### `theorem alocToWittF_prefixAloc`
- **Type**: `(b : ℕ → F) (N : ℕ) : alocToWittF p F ϖ (prefixAloc p F ϖ b N) = ∑ n ∈ Finset.range N, WittVector.teichmuller p (b n) * (p : WittVector p F) ^ n`
- **What**: The `W(F)`-image of a prefix sum is the corresponding truncated Witt series `Σ_{n<N} [bₙ]·pⁿ`.
- **How**: Push the ring hom through the sum (`map_sum`) and use `alocToWittF_alocTeich` termwise.
- **Hypotheses**: none beyond the ambient data.
- **Uses from project**: `prefixAloc`, `alocToWittF`, `alocToWittF_alocTeich`
- **Used by**: `teichCoeffF_prefixAloc`, `wAloc_prefixAloc`, `PhiHatK_teichCoeffAr`
- **Visibility**: public
- **Lines**: 970–976
- **Notes**: none

### `theorem teichCoeffF_prefixAloc`
- **Type**: `(b : ℕ → F) {N j : ℕ} (hj : j < N) : teichCoeffF p F (alocToWittF p F ϖ (prefixAloc p F ϖ b N)) j = b j`
- **What**: The Teichmüller coordinates of a prefix sum recover the prescribed coefficients in the range `j < N`.
- **How**: Rewrite by `alocToWittF_prefixAloc`, pad the sum with the zero tail `p^N·0`, and apply the coordinate-extraction lemma `teichCoeffF_sum_range_add`.
- **Hypotheses**: `j < N`.
- **Uses from project**: `prefixAloc`, `alocToWittF`, `alocToWittF_prefixAloc`, `teichCoeffF`, `teichCoeffF_sum_range_add`
- **Used by**: `teichCoeffAr_PhiHatK`
- **Visibility**: public
- **Lines**: 979–989
- **Notes**: none

### `theorem wAloc_prefixAloc`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (b : ℕ → F) (N : ℕ) : wAloc p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N) = (Finset.range N).sup (fun n => ρ ^ n * perfectoidValuation p F (b n))`
- **What**: **The isometry identity on the dense layer**: the Gauss value of a finite Teichmüller prefix sum is exactly the finite max of the term values `ρⁿ|bₙ|`.
- **How**: Transfer to `W(F)` by `gaussValueF_alocToWittF` and `alocToWittF_prefixAloc`. Each summand `[bₙ]·pⁿ` has value `ρⁿ|bₙ|` and bounded terms (`gaussValueF_p_pow_mul`, `gaussValueF_teichmuller`, `bddAbove_gaussTermF_teichmuller`), so `gaussValueF_finset_sum_le` gives `≤ sup`. For `≥`, `teichCoeffF_sum_range_add` shows the `n`-th Gauss term of the sum is exactly `ρⁿ|bₙ|`, and `gaussTermF_le_gaussValueF` bounds each such term by the value; `Finset.sup_le` concludes.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `prefixAloc`, `wAloc`, `gaussValueF`, `gaussValueF_alocToWittF`, `alocToWittF_prefixAloc`, `gaussTermF`, `gaussTermF_le_gaussValueF`, `gaussValueF_finset_sum_le`, `gaussValueF_p_pow_mul`, `gaussValueF_teichmuller`, `bddAbove_gaussTermF_p_pow_mul`, `bddAbove_gaussTermF_teichmuller`, `teichCoeffF_sum_range_add`, `perfectoidValuation`
- **Used by**: `cauchySeq_prefix_image`, `valued_PhiHatK`
- **Visibility**: public
- **Lines**: 993–1031 (proof ~36 lines)
- **Notes**: proof >30 lines — decompose candidate (the per-summand `hpiece` bundle and the `hterm` coordinate computation are natural helpers)

### `theorem wAloc_p_pow_mul`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (n : ℕ) (u : Aloc p F ϖ) : wAloc p F ϖ hρ0 hρ1 ((p : Aloc p F ϖ) ^ n * u) = ρ ^ n * wAloc p F ϖ hρ0 hρ1 u`
- **What**: Multiplication by `pⁿ` scales the Gauss valuation on `Aloc` by exactly `ρⁿ` — the defining normalization `λ_r(p) = ρ`.
- **How**: Transfer to `W(F)` via `gaussValueF_alocToWittF` and apply `gaussValueF_p_pow_mul`, whose boundedness side condition is `bddAbove_gaussTermF_alocToWittF`.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `wAloc`, `gaussValueF_alocToWittF`, `gaussValueF_p_pow_mul`, `bddAbove_gaussTermF_alocToWittF`, `alocToWittF`, `Aloc`
- **Used by**: `cauchySeq_prefix_image`
- **Visibility**: public
- **Lines**: 1034–1040
- **Notes**: none

### `theorem cauchySeq_of_valued_le`
- **Type**: `{ρ} {hρ0 hρ1} (s : ℕ → hatK p F hρ0 hρ1) (h : ∀ ε : NNReal, 0 < ε → ∃ N₀, ∀ m n, N₀ ≤ m → N₀ ≤ n → Valued.v (s m - s n) ≤ ε) : CauchySeq s`
- **What**: A Cauchy criterion for sequences in the completed field stated in plain `NNReal` bounds, avoiding all reasoning inside the abstract value group.
- **How**: Unfold `CauchySeq` against the valued-field basis (`Valued.hasBasis_uniformity`). Given a value-group unit `γ`, its `NNReal` image is positive (injectivity of `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono` plus `γ.ne_zero`); pick `K` with `ρ^K` below it (`exists_pow_lt_of_lt_one`), apply the hypothesis at `ε = ρ^K`, and push the resulting `NNReal` inequality back through `Valuation.embedding_restrict` and `StrictMono.lt_iff_lt`.
- **Hypotheses**: `0 < ρ < 1` (so `ρ^K` can be made arbitrarily small); nothing about `s` beyond `h`.
- **Uses from project**: `hatK`
- **Used by**: `cauchySeq_prefix_image`
- **Visibility**: public
- **Lines**: 1044–1074 (proof ~29 lines)
- **Notes**: the only place the value-group `embedding` bookkeeping is isolated; keeps `γ`-arithmetic out of the rest of the file

### `theorem prefixAloc_sub`
- **Type**: `(b : ℕ → F) {N M : ℕ} (hNM : N ≤ M) : prefixAloc p F ϖ b M - prefixAloc p F ϖ b N = (p : Aloc p F ϖ) ^ N * prefixAloc p F ϖ (fun j => b (N + j)) (M - N)`
- **What**: A segment of a prefix sum is `p^N` times the prefix sum of the shifted coefficient sequence — the telescoping identity behind the Cauchy estimate.
- **How**: `Finset.sum_Ico_eq_sub` turns the difference into a sum over `Ico N M`, `Finset.sum_Ico_eq_sum_range` reindexes it to `range (M - N)`, and `pow_add` factors out `p^N` termwise.
- **Hypotheses**: `N ≤ M`.
- **Uses from project**: `prefixAloc`, `Aloc`
- **Used by**: `cauchySeq_prefix_image`
- **Visibility**: public
- **Lines**: 1077–1084
- **Notes**: none

### `theorem cauchySeq_prefix_image`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {b : ℕ → F} (hb : Tendsto (fun n => ρ ^ n * perfectoidValuation p F (b n)) atTop (nhds 0)) : CauchySeq (fun N => AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N))`
- **What**: If the coefficient terms `ρⁿ|bₙ|` tend to `0` (the `c₀` condition), the images of the prefix sums form a Cauchy sequence in `hatK`, so the series converges.
- **How**: Use the `NNReal` criterion `cauchySeq_of_valued_le`. For `c ≤ a` past the threshold, `valued_AlocToHatK` + `prefixAloc_sub` + `wAloc_p_pow_mul` + `wAloc_prefixAloc` express the difference's value as `ρ^c · sup_{j < a-c} ρ^j|b_{c+j}|`; `Finset.exists_mem_eq_sup` picks the attaining index `j`, and `pow_add` recombines it into the single term `ρ^{c+j}|b_{c+j}| ≤ ε`. The other order follows by `Valuation.map_neg` on `neg_sub`.
- **Hypotheses**: `0 < ρ < 1`; the `c₀` decay hypothesis `hb`.
- **Uses from project**: `cauchySeq_of_valued_le`, `prefixAloc`, `prefixAloc_sub`, `wAloc_prefixAloc`, `wAloc_p_pow_mul`, `valued_AlocToHatK`, `AlocToHatK`, `perfectoidValuation`
- **Used by**: `tendsto_PhiHatK`
- **Visibility**: public
- **Lines**: 1087–1117 (proof ~29 lines)
- **Notes**: none

### `def PhiHatK`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (b : ℕ → F) : hatK p F hρ0 hρ1`
- **What**: **The `c₀`-parametrization `Φ`**: the point of the completion represented by the formal Teichmüller series `Σ pⁿ[bₙ]`, defined as the limit of its prefix images.
- **How**: Definition — `Filter.limUnder Filter.atTop` of `N ↦ AlocToHatK (prefixAloc b N)`.
- **Hypotheses**: `0 < ρ < 1`; genuinely a limit only under the `c₀` decay condition (see `tendsto_PhiHatK`), junk value otherwise.
- **Uses from project**: `hatK`, `AlocToHatK`, `prefixAloc`
- **Used by**: `tendsto_PhiHatK`, `PhiHatK_mem_ArSub`, `valued_PhiHatK`, `PhiHatK_teichCoeffAr`, `teichCoeffAr_PhiHatK`
- **Visibility**: public
- **Lines**: 1121–1124
- **Notes**: noncomputable

### `theorem tendsto_PhiHatK`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {b : ℕ → F} (hb : Tendsto (fun n => ρ ^ n * perfectoidValuation p F (b n)) atTop (nhds 0)) : Tendsto (fun N => AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N)) atTop (nhds (PhiHatK p F ϖ hρ0 hρ1 b))`
- **What**: Under the `c₀` decay condition the prefix images really converge, and their limit is `PhiHatK b` — so the `limUnder` in the definition is not junk.
- **How**: `cauchySeq_prefix_image` plus completeness of `hatK` (`cauchySeq_tendsto_of_complete`) produce a limit `y`; `Tendsto.limUnder_eq` identifies `PhiHatK b = y`.
- **Hypotheses**: `0 < ρ < 1`; `c₀` decay `hb`; completeness of the valued-field completion `hatK`.
- **Uses from project**: `PhiHatK`, `cauchySeq_prefix_image`, `AlocToHatK`, `prefixAloc`, `perfectoidValuation`
- **Used by**: `PhiHatK_mem_ArSub`, `valued_PhiHatK`, `PhiHatK_teichCoeffAr`, `teichCoeffAr_PhiHatK`
- **Visibility**: public
- **Lines**: 1127–1138
- **Notes**: none

### `theorem PhiHatK_mem_ArSub`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {b : ℕ → F} (hb : …) : PhiHatK p F ϖ hρ0 hρ1 b ∈ ArSub p F ϖ hρ0 hρ1`
- **What**: Every `c₀`-series `Φ b` lands in `A^r` — the parametrization has the right target.
- **How**: Each prefix image lies in the range of `AlocToHatK`, hence in its topological closure (`Subring.le_topologicalClosure`); that closure is closed (`Subring.isClosed_topologicalClosure`), so `IsClosed.mem_of_tendsto` applied to `tendsto_PhiHatK` puts the limit in `ArSub`.
- **Hypotheses**: `c₀` decay `hb`; `0 < ρ < 1`.
- **Uses from project**: `PhiHatK`, `tendsto_PhiHatK`, `ArSub`, `AlocToHatK`, `prefixAloc`, `hatK`, `perfectoidValuation`
- **Used by**: `teichCoeffAr_PhiHatK`
- **Visibility**: public
- **Lines**: 1141–1150
- **Notes**: none

### `theorem valued_PhiHatK`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {b : ℕ → F} (hb : …) : Valued.v (PhiHatK p F ϖ hρ0 hρ1 b) = ⨆ n, ρ ^ n * perfectoidValuation p F (b n)`
- **What**: **The isometry identity for `Φ`**: the value of the series `Σ pⁿ[bₙ]` is the supremum of its term values — Kedlaya (2.2.1) for `c₀`-series.
- **How**: The partial sums satisfy `Valued.v (s N) = sup_{n<N}` (`valued_AlocToHatK` + `wAloc_prefixAloc`), and the term family is bounded above (from `hb` past a threshold, finite `Finset.sup` below it). Split on `Valued.v (Φ b) = 0`: in the zero case a positive term `ρⁿ|bₙ|` would beat a `ρ^K`-ball around `0` (test element `toHatK (p^K)`, `Valued.mem_nhds`, `Valuation.restrict_lt_iff`) that the partial sums eventually enter — contradiction. In the nonzero case the ball `{v(z - Φb) < v(Φb)}` is a neighbourhood, so `Valuation.map_add_eq_of_lt_left` gives `Valued.v (s N) = Valued.v (Φ b)` for all large `N`; then `le_ciSup` and `Finset.sup_le` sandwich the two sides.
- **Hypotheses**: `0 < ρ < 1`; `c₀` decay `hb` (used for boundedness of the term family and for `tendsto_PhiHatK`).
- **Uses from project**: `PhiHatK`, `tendsto_PhiHatK`, `valued_AlocToHatK`, `wAloc_prefixAloc`, `AlocToHatK`, `prefixAloc`, `toHatK`, `valued_toHatK`, `gaussValue`, `gaussVal`, `gaussValue_p_mul`, `gaussValue_one`, `perfectoidValuation`, `hatK`, `Ainf`
- **Used by**: `valued_eq_iSup_teichCoeffAr`
- **Visibility**: public
- **Lines**: 1153–1260 (proof ~106 lines)
- **Notes**: **decompose-proof candidate** — three separable blocks: `hBterms` (boundedness of the term family from `c₀`), the zero case (`ρ^K`-ball contradiction, which duplicates the `z₀ = toHatK (p^K)` computation in `eventually_pair_wAloc_le`), and the nonzero case (`map_add_eq_of_lt_left` stabilization). Contains `push Not` (line 1183)

### `theorem tendsto_gaussTermF_alocToWittF`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : Aloc p F ϖ) : Tendsto (gaussTermF p F ρ (alocToWittF p F ϖ u)) atTop (nhds 0)`
- **What**: **`Aloc`-images decay geometrically**: the Gauss terms of any `u ∈ A_inf[1/[ϖ]]` are `O(ρⁿ)` and hence tend to `0`, so every element of the dense layer is a `c₀`-series.
- **How**: Write `u·[ϖ]^k = a` with `a ∈ A_inf` (`IsLocalization.surj`); `gaussTermF_teichmuller_mul` converts the `n`-th term of `u` into `c^{-k}` times the `A_inf`-term `gaussTerm a n`, which is `≤ ρⁿ` because Teichmüller coordinates of `A_inf`-elements are power-bounded (`perfectoidValuation_le_one`). The geometric bound `ρⁿ·(c^k)⁻¹ → 0` (`tendsto_pow_atTop_nhds_zero_of_lt_one`) then squeezes via `tendsto_of_tendsto_of_tendsto_of_le_of_le`.
- **Hypotheses**: `0 < ρ < 1`; `ϖ ≠ 0` so `c = |ϖ| > 0`.
- **Uses from project**: `gaussTermF`, `gaussTermF_teichmuller_mul`, `gaussTermF_map`, `gaussTerm`, `alocToWittF`, `alocToWittF_algebraMap`, `teichPi`, `teichCoeff`, `perfectoidValuation`, `perfectoidValuation_le_one`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `powerBoundedSubring`, `Ainf`, `Aloc`, `OF`
- **Used by**: `tendsto_gaussTerm_teichCoeffAr`, `PhiHatK_teichCoeffAr`
- **Visibility**: public
- **Lines**: 1264–1313 (proof ~47 lines)
- **Notes**: proof >30 lines — decompose candidate; the `u·[ϖ]^k = a` / `hy` / `himg` preamble is the same one used in `gaussTermF_alocToWittF_le`, `gaussValueF_alocToWittF` and `exists_finite_teichmuller_sum_close`

### `theorem eventually_valued_sub_le`
- **Type**: `{ρ} {hρ0 hρ1} (x : hatK p F hρ0 hρ1) {ε : NNReal} (hε : 0 < ε) : ∀ᶠ u in comap (AlocToHatK …) (nhds x), Valued.v (AlocToHatK p F ϖ hρ0 hρ1 u - x) ≤ ε`
- **What**: The approximants of any point `x` of the completion are eventually within `ε` of `x` in the completed-field valuation — the one-sided companion of `eventually_pair_wAloc_le`.
- **How**: Choose `N` with `ρ^N < ε` and use the test element `z₀ = toHatK (p^N)` of value `ρ^N` (`valued_toHatK`, `gaussValue_p_mul`, `gaussValue_one`). The ball `{(Valued.v).restrict (z - x) < Units.mk0 ((Valued.v).restrict z₀)}` is a neighbourhood of `x` (`Valued.mem_nhds`), and `Valuation.restrict_lt_iff` converts membership into `Valued.v (z - x) < ρ^N ≤ ε`.
- **Hypotheses**: `0 < ρ < 1`; `0 < ε`; no assumption on `x`.
- **Uses from project**: `AlocToHatK`, `toHatK`, `valued_toHatK`, `gaussValue`, `gaussVal`, `gaussValue_p_mul`, `gaussValue_one`, `hatK`, `Ainf`
- **Used by**: `tendsto_gaussTerm_teichCoeffAr`, `PhiHatK_teichCoeffAr`
- **Visibility**: public
- **Lines**: 1316–1358 (proof ~41 lines)
- **Notes**: proof >30 lines — decompose candidate; the `z₀`/`hvz₀`/`hrne`/`γ` preamble is byte-for-byte the one in `eventually_pair_wAloc_le` and `eventually_valued_sub_le_of_tendsto` (three-way duplication, prime dedup target)

### `theorem tendsto_gaussTerm_teichCoeffAr`
- **Type**: `{ρ} {hρ0 hρ1} {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) : Tendsto (fun n => ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)) atTop (nhds 0)`
- **What**: **The decay-closure crux**: for every `x ∈ A^r` the scaled limit coordinates `ρⁿ|xₙ|` tend to `0`, so `teichCoeffAr x` is a legitimate `c₀` coefficient sequence and `PhiHatK` may be applied to it.
- **How**: Via `tendsto_order` it suffices to beat each `a > 0`. Pick `b < a` and one `b`-close approximant `u₀` from `eventually_valued_sub_le`; since `u₀`'s own terms decay (`tendsto_gaussTermF_alocToWittF`), both its tail value and head bound go to `0` (`tendsto_tailValueF_of_tendsto`, `tendsto_headBoundF_of_tendsto`), so past `max N₁ N₂` the threshold `r = max (max (tailValueF w₀ n) (headBoundF w₀ n)) b` is `< a`. For any closer approximant `u`, `valued_AlocToHatK` + `Valuation.map_sub` give `wAloc (u - u₀) ≤ b`, and the moving-prefix estimate `tailValueF_add_le_gaussValueF` on `u = w₀ + (u - w₀)` bounds `gaussTermF u n ≤ tailValueF u n ≤ r` (`gaussTermF_le_tailValueF`). This puts the approximant coordinates in the closed ball of radius `(ρⁿ)⁻¹r` (`isClosed_ball`), so `IsClosed.mem_of_tendsto` with `tendsto_teichCoeffAr` transfers it to the limit coordinate, giving `ρⁿ|xₙ| ≤ r < a`.
- **Hypotheses**: `x ∈ ArSub`; `0 < ρ < 1`.
- **Uses from project**: `teichCoeffAr`, `tendsto_teichCoeffAr`, `eventually_valued_sub_le`, `tendsto_gaussTermF_alocToWittF`, `tendsto_tailValueF_of_tendsto`, `tendsto_headBoundF_of_tendsto`, `tailValueF`, `tailValueF_add_le_gaussValueF`, `headBoundF`, `gaussTermF`, `gaussTermF_le_tailValueF`, `gaussValueF`, `gaussValueF_alocToWittF`, `bddAbove_gaussTermF_alocToWittF`, `isClosed_ball`, `neBot_comap_of_mem_ArSub`, `valued_AlocToHatK`, `wAloc`, `alocToWittF`, `teichCoeffF`, `AlocToHatK`, `ArSub`, `perfectoidValuation`
- **Used by**: `PhiHatK_teichCoeffAr`, `valued_eq_iSup_teichCoeffAr`, `exists_valued_eq_teichCoeffAr`, `wAr_apply`
- **Visibility**: public
- **Lines**: 1365–1441 (proof ~74 lines)
- **Notes**: proof >30 lines — decompose candidate (the inner `hevn` uniform-coordinate-bound block is a standalone lemma about `tailValueF`)

### `theorem eventually_valued_sub_le_of_tendsto`
- **Type**: `{ρ} {hρ0 hρ1} {ι} {l : Filter ι} {g : ι → hatK p F hρ0 hρ1} {y} (hg : Tendsto g l (nhds y)) {ε : NNReal} (hε : 0 < ε) : ∀ᶠ i in l, Valued.v (g i - y) ≤ ε`
- **What**: The filter-generic form of `eventually_valued_sub_le`: along any convergent net in `hatK`, the difference from the limit is eventually of valuation `≤ ε`.
- **How**: Same `z₀ = toHatK (p^N)` device with `ρ^N < ε` (`valued_toHatK`, `gaussValue_p_mul`, `gaussValue_one`); the `γ`-ball around `y` is a neighbourhood (`Valued.mem_nhds`), `Tendsto.eventually` pulls it back along `g`, and `Valuation.restrict_lt_iff` converts to the `NNReal` bound.
- **Hypotheses**: `0 < ρ < 1`; `0 < ε`; `g` converges to `y` along `l`.
- **Uses from project**: `toHatK`, `valued_toHatK`, `gaussValue`, `gaussVal`, `gaussValue_p_mul`, `gaussValue_one`, `hatK`, `Ainf`
- **Used by**: `PhiHatK_teichCoeffAr`
- **Visibility**: public
- **Lines**: 1444–1485 (proof ~40 lines)
- **Notes**: proof >30 lines; near-duplicate of `eventually_valued_sub_le` (which is its special case at `l = comap …`, `g = AlocToHatK`) — dedup candidate

### `theorem PhiHatK_teichCoeffAr`
- **Type**: `{ρ} {hρ0 hρ1} {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) : PhiHatK p F ϖ hρ0 hρ1 (teichCoeffAr p F ϖ hρ0 hρ1 x) = x`
- **What**: **The series realization** (Kedlaya (2.2.1) on the completion, existence direction): every element of `A^r` is the sum of its own Teichmüller series, `x = Σₙ pⁿ[xₙ]` with `xₙ = teichCoeffAr x n`. Together with `teichCoeffAr_PhiHatK` this makes `Φ` a bijection between `c₀` coefficient sequences and `A^r`.
- **How**: Show `Valued.v (Φ b - x) ≤ ε` for every `ε > 0` (then `NNReal.half_lt_self` forces the value to be `0`, and `Valuation.zero_iff` + `sub_eq_zero` give equality). The `ε`-estimate is a three-term ultrametric chain `Φb - x = (Φb - S_N) + ((S_N - u) + (u - x))` where `S_N = AlocToHatK (prefixAloc b N)`: the outer legs come from `eventually_valued_sub_le_of_tendsto` applied to `tendsto_PhiHatK` (needing the `c₀` decay `tendsto_gaussTerm_teichCoeffAr`) and from `eventually_valued_sub_le`. The middle leg is the quantitative core, computed in `W(F)` via `valued_AlocToHatK` + `gaussValueF_alocToWittF` + `alocToWittF_prefixAloc` and split as `w_u - P_b = (w_u - P_u) + (P_u - P_b)`: (i) `gaussValueF_sub_prefix` identifies `gaussValueF (w_u - P_u)` with `tailValueF w_u N`, which is `≤ ε'` by the same base-approximant perturbation as in `tendsto_gaussTerm_teichCoeffAr` (`tailValueF_add_le_gaussValueF` against `u₀`, with `N` past the `tendsto_tailValueF_of_tendsto` / `tendsto_headBoundF_of_tendsto` thresholds); (ii) `P_u - P_b` is the finite sum of the `N` differences `pⁱ([u_i] - [b_i])`, each of which is `≤ ε'` by the Hölder modulus `gaussValueF_teichmuller_sub_le_of_le_scaled` — applicable because the coordinates are capped by `c⁻ᵐ` (finite `Finset.sup` of `|b i|`) and are `δ'`-close by `tendsto_teichCoeffAr` uniformly over `i < N` (`Filter.eventually_all_finset`) — so `gaussValueF_finset_sum_le` bounds the whole sum. Boundedness side conditions come from `exists_iter_splitF` / `bddAbove_gaussTermF_of_coords_shift` / `bddAbove_gaussTermF_teichmuller_sub`, and the two halves are combined by `gaussValueF_add_le`.
- **Hypotheses**: `x ∈ ArSub`; `0 < ρ < 1`; `ϖ` a pseudo-uniformizer with `0 < c = |ϖ| < 1` (used to build the value cap `c⁻ᵐ` and the ball `{|z| ≤ δ'}`); `ε` truncated to `ε' = min ε 1` so the Hölder modulus applies.
- **Uses from project**: `PhiHatK`, `tendsto_PhiHatK`, `teichCoeffAr`, `tendsto_teichCoeffAr`, `tendsto_gaussTerm_teichCoeffAr`, `eventually_valued_sub_le`, `eventually_valued_sub_le_of_tendsto`, `neBot_comap_of_mem_ArSub`, `valued_AlocToHatK`, `AlocToHatK`, `prefixAloc`, `alocToWittF`, `alocToWittF_prefixAloc`, `wAloc`, `gaussValueF`, `gaussValueF_alocToWittF`, `gaussValueF_sub_prefix`, `gaussValueF_add_le`, `gaussValueF_finset_sum_le`, `gaussValueF_p_pow_mul`, `gaussValueF_teichmuller_sub_le_of_le_scaled`, `gaussTermF`, `tailValueF`, `tailValueF_add_le_gaussValueF`, `tendsto_tailValueF_of_tendsto`, `headBoundF`, `tendsto_headBoundF_of_tendsto`, `tendsto_gaussTermF_alocToWittF`, `bddAbove_gaussTermF_alocToWittF`, `bddAbove_gaussTermF_p_pow_mul`, `bddAbove_gaussTermF_teichmuller_sub`, `bddAbove_gaussTermF_of_coords_shift`, `exists_iter_splitF`, `teichCoeffF`, `ball_mem_nhds_zero`, `perfectoidValuation`, `perfectoidValuation_toOF_lt_one`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `ArSub`, `hatK`, `OF`
- **Used by**: `valued_eq_iSup_teichCoeffAr`
- **Visibility**: public
- **Lines**: 1492–1690 (proof ~197 lines)
- **Notes**: **the file's longest proof and the prime decompose-proof candidate**. Natural extraction points: (a) the `capB ≤ (c⁻¹)^m` value-cap lemma (verbatim duplicate of the same block in `tendsto_teichCoeffAr`), (b) `hcoordAll` — uniform `δ'`-closeness of the first `N` coordinates, (c) `htailu` — the base-approximant tail bound (shared with `tendsto_gaussTerm_teichCoeffAr`), (d) `hpieces`/`hsum` — the finite Hölder-sum bound, (e) `hwuPb` — the `W(F)`-side middle-leg estimate, (f) the closing "value below every `ε` is zero" argument, which is a standalone `NNReal` valuation lemma

### `theorem valued_eq_iSup_teichCoeffAr`
- **Type**: `{ρ} {hρ0 hρ1} {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) : Valued.v x = ⨆ n, ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)`
- **What**: **The value formula on `A^r`** (Kedlaya (2.2.1) on the completion): the Gauss value of any element of `A^r` is the supremum of its scaled coordinate values `ρⁿ|xₙ|`.
- **How**: Rewrite `x` as `Φ (teichCoeffAr x)` by `PhiHatK_teichCoeffAr` and apply the isometry identity `valued_PhiHatK`, whose `c₀` hypothesis is `tendsto_gaussTerm_teichCoeffAr`.
- **Hypotheses**: `x ∈ ArSub`; `0 < ρ < 1`.
- **Uses from project**: `PhiHatK_teichCoeffAr`, `valued_PhiHatK`, `tendsto_gaussTerm_teichCoeffAr`, `teichCoeffAr`, `ArSub`, `hatK`, `perfectoidValuation`
- **Used by**: `exists_valued_eq_teichCoeffAr`, `teichCoeffAr_zero`
- **Visibility**: public
- **Lines**: 1694–1699
- **Notes**: the file's headline theorem; short because both halves were proved separately

### `def wAr`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Valuation (ArSub p F ϖ hρ0 hρ1) NNReal`
- **What**: **The Gauss valuation on the completed ring `A^r`** (Kedlaya Definition 2.4 on the completion) — the restriction of the completed-field valuation to the closed subring.
- **How**: Definition — `Valuation.comap` of `Valued.v` along the subring inclusion `(ArSub …).subtype`.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `ArSub`, `hatK`
- **Used by**: `wAr_apply`
- **Visibility**: public
- **Lines**: 1704–1707
- **Notes**: noncomputable

### `theorem wAr_apply`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (z : ArSub p F ϖ hρ0 hρ1) : wAr p F ϖ hρ0 hρ1 z = Valued.v (z : hatK p F hρ0 hρ1)`
- **What**: The defining simp lemma for `wAr`: evaluating it is just evaluating the ambient `Valued.v` on the underlying element.
- **How**: `rfl` — the comap is definitionally the composite.
- **Hypotheses**: none.
- **Uses from project**: `wAr`, `ArSub`, `hatK`
- **Used by**: unused in file (API for downstream)
- **Visibility**: public
- **Lines**: 1710–1713
- **Notes**: `@[simp]`

### `theorem exists_valued_eq_teichCoeffAr`
- **Type**: `{ρ} {hρ0 hρ1} {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) : ∃ n₀, Valued.v x = ρ ^ n₀ * perfectoidValuation p F (teichCoeffAr … x n₀) ∧ ∀ m, ρ ^ m * … ≤ ρ ^ n₀ * …`
- **What**: **Attainment on `A^r`** (Kedlaya Definition 2.4, existence of the degree): a nonzero element of `A^r` attains its value at some coordinate index `n₀`, which dominates all other coordinate terms — so the `⨆` of the value formula is a maximum.
- **How**: The value formula `valued_eq_iSup_teichCoeffAr` rewrites the sup; since the terms tend to `0` (`tendsto_gaussTerm_teichCoeffAr`) and the sup is nonzero (`Valuation.ne_zero_iff` from `x ≠ 0`), the general attainment lemma `exists_iSup_eq_of_tendsto_zero` produces the maximizing index.
- **Hypotheses**: `x ∈ ArSub`, `x ≠ 0`; `0 < ρ < 1`.
- **Uses from project**: `valued_eq_iSup_teichCoeffAr`, `tendsto_gaussTerm_teichCoeffAr`, `exists_iSup_eq_of_tendsto_zero`, `teichCoeffAr`, `ArSub`, `hatK`, `perfectoidValuation`
- **Used by**: unused in file (exported degree statement)
- **Visibility**: public
- **Lines**: 1718–1729
- **Notes**: none

### `theorem teichCoeffAr_PhiHatK`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {b : ℕ → F} (hb : …) (n : ℕ) : teichCoeffAr p F ϖ hρ0 hρ1 (PhiHatK p F ϖ hρ0 hρ1 b) n = b n`
- **What**: **Coordinate recovery for `Φ`**: the limit coordinates of the series `Φ b` are exactly the input coefficients. With `PhiHatK_teichCoeffAr` this shows `Φ` and `teichCoeffAr` are mutually inverse.
- **How**: The prefix sums converge to `Φ b` (`tendsto_PhiHatK`), hence tend to `Φ b` along the comap filter (`Filter.tendsto_comap_iff`); composing with `tendsto_teichCoeffAr` (legitimate since `PhiHatK_mem_ArSub`) makes the `n`-th coordinate of the prefixes converge to `teichCoeffAr (Φ b) n`. But `teichCoeffF_prefixAloc` makes that coordinate eventually constantly `b n`, so `Filter.Tendsto.congr'` plus `tendsto_nhds_unique` (in the `T0`, complete `F`) forces the two limits to agree.
- **Hypotheses**: `c₀` decay `hb`; `0 < ρ < 1`; `F` complete, `T0`, uniform additive group.
- **Uses from project**: `teichCoeffAr`, `PhiHatK`, `tendsto_PhiHatK`, `PhiHatK_mem_ArSub`, `tendsto_teichCoeffAr`, `teichCoeffF_prefixAloc`, `prefixAloc`, `alocToWittF`, `teichCoeffF`, `AlocToHatK`, `IsPerfectoidRing.complete`, `IsPerfectoidRing.t0`, `IsPerfectoidRing.uniformAddGroup`, `perfectoidValuation`
- **Used by**: unused in file (the injectivity half of the parametrization, exported)
- **Visibility**: public
- **Lines**: 1733–1754 (proof ~18 lines)
- **Notes**: none

### `theorem teichCoeffAr_zero`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (n : ℕ) : teichCoeffAr p F ϖ hρ0 hρ1 (0 : hatK p F hρ0 hρ1) n = 0`
- **What**: All limit coordinates of `0` vanish — the normalization making `teichCoeffAr` a genuine coordinate system.
- **How**: Apply the value formula `valued_eq_iSup_teichCoeffAr` at `x = 0` (`zero_mem (ArSub …)`), so the sup of the terms is `Valuation.map_zero = 0`. The term family is bounded above (finite `Finset.sup` below a threshold from `tendsto_gaussTerm_teichCoeffAr`, `< 1` above it), so `le_ciSup` bounds each individual term by `0`; `mul_eq_zero` with `ρⁿ > 0` and `Valuation.zero_iff` then kills the coordinate.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `teichCoeffAr`, `valued_eq_iSup_teichCoeffAr`, `tendsto_gaussTerm_teichCoeffAr`, `ArSub`, `hatK`, `perfectoidValuation`
- **Used by**: unused in file (final normalization lemma)
- **Visibility**: public
- **Lines**: 1757–1783 (proof ~25 lines)
- **Notes**: the `hB` boundedness block duplicates `hBterms` inside `valued_PhiHatK` — dedup candidate (a standalone `BddAbove`-from-`c₀` lemma)

---

### File Summary

**Total declarations: 58** — 43 `theorem`, 13 `def`, 2 `abbrev` (`hatK`, `Aloc`), 0 `instance`. File length 1787 lines, single namespace `FarguesFontaine`, whole file inside `noncomputable section`.

**Key API used by 3+ other declarations in this file** (in-file consumer count):

| Declaration | Kind | Consumers |
|---|---|---|
| `hatK` | abbrev | 28 |
| `Aloc` | abbrev | 25 |
| `AlocToHatK` | def | 18 |
| `alocToWittF` | def | 16 |
| `wAloc` | def | 16 |
| `ArSub` | def | 12 |
| `prefixAloc` | def | 11 |
| `teichCoeffAr` | def | 9 |
| `toHatK` | def | 8 |
| `valued_toHatK` | theorem | 7 |
| `gaussValueF_alocToWittF` | theorem | 6 |
| `valued_AlocToHatK` | theorem | 6 |
| `alocToWittF_algebraMap` | theorem | 5 |
| `bddAbove_gaussTermF_alocToWittF` | theorem | 5 |
| `neBot_comap_of_mem_ArSub` | theorem | 5 |
| `PhiHatK` | def | 5 |
| `wK` | def | 4 |
| `wAloc_algebraMap` | theorem | 4 |
| `tendsto_teichCoeffAr` | theorem | 4 |
| `alocTeich` | def | 4 |
| `tendsto_PhiHatK` | theorem | 4 |
| `tendsto_gaussTerm_teichCoeffAr` | theorem | 4 |
| `gaussTermF_alocToWittF_le` | theorem | 3 |
| `alocToWittF_prefixAloc` | theorem | 3 |

The three load-bearing bridges are `valued_AlocToHatK` (ground valuation ↔ completed-field valuation), `gaussValueF_alocToWittF` (`Aloc` value ↔ `W(F)` Gauss value) and `tendsto_teichCoeffAr` (approximant coordinates ↔ limit coordinates); almost every later proof factors through at least one of them.

**Unused declarations (no in-file consumer — all are exported API, not dead code): 8**
`BrSub` (the `B^r` companion of `ArSub`; defined for the downstream `B^r` theory, never consumed here), `gaussTerm_teichCoeffAr_le`, `wAloc_alocTeich`, `exists_finite_teichmuller_sum_close`, `wAr_apply`, `exists_valued_eq_teichCoeffAr`, `teichCoeffAr_PhiHatK`, `teichCoeffAr_zero`. The last four are the file's exported endpoints (degree attainment, coordinate recovery, normalization, `wAr` simp lemma).

**Declarations with `sorry`: 0.** The file is sorry-free.

**Declarations with `set_option`: 0.** No `maxHeartbeats` / `maxRecDepth` bumps anywhere — notable for a file with a 197-line proof.

**Proofs longer than 30 lines: 14** (of 58 declarations, i.e. ~24%):

| Declaration | Lines | Proof length |
|---|---|---|
| `PhiHatK_teichCoeffAr` | 1492–1690 | ~197 |
| `exists_finite_teichmuller_sum_close` | 837–964 | ~124 |
| `valued_PhiHatK` | 1153–1260 | ~106 |
| `tendsto_teichCoeffAr` | 554–632 | ~74 |
| `tendsto_gaussTerm_teichCoeffAr` | 1365–1441 | ~74 |
| `gaussValueF_alocToWittF` | 276–341 | ~63 |
| `eventually_pair_wAloc_le` | 459–523 | ~59 |
| `gaussTermF_alocToWittF_le` | 212–263 | ~50 |
| `tendsto_gaussTermF_alocToWittF` | 1264–1313 | ~47 |
| `alocToWittF_alocTeich` | 756–798 | ~41 |
| `eventually_valued_sub_le` | 1316–1358 | ~41 |
| `eventually_wAloc_eq` | 637–679 | ~40 |
| `eventually_valued_sub_le_of_tendsto` | 1444–1485 | ~40 |
| `wAloc_prefixAloc` | 993–1031 | ~36 |

(`wAloc_alocTeich`, 801–832, is exactly at the ~30-line boundary.)

**Cross-cutting duplication (dedup / decompose targets).** Three preambles are repeated verbatim across many of the long proofs and account for most of their length:
1. **The `z₀ = toHatK (p^N)` / `γ = Units.mk0 ((Valued.v).restrict z₀)` value-group block** — in `eventually_pair_wAloc_le`, `eventually_valued_sub_le`, `eventually_valued_sub_le_of_tendsto` and the zero case of `valued_PhiHatK` (4 copies, ~25 lines each). `cauchySeq_of_valued_le` already isolates the analogous plumbing; a shared `∃ z₀, Valued.v z₀ = ρ^N` helper would collapse all four.
2. **The `u·[ϖ]^k = a` localization/scaling preamble** (`IsLocalization.surj` + `WittVector.map_teichmuller` + cancel `c^k`) — in `valued_AlocToHatK`, `gaussTermF_alocToWittF_le`, `gaussValueF_alocToWittF`, `alocToWittF_alocTeich`, `wAloc_alocTeich`, `exists_finite_teichmuller_sum_close`, `tendsto_gaussTermF_alocToWittF` (7 copies).
3. **The `B ≤ (c⁻¹)^m` value-cap extraction** — identical in `tendsto_teichCoeffAr` and `PhiHatK_teichCoeffAr`; and the **`BddAbove`-from-`c₀`** block, identical in `valued_PhiHatK` and `teichCoeffAr_zero`.
