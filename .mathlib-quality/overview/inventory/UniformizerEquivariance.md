# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/UniformizerEquivariance.lean`

**File length**: 801 lines
**Namespace**: `FarguesFontaine`
**Imports**: `«Adic spaces».FarguesFontaine.RobbaLoc`, `.IntervalRing`, `.SheafyBI`, `.UniformizerTwist`, `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
**Opens**: `TopologicalRing ValuationSpectrum WittVector NNReal`

**File-level options** (lines 29–30):
- `set_option linter.overlappingInstances false`
- `set_option warn.classDefReducibility false`

**Section variables** (lines 36–40):
```
(p : ℕ) [Fact (Nat.Prime p)]
(F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F] [UniformSpace F]
  [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
(ϖ : PseudoUniformizer F)
{ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
```
Note the *implicit* radius-hypothesis variables `hρ₁0 … hρ₂1` — most statements below take them
implicitly and are applied with named arguments `(hρ₁0 := …)`.

The whole file is inside `noncomputable section`.

---

### `theorem isLocalization_twist_Bloc`
- **Type**: `{ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k) (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) : IsLocalization (Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ')) (Bloc p F ϖ)`
- **What**: If the Teichmüller lift of a second pseudo-uniformizer `ϖ'` has `[ϖ']^k = [ϖ]`, then `Bloc p F ϖ` — defined as the localization of `A_inf` away from `p·[ϖ]` — is *also* the localization of `A_inf` away from `p·[ϖ']`. So `Bloc` does not depend on the chosen uniformizer.
- **How**: Verifies the three `IsLocalization` fields directly. `map_units`: `[ϖ']` becomes a unit because `[ϖ']·[ϖ']^{k-1} = [ϖ]` is already a unit (`isUnit_teichPi_image`), and `p` is a unit by `isUnit_p_image`. `surj`/`exists_of_eq`: transfer denominators via the key identity `(p·[ϖ'])^{km} = (p·[ϖ])^m · p^{km−m}` (from `pow_mul`, `h`, and `Nat.le_mul_of_pos_left`), so every power of `p·[ϖ]` divides a power of `p·[ϖ']` up to the invertible factor `p^{km−m}`.
- **Hypotheses**: `k > 0`; `teichPi p F ϖ' ^ k = teichPi p F ϖ` (the two Teichmüller lifts are related by a `k`-th power); the ambient perfectoid-field instances.
- **Uses from project**: `PseudoUniformizer`, `teichPi`, `Ainf`, `Bloc`, `isUnit_teichPi_image`, `isUnit_p_image`
- **Used by**: `blocTwistEquiv`, `blocTwistEquiv_algebraMap`, `BlocToHatK_twist`
- **Visibility**: public
- **Lines**: 42–120 (proof 48–120, ~73 lines)
- **Notes**: Proof >30 lines; the `hexp` power-splitting `have` block is duplicated verbatim in the `surj` and `exists_of_eq` fields (lines 74–85 and 97–108) — a natural extraction target. Statement is a `theorem` whose type is the class `IsLocalization`, so it plausibly relies on the file-level `warn.classDefReducibility false`; it is deliberately *not* an instance (it would loop over `ϖ'`), and is introduced by `letI` at each use site.

### `def blocTwistEquiv`
- **Type**: `{ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k) (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) : Bloc p F ϖ' ≃+* Bloc p F ϖ`
- **What**: The canonical uniformizer-change ring isomorphism between the localized rings `Bloc` built from `ϖ'` and from `ϖ`.
- **How**: Both rings are localizations of `A_inf` at the same submonoid `powers (p·[ϖ'])` — the source by definition, the target by `isLocalization_twist_Bloc` — so `IsLocalization.algEquiv` gives the unique `A_inf`-algebra equivalence, coerced to a `RingEquiv`.
- **Hypotheses**: `k > 0`; `[ϖ']^k = [ϖ]`.
- **Uses from project**: `PseudoUniformizer`, `teichPi`, `Ainf`, `Bloc`, `isLocalization_twist_Bloc`
- **Used by**: `blocTwistEquiv_algebraMap`, `wLoc_blocTwistEquiv`, `BlocToHatK_twist`, `BISub_twist`
- **Visibility**: public
- **Lines**: 123–129 (body 127–129, 3 lines)
- **Notes**: `noncomputable`; uses `letI` to install the twisted localization instance in the term.

### `theorem blocTwistEquiv_algebraMap` `@[simp]`
- **Type**: `{ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k) (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) (y : Ainf p F) : blocTwistEquiv p F ϖ hk h (algebraMap (Ainf p F) (Bloc p F ϖ') y) = algebraMap (Ainf p F) (Bloc p F ϖ) y`
- **What**: The change isomorphism is the identity on the image of `A_inf`, i.e. it is a map of `A_inf`-algebras.
- **How**: Immediate from `IsLocalization.algEquiv … |>.commutes`, the defining `A_inf`-algebra property of the equivalence used to build `blocTwistEquiv`.
- **Hypotheses**: `k > 0`; `[ϖ']^k = [ϖ]`.
- **Uses from project**: `blocTwistEquiv`, `isLocalization_twist_Bloc`, `Bloc`, `Ainf`, `teichPi`, `PseudoUniformizer`
- **Used by**: `wLoc_blocTwistEquiv`, `BlocToHatK_twist`
- **Visibility**: public
- **Lines**: 131–138 (proof 135–138, 3 lines)
- **Notes**: `@[simp]`.

### `theorem gaussValue_p_teichPi_pow`
- **Type**: `(ϖ'' : PseudoUniformizer F) {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) : gaussValue p F ρ (((p : Ainf p F) * teichPi p F ϖ'') ^ m) = (ρ * perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ'' : OF F) : F)) ^ m`
- **What**: The Gauss valuation of radius `ρ` on the `m`-th power of the localizing element `p·[ϖ'']` is the `m`-th power of `ρ · |ϖ''|`.
- **How**: Induction on `m`; the base case is `gaussValue_one` and the step combines multiplicativity `gaussValue_mul` with the single-factor computation `gaussValue_p_teichPi`.
- **Hypotheses**: `0 < ρ < 1`; `ϖ''` a pseudo-uniformizer (arbitrary — not tied to the section's `ϖ`).
- **Uses from project**: `gaussValue`, `Ainf`, `teichPi`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`, `gaussValue_one`, `gaussValue_mul`, `gaussValue_p_teichPi`
- **Used by**: `wLoc_blocTwistEquiv`
- **Visibility**: public
- **Lines**: 140–152 (proof 146–152, 7 lines)
- **Notes**: none.

### `theorem wLoc_blocTwistEquiv`
- **Type**: `{ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k) (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (z : Bloc p F ϖ') : wLoc p F ϖ hρ0 hρ1 (blocTwistEquiv p F ϖ hk h z) = wLoc p F ϖ' hρ0 hρ1 z`
- **What**: The Gauss valuation `wLoc` of radius `ρ` on `Bloc` is invariant under the uniformizer-change isomorphism — the Gauss value is intrinsically uniformizer-free.
- **How**: Write `z = a / (p·[ϖ'])^m` via `IsLocalization.surj`, push the relation through the equivalence with `blocTwistEquiv_algebraMap`, evaluate both sides with `wLoc_algebraMap` and the explicit denominator value `gaussValue_p_teichPi_pow`, and cancel the common nonzero factor `(ρ·|ϖ'|)^m` by `mul_right_cancel₀` (nonzero via `PseudoUniformizer.toOF_ne_zero` and `Valuation.ne_zero_iff`).
- **Hypotheses**: `k > 0`; `[ϖ']^k = [ϖ]`; `0 < ρ < 1`.
- **Uses from project**: `wLoc`, `blocTwistEquiv`, `blocTwistEquiv_algebraMap`, `gaussValue_p_teichPi_pow`, `wLoc_algebraMap`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `Bloc`, `Ainf`, `teichPi`, `OF`
- **Used by**: unused in file (headline export, advertised in the module docstring)
- **Visibility**: public
- **Lines**: 154–184 (proof 160–184, 25 lines)
- **Notes**: none.

### `theorem BlocToHatK_twist`
- **Type**: `{ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k) (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (z : Bloc p F ϖ') : BlocToHatK p F ϖ hρ0 hρ1 (blocTwistEquiv p F ϖ hk h z) = BlocToHatK p F ϖ' hρ0 hρ1 z`
- **What**: The change isomorphism intertwines the two maps `Bloc → K̂_ρ` into the (uniformizer-free) completed residue field at radius `ρ`.
- **How**: Both `BlocToHatK`s are `IsLocalization.lift`s of the same map `toHatK` on `A_inf`, so the composite `BlocToHatK ϖ ∘ blocTwistEquiv` and `BlocToHatK ϖ'` agree by the uniqueness clause `IsLocalization.ringHom_ext` applied at the submonoid `powers (p·[ϖ'])`, using `blocTwistEquiv_algebraMap` and `IsLocalization.lift_eq` on `A_inf`-elements.
- **Hypotheses**: `k > 0`; `[ϖ']^k = [ϖ]`; `0 < ρ < 1`.
- **Uses from project**: `BlocToHatK`, `blocTwistEquiv`, `blocTwistEquiv_algebraMap`, `isLocalization_twist_Bloc`, `toHatK`, `Bloc`, `Ainf`, `teichPi`
- **Used by**: `BISub_twist`
- **Visibility**: public
- **Lines**: 186–208 (proof 192–208, 17 lines)
- **Notes**: none.

### `theorem BISub_twist`
- **Type**: `{ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k) (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) : BISub p F ϖ' hρ₁0 hρ₁1 hρ₂0 hρ₂1 = BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1`
- **What**: The interval ring `B^I` is uniformizer-invariant *on the nose*: the two subrings of `K̂_{ρ₁} × K̂_{ρ₂}` obtained from `ϖ'` and `ϖ` are literally the same subring, not merely isomorphic.
- **How**: `BISub` is by definition the topological closure of the range of the diagonal `BIProd`; the two ranges coincide as sets because `blocTwistEquiv` (and its inverse, via `RingEquiv.apply_symm_apply`) transports one diagonal to the other by `BlocToHatK_twist` in each coordinate — so the closures are equal.
- **Hypotheses**: `k > 0`; `[ϖ']^k = [ϖ]`; the section's implicit `0 < ρᵢ < 1`.
- **Uses from project**: `BISub`, `BIProd`, `BlocToHatK`, `BlocToHatK_twist`, `blocTwistEquiv`
- **Used by**: unused in file (feeds the `B^I`-equivariance D-i-t2 downstream)
- **Visibility**: public
- **Lines**: 210–235 (proof 215–235, 21 lines)
- **Notes**: none.

### `def blocWIUniformSpace`
- **Type**: `(hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) : UniformSpace (Bloc p F ϖ)`
- **What**: The `w^I`-uniformity on `Bloc`: the uniform structure pulled back from `K̂_{ρ₁} × K̂_{ρ₂}` along the diagonal map `BIProd`.
- **How**: Literally `UniformSpace.comap (BIProd …) inferInstance` — the comap of the product uniformity.
- **Hypotheses**: `0 < ρ₁ < 1`, `0 < ρ₂ < 1` (all four explicit here, unlike most statements below).
- **Uses from project**: `BIProd`, `Bloc`
- **Used by**: `isUniformInducing_blocToBI`, `isUniformAddGroup_blocWI`, `uniformContinuous_blocToBI_interpolate`, `biRes`, `biRes_blocToBI`, `biRes_continuous`
- **Visibility**: public
- **Lines**: 237–241 (body 240–241, 2 lines)
- **Notes**: `noncomputable`. **This is the declaration that needs `set_option warn.classDefReducibility false`**: it is a plain `def` whose result type is the class `UniformSpace`, neither `@[reducible]` nor an `instance` (deliberately — it must not fire globally, and is installed by `letI` at each use site).

### `def blocToBI`
- **Type**: `(hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) : Bloc p F ϖ →+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: The diagonal map `Bloc → K̂_{ρ₁} × K̂_{ρ₂}` corestricted to land in the interval ring `B^I = BISub`.
- **How**: `RingHom.codRestrict` of `BIProd`, with the range-membership witness supplied by `Subring.le_topologicalClosure` (`BISub` is the closure of the range of `BIProd`).
- **Hypotheses**: `0 < ρ₁ < 1`, `0 < ρ₂ < 1`.
- **Uses from project**: `BIProd`, `BISub`, `Bloc`
- **Used by**: `isUniformInducing_blocToBI`, `denseRange_blocToBI`, `uniformContinuous_blocToBI_interpolate`, `biRes_blocToBI`, `biCongr_blocToBI`, `biResQ_blocToBI`, `biResQ_id`, `biResQ_comp`, `biResQ'_blocToBI`, `biResQ'_id`, `biResQ'_comp`
- **Visibility**: public
- **Lines**: 243–249 (body 247–249, 3 lines)
- **Notes**: `noncomputable`. The most heavily used definition in the file — the "dense layer" through which every interval-restriction map is characterised.

### `theorem isUniformInducing_blocToBI`
- **Type**: `@IsUniformInducing _ _ (blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) _ (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: With the `w^I`-uniformity on `Bloc`, the corestricted diagonal `blocToBI` is a uniform embedding onto its image (comap of the target uniformity = the source uniformity).
- **How**: Unfolds to the definitional identity: the subtype uniformity is the comap along `Subtype.val` (`uniformity_subtype`), so comapping again along `blocToBI` and composing (`Filter.comap_comap`) gives exactly the comap along `BIProd`, which is `blocWIUniformSpace` by definition — closed by `rfl`.
- **Hypotheses**: the section's implicit `0 < ρᵢ < 1`; the `w^I`-uniformity installed via `letI`.
- **Uses from project**: `blocWIUniformSpace`, `blocToBI`, `BISub`, `Bloc`
- **Used by**: `biRes`, `biRes_blocToBI`, `biRes_continuous`
- **Visibility**: public
- **Lines**: 251–259 (proof 254–259, 6 lines)
- **Notes**: uses `@`-notation to pin the non-instance uniformity.

### `theorem denseRange_blocToBI`
- **Type**: `DenseRange (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: `Bloc` sits densely in the interval ring `B^I` via the corestricted diagonal.
- **How**: Pushes density down to the ambient product with `Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image`; the image `Subtype.val '' range (blocToBI)` equals `range (BIProd)` (elementwise check), whose closure is `BISub` *by definition* (`rfl`), so every point of the subtype is in the preimage.
- **Hypotheses**: the section's implicit `0 < ρᵢ < 1`.
- **Uses from project**: `blocToBI`, `BIProd`, `BISub`, `hatK`
- **Used by**: `biRes`, `biRes_blocToBI`, `biRes_continuous`, `biResQ_id`, `biResQ_comp`, `biResQ'_id`, `biResQ'_comp`
- **Visibility**: public
- **Lines**: 261–280 (proof 263–280, 18 lines)
- **Notes**: the closing `simp [w.2]` discharges membership using the subtype's own property.

### `theorem isUniformAddGroup_blocWI`
- **Type**: `@IsUniformAddGroup (Bloc p F ϖ) (blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) _`
- **What**: The `w^I`-uniformity on `Bloc` is compatible with its additive group structure.
- **How**: `IsUniformAddGroup.comap` applied to the additive monoid hom underlying `BIProd` — a comap of a uniform-group structure along an additive hom is a uniform-group structure.
- **Hypotheses**: the section's implicit `0 < ρᵢ < 1`.
- **Uses from project**: `blocWIUniformSpace`, `BIProd`, `Bloc`
- **Used by**: `uniformContinuous_blocToBI_interpolate`
- **Visibility**: public
- **Lines**: 283–288 (term proof 287–288, 2 lines)
- **Notes**: a `theorem` whose type is the (Prop-valued) class `IsUniformAddGroup`; like `isLocalization_twist_Bloc` it is intentionally not an instance and may be a `warn.classDefReducibility` site.

### `theorem uniformContinuous_blocToBI_interpolate`
- **Type**: `{θ₁ θ₂ : ℝ} (hθ₁0 : 0 ≤ θ₁) (hθ₁1 : θ₁ ≤ 1) (hθ₂0 : 0 ≤ θ₂) (hθ₂1 : θ₂ ≤ 1) (hσ₁0 : 0 < ρ₁ ^ θ₁ * ρ₂ ^ (1 - θ₁)) (hσ₁1 : ρ₁ ^ θ₁ * ρ₂ ^ (1 - θ₁) < 1) (hσ₂0 : …) (hσ₂1 : …) : @UniformContinuous _ _ (blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) _ (blocToBI p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)`
- **What**: **Three-circles / Hadamard**: for interpolated radii `σⱼ = ρ₁^{θⱼ}·ρ₂^{1−θⱼ}` with `θⱼ ∈ [0,1]`, the `J = [σ₁,σ₂]`-diagonal on `Bloc` is uniformly continuous for the coarser `I = [ρ₁,ρ₂]`-uniformity — the restriction map is 1-Lipschitz.
- **How**: Reduces to continuity at `0` via `uniformContinuous_of_tendsto_zero` (legitimate because both sides are uniform additive groups — `isUniformAddGroup_blocWI` and `isUniformAddGroup_BISub`), rewrites the target neighbourhood filter with `exists_wI_ball_subset` / `wI_ball_mem_nhds` and `nhds_induced`, then closes with the interpolation inequality `wLoc_le_max_of_interpolate` in each coordinate together with `wI_BIProd` and `valued_BlocToHatK`, so `max` of the two interpolated values is `≤ ε`.
- **Hypotheses**: `θ₁, θ₂ ∈ [0,1]`; the interpolated radii `σ₁, σ₂` lie in `(0,1)`; the ambient `0 < ρᵢ < 1`.
- **Uses from project**: `blocWIUniformSpace`, `blocToBI`, `isUniformAddGroup_blocWI`, `isUniformAddGroup_BISub`, `BISub`, `BIProd`, `hatK`, `Bloc`, `exists_wI_ball_subset`, `wI`, `wI_ball_mem_nhds`, `wI_BIProd`, `valued_BlocToHatK`, `wLoc_le_max_of_interpolate`
- **Used by**: `biRes`, `biRes_blocToBI`, `biRes_continuous`
- **Visibility**: public
- **Lines**: 290–338 (proof 298–338, 41 lines)
- **Notes**: Proof >30 lines. This is the analytic heart of the file (the three-circles estimate); everything after it is bookkeeping around the dense extension it enables.

### `def biRes`
- **Type**: `{θ₁ θ₂ : ℝ} (hθ₁0 : 0 ≤ θ₁) (hθ₁1 : θ₁ ≤ 1) (hθ₂0 : 0 ≤ θ₂) (hθ₂1 : θ₂ ≤ 1) (hσ₁0 : 0 < ρ₁ ^ θ₁ * ρ₂ ^ (1 - θ₁)) (hσ₁1 : … < 1) (hσ₂0 : 0 < ρ₁ ^ θ₂ * ρ₂ ^ (1 - θ₂)) (hσ₂1 : … < 1) : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)`
- **What**: **The interval-restriction ring map** `B^{[ρ₁,ρ₂]} → B^{[σ₁,σ₂]}` (ticket D-i-t3) for interpolated sub-radii `σⱼ = ρ₁^{θⱼ}·ρ₂^{1−θⱼ}`.
- **How**: Dense extension: `IsDenseInducing.extendRingHom` applied to the uniform embedding `isUniformInducing_blocToBI`, the density `denseRange_blocToBI`, and the uniform continuity `uniformContinuous_blocToBI_interpolate`; the target's completeness comes from `isComplete_BISub` (`.completeSpace_coe`).
- **Hypotheses**: `θ₁, θ₂ ∈ [0,1]`; the interpolated radii lie in `(0,1)`; the ambient `0 < ρᵢ < 1`.
- **Uses from project**: `BISub`, `Bloc`, `blocWIUniformSpace`, `isComplete_BISub`, `isUniformInducing_blocToBI`, `denseRange_blocToBI`, `uniformContinuous_blocToBI_interpolate`
- **Used by**: `biRes_blocToBI`, `biResQ`, `biResQ_blocToBI`, `biRes_continuous`, `biResQ'`, `biResQ'_blocToBI`
- **Visibility**: public
- **Lines**: 340–360 (body 349–360, 12 lines)
- **Notes**: `noncomputable`; installs the `w^I`-uniformity by `letI` and completeness by `haveI` inside the term.

### `theorem biRes_blocToBI`
- **Type**: `{θ₁ θ₂ : ℝ} (hθ₁0 …) (hσ₂1 …) (z : Bloc p F ϖ) : biRes p F ϖ … (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) = blocToBI p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 z`
- **What**: The characterising property of `biRes`: on the dense `Bloc`-layer it is the identity (it just re-reads the same element at the smaller radii).
- **How**: `IsDenseInducing.extend_eq` — the dense extension agrees with the original map on the dense subset — applied with the `isDenseInducing` upgrade of `isUniformInducing_blocToBI` and the continuity of `uniformContinuous_blocToBI_interpolate`.
- **Hypotheses**: same as `biRes`; `z` ranges over `Bloc`.
- **Uses from project**: `biRes`, `blocToBI`, `Bloc`, `BISub`, `blocWIUniformSpace`, `isComplete_BISub`, `isUniformInducing_blocToBI`, `denseRange_blocToBI`, `uniformContinuous_blocToBI_interpolate`
- **Used by**: `biResQ_blocToBI`, `biResQ'_blocToBI`
- **Visibility**: public
- **Lines**: 362–382 (proof 371–382, 12 lines)
- **Notes**: none.

### `def vpiQ` `@[irreducible]`
- **Type**: `(q : ℚ) : NNReal`
- **What**: The radius `|ϖ|^q` attached to a rational exponent `q` — the real-power `perfectoidValuation p F ϖ ^ (q : ℝ)`. Radii shrink as `q` grows.
- **How**: Direct definition as an `NNReal.rpow` of the perfectoid valuation of the pseudo-uniformizer.
- **Hypotheses**: none beyond the ambient perfectoid-field setup.
- **Uses from project**: `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: `vpiQ_pos`, `vpiQ_lt_one`, `vpiQ_interpolate`, `BIQ`, `vpiQ_antitone`, `vpiQ_natCast`, `vpiQ_one`, `vpiQ_frobRoot`, `vpiQ_pPow`
- **Visibility**: public
- **Lines**: 384–387 (body 386–387, 2 lines)
- **Notes**: `noncomputable` and **`@[irreducible]`** — the docstring says this is a deliberate PERF choice, making the radius an opaque atom for instance search (radii appear in type indices of `hatK`, so unfolding would blow up unification). Every downstream lemma therefore has to `rw [vpiQ]` explicitly to see through it.

### `theorem vpiQ_pos`
- **Type**: `(q : ℚ) : 0 < vpiQ p F ϖ q`
- **What**: The rational-exponent radius is strictly positive.
- **How**: Unfold `vpiQ` and apply `NNReal.rpow_pos`, reducing to `|ϖ| ≠ 0`, which follows from `Valuation.ne_zero_iff` and `PseudoUniformizer.toOF_ne_zero`.
- **Hypotheses**: none (`q` arbitrary, including `q ≤ 0`).
- **Uses from project**: `vpiQ`, `PseudoUniformizer.toOF_ne_zero`
- **Used by**: `BIQ`, `biResQ`, `biResQ_blocToBI`, `biResQ_id`, `biResQ_comp`, `biResQ'`, `biResQ'_blocToBI`, `biResQ'_id`, `biResQ'_comp` (as the `0 < ρ` argument everywhere in the rational-exponent API)
- **Visibility**: public
- **Lines**: 389–393 (proof 389–393, 5 lines)
- **Notes**: none.

### `theorem vpiQ_lt_one`
- **Type**: `{q : ℚ} (hq : 0 < q) : vpiQ p F ϖ q < 1`
- **What**: For a positive exponent the radius `|ϖ|^q` is `< 1`.
- **How**: Unfold `vpiQ` and apply `NNReal.rpow_lt_one` with the base bound `perfectoidValuation_toOF_lt_one` and the cast `0 < (q : ℝ)`.
- **Hypotheses**: `0 < q`.
- **Uses from project**: `vpiQ`, `perfectoidValuation_toOF_lt_one`
- **Used by**: `BIQ`, `biResQ`, `biResQ_blocToBI`, `biResQ_id`, `biResQ_comp`, `biResQ'`, `biResQ'_blocToBI`, `biResQ'_id`, `biResQ'_comp`
- **Visibility**: public
- **Lines**: 395–398 (proof 395–398, 4 lines)
- **Notes**: none.

### `theorem vpiQ_interpolate`
- **Type**: `{q₁ q₂ r : ℚ} (hne : q₁ ≠ q₂) : vpiQ p F ϖ q₁ ^ (((q₂ - r) / (q₂ - q₁) : ℚ) : ℝ) * vpiQ p F ϖ q₂ ^ (1 - (((q₂ - r) / (q₂ - q₁) : ℚ) : ℝ)) = vpiQ p F ϖ r`
- **What**: The rational radii interpolate geometrically: `|ϖ|^r` is the `θ`-weighted geometric mean of `|ϖ|^{q₁}` and `|ϖ|^{q₂}` for the affine parameter `θ = (q₂−r)/(q₂−q₁)`.
- **How**: Unfolds the three `vpiQ`s and collapses the powers with `NNReal.rpow_mul` and `NNReal.rpow_add` (the latter needs `|ϖ| ≠ 0`, obtained from `PseudoUniformizer.toOF_ne_zero`); the remaining exponent identity `q₁θ + q₂(1−θ) = r` is pure field arithmetic, closed by `push_cast; field_simp; ring` with `q₂ − q₁ ≠ 0`.
- **Hypotheses**: `q₁ ≠ q₂` (so the affine parameter is defined).
- **Uses from project**: `vpiQ`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `OF`
- **Used by**: `biResQ`, `biResQ_continuous`, `biResQ'`, `biResQ'_continuous`
- **Visibility**: public
- **Lines**: 400–418 (proof 405–418, 14 lines)
- **Notes**: this is the bridge that lets the real-exponent `biRes` API be applied to rational exponents.

**Extra section variable** (line 421): `{ρ₁' ρ₂' : NNReal}` — a second pair of radii, for the transport lemmas below.

### `def biCongr`
- **Type**: `(h₁ : ρ₁ = ρ₁') (h₂ : ρ₂ = ρ₂') {hρ₁0 hρ₁1 hρ₂0 hρ₂1 hρ₁0' hρ₁1' hρ₂0' hρ₂1'} : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ≃+* ↥(BISub p F ϖ hρ₁0' hρ₁1' hρ₂0' hρ₂1')`
- **What**: Transport of the interval ring `B^I` along equalities of the radii — and, implicitly, proof-irrelevance in the four positivity/`<1` side conditions.
- **How**: `subst` both radius equalities, after which the two subrings are syntactically equal (the remaining hypotheses are `Prop`s and proof-irrelevant), and return `RingEquiv.refl`.
- **Hypotheses**: `ρ₁ = ρ₁'`, `ρ₂ = ρ₂'`.
- **Uses from project**: `BISub`
- **Used by**: `biCongr_blocToBI`, `biResQ`, `biResQ_blocToBI`, `biCongr_continuous`, `biResQ'`, `biResQ'_blocToBI`
- **Visibility**: public
- **Lines**: 423–432 (body 429–432, 3 lines)
- **Notes**: `noncomputable`; defined in tactic mode (`by subst …; exact RingEquiv.refl _`), which is why the companion `biCongr_blocToBI` is needed to compute with it.

### `theorem biCongr_blocToBI` `@[simp]`
- **Type**: `(h₁ : ρ₁ = ρ₁') (h₂ : ρ₂ = ρ₂') {…} (z : Bloc p F ϖ) : biCongr p F ϖ h₁ h₂ … (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) = blocToBI p F ϖ hρ₁0' hρ₁1' hρ₂0' hρ₂1' z`
- **What**: The transport isomorphism is the identity on the dense `Bloc`-layer.
- **How**: `subst` the two radius equalities, after which both sides are definitionally equal — closed by `rfl`.
- **Hypotheses**: `ρ₁ = ρ₁'`, `ρ₂ = ρ₂'`.
- **Uses from project**: `biCongr`, `blocToBI`, `Bloc`
- **Used by**: `biResQ_blocToBI`, `biResQ'_blocToBI`
- **Visibility**: public
- **Lines**: 434–446 (proof 444–446, 3 lines)
- **Notes**: `@[simp]`.

### `def BIQ`
- **Type**: `(q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) : Subring (hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁) × hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂))`
- **What**: **The rational-exponent interval ring** `B^{[q₁,q₂]}` — `BISub` at the radii `|ϖ|^{q₁}, |ϖ|^{q₂}`. Note the exponent-vs-radius inversion flagged in the docstring: the radius at exponent `q` is `|ϖ|^q`, *decreasing* in `q`.
- **How**: Definitional wrapper: `BISub` at the radii produced by `vpiQ`, with the side conditions supplied by `vpiQ_pos` and `vpiQ_lt_one`.
- **Hypotheses**: `0 < q₁`, `0 < q₂` (needed for the radii to be `< 1`).
- **Uses from project**: `BISub`, `hatK`, `vpiQ`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: `biResQ`, `biResQ_id`, `biResQ'`, `biResQ'_id`
- **Visibility**: public
- **Lines**: 448–454 (body 453–454, 2 lines)
- **Notes**: `noncomputable`.

### `theorem theta_mem_unit`
- **Type**: `{q₁ q₂ r : ℚ} (hlt : q₁ < q₂) (hr₁ : q₁ ≤ r) (hr₂ : r ≤ q₂) : (0 : ℝ) ≤ ((q₂ - r) / (q₂ - q₁) : ℚ) ∧ (((q₂ - r) / (q₂ - q₁) : ℚ) : ℝ) ≤ 1`
- **What**: For `r` inside the interval `[q₁, q₂]`, the affine interpolation parameter `θ = (q₂−r)/(q₂−q₁)` lies in `[0,1]`.
- **How**: `div_nonneg` and `div_le_one` (with positive denominator `q₂ − q₁`) reduce both bounds to linear inequalities dispatched by `linarith`, then cast `ℚ → ℝ`.
- **Hypotheses**: `q₁ < q₂`; `q₁ ≤ r ≤ q₂`.
- **Uses from project**: `[]`
- **Used by**: `biResQ`, `biResQ_continuous`
- **Visibility**: public
- **Lines**: 456–467 (proof 461–467, 7 lines)
- **Notes**: the `'`-primed mirror `theta_mem_unit'` (line 675) handles the reversed order `q₂ < q₁`.

### `def biResQ`
- **Type**: `(q₁ q₂ r₁ r₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt : q₁ < q₂) (hr₁m : q₁ ≤ r₁ ∧ r₁ ≤ q₂) (hr₂m : q₁ ≤ r₂ ∧ r₂ ≤ q₂) : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂) →+* ↥(BIQ p F ϖ r₁ r₂ hr₁ hr₂)`
- **What**: **The rational-exponent restriction map** `B^{[q₁,q₂]} → B^{[r₁,r₂]}` for sub-exponents `r₁, r₂ ∈ [q₁, q₂]` (the D-i-t4 substrate for the curve's chart transitions).
- **How**: Composes the real-exponent `biRes` at the interpolation parameters `θᵢ` (in `[0,1]` by `theta_mem_unit`) with the transport `biCongr` along `vpiQ_interpolate`, which identifies the interpolated radii `|ϖ|^{q₁}{}^{θ}·|ϖ|^{q₂}{}^{1−θ}` with `|ϖ|^{rᵢ}`; the four positivity/`<1` side goals are discharged by rewriting with `vpiQ_interpolate` then `vpiQ_pos` / `vpiQ_lt_one`.
- **Hypotheses**: all four exponents positive; `q₁ < q₂`; both `r₁, r₂` inside `[q₁, q₂]`.
- **Uses from project**: `BIQ`, `biRes`, `biCongr`, `vpiQ_interpolate`, `vpiQ_pos`, `vpiQ_lt_one`, `theta_mem_unit`
- **Used by**: `biResQ_blocToBI`, `biResQ_continuous`, `biResQ_id`, `biResQ_comp`
- **Visibility**: public
- **Lines**: 469–491 (body 475–491, 17 lines)
- **Notes**: `noncomputable`. The `by rw [vpiQ_interpolate …]; exact …` blocks appear four times — a repetition also mirrored verbatim in `biResQ'`.

### `theorem biResQ_blocToBI`
- **Type**: `(q₁ q₂ r₁ r₂ : ℚ) (h₁ h₂ hr₁ hr₂ : 0 < ·) (hlt : q₁ < q₂) (hr₁m hr₂m : … ∧ …) (z : Bloc p F ϖ) : biResQ p F ϖ … (blocToBI p F ϖ (vpiQ_pos … q₁) … z) = blocToBI p F ϖ (vpiQ_pos … r₁) … z`
- **What**: The rational-exponent restriction is the identity on the dense `Bloc`-layer — the computation rule that pins `biResQ` down uniquely.
- **How**: Unfolds `biResQ` to the composite `biCongr ∘ biRes` with `show`, then rewrites with the two dense-layer computation rules `biRes_blocToBI` and `biCongr_blocToBI`.
- **Hypotheses**: as `biResQ`.
- **Uses from project**: `biResQ`, `biCongr`, `biRes`, `blocToBI`, `biRes_blocToBI`, `biCongr_blocToBI`, `vpiQ_pos`, `vpiQ_lt_one`, `Bloc`
- **Used by**: `biResQ_id`, `biResQ_comp`
- **Visibility**: public
- **Lines**: 494–506 (proof 503–506, 4 lines)
- **Notes**: the `show … _ _ _ _ …` with placeholder underscores is what keeps this proof short.

### `theorem biRes_continuous`
- **Type**: `{θ₁ θ₂ : ℝ} (hθ₁0 : 0 ≤ θ₁) … (hσ₂1 : … < 1) : Continuous (biRes p F ϖ (hρ₁0 := hρ₁0) … hθ₁0 hθ₁1 hθ₂0 hθ₂1 hσ₁0 hσ₁1 hσ₂0 hσ₂1)`
- **What**: The interval-restriction map `B^I → B^J` is continuous.
- **How**: `uniformContinuous_uniformly_extend` — the dense uniform extension of a uniformly continuous map is uniformly continuous — fed the same three inputs as `biRes` (`isUniformInducing_blocToBI`, `denseRange_blocToBI`, `uniformContinuous_blocToBI_interpolate`), then `.continuous`; completeness of the target from `isComplete_BISub`.
- **Hypotheses**: `θ₁, θ₂ ∈ [0,1]`; interpolated radii in `(0,1)`.
- **Uses from project**: `biRes`, `blocWIUniformSpace`, `BISub`, `Bloc`, `isComplete_BISub`, `isUniformInducing_blocToBI`, `denseRange_blocToBI`, `uniformContinuous_blocToBI_interpolate`
- **Used by**: `biResQ_continuous`, `biResQ'_continuous`
- **Visibility**: public
- **Lines**: 508–525 (proof 514–525, 12 lines)
- **Notes**: none.

### `theorem biCongr_continuous`
- **Type**: `(h₁ : ρ₁ = ρ₁') (h₂ : ρ₂ = ρ₂') {…} : Continuous (biCongr p F ϖ h₁ h₂ …)`
- **What**: The radius-transport isomorphism is continuous.
- **How**: `subst` both radius equalities so `biCongr` reduces to `RingEquiv.refl`, then `continuous_id`.
- **Hypotheses**: `ρ₁ = ρ₁'`, `ρ₂ = ρ₂'`.
- **Uses from project**: `biCongr`
- **Used by**: `biResQ_continuous`, `biResQ'_continuous`
- **Visibility**: public
- **Lines**: 527–536 (proof 533–536, 4 lines)
- **Notes**: none.

### `theorem biResQ_continuous`
- **Type**: `(q₁ q₂ r₁ r₂ : ℚ) (h₁ h₂ hr₁ hr₂ : 0 < ·) (hlt : q₁ < q₂) (hr₁m hr₂m) : Continuous (biResQ p F ϖ q₁ q₂ r₁ r₂ h₁ h₂ hr₁ hr₂ hlt hr₁m hr₂m)`
- **What**: The rational-exponent restriction map is continuous.
- **How**: Unfolds `biResQ` into `biCongr ∘ biRes` and composes `biCongr_continuous` (at the equalities supplied by `vpiQ_interpolate`) with `biRes_continuous` (at the parameters certified by `theta_mem_unit`).
- **Hypotheses**: as `biResQ` — all exponents positive, `q₁ < q₂`, `r₁, r₂ ∈ [q₁, q₂]`.
- **Uses from project**: `biResQ`, `biCongr_continuous`, `biRes_continuous`, `vpiQ_interpolate`, `theta_mem_unit`
- **Used by**: `biResQ_id`, `biResQ_comp`
- **Visibility**: public
- **Lines**: 538–549 (proof 542–549, 8 lines)
- **Notes**: none.

### `theorem biResQ_id`
- **Type**: `(q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) (hlt : q₁ < q₂) : biResQ p F ϖ q₁ q₂ q₁ q₂ h₁ h₂ h₁ h₂ hlt ⟨le_refl q₁, hlt.le⟩ ⟨hlt.le, le_refl q₂⟩ = RingHom.id ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)`
- **What**: **Identity law** of the restriction system: restricting `B^{[q₁,q₂]}` to the same interval is the identity ring hom.
- **How**: A density argument — `DenseRange.equalizer` applied to `denseRange_blocToBI`: two continuous maps (`biResQ_continuous` and `continuous_id`) agreeing on the dense `Bloc`-layer agree everywhere, and on that layer the agreement is exactly `biResQ_blocToBI`. Then `RingHom.ext` upgrades the function equality to hom equality.
- **Hypotheses**: `0 < q₁`, `0 < q₂`, `q₁ < q₂`.
- **Uses from project**: `biResQ`, `BIQ`, `denseRange_blocToBI`, `biResQ_continuous`, `biResQ_blocToBI`, `blocToBI`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: unused in file (exported functoriality law)
- **Visibility**: public
- **Lines**: 551–568 (proof 555–568, 14 lines)
- **Notes**: none.

### `theorem biResQ_comp`
- **Type**: `(q₁ q₂ r₁ r₂ s₁ s₂ : ℚ) (h₁ h₂ hr₁ hr₂ hs₁ hs₂ : 0 < ·) (hlt : q₁ < q₂) (hlt' : r₁ < r₂) (hr₁m hr₂m hs₁m hs₂m) : (biResQ p F ϖ r₁ r₂ s₁ s₂ …).comp (biResQ p F ϖ q₁ q₂ r₁ r₂ …) = biResQ p F ϖ q₁ q₂ s₁ s₂ …`
- **What**: **Composition law** of the restriction system: restricting `[q₁,q₂] → [r₁,r₂] → [s₁,s₂]` equals restricting `[q₁,q₂] → [s₁,s₂]` directly. Together with `biResQ_id` this makes `q ↦ B^{[q₁,q₂]}` a functor on nested rational intervals.
- **How**: Same density scheme as `biResQ_id`: `DenseRange.equalizer` on `denseRange_blocToBI`, with continuity of both sides from `biResQ_continuous` (composed for the left side) and agreement on the dense layer by three rewrites with `biResQ_blocToBI`; finished by `RingHom.ext`.
- **Hypotheses**: all six exponents positive; `q₁ < q₂` and `r₁ < r₂`; `r₁, r₂ ∈ [q₁, q₂]` and `s₁, s₂ ∈ [r₁, r₂]` (the target membership `s ∈ [q₁,q₂]` is derived by `le_trans`).
- **Uses from project**: `biResQ`, `denseRange_blocToBI`, `biResQ_continuous`, `biResQ_blocToBI`, `blocToBI`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: unused in file (exported functoriality law)
- **Visibility**: public
- **Lines**: 570–605 (proof 580–605, 26 lines)
- **Notes**: none.

### `theorem vpiQ_antitone`
- **Type**: `{q q' : ℚ} (h : q ≤ q') : vpiQ p F ϖ q' ≤ vpiQ p F ϖ q`
- **What**: The radius `|ϖ|^q` is antitone in the exponent — larger exponent means smaller radius (the orientation flagged in `BIQ`'s docstring).
- **How**: Unfolds `vpiQ` twice and applies `NNReal.rpow_le_rpow_of_exponent_ge`, whose side conditions are `0 < |ϖ|` (via `Valuation.ne_zero_iff` and `PseudoUniformizer.toOF_ne_zero`) and `|ϖ| ≤ 1` (from `perfectoidValuation_toOF_lt_one`).
- **Hypotheses**: `q ≤ q'`.
- **Uses from project**: `vpiQ`, `PseudoUniformizer.toOF_ne_zero`, `perfectoidValuation_toOF_lt_one`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 607–616 (proof 609–616, 8 lines)
- **Notes**: none.

### `theorem vpiQ_natCast`
- **Type**: `(n : ℕ) : vpiQ p F ϖ (n : ℚ) = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ n`
- **What**: At a natural-number exponent the rational radius is the ordinary `n`-th power of `|ϖ|`.
- **How**: Unfolds `vpiQ`, normalises the double cast `ℕ → ℚ → ℝ` to `ℕ → ℝ` by `push_cast`, and applies `NNReal.rpow_natCast`.
- **Hypotheses**: none.
- **Uses from project**: `vpiQ`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: `vpiQ_one`
- **Visibility**: public
- **Lines**: 618–625 (proof 622–625, 4 lines)
- **Notes**: none.

### `theorem vpiQ_one`
- **Type**: `vpiQ p F ϖ 1 = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)`
- **What**: The radius at exponent `1` is the base radius `|ϖ|`.
- **How**: Specialise `vpiQ_natCast` at `n = 1` and simplify with `pow_one` and `Nat.cast_one`.
- **Hypotheses**: none.
- **Uses from project**: `vpiQ`, `vpiQ_natCast`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 627–632 (proof 630–632, 3 lines)
- **Notes**: none.

### `theorem perfectoidValuation_frobRoot_rpow`
- **Type**: `(s : ℕ) : perfectoidValuation p F ((PseudoUniformizer.toOF F (PseudoUniformizer.frobRoot p F ϖ s) : OF F) : F) = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (((p : ℝ) ^ s)⁻¹)`
- **What**: The valuation of the `p^s`-th Frobenius root of `ϖ` is the `(1/p^s)`-th real power of `|ϖ|`.
- **How**: Starts from the integral statement `perfectoidValuation_frobRoot_pow` (`|ϖ^{1/p^s}|^{p^s} = |ϖ|`), converts the `ℕ`-power to an `rpow` with `NNReal.rpow_natCast`, collapses via `NNReal.rpow_mul`, and cancels the exponent by `mul_inv_cancel₀` (with `(p:ℝ)^s ≠ 0` from `Nat.Prime.pos` and `positivity`).
- **Hypotheses**: `p` prime (from the ambient `Fact`).
- **Uses from project**: `perfectoidValuation`, `PseudoUniformizer.toOF`, `PseudoUniformizer.frobRoot`, `perfectoidValuation_frobRoot_pow`, `OF`
- **Used by**: `vpiQ_frobRoot`
- **Visibility**: public
- **Lines**: 634–647 (proof 640–647, 8 lines)
- **Notes**: none.

### `theorem vpiQ_frobRoot`
- **Type**: `(s : ℕ) (q : ℚ) : vpiQ p F (PseudoUniformizer.frobRoot p F ϖ s) q = vpiQ p F ϖ (q / (p ^ s : ℚ))`
- **What**: **Twist bridge, root side**: changing the pseudo-uniformizer to its `p^s`-th Frobenius root rescales the rational exponent by `1/p^s`, giving the same radius.
- **How**: Unfolds both `vpiQ`s, substitutes `perfectoidValuation_frobRoot_rpow`, merges the two exponents with `NNReal.rpow_mul`, and closes the exponent identity `q · (p^s)⁻¹ = q/p^s` by `push_cast; field_simp`.
- **Hypotheses**: `p` prime (used only to get `(p:ℝ)^s ≠ 0`).
- **Uses from project**: `vpiQ`, `PseudoUniformizer.frobRoot`, `perfectoidValuation_frobRoot_rpow`
- **Used by**: unused in file (feeds the uniformizer-twist comparison downstream)
- **Visibility**: public
- **Lines**: 649–660 (proof 653–660, 8 lines)
- **Notes**: none.

### `theorem vpiQ_pPow`
- **Type**: `(m : ℕ) (hm : 0 < m) (q : ℚ) : vpiQ p F (PseudoUniformizer.pPow F ϖ m hm) q = vpiQ p F ϖ (q * m)`
- **What**: **Twist bridge, power side**: replacing `ϖ` by `ϖ^m` scales the rational exponent by `m`.
- **How**: Unfolds both `vpiQ`s, rewrites the base with `perfectoidValuation_pPow`, converts the `ℕ`-power to an `rpow` (`NNReal.rpow_natCast`) and merges exponents with `NNReal.rpow_mul`; the residual `q·m` identity is `push_cast; ring`.
- **Hypotheses**: `0 < m`.
- **Uses from project**: `vpiQ`, `PseudoUniformizer.pPow`, `perfectoidValuation_pPow`
- **Used by**: unused in file (feeds the uniformizer-twist comparison downstream)
- **Visibility**: public
- **Lines**: 662–671 (proof 666–671, 6 lines)
- **Notes**: none.

### `theorem theta_mem_unit'`
- **Type**: `{q₁ q₂ r : ℚ} (hlt : q₂ < q₁) (hr₁ : q₂ ≤ r) (hr₂ : r ≤ q₁) : (0 : ℝ) ≤ (((q₂ - r) / (q₂ - q₁) : ℚ) : ℝ) ∧ (((q₂ - r) / (q₂ - q₁) : ℚ) : ℝ) ≤ 1`
- **What**: The mirror of `theta_mem_unit` for the *decreasing-exponent* orientation `q₂ < q₁`: the same affine parameter `(q₂−r)/(q₂−q₁)` still lies in `[0,1]`.
- **How**: Rewrites the quotient by cancelling signs (`neg_div_neg_eq`) into `(r−q₂)/(q₁−q₂)`, then `div_nonneg` and `div_le_one` reduce both bounds to `linarith` goals; casts `ℚ → ℝ` at the end.
- **Hypotheses**: `q₂ < q₁`; `q₂ ≤ r ≤ q₁`.
- **Uses from project**: `[]`
- **Used by**: `biResQ'`, `biResQ'_continuous`
- **Visibility**: public
- **Lines**: 673–688 (proof 678–688, 11 lines)
- **Notes**: exists solely because the exponent-vs-radius orientation is inverted (`BIQ`'s docstring); the pairing `(q₁,q₂)` in `BIQ` is radius-ordered, so both `q₁ < q₂` and `q₂ < q₁` occur in practice.

### `def biResQ'`
- **Type**: `(q₁ q₂ r₁ r₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt : q₂ < q₁) (hr₁m : q₂ ≤ r₁ ∧ r₁ ≤ q₁) (hr₂m : q₂ ≤ r₂ ∧ r₂ ≤ q₁) : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂) →+* ↥(BIQ p F ϖ r₁ r₂ hr₁ hr₂)`
- **What**: **The rational-exponent restriction map in the decreasing orientation** `q₂ < q₁` — the exact analogue of `biResQ` for radius-ordered exponent pairs.
- **How**: Identical construction to `biResQ`: `biCongr` (along `vpiQ_interpolate`, invoked with `hlt.ne'` rather than `hlt.ne`) composed with `biRes` at the parameters certified by `theta_mem_unit'`; side goals by `rw [vpiQ_interpolate …]` then `vpiQ_pos` / `vpiQ_lt_one`.
- **Hypotheses**: all four exponents positive; `q₂ < q₁`; `r₁, r₂ ∈ [q₂, q₁]`.
- **Uses from project**: `BIQ`, `biCongr`, `biRes`, `vpiQ_interpolate`, `vpiQ_pos`, `vpiQ_lt_one`, `theta_mem_unit'`
- **Used by**: `biResQ'_blocToBI`, `biResQ'_continuous`, `biResQ'_id`, `biResQ'_comp`
- **Visibility**: public
- **Lines**: 690–713 (body 697–713, 17 lines)
- **Notes**: `noncomputable`. A near-verbatim clone of `biResQ` (lines 469–491) differing only in `hlt.ne'` vs `hlt.ne` and `theta_mem_unit'` vs `theta_mem_unit` — the strongest dedup candidate in the file, e.g. by abstracting the orientation into a single lemma taking `q₁ ≠ q₂` plus a membership hypothesis.

### `theorem biResQ'_blocToBI`
- **Type**: `(q₁ q₂ r₁ r₂ : ℚ) (h₁ h₂ hr₁ hr₂ : 0 < ·) (hlt : q₂ < q₁) (hr₁m hr₂m) (z : Bloc p F ϖ) : biResQ' p F ϖ … (blocToBI p F ϖ (vpiQ_pos … q₁) … z) = blocToBI p F ϖ (vpiQ_pos … r₁) … z`
- **What**: `biResQ'` is the identity on the dense `Bloc`-layer.
- **How**: `show` unfolds to `biCongr ∘ biRes`, then rewrites with `biRes_blocToBI` and `biCongr_blocToBI` — identical to `biResQ_blocToBI`.
- **Hypotheses**: as `biResQ'`.
- **Uses from project**: `biResQ'`, `biCongr`, `biRes`, `blocToBI`, `biRes_blocToBI`, `biCongr_blocToBI`, `vpiQ_pos`, `vpiQ_lt_one`, `Bloc`
- **Used by**: `biResQ'_id`, `biResQ'_comp`
- **Visibility**: public
- **Lines**: 715–727 (proof 724–727, 4 lines)
- **Notes**: proof body is byte-identical to `biResQ_blocToBI`'s (line 506 vs 727).

### `theorem biResQ'_continuous`
- **Type**: `(q₁ q₂ r₁ r₂ : ℚ) (h₁ h₂ hr₁ hr₂ : 0 < ·) (hlt : q₂ < q₁) (hr₁m hr₂m) : Continuous (biResQ' p F ϖ q₁ q₂ r₁ r₂ h₁ h₂ hr₁ hr₂ hlt hr₁m hr₂m)`
- **What**: The decreasing-orientation restriction map is continuous.
- **How**: Unfolds `biResQ'` and composes `biCongr_continuous` (at the `vpiQ_interpolate` equalities) with `biRes_continuous` (at the parameters from `theta_mem_unit'`).
- **Hypotheses**: as `biResQ'`.
- **Uses from project**: `biResQ'`, `biCongr_continuous`, `biRes_continuous`, `vpiQ_interpolate`, `theta_mem_unit'`
- **Used by**: `biResQ'_id`, `biResQ'_comp`
- **Visibility**: public
- **Lines**: 730–741 (proof 734–741, 8 lines)
- **Notes**: mirror of `biResQ_continuous`.

### `theorem biResQ'_id`
- **Type**: `(q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) (hlt : q₂ < q₁) : biResQ' p F ϖ q₁ q₂ q₁ q₂ h₁ h₂ h₁ h₂ hlt ⟨hlt.le, le_refl q₁⟩ ⟨le_refl q₂, hlt.le⟩ = RingHom.id ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)`
- **What**: **Identity law, decreasing orientation**: `biResQ'` from an interval to itself is the identity.
- **How**: `DenseRange.equalizer` on `denseRange_blocToBI` against `continuous_id`, with continuity from `biResQ'_continuous` and dense-layer agreement from `biResQ'_blocToBI`; `RingHom.ext` converts the function equality into hom equality.
- **Hypotheses**: `0 < q₁`, `0 < q₂`, `q₂ < q₁`.
- **Uses from project**: `biResQ'`, `BIQ`, `denseRange_blocToBI`, `biResQ'_continuous`, `biResQ'_blocToBI`, `blocToBI`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: unused in file (exported functoriality law)
- **Visibility**: public
- **Lines**: 743–760 (proof 747–760, 14 lines)
- **Notes**: mirror of `biResQ_id`.

### `theorem biResQ'_comp`
- **Type**: `(q₁ q₂ r₁ r₂ s₁ s₂ : ℚ) (h₁ h₂ hr₁ hr₂ hs₁ hs₂ : 0 < ·) (hlt : q₂ < q₁) (hlt' : r₂ < r₁) (hr₁m hr₂m hs₁m hs₂m) : (biResQ' p F ϖ r₁ r₂ s₁ s₂ …).comp (biResQ' p F ϖ q₁ q₂ r₁ r₂ …) = biResQ' p F ϖ q₁ q₂ s₁ s₂ …`
- **What**: **Composition law, decreasing orientation**: nested `biResQ'` restrictions compose to the direct one.
- **How**: `DenseRange.equalizer` on `denseRange_blocToBI`, continuity of both sides from `biResQ'_continuous` (composed on the left), dense-layer agreement by three rewrites with `biResQ'_blocToBI`, then `RingHom.ext`.
- **Hypotheses**: all six exponents positive; `q₂ < q₁`, `r₂ < r₁`; `r₁, r₂ ∈ [q₂, q₁]`, `s₁, s₂ ∈ [r₂, r₁]` (target memberships by `le_trans`).
- **Uses from project**: `biResQ'`, `denseRange_blocToBI`, `biResQ'_continuous`, `biResQ'_blocToBI`, `blocToBI`, `vpiQ_pos`, `vpiQ_lt_one`
- **Used by**: unused in file (exported functoriality law)
- **Visibility**: public
- **Lines**: 762–797 (proof 772–797, 26 lines)
- **Notes**: mirror of `biResQ_comp`; the pair (`biResQ_comp`, `biResQ'_comp`) is ~50 duplicated lines.

---

### File Summary
- **Total declarations**: 42 (9 defs, 33 lemmas/theorems, 0 instances, 0 structures/classes/abbrevs)
- **Key API (used by 3+ others in this file)**:
  - `blocToBI` (11 consumers) — the dense `Bloc → B^I` layer through which every map is characterised
  - `denseRange_blocToBI` (7) and `blocWIUniformSpace` (6) — the density/uniformity substrate
  - `vpiQ` (9), `vpiQ_pos` (9), `vpiQ_lt_one` (9) — the rational-radius atom and its two side conditions
  - `biRes` (6), `biCongr` (6) — the real-exponent restriction and the radius transport
  - `vpiQ_interpolate` (4), `BIQ` (4), `biResQ` (4), `biResQ'` (4), `blocTwistEquiv` (4)
  - `isLocalization_twist_Bloc` (3), `isUniformInducing_blocToBI` (3), `uniformContinuous_blocToBI_interpolate` (3)
- **Unused declarations** (no consumer *inside* this file — all are intended exports to the curve's chart-transition layer): `wLoc_blocTwistEquiv`, `BISub_twist`, `biResQ_id`, `biResQ_comp`, `vpiQ_antitone`, `vpiQ_one`, `vpiQ_frobRoot`, `vpiQ_pPow`, `biResQ'_id`, `biResQ'_comp`
- **Declarations with `sorry`**: none — the file is sorry-free (no `sorry`, `admit`, `TODO` or `FIXME` anywhere)
- **Declarations with `set_option`**: none per-declaration. Two file-level options at lines 29–30: `linter.overlappingInstances false` and `warn.classDefReducibility false`. The clear consumer of the latter is **`blocWIUniformSpace`** (line 239), a plain `def` whose result type is the class `UniformSpace` and which is deliberately neither `@[reducible]` nor an `instance`; the Prop-valued class-typed theorems `isLocalization_twist_Bloc` (`IsLocalization`) and `isUniformAddGroup_blocWI` (`IsUniformAddGroup`) are the other candidates. `linter.overlappingInstances` is presumably for the many `letI`/`haveI` uniformity installations that shadow ambient instances.
- **Proofs > 30 lines**:
  - `isLocalization_twist_Bloc` — lines 48–120 (~73 lines)
  - `uniformContinuous_blocToBI_interpolate` — lines 298–338 (41 lines)
  - (next largest, both under the bar: `biResQ_comp` 26 lines, `biResQ'_comp` 26 lines)
- **Other attributes**: `@[simp]` on `blocTwistEquiv_algebraMap` and `biCongr_blocToBI`; `@[irreducible]` on `vpiQ` (deliberate PERF choice per its docstring).
- **Dedup opportunities**: the `biResQ*` / `biResQ'*` families (lines 469–605 vs 690–797) are near-verbatim clones differing only in `hlt.ne` vs `hlt.ne'` and `theta_mem_unit` vs `theta_mem_unit'`; the `hexp` power-splitting block inside `isLocalization_twist_Bloc` is duplicated across its two fields (lines 74–85 and 97–108).
