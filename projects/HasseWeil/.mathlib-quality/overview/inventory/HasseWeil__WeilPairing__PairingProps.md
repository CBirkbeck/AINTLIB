# Inventory: ./HasseWeil/WeilPairing/PairingProps.lean

**File purpose**: Proves the two remaining structural properties of the finite-level Weil pairing `e_ℓ : E[ℓ] × E[ℓ] → F` over `K̄`, extending slot-1 bilinearity (`weilPairing_mul_left`, from `Pairing.lean`): **bilinearity in the second slot** `e_ℓ(S, T₁+T₂) = e_ℓ(S,T₁)·e_ℓ(S,T₂)` (III.8.1b, via divisor-pullback functoriality of the Abel–Jacobi function relating the three Weil functions), and **alternating** `e_ℓ(T,T) = 1` (III.8.1d, via a telescoping product of translated Weil functions), with the antisymmetry corollary `e_ℓ(S,T)·e_ℓ(T,S) = 1`. Together with `Pairing.lean` and `PairingNondeg.lean` this completes the full Silverman III.8.1 property suite that `DetDeg` consumes.

**Imports**: `HasseWeil.WeilPairing.Pairing`, `HasseWeil.WeilPairing.DivisorPullback`

**Total declarations**: 9 `theorem`

**Module options**: `set_option linter.unusedSectionVars false`, `linter.unusedDecidableInType false`, `linter.style.longLine false`. No `sorry`, no `maxHeartbeats`.

**Standing hypotheses** (whole file): `{F : Type*} [Field F] [DecidableEq F]`, `(W : WeierstrassCurve F) [W.toAffine.IsElliptic] [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]`. Both sections (`Bilinearity`, `Alternating`) carry `[IsAlgClosed F]`.

---

## Declarations

### `theorem bilinDivisor_isPrincipal`
- **Type**: `(T₁ T₂ : W.toAffine.Point) : (⟨W.toAffine⟩).ProjIsPrincipal (single (T₁+T₂) 1 − single T₁ 1 − single T₂ 1 + single O 1)`
- **What**: **The Abel–Jacobi divisor `D = (T₁+T₂) − (T₁) − (T₂) + (O)` is principal.** Provides the function `k` relating the three Weil functions in slot-2 bilinearity.
- **How**: Applies `projIsPrincipal_of_degZero_of_sigma_eq_zero` (WeilFunction): degree `1−1−1+1 = 0` (via `degreeHom`/`degree_single` + `ring`) and group-sum `(T₁+T₂) − T₁ − T₂ + O = O` (via `projectiveDivisorSum_{add,sub,single}` + `abel`).
- **Hypotheses**: `[IsAlgClosed F]`.
- **Uses from project**: `projIsPrincipal_of_degZero_of_sigma_eq_zero` (WeilFunction), `Curves.ProjectiveDivisor.degreeHom_apply`, `degree_single` (Pullback), `Curves.projectiveDivisorSum_*`, `Affine.Point.toProjectiveSmoothPoint_toAffinePoint`
- **Used by (within file)**: `weilPairing_mul_right`
- **Visibility**: public
- **Lines**: 76–99, proof length: ~17 lines
- **Notes**: File-internal-only.

### `theorem translate_pullback_fixed`
- **Type**: `(ℓ : ℤ) (hℓ0 : ℓ ≠ 0) (S : W.toAffine.Point) (hS : ℓ • S = 0) (z : KE) : translateAlgEquivOfPoint W S ((mulByInt W.toAffine ℓ).pullback z) = (mulByInt W.toAffine ℓ).pullback z`
- **What**: **Covariance of the pullback factor**: for `S ∈ E[ℓ]`, translation `τ_S` fixes any function in the image of `[ℓ].pullback`.
- **How**: Shows `S ∈ ker[ℓ]` (`Isogeny.mem_kernel_iff` + `mulByInt_apply`) and invokes `hcov_mulByInt_of_xy` (the function-field shadow of `[ℓ]∘(·+S) = [ℓ]`, via the division-function invariance `hxy_mulByInt`).
- **Hypotheses**: `[IsAlgClosed F]`, `ℓ ≠ 0`, `S ∈ E[ℓ]`.
- **Uses from project**: `mulByInt` (`.pullback`, `.kernel`, `mulByInt_apply`), `HasseWeil.Isogeny.mem_kernel_iff`, `hcov_mulByInt_of_xy`, `hxy_mulByInt`, `translateAlgEquivOfPoint`
- **Used by (within file)**: `weilPairing_mul_right`. **Used by (project)**: `PairingAdjoint`.
- **Visibility**: public
- **Lines**: 104–110, proof length: ~4 lines

### `theorem weilPairing_mul_right`
- **Type**: `(ℓ) (hℓ) (S T₁ T₂) (hS hT₁ hT₂ h₁₂) : weilPairing W ℓ hℓ S (T₁+T₂) hS h₁₂ = weilPairing W ℓ hℓ S T₁ hS hT₁ * weilPairing W ℓ hℓ S T₂ hS hT₂`
- **What**: **Bilinearity in the second slot** (Silverman III.8.1b): `e_ℓ(S, T₁+T₂) = e_ℓ(S,T₁)·e_ℓ(S,T₂)`.
- **How**: The three Weil functions `g_{T₁}, g_{T₂}, g_{T₁+T₂}` are related via divisor-pullback functoriality. `k` (from `bilinDivisor_isPrincipal`) gives `u = [ℓ]^* k` with `div u = [ℓ]^*(T₁+T₂) − [ℓ]^*(T₁) − [ℓ]^*(T₂) + [ℓ]^*(O)` (`projectiveDivisorOf_pullback_bilinFunction` via `projOrdTransport_mulByInt`). With `weilFunction_divisor` for each `g`, `div(g₁·g₂·u) = div(g₁₂)` (`projectiveDivisorOf_mul` + `abel`), so the quotient has trivial divisor and `const_unit_of_projectiveDivisorOf_eq_zero` extracts `c` with `g₁₂ = c·(g₁·g₂·u)`. Applying `τ_S` (which fixes `c` via `commutes` and `u` via `translate_pullback_fixed`), the engine `pairing_const_mul_invariant_factor` collapses to the claim.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `S, T₁, T₂, T₁+T₂` in `E[ℓ]`.
- **Uses from project**: `mulByInt_ker_finite`, `ProjOrdTransport`/`projOrdTransport_mulByInt`, `bilinDivisor_isPrincipal` (this file), `mulByInt` (`.pullback`, `pullback_injective`), `projectiveDivisorOf_pullback_bilinFunction` (DivisorPullback), `pullbackDiv`, `weilFunction`/`weilFunction_ne_zero`/`weilFunction_divisor` (Pairing), `projectiveDivisorOf_mul`/`projectiveDivisorOf_inv`, `const_unit_of_projectiveDivisorOf_eq_zero`, `pairing_const_mul_invariant_factor`, `translate_pullback_fixed` (this file), `weilPairing`/`weilPairing_translate`, `translateAlgEquivOfPoint`
- **Used by (within file)**: `weilPairing_antisymm`. **Used by (project)**: `Constancy`, `PairingAdjoint`, `DetDeg`.
- **Visibility**: public
- **Lines**: 121–192, proof length: ~66 lines
- **Notes**: Proof >30 lines (the longest; the divisor-functoriality computation).

### `theorem projectiveDivisorOf_prod_range`
- **Type**: `(n : ℕ) (h : ℕ → KE) (hh : ∀ i ∈ Finset.range n, h i ≠ 0) : projectiveDivisorOf (∏ i ∈ range n, h i) = ∑ i ∈ range n, projectiveDivisorOf (h i)`
- **What**: The divisor of a finite product (over `Finset.range n`) of nonzero functions is the sum of the divisors.
- **How**: Induction on `n`; base via `projectiveDivisorOf_one`, step via `projectiveDivisorOf_mul` (with `Finset.prod_ne_zero_iff` for the partial-product nonvanishing).
- **Hypotheses**: `[IsAlgClosed F]`; each factor nonzero on `range n`.
- **Uses from project**: `(⟨W.toAffine⟩).projectiveDivisorOf_one`, `(⟨W.toAffine⟩).projectiveDivisorOf_mul` (PicZero/divisor API)
- **Used by (within file)**: `weilPairing_self`
- **Visibility**: public
- **Lines**: 219–233, proof length: ~12 lines
- **Notes**: File-internal-only. General-purpose; could plausibly live with the divisor API rather than here.

### `theorem weilFunction_translate_prod_ne_zero`
- **Type**: `(ℓ) (hℓ) (T P₀) (hT) (n : ℕ) : (∏ i ∈ range n, translateAlgEquivOfPoint W (i • P₀) (weilFunction W ℓ hℓ T hT)) ≠ 0`
- **What**: The telescoping product `∏ τ_{[i]P₀} g_T` is nonzero.
- **How**: `Finset.prod_ne_zero_iff`; each factor nonzero because translation is a ring automorphism (`map_ne_zero_iff` + injectivity) and `g_T ≠ 0` (`weilFunction_ne_zero`).
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `T ∈ E[ℓ]`.
- **Uses from project**: `translateAlgEquivOfPoint`, `weilFunction`/`weilFunction_ne_zero` (Pairing)
- **Used by (within file)**: `weilPairing_self`
- **Visibility**: public
- **Lines**: 237–243, proof length: ~3 lines
- **Notes**: File-internal-only.

### `theorem weilFunction_translate_div`
- **Type**: `(ℓ) (hℓ) (T) (hT) (S : W.toAffine.Point) : projectiveDivisorOf (τ_S g_T) = pullbackDiv [ℓ] _ (T − ℓ•S) − pullbackDiv [ℓ] _ (0 − ℓ•S)`
- **What**: **The `g_T`-translation law**: `div(τ_S g_T) = [ℓ]^*(T − ℓ•S) − [ℓ]^*(−ℓ•S)` — translating the fibre-difference divisor by `S` shifts both fibres by `−ℓ•S`.
- **How**: `projectiveDivisorOf_translate` rewrites `div(τ_S g_T)` as `equivMapDomain (placeTranslate W S).symm` of `div(g_T)`; `weilFunction_divisor` gives `div(g_T) = [ℓ]^*(T)−[ℓ]^*(O)`. Then, pointwise at every place `w` (`Finsupp.ext`), the general translation law `pullbackDiv_placeTranslate_apply_general` rewrites each term (`f S = ℓ•S` via `mulByInt_apply`).
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `T ∈ E[ℓ]`.
- **Uses from project**: `HasseWeil.projectiveDivisorOf_translate`, `placeTranslate`, `weilFunction`/`weilFunction_divisor`, `mulByInt_ker_finite`, `pullbackDiv`, `HasseWeil.pullbackDiv_placeTranslate_apply_general`, `mulByInt_apply`, `translateAlgEquivOfPoint`
- **Used by (within file)**: `weilPairing_self`
- **Visibility**: public
- **Lines**: 248–285, proof length: ~30 lines
- **Notes**: File-internal-only. Proof ~30 lines (uses two `change`-driven definitional unfoldings because `W_smooth W` is opaque to `rw`).

### `theorem weilPairing_self`
- **Type**: `(ℓ) (hℓ) (T) (hT) : weilPairing W ℓ hℓ T T hT hT = 1`
- **What**: **Alternating**: `e_ℓ(T,T) = 1` (Silverman III.8.1d).
- **How**: Telescoping argument. With `P₀` s.t. `[ℓ]P₀ = T` (`exists_preimage_of_torsion`), `g := ∏_{i<ℓ} τ_{[i]P₀} g_T` is nonzero (`weilFunction_translate_prod_ne_zero`); its divisor telescopes to `0`: each term is `gₛ(i) − gₛ(i+1)` with `gₛ(i) = [ℓ]^*((1−i)•T)` (`weilFunction_translate_div` + point identities), and `Finset.sum_range_sub'` collapses to `[ℓ]^*(T) − [ℓ]^*(T) = 0` using `ℓ•T = 0`. So `g = algebraMap a` is constant (`const_of_projectiveDivisorOf_eq_zero`), hence `τ_{P₀}`-invariant (`commutes`). Reindexing the product gives `τ_{P₀} g = e_ℓ(n•P₀, T)·g`, so `e_ℓ(n•P₀,T) = 1` (`pairing_const_refl`). Finally a sign case-split (`Int.natAbs_eq`, `n•P₀ = ±T`) converts to `e_ℓ(T,T) = 1`, using `weilPairing_mul_left` + `weilPairing_refl_left` in the negative case.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `T ∈ E[ℓ]`.
- **Uses from project**: `exists_preimage_of_torsion`, `weilFunction`/`weilFunction_ne_zero`, `weilFunction_translate_prod_ne_zero`, `projectiveDivisorOf_prod_range`, `weilFunction_translate_div`, `pullbackDiv`, `mulByInt_ker_finite`, `const_of_projectiveDivisorOf_eq_zero`, `translateAlgEquivOfPoint`/`translateAlgEquivOfPoint_add_apply`, `weilPairing`/`weilPairing_translate`/`weilPairing_congr_left`/`weilPairing_mul_left`/`weilPairing_refl_left` (Pairing), `pairing_const_refl`
- **Used by (within file)**: `weilPairing_alternating`, `weilPairing_antisymm`. **Used by (project)**: `DetDeg`.
- **Visibility**: public
- **Lines**: 290–409, proof length: ~119 lines
- **Notes**: Proof >30 lines — by far the longest proof in the cluster (~119 lines). The docstring claims a "slick route via bilinearity + root-of-unity," but the actual proof is the full telescoping/translation argument; the docstring at the file head (around the `Alternating` section) describes the latter accurately. Candidate for `decompose-proof`.

### `theorem weilPairing_alternating`
- **Type**: `(ℓ) (hℓ) (T) (hT) : weilPairing W ℓ hℓ T T hT hT = 1`
- **What**: **Alternating** (named alias of `weilPairing_self`, Silverman III.8.1d).
- **How**: `weilPairing_self W ℓ hℓ T hT`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `T ∈ E[ℓ]`.
- **Uses from project**: `weilPairing_self` (this file), `weilPairing`
- **Used by (within file)**: none. **Used by (project)**: `DetDeg`.
- **Visibility**: public
- **Lines**: 412–414, proof length: 1 line
- **Notes**: **Trivial alias** of `weilPairing_self` (no extra content). Both are exported and used by `DetDeg`; the duplication is purely a naming convenience and could be consolidated to one name (see summary (d)).

### `theorem weilPairing_antisymm`
- **Type**: `(ℓ) (hℓ) (S T) (hS hT) : weilPairing W ℓ hℓ S T hS hT * weilPairing W ℓ hℓ T S hT hS = 1`
- **What**: **Antisymmetry** (Silverman III.8.1c): `e_ℓ(S,T)·e_ℓ(T,S) = 1`.
- **How**: From `1 = e_ℓ(S+T, S+T)` (`weilPairing_self`), expand both slots (`weilPairing_mul_right`, `weilPairing_mul_left` twice), and use the vanishing diagonal terms `e_ℓ(S,S) = e_ℓ(T,T) = 1` (`weilPairing_self`); `one_mul`/`mul_one`/`mul_comm` finish.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `S, T ∈ E[ℓ]`.
- **Uses from project**: `weilPairing`/`weilPairing_self`, `weilPairing_mul_right` (this file), `weilPairing_mul_left` (Pairing)
- **Used by (within file)**: none. **Used by (project)**: `DetDeg`.
- **Visibility**: public
- **Lines**: 419–434, proof length: ~10 lines

---

## Cross-reference summary

| Declaration | Used by (within file) |
|---|---|
| `bilinDivisor_isPrincipal` | `weilPairing_mul_right` |
| `translate_pullback_fixed` | `weilPairing_mul_right` (+ project: PairingAdjoint) |
| `weilPairing_mul_right` | `weilPairing_antisymm` (+ project: Constancy, PairingAdjoint, DetDeg) |
| `projectiveDivisorOf_prod_range` | `weilPairing_self` |
| `weilFunction_translate_prod_ne_zero` | `weilPairing_self` |
| `weilFunction_translate_div` | `weilPairing_self` |
| `weilPairing_self` | `weilPairing_alternating`, `weilPairing_antisymm` (+ project: DetDeg) |
| `weilPairing_alternating` | (project: DetDeg) |
| `weilPairing_antisymm` | (project: DetDeg) |

**Key API** (live exports → all consumed by `DetDeg`): `weilPairing_mul_right`, `weilPairing_self` (= `weilPairing_alternating`), `weilPairing_antisymm`. Plus `translate_pullback_fixed` (reused by `PairingAdjoint`).

## Notes / cleanup analysis

- **(a) Unused within file**: none dead. The four "helper" lemmas (`bilinDivisor_isPrincipal`, `projectiveDivisorOf_prod_range`, `weilFunction_translate_prod_ne_zero`, `weilFunction_translate_div`) are file-internal scaffolding for the two headline theorems; the headline theorems plus `translate_pullback_fixed` are exported.
- **(d) Moral duplication**: `weilPairing_alternating` (L412) is a one-line `:=`-alias of `weilPairing_self` (L290). Both are used by `DetDeg`. Consolidating to a single name (and updating `DetDeg`) would remove a redundant public symbol. Low-risk cleanup.
- **(c) mathlib-fit**: bilinearity/alternating/antisymmetry are stated as plain pointwise multiplicative identities on `weilPairing`, not via a bundled `LinearMap.BilinForm` / mathlib pairing structure. This is appropriate here: `weilPairing` carries dependent hypotheses (`ℓ • S = 0`, `ℓ • T = 0`) so it is not literally a function `E[ℓ] → E[ℓ] → F` that mathlib's `BilinForm` could wrap without first repackaging the pairing on the subtype `E[ℓ]`. If a downstream consumer wanted the bundled symplectic form, the natural place to introduce mathlib's bilinear-form / `Additive`-`ZMod ℓ` API is `DetDeg` (which already imports `RootsOfUnity.rootsOfUnity_addEquiv_zmod`). Flag, not a defect.
- **(b)** No scratch/abandoned content — all on the III.8.1 property path.
- **(decompose) `weilPairing_self`** (~119 lines) is a strong candidate for `/decompose-proof`: the "g is a nonzero constant (telescoping)" block and the "τ_{P₀} g = e_ℓ(n•P₀,T)·g (reindexing)" block are two self-contained lemmas, plus the sign-conversion tail.
- **No `sorry`, no `maxHeartbeats`.** Proofs >30 lines: `weilPairing_self` (~119), `weilPairing_mul_right` (~66), `weilFunction_translate_div` (~30).
