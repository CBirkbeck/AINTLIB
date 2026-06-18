# Inventory: ./HasseWeil/WeilPairing/SeparableScaling.lean

**File purpose**: The **CoordHom-free Weil-pairing scaling engine** `e_ℓ(φS, φT) = e_ℓ(S, T)^{deg φ}`
for separable isogenies `φ` of `E/K̄`, built without any coordinate-ring restriction `φ.CoordHom`
(which does not exist for the separable `1 − π` / `rπ − s` — poles at the affine kernel). The dual
point is supplied as an **abstract** `δ : E.Point →+ E.Point` satisfying the dual relation
`δ ∘ φ = [#ker φ]` (Silverman III.6.2a), feeding the genuinely-geometric `weilPairing_adjoint_core`.
The file contains TWO parallel chains: an EARLIER `…_of_dualComp` chain (abstract dual `δ` + dual
relation `hdc`), and a LATER `…_noδ` chain (reviewer round-22 Q3) that **eliminates `δ` entirely** by
reading the dual point `#ker(φ)•T` off the primitive σ-bridge. The `_noδ` chain is what the live
Hasse-bound proof uses.

**Imports**: `HasseWeil.WeilPairing.HfactLemma`, `HasseWeil.WeilPairing.PicDualDivisorClassLemma`,
`HasseWeil.WeilPairing.DetDeg`

**Total declarations**: 16 theorems. **LIVE/total per verified dependency analysis: 7/16.**
The 7 LIVE are the `…_noδ` / `…_noδ_card` chain (the δ-free route reaching the live `weilScales_noδ`
/ `weilScales_noδ_card` consumed by `OneSubProjOrdTransport.lean` + `PencilComapScaling.lean`). The 9
`…_of_dualComp` decls are **DEAD / SUPERSEDED** (the δ-based predecessor; imported but off the live
proof DAG — their only consumers are the superseded `OneSubScaling`/`OneSubDualDivisor`/
`PencilDualDivisor` divisor-dual routes).

**Flags**: no `sorry`, no `maxHeartbeats`. Two `set_option linter.unusedVariables false in`
(on `weilScales_of_dualComp` and `weilScales_noδ`). Several proofs 30–45 lines.

---

## Declarations

### `theorem sigma_pullbackDivisor_kappaDivisor_eq_dual`  — **DEAD / SUPERSEDED**
- **What**: σ-point identity for an abstract dual `δ`: `σ(φ^*((T)−(O))) = δ T`, from the dual relation
  `hdc` at a preimage `P₀` of `T`.
- **How**: `sigma_pullbackDivisor_kappaDivisor` (primitive σ-bridge) + `hdc` at `P₀` + `mulByInt_apply`,
  `natCast_zsmul`. **Hypotheses**: `Finite φ.ker`, `hdc : δ ∘ φ = [#ker φ]`, `hP₀ : φ P₀ = T`.
- **Uses from project**: `sigma_pullbackDivisor_kappaDivisor`, `pullbackDivisor`, `kappaDivisor`,
  `mulByInt_apply`. **Used by**: `pullbackDivisorClass_of_dualComp`,
  `pullbackDivisorClass_of_dualComp_image` (3 intra-uses). **Visibility**: public.
- **Lines**: 101–115, ~6 lines. **Notes**: superseded by the primitive σ-bridge used directly in the
  `_noδ` chain (`pullbackDivisorClass_image_noδ`).

### `theorem pullbackDivisorClass_of_dualComp`  — **DEAD / SUPERSEDED**
- **What**: projective divisor-class identity (Silverman III.6.1b) for abstract `δ` with surjectivity:
  `φ^*((T)−(O)) ∼ (δT)−(O)`.
- **How**: `hsurj` gives a preimage `P₀`; `projIsPrincipal_of_degZero_of_sigma_eq_zero` (Abel,
  char-free) — degree 0 via `degree_pullbackDivisor_kappaDivisor`, σ = 0 via
  `sigma_pullbackDivisor_kappaDivisor_eq_dual`. **Hypotheses**: `Finite φ.ker`, `hdc`, `hsurj`.
- **Uses from project**: `projIsPrincipal_of_degZero_of_sigma_eq_zero`,
  `degree_pullbackDivisor_kappaDivisor`, `kappaDivisor_degree`, `projectiveDivisorSum_sub`,
  `sigma_pullbackDivisor_kappaDivisor_eq_dual`. **Used by**: `hfact_of_dualComp` (intra). **Visibility**: public.
- **Lines**: 129–149, ~21 lines.

### `theorem pullbackDivisorClass_of_dualComp_image`  — **DEAD / SUPERSEDED**
- **What**: image-restricted variant of the above (no surjectivity; explicit preimage `P₀`).
- **How**: identical Abel argument but `P₀`/`hP₀` taken as hypotheses. **Hypotheses**: `Finite φ.ker`,
  `hdc`, `hP₀ : φ P₀ = T`. **Uses from project**: same as `pullbackDivisorClass_of_dualComp`.
- **Used by**: `hfact_of_dualComp_image` (intra). **Visibility**: public. **Lines**: 159–178, ~20 lines.

### `theorem hfact_of_dualComp`  — **DEAD / SUPERSEDED**
- **What**: the separable divisor factorisation `φ^* g_T = c · g_{δT} · ([ℓ]^* k)` (Silverman III.8.2)
  for abstract `δ` + surjectivity (the `hfact` input to `weilPairing_adjoint_core`).
- **How**: `pullbackDivisorClass_of_dualComp` gives the Abel function `k₀`; the heavy divisor engine
  `hfact_projectiveDivisorOf_eq` (abstract `U := δT`); constant extracted by
  `const_unit_of_projectiveDivisorOf_eq_zero`. **Hypotheses**: `Finite φ.ker`, `hφ : ProjOrdTransport φ`,
  `hcomm`, `hdc`, `hsurj`, torsion conditions. **Uses from project**: `pullbackDivisorClass_of_dualComp`,
  `hfact_projectiveDivisorOf_eq`, `weilFunction_ne_zero`, `const_unit_of_projectiveDivisorOf_eq_zero`,
  `projectiveDivisorOf_mul/_inv`. **Used by**: `weilPairing_adjoint_of_dualComp` (intra). **Visibility**: public.
- **Lines**: 205–246, ~42 lines (>30). **Notes**: needs `[IsAlgClosed F]`, `[IsIntegrallyClosed …]`.

### `theorem hfact_of_dualComp_image`  — **DEAD / SUPERSEDED**
- **What**: image-restricted `hfact` (explicit preimage `P₀`, no surjectivity).
- **How**: routes through `pullbackDivisorClass_of_dualComp_image`; otherwise identical to `hfact_of_dualComp`.
- **Uses from project**: `pullbackDivisorClass_of_dualComp_image`, `hfact_projectiveDivisorOf_eq`, etc.
- **Used by**: `weilPairing_adjoint_of_dualComp_image` (intra). **Visibility**: public.
- **Lines**: 253–291, ~39 lines (>30).

### `theorem weilPairing_adjoint_of_dualComp`  — **DEAD / SUPERSEDED**
- **What**: the separable adjoint `e_ℓ(φS, T) = e_ℓ(S, δT)` (Silverman III.8.2) for abstract `δ`.
- **How**: `hfact_of_dualComp` + `weilPairing_adjoint_core`. **Uses from project**: `hfact_of_dualComp`,
  `weilPairing_adjoint_core`. **Used by**: only `OneSubScaling.lean` (a SUPERSEDED divisor-dual route,
  not on the live DAG). **Visibility**: public. **Lines**: 308–325, ~5 lines.

### `theorem weilPairing_adjoint_of_dualComp_image`  — **DEAD / SUPERSEDED**
- **What**: image-restricted adjoint `e_ℓ(φS, φP₀) = e_ℓ(S, δ(φP₀))` (no surjectivity).
- **How**: `hfact_of_dualComp_image` + `weilPairing_adjoint_core`. **Used by**: `weilPairing_scaling_of_dualComp`
  (intra) and `OneSubScaling.lean` (superseded). **Visibility**: public. **Lines**: 334–354, ~5 lines.

### `theorem weilPairing_scaling_of_dualComp`  — **DEAD / SUPERSEDED**
- **What**: the full symplectic scaling `e_ℓ(φS, φT) = e_ℓ(S, T)^{deg φ}` (Silverman III.8.6.1) for
  abstract `δ` + dual relation `hdc` + degree match `hdeg : #ker φ = deg φ`.
- **How**: image-restricted adjoint at `φT` (preimage `T`), `δ(φT) = #ker(φ)•T = (deg φ)•T` via `hdc`+`hdeg`,
  `weilPairing_congr_right`, `weilPairing_nsmul_right`. **Uses from project**:
  `weilPairing_adjoint_of_dualComp_image`, `weilPairing_congr_right`, `weilPairing_nsmul_right`,
  `mulByInt_apply`, `smul_nsmul_eq_zero_right`. **Used by**: `weilScales_of_dualComp` (intra). **Visibility**: public.
- **Lines**: 388–419, ~32 lines (>30). **Notes**: pays the AG-frontier degree match `#ker = deg`;
  the `_noδ_card` route below avoids it.

### `theorem weilScales_of_dualComp`  — **DEAD / SUPERSEDED**
- **What**: the `WeilScales W ℓ hℓF ψ d` bridge (the `FrobMatrixData`-facing form) from the
  `_of_dualComp` scaling, for an isogeny `φ` realising the bare hom `ψ`.
- **How**: `subst`, `zsmul_eq_zero_of_mem_torsion`, then `weilPairing_scaling_of_dualComp`. **Hypotheses**:
  `[Fact ℓ.Prime]`, `Finite φ.ker`, `hψ`, `hd`, `hφ`, `hcommφ`, `δ`, `hdc`, `hdeg`, `hcomm'`.
- **Uses from project**: `weilPairing_scaling_of_dualComp`, `zsmul_eq_zero_of_mem_torsion`, `WeilScales`.
- **Used by**: `OneSubDualDivisor.lean`, `OneSubScaling.lean`, `PencilDualDivisor.lean`,
  **`SeparableTransportBridge.lean` (the dead file)** — ALL superseded divisor-dual routes; NOT on the
  live `_noδ` DAG. **Visibility**: public. **Lines**: 449–477, ~28 lines.

### `theorem pullbackDivisorClass_image_noδ`  — **LIVE**
- **What**: δ-FREE image-restricted projective divisor-class identity:
  `φ^*((φ P₀)−(O)) ∼ (#ker(φ)•P₀)−(O)`. The dual point is the explicit `#ker(φ)•P₀`.
- **How**: `projIsPrincipal_of_degZero_of_sigma_eq_zero` with the **primitive** σ-bridge
  `sigma_pullbackDivisor_kappaDivisor` (preimage `P₀`) — no `δ`, no `hdc`. **Hypotheses**: `Finite φ.ker`, `P₀`.
- **Uses from project**: `projIsPrincipal_of_degZero_of_sigma_eq_zero`, `degree_pullbackDivisor_kappaDivisor`,
  `kappaDivisor_degree`, `projectiveDivisorSum_sub`, `sigma_pullbackDivisor_kappaDivisor`,
  `projectiveDivisorSum_kappaDivisor`. **Used by**: `hfact_image_noδ` (intra). **Visibility**: public.
- **Lines**: 512–528, ~17 lines.

### `theorem hfact_image_noδ`  — **LIVE**
- **What**: δ-FREE image-restricted `hfact`: `φ^* g_{φP₀} = c · g_{#ker(φ)•P₀} · ([ℓ]^* k)`.
- **How**: `pullbackDivisorClass_image_noδ` + `hfact_projectiveDivisorOf_eq` + `const_unit_of_…`.
  **Hypotheses**: `Finite φ.ker`, `hφ : ProjOrdTransport φ`, `hcomm`, `P₀`, torsion conditions.
- **Uses from project**: `pullbackDivisorClass_image_noδ`, `hfact_projectiveDivisorOf_eq`,
  `weilFunction_ne_zero`, `const_unit_of_projectiveDivisorOf_eq_zero`. **Used by**:
  `weilPairing_adjoint_image_noδ` (intra). **Visibility**: public. **Lines**: 539–577, ~39 lines (>30).

### `theorem weilPairing_adjoint_image_noδ`  — **LIVE**
- **What**: δ-FREE image-restricted adjoint `e_ℓ(φS, φP₀) = e_ℓ(S, #ker(φ)•P₀)`.
- **How**: `hfact_image_noδ` + `weilPairing_adjoint_core` (abstract `U := #ker(φ)•P₀`). **Uses from project**:
  `hfact_image_noδ`, `weilPairing_adjoint_core`. **Used by**: `weilPairing_scaling_noδ`,
  `weilPairing_scaling_noδ_card` (intra). **Visibility**: public. **Lines**: 587–604, ~5 lines.

### `theorem weilPairing_scaling_noδ`  — **LIVE**
- **What**: δ-FREE, surjectivity-free symplectic scaling `e_ℓ(φS, φT) = e_ℓ(S, T)^{deg φ}` (degree
  exponent; pays `hdeg : #ker φ = deg φ` only at the final step).
- **How**: `weilPairing_adjoint_image_noδ` at `φT` (preimage `T`), `weilPairing_nsmul_right`, then `hdeg`.
  **Hypotheses**: `Finite φ.ker`, `hφ`, `hcommφ`, `hdeg`, `hcomm'`, torsion. **Uses from project**:
  `weilPairing_adjoint_image_noδ`, `weilPairing_nsmul_right`, `smul_nsmul_eq_zero_right`. **Used by**:
  `weilScales_noδ` (intra). **Visibility**: public. **Lines**: 626–646, ~7 lines.

### `theorem weilScales_noδ`  — **LIVE (key API)**
- **What**: the δ-FREE, surjectivity-free `WeilScales W ℓ hℓF ψ d` bridge (degree exponent `d`).
  The `FrobMatrixData`-facing form with the `δ`/`hdc`/`hsurj` of `weilScales_of_dualComp` ALL dropped.
- **How**: `subst`, `zsmul_eq_zero_of_mem_torsion`, `weilPairing_scaling_noδ`. **Hypotheses**:
  `[Fact ℓ.Prime]`, `Finite φ.ker`, `hψ`, `hd`, `hφ : ProjOrdTransport φ`, `hcommφ`, `hdeg`, `hcomm'`.
- **Uses from project**: `weilPairing_scaling_noδ`, `zsmul_eq_zero_of_mem_torsion`, `WeilScales`.
- **Used by**: **`OneSubProjOrdTransport.lean`** (leaf-2 live capstone `oneSubFrobeniusScaling_of_comapWitness_noδ`)
  and **`PencilComapScaling.lean`** (leaf-3 degree-exponent route). **Visibility**: public. **Lines**: 660–685, ~26 lines.
- **Notes**: `linter.unusedVariables false`.

### `theorem weilPairing_scaling_noδ_card`  — **LIVE**
- **What**: δ-FREE scaling with the **`#ker` exponent**: `e_ℓ(φS, φT) = e_ℓ(S, T)^{#ker φ}` — NO degree
  match `#ker = deg` (the natural σ-bridge output).
- **How**: `weilPairing_adjoint_image_noδ` + `weilPairing_nsmul_right` (final `hdeg` rewrite removed).
  **Uses from project**: `weilPairing_adjoint_image_noδ`, `weilPairing_nsmul_right`,
  `smul_nsmul_eq_zero_right`. **Used by**: `weilScales_noδ_card` (intra). **Visibility**: public.
- **Lines**: 710–729, ~6 lines.

### `theorem weilScales_noδ_card`  — **LIVE (key API)**
- **What**: the δ-FREE `WeilScales W ℓ hℓF ψ (#ker φ)` bridge with the cardinality exponent —
  **no `δ`, no `hdc`, no surjectivity, AND no degree match `#ker = deg`** (the AG-frontier match
  avoided; the exponent is `Nat.card φ.ker ≥ 0`, discharging the bound's `hdeg_nonneg` by `Nat.cast_nonneg`).
- **How**: `subst`, `zsmul_eq_zero_of_mem_torsion`, `weilPairing_scaling_noδ_card`. **Hypotheses**:
  `[Fact ℓ.Prime]`, `Finite φ.ker`, `hψ`, `hφ`, `hcommφ`, `hcomm'`. **Uses from project**:
  `weilPairing_scaling_noδ_card`, `zsmul_eq_zero_of_mem_torsion`, `WeilScales`. **Used by**:
  **`PencilComapScaling.lean`** (the live leaf-3 `#ker`-exponent route used by the actual Hasse-bound
  proof, via `pencilScaling_holds_coprime`). **Visibility**: public. **Lines**: 744–767, ~24 lines.
- **Notes**: `linter.unusedVariables false`. This is the leaf-3 winning route — it dodges `#ker = deg`.

---

## Cross-reference summary

| Decl | LIVE? | External consumer |
|---|---|---|
| `sigma_pullbackDivisor_kappaDivisor_eq_dual` | DEAD | (intra only) |
| `pullbackDivisorClass_of_dualComp(_image)` | DEAD | (intra only) |
| `hfact_of_dualComp(_image)` | DEAD | (intra only) |
| `weilPairing_adjoint_of_dualComp(_image)` | DEAD | OneSubScaling (superseded) |
| `weilPairing_scaling_of_dualComp` | DEAD | (intra only) |
| `weilScales_of_dualComp` | DEAD | OneSubDualDivisor, OneSubScaling, PencilDualDivisor, SeparableTransportBridge (all superseded) |
| `pullbackDivisorClass_image_noδ` | LIVE | (intra) |
| `hfact_image_noδ` | LIVE | (intra) |
| `weilPairing_adjoint_image_noδ` | LIVE | (intra) |
| `weilPairing_scaling_noδ` | LIVE | (intra) |
| **`weilScales_noδ`** | **LIVE** | OneSubProjOrdTransport, PencilComapScaling |
| `weilPairing_scaling_noδ_card` | LIVE | (intra) |
| **`weilScales_noδ_card`** | **LIVE** | PencilComapScaling (the live leaf-3 route) |

**Key live API**: `weilScales_noδ` (degree exponent) and `weilScales_noδ_card` (`#ker` exponent).

## Cleanup findings

- **DEAD set (9): the entire `…_of_dualComp` chain** (`sigma_pullbackDivisor_kappaDivisor_eq_dual`,
  `pullbackDivisorClass_of_dualComp`, `pullbackDivisorClass_of_dualComp_image`, `hfact_of_dualComp`,
  `hfact_of_dualComp_image`, `weilPairing_adjoint_of_dualComp`, `weilPairing_adjoint_of_dualComp_image`,
  `weilPairing_scaling_of_dualComp`, `weilScales_of_dualComp`). It is the abstract-dual `δ` predecessor
  of the δ-free `…_noδ` chain (reviewer round-22 Q3 superseded round-20). Its consumers
  (OneSubScaling, OneSubDualDivisor, PencilDualDivisor, SeparableTransportBridge) are themselves
  superseded divisor-dual routes off the live proof DAG. **Strong candidate to delete the whole
  `…_of_dualComp` block** (9 decls, ~190 lines) together with the divisor-dual consumer files.
- **`_of_dualComp` vs `_noδ` is line-by-line near-duplication**: each `_noδ` lemma is its `_of_dualComp`
  counterpart with `δ`/`hdc` removed and the primitive σ-bridge substituted for
  `sigma_pullbackDivisor_kappaDivisor_eq_dual`. Once the dead `_of_dualComp` block is deleted the
  duplication disappears; no need to unify (the `_noδ` chain is strictly more general).
- **Separability is hand-rolled** via the project's `Isogeny.IsSeparable` field / `ProjOrdTransport`
  carrier, not mathlib `Algebra.IsSeparable`. The scaling itself never references a separability
  predicate directly — separability enters only through the (carried) `ProjOrdTransport φ` and the
  degree match it is paired with upstream.
