# Inventory: ./HasseWeil/WeilPairing/SeparableTransportBridge.lean

> **STATUS: FULLY DEAD / SUPERSEDED — the entire file is off the live proof DAG.**
> **No file in the repository imports `HasseWeil.WeilPairing.SeparableTransportBridge`** (verified by
> `grep -rl "import …SeparableTransportBridge"` → zero importers; it is also OUT of the transitive
> import closure of `HasseBound.lean`, the live root). Every declaration below is **DEAD**.

**File purpose (as written)**: This was reviewer round-20's "single reusable compatibility layer" —
a `GeometricRealization φ` structure bundling the genuine geometric data of a separable isogeny
(generic-point covariance `hgcomm`, separability/normality/descent, surjectivity, `ProjOrdTransport`),
from which the three per-isogeny separable-scaling witnesses (`Surjective`, `TranslationCovariant`,
`ProjOrdTransport`) plus `#ker = deg` are derived **once** instead of per pencil member. It bridges to
the scaling via `weilScales_of_geometricRealization` (built on the now-DEAD `weilScales_of_dualComp`).

**Why it is dead**: the project converged on the **`δ`-free, surjectivity-free** route
(`SeparableScaling.weilScales_noδ` / `weilScales_noδ_card`, reviewer round-22 Q3). That route reads
the dual point off the primitive σ-bridge and needs neither a `GeometricRealization`, nor a dual `δ`,
nor surjectivity. The live leaf-2/leaf-3 capstones (`OneSubProjOrdTransport.oneSubFrobeniusScaling_holds`,
`PencilComapScaling`/`PencilComapWitnesses.pencilScaling_holds_coprime`) bypass this file entirely.
The reviewer-asked-for consolidation it bundles (`hcomm'`/`hkerdeg` ⟸ the single leaf `hgcomm`) DID
land, but in `SeparableWitnesses.lean` (`hcomm_of_mapTranslateGenericPoint*`,
`hcov_of_mapTranslateGenericPoint_canonical`) — this file is the bundling wrapper that was never wired in.

**Imports**: `HasseWeil.WeilPairing.SeparableWitnesses`, `HasseWeil.WeilPairing.SeparableScaling`

**Total declarations**: 11 (1 `def`, 1 `structure`, 9 `theorem`). **LIVE/total: 0/11.**
**Flags**: no `sorry`, no `maxHeartbeats`. `oneSubFrobeniusScaling_of_geometricRealization` >30 lines (signature).

---

## Declarations (ALL DEAD)

### `def TranslationCovariant`  — **DEAD**
- **What**: the predicate `τ_S(φ^* z) = φ^*(τ_{φS} z)` for all `S, z` — the `hcomm'` shape, as a
  standalone `Prop`. **How**: pure definition over `translateAlgEquivOfPoint`. **Hypotheses**: none
  beyond `φ : Isogeny`. **Uses from project**: `translateAlgEquivOfPoint`. **Used by**: this file's
  `GeometricRealization`-derived lemmas (intra only). **Visibility**: public. **Lines**: 113–116.

### `structure GeometricRealization`  — **DEAD**
- **What**: the reviewer's compatibility bundle for a separable `φ`: fields `hgcomm`
  (`MapTranslateGenericPoint` for the canonical action), `hsep` (`φ.IsSeparable`), `h_normal`
  (function-field extension normal), `hdesc` (generic-point translation torsor), `hsurj`
  (surjectivity), `hproj` (`ProjOrdTransport φ`).
- **How**: `structure … : Prop`. **Uses from project**: `MapTranslateGenericPoint` (SeparableWitnesses),
  `Isogeny.IsSeparable`, `Isogeny.toAlgebra`, `Normal`, `Isogeny.kernel`, `liftPointToKE`,
  `genericPointAct`, `genericPoint`, `ProjOrdTransport`. **Used by**: all the namespace members (intra).
- **Visibility**: public. **Lines**: 133–157, ~25 lines.

### `theorem realization_isGenuineWith`  — **DEAD**
- **What**: the canonical action `Affine.Point.map φ.pullback` is genuine for `φ` (the reviewer's
  *Caution* "comorphism compatibility"). **How**: `HasseWeil.WallA.isogeny_isGenuineWith_pointMap`.
- **Uses from project**: `isogeny_isGenuineWith_pointMap`, `IsGenuineWith`. **Used by**: (none).
- **Visibility**: public. **Lines**: 178–180, 1 line.

### `theorem realization_pullback_eq` / `realization_pointMap_eq`  — **DEAD**
- **What**: `φ.pullback = φ.pullback` / `φ.toAddMonoidHom = φ.toAddMonoidHom` — the reviewer's
  `pullback_eq`/`pointMap_eq`, definitional in this project (the geometric isogeny IS `φ`).
- **How**: `rfl`. **Uses from project**: none. **Used by**: (none). **Visibility**: public.
- **Lines**: 185 / 189, 1 line each. **Notes**: trivial `rfl` placeholders documenting that the
  reviewer's compatibility requirement is automatic.

### `theorem GeometricRealization.translationCovariant`  — **DEAD**
- **What**: derives `TranslationCovariant W φ` from the bundle's `hgcomm`. **How**:
  `hcomm_of_mapTranslateGenericPoint_canonical` (SeparableWitnesses) applied to `hφ.hgcomm`.
- **Uses from project**: `hcomm_of_mapTranslateGenericPoint_canonical`. **Used by**:
  `separable_scaling_witnesses_of_geometricRealization`, `weilScales_of_geometricRealization` (intra).
- **Visibility**: public. **Lines**: 200–202, ~2 lines.

### `theorem GeometricRealization.card_kernel_eq_degree`  — **DEAD**
- **What**: `Nat.card φ.kernel = φ.degree` from the bundle (Silverman III.4.10c). **How**:
  `card_kernel_eq_degree_of_separable_concrete` with `hcov` from `hcov_of_mapTranslateGenericPoint_canonical`
  + `hsep`/`h_normal`/`hdesc`. **Uses from project**: `card_kernel_eq_degree_of_separable_concrete`,
  `hcov_of_mapTranslateGenericPoint_canonical`. **Used by**: `card_ker_eq_degree` (intra). **Visibility**: public.
- **Lines**: 215–219, ~5 lines.

### `theorem GeometricRealization.card_ker_eq_degree`  — **DEAD**
- **What**: `AddMonoidHom.ker` form of `card_kernel_eq_degree`. **How**: definitional restatement.
- **Used by**: `weilScales_of_geometricRealization` (intra). **Visibility**: public. **Lines**: 224–226.

### `theorem separable_scaling_witnesses_of_geometricRealization`  — **DEAD**
- **What**: the reviewer Q5 conjunction `Surjective φ ∧ TranslationCovariant W φ ∧ ProjOrdTransport φ`
  from a `GeometricRealization`. **How**: `⟨hφ.hsurj, hφ.translationCovariant, hφ.hproj⟩`. **Uses from
  project**: `TranslationCovariant`, `ProjOrdTransport`. **Used by**: (none). **Visibility**: public.
- **Lines**: 251–254, ~3 lines.

### `theorem weilScales_of_geometricRealization`  — **DEAD**
- **What**: `WeilScales` from a `GeometricRealization` + abstract dual `δ`/`hdc`. **How**:
  `weilScales_of_dualComp` (the DEAD δ-based bridge) with `hφ.hproj`/`hφ.card_ker_eq_degree`/
  `hφ.translationCovariant`. **Uses from project**: `weilScales_of_dualComp` (DEAD), `mulByInt`.
- **Used by**: (none). **Visibility**: public. **Lines**: 288–300, ~12 lines. **Notes**: built on a
  dead dependency (`weilScales_of_dualComp`), confirming this whole route is superseded.

### `theorem oneSubFrobeniusScaling_of_geometricRealization`  — **DEAD**
- **What**: discharges the leaf-2 `OneSubFrobeniusScaling` for `(1 − π)_{K̄}` from a
  `GeometricRealization` (the "non-vacuity" demonstration). **How**:
  `oneSubFrobeniusScaling_of_divisorDual` (a superseded route) with `hφ.hproj`/`hφ.hsurj` and
  `oneSub_hcommPrime_of_hgcomm hφ.hgcomm`. **Uses from project**: `oneSubFrobeniusScaling_of_divisorDual`,
  `oneSub_hcommPrime_of_hgcomm`, `oneSubFrobeniusIsogBaseChange`, `oneSubFrobeniusPullback_L`.
- **Used by**: (none — the live leaf-2 discharge is `OneSubProjOrdTransport.oneSubFrobeniusScaling_holds`).
- **Visibility**: public. **Lines**: 341–350, signature spans >30 lines. **Notes**: parallel
  superseded leaf-2 proof.

---

## Summary / cleanup recommendation

The whole file (11 decls, 354 lines) is **safe to delete**. It is unimported, off the proof DAG, and
its substantive content (the `hgcomm ⟹ hcomm'`/`hcov` consolidation) lives independently and live in
`SeparableWitnesses.lean`. Its two bridges (`weilScales_of_geometricRealization`,
`oneSubFrobeniusScaling_of_geometricRealization`) are even built on the *also-dead*
`weilScales_of_dualComp` / `oneSubFrobeniusScaling_of_divisorDual`. The `realization_pullback_eq` /
`realization_pointMap_eq` `rfl`-theorems are pure documentation artifacts. No `sorry`,
no `maxHeartbeats`. Deleting it removes one of two consumers' references to the dead
`weilScales_of_dualComp` (SeparableScaling), aiding that file's cleanup too.
