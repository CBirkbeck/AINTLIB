# Inventory: ./HasseWeil/WeilPairing/ProjOrdTransportLocal.lean

**File purpose**: Abstracts the `[ℓ]`-`ProjOrdTransport` assembly of `DivisorPullback.lean`
(`ordTransport_affine_mulByInt → inftyOrdTransport_mulByInt → projOrdTransport_mulByInt`) away from
`[ℓ]` to **any** isogeny `φ` of `E/K̄`. It packages the per-place "SamePlace + e = 1" content at the
**valuation-ring level** as the structure `ComapPointValuationWitness φ` (affine-image comap identity
+ infinity transport), then reduces the divisor-pullback functoriality `ProjOrdTransport φ` —
consumed by the divisor-pushforward dual AND the whole pairing scaling — to that single witness. This
is the **shared order-transport reduction** that BOTH the `1 − π` leaf (via `OneSubProjOrdTransport`)
and the `rπ − s` leaf (via `PencilComapScaling`) instantiate.

**Imports**: `HasseWeil.WeilPairing.DivisorPullback`

**Total declarations**: 5 (1 `structure`, 4 `theorem`). **LIVE/total per verified dependency analysis:
7/12** (the "12" counts section-variable context lines attributed here; of the 5 named decls, **4 are
LIVE, 1 is DEAD**). **Flags**: no `sorry`, no `maxHeartbeats`. `ordTransport_of_comap_pointValuation`
~50 lines (>30).

---

## Declarations

### `structure ComapPointValuationWitness`  — **LIVE (key shared abstraction)**
- **What**: bundles, for an isogeny `φ`, the per-place comap-valuation identities, split by image:
  - `affine`: `φ(P) = some x y h_ns ⟹ (pointValuation P).comap φ.pullback = pointValuation ⟨x,y,h_ns⟩`;
  - `affineToInfty`: `φ(P) = O ⟹ (pointValuation P).comap φ.pullback = ordAtInftyValuation`;
  - `infinity`: `InftyOrdTransport φ` (`ord_∞(φ^* h) = ord_∞ h`).
  This is exactly the pair the DVR glue `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one` produces
  from "SamePlace `IsEquiv` + `e = 1` at one uniformizer".
- **How**: `structure … : Prop` over `SmoothPlaneCurve.pointValuation` / `ordAtInftyValuation` /
  `InftyOrdTransport`. **Hypotheses**: none beyond `φ`. **Uses from project**:
  `SmoothPlaneCurve.pointValuation`, `ordAtInftyValuation`, `InftyOrdTransport`, `SmoothPoint`,
  `toAffinePoint`. **Used by**: `ordTransport_of_comap_pointValuation`,
  `projOrdTransport_of_comap_pointValuation`, `comapPointValuationWitness_mulByInt` (intra) — **and
  externally by `AdditionPullback/SamePlace`, `OneSubComapConcrete`, `OneSubAffineResidues`,
  `OneSubInftyResidues`, `PencilComapWitnesses`, `OneSubProjOrdTransport`, `PencilComapScaling`** (7
  files). **Visibility**: public. **Lines**: 72–92, ~21 lines. **Notes**: the cluster's CENTRAL
  shared interface — the `affine` field for `1 − π` is `comap_pointValuation_oneSub_eq_affine`
  (OneSubAffineResidues), for `[−s']`/pencil it is `comapPointValuationWitness_mulByInt` / pencil
  comap lemmas.

### `theorem ordTransport_of_comap_pointValuation`  — **LIVE**
- **What**: the per-affine-point order transport `OrdTransport φ P` from the comap witnesses — i.e.
  `ord_P(φ^* f) = ord_{φ(P)} f` with no ramification factor (verbatim generalisation of
  `ordTransport_affine_mulByInt`).
- **How**: case `f = 0` trivial; else read the additive order off the comap-valuation identity
  (affine or `∞` image) via the `exp`-bridge `pointValuation_eq_exp_neg_of_ord_P_eq`, with
  `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq` / `WithZero.exp_inj` and `omega`.
- **Hypotheses**: `hcomap : ComapPointValuationWitness W φ`, smooth point `P`. **Uses from project**:
  `ComapPointValuationWitness`, `pointValuation_eq_exp_neg_of_ord_P_eq`, `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`,
  `ord_P_zero`/`ord_P_eq_top_iff`, `projOrdAt(_zero/_some)`, `Isogeny.pullback_injective`,
  `Valuation.comap_apply`. **Used by**: `projOrdTransport_of_comap_pointValuation` (intra). **Visibility**: public.
- **Lines**: 101–149, ~50 lines (>30). **Notes**: the order-arithmetic core; uses the project's
  `ord_P`/`pointValuation`/`WithZero.exp` machinery (NOT `HeightOneSpectrum` directly).

### `theorem projOrdTransport_of_comap_pointValuation`  — **LIVE (key API)**
- **What**: **`ProjOrdTransport φ` from the single witness `ComapPointValuationWitness W φ`** — the
  general reduction (Silverman III.4.10c). The divisor-pullback functoriality `div(φ^* h) = φ^*(div h)`
  that the divisor-pushforward dual and the pairing scaling consume.
- **How**: `projOrdTransport_of_affine_of_infinity` fed by `ordTransport_of_comap_pointValuation` (per
  affine point) + `hcomap.infinity`. **Hypotheses**: `hcomap : ComapPointValuationWitness W φ`.
- **Uses from project**: `projOrdTransport_of_affine_of_infinity`, `ordTransport_of_comap_pointValuation`,
  `ProjOrdTransport`. **Used by**: **`OneSubProjOrdTransport.lean`** (leaf-2: `oneSub_hproj_of_comapWitness`
  → the live `oneSubFrobeniusScaling_holds`) and **`PencilComapScaling.lean`** (leaf-3:
  `pencil_hproj_of_comapWitness`). **Visibility**: public. **Lines**: 162–167, ~4 lines. **Notes**:
  the single reduction both live leaves use to turn local comap witnesses into `ProjOrdTransport`.

### `theorem comapPointValuationWitness_mulByInt`  — **LIVE**
- **What**: the `[ℓ]` comap witnesses, packaged from the PROVED affine/infinity `[ℓ]` comap identities
  — a `ComapPointValuationWitness W (mulByInt W ℓ)`.
- **How**: structure literal: `affine := comap_pointValuation_mulByInt_eq_affine`,
  `affineToInfty := comap_pointValuation_mulByInt_eq_infty`, `infinity := inftyOrdTransport_mulByInt`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`. **Uses from project**:
  `comap_pointValuation_mulByInt_eq_affine`, `comap_pointValuation_mulByInt_eq_infty`,
  `inftyOrdTransport_mulByInt`. **Used by**: **`PencilComapWitnesses.lean` (L2227, live)** — supplies
  the comap witness for the `[−s']` = `mulByInt` summand in the leaf-3 pencil assembly. **Visibility**: public.
- **Lines**: 177–184, ~7 lines.

### `theorem projOrdTransport_mulByInt'`  — **DEAD / SUPERSEDED**
- **What**: re-derives `ProjOrdTransport (mulByInt W ℓ)` from `projOrdTransport_of_comap_pointValuation`
  applied to the `[ℓ]` witnesses — a "sanity instantiation" confirming the abstraction recovers the
  shipped `projOrdTransport_mulByInt`.
- **How**: `projOrdTransport_of_comap_pointValuation (comapPointValuationWitness_mulByInt …)`.
- **Uses from project**: `projOrdTransport_of_comap_pointValuation`, `comapPointValuationWitness_mulByInt`.
- **Used by**: **NOTHING** (no external consumer; the real, consumed `projOrdTransport_mulByInt` lives
  in `DivisorPullback.lean` and is used by HfactLemma/PairingNondeg/PairingProps). **Visibility**: public —
  **DEAD**. **Lines**: 189–191, ~2 lines. **Notes**: a faithfulness/sanity check only; safe to delete.

---

## Cross-reference summary

| Decl | LIVE? | External consumer |
|---|---|---|
| `ComapPointValuationWitness` | **LIVE** | SamePlace, OneSubComapConcrete, OneSubAffineResidues, OneSubInftyResidues, PencilComapWitnesses, OneSubProjOrdTransport, PencilComapScaling (7) |
| `ordTransport_of_comap_pointValuation` | **LIVE** | (intra) |
| `projOrdTransport_of_comap_pointValuation` | **LIVE** | OneSubProjOrdTransport, PencilComapScaling |
| `comapPointValuationWitness_mulByInt` | **LIVE** | PencilComapWitnesses (the `[−s']` summand) |
| `projOrdTransport_mulByInt'` | **DEAD** | (none — sanity recovery; superseded by DivisorPullback's `projOrdTransport_mulByInt`) |

**Key live API**: `ComapPointValuationWitness` (the shared per-place witness interface) and
`projOrdTransport_of_comap_pointValuation` (the general `ProjOrdTransport` reduction both leaves use).

## Cleanup findings

- **This file IS the de-duplication done right for order-transport.** `ComapPointValuationWitness` +
  `projOrdTransport_of_comap_pointValuation` is the SINGLE general reduction that the OneSub (`1 − π`)
  and Pencil (`rπ − s`) leaves both instantiate (and even `[ℓ]` recovers it). Contrast with the
  `residPV_*` residue calculus, which is NOT yet shared (it sits in the `1 − π`-specific
  `OneSubAffineResidues.lean`) — see that file's inventory.
- **Order-transport uses the project's own valuation layer**: `SmoothPlaneCurve.pointValuation` /
  `ord_P` / `ordAtInftyValuation` + mathlib `Valuation.comap` / `WithZero.exp`, NOT
  `IsDedekindDomain.HeightOneSpectrum` valuations directly (those are wrapped one level up).
- **One DEAD decl**: `projOrdTransport_mulByInt'` (sanity recovery, no consumer) — safe to delete; the
  consumed `projOrdTransport_mulByInt` lives in `DivisorPullback.lean`.
- **Under-generality note**: `ComapPointValuationWitness.affineToInfty` is the affine half of the
  image-`O` transport; together with `infinity` (`InftyOrdTransport φ`) it slightly overlaps the
  general `projOrdTransport_of_affine_of_infinity` interface. Fine as-is, but a future tidy could fold
  `affineToInfty`+`infinity` into a single image-`O` transport field.
