# Inventory: ./HasseWeil/WeilPairing/SeparableWitnesses.lean

**File purpose**: The **shared per-isogeny separable-witness table** for the base-changed separable
isogenies `(1 − π)_{K̄}` and `(rπ − s)_{K̄}` over `L = AlgebraicClosure K` (CoordHom-free, Route 2A).
Reduces three standard witnesses to single precisely-stated leaves:
- **Witness 3 (`hcomm'`, translation covariance)** — reduced for BOTH isogenies, uniformly, to the
  single generic-point leaf `hgcomm` (`MapTranslateGenericPoint`) via the shipped `hcomm_of_isGenuineWith`;
- **Witness 2 (`#ker = deg`)** — for the pencil, via the general Galois fibre-count
  `card_kernel_eq_degree_of_separable_isogeny`; for `1 − π`, re-exported from `OneSubWitnesses`;
- **Witness 1 (`hsurj`)** — isolated with a precise CoordHom-free signature and a depth note (it is
  NOT free: the divisor-pushforward dual route is circular for these isogenies).

**Imports**: `HasseWeil.WeilPairing.HcommLemma`, `HasseWeil.WeilPairing.OneSubWitnesses`,
`HasseWeil.WeilPairing.PencilDualDivisor`, `HasseWeil.WallA.VSideDual`,
`HasseWeil.EC.SeparableKernelTorsor`

**Total declarations**: 12 named (2 `def`, 10 `theorem`). **LIVE/total per verified dependency
analysis: 7/15** (the "15" counts section-variable context lines the analysis attributes here).
**Flags**: no `sorry` (the only "sorry" token is in a docstring: "no `sorry` in finished decls"),
no `maxHeartbeats`. `pencil_hkerdeg_of_hgcomm_separable` has a long (~30-line) hypothesis signature.

---

## The `hgcomm`-reduction core (the maximally-shared geometric leaf)

### `def MapTranslateGenericPoint`  — **LIVE (the central leaf, used by both leaves)**
- **What**: the generic-point commutation leaf `hgcomm` (Silverman III.8.2, generic-point form) for an
  abstract genuine action `g`: `Point.map τ_S (g P_gen) = g P_gen + lift (φ S)`, i.e.
  `φ(P_gen + S) = φ(P_gen) + φ(S)` at the generic point. The single residual content of the
  translation covariance, NOT derivable from the abstract `Isogeny` fields.
- **How**: pure `Prop` definition over `Affine.Point.map`, `translateAlgEquivOfPoint.toAlgHom`,
  `genericPoint`, `liftPointToKE`. **Hypotheses**: none beyond `φ`, `g`.
- **Uses from project**: `genericPoint`, `liftPointToKE`, `translateAlgEquivOfPoint`, `W_KE`.
- **Used by**: `hcomm_of_mapTranslateGenericPoint(_canonical)`, `hcov_of_mapTranslateGenericPoint_canonical`,
  `oneSub_hcommPrime_of_hgcomm`, `pencil_hcommPrime_of_hgcomm`, `pencil_hkerdeg_of_hgcomm_separable`
  (14 intra-uses) — **and externally by `MapTranslateGenericAdditive`, `FrobeniusGenericCovariance`,
  `WallAGeometricRealization`, `PencilComapWitnesses`, `PencilComapScaling`, `PencilCovariance`**
  (7 external files). **Visibility**: public. **Lines**: 140–145. **Notes**: the de-duplication
  success story — the ONE leaf that both the OneSub and Pencil covariance/kerdeg reductions bottom out at.

### `theorem hcomm_of_mapTranslateGenericPoint`  — **LIVE**
- **What**: the pointwise covariance `τ_S(φ^* z) = φ^*(τ_{φS} z)` for any `z`, from `hgcomm` + genuineness.
- **How**: pure application of the shipped `hcomm_of_isGenuineWith` (whose `hgcomm` hypothesis is
  exactly `hgcomm S`). **Hypotheses**: `IsGenuineWith W φ g`, `MapTranslateGenericPoint W φ g`.
- **Uses from project**: `hcomm_of_isGenuineWith`. **Used by**: `hcomm_of_mapTranslateGenericPoint_canonical`
  (intra) + externally `SeparableTransportBridge` (dead) and `PencilComapWitnesses` (live). **Visibility**: public.
- **Lines**: 153–159, ~3 lines.

### `theorem hcomm_of_mapTranslateGenericPoint_canonical`  — **LIVE**
- **What**: the same covariance specialised to the **free** canonical action `Affine.Point.map φ.pullback`.
- **How**: `hcomm_of_mapTranslateGenericPoint` + `isogeny_isGenuineWith_pointMap`. **Uses from project**:
  `hcomm_of_mapTranslateGenericPoint`, `isogeny_isGenuineWith_pointMap`. **Used by**:
  `oneSub_hcommPrime_of_hgcomm`, `pencil_hcommPrime_of_hgcomm`, `hcov_of_mapTranslateGenericPoint_canonical`
  (intra) + externally `SeparableTransportBridge` (dead), `PencilComapWitnesses` (live). **Visibility**: public.
- **Lines**: 165–172, ~3 lines.

### `theorem hcov_of_mapTranslateGenericPoint_canonical`  — **LIVE**
- **What**: the kernel-translation invariance `hcov` (`τ_k(φ^* z) = φ^* z` for `k ∈ ker φ`) from the
  SAME leaf `hgcomm` (the input to the concrete Galois fibre-count, witness 2).
- **How**: `hcomm_of_mapTranslateGenericPoint_canonical` at `S = k`; `φ(k) = 0` ⟹ `τ_{φk} = τ_0 = refl`
  (`translateAlgEquivOfPoint_zero`/`mem_kernel_iff`). **Uses from project**:
  `hcomm_of_mapTranslateGenericPoint_canonical`, `Isogeny.mem_kernel_iff`. **Used by**:
  `pencil_hkerdeg_of_hgcomm_separable` (intra) + externally `OneSubInftyResidues` (live),
  `PencilComapWitnesses` (live), `SeparableTransportBridge` (dead). **Visibility**: public. **Lines**: 183–193, ~6 lines.
- **Notes**: demonstrates witnesses 2 AND 3 share the single leaf `hgcomm`.

## The two `hcomm'` instantiations

### `theorem oneSub_hcommPrime_of_hgcomm`  — **LIVE**
- **What**: witness 3 for `(1 − π)_{K̄}` — the full `hcomm'` field (per `ℓ,S,T`) from `hgcomm`.
- **How**: pure instantiation of `hcomm_of_mapTranslateGenericPoint_canonical` at `z = weilFunction …`.
- **Uses from project**: `hcomm_of_mapTranslateGenericPoint_canonical`, `oneSubFrobeniusIsogBaseChange`,
  `oneSubFrobeniusPullback_L`, `weilFunction`, `translateAlgEquivOfPoint`. **Used by**: externally
  `MapTranslateGenericAdditive`, `WallAGeometricRealization` (where the LIVE `oneSub_hcommPrime_discharged`
  that the leaf-2 capstone uses is built), `SeparableTransportBridge` (dead). **Visibility**: public.
- **Lines**: 220–250, ~3-line proof, long signature. **Notes**: feeds the LIVE leaf-2 covariance
  (`WallAGeometricRealization.oneSub_hcommPrime_discharged` = this applied to the proved
  `mapTranslateGenericPoint_oneSub_canonical`).

### `theorem pencil_hcommPrime_of_hgcomm`  — **LIVE**
- **What**: witness 3 for `(rπ − s)_{K̄}` — the full `hcomm'` field from `hgcomm`.
- **How**: pure instantiation of `hcomm_of_mapTranslateGenericPoint_canonical` at `z = weilFunction …`.
- **Uses from project**: `hcomm_of_mapTranslateGenericPoint_canonical`, `pencilIsogBaseChange`,
  `weilFunction`, `translateAlgEquivOfPoint`. **Used by**: **`PencilComapScaling` (live)**,
  `PencilCovariance` (live). **Visibility**: public. **Lines**: 256–281, ~3-line proof, long signature.
- **Notes**: feeds the live leaf-3 capstone `PencilComapScaling`/`pencilScaling_holds_coprime`.

## Witness 2 (`#ker = deg`) — pencil + onesub re-export

### `theorem pencil_hkerdeg_of_separable_witnesses`  — **DEAD / SUPERSEDED**
- **What**: `#ker (rπ − s)_{K̄} = deg` via the general Galois fibre-count, from `hsep`/`h_normal`/`h_card`.
- **How**: `card_kernel_eq_degree_of_separable_isogeny`. **Uses from project**:
  `card_kernel_eq_degree_of_separable_isogeny`, `pencilIsogBaseChange`, `Isogeny.IsSeparable`,
  `Isogeny.toAlgebra`, `Normal`, `Isogeny.kernel`. **Used by**: `GapSpines.lean` (OUT of the live
  closure) and `PencilSeparable.lean`. **Visibility**: public. **Lines**: 315–333, ~3 lines.
- **Notes**: the live leaf-3 route uses the **`#ker` EXPONENT** (`weilScales_noδ_card`), which AVOIDS
  the degree match `#ker = deg` entirely — so this witness is off the live DAG (superseded route).

### `theorem pencil_hkerdeg_of_hgcomm_separable`  — **DEAD / SUPERSEDED**
- **What**: same `#ker = deg` via the *concrete* fibre-count, with `hcov` from the shared leaf `hgcomm`
  (the maximally-shared reduction: witnesses 2+3 bottom out at `hgcomm`).
- **How**: `card_kernel_eq_degree_of_separable_concrete` with `hcov_of_mapTranslateGenericPoint_canonical`.
  **Uses from project**: `card_kernel_eq_degree_of_separable_concrete`,
  `hcov_of_mapTranslateGenericPoint_canonical`. **Used by**: `PencilSeparable`,
  `MapTranslateGenericAdditive`. **Visibility**: public. **Lines**: 350–379, signature ~30 lines.
- **Notes**: superseded for the SAME reason as `pencil_hkerdeg_of_separable_witnesses` (the `#ker`-exponent
  route dodges `#ker = deg`).

### `theorem oneSub_hkerdeg_of_degree_eq_pointCount`  — **DEAD / SUPERSEDED (re-export)**
- **What**: re-export of `OneSubWitnesses.oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount`
  for the shared table. **How**: direct delegation. **Uses from project**:
  `oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount`. **Used by**: (no external consumer).
- **Visibility**: public. **Lines**: 385–394, ~3 lines. **Notes**: the original (in OneSubWitnesses) is
  live for the degree-exponent leaf-2 route, but THIS re-export wrapper has no consumer → **DEAD**.

## Witness 1 (`hsurj`) — isolated, superseded by the δ-free route

### `def HsurjWitness`  — **DEAD / SUPERSEDED**
- **What**: the surjectivity statement `Function.Surjective φ.toAddMonoidHom` carried per isogeny
  (Silverman III.4.10a), pinned with a depth note (NOT free; divisor-pushforward dual route is circular).
- **How**: `def … : Prop`. **Uses from project**: `pencilIsogBaseChange`-shaped isogeny. **Used by**:
  (no consumer). **Visibility**: public. **Lines**: 430–432. **Notes**: the live route is
  surjectivity-FREE (`weilScales_noδ(_card)`), so `hsurj` is never carried → DEAD.

### `theorem oneSub_hsurj_of_self_comp_dual`  — **DEAD / SUPERSEDED (re-export)**
- **What**: re-export of `OneSubWitnesses.oneSubFrobeniusIsogBaseChange_hsurj_of_self_comp_dual`.
- **How**: direct delegation. **Uses from project**:
  `oneSubFrobeniusIsogBaseChange_hsurj_of_self_comp_dual`. **Used by**: (no consumer). **Visibility**: public.
- **Lines**: 440–452, ~3 lines.

### `theorem pencil_hsurj_of_self_comp_dual`  — **DEAD / SUPERSEDED**
- **What**: `hsurj` for `(rπ − s)_{K̄}` from a supplied dual self-composition `φ ∘ δ = [N]`.
- **How**: `mulByInt_point_surjective` + `hself` pointwise (mirror of the onesub version). **Uses from
  project**: `mulByInt_point_surjective`, `mulByInt_apply`, `pencilIsogBaseChange`. **Used by**: (no
  consumer). **Visibility**: public. **Lines**: 458–475, ~6 lines.

---

## Cross-reference / live-set summary

| Decl | LIVE? | Notes |
|---|---|---|
| `MapTranslateGenericPoint` | **LIVE** | the central shared leaf (7 external files) |
| `hcomm_of_mapTranslateGenericPoint` | **LIVE** | shipped-lemma wrapper |
| `hcomm_of_mapTranslateGenericPoint_canonical` | **LIVE** | canonical-action covariance |
| `hcov_of_mapTranslateGenericPoint_canonical` | **LIVE** | kernel-translation invariance (witness 2 leaf) |
| `oneSub_hcommPrime_of_hgcomm` | **LIVE** | leaf-2 `hcomm'` (→ `oneSub_hcommPrime_discharged`) |
| `pencil_hcommPrime_of_hgcomm` | **LIVE** | leaf-3 `hcomm'` (→ `PencilComapScaling`) |
| `pencil_hkerdeg_of_separable_witnesses` | DEAD | `#ker=deg` avoided by `#ker`-exponent route |
| `pencil_hkerdeg_of_hgcomm_separable` | DEAD | ditto |
| `oneSub_hkerdeg_of_degree_eq_pointCount` | DEAD | re-export, no consumer |
| `HsurjWitness` | DEAD | surjectivity-free live route |
| `oneSub_hsurj_of_self_comp_dual` | DEAD | re-export, no consumer |
| `pencil_hsurj_of_self_comp_dual` | DEAD | superseded |

**LIVE (6 of 12 named; 7/15 with section context)**: the `hgcomm`-reduction core
(`MapTranslateGenericPoint`, `hcomm_of_mapTranslateGenericPoint(_canonical)`,
`hcov_of_mapTranslateGenericPoint_canonical`) + the two `hcomm'` instantiations.

**DEAD (6)**: the `#ker = deg` witnesses (both pencil + onesub re-export) and all three `hsurj`
witnesses — superseded by the δ-free, surjectivity-free, `#ker`-exponent route (`weilScales_noδ_card`).

## Cleanup findings

- **Separability detection is hand-rolled via `Isogeny.IsSeparable`** (the project's own field) for the
  pencil witness, NOT mathlib `Algebra.IsSeparable`. The Galois fibre-count
  `card_kernel_eq_degree_of_separable_isogeny` / `_concrete` (`EC/SeparableKernelTorsor.lean`) wraps
  the kernel↔Galois-group bijection by hand. (mathlib `Normal` IS used for the field extension.)
- **`MapTranslateGenericPoint` is the de-duplication SUCCESS**: both the OneSub and Pencil
  covariance (`hcomm'`) and kernel-degree (`hcov`) reductions already bottom out at this ONE leaf —
  this is the consolidation the reviewer asked for, landed here (NOT in the dead
  `SeparableTransportBridge.lean`, which merely re-bundles it).
- **The `hsurj` + `#ker=deg` witnesses are now genuinely dead weight** (6 decls): the live route is
  surjectivity-free and uses the `#ker` exponent. The `oneSub_hkerdeg_of_degree_eq_pointCount` and
  `oneSub_hsurj_of_self_comp_dual` re-exports have zero consumers and can be deleted outright; the
  pencil `hkerdeg`/`hsurj` decls survive only via the OUT-of-closure `GapSpines.lean` and the
  superseded `PencilSeparable` route.
- **`pencil_hsurj_of_self_comp_dual` duplicates `oneSubFrobeniusIsogBaseChange_hsurj_of_self_comp_dual`**
  (OneSubWitnesses) verbatim modulo the isogeny — both are the "`φ ∘ δ = [N]` + `[N]` surjective ⟹ `φ`
  surjective" argument. If `hsurj` is ever revived it should be a single isogeny-generic lemma.
