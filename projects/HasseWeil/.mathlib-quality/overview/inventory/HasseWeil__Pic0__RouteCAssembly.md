# Inventory: ./HasseWeil/Pic0/RouteCAssembly.lean

**File**: `HasseWeil/Pic0/RouteCAssembly.lean`
**Total lines**: 583
**Namespace**: `HasseWeil.Pic0.RouteC`
**Imports**: `HasseWeil.Pic0.PicDual`, `HasseWeil.DegreeQuadraticForm`, `HasseWeil.GapSpines`

**Summary**: Assembly file for the Pic⁰-dual route (Route C) to the Hasse-bound Leaf-1 conclusion
`qf_nonneg`. Builds a witness-parametric chain
`picDual(rπ − s) = rV − s → IsDualOf β_dual β → deg(rπ−s) = N → 0 ≤ N`.
No `sorry`, no `set_option maxHeartbeats`, no instances; all 9 declarations are `theorem`.

---

### `theorem picDual_eq_pointMap`

- **Type**: Given an isogeny `β` with CoordHom data, naturality `hnat`, surjectivities `hsurjDual`/`hsurjβ`, and a point-map `δ` satisfying `δ ∘ β = [finrank]`, conclude `picDual β = δ`.
- **What**: Thin wrapper exposing the shipped III.6.1(a) dual-uniqueness result in the Route-C namespace: the Pic⁰ dual is the unique point map satisfying the dual-defining relation.
- **How**: One-line term-proof directly calling `Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq` from `PicDual.lean`.
- **Hypotheses**: CoordHom data for `β` (injectivity, finiteness), Silverman III.3.4 naturality `hnat`, surjectivity of `picDual β` and of `β.toAddMonoidHom`, the dual-defining composition equality.
- **Uses from project**: `Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq` (PicDual)
- **Used by**: unused in file (exported for external callers)
- **Visibility**: public
- **Lines**: 94–108; proof length: 1 line (term-mode)
- **Notes**: `omit [Fintype K] [Fintype W.toAffine.Point]` — finite-field hypotheses dropped. Pure thin wrapper; no mathematical content beyond the delegation.

---

### `theorem comp_eq_mulByInt_of_genuine`

- **Type**: Given isogenies `β`, `β_dual`, an integer `M`, genuineness witnesses `hgenLeft : IsGenuineWith W (β_dual.comp β) g` and `hgenRight : IsGenuineWith W (mulByInt W M) g`, and a point-map equality `(β_dual.comp β).toAddMonoidHom = (mulByInt W M).toAddMonoidHom`, conclude `β_dual.comp β = mulByInt W M` as isogenies.
- **What**: Lifts a point-map equality between two isogenies that share the same geometric action to a full-isogeny equality (the "comorphism upgrade"). This is the generic form of the Wall-B killer specialized to the composition `β_dual ∘ β` vs a scalar `[M]`.
- **How**: One-line term-proof calling `genuine_isogeny_ext` from `GapSpines.lean`.
- **Hypotheses**: Both isogenies must be genuine with the same geometric action `g`; they must agree on points.
- **Uses from project**: `genuine_isogeny_ext` (GapSpines)
- **Used by**: `isDualOf_of_picDual` (2 calls), `degree_eq_N` (1 call)
- **Visibility**: public
- **Lines**: 137–144; proof length: 1 line (term-mode)
- **Notes**: This is the key mechanical step reused 3 times in this file (key API within the file). No conditions on `M` being nonzero here — that is only needed when applying `mulByInt_isGenuineWith` to supply `hgenRight`.

---

### `theorem isDualOf_of_picDual`

- **Type**: Given isogenies `β`, `β_dual` with CoordHom data, naturality `hnat`, `hsurjDual`, a dual-hom identity `β_dual.toAddMonoidHom = picDual β`, fraction-field tower data `(S, S')` with `finrank` equalities, and four genuineness witnesses for the two composition halves, conclude `IsDualOf W β_dual β`.
- **What**: Upgrades the Pic⁰ point-map dual relation to the full-isogeny `IsDualOf` (Silverman III.6.2(a)) by applying `comp_eq_mulByInt_of_genuine` to each of the two composition halves `β_dual ∘ β` and `β ∘ β_dual`.
- **How**: Builds point-map equalities for both halves from `Isogeny.picDual_comp_toAddMonoidHom_of_surjective_degree` (the `α̂ ∘ α` half) and `Isogeny.toAddMonoidHom_comp_picDual_degree` (the `α ∘ α̂` half), both from `PicDual.lean`, then calls `comp_eq_mulByInt_of_genuine` twice to upgrade each to the full-isogeny level.
- **Hypotheses**: Full CoordHom data for `β`, `hdual_hom` identifying `β_dual` as the Pic⁰ dual at the point-map level, the fraction-field tower `(S, S')` for the `finrank ↔ degree` identification, four `IsGenuineWith` witnesses.
- **Uses from project**: `comp_eq_mulByInt_of_genuine` (this file), `Isogeny.picDual_comp_toAddMonoidHom_of_surjective_degree` (PicDual), `Isogeny.toAddMonoidHom_comp_picDual_degree` (PicDual), `Isogeny.comp_toAddMonoidHom` (Isogeny)
- **Used by**: `degree_eq_N_via_picDual`
- **Visibility**: public
- **Lines**: 165–202; proof length: ~14 lines (tactic-mode `by`)
- **Notes**: The four genuineness witnesses are provided in two pairs sharing the same geometric action `g₁` and `g₂` respectively. This is the main structural theorem of Phase 2.

---

### `theorem degree_eq_N`

- **Type**: For the genuine isogeny `β := genuineIsogSmulSub W r s`, given Verschiebung `V` with `IsDualOf V π`, trace sum `π + V = [t]`, dual point-map `β_dual = r·V − s`, `N ≠ 0`, genuineness witnesses, and `IsDualOf β_dual β`, conclude `(deg β : ℤ) = q·r² − t·r·s + s²`.
- **What**: Extracts the signed III.6.3 degree identity `deg(rπ − s) = N` from the Pic⁰ dual chain via Wall C (`signed_degree_of_genuine_dual_pair`), first upgrading the shipped point-map Vieta to a full-isogeny equality.
- **How**: Applies `comp_eq_mulByInt_of_genuine` to upgrade the shipped `genuine_dual_comp_toAddMonoidHom_eq_mulByInt` (point-map Vieta) to the full-isogeny `β_dual.comp β = [N]`, then calls `signed_degree_of_genuine_dual_pair` (DegreeQuadraticForm) using `h_isDual` and `genuineIsogSmulSub_degree_pos`.
- **Hypotheses**: `IsDualOf V π` (Verschiebung dual of Frobenius), `π + V = [t]` (trace identity), `β_dual = r·V − s` at point level, `N ≠ 0`, genuineness witnesses for the composition and the scalar `[N]`, `IsDualOf β_dual β`.
- **Uses from project**: `comp_eq_mulByInt_of_genuine` (this file), `genuine_dual_comp_toAddMonoidHom_eq_mulByInt` (GapSpines), `signed_degree_of_genuine_dual_pair` (DegreeQuadraticForm), `genuineIsogSmulSub` (GapSpines), `genuineIsogSmulSub_degree_pos` (GapSpines), `frobeniusIsog` (Frobenius), `isogTrace` (Endomorphism), `isogOneSub_negFrobenius` (GapSpines)
- **Used by**: `degree_eq_N_via_picDual`
- **Visibility**: public
- **Lines**: 235–266; proof length: ~11 lines (tactic-mode `by`)
- **Notes**: `h_isDual` is carried abstractly — this theorem is route-agnostic about how `IsDualOf β_dual β` was assembled (Phase 2 vs Wall-A).

---

### `theorem qf_nonneg_of_degree_eq_N`

- **Type**: Given `(deg(genuineIsogSmulSub W r s) : ℤ) = q·r² − t·r·s + s²`, conclude `0 ≤ q·r² − t·r·s + s²`.
- **What**: The non-negativity leaf: once the degree equals the quadratic form value, non-negativity follows because degrees are natural numbers cast to `ℤ`.
- **How**: Rewrites via the hypothesis and applies `Int.natCast_nonneg`.
- **Hypotheses**: The degree identity `h_deg`; `r, s` nonzero in `ℤ` and `K`; `2 ≤ #K`.
- **Uses from project**: `genuineIsogSmulSub` (GapSpines), `isogTrace`, `isogOneSub_negFrobenius`, `frobeniusIsog`
- **Used by**: `qf_nonneg_generic_via_picDual`, `qf_nonneg_generic_via_picDual_reduced`
- **Visibility**: public
- **Lines**: 284–293; proof length: 3 lines
- **Notes**: `omit [Fintype W.toAffine.Point]`. Purely formal; relies only on `Int.natCast_nonneg`.

---

### `theorem degree_eq_N_via_picDual`

- **Type**: The fully-wired `deg(rπ − s) = N` theorem with `IsDualOf β_dual β` assembled inline from the Pic⁰ two-sided dual relation (Phase 2 `isDualOf_of_picDual`), then fed to `degree_eq_N` (Wall C).
- **What**: Chains `isDualOf_of_picDual` → `degree_eq_N` to produce the signed degree identity end-to-end from the Pic⁰ data plus all six genuineness witnesses and the Vieta bundle.
- **How**: First calls `isDualOf_of_picDual` to obtain `h_isDual : IsDualOf β_dual β`, then applies `degree_eq_N` with all residuals forwarded.
- **Hypotheses**: All residuals of `isDualOf_of_picDual` (CoordHom data, naturality, surjectivity, tower, four genuineness witnesses for IsDualOf halves) plus all residuals of `degree_eq_N` (Vieta bundle V/π, trace sum, β_dual hom, hN_ne, two more genuineness witnesses).
- **Uses from project**: `isDualOf_of_picDual` (this file), `degree_eq_N` (this file)
- **Used by**: `qf_nonneg_generic_via_picDual`, `degree_eq_N_via_picDual_reduced`
- **Visibility**: public
- **Lines**: 308–363; proof length: ~7 lines (tactic `by`)
- **Notes**: The longest signature in the file — 6 genuineness witnesses, CoordHom data, tower data. Provides the "fully wired" assembly point.

---

### `theorem qf_nonneg_generic_via_picDual`

- **Type**: The Leaf-1 conclusion `0 ≤ q·r² − t·r·s + s²` for generic `(r, s)`, assembled entirely via `degree_eq_N_via_picDual` → `qf_nonneg_of_degree_eq_N`.
- **What**: Route-C analogue of the shipped Wall-A generic branch of `degree_quadratic_exists_skeleton_nonzero`; gives the Hasse-bound Leaf-1 for generic `(r, s)` along the Pic⁰ dual route.
- **How**: Term-mode composition: `qf_nonneg_of_degree_eq_N` applied to `degree_eq_N_via_picDual` with all arguments forwarded.
- **Hypotheses**: Full residual list of `degree_eq_N_via_picDual`: all six genuineness witnesses, CoordHom data, Vieta bundle, `hN_ne`.
- **Uses from project**: `qf_nonneg_of_degree_eq_N` (this file), `degree_eq_N_via_picDual` (this file)
- **Used by**: unused in file (exported, top-level theorem)
- **Visibility**: public
- **Lines**: 379–427; proof length: 5 lines (term-mode)
- **Notes**: Proof is a single term-mode application spanning 5 lines due to argument length. This is the "with all six genuineness witnesses" version before Phase-4 scalar-side discharge.

---

### `theorem degree_eq_N_via_picDual_reduced`

- **Type**: `deg(rπ − s) = N` with the three scalar-side genuineness witnesses (`hgenR₁`, `hgenR₂`, `hgenN`) discharged internally using `mulByInt_isGenuineWith`, reducing the residuals to only the deep ones plus `hN_ne`.
- **What**: Reduces Phase 4 of the assembly: the three "right" genuineness witnesses in `degree_eq_N_via_picDual` are all of the form `IsGenuineWith W (mulByInt W M) (zsmulPointHom W M)` and are discharged by the shipped axiom-clean `mulByInt_isGenuineWith`. After this, only deep residuals remain (`hnat`, `hsurjDual`, `hgenL₁`, `hgenL₂`, `hgenComp` plus CoordHom data and Vieta bundle).
- **How**: Discharges `hdeg_ne : (deg β : ℤ) ≠ 0` via `genuineIsogSmulSub_degree_pos`, then calls `degree_eq_N_via_picDual` with the three right witnesses supplied by `mulByInt_isGenuineWith W _ hdeg_ne` (×2) and `mulByInt_isGenuineWith W _ hN_ne`.
- **Hypotheses**: Deep residuals only: `hnat`, `hsurjDual`, CoordHom data, Vieta bundle, `hN_ne`, the three V-side left genuineness witnesses `hgenL₁`/`hgenL₂`/`hgenComp` with actions pinned to `zsmulPointHom W (·)`.
- **Uses from project**: `degree_eq_N_via_picDual` (this file), `mulByInt_isGenuineWith` (GapSpines), `genuineIsogSmulSub_degree_pos` (GapSpines)
- **Used by**: `qf_nonneg_generic_via_picDual_reduced`
- **Visibility**: public
- **Lines**: 471–525; proof length: ~10 lines (tactic `by`)
- **Notes**: This is the "cleaned up" version exposing the minimal deep residual list. The three `IsGenuineWith` hypotheses now have their actions pinned to `zsmulPointHom`, making them explicit rather than existential.

---

### `theorem qf_nonneg_generic_via_picDual_reduced`

- **Type**: The Leaf-1 conclusion `0 ≤ q·r² − t·r·s + s²` for generic `(r, s)`, with scalar-side genuineness discharged, via `degree_eq_N_via_picDual_reduced` → `qf_nonneg_of_degree_eq_N`.
- **What**: The reduced top-level Route-C Leaf-1 theorem: same conclusion as `qf_nonneg_generic_via_picDual` but with fewer residuals (three scalar genuineness witnesses discharged).
- **How**: Term-mode composition applying `qf_nonneg_of_degree_eq_N` to `degree_eq_N_via_picDual_reduced`.
- **Hypotheses**: Deep residuals: `hnat`, `hsurjDual`, CoordHom data, Vieta bundle, `hN_ne`, three V-side `hgenL₁`/`hgenL₂`/`hgenComp` witnesses.
- **Uses from project**: `qf_nonneg_of_degree_eq_N` (this file), `degree_eq_N_via_picDual_reduced` (this file)
- **Used by**: unused in file (exported, top-level theorem)
- **Visibility**: public
- **Lines**: 537–581; proof length: 5 lines (term-mode)
- **Notes**: The final and "most reduced" top-level export of the Route-C chain. Mirrors `qf_nonneg_generic_via_picDual` but preferred for downstream use since it presents the minimal residual interface.

---

## Cross-reference summary

| Caller | Callees (in this file) |
|---|---|
| `isDualOf_of_picDual` | `comp_eq_mulByInt_of_genuine` (×2) |
| `degree_eq_N` | `comp_eq_mulByInt_of_genuine` (×1) |
| `degree_eq_N_via_picDual` | `isDualOf_of_picDual`, `degree_eq_N` |
| `qf_nonneg_generic_via_picDual` | `qf_nonneg_of_degree_eq_N`, `degree_eq_N_via_picDual` |
| `degree_eq_N_via_picDual_reduced` | `degree_eq_N_via_picDual`, `mulByInt_isGenuineWith`* |
| `qf_nonneg_generic_via_picDual_reduced` | `qf_nonneg_of_degree_eq_N`, `degree_eq_N_via_picDual_reduced` |

*`mulByInt_isGenuineWith` is from GapSpines, not this file.

**Key API** (used by 3+ others in this file): `comp_eq_mulByInt_of_genuine` (3 callers: `isDualOf_of_picDual` ×2, `degree_eq_N` ×1).

**Unused in file** (not called by any other declaration here): `picDual_eq_pointMap`, `qf_nonneg_generic_via_picDual`, `qf_nonneg_generic_via_picDual_reduced`.

## Statistics

- Total declarations: 9
- Theorems: 9, Defs: 0, Lemmas: 0, Instances: 0
- Sorries: none
- `set_option maxHeartbeats`: none
- Long proofs (>30 lines): none
