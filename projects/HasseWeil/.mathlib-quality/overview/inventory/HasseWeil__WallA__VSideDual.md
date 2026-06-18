# Inventory: ./HasseWeil/WallA/VSideDual.lean

**File purpose:** Assembles the V-side genuine isogeny `β_dual = r·V − s` (built on the Verschiebung `V`) and reduces the Wall-A keystone `deg(r·π − s) = q·r² − t·r·s + s²` to three standing dual residuals via the pivot-chain scaffold in `GapSpines`.

**Total declarations:** 8 (6 theorems/lemmas + 1 noncomputable abbrev + 1 noncomputable def)

**Imports:** `HasseWeil.GapSpines`, `HasseWeil.Verschiebung.Genuine`, `HasseWeil.Hasse.SumTrace`

---

## Declaration Inventory

---

### `theorem isogeny_isGenuineWith_pointMap`

- **Type**: `(φ : Isogeny W.toAffine W.toAffine) → IsGenuineWith W φ (WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback)`
- **What**: Proves that every isogeny `φ` satisfies `IsGenuineWith` with the canonical geometric action `Affine.Point.map φ.pullback`. This is the general non-vacuity check: any genuine geometric isogeny is witnessed by its comorphism action.
- **How**: Constructs the `IsGenuineWith` structure by providing `φ.pullback (x_gen W)` and `φ.pullback (y_gen W)` as the coordinates, using `WeierstrassCurve.Affine.baseChange_nonsingular` for the nonsingularity condition, `genericPoint_xOf_some` to match the `x`-coordinate, and `WeierstrassCurve.Affine.Point.map_some` for the point identity.
- **Hypotheses**: An elliptic curve `W` over a field `K` (Fintype and DecidableEq are omitted via `omit`); an isogeny `φ : W.toAffine → W.toAffine`.
- **Uses from project**: `x_gen` (GenericPoint), `y_gen` (GenericPoint), `WeierstrassCurve.Affine.baseChange_nonsingular` (project), `generic_nonsingular` (GenericPoint), `genericPoint_xOf_some` (GenericPoint), `WeierstrassCurve.Affine.Point.map_some` (project), `IsGenuineWith` (GapSpines)
- **Used by**: `isogeny_isGenuine` (within this file); also referenced in `SeparableWitnesses.lean` and `SeparableTransportBridge.lean` (other files)
- **Visibility**: public
- **Lines**: 75–82; proof length ~6 lines
- **Notes**: `omit [Fintype K] [Fintype W.toAffine.Point]` drops the finite-type hypotheses (not needed for this general statement).

---

### `theorem isogeny_isGenuine`

- **Type**: `(φ : Isogeny W.toAffine W.toAffine) → IsGenuine W φ`
- **What**: Existential form: every isogeny is genuine (via the canonical `map pullback` action). Wraps `isogeny_isGenuineWith_pointMap` in the existential package `IsGenuine`.
- **How**: Direct `⟨_, isogeny_isGenuineWith_pointMap W φ⟩` — wraps the witness form.
- **Hypotheses**: Same as `isogeny_isGenuineWith_pointMap` (Fintype omitted).
- **Uses from project**: `IsGenuine` (GapSpines), `isogeny_isGenuineWith_pointMap` (this file)
- **Used by**: unused in file (no caller within this file; may be used externally)
- **Visibility**: public
- **Lines**: 83–86; proof length 1 line
- **Notes**: `omit [Fintype K] [Fintype W.toAffine.Point]` again. Dead code within the file.

---

### `noncomputable abbrev hSubset`

- **Type**: `(hq : 2 ≤ Fintype.card K) → (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤ (frobeniusIsog W).pullback.range`
- **What**: Abbreviation for the inclusion `Im([q]*) ⊆ Im(π*)` (Silverman II.2.11/III.6.2), the connected Verschiebung-existence witness. Simply aliases `mulByInt_q_pullback_subset_frobenius`.
- **How**: Pure abbreviation: `mulByInt_q_pullback_subset_frobenius W hq`.
- **Hypotheses**: `K` a finite field with `|K| ≥ 2`.
- **Uses from project**: `mulByInt_q_pullback_subset_frobenius` (GapSpines), `frobeniusIsog` (project), `mulByInt` (project)
- **Used by**: `verschiebungV`, `verschiebungV_isDual`
- **Visibility**: public (abbrev)
- **Lines**: 96–99; proof length ~2 lines (abbrev body)
- **Notes**: local-scope helper abbrev, no `sorry`, no `set_option`.

---

### `noncomputable def verschiebungV`

- **Type**: `(hq : 2 ≤ Fintype.card K) → Isogeny W.toAffine W.toAffine`
- **What**: Constructs a concrete Verschiebung `V` (the dual isogeny to the q-power Frobenius `π`) from the subset witness. This is `verschiebungIsog_of_witness` applied to `hSubset`.
- **How**: `verschiebungIsog_of_witness W (hSubset W hq)`.
- **Hypotheses**: `K` a finite field with `|K| ≥ 2`.
- **Uses from project**: `verschiebungIsog_of_witness` (Verschiebung/IsDual), `hSubset` (this file)
- **Used by**: `verschiebungV_isDual`, `verschiebungV_toAddMonoidHom`, `betaDualV`, `betaDualV_toAddMonoidHom_sub`, `genuineIsogSmulSub_degree_eq_signed_closed`
- **Visibility**: public
- **Lines**: 102–104; proof length ~1 line (def body)
- **Notes**: keyApi — referenced by 5 other declarations in this file. No `sorry`, no `set_option`.

---

### `theorem verschiebungV_isDual`

- **Type**: `(hq : 2 ≤ Fintype.card K) → IsDualOf W.toAffine (verschiebungV W hq) (frobeniusIsog W)`
- **What**: Proves `IsDualOf V π` for the concrete Verschiebung — i.e., `V ∘ π = [q]` in the appropriate sense (Silverman III.6.1 Case 2).
- **How**: `verschiebungIsog_of_witness_isDualOf_frobenius W (hSubset W hq)` — directly from the IsDual theorem in Verschiebung/IsDual.
- **Hypotheses**: `K` a finite field with `|K| ≥ 2`.
- **Uses from project**: `verschiebungIsog_of_witness_isDualOf_frobenius` (Verschiebung/IsDual), `hSubset` (this file), `verschiebungV` (this file), `frobeniusIsog` (project), `IsDualOf` (project)
- **Used by**: `betaDualV`, `genuineIsogSmulSub_degree_eq_signed_closed`
- **Visibility**: public
- **Lines**: 107–109; proof length ~1 line
- **Notes**: No `sorry`, no `set_option`.

---

### `@[simp] theorem verschiebungV_toAddMonoidHom`

- **Type**: `(hq : 2 ≤ Fintype.card K) → (verschiebungV W hq).toAddMonoidHom = (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).toAddMonoidHom`
- **What**: States that the point map of the concrete Verschiebung equals the `[q]`-multiplication point map. Since `V ∘ π = [q]` and Frobenius acts as identity on `𝔽_q`-rational points, `V` must carry the `[q]` action.
- **How**: `rfl` — the equality holds definitionally by how `verschiebungIsog_of_witness` computes its `toAddMonoidHom`.
- **Hypotheses**: `K` a finite field with `|K| ≥ 2`.
- **Uses from project**: `verschiebungV` (this file), `mulByInt` (project)
- **Used by**: `betaDualV_toAddMonoidHom_sub` (indirectly, via the structure of `betaDualV`), `genuineIsogSmulSub_degree_eq_signed_closed` (in the `h_sum_trace` statement)
- **Visibility**: public (tagged `@[simp]`)
- **Lines**: 114–117; proof length 1 line (`rfl`)
- **Notes**: `@[simp]` lemma. No `sorry`, no `set_option`.

---

### `noncomputable def betaDualV`

- **Type**: `(hq : 2 ≤ Fintype.card K) (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) → Isogeny W.toAffine W.toAffine`
- **What**: Constructs the V-side genuine isogeny `β_dual = r·V − s`, the exact mirror of the π-side `genuineIsogSmulSub = r·π − s`. Uses `addIsog` via the universal Verschiebung constructor.
- **How**: `genuineIsogSmulSubV_universal_unconditional W (verschiebungV W hq) (verschiebungV_isDual W hq) r s hr hs hrK hsK` — delegates to the Verschiebung/Genuine universal constructor.
- **Hypotheses**: `K` a finite field with `|K| ≥ 2`; integers `r ≠ 0`, `s ≠ 0` with nonzero images in `K`.
- **Uses from project**: `genuineIsogSmulSubV_universal_unconditional` (Verschiebung/Genuine), `verschiebungV` (this file), `verschiebungV_isDual` (this file)
- **Used by**: `betaDualV_toAddMonoidHom_sub`, `genuineIsogSmulSub_degree_eq_signed_closed`
- **Visibility**: public
- **Lines**: 127–131; proof length ~2 lines (def body)
- **Notes**: No `sorry`, no `set_option`.

---

### `theorem betaDualV_toAddMonoidHom_sub`

- **Type**: `(hq : 2 ≤ Fintype.card K) (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) → (betaDualV W hq r s hr hs hrK hsK).toAddMonoidHom = r • (verschiebungV W hq).toAddMonoidHom - s • (AddMonoidHom.id _)`
- **What**: Computes the point map of `betaDualV` as `r·V − s·id`. Shows that `addIsog (V.zsmul r) [−s]` produces `toAddMonoidHom = r • V.toAddMonoidHom - s • id`.
- **How**: Unfolds `betaDualV` via `rfl` to get `toAddMonoidHom = (V.zsmul r).toAddMonoidHom + (mulByInt W.toAffine (−s)).toAddMonoidHom`; then applies `ext P`, `simp` with `AddMonoidHom.add_apply`, `Isogeny.zsmul_apply`, `mulByInt_apply`, and `neg_smul`/`sub_eq_add_neg` to rewrite.
- **Hypotheses**: Same as `betaDualV`.
- **Uses from project**: `betaDualV` (this file), `verschiebungV` (this file), `mulByInt` (project), `Isogeny.zsmul_apply` (project)
- **Used by**: `genuineIsogSmulSub_degree_eq_signed_closed`
- **Visibility**: public
- **Lines**: 137–153; proof length ~14 lines
- **Notes**: Uses a `have hrfl : ... := rfl` to unfold the definition before rewriting. No `sorry`, no `set_option`.

---

### `theorem genuineIsogSmulSub_degree_eq_signed_closed`

- **Type**: `(hq : 2 ≤ Fintype.card K) (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) → h_sum_trace → h_pullback_eq → h_isDual_pair → h_N_ne → ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) = q·r² − t·r·s + s²`
- **What**: The live, witness-parametric closing lemma for the Wall-A keystone. Constructs `V` and `β_dual` internally, discharges the structural pivot inputs (`IsDualOf V π`, `β_dual.toAddMonoidHom`, positivity of degree), and reduces the degree identity to exactly three standing dual residuals: (1) the trace relation `π + V = [t]`, (2) the comorphism identity `(β_dual ∘ β)* = [N]*`, and (3) `IsDualOf β_dual β`.
- **How**: Directly applies `genuineIsogSmulSub_degree_eq_signed_of_full_pivot_chain` (GapSpines) with `V = verschiebungV`, `β_dual = betaDualV`, supplying: `verschiebungV_isDual` for the `IsDualOf V π` field, `betaDualV_toAddMonoidHom_sub` for the point-map field, and `genuineIsogSmulSub_degree_pos` for the positivity field; the three carried residuals are passed through.
- **Hypotheses**: `K` a finite field with `|K| ≥ 2`; `r, s : ℤ` nonzero with nonzero images in `K`; the three standing residuals `h_sum_trace`, `h_pullback_eq`, `h_isDual_pair` (and `h_N_ne`).
- **Uses from project**: `genuineIsogSmulSub_degree_eq_signed_of_full_pivot_chain` (GapSpines), `verschiebungV` (this file), `betaDualV` (this file), `verschiebungV_isDual` (this file), `betaDualV_toAddMonoidHom_sub` (this file), `genuineIsogSmulSub` (GapSpines), `genuineIsogSmulSub_degree_pos` (GapSpines), `frobeniusIsog` (project), `isogTrace` (Endomorphism), `isogOneSub_negFrobenius` (AdditionPullback/Frobenius), `mulByInt` (project), `IsDualOf` (project)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 175–202; proof length ~27 lines (signature + body)
- **Notes**: This is the main theorem of the file. The proof body is only ~8 lines (one application of the GapSpines pivot-chain theorem), but the signature is very long. No `sorry`, no `set_option`. The `h_sum_trace`, `h_pullback_eq`, `h_isDual_pair` hypotheses are the three genuine residuals the project has not yet shipped unconditionally.

---

## Cross-reference Summary

| Declaration | Used by (in file) |
|---|---|
| `isogeny_isGenuineWith_pointMap` | `isogeny_isGenuine` |
| `isogeny_isGenuine` | — (unused in file) |
| `hSubset` | `verschiebungV`, `verschiebungV_isDual` |
| `verschiebungV` | `verschiebungV_isDual`, `verschiebungV_toAddMonoidHom`, `betaDualV`, `betaDualV_toAddMonoidHom_sub`, `genuineIsogSmulSub_degree_eq_signed_closed` |
| `verschiebungV_isDual` | `betaDualV`, `genuineIsogSmulSub_degree_eq_signed_closed` |
| `verschiebungV_toAddMonoidHom` | (simp lemma; not explicitly called) |
| `betaDualV` | `betaDualV_toAddMonoidHom_sub`, `genuineIsogSmulSub_degree_eq_signed_closed` |
| `betaDualV_toAddMonoidHom_sub` | `genuineIsogSmulSub_degree_eq_signed_closed` |
| `genuineIsogSmulSub_degree_eq_signed_closed` | — (unused in file) |

**keyApi**: `verschiebungV` (used by 5 other declarations in the file).

**Dead code within file** (not referenced by anything else in this file): `isogeny_isGenuine`, `verschiebungV_toAddMonoidHom`, `genuineIsogSmulSub_degree_eq_signed_closed`. (All are public and likely used by other files.)

**Sorries**: none.

**set_option maxHeartbeats**: none.

**Long proofs (>30 lines)**: none strictly (the largest is `betaDualV_toAddMonoidHom_sub` at ~14 lines; `genuineIsogSmulSub_degree_eq_signed_closed` has a long signature but short proof body).
