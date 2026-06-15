# Inventory: ./HasseWeil/WeilPairing/OneSubScaling.lean

**File**: `HasseWeil/WeilPairing/OneSubScaling.lean`
**Total declarations**: 8 (1 def, 5 theorems, 1 structure, 0 instances)
**Sorries**: none
**Long proofs (>30 lines)**: none

---

## Summary

Thin "discharge" file for the `OneSubFrobeniusScaling` leaf of `FrobMatrixData.lean`. Builds the
concrete base-changed isogeny `(1 − π)_{K̄}` via `Isogeny.mkBaseChange`, packages all residual
geometric hypotheses into the `OneSubScalingData` bundle, and derives the symplectic Weil-pairing
scaling `e_ℓ((id − π̄)S, (id − π̄)T) = e_ℓ(S,T)^{deg(1−π)}` from `weilScales_of_dualComp`
(CoordHom-free route).

---

## Declarations

---

### `noncomputable def oneSubFrobeniusIsogBaseChange`

- **Type**: `(pullback_L : FunctionField(W_{K̄}) →ₐ[L] FunctionField(W_{K̄})) → Isogeny (W_{K̄}).toAffine (W_{K̄}).toAffine`
  (variables: `W`, `p`, `r`, `L` in context)
- **What**: Constructs the concrete base-changed isogeny `(1 − π)_{K̄}`: packages the supplied
  base-changed pullback AlgHom together with the point map `AddMonoidHom.id _ − frobeniusHomBaseChange W p r L`
  into an `Isogeny` object via `Isogeny.mkBaseChange`.
- **How**: One-liner `Isogeny.mkBaseChange L pullback_L (AddMonoidHom.id _ - frobeniusHomBaseChange W p r L)`.
- **Hypotheses**: `W` an elliptic curve over a finite field `K`, `L` an algebraically-closed extension with characteristic `p`, the base-changed curve is elliptic.
- **Uses from project**: `Isogeny.mkBaseChange`, `frobeniusHomBaseChange`
- **Used by**: `oneSubFrobeniusIsogBaseChange_toAddMonoidHom`, `oneSubFrobeniusIsogBaseChange_pullback`, `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrank`, `oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_baseChange`, `oneSubFrobeniusIsogBaseChange_commute_mulByInt`, `OneSubScalingData` (all fields), `oneSubFrobeniusScaling_of_data`
- **Visibility**: public
- **Lines**: 101–107 (1-line body)
- **Notes**: `noncomputable`; the key constructor for all subsequent declarations.

---

### `@[simp] theorem oneSubFrobeniusIsogBaseChange_toAddMonoidHom`

- **Type**: `(oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom = AddMonoidHom.id _ - frobeniusHomBaseChange W p r L`
- **What**: States that the `toAddMonoidHom` of `oneSubFrobeniusIsogBaseChange` is *definitionally* `id − frobeniusHomBaseChange`, matching the point-map named in `OneSubFrobeniusScaling`.
- **How**: Immediate from `Isogeny.mkBaseChange_toAddMonoidHom`.
- **Hypotheses**: Same section variables as the def.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange`, `Isogeny.mkBaseChange_toAddMonoidHom`
- **Used by**: `oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_baseChange`, `oneSubFrobeniusScaling_of_data`
- **Visibility**: public, `@[simp]`
- **Lines**: 108–113 (1-line proof)
- **Notes**: None.

---

### `@[simp] theorem oneSubFrobeniusIsogBaseChange_pullback`

- **Type**: `(oneSubFrobeniusIsogBaseChange W p r L pullback_L).pullback = pullback_L`
- **What**: States that the `.pullback` field of `oneSubFrobeniusIsogBaseChange` is exactly the supplied `pullback_L`.
- **How**: Immediate from `Isogeny.mkBaseChange_pullback`.
- **Hypotheses**: Same section variables.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange`, `Isogeny.mkBaseChange_pullback`
- **Used by**: unused in this file (dead-code candidate; used by downstream files)
- **Visibility**: public, `@[simp]`
- **Lines**: 115–119 (1-line proof)
- **Notes**: Not referenced in any proof or structure body within this file; its utility is for callers in other files.

---

### `theorem oneSubFrobeniusIsogBaseChange_degree_eq_of_finrank`

- **Type**: Given `hq : 2 ≤ Fintype.card K` and `h_finrank : finrank(φ_L.algebra) = finrank((1−π).algebra)`, proves `(oneSubFrobeniusIsogBaseChange W p r L pullback_L).degree = (isogOneSub_negFrobenius W hq).degree`
- **What**: Reduces degree preservation of the base-changed isogeny to the raw `Module.finrank` equality, showing the degree of `φ_L = (1−π)_{K̄}` equals that of `(1−π)` over `K`. Isolates `Module.finrank_baseChange` as the sole irreducible content.
- **How**: Applies `Isogeny.degree_eq_of_finrank_eq` directly to the finrank hypothesis.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`; the raw finrank equality `h_finrank` (the substantive base-change tensor witness).
- **Uses from project**: `oneSubFrobeniusIsogBaseChange`, `isogOneSub_negFrobenius`, `Isogeny.degree_eq_of_finrank_eq`
- **Used by**: mentioned in the `hdeg_bc` field docstring of `OneSubScalingData`; not called directly in any proof body in this file
- **Visibility**: public
- **Lines**: 129–142 (1-line proof body after hypotheses)
- **Notes**: Not used in any proof within this file (callers construct `hdeg_bc` themselves via this helper).

---

### `theorem oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_baseChange`

- **Type**: `(oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom = AddMonoidHom.id (W.baseChange L).toAffine.Point - (Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).toAddMonoidHom`
- **What**: Shows `id − π̄` (the point map of `oneSubFrobeniusIsogBaseChange`) equals `id` minus the point map of the base-changed Frobenius isogeny, making precise the "base-change of `(1−π)`'s point map" claim.
- **How**: `rw [oneSubFrobeniusIsogBaseChange_toAddMonoidHom]; rfl` — the definition of `frobeniusHomBaseChange` makes this definitional.
- **Hypotheses**: Same section variables.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange`, `oneSubFrobeniusIsogBaseChange_toAddMonoidHom`, `Isogeny.frobeniusIsog_baseChange_charP_pow`
- **Used by**: unused in this file (dead-code candidate; meant for callers in other files)
- **Visibility**: public
- **Lines**: 154–161 (2-line proof)
- **Notes**: Not referenced in any proof or structure body within this file; documents a definitional fact for downstream callers.

---

### `theorem oneSubFrobeniusIsogBaseChange_commute_mulByInt`

- **Type**: `(mulByInt (W.baseChange L).toAffine ℓ).toAddMonoidHom.comp (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom = (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom.comp (mulByInt (W.baseChange L).toAffine ℓ).toAddMonoidHom`
- **What**: Proves `[ℓ] ∘ (id − π̄) = (id − π̄) ∘ [ℓ]` as AddMonoidHom composition — the `hcommφ` required by `weilScales_of_dualComp`.
- **How**: `ext P; rw [..., mulByInt_apply, mulByInt_apply, map_zsmul]` — pure group-hom commutativity with scalar multiplication.
- **Hypotheses**: Same section variables; takes `ℓ : ℤ` explicitly.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange`, `mulByInt`, `mulByInt_apply`
- **Used by**: `oneSubFrobeniusScaling_of_data`
- **Visibility**: public
- **Lines**: 171–181 (3-line proof)
- **Notes**: No geometry — purely algebraic `map_zsmul`.

---

### `structure OneSubScalingData`

- **Type**: `(hq : 2 ≤ Fintype.card K) → Prop`-like structure (it is a `Prop`-valued structure type). Fields:
  - `pullback_L`: the base-changed pullback AlgHom;
  - `finiteKer`: finiteness of `ker(φ_L)`;
  - `hdeg_bc`: degree preservation `φ_L.degree = (1−π).degree`;
  - `hproj : ProjOrdTransport φ_L`: divisor-pullback functoriality;
  - `δ`: the abstract dual additive hom `E_{K̄}.Point →+ E_{K̄}.Point`;
  - `hdc`: the dual relation `δ ∘ φ_L = [#ker φ_L]` (Silverman III.6.2(a));
  - `hsurj`: surjectivity of `φ_L`;
  - `hkerdeg`: separable degree match `#ker φ_L = φ_L.degree`;
  - `hcomm'`: translation covariance `τ_S ∘ φ_L^* = φ_L^* ∘ τ_{φ_L S}` for every ℓ-torsion S, T.
- **What**: Bundles all genuine CoordHom-free geometric residuals for `(1−π)_{K̄}`. The fields are the exact list of hypotheses that `weilScales_of_dualComp` needs (plus the degree witness), making the CoordHom-free route fully parametric.
- **How**: Pure structure definition; no proof obligations.
- **Hypotheses**: `W`, `p`, `r`, `L` section variables; `hq : 2 ≤ Fintype.card K` parameter; `IsAlgClosed L` and `IsIntegrallyClosed` for the coordinate ring.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange`, `isogOneSub_negFrobenius`, `ProjOrdTransport`, `mulByInt`, `translateAlgEquivOfPoint`, `weilFunction`, `frobeniusHomBaseChange`
- **Used by**: `oneSubFrobeniusScaling_of_data`
- **Visibility**: public
- **Lines**: 219–270 (structure body ~52 lines including doc comments)
- **Notes**: Not a sorry-bearing structure — it is a bundle of hypotheses. The `hcomm'` field has the longest type signature (10 lines). `hsurj` is commented as no longer consumed by the scaling itself but kept for constructing `δ`/`hdc`.

---

### `theorem oneSubFrobeniusScaling_of_data`

- **Type**: `(hq : 2 ≤ Fintype.card K) → (d : OneSubScalingData W p r L hq) → OneSubFrobeniusScaling W p r L hq`
- **What**: Discharges `OneSubFrobeniusScaling` (the Weil-pairing scaling leaf in `FrobMatrixData`) from the bundled data `OneSubScalingData`, CoordHom-free. Proves `e_ℓ((id−π̄)S, (id−π̄)T) = e_ℓ(S,T)^{deg(1−π)}` for all ℓ-torsion S, T.
- **How**: Applies `weilScales_of_dualComp` with the concrete isogeny `φL`, point map matched by `oneSubFrobeniusIsogBaseChange_toAddMonoidHom` (rfl), degree from `d.hdeg_bc`, pullback functoriality from `d.hproj`, `[ℓ]`-commutation from `oneSubFrobeniusIsogBaseChange_commute_mulByInt`, dual `d.δ`/`d.hdc`, degree match `d.hkerdeg`, and translation covariance from `d.hcomm'`.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`; `d : OneSubScalingData W p r L hq`; all section variables including `IsAlgClosed L`.
- **Uses from project**: `OneSubScalingData`, `oneSubFrobeniusIsogBaseChange`, `oneSubFrobeniusIsogBaseChange_toAddMonoidHom`, `weilScales_of_dualComp`, `isogOneSub_negFrobenius`, `frobeniusHomBaseChange`, `oneSubFrobeniusIsogBaseChange_commute_mulByInt`, `OneSubFrobeniusScaling`
- **Used by**: unused in this file (the main export; used by other files assembling the Hasse proof)
- **Visibility**: public
- **Lines**: 284–302 (~18-line proof)
- **Notes**: No sorry. `letI : Fact ℓ.Prime` and `haveI := d.finiteKer` are needed for instance synthesis. The `set φL := ...` avoids whnf timeout. Surjectivity `d.hsurj` is NOT passed to `weilScales_of_dualComp` (removed per reviewer round-20 Q2).

---

## Cross-reference summary

| Declaration | Used by (within file) |
|---|---|
| `oneSubFrobeniusIsogBaseChange` | all 6 other declarations + `OneSubScalingData` fields |
| `oneSubFrobeniusIsogBaseChange_toAddMonoidHom` | `oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_baseChange`, `oneSubFrobeniusScaling_of_data` |
| `oneSubFrobeniusIsogBaseChange_pullback` | unused in file |
| `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrank` | unused in file (mentioned in docstring of `OneSubScalingData`) |
| `oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_baseChange` | unused in file |
| `oneSubFrobeniusIsogBaseChange_commute_mulByInt` | `oneSubFrobeniusScaling_of_data` |
| `OneSubScalingData` | `oneSubFrobeniusScaling_of_data` |
| `oneSubFrobeniusScaling_of_data` | unused in file (main export) |

**Key API (used by 3+ declarations in file)**: `oneSubFrobeniusIsogBaseChange` — referenced in all 7 other declarations.
