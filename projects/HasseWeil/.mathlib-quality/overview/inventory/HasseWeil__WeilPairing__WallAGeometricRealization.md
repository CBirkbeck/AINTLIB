# Inventory: ./HasseWeil/WeilPairing/WallAGeometricRealization.lean

**File purpose**: Closes **Wall A (G-004) for the separable isogeny `1 − π` base-changed to `K̄`**.
Proves that the *concrete* opaque base-changed pullback `oneSubFrobeniusPullback_L` is **genuine**
with the translatable geometric action `gKbar = id − π̄` over `K̄` (`oneSub_isGenuineWith_Kbar`),
then chains this through the master translation/Frobenius covariance lemmas to discharge the
per-`(ℓ,S,T)` translation covariance `hcomm'` (`oneSub_hcommPrime_discharged`) — the residual the
`SeparableWitnesses` / `OneSubProjOrdTransport` reductions consume on the active `1 − π` leaf. The
entire route is **CoordHom-free**: `oneSubFrobeniusPullback_L` has poles at the affine kernel so
admits no CoordHom; everything goes through the function-field base-change naturality
(`functionFieldMap`).

**Imports**: `HasseWeil.WeilPairing.WallAGenericRealization`, `HasseWeil.Hasse.IsogOneSubXyFamily`,
`HasseWeil.WeilPairing.FrobeniusGenericCovariance`, `HasseWeil.WeilPairing.SeparableWitnesses`

**Total declarations**: 12 (1 `noncomputable local instance`, 1 `noncomputable def`, 10 `theorem`).
**LIVE ratio: 12/12 — fully live.** Every declaration is consumed (internally or externally); the
terminal export `oneSub_hcommPrime_discharged` is used by `OneSubProjOrdTransport.lean:230`.

**Options set file-wide**: `linter.unusedSectionVars false`, `linter.unusedDecidableInType false`,
`linter.style.longLine false`.

---

## Declarations

### `noncomputable local instance instDecEqACGeom : DecidableEq (AlgebraicClosure K)`
- **What**: `DecidableEq` on `AlgebraicClosure K` via `Classical.decEq`.
- **How**: `Classical.decEq _`.
- **Hypotheses**: none beyond `K : Type*` `[Field K]` in context.
- **Uses from project**: none.
- **Used by**: all theorems mentioning `AlgebraicClosure K` in this file.
- **Visibility**: `local` (file-scoped).
- **Lines**: 82.
- **LIVE.** Standard classical-decidability boilerplate.

---

### `theorem ffbc_frob_comm`
- **Type**: `(P : (W_KE W).toAffine.Point) : ffBaseChangePoint W (AlgebraicClosure K) (frobeniusW_KE W P) = frobFunctionFieldPointKbar W (ffBaseChangePoint W (AlgebraicClosure K) P)`
- **What**: The `q`-power geometric Frobenius commutes with the function-field base-change point map
  (Silverman III.4): `ffBaseChangePoint ∘ frobeniusW_KE = frobFunctionFieldPointKbar ∘ ffBaseChangePoint`.
- **How**: `rcases P`; the `some (x,y)` case reduces via `frobeniusW_KE_some`, `ffBaseChangePoint_some`,
  `Affine.Point.map_some` to the ring-hom commutation `functionFieldMap (x^q) = (functionFieldMap x)^q`
  closed by `Polynomial.map_pow` (`map_pow`).
- **Hypotheses**: section vars `K` finite field, `W` elliptic, base change elliptic.
- **Uses from project**: `ffBaseChangePoint`, `ffBaseChangePoint_some` (WallAGenericRealization);
  `frobeniusW_KE`, `frobeniusW_KE_some`, `frobFunctionFieldPointKbar`; `SmoothPlaneCurve.functionFieldMap`,
  `functionField_baseChange`; `FiniteField.frobeniusAlgHom`; `WeierstrassCurve.Affine.Point.map_some`.
- **Used by**: `gKbar_genericPoint` (L138) **and externally** `PencilCovariance.lean:232` (the pencil leaf's
  analogous covariance).
- **Visibility**: public.
- **Lines**: 96–115, proof ~17 lines.
- **LIVE.** Notes: >15-line proof with two explicit `show` re-typings of `Affine.Point.map`; load-bearing,
  shared between the `1 − π` and `rπ − s` leaves.

---

### `noncomputable def gKbar`
- **Type**: `(W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point →+ (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point`
- **What**: The translatable geometric `K̄`-action `id − π̄` realizing the base-changed `1 − π`.
- **How**: `AddMonoidHom.id _ - frobFunctionFieldPointKbar W`.
- **Hypotheses**: section vars; base change elliptic.
- **Uses from project**: `frobFunctionFieldPointKbar`.
- **Used by**: `gKbar_genericPoint`, `gKbar_genericPoint_eq_map`, `oneSub_isGenuineWith_Kbar`,
  `mapTranslateGenericPoint_gKbar` (all this file).
- **Visibility**: public.
- **Lines**: 120–123.
- **LIVE.** Key local API (used by 4 declarations).

---

### `theorem gKbar_genericPoint`
- **Type**: `gKbar W (genericPoint (W.baseChange K̄)) = ffBaseChangePoint W K̄ (genericPoint W − frobeniusW_KE W (genericPoint W))`
- **What**: `gKbar` at the generic point is the function-field base-change of the `K`-level `1 − π` image
  (Silverman III.8.2, base change).
- **How**: unfolds `gKbar` (`AddMonoidHom.sub_apply`/`id_apply`), `map_sub` of `ffBaseChangePoint`, then
  `ffbc_frob_comm` + `ffBaseChangePoint_genericPoint`; `congr 1`.
- **Hypotheses**: section vars.
- **Uses from project**: `gKbar`, `ffBaseChangePoint`, `ffbc_frob_comm`, `ffBaseChangePoint_genericPoint`
  (this file + WallAGenericRealization); `genericPoint`, `frobeniusW_KE`.
- **Used by**: `gKbar_genericPoint_eq_map` (L162).
- **Visibility**: public.
- **Lines**: 128–139, proof ~8 lines.
- **LIVE.**

---

### `theorem oneSub_pullback_x_gen_eq`
- **Type**: `(hq : 2 ≤ Fintype.card K) : (isogOneSub_negFrobenius W hq).pullback (x_gen W) = addPullback_x W (negFrobeniusIsog W)`
- **What**: identifies `(1 − π).pullback x_gen` with the `K`-level addition-formula x-coordinate.
- **How**: `rw [isogOneSub_negFrobenius_pullback, addPullbackAlgHom_negFrobenius_x_gen_eq]`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `isogOneSub_negFrobenius`, `isogOneSub_negFrobenius_pullback`, `x_gen`,
  `addPullback_x`, `negFrobeniusIsog`, `addPullbackAlgHom_negFrobenius_x_gen_eq` (Hasse layer).
- **Used by**: `oneSub_isGenuineWith_Kbar` (L193) **and externally** `OneSubAffineResidues.lean:312` (real
  `rw` use; also doc-mentioned at L34, L302).
- **Visibility**: public.
- **Lines**: 144–147, proof 1 line.
- **LIVE.**

---

### `theorem oneSub_pullback_y_gen_eq`
- **Type**: y-analogue of `oneSub_pullback_x_gen_eq`.
- **What/How**: as above with `addPullbackAlgHom_negFrobenius_y_gen_eq`.
- **Used by**: `oneSub_isGenuineWith_Kbar` (L196) **and externally** `OneSubAffineResidues.lean:326`.
- **Visibility**: public. **Lines**: 150–153, 1 line. **LIVE.**

---

### `theorem gKbar_genericPoint_eq_map`
- **Type**: `(hq) : gKbar W (genericPoint (W.baseChange K̄)) = Affine.Point.map (W' := W) (S := K) (functionField_baseChange K̄) (genericPoint W − frobeniusW_KE W (genericPoint W))`
- **What**: `gKbar_genericPoint` with `ffBaseChangePoint` unfolded to the underlying `Affine.Point.map`
  (the exact form fed to genuineness).
- **How**: `rw [gKbar_genericPoint]; rfl`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `gKbar`, `gKbar_genericPoint`, `ffBaseChangePoint` (defeq), `functionField_baseChange`.
- **Used by**: `oneSub_isGenuineWith_Kbar` (L189).
- **Visibility**: public. **Lines**: 157–162, 2 lines. **LIVE.**

---

### `theorem oneSub_isGenuineWith_Kbar`
- **Type**: `(hq) : IsGenuineWith (W.baseChange K̄) (oneSubFrobeniusIsogBaseChange W p r K̄ (oneSubFrobeniusPullback_L W K̄ hq)) (gKbar W)`
- **What**: **Wall A closed for `1 − π` (the core G-004 genuineness result).** The concrete base-changed
  pullback is genuine with `gKbar = id − π̄` over `K̄`.
- **How**: `gKbar_genericPoint_eq_map` rewritten via `genericPoint_sub_frobeniusW_KE_apply` gives the
  `(some addPullback_x addPullback_y)` form; the genuineness `⟨_,_,_,hgen,_,_⟩` is closed on each
  coordinate by `oneSubFrobeniusIsogBaseChange_pullback`, `oneSubFrobeniusPullback_L_x/y_gen`,
  `oneSub_pullback_x/y_gen_eq`, `functionField_baseChange_apply`.
- **Hypotheses**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (#K = p^r)]`, `2 ≤ #K`.
- **Uses from project**: `IsGenuineWith`, `oneSubFrobeniusIsogBaseChange(_pullback)`, `oneSubFrobeniusPullback_L`,
  `oneSubFrobeniusPullback_L_x/y_gen` (WallAGenericRealization), `oneSub_pullback_x/y_gen_eq` (this file),
  `gKbar_genericPoint_eq_map` (this file), `genericPoint_sub_frobeniusW_KE_apply` (IsogOneSubXyFamily),
  `SmoothPlaneCurve.functionField_baseChange_apply`.
- **Used by**: `mapTranslateGenericPoint_oneSub_canonical` (L267) **and doc-referenced** by
  `OneSubComapConcrete.lean` (L34, L116 — comments only).
- **Visibility**: public.
- **Lines**: 180–197, proof ~13 lines.
- **LIVE.** Notes: `set_option maxHeartbeats 1600000 in` (8× default) — the **only** heartbeat bump in the
  file; flag for cleanup.

---

### `theorem mapTranslateGenericPoint_gKbar`
- **Type**: `(hq) : MapTranslateGenericPoint (W.baseChange K̄) (oneSubFrobeniusIsogBaseChange …) (gKbar W)`
- **What**: `gKbar` satisfies the generic-point translation-covariance leaf `MapTranslateGenericPoint`
  (Silverman III.8.2 for `1 − π`).
- **How**: from `gKbar = id − π̄`: `map_sub`, then identity component via
  `translateAlgEquivOfPoint_map_genericPoint` and Frobenius component via `frobeniusGenericCovariance_Kbar`;
  `oneSubFrobeniusIsogBaseChange_toAddMonoidHom` + `frobeniusHomBaseChange_eq_geomFrobeniusPoint`
  give `φ_L S = S − π̄ S`; the two `liftPointToKE` images recombine (`map_sub`); closed by `abel`.
- **Hypotheses**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (#K = p^r)]`, `2 ≤ #K`.
- **Uses from project**: `MapTranslateGenericPoint`, `gKbar`, `oneSubFrobeniusIsogBaseChange(_toAddMonoidHom)`,
  `oneSubFrobeniusPullback_L`, `translateAlgEquivOfPoint(_map_genericPoint)`, `frobeniusGenericCovariance_Kbar`,
  `frobeniusHomBaseChange_eq_geomFrobeniusPoint`, `geomFrobeniusPointFun`, `liftPointToKE`,
  `frobFunctionFieldPointKbar`.
- **Used by**: `mapTranslateGenericPoint_oneSub_canonical` (L267).
- **Visibility**: public.
- **Lines**: 207–251, proof ~38 lines.
- **LIVE.** Notes: **>30-line proof** — candidate for `decompose-proof` extraction (the `hφS`/`hlift`
  `have`-blocks are reusable steps).

---

### `theorem mapTranslateGenericPoint_oneSub_canonical`
- **Type**: `(hq) : MapTranslateGenericPoint (W.baseChange K̄) (oneSubFrobeniusIsogBaseChange …) (Affine.Point.map (oneSubFrobeniusIsogBaseChange …).pullback)`
- **What**: the **canonical-action** generic-point covariance `hgcomm` for `(1 − π)_{K̄}` — the form the
  `SeparableWitnesses` reductions consume.
- **How**: term-mode `mapTranslateGenericPoint_canonical_of_genuine` applied to `oneSub_isGenuineWith_Kbar`
  + `mapTranslateGenericPoint_gKbar`.
- **Hypotheses**: as above.
- **Uses from project**: `mapTranslateGenericPoint_canonical_of_genuine`, `oneSub_isGenuineWith_Kbar`,
  `mapTranslateGenericPoint_gKbar` (this file), `oneSubFrobeniusIsogBaseChange`, `oneSubFrobeniusPullback_L`.
- **Used by**: `oneSub_hcommPrime_discharged` (L296) **and externally** `OneSubInftyResidues.lean:391`
  (real use), `OneSubProjOrdTransport.lean:35` (doc).
- **Visibility**: public. **Lines**: 257–267, term-mode. **LIVE.**

---

### `theorem oneSub_hcommPrime_discharged`
- **Type**: a `∀ (ℓ) (hℓF) (S T) (_hS) (hφT), translateAlgEquivOfPoint … (φ.pullback (weilFunction …)) = φ.pullback (translateAlgEquivOfPoint …)` — the per-`(ℓ,S,T)` `hcomm'` field of `OneSubScalingData`, **with no carried `hgcomm` hypothesis**.
- **What**: the translation covariance `hcomm'` for `(1 − π)_{K̄}` fully discharged, CoordHom-free —
  the terminal export of the file (Silverman III.8.2 for base-changed separable `1 − π`).
- **How**: term-mode `oneSub_hcommPrime_of_hgcomm` applied to `mapTranslateGenericPoint_oneSub_canonical`.
- **Hypotheses**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (#K = p^r)]`, `2 ≤ #K`.
- **Uses from project**: `oneSub_hcommPrime_of_hgcomm` (SeparableWitnesses), `mapTranslateGenericPoint_oneSub_canonical`
  (this file), `oneSubFrobeniusIsogBaseChange`, `oneSubFrobeniusPullback_L`, `translateAlgEquivOfPoint`,
  `weilFunction`.
- **Used by**: **externally** `OneSubProjOrdTransport.lean:230` (real `exact` use; doc L34, L100, L151, L191, L284).
- **Visibility**: public. **Lines**: 275–296, term-mode (statement is large but proof is one application). **LIVE.**

---

## File Summary

- **Role in proof**: This is the geometric heart of Wall A on the **active `1 − π` leaf** of Route 2A.
  It supplies the genuineness (`oneSub_isGenuineWith_Kbar`) and, downstream, the discharged translation
  covariance `oneSub_hcommPrime_discharged` consumed by `OneSubProjOrdTransport.lean`, which in turn feeds
  the per-`ℓ` `OneSubFrobeniusScaling` leaf and the capstone `hasse_bound_unconditional`. Two of its
  lemmas (`ffbc_frob_comm`, and the `ffBaseChangePoint*` it imports) are also reused on the `rπ − s`
  pencil leaf via `PencilCovariance.lean`.
- **(a) Dead/unused declarations**: **none** — fully live (12/12). Confirmed by grep: every named decl has
  a real (non-comment) consumer.
- **(b) Scratch/superseded sub-routes**: none in this file. The CoordHom-free route here is the *active*
  one (it replaces the never-existing-CoordHom sketch in `CurveMapBaseChange.lean`).
- **(c) Hand-rolled vs mathlib**: builds entirely on project-level `Affine.Point.map`, `IsGenuineWith`,
  `translateAlgEquivOfPoint`, `liftPointToKE` — appropriate; no mathlib re-implementation.
- **(d) Moral duplication**: `oneSub_pullback_x_gen_eq` / `_y_gen_eq` and the two coordinate branches of
  `oneSub_isGenuineWith_Kbar` are x/y mirror pairs (inherent to coordinate work, low priority). Note the
  pencil leaf has a structurally parallel file (`PencilCovariance.lean`) — see cross-file duplication in
  the final report.
- **(e) Under-general statements**: `gKbar` and all theorems are pinned to `AlgebraicClosure K`
  specifically (not a general `IsAlgClosed L`), unlike `WallAGenericRealization` which is stated over a
  general `[IsAlgebraic K L]`. This is acceptable (the consumers only need `K̄`) but is less general than
  its imported helpers.
- **Cleanup flags**:
  - `set_option maxHeartbeats 1600000 in` at `oneSub_isGenuineWith_Kbar` (L164) — 8× default; investigate
    whether it can drop after the rewrite chain is reordered.
  - `mapTranslateGenericPoint_gKbar` (L207–251) is a **>30-line proof** — extract `hφS`/`hlift` steps.
  - No `sorry` anywhere.
