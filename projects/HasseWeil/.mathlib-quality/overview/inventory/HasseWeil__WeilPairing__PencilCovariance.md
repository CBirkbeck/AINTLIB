# Inventory: ./HasseWeil/WeilPairing/PencilCovariance.lean

**File purpose**: Discharges the generic-point covariance `hgcomm` (and the translation covariance `hcomm'`) for the base-changed separable pencil `(rπ − s)_{K̄}` over `K̄ = AlgebraicClosure K`, CoordHom-free — the `rπ − s` analogue of the `1 − π` Wall A discharge `oneSub_hcommPrime_discharged`. The headline export `mapTranslateGenericPoint_pencil_canonical` is the canonical-action covariance the comap-witness assembly (PencilComapWitnesses) and the bundle (`pencilScalingComapData_hgcomm_canonical`) consume on the live path.

**Imports**: `HasseWeil.WeilPairing.MapTranslateGenericAdditive`, `HasseWeil.WeilPairing.FrobeniusGenericCovariance`, `HasseWeil.WeilPairing.SeparableWitnesses`, `HasseWeil.WeilPairing.PencilSeparable`, `HasseWeil.WeilPairing.WallAGeometricRealization`

**Total declarations**: 10 named (1 `private theorem`, 1 `noncomputable def`, 8 `theorem`) + 1 local `instance`. (The brief's "9/13 live" counts the local instance and possibly the `set_option … in`-wrapped decls separately.)

**No `sorry`.**

---

## LIVE / DEAD verdict

The headline export `mapTranslateGenericPoint_pencil_canonical` (292) is LIVE (consumed by live nodes in PencilComapWitnesses and by the live `pencilScalingComapData_hgcomm_canonical`). Its entire supporting `gKbarPencil` chain is LIVE. The general-field component lemmas are LIVE (they feed the chain). The ONE DEAD declaration is `pencil_hcommPrime_discharged` (314), whose only consumer is the dead `PencilComapScaling.pencilScaling_one_of_comapWitness_noδ`.

- **LIVE** (9): `map_translate_smul_genericPoint` (71), `mapTranslateGenericPoint_zsmul` (94), `mapTranslateGenericPoint_mulByInt` (121), `gKbarPencil` (148), `pencilIsogBaseChange_toAddMonoidHom_decomp` (156), `mapTranslateGenericPoint_gKbarPencil` (179), `gKbarPencil_genericPoint` (207), `pencil_isGenuineWith_Kbar` (248), `mapTranslateGenericPoint_pencil_canonical` (292).
- **DEAD** (1): `pencil_hcommPrime_discharged` (314).

---

## Declarations

### `private theorem map_translate_smul_genericPoint` — **LIVE**
- **Type**: `(ℓ : ℤ) (S : W.toAffine.Point) : Point.map τ_S (ℓ • P_gen) = ℓ • P_gen + lift (ℓ • S)`
- **What**: pure additivity of `Point.map τ_S` on a scaled generic point. (Inlined from the unbuildable `ScratchCov.lean`.)
- **How**: `calc` chain via `map_zsmul`, the master lemma `translateAlgEquivOfPoint_map_genericPoint`, `zsmul_add`, `map_zsmul` on `liftPointToKE`.
- **Uses from project**: `translateAlgEquivOfPoint`, `translateAlgEquivOfPoint_map_genericPoint`, `liftPointToKE`, `genericPoint`
- **Used by**: `mapTranslateGenericPoint_mulByInt` (127, this file). [Also referenced by `ScratchCov.lean:84`, but `ScratchCov.lean` is an untracked scratch file off the build/main path.]
- **Visibility**: private — **Lines**: 71–85
- **Notes**: General field `F`, not `K̄`.

### `theorem mapTranslateGenericPoint_zsmul` — **LIVE**
- **Type**: `(φ : Isogeny W W) (g) (m : ℤ) (h : MapTranslateGenericPoint W φ g) : MapTranslateGenericPoint W (φ.zsmul m) (m • g)`
- **What**: the generic-point covariance leaf is preserved by `zsmul` of the isogeny (Silverman III.8.2 + III.4.2b). If `g` is covariant for `φ`, then `m•g` is covariant for `φ.zsmul m`.
- **How**: `intro S`; `calc` via `map_zsmul` on `Point.map τ_S`, the component covariance `h S`, and `Isogeny.zsmul_apply`/`liftPointToKE.map_zsmul`; closes with `module`.
- **Uses from project**: `MapTranslateGenericPoint`, `Isogeny.zsmul`, `Isogeny.zsmul_apply`, `liftPointToKE`, `genericPoint`, `translateAlgEquivOfPoint`
- **Used by**: `mapTranslateGenericPoint_gKbarPencil` (192)
- **Visibility**: public — **Lines**: 94–115
- **Notes**: General field; the `r·π` component of the additive decomposition.

### `theorem mapTranslateGenericPoint_mulByInt` — **LIVE**
- **Type**: `(m : ℤ) : MapTranslateGenericPoint W (mulByInt W.toAffine m) (zsmulPointHom W m)`
- **What**: the `[m]` generic-point covariance leaf for the geometric action `g = zsmulPointHom m` (Silverman III.8.2 for `[m]`).
- **How**: `intro S`; `show … = m • P_gen + lift([m]S)`; `rw [map_translate_smul_genericPoint, mulByInt_apply]`.
- **Uses from project**: `MapTranslateGenericPoint`, `mulByInt`, `zsmulPointHom`, `map_translate_smul_genericPoint` (this file), `mulByInt_apply`, `liftPointToKE`, `genericPoint`
- **Used by**: `mapTranslateGenericPoint_gKbarPencil` (196, LIVE — the `−s·id` component); also `PencilComapWitnesses.mapTranslateGenericPoint_mulByInt_canonical` (2207, DEAD)
- **Visibility**: public — **Lines**: 121–127
- **Notes**: General field. LIVE via the internal `gKbarPencil` chain.

### `noncomputable def gKbarPencil` — **LIVE**
- **Type**: `(r' s' : ℤ) : (W_KE (E_{K̄})).toAffine.Point →+ (W_KE (E_{K̄})).toAffine.Point`
- **What**: the geometric `K̄`-action `r·frobₗ + [−s]` realising the base-changed pencil at the function-field level.
- **How**: `r' • frobFunctionFieldPointKbar W + zsmulPointHom (E_{K̄}) (-s')`.
- **Uses from project**: `frobFunctionFieldPointKbar`, `zsmulPointHom`
- **Used by**: `mapTranslateGenericPoint_gKbarPencil` (184), `gKbarPencil_genericPoint` (207), `pencil_isGenuineWith_Kbar` (253)
- **Visibility**: public — **Lines**: 148–151

### `theorem pencilIsogBaseChange_toAddMonoidHom_decomp` — **LIVE**
- **Type**: `(r' s') (pullback_L) : (pencilIsogBaseChange …).toAddMonoidHom = ((frobeniusIsog_baseChange…).zsmul r').toAddMonoidHom + (mulByInt (-s')).toAddMonoidHom`
- **What**: the point-map sum decomposition of the pencil isogeny as `(r·π̄) + [−s]`, at the `AddMonoidHom` level.
- **How**: `rw [pencilIsogBaseChange_toAddMonoidHom]`; `ext P`; rewrite via `Isogeny.zsmul_apply`, `mulByInt_apply`, `neg_smul`; close with `abel`.
- **Uses from project**: `pencilIsogBaseChange_toAddMonoidHom` (PencilDualDivisor), `Isogeny.frobeniusIsog_baseChange_charP_pow`, `Isogeny.zsmul_apply`, `mulByInt`, `frobeniusHomBaseChange`
- **Used by**: `mapTranslateGenericPoint_gKbarPencil` (191)
- **Visibility**: public — **Lines**: 156–172

### `theorem mapTranslateGenericPoint_gKbarPencil` — **LIVE**
- **Type**: `(r' s') (pullback_L) : MapTranslateGenericPoint (E_{K̄}) (pencilIsogBaseChange … pullback_L) (gKbarPencil W r' s')`
- **What**: `gKbarPencil` satisfies the generic-point covariance leaf (Silverman III.8.2), against ANY isogeny whose point map is `r·π̄ + [−s]`.
- **How**: `mapTranslateGenericPoint_add` (MapTranslateGenericAdditive) fed the point-map decomposition + the `r·π` component (`mapTranslateGenericPoint_zsmul` of `mapTranslateGenericPoint_frobenius_Kbar`) + the `−s·id` component (`mapTranslateGenericPoint_mulByInt`).
- **Uses from project**: `mapTranslateGenericPoint_add` (MapTranslateGenericAdditive), `pencilIsogBaseChange_toAddMonoidHom_decomp` (this file), `mapTranslateGenericPoint_zsmul` (this file), `mapTranslateGenericPoint_frobenius_Kbar` (FrobeniusGenericCovariance), `mapTranslateGenericPoint_mulByInt` (this file), `frobFunctionFieldPointKbar`, `zsmulPointHom`
- **Used by**: `mapTranslateGenericPoint_pencil_canonical` (304); also `PencilComapWitnesses.pencilScalingComapDataCard_pDvdR` references it in a docstring (DEAD context)
- **Visibility**: public — **Lines**: 179–197
- **Notes**: Pullback-parametric (holds for any `pullback_L`), which is exactly the genericity the `_pDvdR` route hoped to exploit — but the live consumer is via the canonical-action form below.

### `theorem gKbarPencil_genericPoint` — **LIVE**
- **Type**: `(r' s') : gKbarPencil W r' s' (P_gen^{K̄}) = ffBaseChangePoint (((zsmulPointHom r').comp (frobeniusW_KE)) + zsmulPointHom (-s')) (P_gen)`
- **What**: `gKbarPencil` at the generic point is the function-field base change of the K-level genuine `genuineIsogSmulSub` action (Silverman III.8.2 base change).
- **How**: additivity + `zsmul`-compatibility of `ffBaseChangePoint` (`map_add`, `map_zsmul`), `ffbc_frob_comm` (intertwine `frobeniusW_KE` with `frobₗ`), `ffBaseChangePoint_genericPoint`. (`set_option maxHeartbeats 1000000`.)
- **Uses from project**: `gKbarPencil` (this file), `ffBaseChangePoint`, `frobeniusW_KE`, `frobFunctionFieldPointKbar`, `zsmulPointHom`, `ffbc_frob_comm`, `ffBaseChangePoint_genericPoint`, `genericPoint`
- **Used by**: `pencil_isGenuineWith_Kbar` (264)
- **Visibility**: public — **Lines**: 207–233

### `theorem pencil_isGenuineWith_Kbar` — **LIVE**
- **Type**: `(r' s' hr hs hrK hsK) : IsGenuineWith (E_{K̄}) (pencilIsogBaseChange … pencilBaseChangePullback) (gKbarPencil W r' s')`
- **What**: Wall A pencil genuineness (CoordHom-free): the concrete `pencilBaseChangePullback` is genuine with the geometric action `gKbarPencil`.
- **How**: from `genuineIsogSmulSub_isGenuineWith` (K-level), `gKbarPencil_genericPoint`, `ffBaseChangePoint_some`, and the pullback-coordinate realisations `pencilBaseChangePullback ?_gen = functionFieldMap((rπ−s)^K.pullback ?_gen)` (`baseChangePullback_functionFieldMap` + `functionFieldMap_x/y_gen`). (`set_option maxHeartbeats 1600000`.)
- **Uses from project**: `IsGenuineWith`, `genuineIsogSmulSub_isGenuineWith`, `gKbarPencil_genericPoint` (this file), `ffBaseChangePoint_some`, `pencilIsogBaseChange_pullback` (PencilDualDivisor), `pencilBaseChangePullback` (PencilSeparable), `baseChangePullback_functionFieldMap`, `functionFieldMap_x/y_gen`, `functionField_baseChange`
- **Used by**: `mapTranslateGenericPoint_pencil_canonical` (303)
- **Visibility**: public — **Lines**: 248–285
- **Notes**: The substantive III.8.2 base-change realisation; load-bearing for the live covariance.

### `theorem mapTranslateGenericPoint_pencil_canonical` — **LIVE** (key API)
- **Type**: `(r' s' hr hs hrK hsK) : MapTranslateGenericPoint (E_{K̄}) (pencilIsogBaseChange … pencilBaseChangePullback) (Point.map (pencilIsogBaseChange …).pullback)`
- **What**: the **canonical-action** generic-point covariance `hgcomm` for `(rπ−s)_{K̄}` (the form the comap-witness reductions consume).
- **How**: `mapTranslateGenericPoint_canonical_of_genuine` fed `pencil_isGenuineWith_Kbar` + `mapTranslateGenericPoint_gKbarPencil`. (`set_option maxHeartbeats 1600000`.)
- **Uses from project**: `mapTranslateGenericPoint_canonical_of_genuine` (SeparableWitnesses / WallAGeometricRealization), `pencil_isGenuineWith_Kbar` (this file), `mapTranslateGenericPoint_gKbarPencil` (this file)
- **Used by**: `PencilComapWitnesses.pencil_hcov_kernel` (310), `pencil_two_residues` (2057), `pencil_two_residues_summand_infty` (1972, DEAD); `PencilComapScaling.pencilScalingComapData_hgcomm_canonical` (252, LIVE); `pencil_hcommPrime_discharged` (340, DEAD)
- **Visibility**: public — **Lines**: 292–305
- **Notes**: **The headline export of the file.** Multiple live consumers.

### `theorem pencil_hcommPrime_discharged` — **DEAD**
- **Type**: `(r' s' hr hs hrK hsK) : ∀ (ℓ) (hℓF) (S T) (_hS) (hφT), τ_S(φ^*(weilFunction …)) = φ^*(τ_{φS}(weilFunction …))`
- **What**: the translation covariance `hcomm'` for `(rπ−s)_{K̄}`, fully discharged (no carried `hgcomm`) — the per-`(ℓ,S,T)` covariance at `z = weilFunction`.
- **How**: one-liner `pencil_hcommPrime_of_hgcomm` (SeparableWitnesses) fed `mapTranslateGenericPoint_pencil_canonical`.
- **Uses from project**: `pencil_hcommPrime_of_hgcomm` (SeparableWitnesses), `mapTranslateGenericPoint_pencil_canonical` (this file), `weilFunction`, `translateAlgEquivOfPoint`, `pencilIsogBaseChange`, `pencilBaseChangePullback`
- **Used by**: `PencilComapScaling.pencilScaling_one_of_comapWitness_noδ` (157) — DEAD
- **Visibility**: public — **Lines**: 314–340
- **Notes**: **DEAD.** Its only consumer is the dead canonical-pullback degree-match scaling. The live `Card` chain instead calls `pencil_hcommPrime_of_hgcomm` directly (passing the bundle's `hgcomm`), so this pre-applied form is unused.

### `noncomputable local instance instDecEqACPC : DecidableEq (AlgebraicClosure K)` — **LIVE**
- **How**: `Classical.decEq _`. **Lines**: 139.

---

## File Summary

- **Live declarations** (9 + instance): the entire `gKbarPencil → mapTranslateGenericPoint_pencil_canonical` covariance chain, plus the general-field component leaves (`map_translate_smul_genericPoint`, `mapTranslateGenericPoint_zsmul`, `mapTranslateGenericPoint_mulByInt`). This file is **mostly live** — unusual for the leaf-3 cluster.
- **Dead/superseded declarations** (1): `pencil_hcommPrime_discharged` (314), the pre-applied `hcomm'` form. Only consumer is the dead `pencilScaling_one_of_comapWitness_noδ`. Deleting it (and its dead consumer) is safe; the live path uses `pencil_hcommPrime_of_hgcomm` directly.
- **Hand-rolled vs mathlib**: `map_translate_smul_genericPoint` is explicitly inlined from the unbuildable `ScratchCov.lean` (a hand-roll forced by an upstream build issue). `gKbarPencil` is a hand-built geometric action (an `AddMonoidHom` sum), correctly genuine (no placeholder anti-pattern). Covariance assembly reuses the project's `mapTranslateGenericPoint_add`/`_canonical_of_genuine` infrastructure.
- **Duplication**: minimal within this file. The `map_translate_smul_genericPoint` inline duplicates `ScratchCov.map_translate_smul_genericPoint` (the scratch file), but `ScratchCov` is untracked and off the build path — the inline copy here is the canonical one.
- **Under-general statements**: `mapTranslateGenericPoint_gKbarPencil` is already pullback-parametric (general over `pullback_L`); `mapTranslateGenericPoint_pencil_canonical` specialises to the canonical pullback. `mapTranslateGenericPoint_zsmul` / `_mulByInt` are appropriately general (any field `F`).
- **`set_option`**: file-level lint suppressions; `maxHeartbeats 1000000 in` (L200, `gKbarPencil_genericPoint`), `1600000 in` (L235 `pencil_isGenuineWith_Kbar`, L287 `mapTranslateGenericPoint_pencil_canonical`, L307 `pencil_hcommPrime_discharged`). Three of the four heavy-heartbeat decls are live and load-bearing.
- **No `sorry`.**
