# Inventory: ./HasseWeil/WeilPairing/PencilDualDivisor.lean

**File purpose**: Defines the concrete base-changed pencil isogeny `pencilIsogBaseChange (rπ − s)_{K̄}` (`Isogeny.mkBaseChange` with point map `r·π̄ − s·id`) and its structural unfoldings + the `[ℓ]`-commutation. It ALSO carries the **divisor-pushforward dual route** for the leaf-3 scaling (`PencilScalingData` + `pencilScaling_of_divisorDual`) — the mirror of the leaf-2 `OneSubDualDivisor` — but that whole route is now DEAD (superseded by the δ-free comap route in `PencilComapScaling`/`PencilComapWitnesses`).

**Imports**: `HasseWeil.WeilPairing.OneSubDualDivisor`, `HasseWeil.WeilPairing.IsogenyBaseChangeConcrete`

**Total declarations**: 6 named (1 `noncomputable def`, 2 simp `theorem`, 1 `structure`, 2 `theorem`) + 1 local `instance`. (The brief's "4/28 live" counts `PencilScalingData`'s 7 auto-generated projections + the structure + the named decls.)

**No `sorry`.**

---

## LIVE / DEAD verdict

The concrete isogeny constructor and its three structural lemmas are LIVE (used throughout the cluster — they ARE the `(rπ − s)_{K̄}` object everyone manipulates). The dual-divisor scaling route (`PencilScalingData` and its two theorems) is DEAD: it is the divisor-pushforward analogue the live work replaced with the comap route.

- **LIVE** (4): `pencilIsogBaseChange` (101), `pencilIsogBaseChange_toAddMonoidHom` (108), `pencilIsogBaseChange_pullback` (115), `pencilIsogBaseChange_commute_mulByInt` (124).
- **DEAD** (4): `PencilScalingData` (169), `pencilScaling_of_data` (227), `pencilScaling_of_divisorDual` (294), `pencilScaling_of_divisorDual_of_deg` (309).

---

## Declarations

### `noncomputable def pencilIsogBaseChange` — **LIVE** (the central object)
- **Type**: `(r' s' : ℤ) (pullback_L : K(E_{K̄}) →ₐ[L] K(E_{K̄})) : Isogeny (E_{K̄}) (E_{K̄})`
- **What**: the concrete base-changed pencil isogeny, built from a base-changed pullback `pullback_L` and the **concrete** point map `r'·π̄ − s'·id` (where `π̄ = frobeniusHomBaseChange`), via `Isogeny.mkBaseChange`. Its `toAddMonoidHom` is definitionally the bare hom named in `PencilScaling`.
- **How**: `Isogeny.mkBaseChange L pullback_L (r' • frobeniusHomBaseChange W p r L - s' • AddMonoidHom.id …)`.
- **Hypotheses**: `L/K` extension with `ExpChar L p`, `E_{K̄}` elliptic (general `L`, not only `AlgebraicClosure K`).
- **Uses from project**: `Isogeny.mkBaseChange`, `frobeniusHomBaseChange` (IsogenyBaseChange / FrobMatrixData)
- **Used by**: ~150 sites across the whole cluster — every theorem in PencilComapWitnesses, PencilComapScaling, PencilCovariance, PencilSeparable that mentions `(rπ − s)_{K̄}`; plus the dead `PencilScalingData`/scaling route here.
- **Visibility**: public — **Lines**: 101–106
- **Notes**: The canonical realising isogeny. Not a placeholder — its pullback is the genuine base-changed `genuineIsogSmulSub` pullback (carried as the `pullback_L` argument), and its hom is the genuine `r·π̄ − s·id`.

### `@[simp] theorem pencilIsogBaseChange_toAddMonoidHom` — **LIVE**
- **What**: `(pencilIsogBaseChange … pullback_L).toAddMonoidHom = r'•frobeniusHomBaseChange − s'•id` (`rfl`).
- **How**: `Isogeny.mkBaseChange_toAddMonoidHom`.
- **Uses from project**: `Isogeny.mkBaseChange_toAddMonoidHom`, `frobeniusHomBaseChange`
- **Used by**: `PencilComapWitnesses` (`pencil_toAddMonoidHom_decomp` L934 DEAD, `pencilIsogBaseChange_rZero_eq_mulByInt` L2167 DEAD, `pencilKerCard_pullback_indep` L2319 LIVE); `PencilComapScaling.pencilScaling_one_of_comapData_card` (347) and `_one_of_comapWitness_noδ`/`_one_of_comapData` (LIVE/DEAD); `PencilCovariance.pencilIsogBaseChange_toAddMonoidHom_decomp` (162, LIVE)
- **Visibility**: public — **Lines**: 108–113

### `@[simp] theorem pencilIsogBaseChange_pullback` — **LIVE**
- **What**: `(pencilIsogBaseChange … pullback_L).pullback = pullback_L` (`rfl`).
- **How**: `Isogeny.mkBaseChange_pullback`.
- **Uses from project**: `Isogeny.mkBaseChange_pullback`
- **Used by**: `PencilComapWitnesses` (`ordAtInfty_pencil_pullback_x/y_gen` L205/224 LIVE, `omegaPullbackCoeff_pencil` L251 LIVE, `pencil_pullback_x/y_gen_eq_…` DEAD); `PencilCovariance.pencil_isGenuineWith_Kbar` (273/281, LIVE); `PencilSeparable.pencilIsogBaseChange_isSeparable_of_omegaBaseChange` (131, DEAD)
- **Visibility**: public — **Lines**: 115–119

### `theorem pencilIsogBaseChange_commute_mulByInt` — **LIVE**
- **What**: `[ℓ] ∘ φ_L = φ_L ∘ [ℓ]` for `φ_L = (rπ − s)_{K̄}` (any pullback), at the `AddMonoidHom` level. Pure `map_zsmul`, no geometry.
- **How**: `ext P`; `rw [AddMonoidHom.comp_apply, …, mulByInt_apply, mulByInt_apply, map_zsmul]`.
- **Uses from project**: `mulByInt`, `mulByInt_apply`, `pencilIsogBaseChange`
- **Used by**: `PencilComapScaling.pencilScaling_one_of_comapData_card` (349, LIVE); also `_one_of_comapWitness_noδ` (152) and `_one_of_comapData` (214) — DEAD; `pencilScaling_of_data` (243, DEAD)
- **Visibility**: public — **Lines**: 124–133
- **Notes**: Supplies the `[ℓ]`-commutation input to the live `weilScales_noδ_card`.

### `structure PencilScalingData` — **DEAD**
- **Fields**: `pullback_L`, `finiteKer`, `degK`, `hdeg_bc` (degree preservation), `hproj` (`ProjOrdTransport`), `hsurj` (surjectivity over `K̄`), `hkerdeg` (`#ker = deg`), `hcomm'` (translation covariance).
- **What**: the divisor-pushforward-dual geometric bundle for `(rπ − s)_{K̄}` — the mirror of leaf 2's `OneSubScalingData`. Carries the FULL set `{hproj, hsurj, hkerdeg, hcomm'}` plus `degK`/`hdeg_bc` (degree preservation).
- **Used by**: `pencilScaling_of_data` (228), `pencilScaling_of_divisorDual` (295), `pencilScaling_of_divisorDual_of_deg` (311) — all DEAD
- **Visibility**: public — **Lines**: 169–209
- **Notes**: **DEAD route.** No code consumer outside this file (only docstring mentions in PencilSeparable/SeparableWitnesses/PencilCovariance). Superseded by the δ-free `PencilScalingComapDataCard` (PencilComapScaling), which drops `hsurj`/`hkerdeg`/`degK`/`hdeg_bc`/`δ` and refines `hproj` to per-place comap witnesses.

### `theorem pencilScaling_of_data` — **DEAD**
- **Type**: `(r' s') (ℓ) [Fact ℓ.Prime] (hℓF) (d : PencilScalingData …) : WeilScales … (r·π̄ − s·id) d.degK`
- **What**: one `WeilScales` instance from the bundled dual-divisor data, via `weilScales_of_dualComp` + the divisor-pushforward dual `divisorPushforwardDual` and its dual relation `divisorPushforwardDual_comp` (automatic via the σ-bridge, no char-poly).
- **How**: `weilScales_of_dualComp` fed `pencilIsogBaseChange_toAddMonoidHom`, `d.hdeg_bc`, `d.hproj`, `pencilIsogBaseChange_commute_mulByInt`, `divisorPushforwardDual(_comp)`, `d.hkerdeg`, `d.hcomm'`.
- **Uses from project**: `weilScales_of_dualComp` (SeparableScaling), `divisorPushforwardDual`/`divisorPushforwardDual_comp` (OneSubDualDivisor), `pencilIsogBaseChange_toAddMonoidHom`, `pencilIsogBaseChange_commute_mulByInt` (this file)
- **Used by**: `pencilScaling_of_divisorDual` (303), `pencilScaling_of_divisorDual_of_deg` (317) — DEAD
- **Visibility**: public — **Lines**: 227–249

### `theorem pencilScaling_of_divisorDual` — **DEAD**
- **Type**: `(pencilData : ∀ r' s', PencilScalingData …) : PencilScaling W p r K̄ (fun r' s' => (pencilData r' s').degK)`
- **What**: the full leaf `PencilScaling` from a per-pair dual-divisor bundle family, exponent = carried `degK`.
- **How**: `intro`, `Int.toNat_natCast`, `pencilScaling_of_data`.
- **Uses from project**: `pencilScaling_of_data` (this file), `PencilScaling`
- **Used by**: NONE (only a docstring mention in PencilComapScaling L37 contrasting it with the δ-free route)
- **Visibility**: public — **Lines**: 294–303
- **Notes**: **DEAD** — the originally-planned divisor-pushforward-dual leaf-3 closer, replaced by `pencilScaling_holds_coprime`.

### `theorem pencilScaling_of_divisorDual_of_deg` — **DEAD**
- **Type**: `(deg) (pencilData) (hdeg : ∀ r' s', (deg r' s').toNat = (pencilData r' s').degK) : PencilScaling W p r K̄ deg`
- **What**: `PencilScaling` for an arbitrary non-negative `deg` realised by the carried `degK` (dual-divisor bundle).
- **How**: `intro`, `rw [hdeg]`, `pencilScaling_of_data`.
- **Uses from project**: `pencilScaling_of_data` (this file), `PencilScaling`
- **Used by**: NONE
- **Visibility**: public — **Lines**: 309–317

### `noncomputable local instance instDecEqACPencil : DecidableEq (AlgebraicClosure K)` — **LIVE**
- **How**: `Classical.decEq _`. **Lines**: 266.
- **Notes**: In the `Assemble` section, which only houses the dead `_divisorDual` theorems — but the instance itself is harmless boilerplate.

---

## File Summary

- **Live declarations** (4 + instance): `pencilIsogBaseChange` and its three structural lemmas (`_toAddMonoidHom`, `_pullback`, `_commute_mulByInt`). These are the **definitional core** of the entire leaf-3 cluster — every other Pencil file builds on this isogeny.
- **Dead/superseded declarations** (4): the entire **divisor-pushforward-dual scaling route** — `PencilScalingData` (169) and its consumers `pencilScaling_of_data` (227), `pencilScaling_of_divisorDual` (294), `pencilScaling_of_divisorDual_of_deg` (309). This was the leaf-2-style dual route; it carries `hsurj`/`hkerdeg`/`δ` that the live δ-free comap route eliminated.
- **Duplication**: `PencilScalingData` (dead, dual route) vs `PencilScalingComapData`/`PencilScalingComapDataCard` (PencilComapScaling, the comap route) are three parallel bundle records for the same isogeny; `pencilScaling_of_divisorDual`/`_of_deg` parallel `pencilScaling_of_comapData`/`_of_deg`/`_of_comapData_card`. Only the `Card` variant in PencilComapScaling is live.
- **Under-general note**: `pencilIsogBaseChange` (and its three lemmas) are stated for a general `L` with `ExpChar L p` (not only `AlgebraicClosure K`) — appropriately general and reused at `L = K̄` everywhere. Good.
- **Hand-rolled vs mathlib**: `pencilIsogBaseChange` uses the project's `Isogeny.mkBaseChange`; no placeholder anti-pattern (pullback and hom agree by construction). The dead route reuses the project's `divisorPushforwardDual`/`weilScales_of_dualComp`.
- **Cleanup recommendation**: delete the `Data`/`Assemble` sections (L137–319, the dual-divisor route + `PencilScalingData`), keeping only the `BaseChange` section (the live isogeny + 3 lemmas + commute). Note `OneSubDualDivisor` is imported solely for the dead `divisorPushforwardDual` — after deletion this import may also be droppable.
- **`set_option`**: file-level lint suppressions only; no `maxHeartbeats`.
- **No `sorry`.**
