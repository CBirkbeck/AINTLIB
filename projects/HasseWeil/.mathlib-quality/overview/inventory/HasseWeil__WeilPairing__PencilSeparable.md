# Inventory: ./HasseWeil/WeilPairing/PencilSeparable.lean

**File purpose**: Defines the **canonical base-changed pencil pullback** `pencilBaseChangePullback := baseChangePullback (rπ − s).pullback` (the single live export, used as the `pullback_L` everywhere on the live path), and carries the K-level separability of `r·π − s` (Silverman III.5.5) to `K̄` to derive the separable degree match `#ker = deg` (`pencil_hkerdeg_galois`). The `#ker = deg` chain is DEAD — the live path uses the degree-match-free `finiteKer` route instead.

**Imports**: `HasseWeil.GapSpines`, `HasseWeil.WeilPairing.PencilDualDivisor`, `HasseWeil.WeilPairing.SeparableWitnesses`, `HasseWeil.WeilPairing.OmegaBaseChange`

**Total declarations**: 8 named (1 `noncomputable def`, 1 `def` (Prop), 6 `theorem`) + 1 local `instance`. (Matches the brief's "1/8 live".)

**No `sorry`.**

---

## LIVE / DEAD verdict

Only `pencilBaseChangePullback` (65) is LIVE. The other 7 form the separability ⟹ `#ker = deg` chain (`OmegaBaseChangeNeZero` + the two `isSeparable` theorems + the two `hkerdeg_galois` theorems), all of which feed the DEAD degree-match (`hkerdeg`) bundle route. The live path obtains kernel finiteness from the trace-free `finite_kernel_of_hcov` (in `PencilComapWitnesses.pencilIsogBaseChange_finiteKer`), so the separable degree match is never needed.

- **LIVE** (1): `pencilBaseChangePullback` (65).
- **DEAD** (7): `OmegaBaseChangeNeZero` (83), `omegaBaseChangeNeZero_holds` (97), `pencilIsogBaseChange_isSeparable_of_omegaBaseChange` (117), `pencilIsogBaseChange_isSeparable` (141), `pencil_hkerdeg_of_omegaBaseChange_galois` (180), `pencil_hkerdeg_galois` (214).

---

## Declarations

### `noncomputable def pencilBaseChangePullback` — **LIVE** (the canonical pullback)
- **Type**: `(r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0) (hrK : (r':K)≠0) (hsK : (s':K)≠0) : K(E_{K̄}) →ₐ[L] K(E_{K̄})`
- **What**: the concrete base-changed `(rπ − s)_{K̄}^*` pullback — the conjugate `Φ ∘ (id_L ⊗ (rπ−s).pullback) ∘ Φ⁻¹` of the genuine K-level pullback. The canonical `pullback_L` for the bundles, mirroring `oneSubFrobeniusPullback_L`.
- **How**: `baseChangePullback (⟨W.toAffine⟩) L (genuineIsogSmulSub W r' s' …).pullback`.
- **Hypotheses**: `r',s' ≠ 0`, `(r':K),(s':K) ≠ 0`; general `L` with `Algebra.IsAlgebraic K L`, `ExpChar L p`, `E_{K̄}` elliptic.
- **Uses from project**: `baseChangePullback` (IsogenyBaseChangeConcrete), `genuineIsogSmulSub`
- **Used by**: ~ everywhere on the live path — `PencilComapWitnesses.pencilScalingComapDataCard_canonical` (2135), `comapPointValuationWitness_pencil`, `pencilIsogBaseChange_finiteKer`, all the `ordAtInfty_pencil_pullback_*`/`comap_pointValuation_pencil_*`/`pencil_two_residues`/`pencil_hcov_kernel`; `PencilComapScaling.pencilScaling_one_of_comapWitness_noδ` (DEAD); `PencilCovariance.pencil_isGenuineWith_Kbar`/`mapTranslateGenericPoint_pencil_canonical` (LIVE)
- **Visibility**: public — **Lines**: 65–69
- **Notes**: The single live declaration of the file. CoordHom-free.

### `def OmegaBaseChangeNeZero` — **DEAD** (Prop)
- **Type**: `Prop`
- **What**: the naturality statement: an isogeny with non-vanishing `omegaPullbackCoeff` over `K` stays so after base change. (`∀ α_L α, α_L.pullback = baseChangePullback α.pullback → ω-coeff α ≠ 0 → ω-coeff α_L ≠ 0`.)
- **How**: pure `Prop` definition.
- **Uses from project**: `Isogeny`, `baseChangePullback`, `omegaPullbackCoeff`
- **Used by**: `pencilIsogBaseChange_isSeparable_of_omegaBaseChange` (118), `pencil_hkerdeg_of_omegaBaseChange_galois` (181) — DEAD. (Also referenced in `OneSubComapConcrete`/`OneSubAffineResidues` docstrings, contrasting with the `1 − π` case.)
- **Visibility**: public — **Lines**: 83–89
- **Notes**: Docstring (L82) admits "no longer carried by any downstream consumer". DEAD.

### `theorem omegaBaseChangeNeZero_holds` — **DEAD**
- **What**: `OmegaBaseChangeNeZero` is DISCHARGED — the ω-coefficient transports by value (`omegaPullbackCoeff_baseChangePullback`) and `functionFieldMap` is injective, so `≠ 0` carries.
- **How**: `intro α_L α hpb hα`; `rw [omegaPullbackCoeff_baseChangePullback]`; `map_eq_zero_iff` + `functionFieldMap_injective`.
- **Uses from project**: `omegaPullbackCoeff_baseChangePullback` (OmegaBaseChange), `SmoothPlaneCurve.functionFieldMap_injective`
- **Used by**: `pencilIsogBaseChange_isSeparable` (146), `pencil_hkerdeg_galois` (236) — DEAD
- **Visibility**: public — **Lines**: 97–101
- **Notes**: A genuine, axiom-clean theorem — but dead, since its consumers are all in the dead `#ker = deg` chain.

### `theorem pencilIsogBaseChange_isSeparable_of_omegaBaseChange` — **DEAD**
- **Type**: `(hbc : OmegaBaseChangeNeZero W L) (r' s' hr hs hrK hsK) : (pencilIsogBaseChange … pencilBaseChangePullback).IsSeparable`
- **What**: K̄-separability of the base-changed pencil, given the transport leaf `hbc`.
- **How**: K-level separability `genuineIsogSmulSub_isSeparable` ⟹ `ω-coeff ≠ 0`; transport via `hbc`; `isSeparable_iff_omegaPullbackCoeff_ne_zero`.
- **Uses from project**: `isSeparable_iff_omegaPullbackCoeff_ne_zero`, `genuineIsogSmulSub_isSeparable`, `genuineIsogSmulSub`, `pencilIsogBaseChange`, `pencilBaseChangePullback`, `pencilIsogBaseChange_pullback`
- **Used by**: `pencilIsogBaseChange_isSeparable` (145), `pencil_hkerdeg_of_omegaBaseChange_galois` (204) — DEAD
- **Visibility**: public — **Lines**: 117–135

### `theorem pencilIsogBaseChange_isSeparable` — **DEAD**
- **Type**: `(r' s' hr hs hrK hsK) : (pencilIsogBaseChange … pencilBaseChangePullback).IsSeparable`
- **What**: K̄-separability, UNCONDITIONAL (`hbc` discharged by `omegaBaseChangeNeZero_holds`).
- **How**: `pencilIsogBaseChange_isSeparable_of_omegaBaseChange` fed `omegaBaseChangeNeZero_holds`.
- **Uses from project**: `pencilIsogBaseChange_isSeparable_of_omegaBaseChange`, `omegaBaseChangeNeZero_holds` (this file)
- **Used by**: NONE (orphan)
- **Visibility**: public — **Lines**: 141–146
- **Notes**: Axiom-clean and unconditional, but completely unreferenced — separability is not needed on the live `finite_kernel_of_hcov` route.

### `theorem pencil_hkerdeg_of_omegaBaseChange_galois` — **DEAD**
- **Type**: `(hbc) (r' s' hr hs hrK hsK) (h_normal) (h_card) : #ker (rπ − s)_{K̄} = deg`
- **What**: the separable degree match `#ker = deg` (Silverman III.4.10c) for the canonical pullback, given the transport leaf `hbc` + the Galois-correspondence inputs `h_normal`/`h_card`.
- **How**: `pencil_hkerdeg_of_separable_witnesses` fed the separability (`pencilIsogBaseChange_isSeparable_of_omegaBaseChange`) + `h_normal`/`h_card`.
- **Uses from project**: `pencil_hkerdeg_of_separable_witnesses` (SeparableWitnesses), `pencilIsogBaseChange_isSeparable_of_omegaBaseChange` (this file), `pencilIsogBaseChange`, `pencilBaseChangePullback`
- **Used by**: `pencil_hkerdeg_galois` (235) — DEAD
- **Visibility**: public — **Lines**: 180–206

### `theorem pencil_hkerdeg_galois` — **DEAD**
- **Type**: `(r' s' hr hs hrK hsK) (h_normal) (h_card) : #ker (rπ − s)_{K̄} = deg`
- **What**: `#ker = deg` with `hbc` DISCHARGED (only the standard Galois inputs `h_normal`/`h_card` remain).
- **How**: `pencil_hkerdeg_of_omegaBaseChange_galois` fed `omegaBaseChangeNeZero_holds`.
- **Uses from project**: `pencil_hkerdeg_of_omegaBaseChange_galois`, `omegaBaseChangeNeZero_holds` (this file)
- **Used by**: NONE (only a docstring mention in PencilComapScaling L31, "supplied by `pencil_hkerdeg_galois`")
- **Visibility**: public — **Lines**: 214–236
- **Notes**: This was the planned `hkerdeg` supplier for the degree-match bundle `PencilScalingData`/`PencilScalingComapData`. DEAD because the live `Card` bundle uses `finiteKer` (via `finite_kernel_of_hcov`) and the `#ker` exponent, never the degree match. The docstring still claims it is "supplied by `pencil_hkerdeg_galois`" — stale: PencilComapScaling no longer carries `hkerdeg` on the live path.

### `noncomputable local instance instDecEqACPencilSep : DecidableEq (AlgebraicClosure K)` — **LIVE**
- **How**: `Classical.decEq _`. **Lines**: 163.
- **Notes**: In the `AlgClosure` section, which houses only the dead `hkerdeg_galois` theorems; boilerplate.

---

## File Summary

- **Live declarations** (1 + instance): `pencilBaseChangePullback` — the canonical base-changed pullback. This single definition is the most-referenced live export of the file (it is the `pullback_L` plugged into `pencilIsogBaseChange` everywhere on the live path).
- **Dead/superseded declarations** (7): the entire **separability ⟹ `#ker = deg`** chain: `OmegaBaseChangeNeZero` (83), `omegaBaseChangeNeZero_holds` (97), `pencilIsogBaseChange_isSeparable_of_omegaBaseChange` (117), `pencilIsogBaseChange_isSeparable` (141), `pencil_hkerdeg_of_omegaBaseChange_galois` (180), `pencil_hkerdeg_galois` (214). All feed the DEAD degree-match bundle route (`PencilScalingComapData`/`PencilScalingData`); the live path replaces `#ker = deg` with `finiteKer` + the `#ker` exponent.
- **Why dead despite being correct math**: the substantive content here (III.5.5 separability + III.4.10c degree match) is the *classical* way to get a finite kernel and the degree exponent. The reviewer-endorsed Route-2A live path instead uses (a) the trace-free `finite_kernel_of_hcov` for finiteness and (b) `pencilKerCard` (the literal `#ker`) for the exponent — so neither separability nor the degree match is on the bound path. These 7 declarations are sound but vestigial.
- **Stale docstrings**: L31 of PencilComapScaling and the docstrings here still assert the `hkerdeg` field is "supplied by `pencil_hkerdeg_galois`" — no longer true on the live path. Worth correcting during cleanup.
- **Under-general note**: `pencilBaseChangePullback` is stated for general `L` with `Algebra.IsAlgebraic K L`, `ExpChar L p` — appropriately general. The dead `hkerdeg` theorems are specialised to `AlgebraicClosure K` (they need the Galois fibre count).
- **Hand-rolled vs mathlib**: `pencilBaseChangePullback` reuses `baseChangePullback`; `omegaBaseChangeNeZero_holds` reuses `omegaPullbackCoeff_baseChangePullback` + `functionFieldMap_injective`. No hand-rolled structures.
- **Cleanup recommendation**: delete the `AlgClosure` section (L157–238, the two `hkerdeg_galois` theorems + instance) and the four separability declarations (L83–146), keeping only `pencilBaseChangePullback` (and updating the file docstring, which centres on the now-dead separability transport). This would reduce the file to ≈25 lines. The `GapSpines` and `OmegaBaseChange` imports exist mainly for the dead separability machinery and may become droppable.
- **`set_option`**: file-level lint suppressions only; no `maxHeartbeats`.
- **No `sorry`.**
