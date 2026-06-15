# Inventory: ./HasseWeil/WeilPairing/PencilComapScaling.lean

**File purpose**: The `rπ − s` analogue of the leaf-2 closer `OneSubProjOrdTransport`. It wires the divisor-pullback reduction `projOrdTransport_of_comap_pointValuation`, the proved pencil translation covariance (`pencil_hcommPrime_*`), the `[ℓ]`-commutation `pencilIsogBaseChange_commute_mulByInt`, and the δ-free `WeilScales` bridges into the leaf-3 scaling pipeline. It defines the **degree-match-free** bundle `PencilScalingComapDataCard` and the kernel-cardinality exponent `pencilKerCard` that the axiom-clean bound consumes.

**Imports**: `HasseWeil.WeilPairing.PencilCovariance`, `HasseWeil.WeilPairing.ProjOrdTransportLocal`, `HasseWeil.WeilPairing.SeparableScaling`, `HasseWeil.WeilPairing.PencilDualDivisor`, `HasseWeil.WeilPairing.SeparableWitnesses`

**Total declarations**: 14 named (2 `structure`, 1 `noncomputable def`, 11 `theorem`) + 1 local `instance`. (The brief's "12/45 live" counts auto-generated structure projections.)

**No `sorry`.**

---

## LIVE / DEAD verdict

Two parallel bundle chains live here. The **`Card` (degree-match-free)** chain is LIVE; the **degree-match (`hkerdeg`-based)** chain is DEAD.

- **LIVE**: `pencil_hproj_of_comapWitness` (77), `pencilScalingComapData_hgcomm_canonical` (244), `pencilKerCard` (288), `pencilKerCard_nonneg` (298), `PencilScalingComapDataCard` (311), `pencilScaling_one_of_comapData_card` (335).
- **DEAD**: `pencilIsogBaseChange_finiteKer_of_hkerdeg_pos` (90), `pencilScaling_one_of_comapWitness_noδ` (120), `PencilScalingComapData` (173), `pencilScaling_one_of_comapData` (198), `pencilScaling_of_comapData` (225), `pencilScaling_of_comapData_of_deg` (257), `pencilScaling_of_comapData_card` (364).

The live consumer (`PencilComapWitnesses.pencilScaling_holds_coprime`) calls `pencilScaling_one_of_comapData_card` *directly* on a hand-built `pencilScalingComapDataCard_canonical`; it does NOT go through the higher-level assembly theorems `pencilScaling_of_comapData_card`/`_of_comapData`, which are therefore orphaned.

---

## Declarations

### `theorem pencil_hproj_of_comapWitness` — **LIVE**
- **Type**: `(r' s' : ℤ) (pullback_L) (hcomap : ComapPointValuationWitness …) : ProjOrdTransport (pencilIsogBaseChange … pullback_L)`
- **What**: `ProjOrdTransport (rπ−s)_{K̄}` from the per-place comap witnesses (Silverman III.4.10c), CoordHom-free. The `rπ−s` analogue of `oneSub_hproj_of_comapWitness`.
- **How**: one-liner `projOrdTransport_of_comap_pointValuation hcomap`.
- **Hypotheses**: abstract `pullback_L`, `hcomap`; standing `K̄` elliptic + `IsIntegrallyClosed` instances.
- **Uses from project**: `projOrdTransport_of_comap_pointValuation` (ProjOrdTransportLocal), `pencilIsogBaseChange` (PencilDualDivisor), `ComapPointValuationWitness`
- **Used by**: `pencilScaling_one_of_comapData_card` (348, LIVE); also `pencilScaling_one_of_comapWitness_noδ` (150) and `pencilScaling_one_of_comapData` (213) — both DEAD
- **Visibility**: public — **Lines**: 77–83

### `theorem pencilIsogBaseChange_finiteKer_of_hkerdeg_pos` — **DEAD**
- **Type**: `(r' s' : ℤ) (pullback_L) (hkerdeg : #ker = deg) (hdeg_pos : 0 < deg) : Finite (ker …)`
- **What**: kernel finiteness from the degree match `#ker = deg > 0`.
- **How**: `rw [hkerdeg]` then `(Nat.card_pos_iff.mp _).2`.
- **Uses from project**: `pencilIsogBaseChange`, `Nat.card_pos_iff`
- **Used by**: `pencilScaling_one_of_comapWitness_noδ` (140), `pencilScaling_one_of_comapData` (206) — both DEAD
- **Visibility**: public — **Lines**: 90–101
- **Notes**: Superseded by the explicit `finiteKer` field of `PencilScalingComapDataCard` (which uses the trace-free `finite_kernel_of_hcov`, no degree match).

### `theorem pencilScaling_one_of_comapWitness_noδ` — **DEAD**
- **Type**: `(r' s' hr hs hrK hsK) (ℓ) [Fact ℓ.Prime] (hℓF) (hcomap) (hkerdeg) (hdeg_pos) : WeilScales … (r·π̄ − s·id) φ.degree`
- **What**: one δ-free `WeilScales` instance for the canonical pullback, with `hcomm'` discharged internally (Wall A) — but exponent `φ.degree`, paying the degree match.
- **How**: `weilScales_noδ` fed `pencil_hproj_of_comapWitness`, `pencilIsogBaseChange_commute_mulByInt`, `hkerdeg`, and `pencil_hcommPrime_discharged`; finiteness via `pencilIsogBaseChange_finiteKer_of_hkerdeg_pos`.
- **Uses from project**: `weilScales_noδ` (SeparableScaling), `pencil_hproj_of_comapWitness`, `pencilIsogBaseChange_finiteKer_of_hkerdeg_pos`, `pencilIsogBaseChange_commute_mulByInt`, `pencil_hcommPrime_discharged` (PencilCovariance)
- **Used by**: NONE
- **Visibility**: public — **Lines**: 120–157
- **Notes**: Orphan. Uses the canonical pullback directly (not the abstract-bundle form). The only consumer of `pencil_hcommPrime_discharged` (PencilCovariance) — so killing this also kills that.

### `structure PencilScalingComapData` — **DEAD**
- **Fields**: `pullback_L`, `hgcomm` (Wall A `MapTranslateGenericPoint`), `hcomap` (`ComapPointValuationWitness`), `hkerdeg` (`#ker = deg`), `hdeg_pos` (`0 < deg`).
- **What**: the δ-free bundle for an abstract `pullback_L` that still **pays the degree match** `hkerdeg`.
- **Used by**: `pencilScaling_one_of_comapData` (200), `pencilScaling_of_comapData` (226), `pencilScaling_of_comapData_of_deg` (259) — all DEAD
- **Visibility**: public — **Lines**: 173–190
- **Notes**: Superseded by `PencilScalingComapDataCard` (drops `hkerdeg`/`hdeg_pos`, adds `finiteKer`).

### `theorem pencilScaling_one_of_comapData` — **DEAD**
- **Type**: `(r' s') (ℓ) [Fact ℓ.Prime] (hℓF) (d : PencilScalingComapData …) : WeilScales … φ.degree`
- **What**: one `WeilScales` instance from the abstract degree-match bundle.
- **How**: `weilScales_noδ` fed the bundle fields; `hcomm'` from `pencil_hcommPrime_of_hgcomm` (SeparableWitnesses).
- **Uses from project**: `weilScales_noδ`, `pencil_hproj_of_comapWitness`, `pencilIsogBaseChange_finiteKer_of_hkerdeg_pos`, `pencilIsogBaseChange_commute_mulByInt`, `pencil_hcommPrime_of_hgcomm` (SeparableWitnesses)
- **Used by**: `pencilScaling_of_comapData` (236), `pencilScaling_of_comapData_of_deg` (266) — DEAD
- **Visibility**: public — **Lines**: 198–218

### `theorem pencilScaling_of_comapData` — **DEAD**
- **Type**: `(pencilData : ∀ r' s', PencilScalingComapData …) : PencilScaling W p r K̄ (fun r' s' => φ.degree)`
- **What**: the full leaf `PencilScaling` from a per-pair degree-match bundle family, exponent = isogeny degree.
- **How**: `intro`, `Int.toNat_natCast`, `pencilScaling_one_of_comapData`.
- **Uses from project**: `pencilScaling_one_of_comapData`, `pencilIsogBaseChange`, `PencilScaling`
- **Used by**: NONE
- **Visibility**: public — **Lines**: 225–236

### `theorem pencilScalingComapData_hgcomm_canonical` — **LIVE**
- **Type**: `(r' s' hr hs hrK hsK) : MapTranslateGenericPoint … (Point.map (rπ−s)^*)`
- **What**: the `hgcomm` field for the canonical pullback is DISCHARGED — it is the proved Wall A `mapTranslateGenericPoint_pencil_canonical`.
- **How**: one-liner `mapTranslateGenericPoint_pencil_canonical`.
- **Uses from project**: `mapTranslateGenericPoint_pencil_canonical` (PencilCovariance), `pencilIsogBaseChange`, `pencilBaseChangePullback`
- **Used by**: `PencilComapWitnesses.pencilScalingComapDataCard_canonical` (2136, LIVE)
- **Visibility**: public — **Lines**: 244–252
- **Notes**: A thin re-export of the Wall A covariance, specialised to the canonical pullback. Supplies the live `hgcomm` field.

### `theorem pencilScaling_of_comapData_of_deg` — **DEAD**
- **Type**: `(deg) (pencilData) (hdeg : ∀ r' s', (deg r' s').toNat = φ.degree) : PencilScaling W p r K̄ deg`
- **What**: `PencilScaling` for an arbitrary non-negative `deg` realised by the carried degrees (degree-match bundle).
- **How**: `intro`, `rw [hdeg]`, `pencilScaling_one_of_comapData`.
- **Uses from project**: `pencilScaling_one_of_comapData`, `pencilIsogBaseChange`, `PencilScaling`
- **Used by**: NONE
- **Visibility**: public — **Lines**: 257–266

### `noncomputable def pencilKerCard` — **LIVE** (key API)
- **Type**: `(pullback_L : ∀ r' s', AlgHom …) : ℤ → ℤ → ℤ`
- **What**: the kernel-cardinality exponent `(r',s') ↦ (#ker(rπ−s)_{K̄} : ℤ)`. The non-negative integer exponent the δ-free `weilScales_noδ_card` produces — used as the `deg` parameter of the bound to **avoid** the geometric degree match `#ker = deg`.
- **How**: `fun r' s' => (Nat.card (pencilIsogBaseChange … (pullback_L r' s')).toAddMonoidHom.ker : ℤ)`.
- **Uses from project**: `pencilIsogBaseChange` (PencilDualDivisor)
- **Used by**: `HasseBound.lean` (L73), `PencilComapWitnesses` (`pencilScaling_holds`, `pencilScaling_holds_coprime`), `pencilKerCard_nonneg` (298), `pencilScaling_of_comapData_card` (367, DEAD)
- **Visibility**: public — **Lines**: 288–295

### `theorem pencilKerCard_nonneg` — **LIVE**
- **What**: `0 ≤ pencilKerCard …` (a cast of `Nat.card`).
- **How**: `Nat.cast_nonneg _`.
- **Uses from project**: `pencilKerCard` (this file)
- **Used by**: `HasseBound.lean` (L75 — supplies `hdeg_nonneg`)
- **Visibility**: public — **Lines**: 298–303

### `structure PencilScalingComapDataCard` — **LIVE** (key API)
- **Fields**: `pullback_L`, `hgcomm` (Wall A `MapTranslateGenericPoint`, canonical action), `hcomap` (`ComapPointValuationWitness`), `finiteKer` (`Finite (ker …)`).
- **What**: the δ-free, surjectivity-free, **degree-match-free** geometric bundle. Drops `hkerdeg`/`hdeg_pos` (vs `PencilScalingComapData`), replaces them by `finiteKer` (mirroring `OneSubScalingData.finiteKer`). The output exponent is `#ker`, so `#ker = deg` is never needed.
- **Used by**: `PencilComapWitnesses` (`pencilScalingComapDataCard_canonical` L2132, `_rZero`, `_pDvdR`, `_sep`), `pencilScaling_one_of_comapData_card` (337), `pencilScaling_of_comapData_card` (365)
- **Visibility**: public — **Lines**: 311–326

### `theorem pencilScaling_one_of_comapData_card` — **LIVE** (key API)
- **Type**: `(r' s') (ℓ) [Fact ℓ.Prime] (hℓF) (d : PencilScalingComapDataCard …) : WeilScales … (r·π̄ − s·id) (#ker …)`
- **What**: one `WeilScales` instance with the `#ker` exponent from the degree-match-free bundle (Silverman III.8.6.1), CoordHom-free, no δ/hsurj/hkerdeg.
- **How**: `haveI := d.finiteKer`; `weilScales_noδ_card` fed `pencilIsogBaseChange_toAddMonoidHom`, `pencil_hproj_of_comapWitness d.hcomap`, `pencilIsogBaseChange_commute_mulByInt`, and `pencil_hcommPrime_of_hgcomm d.hgcomm`.
- **Hypotheses**: prime `ℓ`, `(ℓ:K̄)≠0`, the bundle `d`.
- **Uses from project**: `weilScales_noδ_card` (SeparableScaling), `pencilIsogBaseChange_toAddMonoidHom`/`pencilIsogBaseChange_commute_mulByInt` (PencilDualDivisor), `pencil_hproj_of_comapWitness` (this file), `pencil_hcommPrime_of_hgcomm` (SeparableWitnesses)
- **Used by**: `PencilComapWitnesses.pencilScaling_holds` (2341, DEAD), `pencilScaling_holds_coprime` (2376, LIVE), `pencilScaling_of_comapData_card` (374, DEAD)
- **Visibility**: public — **Lines**: 335–352
- **Notes**: **The per-pair scaling engine for the live leaf.** Called directly by `pencilScaling_holds_coprime` (bypassing the orphaned `_of_comapData_card`).

### `theorem pencilScaling_of_comapData_card` — **DEAD**
- **Type**: `(pencilData : ∀ r' s', PencilScalingComapDataCard …) : PencilScaling W p r K̄ (pencilKerCard … (fun r' s' => (pencilData r' s').pullback_L))`
- **What**: the full leaf `PencilScaling` from a per-pair degree-match-free bundle family, `#ker` exponent.
- **How**: `intro`, `Int.toNat_natCast`, `pencilScaling_one_of_comapData_card`.
- **Uses from project**: `pencilScaling_one_of_comapData_card`, `pencilKerCard`, `pencilIsogBaseChange`
- **Used by**: NONE (`pencilScaling_holds_coprime` inlines this assembly instead)
- **Visibility**: public — **Lines**: 364–374
- **Notes**: Orphan. This is the "intended" public assembler, but the live leaf re-implements the same body inline (to use the `_canonical` bundle on the coprime locus and `pencilJunkPullback` for the exponent). A cleanup could route `pencilScaling_holds_coprime` through this, but only on the coprime locus, which this total-family version does not directly express.

### `noncomputable local instance instDecEqACPCS : DecidableEq (AlgebraicClosure K)` — **LIVE**
- **How**: `Classical.decEq _`. **Lines**: 65.

---

## File Summary

- **Live declarations** (6): `pencil_hproj_of_comapWitness`, `pencilScalingComapData_hgcomm_canonical`, `pencilKerCard`, `pencilKerCard_nonneg`, `PencilScalingComapDataCard` (+ projections), `pencilScaling_one_of_comapData_card` (+ the local instance).
- **Dead/superseded declarations** (7): the **degree-match (`hkerdeg`) bundle chain** — `PencilScalingComapData` (173) and its three consumers `pencilScaling_one_of_comapData` (198), `pencilScaling_of_comapData` (225), `pencilScaling_of_comapData_of_deg` (257); the degree-match finiteness `pencilIsogBaseChange_finiteKer_of_hkerdeg_pos` (90); the canonical-pullback `pencilScaling_one_of_comapWitness_noδ` (120); and the orphaned total-family assembler `pencilScaling_of_comapData_card` (364).
- **Duplication**: this file is a **clean two-copy parallel**: every `…ComapData…` (degree-match) declaration has a `…ComapDataCard…` (degree-match-free) twin. Only the `Card` twins are live. `pencilScaling_one_of_comapWitness_noδ` (canonical, degree-match) is itself a third near-duplicate of `pencilScaling_one_of_comapData` (abstract, degree-match). Cleanup: delete the entire degree-match chain (≈6 decls + the structure), keeping only the `Card` chain.
- **Under-general / orphan note**: `pencilScaling_of_comapData_card` (the only live-style total assembler in the `Card` chain) is itself orphaned because the live leaf inlines its body to restrict to the coprime locus. Either generalise `pencilScaling_holds_coprime` to call it, or delete it.
- **Hand-rolled vs mathlib**: no hand-rolled structures beyond the two bundle records; `pencilKerCard` is a plain `Nat.card` cast. All scaling goes through the project's `weilScales_noδ`/`weilScales_noδ_card` bridges.
- **`set_option`**: file-level lint suppressions only; no `maxHeartbeats`.
- **No `sorry`.**
