# Inventory: ./HasseWeil/WeilPairing/WallAGenericRealization.lean

**File purpose**: The **reusable, conceptually-hard core of Wall A (G-004)**. Discharges the
compatibility square needed to realize the *opaque* base-changed pullback
`baseChangePullback f = Φ ∘ (id_L ⊗ f) ∘ Φ⁻¹` on the generic-point coordinates over an algebraic
extension `L`. The key fact (`tensorFunctionFieldEquiv_one_tmul`) shows the scalar-extension iso
`Φ : L ⊗_F K(C) ≃ₐ[L] K(C_L)` collapses to the natural inclusion `functionFieldMap` on
`algebraMap`'d elements; everything else (base-change of the pullback, of the generic coordinates,
and of the generic point) follows. The `1 − π` payoff (`oneSubFrobeniusPullback_L_x/y_gen`) is the
G-004 square realized **CoordHom-free**. Stated over a **general** `[Algebra.IsAlgebraic K L]`, so it
serves both the `1 − π` and `rπ − s` leaves.

**Imports**: `HasseWeil.WeilPairing.IsogenyBaseChangeConcrete`, `HasseWeil.EC.GenericPoint`

**Total declarations**: 11 top-level (`grep`-confirmed): 10 `theorem` + 1 `noncomputable def`. The task's
"13/14" ratio counts at a finer granularity (section variables / structure-projection artifacts); **at the
top-level-declaration level all 11 named declarations are LIVE** (each has a real, non-comment consumer,
directly or transitively).

**Options set file-wide**: `linter.unusedSectionVars false`, `linter.unusedDecidableInType false`,
`linter.style.longLine false`.

---

## Section `Compat` (vars `{F} [Field F] (C : SmoothPlaneCurve F)`, `(L) [Field L] [Algebra F L] [Algebra.IsAlgebraic F L]`)

### `theorem tensorFunctionFieldEquiv_one_tmul`
- **Type**: `(z : C.toAffine.FunctionField) : tensorFunctionFieldEquiv C L (1 ⊗ₜ[F] z) = C.functionFieldMap L z`
- **What**: **The Wall-A lynchpin (Silverman I.2).** The function-field scalar-extension iso `Φ` collapses
  to `functionFieldMap` on `1 ⊗ (·)`.
- **How**: `IsFractionRing.ringHom_ext` over `C.CoordinateRing` reduces both `F`-algebra ring homs to
  agreement on `C.CoordinateRing`; there the LHS is pushed through `includeRight_apply`, a structure-hom
  identification (`Algebra.TensorProduct.map_tmul`), `IsScalarTower.of_algebraMap_eq`,
  `IsFractionRing.algEquivOfAlgEquiv_algebraMap`, `IsLocalization.algEquiv`/`AlgEquiv.restrictScalars_apply`,
  `fwdPinned_tmul`, and `functionFieldMap_algebraMap` to `coordRingMap`.
- **Hypotheses**: section vars; uses `letI := C.isDomain_tensorCoordRing L`.
- **Uses from project**: `tensorFunctionFieldEquiv`, `functionFieldMap(_algebraMap)`, `coordRingMap`,
  `tensorFunctionFieldStructureHom`, `tensorFunctionFieldAlgebra`, `functionField_baseChange_fracEquiv`,
  `functionField_tensor_locBaseChange`, `coordRingScalarExtPinned`, `fwdPinned(_tmul)`,
  `tensor_functionField_isFractionRing`, `isDomain_tensorCoordRing` (all `SmoothPlaneCurve`, from
  `IsogenyBaseChangeConcrete` chain).
- **Used by**: `baseChangePullback_functionFieldMap` (L165, L166 — internal, transitively external).
- **Visibility**: public.
- **Lines**: 91–149, proof ~58 lines.
- **LIVE (transitively).** Notes: **>30-line proof** with many `show`/`letI` re-typings — the single
  hardest proof in the file. Candidate for documentation but hard to decompose (it is one
  `ringHom_ext` argument).

---

### `theorem baseChangePullback_functionFieldMap`
- **Type**: `(f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) (z) : baseChangePullback C L f (C.functionFieldMap L z) = C.functionFieldMap L (f z)`
- **What**: the base-changed pullback intertwines `f` with the natural inclusion (Silverman I.2). The
  immediate, widely-reused corollary of the lynchpin.
- **How**: `baseChangePullback_apply`; `Φ⁻¹(functionFieldMap z) = 1 ⊗ z` (from
  `tensorFunctionFieldEquiv_one_tmul` + `symm_apply_apply`); `lTensorMap_tmul`; then the lynchpin again.
- **Hypotheses**: section vars.
- **Uses from project**: `baseChangePullback(_apply)`, `tensorFunctionFieldEquiv`, `functionFieldMap`,
  `lTensorMap_tmul`, `tensorFunctionFieldEquiv_one_tmul` (this file), `isDomain_tensorCoordRing`.
- **Used by**: `oneSubFrobeniusPullback_L_x/y_gen` (this file, L290/L301) **and externally — heavily**:
  `OmegaBaseChange.lean:128`, `PencilComapWitnesses.lean:178,190,650`, `PencilCovariance.lean:276,284`,
  `OneSubAffineResidues.lean:123`. (One of the most-reused lemmas in the WeilPairing layer.)
- **Visibility**: public.
- **Lines**: 157–166, proof ~9 lines.
- **LIVE.** **Key cross-cluster API.**

---

## Section `GenericCoords` (vars `{K} [Field K] (W : WeierstrassCurve K) [IsElliptic]`, `(L) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [(W.baseChange L).IsElliptic]`)

### `theorem coordRingMap_X_gen`
- **Type**: `coordRingMap L (algebraMap (Polynomial K) CoordinateRing X) = algebraMap (Polynomial L) CoordinateRing X`
- **What**: `coordRingMap` sends the `X`-generator class to the `X`-generator class.
- **How**: `CoordinateRing.map_mk`, `Polynomial.map_C/map_X`, then `rfl`.
- **Hypotheses**: section vars.
- **Uses from project**: `SmoothPlaneCurve.coordRingMap`, `WeierstrassCurve.Affine.CoordinateRing.map(_mk)`,
  `WeierstrassCurve.baseChange`.
- **Used by**: `functionFieldMap_x_gen` (L210, internal).
- **Visibility**: public. **Lines**: 179–192, ~10 lines. **LIVE (transitively).**

---

### `theorem coordRingMap_Y_gen`
- **Type**: `coordRingMap L (AdjoinRoot.root W.polynomial) = AdjoinRoot.root (W.baseChange L).polynomial`
- **What**: `coordRingMap` sends the `Y`-generator (the `AdjoinRoot` root) to the `Y`-generator.
- **How**: `← AdjoinRoot.mk_X`, `CoordinateRing.map_mk`, `Polynomial.map_X`, `AdjoinRoot.mk_X`.
- **Uses from project**: `coordRingMap`, `CoordinateRing.map(_mk)`, `AdjoinRoot.root/mk_X`, `baseChange`.
- **Used by**: `functionFieldMap_y_gen` (L219, internal).
- **Visibility**: public. **Lines**: 195–202, ~4 lines. **LIVE (transitively).**

---

### `theorem functionFieldMap_x_gen`
- **Type**: `(⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (x_gen W) = x_gen (W.baseChange L)`
- **What**: base change sends `x_gen^K` to `x_gen^{K̄}` (Silverman I.2).
- **How**: `rw [x_gen, functionFieldMap_algebraMap, coordRingMap_X_gen]; rfl`.
- **Uses from project**: `x_gen`, `functionFieldMap(_algebraMap)`, `coordRingMap_X_gen` (this file).
- **Used by**: `ffBaseChangePoint_genericPoint` (L262), `oneSubFrobeniusPullback_L_x_gen` (L289, internal)
  **and externally — heavily**: `OmegaBaseChange.lean:170,207`, `OneSubAffineResidues.lean:132,158,234,260,284`,
  `PencilComapWitnesses.lean:177,666,686,703,736`, `PencilCovariance.lean:274`.
- **Visibility**: public. **Lines**: 206–211, ~3 lines. **LIVE. Key cross-cluster API.**

---

### `theorem functionFieldMap_y_gen`
- **Type**: y-analogue of `functionFieldMap_x_gen`.
- **How**: as above with `coordRingMap_Y_gen`.
- **Used by**: `ffBaseChangePoint_genericPoint` (L262), `oneSubFrobeniusPullback_L_y_gen` (L300) **and
  externally**: `OmegaBaseChange.lean:172`, `OneSubAffineResidues.lean:161,235,285`,
  `PencilComapWitnesses.lean:189,667,704,747`, `PencilCovariance.lean:282`.
- **Visibility**: public. **Lines**: 215–220, ~3 lines. **LIVE. Key cross-cluster API.**

---

## Section `PointMap` (adds `[DecidableEq K]`, `[DecidableEq L]`)

### `noncomputable def ffBaseChangePoint`
- **Type**: `:= Affine.Point.map (W' := W) (S := K) (functionField_baseChange L)`
- **What**: the function-field base-change point map (geometric realization of `functionFieldMap` on
  `E`-points), typed via `W' := W` over base field `K`.
- **How**: definitional.
- **Hypotheses**: section vars + `[DecidableEq K] [DecidableEq L]`.
- **Uses from project**: `WeierstrassCurve.Affine.Point.map`, `SmoothPlaneCurve.functionField_baseChange`.
- **Used by**: `ffBaseChangePoint_some`, `ffBaseChangePoint_genericPoint` (this file); `ffbc_frob_comm`,
  `gKbar_genericPoint` (WallAGeometricRealization, real uses); `PencilCovariance.lean` (L209,218,…,267, many
  real uses).
- **Visibility**: public. **Lines**: 236–238. **LIVE. Key cross-cluster API.**

---

### `theorem ffBaseChangePoint_some`
- **Type**: `(x y h) : ffBaseChangePoint W L (Affine.Point.some x y h) = Affine.Point.some (functionFieldMap L x) (functionFieldMap L y) (…)`
- **What**: `ffBaseChangePoint` on a `some` applies `functionFieldMap` to both coordinates.
- **How**: `rfl`.
- **Uses from project**: `ffBaseChangePoint`, `functionFieldMap`, `Affine.Point.some`,
  `Affine.baseChange_nonsingular`, `functionField_baseChange`.
- **Used by**: `WallAGeometricRealization.lean:101` (`ffbc_frob_comm`), `PencilCovariance.lean:267` (real uses).
- **Visibility**: public. **Lines**: 242–250. **LIVE.**

---

### `theorem ffBaseChangePoint_genericPoint`
- **Type**: `ffBaseChangePoint W L (genericPoint W) = genericPoint (W.baseChange L)`
- **What**: the base-change point map sends the generic point to the generic point (Silverman I.2/III.4.2).
- **How**: `rw [genericPoint, genericPoint]`, `Affine.Point.some.injEq`, then
  `⟨functionFieldMap_x_gen, functionFieldMap_y_gen⟩`.
- **Uses from project**: `ffBaseChangePoint`, `genericPoint`, `functionFieldMap_x/y_gen` (this file),
  `Affine.Point.some`.
- **Used by**: `WallAGeometricRealization.lean:138` (`gKbar_genericPoint`), `PencilCovariance.lean:232`
  (real uses).
- **Visibility**: public. **Lines**: 257–262, ~4 lines. **LIVE.**

---

## Section `OneSub` (vars `{K} [Field K] [Fintype K] [DecidableEq K]`, `W`, `L` as above)

### `theorem oneSubFrobeniusPullback_L_x_gen`
- **Type**: `(hq : 2 ≤ Fintype.card K) : oneSubFrobeniusPullback_L W L hq (x_gen (W.baseChange L)) = functionFieldMap L ((isogOneSub_negFrobenius W hq).pullback (x_gen W))`
- **What**: **the `1 − π` G-004 payoff (CoordHom-free):** the concrete base-changed pullback of `1 − π` on
  the `K̄`-generic x-coordinate equals the `functionFieldMap`-image of the `K`-level addition-formula pullback.
- **How**: `rw [oneSubFrobeniusPullback_L, ← functionFieldMap_x_gen]`; `exact baseChangePullback_functionFieldMap …`.
- **Hypotheses**: `2 ≤ #K`.
- **Uses from project**: `oneSubFrobeniusPullback_L`, `functionFieldMap_x_gen` (this file),
  `baseChangePullback_functionFieldMap` (this file), `isogOneSub_negFrobenius`, `x_gen`.
- **Used by**: `WallAGeometricRealization.lean:193` (`oneSub_isGenuineWith_Kbar`) **and externally**
  `OneSubAffineResidues.lean:311`, `OneSubInftyResidues.lean:177` (real uses).
- **Visibility**: public. **Lines**: 285–291, ~3 lines. **LIVE.**

---

### `theorem oneSubFrobeniusPullback_L_y_gen`
- **Type**: y-analogue of `oneSubFrobeniusPullback_L_x_gen`.
- **How**: as above with `functionFieldMap_y_gen`.
- **Used by**: `WallAGeometricRealization.lean:196`, `OneSubAffineResidues.lean:325`,
  `OneSubInftyResidues.lean:196` (real uses).
- **Visibility**: public. **Lines**: 296–302, ~3 lines. **LIVE.**

---

## File Summary

- **Role in proof**: The **reusable engine** behind Wall A. `baseChangePullback_functionFieldMap`,
  `functionFieldMap_x/y_gen`, `ffBaseChangePoint(_some/_genericPoint)`, and
  `oneSubFrobeniusPullback_L_x/y_gen` are the most-reused lemmas across the entire WeilPairing
  base-change layer (`OmegaBaseChange`, `OneSubAffineResidues`, `OneSubInftyResidues`,
  `PencilComapWitnesses`, `PencilCovariance`, `WallAGeometricRealization`). All four leaf chains
  (`π`, `1 − π`, `rπ − s`) of Route 2A funnel through it.
- **(a) Dead/unused declarations**: **none at the top-level-declaration level.** All 11 named decls have a
  real consumer (`coordRingMap_X/Y_gen` and `tensorFunctionFieldEquiv_one_tmul` only transitively, via the
  two corollaries that are themselves heavily reused). If the audit's "14" counts section-variable or
  structure-projection nodes, the single non-live node is not a top-level declaration — **no source-level
  decl should be deleted here.**
- **(b) Scratch/superseded sub-routes**: none. This is the active CoordHom-free realization.
- **(c) Hand-rolled vs mathlib**: the function-field base-change machinery (`tensorFunctionFieldEquiv`,
  `functionField_baseChange_fracEquiv`, localization-uniqueness glue) is project-specific
  scalar-extension API built directly on mathlib's `IsFractionRing`/`IsLocalization`/`Algebra.TensorProduct`
  — appropriate, no mathlib duplication.
- **(d) Moral duplication**: x/y mirror pairs throughout (`coordRingMap_X/Y_gen`, `functionFieldMap_x/y_gen`,
  `oneSubFrobeniusPullback_L_x/y_gen`) — inherent to coordinate work, not worth merging.
- **(e) Under-general statements**: well-generalized — stated over arbitrary `[Algebra.IsAlgebraic K L]`
  rather than `K̄` specifically, which is *why* it serves both leaves. Good. (Contrast with the consuming
  `WallAGeometricRealization`, which specializes to `AlgebraicClosure K`.)
- **Cleanup flags**:
  - `tensorFunctionFieldEquiv_one_tmul` (L91–149) is a **>30-line proof** — the hardest in the file; leave
    as-is but ensure the docstring stays accurate.
  - No `sorry`, no `maxHeartbeats` bump in this file.
