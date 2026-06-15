# Inventory: ./HasseWeil/WeilPairing/OmegaBaseChange.lean

**File summary**: 233 lines. Proves that the invariant-differential pullback coefficient (Silverman III.5) is stable under field base change, via a base-change map on Kähler differentials. This is the differential analogue of the finrank base-change identity. No `sorry`, no `maxHeartbeats` overrides (only `synthInstance.maxHeartbeats`).

**Imports**: `HasseWeil.InvariantDifferentialPullback`, `HasseWeil.WeilPairing.WallAGenericRealization`, `HasseWeil.WeilPairing.IsogenyBaseChangeConcrete`

---

### `noncomputable scoped instance algFunctionFieldBaseChange`
- **Type**: `Algebra W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField`
- **What**: Installs the `K(E)`-algebra structure on `K(E_L)` via the function-field base-change `K`-algebra hom `functionField_baseChange`, making `algebraMap K(E) K(E_L) = functionFieldMap` definitionally.
- **How**: Directly applies `.toAlgebra` to the ring hom `SmoothPlaneCurve.functionField_baseChange`.
- **Hypotheses**: `W` smooth elliptic over `K`; `L/K` algebraic field extension; `W.baseChange L` elliptic.
- **Uses from project**: `SmoothPlaneCurve.functionField_baseChange` (from `CurveMapBaseChange`)
- **Used by**: `algebraMap_functionField_baseChange_eq`, `towerFunctionFieldBaseChange`, `smulCommFunctionFieldBaseChange`, `omegaDiffMap`, and indirectly all subsequent lemmas via instance search.
- **Visibility**: scoped (in `HasseWeil.WeilPairing`)
- **Lines**: 69–71, proof length ~1 line
- **Notes**: `set_option synthInstance.maxHeartbeats 1000000` does NOT appear on this instance (only on later ones).

---

### `theorem algebraMap_functionField_baseChange_eq`
- **Type**: `∀ z : W.toAffine.FunctionField, algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField z = (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L z`
- **What**: States that the `algebraMap K(E) → K(E_L)` installed by `algFunctionFieldBaseChange` equals `functionFieldMap` (definitionally `rfl`).
- **How**: `rfl` — the algebra map is defined directly as `functionFieldMap`.
- **Hypotheses**: same as `algFunctionFieldBaseChange`.
- **Uses from project**: (none beyond instances already in context)
- **Used by**: `towerFunctionFieldBaseChange` (L85), `omegaDiffMap_pullbackKaehler` (L147, 161), `omegaDiffMap_invariantDifferential` (L202), `omegaPullbackCoeff_baseChangePullback` (L230).
- **Visibility**: public
- **Lines**: 74–76, proof length 1 line
- **Notes**: This is a key rewriting lemma; used by 4 declarations in this file (keyApi).

---

### `noncomputable scoped instance towerFunctionFieldBaseChange`
- **Type**: `IsScalarTower K W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField`
- **What**: Installs the scalar tower `K → K(E) → K(E_L)`, showing the `K`-algebra structure on `K(E_L)` factors through `K(E)` via `functionFieldMap`.
- **How**: `IsScalarTower.of_algebraMap_eq` + `SmoothPlaneCurve.functionFieldMap_algebraMap_F` (which says `functionFieldMap(algebraMap K _ k) = algebraMap K _ k`) + `rfl`.
- **Hypotheses**: same as `algFunctionFieldBaseChange`.
- **Uses from project**: `SmoothPlaneCurve.functionFieldMap_algebraMap_F` (from `CurveMapBaseChange`); `algebraMap_functionField_baseChange_eq` (implicit via change).
- **Used by**: Indirectly used by instance-search in subsequent lemmas (needed for `KaehlerDifferential.map` to compile).
- **Visibility**: scoped
- **Lines**: 80–86, proof length ~5 lines
- **Notes**: None.

---

### `noncomputable scoped instance smulCommFunctionFieldBaseChange`
- **Type**: `SMulCommClass L W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField`
- **What**: Both `L` and `K(E)` act by multiplication on `K(E_L)` and these actions commute (both sides act by multiplication in the commutative ring `K(E_L)`).
- **How**: Unfolds all four `Algebra.smul_def` applications and closes by `ring`.
- **Hypotheses**: same as `algFunctionFieldBaseChange`.
- **Uses from project**: (none beyond instances in context)
- **Used by**: Instance search for `KaehlerDifferential.map` typecheck (needed for `omegaDiffMap`).
- **Visibility**: scoped
- **Lines**: 88–94, proof length ~4 lines
- **Notes**: `set_option synthInstance.maxHeartbeats 1000000 in` (line 88); no justifying comment present (NO-COMMENT).

---

### `noncomputable def omegaDiffMap`
- **Type**: `Ω[W.toAffine.FunctionField⁄K] →ₗ[W.toAffine.FunctionField] Ω[(W.baseChange L).toAffine.FunctionField⁄L]`
- **What**: The base-change map on Kähler differentials `Ω[K(E)/K] →ₗ Ω[K(E_L)/L]` for the commutative square `K → K(E)`, `L → K(E_L)` with `algebraMap K(E) K(E_L) = functionFieldMap`. Defined as `KaehlerDifferential.map K L K(E) K(E_L)`.
- **How**: Definitional alias for mathlib's `KaehlerDifferential.map`.
- **Hypotheses**: Requires `algFunctionFieldBaseChange`, `towerFunctionFieldBaseChange`, `smulCommFunctionFieldBaseChange` instances in scope.
- **Uses from project**: (none; pure mathlib)
- **Used by**: `omegaDiffMap_D`, `omegaDiffMap_smul`, `omegaDiffMap_pullbackKaehler`, `omegaDiffMap_invariantDifferential`, `omegaPullbackCoeff_baseChangePullback`.
- **Visibility**: public
- **Lines**: 100–103, no proof (def)
- **Notes**: Core definition; used by 5 subsequent declarations (keyApi).

---

### `theorem omegaDiffMap_D`
- **Type**: `∀ z, omegaDiffMap W L (D_K z) = D_L (algebraMap K(E) K(E_L) z)`
- **What**: The differential map sends `D_K(z)` to `D_L(functionFieldMap z)` — the generator compatibility of `KaehlerDifferential.map`.
- **How**: Direct application of `KaehlerDifferential.map_D`.
- **Hypotheses**: Same as `omegaDiffMap`.
- **Uses from project**: (none; pure mathlib)
- **Used by**: `omegaDiffMap_pullbackKaehler` (L145), `omegaDiffMap_invariantDifferential` (L191).
- **Visibility**: public
- **Lines**: 106–110, proof length 1 line
- **Notes**: None.

---

### `theorem omegaDiffMap_smul`
- **Type**: `∀ s ω, omegaDiffMap W L (s • ω) = s • omegaDiffMap W L ω`
- **What**: K(E)-linearity of `omegaDiffMap` (the K(E)-action on `Ω[K(E_L)/L]` factors through `functionFieldMap`).
- **How**: `LinearMap.map_smul` applied to the linear map `omegaDiffMap W L`.
- **Hypotheses**: Same as `omegaDiffMap`.
- **Uses from project**: (none; pure mathlib)
- **Used by**: `omegaDiffMap_pullbackKaehler` (L152, smul case), `omegaDiffMap_invariantDifferential` (L191), `omegaPullbackCoeff_baseChangePullback` (L229).
- **Visibility**: public
- **Lines**: 114–116, proof length 1 line
- **Notes**: Used by 3 declarations (keyApi).

---

### `theorem functionFieldMap_pullback`
- **Type**: `∀ α α_L hpb z, functionFieldMap (α.pullback z) = α_L.pullback (functionFieldMap z)` (where `hpb : α_L.pullback = baseChangePullback ... α.pullback`)
- **What**: `functionFieldMap` intertwines `α.pullback` with `α_L.pullback` for a base-changed isogeny — the function-field shadow of the identity `α_L = α` over `L`.
- **How**: Rewrites via `hpb` and applies `baseChangePullback_functionFieldMap` (from `WallAGenericRealization`) symmetrically.
- **Hypotheses**: `hpb : α_L.pullback = baseChangePullback ... α.pullback`.
- **Uses from project**: `baseChangePullback_functionFieldMap` (from `WallAGenericRealization`)
- **Used by**: `omegaDiffMap_pullbackKaehler` (L148, 162).
- **Visibility**: public
- **Lines**: 120–128, proof length ~8 lines
- **Notes**: None.

---

### `theorem omegaDiffMap_pullbackKaehler`
- **Type**: `∀ α α_L hpb ω, omegaDiffMap W L (α.pullbackKaehler ω) = α_L.pullbackKaehler (omegaDiffMap W L ω)`
- **What**: Pullback compatibility: `omegaDiffMap` commutes with the Kähler pullback maps `α.pullbackKaehler` and `α_L.pullbackKaehler`. This is the differential version of `baseChangePullback_functionFieldMap`.
- **How**: Span induction on `ω` over `Set.range (D K K(E))` using `KaehlerDifferential.span_range_derivation` (which says `Ω[K(E)/K]` is spanned by derivations). Generator case uses `functionFieldMap_pullback`; scalar case uses algebraicity of `algebraMap_functionField_baseChange_eq` to convert the scalar-tower smul.
- **Hypotheses**: `hpb : α_L.pullback = baseChangePullback ... α.pullback`.
- **Uses from project**: `omegaDiffMap_D`, `omegaDiffMap_smul`, `functionFieldMap_pullback`, `algebraMap_functionField_baseChange_eq`; `Isogeny.pullbackKaehler_D`, `Isogeny.pullbackKaehler_smul_KE` (from `InvariantDifferentialPullback`)
- **Used by**: `omegaPullbackCoeff_baseChangePullback` (L227).
- **Visibility**: public
- **Lines**: 133–162, proof length ~24 lines
- **Notes**: None.

---

### `theorem functionFieldMap_u_gen`
- **Type**: `functionFieldMap (u_gen W) = u_gen (W.baseChange L)`
- **What**: The invariant-differential denominator `u = 2y + a₁x + a₃` is preserved by `functionFieldMap` — it base-changes correctly because `x_gen`, `y_gen`, `a₁`, `a₃` all base-change.
- **How**: Unfolds `u_gen` definitionally as `2 * y_gen + a₁ * x_gen + a₃`, rewrites using `functionFieldMap_x_gen`, `functionFieldMap_y_gen` (from `WallAGenericRealization`) and `SmoothPlaneCurve.functionFieldMap_algebraMap_F` for constants.
- **Hypotheses**: Standard assumptions.
- **Uses from project**: `functionFieldMap_x_gen`, `functionFieldMap_y_gen`, `SmoothPlaneCurve.functionFieldMap_algebraMap_F` (all from `WallAGenericRealization`); `u_gen` (from `OmegaPullbackCoeff`); `x_gen`, `y_gen` (from `MulByIntPullback`)
- **Used by**: `omegaDiffMap_invariantDifferential` (L203).
- **Visibility**: public
- **Lines**: 164–180, proof length ~13 lines
- **Notes**: `set_option synthInstance.maxHeartbeats 1000000 in` (line 164); no justifying comment (NO-COMMENT).

---

### `theorem omegaDiffMap_invariantDifferential`
- **Type**: `omegaDiffMap W L (invariantDifferential W.toAffine) = invariantDifferential (W.baseChange L).toAffine`
- **What**: The invariant differential `ω = u⁻¹ • D(x_gen)` is preserved by `omegaDiffMap`, i.e. `ω_K` maps to `ω_L`.
- **How**: Unfolds both invariant differentials as `u⁻¹ • D(x_gen)`, applies `omegaDiffMap_smul` and `omegaDiffMap_D`, then uses `algebraMap_functionField_baseChange_eq`, `map_inv₀`, `functionFieldMap_u_gen`, and `functionFieldMap_x_gen` to match the two sides.
- **Hypotheses**: Standard assumptions.
- **Uses from project**: `omegaDiffMap_smul`, `omegaDiffMap_D`, `algebraMap_functionField_baseChange_eq`, `functionFieldMap_u_gen`, `functionFieldMap_x_gen` (from `WallAGenericRealization`); `invariantDifferential` (from `InvariantDifferential`)
- **Used by**: `omegaPullbackCoeff_baseChangePullback` (L226, 229).
- **Visibility**: public
- **Lines**: 182–207, proof length ~19 lines
- **Notes**: `set_option synthInstance.maxHeartbeats 1000000 in` (line 182); no justifying comment (NO-COMMENT).

---

### `theorem omegaPullbackCoeff_baseChangePullback`
- **Type**: `∀ α α_L hpb, omegaPullbackCoeff (W.baseChange L) α_L = functionFieldMap (omegaPullbackCoeff W α)` (where `hpb : α_L.pullback = baseChangePullback ... α.pullback`)
- **What**: The main result: the omega-pullback coefficient of the base-changed isogeny `α_L` equals the image of the omega-pullback coefficient of `α` under `functionFieldMap`. This is the differential analogue of the degree base-change identity (Silverman III.5).
- **How**: Applies `omegaPullbackCoeff_unique` (uniqueness of the scaling factor from `OmegaPullbackCoeff`) and then rewrites via the chain `a_{α_L} • ω_L = α_L^*(ω_L) = α_L^*(omegaDiffMap ω_K) = omegaDiffMap(α^* ω_K) = omegaDiffMap(a_α • ω_K) = functionFieldMap(a_α) • ω_L`, using `omegaDiffMap_invariantDifferential`, `omegaDiffMap_pullbackKaehler`, `Isogeny.pullbackKaehler_invariantDifferential`, `omegaDiffMap_smul`, and `algebraMap_smul`.
- **Hypotheses**: `hpb : α_L.pullback = baseChangePullback ... α.pullback`.
- **Uses from project**: `omegaPullbackCoeff_unique` (from `OmegaPullbackCoeff`); `omegaDiffMap_invariantDifferential`, `omegaDiffMap_pullbackKaehler`, `omegaDiffMap_smul`, `algebraMap_functionField_baseChange_eq`; `Isogeny.pullbackKaehler_invariantDifferential` (from `InvariantDifferentialPullback`)
- **Used by**: unused in this file; used externally in `PencilSeparable.lean` (`omegaBaseChangeNeZero_holds`), `OneSubComapConcrete.lean`, `PencilComapWitnesses.lean`.
- **Visibility**: public
- **Lines**: 218–230, proof length ~7 lines
- **Notes**: The capstone theorem of the file. External callers discharge the `OmegaBaseChangeNeZero` hypothesis used throughout the Weil-pairing proof.

---

## Key API (used by 3+ declarations in this file)

- `omegaDiffMap` — used by 5 declarations (`omegaDiffMap_D`, `omegaDiffMap_smul`, `omegaDiffMap_pullbackKaehler`, `omegaDiffMap_invariantDifferential`, `omegaPullbackCoeff_baseChangePullback`)
- `algebraMap_functionField_baseChange_eq` — used by 4 declarations
- `omegaDiffMap_smul` — used by 3 declarations

## Unused in file (dead-code candidates — may be used by other files)

All declarations are part of a logical chain leading to `omegaPullbackCoeff_baseChangePullback`. The three infrastructure instances (`algFunctionFieldBaseChange`, `towerFunctionFieldBaseChange`, `smulCommFunctionFieldBaseChange`) and the helper theorems `omegaDiffMap_D`, `omegaDiffMap_smul` are only used internally. The final theorem `omegaPullbackCoeff_baseChangePullback` is the external API.

Within the file, `functionFieldMap_pullback` is only used by `omegaDiffMap_pullbackKaehler`. The instances are consumed silently by elaboration.

No declarations in this file appear to be unused — each feeds the next in the chain.
