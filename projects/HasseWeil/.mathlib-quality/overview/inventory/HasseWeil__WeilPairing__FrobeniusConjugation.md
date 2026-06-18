# Inventory: ./HasseWeil/WeilPairing/FrobeniusConjugation.lean

**File purpose**: Proves `frobeniusFunctionFieldEquiv_conj`, the translation-covariance identity `σ(τ_S g) = τ_{π̄ S}(σ g)` for the arithmetic Frobenius `σ` of `K̄(E)`. This was the last geometric residual of leaf 1 (`frobeniusGaloisGeometric_holds`), completing `frobeniusScaling_holds` axiom-clean.

**Imports**: `HasseWeil.WeilPairing.FrobeniusGenericCovariance`, `HasseWeil.WeilPairing.FrobeniusFunctionFieldEquiv`

**Total declarations**: 18 (2 defs, 1 local instance, 15 theorems/lemmas)
**No sorries, no `set_option maxHeartbeats` overrides.**

---

## Section `RingHomExt` (general, field `F`)

### `theorem ringHom_ext_base_x_y_gen`
- **Type**: `(ψ₁ ψ₂ : KE →+* KE) → (∀ a : F, ψ₁ (algebraMap F KE a) = ψ₂ (algebraMap F KE a)) → ψ₁ (x_gen W) = ψ₂ (x_gen W) → ψ₁ (y_gen W) = ψ₂ (y_gen W) → ψ₁ = ψ₂`
- **What**: Ring-hom extensionality for endomorphisms of the function field `K(E)`: two ring homs that agree on the base constants `algebraMap F`, on `x_gen`, and on `y_gen` are equal.
- **How**: Three-layer reduction — `IsFractionRing.ringHom_ext` peels the fraction field, `AdjoinRoot.ringHom_ext` splits into the polynomial inclusion and the root, `Polynomial.ringHom_ext` splits into `C a` (base) and `X` (x_gen).
- **Hypotheses**: `W : WeierstrassCurve F`, `W.toAffine.IsElliptic`, `[DecidableEq F]`
- **Uses from project**: none (uses only mathlib's `IsFractionRing.ringHom_ext`, `AdjoinRoot.ringHom_ext`, `Polynomial.ringHom_ext`)
- **Used by**: `frobeniusFunctionFieldEquiv_conj`
- **Visibility**: public
- **Lines**: 82–122, proof length ~36 lines
- **Notes**: Proof >30 lines. Handles ring homs that are NOT `F`-linear (specifically the arithmetic Frobenius `σ`), unlike the existing `algHom_ext_x_y_gen`.

---

## Section `coordRingMap_X/root` (general, rings `R → S`)

### `theorem coordRingMap_X`
- **Type**: `(W' : WeierstrassCurve.Affine R) (f : R →+* S) → CoordinateRing.map W' f (algebraMap (Polynomial R) W'.CoordinateRing X) = algebraMap (Polynomial S) (W'.map f).toAffine.CoordinateRing X`
- **What**: `CoordinateRing.map f` fixes the `X`-generator (i.e., the image of `Polynomial.X` in the coordinate ring is the `X`-generator of the mapped coordinate ring).
- **How**: Unfolds `algebraMap _ _ X = mk (C X)`, applies `CoordinateRing.map_mk`, uses `Polynomial.map_C`/`map_X` to see `(C X).map (mapRingHom f) = C X`, then closes by `AdjoinRoot.of` unfolding.
- **Hypotheses**: `CommRing R`, `CommRing S`
- **Uses from project**: none
- **Used by**: `frobeniusFunctionFieldEquiv_x_gen`
- **Visibility**: public
- **Lines**: 132–150, proof length ~18 lines

### `theorem coordRingMap_root`
- **Type**: `(W' : WeierstrassCurve.Affine R) (f : R →+* S) → CoordinateRing.map W' f (AdjoinRoot.root W'.polynomial) = AdjoinRoot.root (W'.map f).toAffine.polynomial`
- **What**: `CoordinateRing.map f` fixes the root generator `AdjoinRoot.root poly`.
- **How**: Unfolds `CoordinateRing.map` as `AdjoinRoot.lift` and applies `AdjoinRoot.lift_root`.
- **Hypotheses**: `CommRing R`, `CommRing S`
- **Uses from project**: none
- **Used by**: `frobeniusFunctionFieldEquiv_y_gen`
- **Visibility**: public
- **Lines**: 155–160, proof length ~5 lines

---

## Section `BaseChange` (finite field `K`, `K̄ = AlgebraicClosure K`)

### `noncomputable local instance instDecEqACFC`
- **Type**: `DecidableEq (AlgebraicClosure K)`
- **What**: Provides classical decidable equality on `AlgebraicClosure K` for use throughout the section.
- **How**: `Classical.decEq _`
- **Hypotheses**: `[Field K]`
- **Uses from project**: none
- **Used by**: used implicitly throughout `BaseChange` section
- **Visibility**: local (scoped)
- **Lines**: 167

### `theorem frobeniusFunctionFieldEquiv_x_gen`
- **Type**: `frobeniusFunctionFieldEquiv W (x_gen (W.baseChange (AlgebraicClosure K))) = x_gen (W.baseChange (AlgebraicClosure K))`
- **What**: The arithmetic Frobenius `σ` fixes the `𝔽_q`-rational generator `x_gen`.
- **How**: Rewrites `frobeniusFunctionFieldEquiv` as `ffFrobEquivRaw.trans ffFrobCast`, applies `IsFractionRing.ringEquivOfRingEquiv_algebraMap` and `crFrobEquiv_apply`, then uses `coordRingMap_X`, and closes the codomain cast via `RingEquiv.cast` with `subst h; rfl`.
- **Hypotheses**: `[Fintype K]`, `[DecidableEq K]`, `W.toAffine.IsElliptic`, base-changed IsElliptic
- **Uses from project**: `coordRingMap_X`, `ffFrobEquivRaw`, `crFrobEquiv_apply`, `ffFrobCast`, `map_coeffFrobEquiv_eq` (from `FrobeniusFunctionFieldEquiv`)
- **Used by**: `sigmaConjugation_fix_genericPoint`
- **Visibility**: public
- **Lines**: 179–202, proof length ~23 lines

### `theorem frobeniusFunctionFieldEquiv_y_gen`
- **Type**: `frobeniusFunctionFieldEquiv W (y_gen (W.baseChange (AlgebraicClosure K))) = y_gen (W.baseChange (AlgebraicClosure K))`
- **What**: The arithmetic Frobenius `σ` fixes the `𝔽_q`-rational generator `y_gen`.
- **How**: Same structure as `frobeniusFunctionFieldEquiv_x_gen` but uses `coordRingMap_root` (instead of `coordRingMap_X`) and `AdjoinRoot.root`.
- **Hypotheses**: Same as `frobeniusFunctionFieldEquiv_x_gen`
- **Uses from project**: `coordRingMap_root`, `ffFrobEquivRaw`, `crFrobEquiv_apply`, `ffFrobCast`, `map_coeffFrobEquiv_eq`
- **Used by**: `sigmaConjugation_fix_genericPoint`
- **Visibility**: public
- **Lines**: 207–226, proof length ~19 lines

### `theorem frobeniusFunctionFieldEquiv_baseField`
- **Type**: `(a : K) → frobeniusFunctionFieldEquiv W (algebraMap K (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) = algebraMap K ... a`
- **What**: The arithmetic Frobenius `σ` fixes every element of the base field `K = 𝔽_q`.
- **How**: Uses the scalar tower `K → K̄ → K̄(E)`, applies `frobeniusFunctionFieldEquiv_algebraMap` (which `q`-powers the `K̄`-constant), then `FiniteField.pow_card` to conclude `a^q = a` in `K`.
- **Hypotheses**: Same finite-field setup
- **Uses from project**: `frobeniusFunctionFieldEquiv_algebraMap` (from `FrobeniusFunctionFieldEquiv`)
- **Used by**: `frobeniusFunctionFieldEquivK` (its `commutes'` field)
- **Visibility**: public
- **Lines**: 236–244, proof length ~8 lines

### `noncomputable def frobeniusFunctionFieldEquivK`
- **Type**: `(W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[K] (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField`
- **What**: The arithmetic Frobenius `σ` viewed as a `K`-algebra hom (not just a ring hom). This enables `Affine.Point.map (W' := W)` which consumes a `K`-AlgHom typed over the base curve.
- **How**: Packages `frobeniusFunctionFieldEquiv W` (a ring equiv) with `commutes'` from `frobeniusFunctionFieldEquiv_baseField`.
- **Hypotheses**: Same finite-field setup
- **Uses from project**: `frobeniusFunctionFieldEquiv`, `frobeniusFunctionFieldEquiv_baseField`
- **Used by**: `frobeniusFunctionFieldEquivK_apply`, `sigmaFunctionFieldPointKbar`, `sigmaConjugation_lift_twist`, `sigmaConjugation_fix_genericPoint`, `sigmaConjugation_point`, `sigmaConjugation_x_y_gen`
- **Visibility**: public
- **Lines**: 250–254

### `@[simp] theorem frobeniusFunctionFieldEquivK_apply`
- **Type**: `(z : KE̅) → frobeniusFunctionFieldEquivK W z = frobeniusFunctionFieldEquiv W z`
- **What**: Reduction lemma: `σ_K` applied to `z` equals `σ` applied to `z`.
- **How**: `rfl`
- **Hypotheses**: Same
- **Uses from project**: `frobeniusFunctionFieldEquivK`, `frobeniusFunctionFieldEquiv`
- **Used by**: `sigmaConjugation_lift_twist`, `sigmaConjugation_x_y_gen`
- **Visibility**: public (simp lemma)
- **Lines**: 256–258

### `theorem map_genericPoint_some`
- **Type**: For any `K`-AlgHom `h : KE̅ →ₐ[K] KE̅`, there exists `hns` such that `Point.map (W' := W) h (genericPoint ...) = some (h x_gen) (h y_gen) hns`
- **What**: Peeling lemma: `Point.map h` applied to the generic point `P_gen = (x_gen, y_gen)` returns an explicit affine point `some (h x_gen) (h y_gen)`.
- **How**: Rewrites via `genericPoint_xOf_some`, then applies `Affine.Point.map_some (W' := W)` via an existential. Uses `show` to bridge the scalar-tower diamond without forcing kernel whnf of the heavy Frobenius.
- **Hypotheses**: Same
- **Uses from project**: `HasseWeil.genericPoint`, `HasseWeil.genericPoint_xOf_some`, `HasseWeil.generic_nonsingular`
- **Used by**: `sigmaConjugation_x_y_gen`
- **Visibility**: public
- **Lines**: 266–275, proof length ~9 lines

### `noncomputable def sigmaFunctionFieldPointKbar`
- **Type**: `(W_KE (W.baseChange K̄)).toAffine.Point →+ (W_KE (W.baseChange K̄)).toAffine.Point`
- **What**: The point-level action of the arithmetic Frobenius `σ` on function-field points of `E_{K̄}`, defined as `Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W)`.
- **How**: Direct definition wrapping `Affine.Point.map`.
- **Hypotheses**: Same
- **Uses from project**: `W_KE`, `frobeniusFunctionFieldEquivK`
- **Used by**: `sigmaFunctionFieldPointKbar_apply`, `sigmaConjugation_lift_twist`, `sigmaConjugation_fix_genericPoint`, `sigmaConjugation_point`
- **Visibility**: public
- **Lines**: 282–285

### `theorem sigmaFunctionFieldPointKbar_apply`
- **Type**: `(P : ...) → sigmaFunctionFieldPointKbar W P = Point.map (W' := W) (frobeniusFunctionFieldEquivK W) P`
- **What**: Reduction lemma: unfolds `sigmaFunctionFieldPointKbar` to its defining `Point.map`.
- **How**: `rfl`
- **Hypotheses**: Same
- **Uses from project**: `sigmaFunctionFieldPointKbar`, `frobeniusFunctionFieldEquivK`
- **Used by**: `sigmaConjugation_point`
- **Visibility**: public
- **Lines**: 287–290

### `theorem sigmaConjugation_tau_mapW`
- **Type**: `Point.map (W' := W.baseChange K̄) (translateAlgEquivOfPoint ... S).toAlgHom P = Point.map (W' := W) ((translateAlgEquivOfPoint ... S).toAlgHom.restrictScalars K) P`
- **What**: Cross-`W'` bridge for the translation `τ_S`: the `K̄`-linear translation applied via `Point.map (W' := W.baseChange K̄)` equals the `K`-restriction applied via `Point.map (W' := W)`. Sidesteps the scalar-tower diamond.
- **How**: `cases P <;> rfl` — both sides act through the same underlying ring hom on coordinates.
- **Hypotheses**: `S : (W.baseChange K̄).toAffine.Point`, `P : (W_KE (W.baseChange K̄)).toAffine.Point`
- **Uses from project**: `HasseWeil.translateAlgEquivOfPoint`
- **Used by**: `sigmaConjugation_point`
- **Visibility**: public
- **Lines**: 297–303, proof ~1 line

### `theorem sigmaConjugation_lift_twist`
- **Type**: `sigmaFunctionFieldPointKbar W (liftPointToKE (W.baseChange K̄) S) = liftPointToKE (W.baseChange K̄) (geomFrobeniusPointFun W S)`
- **What**: Point-level action of `σ`: `Point.map σ_K` sends the lift of a `K̄`-point `S` to the lift of its geometric Frobenius `π̄ S = (S_x^q, S_y^q)`.
- **How**: Case splits on `S`: for zero, `map_zero`; for affine `some sx sy`, uses `geomFrobeniusPointFun_some` + `liftPointToKE_some` + `liftSomePoint`, applies `map_some (W' := W)`, then `frobeniusFunctionFieldEquiv_algebraMap` to establish that `σ(algebraMap sx) = algebraMap (sx^q)`.
- **Hypotheses**: `S : (W.baseChange K̄).toAffine.Point`
- **Uses from project**: `sigmaFunctionFieldPointKbar`, `HasseWeil.liftPointToKE`, `HasseWeil.liftPointToKE_some`, `HasseWeil.liftSomePoint`, `geomFrobeniusPointFun`, `geomFrobeniusPointFun_zero`, `geomFrobeniusPointFun_some`, `frobeniusFunctionFieldEquivK_apply`, `frobeniusFunctionFieldEquiv_algebraMap`
- **Used by**: `sigmaConjugation_point`
- **Visibility**: public
- **Lines**: 314–331, proof length ~17 lines

### `theorem sigmaConjugation_fix_genericPoint`
- **Type**: `sigmaFunctionFieldPointKbar W (genericPoint (W.baseChange K̄)) = genericPoint (W.baseChange K̄)`
- **What**: The point-level `σ` fixes the generic point `P_gen = (x_gen, y_gen)`.
- **How**: Rewrites via `genericPoint_xOf_some` to expose `some x_gen y_gen`, applies `map_some (W' := W)`, then uses `frobeniusFunctionFieldEquiv_x_gen` and `frobeniusFunctionFieldEquiv_y_gen`.
- **Hypotheses**: Same
- **Uses from project**: `sigmaFunctionFieldPointKbar`, `HasseWeil.genericPoint`, `HasseWeil.genericPoint_xOf_some`, `frobeniusFunctionFieldEquivK`, `frobeniusFunctionFieldEquiv_x_gen`, `frobeniusFunctionFieldEquiv_y_gen`
- **Used by**: `sigmaConjugation_point`
- **Visibility**: public
- **Lines**: 336–345, proof length ~9 lines

### `theorem sigmaConjugation_point`
- **Type**: `Point.map (W':=W) σ_K (Point.map (W':=W) (τ_S.restrictScalars K) P_gen) = Point.map (W':=W) ((τ_{π̄ S}).restrictScalars K) (Point.map (W':=W) σ_K P_gen)`
- **What**: The translation conjugation at the generic point: `σ ∘ τ_S` and `τ_{π̄ S} ∘ σ` agree at `P_gen`. Both sides equal `P_gen + lift(π̄ S)`.
- **How**: Rewrites both `Point.map σ_K` occurrences as `sigmaFunctionFieldPointKbar` (via `_apply`). RHS: `sigmaConjugation_fix_genericPoint` (fixes P_gen) then `translateAlgEquivOfPoint_map_genericPoint` at `π̄ S`. LHS: `translateAlgEquivOfPoint_map_genericPoint` at `S`, then `map_add`, then `sigmaConjugation_fix_genericPoint` and `sigmaConjugation_lift_twist`.
- **Hypotheses**: `S : (W.baseChange K̄).toAffine.Point`
- **Uses from project**: `sigmaFunctionFieldPointKbar_apply`, `sigmaConjugation_fix_genericPoint`, `sigmaConjugation_tau_mapW`, `sigmaConjugation_lift_twist`, `HasseWeil.translateAlgEquivOfPoint_map_genericPoint`, `geomFrobeniusPointFun`
- **Used by**: `sigmaConjugation_x_y_gen`
- **Visibility**: public
- **Lines**: 358–378, proof length ~19 lines

### `theorem sigmaConjugation_x_y_gen`
- **Type**: `(S : (W.baseChange K̄).toAffine.Point) → σ(τ_S x_gen) = τ_{π̄ S}(σ x_gen) ∧ σ(τ_S y_gen) = τ_{π̄ S}(σ y_gen)`
- **What**: The translation conjugation on generators: reads off the x- and y-coordinate equalities from the generic-point conjugation lemma.
- **How**: Calls `sigmaConjugation_point`, then uses `map_genericPoint_some` twice to peel inner `Point.map`s, applies `map_some` twice and `some.injEq` to extract coordinate equalities, closes `restrictScalars`/`σ_K` coercions with `simp` + `frobeniusFunctionFieldEquivK_apply`.
- **Hypotheses**: `S : (W.baseChange K̄).toAffine.Point`
- **Uses from project**: `sigmaConjugation_point`, `map_genericPoint_some`, `frobeniusFunctionFieldEquivK`, `frobeniusFunctionFieldEquivK_apply`, `geomFrobeniusPointFun`
- **Used by**: `frobeniusFunctionFieldEquiv_conj`
- **Visibility**: public
- **Lines**: 384–416, proof length ~32 lines
- **Notes**: Proof >30 lines.

### `theorem frob_comp_tau_apply`
- **Type**: `((σ.toRingHom.comp τ_S.toRingEquiv.toRingHom) g = σ (τ_S g))`
- **What**: Comp-unfold helper: `σ ∘ τ_S` evaluated at `g` equals `σ(τ_S g)`. Avoids simp-unfolding the coercion tower of the heavy `frobeniusFunctionFieldEquiv`.
- **How**: `RingHom.comp_apply _ _ g` — bare term proof.
- **Hypotheses**: `S : (W.baseChange K̄).toAffine.Point`, `g : K̄(E)`
- **Uses from project**: `frobeniusFunctionFieldEquiv`, `HasseWeil.translateAlgEquivOfPoint`
- **Used by**: `frobeniusFunctionFieldEquiv_conj`
- **Visibility**: public
- **Lines**: 425–432, proof 1 line

### `theorem tau_comp_frob_apply`
- **Type**: `((τ_{π̄ S}.toRingEquiv.toRingHom.comp σ.toRingHom) g = τ_{π̄ S}(σ g))`
- **What**: Comp-unfold helper: `τ_{π̄ S} ∘ σ` evaluated at `g` equals `τ_{π̄ S}(σ g)`. Companion to `frob_comp_tau_apply`.
- **How**: `RingHom.comp_apply _ _ g` — bare term proof.
- **Hypotheses**: Same as `frob_comp_tau_apply`
- **Uses from project**: `frobeniusFunctionFieldEquiv`, `HasseWeil.translateAlgEquivOfPoint`, `geomFrobeniusPointFun`
- **Used by**: `frobeniusFunctionFieldEquiv_conj`
- **Visibility**: public
- **Lines**: 436–444, proof 1 line

### `theorem frobeniusFunctionFieldEquiv_conj`
- **Type**: `(S : (W.baseChange K̄).toAffine.Point) (g : K̄(E)) → σ(τ_S g) = τ_{π̄ S}(σ g)`
- **What**: **Main theorem**: the arithmetic Frobenius `σ` commutes with translation by `S` up to the geometric Frobenius twist: `σ ∘ τ_S = τ_{π̄ S} ∘ σ` pointwise. This is Silverman III.8.1d, the last geometric residual of leaf 1.
- **How**: Proves equality of the two ring homs `σ ∘ τ_S` and `τ_{π̄ S} ∘ σ` via `ringHom_ext_base_x_y_gen`: base agreement via `frobeniusFunctionFieldEquiv_algebraMap` (both sides q-power K̄-constants), generator agreement via `sigmaConjugation_x_y_gen`. The comp-unfold helpers `frob_comp_tau_apply` and `tau_comp_frob_apply` bridge back to pointwise form at `g` via `RingHom.congr_fun`.
- **Hypotheses**: `[Fintype K]`, `[DecidableEq K]`, `W.toAffine.IsElliptic`, base-changed IsElliptic
- **Uses from project**: `sigmaConjugation_x_y_gen`, `ringHom_ext_base_x_y_gen`, `frob_comp_tau_apply`, `tau_comp_frob_apply`, `frobeniusFunctionFieldEquiv_algebraMap`, `HasseWeil.translateAlgEquivOfPoint`, `geomFrobeniusPointFun`
- **Used by**: `FrobeniusGaloisScaling.lean` (external — discharged the `hcomm` field in `frobeniusGaloisGeometric_holds`)
- **Visibility**: public
- **Lines**: 455–483, proof length ~28 lines

---

## Summary table

| Declaration | Kind | Lines | Sorry | Long |
|---|---|---|---|---|
| `ringHom_ext_base_x_y_gen` | theorem | 82–122 | no | yes (36) |
| `coordRingMap_X` | theorem | 132–150 | no | no |
| `coordRingMap_root` | theorem | 155–160 | no | no |
| `instDecEqACFC` | local instance | 167 | no | no |
| `frobeniusFunctionFieldEquiv_x_gen` | theorem | 179–202 | no | no |
| `frobeniusFunctionFieldEquiv_y_gen` | theorem | 207–226 | no | no |
| `frobeniusFunctionFieldEquiv_baseField` | theorem | 236–244 | no | no |
| `frobeniusFunctionFieldEquivK` | def | 250–254 | no | no |
| `frobeniusFunctionFieldEquivK_apply` | theorem | 256–258 | no | no |
| `map_genericPoint_some` | theorem | 266–275 | no | no |
| `sigmaFunctionFieldPointKbar` | def | 282–285 | no | no |
| `sigmaFunctionFieldPointKbar_apply` | theorem | 287–290 | no | no |
| `sigmaConjugation_tau_mapW` | theorem | 297–303 | no | no |
| `sigmaConjugation_lift_twist` | theorem | 314–331 | no | no |
| `sigmaConjugation_fix_genericPoint` | theorem | 336–345 | no | no |
| `sigmaConjugation_point` | theorem | 358–378 | no | no |
| `sigmaConjugation_x_y_gen` | theorem | 384–416 | no | yes (32) |
| `frob_comp_tau_apply` | theorem | 425–432 | no | no |
| `tau_comp_frob_apply` | theorem | 436–444 | no | no |
| `frobeniusFunctionFieldEquiv_conj` | theorem | 455–483 | no | no |

**Key API** (used by 3+ declarations in this file): `frobeniusFunctionFieldEquivK` (used by `frobeniusFunctionFieldEquivK_apply`, `sigmaFunctionFieldPointKbar`, `sigmaConjugation_lift_twist`, `sigmaConjugation_fix_genericPoint`, `sigmaConjugation_point`, `sigmaConjugation_x_y_gen` — 6 users), `sigmaFunctionFieldPointKbar` (used by `sigmaFunctionFieldPointKbar_apply`, `sigmaConjugation_lift_twist`, `sigmaConjugation_fix_genericPoint`, `sigmaConjugation_point` — 4 users), `frobeniusFunctionFieldEquiv_x_gen`/`_y_gen` each used by 2 (just under threshold but key).

**Declarations not referenced by anything else in THIS file** (dead-code candidates from file perspective): `coordRingMap_X`, `coordRingMap_root`, `frobeniusFunctionFieldEquiv_baseField`, `map_genericPoint_some`, `sigmaConjugation_tau_mapW`, `sigmaConjugation_lift_twist`, `sigmaConjugation_fix_genericPoint`, `sigmaConjugation_x_y_gen`, `frob_comp_tau_apply`, `tau_comp_frob_apply`. (All are used internally as intermediate steps; `coordRingMap_X/root` are general lemmas potentially usable elsewhere; `frobeniusFunctionFieldEquiv_conj` is the leaf consumed by `FrobeniusGaloisScaling.lean`.)
