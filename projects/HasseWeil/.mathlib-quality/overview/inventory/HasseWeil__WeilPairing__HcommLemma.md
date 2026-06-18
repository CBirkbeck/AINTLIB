# Inventory: ./HasseWeil/WeilPairing/HcommLemma.lean

**File**: `HasseWeil/WeilPairing/HcommLemma.lean`
**Lines**: 172
**Namespace**: `HasseWeil.WeilPairing`
**Imports**: `HasseWeil.WeilPairing.TorsionGeometric`, `HasseWeil.GapSpines`

---

## Summary

A focused 4-theorem file proving the translation–isogeny commutation `τ_S ∘ φ* = φ* ∘ τ_{φS}` in
three forms (point, alg-hom, pointwise), under the hypotheses `IsGenuineWith` (for the generic-point
action) and `hgcomm` (the geometric point-level commutation). This is the `hcomm` witness consumed
by `weilPairing_adjoint_picDual`/`weilPairing_scaling` in `PairingAdjoint.lean`. No sorries, no
`set_option maxHeartbeats`.

---

### `theorem map_pullback_genericPoint_of_isGenuineWith`

- **Type**:
  ```
  (φ : Isogeny W.toAffine W.toAffine)
  {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
  (hgen : IsGenuineWith W φ g) :
  WeierstrassCurve.Affine.Point.map φ.pullback (HasseWeil.genericPoint W) =
    g (HasseWeil.genericPoint W)
  ```
- **What**: At the generic point, the function-field-level map `Point.map φ*` agrees with the
  geometric action `g`. In other words, `φ* (P_gen) = g(P_gen)`.
- **How**: Destructs `IsGenuineWith` to extract coordinates, rewrites with
  `HasseWeil.genericPoint_xOf_some` to expose the `some` shape, then applies
  `Affine.Point.map_some` (which computes `Point.map f (some x y _) = some (f x) (f y) _`) and
  uses `Affine.Point.some.injEq` with `hX.symm`/`hY.symm` to match coordinates.
- **Hypotheses**: `IsGenuineWith W φ g` — the isogeny `φ` has geometric action `g`, meaning
  `g(P_gen) = some (φ* x_gen) (φ* y_gen)`.
- **Uses from project**: `HasseWeil.IsGenuineWith` (GapSpines), `HasseWeil.genericPoint`,
  `HasseWeil.genericPoint_xOf_some` (GenericPoint), `HasseWeil.generic_nonsingular` (GenericPoint)
- **Used by**: `hcomm_point_of_isGenuineWith` (lines 104, 123), `hcomm_algHom_of_isGenuineWith`
  (mentioned in docstring only, via `hcomm_point_of_isGenuineWith`)
- **Visibility**: public
- **Lines**: 64–74, proof 69–74 (~6 lines)
- **Notes**: Short clean proof; no special options.

---

### `theorem hcomm_point_of_isGenuineWith`

- **Type**:
  ```
  (φ : Isogeny W.toAffine W.toAffine)
  {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
  (hgen : IsGenuineWith W φ g) (S : W.toAffine.Point)
  (hgcomm : Point.map (τ_S).toAlgHom (g P_gen) = g P_gen + liftPointToKE W (φ.toAddMonoidHom S)) :
  Point.map (τ_S).toAlgHom (Point.map φ* P_gen) =
    Point.map φ* (Point.map (τ_{φS}).toAlgHom P_gen)
  ```
- **What**: The translation–isogeny commutation at the generic point in `Point` form: applying the
  translation-by-S map after `φ*` gives the same point as applying `φ*` after the translation-by-φS
  map, when both are applied to the generic point `P_gen`.
- **How**: Introduces an abbreviation `V = g(P_gen) + lift(φS)`, then establishes:
  (LHS) `Point.map τ_S (φ* P_gen) = V` by first applying `map_pullback_genericPoint_of_isGenuineWith`
  (so `φ* P_gen = g(P_gen)`) and then `hgcomm`; (RHS) `φ* (τ_{φS} P_gen) = V` by rewriting with
  `HasseWeil.translateAlgEquivOfPoint_map_genericPoint` (master lemma: `τ_k P_gen = P_gen + lift k`),
  additivity of `φpb` (`map_add`), and the key fact `φ* (lift k) = lift k` (since `φ*` fixes
  constants via `φ.pullback.commutes`). Uses `Affine.Point.some.injEq` for the constant-fix step.
- **Hypotheses**: `IsGenuineWith W φ g` plus the geometric commutation `hgcomm` at the generic point.
- **Uses from project**: `map_pullback_genericPoint_of_isGenuineWith` (this file),
  `HasseWeil.translateAlgEquivOfPoint_map_genericPoint` (SeparableKernelTorsor),
  `HasseWeil.liftPointToKE_some` (TranslationOrd),
  `HasseWeil.liftSomePoint` (TranslationOrd),
  `HasseWeil.liftPointToKE` (TranslationOrd/PointMap),
  `HasseWeil.translateAlgEquivOfPoint` (TranslationOrd)
- **Used by**: `hcomm_algHom_of_isGenuineWith` (line 147)
- **Visibility**: public
- **Lines**: 84–131, proof 97–131 (~35 lines)
- **Notes**: Proof exceeds 30 lines (35 lines). The longest proof in the file. Uses `set` to name
  intermediate values cleanly; the `hfix` subgoal (proving `φ*` fixes constant lifts) requires a
  case split on whether `φS = 0` or `some xk yk`.

---

### `theorem hcomm_algHom_of_isGenuineWith`

- **Type**:
  ```
  (φ : Isogeny W.toAffine W.toAffine)
  {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
  (hgen : IsGenuineWith W φ g) (S : W.toAffine.Point)
  (hgcomm : ...) :
  (τ_S).toAlgHom.comp φ.pullback =
    φ.pullback.comp (τ_{φS}).toAlgHom
  ```
- **What**: The translation–isogeny commutation as equality of `F`-algebra endomorphisms of `K(E)`:
  `τ_S ∘ φ* = φ* ∘ τ_{φS}`.
- **How**: Applies `hcomm_point_of_isGenuineWith` to get the point identity, rewrites via
  `Affine.Point.map_map` (to compose maps), then uses `genericPoint_xOf_some` to expose the `some`
  shape, extracts coordinates via `Affine.Point.some.inj`, and closes with
  `HasseWeil.algHom_ext_x_y_gen` (generator-extensionality: alg-hom equality follows from
  agreement on `x_gen` and `y_gen`).
- **Hypotheses**: Same as `hcomm_point_of_isGenuineWith`: `IsGenuineWith` plus `hgcomm`.
- **Uses from project**: `hcomm_point_of_isGenuineWith` (this file),
  `HasseWeil.algHom_ext_x_y_gen` (TranslationOrd),
  `HasseWeil.genericPoint_xOf_some` (GenericPoint)
- **Used by**: `hcomm_of_isGenuineWith` (line 168)
- **Visibility**: public
- **Lines**: 136–152, proof 145–152 (~8 lines)
- **Notes**: Short proof; relies heavily on the point-form result.

---

### `theorem hcomm_of_isGenuineWith`

- **Type**:
  ```
  (φ : Isogeny W.toAffine W.toAffine)
  {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
  (hgen : IsGenuineWith W φ g) (S : W.toAffine.Point)
  (hgcomm : ...) (z : KE) :
  translateAlgEquivOfPoint W S (φ.pullback z) =
    φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S) z)
  ```
- **What**: The pointwise translation–isogeny commutation: `τ_S (φ* z) = φ* (τ_{φS} z)` for every
  `z : K(E)`. This is exactly the `hcomm` hypothesis consumed by `weilPairing_adjoint_picDual` and
  `weilPairing_scaling`.
- **How**: Applies `hcomm_algHom_of_isGenuineWith` to get the alg-hom equality, then extracts the
  pointwise statement via `DFunLike.congr_fun`.
- **Hypotheses**: Same as `hcomm_algHom_of_isGenuineWith`.
- **Uses from project**: `hcomm_algHom_of_isGenuineWith` (this file)
- **Used by**: Used externally in `SeparableWitnesses.lean` (line 159). Unused in this file.
- **Visibility**: public
- **Lines**: 158–170, proof 166–170 (~5 lines)
- **Notes**: Pure wrapper over `hcomm_algHom_of_isGenuineWith`.

---

## Cross-reference Summary

| Declaration | Internal callers | External callers |
|---|---|---|
| `map_pullback_genericPoint_of_isGenuineWith` | `hcomm_point_of_isGenuineWith` (×2) | `MapTranslateGenericAdditive.lean` (×2) |
| `hcomm_point_of_isGenuineWith` | `hcomm_algHom_of_isGenuineWith` | none found |
| `hcomm_algHom_of_isGenuineWith` | `hcomm_of_isGenuineWith` | `MapTranslateGenericAdditive.lean` (mention) |
| `hcomm_of_isGenuineWith` | none (leaf) | `SeparableWitnesses.lean` (line 159) |
