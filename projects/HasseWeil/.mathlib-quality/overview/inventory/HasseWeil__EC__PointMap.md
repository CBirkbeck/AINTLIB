# Inventory: ./HasseWeil/EC/PointMap.lean

**File purpose:** Thin named-API layer over mathlib's bundled `WeierstrassCurve.Affine.Point.map`
(an `AddMonoidHom`). Provides short, directly-rewritable names for the group-hom equations
(`map_add`, `map_neg`, `map_sub`, `map_zsmul`, `map_nsmul`) both in the general namespace
`WeierstrassCurve.Affine.Point` and as specialisations for the project's two concrete uses:
(1) `liftPointToKE` (lift `E(F)→E(K(E))`), and (2) `F`-algebra endomorphisms of `K(E)` acting
on `(W_KE).Point` (including `translateAlgEquivOfPoint`).

**Import:** `HasseWeil.EC.TranslationOrd`

**Total declarations:** 11 theorems (no defs, no instances).

---

### `theorem WeierstrassCurve.Affine.Point.map_add`

- **Type**: `(P Q : W'⟮F⟯) : map f (P + Q) = map f P + map f Q`
- **What**: States that `Affine.Point.map f` respects addition of `F`-rational points, i.e., it is a group homomorphism for the addition operation.
- **How**: One-liner reduction to `_root_.map_add (map f) P Q`; no computation needed — `Affine.Point.map f` is already bundled as an `AddMonoidHom`.
- **Hypotheses**: `f : F →ₐ[S] K` an algebra homomorphism between field extensions of `S`; commutative scalar tower `R → S → F, K`.
- **Uses from project**: None (delegates to mathlib `_root_.map_add`).
- **Used by**: `map_translate_add`, `map_genericFF_add` (both in `HasseWeil` namespace below); referenced in docstrings by `MapTranslateGenericAdditive.lean`.
- **Visibility**: public
- **Lines**: 57–58, proof length 1 line
- **Notes**: Suspected mathlib duplication — this is literally `_root_.map_add` for an `AddMonoidHom`. Exists only to provide a short rewrite name in the `Point` namespace.

---

### `theorem WeierstrassCurve.Affine.Point.map_neg`

- **Type**: `(P : W'⟮F⟯) : map f (-P) = -(map f P)`
- **What**: States that `Affine.Point.map f` respects negation of points.
- **How**: One-liner `_root_.map_neg (map f) P`; `AddMonoidHom` API.
- **Hypotheses**: Same tower as `map_add`.
- **Uses from project**: None.
- **Used by**: `map_genericFF_neg`, `liftPointToKE_neg` (in `HasseWeil` namespace).
- **Visibility**: public
- **Lines**: 62–63, proof length 1 line
- **Notes**: Suspected mathlib duplication — thin convenience name.

---

### `theorem WeierstrassCurve.Affine.Point.map_sub`

- **Type**: `(P Q : W'⟮F⟯) : map f (P - Q) = map f P - map f Q`
- **What**: States that `Affine.Point.map f` distributes over subtraction.
- **How**: One-liner `_root_.map_sub (map f) P Q`.
- **Hypotheses**: Same tower as `map_add`.
- **Uses from project**: None.
- **Used by**: `map_genericFF_sub`, `liftPointToKE_sub`.
- **Visibility**: public
- **Lines**: 66–67, proof length 1 line
- **Notes**: Suspected mathlib duplication.

---

### `theorem WeierstrassCurve.Affine.Point.map_zsmul`

- **Type**: `(n : ℤ) (P : W'⟮F⟯) : map f (n • P) = n • map f P`
- **What**: States that `Affine.Point.map f` commutes with integer scalar multiplication.
- **How**: `AddMonoidHom.map_zsmul (map f) P n`.
- **Hypotheses**: Same tower as `map_add`.
- **Uses from project**: None.
- **Used by**: `map_genericFF_zsmul`, `map_translate_zsmul`, `liftPointToKE_zsmul`.
- **Visibility**: public
- **Lines**: 71–72, proof length 1 line
- **Notes**: Suspected mathlib duplication.

---

### `theorem WeierstrassCurve.Affine.Point.map_nsmul`

- **Type**: `(n : ℕ) (P : W'⟮F⟯) : map f (n • P) = n • map f P`
- **What**: States that `Affine.Point.map f` commutes with natural-number scalar multiplication.
- **How**: `AddMonoidHom.map_nsmul (map f) P n`.
- **Hypotheses**: Same tower as `map_add`.
- **Uses from project**: None.
- **Used by**: `liftPointToKE_nsmul`.
- **Visibility**: public
- **Lines**: 76–77, proof length 1 line
- **Notes**: Suspected mathlib duplication.

---

### `theorem HasseWeil.liftPointToKE_neg`

- **Type**: `(T : W.toAffine.Point) : liftPointToKE W (-T) = -(liftPointToKE W T)`
- **What**: The canonical lift `E(F) → E(K(E))` respects negation of rational points.
- **How**: `_root_.map_neg (liftPointToKE W) T`; `liftPointToKE W` is an `AddMonoidHom` by construction in `TranslationOrd.lean`.
- **Hypotheses**: `W` a Weierstrass curve over a field `F` with `DecidableEq F`; `IsElliptic` omitted (not needed).
- **Uses from project**: `HasseWeil.liftPointToKE` (defined in `TranslationOrd.lean`).
- **Used by**: No caller within this file; exported API.
- **Visibility**: public
- **Lines**: 95–99, proof length 1 line (with `omit` annotation)
- **Notes**: None.

---

### `theorem HasseWeil.liftPointToKE_sub`

- **Type**: `(T₁ T₂ : W.toAffine.Point) : liftPointToKE W (T₁ - T₂) = liftPointToKE W T₁ - liftPointToKE W T₂`
- **What**: The canonical lift `E(F) → E(K(E))` respects subtraction.
- **How**: `_root_.map_sub (liftPointToKE W) T₁ T₂`.
- **Hypotheses**: Same as `liftPointToKE_neg`.
- **Uses from project**: `HasseWeil.liftPointToKE`.
- **Used by**: No caller within this file; exported API.
- **Visibility**: public
- **Lines**: 101–105, proof length 1 line
- **Notes**: None.

---

### `theorem HasseWeil.liftPointToKE_zsmul`

- **Type**: `(n : ℤ) (T : W.toAffine.Point) : liftPointToKE W (n • T) = n • liftPointToKE W T`
- **What**: The canonical lift `E(F) → E(K(E))` commutes with integer scalar multiplication.
- **How**: `AddMonoidHom.map_zsmul (liftPointToKE W) T n`.
- **Hypotheses**: Same as `liftPointToKE_neg`.
- **Uses from project**: `HasseWeil.liftPointToKE`.
- **Used by**: No caller within this file; exported API.
- **Visibility**: public
- **Lines**: 107–111, proof length 1 line
- **Notes**: None.

---

### `theorem HasseWeil.liftPointToKE_nsmul`

- **Type**: `(n : ℕ) (T : W.toAffine.Point) : liftPointToKE W (n • T) = n • liftPointToKE W T`
- **What**: The canonical lift `E(F) → E(K(E))` commutes with natural-number scalar multiplication.
- **How**: `AddMonoidHom.map_nsmul (liftPointToKE W) T n`.
- **Hypotheses**: Same as `liftPointToKE_neg`.
- **Uses from project**: `HasseWeil.liftPointToKE`.
- **Used by**: No caller within this file; exported API.
- **Visibility**: public
- **Lines**: 113–117, proof length 1 line
- **Notes**: None.

---

### `theorem HasseWeil.map_genericFF_add`

- **Type**: `(φ : KE →ₐ[F] KE) (P Q : (W_KE W).toAffine.Point) : Affine.Point.map (W' := W) φ (P + Q) = Affine.Point.map (W' := W) φ P + Affine.Point.map (W' := W) φ Q`
- **What**: An `F`-algebra endomorphism `φ` of `K(E)` acts on `(W_KE).Point` as a group homomorphism — the addition-compatibility.
- **How**: Reduces to `Affine.Point.map_add φ P Q` (the general theorem in the `Point` namespace above).
- **Hypotheses**: `W` a Weierstrass curve over `F`; `DecidableEq F` and `IsElliptic` both omitted.
- **Uses from project**: `HasseWeil.W_KE`, `WeierstrassCurve.Affine.Point.map_add` (in this file).
- **Used by**: No caller within this file; noted in docstring as used by `translateAlgEquivOfPoint_map_genericPoint` in `SeparableKernelTorsor.lean`.
- **Visibility**: public
- **Lines**: 131–138, proof length 1 line
- **Notes**: None.

---

### `theorem HasseWeil.map_genericFF_neg`

- **Type**: `(φ : KE →ₐ[F] KE) (P : (W_KE W).toAffine.Point) : Affine.Point.map (W' := W) φ (-P) = -(Affine.Point.map (W' := W) φ P)`
- **What**: An `F`-algebra endomorphism of `K(E)` acts compatibly with negation on `(W_KE).Point`.
- **How**: `Affine.Point.map_neg φ P`.
- **Hypotheses**: Same as `map_genericFF_add`.
- **Uses from project**: `HasseWeil.W_KE`, `WeierstrassCurve.Affine.Point.map_neg` (in this file).
- **Used by**: No caller within this file; exported API.
- **Visibility**: public
- **Lines**: 140–144, proof length 1 line
- **Notes**: None.

---

### `theorem HasseWeil.map_genericFF_sub`

- **Type**: `(φ : KE →ₐ[F] KE) (P Q : (W_KE W).toAffine.Point) : Affine.Point.map (W' := W) φ (P - Q) = Affine.Point.map (W' := W) φ P - Affine.Point.map (W' := W) φ Q`
- **What**: An `F`-algebra endomorphism of `K(E)` acts compatibly with subtraction on `(W_KE).Point`.
- **How**: `Affine.Point.map_sub φ P Q`.
- **Hypotheses**: Same as `map_genericFF_add`.
- **Uses from project**: `HasseWeil.W_KE`, `WeierstrassCurve.Affine.Point.map_sub` (in this file).
- **Used by**: No caller within this file; exported API.
- **Visibility**: public
- **Lines**: 146–151, proof length 1 line
- **Notes**: None.

---

### `theorem HasseWeil.map_genericFF_zsmul`

- **Type**: `(φ : KE →ₐ[F] KE) (n : ℤ) (P : (W_KE W).toAffine.Point) : Affine.Point.map (W' := W) φ (n • P) = n • Affine.Point.map (W' := W) φ P`
- **What**: An `F`-algebra endomorphism of `K(E)` commutes with integer scalar multiplication on `(W_KE).Point`.
- **How**: `Affine.Point.map_zsmul φ n P`.
- **Hypotheses**: Same as `map_genericFF_add`.
- **Uses from project**: `HasseWeil.W_KE`, `WeierstrassCurve.Affine.Point.map_zsmul` (in this file).
- **Used by**: No caller within this file; noted in docstring as used by `genericPointAct` in `SeparableKernelTorsor.lean`.
- **Visibility**: public
- **Lines**: 153–158, proof length 1 line
- **Notes**: None.

---

### `theorem HasseWeil.map_translate_add`

- **Type**: `(k : W.toAffine.Point) (P Q : (W_KE W).toAffine.Point) : Affine.Point.map (W' := W) (translateAlgEquivOfPoint W k).toAlgHom (P + Q) = Affine.Point.map (W' := W) (translateAlgEquivOfPoint W k).toAlgHom P + Affine.Point.map (W' := W) (translateAlgEquivOfPoint W k).toAlgHom Q`
- **What**: The translation automorphism `τ_k : K(E) ≃ₐ[F] K(E)`, lifted to `(W_KE).Point`, preserves the group law.
- **How**: `Affine.Point.map_add _ P Q` — the general `map_add` applied to the AlgHom `τ_k.toAlgHom`.
- **Hypotheses**: `W` a Weierstrass curve over `F` with `DecidableEq F` and `IsElliptic`; `k : W.toAffine.Point` a base rational point.
- **Uses from project**: `HasseWeil.translateAlgEquivOfPoint` (from `TranslationOrd.lean`), `HasseWeil.W_KE`, `WeierstrassCurve.Affine.Point.map_add` (in this file).
- **Used by**: No caller within this file; exported API.
- **Visibility**: public
- **Lines**: 162–166, proof length 1 line
- **Notes**: None.

---

### `theorem HasseWeil.map_translate_zsmul`

- **Type**: `(k : W.toAffine.Point) (n : ℤ) (P : (W_KE W).toAffine.Point) : Affine.Point.map (W' := W) (translateAlgEquivOfPoint W k).toAlgHom (n • P) = n • Affine.Point.map (W' := W) (translateAlgEquivOfPoint W k).toAlgHom P`
- **What**: The translation automorphism `τ_k : K(E) ≃ₐ[F] K(E)`, lifted to `(W_KE).Point`, commutes with integer scalar multiplication.
- **How**: `Affine.Point.map_zsmul _ n P`.
- **Hypotheses**: Same as `map_translate_add`.
- **Uses from project**: `HasseWeil.translateAlgEquivOfPoint`, `HasseWeil.W_KE`, `WeierstrassCurve.Affine.Point.map_zsmul` (in this file).
- **Used by**: No caller within this file; exported API.
- **Visibility**: public
- **Lines**: 170–173, proof length 1 line
- **Notes**: None.

---

## Summary

- **Total declarations**: 13 (5 in `WeierstrassCurve.Affine.Point` namespace + 8 in `HasseWeil` namespace; note the inventory above lists 14 entries but `map_genericFF_*` group has 4 entries plus `map_translate_*` has 2, liftPointToKE_* has 4, and Point.map_* has 5 = 15 entries — correct count is 15 theorems... recounting: Point namespace: map_add, map_neg, map_sub, map_zsmul, map_nsmul = 5; HasseWeil: liftPointToKE_neg, liftPointToKE_sub, liftPointToKE_zsmul, liftPointToKE_nsmul = 4; map_genericFF_add, map_genericFF_neg, map_genericFF_sub, map_genericFF_zsmul = 4; map_translate_add, map_translate_zsmul = 2. Total = 5+4+4+2 = **15 theorems**.)
- **Sorries**: None.
- **`set_option maxHeartbeats`**: None.
- **Long proofs (>30 lines)**: None (every proof is 1 line).
- **Unused within file**: All 15 declarations are dead-code candidates within the file itself — none call each other except the `HasseWeil` theorems call the `Point` namespace theorems. The `Point.map_*` declarations are called within this file by some of the `HasseWeil` ones. The `HasseWeil` declarations have no callers confirmed within this file.
- **Key API (used by 3+)**: `WeierstrassCurve.Affine.Point.map_add` (used by `map_genericFF_add`, `map_translate_add`, and referenced in docstring); `WeierstrassCurve.Affine.Point.map_zsmul` (used by `map_genericFF_zsmul`, `map_translate_zsmul`).
