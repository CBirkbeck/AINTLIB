# Inventory: ./HasseWeil/WeilPairing/MapTranslateGenericAdditive.lean

**File**: `HasseWeil/WeilPairing/MapTranslateGenericAdditive.lean`
**Import**: `HasseWeil.WeilPairing.SeparableWitnesses`
**Namespace**: `HasseWeil.WeilPairing`
**Sections**: `Additive` (lines 63–141), `Frobenius` (lines 168–210)
**Total declarations**: 3 theorems (all `theorem`)
**Sorries**: none
**set_option maxHeartbeats**: none

---

## Overview

This file establishes two structural results for the generic-point covariance predicate
`MapTranslateGenericPoint` (defined in `SeparableWitnesses.lean`): additivity in the geometric action,
and a bridge from any genuine action to the canonical pullback action.  It also provides the
commutation of the `q`-power Frobenius with translation (`frobeniusAlgHom_translate_commute`), which
is the kernel of the Frobenius component of the round-21 structural decomposition.

---

### `theorem mapTranslateGenericPoint_add`

- **Type**:
  ```
  (φ α₁ α₂ : Isogeny W.toAffine W.toAffine)
  (g₁ g₂ : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point)
  (hφhom : φ.toAddMonoidHom = α₁.toAddMonoidHom + α₂.toAddMonoidHom)
  (h₁ : MapTranslateGenericPoint W α₁ g₁)
  (h₂ : MapTranslateGenericPoint W α₂ g₂) :
  MapTranslateGenericPoint W φ (g₁ + g₂)
  ```
- **What**: If `g₁` satisfies the generic-point covariance for `α₁` and `g₂` for `α₂`, then
  `g₁ + g₂` satisfies it for any isogeny `φ` whose point map equals `α₁ + α₂`.  This is the
  additivity of `hgcomm` in the geometric action (reviewer round-21 structural decomposition).
- **How**: Pure additive bookkeeping.  `Point.map τ_S` is an `AddMonoidHom` so `map_add` distributes
  over `(g₁ + g₂) P_gen`; the two component covariances `h₁ S`, `h₂ S` rewrite each summand;
  `liftPointToKE_add` recombines the two lifts via `hφhom`.  Finished with `abel`.
- **Hypotheses**: Fields `F` with `DecidableEq`, `W` an elliptic Weierstrass curve; three isogenies
  on `W.toAffine`; two AddMonoidHom geometric actions; `hφhom` identifying `φ`'s point map as the
  sum of `α₁` and `α₂`; generic-point covariances `h₁`, `h₂` for the components.
- **Uses from project**:
  - `MapTranslateGenericPoint` (predicate, from `SeparableWitnesses.lean`)
  - `W_KE` (function-field base change, from project)
  - `translateAlgEquivOfPoint` (translation algebra equivalence, from project)
  - `genericPoint` (the generic point of `W_KE W`, from project)
  - `liftPointToKE` (lift of a base-field point to the function-field curve, from project)
  - `liftPointToKE_add` (additivity of `liftPointToKE`, from project)
- **Used by**: unused in file; called by `PencilCovariance.lean` (line 185) and referenced in
  `FrobeniusGenericCovariance.lean` (line 208) in other files
- **Visibility**: public
- **Lines**: 82–107 (proof lines 88–107, ~20 lines)
- **Notes**: No `set_option`. Proof is under 30 lines.

---

### `theorem mapTranslateGenericPoint_canonical_of_genuine`

- **Type**:
  ```
  (φ : Isogeny W.toAffine W.toAffine)
  {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
  (hgen : IsGenuineWith W φ g)
  (hg : MapTranslateGenericPoint W φ g) :
  MapTranslateGenericPoint W φ (WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback)
  ```
- **What**: For an isogeny `φ` genuine with geometric action `g`, the generic-point covariance for
  the **canonical** action `Affine.Point.map φ.pullback` follows from the covariance for `g`.
  Since `MapTranslateGenericPoint` only constrains the value at `P_gen`, and a genuine `g` equals
  the canonical action at `P_gen`, the leaf for `g` is exactly the leaf for the canonical action.
- **How**: Uses `map_pullback_genericPoint_of_isGenuineWith` (from project) to obtain
  `Point.map φ.pullback P_gen = g P_gen`, rewrites this equality in `hg S` to convert the `g`-leaf
  into the canonical-action leaf, then closes with `exact`.
- **Hypotheses**: `W` an elliptic Weierstrass curve over `F`; `φ` genuine with action `g` (i.e.
  `IsGenuineWith W φ g`); `hg` the generic-point covariance for `g`.
- **Uses from project**:
  - `MapTranslateGenericPoint` (predicate, from `SeparableWitnesses.lean`)
  - `IsGenuineWith` (predicate, from `SeparableWitnesses.lean`)
  - `W_KE` (function-field base change, from project)
  - `genericPoint` (from project)
  - `map_pullback_genericPoint_of_isGenuineWith` (bridge lemma, from project)
- **Used by**: unused in file; called by `PencilCovariance.lean` (lines 300, 305),
  `WallAGeometricRealization.lean` (line 264), and `PencilComapWitnesses.lean` (line 2205) in other
  files
- **Visibility**: public
- **Lines**: 125–139 (proof lines 131–139, ~9 lines)
- **Notes**: No `set_option`. Short proof. The key insight — that rewriting the single-point equality
  turns one leaf into the other — is elegant and minimal.

---

### `theorem frobeniusAlgHom_translate_commute`

- **Type**:
  ```
  (S : (W.baseChange L).toAffine.Point)
  (g : (W.baseChange L).toAffine.FunctionField) :
  (FiniteField.frobeniusAlgHom K (W.baseChange L).toAffine.FunctionField)
      (translateAlgEquivOfPoint (W.baseChange L) S g) =
    translateAlgEquivOfPoint (W.baseChange L) S
      ((FiniteField.frobeniusAlgHom K (W.baseChange L).toAffine.FunctionField) g)
  ```
- **What**: The `q`-power `𝔽_q`-algebra Frobenius `frob` commutes with translation `τ_S` on the
  function field `K̄(E)`, i.e. `frob(τ_S g) = τ_S(frob g)` for all `g`.  Since `frob = (· ^ q)` and
  `τ_S` is a ring hom, both sides equal `(τ_S g)^q`.
- **How**: Uses `FiniteField.coe_frobeniusAlgHom` (simp) to unfold the Frobenius as the `q`-power
  map, then applies `map_pow` (the ring-hom power law) in reverse (`symm`) — the core one-line
  argument.
- **Hypotheses**: `K` a finite field, `W` an elliptic Weierstrass curve over `K`, `L` a field
  extension of `K` with the base-changed curve being elliptic; `S` a point on `E_L`, `g` a function
  field element.
- **Uses from project**:
  - `translateAlgEquivOfPoint` (translation algebra equivalence over the base-changed curve, from
    project)
- **Used by**: `frobeniusAlgHom_translate_commute_ringHom` (directly, within this file)
- **Visibility**: public
- **Lines**: 184–191 (proof lines 189–191, ~3 lines)
- **Notes**: No `set_option`. Very short. This is the `K̄` analogue of the project's
  `frobeniusIsog_pullback_universal_commute` (which holds only over `𝔽_q`).

---

### `theorem frobeniusAlgHom_translate_commute_ringHom`

- **Type**:
  ```
  (S : (W.baseChange L).toAffine.Point) :
  (FiniteField.frobeniusAlgHom K (W.baseChange L).toAffine.FunctionField).toRingHom.comp
      (translateAlgEquivOfPoint (W.baseChange L) S).toAlgHom.toRingHom =
    (translateAlgEquivOfPoint (W.baseChange L) S).toAlgHom.toRingHom.comp
      (FiniteField.frobeniusAlgHom K (W.baseChange L).toAffine.FunctionField).toRingHom
  ```
- **What**: The `RingHom.comp` packaging of `frobeniusAlgHom_translate_commute`: `frob ∘ τ_S = τ_S
  ∘ frob` as ring endomorphisms of `K̄(E)`.  Sidesteps the scalar-tower mismatch between the
  `𝔽_q`-algebra Frobenius and the `K̄`-algebra translation.
- **How**: Proved by `ext` followed by `simp` unfolding `RingHom.comp`, `AlgHom.toRingHom`, etc.,
  then invoking `frobeniusAlgHom_translate_commute` pointwise.
- **Hypotheses**: Same as `frobeniusAlgHom_translate_commute` (minus the explicit `g`).
- **Uses from project**:
  - `translateAlgEquivOfPoint` (from project)
  - `frobeniusAlgHom_translate_commute` (within this file)
- **Used by**: unused in file; intended for use by Frobenius generic-point covariance constructions
  in other files (doc-comment notes `Affine.Point.map_map`)
- **Visibility**: public
- **Lines**: 199–208 (proof lines 204–208, ~5 lines)
- **Notes**: No `set_option`. Short. The `RingHom.comp` wrapping addresses the scalar-tower diamond
  (`frob` is `𝔽_q`-linear, `τ_S` is `K̄`-linear) that prevents a direct `AlgHom.comp` packaging.

---

## Summary

| Name | Kind | Lines | Proof length | Sorries |
|---|---|---|---|---|
| `mapTranslateGenericPoint_add` | theorem | 82–107 | ~20 | none |
| `mapTranslateGenericPoint_canonical_of_genuine` | theorem | 125–139 | ~9 | none |
| `frobeniusAlgHom_translate_commute` | theorem | 184–191 | ~3 | none |
| `frobeniusAlgHom_translate_commute_ringHom` | theorem | 199–208 | ~5 | none |

**Total**: 4 declarations, all theorems, no defs, no instances, no sorries.

**Key API used by 3+ others in this file**: none (the file has only 4 declarations with
`frobeniusAlgHom_translate_commute` used once internally by
`frobeniusAlgHom_translate_commute_ringHom`).

**Notable**: The file is a thin structural bridge with very short proofs.  All four declarations
are intended for use by callers in other files; only `frobeniusAlgHom_translate_commute` has an
intra-file caller.  No `set_option maxHeartbeats`, no sorries, no long proofs.
