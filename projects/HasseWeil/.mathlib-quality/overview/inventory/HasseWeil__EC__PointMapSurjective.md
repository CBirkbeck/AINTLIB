# Inventory: ./HasseWeil/EC/PointMapSurjective.lean

**File**: `HasseWeil/EC/PointMapSurjective.lean`
**Module header**: Surjectivity of `Affine.Point.map` and the geometric Frobenius over `K̄`
**Import**: `HasseWeil.Curves.FrobeniusFixedPoint`
**Total declarations**: 4 (3 theorems + 1 local noncomputable instance)

---

## Summary

A short, self-contained file (123 lines) establishing two results:
1. `Affine.Point.map f` is surjective whenever the underlying field hom `f` is surjective.
2. The geometric Frobenius `geomFrobeniusPoint W` on `K̄`-points is bijective.

No sorries, no `set_option maxHeartbeats`, all proofs are short (≤10 lines each).

---

## Declarations

---

### `noncomputable local instance instDecEqACSurjFrob`

- **Type**: `DecidableEq (AlgebraicClosure K)`
- **What**: Provides `DecidableEq` for the algebraic closure of `K` via `Classical.decEq`, needed as a typeclass for `Affine.Point.map` on `K̄`-points.
- **How**: Direct application of `Classical.decEq`.
- **Hypotheses**: `K` a finite field.
- **Uses from project**: none
- **Used by**: `geomFrobeniusPoint_surjective`, `geomFrobeniusPoint_bijective` (implicitly via typeclass inference in the `GeomFrobenius` section)
- **Visibility**: private (local instance)
- **Lines**: 83–84, proof length: 1 line
- **Notes**: Local instance scoped to the `GeomFrobenius` section; avoids polluting the global namespace with a classical `DecidableEq`.

---

### `theorem affinePointMap_surjective`

- **Type**:
  ```
  {f : F →ₐ[S] K} (hf : Function.Surjective f) :
      Function.Surjective (WeierstrassCurve.Affine.Point.map (W' := W') f)
  ```
- **What**: If an algebra hom `f : F →ₐ[S] K` between fields is surjective, then the induced group hom on Weierstrass affine points `W'⟮F⟯ →+ W'⟮K⟯` is surjective. The identity point lifts to itself; an affine point `(x', y')` lifts to `(x, y)` with `f x = x'`, `f y = y'`, and source nonsingularity is obtained by transporting `h'` back through `baseChange_nonsingular`.
- **How**: Case-splits on `0` vs `some x' y' h'` via `rintro`; uses `hf` to get preimages; applies `WeierstrassCurve.Affine.baseChange_nonsingular (f.restrictScalars R).injective` (mathlib) to transport target nonsingularity to source; closes with `Affine.Point.map_some` and `Affine.Point.some.injEq`.
- **Hypotheses**: `W' : WeierstrassCurve R`, `F` and `K` fields over `R` via `S`, `f : F →ₐ[S] K` surjective.
- **Uses from project**: none (pure mathlib)
- **Used by**: `geomFrobeniusPoint_surjective`
- **Visibility**: public
- **Lines**: 54–72, proof length: ~18 lines
- **Notes**: General utility lemma; the `restrictScalars R` wrapping is needed because `baseChange_nonsingular` expects an `R`-algebra hom.

---

### `theorem frobeniusAlgHom_surjective_algebraicClosure`

- **Type**:
  ```
  Function.Surjective (FiniteField.frobeniusAlgHom K (AlgebraicClosure K))
  ```
- **What**: The `q`-power Frobenius `K`-algebra hom of `AlgebraicClosure K` is surjective. This follows because the Frobenius on an algebraic extension of a finite field is an automorphism (`frobeniusAlgEquivOfAlgebraic`), hence surjective.
- **How**: Proves that `frobeniusAlgHom` and `frobeniusAlgEquivOfAlgebraic` agree as functions via `FiniteField.coe_frobeniusAlgHom` and `FiniteField.coe_frobeniusAlgEquivOfAlgebraic` (both mathlib), then uses `AlgEquiv.surjective` of the equivalence.
- **Hypotheses**: `K` a finite field, `K̄ = AlgebraicClosure K`.
- **Uses from project**: none (pure mathlib)
- **Used by**: `geomFrobeniusPoint_surjective`
- **Visibility**: public
- **Lines**: 89–97, proof length: ~8 lines
- **Notes**: The key mathlib lemmas are `FiniteField.coe_frobeniusAlgHom` and `FiniteField.coe_frobeniusAlgEquivOfAlgebraic` (coercion lemmas).

---

### `theorem geomFrobeniusPoint_surjective`

- **Type**:
  ```
  Function.Surjective (geomFrobeniusPoint W)
  ```
- **What**: The geometric Frobenius group hom `geomFrobeniusPoint W : (W.baseChange K̄).toAffine.Point →+ ...` is surjective (Silverman III.4.10a, Frobenius factor).
- **How**: Unfolds `geomFrobeniusPoint` as `Affine.Point.map (frobeniusAlgHom K K̄)` via `change`, then applies `affinePointMap_surjective` with `frobeniusAlgHom_surjective_algebraicClosure`.
- **Hypotheses**: `W : WeierstrassCurve K` with `K` finite, `W.toAffine.IsElliptic`, `(W.baseChange K̄).toAffine.IsElliptic`.
- **Uses from project**: `geomFrobeniusPoint` (from `HasseWeil.Curves.FrobeniusFixedPoint`), `affinePointMap_surjective`, `frobeniusAlgHom_surjective_algebraicClosure`
- **Used by**: `geomFrobeniusPoint_bijective`
- **Visibility**: public
- **Lines**: 103–107, proof length: 4 lines
- **Notes**: The `change` tactic is needed because `geomFrobeniusPoint` is a `noncomputable def` wrapping `Affine.Point.map`.

---

### `theorem geomFrobeniusPoint_bijective`

- **Type**:
  ```
  Function.Bijective (geomFrobeniusPoint W)
  ```
- **What**: The geometric Frobenius point map over `K̄` is bijective: surjective by `geomFrobeniusPoint_surjective`, injective because `Affine.Point.map` of an injective field hom is injective (mathlib `Affine.Point.map_injective`).
- **How**: Pairs injectivity (`Affine.Point.map_injective` applied to `frobeniusAlgHom`, which is injective as a ring hom of a field) with `geomFrobeniusPoint_surjective`.
- **Hypotheses**: Same as `geomFrobeniusPoint_surjective`.
- **Uses from project**: `geomFrobeniusPoint` (from `HasseWeil.Curves.FrobeniusFixedPoint`), `geomFrobeniusPoint_surjective`
- **Used by**: unused in file (exported API)
- **Visibility**: public
- **Lines**: 112–118, proof length: 6 lines
- **Notes**: None.

---

## Cross-reference summary

| Declaration | Used by (in file) |
|---|---|
| `instDecEqACSurjFrob` | implicit typeclass use in `GeomFrobenius` section |
| `affinePointMap_surjective` | `geomFrobeniusPoint_surjective` |
| `frobeniusAlgHom_surjective_algebraicClosure` | `geomFrobeniusPoint_surjective` |
| `geomFrobeniusPoint_surjective` | `geomFrobeniusPoint_bijective` |
| `geomFrobeniusPoint_bijective` | unused in file |

**Key API** (used by 3+ declarations): none — `geomFrobeniusPoint_surjective` is used by only 1 other declaration in the file.

**Sorries**: none.

**`set_option maxHeartbeats`**: none.

**Long proofs (>30 lines)**: none.
