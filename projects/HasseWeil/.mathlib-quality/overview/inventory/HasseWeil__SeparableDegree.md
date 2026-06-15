# Inventory: ./HasseWeil/SeparableDegree.lean

**File**: `HasseWeil/SeparableDegree.lean`
**Lines**: 1–63
**Imports**: `HasseWeil.Isogeny`, `Mathlib.FieldTheory.SeparableDegree`
**Namespace**: `HasseWeil.Isogeny`

This is a small interface file (5 declarations) connecting the project's `PullbackIsogeny` type to mathlib's `Field.finSepDegree` machinery.

---

### `noncomputable def sepDegree`

- **Type**: `(φ : PullbackIsogeny F W₁ W₂) → ℕ`
- **What**: Defines the separable degree of an isogeny as the number of `F`-algebra embeddings of `K(E₂)` into an algebraic closure of `K(E₁)`, via the pullback algebra structure `φ.toAlgebra`.
- **How**: Single-line definition: `@Field.finSepDegree W₂.FunctionField W₁.FunctionField _ _ φ.toAlgebra`. Delegates entirely to mathlib's `Field.finSepDegree`.
- **Hypotheses**: `F` is a field; `W₁`, `W₂` are elliptic curves over `F`.
- **Uses from project**: `PullbackIsogeny`, `PullbackIsogeny.toAlgebra` (from `HasseWeil.Isogeny`), `Affine.FunctionField` (implicit via `W₂.FunctionField`)
- **Used by**: `IsSeparable` (in this file); `sepDegree_dvd_degree`; `sepDegree_le_degree`; extensively by callers in `GapSpines.lean`, `EC/IsogenyKernel.lean`, `AdditionPullback/SilvermanIV14.lean`, `Verschiebung/Cascade.lean`, `EC/IsogenyAG.lean`, `Hasse/BoundOfWitnesses.lean`, `Hasse/QuadraticForm.lean`
- **Visibility**: public
- **Lines**: 40–41, proof length: 1 line (definition)
- **Notes**: `noncomputable` because `Field.finSepDegree` is noncomputable. No `sorry`, no `set_option maxHeartbeats`.

---

### `def IsSeparable`

- **Type**: `(φ : PullbackIsogeny F W₁ W₂) → Prop`
- **What**: Defines the predicate that an isogeny is separable, meaning its separable degree equals its total degree.
- **How**: Single-line definition: `φ.sepDegree = φ.degree`. No proof needed.
- **Hypotheses**: `F` is a field; `W₁`, `W₂` are elliptic curves over `F`.
- **Uses from project**: `sepDegree` (this file), `PullbackIsogeny.degree` (from `HasseWeil.Isogeny`)
- **Used by**: Unused directly in this file (but heavily used externally: `BridgeFrobenius.lean`, `AdditionPullback/SilvermanIV14.lean`, `EC/IsogenyAG.lean`, `Verschiebung/Cascade.lean`)
- **Visibility**: public
- **Lines**: 44–45, definition (0 proof lines)
- **Notes**: No `sorry`, no `set_option maxHeartbeats`. Note: `EC/IsogenyAG.lean` defines its own `abbrev IsSeparable` for the `Isogeny` wrapper type (`φ.toCurveMap.IsSeparable`), distinct from this `PullbackIsogeny`-based definition.

---

### `theorem sepDegree_dvd_degree`

- **Type**: `(φ : PullbackIsogeny F W₁ W₂) → φ.sepDegree ∣ φ.degree`
- **What**: Proves that the separable degree of an isogeny divides its total degree (the finite extension degree).
- **How**: Unfolds `sepDegree` and `degree` to expose the mathlib definitions, then applies `@Field.finSepDegree_dvd_finrank` with the explicit algebra instance `φ.toAlgebra`.
- **Hypotheses**: `F` is a field; `W₁`, `W₂` are elliptic curves over `F`. No finite-dimensionality hypothesis required (this holds unconditionally from mathlib).
- **Uses from project**: `PullbackIsogeny`, `PullbackIsogeny.toAlgebra`, `PullbackIsogeny.degree` (via `unfold degree`); `sepDegree` (via `unfold sepDegree`)
- **Used by**: Unused in this file (dead-code candidate within file; may be used externally)
- **Visibility**: public
- **Lines**: 48–51, proof length: 2 lines
- **Notes**: No `sorry`, no `set_option maxHeartbeats`. Proof is a direct reduction to mathlib's `Field.finSepDegree_dvd_finrank`.

---

### `theorem sepDegree_le_degree`

- **Type**: `(φ : PullbackIsogeny F W₁ W₂) → FiniteDimensional W₂.FunctionField W₁.FunctionField (via φ.toAlgebra.toModule) → φ.sepDegree ≤ φ.degree`
- **What**: Proves that the separable degree is at most the total degree, under the assumption that the field extension is finite-dimensional.
- **How**: Unfolds `sepDegree` and `degree`, then applies `@Field.finSepDegree_le_finrank` with the explicit algebra and finite-dimensionality instances.
- **Hypotheses**: `F` is a field; `W₁`, `W₂` are elliptic curves over `F`; the extension `K(E₁)/φ^*K(E₂)` is finite-dimensional (carried as explicit hypothesis `hfin`).
- **Uses from project**: `PullbackIsogeny`, `PullbackIsogeny.toAlgebra`, `PullbackIsogeny.degree` (via `unfold`); `sepDegree` (via `unfold`)
- **Used by**: Unused in this file (dead-code candidate within file; may be used externally)
- **Visibility**: public
- **Lines**: 54–58, proof length: 3 lines
- **Notes**: No `sorry`, no `set_option maxHeartbeats`. The `hfin` hypothesis is passed using the explicit algebra form `φ.toAlgebra.toModule` to avoid instance mismatch. This is a weaker statement than `sepDegree_dvd_degree` being unconditional — it requires finite-dimensionality.

---

## Summary

| Name | Kind | Lines | Sorry | Notes |
|---|---|---|---|---|
| `sepDegree` | noncomputable def | 40–41 | No | wraps `Field.finSepDegree` |
| `IsSeparable` | def | 44–45 | No | predicate: `sepDegree = degree` |
| `sepDegree_dvd_degree` | theorem | 48–51 | No | 2-line proof via mathlib |
| `sepDegree_le_degree` | theorem | 54–58 | No | 3-line proof via mathlib |

**Total**: 4 declarations (2 defs, 2 theorems, 0 instances).

No `set_option maxHeartbeats` occurrences. No `sorry`. No proof longer than 30 lines. No instances.

The file serves as a thin adapter layer; `sepDegree_dvd_degree` and `sepDegree_le_degree` appear unused within this file (they are API exported for callers). The key API consumers (`sepDegree`, `IsSeparable`) are used by many downstream files. Note that the more developed API (`isSeparable_iff_sepDegree_eq_degree`, `sepDegree_eq_card_emb`, `card_kernel_eq_degree_of_sepDegree_eq_card_kernel`) lives in `EC/IsogenyKernel.lean`, not here — this file provides only the primitive definitions and two elementary divisibility/monotonicity facts.
