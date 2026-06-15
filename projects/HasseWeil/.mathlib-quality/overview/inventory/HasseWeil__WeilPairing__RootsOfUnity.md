# Inventory: ./HasseWeil/WeilPairing/RootsOfUnity.lean

**File purpose**: Supplies the additive identification `μ_ℓ ≅ ℤ/ℓ` used to convert the multiplicative Weil-pairing values into the **additive** `ℤ/ℓ`-valued symplectic form that the finite-level determinant residual (`hscale` / `DetDeg`) works with. A one-declaration bridge file.

**Imports**: `Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots` (mathlib only — no project imports)

**Total declarations**: 1 (`noncomputable def`)

**Module options**: none. No `sorry`, no `maxHeartbeats`.

---

## Declarations

### `noncomputable def rootsOfUnity_addEquiv_zmod`
- **Type**: `{F : Type*} [Field F] {ℓ : ℕ} [NeZero ℓ] {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ ℓ) : Additive (rootsOfUnity ℓ F) ≃+ ZMod ℓ`
- **What**: **`μ_ℓ ≅ ℤ/ℓ` additively**: given a primitive `ℓ`-th root of unity `ζ` in a field `F`, the group of `ℓ`-th roots of unity (written additively) is isomorphic as an additive group to `ZMod ℓ`. This is the codomain-additivisation of the Weil pairing.
- **How**: Composes mathlib's `IsPrimitiveRoot.zmodEquivZPowers` (`ZMod ℓ ≃+ Additive (zpowers ζ)`) with `IsPrimitiveRoot.zpowers_eq` (`zpowers ζ = rootsOfUnity ℓ F`, rewritten via `▸`), then takes `.symm`.
- **Hypotheses**: `F` a field, `ℓ : ℕ` with `[NeZero ℓ]`, and a primitive `ℓ`-th root of unity `ζ : Fˣ`.
- **Uses from project**: none (pure mathlib: `IsPrimitiveRoot.zmodEquivZPowers`, `IsPrimitiveRoot.zpowers_eq`)
- **Used by (within file)**: none. **Used by (project)**: `HasseWeil/WeilPairing/DetDeg.lean` (the single consumer — the additivisation of `e_ℓ` values into the `ℤ/ℓ` symplectic form).
- **Visibility**: public
- **Lines**: 22–25, proof length: 1 line (term)

---

## Cross-reference summary

| Declaration | Used by |
|---|---|
| `rootsOfUnity_addEquiv_zmod` | (project) `DetDeg.lean` |

**Key API**: `rootsOfUnity_addEquiv_zmod` (the file's sole export; live — used by `DetDeg`).

## Notes / cleanup analysis

- **(c) mathlib-fit — POSITIVE**: This file does **not** hand-roll a custom `μ_ℓ`. It correctly reuses mathlib's `rootsOfUnity ℓ F`, `IsPrimitiveRoot`, `zmodEquivZPowers`, and `zpowers_eq`. The declaration is a thin, idiomatic composition. No custom roots-of-unity structure to flag.
- **(a) Unused within file**: trivially none (single declaration); it is live via `DetDeg`.
- **(b) No scratch/superseded content.**
- **(e) Generalisation**: already maximally general for the use case (any field with a primitive `ℓ`-th root). The `Field` hypothesis could in principle be weakened toward `CommRing` + the relevant `IsPrimitiveRoot` hypotheses, but mathlib's `zmodEquivZPowers`/`zpowers_eq` lemmas drive the natural generality, and the Weil-pairing application only ever needs a field, so this is appropriately stated.
- **Smallest file in the cluster (27 lines).** No `sorry`, no `maxHeartbeats`, no long proofs.
