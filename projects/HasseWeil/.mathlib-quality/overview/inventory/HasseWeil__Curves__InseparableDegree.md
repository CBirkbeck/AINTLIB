# Inventory: ./HasseWeil/Curves/InseparableDegree.lean

File: `HasseWeil/Curves/InseparableDegree.lean`
Module: `Mathlib.FieldTheory.SeparableClosure`, `Mathlib.FieldTheory.PurelyInseparable.Basic`
Namespace: `HasseWeil.EC.Isogeny`
Total declarations: 10 (8 theorems + 1 noncomputable def + 1 theorem = 10)

## Overview

This file builds the inseparable-degree API for elliptic-curve isogenies (Silverman II.2.10–12), bridging the project's `Isogeny.inseparableDegree` / `Isogeny.separableDegree` / `Isogeny.degree` with mathlib's `Field.finInsepDegree` / `Field.finSepDegree` / `Module.finrank` in the pullback algebra structure on `W.FunctionField`.

---

### `theorem separableDegree_eq_finSepDegree`

- **Type**: `(α : Isogeny W W) → α.separableDegree = @Field.finSepDegree W.FunctionField W.FunctionField _ _ α.toAlgebra`
- **What**: States that the project's `Isogeny.separableDegree` equals mathlib's `Field.finSepDegree` under the pullback algebra structure. Definitional unfold (proof is `rfl`).
- **How**: Pure `rfl` — the two quantities are definitionally equal.
- **Hypotheses**: `W : Affine F` elliptic, `α : Isogeny W W`.
- **Uses from project**: `Isogeny.toAlgebra`, `W.FunctionField`
- **Used by**: `separableDegree_mul_finInsepDegree` (line 74), `inseparableDegree_isPow_of_charP` (line 153)
- **Visibility**: public
- **Lines**: 54–56, proof length 1 line
- **Notes**: None

---

### `theorem degree_eq_finrank`

- **Type**: `(α : Isogeny W W) → α.degree = @Module.finrank W.FunctionField W.FunctionField _ _ α.toAlgebra.toModule`
- **What**: States that the project's `Isogeny.degree` equals `Module.finrank` under the pullback algebra structure. Definitional unfold.
- **How**: Pure `rfl`.
- **Hypotheses**: `W : Affine F` elliptic, `α : Isogeny W W`.
- **Uses from project**: `Isogeny.toAlgebra`, `W.FunctionField`
- **Used by**: `separableDegree_mul_finInsepDegree` (line 74)
- **Visibility**: public
- **Lines**: 60–63, proof length 1 line
- **Notes**: None

---

### `theorem separableDegree_mul_finInsepDegree`

- **Type**: `(α : Isogeny W W) → letI := α.toAlgebra; α.separableDegree * Field.finInsepDegree W.FunctionField W.FunctionField = α.degree`
- **What**: Proves multiplicativity `separableDegree · finInsepDegree = degree`, i.e., the degree of the field extension factors into its separable and inseparable parts.
- **How**: Rewrites via `separableDegree_eq_finSepDegree` and `degree_eq_finrank`, then applies mathlib's `Field.finSepDegree_mul_finInsepDegree`.
- **Hypotheses**: `W : Affine F` elliptic, `α : Isogeny W W`.
- **Uses from project**: `separableDegree_eq_finSepDegree`, `degree_eq_finrank`, `Isogeny.toAlgebra`
- **Used by**: `inseparableDegree_eq_finInsepDegree` (line 92), `inseparableDegree_dvd_degree` (line 108)
- **Visibility**: public
- **Lines**: 68–75, proof length 7 lines
- **Notes**: None

---

### `theorem inseparableDegree_eq_finInsepDegree`

- **Type**: `(α : Isogeny W W) → (h_sep_pos : 0 < α.separableDegree) → letI := α.toAlgebra; α.inseparableDegree = Field.finInsepDegree W.FunctionField W.FunctionField`
- **What**: Identifies the project's `inseparableDegree` (defined as `degree / separableDegree`) with mathlib's `finInsepDegree`, under the condition that `separableDegree > 0`.
- **How**: Uses `separableDegree_mul_finInsepDegree` to rewrite `degree = separableDegree * finInsepDegree`, then cancels via `Nat.mul_div_cancel_left`.
- **Hypotheses**: `W : Affine F` elliptic, `α : Isogeny W W`, separable degree positive.
- **Uses from project**: `separableDegree_mul_finInsepDegree`
- **Used by**: `inseparableDegree_isPow_of_charP` (line 157)
- **Visibility**: public
- **Lines**: 81–97, proof length 16 lines
- **Notes**: None

---

### `theorem inseparableDegree_dvd_degree`

- **Type**: `(α : Isogeny W W) → α.inseparableDegree ∣ α.degree`
- **What**: Proves that the inseparable degree divides the degree of the isogeny.
- **How**: Uses `separableDegree_mul_finInsepDegree` to factor degree, then does a case split on whether `separableDegree = 0` or not; the nonzero case uses `Nat.mul_div_cancel_left` and `Dvd.intro_left`.
- **Hypotheses**: `W : Affine F` elliptic, `α : Isogeny W W`.
- **Uses from project**: `separableDegree_mul_finInsepDegree`
- **Used by**: unused in file (external: `HasseWeil/Hasse/Separability.lean`)
- **Visibility**: public
- **Lines**: 103–117, proof length 14 lines
- **Notes**: None

---

### `theorem inseparableDegree_eq_one_iff_separable`

- **Type**: `(α : Isogeny W W) → α.inseparableDegree = 1 ↔ α.IsSeparable`
- **What**: States the equivalence between `inseparableDegree = 1` and the project's `IsSeparable` predicate. Definitional identity (proof is `rfl`).
- **How**: Pure `rfl` — `IsSeparable` is defined as `inseparableDegree = 1`.
- **Hypotheses**: `W : Affine F` elliptic, `α : Isogeny W W`.
- **Uses from project**: `Isogeny.IsSeparable`, `Isogeny.inseparableDegree`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 121–123, proof length 1 line
- **Notes**: None

---

### `theorem inseparableDegree_isPow_of_charP`

- **Type**: `{K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] {W : WeierstrassCurve K} [W.toAffine.IsElliptic] (α : Isogeny W.toAffine W.toAffine) (h_deg_pos : 0 < α.degree) → ∃ e : ℕ, α.inseparableDegree = p ^ e`
- **What**: In characteristic `p`, the inseparable degree of a nonzero-degree isogeny is a power of `p`, i.e., `p^e` for some `e ≥ 0`.
- **How**: Transports `CharP` to the function field via `charP_of_injective_algebraMap`, derives `ExpChar` from `CharP` + `Fact p.Prime`, establishes `FiniteDimensional` from `h_deg_pos` via `FiniteDimensional.of_finrank_pos`, then applies mathlib's `finInsepDegree_eq_pow` and bridges via `inseparableDegree_eq_finInsepDegree`.
- **Hypotheses**: `K` a field of characteristic `p` (prime), `W` an elliptic Weierstrass curve over `K`, isogeny `α` with positive degree.
- **Uses from project**: `separableDegree_eq_finSepDegree`, `inseparableDegree_eq_finInsepDegree`
- **Used by**: unused in file (external: `HasseWeil/Hasse/Separability.lean`)
- **Visibility**: public
- **Lines**: 129–158, proof length 29 lines
- **Notes**: Proof is 29 lines (just under the 30-line threshold). Uses `finInsepDegree_eq_pow` from mathlib and relies on `Field.instNeZeroFinSepDegree` for the separability positivity subgoal.

---

### `noncomputable def separableSubfield`

- **Type**: `(α : Isogeny W W) → IntermediateField α.pullback.fieldRange W.FunctionField`
- **What**: Defines the maximal intermediate field (separable closure of `α^*(K(E))` inside `K(E)`) over which `K(E)` is purely inseparable. This is a direct specialisation of mathlib's `separableClosure`.
- **How**: Pure definition: `separableClosure α.pullback.fieldRange W.FunctionField`.
- **Hypotheses**: `W : Affine F` elliptic, `α : Isogeny W W`. Requires `set_option backward.isDefEq.respectTransparency false` to avoid definitional equality issues.
- **Uses from project**: `Isogeny.pullback`, `W.FunctionField`
- **Used by**: `separableSubfield_includes_pullbackRange` (line 176), `function_field_over_separableSubfield_purely_inseparable` (line 185)
- **Visibility**: public
- **Lines**: 166–171 (with `set_option`), proof length 1 line (definitional)
- **Notes**: Uses `set_option backward.isDefEq.respectTransparency false` (NO-COMMENT — no justifying comment explaining why this is needed).

---

### `theorem separableSubfield_includes_pullbackRange`

- **Type**: `(α : Isogeny W W) → ⊥ ≤ α.separableSubfield`
- **What**: States that the bottom element (the base field `α^*(K(E))`) is below the separable subfield, i.e., the pullback range is contained in the separable subfield.
- **How**: `bot_le` (trivial lattice fact).
- **Hypotheses**: `W : Affine F` elliptic, `α : Isogeny W W`. Requires `set_option backward.isDefEq.respectTransparency false`.
- **Uses from project**: `separableSubfield`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 173–176 (with `set_option`), proof length 1 line
- **Notes**: Uses `set_option backward.isDefEq.respectTransparency false` (NO-COMMENT). The `⊥ ≤ α.separableSubfield` statement is trivially `bot_le`; unclear what mathematical content is intended beyond the definitional layer — this may be parked/placeholder.

---

### `theorem function_field_over_separableSubfield_purely_inseparable`

- **Type**: `(α : Isogeny W W) → [Algebra.IsAlgebraic α.pullback.fieldRange W.FunctionField] → IsPurelyInseparable (↥α.separableSubfield) W.FunctionField`
- **What**: Proves that `K(E)` is purely inseparable over the separable subfield of `α^*(K(E))`, i.e., the extension `K(E) / separableSubfield` is purely inseparable.
- **How**: Direct application of mathlib's `separableClosure.isPurelyInseparable`.
- **Hypotheses**: `W : Affine F` elliptic, `α : Isogeny W W`, algebraicity of `K(E)` over `α^*(K(E))` (automatic for `Module.Finite`). Requires `set_option backward.isDefEq.respectTransparency false`.
- **Uses from project**: `separableSubfield`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 178–186 (with `set_option`), proof length 1 line
- **Notes**: Uses `set_option backward.isDefEq.respectTransparency false` (NO-COMMENT). The algebraicity hypothesis is carried explicitly; it is automatically satisfied for finite-degree isogenies but not synthesized automatically here.

---

## Summary table

| Declaration | Kind | Lines | Sorries | Internal callers |
|---|---|---|---|---|
| `separableDegree_eq_finSepDegree` | theorem | 54–56 | 0 | 2 |
| `degree_eq_finrank` | theorem | 60–63 | 0 | 1 |
| `separableDegree_mul_finInsepDegree` | theorem | 68–75 | 0 | 2 |
| `inseparableDegree_eq_finInsepDegree` | theorem | 81–97 | 0 | 1 |
| `inseparableDegree_dvd_degree` | theorem | 103–117 | 0 | 0 |
| `inseparableDegree_eq_one_iff_separable` | theorem | 121–123 | 0 | 0 |
| `inseparableDegree_isPow_of_charP` | theorem | 129–158 | 0 | 0 |
| `separableSubfield` | noncomputable def | 166–171 | 0 | 2 |
| `separableSubfield_includes_pullbackRange` | theorem | 173–176 | 0 | 0 |
| `function_field_over_separableSubfield_purely_inseparable` | theorem | 178–186 | 0 | 0 |

**No sorries. No proofs > 30 lines. No maxHeartbeats (only `set_option backward.isDefEq.respectTransparency false`).**

keyApi (2+ internal callers): `separableDegree_mul_finInsepDegree` (2 callers), `separableDegree_eq_finSepDegree` (2 callers), `separableSubfield` (2 callers).

Declarations unused within this file (dead-code candidates for this file; all are used externally or are public API): `inseparableDegree_dvd_degree`, `inseparableDegree_eq_one_iff_separable`, `inseparableDegree_isPow_of_charP`, `separableSubfield_includes_pullbackRange`, `function_field_over_separableSubfield_purely_inseparable`.
