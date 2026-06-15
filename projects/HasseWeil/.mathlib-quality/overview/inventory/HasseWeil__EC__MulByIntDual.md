# Inventory: ./HasseWeil/EC/MulByIntDual.lean

**File**: `HasseWeil/EC/MulByIntDual.lean`
**Lines**: 49
**Imports**: `HasseWeil.DualIsogeny`, `HasseWeil.EC.GenericPointZsmul`
**Purpose**: Proves Silverman III.6.2(d): the dual isogeny of `[n]` equals `[n]` itself (`isogDual_mulByInt`).

---

## Declarations

### `theorem isogDual_mulByInt`

- **Type**:
  ```lean
  theorem isogDual_mulByInt (E : WeierstrassCurve F) [E.toAffine.IsElliptic]
      (n : ℤ) (hn : n ≠ 0) :
      isogDual E.toAffine (mulByInt E.toAffine n) = mulByInt E.toAffine n
  ```

- **What**: For any elliptic curve `E` over a field `F` and any nonzero integer `n`, the dual isogeny of the multiplication-by-`n` map equals the multiplication-by-`n` map itself: `[n]̂ = [n]`. This is Silverman III.6.2(d).

- **How**: Applies `isogDual_mulByInt_of_comp` (the parametric witness form in `DualIsogeny.lean`) with the composition identity `[n] ∘ [n] = [n²]` (from `mulByInt_comp_eq_mul`, T-III-4-020b) and the degree formula `deg [n] = n².toNat` (from `mulByInt_degree`). A `congr 1` reduces the `toNat` arithmetic to `n * n = n ^ 2` plus `Int.toNat_of_nonneg`.

- **Hypotheses**: `E` is an elliptic curve (i.e., `E.toAffine.IsElliptic`); `n ≠ 0` (so that `[n]` is a nonzero isogeny and its dual is defined).

- **Uses from project**:
  - `isogDual_mulByInt_of_comp` (`HasseWeil.DualIsogeny`, line 344) — the parametric uniqueness witness: if `[n] ∘ [n] = [n²]` and `deg [n] = n².toNat`, then `isogDual [n] = [n]`.
  - `mulByInt_comp_eq_mul` (`HasseWeil.EC.GenericPointZsmul`, line 968) — composition identity `[m] ∘ [n] = [m·n]`.
  - `mulByInt_degree` (`HasseWeil.Basic`, line 1122) — degree formula `deg [n] = (n^2).toNat` (as a natural number).

- **Used by**: Nothing else in this file (sole declaration). Not referenced by any other `.lean` file that was found (no file imports `HasseWeil.EC.MulByIntDual`).

- **Visibility**: public

- **Lines**: 39–48 (proof body lines 42–47, approximately 6 lines)

- **Notes**: No `set_option maxHeartbeats`, no `sorry`. Proof is short (6 lines). The `Int.toNat_of_nonneg` call handles the `ℕ`-vs-`ℤ` coercion for `n^2`. No apparent mathlib duplication — this is project-specific given the project's `mulByInt`/`isogDual` API.

---

## Summary

| Metric | Value |
|---|---|
| Total declarations | 1 |
| Theorems/Lemmas | 1 |
| Defs | 0 |
| Instances | 0 |
| Sorries | none |
| `set_option maxHeartbeats` | none |
| Long proofs (>30 lines) | none |
| Unused in file | `isogDual_mulByInt` (sole decl; not referenced elsewhere in file; no known file imports this module) |
| Key API | none (only 1 decl) |
