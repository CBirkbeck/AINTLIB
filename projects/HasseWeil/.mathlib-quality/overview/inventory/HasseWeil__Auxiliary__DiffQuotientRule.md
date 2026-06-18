# Inventory: ./HasseWeil/Auxiliary/DiffQuotientRule.lean

## File summary

**Path**: `HasseWeil/Auxiliary/DiffQuotientRule.lean`  
**Imports**: `HasseWeil.InvariantDifferential`, `Mathlib.RingTheory.Kaehler.Basic`  
**Module doc**: "Quotient rule and inverse rule for the universal derivation."  
**Total declarations**: 2 (both `theorem`, public)  
**Instances**: 0 | **Defs**: 0 | **Lemmas/Theorems**: 2  
**Sorries**: none  
**`set_option maxHeartbeats`**: none  

---

## Declarations

---

### `theorem D_inv_smul`

- **Type**:
  ```lean
  D_inv_smul (f : KE) (hf : f ≠ 0) :
      KaehlerDifferential.D F KE f⁻¹ =
        -(f⁻¹ ^ 2 • KaehlerDifferential.D F KE f)
  ```
- **What**: States the inverse rule for the universal Kähler derivation on the function field of an elliptic curve: `D(f⁻¹) = −f⁻² · D(f)` for any nonzero `f ∈ K(E)`.
- **How**: Differentiates the identity `f · f⁻¹ = 1` using Leibniz (`Derivation.leibniz`) and `Derivation.map_one_eq_zero` to get `f · D(f⁻¹) + f⁻¹ · D(f) = 0`, then solves for `D(f⁻¹)` by a `calc` chain using `smul_smul`, `inv_mul_cancel₀`, and `sq`.
- **Hypotheses**: `F` a field with `DecidableEq` (omitted via `omit`), `E` an elliptic Weierstrass curve; `f ≠ 0`.
- **Uses from project**: `E.FunctionField` (via the `KE` notation alias, defined in `HasseWeil.InvariantDifferential` or an upstream file); no other project-internal declarations are called in the proof body.
- **Used by**: `D_mul_inv_smul` (calls `D_inv_smul E g hg`)
- **Visibility**: public
- **Lines**: 21–32 (proof body: lines 23–32, ~10 lines)
- **Notes**: `omit [DecidableEq F] in` drops the `DecidableEq` instance that is in scope for the variable block but not needed here. Proof is concise; no sorries; no `maxHeartbeats` override.

---

### `theorem D_mul_inv_smul`

- **Type**:
  ```lean
  D_mul_inv_smul (f g : KE) (hg : g ≠ 0) :
      KaehlerDifferential.D F KE (f * g⁻¹) =
        g⁻¹ • KaehlerDifferential.D F KE f +
        f • (-(g⁻¹ ^ 2 • KaehlerDifferential.D F KE g))
  ```
- **What**: The quotient rule for the Kähler derivation: `D(f / g) = g⁻¹ D(f) − f g⁻² D(g)`, expressed via the Leibniz rule applied to `f · g⁻¹` and the previously proved inverse rule.
- **How**: Two-step rewrite: first `Derivation.leibniz` expands `D(f · g⁻¹)` into `f · D(g⁻¹) + g⁻¹ · D(f)`, then `D_inv_smul E g hg` substitutes `D(g⁻¹) = −g⁻² D(g)`, and `add_comm` brings the terms to the stated order.
- **Hypotheses**: Same ambient context as above; `g ≠ 0`.
- **Uses from project**: `D_inv_smul` (from this file).
- **Used by**: unused in this file (leaf declaration; may be consumed by importers).
- **Visibility**: public
- **Lines**: 35–42 (proof body: lines 40–42, 3 lines)
- **Notes**: `omit [DecidableEq F] in` again. Very short proof. No sorries, no heartbeat overrides.

---

## Cross-reference summary

| Caller | Callee (this file) |
|--------|--------------------|
| `D_mul_inv_smul` | `D_inv_smul` |

**Key API** (used by 3+ declarations in this file): none (only 2 declarations total).

**Unused in file** (dead-code candidates within this file): `D_mul_inv_smul` — it calls `D_inv_smul` but nothing in this file calls `D_mul_inv_smul`. Both may be used by importers.

**Long proofs (>30 lines)**: none.
