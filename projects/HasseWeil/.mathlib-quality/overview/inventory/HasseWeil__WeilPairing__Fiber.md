# Inventory: ./HasseWeil/WeilPairing/Fiber.lean

**File purpose:** Group-theoretic foundation for fibres of point-map endomorphisms on an elliptic curve. Establishes that a fibre of an `AddMonoidHom` on `W.Point` is a coset of the kernel, hence finite when the kernel is finite. Referenced by the Weil-pairing and separable-adjoint constructions (Silverman III.4).

**Total declarations:** 3 (1 def, 2 theorems, 0 instances)  
**Sorries:** none  
**Lines:** 51

---

### `def fiberEquivKer`

- **Type**: `(f : W.Point →+ W.Point) → f P₀ = Q → {P : W.Point // f P = Q} ≃ f.ker`
- **What**: Constructs an explicit equivalence between the fibre `{P | f P = Q}` and the kernel of `f`, given a base point `P₀` in the fibre. The bijection sends `P ↦ P − P₀` with inverse `T ↦ P₀ + T`.
- **How**: Direct construction of an `Equiv` using `AddMonoidHom.mem_ker` and `map_sub`/`map_add`; left and right inverses close by `simp`.
- **Hypotheses**: `f` is an `AddMonoidHom` on `W.Point`; `P₀` is a point with `f P₀ = Q`.
- **Uses from project**: none
- **Used by**: `fiber_finite`, `fiber_card_eq_ker_card`
- **Visibility**: public
- **Lines**: 29–34, proof length ~6 lines (inline term-mode)
- **Notes**: none

---

### `theorem fiber_finite`

- **Type**: `(f : W.Point →+ W.Point) → Finite f.ker → (Q : W.Point) → Finite {P : W.Point // f P = Q}`
- **What**: Proves the fibre over any point `Q` is a finite type, provided the kernel is finite. Handles the two cases: nonempty fibre (transported from `fiberEquivKer`) and empty fibre (immediately an `IsEmpty` instance).
- **How**: Uses `Classical.em` to split on existence of a base point; in the nonempty case applies `Finite.of_equiv` via `fiberEquivKer.symm`; in the empty case constructs `IsEmpty` directly and invokes `infer_instance`.
- **Hypotheses**: `f.ker` is finite.
- **Uses from project**: `fiberEquivKer`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 37–42, proof length ~6 lines
- **Notes**: none

---

### `theorem fiber_card_eq_ker_card`

- **Type**: `(f : W.Point →+ W.Point) → f P₀ = Q → Nat.card {P : W.Point // f P = Q} = Nat.card f.ker`
- **What**: Computes the cardinality of a (nonempty) fibre: it equals the cardinality of the kernel. This is the constant-fibre-size fact underlying `deg = #ker` for separable isogenies (Silverman III.4.10c).
- **How**: A one-liner applying `Nat.card_eq_of_bijective` to the bijection `fiberEquivKer f hP₀`.
- **Hypotheses**: There exists a base point `P₀` in the fibre over `Q`.
- **Uses from project**: `fiberEquivKer`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 46–48, proof length ~2 lines
- **Notes**: none

---

## Summary

| Field | Value |
|---|---|
| Total declarations | 3 |
| Defs | 1 |
| Lemmas/Theorems | 2 |
| Instances | 0 |
| Sorries | none |
| `set_option maxHeartbeats` | none |
| Long proofs (>30 lines) | none |
| Key API (used by 3+) | `fiberEquivKer` (used by 2 others — nothing reaches ≥3 in this small file) |
| Unused in file | `fiber_finite`, `fiber_card_eq_ker_card` (both exported API, likely used by other files) |

**Notes:** Minimal self-contained utility file; the three declarations form a clean Silverman-III.4 kernel-coset package with no project imports beyond `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`. No sorries, no heartbeat overrides, no long proofs. Likely consumed by separable-degree and Weil-pairing pullback files elsewhere in the project.
