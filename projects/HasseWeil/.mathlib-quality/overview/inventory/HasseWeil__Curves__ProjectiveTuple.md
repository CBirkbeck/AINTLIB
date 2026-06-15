# Inventory: ./HasseWeil/Curves/ProjectiveTuple.lean

**File**: `HasseWeil/Curves/ProjectiveTuple.lean`
**Lines**: 1–79
**Imports**: `HasseWeil.Curves.Valuation`, `Mathlib.LinearAlgebra.Projectivization.Basic`
**Module doc**: Defines projective tuples on smooth plane curves — the algebraic model of rational maps `C ⇢ ℙᴺ`. References Silverman I.3.

---

## Declarations

### `def ProjectiveTuple`

- **Type**: `(C : SmoothPlaneCurve F) → (N : ℕ) → Type _`
- **What**: Defines a projective tuple of length `N + 1` on a smooth plane curve `C` as the projective space `ℙ K(C) (Fin (N + 1) → K(C))`. This is the algebraic encoding of a rational map `C ⇢ ℙᴺ`.
- **How**: Pure `def`; unfolds to `Projectivization C.FunctionField (Fin (N + 1) → C.FunctionField)` from Mathlib.
- **Hypotheses**: `F` is a field; `C` is a smooth plane curve over `F`.
- **Uses from project**: `SmoothPlaneCurve.FunctionField` (via `C.FunctionField`)
- **Used by**: `mk`, `repr`, `repr_ne_zero`, `mk_repr`, `mk_eq_mk_iff`, `mk_smul` (all in this file); also used in `HasseWeil/Curves/RationalMap.lean`
- **Visibility**: public
- **Lines**: 34–35, definition body 1 line
- **Notes**: None.

---

### `noncomputable def mk`

- **Type**: `(f : Fin (N + 1) → C.FunctionField) → (hf : f ≠ 0) → ProjectiveTuple C N`
- **What**: Constructs a projective tuple from a nonzero `(N+1)`-tuple of function-field elements by quotienting via `Projectivization.mk`.
- **How**: Direct delegation to `Projectivization.mk C.FunctionField f hf`.
- **Hypotheses**: `f` is a nonzero tuple of elements of `C.FunctionField`.
- **Uses from project**: `ProjectiveTuple` (unfolded)
- **Used by**: `mk_repr`, `mk_eq_mk_iff`, `mk_smul` (all in this file)
- **Visibility**: public
- **Lines**: 43–45, proof length: 1 line (term-mode)
- **Notes**: Marked `noncomputable` because `FunctionField` / `Projectivization` involve classical choice.

---

### `noncomputable def repr`

- **Type**: `(φ : ProjectiveTuple C N) → Fin (N + 1) → C.FunctionField`
- **What**: Chooses a canonical nonzero representative tuple for a projective tuple, via `Projectivization.rep`.
- **How**: Direct delegation to `Projectivization.rep φ`.
- **Hypotheses**: None beyond `φ : ProjectiveTuple C N`.
- **Uses from project**: `ProjectiveTuple` (unfolded)
- **Used by**: `repr_ne_zero`, `mk_repr` (in this file)
- **Visibility**: public
- **Lines**: 48–50, proof length: 1 line (term-mode)
- **Notes**: `noncomputable` for the same reason as `mk`.

---

### `theorem repr_ne_zero`

- **Type**: `(φ : ProjectiveTuple C N) → φ.repr ≠ 0`
- **What**: The chosen representative of any projective tuple is nonzero.
- **How**: Direct application of `Projectivization.rep_nonzero φ`.
- **Hypotheses**: None.
- **Uses from project**: `repr`
- **Used by**: `mk_repr` (in this file)
- **Visibility**: public
- **Lines**: 52–53, proof length: 1 line (term-mode)
- **Notes**: None.

---

### `@[simp] theorem mk_repr`

- **Type**: `(φ : ProjectiveTuple C N) → mk φ.repr φ.repr_ne_zero = φ`
- **What**: Round-trip lemma: constructing a projective tuple from its own representative recovers the original. Tagged `@[simp]`.
- **How**: Direct application of `Projectivization.mk_rep φ`.
- **Hypotheses**: None.
- **Uses from project**: `mk`, `repr`, `repr_ne_zero`
- **Used by**: unused in file (likely used externally in `RationalMap.lean`)
- **Visibility**: public
- **Lines**: 55–57, proof length: 1 line (term-mode)
- **Notes**: `@[simp]` attribute registered.

---

### `theorem mk_eq_mk_iff`

- **Type**: `{f g : Fin (N + 1) → C.FunctionField} → (hf : f ≠ 0) → (hg : g ≠ 0) → (mk f hf = mk g hg ↔ ∃ a : C.FunctionFieldˣ, a • g = f)`
- **What**: Two tuples define the same projective tuple if and only if they are related by scalar multiplication by a unit of `K(C)`. This is the equivalence relation defining projective space.
- **How**: Direct application of `Projectivization.mk_eq_mk_iff C.FunctionField f g hf hg`.
- **Hypotheses**: Both `f` and `g` are nonzero.
- **Uses from project**: `mk`
- **Used by**: `mk_smul` (in this file)
- **Visibility**: public
- **Lines**: 61–64, proof length: 1 line (term-mode)
- **Notes**: None.

---

### `theorem mk_smul`

- **Type**: `(f : Fin (N + 1) → C.FunctionField) → (hf : f ≠ 0) → (a : C.FunctionFieldˣ) → mk ((a : C.FunctionField) • f) (smul_ne_zero_iff.mpr ⟨a.ne_zero, hf⟩) = mk f hf`
- **What**: Scaling a representative tuple by a unit of `K(C)` yields the same projective tuple. This directly embodies the projective equivalence relation.
- **How**: Uses `mk_eq_mk_iff` with the witness `⟨a, rfl⟩`.
- **Hypotheses**: `f` is nonzero, `a` is a unit of `C.FunctionField`.
- **Uses from project**: `mk`, `mk_eq_mk_iff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 68–72, proof length: 1 line (term-mode)
- **Notes**: None.

---

## Summary

| Metric | Value |
|--------|-------|
| Total declarations | 7 |
| `def` / `noncomputable def` | 3 |
| `theorem` | 4 |
| Instances | 0 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |
| Long proofs (>30 lines) | 0 |
| Key API (used by 3+) | `ProjectiveTuple` (used by all 6 downstream decls) |
| Unused in file | `mk_repr`, `mk_smul` |

**Notes**: This is a thin, infrastructure-only wrapper around Mathlib's `Projectivization`. Every proof is a one-line delegation. The file is consumed by `HasseWeil/Curves/RationalMap.lean`. No sorries, no heartbeat overrides, no experimental content.
