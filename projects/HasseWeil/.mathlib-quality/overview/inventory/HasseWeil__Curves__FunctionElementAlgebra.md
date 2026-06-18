# Inventory: ./HasseWeil/Curves/FunctionElementAlgebra.lean

**File**: `HasseWeil/Curves/FunctionElementAlgebra.lean`
**Lines**: 121
**Imports**: `HasseWeil.Curves.FiniteOverKx`, `Mathlib.RingTheory.Polynomial.Basic`
**Namespace**: `HasseWeil.Curves.SmoothPlaneCurve`
**Module doc**: Foundational algebra-structure piece for Computation A — equips `K(C)` with a `Polynomial F`-algebra structure via `Y ↦ f` for an arbitrary function element `f`, parallel to the standard `coordX`-based algebra.

---

## Declarations

---

### `noncomputable def algebraOfFunctionElement`

- **Type**: `(f : C.FunctionField) : Algebra (Polynomial F) C.FunctionField`
- **What**: Equips the function field `K(C)` with a `Polynomial F`-algebra structure by sending the polynomial indeterminate to the function element `f`, via `Polynomial.aeval f`.
- **How**: Constructs the algebra from `(Polynomial.aeval f : Polynomial F →ₐ[F] C.FunctionField).toRingHom.toAlgebra`. This is a definitional construction; no proof steps.
- **Hypotheses**: `C : SmoothPlaneCurve F`, `f : C.FunctionField`, `F` a field.
- **Uses from project**: `C.FunctionField` (implicit via `SmoothPlaneCurve`)
- **Used by**: `algebraOfFunctionElement_algebraMap`, `algebraOfFunctionElement_X`, `algebraOfFunctionElement_injective`, `algebraOfFunctionElement_coordX_agrees` (all via `letI`)
- **Visibility**: public (tagged `@[reducible]`)
- **Lines**: 46–48, proof length 1 line (term-mode definition)
- **Notes**: Tagged `@[reducible]` so that downstream `letI` introductions are transparent to unification. Annotated `noncomputable` because `FunctionField` is noncomputable.

---

### `@[simp] theorem algebraOfFunctionElement_algebraMap`

- **Type**: `(f : C.FunctionField) (p : Polynomial F) : letI := algebraOfFunctionElement C f; algebraMap (Polynomial F) C.FunctionField p = Polynomial.aeval f p`
- **What**: States that under `algebraOfFunctionElement f`, the `algebraMap` from `Polynomial F` to `K(C)` is exactly `Polynomial.aeval f`. This is definitional.
- **How**: Proved by `rfl` — the identity is definitional from the construction.
- **Hypotheses**: None beyond the variable context.
- **Uses from project**: `algebraOfFunctionElement`
- **Used by**: Intended for downstream consumers (not referenced within this file by other declarations); unused in file.
- **Visibility**: public (tagged `@[simp]`)
- **Lines**: 52–55, proof length 1 line (`rfl`)
- **Notes**: `@[simp]` tag makes this a simp lemma. Proof is definitional.

---

### `@[simp] theorem algebraOfFunctionElement_X`

- **Type**: `(f : C.FunctionField) : letI := algebraOfFunctionElement C f; algebraMap (Polynomial F) C.FunctionField Polynomial.X = f`
- **What**: Under `algebraOfFunctionElement f`, the image of the polynomial indeterminate `X` is exactly `f`. This is the key "indeterminate maps to generator" fact.
- **How**: Reduces via `show` to `Polynomial.aeval f Polynomial.X = f`, then closes with `Polynomial.aeval_X f` from Mathlib.
- **Hypotheses**: None beyond the variable context.
- **Uses from project**: `algebraOfFunctionElement`
- **Used by**: Unused in this file (intended for downstream).
- **Visibility**: public (tagged `@[simp]`)
- **Lines**: 58–62, proof length 3 lines
- **Notes**: Uses `Polynomial.aeval_X` from Mathlib. Straightforward.

---

### `theorem algebraOfFunctionElement_injective`

- **Type**: `(f : C.FunctionField) (hf : Transcendental F f) : letI := algebraOfFunctionElement C f; Function.Injective (algebraMap (Polynomial F) C.FunctionField)`
- **What**: The algebra map `Polynomial F → K(C)` induced by `algebraOfFunctionElement f` is injective when `f` is transcendental over `F`.
- **How**: Reduces via `show` to injectivity of `(Polynomial.aeval f).toRingHom`, then rewrites `hf` using `transcendental_iff_injective` (Mathlib) via `rwa`.
- **Hypotheses**: `f` transcendental over `F` (i.e., `Transcendental F f`).
- **Uses from project**: `algebraOfFunctionElement`
- **Used by**: Unused in this file (intended for downstream).
- **Visibility**: public
- **Lines**: 71–76, proof length 4 lines
- **Notes**: Uses `transcendental_iff_injective` from Mathlib. Essentially a direct unfolding.

---

### `theorem aeval_injective_of_transcendental`

- **Type**: `(f : C.FunctionField) (hf : Transcendental F f) : Function.Injective (Polynomial.aeval f : Polynomial F → C.FunctionField)`
- **What**: The ring map `Polynomial.aeval f : Polynomial F → K(C)` is injective when `f` is transcendental. A direct variant of `algebraOfFunctionElement_injective` stated without the algebra-structure wrapper.
- **How**: Same as above: `rwa [transcendental_iff_injective] at hf`.
- **Hypotheses**: `f` transcendental over `F`.
- **Uses from project**: (none — no project-specific declarations referenced; uses `C.FunctionField` only as a type)
- **Used by**: Unused in this file (intended for downstream).
- **Visibility**: public
- **Lines**: 80–83, proof length 2 lines
- **Notes**: Largely duplicates `algebraOfFunctionElement_injective`'s mathematical content; the distinction is that this version expresses the conclusion directly on `Polynomial.aeval f` rather than on the `algebraMap` of a `letI`-introduced instance.

---

### `theorem algebraOfFunctionElement_coordX_agrees`

- **Type**: `(p : Polynomial F) : letI := algebraOfFunctionElement C C.coordX; algebraMap (Polynomial F) C.FunctionField p = algebraMap (Polynomial F) C.FunctionField p`
- **What**: Sanity-check / specialisation: when `f = C.coordX`, the `algebraOfFunctionElement` algebra map agrees with itself. The statement is tautologically `rfl`.
- **How**: `rfl` — both sides are literally identical.
- **Hypotheses**: None.
- **Uses from project**: `algebraOfFunctionElement`, `C.coordX`
- **Used by**: Unused in this file.
- **Visibility**: public
- **Lines**: 93–96, proof length 1 line
- **Notes**: The theorem as stated is a tautology (LHS = RHS definitionally); the intended content — that `algebraOfFunctionElement C C.coordX` recovers the project's standard algebra instance — is not actually expressed. This is a placeholder / partial sanity check that may need to be strengthened to a genuine interoperability lemma.

---

## Cross-reference summary

| Caller \ Callee              | `algebraOfFunctionElement` | `algebraOfFunctionElement_algebraMap` | `algebraOfFunctionElement_X` | `algebraOfFunctionElement_injective` | `aeval_injective_of_transcendental` | `algebraOfFunctionElement_coordX_agrees` |
|-|-|-|-|-|-|-|
| `algebraOfFunctionElement_algebraMap` | ✓ | — | — | — | — | — |
| `algebraOfFunctionElement_X`          | ✓ | — | — | — | — | — |
| `algebraOfFunctionElement_injective`  | ✓ | — | — | — | — | — |
| `algebraOfFunctionElement_coordX_agrees` | ✓ | — | — | — | — | — |

`algebraOfFunctionElement` is used by 4 other declarations in this file — it is the key API.

All five non-def declarations are unused within this file by any other declaration in the file; they are all leaf exports.

---

## Summary statistics

- **Total declarations**: 6 (1 def + 5 theorems)
- **Defs**: 1
- **Lemmas/theorems**: 5
- **Instances**: 0
- **Sorries**: none
- **`set_option maxHeartbeats`**: none
- **Long proofs (>30 lines)**: none (longest proof is 4 lines)
- **Key API** (used by 3+ others in file): `algebraOfFunctionElement` (used by 4)
- **Unused in file**: `algebraOfFunctionElement_algebraMap`, `algebraOfFunctionElement_X`, `algebraOfFunctionElement_injective`, `aeval_injective_of_transcendental`, `algebraOfFunctionElement_coordX_agrees` — all five theorems are dead code within this file; they export to future downstream files.
- **Notable**: `algebraOfFunctionElement_coordX_agrees` is a tautology as stated; `aeval_injective_of_transcendental` largely duplicates `algebraOfFunctionElement_injective`. The file is a stub/foundation for the Computation A arc (multi-session, deferred).
