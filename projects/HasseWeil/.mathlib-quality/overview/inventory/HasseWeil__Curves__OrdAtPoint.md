# Inventory: ./HasseWeil/Curves/OrdAtPoint.lean

**File**: `HasseWeil/Curves/OrdAtPoint.lean`
**Namespace**: `HasseWeil.Curves.SmoothPlaneCurve`
**Imports**: `HasseWeil.Curves.Infinity`, `HasseWeil.Curves.Valuation`, `HasseWeil.Curves.Divisors`
**Total declarations**: 11 (1 def, 10 theorems, 0 instances)
**Sorries**: none
**set_option maxHeartbeats**: none

---

## Purpose

Packages the two specialised order functions (`ordAtInfty` from `Curves/Infinity.lean` and `ord_P` from `Curves/Valuation.lean`) into a single uniform API `ordAtPoint` via a pattern match on `C.toAffine.Point`. All companion lemmas delegate by case-splitting. This is a thin adapter layer; no new mathematics is proven here.

---

## Declarations

### `noncomputable def ordAtPoint`
- **Type**: `(T : C.toAffine.Point) → (f : C.FunctionField) → WithTop ℤ`
- **What**: The order of a function field element `f` at a closed point `T`, uniformly defined: at `.zero` it equals `ordAtInfty f`; at `.some x y h_ns` it equals `ord_P ⟨x, y, h_ns⟩ f`.
- **How**: Direct pattern match; both branches are definitional equalities to the specialized functions `C.ordAtInfty` and `C.ord_P`.
- **Hypotheses**: `C : SmoothPlaneCurve F`, `F` a field.
- **Uses from project**: `ordAtInfty` (Curves/Infinity.lean), `ord_P` (Curves/Valuation.lean)
- **Used by**: `ordAtPoint_zero_eq_ordAtInfty`, `ordAtPoint_some_eq_ord_P`, `ordAtPoint_zero_function`, `ordAtPoint_one`, `ordAtPoint_eq_top_iff`, `ordAtPoint_mul`, `ordAtPoint_add_le`, `ordAtPoint_inv`, `ordAtPoint_algebraMap_F_of_ne_zero`, `ordAtPoint_add_eq_of_lt` (all in this file); heavily used in `Hasse/L6Witnesses.lean`, `Hasse/OpenLemmaPrimitives.lean`, `Hasse/OpenLemmas.lean`
- **Visibility**: public
- **Lines**: 57–61 (proof length: 3 lines)
- **Notes**: none

---

### `@[simp] theorem ordAtPoint_zero_eq_ordAtInfty`
- **Type**: `C.ordAtPoint .zero f = C.ordAtInfty f`
- **What**: Reduction lemma: `ordAtPoint` at the point at infinity equals `ordAtInfty`. This is a definitional equality.
- **How**: `rfl` — both sides reduce to the same term by definition of `ordAtPoint`.
- **Hypotheses**: none beyond type class context.
- **Uses from project**: `ordAtPoint` (this file), `ordAtInfty` (Curves/Infinity.lean)
- **Used by**: unused in this file (consumers: `Hasse/L6Witnesses.lean`, `Hasse/OpenLemmaPrimitives.lean`)
- **Visibility**: public
- **Lines**: 66–67 (proof length: 1 line)
- **Notes**: simp lemma

---

### `@[simp] theorem ordAtPoint_some_eq_ord_P`
- **Type**: `C.ordAtPoint (.some x y h_ns) f = C.ord_P ⟨x, y, h_ns⟩ f`
- **What**: Reduction lemma: `ordAtPoint` at a finite smooth point equals `ord_P`. Definitional equality.
- **How**: `rfl`.
- **Hypotheses**: `h_ns : C.toAffine.Nonsingular x y`.
- **Uses from project**: `ordAtPoint` (this file), `ord_P` (Curves/Valuation.lean)
- **Used by**: unused in this file (consumers: `Hasse/L6Witnesses.lean`, `Hasse/OpenLemmaPrimitives.lean`)
- **Visibility**: public
- **Lines**: 70–72 (proof length: 1 line)
- **Notes**: simp lemma

---

### `@[simp] theorem ordAtPoint_zero_function`
- **Type**: `C.ordAtPoint T 0 = ⊤`
- **What**: The order of the zero function is `⊤` at every closed point — the universal "only zero has infinite order" convention.
- **How**: Case-split on `T`; infinity branch uses `C.ordAtInfty_zero`; finite branch uses `C.ord_P_zero`.
- **Hypotheses**: none.
- **Uses from project**: `ordAtPoint` (this file), `ordAtInfty_zero` (Curves/Infinity.lean), `ord_P_zero` (Curves/Valuation.lean)
- **Used by**: unused in this file (referenced in `Hasse/OpenLemmas.lean` comments)
- **Visibility**: public
- **Lines**: 78–82 (proof length: 4 lines)
- **Notes**: simp lemma

---

### `@[simp] theorem ordAtPoint_one`
- **Type**: `C.ordAtPoint T 1 = 0`
- **What**: The order of the constant function `1` is `0` at every closed point (it is a unit everywhere).
- **How**: Case-split on `T`; infinity branch uses `C.ordAtInfty_one`; finite branch uses `C.ord_P_one`.
- **Hypotheses**: none.
- **Uses from project**: `ordAtPoint` (this file), `ordAtInfty_one` (Curves/Infinity.lean), `ord_P_one` (Curves/Valuation.lean)
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 86–90 (proof length: 4 lines)
- **Notes**: simp lemma

---

### `theorem ordAtPoint_eq_top_iff`
- **Type**: `C.ordAtPoint T f = ⊤ ↔ f = 0`
- **What**: The order of `f` at any closed point `T` is `⊤` if and only if `f = 0`. This is the place-by-place version of the valuation axiom that only zero has infinite valuation.
- **How**: Case-split on `T`; infinity branch uses `C.ordAtInfty_eq_top_iff`; finite branch uses `ord_P_eq_top_iff`.
- **Hypotheses**: none.
- **Uses from project**: `ordAtPoint` (this file), `ordAtInfty_eq_top_iff` (Curves/Infinity.lean), `ord_P_eq_top_iff` (Curves/Valuation.lean)
- **Used by**: unused in this file (referenced in `Hasse/OpenLemmas.lean` comments)
- **Visibility**: public
- **Lines**: 96–100 (proof length: 4 lines)
- **Notes**: none

---

### `theorem ordAtPoint_mul`
- **Type**: `C.ordAtPoint T (f * g) = C.ordAtPoint T f + C.ordAtPoint T g`
- **What**: The order is multiplicative (log of the valuation): `ord_T(fg) = ord_T(f) + ord_T(g)`, uniformly at every closed point.
- **How**: Case-split on `T`. The `.some` branch delegates unconditionally to `C.ord_P_mul`. The `.zero` branch requires `f ≠ 0` and `g ≠ 0` for `C.ordAtInfty_mul`; the degenerate cases `f = 0` or `g = 0` are handled first by `simp` (using `⊤ + _ = ⊤` absorption).
- **Hypotheses**: none (the proof handles `f = 0` and `g = 0` internally).
- **Uses from project**: `ordAtPoint` (this file), `ordAtInfty_mul` (Curves/Infinity.lean), `ord_P_mul` (Curves/Valuation.lean)
- **Used by**: unused in this file (referenced in `Hasse/OpenLemmas.lean` comments)
- **Visibility**: public
- **Lines**: 107–118 (proof length: 11 lines)
- **Notes**: The `.zero` branch needs a manual case-split on `f = 0` / `g = 0` to handle the conditional nature of `ordAtInfty_mul`, while `ord_P_mul` is unconditional.

---

### `theorem ordAtPoint_add_le`
- **Type**: `min (C.ordAtPoint T f) (C.ordAtPoint T g) ≤ C.ordAtPoint T (f + g)`
- **What**: Non-archimedean triangle inequality: the order of a sum is at least the minimum of the orders of the summands, uniformly at every closed point.
- **How**: Case-split on `T`; infinity branch uses `C.ordAtInfty_add_ge_min`; finite branch uses `C.ord_P_add_le`; both via `simpa`.
- **Hypotheses**: none.
- **Uses from project**: `ordAtPoint` (this file), `ordAtInfty_add_ge_min` (Curves/Infinity.lean), `ord_P_add_le` (Curves/Valuation.lean)
- **Used by**: unused in this file (referenced in `Hasse/OpenLemmas.lean` comments)
- **Visibility**: public
- **Lines**: 123–127 (proof length: 4 lines)
- **Notes**: none

---

### `theorem ordAtPoint_inv`
- **Type**: `C.ordAtPoint T f⁻¹ = -(C.ordAtPoint T f)`
- **What**: The order of the inverse is the negation of the order: `ord_T(f⁻¹) = -ord_T(f)`, uniformly at every closed point.
- **How**: Case-split on `T`. Infinity branch uses `C.ordAtInfty_inv` (unconditional). Finite branch uses `C.ord_P_inv` which requires `f ≠ 0`; the `f = 0` case is handled by `simp [inv_zero]`.
- **Hypotheses**: none (the proof handles `f = 0` internally).
- **Uses from project**: `ordAtPoint` (this file), `ordAtInfty_inv` (Curves/Infinity.lean), `ord_P_inv` (Curves/Valuation.lean)
- **Used by**: unused in this file (used in `Hasse/OpenLemmaPrimitives.lean` via `SmoothPlaneCurve.ordAtPoint_inv`)
- **Visibility**: public
- **Lines**: 132–139 (proof length: 7 lines)
- **Notes**: none

---

### `theorem ordAtPoint_algebraMap_F_of_ne_zero`
- **Type**: `(hc : c ≠ 0) → C.ordAtPoint T (algebraMap F C.FunctionField c) = 0`
- **What**: A nonzero constant from the base field `F` has order `0` at every closed point; it is a unit of every local ring.
- **How**: Case-split on `T`; infinity branch uses `C.ordAtInfty_algebraMap_F_nonzero`; finite branch uses `ord_P_algebraMap_F_of_ne_zero`.
- **Hypotheses**: `c ≠ 0`.
- **Uses from project**: `ordAtPoint` (this file), `ordAtInfty_algebraMap_F_nonzero` (Curves/Infinity.lean), `ord_P_algebraMap_F_of_ne_zero` (Curves/Valuation.lean)
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 145–150 (proof length: 5 lines)
- **Notes**: none

---

### `theorem ordAtPoint_add_eq_of_lt`
- **Type**: `(h : C.ordAtPoint T f < C.ordAtPoint T g) → C.ordAtPoint T (f + g) = C.ordAtPoint T f`
- **What**: Strict non-archimedean: when `ord_T(f) < ord_T(g)`, the dominant term wins and `ord_T(f + g) = ord_T(f)`.
- **How**: Case-split on `T`; infinity branch uses `C.ordAtInfty_add_eq_of_lt`; finite branch uses `C.ord_P_add_eq_of_lt`.
- **Hypotheses**: `C.ordAtPoint T f < C.ordAtPoint T g`.
- **Uses from project**: `ordAtPoint` (this file), `ordAtInfty_add_eq_of_lt` (Curves/Infinity.lean), `ord_P_add_eq_of_lt` (Curves/Valuation.lean)
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 156–161 (proof length: 5 lines)
- **Notes**: none

---

## Cross-reference summary

All 10 theorems in this file use `ordAtPoint` (defined in this file) as their primary subject. No theorem in this file references another theorem from this file; each delegates directly to the specialized `ordAtInfty_*` or `ord_P_*` declarations from the imported files.

**Key API (used by 3+ declarations in this file)**:
- `ordAtPoint` — used by all 10 theorems

**Dead-code candidates within this file**: all 10 theorems are referenced only externally (by `Hasse/L6Witnesses.lean`, `Hasse/OpenLemmaPrimitives.lean`, `Hasse/OpenLemmas.lean`).

**Project declarations from imports used in proof bodies**:
- From `Curves/Infinity.lean`: `ordAtInfty`, `ordAtInfty_zero`, `ordAtInfty_one`, `ordAtInfty_eq_top_iff`, `ordAtInfty_mul`, `ordAtInfty_add_ge_min`, `ordAtInfty_inv`, `ordAtInfty_algebraMap_F_nonzero`, `ordAtInfty_add_eq_of_lt`
- From `Curves/Valuation.lean`: `ord_P`, `ord_P_zero`, `ord_P_one`, `ord_P_eq_top_iff`, `ord_P_mul`, `ord_P_add_le`, `ord_P_inv`, `ord_P_algebraMap_F_of_ne_zero`, `ord_P_add_eq_of_lt`
