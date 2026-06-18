# Inventory: ./HasseWeil/Curves/SmoothPointTranslate.lean

**File**: `HasseWeil/Curves/SmoothPointTranslate.lean`
**Module**: `HasseWeil.Curves` (namespace `HasseWeil.Curves`, then `SmoothPlaneCurve`, then `SmoothPlaneCurve.Conditional`)
**Imports**: `HasseWeil.Curves.PointFunctor`, `HasseWeil.Curves.Valuation`, `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`
**Total lines**: 332
**Total declarations**: 12 (1 def, 1 noncomputable def, 9 theorems, 1 private theorem)

---

## Section 1 — `Affine.Point.IsSome` predicate (lines 46–64)

### `def _root_.WeierstrassCurve.Affine.Point.IsSome`
- **Type**: `{R : Type*} [CommRing R] {W : Affine R} (P : W.Point) : Prop`
- **What**: Defines the predicate "P is not the identity (point at infinity)" on `WeierstrassCurve.Affine.Point`. Concretely `P ≠ Affine.Point.zero`.
- **How**: Direct definitional unfolding; `P ≠ Affine.Point.zero`.
- **Hypotheses**: `R` a commutative ring, `W : Affine R`.
- **Uses from project**: none.
- **Used by**: `some_isSome`, `zero_not_isSome`, `exists_some_of_isSome`, `translate_of_finite` (via `IsSome` in signature), `translate_of_finite_toAffinePoint`, `translate_of_finite_x`, `translate_of_finite_y`, `translate_of_finite_zero`, all Step B theorems.
- **Visibility**: public (declared in `_root_`)
- **Lines**: 46–49, proof length: 1 line (definitional).
- **Notes**: none.

---

### `@[simp] theorem _root_.WeierstrassCurve.Affine.Point.some_isSome`
- **Type**: `{R : Type*} [CommRing R] {W : Affine R} (x y : R) (h_ns : W.Nonsingular x y) : (Affine.Point.some x y h_ns : W.Point).IsSome`
- **What**: States that `Affine.Point.some x y h_ns` always satisfies `IsSome` (i.e., is never the identity). Marked `@[simp]`.
- **How**: `unfold Affine.Point.IsSome` then `intro h; nomatch h` — the `some` constructor cannot equal `zero` by exhaustive case analysis on the discriminant.
- **Hypotheses**: None beyond `Nonsingular x y`.
- **Uses from project**: `Affine.Point.IsSome` (unfolded).
- **Used by**: unused in file (likely called from other files in the project).
- **Visibility**: public (declared in `_root_`)
- **Lines**: 52–57, proof length: 3 lines.
- **Notes**: none.

---

### `theorem _root_.WeierstrassCurve.Affine.Point.zero_not_isSome`
- **Type**: `{R : Type*} [CommRing R] {W : Affine R} : ¬ ((Affine.Point.zero : W.Point).IsSome)`
- **What**: States that `Affine.Point.zero` does NOT satisfy `IsSome`.
- **How**: `unfold Affine.Point.IsSome; intro h; exact h rfl` — `IsSome zero` expands to `zero ≠ zero`, which `h rfl` contradicts.
- **Hypotheses**: None.
- **Uses from project**: `Affine.Point.IsSome` (unfolded).
- **Used by**: unused in file.
- **Visibility**: public (declared in `_root_`)
- **Lines**: 60–64, proof length: 3 lines.
- **Notes**: none.

---

## Section 2 — `SmoothPoint.translate_of_finite` and coordinate lemmas (lines 80–157)

### `private theorem _root_.WeierstrassCurve.Affine.Point.exists_some_of_isSome`
- **Type**: `{R : Type*} [CommRing R] {W : Affine R} (P : W.Point) (h : P.IsSome) : ∃ x y : R, ∃ h_ns : W.Nonsingular x y, P = Affine.Point.some x y h_ns`
- **What**: Helper: any point satisfying `IsSome` (i.e., not `zero`) has an explicit `(x, y, h_ns)` decomposition. Existential witness extraction.
- **How**: Pattern-matching on `P`: the `zero` case is dismissed by `absurd rfl h`; the `some` case gives the witness directly with `rfl`.
- **Hypotheses**: `P.IsSome`.
- **Uses from project**: `Affine.Point.IsSome`.
- **Used by**: `SmoothPoint.translate_of_finite` (in the body), `SmoothPoint.translate_of_finite_toAffinePoint`.
- **Visibility**: private.
- **Lines**: 80–87, proof length: 4 lines.
- **Notes**: none.

---

### `noncomputable def SmoothPoint.translate_of_finite`
- **Type**: `(P : C.SmoothPoint) (k : C.toAffine.Point) (h : (P.toAffinePoint + k).IsSome) : C.SmoothPoint`
- **What**: Step (A) of the ord-transport arc. Partially translates a smooth point `P` by a group element `k`, conditional on the affine sum `P.toAffinePoint + k` being non-zero, and lifts the result back to a `SmoothPoint`.
- **How**: Uses `exists_some_of_isSome` to extract `(x, y, h_ns)` from the non-zero sum via `Classical.choose`; packages them as a `SmoothPoint` via the anonymous constructor.
- **Hypotheses**: `C` a `SmoothPlaneCurve F` with `IsElliptic`, `h : (P.toAffinePoint + k).IsSome`.
- **Uses from project**: `Affine.Point.exists_some_of_isSome` (private helper in this file).
- **Used by**: `translate_of_finite_toAffinePoint`, `translate_of_finite_x`, `translate_of_finite_y`, `translate_of_finite_zero`, all Step B theorems in `Conditional`.
- **Visibility**: public.
- **Lines**: 95–100, proof length: 2 lines (term-mode).
- **Notes**: `noncomputable` (uses `Classical.choose` via `exists_some_of_isSome`); key API declaration.

---

### `@[simp] theorem SmoothPoint.translate_of_finite_toAffinePoint`
- **Type**: `(P : C.SmoothPoint) (k : C.toAffine.Point) (h : (P.toAffinePoint + k).IsSome) : (P.translate_of_finite k h).toAffinePoint = P.toAffinePoint + k`
- **What**: The `toAffinePoint` of the translated smooth point is exactly the affine group sum `P.toAffinePoint + k`. Simp lemma for unfolding the translation.
- **How**: Unfolds `translate_of_finite`, then recovers the equality from `exists_some_of_isSome`'s `choose_spec` chain (the last component is the equation `P = some x y h_ns`), using `symm`.
- **Hypotheses**: `h : (P.toAffinePoint + k).IsSome`.
- **Uses from project**: `SmoothPoint.translate_of_finite`, `Affine.Point.exists_some_of_isSome`.
- **Used by**: `translate_of_finite_x`, `translate_of_finite_y`, `translate_of_finite_zero`, (Step B theorems implicitly via simp).
- **Visibility**: public.
- **Lines**: 103–110, proof length: 5 lines.
- **Notes**: Key simp lemma; used by 3+ declarations.

---

### `theorem SmoothPoint.translate_of_finite_x`
- **Type**: `(P : C.SmoothPoint) (k : C.toAffine.Point) (h : (P.toAffinePoint + k).IsSome) {x y : F} {h_ns : C.toAffine.Nonsingular x y} (hsum : P.toAffinePoint + k = Affine.Point.some x y h_ns) : (P.translate_of_finite k h).x = x`
- **What**: The x-coordinate of the translated smooth point matches the x-coordinate of the explicit `some x y h_ns` form of the sum, given a proof that the sum equals `some x y h_ns`.
- **How**: Applies `translate_of_finite_toAffinePoint`, rewrites with `hsum`, then extracts the first component of `Affine.Point.some.injEq`.
- **Hypotheses**: An explicit `hsum : P.toAffinePoint + k = Affine.Point.some x y h_ns`.
- **Uses from project**: `SmoothPoint.translate_of_finite_toAffinePoint`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 114–122, proof length: 5 lines.
- **Notes**: none.

---

### `theorem SmoothPoint.translate_of_finite_y`
- **Type**: `(P : C.SmoothPoint) (k : C.toAffine.Point) (h : (P.toAffinePoint + k).IsSome) {x y : F} {h_ns : C.toAffine.Nonsingular x y} (hsum : P.toAffinePoint + k = Affine.Point.some x y h_ns) : (P.translate_of_finite k h).y = y`
- **What**: The y-coordinate of the translated smooth point matches `y` in `some x y h_ns`, given `hsum`. Mirror of `translate_of_finite_x`.
- **How**: Same as `translate_of_finite_x` but extracts the second component (`.2`) of `Affine.Point.some.injEq`.
- **Hypotheses**: Same as `translate_of_finite_x`.
- **Uses from project**: `SmoothPoint.translate_of_finite_toAffinePoint`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 126–134, proof length: 5 lines.
- **Notes**: Direct mirror of `translate_of_finite_x`; potential for a combined lemma.

---

### `@[simp] theorem SmoothPoint.translate_of_finite_zero`
- **Type**: `(P : C.SmoothPoint) (h : (P.toAffinePoint + (0 : C.toAffine.Point)).IsSome) : P.translate_of_finite (0 : C.toAffine.Point) h = P`
- **What**: Translation by the identity element `0 : C.toAffine.Point` is the identity on `SmoothPoint`. Simp lemma.
- **How**: Applies `SmoothPoint.ext` to reduce to x and y equality separately; uses `translate_of_finite_toAffinePoint` + `add_zero` to simplify, then `SmoothPoint.toAffinePoint_def` and `Affine.Point.some.injEq` to extract coordinates.
- **Hypotheses**: `h : (P.toAffinePoint + 0).IsSome` (which requires that `P.toAffinePoint` itself is not zero, i.e., P is not the identity, which is already true for a `SmoothPoint`).
- **Uses from project**: `SmoothPoint.translate_of_finite_toAffinePoint`, `SmoothPoint.ext`, `SmoothPoint.toAffinePoint_def`.
- **Used by**: `comap_pointValuation_refl_eq` (in `Conditional`).
- **Visibility**: public.
- **Lines**: 141–157, proof length: 14 lines.
- **Notes**: none.

---

## Section 3 — Step (B) Conditional: pointValuation transport (lines 196–326)

*All declarations in `namespace SmoothPlaneCurve.Conditional`.*

### `theorem pointValuation_translate_of_smul_eq_of_transport_witness`
- **Type**: `{P : C.SmoothPoint} {k : C.toAffine.Point} {h : (P.toAffinePoint + k).IsSome} (τ_k : C.FunctionField ≃+* C.FunctionField) (f : C.FunctionField) (h_eq : (C.pointValuation P).comap τ_k.toRingHom f = C.pointValuation (P.translate_of_finite k h) f) : C.pointValuation P (τ_k f) = C.pointValuation (P.translate_of_finite k h) f`
- **What**: Step (B) Conditional: given a pointwise maximal-ideal-transport witness `h_eq`, concludes the pointValuation transport identity `pointValuation P (τ_k f) = pointValuation (P.translate_of_finite k h) f`. The key observation is that `(comap τ_k v) f = v (τ_k f)` by definition.
- **How**: The proof is `exact h_eq` — the hypothesis is definitionally equal to the conclusion because `Valuation.comap` is defined pointwise as `v (τ_k f)`.
- **Hypotheses**: Pointwise transport hypothesis `h_eq` at a fixed `f`.
- **Uses from project**: `SmoothPoint.translate_of_finite` (in type); `C.pointValuation` (from `HasseWeil.Curves.Valuation`).
- **Used by**: `pointValuation_translate_of_smul_eq_of_valuation_witness` (calls this).
- **Visibility**: public.
- **Lines**: 208–219, proof length: 3 lines (including comment).
- **Notes**: The 1-line proof `exact h_eq` reflects that `Valuation.comap` unfolds definitionally.

---

### `theorem comap_pointValuation_eq_of_pointwise_transport`
- **Type**: `{P : C.SmoothPoint} {k : C.toAffine.Point} {h : (P.toAffinePoint + k).IsSome} (τ_k : C.FunctionField ≃+* C.FunctionField) (h_eq : ∀ f, (C.pointValuation P).comap τ_k.toRingHom f = C.pointValuation (P.translate_of_finite k h) f) : (C.pointValuation P).comap τ_k.toRingHom = C.pointValuation (P.translate_of_finite k h)`
- **What**: Step (B') upgrade: a pointwise transport hypothesis for all `f` upgrades to a Valuation equality, via `Valuation.ext`.
- **How**: Direct application of `Valuation.ext h_eq` (mathlib).
- **Hypotheses**: Universal pointwise transport `∀ f, ...`.
- **Uses from project**: `SmoothPoint.translate_of_finite` (in type); `C.pointValuation`.
- **Used by**: unused in file (provides the reverse direction; no internal caller).
- **Visibility**: public.
- **Lines**: 255–263, proof length: 2 lines.
- **Notes**: Thin wrapper over `Valuation.ext`; exposed as a named interface lemma.

---

### `theorem pointwise_transport_of_comap_pointValuation_eq`
- **Type**: `{P : C.SmoothPoint} {k : C.toAffine.Point} {h : (P.toAffinePoint + k).IsSome} (τ_k : C.FunctionField ≃+* C.FunctionField) (h_val_eq : (C.pointValuation P).comap τ_k.toRingHom = C.pointValuation (P.translate_of_finite k h)) (f : C.FunctionField) : (C.pointValuation P).comap τ_k.toRingHom f = C.pointValuation (P.translate_of_finite k h) f`
- **What**: Step (B') downgrade: a Valuation equality gives the pointwise transport identity at every fixed `f`. The converse direction to `comap_pointValuation_eq_of_pointwise_transport`.
- **How**: `rw [h_val_eq]` — rewrites the LHS valuation to the RHS.
- **Hypotheses**: Valuation equality `h_val_eq`.
- **Uses from project**: `SmoothPoint.translate_of_finite` (in type); `C.pointValuation`.
- **Used by**: `pointValuation_translate_of_smul_eq_of_valuation_witness` (called at line 301).
- **Visibility**: public.
- **Lines**: 267–276, proof length: 2 lines.
- **Notes**: none.

---

### `theorem pointValuation_translate_of_smul_eq_of_valuation_witness`
- **Type**: `{P : C.SmoothPoint} {k : C.toAffine.Point} {h : (P.toAffinePoint + k).IsSome} (τ_k : C.FunctionField ≃+* C.FunctionField) (h_val_eq : (C.pointValuation P).comap τ_k.toRingHom = C.pointValuation (P.translate_of_finite k h)) (f : C.FunctionField) : C.pointValuation P (τ_k f) = C.pointValuation (P.translate_of_finite k h) f`
- **What**: Step (B') Conditional Valuation form: stronger formulation of Step (B) Conditional. Takes the Valuation equality (one equation, no quantifier) and discharges the pointwise transport identity for any `f`.
- **How**: Chains `pointValuation_translate_of_smul_eq_of_transport_witness` and `pointwise_transport_of_comap_pointValuation_eq` (both from this file).
- **Hypotheses**: Valuation equality `h_val_eq : (C.pointValuation P).comap τ_k.toRingHom = C.pointValuation (P.translate_of_finite k h)`.
- **Uses from project**: `pointValuation_translate_of_smul_eq_of_transport_witness`, `pointwise_transport_of_comap_pointValuation_eq` (both in this file); `C.pointValuation`.
- **Used by**: unused in file (the main export for external callers).
- **Visibility**: public.
- **Lines**: 291–301, proof length: 3 lines.
- **Notes**: Main Step (B') export; combines the two helper directions.

---

### `theorem comap_pointValuation_refl_eq`
- **Type**: `(P : C.SmoothPoint) (h : (P.toAffinePoint + (0 : C.toAffine.Point)).IsSome) : (C.pointValuation P).comap (RingEquiv.refl C.FunctionField).toRingHom = C.pointValuation (P.translate_of_finite (0 : C.toAffine.Point) h)`
- **What**: Base case: when the ring automorphism is `RingEquiv.refl` (trivial translation by 0), the valuation comap is the identity, proved via `Valuation.comap_id`. The `P.translate_of_finite 0 h = P` simp lemma closes the goal.
- **How**: Rewrites `translate_of_finite_zero` (simp), changes to `Valuation.comap (RingHom.id _)`, then applies `Valuation.comap_id` (mathlib).
- **Hypotheses**: `h : (P.toAffinePoint + 0).IsSome`.
- **Uses from project**: `SmoothPoint.translate_of_finite_zero`, `C.pointValuation`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 317–325, proof length: 5 lines.
- **Notes**: none.

---

## Summary table

| # | Kind | Name | Lines | Proof LOC | Sorry |
|---|------|------|-------|-----------|-------|
| 1 | def | `Affine.Point.IsSome` | 46–49 | 1 | no |
| 2 | @[simp] theorem | `Affine.Point.some_isSome` | 52–57 | 3 | no |
| 3 | theorem | `Affine.Point.zero_not_isSome` | 60–64 | 3 | no |
| 4 | private theorem | `Affine.Point.exists_some_of_isSome` | 80–87 | 4 | no |
| 5 | noncomputable def | `SmoothPoint.translate_of_finite` | 95–100 | 2 | no |
| 6 | @[simp] theorem | `SmoothPoint.translate_of_finite_toAffinePoint` | 103–110 | 5 | no |
| 7 | theorem | `SmoothPoint.translate_of_finite_x` | 114–122 | 5 | no |
| 8 | theorem | `SmoothPoint.translate_of_finite_y` | 126–134 | 5 | no |
| 9 | @[simp] theorem | `SmoothPoint.translate_of_finite_zero` | 141–157 | 14 | no |
| 10 | theorem | `pointValuation_translate_of_smul_eq_of_transport_witness` | 208–219 | 3 | no |
| 11 | theorem | `comap_pointValuation_eq_of_pointwise_transport` | 255–263 | 2 | no |
| 12 | theorem | `pointwise_transport_of_comap_pointValuation_eq` | 267–276 | 2 | no |
| 13 | theorem | `pointValuation_translate_of_smul_eq_of_valuation_witness` | 291–301 | 3 | no |
| 14 | theorem | `comap_pointValuation_refl_eq` | 317–325 | 5 | no |

**Totals**: 14 declarations (2 defs, 12 theorems/lemmas, 0 instances); 0 sorries; 0 `set_option maxHeartbeats`; 0 proofs >30 lines.

**Key API** (used by 3+ others in file): `SmoothPoint.translate_of_finite_toAffinePoint` (used by `translate_of_finite_x`, `translate_of_finite_y`, `translate_of_finite_zero`).

**Unused in file**: `some_isSome`, `zero_not_isSome`, `translate_of_finite_x`, `translate_of_finite_y`, `comap_pointValuation_eq_of_pointwise_transport`, `pointValuation_translate_of_smul_eq_of_valuation_witness`, `comap_pointValuation_refl_eq` — all are likely consumed by other project files.

**Notes**: This file is a clean, modular Step (A)+(B) scaffold for the ord-transport arc (no sorries, no heartbeat bumps). The `Conditional` namespace wraps the Step (B) theorems as witness-parametric stubs, deferring the substantive geometric content (maximal-ideal-transport for `translateAlgEquivOfPoint`) to subsequent files. The `translate_of_finite_x` / `translate_of_finite_y` pair is a mild duplication pattern (differ only in `.1` vs `.2` projection).
