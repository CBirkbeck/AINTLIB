# Inventory: ./HasseWeil/Curves/RationalMap.lean

File: `HasseWeil/Curves/RationalMap.lean`
Lines: 1–119 (module preamble + 4 declarations)
Import: `HasseWeil.Curves.ProjectiveTuple`
Namespace: `HasseWeil.Curves.SmoothPlaneCurve.ProjectiveTuple`

---

## Declaration Inventory

---

### `def IsRegularAt`

- **Type**: `(φ : ProjectiveTuple C N) → (P : C.SmoothPoint) → Prop`
- **What**: Predicates that a projective tuple `φ` is *regular* at a smooth point `P`: there exists a representative `f : Fin (N+1) → C.FunctionField` with `φ = [f₀:…:f_N]` such that every `ord_P(f_i) ≥ 0` and some `ord_P(f_j) = 0`.
- **How**: Pure existential definition; no proof content.
- **Hypotheses**: `F : Field`, `C : SmoothPlaneCurve F`, `N : ℕ` (implicit variables).
- **Uses from project**: `ProjectiveTuple.mk`, `SmoothPlaneCurve.ord_P`
- **Used by**: `isRegularAt_of_smooth` (consumes this type), `IsMorphism` (universally quantifies over it)
- **Visibility**: public
- **Lines**: 36–41, definitional (no proof)
- **Notes**: None.

---

### `def IsMorphism`

- **Type**: `(φ : ProjectiveTuple C N) → Prop`
- **What**: A projective tuple `φ` is a *morphism* `C → ℙᴺ` if it is regular at every smooth point of `C`.
- **How**: One-line universal quantification over `IsRegularAt`.
- **Hypotheses**: Same as `IsRegularAt`.
- **Uses from project**: `IsRegularAt`
- **Used by**: `isMorphism_of_smooth`
- **Visibility**: public
- **Lines**: 44–45, definitional (no proof)
- **Notes**: None.

---

### `theorem mk_smul_eq_mk`

- **Type**: `(s : C.FunctionField) → (hs : s ≠ 0) → (f : Fin (N + 1) → C.FunctionField) → (hf : f ≠ 0) → mk (fun i => s * f i) _ = mk f hf`
- **What**: Scaling a representative tuple by a nonzero scalar `s` does not change the projective equivalence class: `[s·f₀ : … : s·f_N] = [f₀ : … : f_N]`.
- **How**: Applies `mk_eq_mk_iff` from `ProjectiveTuple` and supplies the witness `Units.mk0 s hs` as the scalar unit; `funext` produces the coordinatewise identity `s * f i = s * f i`.
- **Hypotheses**: `s ≠ 0`, `f ≠ 0`.
- **Uses from project**: `ProjectiveTuple.mk_eq_mk_iff`
- **Used by**: `isRegularAt_of_smooth` (used to identify the scaled representative with `φ`)
- **Visibility**: public
- **Lines**: 51–56, proof length 3 lines
- **Notes**: None.

---

### `theorem isRegularAt_of_smooth`

- **Type**: `(φ : ProjectiveTuple C N) → (P : C.SmoothPoint) → φ.IsRegularAt P`
- **What**: Silverman II.2.1 — every rational map from a smooth plane curve to projective space is regular at every smooth point. The proof constructs an explicit "normalized" representative by scaling `φ.repr` by an element of valuation `−m`, where `m = min_i ord_P(repr i)`.
- **How**: (1) Applies `Finset.exists_min_image` to find the index `j` minimizing `ord_P(repr i)` over all `i`. (2) Shows `repr j ≠ 0` (else all components are zero by minimality and `ord_P_eq_top_iff`). (3) Extracts `m = ord_P(repr j) : ℤ` via `WithTop.coe_untop`. (4) Calls `Uniformizer.exists_ord_P_eq (-m)` (from `Valuation.lean`) to produce `s` with `ord_P s = -m`. (5) Verifies the three conditions: representative equality via `mk_smul_eq_mk`, lower bound via `ord_P_mul` + `WithTop.coe_le_coe` + `omega`, and zero-equality at `j` via `ord_P_mul` + arithmetic.
- **Hypotheses**: None beyond the ambient `Field F`, `C : SmoothPlaneCurve F`.
- **Uses from project**: `ProjectiveTuple.repr_ne_zero`, `ProjectiveTuple.mk_repr`, `SmoothPlaneCurve.exists_uniformizer`, `SmoothPlaneCurve.ord_P_eq_top_iff`, `SmoothPlaneCurve.ord_P_mul`, `Uniformizer.exists_ord_P_eq`, `mk_smul_eq_mk`
- **Used by**: `isMorphism_of_smooth`
- **Visibility**: public
- **Lines**: 63–108, proof length 45 lines
- **Notes**: Proof exceeds 30 lines. No `sorry`. No `set_option maxHeartbeats`. The key mathematical content is in the minimality argument and the `WithTop`/`omega` arithmetic to prove `0 ≤ -m + k`.

---

### `theorem isMorphism_of_smooth`

- **Type**: `(φ : ProjectiveTuple C N) → φ.IsMorphism`
- **What**: Corollary: every rational map from a smooth plane curve to projective space is a morphism (regular at every smooth point).
- **How**: One-liner: unfolds `IsMorphism` and applies `isRegularAt_of_smooth` pointwise.
- **Hypotheses**: None beyond ambient variables.
- **Uses from project**: `isRegularAt_of_smooth`
- **Used by**: unused in this file (intended for downstream consumers)
- **Visibility**: public
- **Lines**: 112–113, proof length 1 line
- **Notes**: Not referenced within this file; likely the main export for downstream use.

---

## Summary

| Name | Kind | Lines | Sorry | Notes |
|---|---|---|---|---|
| `IsRegularAt` | def | 36–41 | No | |
| `IsMorphism` | def | 44–45 | No | |
| `mk_smul_eq_mk` | theorem | 51–56 | No | |
| `isRegularAt_of_smooth` | theorem | 63–108 | No | >30 lines |
| `isMorphism_of_smooth` | theorem | 112–113 | No | unused in file |

**Total declarations**: 5 (2 defs, 3 theorems/lemmas, 0 instances)

**Key API used by ≥3 other declarations in this file**: none (each is used by at most 2 others).

**Long proofs (>30 lines)**: `isRegularAt_of_smooth` (45 lines).

**Unused in file**: `isMorphism_of_smooth` (not called by anything else in this file).
