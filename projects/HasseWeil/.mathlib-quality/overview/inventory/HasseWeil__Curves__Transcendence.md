# Inventory: ./HasseWeil/Curves/Transcendence.lean

**File**: `HasseWeil/Curves/Transcendence.lean`
**Lines**: 151
**Namespace**: `HasseWeil.Curves.SmoothPlaneCurve`
**Imports**: `HasseWeil.Curves.FiniteOverKx`, `HasseWeil.Curves.CurveMap`, `Mathlib.RingTheory.Algebraic.Integral`, `Mathlib.RingTheory.Algebraic.Basic`, `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`

---

## Summary

Four declarations: 2 instances + 1 theorem + 1 theorem. No `sorry`, no `set_option maxHeartbeats`. The file proves three foundational facts about the function field `F(C)` of a smooth plane curve: algebraicity over `F[X]`, integrality over `F(x) = Frac(F[X])`, the non-`p`th-power property of uniformizers, and transcendence degree 1 over `F`. All are axiom-clean. The `isAlgebraic_polynomialX_functionField` and `isIntegral_fracPolynomialX_functionField` instances have no callers within the file (nor apparent callers outside it in the repo); `functionField_trdeg_eq_one` is used by `Differentials.lean`.

---

## Declaration Inventory

---

### `instance isAlgebraic_polynomialX_functionField`

- **Type**: `Algebra.IsAlgebraic (Polynomial F) C.FunctionField`
- **What**: `F(C)` is algebraic over `F[X]` as an algebra; every element of the function field satisfies a nonzero polynomial with coefficients in `F[X]`.
- **How**: Two-step tower: `F[X] → Frac(F[X])` is algebraic by `IsLocalization.isAlgebraic`, and `Frac(F[X]) → F(C)` is algebraic by `Algebra.IsAlgebraic.of_finite` (since `F(C)` is a finite `Frac(F[X])`-module, from `FiniteOverKx`). Transitivity is `Algebra.IsAlgebraic.trans`.
- **Hypotheses**: `F` is a field; `C` is a smooth plane curve over `F` (providing `Module.Finite (FractionRing (Polynomial F)) C.FunctionField` via `FiniteOverKx`).
- **Uses from project**: `C.FunctionField` (type from `SmoothPlaneCurve`); the `Module.Finite` instance comes from `HasseWeil.Curves.FiniteOverKx`.
- **Used by**: unused in file (used transitively by `isIntegral_fracPolynomialX_functionField`; directly by `functionField_trdeg_eq_one`).
- **Visibility**: public
- **Lines**: 50–57 (proof body ~7 lines)
- **Notes**: No `set_option`. No `sorry`. Proof is short and clean.

---

### `instance isIntegral_fracPolynomialX_functionField`

- **Type**: `Algebra.IsIntegral (FractionRing (Polynomial F)) C.FunctionField`
- **What**: `F(C)` is integral over `F(x) = Frac(F[X])`; since `F(x)` is a field and `F(C)/F(x)` is algebraic and finite, every element is integral.
- **How**: Uses `Algebra.IsAlgebraic.of_finite` to obtain `Algebra.IsAlgebraic (FractionRing (Polynomial F)) C.FunctionField` (finite module from `FiniteOverKx`), then applies `Algebra.IsAlgebraic.isIntegral`.
- **Hypotheses**: `F` is a field; `C` is a smooth plane curve (providing `Module.Finite (FractionRing (Polynomial F)) C.FunctionField`).
- **Uses from project**: `C.FunctionField`; `Module.Finite` instance from `HasseWeil.Curves.FiniteOverKx`.
- **Used by**: unused in file; no callers found in the rest of the project.
- **Visibility**: public
- **Lines**: 70–74 (proof body ~4 lines)
- **Notes**: No `set_option`. No `sorry`. The docstring honestly notes that `F[X]` is not a field, so algebraic ≠ integral over `F[X]`, but the instance stated here is over `Frac(F[X])` which is a field, so integrality ≡ algebraicity. Possible dead code if `isAlgebraic_polynomialX_functionField` is the only one downstream needs.

---

### `theorem notMem_pthPowers_of_uniformizer`

- **Type**: `{p : ℕ} → (hp : 1 < p) → {P : C.SmoothPoint} → {t : C.FunctionField} → (ht : Uniformizer C P t) → (f : C.FunctionField) → t ≠ f ^ p`
- **What**: A uniformizer `t` at a smooth point `P` is not a `p`-th power in the function field for any integer `p ≥ 2`. This is (half of) the separability characterization of `F(C)/F(t)` from Silverman II.1.4.
- **How**: Assumes `t = f^p` and derives a contradiction via order arithmetic. The key lemma is `C.ord_P_pow f p : C.ord_P P (f^p) = p • C.ord_P P f` and `C.ord_P P t = 1` from `ht : Uniformizer C P t`. The value `p • n = 1` (with `p ≥ 2`, `n : ℤ`) is impossible by `nlinarith`, after extracting `n` from `WithTop.ne_top_iff_exists` and coercing via `WithTop.coe_nsmul` and `Int.nsmul_eq_mul`.
- **Hypotheses**: `p : ℕ` with `1 < p`; `P : C.SmoothPoint`; `t : C.FunctionField` with `Uniformizer C P t` (meaning `C.ord_P P t = 1` and `t ≠ 0`).
- **Uses from project**: `Uniformizer` (from `HasseWeil.Curves.Valuation`), `C.ord_P` (from `HasseWeil.Curves.Valuation`), `C.ord_P_pow` (from `HasseWeil.Curves.Valuation`), `C.ord_P_eq_top_iff` (from `HasseWeil.Curves.Valuation`).
- **Used by**: unused in file; no callers found in the rest of the project.
- **Visibility**: public
- **Lines**: 85–117 (proof body ~33 lines)
- **Notes**: No `set_option`. No `sorry`. Proof is 33 lines (just over the 30-line threshold). Tagged in the file as `T-II-1-005`. No known callers outside the file; may be parked/experimental pending the full separability characterization.

---

### `theorem functionField_trdeg_eq_one`

- **Type**: `Algebra.trdeg F C.FunctionField = 1`
- **What**: The function field `F(C)` of a smooth plane curve has transcendence degree 1 over the base field `F`.
- **How**: Tower computation via `trdeg_add_eq` applied twice. First: `trdeg F (Polynomial F) = 1` by `Polynomial.trdeg_of_isDomain`; `trdeg (Polynomial F) (Frac(F[X])) = 0` by `trdeg_eq_zero` (using the algebraicity instance from `IsLocalization.isAlgebraic`); so `trdeg F (Frac(F[X])) = 1`. Second: `trdeg (Frac(F[X])) F(C) = 0` by `trdeg_eq_zero` (algebraicity from `Algebra.IsAlgebraic.of_finite`); so `trdeg F F(C) = 1`.
- **Hypotheses**: `F` is a field; `C` is a smooth plane curve (providing `Module.Finite (FractionRing (Polynomial F)) C.FunctionField`).
- **Uses from project**: `C.FunctionField`; `Module.Finite` instance from `HasseWeil.Curves.FiniteOverKx`.
- **Used by**: unused in this file; called by `Differentials.lean` (`weierstrass_functionField_trdeg_eq_one` at line 752, which then feeds `Differentials.lean` lines 859 and 861).
- **Visibility**: public
- **Lines**: 132–146 (proof body ~15 lines)
- **Notes**: No `set_option`. No `sorry`. The key API lemma of this file (cited downstream). The docstring notes the full `CurveMap.pullback_image_finite_codim` (T-II-INFRA-B-009) still needs additional typeclass-plumbing for the subalgebra setting.

---

## Cross-reference summary

| Declaration | Lines | Proof length | Has sorry | maxHeartbeats |
|---|---|---|---|---|
| `isAlgebraic_polynomialX_functionField` | 50–57 | ~7 | No | — |
| `isIntegral_fracPolynomialX_functionField` | 70–74 | ~4 | No | — |
| `notMem_pthPowers_of_uniformizer` | 85–117 | ~33 | No | — |
| `functionField_trdeg_eq_one` | 132–146 | ~15 | No | — |

## Key API (used by 3+ others in this file)
None — the file has only 4 declarations with no intra-file cross-references.

## Unused declarations (dead-code candidates)
- `isAlgebraic_polynomialX_functionField` — no callers found outside this file (instances can be picked up implicitly, but no explicit reference was found)
- `isIntegral_fracPolynomialX_functionField` — no callers found anywhere
- `notMem_pthPowers_of_uniformizer` — no callers found anywhere; tagged T-II-1-005, likely parked pending further separability theory

## Notes
- The file imports `HasseWeil.Curves.CurveMap` but makes no explicit use of `CurveMap` declarations in the proofs; the import is noted in the module doc as providing context for the planned T-II-INFRA-B-009 follow-up.
- `functionField_trdeg_eq_one` is the only declaration actually consumed downstream (via `Differentials.lean`).
- All declarations are axiom-clean (no `sorry`, no `sorryAx`).
