# Inventory: ./HasseWeil/Curves/PoleOrderParity.lean

**File summary**: 183 lines, 3 theorems, 0 defs, 0 instances.  
Imports: `HasseWeil.Curves.Infinity`, `HasseWeil.Curves.PicZero`.  
Two namespaces: `HasseWeil.Curves.SmoothPlaneCurve` (lines 25–107) and `HasseWeil.Curves` (lines 126–182).

---

## Declarations

### `theorem coordRingImage_ordAtInfty_ne_neg_one`

- **Type**:
  ```
  (u : C.CoordinateRing) (hu : u ≠ 0) :
    C.ordAtInfty (algebraMap C.CoordinateRing C.FunctionField u) ≠ ((-1 : ℤ) : WithTop ℤ)
  ```
- **What**: For any nonzero coordinate-ring element `u`, the order of its function-field image at the point at infinity is never −1. This is the key parity obstruction: the `{1, y}` basis decomposition forces `ord_∞` to be even (from the `p(x)` part) or odd and ≤ −3 (from the `q(x)·y` part), never −1.
- **How**: Decomposes `u = p·1 + q·Y` via `WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq`, then branches on whether `p` and `q` are zero. In the `q ≠ 0, p = 0` case uses `ordAtInfty_mul` + `ordAtInfty_coordYInFunctionField` + `ordAtInfty_algebraMap_polynomial_of_ne_zero`; in the `p ≠ 0, q = 0` case uses `ordAtInfty_algebraMap_polynomial_of_ne_zero`; in the both-nonzero case uses `ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero`. In all cases, arithmetic via `omega` shows the resulting integer cannot equal −1.
- **Hypotheses**: `C` is a smooth plane curve over a field `F` with `C.toAffine.IsElliptic`; `u ≠ 0`.
- **Uses from project**:
  - `WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq` (mathlib/project — basis decomposition)
  - `C.algebraMap_smul_basis_eq` (Infinity.lean)
  - `C.ordAtInfty_mul` (Infinity.lean)
  - `C.coordYInFunctionField_ne_zero` (Infinity.lean)
  - `ordAtInfty_coordYInFunctionField` (Infinity.lean)
  - `C.ordAtInfty_algebraMap_polynomial_of_ne_zero` (Infinity.lean)
  - `C.ordAtInfty_smul_basis_coordinateRing_of_both_ne_zero` (Infinity.lean)
- **Used by**: `funcField_image_ordAtInfty_ne_neg_one` (this file); `coordRingImage_ordAtInfty_ne_neg_one` in `HasseWeil/Hasse/OpenLemmas.lean` (re-statement/use)
- **Visibility**: public
- **Lines**: 38–93, proof length ~52 lines
- **Notes**: Proof > 30 lines. No sorry. No `set_option maxHeartbeats`. The `FaithfulSMul.algebraMap_injective` call at line 61 handles injectivity of `Polynomial F → C.FunctionField`.

---

### `theorem funcField_image_ordAtInfty_ne_neg_one`

- **Type**:
  ```
  (f : C.FunctionField) (hf : f ≠ 0)
  (h_coord : ∃ u : C.CoordinateRing, algebraMap C.CoordinateRing C.FunctionField u = f) :
    C.ordAtInfty f ≠ ((-1 : ℤ) : WithTop ℤ)
  ```
- **What**: The function-field version of the parity obstruction: any nonzero `f` in the function field that lies in the image of the coordinate ring has `ord_∞(f) ≠ −1`.
- **How**: Immediately lifts to the coordinate-ring version by unwrapping the existential hypothesis and applying `coordRingImage_ordAtInfty_ne_neg_one`.
- **Hypotheses**: `C` smooth plane elliptic curve over `F`; `f ≠ 0`; `f` is in the image of the coordinate ring.
- **Uses from project**:
  - `C.coordRingImage_ordAtInfty_ne_neg_one` (this file)
- **Used by**: `point_minus_O_principal_eq_zero_of_coord` (this file, line 179)
- **Visibility**: public
- **Lines**: 97–105, proof length ~8 lines
- **Notes**: No sorry. Short wrapper.

---

### `theorem point_minus_O_principal_eq_zero_of_coord`

- **Type**:
  ```
  (P : W.Point) (f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) (hf : f ≠ 0)
  (h_div : (⟨W⟩ : SmoothPlaneCurve F).projectiveDivisorOf f = kappaDivisor W P)
  (h_coord : ∃ u : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing,
    algebraMap _ (⟨W⟩ : SmoothPlaneCurve F).FunctionField u = f) :
    P = 0
  ```
- **What**: Specialized Silverman III.3.3: if `(P) − (O)` is a principal divisor witnessed by `f` and `f` lies in the coordinate-ring image, then `P = 0`. This is the key step in the A-002/F-001 package (ruling out `(P) − (O)` principal for `P ≠ O`).
- **How**: By contradiction: if `P ≠ 0`, evaluates the divisor equality `h_div` at the point at infinity using `Finsupp.sub_apply` and `Finsupp.single_apply` to derive `projectiveDivisorOf f` at `∞` = −1. Then uses `projectiveDivisorOf_apply_infinity` to convert this to `ordAtInfty f = −1` (handling the `⊤` case via `ordAtInfty_eq_top_iff`). Finally applies `funcField_image_ordAtInfty_ne_neg_one` to get a contradiction.
- **Hypotheses**: `W` an affine Weierstrass elliptic curve over a field with `DecidableEq`; `f ≠ 0`; divisor of `f` equals `kappaDivisor W P`; `f` is in the coordinate-ring image.
- **Uses from project**:
  - `kappaDivisor` (PicZero.lean)
  - `P.toProjectiveSmoothPoint` (project infrastructure)
  - `P.toProjectiveSmoothPoint_toAffinePoint` (project infrastructure)
  - `ProjectiveSmoothPoint.toAffinePoint_infinity` (project infrastructure)
  - `SmoothPlaneCurve.projectiveDivisorOf_apply_infinity` (Infinity.lean)
  - `(⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_eq_top_iff` (Infinity.lean)
  - `(⟨W⟩ : SmoothPlaneCurve F).funcField_image_ordAtInfty_ne_neg_one` (this file)
- **Used by**: `HasseWeil.Curves.AFConditional` (line 145 of `AFConditional.lean`)
- **Visibility**: public
- **Lines**: 139–181, proof length ~42 lines
- **Notes**: Proof > 30 lines. No sorry. No `set_option maxHeartbeats`. The `DecidableEq F` hypothesis in the outer `variable` is needed for `Finsupp` operations. The comment at lines 119–124 explicitly flags the unconditional version (removing `h_coord`) as a separate ~80-150 LOC ticket requiring `IntegralClosure.lean` + `NormValuation.lean` bridges.

---

## Cross-reference summary

| Declaration | Used by (in-file) | Used by (other files) |
|---|---|---|
| `coordRingImage_ordAtInfty_ne_neg_one` | `funcField_image_ordAtInfty_ne_neg_one` | `HasseWeil/Hasse/OpenLemmas.lean` |
| `funcField_image_ordAtInfty_ne_neg_one` | `point_minus_O_principal_eq_zero_of_coord` | (none found) |
| `point_minus_O_principal_eq_zero_of_coord` | (none) | `HasseWeil/Curves/AFConditional.lean` |

**Key API** (used by 2+ declarations in file): `funcField_image_ordAtInfty_ne_neg_one` is used by `point_minus_O_principal_eq_zero_of_coord`; `coordRingImage_ordAtInfty_ne_neg_one` is used by `funcField_image_ordAtInfty_ne_neg_one`.

No declaration in this file has 3+ in-file callers (file has only 3 declarations total).

**Long proofs**: `coordRingImage_ordAtInfty_ne_neg_one` (~52 lines), `point_minus_O_principal_eq_zero_of_coord` (~42 lines).

**Sorries**: none.

**`set_option maxHeartbeats`**: none.
