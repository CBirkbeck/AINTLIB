# Inventory: ./HasseWeil/Endomorphism.lean

File: `HasseWeil/Endomorphism.lean` (175 lines)
Import: `HasseWeil.Basic`
Namespace: `HasseWeil`

This file defines the trace of an endomorphism isogeny and provides concrete
"scalar" specializations of `1 - [m]` and `r·[m] - s` (which reduce to
`[1-m]` and `[rm-s]` respectively), together with the degree quadratic form
identity for the mulByInt case (Silverman III.6.3, unconditional special case).

---

## Section `ScalarPullbacks`

Variable context: `{W : WeierstrassCurve F}`, `[W.toAffine.IsElliptic]`.

---

### `noncomputable def isogOneSub_mulByInt`

- **Type**: `(n : ℤ) → Isogeny W.toAffine W.toAffine`
- **What**: Defines the isogeny `1 - [n]` concretely as `[1-n]` (i.e., `mulByInt W (1-n)`), providing a genuine function-field pullback via division polynomials.
- **How**: Pure definitional unfolding — body is `mulByInt W (1 - n)`. No proof needed.
- **Hypotheses**: `W.toAffine.IsElliptic`
- **Uses from project**: `mulByInt` (from `Basic.lean`)
- **Used by**: `isogOneSub_mulByInt_pullback`, `isogOneSub_mulByInt_degree`
- **Visibility**: public
- **Lines**: 77–78, proof length 1 line (body)
- **Notes**: noncomputable; replaces a deleted "placeholder" version that used `AlgHom.id` and gave a false degree.

---

### `@[simp] theorem isogOneSub_mulByInt_pullback`

- **Type**: `(isogOneSub_mulByInt (W := W) n).pullback = (mulByInt W (1 - n)).pullback`
- **What**: States that the pullback of `isogOneSub_mulByInt n` is definitionally equal to that of `mulByInt W (1-n)`.
- **How**: Proved by `rfl` (definitional equality from the def above).
- **Hypotheses**: `W.toAffine.IsElliptic`
- **Uses from project**: `isogOneSub_mulByInt`, `mulByInt`
- **Used by**: unused in file (used by external callers)
- **Visibility**: public (`@[simp]`)
- **Lines**: 80–81, proof length 1 line
- **Notes**: `@[simp]` tag; trivial `rfl` proof.

---

### `theorem isogOneSub_mulByInt_degree`

- **Type**: `(isogOneSub_mulByInt (W := W) n).degree = (mulByInt W (1 - n)).degree`
- **What**: States that the degree of `isogOneSub_mulByInt n` equals that of `mulByInt W (1-n)`.
- **How**: Proved by `rfl`.
- **Hypotheses**: `W.toAffine.IsElliptic`
- **Uses from project**: `isogOneSub_mulByInt`, `mulByInt`
- **Used by**: unused in file (used by external callers)
- **Visibility**: public
- **Lines**: 84–85, proof length 1 line
- **Notes**: Trivial `rfl` proof.

---

### `noncomputable def isogSmulSub_mulByInt`

- **Type**: `(m r s : ℤ) → Isogeny W.toAffine W.toAffine`
- **What**: Defines the isogeny `r·[m] - s` concretely as `[r·m - s]` (i.e., `mulByInt W (r * m - s)`), providing a genuine function-field pullback.
- **How**: Pure definitional unfolding — body is `mulByInt W (r * m - s)`.
- **Hypotheses**: `W.toAffine.IsElliptic`
- **Uses from project**: `mulByInt` (from `Basic.lean`)
- **Used by**: `isogSmulSub_mulByInt_pullback`, `isogSmulSub_mulByInt_degree`, `degree_quadratic_mulByInt`, `degree_quadratic_mulByInt_nonneg`
- **Visibility**: public
- **Lines**: 91–92, proof length 1 line (body)
- **Notes**: noncomputable; the key "scalar pencil" isogeny used in the degree quadratic form section.

---

### `@[simp] theorem isogSmulSub_mulByInt_pullback`

- **Type**: `(isogSmulSub_mulByInt (W := W) m r s).pullback = (mulByInt W (r * m - s)).pullback`
- **What**: States that the pullback of `isogSmulSub_mulByInt m r s` is definitionally equal to that of `mulByInt W (r*m - s)`.
- **How**: Proved by `rfl`.
- **Hypotheses**: `W.toAffine.IsElliptic`
- **Uses from project**: `isogSmulSub_mulByInt`, `mulByInt`
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 94–96, proof length 1 line
- **Notes**: `@[simp]` tag; trivial `rfl` proof.

---

### `theorem isogSmulSub_mulByInt_degree`

- **Type**: `(isogSmulSub_mulByInt (W := W) m r s).degree = (mulByInt W (r * m - s)).degree`
- **What**: States that the degree of `isogSmulSub_mulByInt m r s` equals that of `mulByInt W (r*m - s)`.
- **How**: Proved by `rfl`.
- **Hypotheses**: `W.toAffine.IsElliptic`
- **Uses from project**: `isogSmulSub_mulByInt`, `mulByInt`
- **Used by**: `degree_quadratic_mulByInt`
- **Visibility**: public
- **Lines**: 99–100, proof length 1 line
- **Notes**: Trivial `rfl` proof; used in the degree quadratic form proof.

---

## Section `Trace`

Variable context: `{E : Affine F}`, `[E.IsElliptic]`.

---

### `noncomputable def isogTrace`

- **Type**: `(α : Isogeny E E) → (one_sub_α : Isogeny E E) → ℤ`
- **What**: Defines the trace of an endomorphism isogeny α as `tr(α) = 1 + deg(α) - deg(1-α)`, following Silverman III.8. The isogeny `1 - α` must be supplied as a separate argument because no general function-field pullback for `1 - α` exists.
- **How**: Pure arithmetic definition: `1 + (α.degree : ℤ) - (one_sub_α.degree : ℤ)`.
- **Hypotheses**: `E.IsElliptic`
- **Uses from project**: `Isogeny.degree` (via `.degree` field from `Basic.lean`)
- **Used by**: `isogTrace_mulByInt`, `degree_quadratic_mulByInt`, `degree_quadratic_mulByInt_nonneg`
- **Visibility**: public
- **Lines**: 118–119, body length 1 line
- **Notes**: noncomputable; parametric design (carries `one_sub_α` explicitly) because the project has no general `1 - α` pullback.

---

### `theorem isogTrace_mulByInt`

- **Type**: `(n : ℤ) → (hn : n ≠ 0) → (hn1 : 1 - n ≠ 0) → isogTrace (mulByInt E n) (mulByInt E (1 - n)) = 2 * n`
- **What**: Proves that the trace of the scalar isogeny `[n]` equals `2n`, i.e., `1 + n² - (1-n)² = 2n`.
- **How**: Uses `mulByInt_degree` (from `Basic.lean`) to convert degree to `(n^2).toNat` and `(1-n)^2.toNat`, then `Int.toNat_of_nonneg` for the non-negative squares, and `ring` to close the arithmetic identity `1 + n² - (1-n)² = 2n`.
- **Hypotheses**: `n ≠ 0`, `1 - n ≠ 0` (needed for `mulByInt_degree`)
- **Uses from project**: `isogTrace`, `mulByInt`, `mulByInt_degree`
- **Used by**: `degree_quadratic_mulByInt`
- **Visibility**: public
- **Lines**: 122–129, proof length 7 lines
- **Notes**: Uses `sq_nonneg` + `Int.toNat_of_nonneg` to handle the `ℕ → ℤ` coercion of degrees.

---

## Section `DegreeQuadraticMulByInt`

Variable context: `{W : WeierstrassCurve F}`, `[W.toAffine.IsElliptic]`.

---

### `theorem degree_quadratic_mulByInt`

- **Type**: `(m r s : ℤ) → (hm : m ≠ 0) → (hm1 : 1 - m ≠ 0) → (h_ne : r * m - s ≠ 0) → ((isogSmulSub_mulByInt (W := W) m r s).degree : ℤ) = ((mulByInt W.toAffine m).degree : ℤ) * r ^ 2 - isogTrace (mulByInt W.toAffine m) (mulByInt W.toAffine (1 - m)) * r * s + s ^ 2`
- **What**: The Silverman III.6.3 degree quadratic formula for scalar isogenies: `deg([r·m - s]) = deg([m])·r² - tr([m])·r·s + s²`. This is the unconditional special case where `α = [m]`.
- **How**: Rewrites `isogSmulSub_mulByInt_degree` to reduce to `mulByInt_degree`, then applies `isogTrace_mulByInt` to replace the trace term with `2m`, then uses `Int.toNat_of_nonneg` for the degree coercions and `ring` for the arithmetic identity `(rm-s)² = m²r² - 2mrs + s²`.
- **Hypotheses**: `m ≠ 0`, `1 - m ≠ 0`, `r * m - s ≠ 0`
- **Uses from project**: `isogSmulSub_mulByInt`, `isogSmulSub_mulByInt_degree`, `mulByInt`, `mulByInt_degree`, `isogTrace`, `isogTrace_mulByInt`
- **Used by**: `degree_quadratic_mulByInt_nonneg`
- **Visibility**: public
- **Lines**: 148–159, proof length 11 lines
- **Notes**: Key theorem for the Hasse bound argument; proof >10 lines relies on `mulByInt_degree` and `isogTrace_mulByInt`.

---

### `theorem degree_quadratic_mulByInt_nonneg`

- **Type**: `(m r s : ℤ) → (hm : m ≠ 0) → (hm1 : 1 - m ≠ 0) → (h_ne : r * m - s ≠ 0) → 0 ≤ ((mulByInt W.toAffine m).degree : ℤ) * r ^ 2 - isogTrace (mulByInt W.toAffine m) (mulByInt W.toAffine (1 - m)) * r * s + s ^ 2`
- **What**: Non-negativity of the degree quadratic form for scalar isogenies: the expression `deg([m])·r² - tr([m])·r·s + s²` is non-negative, because it equals a degree (a natural number coerced to ℤ).
- **How**: Rewrites via `degree_quadratic_mulByInt` (backwards, `←`) to convert the expression to `(isogSmulSub_mulByInt m r s).degree`, then uses `Int.natCast_nonneg` to conclude non-negativity.
- **Hypotheses**: `m ≠ 0`, `1 - m ≠ 0`, `r * m - s ≠ 0`
- **Uses from project**: `isogSmulSub_mulByInt`, `mulByInt`, `isogTrace`, `degree_quadratic_mulByInt`
- **Used by**: unused in file (used by external callers such as `DegreeQuadraticForm.lean`)
- **Visibility**: public
- **Lines**: 164–170, proof length 6 lines
- **Notes**: The non-negativity is trivial once `degree_quadratic_mulByInt` is established; this is the "QF ≥ 0" form needed for Hasse bound arguments.

---

## Cross-reference summary

| Declaration | Used by (in this file) |
|---|---|
| `isogOneSub_mulByInt` | `isogOneSub_mulByInt_pullback`, `isogOneSub_mulByInt_degree` |
| `isogSmulSub_mulByInt` | `isogSmulSub_mulByInt_pullback`, `isogSmulSub_mulByInt_degree`, `degree_quadratic_mulByInt`, `degree_quadratic_mulByInt_nonneg` |
| `isogTrace` | `isogTrace_mulByInt`, `degree_quadratic_mulByInt`, `degree_quadratic_mulByInt_nonneg` |
| `isogSmulSub_mulByInt_degree` | `degree_quadratic_mulByInt` |
| `isogTrace_mulByInt` | `degree_quadratic_mulByInt` |
| `degree_quadratic_mulByInt` | `degree_quadratic_mulByInt_nonneg` |
| `mulByInt` (from Basic.lean) | used by 7 declarations in this file |
| `mulByInt_degree` (from Basic.lean) | used by 3 declarations |

Key API (used by 3+ declarations in this file): `mulByInt`, `isogTrace`, `isogSmulSub_mulByInt`.

## Notes

- No `sorry`, no `set_option maxHeartbeats`, no `sorry`-carrying declarations.
- No proofs exceed 30 lines (longest is `degree_quadratic_mulByInt` at 11 lines).
- `isogOneSub_mulByInt_pullback`, `isogOneSub_mulByInt_degree`, and `isogSmulSub_mulByInt_pullback` are unused within this file (dead-code candidates within the file; they are used by external files).
- The file has a substantial comment block explaining that general `isogOneSub α` / `isogSmulSub α r s` placeholders were deleted (2026-05-28) because no genuine function-field pullback exists for a general `1 − α`; only the scalar `mulByInt` specializations are provided.
- Heavy external usage: `isogTrace` and the quadratic form lemmas are consumed by `DegreeQuadraticForm.lean`, `GapSpines.lean`, `Frobenius.lean`, and many `Hasse/` and `WeilPairing/` files.
