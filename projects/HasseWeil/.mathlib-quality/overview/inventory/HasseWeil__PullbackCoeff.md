# Inventory: ./HasseWeil/PullbackCoeff.lean

**File**: `HasseWeil/PullbackCoeff.lean`
**Lines**: 222
**Module doc**: Defines the pullback coefficient `a_φ` for an endomorphism φ of an elliptic curve, covering Silverman III.5.6 (chain rule, dual relation) and III.6.2c (dual additivity). Imports `HasseWeil.DualIsogeny` and `HasseWeil.InvariantDifferentialPullback`.

---

## Declaration inventory

---

### `noncomputable def D_x`

- **Type**: `(W : WeierstrassCurve F) → [W.toAffine.IsElliptic] → KaehlerDifferential F W.toAffine.FunctionField`
- **What**: Defines the element `D(x)` in the Kähler differential module `Ω[K(E)/F]`, obtained by applying the universal derivation `D` to the image of the coordinate-ring generator `X` in the function field.
- **How**: Direct composition of `KaehlerDifferential.D` with `algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField` applied to `algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X`.
- **Hypotheses**: `E` is an elliptic curve over a field `F`.
- **Uses from project**: (none beyond mathlib's `KaehlerDifferential`)
- **Used by**: `D_x_ne_zero'` (directly)
- **Visibility**: public
- **Lines**: 59–63, trivial definition (no tactic proof)
- **Notes**: This definition duplicates what `InvariantDifferential.lean` already calls `D_x_ne_zero` at the `Affine` level. The definition is essentially a re-packaging convenience, though the doc-comment acknowledges that the actual coefficient extracted by `isogPullbackCoeff` follows the Silverman ω-convention (via `omegaPullbackCoeff`), NOT this `D(x)` basis approach.

---

### `theorem D_x_ne_zero'`

- **Type**: `(W : WeierstrassCurve F) → [W.toAffine.IsElliptic] → D_x W ≠ 0`
- **What**: States that `D(x) ≠ 0` in the Kähler differential module. Wrapper around the existing `D_x_ne_zero` from `InvariantDifferential.lean`.
- **How**: One-line proof delegating to `D_x_ne_zero W.toAffine` (from `HasseWeil/InvariantDifferential.lean`).
- **Hypotheses**: `E` is an elliptic curve.
- **Uses from project**: `D_x_ne_zero` (from `InvariantDifferential.lean`), `D_x`
- **Used by**: unused in this file (dead-code candidate)
- **Visibility**: public
- **Lines**: 66–68, proof length 1
- **Notes**: Thin wrapper; `D_x` itself is also not used except here. Both `D_x` and `D_x_ne_zero'` appear to be legacy scaffolding that predates the ω-based `omegaPullbackCoeff` approach. Possibly parked/experimental.

---

### `noncomputable def isogPullbackCoeff`

- **Type**: `(W : WeierstrassCurve F) → [W.toAffine.IsElliptic] → (α : Isogeny W.toAffine W.toAffine) → W.toAffine.FunctionField`
- **What**: Defines the pullback coefficient `a_α` for an endomorphism isogeny `α : E → E` as the unique scalar `c ∈ K(E)` such that `c • ω = α*(ω)`, where `ω` is the invariant differential. This is the Silverman III.5 convention.
- **How**: Pure abbreviation: `omegaPullbackCoeff W α` (delegates entirely to `OmegaPullbackCoeff.lean`).
- **Hypotheses**: `E` is an elliptic curve over a field `F`.
- **Uses from project**: `omegaPullbackCoeff` (from `OmegaPullbackCoeff.lean`)
- **Used by**: `isogPullbackCoeff_spec`, `isogPullbackCoeff_mulByInt`, `isogPullbackCoeff_comp`, `isogPullbackCoeff_dual_mul`, `isogDual_add_pullbackCoeff`
- **Visibility**: public
- **Lines**: 89–92, trivial (one-line body)
- **Notes**: This is essentially a renaming alias for `omegaPullbackCoeff`. The lengthy doc-comment describes a discarded `D(x)`-based approach and why it was not used. The doc-note that `a_α ∈ K(E)` (not `F`) is a standing issue noted for future work.

---

### `theorem isogPullbackCoeff_spec`

- **Type**: `(W : WeierstrassCurve F) → [W.toAffine.IsElliptic] → (α : Isogeny W.toAffine W.toAffine) → isogPullbackCoeff W α • invariantDifferential W.toAffine = (alpha_star_u W α)⁻¹ • KaehlerDifferential.D F W.toAffine.FunctionField (α.pullback (algebraMap … Polynomial.X))`
- **What**: The defining specification: `a_α • ω = (α*(u))⁻¹ • D(α*(x))`, where `u` is the denominator of the invariant differential. This is the invariant-differential reformulation linking the `D(x)` and `ω`-based views.
- **How**: One-line proof: `omegaPullbackCoeff_spec W α` (from `OmegaPullbackCoeff.lean`).
- **Hypotheses**: `E` is an elliptic curve.
- **Uses from project**: `omegaPullbackCoeff_spec` (from `OmegaPullbackCoeff.lean`), `isogPullbackCoeff`, `invariantDifferential` (from `InvariantDifferential.lean`), `alpha_star_u` (from `OmegaPullbackCoeff.lean`)
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 97–105, proof length 1
- **Notes**: Exposed as part of the public interface but not consumed within this file.

---

### `theorem isogPullbackCoeff_mulByInt`

- **Type**: `(n : ℤ) → (hn : n ≠ 0) → isogPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F W.toAffine.FunctionField n`
- **What**: Silverman Cor. III.5.3: the pullback coefficient of `[n]` (multiplication by `n`) equals `n` (as an element of `K(E)` via the structure map from `F`).
- **How**: One-line proof: `omegaPullbackCoeff_mulByInt W n hn` (from `OmegaPullbackCoeff.lean`).
- **Hypotheses**: `E` elliptic, `n : ℤ` nonzero.
- **Uses from project**: `omegaPullbackCoeff_mulByInt` (from `OmegaPullbackCoeff.lean`), `isogPullbackCoeff`, `mulByInt`
- **Used by**: `isogPullbackCoeff_dual_mul` (line 177)
- **Visibility**: public
- **Lines**: 123–126, proof length 1
- **Notes**: None.

---

### `theorem isogPullbackCoeff_comp`

- **Type**: `(α β : Isogeny W.toAffine W.toAffine) → (c_α : F) → (hα : isogPullbackCoeff W α = algebraMap F _ c_α) → isogPullbackCoeff W (α.comp β) = algebraMap F _ c_α * isogPullbackCoeff W β`
- **What**: Silverman III.5.6(a): the chain rule `a_{α∘β} = a_α · a_β`, stated here in the form where `a_α` is known to be a base-field constant `c_α ∈ F`.
- **How**: One-line proof: `omegaPullbackCoeff_comp_of_base W α β c_α hα` (from `InvariantDifferentialPullback.lean`).
- **Hypotheses**: `E` elliptic; `a_α` must be a base-field constant (carried as explicit hypothesis `hα`), reflecting the current limitation that the K(E)-valued coefficient is not yet shown to always lie in `F`.
- **Uses from project**: `omegaPullbackCoeff_comp_of_base` (from `InvariantDifferentialPullback.lean`), `isogPullbackCoeff`
- **Used by**: `isogPullbackCoeff_dual_mul` (line 175)
- **Visibility**: public
- **Lines**: 151–155, proof length 1
- **Notes**: The doc-comment explicitly flags that `a_α ∈ F` (not just `K(E)`) is an unformalized unconditional fact from Silverman III.1.5.

---

### `theorem isogPullbackCoeff_dual_mul`

- **Type**: `(α : Isogeny W.toAffine W.toAffine) → (c_dual : F) → (hdual_base : isogPullbackCoeff W (isogDual W.toAffine α) = algebraMap F _ c_dual) → (hα_ne : α.degree ≠ 0) → isogPullbackCoeff W (isogDual W.toAffine α) * isogPullbackCoeff W α = algebraMap F W.toAffine.FunctionField α.degree`
- **What**: The identity `a_{φ̂} · a_φ = deg(φ)` in `K(E)`, derived from the compositional identity `φ̂∘φ = [deg φ]` and the chain rule together with `a_{[n]}=n`.
- **How**: Uses `isogPullbackCoeff_comp` (chain rule) with `isogDual W.toAffine α` as the outer isogeny, then rewrites using `HasseWeil.isogDual_comp_self` (from `DualIsogeny.lean`) to identify `(φ̂∘φ) = [deg φ]`, then `isogPullbackCoeff_mulByInt` for `a_{[deg φ]} = deg φ`. Closes by `push_cast; rfl`.
- **Hypotheses**: `E` elliptic; `a_{φ̂}` must be a base-field constant (carried as `hdual_base`); `deg φ ≠ 0`.
- **Uses from project**: `isogPullbackCoeff_comp` (this file), `isogPullbackCoeff_mulByInt` (this file), `HasseWeil.isogDual_comp_self` (from `DualIsogeny.lean`), `isogPullbackCoeff`, `isogDual`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 165–182, proof length ~18 lines
- **Notes**: The proof is the most non-trivial in this file, combining three prior results. The carry of `hdual_base` acknowledges an open formalization gap.

---

### `theorem isogDual_add_pullbackCoeff`

- **Type**: `(α β : Isogeny W.toAffine W.toAffine) → (ha : isogPullbackCoeff W α ≠ 0) → (hb : isogPullbackCoeff W β ≠ 0) → (hab : isogPullbackCoeff W α + isogPullbackCoeff W β ≠ 0) → (αβ : Isogeny W.toAffine W.toAffine) → (_h_sum : αβ.toAddMonoidHom = α.toAddMonoidHom + β.toAddMonoidHom) → (hquad : (algebraMap F KE αβ.degree) * isogPullbackCoeff W α * isogPullbackCoeff W β = (algebraMap F KE α.degree + algebraMap F KE β.degree) * isogPullbackCoeff W α * isogPullbackCoeff W β + isogPullbackCoeff W α ^ 2 * algebraMap F KE β.degree + isogPullbackCoeff W β ^ 2 * algebraMap F KE α.degree) → (algebraMap F KE αβ.degree) * isogPullbackCoeff W α * isogPullbackCoeff W β = (isogPullbackCoeff W α + isogPullbackCoeff W β) * (algebraMap F KE α.degree * isogPullbackCoeff W β + algebraMap F KE β.degree * isogPullbackCoeff W α)`
- **What**: Silverman III.6.2c at the level of pullback coefficients: given the quadratic degree formula for `deg(α+β)` (carried as `hquad`), the product `deg(α+β)·a_α·a_β` factors as `(a_α+a_β)·(deg(α)·a_β + deg(β)·a_α)`. This is the algebraic core of the dual-additivity identity `(α+β)^ = α̂+β̂`.
- **How**: Pure application of `dual_additivity_algebraic` (from `FormalGroupAssoc.lean`) to the pullback coefficients and degrees. One-line body.
- **Hypotheses**: `a_α ≠ 0`, `a_β ≠ 0`, `a_α + a_β ≠ 0` (all separability assumptions); the quadratic-degree hypothesis `hquad` (the degree of the sum formula — an unformalized but carried fact).
- **Uses from project**: `dual_additivity_algebraic` (from `FormalGroupAssoc.lean`), `isogPullbackCoeff`, `isogDual` (in doc-comment only)
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 197–219, proof length ~20 lines (body is 1 line; signature is long)
- **Notes**: The actual mathematical work (the algebraic identity) lives in `dual_additivity_algebraic`; this lemma is purely a specialization. The hypothesis `_h_sum` is explicitly unnamed (underscore), indicating it is not used in the proof body — the proof only invokes the algebraic identity on the numeric data. The `hquad` hypothesis is the real mathematical content being assumed; connecting it to the actual degree formula for `α+β` is left as future work.

---

## Cross-reference summary

| Declaration | Used by (in this file) |
|---|---|
| `D_x` | `D_x_ne_zero'` |
| `D_x_ne_zero'` | (nothing) |
| `isogPullbackCoeff` | `isogPullbackCoeff_spec`, `isogPullbackCoeff_mulByInt`, `isogPullbackCoeff_comp`, `isogPullbackCoeff_dual_mul`, `isogDual_add_pullbackCoeff` |
| `isogPullbackCoeff_spec` | (nothing) |
| `isogPullbackCoeff_mulByInt` | `isogPullbackCoeff_dual_mul` |
| `isogPullbackCoeff_comp` | `isogPullbackCoeff_dual_mul` |
| `isogPullbackCoeff_dual_mul` | (nothing) |
| `isogDual_add_pullbackCoeff` | (nothing) |

**keyApi** (used by 3+ others in this file): `isogPullbackCoeff` (used by 5 declarations).

**Declarations unused within this file** (dead-code candidates for this file; may be used by other files):
- `D_x` (used only by `D_x_ne_zero'`, which is itself unused)
- `D_x_ne_zero'` (not called by anything)
- `isogPullbackCoeff_spec` (not called)
- `isogPullbackCoeff_dual_mul` (not called)
- `isogDual_add_pullbackCoeff` (not called)

None of these appear to be imported by any other project file (grep found no external uses of `isogPullbackCoeff`, `D_x`, or `D_x_ne_zero'` outside this file).

## Summary statistics

- **Total declarations**: 8 (2 `noncomputable def`, 6 `theorem`)
- **Defs**: 2
- **Lemmas/theorems**: 6
- **Instances**: 0
- **Sorries**: none
- **`set_option maxHeartbeats`**: none
- **Long proofs (>30 lines)**: none
- **Notable**: This file is essentially a thin wrapper/API layer over `omegaPullbackCoeff` (defined in `OmegaPullbackCoeff.lean`) and the algebraic identity in `FormalGroupAssoc.lean`. Most proofs are one-liners delegating to the underlying machinery. The `D_x`/`D_x_ne_zero'` pair appears to be dead scaffolding from an earlier D(x)-based design that was superseded. No external callers of any declaration in this file were found in the project (beyond the root `HasseWeil.lean` import).
