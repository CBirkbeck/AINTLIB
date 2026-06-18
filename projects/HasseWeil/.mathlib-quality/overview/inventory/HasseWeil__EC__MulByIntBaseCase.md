# Inventory: ./HasseWeil/EC/MulByIntBaseCase.lean

**File**: `HasseWeil/EC/MulByIntBaseCase.lean`
**Import**: `HasseWeil.OmegaPullbackCoeff`
**Total declarations**: 13 theorems, 0 defs, 0 instances
**Sorries**: none
**maxHeartbeats overrides**: none

---

## Summary

Base-case identities for the multiplication-by-integer isogeny `mulByInt W n` at `n = 1`:
establishes `[1] = id` at the level of division-polynomial rational maps, pullback algebra
homomorphism, `toAddMonoidHom`, and full `Isogeny` equality. Also provides the uniqueness
characterisation of `(mulByInt W n).pullback` and substitution lemmas for `Φ_ff`/`ΨSq_ff`.

---

### `theorem mulByInt_x_one`

- **Type**: `mulByInt_x W 1 = x_gen W`
- **What**: The `[1]`-image of the generic x-coordinate `Φ_1/ΨSq_1` equals `x_gen` in the function field `K(E)`.
- **How**: `unfold` exposes `Φ_ff`/`ΨSq_ff`; rewrites `WeierstrassCurve.Φ_one` (= `Polynomial.X`) and `WeierstrassCurve.ΨSq_one` (= `1`); finishes with `div_one`.
- **Hypotheses**: `W` is an elliptic curve over a field `F` (with `DecidableEq`).
- **Uses from project**: `mulByInt_x`, `x_gen`, `Φ_ff`, `ΨSq_ff` (all from import)
- **Used by**: `mulByInt_pullback_x_one`
- **Visibility**: public
- **Lines**: 38–41 (proof 4 lines)
- **Notes**: none

---

### `theorem mulByInt_y_one`

- **Type**: `mulByInt_y W 1 = algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (AdjoinRoot.root W.toAffine.polynomial)`
- **What**: The `[1]`-image of the generic y-coordinate `ω_1/ψ_1³` equals the canonical root (= `y_gen`) in `K(E)`.
- **How**: `unfold` exposes `ω_ff`/`ψ_ff`; rewrites `WeierstrassCurve.ω_one` (= `Y`) and `WeierstrassCurve.ψ_one` (= `1`); finishes with `div_one` via `simp` and `map_one`.
- **Hypotheses**: Same as above.
- **Uses from project**: `mulByInt_y`, `ω_ff`, `ψ_ff` (from import)
- **Used by**: `mulByInt_pullback_y_one`
- **Visibility**: public
- **Lines**: 45–51 (proof 7 lines)
- **Notes**: none

---

### `theorem mulByInt_pullback_x_one`

- **Type**: `(mulByInt W.toAffine 1).pullback (algebraMap (Polynomial F) W.toAffine.FunctionField Polynomial.X) = algebraMap (Polynomial F) W.toAffine.FunctionField Polynomial.X`
- **What**: The pullback algebra homomorphism of `[1]` fixes the canonical image of `Polynomial.X` (= `x_gen`) in `K(E)`.
- **How**: Rewrites via `mulByInt_pullback_x W 1 one_ne_zero` (which evaluates `[1].pullback(x_gen)` to `mulByInt_x W 1`) and then `mulByInt_x_one`; finishes by `rfl`.
- **Hypotheses**: Same as above.
- **Uses from project**: `mulByInt_pullback_x` (import), `mulByInt_x_one` (this file)
- **Used by**: `mulByInt_one_pullback_eq_id`
- **Visibility**: public
- **Lines**: 55–62 (proof 3 lines)
- **Notes**: none

---

### `theorem mulByInt_pullback_y_one`

- **Type**: `(mulByInt W.toAffine 1).pullback (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (AdjoinRoot.root W.toAffine.polynomial)) = algebraMap ... (AdjoinRoot.root ...)`
- **What**: The pullback of `[1]` fixes the canonical root `y_gen` in `K(E)`.
- **How**: Rewrites via `mulByInt_pullback_y W 1 one_ne_zero` and `mulByInt_y_one`.
- **Hypotheses**: Same as above.
- **Uses from project**: `mulByInt_pullback_y` (import), `mulByInt_y_one` (this file)
- **Used by**: `mulByInt_one_pullback_eq_id`
- **Visibility**: public
- **Lines**: 66–72 (proof 2 lines)
- **Notes**: none

---

### `theorem mulByInt_one_pullback_eq_id`

- **Type**: `(mulByInt W.toAffine 1).pullback = AlgHom.id F W.toAffine.FunctionField`
- **What**: The pullback F-algebra endomorphism of `[1]` is the identity on `K(E)`.
- **How**: Reduction chain: `AlgHom.coe_ringHom_injective` → `IsLocalization.ringHom_ext` (on `CoordinateRing → FunctionField`) → `AdjoinRoot.ringHom_ext` → `Polynomial.ringHom_ext`; base case by `AlgHom.commutes`; x-gen case by `mulByInt_pullback_x_one`; y-gen case by `mulByInt_pullback_y_one`.
- **Hypotheses**: Same as above.
- **Uses from project**: `mulByInt_pullback_x_one` (this file), `mulByInt_pullback_y_one` (this file)
- **Used by**: `mulByInt_one_eq_id`, `mulByInt_one_comp_mulByInt_one`
- **Visibility**: public
- **Lines**: 88–101 (proof 14 lines)
- **Notes**: Proof > 10 lines; uses the four-layer ringHom_ext reduction chain described in the module docstring.

---

### `theorem mulByInt_one_toAddMonoidHom_eq_id`

- **Type**: `(mulByInt W.toAffine 1).toAddMonoidHom = AddMonoidHom.id _`
- **What**: The point-map part of `[1]` is the identity additive monoid homomorphism: `1 • P = P` for all `P`.
- **How**: Extensionality `ext P`, then `one_zsmul`.
- **Hypotheses**: Same as above.
- **Uses from project**: `mulByInt` (import)
- **Used by**: `mulByInt_one_eq_id`
- **Visibility**: public
- **Lines**: 105–109 (proof 4 lines)
- **Notes**: none

---

### `theorem mulByInt_one_eq_id`

- **Type**: `mulByInt W.toAffine 1 = Isogeny.id W.toAffine`
- **What**: The multiplication-by-one isogeny equals the identity isogeny as `Isogeny` structures.
- **How**: Cases on the `Isogeny` record; substitutes `mulByInt_one_pullback_eq_id` and `mulByInt_one_toAddMonoidHom_eq_id` into both fields; closes by `rfl`.
- **Hypotheses**: Same as above.
- **Uses from project**: `mulByInt_one_pullback_eq_id` (this file), `mulByInt_one_toAddMonoidHom_eq_id` (this file), `Isogeny.id` (import)
- **Used by**: unused in file (intended for callers in other files)
- **Visibility**: public
- **Lines**: 114–122 (proof 9 lines)
- **Notes**: none

---

### `theorem mulByInt_add_toAddMonoidHom`

- **Type**: `(mulByInt W.toAffine (m + n)).toAddMonoidHom = (mulByInt W.toAffine m).toAddMonoidHom + (mulByInt W.toAffine n).toAddMonoidHom`
- **What**: The point-map of `[m+n]` equals the sum of those of `[m]` and `[n]`, reflecting the ℤ-module law `(m+n)•P = m•P + n•P`.
- **How**: `ext P`, then `add_zsmul`.
- **Hypotheses**: `m n : ℤ`, same curve hypotheses.
- **Uses from project**: `mulByInt` (import)
- **Used by**: `mulByInt_succ_toAddMonoidHom`
- **Visibility**: public
- **Lines**: 126–131 (proof 5 lines)
- **Notes**: none

---

### `theorem mulByInt_succ_toAddMonoidHom`

- **Type**: `(mulByInt W.toAffine (k + 1)).toAddMonoidHom = (mulByInt W.toAffine k).toAddMonoidHom + (mulByInt W.toAffine 1).toAddMonoidHom`
- **What**: Specialisation of `mulByInt_add_toAddMonoidHom` to the successor step `k → k+1`; enables inductive arguments.
- **How**: Direct instantiation of `mulByInt_add_toAddMonoidHom W k 1`.
- **Hypotheses**: `k : ℤ`, same curve hypotheses.
- **Uses from project**: `mulByInt_add_toAddMonoidHom` (this file)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 135–138 (proof 1 line)
- **Notes**: none

---

### `theorem mulByInt_one_comp_mulByInt_one`

- **Type**: `(mulByInt W.toAffine 1).comp (mulByInt W.toAffine 1) = mulByInt W.toAffine 1`
- **What**: Composing `[1]` with itself gives `[1]`; i.e. the identity isogeny is idempotent under composition.
- **How**: Unfolds `Isogeny.comp` as an `Isogeny.mk` record; handles the pullback field by `mulByInt_one_pullback_eq_id` + `AlgHom.id_comp`; handles the hom field by `ext P` + `simp`; closes by rewriting both back.
- **Hypotheses**: Same curve hypotheses.
- **Uses from project**: `mulByInt_one_pullback_eq_id` (this file)
- **Used by**: `mulByInt_one_comp_eq_mulByInt_degree`
- **Visibility**: public
- **Lines**: 144–157 (proof 14 lines)
- **Notes**: Proof > 10 lines; uses `AlgHom.id_comp`.

---

### `theorem mulByInt_one_comp_eq_mulByInt_degree`

- **Type**: `(mulByInt W.toAffine 1).comp (mulByInt W.toAffine 1) = mulByInt W.toAffine ((mulByInt W.toAffine 1).degree : ℤ)`
- **What**: `[1] ∘ [1] = [[1].degree]`; the required form for `isogDual_mulByInt_of_comp`, since `[1].degree = 1`.
- **How**: Rewrites via `mulByInt_one_comp_mulByInt_one` and `mulByInt_degree W.toAffine 1 one_ne_zero`; normalises `(1:ℤ) = ...` with `norm_num`.
- **Hypotheses**: Same curve hypotheses.
- **Uses from project**: `mulByInt_one_comp_mulByInt_one` (this file), `mulByInt_degree` (import)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 161–165 (proof 4 lines)
- **Notes**: none

---

### `theorem algHom_apply_polynomial`

- **Type**: `f (algebraMap (Polynomial F) W.toAffine.FunctionField p) = Polynomial.eval₂ (algebraMap F W.toAffine.FunctionField) (f (algebraMap (Polynomial F) W.toAffine.FunctionField Polynomial.X)) p` for any F-algebra endomorphism `f` and polynomial `p`.
- **What**: Any F-algebra endomorphism of `K(E)` acts on polynomial images by substituting the generator `X ↦ f(X)`; i.e. polynomial images are determined by where `X` goes.
- **How**: Rewrites `algebraMap p` as `Polynomial.aeval` of the X-image via `Polynomial.aeval_algebraMap_apply` and `Polynomial.aeval_algHom_apply`; then uses `Polynomial.aeval_def`.
- **Hypotheses**: `f : K(E) →ₐ[F] K(E)`, `p : Polynomial F`.
- **Uses from project**: none
- **Used by**: `mulByInt_pullback_Φ_ff`, `mulByInt_pullback_ΨSq_ff`
- **Visibility**: public
- **Lines**: 186–197 (proof 7 lines)
- **Notes**: none

---

### `theorem mulByInt_pullback_unique`

- **Type**: Given `n ≠ 0` and an F-algebra endomorphism `f` of `K(E)` satisfying `f(x_gen) = mulByInt_x W n` and `f(root) = mulByInt_y W n`, then `f = (mulByInt W.toAffine n).pullback`.
- **What**: The pullback of `[n]` is the unique F-algebra endomorphism of `K(E)` that sends the generic coordinates to the division-polynomial expressions for `[n]`.
- **How**: Same four-layer reduction as `mulByInt_one_pullback_eq_id`: `AlgHom.coe_ringHom_injective` → `IsLocalization.ringHom_ext` → `AdjoinRoot.ringHom_ext` → `Polynomial.ringHom_ext`; base by `AlgHom.commutes` + scalar tower via `IsScalarTower.algebraMap_apply`; x-gen by `h_x` and `mulByInt_pullback_x W n hn`; y-gen by `h_y` and `mulByInt_pullback_y W n hn`.
- **Hypotheses**: `n ≠ 0`; `f(x_gen) = mulByInt_x W n`; `f(root) = mulByInt_y W n`.
- **Uses from project**: `x_gen` (import), `mulByInt_x` (import), `mulByInt_y` (import), `mulByInt_pullback_x` (import), `mulByInt_pullback_y` (import)
- **Used by**: unused in file (intended as infrastructure for `MulByIntComp`)
- **Visibility**: public
- **Lines**: 203–240 (proof 38 lines)
- **Notes**: Proof > 30 lines. Uses `IsScalarTower.algebraMap_apply` for the scalar tower book-keeping in the base case.

---

### `theorem mulByInt_pullback_Φ_ff`

- **Type**: `(mulByInt W.toAffine m).pullback (Φ_ff W n) = Polynomial.eval₂ (algebraMap F W.toAffine.FunctionField) (mulByInt_x W m) (W.Φ n)`
- **What**: The pullback of `[m]` applied to `Φ_ff W n` equals the numerator polynomial `W.Φ n` evaluated at `mulByInt_x W m`.
- **How**: Normalises `Φ_ff W n` as `algebraMap (Polynomial F) KE (W.Φ n)` via `IsScalarTower.algebraMap_apply`; identifies `[m].pullback(X) = mulByInt_x W m` via `mulByInt_pullback_x W m hm`; applies `algHom_apply_polynomial`.
- **Hypotheses**: `m ≠ 0`.
- **Uses from project**: `Φ_ff` (import), `x_gen` (import), `mulByInt_x` (import), `mulByInt_pullback_x` (import), `algHom_apply_polynomial` (this file)
- **Used by**: `mulByInt_pullback_mulByInt_x`
- **Visibility**: public
- **Lines**: 248–266 (proof 15 lines)
- **Notes**: Proof > 10 lines.

---

### `theorem mulByInt_pullback_ΨSq_ff`

- **Type**: `(mulByInt W.toAffine m).pullback (ΨSq_ff W n) = Polynomial.eval₂ (algebraMap F W.toAffine.FunctionField) (mulByInt_x W m) (W.ΨSq n)`
- **What**: Analogous to `mulByInt_pullback_Φ_ff` for the denominator polynomial `ΨSq`.
- **How**: Same pattern as `mulByInt_pullback_Φ_ff`: normalize `ΨSq_ff`; identify X-pullback; apply `algHom_apply_polynomial`.
- **Hypotheses**: `m ≠ 0`.
- **Uses from project**: `ΨSq_ff` (import), `x_gen` (import), `mulByInt_x` (import), `mulByInt_pullback_x` (import), `algHom_apply_polynomial` (this file)
- **Used by**: `mulByInt_pullback_mulByInt_x`
- **Visibility**: public
- **Lines**: 270–288 (proof 15 lines)
- **Notes**: Proof > 10 lines. Nearly identical to `mulByInt_pullback_Φ_ff`; duplication is intentional (different polynomial arguments).

---

### `theorem mulByInt_pullback_mulByInt_x`

- **Type**: `(mulByInt W.toAffine m).pullback (mulByInt_x W n) = Polynomial.eval₂ (algebraMap F KE) (mulByInt_x W m) (W.Φ n) / Polynomial.eval₂ (algebraMap F KE) (mulByInt_x W m) (W.ΨSq n)`
- **What**: The pullback of `[m]` applied to the x-rational-map `[n]_x = Φ_n/ΨSq_n` equals the ratio of those polynomials evaluated at `[m]_x`.
- **How**: Expands `mulByInt_x W n = Φ_ff W n / ΨSq_ff W n` and uses `map_div₀`; then applies `mulByInt_pullback_Φ_ff` and `mulByInt_pullback_ΨSq_ff`.
- **Hypotheses**: `m ≠ 0`.
- **Uses from project**: `mulByInt_x` (import), `Φ_ff` (import), `ΨSq_ff` (import), `mulByInt_pullback_Φ_ff` (this file), `mulByInt_pullback_ΨSq_ff` (this file)
- **Used by**: unused in file (public API for `MulByIntComp`)
- **Visibility**: public
- **Lines**: 291–302 (proof 12 lines)
- **Notes**: none

---

## Key API (used by 3+ declarations in this file)

- `mulByInt_one_pullback_eq_id` — used by `mulByInt_one_eq_id` (x2 at lines 116, 155–156) and `mulByInt_one_comp_mulByInt_one` (line 155): 3 uses.
- `algHom_apply_polynomial` — used by `mulByInt_pullback_Φ_ff` and `mulByInt_pullback_ΨSq_ff`.
- `mulByInt_pullback_x` (from import) — used by `mulByInt_pullback_x_one`, `mulByInt_pullback_unique`, `mulByInt_pullback_Φ_ff`, `mulByInt_pullback_ΨSq_ff`: 4 uses.

## Dead code (unused within this file)

- `mulByInt_one_eq_id` — exported for other files; no internal caller.
- `mulByInt_succ_toAddMonoidHom` — exported for inductive infrastructure; no internal caller.
- `mulByInt_one_comp_eq_mulByInt_degree` — exported; no internal caller.
- `mulByInt_pullback_unique` — exported for `MulByIntComp`; no internal caller.
- `mulByInt_pullback_mulByInt_x` — exported for `MulByIntComp`; no internal caller.

## Long proofs (> 30 lines)

- `mulByInt_pullback_unique`: lines 203–240, ~38 lines.
