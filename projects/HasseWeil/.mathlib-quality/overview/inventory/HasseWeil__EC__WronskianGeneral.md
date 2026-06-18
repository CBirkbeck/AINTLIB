# Inventory: ./HasseWeil/EC/WronskianGeneral.lean

**File purpose:** Provides an axiom-clean proof of the division-polynomial Wronskian identity
`Φ_n' · ΨSq_n − Φ_n · ΨSq_n' = n · preΨ_{2n}` in `F[X]` (Silverman Exercise III.3.7), routing
through the function field to avoid the EDS addition formula needed by the existing inductive proof
in `OmegaPullbackCoeff.lean`.

**Import:** `HasseWeil.WeilPairing.TorsionGeometric` (transitively imports `RouteBInduction`,
`OmegaPullbackCoeff`, `BridgeMulByInt`, and the full elliptic-curve function-field stack).

**Total declarations:** 2 (both theorems, both public)

---

## Declaration inventory

---

### `theorem algebraMap_polynomial_KE_injective`

- **Type**: `Function.Injective (algebraMap (Polynomial F) KE)`
  where `KE = W.toAffine.FunctionField`, `F` a field, `W : WeierstrassCurve F`, no `IsElliptic` or
  `DecidableEq` required (both omitted).
- **What**: The ring map `F[X] → K(E)` (function field of the elliptic curve) is injective, i.e.,
  `x_gen` is transcendental over `F`.
- **How**: Factors the map as `F[X] → CoordinateRing → FunctionField` using
  `IsScalarTower.algebraMap_eq`; injectivity of the first factor is
  `Affine.CoordinateRing.algebraMap_poly_injective` (a mathlib/project lemma asserting X is
  transcendental in the coordinate ring), and the second factor is `IsFractionRing.injective`
  (fraction field inclusion is injective).
- **Hypotheses**: `W : WeierstrassCurve F`, `F` a field. No ellipticity or `DecidableEq` needed.
- **Uses from project**: `Affine.CoordinateRing.algebraMap_poly_injective` (from
  `HasseWeil/Basic.lean` or Mathlib)
- **Used by**: `wronskian_Φ_ΨSq_general` (within this file, at line 123)
- **Visibility**: public
- **Lines**: 57–65, proof lines 58–65 (8 lines)
- **Notes**: `omit [DecidableEq F] [W.toAffine.IsElliptic] in` — the proof does not use ellipticity.
  A nearly identical private theorem exists in `OrdAtInftyBridge.lean:183`; this public version is
  a de-duplication candidate.

---

### `theorem wronskian_Φ_ΨSq_general`

- **Type**: For `n : ℤ`, `hn : n ≠ 0`:
  ```
  Polynomial.derivative (W.Φ n) * W.ΨSq n - W.Φ n * Polynomial.derivative (W.ΨSq n)
  = Polynomial.C ((n : ℤ) : F) * W.preΨ (2 * n)
  ```
  in `Polynomial F`.
- **What**: The division-polynomial Wronskian identity (Silverman Ex. III.3.7):
  `Φ_n' · ΨSq_n − Φ_n · ΨSq_n' = n · preΨ_{2n}` as polynomials over any field `F`, for `n ≠ 0`.
  This is the axiom-clean replacement for `HasseWeil.wronskian_Φ_ΨSq` (which carries `sorryAx`).
- **How**: Four-step chain:
  1. `WeilPairing.TorsionGeometric.omegaCoeff_mulByInt W n hn` provides `a_{[n]} = n` (the
     general-field differential coefficient, Route-B chord recurrence, EDS-free).
  2. `divPoly_wronskian_identity_of_omega W n hn homega` (from `OmegaPullbackCoeff`) lifts this to
     a K(E)-level Wronskian identity `(Φ' ΨSq − Φ ΨSq') · u = n · ΨSq² · α*u`.
  3. `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u W n hn` (from `OmegaPullbackCoeff`) rewrites
     `ΨSq² · α*u = preΨ_{2n} · u`, collapsing the RHS to `n · preΨ_{2n} · u`.
  4. Cancels `u_gen` (nonzero by `u_gen_ne_zero W`) and descends via
     `algebraMap_polynomial_KE_injective` to the polynomial identity.
  Intermediate steps use `IsScalarTower.algebraMap_apply` to fold `Φ_ff`/`ΨSq_ff` into algebraMap
  images, `Polynomial.C_eq_algebraMap` to fold the scalar `n`, and `map_sub`/`map_mul` to collect
  both sides as single algebraMap-images.
- **Hypotheses**: `W : WeierstrassCurve F` elliptic, `F` a field with `DecidableEq`, `n : ℤ`,
  `n ≠ 0`.
- **Uses from project**:
  - `WeilPairing.TorsionGeometric.omegaCoeff_mulByInt` (from `TorsionGeometric.lean`)
  - `divPoly_wronskian_identity_of_omega` (from `OmegaPullbackCoeff.lean`)
  - `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u` (from `OmegaPullbackCoeff.lean`)
  - `u_gen_ne_zero` (from `OmegaPullbackCoeff.lean`)
  - `algebraMap_polynomial_KE_injective` (within this file)
  - `Φ_ff`, `ΨSq_ff` (notation/defs from `OmegaPullbackCoeff` or `BridgeMulByInt`)
- **Used by**: unused in this file; called by `MulByIntUnramified.lean:390`
  (`fibrePoly_derivative_eval_ne_zero`) as the EDS-free Wronskian for affine unramifiedness.
- **Visibility**: public
- **Lines**: 67–124 (with docstring starting at 67; proof body lines 82–123, 42 proof lines)
- **Notes**: `set_option linter.unusedDecidableInType false in` — suppresses a linter warning about
  the `DecidableEq F` instance that appears in the variable context but is not directly consumed
  by the proof (it is needed transitively via `IsElliptic` typeclass machinery). Proof is 42 lines
  long (>30). No `sorry`. Axiom-clean per module docstring. The mathematical content duplicates
  `wronskian_Φ_ΨSq` in `OmegaPullbackCoeff.lean` but the route is entirely different and
  axiom-clean.

---

## Summary

| Metric | Value |
|---|---|
| Total declarations | 2 |
| Theorems | 2 |
| Defs/abbrevs/instances | 0 |
| Sorries | none |
| Long proofs (>30 lines) | `wronskian_Φ_ΨSq_general` (42 lines) |
| set_option maxHeartbeats | none |
| Other set_option | `linter.unusedDecidableInType false` (line 67, no justifying comment beyond the docstring) |
| Key API (used by 3+) | none (only 2 declarations) |
| Unused in file | `wronskian_Φ_ΨSq_general` (used externally in `MulByIntUnramified`) |

**Notable:** This file is a thin two-declaration "axiom-clean wrapper" that re-proves a polynomial
identity via a longer but sorry-free path through the function field; the real work lives in
`OmegaPullbackCoeff.lean` and `TorsionGeometric.lean`. The private `algebraMap_polynomial_KE_injective`
in `OrdAtInftyBridge.lean:183` is a duplication of the public version here.
