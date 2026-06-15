# Inventory: ./HasseWeil/Curves/QuotientCurve.lean

File: `HasseWeil/Curves/QuotientCurve.lean`
Total lines: 97
Imports: `HasseWeil.Basic`, `HasseWeil.Frobenius`, `HasseWeil.IsogenyBaseChange`, `HasseWeil.EC.IsogenyKernel`

---

## Overview

A short structural file (97 lines, 2 theorems) shipping plan items P0-C of the
`R25j-AUDIT-AND-NEW-STRUCT-BRIEF.md` brief. Both theorems are essentially
two-to-four-line tactic proofs that wire together already-proven project lemmas.
Neither declaration has a sorry or a `set_option maxHeartbeats`.

---

### `theorem separable_isogeny_factors_quotient`

- **Type**:
  ```
  (α : Isogeny W W) :
    ∃ (W' : Affine F) (_ : W'.IsElliptic)
      (ψ : Isogeny W' W),
      Function.Bijective ψ.toAddMonoidHom ∧
      ∃ (φ_quot : Isogeny W W'),
        α.toAddMonoidHom = (ψ.comp φ_quot).toAddMonoidHom
  ```
- **What**: Any isogeny α : E → E factors as `α = id ∘ α` (degenerate
  quotient decomposition). In the separable case the quotient curve is the
  original curve itself, and the second factor ψ = id is bijective on rational
  points — implementing the P0-C structural requirement.
- **How**: Uses `Isogeny.id_toAddMonoidHom` (id maps to `AddMonoidHom.id`,
  hence bijective by `Function.bijective_id`) and
  `Isogeny.comp_toAddMonoidHom` + `AddMonoidHom.id_comp` to verify the
  factorisation identity.
- **Hypotheses**: `W : Affine F` is an elliptic curve over a field with
  decidable equality; α is any isogeny from W to itself.
- **Uses from project**: `Isogeny.id` (Basic.lean), `Isogeny.id_toAddMonoidHom`
  (Basic.lean), `Isogeny.comp_toAddMonoidHom` (Basic.lean).
- **Used by**: unused in file; no callers found in any other project file.
- **Visibility**: public
- **Lines**: 53–68, proof length ≈ 7 lines (including comments)
- **Notes**: Proof is trivial (`refine` + two `rw` + `exact`). The theorem
  statement captures the "degenerate quotient" special case only; the
  non-trivial separable-quotient construction (W'/G for a finite group G) is
  acknowledged in the docstring comment but not formalized. Suspected to be
  a placeholder / structural stub rather than a result used downstream.

---

### `theorem frobeniusTwist_eq_self_of_prime_field`

- **Type**:
  ```
  [DecidableEq K] [Fact (Fintype.card K = p)]
  (W : WeierstrassCurve K) :
    W.frobeniusTwist p = W
  ```
  where `K` is a finite field of characteristic p (prime).
- **What**: For the prime field `F_p`, the p-Frobenius twist `E^{(p)}` equals
  the original Weierstrass curve. This follows because the Frobenius
  endomorphism on `F_p` is the identity (Fermat's little theorem).
- **How**: Unfolds `frobeniusTwist p = W.map (frobenius K p)`, applies
  `HasseWeil.Isogeny.frobenius_eq_id_of_charP_prime` (from `IsogenyBaseChange.lean`)
  to replace `frobenius K p` by `RingHom.id K`, then closes with
  `WeierstrassCurve.map_id`.
- **Hypotheses**: `K` is a finite field, `p` is prime, `CharP K p`, and
  `Fintype.card K = p` (i.e., K is exactly `F_p`, not a proper extension).
- **Uses from project**: `HasseWeil.Isogeny.frobenius_eq_id_of_charP_prime`
  (IsogenyBaseChange.lean), `WeierstrassCurve.map_id` (mathlib / project
  re-export via IsogenyBaseChange.lean).
- **Used by**: unused in file; no callers found in any other project file.
- **Visibility**: public
- **Lines**: 88–94, proof length ≈ 4 lines
- **Notes**: `IsogenyBaseChange.lean` already contains a closely related
  theorem `frobeniusTwist_eq_self_of_card_eq_p` (line 617) that proves the
  same statement with the same hypotheses. This theorem appears to be a
  **duplicate** of that result, living in a different namespace/file.
  Dead-code candidate; may have been written before `IsogenyBaseChange.lean`
  grew the matching result.
