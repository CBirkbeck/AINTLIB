# Inventory: ./HasseWeil/WronskianAux.lean

**File purpose**: Two **pure polynomial Wronskian auxiliary identities** for Weierstrass division
polynomials (Silverman III.3 Exercise 3.7), isolated into their own file because their `ring`
elaboration is extremely expensive. Each identity `LHS − RHS` factors as `M(X) · (4b₈ − b₂b₆ + b₄²)`
in `ℤ[b₂,b₄,b₆,b₈,X]` for an explicit (offline-computed) multiplier polynomial `M`; the proof is
`linear_combination M · h_P` where `h_P` is `b_relation` lifted to `R[X]`. They discharge the `m = 3`
and `m = 4` base cases of the division-polynomial Wronskian recursion `wronskian_Φ_ΨSq`
(`OmegaPullbackCoeff.lean`), which underpins the `#E[ℓ] = ℓ²` / separability machinery consumed by
Route 2A. **This file is on the live capstone import path** (`WeilPairing/HasseBound` → … →
`OmegaPullbackCoeff` → here).

**Imports**: `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`,
`Mathlib.Algebra.Polynomial.Derivation`, `HasseWeil.WronskianAux.CNorm`

**Total declarations**: 3 (1 `private lemma`, 2 `lemma`). **All LIVE** (the two public lemmas are
consumed by `OmegaPullbackCoeff.lean`; the private one feeds both).

**Variables**: `{R : Type*} [CommRing R] (W : WeierstrassCurve R)`.

---

## Declarations

### `private lemma b_relation_poly`  — **LIVE**
- **Type**: `((4 : R[X]) * Polynomial.C W.b₈ : R[X]) = Polynomial.C W.b₂ * Polynomial.C W.b₆ − Polynomial.C W.b₄ ^ 2`
- **What**: `W.b_relation` (`4·b₈ = b₂·b₆ − b₄²`) lifted to `R[X]` in `C`-distributed form, so
  `linear_combination` can multiply it by a polynomial multiplier `M`.
- **How**: rewrite `(4 : R[X]) = Polynomial.C 4`, distribute `C` (`C_mul`, `C_pow`, `C_sub`), then
  `congrArg Polynomial.C W.b_relation`.
- **Hypotheses**: none (any `CommRing R`).
- **Uses from project**: `WeierstrassCurve.b_relation`, `W.b₂/b₄/b₆/b₈` (mathlib elliptic-curve API).
- **Used by**: `wronskian_aux_three` (L104), `wronskian_aux_four` (L158) — this file.
- **Visibility**: `private`. **Lines**: 71–76, ~3 lines. **LIVE.**

---

### `lemma wronskian_aux_three`  — **LIVE**
- **Type**: `4 * W.Ψ₃ ^ 3 + 2 * W.preΨ₄ * W.Ψ₂Sq * derivative W.Ψ₃ − derivative (W.preΨ₄ * W.Ψ₂Sq) * W.Ψ₃ = C 3 * W.preΨ₄ * W.Ψ₂Sq ^ 2 − C 3 * W.preΨ₄ ^ 2`
- **What**: the `m = 3` Wronskian auxiliary identity (Silverman III.3.7).
- **How**: `linear_combination (norm := …) M₃ · b_relation_poly W` where the `norm` tactic is
  `simp only [Ψ₃, preΨ₄, Ψ₂Sq, derivative_*, C_*, C_ofNat, Nat.cast_ofNat]; ring`, and `M₃` is the
  explicit degree-8 multiplier `b₈² + 4b₆b₈·X + 6b₄b₈·X² + 4b₂b₈·X³ + (b₂b₆+34b₈)·X⁴ + 36b₆·X⁵ +
  18b₄·X⁶ + 4b₂·X⁷ + 9·X⁸`.
- **Hypotheses**: none (any `CommRing R`).
- **Uses from project**: `b_relation_poly` (this file); `WeierstrassCurve.Ψ₃`, `preΨ₄`, `Ψ₂Sq` (mathlib
  division-polynomial API); the `CNorm` normalization pattern (`C_ofNat` + `Nat.cast_ofNat`).
- **Used by**: `OmegaPullbackCoeff.wronskian_Φ_ΨSq_three` (L394, real `have haux := …` use).
- **Visibility**: public. **Lines**: 84–104; proof ~17 lines (mostly the literal multiplier).
- **LIVE.** Notes: `set_option maxRecDepth 4096 in`; runs at **default `maxHeartbeats 200000`** (a 160×
  reduction from the original 32M). No `sorry`.

---

### `lemma wronskian_aux_four`  — **LIVE**
- **Type**: `(W.preΨ₄ ^ 2 * W.Ψ₂Sq) ^ 2 − (derivative (W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 − W.Ψ₃ ^ 3)) * (W.preΨ₄ ^ 2 * W.Ψ₂Sq) − W.Ψ₃ * (…) * derivative (W.preΨ₄ ^ 2 * W.Ψ₂Sq)) = C 4 * (W.Ψ₃ ^ 2 * W.preΨ₄ * (…) − W.preΨ₄ * (…) ^ 2)`
- **What**: the `m = 4` Wronskian auxiliary identity (Silverman III.3.7).
- **How**: `linear_combination (norm := simp only […]; ring) M₄ · b_relation_poly W` where `M₄` is the
  explicit **degree-26** multiplier in `b₂,b₄,b₆,b₈` (computed offline by polynomial division — the long
  `Polynomial.C (...) * X^k` sum, L132–158).
- **Hypotheses**: none (any `CommRing R`).
- **Uses from project**: `b_relation_poly` (this file); `Ψ₃`, `preΨ₄`, `Ψ₂Sq` (mathlib); `CNorm` pattern.
- **Used by**: `OmegaPullbackCoeff.wronskian_Φ_ΨSq_four` (L451, real use).
- **Visibility**: public. **Lines**: 106–158; proof body dominated by the ~26-term multiplier.
- **LIVE.** Notes: **`set_option maxHeartbeats 400000 in`** (2× default) + `maxRecDepth 4096 in`. The
  file's docstring carries a **TODO** to reduce to default 200K and four candidate strategies (none yet
  applied). No `sorry`. The degree-26 multiplier (~25 lines of `C(...)·X^k`) is the single largest literal
  in the project.

---

## File Summary

- **Role in proof**: supplies the `m = 3, 4` base cases of the EDS/division-polynomial Wronskian recursion
  `wronskian_Φ_ΨSq` (`OmegaPullbackCoeff.lean`). That recursion (whose `m ≥ 5` inductive step carries a
  `sorryAx` per the OmegaPullbackCoeff notes, L953 — **not** in these aux lemmas) underlies the
  `#E[ℓ] = ℓ²` separability facts used throughout Route 2A. These two lemmas are themselves **sorry-free**.
- **(a) Dead/unused declarations**: none. All three LIVE.
- **(b) Scratch/superseded sub-routes**: none. This file *is* the cleaned-up isolation of identities that
  previously lived (much more expensively) in `OmegaPullbackCoeff.lean` (see the comments there, L360–406).
- **(c) Hand-rolled vs mathlib — Wronskian API**: **⚠️ mathlib HAS a Wronskian API** in
  `Mathlib.RingTheory.Polynomial.Wronskian`: `Polynomial.wronskian a b = a·b' − a'·b`, the bilinear map
  `wronskianBilin`, `wronskian_eq_of_sum_zero`, `wronskian_self_eq_zero`/`isAlt`, and degree bounds
  (`degree_wronskian_lt_add`, `natDegree_wronskian_lt_add`, `IsCoprime.wronskian_eq_zero_iff`). **The
  project does not import or use it** — these identities and the `wronskian_X_mul_sub` /
  `wronskian_Φ_ΨSq_*` helpers in `OmegaPullbackCoeff` are written out longhand in the `ab' − a'b` shape.
  The *content* here (division-polynomial-specific factoring identities) is genuinely not in mathlib, so
  the auxiliary lemmas can't be replaced wholesale — but the surrounding `OmegaPullbackCoeff` Wronskian
  scaffolding (`wronskian_X_mul_sub` and the `derivative(Φ)·ΨSq − Φ·derivative(ΨSq)` shape) could be
  re-expressed via `Polynomial.wronskian`/`wronskianBilin` to inherit bilinearity lemmas and the
  alternating/degree API. **Recommend a follow-up to adopt mathlib's `Polynomial.wronskian`.**
- **(d) Moral duplication**: `wronskian_aux_three`/`_four` share the identical `linear_combination (norm :=
  simp only […]; ring) M · b_relation_poly W` skeleton (only the multiplier and the LHS/RHS differ) — this
  is inherent to the offline-multiplier method, not worth abstracting.
- **(e) Under-general statements**: appropriately general (`CommRing R`, no field/elliptic hypotheses).
- **Cleanup flags**:
  - `wronskian_aux_four` `maxHeartbeats 400000` — open **TODO** to reduce to default (documented strategies
    in the file header).
  - Adopt mathlib `Polynomial.wronskian` API (see (c)).
  - The multiplier polynomials are derived by `scripts/compute_multipliers.py` (confirmed present, alongside
    `gen_m4_multiplier.py` and the `verify_*` helpers) — reproducible.
