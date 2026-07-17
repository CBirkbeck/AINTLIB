/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# The ring-level `3`-torsion coordinate certificate (KM L4-iii / CHARTER-K, K1)

**[KM-W0 / hArb BRIDGE core]** The purely-algebraic heart of the two hArb bridges
(`BRIDGE-P`, `BRIDGE-Q`): over ANY commutative ring `R`, a Weierstrass point `(p, q)`
whose doubling equals its negation (`x(2P) = x(P)`, cleared of the `ψ₂`-denominator)
roots the `3`-division polynomial `Ψ₃`. This is a `linear_combination` certificate —
non-reduced-tolerant, unlike the field-level `psi3_eval_eq_zero_of_three_zsmul`
(`E3NormalForm.lean`), which the `ε`-example (`y²+y = x³+a₄x` over `ℤ[a₄]/(a₄²)`) shows is
insufficient: the `3`-torsion ideal is `(a₄²)`, not radical, so only the exact ring
identity `Ψ₃(0) = −a₄² = 0` holds — never `a₄ = 0`.

Certificate (CAS-verified, stated in `E3NormalForm.lean:144` and `TateNormalForm.lean:259`):
`N² + a₁·N·d − (a₂ + 3p)·d² + Ψ₃(p) = −(b₂ + 12p)·(curve defect)`,
where `N = 3p² + 2a₂p + a₄ − a₁q` (tangent slope numerator) and `d = 2q + a₁p + a₃ = ψ₂`.
So on the curve, the cleared doubling condition `N² + a₁Nd − (a₂+3p)d² = 0` gives `Ψ₃(p) = 0`.
-/

open Polynomial WeierstrassCurve

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The tangent-slope numerator at `(p, q)`: `3p² + 2a₂p + a₄ − a₁q`. -/
def tangentNum (p q : R) : R := 3 * p ^ 2 + 2 * W.a₂ * p + W.a₄ - W.a₁ * q

/-- The tangent-slope denominator at `(p, q)`: `2q + a₁p + a₃` (the `ψ₂`-value; `2P` is
finite exactly where this is a unit). -/
def tangentDen (p q : R) : R := 2 * q + W.a₁ * p + W.a₃

/-- **[LEAF A — the ring-level `3`-torsion certificate ★]** If `(p, q)` lies on the
curve and the cleared doubling-equals-negation condition holds
(`N² + a₁Nd − (a₂+3p)d² = 0`, i.e. `x(2P) = x(P)` after clearing `d²`), then `(p, q)`
roots the `3`-division polynomial: `Ψ₃.eval p = 0`. Pure `linear_combination`, valid over
any commutative ring (no field, no reducedness). -/
theorem Ψ₃_eval_eq_zero_of_dbl_eq_neg (p q : R)
    (hcurve : q ^ 2 + W.a₁ * p * q + W.a₃ * q
      = p ^ 3 + W.a₂ * p ^ 2 + W.a₄ * p + W.a₆)
    (hdbl : (W.tangentNum p q) ^ 2 + W.a₁ * (W.tangentNum p q) * (W.tangentDen p q)
      - (W.a₂ + 3 * p) * (W.tangentDen p q) ^ 2 = 0) :
    W.Ψ₃.eval p = 0 := by
  simp only [Ψ₃, tangentNum, tangentDen, b₂, b₄, b₆, b₈, eval_add, eval_mul, eval_pow,
    eval_ofNat, eval_C, eval_X] at hdbl ⊢
  linear_combination (norm := ring_nf) (-1 : R) * hdbl
    + (-(W.a₁ ^ 2 + 4 * W.a₂ + 12 * p)) * hcurve
