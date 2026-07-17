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

/-- **[BRIDGE-P algebraic form]** On an origin-marked chart (`a₆ = 0`), the cleared
doubling-equals-negation condition at `(0, 0)` IS the `BRIDGE-P` identity
`a₂a₃² − a₄a₁a₃ − a₄² = 0` (`N(0,0) = a₄`, `d(0,0) = a₃`). Provided directly for the
assembly; the content is the scheme-level `3 • σ = 0 ⟹ x(2σ) = x(σ)` input. -/
theorem bridgeP_of_dbl_origin (ha₆ : W.a₆ = 0)
    (hdbl : (W.tangentNum 0 0) ^ 2 + W.a₁ * (W.tangentNum 0 0) * (W.tangentDen 0 0)
      - (W.a₂ + 3 * 0) * (W.tangentDen 0 0) ^ 2 = 0) :
    W.a₂ * W.a₃ ^ 2 - W.a₄ * W.a₁ * W.a₃ - W.a₄ ^ 2 = 0 := by
  simp only [tangentNum, tangentDen] at hdbl
  linear_combination (norm := ring_nf) (-1 : R) * hdbl

/-- **[BRIDGE-Q flex factorization]** On a flex chart (`a₂ = a₄ = a₆ = 0`) the
`3`-division polynomial factors as `Ψ₃(p) = p · (3p³ + a₁²p² + 3a₁a₃p + 3a₃²)`. -/
theorem Ψ₃_eval_flex (ha₂ : W.a₂ = 0) (ha₄ : W.a₄ = 0) (ha₆ : W.a₆ = 0) (p : R) :
    W.Ψ₃.eval p = p * (3 * p ^ 3 + W.a₁ ^ 2 * p ^ 2 + 3 * W.a₁ * W.a₃ * p
      + 3 * W.a₃ ^ 2) := by
  simp only [Ψ₃, b₂, b₄, b₆, b₈, ha₂, ha₄, ha₆, eval_add, eval_mul, eval_pow,
    eval_ofNat, eval_C, eval_X]
  ring

/-- **[BRIDGE-Q algebraic form]** On a flex chart with `Q = (p, q)` roots of `Ψ₃` and `p`
a unit, the `BRIDGE-Q` flex cubic vanishes: `3p³ + a₁²p² + 3a₁a₃p + 3a₃² = 0`. -/
theorem bridgeQ_cubic_of_Ψ₃ (ha₂ : W.a₂ = 0) (ha₄ : W.a₄ = 0) (ha₆ : W.a₆ = 0)
    (p : R) (hp : IsUnit p) (hΨ : W.Ψ₃.eval p = 0) :
    3 * p ^ 3 + W.a₁ ^ 2 * p ^ 2 + 3 * W.a₁ * W.a₃ * p + 3 * W.a₃ ^ 2 = 0 := by
  rw [Ψ₃_eval_flex W ha₂ ha₄ ha₆ p] at hΨ
  exact hp.mul_right_eq_zero.mp hΨ
