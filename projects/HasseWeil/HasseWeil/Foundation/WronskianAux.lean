/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Algebra.Polynomial.Derivation
import HasseWeil.Foundation.WronskianAux.CNorm

/-!
# Wronskian identities for Weierstrass division polynomials

Two auxiliary polynomial identities used in the proof of the division-polynomial
Wronskian identity (Silverman III.3 Exercise 3.7):

* `wronskian_aux_three` — the `m = 3` case.
* `wronskian_aux_four` — the `m = 4` case.

## Strategy

Both identities are pure polynomial identities in `R[X]` that hold because of
`b_relation : 4·b₈ = b₂·b₆ - b₄²`. Concretely, `LHS - RHS` factors as
`M(X) · (4b₈ - b₂b₆ + b₄²)` in `ℤ[b₂,b₄,b₆,b₈,X]` for an explicit polynomial
`M`. The multipliers `M` were computed by dividing the expanded difference by
`(4b₈ - b₂b₆ + b₄²)` over `ℤ[b₂,b₄,b₆,b₈]` (with `b₈` as the leading variable);
see `scripts/compute_multipliers.py`.

The proof uses `linear_combination M · h_P` where `h_P` is `b_relation` lifted
to `R[X]`. The `C`-normalization lemmas imported from `CNorm.lean` handle the
`C (Nat.cast n : R)` vs `C (OfNat.ofNat n : R)` atomization issue that
otherwise blocks `ring` from closing the residual.

Resource usage (vs original):

* `wronskian_aux_three`: default `maxHeartbeats 200000` (was 32M, 160× reduction).
* `wronskian_aux_four`: default `maxHeartbeats 200000` (was 64M, and latterly 350000).

Getting `wronskian_aux_four` to the default did not need the quotient-ring construction
once considered here. The cost was elaborating the degree-26 multiplier `M(X)` inline
inside the `linear_combination` call, not `ring`'s normalization: `M` is now one
`private def` per `Xᵏ` coefficient (`wronskianFourMul1 … wronskianFourMul27`), summed by
`wronskianFourMultiplier`, and the `norm` block unfolds them by name so `ring` still sees
the full polynomial. Each coefficient elaborates comfortably inside the default budget;
splitting into 6 groups was still too coarse, one-per-coefficient works.

RAM usage: ~1-2 GB (was ~57 GB, ~30× reduction).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.3 Exercise 3.7.
-/

open WeierstrassCurve Polynomial

namespace HasseWeil

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

-- `b_relation` lifted to an equality in `R[X]`. The `C`-distributed statement shape is
-- load-bearing: the `wronskian_aux_*` proofs below pass this to `linear_combination`,
-- whose `ring` normalization treats each `C _` application as an atom.
private lemma b_relation_poly :
    ((4 : R[X]) * Polynomial.C W.b₈ : R[X]) =
      Polynomial.C W.b₂ * Polynomial.C W.b₆ - Polynomial.C W.b₄ ^ 2 := by
  simpa [Polynomial.C_ofNat] using congrArg Polynomial.C W.b_relation

/-- Wronskian auxiliary identity, `m = 3` case (Silverman III.3.7).
`4·Ψ₃³ + 2·preΨ₄·Ψ₂Sq·Ψ₃' − (preΨ₄·Ψ₂Sq)'·Ψ₃
= 3·preΨ₄·Ψ₂Sq² − 3·preΨ₄²`.

Multiplier: `M = b₈² + 4b₆b₈·X + 6b₄b₈·X² + 4b₂b₈·X³ + (b₂b₆ + 34b₈)·X⁴
               + 36b₆·X⁵ + 18b₄·X⁶ + 4b₂·X⁷ + 9·X⁸`. -/
lemma wronskian_aux_three :
    4 * W.Ψ₃ ^ 3 + 2 * W.preΨ₄ * W.Ψ₂Sq * Polynomial.derivative W.Ψ₃ -
      Polynomial.derivative (W.preΨ₄ * W.Ψ₂Sq) * W.Ψ₃ =
    Polynomial.C 3 * W.preΨ₄ * W.Ψ₂Sq ^ 2 - Polynomial.C 3 * W.preΨ₄ ^ 2 := by
  linear_combination (norm := (
    simp only [Ψ₃, preΨ₄, Ψ₂Sq,
      Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_X,
      Polynomial.derivative_C, Polynomial.derivative_ofNat,
      Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow,
      Polynomial.C_ofNat, Nat.cast_ofNat]
    ring))
    (Polynomial.C (W.b₈ ^ 2)
    + Polynomial.C (4 * W.b₆ * W.b₈) * Polynomial.X
    + Polynomial.C (6 * W.b₄ * W.b₈) * Polynomial.X ^ 2
    + Polynomial.C (4 * W.b₂ * W.b₈) * Polynomial.X ^ 3
    + Polynomial.C (W.b₂ * W.b₆ + 34 * W.b₈) * Polynomial.X ^ 4
    + Polynomial.C (36 * W.b₆) * Polynomial.X ^ 5
    + Polynomial.C (18 * W.b₄) * Polynomial.X ^ 6
    + Polynomial.C (4 * W.b₂) * Polynomial.X ^ 7
    + Polynomial.C 9 * Polynomial.X ^ 8) * b_relation_poly W

private noncomputable def wronskianFourMul1 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (-W.b₆ ^ 6 * W.b₈ ^ 2 + (-2 * W.b₆ ^ 2 * W.b₈ ^ 5) + 2 * W.b₄ * W.b₈ ^ 6 + (-W.b₄ ^
    2 * W.b₆ ^ 2 * W.b₈ ^ 4) + 2 * W.b₄ * W.b₆ ^ 4 * W.b₈ ^ 3)

private noncomputable def wronskianFourMul2 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (-26 * W.b₆ ^ 3 * W.b₈ ^ 4 + (-4 * W.b₆ ^ 7 * W.b₈) + 2 * W.b₂ * W.b₈ ^ 6 + (-4 *
    W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 4) + 2 * W.b₂ * W.b₆ ^ 4 * W.b₈ ^ 3 + 2 * W.b₄ * W.b₆ ^ 5 * W.b₈ ^ 2 +
    6 * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈ ^ 3 + 24 * W.b₄ * W.b₆ * W.b₈ ^ 5 + (-2 * W.b₂ * W.b₄ * W.b₆ ^ 2
    * W.b₈ ^ 4)) * Polynomial.X

private noncomputable def wronskianFourMul3 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (-4 * W.b₆ ^ 8 + 20 * W.b₈ ^ 6 + (-108 * W.b₆ ^ 4 * W.b₈ ^ 3) + (-4 * W.b₄ ^ 4 *
    W.b₈ ^ 4) + 28 * W.b₄ ^ 2 * W.b₈ ^ 5 + (-W.b₂ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 4) + (-18 * W.b₄ * W.b₆ ^
    6 * W.b₈) + (-2 * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈ ^ 3) + 6 * W.b₂ * W.b₆ ^ 5 * W.b₈ ^ 2 + 26 * W.b₂
    * W.b₆ * W.b₈ ^ 5 + 27 * W.b₄ ^ 2 * W.b₆ ^ 4 * W.b₈ ^ 2 + 54 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 4 +
    (-10 * W.b₂ * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 4) + 6 * W.b₂ * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 3) *
    Polynomial.X ^ 2

private noncomputable def wronskianFourMul4 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (-196 * W.b₆ ^ 5 * W.b₈ ^ 2 + (-28 * W.b₄ * W.b₆ ^ 7) + 280 * W.b₆ * W.b₈ ^ 5 + (-96
    * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 3) + (-16 * W.b₄ ^ 4 * W.b₆ * W.b₈ ^ 3) + (-16 * W.b₄ ^ 2 * W.b₆ ^ 5
    * W.b₈) + (-12 * W.b₂ * W.b₄ ^ 3 * W.b₈ ^ 4) + 40 * W.b₂ * W.b₄ * W.b₈ ^ 5 + 52 * W.b₄ ^ 3 *
    W.b₆ ^ 3 * W.b₈ ^ 2 + 96 * W.b₂ * W.b₆ ^ 2 * W.b₈ ^ 4 + 156 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 4 + (-16
    * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 3) + (-8 * W.b₂ ^ 2 * W.b₄ * W.b₆ * W.b₈ ^ 4) + 44 * W.b₂
    * W.b₄ * W.b₆ ^ 4 * W.b₈ ^ 2) * Polynomial.X ^ 3

private noncomputable def wronskianFourMul5 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (-136 * W.b₆ ^ 6 * W.b₈ + (-76 * W.b₄ ^ 2 * W.b₆ ^ 6) + (-9 * W.b₂ * W.b₆ ^ 7) + (-8
    * W.b₄ ^ 5 * W.b₈ ^ 3) + 12 * W.b₂ ^ 2 * W.b₈ ^ 5 + 48 * W.b₄ ^ 3 * W.b₈ ^ 4 + 356 * W.b₄ *
    W.b₈ ^ 5 + 1374 * W.b₆ ^ 2 * W.b₈ ^ 4 + (-508 * W.b₄ * W.b₆ ^ 4 * W.b₈ ^ 2) + (-13 * W.b₂ ^ 2 *
    W.b₄ ^ 2 * W.b₈ ^ 4) + (-2 * W.b₂ ^ 3 * W.b₆ * W.b₈ ^ 4) + 11 * W.b₂ ^ 2 * W.b₆ ^ 4 * W.b₈ ^ 2
    + 28 * W.b₄ ^ 4 * W.b₆ ^ 2 * W.b₈ ^ 2 + 30 * W.b₄ ^ 3 * W.b₆ ^ 4 * W.b₈ + 128 * W.b₂ * W.b₆ ^ 3
    * W.b₈ ^ 3 + 216 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 3 + (-52 * W.b₂ * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 3) +
    (-20 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 3) + 30 * W.b₂ * W.b₄ * W.b₆ ^ 5 * W.b₈ + 81 * W.b₂
    * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈ ^ 2 + 240 * W.b₂ * W.b₄ * W.b₆ * W.b₈ ^ 4) * Polynomial.X ^ 4

private noncomputable def wronskianFourMul6 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (-2 * W.b₆ ^ 7 + (-100 * W.b₄ ^ 3 * W.b₆ ^ 5) + 188 * W.b₂ * W.b₈ ^ 5 + 3056 * W.b₆
    ^ 3 * W.b₈ ^ 3 + (-468 * W.b₄ * W.b₆ ^ 5 * W.b₈) + (-410 * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈ ^ 2) +
    (-46 * W.b₂ * W.b₄ * W.b₆ ^ 6) + (-28 * W.b₂ * W.b₆ ^ 4 * W.b₈ ^ 2) + (-24 * W.b₂ * W.b₄ ^ 4 *
    W.b₈ ^ 3) + (-6 * W.b₂ ^ 3 * W.b₄ * W.b₈ ^ 4) + (-6 * W.b₂ ^ 3 * W.b₆ ^ 2 * W.b₈ ^ 3) + 14 *
    W.b₂ ^ 2 * W.b₆ ^ 5 * W.b₈ + 56 * W.b₄ ^ 4 * W.b₆ ^ 3 * W.b₈ + 64 * W.b₂ * W.b₄ ^ 2 * W.b₈ ^ 4
    + 68 * W.b₂ ^ 2 * W.b₆ * W.b₈ ^ 4 + 248 * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 3 + 3168 * W.b₄ * W.b₆ *
    W.b₈ ^ 4 + (-58 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 3) + 24 * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 2 *
    W.b₈ ^ 2 + 24 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 2 + 122 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 4 * W.b₈
    + 528 * W.b₂ * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 3) * Polynomial.X ^ 5

private noncomputable def wronskianFourMul7 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (664 * W.b₈ ^ 5 + (-W.b₂ ^ 4 * W.b₈ ^ 4) + (-64 * W.b₄ ^ 4 * W.b₆ ^ 4) + (-6 * W.b₂
    ^ 2 * W.b₆ ^ 6) + 116 * W.b₄ * W.b₆ ^ 6 + 116 * W.b₄ ^ 4 * W.b₈ ^ 3 + 1500 * W.b₄ ^ 2 * W.b₈ ^
    4 + 2572 * W.b₆ ^ 4 * W.b₈ ^ 2 + (-W.b₂ ^ 3 * W.b₆ ^ 3 * W.b₈ ^ 2) + (-758 * W.b₄ ^ 2 * W.b₆ ^
    4 * W.b₈) + (-110 * W.b₂ * W.b₆ ^ 5 * W.b₈) + (-106 * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈ ^ 2) + (-85 *
    W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 5) + (-26 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₈ ^ 3) + 12 * W.b₂ ^ 2 * W.b₄ *
    W.b₈ ^ 4 + 24 * W.b₄ ^ 5 * W.b₆ ^ 2 * W.b₈ + 168 * W.b₂ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 3 + 1610 * W.b₂
    * W.b₆ * W.b₈ ^ 4 + 10544 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 3 + (-27 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 2
    * W.b₈ ^ 2) + (-26 * W.b₂ ^ 3 * W.b₄ * W.b₆ * W.b₈ ^ 3) + (-20 * W.b₂ * W.b₄ ^ 4 * W.b₆ * W.b₈
    ^ 2) + 76 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 4 * W.b₈ + 78 * W.b₂ * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 2 + 156 *
    W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 3 * W.b₈ + 484 * W.b₂ * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 3) * Polynomial.X ^ 6

private noncomputable def wronskianFourMul8 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (-336 * W.b₆ ^ 5 * W.b₈ + (-16 * W.b₄ ^ 5 * W.b₆ ^ 3) + (-4 * W.b₂ ^ 3 * W.b₈ ^ 4) +
    48 * W.b₂ * W.b₆ ^ 6 + 516 * W.b₄ ^ 2 * W.b₆ ^ 5 + 6552 * W.b₆ * W.b₈ ^ 4 + (-1032 * W.b₄ ^ 3 *
    W.b₆ ^ 3 * W.b₈) + (-68 * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 4) + (-20 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 5) +
    (-12 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₈ ^ 3) + (-4 * W.b₂ ^ 4 * W.b₆ * W.b₈ ^ 3) + 12 * W.b₂ ^ 3 *
    W.b₆ ^ 4 * W.b₈ + 80 * W.b₂ ^ 2 * W.b₆ ^ 3 * W.b₈ ^ 2 + 212 * W.b₄ ^ 4 * W.b₆ * W.b₈ ^ 2 + 304
    * W.b₂ * W.b₄ ^ 3 * W.b₈ ^ 3 + 1272 * W.b₂ * W.b₄ * W.b₈ ^ 4 + 5552 * W.b₂ * W.b₆ ^ 2 * W.b₈ ^
    3 + 11312 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 3 + 12336 * W.b₄ * W.b₆ ^ 3 * W.b₈ ^ 2 + (-472 * W.b₂ *
    W.b₄ * W.b₆ ^ 4 * W.b₈) + (-44 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 2) + (-28 * W.b₂ ^ 3 *
    W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 2) + 64 * W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 2 * W.b₈ + 108 * W.b₂ * W.b₄ ^ 2 *
    W.b₆ ^ 2 * W.b₈ ^ 2 + 116 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈ + 240 * W.b₂ ^ 2 * W.b₄ *
    W.b₆ * W.b₈ ^ 3) * Polynomial.X ^ 7

private noncomputable def wronskianFourMul9 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (-883 * W.b₆ ^ 6 + (-W.b₂ ^ 3 * W.b₆ ^ 5) + 198 * W.b₄ ^ 5 * W.b₈ ^ 2 + 216 * W.b₂ ^
    2 * W.b₈ ^ 4 + 790 * W.b₄ ^ 3 * W.b₆ ^ 4 + 4720 * W.b₄ ^ 3 * W.b₈ ^ 3 + 5526 * W.b₄ * W.b₈ ^ 4
    + 26236 * W.b₆ ^ 2 * W.b₈ ^ 3 + (-918 * W.b₄ ^ 4 * W.b₆ ^ 2 * W.b₈) + (-270 * W.b₄ * W.b₆ ^ 4 *
    W.b₈) + (-70 * W.b₂ ^ 2 * W.b₆ ^ 4 * W.b₈) + (-22 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 4) + (-20 *
    W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 3) + (-6 * W.b₂ ^ 4 * W.b₆ ^ 2 * W.b₈ ^ 2) + (-2 * W.b₂ ^ 4 * W.b₄ *
    W.b₈ ^ 3) + 32 * W.b₂ ^ 3 * W.b₆ * W.b₈ ^ 3 + 300 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₈ ^ 3 + 354 * W.b₂
    * W.b₄ * W.b₆ ^ 5 + 7316 * W.b₂ * W.b₆ ^ 3 * W.b₈ ^ 2 + 21030 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 2
    + (-1346 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈) + (-33 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 2) +
    30 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 3 * W.b₈ + 54 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈ + 72 * W.b₂
    ^ 2 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 2 + 588 * W.b₂ * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 2 + 10848 * W.b₂ *
    W.b₄ * W.b₆ * W.b₈ ^ 3) * Polynomial.X ^ 8

private noncomputable def wronskianFourMul10 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (-4494 * W.b₄ * W.b₆ ^ 5 + 62 * W.b₂ ^ 2 * W.b₆ ^ 5 + 506 * W.b₄ ^ 4 * W.b₆ ^ 3 +
    1870 * W.b₂ * W.b₈ ^ 4 + 47004 * W.b₆ ^ 3 * W.b₈ ^ 2 + (-312 * W.b₄ ^ 5 * W.b₆ * W.b₈) + (-8 *
    W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 3) + (-2 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 4) + (-2 * W.b₂ ^ 3 * W.b₆ ^ 2
    * W.b₈ ^ 2) + 2 * W.b₂ ^ 4 * W.b₆ ^ 3 * W.b₈ + 136 * W.b₂ ^ 3 * W.b₄ * W.b₈ ^ 3 + 550 * W.b₂ *
    W.b₄ ^ 4 * W.b₈ ^ 2 + 706 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 4 + 1610 * W.b₄ ^ 2 * W.b₆ ^ 3 * W.b₈ +
    2042 * W.b₂ * W.b₆ ^ 4 * W.b₈ + 2344 * W.b₂ ^ 2 * W.b₆ * W.b₈ ^ 3 + 7136 * W.b₂ * W.b₄ ^ 2 *
    W.b₈ ^ 3 + 18064 * W.b₄ ^ 3 * W.b₆ * W.b₈ ^ 2 + 49456 * W.b₄ * W.b₆ * W.b₈ ^ 3 + (-1592 * W.b₂
    * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈) + (-600 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 3 * W.b₈) + (-10 * W.b₂ ^ 4 *
    W.b₄ * W.b₆ * W.b₈ ^ 2) + 18 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ + 546 * W.b₂ ^ 2 * W.b₄ ^
    2 * W.b₆ * W.b₈ ^ 2 + 21708 * W.b₂ * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 2) * Polynomial.X ^ 9

private noncomputable def wronskianFourMul11 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (3532 * W.b₈ ^ 4 + (-9537 * W.b₄ ^ 2 * W.b₆ ^ 4) + (-936 * W.b₂ * W.b₆ ^ 5) + 24 *
    W.b₂ ^ 4 * W.b₈ ^ 3 + 114 * W.b₄ ^ 5 * W.b₆ ^ 2 + 6304 * W.b₄ ^ 4 * W.b₈ ^ 2 + 27864 * W.b₄ ^ 2
    * W.b₈ ^ 3 + 35644 * W.b₆ ^ 4 * W.b₈ + (-W.b₂ ^ 5 * W.b₆ * W.b₈ ^ 2) + (-W.b₂ ^ 3 * W.b₄ ^ 2 *
    W.b₆ ^ 3) + (-98 * W.b₂ ^ 3 * W.b₆ ^ 3 * W.b₈) + 192 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 4 + 532 * W.b₂
    * W.b₄ ^ 3 * W.b₆ ^ 3 + 578 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₈ ^ 2 + 3608 * W.b₂ ^ 2 * W.b₄ * W.b₈ ^
    3 + 4818 * W.b₂ ^ 2 * W.b₆ ^ 2 * W.b₈ ^ 2 + 5778 * W.b₄ ^ 3 * W.b₆ ^ 2 * W.b₈ + 19028 * W.b₂ *
    W.b₆ * W.b₈ ^ 3 + 131228 * W.b₄ * W.b₆ ^ 2 * W.b₈ ^ 2 + (-966 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 2
    * W.b₈) + (-598 * W.b₂ * W.b₄ ^ 4 * W.b₆ * W.b₈) + 2 * W.b₂ ^ 4 * W.b₄ * W.b₆ ^ 2 * W.b₈ + 222
    * W.b₂ ^ 3 * W.b₄ * W.b₆ * W.b₈ ^ 2 + 6986 * W.b₂ * W.b₄ * W.b₆ ^ 3 * W.b₈ + 26712 * W.b₂ *
    W.b₄ ^ 2 * W.b₆ * W.b₈ ^ 2) * Polynomial.X ^ 10

private noncomputable def wronskianFourMul12 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (8884 * W.b₆ ^ 5 + (-9916 * W.b₄ ^ 3 * W.b₆ ^ 3) + 12 * W.b₂ ^ 3 * W.b₆ ^ 4 + 640 *
    W.b₂ ^ 3 * W.b₈ ^ 3 + 36848 * W.b₆ * W.b₈ ^ 3 + (-4596 * W.b₂ * W.b₄ * W.b₆ ^ 4) + 36 * W.b₂ ^
    4 * W.b₆ * W.b₈ ^ 2 + 132 * W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 2 + 180 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 3 +
    288 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₈ ^ 2 + 1968 * W.b₂ ^ 2 * W.b₆ ^ 3 * W.b₈ + 6096 * W.b₄ ^ 4 *
    W.b₆ * W.b₈ + 11592 * W.b₂ * W.b₄ ^ 3 * W.b₈ ^ 2 + 24400 * W.b₂ * W.b₄ * W.b₈ ^ 3 + 49728 *
    W.b₂ * W.b₆ ^ 2 * W.b₈ ^ 2 + 124416 * W.b₄ * W.b₆ ^ 3 * W.b₈ + 134568 * W.b₄ ^ 2 * W.b₆ * W.b₈
    ^ 2 + (-408 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ * W.b₈) + (-240 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 2 * W.b₈) +
    12480 * W.b₂ ^ 2 * W.b₄ * W.b₆ * W.b₈ ^ 2 + 13560 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈) *
    Polynomial.X ^ 11

private noncomputable def wronskianFourMul13 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (-4902 * W.b₄ ^ 4 * W.b₆ ^ 2 + (-545 * W.b₂ ^ 2 * W.b₆ ^ 4) + 1932 * W.b₄ ^ 5 * W.b₈
    + 5736 * W.b₂ ^ 2 * W.b₈ ^ 3 + 35344 * W.b₄ * W.b₆ ^ 4 + 45144 * W.b₄ * W.b₈ ^ 3 + 46752 * W.b₄
    ^ 3 * W.b₈ ^ 2 + 105356 * W.b₆ ^ 2 * W.b₈ ^ 2 + (-7315 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 3) + (-18 *
    W.b₂ ^ 4 * W.b₆ ^ 2 * W.b₈) + 18 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 3 + 50 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆
    ^ 2 + 68 * W.b₂ ^ 4 * W.b₄ * W.b₈ ^ 2 + 1960 * W.b₂ ^ 3 * W.b₆ * W.b₈ ^ 2 + 7602 * W.b₂ ^ 2 *
    W.b₄ ^ 2 * W.b₈ ^ 2 + 45016 * W.b₂ * W.b₆ ^ 3 * W.b₈ + 173648 * W.b₄ ^ 2 * W.b₆ ^ 2 * W.b₈ +
    (-118 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ * W.b₈) + 7284 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 2 * W.b₈ + 12548 *
    W.b₂ * W.b₄ ^ 3 * W.b₆ * W.b₈ + 107360 * W.b₂ * W.b₄ * W.b₆ * W.b₈ ^ 2) * Polynomial.X ^ 12

private noncomputable def wronskianFourMul14 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (-912 * W.b₄ ^ 5 * W.b₆ + 6 * W.b₂ ^ 5 * W.b₈ ^ 2 + 12024 * W.b₂ * W.b₆ ^ 4 + 20232
    * W.b₂ * W.b₈ ^ 3 + 59770 * W.b₄ ^ 2 * W.b₆ ^ 3 + 112576 * W.b₆ ^ 3 * W.b₈ + (-4656 * W.b₂ *
    W.b₄ ^ 3 * W.b₆ ^ 2) + (-1600 * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 3) + 6 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^
    2 + 1206 * W.b₂ ^ 3 * W.b₆ ^ 2 * W.b₈ + 2124 * W.b₂ ^ 3 * W.b₄ * W.b₈ ^ 2 + 3892 * W.b₂ * W.b₄
    ^ 4 * W.b₈ + 22208 * W.b₂ ^ 2 * W.b₆ * W.b₈ ^ 2 + 54192 * W.b₂ * W.b₄ ^ 2 * W.b₈ ^ 2 + 108840 *
    W.b₄ ^ 3 * W.b₆ * W.b₈ + 217088 * W.b₄ * W.b₆ * W.b₈ ^ 2 + (-12 * W.b₂ ^ 4 * W.b₄ * W.b₆ *
    W.b₈) + 8514 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ * W.b₈ + 128256 * W.b₂ * W.b₄ * W.b₆ ^ 2 * W.b₈) *
    Polynomial.X ^ 13

private noncomputable def wronskianFourMul15 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (24720 * W.b₈ ^ 3 + 39812 * W.b₆ ^ 4 + (-69 * W.b₂ ^ 3 * W.b₆ ^ 3) + 210 * W.b₂ ^ 4
    * W.b₈ ^ 2 + 24836 * W.b₄ ^ 4 * W.b₈ + 51722 * W.b₄ ^ 3 * W.b₆ ^ 2 + 101464 * W.b₄ ^ 2 * W.b₈ ^
    2 + (-1395 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 2) + (-1026 * W.b₂ * W.b₄ ^ 4 * W.b₆) + 2946 * W.b₂ ^
    2 * W.b₄ ^ 3 * W.b₈ + 20544 * W.b₂ ^ 2 * W.b₄ * W.b₈ ^ 2 + 24296 * W.b₂ ^ 2 * W.b₆ ^ 2 * W.b₈ +
    40930 * W.b₂ * W.b₄ * W.b₆ ^ 3 + 85700 * W.b₂ * W.b₆ * W.b₈ ^ 2 + 308736 * W.b₄ * W.b₆ ^ 2 *
    W.b₈ + 2394 * W.b₂ ^ 3 * W.b₄ * W.b₆ * W.b₈ + 116300 * W.b₂ * W.b₄ ^ 2 * W.b₆ * W.b₈) *
    Polynomial.X ^ 14

private noncomputable def wronskianFourMul16 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (2472 * W.b₂ ^ 3 * W.b₈ ^ 2 + 7232 * W.b₂ ^ 2 * W.b₆ ^ 3 + 22172 * W.b₄ ^ 4 * W.b₆ +
    108016 * W.b₆ * W.b₈ ^ 2 + 132592 * W.b₄ * W.b₆ ^ 3 + (-380 * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆) +
    (-100 * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 2) + 236 * W.b₂ ^ 4 * W.b₆ * W.b₈ + 1060 * W.b₂ ^ 3 * W.b₄ ^ 2
    * W.b₈ + 33232 * W.b₂ * W.b₄ ^ 3 * W.b₈ + 50972 * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 2 + 72816 * W.b₂ *
    W.b₄ * W.b₈ ^ 2 + 110896 * W.b₂ * W.b₆ ^ 2 * W.b₈ + 263536 * W.b₄ ^ 2 * W.b₆ * W.b₈ + 40912 *
    W.b₂ ^ 2 * W.b₄ * W.b₆ * W.b₈) * Polynomial.X ^ 15

private noncomputable def wronskianFourMul17 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (3710 * W.b₄ ^ 5 + 8 * W.b₂ ^ 4 * W.b₆ ^ 2 + 12320 * W.b₂ ^ 2 * W.b₈ ^ 2 + 43908 *
    W.b₂ * W.b₆ ^ 3 + 70896 * W.b₄ ^ 3 * W.b₈ + 85422 * W.b₄ * W.b₈ ^ 2 + 149190 * W.b₆ ^ 2 * W.b₈
    + 157539 * W.b₄ ^ 2 * W.b₆ ^ 2 + (-37 * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆) + 182 * W.b₂ ^ 4 * W.b₄ *
    W.b₈ + 4632 * W.b₂ ^ 3 * W.b₆ * W.b₈ + 16268 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₈ + 16744 * W.b₂ ^ 2 *
    W.b₄ * W.b₆ ^ 2 + 27268 * W.b₂ * W.b₄ ^ 3 * W.b₆ + 175520 * W.b₂ * W.b₄ * W.b₆ * W.b₈) *
    Polynomial.X ^ 16

private noncomputable def wronskianFourMul18 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (65230 * W.b₆ ^ 3 + 12 * W.b₂ ^ 5 * W.b₈ + 1794 * W.b₂ ^ 3 * W.b₆ ^ 2 + 5302 * W.b₂
    * W.b₄ ^ 4 + 27230 * W.b₂ * W.b₈ ^ 2 + 79828 * W.b₄ ^ 3 * W.b₆ + 6 * W.b₂ ^ 4 * W.b₄ * W.b₆ +
    3432 * W.b₂ ^ 3 * W.b₄ * W.b₈ + 12422 * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ + 27992 * W.b₂ ^ 2 * W.b₆ *
    W.b₈ + 66496 * W.b₂ * W.b₄ ^ 2 * W.b₈ + 97734 * W.b₂ * W.b₄ * W.b₆ ^ 2 + 223992 * W.b₄ * W.b₆ *
    W.b₈) * Polynomial.X ^ 17

private noncomputable def wronskianFourMul19 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (14684 * W.b₄ ^ 4 + 21868 * W.b₈ ^ 2 + W.b₂ ^ 5 * W.b₆ + 264 * W.b₂ ^ 4 * W.b₈ +
    2982 * W.b₂ ^ 2 * W.b₄ ^ 3 + 14687 * W.b₂ ^ 2 * W.b₆ ^ 2 + 81548 * W.b₄ ^ 2 * W.b₈ + 139902 *
    W.b₄ * W.b₆ ^ 2 + 2466 * W.b₂ ^ 3 * W.b₄ * W.b₆ + 20136 * W.b₂ ^ 2 * W.b₄ * W.b₈ + 67922 * W.b₂
    * W.b₆ * W.b₈ + 70114 * W.b₂ * W.b₄ ^ 2 * W.b₆) * Polynomial.X ^ 18

private noncomputable def wronskianFourMul20 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (180 * W.b₂ ^ 4 * W.b₆ + 824 * W.b₂ ^ 3 * W.b₄ ^ 2 + 1984 * W.b₂ ^ 3 * W.b₈ + 16324
    * W.b₂ * W.b₄ ^ 3 + 40320 * W.b₂ * W.b₆ ^ 2 + 57464 * W.b₆ * W.b₈ + 97500 * W.b₄ ^ 2 * W.b₆ +
    20040 * W.b₂ ^ 2 * W.b₄ * W.b₆ + 47624 * W.b₂ * W.b₄ * W.b₈) * Polynomial.X ^ 19

private noncomputable def wronskianFourMul21 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (22160 * W.b₄ ^ 3 + 36374 * W.b₆ ^ 2 + 112 * W.b₂ ^ 4 * W.b₄ + 1874 * W.b₂ ^ 3 *
    W.b₆ + 6675 * W.b₂ ^ 2 * W.b₄ ^ 2 + 6828 * W.b₂ ^ 2 * W.b₈ + 39492 * W.b₄ * W.b₈ + 54192 * W.b₂
    * W.b₄ * W.b₆) * Polynomial.X ^ 20

private noncomputable def wronskianFourMul22 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (6 * W.b₂ ^ 5 + 1194 * W.b₂ ^ 3 * W.b₄ + 7420 * W.b₂ ^ 2 * W.b₆ + 11068 * W.b₂ *
    W.b₈ + 17840 * W.b₂ * W.b₄ ^ 2 + 48224 * W.b₄ * W.b₆) * Polynomial.X ^ 21

private noncomputable def wronskianFourMul23 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (79 * W.b₂ ^ 4 + 6872 * W.b₈ + 15692 * W.b₄ ^ 2 + 4724 * W.b₂ ^ 2 * W.b₄ + 12978 *
    W.b₂ * W.b₆) * Polynomial.X ^ 22

private noncomputable def wronskianFourMul24 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (412 * W.b₂ ^ 3 + 8440 * W.b₆ + 8216 * W.b₂ * W.b₄) * Polynomial.X ^ 23

private noncomputable def wronskianFourMul25 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (1064 * W.b₂ ^ 2 + 5306 * W.b₄) * Polynomial.X ^ 24

private noncomputable def wronskianFourMul26 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C (1362 * W.b₂) * Polynomial.X ^ 25

private noncomputable def wronskianFourMul27 (W : WeierstrassCurve R) : Polynomial R :=
  Polynomial.C 692 * Polynomial.X ^ 26

/-- The degree-26 multiplier `M(X)` of `wronskian_aux_four`, one definition per `Xᵏ`
coefficient so that each elaborates inside the default heartbeat budget. -/
private noncomputable def wronskianFourMultiplier (W : WeierstrassCurve R) : Polynomial R :=
  wronskianFourMul1 W + wronskianFourMul2 W + wronskianFourMul3 W + wronskianFourMul4 W
    + wronskianFourMul5 W + wronskianFourMul6 W + wronskianFourMul7 W + wronskianFourMul8 W
    + wronskianFourMul9 W + wronskianFourMul10 W + wronskianFourMul11 W + wronskianFourMul12 W
    + wronskianFourMul13 W + wronskianFourMul14 W + wronskianFourMul15 W + wronskianFourMul16 W
    + wronskianFourMul17 W + wronskianFourMul18 W + wronskianFourMul19 W + wronskianFourMul20 W
    + wronskianFourMul21 W + wronskianFourMul22 W + wronskianFourMul23 W + wronskianFourMul24 W
    + wronskianFourMul25 W + wronskianFourMul26 W + wronskianFourMul27 W

-- Measured minimum (2026-07-16, #7205): 300000 fails at `synthesize pending MVars`
-- (ring's normalization of the degree-30 residual), 350000 passes. Removal attempts:
-- default budget and a type-ascribed multiplier both time out — the structural fix is the
-- quotient-ring route documented above (producer/decompose work).
/-- Wronskian auxiliary identity, `m = 4` case (Silverman III.3.7).

Multiplier `M(X)` is a degree-26 polynomial in `W.b₂, W.b₄, W.b₆, W.b₈` with
integer coefficients, computed offline by polynomial division of `LHS - RHS`
by `(4b₈ - b₂b₆ + b₄²)` over `ℤ[b₂, b₄, b₆, b₈]`. See
`scripts/compute_multipliers.py` for the derivation. -/
lemma wronskian_aux_four :
    (W.preΨ₄ ^ 2 * W.Ψ₂Sq) ^ 2 -
    (Polynomial.derivative (W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3)) *
        (W.preΨ₄ ^ 2 * W.Ψ₂Sq) -
      W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) *
        Polynomial.derivative (W.preΨ₄ ^ 2 * W.Ψ₂Sq)) =
    Polynomial.C 4 *
      (W.Ψ₃ ^ 2 * W.preΨ₄ *
          (W.Ψ₃ * ((W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) - W.preΨ₄ ^ 2)) -
        W.preΨ₄ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3) ^ 2) := by
  linear_combination (norm := (
    simp only [wronskianFourMultiplier, wronskianFourMul1, wronskianFourMul2, wronskianFourMul3, wronskianFourMul4, wronskianFourMul5, wronskianFourMul6, wronskianFourMul7, wronskianFourMul8, wronskianFourMul9, wronskianFourMul10, wronskianFourMul11, wronskianFourMul12, wronskianFourMul13, wronskianFourMul14, wronskianFourMul15, wronskianFourMul16, wronskianFourMul17, wronskianFourMul18, wronskianFourMul19, wronskianFourMul20, wronskianFourMul21, wronskianFourMul22, wronskianFourMul23, wronskianFourMul24, wronskianFourMul25, wronskianFourMul26, wronskianFourMul27,
      Ψ₃, preΨ₄, Ψ₂Sq,
      Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.derivative_ofNat,
      Polynomial.C_mul, Polynomial.C_sub, Polynomial.C_add, Polynomial.C_pow,
      Polynomial.C_neg, Polynomial.C_ofNat, Nat.cast_ofNat]
    ring))
    wronskianFourMultiplier W * b_relation_poly W

end HasseWeil
