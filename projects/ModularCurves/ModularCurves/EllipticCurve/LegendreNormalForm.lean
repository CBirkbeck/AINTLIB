/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# The Legendre normal form `y² = x(x−1)(x−λ)` (T-E14a)

**(T-E14a leaf (b), STREAM-OMEGA 2026-07-14; board: T-E14 continuation
decomposition.)** The Legendre family and the variable-change normalisation that
produces it: over a ring in which `2` is invertible, a Weierstrass curve with a chosen
pair of disjoint fibrewise-nonzero `2`-torsion points is carried by a unique-up-to-`±1`
variable change to `y² = x(x−1)(x−λ)` with the chosen points at `x = 0` and `x = 1`
(KM 4.6.2; GME Ex. 2.2.1 p. 117). Mirrors the point-based normalisation pattern of
`ForMathlib/TateNormalForm.lean` (`toTateNF`), with mathlib's
`WeierstrassCurve.toCharNeTwoNF` as step 1.

The residual `{±1}` (the `u`-ambiguity left after pinning `x(P) = 0`, `x(Q) = 1`) is
exactly the `ω`-factor of KM's engine axiom 2 — `negVC` with `u = −1`
(`EllipticCurve/InvariantDifferential.lean`, T-OM-B8/B9).
-/

universe u

namespace ModularCurves

open WeierstrassCurve

variable {R : Type u} [CommRing R]

/-- **(T-E14a)** The Legendre Weierstrass curve `y² = x(x−1)(x−λ)`:
`a₂ = −(λ+1)`, `a₄ = λ`, `a₁ = a₃ = a₆ = 0`. -/
def legendreCurve (lam : R) : WeierstrassCurve R :=
  ⟨0, -(lam + 1), 0, lam, 0⟩

@[simp] theorem legendreCurve_a₁ (lam : R) : (legendreCurve lam).a₁ = 0 := rfl
@[simp] theorem legendreCurve_a₂ (lam : R) : (legendreCurve lam).a₂ = -(lam + 1) := rfl
@[simp] theorem legendreCurve_a₃ (lam : R) : (legendreCurve lam).a₃ = 0 := rfl
@[simp] theorem legendreCurve_a₄ (lam : R) : (legendreCurve lam).a₄ = lam := rfl
@[simp] theorem legendreCurve_a₆ (lam : R) : (legendreCurve lam).a₆ = 0 := rfl

/-- **(T-E14a)** The discriminant of the Legendre curve is `16 λ² (λ−1)²`. -/
theorem legendreCurve_Δ (lam : R) :
    (legendreCurve lam).Δ = 16 * lam ^ 2 * (lam - 1) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, legendreCurve_a₁, legendreCurve_a₂,
    legendreCurve_a₃, legendreCurve_a₄, legendreCurve_a₆]
  ring

/-- **(T-E14a)** Over a base with `2` invertible, the Legendre curve is elliptic iff
`λ(λ−1)` is a unit. -/
theorem legendreCurve_isElliptic_iff (h2 : IsUnit (2 : R)) (lam : R) :
    (legendreCurve lam).IsElliptic ↔ IsUnit (lam * (lam - 1)) := by
  rw [WeierstrassCurve.isElliptic_iff, legendreCurve_Δ]
  constructor
  · intro h
    have h' : IsUnit ((16 : R) * (lam * (lam - 1)) ^ 2) := by
      rw [show (16 : R) * (lam * (lam - 1)) ^ 2 = 16 * lam ^ 2 * (lam - 1) ^ 2 by ring]
      exact h
    have h2t : IsUnit ((lam * (lam - 1)) ^ 2) := isUnit_of_mul_isUnit_right h'
    exact (isUnit_pow_iff (n := 2) (by norm_num)).mp h2t
  · intro h
    rw [show (16 : R) * lam ^ 2 * (lam - 1) ^ 2 = 2 ^ 4 * (lam * (lam - 1)) ^ 2 by ring]
    exact (h2.pow 4).mul (h.pow 2)

end ModularCurves
