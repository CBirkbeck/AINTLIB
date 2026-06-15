/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Algebra.Polynomial.Expand

/-!
# Generic-CommRing division polynomial expand-range membership

For a Weierstrass curve `W : WeierstrassCurve R` over a commutative ring `R`
with `[CharP R p]` (`p` prime), the division polynomials `Φ_p, Ψ_p², Ψ_p` lie
in the image of `Polynomial.expand R p`. This is the **base case** of
Silverman III.6.2 for `q = p`.

This file contains generic-CommRing forms (works for any `[CharP R p]`,
including K-level `[Field K] [CharP K p]` and universal-MvPolynomial-level
`URing p = MvPolynomial AVar (ZMod p)`). The K-level versions in
`Verschiebung/QthRoots.lean` and the universal-level corollaries in
`Verschiebung/Route2Universal.lean` are direct one-line specialisations.

## Main results

* `Φ_two_mem_expand_two_charP`, `ΨSq_two_mem_expand_two_charP` — base case
  for `q = 2` (any `[CharP R 2]`).
* `b_relation_of_charP_three` — `b₈ = b₂ b₆ - b₄²` in `[CharP R 3]`.
* `Ψ₃_mem_expand_three_charP`, `ΨSq_three_mem_expand_three_charP`,
  `Φ_three_mem_expand_three_charP` — base case for `q = 3`
  (any `[CharP R 3]`).

## References

Silverman, *The Arithmetic of Elliptic Curves*, III.6.2.
-/

namespace HasseWeil

variable {R : Type*} [CommRing R]

/-! ### Base case `q = 2` -/

/-- **Φ_2 ∈ expand 2 range, generic in `R`** with `[CharP R 2]`. The base
    case of Silverman III.6.2 for `q = 2`.

    `W.Φ 2 = X^4 - b₄ X² - 2 b₆ X - b₈`; in char 2 the `2 b₆ X` term
    vanishes, leaving `expand 2 (X² - b₄ X - b₈)`. -/
theorem Φ_two_mem_expand_two_charP [CharP R 2] (W : WeierstrassCurve R) :
    W.Φ 2 ∈ Set.range (⇑(Polynomial.expand R 2)) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C W.b₄ * Polynomial.X - Polynomial.C W.b₈, ?_⟩
  rw [W.Φ_two]
  rw [map_sub, map_sub, map_mul, Polynomial.expand_C, Polynomial.expand_X,
    map_pow, Polynomial.expand_X, Polynomial.expand_C]
  have h_2b6 : (2 : R) * W.b₆ = 0 := by
    rw [show (2 : R) = 0 from CharP.cast_eq_zero R 2, zero_mul]
  rw [h_2b6, map_zero, zero_mul, sub_zero]
  ring

/-- **ΨSq_2 ∈ expand 2 range, generic in `R`** with `[CharP R 2]`. Companion
    of `Φ_two_mem_expand_two_charP`.

    `W.ΨSq 2 = W.Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`; in char 2 the `4X³` and
    `2b₄X` terms vanish, leaving `expand 2 (b₂ X + b₆)`. -/
theorem ΨSq_two_mem_expand_two_charP [CharP R 2] (W : WeierstrassCurve R) :
    W.ΨSq 2 ∈ Set.range (⇑(Polynomial.expand R 2)) := by
  refine ⟨Polynomial.C W.b₂ * Polynomial.X + Polynomial.C W.b₆, ?_⟩
  rw [W.ΨSq_two, WeierstrassCurve.Ψ₂Sq]
  rw [map_add, map_mul, Polynomial.expand_C, Polynomial.expand_X, Polynomial.expand_C]
  have h_2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h_4 : (4 : R) = 0 := by
    rw [show (4 : R) = 2 * 2 from by ring, h_2, mul_zero]
  have h_2b4 : (2 : R) * W.b₄ = 0 := by rw [h_2, zero_mul]
  rw [h_4, h_2b4, map_zero, zero_mul, zero_mul]
  ring

/-! ### Base case `q = 3` -/

/-- **Char-3 b-relation, generic in `R`**: `b₈ = b₂ · b₆ - b₄²`.
    Specialisation of mathlib's `WeierstrassCurve.b_relation` (`4·b₈ = b₂·b₆ - b₄²`)
    via `4 = 1` in char 3. -/
theorem b_relation_of_charP_three [CharP R 3] (W : WeierstrassCurve R) :
    W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  have h := W.b_relation
  have h_4 : (4 : R) = 1 := by
    have h_3 : (3 : R) = 0 := CharP.cast_eq_zero R 3
    rw [show (4 : R) = 3 + 1 from by ring, h_3, zero_add]
  rw [h_4, one_mul] at h
  exact h

/-- **Ψ₃ ∈ expand 3 range, generic in `R`** with `[CharP R 3]`.

    `W.Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`; in char 3 the `3X⁴`, `3b₄X²`,
    `3b₆X` terms vanish, leaving `b₂X³ + b₈ = expand 3 (b₂X + b₈)`. -/
theorem Ψ₃_mem_expand_three_charP [CharP R 3] (W : WeierstrassCurve R) :
    W.Ψ₃ ∈ Set.range (⇑(Polynomial.expand R 3)) := by
  refine ⟨Polynomial.C W.b₂ * Polynomial.X + Polynomial.C W.b₈, ?_⟩
  rw [WeierstrassCurve.Ψ₃]
  rw [map_add, map_mul, Polynomial.expand_C, Polynomial.expand_X, Polynomial.expand_C]
  have h_3 : (3 : R) = 0 := CharP.cast_eq_zero R 3
  have h_3P : (3 : Polynomial R) = 0 := by
    show ((3 : ℕ) : Polynomial R) = 0
    rw [Nat.cast_ofNat]
    show Polynomial.C ((3 : ℕ) : R) = 0
    rw [show ((3 : ℕ) : R) = 0 by exact_mod_cast h_3, Polynomial.C_0]
  linear_combination -(Polynomial.X ^ 4 + Polynomial.C W.b₄ * Polynomial.X ^ 2 +
    Polynomial.C W.b₆ * Polynomial.X) * h_3P

/-- **ΨSq_3 ∈ expand 3 range, generic in `R`** with `[CharP R 3]`. Direct
    from `W.ΨSq_three : W.ΨSq 3 = W.Ψ₃ ^ 2` and the multiplicativity of
    `Polynomial.expand`. -/
theorem ΨSq_three_mem_expand_three_charP [CharP R 3] (W : WeierstrassCurve R) :
    W.ΨSq 3 ∈ Set.range (⇑(Polynomial.expand R 3)) := by
  obtain ⟨g, hg⟩ := Ψ₃_mem_expand_three_charP W
  refine ⟨g ^ 2, ?_⟩
  rw [W.ΨSq_three, ← hg, map_pow]

set_option maxHeartbeats 1000000 in
/-- **Φ_3 ∈ expand 3 range, generic in `R`** with `[CharP R 3]`.

    Witness `g(X) = X³ + 2·b₂·b₄·X² + (2·b₂³·b₆ + b₂²·b₄² + b₂·b₄·b₆)·X +
    (2·b₂·b₄·b₆² + b₄³·b₆ + b₆³)`, sympy-verified in
    `scripts/verify_phi_3_universal.py`. The proof rewrites via
    `b_relation_of_charP_three` (`b₈ = b₂·b₆ - b₄²`), then closes via the
    explicit char-3 multiplier. -/
theorem Φ_three_mem_expand_three_charP [CharP R 3] (W : WeierstrassCurve R) :
    W.Φ 3 ∈ Set.range (⇑(Polynomial.expand R 3)) := by
  refine ⟨Polynomial.X ^ 3 +
      Polynomial.C (2 * W.b₂ * W.b₄) * Polynomial.X ^ 2 +
      Polynomial.C (2 * W.b₂ ^ 3 * W.b₆ + W.b₂ ^ 2 * W.b₄ ^ 2 + W.b₂ * W.b₄ * W.b₆) *
        Polynomial.X +
      Polynomial.C (2 * W.b₂ * W.b₄ * W.b₆ ^ 2 + W.b₄ ^ 3 * W.b₆ + W.b₆ ^ 3),
      ?_⟩
  have h_3 : (3 : R) = 0 := CharP.cast_eq_zero R 3
  have h_3P : (3 : Polynomial R) = 0 := by
    show ((3 : ℕ) : Polynomial R) = 0
    rw [Nat.cast_ofNat]
    show Polynomial.C ((3 : ℕ) : R) = 0
    rw [show ((3 : ℕ) : R) = 0 by exact_mod_cast h_3, Polynomial.C_0]
  rw [W.Φ_three, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq,
    b_relation_of_charP_three W]
  push_cast
  simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, Polynomial.expand_C,
    Polynomial.expand_X, Polynomial.C_mul, Polynomial.C_sub, Polynomial.C_pow,
    Polynomial.C_add, Polynomial.C_ofNat]
  linear_combination
    (2 * Polynomial.C W.b₄ * Polynomial.X ^ 7 +
      Polynomial.C W.b₂ * Polynomial.C W.b₄ * Polynomial.X ^ 6 +
      8 * Polynomial.C W.b₆ * Polynomial.X ^ 6 +
      13 * Polynomial.C W.b₂ * Polynomial.C W.b₆ * Polynomial.X ^ 5 -
      11 * Polynomial.C W.b₄ ^ 2 * Polynomial.X ^ 5 +
      4 * Polynomial.C W.b₂ ^ 2 * Polynomial.C W.b₆ * Polynomial.X ^ 4 -
      4 * Polynomial.C W.b₂ * Polynomial.C W.b₄ ^ 2 * Polynomial.X ^ 4 +
      Polynomial.C W.b₄ * Polynomial.C W.b₆ * Polynomial.X ^ 4 +
      Polynomial.C W.b₂ ^ 3 * Polynomial.C W.b₆ * Polynomial.X ^ 3 +
      6 * Polynomial.C W.b₂ * Polynomial.C W.b₄ * Polynomial.C W.b₆ * Polynomial.X ^ 3 -
      6 * Polynomial.C W.b₄ ^ 3 * Polynomial.X ^ 3 -
      Polynomial.C W.b₆ ^ 2 * Polynomial.X ^ 3 +
      Polynomial.C W.b₂ ^ 2 * Polynomial.C W.b₄ * Polynomial.C W.b₆ * Polynomial.X ^ 2 -
      Polynomial.C W.b₂ * Polynomial.C W.b₄ ^ 3 * Polynomial.X ^ 2 +
      Polynomial.C W.b₂ * Polynomial.C W.b₆ ^ 2 * Polynomial.X ^ 2 -
      2 * Polynomial.C W.b₄ ^ 2 * Polynomial.C W.b₆ * Polynomial.X ^ 2 +
      Polynomial.C W.b₂ * Polynomial.C W.b₄ ^ 2 * Polynomial.C W.b₆ * Polynomial.X -
      Polynomial.C W.b₄ ^ 4 * Polynomial.X -
      Polynomial.C W.b₄ * Polynomial.C W.b₆ ^ 2 * Polynomial.X +
      Polynomial.C W.b₂ * Polynomial.C W.b₄ * Polynomial.C W.b₆ ^ 2) * h_3P

end HasseWeil
