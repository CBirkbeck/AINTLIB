/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.TateNormalForm

/-!
# The `ℰ₃`-normal form (flex normalization) — the algebraic core of [T-E15-NORM]

This file builds the **existence** direction of KM Ex. 2.2.2 at the level of
`WeierstrassCurve` variable changes: given a point `P` of order `3` on a
Weierstrass curve (equivalently, a rational flex), a variable change brings the
curve to the shape `y² + a₁xy + a₃y = x³` (all of `a₂, a₄, a₆` vanish). This is
the "`order-3 ⟹ flex`" half of the normalization ticket.

The construction is mathlib's `ofTwiceNeZero` (which needs only `2 • P ≠ 0`,
`P.TwiceNeZero`): it moves `P` to the origin with horizontal tangent, forcing
`a₄ = a₆ = 0` and `a₂ = P.μ`. The extra input of *order exactly `3`* is the
vanishing `P.μ = 0` (the `3`-division quantity), which kills the last coefficient
`a₂`. This is the OPPOSITE regime to `toTateNF`, which needs `3 • P ≠ 0`
(`IsUnit P.μ`) to *scale* by `μ⁻¹`; here `μ = 0` and no scaling is possible —
the curve is already in flex form.

`IsE3Form` (in `Moduli/UniversalLevelThree.lean`) strengthens `IsFlexNF` by
additionally pinning `a₁ = 3γ − 1` and `a₃ = −3γ²−β−3βγ` through a *second*
marked `3`-torsion point `Q = (γ, β+γ)`; that second normalization is a separate
step. This file delivers the flex shape.
-/

open WeierstrassCurve

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- The **flex normal form** shape `y² + a₁xy + a₃y = x³`: the coefficients
`a₂, a₄, a₆` all vanish. A Weierstrass curve with a rational flex moved to the
origin (a `3`-torsion point at `(0,0)` with horizontal tangent) is of this shape.
Weaker than `IsE3Form`, which additionally pins `a₁` and `a₃` via a second marked
`3`-torsion point. -/
def IsFlexNF (W : WeierstrassCurve R) : Prop :=
  W.a₂ = 0 ∧ W.a₄ = 0 ∧ W.a₆ = 0

namespace Affine.Point

variable {W : WeierstrassCurve R} (P : W.toAffine.Point)

/-- **(T-E15-NORM, flex core)** A point `P` with `2 • P ≠ 0` (`P.TwiceNeZero`) and
`P.μ = 0` (the order-`3`/flex condition) is brought by `ofTwiceNeZero` to a curve
in **flex normal form** `y² + a₁xy + a₃y = x³`.

`ofTwiceNeZero` moves `P` to the origin with horizontal tangent (`a₄ = a₆ = 0`
unconditionally) and leaves `a₂ = P.μ`; the flex hypothesis `P.μ = 0` clears it. -/
theorem ofTwiceNeZero_isFlexNF [P.TwiceNeZero] (hμ : P.μ = 0) :
    (W.toAffine.ofTwiceNeZero P • W).IsFlexNF :=
  ⟨by rw [ofTwiceNeZero_a₂, hμ], ofTwiceNeZero_a₄ .., ofTwiceNeZero_a₆ ..⟩

end Affine.Point

/-! ## The field-level 3-torsion killing on the `ℰ₃`-form (T-E15-NORM Stage A)

The flex-relation algebra behind the killing halves of `hL`: on a flex-normal-form
curve over a field the origin is `3`-torsion, and on an `ℰ₃`-form curve the second
marked point `(γ, β + γ)` is `3`-torsion. Both are pure mathlib `Affine.Point`
group-law computations (`slope`/`addX`/`addY` + `add_of_Y_eq`): the doubling of the
origin has slope `0` and lands on `(0, −a₃) = −P`; the doubling of `(γ, β+γ)` has
slope `1` and lands on `(γ, 3βγ) = −Q`. These feed the fibrewise evaluation of the
section-level killing `[3]P = [3]Q = 0` of the universal `ℰ₃`-datum. -/

namespace Affine.Point

open WeierstrassCurve.Affine (negY slope addX addY negAddY)

variable {F : Type*} [Field F] [DecidableEq F]

/-- **(Stage A, the `P`-killing ★)** On a flex-normal-form curve `y² + a₁xy + a₃y = x³`
over a field with `a₃ ≠ 0`, the origin is `3`-torsion: the tangent at `(0,0)` is
horizontal (slope `0`, since `a₄ = 0`), so `2P = (0, −a₃) = −P`. -/
theorem three_zsmul_some_origin {W : WeierstrassCurve F} (hW : W.IsFlexNF)
    (ha₃ : W.a₃ ≠ 0) (h : W.toAffine.Nonsingular 0 0) :
    (3 : ℤ) • (Affine.Point.some 0 0 h : W.toAffine.Point) = 0 := by
  obtain ⟨ha₂, ha₄, ha₆⟩ := hW
  have hyne : (0 : F) ≠ W.toAffine.negY 0 0 := by
    rw [Affine.negY]
    intro hc
    exact ha₃ (by linear_combination hc)
  have hne : ¬((0 : F) = 0 ∧ (0 : F) = W.toAffine.negY 0 0) := fun hc => hyne hc.2
  have hℓ : W.toAffine.slope 0 0 0 0 = 0 := by
    rw [Affine.slope_of_Y_ne rfl hyne]
    rw [show 3 * (0:F) ^ 2 + 2 * W.a₂ * 0 + W.a₄ - W.a₁ * 0 = 0 by
      rw [ha₄]; ring]
    exact zero_div _
  have hx2 : W.toAffine.addX 0 0 (W.toAffine.slope 0 0 0 0) = 0 := by
    rw [hℓ, Affine.addX, ha₂]; ring
  have hy2 : W.toAffine.addY 0 0 0 (W.toAffine.slope 0 0 0 0) = W.toAffine.negY 0 0 := by
    rw [hℓ, Affine.addY, Affine.negAddY, Affine.negY, Affine.negY, Affine.addX, ha₂]
    ring
  rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, two_zsmul, one_zsmul,
    Affine.Point.add_some hne]
  exact Affine.Point.add_of_Y_eq hx2 hy2

/-- **(Stage A, the `Q`-killing ★)** On an `ℰ₃`-form curve (`a₁ = 3γ−1`,
`a₃ = −3γ²−β−3βγ`, `a₂ = a₄ = a₆ = 0`) over a field, the marked point `(γ, β+γ)` is
`3`-torsion whenever `β + γ − 3βγ ≠ 0` (the non-`2`-torsion certificate, a unit on the
universal `ℰ₃`): the tangent at `Q` has slope `1` — numerator and denominator both equal
`β + γ − 3βγ` — so `2Q = (γ, 3βγ) = −Q`. -/
theorem three_zsmul_some_e3Q {W : WeierstrassCurve F} {β γ : F}
    (ha₁ : W.a₁ = 3 * γ - 1) (ha₂ : W.a₂ = 0)
    (ha₃ : W.a₃ = -3 * γ ^ 2 - β - 3 * β * γ) (ha₄ : W.a₄ = 0)
    (hden : β + γ - 3 * β * γ ≠ 0)
    (h : W.toAffine.Nonsingular γ (β + γ)) :
    (3 : ℤ) • (Affine.Point.some γ (β + γ) h : W.toAffine.Point) = 0 := by
  have hnegY : W.toAffine.negY γ (β + γ) = 3 * β * γ := by
    rw [Affine.negY, ha₁, ha₃]; ring
  have hyne : (β + γ) ≠ W.toAffine.negY γ (β + γ) := by
    rw [hnegY]; exact fun hc => hden (by linear_combination hc)
  have hne : ¬(γ = γ ∧ (β + γ) = W.toAffine.negY γ (β + γ)) := fun hc => hyne hc.2
  have hℓ : W.toAffine.slope γ γ (β + γ) (β + γ) = 1 := by
    rw [Affine.slope_of_Y_ne rfl hyne]
    rw [show 3 * γ ^ 2 + 2 * W.a₂ * γ + W.a₄ - W.a₁ * (β + γ) = β + γ - 3 * β * γ by
      rw [ha₁, ha₂, ha₄]; ring]
    rw [show (β + γ) - W.toAffine.negY γ (β + γ) = β + γ - 3 * β * γ by rw [hnegY]]
    exact div_self hden
  have hx2 : W.toAffine.addX γ γ (W.toAffine.slope γ γ (β + γ) (β + γ)) = γ := by
    rw [hℓ, Affine.addX, ha₁, ha₂]; ring
  have hy2 : W.toAffine.addY γ γ (β + γ) (W.toAffine.slope γ γ (β + γ) (β + γ))
      = W.toAffine.negY γ (β + γ) := by
    rw [hℓ, Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, Affine.negY,
      ha₁, ha₂]
    ring
  rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, two_zsmul, one_zsmul,
    Affine.Point.add_some hne]
  exact Affine.Point.add_of_Y_eq hx2 hy2

end Affine.Point

end WeierstrassCurve
