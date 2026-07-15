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

end WeierstrassCurve
