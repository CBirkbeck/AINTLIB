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

/-! ## The torsion→coordinate bridge ([T-E15-NORM] hArb)

The ⟹-direction completing Stage A's ⟸: a `3`-torsion affine point roots the
`3`-division polynomial. The certificate (CAS-verified):
`(3x²+2a₂x+a₄−a₁y)² + a₁(…)d − (a₂+3x)d² + Ψ₃(x) = −(b₂+12x)·(curve)` with
`d = 2y+a₁x+a₃`, so `x(2P) = x(−P)` clears to `Ψ₃(x) = 0` on the curve. -/

namespace WeierstrassCurve

namespace Affine.Point

open Polynomial in
/-- **(the bridge ★★)** On any Weierstrass curve over a field, a `3`-torsion affine
point roots the `3`-division polynomial: `3•P = 0 → Ψ₃(x(P)) = 0`. -/
theorem psi3_eval_eq_zero_of_three_zsmul {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve F} {x y : F} (h : W.toAffine.Nonsingular x y)
    (h3 : (3 : ℤ) • (Affine.Point.some x y h : W.toAffine.Point) = 0) :
    W.Ψ₃.eval x = 0 := by
  have hcurve := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
  by_cases hd : y = W.toAffine.negY x y
  · -- `P` would be `2`-torsion, hence `P = 3P − 2P = 0` — impossible
    have h2 : (2 : ℤ) • (Affine.Point.some x y h : W.toAffine.Point) = 0 := by
      rw [two_zsmul]
      exact Affine.Point.add_of_Y_eq rfl hd
    have hP : (Affine.Point.some x y h : W.toAffine.Point) = 0 := by
      have hsub : ((3 : ℤ) - 2) • (Affine.Point.some x y h : W.toAffine.Point)
          = 0 := by rw [sub_smul, h3, h2, sub_zero]
      simpa using hsub
    exact absurd hP (Affine.Point.some_ne_zero h)
  · -- `2P = −P`, so the doubling abscissa equals `x`; clear denominators
    have h2P : (2 : ℤ) • (Affine.Point.some x y h : W.toAffine.Point)
        = -(Affine.Point.some x y h) := by
      have h3' : (2 : ℤ) • (Affine.Point.some x y h : W.toAffine.Point)
          + (Affine.Point.some x y h) = 0 := by
        rw [show (2 : ℤ) • (Affine.Point.some x y h : W.toAffine.Point)
            + (Affine.Point.some x y h)
          = (3 : ℤ) • (Affine.Point.some x y h : W.toAffine.Point) by
          rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, one_zsmul]]
        exact h3
      exact eq_neg_of_add_eq_zero_left h3'
    rw [two_zsmul, Affine.Point.add_some (fun hc => hd hc.2),
      Affine.Point.neg_some] at h2P
    have hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) = x := by
      injection h2P
    rw [Affine.slope_of_Y_ne rfl hd] at hx2
    have hdne : y - W.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hd
    rw [Affine.addX] at hx2
    field_simp at hx2
    simp only [WeierstrassCurve.Ψ₃, eval_add, eval_mul, eval_pow, eval_ofNat,
      eval_C, eval_X, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, WeierstrassCurve.Affine.negY] at hx2 ⊢
    linear_combination (norm := ring_nf)
      (-(W.a₁ ^ 2) - 4 * W.a₂ - 12 * x) * hcurve - hx2

open Polynomial in
/-- **(the bridge, `μ`-form ★)** A `3`-torsion affine point over a field is nowhere
`2`-torsion (`TwiceNeZero`) and has vanishing `μ` — the exact inputs of the flex
normalization `ofTwiceNeZero_isFlexNF`. -/
theorem mu_eq_zero_of_three_zsmul {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve F} {x y : F} (h : W.toAffine.Nonsingular x y)
    (h3 : (3 : ℤ) • (Affine.Point.some x y h : W.toAffine.Point) = 0)
    [htw : (Affine.Point.some x y h : W.toAffine.Point).TwiceNeZero] :
    (Affine.Point.some x y h : W.toAffine.Point).μ = 0 := by
  haveI : (Affine.Point.some x y h : W.toAffine.Point).NeZero :=
    ⟨Affine.Point.some_ne_zero h⟩
  have hpsi := psi3_eval_eq_zero_of_three_zsmul h h3
  have hpsiX : W.Ψ₃.eval (Affine.Point.some x y h : W.toAffine.Point).X = 0 := by
    rwa [Affine.Point.X_some]
  rw [Affine.Point.Ψ₃_eval_X] at hpsiX
  set P : W.toAffine.Point := Affine.Point.some x y h with hP
  have hkey : P.μ = ((W.a₂ + 3 * P.X) * P.pY ^ 2 + P.pX * W.a₁ * P.pY - P.pX ^ 2)
      * (P.pY_inv : F) ^ 2 := by
    have h1 : P.pY * (P.pY_inv : F) = 1 := P.pY_mul_inv
    rw [Affine.Point.μ]
    linear_combination (-(W.a₂ + 3 * P.X) * (1 + P.pY * (P.pY_inv : F))
      - P.pX * W.a₁ * (P.pY_inv : F)) * h1
  rw [hkey, hpsiX, zero_mul]

/-- **(the bridge, `TwiceNeZero`-form)** Over a field, a `3`-torsion affine point is
nowhere `2`-torsion. -/
theorem twiceNeZero_of_three_zsmul {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve F} {x y : F} (h : W.toAffine.Nonsingular x y)
    (h3 : (3 : ℤ) • (Affine.Point.some x y h : W.toAffine.Point) = 0) :
    (Affine.Point.some x y h : W.toAffine.Point).TwiceNeZero := by
  refine { toNeZero := ⟨Affine.Point.some_ne_zero h⟩, twiceNeZero := ?_ }
  rw [show (Affine.Point.some x y h : W.toAffine.Point).pY = 2 * y + W.a₁ * x + W.a₃
    from by rw [Affine.Point.pY, Affine.Point.X_some, Affine.Point.Y_some]]
  refine isUnit_iff_ne_zero.mpr ?_
  intro hc
  have hd : y = W.toAffine.negY x y := by
    rw [WeierstrassCurve.Affine.negY]
    show y = -y - W.a₁ * x - W.a₃
    linear_combination hc
  have h2 : (2 : ℤ) • (Affine.Point.some x y h : W.toAffine.Point) = 0 := by
    rw [two_zsmul]
    exact Affine.Point.add_of_Y_eq rfl hd
  have hPz : (Affine.Point.some x y h : W.toAffine.Point) = 0 := by
    have hsub : ((3 : ℤ) - 2) • (Affine.Point.some x y h : W.toAffine.Point) = 0 := by
      rw [sub_smul, h3, h2, sub_zero]
    simpa using hsub
  exact Affine.Point.some_ne_zero h hPz

end Affine.Point

end WeierstrassCurve

