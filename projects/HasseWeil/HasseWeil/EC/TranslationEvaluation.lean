import HasseWeil.EC.Translation
import HasseWeil.EC.TranslationOrd

/-!
# Lemma-discovery file for Helper 2 of ord-transport Step (B'') discharge

This file crystallises the addressing knowledge — shipped lemma signatures
needed by Helper 2 (`pointValuation_translateX_xy_sub_addX_eq_zero`) and
its companions for the substantive non-zero `k` case of
`IsTranslateXY_evaluatesAt`.

The substantive proof of Helper 2 layers in subsequent sessions on the
infrastructure indexed here.

## Helper 2 plan

For `P : (W_smooth W).SmoothPoint` and `(xk, yk) : F × F` with
`(P.toAffinePoint + Affine.Point.some xk yk h_ns).IsSome` (the translation
yields a finite point), prove

```
(W_smooth W).pointValuation P (translateX_xy W xk yk -
    algebraMap F W.toAffine.FunctionField (P.translate_of_finite ... ).x) < 1
```

via:
1. **Helper 1** (commit fb2f482, used here): `translateX_xy = (W_KE).addX(...)`.
2. **Affine.Point addition formula**: `add_some` gives the explicit
   `(P.toAffinePoint + Q).x = (W).addX P.x Q.x slope` for non-inverse pairs.
3. **Smooth-point evaluation**: compute `(W).addX(P.x, xk, slope_at_P)`
   in F via the `Affine.addX` formula, equating it with the X-coord of
   `P + (xk, yk)` (a smooth point or zero based on degeneracy).
4. **Vanishing/non-vanishing case-split**: if `x_gen W - algMap xk` does
   not vanish at P (i.e., `P.x ≠ xk`), the slope `translateSlope_xy`
   evaluates at P to the chord slope `(P.y - yk) / (P.x - xk)`. If
   `P.x = xk` (the doubling case), additional analysis applies.

## Crystallised lemma signatures

The following `#check` statements verify the existing lemma signatures
needed by Helper 2's downstream construction. -/

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

-- Helper 1 (this turn, commit fb2f482):
example (xk yk : F) :
    translateX_xy W xk yk =
      (W_KE W).toAffine.addX (x_gen W) (algebraMap F W.toAffine.FunctionField xk)
        (translateSlope_xy W xk yk) :=
  translateX_xy_eq_addX W xk yk

example (xk yk : F) :
    translateY_xy W xk yk =
      (W_KE W).toAffine.addY (x_gen W)
        (algebraMap F W.toAffine.FunctionField xk) (y_gen W)
        (translateSlope_xy W xk yk) :=
  translateY_xy_eq_addY W xk yk

-- Affine.Point addition formula in mathlib (for the F-rational case):
example (x₁ x₂ y₁ y₂ : F) (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (WeierstrassCurve.Affine.Point.some (W' := W.toAffine) x₁ y₁ h₁ +
      WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) =
      WeierstrassCurve.Affine.Point.some _ _
        (WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy) :=
  WeierstrassCurve.Affine.Point.add_some hxy

-- algMap-compatibility of addX (mathlib's map_addX). This is the key
-- structural identity for Helper 2: it expresses that
-- (W_KE).addX(algMap a, algMap b, algMap c) = algMap (W.addX a b c).
-- Useful when slope happens to be in algMap '' F (the chord-slope case
-- with explicit base-field values).
example (a b c : F) :
    (W_KE W).toAffine.addX (algebraMap F W.toAffine.FunctionField a)
        (algebraMap F W.toAffine.FunctionField b)
        (algebraMap F W.toAffine.FunctionField c) =
      algebraMap F W.toAffine.FunctionField (W.toAffine.addX a b c) := by
  show (W.map (algebraMap F W.toAffine.FunctionField)).toAffine.addX _ _ _ = _
  exact WeierstrassCurve.Affine.map_addX _ _ _ _

example (a b c d : F) :
    (W_KE W).toAffine.addY (algebraMap F W.toAffine.FunctionField a)
        (algebraMap F W.toAffine.FunctionField b)
        (algebraMap F W.toAffine.FunctionField c)
        (algebraMap F W.toAffine.FunctionField d) =
      algebraMap F W.toAffine.FunctionField (W.toAffine.addY a b c d) := by
  show (W.map (algebraMap F W.toAffine.FunctionField)).toAffine.addY _ _ _ _ = _
  exact WeierstrassCurve.Affine.map_addY _ _ _ _ _

end HasseWeil
