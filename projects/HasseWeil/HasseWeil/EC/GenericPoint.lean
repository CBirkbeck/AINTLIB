import HasseWeil.MulByIntPullback

/-!
# The generic point of an elliptic curve (T-III-4-020b-1)

The **generic point** `genericPoint W` is the `K(E)`-rational point of `W_KE`
(the base-change of `W` to the function field `K(E)`) with coordinates
`(x_gen W, y_gen W)`. It is the universal affine point on `W` (in the sense
that any rational function of points on `W` can be uniformly evaluated at
`genericPoint W`).

This is the first step in the universal-setting approach to proving
`[m] ∘ [n] = [m*n]` at the isogeny level (T-III-4-020b): once we have a
concrete generic point in `(W_KE).toAffine.Point`, the group-structure
identity `(m*n) • P = m • (n • P)` is free, and combined with a connection
between `mulByInt_x W n` and `Affine.Point.xOf (n • genericPoint)`, the
composition formula falls out.

## Main definitions

* `HasseWeil.genericPoint W` — the generic affine point on `W_KE`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.2.
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- The generic point is nonsingular on `W_KE`. Over an elliptic curve the
    Weierstrass equation implies nonsingularity (`Affine.equation_iff_nonsingular`). -/
theorem generic_nonsingular :
    (W_KE W).toAffine.Nonsingular (x_gen W) (y_gen W) :=
  Affine.equation_iff_nonsingular.mp (generic_equation W)

/-- The **generic point** `(x_gen, y_gen)` of `W_KE` in affine coordinates.
    It satisfies the Weierstrass equation of `W` base-changed to `K(E)` by
    construction (`generic_equation`) and is nonsingular (`generic_nonsingular`).

    Every rational function on `W` evaluated at this point gives the
    corresponding element of `K(E)`; the `[n]`-image of this point has
    coordinates `(mulByInt_x W n, mulByInt_y W n)`. -/
noncomputable def genericPoint : (W_KE W).toAffine.Point :=
  Affine.Point.some (x_gen W) (y_gen W) (generic_nonsingular W)

/-- Sanity check: the generic point's x-coordinate is `x_gen W`. -/
@[simp] theorem genericPoint_xOf_some :
    genericPoint W = Affine.Point.some (x_gen W) (y_gen W) (generic_nonsingular W) :=
  rfl

end HasseWeil
