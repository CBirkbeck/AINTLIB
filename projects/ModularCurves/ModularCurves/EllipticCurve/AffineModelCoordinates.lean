import ModularCurves.EllipticCurve.PoleFiltration

/-!
# Evaluation on the affine Weierstrass model

A pair satisfying the mapped affine Weierstrass equation defines a ring
homomorphism from the affine coordinate ring.  The formulas below record its
values on the base ring and the two standard coordinates.
-/

universe u

namespace ModularCurves

noncomputable section

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Evaluation of the affine Weierstrass coordinate ring at a pair satisfying
the mapped affine equation. -/
noncomputable def affineModelEval
    (W : WeierstrassCurve R) (f : R →+* A) (x y : A)
    (hxy : (W.map f).toAffine.Equation x y) :
    W.toAffine.CoordinateRing →+* A :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom f x) y (by
    rw [Polynomial.eval₂_eval₂RingHom_apply,
      ← W.toAffine.map_polynomial f]
    exact hxy)

@[simp]
lemma affineModelEval_coordX
    (W : WeierstrassCurve R) (f : R →+* A) (x y : A)
    (hxy : (W.map f).toAffine.Equation x y) :
    affineModelEval W f x y hxy (coordX W) = x := by
  rw [show coordX W =
    AdjoinRoot.of W.toAffine.polynomial Polynomial.X from rfl]
  unfold affineModelEval
  rw [AdjoinRoot.lift_of]
  exact Polynomial.eval₂_X _ _

@[simp]
lemma affineModelEval_coordY
    (W : WeierstrassCurve R) (f : R →+* A) (x y : A)
    (hxy : (W.map f).toAffine.Equation x y) :
    affineModelEval W f x y hxy (coordY W) = y := by
  rw [show coordY W =
    AdjoinRoot.root W.toAffine.polynomial from rfl]
  unfold affineModelEval
  rw [AdjoinRoot.lift_root]

lemma affineModelEval_comp_algebraMap
    (W : WeierstrassCurve R) (f : R →+* A) (x y : A)
    (hxy : (W.map f).toAffine.Equation x y) :
    (affineModelEval W f x y hxy).comp
      (algebraMap R W.toAffine.CoordinateRing) = f := by
  ext r
  rw [RingHom.comp_apply]
  change affineModelEval W f x y hxy
    (AdjoinRoot.of W.toAffine.polynomial (Polynomial.C r)) = f r
  unfold affineModelEval
  rw [AdjoinRoot.lift_of, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C]

end

end ModularCurves
