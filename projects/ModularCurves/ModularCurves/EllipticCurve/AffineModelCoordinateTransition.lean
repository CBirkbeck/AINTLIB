import ModularCurves.EllipticCurve.AffineModelCoordinates
import ModularCurves.EllipticCurve.WeierstrassModelCoordinateTransition

/-!
# The affine evaluation map on the projective `Z`-chart

The chart homomorphism attached to a projective triple `[x,y,1]` is the
affine Weierstrass evaluation map after identifying the `Z`-chart ring with
the affine coordinate ring.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open WeierstrassCurve.Projective

universe u

namespace ModularCurves

noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Transporting the chart homomorphism of `[x,y,1]` through the standard
`Z`-chart equivalence gives affine evaluation at `(x,y)`. -/
lemma chartAwayHomOfTriple_z_comp_chartZRingEquiv_symm
    (W : WeierstrassCurve R) (x y : S)
    (hxy : (W.map (algebraMap R S)).toAffine.Equation x y) :
    let P : Fin 3 → S := ![x, y, 1]
    let hP : (W.map (algebraMap R S)).toProjective.Equation P := by
      rw [WeierstrassCurve.Projective.equation_some]
      exact hxy
    ((chartAwayHomOfTriple W 2 P 1 (by simp [P]) hP).toRingHom.comp
      (chartZRingEquiv W).symm.toRingHom) =
        affineModelEval W (algebraMap R S) x y hxy := by
  dsimp only
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply]
      change chartAwayHomOfTriple W 2 ![x, y, 1] 1 _ _
          ((chartZRingEquiv W).symm
            (algebraMap R W.toAffine.CoordinateRing a)) = _
      rw [← chartZRingEquiv_fromZero W a, RingEquiv.symm_apply_apply]
      change chartAwayHomOfTriple W 2 ![x, y, 1] 1 _ _
          (algebraMap R (chartAway W 2) a) = _
      rw [(chartAwayHomOfTriple W 2 ![x, y, 1] 1 _ _).commutes]
      exact (RingHom.congr_fun (affineModelEval_comp_algebraMap W
        (algebraMap R S) x y hxy) a).symm
    · simp only [RingHom.comp_apply]
      change chartAwayHomOfTriple W 2 ![x, y, 1] 1 _ _
          ((chartZRingEquiv W).symm (coordX W)) =
        affineModelEval W (algebraMap R S) x y hxy (coordX W)
      rw [affineModelEval_coordX]
      rw [← chartZRingEquiv_x W, RingEquiv.symm_apply_apply]
      rw [chartAwayHomOfTriple_isLocalizationElem
        (hkl := by decide)]
      simp
  · simp only [RingHom.comp_apply]
    change chartAwayHomOfTriple W 2 ![x, y, 1] 1 _ _
        ((chartZRingEquiv W).symm (coordY W)) =
      affineModelEval W (algebraMap R S) x y hxy (coordY W)
    rw [affineModelEval_coordY]
    rw [← chartZRingEquiv_y W, RingEquiv.symm_apply_apply]
    rw [chartAwayHomOfTriple_isLocalizationElem
      (hkl := by decide)]
    simp

end

end ModularCurves
