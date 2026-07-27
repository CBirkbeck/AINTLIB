import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapGlue

/-!
# Properness of the pole-sheaf Weierstrass comparison

Over an affine base, a morphism from a proper family to a projective
Weierstrass model is proper as soon as it respects the structural morphisms.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

noncomputable section

/-- A morphism from a proper family to a projective Weierstrass model over an
affine base is proper when it respects the structural morphisms. -/
theorem projModelMap_isProper_of_isAffine
    {C S : Scheme.{u}} {π : C ⟶ S} [IsAffine S] [IsProper π]
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (f : C ⟶ projModel W)
    (hf : f ≫ projModelπ W = π ≫ S.toSpecΓ) :
    IsProper f := by
  haveI : IsIso S.toSpecΓ := IsAffine.affine
  haveI : IsProper (f ≫ projModelπ W) := by
    rw [hf]
    infer_instance
  exact IsProper.of_comp f (projModelπ W)

/-- Restricting a proper morphism to the exact preimage of a target open remains proper. -/
theorem resLE_isProper_of_preimage_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (U : Y.Opens) (V : X.Opens) (h : f ⁻¹ᵁ U = V) :
    IsProper (f.resLE U V (le_of_eq h.symm)) := by
  subst V
  rw [f.resLE_eq_morphismRestrict]
  infer_instance

end

end ModularCurves
