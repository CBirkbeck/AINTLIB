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

end

end ModularCurves
