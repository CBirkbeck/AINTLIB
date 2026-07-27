/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapSectionNeighborhoodAway
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapZeroIdeal
import ModularCurves.ForMathlib.FiniteRingHomCartierPatch

/-!
# The pole-sheaf comparison on the section neighborhood

This file combines the punctured comparison with the scheme-theoretic
marked-section quotient on the canonical affine neighborhood.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace ModularCurves

universe u

/-- Pointedness makes the section-neighborhood comparison surjective after
restriction to the marked section. -/
theorem projModelMap_sectionNeighborhood_section_comp_surjective
    {C S : Scheme.{u}} [IsAffine S]
    (z : S ⟶ C)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (F : C ⟶ projModel W) [IsAffineHom F]
    (hpoint : z ≫ F = S.toSpecΓ ≫ projModelZero W) :
    let N := projModelSectionNeighborhood W
    let P : C.affineOpens := ⟨F ⁻¹ᵁ N.1, N.2.preimage F⟩
    Function.Surjective
      ((z.app P.1).hom.comp (F.appLE N.1 P.1 le_rfl).hom) := by
  dsimp only
  let N := projModelSectionNeighborhood W
  let P : C.affineOpens := ⟨F ⁻¹ᵁ N.1, N.2.preimage F⟩
  letI : IsIso S.toSpecΓ := IsAffine.affine
  letI : IsClosedImmersion (projModelZero W) :=
    isClosedImmersion_section
      (projModelZero W) (projModelZero_projModelπ W)
  letI : IsClosedImmersion (S.toSpecΓ ≫ projModelZero W) :=
    inferInstance
  have hsurj :
      Function.Surjective
        ((S.toSpecΓ ≫ projModelZero W).app N.1).hom :=
    (S.toSpecΓ ≫ projModelZero W).app_surjective N.1 N.2
  change Function.Surjective
    ((F.appLE N.1 P.1 le_rfl ≫ z.app P.1).hom)
  rw [F.appLE_eq_app]
  change Function.Surjective ((z ≫ F).app N.1).hom
  rw [hpoint]
  exact hsurj

end ModularCurves
