/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.Comparison
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapSectionNeighborhood

/-!
# The pole-sheaf Weierstrass comparison

This file converts the global pointed pole-sheaf comparison into the
`LocallyWeierstrass` predicate and packages the construction from normalized
Cartier-chart pole coordinates.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace ModularCurves

universe u

/-- A pointed global isomorphism to a projective Weierstrass model turns
fibrewise ellipticity into the locally Weierstrass condition. -/
theorem locallyWeierstrass_of_projModelIso
    {C S : Scheme.{u}} {π : C ⟶ S} [IsAffine S]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (F : C ⟶ projModel W) [IsIso F]
    (hF : F ≫ projModelπ W = π ≫ S.toSpecΓ)
    (hpoint : z ≫ F = S.toSpecΓ ≫ projModelZero W) :
    LocallyWeierstrass π z hz := by
  let eF := asIso F
  let eS := asIso S.toSpecΓ
  have hFinv :
      eF.symm.hom ≫ π = projModelπ W ≫ eS.symm.hom := by
    rw [← cancel_mono eS.hom]
    dsimp only [eF, eS, Iso.symm_hom, asIso_hom, asIso_inv]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← hF, IsIso.inv_hom_id_assoc]
  have hzinv :
      eS.symm.hom ≫ z = projModelZero W ≫ eF.symm.hom := by
    rw [← cancel_mono eF.hom]
    dsimp only [eF, eS, Iso.symm_hom, asIso_hom, asIso_inv]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [hpoint, IsIso.inv_hom_id_assoc]
  have hModel : FibrewiseElliptic
      (projModelπ W) (projModelZero W)
        (projModelZero_projModelπ W) :=
    h.of_iso eF.symm eS.symm hFinv hzinv
  have hElliptic : W.IsElliptic :=
    isElliptic_of_fibrewiseElliptic_projModel W hModel
  have hLocally : LocallyWeierstrass
      (projModelπ W) (projModelZero W)
        (projModelZero_projModelπ W) :=
    (locallyWeierstrass_projModel_iff_isElliptic W).2 hElliptic
  exact hLocally.of_iso eF eS hF hpoint.symm

/-- Normalized degree-two and degree-three pole coordinates on a Cartier
generator chart produce a locally Weierstrass presentation. -/
theorem sectionPoleSheafPower_six_locallyWeierstrass_of_CartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S} [IsAffine S] [IsProper π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hH1 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (hH2 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 2).sheaf 1))
    (hH3 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 3).sheaf 1))
    (hH4 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 4).sheaf 1))
    (hH5 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 5).sheaf 1))
    (bOne : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz 1)))
    (hbOne : bOne 0 = sectionPoleSheafPowerOneSection π z hz)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1) :
    LocallyWeierstrass π z hz := by
  obtain ⟨a₁, a₂, a₃, a₄, a₆, hrel⟩ :=
    sectionPoleSheafPower_exists_monomial_weierstrass_relation_of_CartierGenerator
      hsm z hz U hU r hspan hnzd hH1 hH2 hH3 hH4 hH5
        bOne hbOne x hx y hy
  let W : WeierstrassCurve Γ(S, (⊤ : S.Opens)) :=
    ⟨a₁, a₂, a₃, a₄, a₆⟩
  obtain ⟨F, hF, hpoint, hIso⟩ :=
    sectionPoleSheafPower_six_exists_projModelIso_of_relation
      hsm z hz h U hU r hspan hnzd hH1 bOne hbOne
        x hx y hy a₁ a₂ a₃ a₄ a₆ hrel
  letI : IsIso F := hIso
  exact locallyWeierstrass_of_projModelIso
    z hz h W F hF hpoint

end ModularCurves
