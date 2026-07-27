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

/-- A finite pointed comparison that is an isomorphism away from the marked
section is bijective on the affine section-neighborhood rings once it
identifies the two marked-section ideals. -/
theorem projModelMap_sectionNeighborhood_appLE_bijective
    {C S : Scheme.{u}} {π : C ⟶ S}
    [IsAffine S] [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (F : C ⟶ projModel W) [IsFinite F]
    (hpre : F ⁻¹ᵁ (projModelZChart W : (projModel W).Opens) =
      sectionAway z hz)
    [IsIso
      (F.resLE (projModelZChart W : (projModel W).Opens)
        (sectionAway z hz) (le_of_eq hpre.symm))]
    (hpoint : z ≫ F = S.toSpecΓ ≫ projModelZero W)
    (hideal : (projModelZero W).ker.comap F = z.ker) :
    let N := projModelSectionNeighborhood W
    let P : C.affineOpens := ⟨F ⁻¹ᵁ N.1, N.2.preimage F⟩
    Function.Bijective (F.appLE N.1 P.1 le_rfl).hom := by
  dsimp only
  let N := projModelSectionNeighborhood W
  let P : C.affineOpens := ⟨F ⁻¹ᵁ N.1, N.2.preimage F⟩
  let φ := (F.appLE N.1 P.1 le_rfl).hom
  have hfinite : φ.Finite := by
    dsimp only [φ]
    rw [F.appLE_eq_app]
    exact F.finite_app N.1 N.2
  have hnzd :
      projModelSectionRoot W ∈
        nonZeroDivisors Γ(projModel W, N.1) :=
    projModelSectionRoot_mem_nonZeroDivisors W
  have hAway :
      Function.Bijective
        (Localization.awayMap φ (projModelSectionRoot W)) :=
    projModelMap_sectionNeighborhood_awayMap_bijective
      W F (sectionAway z hz) hpre
  have hsurj :
      Function.Surjective ((z.app P.1).hom.comp φ) :=
    projModelMap_sectionNeighborhood_section_comp_surjective
      z W F hpoint
  have hker :
      RingHom.ker (z.app P.1).hom =
        Ideal.span {φ (projModelSectionRoot W)} :=
    projModelMap_sectionNeighborhood_ker_eq_span
      z hz W F hideal
  exact RingHom.Finite.bijective_of_awayMap_bijective_of_ker_eq_span
    φ hfinite (projModelSectionRoot W) hnzd hAway
    (z.app P.1).hom hsurj hker

/-- The coordinate-ring Cartier patch upgrades to an isomorphism on the
exact affine section neighborhood. -/
theorem projModelMap_sectionNeighborhood_isIso
    {C S : Scheme.{u}} {π : C ⟶ S}
    [IsAffine S] [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (F : C ⟶ projModel W) [IsFinite F]
    (hpre : F ⁻¹ᵁ (projModelZChart W : (projModel W).Opens) =
      sectionAway z hz)
    [IsIso
      (F.resLE (projModelZChart W : (projModel W).Opens)
        (sectionAway z hz) (le_of_eq hpre.symm))]
    (hpoint : z ≫ F = S.toSpecΓ ≫ projModelZero W)
    (hideal : (projModelZero W).ker.comap F = z.ker) :
    let N := projModelSectionNeighborhood W
    let P : C.affineOpens := ⟨F ⁻¹ᵁ N.1, N.2.preimage F⟩
    IsIso (F.resLE N.1 P.1 le_rfl) := by
  dsimp only
  let N := projModelSectionNeighborhood W
  let P : C.affineOpens := ⟨F ⁻¹ᵁ N.1, N.2.preimage F⟩
  have hbij :
      Function.Bijective (F.appLE N.1 P.1 le_rfl).hom :=
    projModelMap_sectionNeighborhood_appLE_bijective
      z hz W F hpre hpoint hideal
  rw [F.resLE_eq_morphismRestrict]
  rw [isIso_morphismRestrict_iff_isIso_app F N.2]
  rw [ConcreteCategory.isIso_iff_bijective]
  rw [← F.appLE_eq_app]
  exact hbij

/-- The punctured and section-neighborhood comparisons glue to a global
isomorphism with the projective Weierstrass model. -/
theorem projModelMap_isIso_of_sectionNeighborhood
    {C S : Scheme.{u}} {π : C ⟶ S}
    [IsAffine S] [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (F : C ⟶ projModel W) [IsFinite F]
    (hpre : F ⁻¹ᵁ (projModelZChart W : (projModel W).Opens) =
      sectionAway z hz)
    [IsIso
      (F.resLE (projModelZChart W : (projModel W).Opens)
        (sectionAway z hz) (le_of_eq hpre.symm))]
    (hpoint : z ≫ F = S.toSpecΓ ≫ projModelZero W)
    (hideal : (projModelZero W).ker.comap F = z.ker) :
    IsIso F := by
  let A : Bool → (projModel W).Opens := fun q =>
    cond q (projModelZChart W).1
      (projModelSectionNeighborhood W).1
  rw [← MorphismProperty.isomorphisms.iff]
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) A
  · rw [iSup_bool_eq]
    exact projModelZChart_sup_sectionNeighborhood_eq_top W
  · intro q
    cases q
    · change MorphismProperty.isomorphisms Scheme
        (F ∣_ (projModelSectionNeighborhood W).1)
      rw [MorphismProperty.isomorphisms.iff]
      rw [← F.resLE_eq_morphismRestrict]
      exact projModelMap_sectionNeighborhood_isIso
        z hz W F hpre hpoint hideal
    · change MorphismProperty.isomorphisms Scheme
        (F ∣_ (projModelZChart W).1)
      rw [MorphismProperty.isomorphisms.iff]
      rw [← F.resLE_eq_morphismRestrict]
      rw [← MorphismProperty.isomorphisms.iff]
      apply (F.resLE_congr le_rfl rfl hpre
        (MorphismProperty.isomorphisms Scheme)).mpr
      rw [MorphismProperty.isomorphisms.iff]
      infer_instance

end ModularCurves
