/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapSectionNeighborhoodAway
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapZeroIdeal
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapPreimage
import ModularCurves.EllipticCurve.PoleSheafWeierstrassPointed
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

/-- A normalized degree-six pole relation constructs a pointed isomorphism
from the family to its projective Weierstrass model. -/
theorem sectionPoleSheafPower_six_exists_projModelIso_of_relation
    {C S : Scheme.{u}} {π : C ⟶ S} [IsAffine S] [IsProper π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hHOne : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
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
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (a₁ a₂ a₃ a₄ a₆ : Γ(S, (⊤ : S.Opens)))
    (hrel :
      sectionPoleSheafPower_baseSectionsMul z hz 3 3 (y ⊗ₜ y) +
          a₁ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (sectionPoleSheafPower_baseSectionsMul z hz 2 3 (x ⊗ₜ y)) +
          a₃ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (Scheme.Modules.baseSectionsMap π
                    (sectionPoleSheafSuccHom π z hz 3) y)) =
        sectionPoleSheafPower_baseSectionsMul z hz 2 4
            (x ⊗ₜ sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x)) +
          a₂ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x))) +
          a₄ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (Scheme.Modules.baseSectionsMap π
                    (sectionPoleSheafSuccHom π z hz 3)
                      (Scheme.Modules.baseSectionsMap π
                        (sectionPoleSheafSuccHom π z hz 2) x))) +
          a₆ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (Scheme.Modules.baseSectionsMap π
                    (sectionPoleSheafSuccHom π z hz 3)
                      (Scheme.Modules.baseSectionsMap π
                        (sectionPoleSheafSuccHom π z hz 2)
                          (Scheme.Modules.baseSectionsMap π
                            (sectionPoleSheafSuccHom π z hz 1)
                              (sectionPoleSheafPowerOneSection π z hz)))))) :
    let W : WeierstrassCurve Γ(S, (⊤ : S.Opens)) :=
      ⟨a₁, a₂, a₃, a₄, a₆⟩
    ∃ F : C ⟶ projModel W,
      F ≫ projModelπ W = π ≫ S.toSpecΓ ∧
        z ≫ F = S.toSpecΓ ≫ projModelZero W ∧
          IsIso F := by
  dsimp only
  let hr : r ∈ z.ker.ideal U :=
    hspan ▸ Ideal.subset_span (Set.mem_singleton r)
  let V := sectionAway z hz
  have hV : z ⁻¹ᵁ V = ⊥ := preimage_sectionAway z hz
  have hUV : U.1 ⊔ V = ⊤ :=
    sup_sectionAway_eq_top_of_preimage_eq_top z hz U.1 hU
  let XU := localTrivializationCoefficient
    (sectionPoleSheafPower π z hz 2) U
    (sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd 2) x
  let YU := localTrivializationCoefficient
    (sectionPoleSheafPower π z hz 3) U
    (sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd 3) y
  let XV := overTrivializationCoefficient
    (sectionPoleSheafPower π z hz 2) V
    (Scheme.Modules.overTrivializationOfRestrictIso
      (sectionPoleSheafPower π z hz 2) V
      (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
        z hz V hV 2)) x
  let YV := overTrivializationCoefficient
    (sectionPoleSheafPower π z hz 3) V
    (Scheme.Modules.overTrivializationOfRestrictIso
      (sectionPoleSheafPower π z hz 3) V
      (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
        z hz V hV 3)) y
  let AU : Γ(S, (⊤ : S.Opens)) →+* Γ(C, U.1) :=
    (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
  let AV : Γ(S, (⊤ : S.Opens)) →+* Γ(C, V) :=
    (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
  let W : WeierstrassCurve Γ(S, (⊤ : S.Opens)) :=
    ⟨a₁, a₂, a₃, a₄, a₆⟩
  let τU : Γ(C, U.1) →+*
      Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
    U.1.topIso.inv.hom
  let τV : Γ(C, V) →+*
      Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
    V.topIso.inv.hom
  let fU := τU.comp AU
  let fV := τV.comp AV
  let PU : Fin 3 → Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
    τU ∘ ![XU * r, YU, r ^ 3]
  let PV : Fin 3 → Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
    τV ∘ ![XV, YV, 1]
  let hPU : (W.map fU).toProjective.Equation PU := by
    have hPU₀ :=
      sectionPoleSheafPower_six_local_homogeneous_weierstrass_equation_of_relation
        z hz U r hr hspan hnzd x y a₁ a₂ a₃ a₄ a₆ hrel
    simpa only [W, fU, PU, WeierstrassCurve.map_map] using hPU₀.map τU
  let hPV : (W.map fV).toProjective.Equation PV := by
    have hVeq :=
      sectionPoleSheafPower_six_over_weierstrass_equation_of_preimage_eq_bot
        z hz V hV x y a₁ a₂ a₃ a₄ a₆ hrel
    have hPV₀ : (W.map AV).toProjective.Equation ![XV, YV, 1] := by
      rw [WeierstrassCurve.Projective.equation_some]
      simpa only [XV, YV, AV, W] using hVeq
    simpa only [W, fV, PV, WeierstrassCurve.map_map] using hPV₀.map τV
  have hcopU :=
    sectionPoleSheafPower_succ_isCoprime_coefficient_generator_pow
      hsm z hz U hU r hspan hnzd 2 3 y hy
  have hcop : IsCoprime (PU 1) (PU 2) := by
    simpa only [PU, Function.comp_apply,
      WeierstrassCurve.Projective.fin3_def_ext] using hcopU.map τU
  let hZ : IsUnit (PV 2) := by
    simpa only [PV, Function.comp_apply,
      WeierstrassCurve.Projective.fin3_def_ext, map_one] using
      (isUnit_one :
        IsUnit (1 : Γ(V.toScheme, (⊤ : V.toScheme.Opens))))
  obtain ⟨F, hFU, hFV, hF⟩ :=
    sectionPoleSheafPower_six_exists_projModelMap_of_cartier_away_cover
      z hz U r hr hspan hnzd V hV hUV x y
        a₁ a₂ a₃ a₄ a₆ hrel hcop
  dsimp only [V] at hFV
  have hpre :
      F ⁻¹ᵁ (projModelZChart W : (projModel W).Opens) =
        sectionAway z hz := by
    exact projModelMap_preimage_zChart_eq_sectionAway_of_restrict
      z hz U hU r hspan W fU PU hPU hcop
        (by rfl) fV PV hPV hZ F hFU hFV
  have hxy : (W.map AV).toAffine.Equation XV YV := by
    exact
      sectionPoleSheafPower_six_over_weierstrass_equation_of_preimage_eq_bot
        z hz V hV x y a₁ a₂ a₃ a₄ a₆ hrel
  haveI hAway : IsIso
      (F.resLE (projModelZChart W : (projModel W).Opens)
        (sectionAway z hz) (le_of_eq hpre.symm)) :=
    projModelMap_sectionAway_isIso_of_poleCoordinates
      hsm z hz h U hU r hspan hnzd hHOne bOne hbOne
        x hx y hy W F hF hpre hxy (by
          convert hFV using 1
          congr 1
          funext i
          fin_cases i <;> simp)
  haveI hFinite : IsFinite F :=
    projModelMap_isFinite_of_sectionAway_isIso z hz W F hF hpre
  have hpoint : z ≫ F = S.toSpecΓ ≫ projModelZero W :=
    sectionPoleSheafPower_six_projModelMap_pointed_of_restrict
      hsm z hz U hU r hspan hnzd x y hy W F hPU hcop hFU
  have hpreX : z ⁻¹ᵁ C.basicOpen XU = ⊤ := by
    exact sectionPoleSheafPower_succ_preimage_basicOpen_coefficient_eq_top
      hsm z hz U hU r hspan hnzd 1 x hx
  have hpreY : z ⁻¹ᵁ C.basicOpen YU = ⊤ := by
    exact sectionPoleSheafPower_succ_preimage_basicOpen_coefficient_eq_top
      hsm z hz U hU r hspan hnzd 2 y hy
  have hpreXY : z ⁻¹ᵁ C.basicOpen (XU * YU) = ⊤ := by
    rw [C.basicOpen_mul, Scheme.Hom.preimage_inf,
      hpreX, hpreY, inf_top_eq]
  have hideal : (projModelZero W).ker.comap F = z.ker := by
    exact projModelMap_comap_zeroIdeal_eq_section_ker_of_normalized_restrict
      z hz U XU YU r hspan hpreXY W fU PU hPU hcop
        (by rfl) (by rfl) (by rfl) F hFU hpre
  have hIso : IsIso F :=
    projModelMap_isIso_of_sectionNeighborhood
      z hz W F hpre hpoint hideal
  exact ⟨F, hF, hpoint, hIso⟩

end ModularCurves
