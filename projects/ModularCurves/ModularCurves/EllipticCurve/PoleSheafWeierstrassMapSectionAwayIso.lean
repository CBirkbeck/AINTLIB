import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapFinite

/-!
# The pole-sheaf comparison on the marked-section complement

The finite punctured comparison is an isomorphism for the normalized
degree-two and degree-three pole coordinates.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open WeierstrassCurve.Projective

universe u

namespace ModularCurves

noncomputable section

/-- The pole-sheaf comparison identifies the exact marked-section complement
with the standard affine `Z`-chart of the projective Weierstrass model. -/
theorem projModelMap_sectionAway_isIso_of_poleCoordinates
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
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (F : C ⟶ projModel W)
    (hF : F ≫ projModelπ W = π ≫ S.toSpecΓ)
    (hpre : F ⁻¹ᵁ (projModelZChart W : (projModel W).Opens) =
      sectionAway z hz) :
    let V := sectionAway z hz
    let A : Γ(S, (⊤ : S.Opens)) →+* Γ(C, V) :=
      (C.presheaf.map
        (homOfLE (le_top : V ≤ (⊤ : C.Opens))).op).hom.comp
          π.appTop.hom
    let X := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz 2) V
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz 2) V
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V (preimage_sectionAway z hz) 2)) x
    let Y := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz 3) V
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz 3) V
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V (preimage_sectionAway z hz) 3)) y
    let τ : Γ(C, V) →+*
        Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
      V.topIso.inv.hom
    let f := τ.comp A
    ∀ hxy : (W.map A).toAffine.Equation X Y,
      let hxy' := affineEquation_map_comp W A τ X Y hxy
      let hP : (W.map f).toProjective.Equation
          ![τ X, τ Y, 1] := by
        rw [WeierstrassCurve.Projective.equation_some]
        exact hxy'
      let hZ : IsUnit ((![τ X, τ Y, 1] :
          Fin 3 → Γ(V.toScheme, (⊤ : V.toScheme.Opens))) 2) := by
        simp
      (V.ι ≫ F =
        projModelFromOfGlobalSections W f ![τ X, τ Y, 1] hP 2 hZ) →
      IsIso
        (F.resLE (projModelZChart W : (projModel W).Opens)
          V (le_of_eq hpre.symm)) := by
  dsimp only
  intro hxy hFV
  let hxy' := affineEquation_map_comp W
    ((C.presheaf.map
      (homOfLE (le_top :
        sectionAway z hz ≤ (⊤ : C.Opens))).op).hom.comp
          π.appTop.hom)
    (sectionAway z hz).topIso.inv.hom _ _ hxy
  let hP : (W.map ((sectionAway z hz).topIso.inv.hom.comp
      ((C.presheaf.map
        (homOfLE (le_top :
          sectionAway z hz ≤ (⊤ : C.Opens))).op).hom.comp
            π.appTop.hom))).toProjective.Equation
        ![(sectionAway z hz).topIso.inv.hom
            (overTrivializationCoefficient
              (sectionPoleSheafPower π z hz 2) (sectionAway z hz)
              (Scheme.Modules.overTrivializationOfRestrictIso
                (sectionPoleSheafPower π z hz 2) (sectionAway z hz)
                (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
                  z hz (sectionAway z hz) (preimage_sectionAway z hz) 2)) x),
          (sectionAway z hz).topIso.inv.hom
            (overTrivializationCoefficient
              (sectionPoleSheafPower π z hz 3) (sectionAway z hz)
              (Scheme.Modules.overTrivializationOfRestrictIso
                (sectionPoleSheafPower π z hz 3) (sectionAway z hz)
                (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
                  z hz (sectionAway z hz) (preimage_sectionAway z hz) 3)) y),
          1] := by
    rw [WeierstrassCurve.Projective.equation_some]
    exact hxy'
  let hZ : IsUnit
      ((![(sectionAway z hz).topIso.inv.hom
            (overTrivializationCoefficient
              (sectionPoleSheafPower π z hz 2) (sectionAway z hz)
              (Scheme.Modules.overTrivializationOfRestrictIso
                (sectionPoleSheafPower π z hz 2) (sectionAway z hz)
                (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
                  z hz (sectionAway z hz) (preimage_sectionAway z hz) 2)) x),
          (sectionAway z hz).topIso.inv.hom
            (overTrivializationCoefficient
              (sectionPoleSheafPower π z hz 3) (sectionAway z hz)
              (Scheme.Modules.overTrivializationOfRestrictIso
                (sectionPoleSheafPower π z hz 3) (sectionAway z hz)
                (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
                  z hz (sectionAway z hz) (preimage_sectionAway z hz) 3)) y),
          1] :
        Fin 3 → Γ((sectionAway z hz).toScheme,
          (⊤ : (sectionAway z hz).toScheme.Opens))) 2) := by
    simp
  have hchart :=
    sectionAway_chartSpecMapOfRingHom_isIso
      hsm z hz U hU r hspan hnzd hHOne bOne hbOne x hx y hy W hxy
  exact projModelMap_sectionAway_isIso_of_restrict
    z hz h W F hF hpre
    ((sectionAway z hz).topIso.inv.hom.comp
      ((C.presheaf.map
        (homOfLE (le_top :
          sectionAway z hz ≤ (⊤ : C.Opens))).op).hom.comp
            π.appTop.hom))
    ![(sectionAway z hz).topIso.inv.hom
        (overTrivializationCoefficient
          (sectionPoleSheafPower π z hz 2) (sectionAway z hz)
          (Scheme.Modules.overTrivializationOfRestrictIso
            (sectionPoleSheafPower π z hz 2) (sectionAway z hz)
            (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
              z hz (sectionAway z hz) (preimage_sectionAway z hz) 2)) x),
      (sectionAway z hz).topIso.inv.hom
        (overTrivializationCoefficient
          (sectionPoleSheafPower π z hz 3) (sectionAway z hz)
          (Scheme.Modules.overTrivializationOfRestrictIso
            (sectionPoleSheafPower π z hz 3) (sectionAway z hz)
            (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
              z hz (sectionAway z hz) (preimage_sectionAway z hz) 3)) y),
      1]
    hP hZ hFV hchart

end

end ModularCurves
