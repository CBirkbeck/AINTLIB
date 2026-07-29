import ModularCurves.EllipticCurve.AffineModelCoordinates
import ModularCurves.EllipticCurve.PoleSheafAwayCoordinateRing

/-!
# Affine Weierstrass evaluation on the section complement

The normalized pole coordinates on the exact complement of the marked
section define a bijective homomorphism from the affine Weierstrass coordinate
ring whenever they satisfy the affine equation.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace ModularCurves

noncomputable section

/-- The affine Weierstrass evaluation at the canonical pole coordinates on
the exact complement of the marked section is bijective. -/
theorem sectionAway_affineModelEval_bijective
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
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
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens))) :
    let A : Γ(S, (⊤ : S.Opens)) →+*
        Γ(C, sectionAway z hz) :=
      (C.presheaf.map
        (homOfLE (le_top :
          sectionAway z hz ≤ (⊤ : C.Opens))).op).hom.comp
            π.appTop.hom
    let X := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz 2) (sectionAway z hz)
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz 2) (sectionAway z hz)
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz (sectionAway z hz) (preimage_sectionAway z hz) 2)) x
    let Y := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz 3) (sectionAway z hz)
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz 3) (sectionAway z hz)
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz (sectionAway z hz) (preimage_sectionAway z hz) 3)) y
    ∀ hxy : (W.map A).toAffine.Equation X Y,
      Function.Bijective (affineModelEval W A X Y hxy) := by
  dsimp only
  intro hxy
  apply sectionAwayCoordinateRingHom_bijective
    hsm z hz U hU r hspan hnzd hHOne bOne hbOne x hx y hy W
  · exact affineModelEval_comp_algebraMap _ _ _ _ _
  · exact affineModelEval_coordX _ _ _ _ _
  · exact affineModelEval_coordY _ _ _ _ _

/-- Transporting the canonical affine evaluation through the top-open
equivalence preserves its bijectivity. -/
theorem sectionAway_top_affineModelEval_bijective
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
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
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens))) :
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
    ∀ hxy : (W.map A).toAffine.Equation X Y,
      Function.Bijective
        (affineModelEval W (τ.comp A) (τ X) (τ Y)
          (affineEquation_map_comp W A τ X Y hxy)) := by
  dsimp only
  intro hxy
  apply affineModelEval_map_bijective
  · exact
      (sectionAway z hz).topIso.symm.commRingCatIsoToRingEquiv.bijective
  · exact sectionAway_affineModelEval_bijective
      hsm z hz U hU r hspan hnzd hHOne bOne hbOne x hx y hy W hxy

end

end ModularCurves
