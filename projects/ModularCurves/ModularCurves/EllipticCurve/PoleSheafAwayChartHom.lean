import ModularCurves.EllipticCurve.AffineModelCoordinateTransition
import ModularCurves.EllipticCurve.PoleSheafAwayAffineModelEval

/-!
# The projective chart map on the section complement

The affine pole coordinates on the complement of the marked section induce
a bijective homomorphism from the standard projective `Z`-chart ring.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open WeierstrassCurve.Projective

universe u

namespace ModularCurves

noncomputable section

/-- The `Z`-chart homomorphism defined by the canonical pole coordinates on
the section complement is bijective. -/
theorem sectionAway_chartAwayHomOfTriple_z_bijective
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
    let f := τ.comp A
    ∀ hxy : (W.map A).toAffine.Equation X Y,
      let hxy' := affineEquation_map_comp W A τ X Y hxy
      letI : Algebra Γ(S, (⊤ : S.Opens))
          Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
        f.toAlgebra
      let hxy'' : (W.map (algebraMap Γ(S, (⊤ : S.Opens))
          Γ(V.toScheme, (⊤ : V.toScheme.Opens)))).toAffine.Equation
          (τ X) (τ Y) := by
        rw [RingHom.algebraMap_toAlgebra]
        exact hxy'
      let P : Fin 3 → Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
        ![τ X, τ Y, 1]
      let hP : (W.map (algebraMap Γ(S, (⊤ : S.Opens))
          Γ(V.toScheme, (⊤ : V.toScheme.Opens)))).toProjective.Equation P := by
        rw [WeierstrassCurve.Projective.equation_some]
        exact hxy''
      Function.Bijective
        (chartAwayHomOfTriple W 2 P 1 (by simp [P]) hP).toRingHom := by
  dsimp only
  intro hxy
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ((sectionAway z hz).toScheme,
        (⊤ : (sectionAway z hz).toScheme.Opens)) :=
    ((sectionAway z hz).topIso.inv.hom.comp
      ((C.presheaf.map
        (homOfLE (le_top :
          sectionAway z hz ≤ (⊤ : C.Opens))).op).hom.comp
            π.appTop.hom)).toAlgebra
  apply chartAwayHomOfTriple_z_bijective_of_ringHom
  exact sectionAway_top_affineModelEval_bijective
    hsm z hz U hU r hspan hnzd hHOne bOne hbOne x hx y hy W hxy

end

end ModularCurves
