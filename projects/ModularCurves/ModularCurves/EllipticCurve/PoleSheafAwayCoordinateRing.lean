import ModularCurves.EllipticCurve.PoleFiltrationExhaustive
import ModularCurves.EllipticCurve.PoleSheafAwayCoefficientInjective
import ModularCurves.EllipticCurve.PoleSheafFiniteStageAwayCompatibility

/-!
# The coordinate ring of the complement of a marked section

The compatible pole bases identify every finite pole stage with the
corresponding filtration of an affine Weierstrass coordinate ring. Exhaustion
and denominator clearing promote this finite-stage comparison to a bijection
on the exact complement of the marked section.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace ModularCurves

noncomputable section

/-- A coordinate-ring homomorphism compatible with the normalized pole
coordinates is bijective on the exact complement of the marked section. -/
theorem sectionAwayCoordinateRingHom_bijective
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
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (φ : W.toAffine.CoordinateRing →+* Γ(C, sectionAway z hz))
    (hφ : φ.comp
      (algebraMap Γ(S, (⊤ : S.Opens)) W.toAffine.CoordinateRing) =
        (C.presheaf.map
          (homOfLE (le_top : sectionAway z hz ≤ (⊤ : C.Opens))).op).hom.comp
            π.appTop.hom)
    (hφx : φ (coordX W) =
      overTrivializationCoefficient
        (sectionPoleSheafPower π z hz 2) (sectionAway z hz)
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz 2) (sectionAway z hz)
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz (sectionAway z hz) (preimage_sectionAway z hz) 2)) x)
    (hφy : φ (coordY W) =
      overTrivializationCoefficient
        (sectionPoleSheafPower π z hz 3) (sectionAway z hz)
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz 3) (sectionAway z hz)
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz (sectionAway z hz) (preimage_sectionAway z hz) 3)) y) :
    Function.Bijective φ := by
  constructor
  · suffices hker : ∀ a, φ a = 0 → a = 0 by
      intro a b hab
      rw [← sub_eq_zero]
      apply hker
      rw [map_sub, hab, sub_self]
    intro a ha
    obtain ⟨n, han⟩ := exists_mem_poleOrderFiltration W a
    let aStage : poleOrderFiltration W (n + 1) :=
      ⟨a, poleOrderFiltration_mono W (Nat.le_succ n) han⟩
    let e := sectionPoleSheafPower_poleOrderFiltrationLinearEquiv
      hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy W n
    let q := e.symm aStage
    have hcompat :=
      sectionPoleSheafPower_poleOrderFiltrationLinearEquiv_away
        hsm z hz U hU r hspan hnzd hHOne bOne hbOne x hx y hy
        (sectionAway z hz) (preimage_sectionAway z hz) W φ hφ hφx hφy n q
    have hcoeff :
        overTrivializationCoefficient
            (sectionPoleSheafPower π z hz (n + 1)) (sectionAway z hz)
            (Scheme.Modules.overTrivializationOfRestrictIso
              (sectionPoleSheafPower π z hz (n + 1)) (sectionAway z hz)
              (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
                z hz (sectionAway z hz) (preimage_sectionAway z hz) (n + 1))) q =
          0 := by
      rw [← hcompat]
      simpa only [q, e, LinearEquiv.apply_symm_apply, aStage] using ha
    have hq : q = 0 := by
      apply sectionPoleSheafPower_away_coefficient_injective
        z hz U hU r hspan hnzd (n + 1)
      have hzero :
          overTrivializationCoefficient
              (sectionPoleSheafPower π z hz (n + 1)) (sectionAway z hz)
              (Scheme.Modules.overTrivializationOfRestrictIso
                (sectionPoleSheafPower π z hz (n + 1)) (sectionAway z hz)
                (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
                  z hz (sectionAway z hz) (preimage_sectionAway z hz) (n + 1)))
              0 = 0 := by
        unfold overTrivializationCoefficient
        rw [map_zero]
        exact
          ((Scheme.Modules.overTrivializationOfRestrictIso
            (sectionPoleSheafPower π z hz (n + 1)) (sectionAway z hz)
            (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
              z hz (sectionAway z hz) (preimage_sectionAway z hz)
                (n + 1))).hom.val.app
              (.op (Over.mk (𝟙 (sectionAway z hz))))).hom.map_zero
      exact hcoeff.trans hzero.symm
    have haStage : aStage = 0 := by
      rw [← e.apply_symm_apply aStage]
      change e q = 0
      rw [hq, map_zero]
    exact congrArg Subtype.val haStage
  · intro s
    obtain ⟨n, m, hm⟩ :=
      exists_sectionPoleSheafPower_away_coefficient_eq
        z hz U hU r hspan hnzd s
    let q0 : Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz n) :=
      (Scheme.Modules.baseSectionsIsoRestrictScalarsTop π
        (sectionPoleSheafPower π z hz n)).inv m
    let q := Scheme.Modules.baseSectionsMap π
      (sectionPoleSheafSuccHom π z hz n) q0
    let e := sectionPoleSheafPower_poleOrderFiltrationLinearEquiv
      hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy W n
    refine ⟨((e q : poleOrderFiltration W (n + 1)) :
      W.toAffine.CoordinateRing), ?_⟩
    rw [sectionPoleSheafPower_poleOrderFiltrationLinearEquiv_away
      hsm z hz U hU r hspan hnzd hHOne bOne hbOne x hx y hy
      (sectionAway z hz) (preimage_sectionAway z hz) W φ hφ hφx hφy n q]
    rw [show q = Scheme.Modules.baseSectionsMap π
      (sectionPoleSheafSuccHom π z hz n) q0 from rfl,
      overTrivializationCoefficient_sectionPoleSheafPower_baseSectionsSucc_of_preimage_eq_bot]
    change
      overTrivializationCoefficient
          (sectionPoleSheafPower π z hz n) (sectionAway z hz)
          (Scheme.Modules.overTrivializationOfRestrictIso
            (sectionPoleSheafPower π z hz n) (sectionAway z hz)
            (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
              z hz (sectionAway z hz) (preimage_sectionAway z hz) n))
          ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π
            (sectionPoleSheafPower π z hz n)).hom q0) = s
    have hq0 :
        (Scheme.Modules.baseSectionsIsoRestrictScalarsTop π
          (sectionPoleSheafPower π z hz n)).hom q0 = m := by
      change ConcreteCategory.hom
        ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π
          (sectionPoleSheafPower π z hz n)).inv ≫
            (Scheme.Modules.baseSectionsIsoRestrictScalarsTop π
              (sectionPoleSheafPower π z hz n)).hom) m = m
      rw [Iso.inv_hom_id]
      rfl
    rw [hq0, hm]

end

end ModularCurves
