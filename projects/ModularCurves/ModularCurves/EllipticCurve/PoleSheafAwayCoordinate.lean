import ModularCurves.EllipticCurve.PoleSheafBaseSectionsMul
import ModularCurves.EllipticCurve.PoleSheafPowerOneSection
import ModularCurves.EllipticCurve.PoleSheafQuasicoherent

/-!
# Pole coordinates away from the marked section

On an open disjoint from the marked section, the canonical frames of all pole
powers identify their sections with ordinary regular functions. This file
records the additive, scalar, unit, and filtration rules for those coordinates.
-/

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace ModularCurves

noncomputable section

noncomputable local instance poleSheafAwayCoordinateMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Taking a coefficient in an over-site frame is additive. -/
theorem overTrivializationCoefficient_add
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (m n : Γ(M, (⊤ : X.Opens))) :
    overTrivializationCoefficient M U e (m + n) =
      overTrivializationCoefficient M U e m +
        overTrivializationCoefficient M U e n := by
  unfold overTrivializationCoefficient
  rw [map_add]
  exact (e.hom.val.app (.op (Over.mk (𝟙 U)))).hom.map_add _ _

/-- A base scalar in an over-site frame is the restriction of its image under
the structure morphism. -/
theorem overTrivializationCoefficient_baseSections_smul
    {C S : Scheme.{u}} (π : C ⟶ S) (M : C.Modules)
    (U : C.Opens)
    (e : M.over U ≅ SheafOfModules.unit (C.ringCatSheaf.over U))
    (a : Γ(S, (⊤ : S.Opens)))
    (x : Scheme.Modules.baseSections π M) :
    overTrivializationCoefficient M U e
        ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom
          (a • x)) =
      C.presheaf.map (homOfLE le_top).op (π.appTop.hom a) *
        overTrivializationCoefficient M U e
          ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom x) := by
  rw [map_smul]
  exact overTrivializationCoefficient_smul M U e (π.appTop.hom a)
    ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom x)

/-- The canonical section of the localized monoidal unit has coefficient one
in its canonical frame on every open. -/
theorem overTrivializationCoefficient_monoidalUnitSection
    {X : Scheme.{u}} (U : X.Opens) :
    overTrivializationCoefficient (𝟙_ X.Modules) U
        (Scheme.Modules.overTrivializationOfRestrictIso
          (𝟙_ X.Modules) U
          (restrictMonoidalUnitIso U.ι ≪≫
            monoidalUnitObjIso U.toScheme))
        (monoidalUnitSection X) = 1 := by
  let M := 𝟙_ X.Modules
  let N := Scheme.Modules.unitObj X
  let c := monoidalUnitObjIso X
  let eUnitOver : N.over U ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) := Iso.refl _
  let eUnit := restrictTrivializationOfOverIso N U eUnitOver
  let eZero : M.restrict U.ι ≅ Scheme.Modules.unitObj U.toScheme :=
    restrictMonoidalUnitIso U.ι ≪≫ monoidalUnitObjIso U.toScheme
  have hzero :
      (Scheme.Modules.restrictFunctor U.ι).map c.hom ≫ eUnit.hom =
        eZero.hom :=
    restrictFunctor_map_monoidalUnitObjIso_hom_comp_unitTrivialization U
  have hmap := overTrivializationCoefficient_map
    c.hom U eZero eUnit hzero (monoidalUnitSection X)
  let oneN : Γ(N, (⊤ : X.Opens)) :=
    show X.presheaf.obj (.op ⊤) from 1
  have hc :
      c.hom.val.app (.op ⊤) (monoidalUnitSection X) =
        oneN := by
    simpa only [c, monoidalUnitSection] using
      Scheme.Modules.iso_inv_hom_app_applyT c (.op ⊤) oneN
  rw [hc] at hmap
  have he :
      Scheme.Modules.overTrivializationOfRestrictIso N U eUnit =
        eUnitOver := by
    exact overTrivializationOfRestrictTrivializationOfOverIso N U eUnitOver
  rw [he] at hmap
  unfold overTrivializationCoefficient at hmap
  change X.presheaf.map (homOfLE le_top).op 1 = _ at hmap
  rw [map_one] at hmap
  exact hmap.symm

/-- Away from the marked section, a consecutive pole-filtration map does not
change the coefficient of a global section in the canonical power frames. -/
theorem
    overTrivializationCoefficient_sectionPoleSheafPower_baseSectionsSucc_of_preimage_eq_bot
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (hU : z ⁻¹ᵁ U = ⊥) (n : ℕ)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz n)) :
    overTrivializationCoefficient
        (sectionPoleSheafPower π z hz (n + 1)) U
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz (n + 1)) U
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz U hU (n + 1)))
        (Scheme.Modules.baseSectionsMap π
          (sectionPoleSheafSuccHom π z hz n) x) =
      overTrivializationCoefficient
        (sectionPoleSheafPower π z hz n) U
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz n) U
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz U hU n)) x := by
  exact overTrivializationCoefficient_map
    (sectionPoleSheafSuccHom π z hz n) U
    (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
      z hz U hU n)
    (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
      z hz U hU (n + 1))
    (sectionPoleSheafSuccHom_restrict_comp_trivializationOfSectionPreimageEqBot
      z hz U hU n) x

/-- The literal first-pole section has coefficient one in the canonical frame
on every open disjoint from the marked section. -/
theorem
    overTrivializationCoefficient_sectionPoleSheafPowerOneSection_of_preimage_eq_bot
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (hU : z ⁻¹ᵁ U = ⊥) :
    overTrivializationCoefficient
        (sectionPoleSheafPower π z hz 1) U
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz 1) U
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz U hU 1))
        (sectionPoleSheafPowerOneSection π z hz) = 1 := by
  calc
    _ = overTrivializationCoefficient
        (sectionPoleSheafPower π z hz 0) U
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz 0) U
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz U hU 0))
        (monoidalUnitSection C) := by
      simpa only [sectionPoleSheafPowerOneSection] using
        overTrivializationCoefficient_sectionPoleSheafPower_baseSectionsSucc_of_preimage_eq_bot
          z hz U hU 0 (monoidalUnitSection C)
    _ = 1 := overTrivializationCoefficient_monoidalUnitSection U

end

end ModularCurves
