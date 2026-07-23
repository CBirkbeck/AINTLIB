/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafPowerOneSection

/-!
# Cartier-chart coefficients of pole sections

The trivialization of the pole sheaf induced by a local Cartier generator is
named explicitly, and the pole-filtration inclusion is computed in those
coordinates. In particular, the literal first-pole section has coefficient
equal to the Cartier generator.
-/

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace ModularCurves

noncomputable section

local instance poleSheafCartierTrivializationIsMulCommutative
    (X : Scheme.{u}) : ∀ V, IsMulCommutative (X.ringCatSheaf.obj.obj V) :=
  fun V ↦ by
    change IsMulCommutative (X.presheaf.obj V)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

local instance poleSheafCartierTrivializationMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- The simple-pole trivialization induced by a Cartier generator of the
marked section's ideal. -/
noncomputable def sectionPoleSheafTrivializationOfCartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) :
    (sectionPoleSheaf π z hz).restrict U.1.ι ≅
      Scheme.Modules.unitObj U.1.toScheme := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  let eGen := localIdealGeneratorIso z U r hr hspan hnzd
  let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
    (sectionIdealModule π z hz) U.1 eGen.symm
  let ePoleOver := SheafOfModules.dualOverIsoOfIso
    C.ringCatSheaf (sectionIdealModule π z hz) U.1 eIdeal
  exact restrictTrivializationOfOverIso
    (sectionPoleSheaf π z hz) U.1 ePoleOver

/-- The compatible trivialization of a pole-sheaf power induced by a Cartier
generator of the marked section's ideal. -/
noncomputable def sectionPoleSheafPowerTrivializationOfCartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ) :
    (sectionPoleSheafPower π z hz n).restrict U.1.ι ≅
      Scheme.Modules.unitObj U.1.toScheme :=
  sectionPoleSheafPowerTrivialization z hz U.1
    (sectionPoleSheafTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd) n

private theorem sectionPoleSheafPowerTrivializationOfCartierGenerator_zero
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) :
    sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd 0 =
      restrictMonoidalUnitIso U.1.ι ≪≫ monoidalUnitObjIso U.1.toScheme :=
  rfl

/-- In Cartier-generator coordinates, applying the pole-filtration inclusion
to a base section multiplies its coefficient by the generator. -/
theorem localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsSucc
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz n)) :
    localTrivializationCoefficient
        (sectionPoleSheafPower π z hz (n + 1)) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd (n + 1))
        (Scheme.Modules.baseSectionsMap π
          (sectionPoleSheafSuccHom π z hz n) x) =
      localTrivializationCoefficient
          (sectionPoleSheafPower π z hz n) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd n) x * r := by
  unfold sectionPoleSheafPowerTrivializationOfCartierGenerator
  unfold sectionPoleSheafTrivializationOfCartierGenerator
  exact localTrivializationCoefficient_sectionPoleSheafSuccHom
    z hz U r hr hspan hnzd n x

/-- The literal first-pole section has coefficient equal to the Cartier
generator in the compatible local trivialization. -/
theorem localTrivializationCoefficient_sectionPoleSheafPowerOneSection
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) :
    localTrivializationCoefficient
        (sectionPoleSheafPower π z hz 1) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd 1)
        (sectionPoleSheafPowerOneSection π z hz) = r := by
  calc
    _ = localTrivializationCoefficient
          (sectionPoleSheafPower π z hz 0) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd 0) (monoidalUnitSection C) * r := by
      simpa only [sectionPoleSheafPowerOneSection] using
        localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsSucc
          (π := π) z hz U r hr hspan hnzd 0 (monoidalUnitSection C)
    _ = r := by
      have hcoeff : localTrivializationCoefficient
          (sectionPoleSheafPower π z hz 0) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd 0) (monoidalUnitSection C) = 1 := by
        rw [sectionPoleSheafPowerTrivializationOfCartierGenerator_zero]
        change affineOpenAmbientSection U
          (localTrivializationTopSection (𝟙_ C.Modules) U
            (restrictMonoidalUnitIso U.1.ι ≪≫ monoidalUnitObjIso U.1.toScheme)
            (monoidalUnitSection C)) = 1
        rw [localTrivializationTopSection_monoidalUnitSection]
        simp [affineOpenAmbientSection]
      rw [hcoeff, one_mul]

end

end ModularCurves
