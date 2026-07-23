/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafProjectiveXY
import ModularCurves.EllipticCurve.PoleSheafBaseSectionsMul

/-!
# Multiplication of successor pole coordinates

The highest consecutive-quotient coordinate of a product of positive pole
sections is the product of their highest coordinates.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open TensorProduct

universe u

namespace ModularCurves

local instance poleSheafSuccessorCoordinateMulIsMulCommutative (X : Scheme.{u}) :
    ∀ V, IsMulCommutative (X.ringCatSheaf.obj.obj V) :=
  fun V ↦ by
    change IsMulCommutative (X.presheaf.obj V)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- For one Cartier generator, the highest successor coordinate of a pure
tensor pole product is the product of the two highest coordinates. -/
theorem sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator_mul
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (m n : ℕ)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (m + 1)))
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1))) :
    sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
        hsm z hz U hU r hspan hnzd ((m + 1) + n)
        (sectionPoleSheafPower_baseSectionsMul z hz (m + 1) (n + 1) (x ⊗ₜ y)) =
      sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
          hsm z hz U hU r hspan hnzd m x *
        sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
          hsm z hz U hU r hspan hnzd n y := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  have hr : r ∈ z.ker.ideal U := by
    rw [hspan]
    exact Ideal.mem_span_singleton_self r
  let eGen := localIdealGeneratorIso z U r hr hspan hnzd
  let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
    (sectionIdealModule π z hz) U.1 eGen.symm
  let ePoleOver := SheafOfModules.dualOverIsoOfIso
    C.ringCatSheaf (sectionIdealModule π z hz) U.1 eIdeal
  let ePole := restrictTrivializationOfOverIso
    (sectionPoleSheaf π z hz) U.1 ePoleOver
  have hprod :=
    sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator_hom_baseSectionsMap
      hsm z hz U hU r hspan hnzd ((m + 1) + n)
        (sectionPoleSheafPower_baseSectionsMul z hz (m + 1) (n + 1) (x ⊗ₜ y))
  have hx :=
    sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator_hom_baseSectionsMap
      hsm z hz U hU r hspan hnzd m x
  have hy :=
    sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator_hom_baseSectionsMap
      hsm z hz U hU r hspan hnzd n y
  dsimp only at hprod hx hy
  have hmul :=
    localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsMul_tmul
      z hz U ePole (m + 1) (n + 1) x y
  rw [sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator_apply]
  rw [hprod]
  change
    S.presheaf.map (eqToHom hU.symm).op
        (z.app U.1
          (localTrivializationCoefficient
            (sectionPoleSheafPower π z hz (m + 1 + n + 1)) U
            (sectionPoleSheafPowerTrivialization z hz U.1 ePole (m + 1 + n + 1))
            (sectionPoleSheafPower_baseSectionsMul z hz
              (m + 1) (n + 1) (x ⊗ₜ y)))) = _
  rw [show
    localTrivializationCoefficient
        (sectionPoleSheafPower π z hz (m + 1 + n + 1)) U
        (sectionPoleSheafPowerTrivialization z hz U.1 ePole (m + 1 + n + 1))
        (sectionPoleSheafPower_baseSectionsMul z hz (m + 1) (n + 1) (x ⊗ₜ y)) =
      localTrivializationCoefficient
          (sectionPoleSheafPower π z hz (m + 1)) U
          (sectionPoleSheafPowerTrivialization z hz U.1 ePole (m + 1)) x *
        localTrivializationCoefficient
          (sectionPoleSheafPower π z hz (n + 1)) U
          (sectionPoleSheafPowerTrivialization z hz U.1 ePole (n + 1)) y by
      convert hmul using 1
      congr 3]
  rw [map_mul, map_mul]
  rw [← hx, ← hy]
  rfl

end ModularCurves
