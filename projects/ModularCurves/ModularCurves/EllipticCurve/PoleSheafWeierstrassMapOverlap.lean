/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafWeierstrassOverlap

/-!
# Weierstrass comparison maps on Cartier/away overlaps

The local pole coordinates from a Cartier frame and the canonical frame away
from the marked section are compared after restriction to their overlap.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace ModularCurves

noncomputable section

/-- Restricting a Cartier-frame pole coefficient to a Cartier/away overlap
gives the away-frame coefficient times the appropriate power of the Cartier
generator. -/
theorem sectionPoleSheafPower_cartier_away_overlap_restrict_coefficient
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥)
    (n : ℕ)
    (m : Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens))) :
    let W := U.1 ⊓ V
    let XU := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz n) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd n) m
    let XV := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz n) V
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz n) V
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V hV n)) m
    let resU : Γ(C, U.1) →+* Γ(C, W) :=
      (C.presheaf.map (homOfLE inf_le_left).op).hom
    let resV : Γ(C, V) →+* Γ(C, W) :=
      (C.presheaf.map (homOfLE inf_le_right).op).hom
    resU XU = resV XV * resU r ^ n := by
  dsimp only
  rw [← localTrivializationCoefficient_restrict
    (sectionPoleSheafPower π z hz n) U inf_le_left
    (sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd n) m]
  rw [← overTrivializationCoefficient_restrict
    (sectionPoleSheafPower π z hz n) inf_le_right
    (Scheme.Modules.overTrivializationOfRestrictIso
      (sectionPoleSheafPower π z hz n) V
      (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
        z hz V hV n)) m]
  simpa only [
    Scheme.Modules.overTrivializationOfRestrictOpenTrivialization] using
      sectionPoleSheafPower_cartier_away_overlap_coefficient
        z hz U r hr hspan hnzd V hV n m

end

end ModularCurves
