/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafSuccessorProductBasis

/-!
# Monomial bases of low pole-section modules

Normalized pole-order-two and pole-order-three sections generate compatible
monomial bases in the pole filtration through order six.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open TensorProduct

universe u

namespace ModularCurves

/-- A normalized pole-order-two section adjoins its square to a basis of the
third pole module, producing a compatible basis of the fourth pole module. -/
theorem sectionPoleSheafPower_four_baseSectionsBasisOfCartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hH3 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 3).sheaf 1))
    (b3 : Module.Basis (Fin 3) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 3)))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1) :
    ∃ b4 : Module.Basis (Fin 4) Γ(S, (⊤ : S.Opens))
        (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 4)),
      (∀ i : Fin 3,
        b4 (Fin.castAdd 1 i) =
          Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 3) (b3 i)) ∧
        b4 (Fin.last 3) =
          sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x) := by
  simpa using
    sectionPoleSheafPower_succ_baseSectionsBasisOfCartierGenerator_mul
      hsm z hz U hU r hspan hnzd 1 1 hH3 b3 x hx x hx

end ModularCurves
