/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafProjectiveXY
import ModularCurves.EllipticCurve.PoleSheafSuccessorBasis

/-!
# The rank-two and rank-three pole modules (GAP-A-3)

`π_*𝒪(2[0])` free of rank `2` and `π_*𝒪(3[0])` free of rank `3` over an arbitrary base,
in the shape the theorem-of-the-square construction consumes.

These are the two stages the relative theorem of the square actually needs: the line
through `P` and `Q` lives in `π_*𝒪(3[0])` and the vertical through `P + Q` in
`π_*𝒪(2[0])` (GAP-A-4/5 on the dev board). The higher stages
(`PoleSheafMonomialBasis.lean`, degrees 4–6) are for the Weierstrass relation and the
projective embedding, and are not used here.

Both results are thin wrappers of the generic ladder step
`sectionPoleSheafPower_succ_baseSectionsBasisOfCartierGenerator`, phrased with the
normalised-coordinate hypothesis
(`sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator … = 1`) that
`FibrewiseElliptic.exists_sectionPoleSheafPower_baseChange_projectiveClosed_local_xy`
produces, so the two fit together with no bridging at the use site.

The rank-one input `bOne` and the `H¹` vanishing are supplied, Zariski-locally on the
base, by `PoleSheafPowerOneAwayBaseChangeBasis.lean` and
`FibrewiseElliptic.sectionPoleSheafPower_baseChange_projectiveClosed_subsingleton_H_one`
respectively.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace ModularCurves

/-- **(GAP-A-3, rank two)** A normalised pole-order-two section extends a rank-one basis
of `π_*𝒪([0])` to a rank-two basis of `π_*𝒪(2[0])`. -/
theorem sectionPoleSheafPower_two_baseSectionsBasisOfCartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hH1 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (bOne : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 1)))
    (x : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1) :
    ∃ b2 : Module.Basis (Fin 2) Γ(S, (⊤ : S.Opens))
        (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 2)),
      (∀ i : Fin 1,
        b2 (Fin.castAdd 1 i) =
          Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 1) (bOne i)) ∧
        b2 (Fin.last 1) = x := by
  simpa using
    sectionPoleSheafPower_succ_baseSectionsBasisOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 hH1 bOne x hx

/-- **(GAP-A-3, rank three)** A normalised pole-order-three section extends a rank-two
basis of `π_*𝒪(2[0])` to a rank-three basis of `π_*𝒪(3[0])`. -/
theorem sectionPoleSheafPower_three_baseSectionsBasisOfCartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hH2 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 2).sheaf 1))
    (b2 : Module.Basis (Fin 2) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 2)))
    (y : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1) :
    ∃ b3 : Module.Basis (Fin 3) Γ(S, (⊤ : S.Opens))
        (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 3)),
      (∀ i : Fin 2,
        b3 (Fin.castAdd 1 i) =
          Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 2) (b2 i)) ∧
        b3 (Fin.last 2) = y := by
  simpa using
    sectionPoleSheafPower_succ_baseSectionsBasisOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 hH2 b2 y hy

end ModularCurves
