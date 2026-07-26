/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafAwayCoordinate
import ModularCurves.EllipticCurve.PoleSheafWeierstrassRelation

/-!
# The Weierstrass equation away from the marked section

The global pole-sheaf relation is evaluated in the canonical frames on an open
disjoint from the marked section. This gives the affine Weierstrass equation
with the same coefficients as the homogeneous equation near the section.
-/

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace ModularCurves

noncomputable section

noncomputable local instance poleSheafWeierstrassAwayMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem overTrivializationCoefficient_baseSections_add
    {C S : Scheme.{u}} (π : C ⟶ S) (M : C.Modules)
    (U : C.Opens)
    (e : M.over U ≅ SheafOfModules.unit (C.ringCatSheaf.over U))
    (x y : Scheme.Modules.baseSections π M) :
    overTrivializationCoefficient M U e
        ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom (x + y)) =
      overTrivializationCoefficient M U e
          ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom x) +
        overTrivializationCoefficient M U e
          ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom y) := by
  rw [map_add]
  exact overTrivializationCoefficient_add M U e _ _

private theorem overTrivializationCoefficient_baseSectionsIso_hom
    {C S : Scheme.{u}} (π : C ⟶ S) (M : C.Modules)
    (U : C.Opens)
    (e : M.over U ≅ SheafOfModules.unit (C.ringCatSheaf.over U))
    (x : Scheme.Modules.baseSections π M) :
    overTrivializationCoefficient M U e
        ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom x) =
      overTrivializationCoefficient M U e x := by
  rfl

/-- On an open disjoint from the marked section, a global degree-six pole
relation becomes the affine generalized Weierstrass equation in the canonical
regular coordinates. -/
theorem sectionPoleSheafPower_six_over_weierstrass_equation_of_preimage_eq_bot
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (a₁ a₂ a₃ a₄ a₆ : Γ(S, (⊤ : S.Opens)))
    (hrel :
      sectionPoleSheafPower_baseSectionsMul z hz 3 3 (y ⊗ₜ y) +
          a₁ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (sectionPoleSheafPower_baseSectionsMul z hz 2 3 (x ⊗ₜ y)) +
          a₃ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (Scheme.Modules.baseSectionsMap π
                    (sectionPoleSheafSuccHom π z hz 3) y)) =
        sectionPoleSheafPower_baseSectionsMul z hz 2 4
            (x ⊗ₜ sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x)) +
          a₂ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x))) +
          a₄ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (Scheme.Modules.baseSectionsMap π
                    (sectionPoleSheafSuccHom π z hz 3)
                      (Scheme.Modules.baseSectionsMap π
                        (sectionPoleSheafSuccHom π z hz 2) x))) +
          a₆ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (Scheme.Modules.baseSectionsMap π
                    (sectionPoleSheafSuccHom π z hz 3)
                      (Scheme.Modules.baseSectionsMap π
                        (sectionPoleSheafSuccHom π z hz 2)
                          (Scheme.Modules.baseSectionsMap π
                            (sectionPoleSheafSuccHom π z hz 1)
                              (sectionPoleSheafPowerOneSection π z hz)))))) :
    let X := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz 2) V
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz 2) V
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V hV 2)) x
    let Y := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz 3) V
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz 3) V
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V hV 3)) y
    let A : Γ(S, (⊤ : S.Opens)) →+* Γ(C, V) :=
      (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
    let W : WeierstrassCurve Γ(S, (⊤ : S.Opens)) :=
      ⟨a₁, a₂, a₃, a₄, a₆⟩
    (W.map A).toAffine.Equation X Y := by
  dsimp only
  rw [WeierstrassCurve.Affine.equation_iff]
  have hcoeff := congrArg
    (fun q : Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz 6) ↦
      overTrivializationCoefficient
        (sectionPoleSheafPower π z hz 6) V
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz 6) V
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz V hV 6))
        ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π
          (sectionPoleSheafPower π z hz 6)).hom q)) hrel
  simp only [overTrivializationCoefficient_baseSections_add,
    overTrivializationCoefficient_baseSections_smul] at hcoeff
  simp only [overTrivializationCoefficient_baseSectionsIso_hom] at hcoeff
  let ePole :=
    sectionPoleSheafTrivializationOfSectionPreimageEqBot z hz V hV
  have hmul (m n : ℕ)
      (p : Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz m))
      (q : Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz n)) :
      overTrivializationCoefficient
          (sectionPoleSheafPower π z hz (m + n)) V
          (Scheme.Modules.overTrivializationOfRestrictIso
            (sectionPoleSheafPower π z hz (m + n)) V
            (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
              z hz V hV (m + n)))
          (sectionPoleSheafPower_baseSectionsMul z hz m n (p ⊗ₜ q)) =
        overTrivializationCoefficient
            (sectionPoleSheafPower π z hz m) V
            (Scheme.Modules.overTrivializationOfRestrictIso
              (sectionPoleSheafPower π z hz m) V
              (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
                z hz V hV m)) p *
          overTrivializationCoefficient
            (sectionPoleSheafPower π z hz n) V
            (Scheme.Modules.overTrivializationOfRestrictIso
              (sectionPoleSheafPower π z hz n) V
              (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
                z hz V hV n)) q := by
    simpa only [ePole,
      sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot] using
      overTrivializationCoefficient_sectionPoleSheafPower_baseSectionsMul_tmul
        z hz V ePole m n p q
  have hyy := hmul 3 3 y y
  have hxy := hmul 2 3 x y
  have hxx := hmul 2 2 x x
  have hxxx := hmul 2 4 x
    (sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x))
  have hone :=
    overTrivializationCoefficient_sectionPoleSheafPowerOneSection_of_preimage_eq_bot
      z hz V hV
  rw [hyy] at hcoeff
  simp only [
    overTrivializationCoefficient_sectionPoleSheafPower_baseSectionsSucc_of_preimage_eq_bot]
      at hcoeff
  simp only [hxy, hxx, hxxx, hone] at hcoeff
  have hA (a : Γ(S, (⊤ : S.Opens))) :
      C.presheaf.map
          (homOfLE (le_top : V ≤ (⊤ : C.Opens))).op (π.appTop.hom a) =
        ((C.presheaf.map
          (homOfLE (le_top : V ≤ (⊤ : C.Opens))).op).hom.comp
            π.appTop.hom) a := by
    rfl
  simp only [hA] at hcoeff
  simp only [WeierstrassCurve.map, RingHom.comp_apply]
  linear_combination hcoeff

end

end ModularCurves
