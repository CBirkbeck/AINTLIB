/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafAwaySections

/-!
# Injectivity of pole coefficients away from a marked section

Restriction from a Cartier chart to the complement of its marked section is
localization at a nonzerodivisor. Consequently, a global section of any pole
power is determined by its ordinary coefficient away from the section.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace ModularCurves

/-- Restriction from a Cartier chart to its intersection with the complement
of the marked section is injective. -/
theorem affine_inf_sectionAway_restrict_injective
    {C S : Scheme.{u}} {π : C ⟶ S}
    [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1))
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) :
    Function.Injective
      (C.presheaf.map
        (homOfLE
          (inf_le_left :
            U.1 ⊓ sectionAway z hz ≤ U.1)).op).hom := by
  let V := U.1 ⊓ sectionAway z hz
  let res : Γ(C, U.1) ⟶ Γ(C, V) :=
    C.presheaf.map (homOfLE (inf_le_left : V ≤ U.1)).op
  letI : Algebra Γ(C, U.1) Γ(C, V) := res.hom.toAlgebra
  haveI : IsLocalization.Away r Γ(C, V) :=
    U.2.isLocalization_of_eq_basicOpen (f := r)
      (homOfLE (inf_le_left : V ≤ U.1))
      (affine_inf_sectionAway_eq_basicOpen z hz U r hspan)
  exact IsLocalization.injective Γ(C, V)
    (Submonoid.powers_le.mpr hnzd)

/-- A global section of `O(n[z])` is determined by its ordinary coefficient on
the complement of the marked section. -/
theorem sectionPoleSheafPower_away_coefficient_injective
    {C S : Scheme.{u}} {π : C ⟶ S}
    [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (n : ℕ) :
    Function.Injective
      (fun m : Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) =>
        overTrivializationCoefficient
          (sectionPoleSheafPower π z hz n) (sectionAway z hz)
          (Scheme.Modules.overTrivializationOfRestrictIso
            (sectionPoleSheafPower π z hz n) (sectionAway z hz)
            (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
              z hz (sectionAway z hz) (preimage_sectionAway z hz) n)) m) := by
  intro m₁ m₂ hcoeff
  let M := sectionPoleSheafPower π z hz n
  let V := sectionAway z hz
  let W := U.1 ⊓ V
  have hV : z ⁻¹ᵁ V = ⊥ := preimage_sectionAway z hz
  have hUV : U.1 ⊔ V = ⊤ :=
    sup_sectionAway_eq_top_of_preimage_eq_top z hz U.1 hU
  have hr : r ∈ z.ker.ideal U := by
    rw [hspan]
    exact Ideal.mem_span_singleton_self r
  let eU :=
    sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd n
  let eV :=
    sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
      z hz V hV n
  let eUW :=
    Scheme.Modules.restrictOpenTrivialization
      (inf_le_left : W ≤ U.1) eU
  let eVW :=
    Scheme.Modules.restrictOpenTrivialization
      (inf_le_right : W ≤ V) eV
  have hcoeffV :
      overTrivializationCoefficient M V
          (Scheme.Modules.overTrivializationOfRestrictIso M V eV) m₁ =
        overTrivializationCoefficient M V
          (Scheme.Modules.overTrivializationOfRestrictIso M V eV) m₂ := by
    simpa only [M, V, eV] using hcoeff
  have hcoeffW :
      overTrivializationCoefficient M W
          (Scheme.Modules.overTrivializationOfRestrictIso M W eVW) m₁ =
        overTrivializationCoefficient M W
          (Scheme.Modules.overTrivializationOfRestrictIso M W eVW) m₂ := by
    calc
      _ = C.presheaf.map (homOfLE (inf_le_right : W ≤ V)).op
          (overTrivializationCoefficient M V
            (Scheme.Modules.overTrivializationOfRestrictIso M V eV) m₁) := by
        rw [Scheme.Modules.overTrivializationOfRestrictOpenTrivialization]
        exact overTrivializationCoefficient_restrict M inf_le_right
          (Scheme.Modules.overTrivializationOfRestrictIso M V eV) m₁
      _ = C.presheaf.map (homOfLE (inf_le_right : W ≤ V)).op
          (overTrivializationCoefficient M V
            (Scheme.Modules.overTrivializationOfRestrictIso M V eV) m₂) := by
        rw [hcoeffV]
      _ = _ := by
        rw [Scheme.Modules.overTrivializationOfRestrictOpenTrivialization]
        exact (overTrivializationCoefficient_restrict M inf_le_right
          (Scheme.Modules.overTrivializationOfRestrictIso M V eV) m₂).symm
  have hcoeffUW :
      overTrivializationCoefficient M W
          (Scheme.Modules.overTrivializationOfRestrictIso M W eUW) m₁ =
        overTrivializationCoefficient M W
          (Scheme.Modules.overTrivializationOfRestrictIso M W eUW) m₂ := by
    calc
      _ = overTrivializationCoefficient M W
            (Scheme.Modules.overTrivializationOfRestrictIso M W eVW) m₁ *
          C.presheaf.map (homOfLE (inf_le_left : W ≤ U.1)).op r ^ n := by
        simpa only [M, V, W, eUW, eVW] using
          sectionPoleSheafPower_cartier_away_overlap_coefficient
            z hz U r hr hspan hnzd V hV n m₁
      _ = overTrivializationCoefficient M W
            (Scheme.Modules.overTrivializationOfRestrictIso M W eVW) m₂ *
          C.presheaf.map (homOfLE (inf_le_left : W ≤ U.1)).op r ^ n := by
        rw [hcoeffW]
      _ = _ := by
        simpa only [M, V, W, eUW, eVW] using
          (sectionPoleSheafPower_cartier_away_overlap_coefficient
            z hz U r hr hspan hnzd V hV n m₂).symm
  have hlocalU :
      localTrivializationCoefficient M U eU m₁ =
        localTrivializationCoefficient M U eU m₂ := by
    apply affine_inf_sectionAway_restrict_injective
      z hz U r hspan hnzd
    calc
      _ = overTrivializationCoefficient M W
          (Scheme.Modules.overTrivializationOfRestrictIso M W eUW) m₁ :=
        (localTrivializationCoefficient_restrict M U inf_le_left eU m₁).symm
      _ = overTrivializationCoefficient M W
          (Scheme.Modules.overTrivializationOfRestrictIso M W eUW) m₂ :=
        hcoeffUW
      _ = _ :=
        localTrivializationCoefficient_restrict M U inf_le_left eU m₂
  have hresU :=
    restrict_eq_of_localTrivializationCoefficient_eq M U eU m₁ m₂ hlocalU
  have hresV :=
    restrict_eq_of_overTrivializationCoefficient_eq M V
      (Scheme.Modules.overTrivializationOfRestrictIso M V eV)
      m₁ m₂ hcoeffV
  exact TopCat.Sheaf.eq_of_locally_eq₂ ⟨M.presheaf, M.isSheaf⟩
    (homOfLE (le_top : U.1 ≤ (⊤ : C.Opens)))
    (homOfLE (le_top : V ≤ (⊤ : C.Opens)))
    (by rw [hUV]) m₁ m₂ hresU hresV

end ModularCurves
