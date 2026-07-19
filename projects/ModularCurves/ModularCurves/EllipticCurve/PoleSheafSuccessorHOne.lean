import ModularCurves.EllipticCurve.PoleSheafQuasicoherent
import ModularCurves.ForMathlib.AcyclicAffineOpenCover
import ModularCurves.ForMathlib.TwoOpenHOne

/-!
# Cohomology of successive pole quotients

This file proves the first cohomological consequence of the pole-filtration support
calculation. A successive quotient has vanishing first cohomology whenever an affine
open containing its support and an open disjoint from the section cover the curve.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace ModularCurves

/-- A successive pole quotient has vanishing first cohomology when an affine open and
an open disjoint from the section cover the curve. -/
theorem sectionPoleSheafSuccCoker_subsingleton_H_one_of_affine_open_cover
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ)
    (U : C.affineOpens) (V : C.Opens)
    (hUV : U.1 ⊔ V = ⊤) (hV : z ⁻¹ᵁ V = ⊥) :
    Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafSuccCoker π z hz n).sheaf 1) := by
  let M := sectionPoleSheafSuccCoker π z hz n
  letI : SheafOfModules.IsQuasicoherent.{u} M := by
    dsimp only [M]
    exact sectionPoleSheafSuccCoker_isQuasicoherent hsm z hz n
  apply TopCat.Sheaf.subsingleton_H_one_of_two_open_cover M.sheaf U.1 V hUV
  · exact Scheme.Modules.restrict_subsingleton_H_of_isAffineOpen M U.1 U.2 0
  · change Subsingleton (CategoryTheory.Sheaf.H (M.restrict V.ι).sheaf 1)
    have hzero : IsZero (M.restrict V.ι) :=
      sectionPoleSheafSuccCoker_restrict_isZero_of_section_preimage_eq_bot
        hsm z hz V hV n
    exact CategoryTheory.Sheaf.subsingleton_H_of_isZero
      ((SheafOfModules.toSheaf V.toScheme.ringCatSheaf).map_isZero hzero) 1
  · intro a
    change Γ(M, U.1 ⊓ V) at a
    have hpre : z ⁻¹ᵁ (U.1 ⊓ V) = ⊥ := by
      rw [Scheme.Hom.preimage_inf, hV, inf_bot_eq]
    have hzero : IsZero (M.restrict (U.1 ⊓ V).ι) :=
      sectionPoleSheafSuccCoker_restrict_isZero_of_section_preimage_eq_bot
        hsm z hz (U.1 ⊓ V) hpre n
    let F := SheafOfModules.toSheaf (U.1 ⊓ V).toScheme.ringCatSheaf
    have hzeroSheaf : IsZero (F.obj (M.restrict (U.1 ⊓ V).ι)) :=
      F.map_isZero hzero
    let E := TopCat.Sheaf.forget AddCommGrpCat (U.1 ⊓ V).toScheme.toTopCat ⋙
      (CategoryTheory.evaluation ((U.1 ⊓ V).toScheme.Opens)ᵒᵖ
        AddCommGrpCat).obj (.op ⊤)
    letI : E.PreservesZeroMorphisms := by
      constructor
      intro A B
      rfl
    have htop : Subsingleton ↑Γ(M.restrict (U.1 ⊓ V).ι, ⊤) :=
      AddCommGrpCat.subsingleton_of_isZero (E.map_isZero hzeroSheaf)
    haveI hoverlap : Subsingleton ↑Γ(M, U.1 ⊓ V) := by
      rw [← Scheme.Opens.opensRange_ι (U := U.1 ⊓ V),
        ← Scheme.Hom.image_top_eq_opensRange]
      change Subsingleton ↑Γ(M.restrict (U.1 ⊓ V).ι, ⊤)
      exact htop
    have hoverlapSheaf :
        Subsingleton ↑(M.sheaf.obj.obj (op (U.1 ⊓ V))) := by
      change Subsingleton ↑Γ(M, U.1 ⊓ V)
      exact hoverlap
    have ha : (0 : ↑(M.sheaf.obj.obj (op (U.1 ⊓ V)))) = a :=
      hoverlapSheaf.elim 0 a
    exact ⟨0, 0, by simpa using ha⟩

/-- A successive pole quotient has vanishing first cohomology when an affine open
contains the section. -/
theorem sectionPoleSheafSuccCoker_subsingleton_H_one_of_affine_neighborhood
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤) :
    Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafSuccCoker π z hz n).sheaf 1) := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  let V : C.Opens :=
    ⟨(Set.range ⇑z)ᶜ, z.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hV : z ⁻¹ᵁ V = ⊥ := by
    ext s
    change z s ∈ (Set.range ⇑z)ᶜ ↔ s ∈ (⊥ : S.Opens)
    simp
  have hUV : U.1 ⊔ V = ⊤ := by
    ext c
    change c ∈ (U.1 : Set C) ∪ (Set.range ⇑z)ᶜ ↔ c ∈ Set.univ
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hc : c ∈ Set.range ⇑z
    · left
      obtain ⟨s, rfl⟩ := hc
      have hs : s ∈ z ⁻¹ᵁ U.1 := by
        rw [hU]
        trivial
      exact hs
    · exact Or.inr hc
  exact sectionPoleSheafSuccCoker_subsingleton_H_one_of_affine_open_cover
    hsm z hz n U V hUV hV

end ModularCurves
