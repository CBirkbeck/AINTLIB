import ModularCurves.EllipticCurve.PoleSheafQuasicoherent
import ModularCurves.ForMathlib.SheafDisjointUnion

/-!
# Sections of successive pole quotients

This file computes global sections of a consecutive pole-filtration quotient from
any open neighborhood of the marked section.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace ModularCurves

/-- Global sections of a consecutive pole quotient are determined by any open
containing the whole marked section. -/
theorem sectionPoleSheafSuccCoker_bijective_restrict_of_neighborhood
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ)
    (U : C.Opens) (hU : z ⁻¹ᵁ U = ⊤) :
    let M := sectionPoleSheafSuccCoker π z hz n
    Function.Bijective fun s : Γ(M, (⊤ : C.Opens)) ↦
      M.presheaf.map (homOfLE (le_top : U ≤ (⊤ : C.Opens))).op s := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  let M := sectionPoleSheafSuccCoker π z hz n
  let F := (SheafOfModules.toSheaf C.ringCatSheaf).obj M
  let V : C.Opens :=
    ⟨(Set.range ⇑z)ᶜ, z.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hV : z ⁻¹ᵁ V = ⊥ := by
    ext s
    change z s ∈ (Set.range ⇑z)ᶜ ↔ s ∈ (⊥ : S.Opens)
    simp
  have hUV : U ⊔ V = ⊤ := by
    ext c
    change c ∈ (U : Set C) ∪ (Set.range ⇑z)ᶜ ↔ c ∈ Set.univ
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hc : c ∈ Set.range ⇑z
    · left
      obtain ⟨s, rfl⟩ := hc
      have hs : s ∈ z ⁻¹ᵁ U := by
        rw [hU]
        trivial
      exact hs
    · exact Or.inr hc
  have hzeroV : IsZero (M.restrict V.ι) :=
    sectionPoleSheafSuccCoker_restrict_isZero_of_section_preimage_eq_bot
      hsm z hz V hV n
  haveI hVsections : Subsingleton Γ(M, V) :=
    Scheme.Modules.subsingleton_sections_of_isZero_restrict M V hzeroV
  haveI hVsheaf : Subsingleton (ToType (F.1.obj (op V))) := by
    change Subsingleton Γ(M, V)
    infer_instance
  have hpreOverlap : z ⁻¹ᵁ (U ⊓ V) = ⊥ := by
    rw [Scheme.Hom.preimage_inf, hV, inf_bot_eq]
  have hzeroOverlap : IsZero (M.restrict (U ⊓ V).ι) :=
    sectionPoleSheafSuccCoker_restrict_isZero_of_section_preimage_eq_bot
      hsm z hz (U ⊓ V) hpreOverlap n
  haveI hoverlap : Subsingleton Γ(M, U ⊓ V) :=
    Scheme.Modules.subsingleton_sections_of_isZero_restrict
      M (U ⊓ V) hzeroOverlap
  haveI hoverlapSheaf :
      Subsingleton (ToType (F.1.obj (op (U ⊓ V)))) := by
    change Subsingleton Γ(M, U ⊓ V)
    infer_instance
  exact TopCat.Sheaf.bijective_restrict_of_sup_eq_top_of_subsingleton
    F hUV

end ModularCurves
