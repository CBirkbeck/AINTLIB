import ModularCurves.EllipticCurve.PoleSheafQuasicoherent
import ModularCurves.ForMathlib.AffinePatchBaseChange
import ModularCurves.ForMathlib.SchemeModuleBaseCechZero
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

/-- On a Cartier-generator neighborhood containing the section, global base
sections of a consecutive pole quotient form the regular rank-one base
module. -/
noncomputable def sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ) :
    Scheme.Modules.baseSections π (sectionPoleSheafSuccCoker π z hz n) ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens)) Γ(S, (⊤ : S.Opens)) := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  let M := sectionPoleSheafSuccCoker π z hz n
  have hr : r ∈ z.ker.ideal U := by
    rw [hspan]
    exact Ideal.mem_span_singleton_self r
  exact Scheme.Modules.baseSectionsRestrictIsoOfBijective π M U.1
      (sectionPoleSheafSuccCoker_bijective_restrict_of_neighborhood
        hsm z hz n U.1 hU) ≪≫
    Scheme.Modules.baseSectionsMapIso (U.1.ι ≫ π)
      (sectionPoleSheafSuccCoker_restrictIsoPushforwardUnit
        z hz U r hr hspan hnzd n) ≪≫
    Scheme.Modules.baseSectionsRestrictPushforwardUnitIsoOfSection
      π z hz U.1 hU

/-- Around every point of an affine base, the base-changed section has an affine
neighborhood on which its ideal has an explicit regular generator. -/
theorem exists_affineBaseChange_sectionCartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S} [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (s : S) :
    ∃ V : S.affineOpens, s ∈ V.1 ∧
      let t : V.1.toScheme ⟶ S := V.1.ι
      let zV := sectionBaseChange z hz t
      ∃ U : (pullback π t).affineOpens,
        zV ⁻¹ᵁ U.1 = ⊤ ∧
          ∃ r : Γ(pullback π t, U.1),
            zV.ker.ideal U = Ideal.span {r} ∧
              r ∈ nonZeroDivisors Γ(pullback π t, U.1) := by
  obtain ⟨U, hzsU, r, hspan, hnzd⟩ :=
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm z hz).locallyPrincipal (z s)
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, hVU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      hzsU ((z ⁻¹ᵁ U.1).2)
  let Vaff : S.affineOpens := ⟨V, hV⟩
  refine ⟨Vaff, hsV, ?_⟩
  dsimp only
  let t : Vaff.1.toScheme ⟶ S := Vaff.1.ι
  let g : pullback π t ⟶ C := pullback.fst π t
  let zV : Vaff.1.toScheme ⟶ pullback π t := sectionBaseChange z hz t
  let UV : (pullback π t).Opens := g ⁻¹ᵁ U.1
  letI : IsAffine Vaff.1.toScheme := Vaff.2
  have hUVaff : IsAffineOpen UV := by
    dsimp only [UV, g]
    exact IsAffineOpen.preimage_pullback_fst π t U.2
  let UVaff : (pullback π t).affineOpens := ⟨UV, hUVaff⟩
  have hzUV : zV ⁻¹ᵁ UV = ⊤ := by
    rw [← Scheme.Hom.comp_preimage]
    rw [show zV ≫ g = t ≫ z by
      dsimp only [zV, g]
      exact sectionBaseChange_fst z hz t]
    rw [Scheme.Hom.comp_preimage]
    ext x
    change z x.1 ∈ U.1 ↔ x ∈ (⊤ : Vaff.1.toScheme.Opens)
    simp only [Opens.mem_top, iff_true]
    exact hVU x.2
  let rV : Γ(pullback π t, UVaff.1) :=
    affinePullbackSection g UVaff U le_rfl r
  have hspanV : zV.ker.ideal UVaff = Ideal.span {rV} := by
    have hker : zV.ker = z.ker.comap g := by
      dsimp only [zV, g]
      exact RelEffCartierDiv.ker_sectionBaseChange z hz t
    rw [hker]
    exact ideal_comap_affineOpens_span z.ker g UVaff U le_rfl r hspan
  have hnzdV : rV ∈ nonZeroDivisors Γ(pullback π t, UVaff.1) := by
    dsimp only [rV]
    exact affinePullbackSection_mem_nonZeroDivisors g UVaff U le_rfl hnzd
  exact ⟨UVaff, hzUV, rV, hspanV, hnzdV⟩

end ModularCurves
