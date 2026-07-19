import Mathlib.Algebra.Module.Projective
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

/-- Global base sections are exact at two consecutive pole modules. -/
theorem sectionPoleSheafPower_baseSectionsSucc_exact
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    Function.Exact
      (Scheme.Modules.baseSectionsMap π
        (sectionPoleSheafSuccHom π z hz n)).hom
      (Scheme.Modules.baseSectionsMap π
        (cokernel.π (sectionPoleSheafSuccHom π z hz n))).hom := by
  letI : Mono (sectionPoleSheafSuccHom π z hz n) :=
    sectionPoleSheafSuccHom_mono hsm z hz n
  exact Scheme.Modules.baseSectionsMap_exact_cokernel π
    (sectionPoleSheafSuccHom π z hz n)

/-- If the lower pole module has vanishing first cohomology, then its successor
surjects onto the successive quotient on global base sections. -/
theorem sectionPoleSheafSuccCoker_baseSectionsMap_surjective_of_subsingleton_H_one
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ)
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz n).sheaf 1)) :
    Function.Surjective (Scheme.Modules.baseSectionsMap π
      (cokernel.π (sectionPoleSheafSuccHom π z hz n))) := by
  letI : Mono (sectionPoleSheafSuccHom π z hz n) :=
    sectionPoleSheafSuccHom_mono hsm z hz n
  letI : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz n).sheaf 1) := hH
  exact Scheme.Modules.baseSectionsMap_cokernel_surjective_of_subsingleton_H_one
    π (sectionPoleSheafSuccHom π z hz n)

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

/-- If the lower pole sheaf has vanishing first cohomology, the generator of a
successive rank-one quotient lifts to a section of the next pole sheaf. -/
theorem exists_sectionPoleSheafPower_succ_baseSection_generator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz n).sheaf 1)) :
    ∃ x : Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz (n + 1)),
      (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
        hsm z hz U hU r hspan hnzd n).hom
        (Scheme.Modules.baseSectionsMap π
          (cokernel.π (sectionPoleSheafSuccHom π z hz n)) x) = 1 := by
  obtain ⟨x, hx⟩ :=
    sectionPoleSheafSuccCoker_baseSectionsMap_surjective_of_subsingleton_H_one
      hsm z hz n hH
      ((sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
        hsm z hz U hU r hspan hnzd n).inv 1)
  refine ⟨x, ?_⟩
  rw [hx, Iso.inv_hom_id_apply]

private noncomputable def
    sectionPoleSheafPower_succ_baseSectionsSplitDataOfCartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz n).sheaf 1)) :
    let R := Γ(S, (⊤ : S.Opens))
    let P := Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n)
    let Q := Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1))
    let f := (Scheme.Modules.baseSectionsMap π
      (sectionPoleSheafSuccHom π z hz n)).hom
    let e := (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
      hsm z hz U hU r hspan hnzd n).toLinearEquiv
    let g := e.toLinearMap ∘ₗ (Scheme.Modules.baseSectionsMap π
      (cokernel.π (sectionPoleSheafSuccHom π z hz n))).hom
    { d : Q ≃ₗ[R] P × R //
      f = d.symm.toLinearMap ∘ₗ LinearMap.inl R P R ∧
        g = LinearMap.snd R P R ∘ₗ d.toLinearMap } := by
  dsimp only
  let f := (Scheme.Modules.baseSectionsMap π
    (sectionPoleSheafSuccHom π z hz n)).hom
  let g₀ := (Scheme.Modules.baseSectionsMap π
    (cokernel.π (sectionPoleSheafSuccHom π z hz n))).hom
  let e := (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
    hsm z hz U hU r hspan hnzd n).toLinearEquiv
  let g := e.toLinearMap ∘ₗ g₀
  have hsurj₀ : Function.Surjective g₀ :=
    sectionPoleSheafSuccCoker_baseSectionsMap_surjective_of_subsingleton_H_one
      hsm z hz n hH
  have hsurj : Function.Surjective g := e.surjective.comp hsurj₀
  have hexact₀ : Function.Exact f g₀ :=
    sectionPoleSheafPower_baseSectionsSucc_exact hsm z hz n
  have hexact : Function.Exact f g :=
    (LinearEquiv.postcomp_exact_iff_exact (f := f) (g := g₀) (e := e)).mpr hexact₀
  have hf : Function.Injective f := by
    apply (ModuleCat.mono_iff_injective
      (Scheme.Modules.baseSectionsMap π
        (sectionPoleSheafSuccHom π z hz n))).mp
    exact Scheme.Modules.baseSectionsMap_mono π
      (sectionPoleSheafSuccHom π z hz n)
      (sectionPoleSheafSuccHom_mono hsm z hz n)
  let hsplitting := g.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let l := Classical.choose hsplitting
  have hl := Classical.choose_spec hsplitting
  exact hexact.splitSurjectiveEquiv hf ⟨l, hl⟩

/-- If the lower pole sheaf has vanishing first cohomology, the next pole
module splits as the lower pole module and its rank-one successive quotient. -/
noncomputable def sectionPoleSheafPower_succ_baseSectionsSplitEquivOfCartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz n).sheaf 1)) :
    Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz (n + 1)) ≃ₗ[Γ(S, (⊤ : S.Opens))]
      Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n) ×
        Γ(S, (⊤ : S.Opens)) :=
  (sectionPoleSheafPower_succ_baseSectionsSplitDataOfCartierGenerator
    hsm z hz U hU r hspan hnzd n hH).1

/-- The old pole module is the first summand in the successor splitting. -/
@[simp]
theorem sectionPoleSheafPower_succ_baseSectionsSplitEquiv_symm_apply_inl
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz n).sheaf 1))
    (x : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n)) :
    (sectionPoleSheafPower_succ_baseSectionsSplitEquivOfCartierGenerator
      hsm z hz U hU r hspan hnzd n hH).symm (x, 0) =
      Scheme.Modules.baseSectionsMap π
        (sectionPoleSheafSuccHom π z hz n) x := by
  let d := sectionPoleSheafPower_succ_baseSectionsSplitDataOfCartierGenerator
    hsm z hz U hU r hspan hnzd n hH
  have hd := LinearMap.congr_fun d.2.1 x
  change d.1.symm (x, 0) =
    Scheme.Modules.baseSectionsMap π
      (sectionPoleSheafSuccHom π z hz n) x
  rw [LinearMap.comp_apply, LinearMap.inl_apply] at hd
  exact hd.symm

/-- The second coordinate in the successor splitting is the canonical
successive-quotient coordinate. -/
@[simp]
theorem sectionPoleSheafPower_succ_baseSectionsSplitEquiv_apply_snd
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz n).sheaf 1))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1))) :
    (sectionPoleSheafPower_succ_baseSectionsSplitEquivOfCartierGenerator
      hsm z hz U hU r hspan hnzd n hH x).2 =
      (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
        hsm z hz U hU r hspan hnzd n).hom
        (Scheme.Modules.baseSectionsMap π
          (cokernel.π (sectionPoleSheafSuccHom π z hz n)) x) := by
  let d := sectionPoleSheafPower_succ_baseSectionsSplitDataOfCartierGenerator
    hsm z hz U hU r hspan hnzd n hH
  have hd := LinearMap.congr_fun d.2.2 x
  change (d.1 x).2 =
    (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
      hsm z hz U hU r hspan hnzd n).hom
      (Scheme.Modules.baseSectionsMap π
        (cokernel.π (sectionPoleSheafSuccHom π z hz n)) x)
  rw [LinearMap.comp_apply, LinearMap.snd_apply] at hd
  change
    (sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator
      hsm z hz U hU r hspan hnzd n).hom
      (Scheme.Modules.baseSectionsMap π
        (cokernel.π (sectionPoleSheafSuccHom π z hz n)) x) =
      (d.1 x).2 at hd
  exact hd.symm

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
