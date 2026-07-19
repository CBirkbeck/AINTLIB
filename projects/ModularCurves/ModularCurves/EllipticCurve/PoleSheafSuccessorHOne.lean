import ModularCurves.EllipticCurve.PoleSheafQuasicoherent
import ModularCurves.ForMathlib.AcyclicAffineOpenCover
import ModularCurves.ForMathlib.AffinePatchBaseChange
import ModularCurves.ForMathlib.SheafCohomologyExact
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
    haveI hoverlap : Subsingleton ↑Γ(M, U.1 ⊓ V) := by
      exact Scheme.Modules.subsingleton_sections_of_isZero_restrict
        M (U.1 ⊓ V) hzero
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

/-- Vanishing of first cohomology propagates across one pole-filtration step
when the successive quotient also has vanishing first cohomology. -/
theorem sectionPoleSheafPower_succ_subsingleton_H_one
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ)
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz n).sheaf 1))
    (hQ : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafSuccCoker π z hz n).sheaf 1)) :
    Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz (n + 1)).sheaf 1) := by
  letI : Mono (sectionPoleSheafSuccHom π z hz n) :=
    sectionPoleSheafSuccHom_mono hsm z hz n
  let T := ShortComplex.mk (sectionPoleSheafSuccHom π z hz n)
    (cokernel.π (sectionPoleSheafSuccHom π z hz n))
    (cokernel.condition (sectionPoleSheafSuccHom π z hz n))
  have hT : T.ShortExact :=
    ShortComplex.ShortExact.mk
      (ShortComplex.exact_cokernel (sectionPoleSheafSuccHom π z hz n))
  let Ts := T.map (Scheme.Modules.toSheaf C)
  have hTs : Ts.ShortExact :=
    ShortComplex.ShortExact.map_of_exact hT (Scheme.Modules.toSheaf C)
  apply CategoryTheory.Sheaf.H.subsingleton_H_X₂_of_shortExact (hS := hTs) 1
  · exact hH
  · exact hQ

/-- On an affine neighborhood containing the section, vanishing of first
cohomology propagates from one pole sheaf to its successor. -/
theorem sectionPoleSheafPower_succ_subsingleton_H_one_of_affine_neighborhood
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤) (n : ℕ)
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz n).sheaf 1)) :
    Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz (n + 1)).sheaf 1) :=
  sectionPoleSheafPower_succ_subsingleton_H_one hsm z hz n hH
    (sectionPoleSheafSuccCoker_subsingleton_H_one_of_affine_neighborhood
      hsm z hz n U hU)

/-- On an affine neighborhood containing the section, vanishing of
`H¹(O([0]))` implies vanishing of `H¹(O(n[0]))` for every positive `n`. -/
theorem sectionPoleSheafPower_subsingleton_H_one_of_one_of_affine_neighborhood
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (hHOne : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    {n : ℕ} (hn : 1 ≤ n) :
    Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz n).sheaf 1) := by
  induction n, hn using Nat.le_induction with
  | base => exact hHOne
  | succ n hn ih =>
      exact sectionPoleSheafPower_succ_subsingleton_H_one_of_affine_neighborhood
        hsm z hz U hU n ih

/-- Around every point of an affine base, successive pole quotients have vanishing
first cohomology after restricting the family to a suitable affine neighborhood. -/
theorem exists_affineBaseChange_sectionPoleSheafSuccCoker_subsingleton_H_one
    {C S : Scheme.{u}} {π : C ⟶ S} [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (s : S) (n : ℕ) :
    ∃ V : S.affineOpens, s ∈ V.1 ∧
      let t : V.1.toScheme ⟶ S := V.1.ι
      let πV := pullback.snd π t
      let zV := sectionBaseChange z hz t
      Subsingleton (CategoryTheory.Sheaf.H
        (sectionPoleSheafSuccCoker πV zV (sectionBaseChange_snd z hz t) n).sheaf 1) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzsU, -⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (z s)) isOpen_univ
  let Uaff : C.affineOpens := ⟨U, hU⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, hVU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      hzsU ((z ⁻¹ᵁ Uaff.1).2)
  let Vaff : S.affineOpens := ⟨V, hV⟩
  refine ⟨Vaff, hsV, ?_⟩
  dsimp only
  let t : Vaff.1.toScheme ⟶ S := Vaff.1.ι
  let πV := pullback.snd π t
  let zV := sectionBaseChange z hz t
  let UV : (pullback π t).Opens := pullback.fst π t ⁻¹ᵁ Uaff.1
  letI : IsAffine Vaff.1.toScheme := Vaff.2
  have hUVaff : IsAffineOpen UV := by
    dsimp only [UV]
    exact IsAffineOpen.preimage_pullback_fst π t Uaff.2
  let UVaff : (pullback π t).affineOpens := ⟨UV, hUVaff⟩
  have hzUV : zV ⁻¹ᵁ UV = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, sectionBaseChange_fst,
      Scheme.Hom.comp_preimage]
    ext x
    change z x.1 ∈ Uaff.1 ↔ x ∈ (⊤ : Vaff.1.toScheme.Opens)
    simp only [Opens.mem_top, iff_true]
    exact hVU x.2
  have hsmV : SmoothOfRelativeDimension 1 πV := by
    exact
      (AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback π t) hsm
  exact sectionPoleSheafSuccCoker_subsingleton_H_one_of_affine_neighborhood
    hsmV zV (sectionBaseChange_snd z hz t) n UVaff hzUV

end ModularCurves
