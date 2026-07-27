import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapSectionAwayIso

/-!
# Global finiteness of the pole-sheaf Weierstrass comparison

A structurally compatible comparison is finite once it is an isomorphism on
the exact complement of the marked section.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace ModularCurves

noncomputable section

/-- A structurally compatible comparison is injective when it is an
isomorphism on the exact complement of the marked section. -/
theorem projModelMap_injective_of_sectionAway_isIso
    {C S : Scheme.{u}} {π : C ⟶ S} [IsAffine S] [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (F : C ⟶ projModel W)
    (hF : F ≫ projModelπ W = π ≫ S.toSpecΓ)
    (hpre : F ⁻¹ᵁ (projModelZChart W : (projModel W).Opens) =
      sectionAway z hz)
    [IsIso
      (F.resLE (projModelZChart W : (projModel W).Opens)
        (sectionAway z hz) (le_of_eq hpre.symm))] :
    Function.Injective F := by
  let V := sectionAway z hz
  let Z : (projModel W).Opens := projModelZChart W
  let G := F.resLE Z V (le_of_eq hpre.symm)
  haveI : IsIso S.toSpecΓ := IsAffine.affine
  have hπ_of_eq {x y : C} (hxy : F x = F y) : π x = π y := by
    apply S.toSpecΓ.homeomorph.injective
    calc
      S.toSpecΓ (π x) = projModelπ W (F x) := by
        simpa only [Scheme.Hom.comp_apply] using
          congrArg (fun q : C ⟶ Spec Γ(S, (⊤ : S.Opens)) ↦ q x) hF.symm
      _ = projModelπ W (F y) := congrArg _ hxy
      _ = S.toSpecΓ (π y) := by
        simpa only [Scheme.Hom.comp_apply] using
          congrArg (fun q : C ⟶ Spec Γ(S, (⊤ : S.Opens)) ↦ q y) hF
  intro x y hxy
  by_cases hx : x ∈ V
  · have hxpre : x ∈ F ⁻¹ᵁ Z := by
      rwa [hpre]
    have hyZ : F y ∈ Z := by
      rw [← hxy]
      exact hxpre
    have hy : y ∈ V := by
      change y ∈ sectionAway z hz
      rw [← hpre]
      exact hyZ
    have hGxy : G ⟨x, hx⟩ = G ⟨y, hy⟩ := by
      apply Subtype.ext
      dsimp only [G]
      rw [Scheme.Hom.coe_resLE_apply, Scheme.Hom.coe_resLE_apply]
      exact hxy
    exact congrArg Subtype.val
      (G.homeomorph.injective hGxy)
  · have hy : y ∉ V := by
      intro hy
      have hypre : y ∈ F ⁻¹ᵁ Z := by
        rwa [hpre]
      have hxZ : F x ∈ Z := by
        rw [hxy]
        exact hypre
      apply hx
      change x ∈ sectionAway z hz
      rw [← hpre]
      exact hxZ
    have hxrange : x ∈ Set.range z := by
      change x ∉ sectionAway z hz at hx
      change x ∉ (Set.range z)ᶜ at hx
      simpa only [Set.mem_compl_iff, not_not] using hx
    have hyrange : y ∈ Set.range z := by
      change y ∉ sectionAway z hz at hy
      change y ∉ (Set.range z)ᶜ at hy
      simpa only [Set.mem_compl_iff, not_not] using hy
    obtain ⟨s, rfl⟩ := hxrange
    obtain ⟨t, rfl⟩ := hyrange
    have hst : s = t := by
      calc
        s = π (z s) := by
          have hs := congrArg (fun q : S ⟶ S ↦ q s) hz.symm
          change s = π (z s) at hs
          exact hs
        _ = π (z t) := hπ_of_eq hxy
        _ = t := by
          have ht := congrArg (fun q : S ⟶ S ↦ q t) hz
          change π (z t) = t at ht
          exact ht
    rw [hst]

/-- A proper structurally compatible comparison is finite when it is an
isomorphism on the exact complement of the marked section. -/
theorem projModelMap_isFinite_of_sectionAway_isIso
    {C S : Scheme.{u}} {π : C ⟶ S} [IsAffine S] [IsProper π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (F : C ⟶ projModel W)
    (hF : F ≫ projModelπ W = π ≫ S.toSpecΓ)
    (hpre : F ⁻¹ᵁ (projModelZChart W : (projModel W).Opens) =
      sectionAway z hz)
    [IsIso
      (F.resLE (projModelZChart W : (projModel W).Opens)
        (sectionAway z hz) (le_of_eq hpre.symm))] :
    IsFinite F := by
  have hFinj : Function.Injective F :=
    projModelMap_injective_of_sectionAway_isIso
      z hz W F hF hpre
  haveI : IsProper F := projModelMap_isProper_of_isAffine W F hF
  haveI : LocallyQuasiFinite F := LocallyQuasiFinite.of_injective hFinj
  exact IsFinite.of_isProper_of_locallyQuasiFinite F

end

end ModularCurves
