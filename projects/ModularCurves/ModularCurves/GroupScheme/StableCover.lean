/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.StableCharts

/-!
# The `G`-stable affine cover of `E` — complement stability (`[HG-C3b]`)

First brick of `[HG-C3]` (`.mathlib-quality/decomposition-hopf-c3-cover.md`): the complement
`E ∖ G` of the subgroup scheme is **stable** under the translation action, directly from the
preimage predicate `IsStableOpen`. The content is the subgroup property in point form: for a
point `(t, y)` of `G ×_S E` whose translate `y + ι t` lands in `G`, the point `y` itself lies
in `G` — because `y = (y + ι t) - ι t` is a difference of two members of `pointSubgroup`, and
`pointSubgroup` is closed under subtraction. Topologically the difference identity is realised
over the fibre product `W = (G ×_S E) ×_{act, E, ι} G`, whose points surject onto the
compatible pairs (`Scheme.Pullback.exists_preimage_pullback`).

The complement chart `complOpen` is the first of the two charts of the `[HG-C3e]` cover; its
affineness is `[HG-C3c]` (the Proj basic-open route).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

namespace FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : FiniteLocallyFreeSubgroup E)

/-- The (closed) support of the subgroup scheme inside `E`: the image of `ι`. -/
theorem isClosed_range_ι : IsClosed (Set.range G.ι.base) :=
  G.closedImmersion.base_closed.isClosed_range

/-- The open complement `E ∖ G` of the subgroup scheme — the first chart of the `[HG-C3]`
cover. -/
noncomputable def complOpen : E.E.Opens :=
  ⟨(Set.range G.ι.base)ᶜ, G.isClosed_range_ι.isOpen_compl⟩

@[simp]
theorem mem_complOpen {e : E.E} : e ∈ G.complOpen ↔ e ∉ Set.range G.ι.base :=
  Iff.rfl

/-- **`[HG-C3b]` — stability of the complement.** The complement `E ∖ G` is stable under the
translation action of `G`: if a point of `G ×_S E` projects into the complement, its translate
stays in the complement. Contrapositive + `pointSubgroup` subtraction: if `y + ι t ∈ G` then
`y = (y + ι t) - ι t ∈ G`. -/
theorem isStableOpen_complOpen : G.IsStableOpen G.complOpen := by
  intro p hp
  -- `hp : actionProj p ∈ E ∖ G`; goal (after unfolding): `translationAction p ∈ E ∖ G`.
  have hp' : G.actionProj.left.base p ∉ Set.range G.ι.base := hp
  show G.translationAction.left.base p ∈ (Set.range G.ι.base)ᶜ
  intro hμ
  apply hp'
  obtain ⟨z₀, hz₀⟩ := hμ
  -- the fibre product `W = (G ×_S E) ×_{act, E, ι} G` and a point over `(p, z₀)`
  obtain ⟨w₀, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := G.translationAction.left) (g := G.ι) p z₀ hz₀.symm
  set c₁ := pullback.fst G.translationAction.left G.ι with hc₁
  set c₂ := pullback.snd G.translationAction.left G.ι with hc₂
  -- the structure map of `W` over `S`, through the ambient `G ×_S E`
  set w : pullback G.translationAction.left G.ι ⟶ S :=
    c₁ ≫ ((Over.mk G.π) ⊗ E.asOver).hom with hwdef
  letI : CommGroup (Over.mk w ⟶ E.asOver) := Hom.commGroup
  -- `c₁` as a morphism over `S`
  let c₁O : Over.mk w ⟶ (Over.mk G.π) ⊗ E.asOver := Over.homMk c₁ rfl
  -- the base compatibility of the `G`-side leg
  have hZw : (c₂ ≫ G.ι) ≫ E.π = w :=
    (congrArg (· ≫ E.π) pullback.condition).symm.trans <|
      (Category.assoc _ _ _).trans <|
        congrArg (c₁ ≫ ·) (G.translationAction_left_π)
  -- the three points of `E` over `w`: the projection, the translating `G`-point, the sum
  set Ypt : E.Point w :=
    (E.pointEquivOverHom w).symm (c₁O ≫ snd (Over.mk G.π) E.asOver) with hYdef
  set Tpt : E.Point w :=
    (E.pointEquivOverHom w).symm (c₁O ≫ (fst (Over.mk G.π) E.asOver ≫ G.ιOver)) with hTdef
  set Zpt : E.Point w :=
    (E.pointEquivOverHom w).symm (Over.homMk (c₂ ≫ G.ι) hZw) with hZdef
  have eY : (E.pointEquivOverHom w) Ypt = c₁O ≫ snd (Over.mk G.π) E.asOver :=
    (E.pointEquivOverHom w).apply_symm_apply _
  have eT : (E.pointEquivOverHom w) Tpt = c₁O ≫ (fst (Over.mk G.π) E.asOver ≫ G.ιOver) :=
    (E.pointEquivOverHom w).apply_symm_apply _
  have eZ : (E.pointEquivOverHom w) Zpt = Over.homMk (c₂ ≫ G.ι) hZw :=
    (E.pointEquivOverHom w).apply_symm_apply _
  -- the translation identity: `Ypt + Tpt = Zpt` (`act = pr_E + ι ∘ pr_G` over `W`)
  have hadd : (E.pointEquivOverHom w) (Ypt + Tpt) = c₁O ≫ G.translationAction := by
    have h3 := congrArg (c₁O ≫ ·) G.translationAction_eq_mul
    rw [MonObj.comp_mul] at h3
    rw [E.pointEquivOverHom_add, eY, eT, h3]
    exact mul_comm _ _
  have hZeq : Ypt + Tpt = Zpt := by
    apply (E.pointEquivOverHom w).injective
    rw [hadd, eZ]
    refine Over.OverMorphism.ext ?_
    show c₁ ≫ G.translationAction.left = c₂ ≫ G.ι
    exact pullback.condition
  -- both `Tpt` and `Zpt` lie in the point subgroup; hence so does `Ypt = Zpt - Tpt`
  have hT : Tpt ∈ G.pointSubgroup w :=
    ⟨c₁ ≫ (fst (Over.mk G.π) E.asOver).left,
      (Category.assoc _ _ _).trans (congrArg CommaMorphism.left eT).symm⟩
  have hZ : Zpt ∈ G.pointSubgroup w :=
    ⟨c₂, (congrArg CommaMorphism.left eZ).symm⟩
  have hYmem : Ypt ∈ G.pointSubgroup w := by
    have hsub : Ypt = Zpt - Tpt := eq_sub_of_add_eq hZeq
    rw [hsub]
    exact sub_mem hZ hT
  -- extract the factorization and evaluate at the point `w₀` over `(p, z₀)`
  obtain ⟨h, hh⟩ := hYmem
  have hY1 : Ypt.1 = c₁ ≫ G.actionProj.left := congrArg CommaMorphism.left eY
  refine ⟨h.base w₀, ?_⟩
  have hev : (h ≫ G.ι).base w₀ = (c₁ ≫ G.actionProj.left).base w₀ :=
    congrArg (fun m : pullback G.translationAction.left G.ι ⟶ E.E => m.base w₀)
      (hh.trans hY1)
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw₁] at hev
  exact hev

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
