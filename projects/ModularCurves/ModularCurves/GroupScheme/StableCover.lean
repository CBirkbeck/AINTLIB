/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.StableCharts
import ModularCurves.EllipticCurve.WeierstrassModel
import ModularCurves.ForMathlib.BaseChangeAlongCompat

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

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

namespace EllipticCurve

namespace FiniteLocallyFreeSubgroup

variable {S : Scheme.{u}} {E : EllipticCurve S} (G : FiniteLocallyFreeSubgroup E)

/-- The (closed) support of the subgroup scheme inside `E`: the image of `ι`. -/
theorem isClosed_range_ι : IsClosed (Set.range G.ι.base) :=
  G.closedImmersion.isClosedEmbedding.isClosed_range

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

/-! ### `[n]`-preimage charts: stable and affine for free

For `G` killed by `n` (morphism form: `ι ≫ [n] = π_G ≫ zero`), multiplication by `n` is
invariant under translation by `G` — `[n] ∘ act = [n] ∘ pr` — so the `[n]`-preimage of **any**
open is `G`-stable; and `[n]` is finite, hence affine, so the `[n]`-preimage of any affine
open is affine. Preimages of a cover form a cover. This kills the `[HG-C3c]` "divisor ↔
homogeneous-section bridge": the two Weierstrass basic-open charts `D₊(Y), D₊(Z)` of `E`
pull back to a two-element `G`-stable affine cover directly. -/

section MulPreimage

/-- **The killing identity in action form.** If `G` is killed by `n` (`ι ≫ [n]` is the zero
section over `G`), then `[n]` coequalizes the translation action and the projection:
`act ≫ [n] = pr ≫ [n]`. Hom-group computation: `(x + ι t)^n = x^n · (ι t)^n = x^n`. -/
theorem translationAction_comp_mulByHom (n : ℤ)
    (hkill : G.ι ≫ E.mulByHom n = G.π ≫ E.zero) :
    G.translationAction.left ≫ E.mulByHom n = G.actionProj.left ≫ E.mulByHom n := by
  letI : CommGroup ((Over.mk G.π) ⊗ E.asOver ⟶ E.asOver) := Hom.commGroup
  letI : CommGroup (Over.mk G.π ⟶ E.asOver) := Hom.commGroup
  -- composition with `mulBy n` is the `n`-th power in the hom-group
  have hpow : ∀ f : (Over.mk G.π) ⊗ E.asOver ⟶ E.asOver, f ≫ E.mulBy n = f ^ n := by
    intro f
    show f ≫ (𝟙 E.asOver) ^ n = f ^ n
    rw [GrpObj.comp_zpow, Category.comp_id]
  have hpowι : G.ιOver ≫ E.mulBy n = G.ιOver ^ n := by
    show G.ιOver ≫ (𝟙 E.asOver) ^ n = G.ιOver ^ n
    rw [GrpObj.comp_zpow, Category.comp_id]
  -- the killing hypothesis says `ιOver ^ n` is the unit of the hom-group
  have hunit : G.ιOver ^ n = (1 : Over.mk G.π ⟶ E.asOver) := by
    rw [← hpowι]
    refine Over.OverMorphism.ext ?_
    show G.ι ≫ E.mulByHom n = (toUnit (Over.mk G.π) ≫ η[E.asOver]).left
    rw [hkill, Over.comp_left, E.one_eq_zero]
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ E.zero) (Over.w (toUnit (Over.mk G.π))))).symm
  -- expand the action as a product and kill the `G`-factor
  have hover : G.translationAction ≫ E.mulBy n = G.actionProj ≫ E.mulBy n := by
    rw [hpow, hpow, G.translationAction_eq_mul, mul_zpow, ← GrpObj.comp_zpow, hunit]
    show (fst (Over.mk G.π) E.asOver ≫ (1 : Over.mk G.π ⟶ E.asOver))
        * (snd (Over.mk G.π) E.asOver) ^ n = _
    rw [MonObj.comp_one, _root_.one_mul]
    rfl
  have h2 : G.translationAction.left ≫ (E.mulBy n).left
      = G.actionProj.left ≫ (E.mulBy n).left := by
    simpa only [Over.comp_left] using congrArg CommaMorphism.left hover
  exact h2

/-- **`[HG-C3` stable charts for free`]`** For `G` killed by `n`, the `[n]`-preimage of *any*
open of `E` is `G`-stable: the two preimage-opens in the stability predicate agree, since
`act ≫ [n] = pr ≫ [n]`. -/
theorem isStableOpen_mulByHom_preimage (n : ℤ)
    (hkill : G.ι ≫ E.mulByHom n = G.π ≫ E.zero) (U : E.E.Opens) :
    G.IsStableOpen (E.mulByHom n ⁻¹ᵁ U) := by
  intro p hp
  have hp' : (G.actionProj.left ≫ E.mulByHom n).base p ∈ U := by
    rw [Scheme.Hom.comp_apply]; exact hp
  have h2 : (G.translationAction.left ≫ E.mulByHom n).base p ∈ U := by
    rw [G.translationAction_comp_mulByHom n hkill]; exact hp'
  show (E.mulByHom n).base (G.translationAction.left.base p) ∈ U
  rwa [Scheme.Hom.comp_apply] at h2

/-- The `[N]`-preimage of an affine open is affine (`[N]` is finite, hence affine). -/
theorem isAffineOpen_mulByHom_preimage (N : ℕ) [NeZero N] {U : E.E.Opens}
    (hU : IsAffineOpen U) : IsAffineOpen (E.mulByHom N ⁻¹ᵁ U) := by
  haveI := E.mulByHom_isFinite N
  exact hU.preimage (E.mulByHom N)

/-- Preimages of a cover cover. -/
theorem iSup_mulByHom_preimage_eq_top {κ : Type*} (n : ℤ) (U : κ → E.E.Opens)
    (hU : iSup U = ⊤) : (⨆ i, E.mulByHom n ⁻¹ᵁ U i) = ⊤ := by
  apply TopologicalSpace.Opens.ext
  apply Set.eq_univ_of_univ_subset
  intro p _
  have hmem : (E.mulByHom n).base p ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hpV⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hpV⟩

/-- **The killing identity from the rank (KM 1.4.2, via BB-DELIGNE).** A subgroup scheme of
constant rank `N` is killed by `N`, in the morphism form the charts consume: apply the
point-level Deligne bound to the tautological point `ι` of `E` over `G.π`. -/
theorem ι_comp_mulByHom_of_hasRank {N : ℕ} [NeZero N] (hG : G.HasRank N) :
    G.ι ≫ E.mulByHom N = G.π ≫ E.zero := by
  have hP : (⟨G.ι, G.ι_π⟩ : E.Point G.π) ∈ G.pointSubgroup G.π :=
    ⟨𝟙 G.G, Category.id_comp _⟩
  have h0 := hG.smul_eq_zero_of_factors G.π ⟨G.ι, G.ι_π⟩ hP
  exact (E.smul_eq_zero_iff_comp_mulByHom G.π N ⟨G.ι, G.ι_π⟩).mp h0

/-- **A constant-rank subgroup carries a killing integer** (KM 1.4.2): `HasRank N ⟹ HasKillingInt`,
with `N` itself the killing integer. The bridge from the rank datum (a `Prop` hypothesis threaded
by the moduli layer) to the `HasKillingInt` class that the option-γ quotient `E/G` consumes; a
consumer with `hrank : G.HasRank N` supplies the instance via `haveI := G.hasKillingInt_of_hasRank hrank`. -/
theorem hasKillingInt_of_hasRank {N : ℕ} [NeZero N] (hG : G.HasRank N) : G.HasKillingInt :=
  ⟨N, NeZero.ne N, G.ι_comp_mulByHom_of_hasRank hG⟩

end MulPreimage

/-! ### Stability closure micro-lemmas -/

section StabilityClosure

/-- π-preimages are stable: the action is a morphism over `S`. -/
theorem isStableOpen_π_preimage (V : S.Opens) : G.IsStableOpen (E.π ⁻¹ᵁ V) := by
  intro p hp
  have hp' : (G.actionProj.left ≫ E.π).base p ∈ V := by
    rw [Scheme.Hom.comp_apply]; exact hp
  rw [G.actionProj_left_π, ← G.translationAction_left_π] at hp'
  show E.π.base (G.translationAction.left.base p) ∈ V
  rwa [Scheme.Hom.comp_apply] at hp'

/-- Stable opens are closed under intersection. -/
theorem IsStableOpen.inf {U U' : E.E.Opens} (hU : G.IsStableOpen U)
    (hU' : G.IsStableOpen U') : G.IsStableOpen (U ⊓ U') := by
  intro p hp
  have h1 : p ∈ G.actionProj.left ⁻¹ᵁ U := hp.1
  have h2 : p ∈ G.actionProj.left ⁻¹ᵁ U' := hp.2
  exact ⟨hU h1, hU' h2⟩

end StabilityClosure

/-! ### The chart existence: every point of `E` lies in a `G`-stable affine open over an
affine base patch

Instantiation of the `[n]`-preimage engine on the Weierstrass atlas (`E.localModel`): near
any `x ∈ E`, pick the atlas patch `V ∋ π x` with `E|_V ≅ projModel W`, take the Proj
basic-open chart `D₊(Xᵢ)` containing the image of `[N] x` (three-chart cover), transport it
to an affine open of `E` through the atlas iso and the open immersion `E|_V ↪ E`, and pull
back along `[N]`. -/

section ChartExistence

/-- **Chart transport, abstract model form.** Given an affine base patch `V`, an iso `e` of
`E|_V` with an *abstract* scheme `P` (kept opaque so instance search never unfolds the
Weierstrass `Proj`), and an affine open `A ⊆ P` containing the image of a preimage `y'` of
`[N] x`, transporting `A` back to `E` and pulling back along `[N]` yields a `G`-stable
affine open around `x` over `V`. -/
theorem exists_mem_stableAffineOpen_aux (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) (x : E.E) (V : S.affineOpens)
    {P : Scheme.{u}} (e : pullback E.π V.1.ι ≅ P) {A : P.Opens} (hAaff : IsAffineOpen A)
    {y' : ↥(pullback E.π V.1.ι)}
    (hy' : (pullback.fst E.π V.1.ι).base y' = (E.mulByHom N).base x)
    (hzi : e.hom.base y' ∈ A) :
    ∃ (V' : S.affineOpens) (Uc : E.E.Opens),
      x ∈ Uc ∧ IsAffineOpen Uc ∧ G.IsStableOpen Uc ∧ Uc ≤ E.π ⁻¹ᵁ V'.1 := by
  set B : (pullback E.π V.1.ι).Opens := e.inv ''ᵁ A with hB
  have hBaff : IsAffineOpen B := hAaff.image_of_isOpenImmersion e.inv
  have hyB : y' ∈ B := by
    refine ⟨e.hom.base y', hzi, ?_⟩
    have hbase := congrArg (fun m : pullback E.π V.1.ι ⟶ pullback E.π V.1.ι => m.base y')
      e.hom_inv_id
    simpa [Scheme.Hom.comp_apply] using hbase
  set C : E.E.Opens := (pullback.fst E.π V.1.ι) ''ᵁ B with hC
  have hCaff : IsAffineOpen C := hBaff.image_of_isOpenImmersion _
  -- the transported chart lies over the base patch
  have hCle : C ≤ E.π ⁻¹ᵁ V.1 := by
    rintro c ⟨q, -, rfl⟩
    have hcond := congrArg (fun m : pullback E.π V.1.ι ⟶ S => m.base q)
      (pullback.condition (f := E.π) (g := V.1.ι))
    have h2 : E.π.base ((pullback.fst E.π V.1.ι).base q)
        = V.1.ι.base ((pullback.snd E.π V.1.ι).base q) := by
      simpa [Scheme.Hom.comp_apply] using hcond
    show E.π.base ((pullback.fst E.π V.1.ι).base q) ∈ V.1
    rw [h2]
    have := ((pullback.snd E.π V.1.ι).base q).2
    simpa using this
  refine ⟨V, E.mulByHom N ⁻¹ᵁ C, ?_, ?_, ?_, ?_⟩
  · show (E.mulByHom N).base x ∈ C
    exact ⟨y', hyB, hy'⟩
  · exact isAffineOpen_mulByHom_preimage N hCaff
  · exact G.isStableOpen_mulByHom_preimage N hkill C
  · intro p hp
    have hpV : E.π.base ((E.mulByHom N).base p) ∈ V.1 := hCle hp
    show E.π.base p ∈ V.1
    have hππp : E.π.base ((E.mulByHom N).base p) = E.π.base p := by
      rw [← Scheme.Hom.comp_apply, E.mulByHom_π]
    rwa [hππp] at hpV

/-- **[HG-C3 chart existence]** For `G` killed by `N`, every point of `E` lies in a
`G`-stable affine open lying over an affine open of the base. This is the geometric heart
of the `[HG-C3]` cover; the freeness refinement (shrinking the base patch until `groupRing`
is free) is `[HG-C3d]`. -/
theorem exists_mem_stableAffineOpen (N : ℕ) [NeZero N]
    (hkill : G.ι ≫ E.mulByHom N = G.π ≫ E.zero) (x : E.E) :
    ∃ (V : S.affineOpens) (Uc : E.E.Opens),
      x ∈ Uc ∧ IsAffineOpen Uc ∧ G.IsStableOpen Uc ∧ Uc ≤ E.π ⁻¹ᵁ V.1 := by
  classical
  -- the base point and the atlas patch around it
  set y : E.E := (E.mulByHom N).base x with hy
  have hππ : E.π.base y = E.π.base x := by
    show E.π.base ((E.mulByHom N).base x) = E.π.base x
    rw [← Scheme.Hom.comp_apply, E.mulByHom_π]
  obtain ⟨U, hsU, W, hell, e, heπ, hez⟩ := E.localModel (E.π.base x)
  -- `y` lies over `U`, hence in the range of the atlas-patch inclusion
  have hyU : y ∈ E.π ⁻¹ᵁ U.1 := by
    show E.π.base y ∈ U.1
    rw [hππ]; exact hsU
  have hymem : y ∈ Set.range (pullback.fst E.π U.1.ι).base := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, Scheme.Opens.range_ι, SetLike.mem_coe]
    exact hyU
  obtain ⟨y', hy'⟩ := hymem
  -- the Proj chart containing the image of `y'`
  have htop := Proj.iSup_basicOpen_eq_top ((projIdeal W).quotientGrading)
    (fun i : Fin 3 => Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X i))
    (quotient_irrelevant_le_span_mk_X W)
  have hz : e.hom.base y' ∈ (⊤ : (projModel W).Opens) := trivial
  rw [← htop] at hz
  obtain ⟨i, hzi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  exact G.exists_mem_stableAffineOpen_aux N hkill x U e
    (Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W i) one_pos) hy' hzi

end ChartExistence

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
