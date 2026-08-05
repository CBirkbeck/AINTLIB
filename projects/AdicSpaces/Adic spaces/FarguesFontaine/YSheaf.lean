/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RestrictedLimitSheaf

/-!
# The Fargues–Fontaine `𝒴` as an object of `𝒱` (YB6c-3e)

The categorical conversion at the restricted site: the `Y`-relative all-open
condition (`isLimitSheafOn_Y`, from `isSheafyOn_Y` + quasicompactness of
`A_inf`-rationals) turns into the sheaf-of-topological-rings condition for the
restricted presheaf through the open-image functor — every image-open lies
inside the `𝒴`-trace, so the `S`-guarded `Hom`-gluing core applies verbatim.
`yVObj` completes the YB-track: `𝒴` is an object of Wedhorn's category `𝒱`.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology Filter CategoryTheory Opposite

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- Cross-transport of section-restriction equalities along an equality of
opens (proof-irrelevant in the two `≤`-witnesses). -/
theorem limitRestrict_cross_eq_of_opens_eq
    {W W' V₁ V₂ : Opens ↥(Spa A A⁺)} (hWW' : W = W')
    (h₁ : W ≤ V₁) (h₂ : W ≤ V₂) (h₁' : W' ≤ V₁) (h₂' : W' ≤ V₂)
    {x : ↥(limitSections V₁)} {y : ↥(limitSections V₂)}
    (hxy : limitRestrict h₁ x = limitRestrict h₂ y) :
    limitRestrict h₁' x = limitRestrict h₂' y := by
  subst hWW'
  exact hxy

end ValuationSpectrum

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

noncomputable local instance : DecidableEq (Ainf p F) := Classical.decEq _
noncomputable local instance : DecidableEq (RationalLocData (Ainf p F)) :=
  Classical.decEq _

/-- **The `Y`-relative all-open sheaf condition over `A_inf`** — the three
arbitrary-cover fields for opens inside the `𝒴`-trace. -/
theorem isLimitSheafOn_Y :
    ValuationSpectrum.IsLimitSheafOn (A := Ainf p F) (Y p F ϖ) :=
  ValuationSpectrum.isLimitSheafOn_of_isSheafyOn (isSheafyOn_Y p F ϖ)
    (fun D hD => isCompact_subtype_rationalOpen_ainf p F D hD)

/-- The open-image functor of the `𝒴`-inclusion. -/
def yFunctor : Opens ↥(yTop p F ϖ) ⥤ Opens ↥(SpaTop (Ainf p F)) :=
  (yIncl_isOpenEmbedding p F ϖ).isOpenMap.functor

omit [CharP F p] in
theorem yFunctor_trace (W : Opens ↥(yTop p F ϖ)) :
    ((yFunctor p F ϖ).obj W : Set ↥(SpaTop (Ainf p F)))
      ⊆ Subtype.val ⁻¹' Y p F ϖ := by
  rintro v ⟨x, -, rfl⟩
  exact x.2

omit [CharP F p] in
theorem yFunctor_cov {ι : Type*} (U : ι → Opens ↥(yTop p F ϖ)) :
    (((yFunctor p F ϖ).obj (iSup U)) : Set ↥(SpaTop (Ainf p F)))
      ⊆ ⋃ i, ((yFunctor p F ϖ).obj (U i) : Set ↥(SpaTop (Ainf p F))) := by
  show (yIncl p F ϖ) '' ((iSup U : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)) ⊆ _
  rw [Opens.coe_iSup, Set.image_iUnion]
  exact Set.iUnion_mono fun i => subset_rfl

omit [CharP F p] in
theorem yFunctor_inf (W₁ W₂ : Opens ↥(yTop p F ϖ)) :
    (yFunctor p F ϖ).obj (W₁ ⊓ W₂)
      = (yFunctor p F ϖ).obj W₁ ⊓ (yFunctor p F ϖ).obj W₂ := by
  refine Opens.ext ?_
  show (yIncl p F ϖ) '' ((W₁ ⊓ W₂ : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ)) = _
  rw [Opens.coe_inf, Set.image_inter
    (show Function.Injective (⇑(ConcreteCategory.hom (yIncl p F ϖ)))
      from Subtype.val_injective)]
  rfl

/-- The restricted presheaf's action, at the ambient spelling (pointwise). -/
theorem yPresheaf_map_apply {W W' : Opens ↥(yTop p F ϖ)} (h : W' ≤ W)
    (x : ↥(limitSections ((yFunctor p F ϖ).obj W))) :
    ((yPresheafedSpace p F ϖ).presheaf.map (homOfLE h).op).1 x
      = limitRestrict (leOfHom ((yFunctor p F ϖ).map (homOfLE h))) x :=
  structurePresheaf_map (((yFunctor p F ϖ).map (homOfLE h)).op) x

/-- **YB6c-3e — the `𝒴`-presheaf is a sheaf of topological rings** (Wedhorn
Remark 8.20 at the restricted site): every image-open lies inside the
`𝒴`-trace, so the `Y`-relative `Hom`-gluing core applies. -/
theorem yPresheaf_isSheafOfTopologicalRings :
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (yPresheafedSpace p F ϖ).presheaf := by
  intro T _tc _tt _tr ι U f hcompat
  set V' : Opens ↥(SpaTop (Ainf p F)) := (yFunctor p F ϖ).obj (iSup U)
    with hV'def
  set U' : ι → Opens ↥(SpaTop (Ainf p F)) :=
    fun i => (yFunctor p F ϖ).obj (U i) with hU'def
  have hle : ∀ i, U' i ≤ V' :=
    fun i => leOfHom ((yFunctor p F ϖ).map (homOfLE (le_iSup U i)))
  have hVS : (V' : Set ↥(SpaTop (Ainf p F))) ⊆ Subtype.val ⁻¹' Y p F ϖ :=
    yFunctor_trace p F ϖ (iSup U)
  have hcov : (V' : Set ↥(SpaTop (Ainf p F)))
      ⊆ ⋃ i, (U' i : Set ↥(SpaTop (Ainf p F))) := yFunctor_cov p F ϖ U
  have hcompat' : ∀ i j,
      (limitRestrict (inf_le_left (a := U' i) (b := U' j))).comp
          ((f i).1 : T →+* ↥(limitSections (U' i)))
        = (limitRestrict (inf_le_right (a := U' i) (b := U' j))).comp
            ((f j).1 : T →+* ↥(limitSections (U' j))) := by
    intro i j
    refine RingHom.ext fun t => ?_
    have h0 := DFunLike.congr_fun (hcompat i j) t
    have hL := yPresheaf_map_apply p F ϖ
      (inf_le_left (a := U i) (b := U j)) ((f i).1 t)
    have hR := yPresheaf_map_apply p F ϖ
      (inf_le_right (a := U i) (b := U j)) ((f j).1 t)
    have h0' := (hL.symm.trans h0).trans hR
    exact ValuationSpectrum.limitRestrict_cross_eq_of_opens_eq
      (yFunctor_inf p F ϖ (U i) (U j))
      (leOfHom ((yFunctor p F ϖ).map (homOfLE
        (inf_le_left (a := U i) (b := U j)))))
      (leOfHom ((yFunctor p F ϖ).map (homOfLE
        (inf_le_right (a := U i) (b := U j)))))
      (inf_le_left (a := U' i) (b := U' j))
      (inf_le_right (a := U' i) (b := U' j)) h0'
  obtain ⟨g, hg, huniq⟩ := (isLimitSheafOn_Y p F ϖ).homGlue hVS hle hcov
    (fun i => ((f i).1 : T →+* ↥(limitSections (U' i))))
    (fun i => (f i).2) hcompat'
  refine ⟨⟨g.1, g.2⟩, fun i => ?_, ?_⟩
  · refine RingHom.ext fun t => ?_
    have hmap := yPresheaf_map_apply p F ϖ (le_iSup U i) (g.1.1 t)
    exact hmap.trans (DFunLike.congr_fun (hg i) t)
  · rintro ⟨g'', hg''c⟩ hg''
    have := huniq ⟨g'', hg''c⟩ (fun i => RingHom.ext fun t => by
      have hmap := yPresheaf_map_apply p F ϖ (le_iSup U i) (g'' t)
      exact hmap.symm.trans (DFunLike.congr_fun (hg'' i) t))
    exact Subtype.ext (congrArg Subtype.val this)

/-- **The Fargues–Fontaine `𝒴` as an object of Wedhorn's category `𝒱`**:
the `𝒱^pre`-object of YB4/5 together with the sheaf-of-topological-rings
condition of the restricted site. -/
noncomputable def yVObj : ValuationSpectrum.VObj :=
  { yVPreObj p F ϖ with
    isSheafTopRings := yPresheaf_isSheafOfTopologicalRings p F ϖ }

end FarguesFontaine

end
