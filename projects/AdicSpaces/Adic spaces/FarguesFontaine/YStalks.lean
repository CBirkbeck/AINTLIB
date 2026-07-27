/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.YCharts
import «Adic spaces».StructureSheafStalks

/-!
# Stalk locality of the ambient structure presheaf at points of `𝒴` (YB3c)

The Wedhorn 8.14 shrink argument over the NON-TATE ambient `A_inf`: at
`𝒴`-interior rationals the completed localizations are concretely Tate
(`isTateRing_presheafValue_of_rationalOpen_subset_Y`), so the Laurent-scaling
shrink replays verbatim with the de-Tated S3 machinery and the general-Huber
rational basis. See the board's YB-plan.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace CategoryTheory TopCat

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- The localization-lift package at the ambient `A_inf`, as an instance
(the uniformizer only feeds the ϖ-independent T2/completeness facts). -/
noncomputable instance : HasLocLiftPowerBounded (Ainf p F) :=
  hasLocLiftPowerBounded_Ainf p F
    (IsTateRing.pseudoUniformizer (A := F))

/-- **The rational shrink claim at `Y`-interior rationals** (the Wedhorn 8.14
core over the non-Tate ambient `A_inf`): the concrete Tate structure of the
completed localization comes from `𝒴`-interiority (`YB1`), everything else is
the Tate-free machinery. -/
theorem rationalShrink_Y
    (D : RationalLocData (Ainf p F)) (hD : D.IsRational)
    (hDY : rationalOpen D.T D.s ⊆ Y p F ϖ)
    (v' : Spv (Ainf p F))
    (hv : v' ∈ (rationalOpen D.T D.s
      ∩ Spa (Ainf p F) (ringPlus (Ainf p F)) : Set (Spv (Ainf p F))))
    (b : presheafValue D) (hnz : ¬ (pointValue D hv).vle b 0) :
    ∃ (D' : RationalLocData (Ainf p F)) (_hD' : D'.IsRational)
      (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s),
      rationalOpen D'.T D'.s ⊆ Y p F ϖ
      ∧ v' ∈ rationalOpen D'.T D'.s
      ∧ IsUnit (restrictionMapHom D D' h b) := by
  classical
  haveI : IsRingOfIntegralElements
      ((Ainf p F)⁺ : Subring (Ainf p F)) := isAffinoidRing_Ainf p F
  haveI : T2Space (Ainf p F) := t2Space_Ainf p F ϖ
  haveI := completeSpace_right_Ainf p F ϖ
  haveI hTate : IsTateRing (presheafValue D) :=
    isTateRing_presheafValue_of_rationalOpen_subset_Y p F ϖ D hDY
  have hwspa := pointValue_mem_spa D hv
  have hwcont := pointValue_isContinuous D hv
  obtain ⟨u, hu⟩ := hTate.exists_topologicallyNilpotent_unit
  obtain ⟨k, hk⟩ := exists_pow_vle_of_isContinuous hwcont hu hnz
  set c : presheafValue D := ((u⁻¹ : _ˣ) : presheafValue D) ^ k * b with hcdef
  have h1c : (pointValue D hv).vle 1 c := by
    have h1 := (pointValue D hv).mul_vle_mul_left hk
      (((u⁻¹ : _ˣ) : presheafValue D) ^ k)
    rw [show ((u : presheafValue D) ^ k
          * ((u⁻¹ : _ˣ) : presheafValue D) ^ k) = 1 from by
        rw [← mul_pow, Units.mul_inv, one_pow],
      show b * ((u⁻¹ : _ˣ) : presheafValue D) ^ k = c from by
        rw [hcdef]; ring] at h1
    exact h1
  have hc0 : ¬ (pointValue D hv).vle c 0 := by
    intro hcon
    refine hnz ?_
    have h2 := (pointValue D hv).mul_vle_mul_left hcon
      ((u : presheafValue D) ^ k)
    rw [zero_mul, show c * (u : presheafValue D) ^ k = b from by
      rw [hcdef, mul_comm _ b, mul_assoc, ← mul_pow, Units.inv_mul, one_pow,
        mul_one]] at h2
    exact h2
  obtain ⟨W, hWopen, hvW, hcapture⟩ := exists_A_level_open_presentation' D
    u hu hwspa (ι := Unit) (fam := {()})
    (F := fun _ => (1 : presheafValue D))
    (G := fun _ => c) (fun i _ => ⟨h1c, hc0⟩)
  rw [comap_pointValue D hv] at hvW
  obtain ⟨D', hD', hvD', hD'sub⟩ := exists_isRational_spaOpen_subset_huber
    (V := Subtype.val ⁻¹' W ∩ spaOpen D)
    (IsOpen.inter (hWopen.preimage continuous_subtype_val)
      (isOpen_spaOpen D))
    (v := ⟨v', hv.2⟩) ⟨hvW, mem_spaOpen.mpr hv.1⟩
  have hsub : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s :=
    spaOpen_subset_iff.mp (hD'sub.trans Set.inter_subset_right)
  refine ⟨D', hD', hsub, hsub.trans hDY, mem_spaOpen.mp hvD', ?_⟩
  haveI hTate' : IsTateRing (presheafValue D') :=
    isTateRing_presheafValue_of_rationalOpen_subset_Y p F ϖ D'
      (hsub.trans hDY)
  haveI : IsHuberRing (presheafValue D') := presheafValue_isHuberRing_huber D'
  letI P_B : PairOfDefinition (presheafValue D') := presheafValue_concretePair D'
  haveI : IsAdicComplete P_B.I P_B.A₀ := presheafValue_isAdicComplete D'
  rw [isUnit_iff_forall_not_vle_zero_of_completePair P_B]
  intro w'' hw'' hcon
  have hwPD := comap_restrictionMapHom_mem_spa D D' hsub hw''
  have hbase' := comap_canonicalMap_mem_rationalOpen_inter_spa D' ⟨w'', hw''⟩
  have hbaseEq : comap D.canonicalMap
      (comap (restrictionMapHom D D' hsub) w'')
      = comap D'.canonicalMap w'' := by
    rw [show comap D.canonicalMap (comap (restrictionMapHom D D' hsub) w'')
        = comap ((restrictionMapHom D D' hsub).comp D.canonicalMap) w'' from
      by rw [comap_comp]; rfl]
    have hcomp : (restrictionMapHom D D' hsub).comp D.canonicalMap
        = D'.canonicalMap :=
      RingHom.ext (restrictionMapHom_canonicalMap_generic D D' hsub)
    rw [hcomp]
  have hW' : comap D.canonicalMap
      (comap (restrictionMapHom D D' hsub) w'') ∈ W := by
    rw [hbaseEq]
    exact (hD'sub (show (⟨comap D'.canonicalMap w'', hbase'.2⟩
      : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) ∈ spaOpen D' from
      hbase'.1)).1
  have hcap := hcapture (comap (restrictionMapHom D D' hsub) w'') hwPD hW'
    () (Finset.mem_singleton_self ())
  refine hcap.2 ?_
  show (comap (restrictionMapHom D D' hsub) w'').vle c 0
  have hcb : (comap (restrictionMapHom D D' hsub) w'').vle b 0 := by
    show w''.vle (restrictionMapHom D D' hsub b)
      (restrictionMapHom D D' hsub 0)
    rw [map_zero]
    exact hcon
  have h3 := (comap (restrictionMapHom D D' hsub) w'').mul_vle_mul_left hcb
    (((u⁻¹ : _ˣ) : presheafValue D) ^ k)
  rw [zero_mul, show b * ((u⁻¹ : _ˣ) : presheafValue D) ^ k = c from by
    rw [hcdef]; ring] at h3
  exact h3

/-- The plus subring of `A_inf` is a ring of integral elements (instance
form of `isAffinoidRing_Ainf`). -/
instance : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
  isAffinoidRing_Ainf p F

/-- `A_inf` is separated (instance at the canonical uniformizer). -/
instance : T2Space (Ainf p F) :=
  t2Space_Ainf p F (IsTateRing.pseudoUniformizer (A := F))

/-- `A_inf` is right-complete (instance at the canonical uniformizer). -/
noncomputable instance :
    @CompleteSpace (Ainf p F)
      (IsTopologicalAddGroup.rightUniformSpace (Ainf p F)) :=
  completeSpace_right_Ainf p F (IsTateRing.pseudoUniformizer (A := F))

/-- **The stalk shrink claim at points of `𝒴`** (Wedhorn 8.14 over the
ambient `A_inf`, `Y`-locally): representing the germ over a `Y`-interior
rational and shrinking by `rationalShrink_Y`. -/
theorem stalkShrink_Y
    (v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (hvY : (v : Spv (Ainf p F)) ∈ Y p F ϖ) :
    StalkShrink v := by
  classical
  intro x hx
  obtain ⟨U, hvU, f, rfl⟩ := (spaRingPresheaf (Ainf p F)).exists_germ_eq x
  have hnz : ¬ (openValue U hvU).vle f 0 := by
    intro hcon
    refine hx ⟨U, hvU, f, 0, rfl, germ_zero U hvU, hcon⟩
  -- choose a Y-interior rational index inside `U`
  obtain ⟨E, hErat, hvE, hEsub⟩ := exists_isRational_spaOpen_subset_huber
    (V := (show Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))
        from (U : Set ↥(SpaTop (Ainf p F))))
      ∩ Subtype.val ⁻¹' (Y p F ϖ))
    ((show IsOpen (show Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))
        from (U : Set ↥(SpaTop (Ainf p F)))) from U.2).inter
      (isOpen_Y p F ϖ))
    (v := v) ⟨hvU, hvY⟩
  have hEY : rationalOpen E.T E.s ⊆ Y p F ϖ := by
    intro w hw
    have hwspa : w ∈ Spa (Ainf p F) (ringPlus (Ainf p F)) := hw.1
    have hmem : (⟨w, hwspa⟩ : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
        ∈ spaOpen E := mem_spaOpen.mpr hw
    exact (hEsub hmem).2
  set i : RationalIndex U :=
    ⟨E, hErat, hEsub.trans Set.inter_subset_left⟩ with hidef
  have hvi : (v : Spv (Ainf p F)) ∈ (rationalOpen i.D.T i.D.s
      ∩ Spa (Ainf p F) (ringPlus (Ainf p F)) : Set (Spv (Ainf p F))) :=
    ⟨mem_spaOpen.mp hvE, v.2⟩
  have hcoh := comap_limitEvalHom_pointValue hvU i hvi
  have hnzD : ¬ (pointValue i.D hvi).vle (limitEvalHom i f) 0 := by
    intro hcon
    refine hnz ?_
    rw [← hcoh]
    exact (comap_vle (limitEvalHom i) (pointValue i.D hvi) f 0).mpr (by
      rwa [map_zero])
  obtain ⟨D', hD', hsub, hD'Y, hvD', hunit⟩ := rationalShrink_Y p F ϖ
    i.D i.isRational hEY (v : Spv (Ainf p F)) hvi (limitEvalHom i f) hnzD
  have hW'U : spaOpens D' ≤ U :=
    (spaOpen_subset_of_rationalOpen_subset hsub).trans i.subset
  have hvW' : v ∈ spaOpens D' := mem_spaOpen.mpr hvD'
  have hcomp : limitEval hD' (limitRestrict hW'U f)
      = restrictionMapHom i.D D' hsub (limitEvalHom i f) :=
    (f.2 i ((RationalIndex.self D' hD').mono hW'U) hsub).symm
  have hfunit : IsUnit (limitRestrict hW'U f) := by
    have h1 : IsUnit (limitEval hD' (limitRestrict hW'U f)) := by
      rw [hcomp]
      exact hunit
    have h2 := h1.map (limitEval hD').symm.toRingHom
    rwa [show (limitEval hD').symm.toRingHom (limitEval hD'
        (limitRestrict hW'U f)) = limitRestrict hW'U f from
      (limitEval hD').symm_apply_apply _] at h2
  have hgerm : (spaRingPresheaf (Ainf p F)).germ (spaOpens D') v hvW'
      (limitRestrict hW'U f)
      = (spaRingPresheaf (Ainf p F)).germ U v hvU f :=
    germ_limitRestrict hW'U hvW' f
  rw [← hgerm]
  exact isUnit_germ_of_isUnit hvW' hfunit

/-- **Wedhorn 8.14 at points of `𝒴`, unconditional**: the stalk of the
ambient structure presheaf at any `𝒴`-point is a local ring. -/
theorem isLocalRing_stalk_Y
    (v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (hvY : (v : Spv (Ainf p F)) ∈ Y p F ϖ) :
    IsLocalRing (ToType ((spaRingPresheaf (Ainf p F)).stalk v)) :=
  isLocalRing_stalk_of_shrink (stalkShrink_Y p F ϖ v hvY)

/-- **Wedhorn 8.14 at points of `𝒴`, the maximal ideal**: it is the support
of the stalk valuation. -/
theorem maximalIdeal_stalk_Y
    (v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
    (hvY : (v : Spv (Ainf p F)) ∈ Y p F ϖ) :
    @IsLocalRing.maximalIdeal _ _ (isLocalRing_stalk_Y p F ϖ v hvY)
      = (stalkValue v).supp :=
  maximalIdeal_stalk_eq_supp (stalkShrink_Y p F ϖ v hvY)

end FarguesFontaine

end
