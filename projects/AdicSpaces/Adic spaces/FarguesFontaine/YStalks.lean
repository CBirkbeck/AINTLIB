/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.YCharts
import «Adic spaces».StructureSheafStalks
import «Adic spaces».RelativeDescentHuber
import «Adic spaces».FarguesFontaine.ChartVObj
import «Adic spaces».SpaQCviaSpvAI

/-!
# Stalk locality of the ambient structure presheaf at points of `𝒴` (YB3c)

The Wedhorn 8.14 shrink argument over the NON-TATE ambient `A_inf`: at
`𝒴`-interior rationals the completed localizations are concretely Tate
(`isTateRing_presheafValue_of_rationalOpen_subset_Y`), so the Laurent-scaling
shrink replays verbatim with the de-Tated S3 machinery and the general-Huber
rational basis. See the board's YB-plan.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace CategoryTheory TopCat AlgebraicGeometry

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

/-- The `𝒴`-trace inside the `Spa`-subspace. -/
def ySpaSet : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) :=
  Subtype.val ⁻¹' Y p F ϖ

/-- The `𝒴`-carrier as a topological space. -/
def yTop : TopCat := TopCat.of ↥(ySpaSet p F ϖ)

/-- The inclusion of the `𝒴`-carrier into `Spa (A_inf, A_inf)`. -/
def yIncl : yTop p F ϖ ⟶ SpaTop (Ainf p F) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion is an open embedding (`𝒴` is open in `Spa`). -/
theorem yIncl_isOpenEmbedding :
    Topology.IsOpenEmbedding (yIncl p F ϖ) :=
  (isOpen_Y p F ϖ).isOpenEmbedding_subtypeVal

/-- **The ambient `Spa (A_inf, A_inf)` as a presheafed space** (general-Huber
form of `spaPresheafedSpace`, available through the M8 package). -/
def yAmbientPresheafedSpace : TopRingPresheafedSpace where
  carrier := SpaTop (Ainf p F)
  presheaf := structurePresheaf (Ainf p F)

/-- **The `𝒴`-presheafed space**: the restriction of the ambient structure
presheaf along the open inclusion. -/
def yPresheafedSpace : TopRingPresheafedSpace :=
  (yAmbientPresheafedSpace p F).restrict (yIncl_isOpenEmbedding p F ϖ)

/-- The ambient space with its ring presheaf, as a `CommRingCat`-valued
presheafed space (the stalk-comparison vehicle). -/
def yAmbientRingSpace : AlgebraicGeometry.PresheafedSpace CommRingCat where
  carrier := SpaTop (Ainf p F)
  presheaf := (yAmbientPresheafedSpace p F).ringPresheaf

/-- **The restricted ring stalks are the ambient ring stalks** (mathlib's
`restrictStalkIso` at the ring-presheaf level; the two restricted ring
presheaves agree by associativity of functor composition). -/
noncomputable def yRingStalkIso (x : yTop p F ϖ) :
    (yPresheafedSpace p F ϖ).ringStalk x
      ≅ (yAmbientPresheafedSpace p F).ringStalk ((yIncl p F ϖ) x) :=
  AlgebraicGeometry.PresheafedSpace.restrictStalkIso
    (yAmbientRingSpace p F) (yIncl_isOpenEmbedding p F ϖ) x

/-- The ambient `Spa`-point of a `𝒴`-carrier point (spelled as the
inclusion image, so the stalk types line up definitionally). -/
def ySpaPoint (x : yTop p F ϖ) :
    ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) :=
  show ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))
    from (ConcreteCategory.hom (yIncl p F ϖ)) x

/-- The `Y`-membership of the ambient point. -/
theorem ySpaPoint_mem_Y (x : yTop p F ϖ) :
    ((ySpaPoint p F ϖ x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
      : Spv (Ainf p F)) ∈ Y p F ϖ :=
  (x : ↥(ySpaSet p F ϖ)).2

/-- The stalk comparison as a ring equivalence. -/
noncomputable def yRingStalkEquiv (x : yTop p F ϖ) :
    ToType ((yPresheafedSpace p F ϖ).ringStalk x)
      ≃+* ToType ((spaRingPresheaf (Ainf p F)).stalk (ySpaPoint p F ϖ x)) :=
  (yRingStalkIso p F ϖ x).commRingCatIsoToRingEquiv

/-- **The stalks of the `𝒴`-presheafed space are local** (transport of the
`Y`-point Wedhorn 8.14 package along the restriction stalk iso). -/
theorem isLocalRing_yStalk (x : yTop p F ϖ) :
    IsLocalRing (ToType ((yPresheafedSpace p F ϖ).ringStalk x)) := by
  haveI : IsLocalRing (ToType ((spaRingPresheaf (Ainf p F)).stalk
      (ySpaPoint p F ϖ x))) :=
    isLocalRing_stalk_Y p F ϖ (ySpaPoint p F ϖ x) (ySpaPoint_mem_Y p F ϖ x)
  exact (yRingStalkEquiv p F ϖ x).symm.isLocalRing

/-- **`𝒴` as an object of `𝒱^pre`** (Wedhorn Definition 8.5): the ambient
structure presheaf restricted to the open subset `𝒴`, with the Wedhorn 8.14
stalk package transported along the restriction stalk isomorphisms. -/
noncomputable def yVPreObj : VPreObj where
  toPresheafedSpace := yPresheafedSpace p F ϖ
  isLocalRing_stalk := fun x => isLocalRing_yStalk p F ϖ x
  val := fun x => comap ((yRingStalkEquiv p F ϖ x : _ →+* _))
    (stalkValue (ySpaPoint p F ϖ x))
  val_supp := fun x => by
    haveI hSloc : IsLocalRing (ToType ((spaRingPresheaf (Ainf p F)).stalk
        (ySpaPoint p F ϖ x))) :=
      isLocalRing_stalk_Y p F ϖ (ySpaPoint p F ϖ x) (ySpaPoint_mem_Y p F ϖ x)
    rw [supp_comap]
    rw [show (stalkValue (ySpaPoint p F ϖ x)).supp
        = @IsLocalRing.maximalIdeal _ _ hSloc from
      (maximalIdeal_stalk_Y p F ϖ (ySpaPoint p F ϖ x)
        (ySpaPoint_mem_Y p F ϖ x)).symm]
    exact @IsLocalRing.maximalIdeal_comap _ _ _ (isLocalRing_yStalk p F ϖ x)
      _ hSloc (((yRingStalkEquiv p F ϖ x) : _ →+* _))
      ⟨fun a ha => (isLocalHom_equiv (yRingStalkEquiv p F ϖ x)).map_nonunit a ha⟩

/-- Each Big window is the rational open of its window chart datum. -/
theorem bigWindow_eq_rationalOpen_windowUnif (n : ℤ) :
    bigWindow p F ϖ n
      = rationalOpen (chartData p F (windowUnif p F ϖ n) 1 1 p 1).T
          (chartData p F (windowUnif p F ϖ n) 1 1 p 1).s := by
  match n with
  | .ofNat k =>
    rw [show (Int.ofNat k) = ((k : ℕ) : ℤ) from rfl,
      bigWindow_eq_rationalOpen_ofNat p F ϖ k (one_lt_p p)]
    rfl
  | .negSucc m =>
    rw [show (Int.negSucc m) = (-(((m + 1 : ℕ)) : ℤ)) from rfl,
      bigWindow_eq_rationalOpen_neg p F ϖ (m + 1) (one_lt_p p)]
    rfl

/-- **`p·[ϖ]` maps to a unit of every window chart ring** (the chart ring is
Tate with the `chartS`-image as topologically nilpotent unit; `p[ϖ]` divides
a `chartS`-power and conversely, so its image is a unit — routed through the
Spa-point criterion like `YB1`). -/
theorem isUnit_canonicalMap_p_teichPi_window (n : ℤ) :
    IsUnit ((chartData p F (windowUnif p F ϖ n) 1 1 p 1).canonicalMap
      ((p : Ainf p F) * teichPi p F ϖ)) := by
  haveI : IsRingOfIntegralElements
      ((Ainf p F)⁺ : Subring (Ainf p F)) := isAffinoidRing_Ainf p F
  haveI : IsHuberRing (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1)) :=
    presheafValue_isHuberRing_huber _
  letI P_B : PairOfDefinition (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1)) :=
    presheafValue_concretePair _
  haveI : IsAdicComplete P_B.I P_B.A₀ := presheafValue_isAdicComplete _
  rw [isUnit_iff_forall_not_vle_zero_of_completePair P_B]
  intro w hw hcon
  have hmem := comap_canonicalMap_mem_rationalOpen
    (chartData p F (windowUnif p F ϖ n) 1 1 p 1)
    (canonicalMap_continuous _) hw
  have hY : comap (chartData p F (windowUnif p F ϖ n) 1 1 p 1).canonicalMap w
      ∈ Y p F ϖ := by
    have hbig : comap (chartData p F (windowUnif p F ϖ n) 1 1 p 1).canonicalMap
        w ∈ bigWindow p F ϖ n := by
      rw [bigWindow_eq_rationalOpen_windowUnif p F ϖ n]
      exact hmem
    have hcov := Y_eq_iUnion_bigWindow p F ϖ (one_lt_p p)
    rw [hcov]
    exact Set.mem_iUnion.mpr ⟨n, hbig⟩
  refine hY.2 ?_
  exact (comap_vle _ w _ 0).mpr (by rwa [map_zero])

/-- **The image-span certificate at the window charts**: every valid
`A_inf`-rational datum's tray hits `⊤` after mapping into a window chart
ring (`(p[ϖ])^N` lies in the open tray span; its image is a unit). -/
theorem span_image_windowChart_eq_top (n : ℤ)
    [DecidableEq (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1))]
    (E : RationalLocData (Ainf p F)) (hErat : E.IsRational) :
    Ideal.span ((E.T.image
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1).canonicalMap
      : Finset (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1)))
      : Set (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1)))
      = ⊤ := by
  classical
  obtain ⟨N, hN⟩ := (isAdic_iff.mp (isAdic_Iinf p F ϖ)).2
    _ (hErat.mem_nhds (by
      exact (Ideal.span ((E.T : Finset (Ainf p F)) : Set (Ainf p F))).zero_mem))
  have hpow : ((p : Ainf p F) * teichPi p F ϖ) ^ N
      ∈ Ideal.span ((E.T : Finset (Ainf p F)) : Set (Ainf p F)) := by
    refine hN ?_
    exact Ideal.pow_mem_pow
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))) N
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hpow
  have himg : ((chartData p F (windowUnif p F ϖ n) 1 1 p 1).canonicalMap
        ((p : Ainf p F) * teichPi p F ϖ)) ^ N
      ∈ Ideal.span ((E.T.image
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1).canonicalMap
      : Finset (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1)))
      : Set (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1))) := by
    rw [← map_pow, ← hc]
    rw [map_sum]
    refine Ideal.sum_mem _ fun t ht => ?_
    rw [smul_eq_mul, map_mul]
    exact Ideal.mul_mem_left _ _
      (Ideal.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ ht)))
  exact Ideal.eq_top_of_isUnit_mem _ himg
    ((isUnit_canonicalMap_p_teichPi_window p F ϖ n).pow N)

noncomputable local instance : DecidableEq (Ainf p F) := Classical.decEq _

noncomputable local instance (n : ℤ) :
    DecidableEq (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1)) :=
  Classical.decEq _

/-- **The window keystone**: the value of the ambient structure presheaf on a
valid rational inside a Big window is the value of the window chart's own
structure presheaf on the image datum (`keystoneO` at the certificate). -/
noncomputable def windowKeystone (n : ℤ) (E : RationalLocData (Ainf p F))
    (hErat : E.IsRational)
    (hEwin : rationalOpen E.T E.s
      ⊆ rationalOpen (chartData p F (windowUnif p F ϖ n) 1 1 p 1).T
          (chartData p F (windowUnif p F ϖ n) 1 1 p 1).s) :
    presheafValue E ≃+* presheafValue
      (imgDatumO (chartData p F (windowUnif p F ϖ n) 1 1 p 1) E
        (span_image_windowChart_eq_top p F ϖ n E hErat)) :=
  keystoneO (chartData p F (windowUnif p F ϖ n) 1 1 p 1)
    (span_image_windowChart_eq_top p F ϖ n E hErat) hEwin

end FarguesFontaine

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- **The subset-relative sheaf condition**: the two `IsSheafy`-fields, for
rational coverings whose base lies inside `S`. -/
structure IsSheafyOn (S : Set (Spv A)) [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] : Prop where
  embedding : ∀ (C : RationalCoveringData A), C.IsRational →
    rationalOpen C.base.T C.base.s ⊆ S →
    Topology.IsEmbedding (productRestrictionSub A C)
  gluing : ∀ (C : RationalCoveringData A), C.IsRational →
    rationalOpen C.base.T C.base.s ⊆ S →
    ∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
    (∀ (D₁ D₂ : ↥C.covers)
       (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
         restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D

end ValuationSpectrum

namespace ValuationSpectrum

universe u

/-- `IsSheafy` transports across an equality of `PlusSubring` instances
(the only data-valued instance in its signature; all the others are
`Prop`-classes and transport by proof irrelevance). -/
theorem isSheafy_congr_plusSubring {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [hc : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    (inst₁ inst₂ : PlusSubring A) (h : inst₁ = inst₂)
    (hint₁ : IsRingOfIntegralElements
      ((@ringPlus A _ inst₁) : Subring A))
    (hint₂ : IsRingOfIntegralElements
      ((@ringPlus A _ inst₂) : Subring A))
    (hs : @IsSheafy A _ _ _ inst₁ _ _ _ hc hint₁) :
    @IsSheafy A _ _ _ inst₂ _ _ _ hc hint₂ := by
  subst h
  exact hs

end ValuationSpectrum

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- The window-chart exactness data, packaged. -/
theorem window_hexact2 (n : ℤ) :
    (rhoRight p F (windowUnif p F ϖ n) p 1) ^ p
      = perfectoidValuation p F
          ((PseudoUniformizer.toOF F (windowUnif p F ϖ n) : OF F) : F) ^ 1 := by
  exact rhoRight_pow_exact p F (windowUnif p F ϖ n) p 1
    (Nat.Prime.pos (Fact.out : Nat.Prime p))

/-- The transported (`B^I`-ball) plus instance of a `(a, 1)`-chart equals the
canonical `completedPlusSubring`-based instance — the instance-level form of
the r5c plus reconciliation. -/
theorem chartPlus_instance_eq_canonical {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁}
    {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1} (a : ℕ) (ha : 0 < a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ 1) :
    chartPlus p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) a 1 ha one_pos ha hexact1 hexact2
      = RationalLocData.presheafValuePlusSubring (chartData p F ϖ 1 1 a 1) :=
  congrArg ValuationSpectrum.PlusSubring.mk
    (chartPlus_eq_canonical p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a ha hexact1 hexact2)

/-- **YB6c-3c′ — the window chart ring is sheafy at the canonical
instances**: `IsSheafy (presheafValue (chartData (windowUnif n) 1 1 p 1))`
with the canonical (`completedPlusSubring`-based) plus subring, the chart's
own Tate-Huber structure, and the canonical ring-of-integral-elements
instance — the form consumed by the single-`D₀` transport theorems. -/
theorem isSheafy_canonical_window (n : ℤ) :
    letI : IsHuberRing (presheafValue
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1)) :=
      (isTateRing_bigWindowChart p F (windowUnif p F ϖ n)).toIsHuberRing
    letI : @CompleteSpace (presheafValue
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1))
        (IsTopologicalAddGroup.rightUniformSpace (presheafValue
          (chartData p F (windowUnif p F ϖ n) 1 1 p 1))) :=
      completeSpace_right_presheafValue
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1)
    ValuationSpectrum.IsSheafy (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1)) := by
  have hp : 1 < p := one_lt_p p
  have hs := isSheafy_presheafChart p F (windowUnif p F ϖ n)
    (hρ₁0 := vpi_pos p F (windowUnif p F ϖ n))
    (hρ₁1 := perfectoidValuation_toOF_lt_one p F (windowUnif p F ϖ n))
    (hρ₂0 := rhoRight_pos p F (windowUnif p F ϖ n) p 1)
    (hρ₂1 := rhoRight_lt_one p F (windowUnif p F ϖ n) p 1 (by omega) one_pos)
    p 1 (by omega) one_pos (by omega) rfl
    (window_hexact2 p F ϖ n)
  exact ValuationSpectrum.isSheafy_congr_plusSubring _ _
    (chartPlus_instance_eq_canonical p F (windowUnif p F ϖ n) p (by omega)
      rfl (window_hexact2 p F ϖ n)) _ _ hs

/-- **YB6c-3c′, assembled — the single-window sheaf condition over the
ambient `A_inf`**: every valid rational covering whose base lies inside a
window chart's rational open satisfies both `IsSheafy`-fields, by the
single-`D₀` transport at the window chart ring (which is sheafy at the
canonical instances) with span certificates from the `p`-adic window unit. -/
theorem isSheafyOn_window (n : ℤ) :
    ValuationSpectrum.IsSheafyOn (A := Ainf p F)
      (rationalOpen (chartData p F (windowUnif p F ϖ n) 1 1 p 1).T
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1).s) := by
  classical
  haveI : IsTateRing (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1)) :=
    isTateRing_bigWindowChart p F (windowUnif p F ϖ n)
  haveI : IsHuberRing (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1)) :=
    IsTateRing.toIsHuberRing
  letI : @CompleteSpace (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1))
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue
        (chartData p F (windowUnif p F ϖ n) 1 1 p 1))) :=
    completeSpace_right_presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1)
  haveI : ValuationSpectrum.IsSheafy (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1)) :=
    isSheafy_canonical_window p F ϖ n
  refine ⟨?_, ?_⟩
  · intro C hC hCS
    exact isEmbedding_productRestrictionSub_of_imgCovering
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1)
      (fun E hE => span_image_windowChart_eq_top p F ϖ n E hE) C hC hCS
  · intro C hC hCS f hf
    exact exists_glue_of_imgCovering
      (chartData p F (windowUnif p F ϖ n) 1 1 p 1)
      (fun E hE => span_image_windowChart_eq_top p F ϖ n E hE) C hC hCS f hf

/-- **The run window** `{v : κ(v) ∈ [p^n, p^{n+k+1}]}` — the union of the
`k + 1` adjacent Big windows starting at `n`. -/
def runWindow (n : ℤ) (k : ℕ) : Set (Spv (Ainf p F)) :=
  {v ∈ Y p F ϖ | KGE p F ϖ ((p : ℚ) ^ n) v
    ∧ KLE p F ϖ ((p : ℚ) ^ (n + k + 1)) v}

/-- **The run window is the rational open of the `(p^{k+1}, 1)`-chart in the
window uniformizer** (nonnegative side): generalizes
`bigWindow_eq_rationalOpen_ofNat` from `a = p` to `a = p^{k+1}`. -/
theorem runWindow_eq_rationalOpen_ofNat (n : ℕ) (k : ℕ) (hp : 1 < p) :
    runWindow p F ϖ (n : ℤ) k
      = rationalOpen
          (chartT p F (PseudoUniformizer.frobRoot p F ϖ n) (p ^ (k + 1)) 1)
          (chartS p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1) := by
  have hppos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hppos
  have hpk : 0 < p ^ n := pow_pos hppos n
  set ϖ' := PseudoUniformizer.frobRoot p F ϖ n with hϖ'def
  have hteich : teichPi p F ϖ' ^ p ^ n = teichPi p F ϖ :=
    teichPi_frobRoot_pow p F ϖ n
  have hYeq : Y p F ϖ' = Y p F ϖ :=
    Y_eq_of_teichPi_pow p F ϖ hpk hteich
  ext v
  have hiff := mem_rationalOpen_chartData_iff p F ϖ' 1 1 (p ^ (k + 1)) 1
    one_pos one_pos (pow_pos hppos _) one_pos v
  rw [show 1 + p ^ (k + 1) - 1 = p ^ (k + 1) from by omega,
    show 1 + 1 - 1 = 1 from by omega] at hiff
  rw [runWindow, Set.mem_setOf_eq, hiff, hYeq]
  have hq1 : (0 : ℚ) < (p : ℚ) ^ (n : ℤ) := zpow_pos hp0 _
  have hq2 : (0 : ℚ) < (p : ℚ) ^ ((n : ℤ) + k + 1) := zpow_pos hp0 _
  have hab1 : (p : ℚ) ^ (n : ℤ) = ((p ^ n : ℕ) : ℚ) / ((1 : ℕ) : ℚ) := by
    push_cast
    rw [zpow_natCast]
    ring
  have hab2 : (p : ℚ) ^ ((n : ℤ) + k + 1)
      = ((p ^ (n + k + 1) : ℕ) : ℚ) / ((1 : ℕ) : ℚ) := by
    push_cast
    rw [show (n : ℤ) + k + 1 = ((n + k + 1 : ℕ) : ℤ) from by push_cast; ring,
      zpow_natCast]
    ring
  have hmul : p ^ (k + 1) * p ^ n = p ^ (n + k + 1) := by
    rw [← pow_add]
    ring_nf
  constructor
  · rintro ⟨hY, hge, hle⟩
    have hgev := (KGE_iff hY hq1 one_pos hab1).mp hge
    have hlev := (KLE_iff hY hq2 one_pos hab2).mp hle
    rw [pow_one] at hgev hlev
    refine ⟨hY, ?_, ?_⟩
    · refine (vle_pow_iff hpk _ _).mp ?_
      simp only [pow_one]
      rw [hteich]
      exact hgev
    · refine (vle_pow_iff hpk _ _).mp ?_
      simp only [pow_one]
      rw [hteich, ← pow_mul, hmul]
      exact hlev
  · rintro ⟨hY, hge, hle⟩
    simp only [pow_one] at hge hle
    refine ⟨hY, ?_, ?_⟩
    · refine (KGE_iff hY hq1 one_pos hab1).mpr ?_
      have h := (vle_pow_iff (v := v) hpk _ _).mpr hge
      rw [hteich] at h
      rw [pow_one]
      exact h
    · refine (KLE_iff hY hq2 one_pos hab2).mpr ?_
      have h := (vle_pow_iff (v := v) hpk _ _).mpr hle
      rw [hteich, ← pow_mul, hmul] at h
      rw [pow_one]
      exact h

/-- **The run window is a rational open (negative side)**: as
`runWindow_eq_rationalOpen_ofNat`, at the `p^m`-th power uniformizer. -/
theorem runWindow_eq_rationalOpen_neg (m k : ℕ) (hp : 1 < p) :
    runWindow p F ϖ (-(m : ℤ)) k
      = rationalOpen
          (chartT p F (PseudoUniformizer.pPow F ϖ (p ^ m)
            (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) (p ^ (k + 1)) 1)
          (chartS p F (PseudoUniformizer.pPow F ϖ (p ^ m)
            (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1) := by
  have hppos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hppos
  have hpk : 0 < p ^ m := pow_pos hppos m
  set ϖ' := PseudoUniformizer.pPow F ϖ (p ^ m) (pow_pos hppos m) with hϖ'def
  have hteich : teichPi p F ϖ' = teichPi p F ϖ ^ p ^ m :=
    teichPi_pPow p F ϖ (p ^ m) (pow_pos hppos m)
  have hYeq : Y p F ϖ' = Y p F ϖ :=
    (Y_eq_of_teichPi_pow p F ϖ' hpk hteich.symm).symm
  ext v
  have hiff := mem_rationalOpen_chartData_iff p F ϖ' 1 1 (p ^ (k + 1)) 1
    one_pos one_pos (pow_pos hppos _) one_pos v
  rw [show 1 + p ^ (k + 1) - 1 = p ^ (k + 1) from by omega,
    show 1 + 1 - 1 = 1 from by omega] at hiff
  rw [runWindow, Set.mem_setOf_eq, hiff, hYeq]
  have hq1 : (0 : ℚ) < (p : ℚ) ^ (-(m : ℤ)) := zpow_pos hp0 _
  have hq2 : (0 : ℚ) < (p : ℚ) ^ (-(m : ℤ) + k + 1) := zpow_pos hp0 _
  have hab1 : (p : ℚ) ^ (-(m : ℤ)) = ((1 : ℕ) : ℚ) / ((p ^ m : ℕ) : ℚ) := by
    rw [zpow_neg, zpow_natCast]
    push_cast
    rw [one_div]
  have hab2 : (p : ℚ) ^ (-(m : ℤ) + k + 1)
      = ((p ^ (k + 1) : ℕ) : ℚ) / ((p ^ m : ℕ) : ℚ) := by
    rw [show -(m : ℤ) + k + 1 = ((k + 1 : ℕ) : ℤ) - ((m : ℕ) : ℤ) from by
        push_cast
        ring,
      zpow_sub₀ hp0.ne', zpow_natCast, zpow_natCast]
    push_cast
    ring
  constructor
  · rintro ⟨hY, hge, hle⟩
    have hgev := (KGE_iff hY hq1 hpk hab1).mp hge
    have hlev := (KLE_iff hY hq2 hpk hab2).mp hle
    rw [pow_one] at hgev
    refine ⟨hY, ?_, ?_⟩
    · simp only [pow_one]
      rw [hteich]
      exact hgev
    · simp only [pow_one]
      rw [hteich]
      exact hlev
  · rintro ⟨hY, hge, hle⟩
    simp only [pow_one] at hge hle
    rw [hteich] at hge hle
    refine ⟨hY, ?_, ?_⟩
    · refine (KGE_iff hY hq1 hpk hab1).mpr ?_
      rw [pow_one]
      exact hge
    · exact (KLE_iff hY hq2 hpk hab2).mpr hle

/-- **The run window is the rational open of the `(p^{k+1}, 1)`-window-chart
datum**, uniformly in `n : ℤ`. -/
theorem runWindow_eq_rationalOpen (n : ℤ) (k : ℕ) :
    runWindow p F ϖ n k
      = rationalOpen
          (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).T
          (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).s := by
  match n with
  | .ofNat j =>
    rw [show (Int.ofNat j) = ((j : ℕ) : ℤ) from rfl,
      runWindow_eq_rationalOpen_ofNat p F ϖ j k (one_lt_p p)]
    rfl
  | .negSucc m =>
    rw [show (Int.negSucc m) = (-(((m + 1 : ℕ)) : ℤ)) from rfl,
      runWindow_eq_rationalOpen_neg p F ϖ (m + 1) k (one_lt_p p)]
    rfl

/-- Run windows lie inside `Y`. -/
theorem runWindow_subset_Y (n : ℤ) (k : ℕ) :
    runWindow p F ϖ n k ⊆ Y p F ϖ :=
  fun _ hv => hv.1

/-- **Each Big window of the run lies in the run window.** -/
theorem bigWindow_subset_runWindow (n : ℤ) (k : ℕ) {j : ℤ}
    (hj1 : n ≤ j) (hj2 : j ≤ n + k) :
    bigWindow p F ϖ j ⊆ runWindow p F ϖ n k := by
  have hpQ : (1 : ℚ) < p := by
    exact_mod_cast Nat.Prime.one_lt (Fact.out : Nat.Prime p)
  have hp0 : (0 : ℚ) < p := zero_lt_one.trans hpQ
  rintro v ⟨hY, hge, hle⟩
  refine ⟨hY, ?_, ?_⟩
  · exact KGE_mono p F ϖ hY (zpow_pos hp0 n)
      (zpow_le_zpow_right₀ hpQ.le hj1) hge
  · exact KLE_mono p F ϖ hY (zpow_pos hp0 (j + 1))
      (zpow_le_zpow_right₀ hpQ.le (by omega)) hle

/-- **`p·[ϖ]` maps to a unit of every run chart ring** (as
`isUnit_canonicalMap_p_teichPi_window`, with the run-window `⊆ Y` input). -/
theorem isUnit_canonicalMap_p_teichPi_runChart (n : ℤ) (k : ℕ) :
    IsUnit ((chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).canonicalMap
      ((p : Ainf p F) * teichPi p F ϖ)) := by
  haveI : IsRingOfIntegralElements
      ((Ainf p F)⁺ : Subring (Ainf p F)) := isAffinoidRing_Ainf p F
  haveI : IsHuberRing (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)) :=
    presheafValue_isHuberRing_huber _
  letI P_B : PairOfDefinition (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)) :=
    presheafValue_concretePair _
  haveI : IsAdicComplete P_B.I P_B.A₀ := presheafValue_isAdicComplete _
  rw [isUnit_iff_forall_not_vle_zero_of_completePair P_B]
  intro w hw hcon
  have hmem := comap_canonicalMap_mem_rationalOpen
    (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)
    (canonicalMap_continuous _) hw
  have hY : comap (chartData p F (windowUnif p F ϖ n) 1 1
      (p ^ (k + 1)) 1).canonicalMap w ∈ Y p F ϖ := by
    refine runWindow_subset_Y p F ϖ n k ?_
    rw [runWindow_eq_rationalOpen p F ϖ n k]
    exact hmem
  refine hY.2 ?_
  exact (comap_vle _ w _ 0).mpr (by rwa [map_zero])

/-- **The image-span certificate at the run charts**: as
`span_image_windowChart_eq_top`. -/
theorem span_image_runChart_eq_top (n : ℤ) (k : ℕ)
    [DecidableEq (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1))]
    (E : RationalLocData (Ainf p F)) (hErat : E.IsRational) :
    Ideal.span ((E.T.image
        (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).canonicalMap
      : Finset (presheafValue
        (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)))
      : Set (presheafValue
        (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)))
      = ⊤ := by
  classical
  obtain ⟨N, hN⟩ := (isAdic_iff.mp (isAdic_Iinf p F ϖ)).2
    _ (hErat.mem_nhds (by
      exact (Ideal.span ((E.T : Finset (Ainf p F)) : Set (Ainf p F))).zero_mem))
  have hpow : ((p : Ainf p F) * teichPi p F ϖ) ^ N
      ∈ Ideal.span ((E.T : Finset (Ainf p F)) : Set (Ainf p F)) := by
    refine hN ?_
    exact Ideal.pow_mem_pow
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))) N
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hpow
  have himg : ((chartData p F (windowUnif p F ϖ n) 1 1
        (p ^ (k + 1)) 1).canonicalMap
        ((p : Ainf p F) * teichPi p F ϖ)) ^ N
      ∈ Ideal.span ((E.T.image
        (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).canonicalMap
      : Finset (presheafValue
        (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)))
      : Set (presheafValue
        (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1))) := by
    rw [← map_pow, ← hc]
    rw [map_sum]
    refine Ideal.sum_mem _ fun t ht => ?_
    rw [smul_eq_mul, map_mul]
    exact Ideal.mul_mem_left _ _
      (Ideal.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ ht)))
  exact Ideal.eq_top_of_isUnit_mem _ himg
    ((isUnit_canonicalMap_p_teichPi_runChart p F ϖ n k).pow N)

/-- The run-chart exactness data, packaged. -/
theorem run_hexact2 (n : ℤ) (k : ℕ) :
    (rhoRight p F (windowUnif p F ϖ n) (p ^ (k + 1)) 1) ^ (p ^ (k + 1))
      = perfectoidValuation p F
          ((PseudoUniformizer.toOF F (windowUnif p F ϖ n) : OF F) : F) ^ 1 := by
  exact rhoRight_pow_exact p F (windowUnif p F ϖ n) (p ^ (k + 1)) 1
    (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) (k + 1))

/-- **The run chart datum is Tate** (as `isTateRing_bigWindowChart`, at
`(a, b) = (p^{k+1}, 1)`). -/
theorem isTateRing_runChart (n : ℤ) (k : ℕ) :
    IsTateRing (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)) := by
  have hp : 1 < p := one_lt_p p
  have ha : 0 < p ^ (k + 1) := pow_pos (by omega) (k + 1)
  exact isTateRing_presheafChart p F (windowUnif p F ϖ n)
    (hρ₁0 := vpi_pos p F (windowUnif p F ϖ n))
    (hρ₁1 := perfectoidValuation_toOF_lt_one p F (windowUnif p F ϖ n))
    (hρ₂0 := rhoRight_pos p F (windowUnif p F ϖ n) (p ^ (k + 1)) 1)
    (hρ₂1 := rhoRight_lt_one p F (windowUnif p F ϖ n) (p ^ (k + 1)) 1
      (by omega) one_pos)
    (p ^ (k + 1)) 1 (by omega) one_pos (by omega) rfl
    (by rw [run_hexact2 p F ϖ n k, pow_one])

/-- **The run chart ring is sheafy at the canonical instances** (as
`isSheafy_canonical_window`, at `a = p^{k+1}`). -/
theorem isSheafy_canonical_runChart (n : ℤ) (k : ℕ) :
    letI : IsHuberRing (presheafValue
        (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)) :=
      (isTateRing_runChart p F ϖ n k).toIsHuberRing
    letI : @CompleteSpace (presheafValue
        (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1))
        (IsTopologicalAddGroup.rightUniformSpace (presheafValue
          (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1))) :=
      completeSpace_right_presheafValue
        (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)
    ValuationSpectrum.IsSheafy (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)) := by
  have hp : 1 < p := one_lt_p p
  have ha : 0 < p ^ (k + 1) := pow_pos (by omega) (k + 1)
  have hs := isSheafy_presheafChart p F (windowUnif p F ϖ n)
    (hρ₁0 := vpi_pos p F (windowUnif p F ϖ n))
    (hρ₁1 := perfectoidValuation_toOF_lt_one p F (windowUnif p F ϖ n))
    (hρ₂0 := rhoRight_pos p F (windowUnif p F ϖ n) (p ^ (k + 1)) 1)
    (hρ₂1 := rhoRight_lt_one p F (windowUnif p F ϖ n) (p ^ (k + 1)) 1
      (by omega) one_pos)
    (p ^ (k + 1)) 1 (by omega) one_pos (by omega) rfl
    (run_hexact2 p F ϖ n k)
  exact ValuationSpectrum.isSheafy_congr_plusSubring _ _
    (chartPlus_instance_eq_canonical p F (windowUnif p F ϖ n) (p ^ (k + 1))
      (by omega) rfl (run_hexact2 p F ϖ n k)) _ _ hs

/-- **The run-window sheaf condition over the ambient `A_inf`** (as
`isSheafyOn_window`, at the run chart). -/
theorem isSheafyOn_runChart (n : ℤ) (k : ℕ) :
    ValuationSpectrum.IsSheafyOn (A := Ainf p F)
      (rationalOpen (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).T
        (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).s) := by
  classical
  haveI : IsTateRing (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)) :=
    isTateRing_runChart p F ϖ n k
  haveI : IsHuberRing (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)) :=
    IsTateRing.toIsHuberRing
  letI : @CompleteSpace (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1))
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue
        (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1))) :=
    completeSpace_right_presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)
  haveI : ValuationSpectrum.IsSheafy (presheafValue
      (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)) :=
    isSheafy_canonical_runChart p F ϖ n k
  refine ⟨?_, ?_⟩
  · intro C hC hCS
    exact isEmbedding_productRestrictionSub_of_imgCovering
      (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)
      (fun E hE => span_image_runChart_eq_top p F ϖ n k E hE) C hC hCS
  · intro C hC hCS f hf
    exact exists_glue_of_imgCovering
      (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1)
      (fun E hE => span_image_runChart_eq_top p F ϖ n k E hE) C hC hCS f hf

/-- **Valid rational subsets of `Spa(A_inf, A_inf)` are quasi-compact**
(Wedhorn 7.35(2) at the two-generator ideal `(p, [ϖ])`): openness of the
tray span gives `I_inf ≤ √(span T)`. -/
theorem isCompact_subtype_rationalOpen_ainf (E : RationalLocData (Ainf p F))
    (hErat : E.IsRational) :
    IsCompact (Subtype.val ⁻¹' rationalOpen E.T E.s
      : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) := by
  classical
  obtain ⟨P, g₁, g₂, hpair, hA₀le, hIeq⟩ := exists_pairOfDefinition_Iinf p F
  refine isCompact_subtype_rationalOpen₂ P hpair hA₀le _ hIeq E.T E.s ?_
  obtain ⟨N, hN⟩ := (isAdic_iff.mp
      (isAdic_Iinf p F (IsTateRing.pseudoUniformizer (A := F)))).2
    _ (hErat.mem_nhds (by
      exact (Ideal.span ((E.T : Finset (Ainf p F)) : Set (Ainf p F))).zero_mem))
  intro x hx
  exact ⟨N, hN (Ideal.pow_mem_pow hx N)⟩

/-- **Every valid `Y`-interior rational open lies inside a run chart**: the
quasi-compact trace meets only finitely many Big windows. -/
theorem exists_runChart_superset (E : RationalLocData (Ainf p F))
    (hErat : E.IsRational) (hEY : rationalOpen E.T E.s ⊆ Y p F ϖ) :
    ∃ n : ℤ, ∃ k : ℕ, rationalOpen E.T E.s
      ⊆ rationalOpen
          (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).T
          (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).s := by
  classical
  have hcomp := isCompact_subtype_rationalOpen_ainf p F E hErat
  have hopen : ∀ n : ℤ, IsOpen (Subtype.val ⁻¹' bigWindow p F ϖ n
      : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) := by
    intro n
    rw [bigWindow_eq_rationalOpen_windowUnif p F ϖ n]
    exact rationalOpen_isOpen _ _
  have hcov : (Subtype.val ⁻¹' rationalOpen E.T E.s
      : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
      ⊆ ⋃ n : ℤ, Subtype.val ⁻¹' bigWindow p F ϖ n := by
    intro x hx
    have hxY : (x : Spv (Ainf p F)) ∈ Y p F ϖ := hEY hx
    rw [Y_eq_iUnion_bigWindow p F ϖ (one_lt_p p)] at hxY
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxY
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨J, hJ⟩ := hcomp.elim_finite_subcover
    (fun n : ℤ => Subtype.val ⁻¹' bigWindow p F ϖ n) hopen hcov
  set J' : Finset ℤ := insert 0 J with hJ'def
  have hJ'ne : J'.Nonempty := ⟨0, Finset.mem_insert_self 0 J⟩
  set n₀ := J'.min' hJ'ne with hn₀def
  set N := J'.max' hJ'ne with hNdef
  have hn₀N : n₀ ≤ N := J'.min'_le_max' hJ'ne
  refine ⟨n₀, (N - n₀).toNat, ?_⟩
  rw [← runWindow_eq_rationalOpen p F ϖ n₀ (N - n₀).toNat]
  intro v hv
  have hvSpa : v ∈ Spa (Ainf p F) (ringPlus (Ainf p F)) :=
    rationalOpen_subset_spa hv
  have hvtrace := hJ (Set.mem_preimage.mpr
    (show ((⟨v, hvSpa⟩ : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))
      : Spv (Ainf p F)) ∈ rationalOpen E.T E.s from hv))
  obtain ⟨j, hjJ, hjmem⟩ := by
    simpa only [Set.mem_iUnion, Set.mem_preimage, exists_prop] using hvtrace
  refine bigWindow_subset_runWindow p F ϖ n₀ (N - n₀).toNat
    (J'.min'_le j (Finset.mem_insert_of_mem hjJ)) ?_ hjmem
  have : (j : ℤ) ≤ N := J'.le_max' j (Finset.mem_insert_of_mem hjJ)
  omega

/-- **YB6c-3d — the `Y`-interior sheaf condition over the ambient `A_inf`**:
every valid rational covering whose base lies inside `Y` satisfies both
`IsSheafy`-fields — quasi-compactness places the base inside a single run
chart, whose `isSheafyOn_runChart` applies. -/
theorem isSheafyOn_Y :
    ValuationSpectrum.IsSheafyOn (A := Ainf p F) (Y p F ϖ) := by
  constructor
  · intro C hC hCS
    obtain ⟨n, k, hsub⟩ := exists_runChart_superset p F ϖ C.base hC.base hCS
    exact (isSheafyOn_runChart p F ϖ n k).embedding C hC hsub
  · intro C hC hCS f hf
    obtain ⟨n, k, hsub⟩ := exists_runChart_superset p F ϖ C.base hC.base hCS
    exact (isSheafyOn_runChart p F ϖ n k).gluing C hC hsub f hf

end FarguesFontaine


end
