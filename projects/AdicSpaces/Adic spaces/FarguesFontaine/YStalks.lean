/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.YCharts
import «Adic spaces».StructureSheafStalks
import «Adic spaces».RelativeDescentHuber

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

/-- Maximal ideals transport through a ring equivalence of local rings
(instance-explicit form). -/
theorem maximalIdeal_comap_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (instR : IsLocalRing R) (instS : IsLocalRing S) (e : R ≃+* S) :
    @IsLocalRing.maximalIdeal R _ instR
      = (@IsLocalRing.maximalIdeal S _ instS).comap (e : R →+* S) := by
  refine Ideal.ext fun r => ?_
  rw [@IsLocalRing.mem_maximalIdeal _ _ instR, Ideal.mem_comap,
    @IsLocalRing.mem_maximalIdeal _ _ instS, mem_nonunits_iff,
    mem_nonunits_iff, not_iff_not]
  exact ⟨fun h => h.map (e : R →+* S), fun h => by
    have := h.map (e.symm : S →+* R)
    rwa [show (e.symm : S →+* R) ((e : R →+* S) r) = r from
      e.symm_apply_apply r] at this⟩

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
    exact (maximalIdeal_comap_ringEquiv (isLocalRing_yStalk p F ϖ x)
      hSloc (yRingStalkEquiv p F ϖ x)).symm

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

end
