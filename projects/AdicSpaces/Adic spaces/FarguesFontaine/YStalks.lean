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

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace

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

end FarguesFontaine

end
