/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI contributors
-/
import «Adic spaces».StructureSheafStalks
import «Adic spaces».SheafyEndpoints
import «Adic spaces».WedhornCechAcyclicity
import «Adic spaces».NonTateRationalOpenHomeomorph

/-!
# `Spa` of a sheafy complete Tate ring as a `𝒱`-object (Campaign 9, P5-2)

The affinoid adic spaces of Wedhorn Definition 8.22:
* `rationalShrink_tate` — the Wedhorn 8.14 rational shrink claim over a
  complete Tate ring (every rational localization is itself Tate, so the
  nilpotent-unit rescale and the `A`-level open presentation apply);
* `spaVObjTate` — `Spa (A, A⁺)` with its structure presheaf, stalk locality
  (via the shrink claim), stalk valuations, and the
  sheaf-of-topological-rings condition (via Wedhorn 8.28(b) for strongly
  noetherian `A`), as an object of `𝒱`.
-/


open CategoryTheory TopologicalSpace Opposite

noncomputable section

universe u

namespace ValuationSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
  [IsRingOfIntegralElements (A⁺ : Subring A)]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
    CompleteSpace A]

/-- **The rational shrink claim over a complete Tate ring** (the Wedhorn 8.14
core, honest-Tate case): every rational localization is itself Tate, so the
nilpotent-unit rescale and the `A`-level open presentation apply verbatim. -/
theorem rationalShrink_tate : RationalShrink A := by
  intro D hD v' hv b hnz
  classical
  haveI hTate : IsTateRing (presheafValue D) :=
    presheafValue_isTateRing_concrete D
  have hwspa := pointValue_mem_spa D hv
  have hwcont := pointValue_isContinuous D hv
  obtain ⟨u, hu⟩ := hTate.exists_topologicallyNilpotent_unit
  obtain ⟨k, hk⟩ := exists_pow_vle_of_isContinuous hwcont hu hnz
  set c : presheafValue D := ((u⁻¹ : _ˣ) : presheafValue D) ^ k * b with hcdef
  have h1c : (pointValue D hv).vle 1 c := by
    have h1 := (pointValue D hv).mul_vle_mul_left hk
      (((u⁻¹ : _ˣ) : presheafValue D) ^ k)
    rw [show ((u : presheafValue D) ^ k
          * ((u⁻¹ : _ˣ) : presheafValue D) ^ k) = 1 by
        rw [← mul_pow, Units.mul_inv, one_pow],
      show b * ((u⁻¹ : _ˣ) : presheafValue D) ^ k = c by
        rw [hcdef]; ring] at h1
    exact h1
  have hc0 : ¬ (pointValue D hv).vle c 0 := by
    intro hcon
    refine hnz ?_
    have h2 := (pointValue D hv).mul_vle_mul_left hcon
      ((u : presheafValue D) ^ k)
    rw [zero_mul, show c * (u : presheafValue D) ^ k = b by
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
  refine ⟨D', hD', hsub, mem_spaOpen.mp hvD', ?_⟩
  haveI hTate' : IsTateRing (presheafValue D') :=
    presheafValue_isTateRing_concrete D'
  haveI : IsHuberRing (presheafValue D') := presheafValue_isHuberRing_huber D'
  letI P_B : PairOfDefinition (presheafValue D') := presheafValue_concretePair D'
  haveI : IsAdicComplete P_B.I P_B.A₀ := presheafValue_isAdicComplete D'
  rw [isUnit_iff_forall_not_vle_zero_of_completePair P_B]
  exact fun w'' hw'' => not_vle_zero_of_shrink D D' hsub hD'sub hcdef
    (fun w' hw' hW => (hcapture w' hw' hW () (Finset.mem_singleton_self ())).2) w'' hw''


/-- The stalk shrink claim over a complete Tate ring. -/
theorem stalkShrink_tate (v : ↥(Spa A A⁺)) : StalkShrink v :=
  stalkShrink_of_rationalShrink rationalShrink_tate v

/-- The ambient `Spa (A, A⁺)` as a presheafed space of complete topological
rings. -/
def spaPresheafedSpaceTate : TopRingPresheafedSpace where
  carrier := SpaTop A
  presheaf := structurePresheaf A

/-- **`Spa` of a sheafy strongly noetherian complete Tate ring as an object
of Wedhorn's category `𝒱`** (the affinoid adic spaces of Definition 8.22). -/
noncomputable def spaVObjTate [IsStronglyNoetherian A] : VObj where
  toPresheafedSpace := spaPresheafedSpaceTate (A := A)
  isLocalRing_stalk := fun v => isLocalRing_stalk_of_shrink (stalkShrink_tate v)
  val := fun v => stalkValue v
  val_supp := fun v => (maximalIdeal_stalk_eq_supp (stalkShrink_tate v)).symm
  isSheafTopRings := by
    classical
    haveI : IsNoetherianRing A := IsStronglyNoetherian.isNoetherianRing A
    haveI := hasLocLiftPowerBounded_faithful (A := A)
    haveI : IsSheafy A := isSheafy_of_stronglyNoetherian_828b
    exact (structurePresheaf_isSheafOfTopologicalRings_iff A).mpr
      isLimitSheaf_of_isSheafy

end ValuationSpectrum

end
