/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Presheaf

/-!
# Covariant functoriality of the presheaf value along a continuous ring hom

For a continuous ring homomorphism `φ : R →+* S` and rational localization data
`D` of `R`, `D'` of `S` with matching denominator (`D'.s = φ D.s`) and numerator
containment (`φ '' D.T ⊆ D'.T`), the completed rational localization is covariantly
functorial:

* `locMapOfHom` — the localization-level map `Rₛ →+* S_{s'}` (`IsLocalization.map`);
* `pushMapAlg` — its composition into the completion `𝒪(D')`;
* `presheafValueMapOfHom : 𝒪(D) →+* 𝒪(D')` — the completed covariant map, with
  `_continuous`, `_coe`, and `_canonicalMap` (naturality on `R`).

This is the ring-hom generalization of the noetherian-free keystone
(`RelativeDescent.lean`, the same-ring image-datum case). It was previously
stranded inside `namespace FiniteJet` (`FJP/FiniteJetFunctoriality.lean`); it is
generic (no jet structure) and used here by the ring-equivalence presheaf
transport (`RingEquivPresheafTransport.lean`) and re-used by FJP.

## Reference

[FJP] Lemma 5.1; the localization-topology continuity engine
(`locTopology_continuous_lift`) and completion functoriality
(`UniformSpace.Completion.extensionHom`).
-/

noncomputable section

open Filter Topology

namespace ValuationSpectrum

section CovariantPush

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

/-- The localization-level covariant map of a pushed rational datum. -/
noncomputable def locMapOfHom (φ : R →+* S) (D : RationalLocData R)
    (D' : RationalLocData S) (hs : D'.s = φ D.s) :
    Localization.Away D.s →+* Localization.Away D'.s :=
  IsLocalization.map (Localization.Away D'.s) φ
    (show Submonoid.powers D.s ≤ (Submonoid.powers D'.s).comap φ from
      Submonoid.powers_le.mpr (show φ D.s ∈ Submonoid.powers D'.s from
        ⟨1, by show D'.s ^ 1 = φ D.s; rw [pow_one, hs]⟩))

theorem locMapOfHom_algebraMap (φ : R →+* S) (D : RationalLocData R)
    (D' : RationalLocData S) (hs : D'.s = φ D.s) (a : R) :
    locMapOfHom φ D D' hs (algebraMap R (Localization.Away D.s) a) =
      algebraMap S (Localization.Away D'.s) (φ a) := by
  unfold locMapOfHom
  rw [IsLocalization.map_eq]

theorem locMapOfHom_divByS (φ : R →+* S) (D : RationalLocData R)
    (D' : RationalLocData S) (hs : D'.s = φ D.s) (t : R) :
    locMapOfHom φ D D' hs (divByS t D.s) = divByS (φ t) D'.s := by
  rw [divByS, divByS, locMapOfHom, IsLocalization.map_mk']
  exact congrArg _ (Subtype.ext hs.symm)

/-- Continuity of the localization-level covariant map (universal property of the
localization topology; the pushed generators are in `locSubring D'`, hence
power-bounded). -/
theorem locMapOfHom_continuous (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) :
    @Continuous _ _ D.topology D'.topology (locMapOfHom φ D D' hs) := by
  letI := D'.topology
  haveI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  haveI : @NonarchimedeanRing _ _ D'.topology :=
    (locBasis D'.P D'.T D'.s D'.hopen).nonarchimedean
  have hf_alg : @Continuous _ _ _ D'.topology
      ((locMapOfHom φ D D' hs).comp (algebraMap R (Localization.Away D.s))) := by
    have h_eq : (locMapOfHom φ D D' hs).comp (algebraMap R (Localization.Away D.s)) =
        (algebraMap S (Localization.Away D'.s)).comp φ := by
      ext a; exact locMapOfHom_algebraMap φ D D' hs a
    rw [show ⇑((locMapOfHom φ D D' hs).comp (algebraMap R (Localization.Away D.s)))
        = ⇑((algebraMap S (Localization.Away D'.s)).comp φ) from congrArg _ h_eq,
      RingHom.coe_comp]
    refine Continuous.comp ?_ hφ
    -- `algebraMap S (Localization.Away D'.s)` is continuous into `D'.topology`
    -- (inlined from `algebraMap_continuous_loc`, avoiding its nonarchimedean variable).
    apply continuous_of_continuousAt_zero
      (algebraMap S (Localization.Away D'.s)).toAddMonoidHom
    rw [ContinuousAt, map_zero, Filter.tendsto_def]
    intro U hU
    obtain ⟨n, -, hn⟩ :=
      (locBasis D'.P D'.T D'.s D'.hopen).hasBasis_nhds_zero.mem_iff.mp hU
    apply Filter.mem_of_superset (D'.P.hasBasis_nhds_zero.mem_of_mem (i := n) trivial)
    intro a ha
    obtain ⟨⟨b, hb⟩, hbn, hab⟩ := ha
    rw [← hab]
    exact hn ⟨algebraMapD D'.P D'.T D'.s ⟨b, hb⟩,
      by rw [locIdeal, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hbn, rfl⟩
  refine locTopology_continuous_lift D.P D.T D.s D.hopen _ hf_alg fun t ht => ?_
  rw [locMapOfHom_divByS]
  exact (locSubring_isBounded_of_pair D'.P D'.T D'.s D'.hopen).isPowerBounded_of_mem
    (divByS_mem_locSubring D'.P D'.T D'.s (hT t ht))

/-- The covariant map into the completion (algebraic side). -/
noncomputable def pushMapAlg (φ : R →+* S) (D : RationalLocData R)
    (D' : RationalLocData S) (hs : D'.s = φ D.s) :
    Localization.Away D.s →+* presheafValue D' :=
  D'.coeRingHom.comp (locMapOfHom φ D D' hs)

theorem pushMapAlg_continuous (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) :
    @Continuous _ _ D.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      (pushMapAlg φ D D' hs) := by
  letI := D.topology
  letI := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  have hcoe : @Continuous _ _ D'.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D'.uniformSpace))
      D'.coeRingHom :=
    @UniformSpace.Completion.continuous_coe _ D'.uniformSpace
  exact hcoe.comp (locMapOfHom_continuous φ hφ D D' hs hT)

/-- The covariant presheaf-value map `𝒪(D) →+* 𝒪(D')` along `φ` ([FJP] Lemma 5.1). -/
noncomputable def presheafValueMapOfHom (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) :
    presheafValue D →+* presheafValue D' := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (pushMapAlg φ D D' hs)
    (pushMapAlg_continuous φ hφ D D' hs hT)

theorem presheafValueMapOfHom_continuous (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) :
    Continuous (presheafValueMapOfHom φ hφ D D' hs hT) := by
  letI := D.uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-- The covariant map agrees with the algebraic map on the dense image. -/
theorem presheafValueMapOfHom_coe (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) (a : Localization.Away D.s) :
    presheafValueMapOfHom φ hφ D D' hs hT
      (@UniformSpace.Completion.coeRingHom _ _ D.uniformSpace
        D.isTopologicalRing D.isUniformAddGroup a) =
      pushMapAlg φ D D' hs a := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (pushMapAlg φ D D' hs)
    (pushMapAlg_continuous φ hφ D D' hs hT) a

/-- The covariant map intertwines the canonical maps ([FJP] Lemma 5.1 naturality on `A`). -/
theorem presheafValueMapOfHom_canonicalMap (φ : R →+* S) (hφ : Continuous φ)
    (D : RationalLocData R) (D' : RationalLocData S) (hs : D'.s = φ D.s)
    (hT : ∀ t ∈ D.T, φ t ∈ D'.T) (a : R) :
    presheafValueMapOfHom φ hφ D D' hs hT (D.canonicalMap a) =
      D'.canonicalMap (φ a) := by
  have h1 : presheafValueMapOfHom φ hφ D D' hs hT (D.canonicalMap a) =
      pushMapAlg φ D D' hs (algebraMap R (Localization.Away D.s) a) :=
    presheafValueMapOfHom_coe φ hφ D D' hs hT (algebraMap R (Localization.Away D.s) a)
  rw [h1]
  show D'.coeRingHom (locMapOfHom φ D D' hs (algebraMap R (Localization.Away D.s) a)) = _
  rw [locMapOfHom_algebraMap]
  rfl

end CovariantPush

end ValuationSpectrum
