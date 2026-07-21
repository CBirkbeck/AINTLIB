/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».CompletionModelIndependence
import «Adic spaces».PresheafIdentification
import «Adic spaces».SheafyRingEquivTransport

/-!
# The clean complete-ring/completion-model equivalence and model independence

**C0.** For a *complete* Huber ring `A` (no Tate, no noetherian hypotheses), the
canonical map into any completion model is a bicontinuous ring equivalence:

* `completeRingEquivCompletionModel (P) : A ≃+* CompletionModel A P`, whose
  forward map is literally `(globalLocData P).canonicalMap`
  (`completeRingEquivCompletionModel_apply`), with
  `completeRingEquivCompletionModel_continuous` and `_symm_continuous`.

The inverse is the completion-extension of the away-one collapse
`Localization.Away 1 →+* A` (the `IsLocalization.Away.lift` of the identity),
which is continuous for the localization topology by
`locTopology_continuous_lift` (the only generator is `1`, whose image is
power-bounded).

This replaces any use of the overscoped `globalSections_equiv` (which leaks
`PlusSubring`, `DecidableEq`, noetherian and restriction-lift hypotheses and is
unusable for the finite-jet ring).

**C1.** Completion-model independence of ring-level sheafiness, for a Tate
ring `A` (no completeness of `A`, no plus rings, no noetherian hypotheses):

* `isSheafyTateRing_iff_for_completionModel` — checking one completion model is
  equivalent to checking every completion model;
* `isSheafyTateRing_iff_exists_completionModel` — the existential form;
* `isSheafyTateRing_iff_isSheafyComplete` — for *complete* Tate `A`, the
  ring-level Definition 8.26 collapses to `IsSheafyComplete A` through the C0
  equivalence.

Only bicontinuity of `completionModelCompare` is used — canonical-map
compatibility is not needed for the sheafiness transport.
-/

noncomputable section

namespace ValuationSpectrum

universe u

section C0

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

-- The away-one collapse `Localization.Away 1 →+* A`: the `IsLocalization` lift of the
-- identity along the (unit) image of `1`.
private noncomputable def completeRingCollapseAlg (P : PairOfDefinition A) :
    Localization.Away ((globalLocData P).s) →+* A :=
  IsLocalization.Away.lift (g := RingHom.id A) (globalLocData P).s isUnit_one

omit [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
-- The collapse tracks the algebra map.
private theorem completeRingCollapseAlg_algebraMap (P : PairOfDefinition A) (a : A) :
    completeRingCollapseAlg P (algebraMap A (Localization.Away ((globalLocData P).s)) a) = a :=
  IsLocalization.Away.lift_eq (g := RingHom.id A) _ _ a

omit [T2Space A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
-- Continuity of the collapse for the whole-space localization topology: the generator set
-- is `{1}`, whose image is power-bounded.
private theorem completeRingCollapseAlg_continuous (P : PairOfDefinition A) :
    @Continuous _ _ (globalLocData P).topology _ (completeRingCollapseAlg P) := by
  refine locTopology_continuous_lift P ({1} : Finset A) (1 : A) (globalLocData P).hopen
    (completeRingCollapseAlg P) ?_ ?_
  · exact continuous_id.congr fun a ↦ (completeRingCollapseAlg_algebraMap P a).symm
  · intro t ht
    rw [Finset.mem_singleton.mp ht, divByS_eq_algebraMap, map_one]
    exact (map_one (completeRingCollapseAlg P)).symm ▸ TopologicalRing.isPowerBounded_one

-- The inverse map: the completion-extension of the away-one collapse.
private noncomputable def completeRingCompletionModelInv (P : PairOfDefinition A) :
    CompletionModel A P →+* A :=
  letI : UniformSpace (Localization.Away ((globalLocData P).s)) := (globalLocData P).uniformSpace
  letI : IsUniformAddGroup (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).isUniformAddGroup
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  UniformSpace.Completion.extensionHom (completeRingCollapseAlg P)
    (completeRingCollapseAlg_continuous P)

-- The inverse on the dense localization image is the collapse.
private theorem completeRingCompletionModelInv_coe (P : PairOfDefinition A)
    (l : Localization.Away ((globalLocData P).s)) :
    completeRingCompletionModelInv P ((globalLocData P).coeRingHom l) =
      completeRingCollapseAlg P l := by
  letI : UniformSpace (Localization.Away ((globalLocData P).s)) := (globalLocData P).uniformSpace
  letI : IsUniformAddGroup (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).isUniformAddGroup
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  exact UniformSpace.Completion.extensionHom_coe _ _ l

-- Backward-after-canonical is the identity.
private theorem completeRingCompletionModelInv_canonicalMap (P : PairOfDefinition A) (a : A) :
    completeRingCompletionModelInv P ((globalLocData P).canonicalMap a) = a :=
  (completeRingCompletionModelInv_coe P _).trans (completeRingCollapseAlg_algebraMap P a)

-- Canonical-after-backward is the identity, via `UniformSpace.Completion.ext'` applied at the
-- literal target `presheafValue (globalLocData P)` (not the defeq `CompletionModel A P` alias).
private theorem canonicalMap_completeRingCompletionModelInv (P : PairOfDefinition A)
    (x : presheafValue (globalLocData P)) :
    (globalLocData P).canonicalMap (completeRingCompletionModelInv P x) = x := by
  letI : UniformSpace (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).uniformSpace
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  refine @UniformSpace.Completion.ext' _ _ (presheafValue (globalLocData P)) _ _
    (fun y ↦ (globalLocData P).canonicalMap (completeRingCompletionModelInv P y)) (fun y ↦ y)
    ((canonicalMap_continuous _).comp UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  intro l
  change (globalLocData P).canonicalMap
    (completeRingCompletionModelInv P ((globalLocData P).coeRingHom l)) =
    (globalLocData P).coeRingHom l
  rw [completeRingCompletionModelInv_coe]
  have hhom : (globalLocData P).canonicalMap.comp (completeRingCollapseAlg P) =
      (globalLocData P).coeRingHom :=
    IsLocalization.ringHom_ext (Submonoid.powers (globalLocData P).s) <| RingHom.ext fun a ↦
      DFunLike.congr_arg (globalLocData P).canonicalMap (completeRingCollapseAlg_algebraMap P a)
  exact DFunLike.congr_fun hhom l

/-- **The complete-ring/completion-model equivalence** (C0, Wedhorn Remark 8.3
for complete `A`): the canonical map `A → Â = CompletionModel A P` is a ring
equivalence. Hypotheses: complete Huber only — no Tate, no noetherian, no plus
ring, no `DecidableEq`, no localization-lift package. -/
noncomputable def completeRingEquivCompletionModel (P : PairOfDefinition A) :
    A ≃+* CompletionModel A P :=
  RingEquiv.ofRingHom (globalLocData P).canonicalMap (completeRingCompletionModelInv P)
    (RingHom.ext (canonicalMap_completeRingCompletionModelInv P))
    (RingHom.ext (completeRingCompletionModelInv_canonicalMap P))

/-- The forward map of the C0 equivalence is literally the canonical map `A → Â`. -/
@[simp] theorem completeRingEquivCompletionModel_apply (P : PairOfDefinition A) (a : A) :
    completeRingEquivCompletionModel P a = (globalLocData P).canonicalMap a := rfl

/-- The C0 equivalence is continuous (it is the canonical map `A → Â`). -/
theorem completeRingEquivCompletionModel_continuous (P : PairOfDefinition A) :
    Continuous (completeRingEquivCompletionModel P) :=
  canonicalMap_continuous (globalLocData P)

/-- The inverse of the C0 equivalence is continuous (a completion extension). -/
theorem completeRingEquivCompletionModel_symm_continuous (P : PairOfDefinition A) :
    Continuous (completeRingEquivCompletionModel P).symm := by
  letI : UniformSpace (Localization.Away ((globalLocData P).s)) := (globalLocData P).uniformSpace
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  exact UniformSpace.Completion.continuous_extension

end C0

/-! ### C1: completion-model independence of ring-level sheafiness -/

section C1

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTateRing A]

/-- **Checking one completion model suffices** (C1): ring-level Tate sheafiness
(`IsSheafyTateRing`, which quantifies over *every* completion model) is
equivalent to `IsSheafyComplete` of any *single* completion model. No plus-ring,
noetherian, decidable-equality, or localization-lift hypotheses appear. -/
theorem isSheafyTateRing_iff_for_completionModel (P : PairOfDefinition A) :
    IsSheafyTateRing A ↔ IsSheafyComplete (CompletionModel A P) :=
  -- forward: specialize the every-model quantifier at `P`; backward: transport the fixed
  -- model's sheafiness to every other model along the bicontinuous `completionModelCompare`
  ⟨fun h ↦ h P, fun h P' ↦
    (isSheafyComplete_congr (completionModelCompare P P') (completionModelCompare_continuous P P')
      (completionModelCompare_symm_continuous P P')).mp h⟩

/-- **The existential form** (C1): ring-level Tate sheafiness is equivalent to
sheafiness of *some* completion model. -/
theorem isSheafyTateRing_iff_exists_completionModel :
    IsSheafyTateRing A ↔ ∃ P : PairOfDefinition A, IsSheafyComplete (CompletionModel A P) :=
  ⟨fun h ↦ (‹IsTateRing A›.toIsHuberRing).exists_pairOfDefinition.elim fun P ↦
      ⟨P, (isSheafyTateRing_iff_for_completionModel P).mp h⟩,
    fun ⟨P, hP⟩ ↦ (isSheafyTateRing_iff_for_completionModel P).mpr hP⟩

variable [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-- **For complete Tate rings the two ring-level notions coincide** (C1): the
completion-model quantification of Wedhorn Definition 8.26 collapses to
`IsSheafyComplete A` itself, through the C0 equivalence `A ≃+* Â`. -/
theorem isSheafyTateRing_iff_isSheafyComplete : IsSheafyTateRing A ↔ IsSheafyComplete A :=
  (‹IsTateRing A›.toIsHuberRing).exists_pairOfDefinition.elim fun P ↦
    (isSheafyTateRing_iff_for_completionModel P).trans
      (isSheafyComplete_congr (completeRingEquivCompletionModel P)
        (completeRingEquivCompletionModel_continuous P)
        (completeRingEquivCompletionModel_symm_continuous P)).symm

end C1

end ValuationSpectrum
