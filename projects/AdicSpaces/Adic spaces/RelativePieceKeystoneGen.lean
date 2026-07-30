/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI contributors
-/
import «Adic spaces».RelativePieceKeystone

/-!
# The relative-piece keystone at weakened hypotheses (Campaign 9, P5-3a)

`RelativePieceKeystone.lean` proves Wedhorn Prop 8.16 (`relativePiece_equiv`)
over a **Tate** base `A`. Inspection of that chain shows the base-level
`[IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]` hypotheses are
used for exactly one purpose: to supply `IsTateRing`, `IsNoetherianRing` and
`IsStronglyNoetherian` for the **value** ring `B := 𝒪_X(D₀)` through the
`_faithful` suppliers.

This file re-derives the same chain with those three hypotheses moved to `B`
itself. That is what makes the keystone usable over `A_inf`, which is **not**
Tate but whose window-chart values are complete Tate and strongly noetherian —
the missing ingredient for the Fargues–Fontaine curve's Wedhorn-8.22 charts.

Statements and proofs are the Tate-base originals with the hypothesis block
moved; see `RelativePieceKeystone.lean` for the mathematical commentary.
-/

open Pointwise

noncomputable section

universe u

namespace ValuationSpectrum

namespace GenKeystone

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

set_option linter.unusedSectionVars false in
/-- The span of the image of an ideal-generating set is the unit ideal. -/
theorem span_image_canonicalMap_eq_top
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    Ideal.span (D₀.canonicalMap '' (T : Set A)) = ⊤ := by
  rw [← Ideal.map_span D₀.canonicalMap, hspan]
  exact Ideal.map_top _

omit [PlusSubring A] [IsHuberRing A] in
/-- **The A-side gen-set piece** `R(T/t)` (Wedhorn p. 83's `U_t := R(T/t)` cover form),
with the `hopen`-condition supplied by `genPiece_hopen` (span + absorption).
(`A⁺`-free: the datum and its openness use only the pair of definition.) -/
noncomputable def genPieceDatum (P : PairOfDefinition A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) : RationalLocData A :=
  { P := P
    T := T
    s := t
    hopen := genPiece_hopen P T t hspan }

omit [PlusSubring A] [IsHuberRing A] in
@[simp] theorem genPieceDatum_P (P : PairOfDefinition A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) : (genPieceDatum P T t hspan).P = P := rfl

omit [PlusSubring A] [IsHuberRing A] in
@[simp] theorem genPieceDatum_T (P : PairOfDefinition A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) : (genPieceDatum P T t hspan).T = T := rfl

omit [PlusSubring A] [IsHuberRing A] in
@[simp] theorem genPieceDatum_s (P : PairOfDefinition A) (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) : (genPieceDatum P T t hspan).s = t := rfl

/-- **The B-side image piece** `R(canMap T / canMap t)` over `B = presheafValue D₀`
(Wedhorn Remark 8.4 / Prop 8.2(1) vocabulary: the rational subset of `Spa 𝒪_X(D₀)`
corresponding to `D₀ ∩ R(T/t)`). The `hopen`-condition is `genPiece_hopen` at `B`
(span-combination + absorption). -/
noncomputable def imagePieceDatum
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    RationalLocData (presheafValue D₀) :=
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  letI : DecidableEq (presheafValue D₀) := Classical.decEq _
  letI : DecidableEq (RationalLocData (presheafValue D₀)) := Classical.decEq _
  { P := presheafValue_concretePair D₀
    T := T.image D₀.canonicalMap
    s := D₀.canonicalMap t
    hopen := genPiece_hopen (presheafValue_concretePair D₀)
      (T.image D₀.canonicalMap) (D₀.canonicalMap t)
      (by rw [Finset.coe_image]; exact span_image_canonicalMap_eq_top D₀ T hspan) }

/-- The pair of definition of `imagePieceDatum` is `presheafValue_concretePair D₀`.

Named projection lemma (see `RationalLocData.interSamePair_P`): pair-equality proofs
between two `imagePieceDatum`s must be built from this by `Eq.trans`/`Eq.symm` so they
stay well-typed at reducible transparency (a bare `rfl` needs the semireducible
`imagePieceDatum` unfolded and makes v4.33 `kabstract` choke on any enclosing goal). -/
theorem imagePieceDatum_P
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    (imagePieceDatum D₀ T t hspan).P = presheafValue_concretePair D₀ := rfl

/-- The image piece is rational (Wedhorn 7.29): its tray is the `canonicalMap`-image of
a `⊤`-spanning family, which spans `⊤` (`span_image_canonicalMap_eq_top`). -/
theorem imagePieceDatum_isRational
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    (imagePieceDatum D₀ T t hspan).IsRational := by
  letI : DecidableEq (presheafValue D₀) := Classical.decEq _
  refine RationalLocData.isRational_of_span_eq_top ?_
  show Ideal.span (((T.image D₀.canonicalMap) : Finset (presheafValue D₀)) :
    Set (presheafValue D₀)) = ⊤
  rw [Finset.coe_image]
  exact span_image_canonicalMap_eq_top D₀ T hspan

set_option linter.unusedSectionVars false in
/-- **General relative piece, forward base unit (G1-1)**: `s_inter = D₀.s·t` maps to a
unit of `Localization.Away (canMap t)` over `B`. -/
theorem genPiece_rel_baseHom_isUnit
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    IsUnit (((algebraMap (presheafValue D₀) (Localization.Away
        ((imagePieceDatum D₀ T t hspan).s))).comp D₀.canonicalMap)
      ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s)) := by
  have hs : ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s : A) =
      D₀.s * t := rfl
  rw [RingHom.comp_apply, hs, map_mul, map_mul]
  refine IsUnit.mul ?_ ?_
  · exact ((isUnit_s_in_presheafValue D₀).map _)
  · exact IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away ((imagePieceDatum D₀ T t hspan).s))
      ((imagePieceDatum D₀ T t hspan).s)

/-- **General relative piece, forward loc-hom (G1-2)**. -/
noncomputable def genPiece_rel_forwardLocHom
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    Localization.Away ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) →+*
      Localization.Away ((imagePieceDatum D₀ T t hspan).s) :=
  IsLocalization.Away.lift
    (x := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s)
    (g := (algebraMap (presheafValue D₀) (Localization.Away
      ((imagePieceDatum D₀ T t hspan).s))).comp D₀.canonicalMap)
    (genPiece_rel_baseHom_isUnit D₀ T t hspan)

set_option linter.unusedSectionVars false in
/-- G1-3: the forward loc-hom sends `algebraMap a ↦ algebraMap (canonicalMap a)`. -/
theorem genPiece_rel_forwardLocHom_algebraMap
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) (a : A) :
    genPiece_rel_forwardLocHom D₀ T t hspan
        (algebraMap A (Localization.Away
          ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s)) a) =
      algebraMap (presheafValue D₀)
        (Localization.Away ((imagePieceDatum D₀ T t hspan).s))
        (D₀.canonicalMap a) := by
  rw [genPiece_rel_forwardLocHom, IsLocalization.Away.lift_eq]
  rfl

set_option linter.unusedSectionVars false in
/-- **General relative piece, per-generator witnesses (G1-4)**: every
`t' ∈ T_inter` (a product `p·q`, `p ∈ insert D₀.s D₀.T`, `q ∈ insert t T`) has a
`locSubring`-witness over the B-side image datum: `y = aM(coe(p/s))·((im q)/(im t))`.
Uniform equation (no unit-juggling); only the membership splits on `q = t` vs `q ∈ T`. -/
theorem genPiece_rel_forward_witness
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (w : A) (hw : w ∈ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).T) :
    ∃ y : Localization.Away ((imagePieceDatum D₀ T t hspan).s),
      y ∈ locSubring (imagePieceDatum D₀ T t hspan).P
          (imagePieceDatum D₀ T t hspan).T (imagePieceDatum D₀ T t hspan).s ∧
      ((imagePieceDatum D₀ T t hspan).coeRingHom).comp
        (genPiece_rel_forwardLocHom D₀ T t hspan)
        (divByS w ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s)) =
      (imagePieceDatum D₀ T t hspan).coeRingHom y := by
  classical
  set DI := D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl with hDI
  set DB := imagePieceDatum D₀ T t hspan with hDB
  set F := (DB.coeRingHom).comp (genPiece_rel_forwardLocHom D₀ T t hspan) with hF
  have hF_alg : ∀ a : A, F (algebraMap A (Localization.Away DI.s) a) =
      DB.canonicalMap (D₀.canonicalMap a) := by
    intro a
    rw [hF, RingHom.comp_apply, genPiece_rel_forwardLocHom_algebraMap]
    rfl
  have hu : IsUnit (F (algebraMap A (Localization.Away DI.s) DI.s)) := by
    rw [hF_alg]
    exact (genPiece_rel_baseHom_isUnit D₀ T t hspan).map DB.coeRingHom
  have hF_div : ∀ (c : A) (z : presheafValue DB),
      F (algebraMap A (Localization.Away DI.s) c) =
        F (algebraMap A (Localization.Away DI.s) DI.s) * z →
      F (divByS c DI.s) = z := by
    intro c z hz
    have h1 : F (algebraMap A (Localization.Away DI.s) DI.s) * F (divByS c DI.s) =
        F (algebraMap A (Localization.Away DI.s) c) := by
      rw [← map_mul, algebraMap_s_mul_divByS]
    exact hu.mul_left_cancel (h1.trans hz)
  have hps : ∀ p : A, D₀.canonicalMap p =
      D₀.canonicalMap D₀.s * D₀.coeRingHom (divByS p D₀.s) :=
    canonicalMap_eq_canonicalMap_s_mul_coeRingHom_divByS D₀
  have hA₀ : ∀ p ∈ insert D₀.s D₀.T,
      D₀.coeRingHom (divByS p D₀.s) ∈ (presheafValue_concretePair D₀).A₀ :=
    fun p hp => coeRingHom_divByS_mem_concretePair_A₀ D₀ (Finset.mem_insert.mp hp)
  -- the B-side `q/t`-identity: `canMap_B (canMap q) = canMap_B (canMap t) · coe ((im q)/(im t))`
  -- the same `p/s`-factorisation as `hps`, one level up: `DB.s` is `D₀.canonicalMap t` by rfl
  have hqt : ∀ q : A, DB.canonicalMap (D₀.canonicalMap q) =
      DB.canonicalMap (D₀.canonicalMap t) *
        DB.coeRingHom (divByS (D₀.canonicalMap q) DB.s) := fun q =>
    canonicalMap_eq_canonicalMap_s_mul_coeRingHom_divByS DB (D₀.canonicalMap q)
  -- the witness membership for the `q`-factor
  have hq_mem : ∀ q ∈ insert t T,
      divByS (D₀.canonicalMap q) DB.s ∈ locSubring DB.P DB.T DB.s := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · have h1 : divByS (D₀.canonicalMap q) DB.s = 1 := by
        rw [show (DB.s : presheafValue D₀) = D₀.canonicalMap q from rfl]
        unfold divByS
        exact IsLocalization.mk'_self (M := Submonoid.powers (D₀.canonicalMap q))
          (S := Localization.Away (D₀.canonicalMap q)) ⟨1, pow_one _⟩
      rw [h1]
      exact one_mem _
    · refine divByS_mem_locSubring DB.P DB.T DB.s ?_
      show D₀.canonicalMap q ∈ T.image D₀.canonicalMap
      exact Finset.mem_image_of_mem _ hq'
  -- decompose `w = p · q`
  have hw' : w ∈ ((insert D₀.s D₀.T).product
      (insert t T)).image (fun r : A × A => r.1 * r.2) := hw
  rw [Finset.mem_image] at hw'
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := hw'
  have hp : p ∈ insert D₀.s D₀.T := (Finset.mem_product.mp hpq).1
  have hq : q ∈ insert t T := (Finset.mem_product.mp hpq).2
  rw [show (((p, q).1 : A) * (p, q).2 : A) = p * q from rfl]
  refine ⟨algebraMap (presheafValue D₀) (Localization.Away DB.s)
      (D₀.coeRingHom (divByS p D₀.s)) * divByS (D₀.canonicalMap q) DB.s,
    (locSubring DB.P DB.T DB.s).mul_mem
      (algebraMap_mem_locSubring DB.P DB.T DB.s (hA₀ p hp))
      (hq_mem q hq), ?_⟩
  refine hF_div _ _ ?_
  rw [hF_alg, hF_alg]
  rw [show DB.coeRingHom (algebraMap (presheafValue D₀) (Localization.Away DB.s)
      (D₀.coeRingHom (divByS p D₀.s)) * divByS (D₀.canonicalMap q) DB.s) =
    DB.canonicalMap (D₀.coeRingHom (divByS p D₀.s)) *
      DB.coeRingHom (divByS (D₀.canonicalMap q) DB.s) from by rw [map_mul]; rfl]
  rw [show ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s : A) =
    D₀.s * t from rfl]
  rw [map_mul (D₀.canonicalMap), map_mul (D₀.canonicalMap), map_mul (DB.canonicalMap),
    map_mul (DB.canonicalMap)]
  rw [show D₀.canonicalMap p = D₀.canonicalMap D₀.s *
    D₀.coeRingHom (divByS p D₀.s) from hps p]
  rw [map_mul (DB.canonicalMap), hqt q]
  ring

set_option linter.unusedSectionVars false in
/-- G1-5: forward continuity. -/
theorem genPiece_rel_forwardCompletion_continuous
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    @Continuous _ _ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).topology _
      (((imagePieceDatum D₀ T t hspan).coeRingHom).comp (genPiece_rel_forwardLocHom D₀ T t hspan)) := by
  classical
  set DI := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) with hDI
  set DB := (imagePieceDatum D₀ T t hspan) with hDB
  set F := (DB.coeRingHom).comp (genPiece_rel_forwardLocHom D₀ T t hspan) with hF
  have hF_alg : ∀ a : A, F (algebraMap A (Localization.Away DI.s) a) =
      DB.canonicalMap (D₀.canonicalMap a) := by
    intro a
    rw [hF, RingHom.comp_apply, genPiece_rel_forwardLocHom_algebraMap]
    rfl
  change @Continuous _ _ (locTopology DI.P DI.T DI.s DI.hopen) _ F
  refine locTopology_continuous_lift DI.P DI.T DI.s DI.hopen F ?_ ?_
  · have heq : F.comp (algebraMap A (Localization.Away DI.s)) =
        (DB.canonicalMap).comp D₀.canonicalMap := by
      ext a; exact hF_alg a
    rw [heq]
    exact (canonicalMap_continuous DB).comp (canonicalMap_continuous D₀)
  · intro w hw
    obtain ⟨y, hy_mem, hy_eq⟩ := genPiece_rel_forward_witness D₀ T t hspan w hw
    rw [show F (divByS w DI.s) = DB.coeRingHom y from hy_eq]
    have hbddB := CompletionLocalization.coeRingHom_image_locSubring_isBounded DB
    refine hbddB.subset ?_
    rintro _ ⟨k, rfl⟩
    exact ⟨y ^ k, pow_mem hy_mem k, by rw [map_pow]⟩

/-- G1-6: forward map. -/
noncomputable def genPiece_rel_forward
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    presheafValue (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) →+* presheafValue (imagePieceDatum D₀ T t hspan) := by
  letI : UniformSpace (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom
    (((imagePieceDatum D₀ T t hspan).coeRingHom).comp (genPiece_rel_forwardLocHom D₀ T t hspan))
    (genPiece_rel_forwardCompletion_continuous D₀ T t hspan)

/-- G1-6′ coe-tracking. -/
theorem genPiece_rel_forward_coe
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (y : Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) :
    genPiece_rel_forward D₀ T t hspan ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom y) =
      (imagePieceDatum D₀ T t hspan).coeRingHom (genPiece_rel_forwardLocHom D₀ T t hspan y) := by
  letI : UniformSpace (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe
    (((imagePieceDatum D₀ T t hspan).coeRingHom).comp (genPiece_rel_forwardLocHom D₀ T t hspan))
    (genPiece_rel_forwardCompletion_continuous D₀ T t hspan) y

set_option linter.unusedSectionVars false in
/-- G1-7a: backward base unit (the restriction of `canMap t` is a unit, dividing the
unit `canMap (D₀.s·t)`). -/
theorem genPiece_rel_backward_baseHom_isUnit
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    IsUnit ((restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
        (RationalLocData.interSamePair_subset_left _ _ _))
      ((imagePieceDatum D₀ T t hspan).s)) := by
  rw [show ((imagePieceDatum D₀ T t hspan).s : presheafValue D₀) = D₀.canonicalMap t from rfl]
  rw [restrictionMapHom_canonicalMap]
  have hu : IsUnit ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).canonicalMap ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s)) := isUnit_s_in_presheafValue _
  rw [show ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s : A) = D₀.s * t from rfl, map_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- G1-7b: backward loc-hom. -/
noncomputable def genPiece_rel_backwardLocHom
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    Localization.Away ((imagePieceDatum D₀ T t hspan).s) →+* presheafValue (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) :=
  IsLocalization.Away.lift
    (x := (imagePieceDatum D₀ T t hspan).s)
    (g := restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
      (RationalLocData.interSamePair_subset_left _ _ _))
    (genPiece_rel_backward_baseHom_isUnit D₀ T t hspan)

set_option linter.unusedSectionVars false in
/-- G1-7c: backward loc-hom tracking. -/
theorem genPiece_rel_backwardLocHom_algebraMap
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) (x : presheafValue D₀) :
    genPiece_rel_backwardLocHom D₀ T t hspan
        (algebraMap (presheafValue D₀) (Localization.Away ((imagePieceDatum D₀ T t hspan).s)) x) =
      restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
        (RationalLocData.interSamePair_subset_left _ _ _) x := by
  rw [genPiece_rel_backwardLocHom, IsLocalization.Away.lift_eq]

set_option linter.unusedSectionVars false in
/-- G1-7d: the `q/t`-generator identity in `O_X(D₀ ∩ R(T/t))`: `canMap_DI q` is
`canMap_DI t` times the image of `(D₀.s·q)/s_inter` (cancel the unit `canMap D₀.s`). -/
theorem genPiece_rel_canonicalMap_q_eq
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) (q : A) :
    (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).canonicalMap q =
      (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).canonicalMap t * (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom (divByS (D₀.s * q) (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := by
  set DI := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) with hDI
  have hchase : ∀ c : A, DI.canonicalMap DI.s * DI.coeRingHom (divByS c DI.s) =
      DI.canonicalMap c := by
    intro c
    rw [show DI.canonicalMap DI.s * DI.coeRingHom (divByS c DI.s) =
      DI.coeRingHom (algebraMap A (Localization.Away DI.s) DI.s *
        divByS c DI.s) from by rw [map_mul]; rfl]
    rw [algebraMap_s_mul_divByS]
    rfl
  have hsplit : DI.canonicalMap DI.s = DI.canonicalMap D₀.s * DI.canonicalMap t := by
    rw [show DI.canonicalMap DI.s = DI.canonicalMap (D₀.s * t) from by
      rw [show (DI.s : A) = D₀.s * t from rfl]]
    rw [map_mul]
  have hu_s : IsUnit (DI.canonicalMap D₀.s) := by
    have hu : IsUnit (DI.canonicalMap DI.s) := isUnit_s_in_presheafValue DI
    rw [hsplit] at hu
    exact isUnit_of_mul_isUnit_left hu
  refine hu_s.mul_left_cancel ?_
  have h2 := hchase (D₀.s * q)
  rw [hsplit] at h2
  calc DI.canonicalMap D₀.s * DI.canonicalMap q = DI.canonicalMap (D₀.s * q) := by
        rw [map_mul]
    _ = DI.canonicalMap D₀.s * DI.canonicalMap t *
        DI.coeRingHom (divByS (D₀.s * q) DI.s) := h2.symm
    _ = DI.canonicalMap D₀.s * (DI.canonicalMap t *
        DI.coeRingHom (divByS (D₀.s * q) DI.s)) := by ring

set_option linter.unusedSectionVars false in
/-- G1-7e: backward continuity (each image-generator `(im q)/(im t)` lands on the
ring-of-definition element `(D₀.s·q)/s_inter`). -/
theorem genPiece_rel_backwardLocHom_continuous
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    @Continuous _ _ (imagePieceDatum D₀ T t hspan).topology _
      (genPiece_rel_backwardLocHom D₀ T t hspan) := by
  classical
  set DI := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) with hDI
  set DB := (imagePieceDatum D₀ T t hspan) with hDB
  change @Continuous _ _ (locTopology DB.P DB.T DB.s DB.hopen) _
    (genPiece_rel_backwardLocHom D₀ T t hspan)
  refine locTopology_continuous_lift DB.P DB.T DB.s DB.hopen
    (genPiece_rel_backwardLocHom D₀ T t hspan) ?_ ?_
  · have heq : (genPiece_rel_backwardLocHom D₀ T t hspan).comp
        (algebraMap (presheafValue D₀) (Localization.Away DB.s)) =
        restrictionMapHom D₀ DI (RationalLocData.interSamePair_subset_left _ _ _) := by
      ext x; exact genPiece_rel_backwardLocHom_algebraMap D₀ T t hspan x
    rw [heq]
    exact restrictionMapHom_continuous D₀ DI _
  · intro w hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (hw : w ∈ T.image D₀.canonicalMap)
    have hu_b : IsUnit (genPiece_rel_backwardLocHom D₀ T t hspan
        (algebraMap (presheafValue D₀) (Localization.Away DB.s) DB.s)) := by
      rw [genPiece_rel_backwardLocHom_algebraMap]
      exact genPiece_rel_backward_baseHom_isUnit D₀ T t hspan
    have hwit : genPiece_rel_backwardLocHom D₀ T t hspan
        (divByS (D₀.canonicalMap q) DB.s) =
        DI.coeRingHom (divByS (D₀.s * q) DI.s) := by
      refine hu_b.mul_left_cancel ?_
      have h1 : genPiece_rel_backwardLocHom D₀ T t hspan
          (algebraMap (presheafValue D₀) (Localization.Away DB.s) DB.s) *
          genPiece_rel_backwardLocHom D₀ T t hspan
            (divByS (D₀.canonicalMap q) DB.s) =
          genPiece_rel_backwardLocHom D₀ T t hspan
            (algebraMap (presheafValue D₀) (Localization.Away DB.s)
              (D₀.canonicalMap q)) := by
        rw [← map_mul]
        congr 1
        exact algebraMap_s_mul_divByS DB (D₀.canonicalMap q)
      rw [h1, genPiece_rel_backwardLocHom_algebraMap,
        genPiece_rel_backwardLocHom_algebraMap]
      rw [show (DB.s : presheafValue D₀) = D₀.canonicalMap t from rfl]
      rw [restrictionMapHom_canonicalMap, restrictionMapHom_canonicalMap]
      exact genPiece_rel_canonicalMap_q_eq D₀ T t hspan q
    rw [hwit]
    have hbdd := CompletionLocalization.coeRingHom_image_locSubring_isBounded DI
    refine hbdd.subset ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨divByS (D₀.s * q) DI.s ^ k, pow_mem (divByS_mem_locSubring DI.P DI.T DI.s
      ?_) k, by rw [map_pow]⟩
    show D₀.s * q ∈ ((insert D₀.s D₀.T).product
      (insert t T)).image (fun r : A × A => r.1 * r.2)
    exact Finset.mem_image.mpr ⟨(D₀.s, q), Finset.mem_product.mpr
      ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hq⟩, rfl⟩

/-- G1-7f: backward map. -/
noncomputable def genPiece_rel_backward
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    presheafValue (imagePieceDatum D₀ T t hspan) →+* presheafValue (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) := by
  letI : UniformSpace (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom
    (genPiece_rel_backwardLocHom D₀ T t hspan)
    (genPiece_rel_backwardLocHom_continuous D₀ T t hspan)

/-- G1-7f′ coe-tracking. -/
theorem genPiece_rel_backward_coe
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (y : Localization.Away (imagePieceDatum D₀ T t hspan).s) :
    genPiece_rel_backward D₀ T t hspan ((imagePieceDatum D₀ T t hspan).coeRingHom y) =
      genPiece_rel_backwardLocHom D₀ T t hspan y := by
  letI : UniformSpace (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe
    (genPiece_rel_backwardLocHom D₀ T t hspan)
    (genPiece_rel_backwardLocHom_continuous D₀ T t hspan) y

set_option linter.unusedSectionVars false in
/-- G1-8a: loc-level restriction base unit (`D₀.s` divides the localized-away unit
`s_inter = D₀.s·t`). -/
theorem genPiece_rel_locRestriction_baseUnit
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    IsUnit (algebraMap A (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) D₀.s) := by
  have h2 : IsUnit (algebraMap A (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) D₀.s *
      algebraMap A (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) t) := by
    rw [← map_mul]
    rw [show ((D₀.s * t : A)) = (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s from rfl]
    exact IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s
  exact isUnit_of_mul_isUnit_left h2

/-- G1-8a′: loc-level restriction. -/
noncomputable def genPiece_rel_locRestriction
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    Localization.Away D₀.s →+* Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s :=
  IsLocalization.Away.lift (x := D₀.s)
    (g := algebraMap A (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s))
    (genPiece_rel_locRestriction_baseUnit D₀ T t hspan)

set_option linter.unusedSectionVars false in
/-- G1-8a″ tracking. -/
theorem genPiece_rel_locRestriction_algebraMap
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) (a : A) :
    genPiece_rel_locRestriction D₀ T t hspan
        (algebraMap A (Localization.Away D₀.s) a) =
      algebraMap A (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) a := by
  rw [genPiece_rel_locRestriction, IsLocalization.Away.lift_eq]

set_option linter.unusedSectionVars false in
/-- G1-8b: restriction factorization. -/
theorem genPiece_rel_restriction_factor
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    (restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
        (RationalLocData.interSamePair_subset_left _ _ _)).comp D₀.coeRingHom =
      ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom).comp (genPiece_rel_locRestriction D₀ T t hspan) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers D₀.s) ?_
  ext a
  simp only [RingHom.comp_apply]
  rw [show D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) a) =
    D₀.canonicalMap a from rfl, restrictionMapHom_canonicalMap,
    genPiece_rel_locRestriction_algebraMap]
  rfl

set_option linter.unusedSectionVars false in
/-- G1-8c: loc-level roundtrip 1. -/
theorem genPiece_rel_locRoundtrip1
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    (genPiece_rel_backwardLocHom D₀ T t hspan).comp
        (genPiece_rel_forwardLocHom D₀ T t hspan) =
      (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) ?_
  ext a
  simp only [RingHom.comp_apply]
  rw [genPiece_rel_forwardLocHom_algebraMap,
    genPiece_rel_backwardLocHom_algebraMap, restrictionMapHom_canonicalMap]
  rfl

set_option linter.unusedSectionVars false in
/-- G1-8d: loc-level roundtrip 2. -/
theorem genPiece_rel_locRoundtrip2
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    (genPiece_rel_forwardLocHom D₀ T t hspan).comp
        (genPiece_rel_locRestriction D₀ T t hspan) =
      (algebraMap (presheafValue D₀) (Localization.Away (imagePieceDatum D₀ T t hspan).s)).comp
        D₀.coeRingHom := by
  refine IsLocalization.ringHom_ext (Submonoid.powers D₀.s) ?_
  ext a
  simp only [RingHom.comp_apply]
  rw [genPiece_rel_locRestriction_algebraMap, genPiece_rel_forwardLocHom_algebraMap]
  rfl

set_option linter.unusedSectionVars false in
/-- G1-8e: `backward ∘ forward = id`. -/
theorem genPiece_rel_backward_forward
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (x : presheafValue (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)) :
    genPiece_rel_backward D₀ T t hspan (genPiece_rel_forward D₀ T t hspan x) = x := by
  letI : UniformSpace (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isUniformAddGroup
  letI : UniformSpace (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isUniformAddGroup
  refine @UniformSpace.Completion.ext'
    (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).uniformSpace
    (presheafValue (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)) _ _ _ _
    (UniformSpace.Completion.continuous_extension.comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ x
  intro a
  show genPiece_rel_backward D₀ T t hspan (genPiece_rel_forward D₀ T t hspan
    ((D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom a)) = (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom a
  rw [genPiece_rel_forward_coe, genPiece_rel_backward_coe]
  exact RingHom.congr_fun (genPiece_rel_locRoundtrip1 D₀ T t hspan) a

set_option linter.unusedSectionVars false in
/-- G1-8f: forward-restriction intertwining (the Prop 8.2 naturality). -/
theorem genPiece_rel_forward_restriction
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (x : presheafValue D₀) :
    genPiece_rel_forward D₀ T t hspan
        (restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
          (RationalLocData.interSamePair_subset_left _ _ _) x) =
      (imagePieceDatum D₀ T t hspan).canonicalMap x := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : UniformSpace (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isUniformAddGroup
  letI : UniformSpace (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isUniformAddGroup
  refine @UniformSpace.Completion.ext' (Localization.Away D₀.s) D₀.uniformSpace
    (presheafValue (imagePieceDatum D₀ T t hspan)) _ _ _ _
    (UniformSpace.Completion.continuous_extension.comp
      UniformSpace.Completion.continuous_extension)
    (canonicalMap_continuous (imagePieceDatum D₀ T t hspan)) ?_ x
  intro z
  show genPiece_rel_forward D₀ T t hspan
      (restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
        (RationalLocData.interSamePair_subset_left _ _ _) (D₀.coeRingHom z)) =
    (imagePieceDatum D₀ T t hspan).canonicalMap (D₀.coeRingHom z)
  rw [show restrictionMapHom D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
      (RationalLocData.interSamePair_subset_left _ _ _) (D₀.coeRingHom z) =
    (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).coeRingHom (genPiece_rel_locRestriction D₀ T t hspan z) from
    RingHom.congr_fun (genPiece_rel_restriction_factor D₀ T t hspan) z]
  rw [genPiece_rel_forward_coe]
  exact congrArg _ (RingHom.congr_fun (genPiece_rel_locRoundtrip2 D₀ T t hspan) z)

set_option linter.unusedSectionVars false in
/-- G1-8g: `forward ∘ backward = id`. -/
theorem genPiece_rel_forward_backward
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (y : presheafValue (imagePieceDatum D₀ T t hspan)) :
    genPiece_rel_forward D₀ T t hspan (genPiece_rel_backward D₀ T t hspan y) = y := by
  have hloc : (genPiece_rel_forward D₀ T t hspan).comp
      (genPiece_rel_backwardLocHom D₀ T t hspan) =
      (imagePieceDatum D₀ T t hspan).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (imagePieceDatum D₀ T t hspan).s) ?_
    ext x
    simp only [RingHom.comp_apply]
    rw [genPiece_rel_backwardLocHom_algebraMap, genPiece_rel_forward_restriction]
    rfl
  letI : UniformSpace (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).s) := (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl).isUniformAddGroup
  letI : UniformSpace (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).uniformSpace
  letI : IsTopologicalRing (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (imagePieceDatum D₀ T t hspan).s) := (imagePieceDatum D₀ T t hspan).isUniformAddGroup
  refine @UniformSpace.Completion.ext'
    (Localization.Away (imagePieceDatum D₀ T t hspan).s) (imagePieceDatum D₀ T t hspan).uniformSpace
    (presheafValue (imagePieceDatum D₀ T t hspan)) _ _ _ _
    (UniformSpace.Completion.continuous_extension.comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ y
  intro w
  show genPiece_rel_forward D₀ T t hspan (genPiece_rel_backward D₀ T t hspan
    ((imagePieceDatum D₀ T t hspan).coeRingHom w)) = (imagePieceDatum D₀ T t hspan).coeRingHom w
  rw [genPiece_rel_backward_coe]
  exact RingHom.congr_fun hloc w

/-- **The general relative-piece identification (Wedhorn Prop 8.2 / Remark 8.4)**:
the structure ring of `D₀ ∩ R(T/t)` is the structure ring of the image piece
`R(canMap T / canMap t)` over `B = 𝒪_X(D₀)`, for any ideal-generating `T`.
The R2-transport workhorse (T-R2-SECTION-COMPAT). -/
noncomputable def genPiece_relative_equiv
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    presheafValue (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl) ≃+* presheafValue (imagePieceDatum D₀ T t hspan) :=
  RingEquiv.ofRingHom (genPiece_rel_forward D₀ T t hspan)
    (genPiece_rel_backward D₀ T t hspan)
    (RingHom.ext (genPiece_rel_forward_backward D₀ T t hspan))
    (RingHom.ext (genPiece_rel_backward_forward D₀ T t hspan))

set_option linter.unusedSectionVars false in
/-- The general relative-piece iso intertwines restriction with `canonicalMap` over `B`
(Wedhorn Prop 8.2 base-change naturality; the transport-compatibility). -/
theorem genPiece_relative_equiv_restrictionMap
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (T : Finset A) (t : A)
    (hspan : Ideal.span (T : Set A) = ⊤)
    (x : presheafValue D₀) :
    genPiece_relative_equiv D₀ T t hspan
        (restrictionMap D₀ (D₀.interSamePair (genPieceDatum D₀.P T t hspan) rfl)
          (RationalLocData.interSamePair_subset_left _ _ _) x) =
      (imagePieceDatum D₀ T t hspan).canonicalMap x :=
  genPiece_rel_forward_restriction D₀ T t hspan x

/-- The image-span proof at the `Finset`-coe form (helper for the B-cover). -/
theorem imageGenCover_span
    (D₀ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] [DecidableEq (presheafValue D₀)] (T : Finset A)
    (hspan : Ideal.span (T : Set A) = ⊤) :
    Ideal.span ((T.image D₀.canonicalMap : Finset (presheafValue D₀)) :
      Set (presheafValue D₀)) = ⊤ := by
  rw [Finset.coe_image]
  exact span_image_canonicalMap_eq_top D₀ T hspan

set_option linter.unusedSectionVars false in
/-- **THE 8.16-KEYSTONE (Wedhorn Prop 8.16 / Prop 8.2, [Hu2] 1.4.4)**: for a
rational piece `E` inside `D₀` (with the rational-subset span condition of
Wedhorn Def 7.29), the section ring `𝒪_X(E)` is canonically isomorphic to the
`B`-side section ring of the image datum `R_B(im E.T / im E.s)`,
`B := 𝒪_X(D₀)`. This is the general-piece base change behind BOTH "we may
assume X = V" (Prop 8.30's opening, wedhorn.txt:4099) and the R2-transport
of acyclicity to general bases.

Factors through two PROVEN pieces: the open-equality
`E ≈ D₀ ∩ R(E.T/E.s)` (restriction-bijectivity between open-equal data) and
the relative-piece equivalence `genPiece_relative_equiv` (the
Example-6.38-template machinery, G1). -/
noncomputable def relativePiece_equiv
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ E : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)]
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)
    (hspanE : Ideal.span (E.T : Set A) = ⊤) :
    presheafValue E ≃+* presheafValue (imagePieceDatum D₀ E.T E.s hspanE) :=
  have h_eq : rationalOpen E.T E.s =
      rationalOpen (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).T
        (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).s := by
    -- v4.33: `rw [interSamePair_rationalOpen]` fails to match through the goal's embedded
    -- `rfl : (genPieceDatum …).P = D₀.P` (re-checked at reducible transparency). Apply the
    -- lemma with an explicit `genPieceDatum_P` proof instead and compose by `Eq.trans`.
    have h := RationalLocData.interSamePair_rationalOpen D₀
      (genPieceDatum D₀.P E.T E.s hspanE) (genPieceDatum_P D₀.P E.T E.s hspanE)
    rw [genPieceDatum_T, genPieceDatum_s] at h
    exact (h.trans (Set.inter_eq_right.mpr hE_sub)).symm
  (RingEquiv.ofBijective
    (restrictionMapHom E
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl) h_eq.symm.le)
    (restrictionMap_bijective_of_rationalOpen_eq E
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl) h_eq)).trans
    (genPiece_relative_equiv D₀ E.T E.s hspanE)

set_option linter.unusedSectionVars false in
/-- The 8.16-keystone intertwines the canonical maps: restricting `x : 𝒪_X(D₀)`
to `E` and passing to the `B`-side equals the `B`-side canonical map of `x`
(Wedhorn Prop 8.2 base-change naturality, general-piece form). -/
theorem relativePiece_equiv_restrictionMap
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ E : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)]
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)
    (hspanE : Ideal.span (E.T : Set A) = ⊤)
    (x : presheafValue D₀) :
    relativePiece_equiv D₀ E hE_sub hspanE
        (restrictionMap D₀ E hE_sub x) =
      (imagePieceDatum D₀ E.T E.s hspanE).canonicalMap x := by
  have h_eq : rationalOpen E.T E.s =
      rationalOpen (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).T
        (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).s := by
    -- v4.33: `rw [interSamePair_rationalOpen]` fails to match through the goal's embedded
    -- `rfl : (genPieceDatum …).P = D₀.P` (re-checked at reducible transparency). Apply the
    -- lemma with an explicit `genPieceDatum_P` proof instead and compose by `Eq.trans`.
    have h := RationalLocData.interSamePair_rationalOpen D₀
      (genPieceDatum D₀.P E.T E.s hspanE) (genPieceDatum_P D₀.P E.T E.s hspanE)
    rw [genPieceDatum_T, genPieceDatum_s] at h
    exact (h.trans (Set.inter_eq_right.mpr hE_sub)).symm
  show genPiece_relative_equiv D₀ E.T E.s hspanE
      (restrictionMapHom E
        (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl) h_eq.symm.le
        (restrictionMap D₀ E hE_sub x)) =
    (imagePieceDatum D₀ E.T E.s hspanE).canonicalMap x
  have hcomp : restrictionMapHom E
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl) h_eq.symm.le
      (restrictionMap D₀ E hE_sub x) =
      restrictionMap D₀
        (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl)
        (RationalLocData.interSamePair_subset_left _ _ _) x :=
    congrFun (restrictionMap_comp D₀ E
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl)
      hE_sub h_eq.symm.le) x
  rw [hcomp]
  exact genPiece_relative_equiv_restrictionMap D₀ E.T E.s hspanE x

set_option linter.unusedSectionVars false in
/-- **The comap characterisation of image-piece opens** (Wedhorn Prop 8.2 +
Remark 8.4: the homeomorphism `Spa B ≅ U` matches rational subsets, [Hu2] 1.4.4):
a point of `Spv B` lies in the image piece's rational open iff it is a Spa-`B`
point whose `A`-shadow lies in the original piece's rational open. The conditions
transport verbatim through `comap_vle` (an equality of propositions). -/
theorem imagePieceDatum_mem_rationalOpen_iff
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ E : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)] (hspanE : Ideal.span (E.T : Set A) = ⊤)
    (w : Spv (presheafValue D₀)) :
      haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
    haveI : DecidableEq (presheafValue D₀) := Classical.decEq _
    (w ∈ rationalOpen (imagePieceDatum D₀ E.T E.s hspanE).T
        (imagePieceDatum D₀ E.T E.s hspanE).s ↔
      w ∈ Spa (presheafValue D₀) (presheafValue D₀)⁺ ∧
        comap D₀.canonicalMap w ∈ rationalOpen E.T E.s) := by
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  letI : DecidableEq (presheafValue D₀) := Classical.decEq _
  have hT : (imagePieceDatum D₀ E.T E.s hspanE).T = E.T.image D₀.canonicalMap := rfl
  have hs : (imagePieceDatum D₀ E.T E.s hspanE).s = D₀.canonicalMap E.s := rfl
  constructor
  · rintro ⟨hspa, hcond, hnz⟩
    refine ⟨hspa, comap_mem_spa (canonicalMap_continuous D₀)
      D₀.canonicalMap_integral hspa, fun t ht => ?_, fun h0 => ?_⟩
    · rw [comap_vle]
      have := hcond (D₀.canonicalMap t) (by rw [hT]; exact Finset.mem_image_of_mem _ ht)
      rwa [hs] at this
    · rw [comap_vle, map_zero] at h0
      rw [hs] at hnz
      exact hnz h0
  · rintro ⟨hspa, -, hcond, hnz⟩
    refine ⟨hspa, fun x hx => ?_, fun h0 => ?_⟩
    · rw [hT, Finset.mem_image] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      rw [hs]
      have := hcond t ht
      rwa [comap_vle] at this
    · rw [hs] at h0
      exact hnz (by rw [comap_vle, map_zero]; exact h0)

set_option linter.unusedSectionVars false in
/-- Image pieces preserve containment of rational opens (Wedhorn Remark 8.4). -/
theorem imagePieceDatum_rationalOpen_mono
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ E E' : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)]
    (hspanE : Ideal.span (E.T : Set A) = ⊤)
    (hspanE' : Ideal.span (E'.T : Set A) = ⊤)
    (h : rationalOpen E'.T E'.s ⊆ rationalOpen E.T E.s) :
      haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
    rationalOpen (imagePieceDatum D₀ E'.T E'.s hspanE').T
        (imagePieceDatum D₀ E'.T E'.s hspanE').s ⊆
      rationalOpen (imagePieceDatum D₀ E.T E.s hspanE).T
        (imagePieceDatum D₀ E.T E.s hspanE).s := by
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  intro w hw
  rw [imagePieceDatum_mem_rationalOpen_iff] at hw ⊢
  exact ⟨hw.1, h hw.2⟩

set_option linter.unusedSectionVars false in
/-- Image pieces match intersections of rational opens (Wedhorn Remark 8.4). -/
theorem imagePieceDatum_rationalOpen_inter
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ E₁ E₂ E₃ : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)]
    (hspanE₁ : Ideal.span (E₁.T : Set A) = ⊤)
    (hspanE₂ : Ideal.span (E₂.T : Set A) = ⊤)
    (hspanE₃ : Ideal.span (E₃.T : Set A) = ⊤)
    (h₃ : rationalOpen E₃.T E₃.s =
      rationalOpen E₁.T E₁.s ∩ rationalOpen E₂.T E₂.s) :
      haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
    rationalOpen (imagePieceDatum D₀ E₃.T E₃.s hspanE₃).T
        (imagePieceDatum D₀ E₃.T E₃.s hspanE₃).s =
      rationalOpen (imagePieceDatum D₀ E₁.T E₁.s hspanE₁).T
          (imagePieceDatum D₀ E₁.T E₁.s hspanE₁).s ∩
        rationalOpen (imagePieceDatum D₀ E₂.T E₂.s hspanE₂).T
          (imagePieceDatum D₀ E₂.T E₂.s hspanE₂).s := by
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  ext w
  rw [Set.mem_inter_iff, imagePieceDatum_mem_rationalOpen_iff,
    imagePieceDatum_mem_rationalOpen_iff, imagePieceDatum_mem_rationalOpen_iff, h₃]
  constructor
  · rintro ⟨hspa, h₁, h₂⟩
    exact ⟨⟨hspa, h₁⟩, hspa, h₂⟩
  · rintro ⟨⟨hspa, h₁⟩, -, h₂⟩
    exact ⟨hspa, h₁, h₂⟩

set_option linter.unusedSectionVars false in
/-- **The keystone restriction square** (Wedhorn Prop 8.16 naturality for nested
pieces, [Hu2] 1.4.4): for rational pieces `E' ⊆ E ⊆ D₀` the base-change
isomorphisms intertwine the `A`-side and `B`-side restriction maps:

```
        𝒪_X(E)  ──restrict──→  𝒪_X(E')
          ≃ keystone_E            ≃ keystone_E'
        𝒪_B(im E) ─restrict─→  𝒪_B(im E')
```

**Proof recipe (G1/G3b)**: both composites are continuous ring homomorphisms
`𝒪_X(E) → 𝒪_B(im E')`; they agree on the canonical `A`-image by
`relativePiece_equiv_restrictionMap` + `restrictionMapHom_canonicalMap` (both
sides send `(canonicalMap E a)` to `(im E').canonicalMap (D₀.canonicalMap a)`-
style values), hence on the dense localization image (ring homs preserve the
inverted `E.s`), hence everywhere by continuity + `T2`. Same 8-step stack as
`genPiece_relative_equiv`'s G3b overlap squares. -/
theorem relativePiece_equiv_restrict_square
    [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A] [IsRingOfIntegralElements (A⁺)]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ E E' : RationalLocData A)
    [IsTateRing (presheafValue D₀)] [IsNoetherianRing (presheafValue D₀)]
    [IsStronglyNoetherian (presheafValue D₀)]
    (hE_sub : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s)
    (hE'_sub : rationalOpen E'.T E'.s ⊆ rationalOpen E.T E.s)
    (hspanE : Ideal.span (E.T : Set A) = ⊤)
    (hspanE' : Ideal.span (E'.T : Set A) = ⊤)
    (y : presheafValue E) :
      haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
    haveI : @CompleteSpace (presheafValue D₀)
        (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)) :=
      presheafValue_completeSpace_rightUniformSpace D₀
    haveI : HasLocLiftPowerBounded (presheafValue D₀) := hasLocLiftPowerBounded_faithful
    relativePiece_equiv D₀ E' (hE'_sub.trans hE_sub) hspanE'
        (restrictionMap E E' hE'_sub y) =
      restrictionMap (imagePieceDatum D₀ E.T E.s hspanE)
        (imagePieceDatum D₀ E'.T E'.s hspanE')
        (imagePieceDatum_rationalOpen_mono D₀ E E' hspanE hspanE' hE'_sub)
        (relativePiece_equiv D₀ E hE_sub hspanE y) := by
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  haveI : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)) :=
    presheafValue_completeSpace_rightUniformSpace D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hasLocLiftPowerBounded_faithful
  haveI : IsHuberRing (presheafValue D₀) := IsTateRing.toIsHuberRing
  -- both composites, postcomposed with `E.coeRingHom`, agree as ring homs out of
  -- the localization (determined on the `algebraMap`-range by the trackings)
  have hloc :
      ((relativePiece_equiv D₀ E' (hE'_sub.trans hE_sub) hspanE') :
          presheafValue E' →+* presheafValue (imagePieceDatum D₀ E'.T E'.s hspanE')).comp
        ((restrictionMapHom E E' hE'_sub).comp E.coeRingHom) =
      ((restrictionMapHom (imagePieceDatum D₀ E.T E.s hspanE)
          (imagePieceDatum D₀ E'.T E'.s hspanE')
          (imagePieceDatum_rationalOpen_mono D₀ E E' hspanE hspanE' hE'_sub)).comp
        (((relativePiece_equiv D₀ E hE_sub hspanE) :
          presheafValue E →+* presheafValue (imagePieceDatum D₀ E.T E.s hspanE)).comp
          E.coeRingHom)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers E.s) ?_
    ext a
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
    rw [show E.coeRingHom (algebraMap A (Localization.Away E.s) a) =
      E.canonicalMap a from rfl]
    rw [restrictionMapHom_canonicalMap E E' hE'_sub a]
    rw [show (E'.canonicalMap a : presheafValue E') =
        restrictionMapHom D₀ E' (hE'_sub.trans hE_sub) (D₀.canonicalMap a) from
      (restrictionMapHom_canonicalMap D₀ E' (hE'_sub.trans hE_sub) a).symm]
    rw [show (E.canonicalMap a : presheafValue E) =
        restrictionMapHom D₀ E hE_sub (D₀.canonicalMap a) from
      (restrictionMapHom_canonicalMap D₀ E hE_sub a).symm]
    rw [show (relativePiece_equiv D₀ E' (hE'_sub.trans hE_sub) hspanE')
          (restrictionMapHom D₀ E' (hE'_sub.trans hE_sub) (D₀.canonicalMap a)) =
        (imagePieceDatum D₀ E'.T E'.s hspanE').canonicalMap (D₀.canonicalMap a) from
      relativePiece_equiv_restrictionMap D₀ E' (hE'_sub.trans hE_sub) hspanE'
        (D₀.canonicalMap a)]
    rw [show (relativePiece_equiv D₀ E hE_sub hspanE)
          (restrictionMapHom D₀ E hE_sub (D₀.canonicalMap a)) =
        (imagePieceDatum D₀ E.T E.s hspanE).canonicalMap (D₀.canonicalMap a) from
      relativePiece_equiv_restrictionMap D₀ E hE_sub hspanE (D₀.canonicalMap a)]
    exact (restrictionMapHom_canonicalMap (imagePieceDatum D₀ E.T E.s hspanE)
      (imagePieceDatum D₀ E'.T E'.s hspanE')
      (imagePieceDatum_rationalOpen_mono D₀ E E' hspanE hspanE' hE'_sub)
      (D₀.canonicalMap a)).symm
  -- extend along the dense localization image by continuity (both composites are
  -- compositions of completion extensions) + T2
  letI : UniformSpace (Localization.Away E.s) := E.uniformSpace
  letI : IsTopologicalRing (Localization.Away E.s) := E.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away E.s) := E.isUniformAddGroup
  letI : UniformSpace (Localization.Away E'.s) := E'.uniformSpace
  letI : IsTopologicalRing (Localization.Away E'.s) := E'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away E'.s) := E'.isUniformAddGroup
  letI : UniformSpace (Localization.Away
      (D₀.interSamePair (genPieceDatum D₀.P E'.T E'.s hspanE') rfl).s) :=
    (D₀.interSamePair (genPieceDatum D₀.P E'.T E'.s hspanE') rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away
      (D₀.interSamePair (genPieceDatum D₀.P E'.T E'.s hspanE') rfl).s) :=
    (D₀.interSamePair (genPieceDatum D₀.P E'.T E'.s hspanE') rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away
      (D₀.interSamePair (genPieceDatum D₀.P E'.T E'.s hspanE') rfl).s) :=
    (D₀.interSamePair (genPieceDatum D₀.P E'.T E'.s hspanE') rfl).isUniformAddGroup
  letI : UniformSpace (Localization.Away
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).s) :=
    (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).uniformSpace
  letI : IsTopologicalRing (Localization.Away
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).s) :=
    (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away
      (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).s) :=
    (D₀.interSamePair (genPieceDatum D₀.P E.T E.s hspanE) rfl).isUniformAddGroup
  letI : UniformSpace (Localization.Away (imagePieceDatum D₀ E.T E.s hspanE).s) :=
    (imagePieceDatum D₀ E.T E.s hspanE).uniformSpace
  letI : IsTopologicalRing
      (Localization.Away (imagePieceDatum D₀ E.T E.s hspanE).s) :=
    (imagePieceDatum D₀ E.T E.s hspanE).isTopologicalRing
  letI : IsUniformAddGroup
      (Localization.Away (imagePieceDatum D₀ E.T E.s hspanE).s) :=
    (imagePieceDatum D₀ E.T E.s hspanE).isUniformAddGroup
  refine @UniformSpace.Completion.ext' (Localization.Away E.s) E.uniformSpace
    (presheafValue (imagePieceDatum D₀ E'.T E'.s hspanE')) _ _ _ _
    (UniformSpace.Completion.continuous_extension.comp
      (UniformSpace.Completion.continuous_extension.comp
        UniformSpace.Completion.continuous_extension))
    (UniformSpace.Completion.continuous_extension.comp
      (UniformSpace.Completion.continuous_extension.comp
        UniformSpace.Completion.continuous_extension))
    ?_ y
  intro z
  exact RingHom.congr_fun hloc z
end GenKeystone

end ValuationSpectrum

end
