/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».SheafyPair
import «Adic spaces».WedhornCechAcyclicity

/-!
# Pair-level and ring-level sheafiness; the strongly noetherian Tate theorems

The literature-facing sheafiness API (Wedhorn Definition 8.26, Kedlaya Remarks
1.6.8–1.6.10), on top of the C-phase equivalence `isSheafy_iff_isLimitSheaf`:

* `IsSheafyFor A Aplus` — **pair-level sheafiness** for an explicit **bundled valid**
  choice `Aplus : RingOfIntegralElements A`: the genuine all-open projective-limit
  structure presheaf of `Spa (A, Aplus)` is a sheaf of topological rings. Defined at
  the complete analytic (Tate) scope — exactly where Wedhorn's restriction maps exist
  (Prop 8.2 via 7.52(2)) — with the restriction-map package **derived** from that
  scope (`hasLocLiftPowerBounded_faithful`), so `HasLocLiftPowerBounded` appears
  *nowhere*: not as a hypothesis, not existentially, not in `#check`.
* `IsSheafyComplete A` — the complete-ring specialization of Definition 8.26
  (*every* valid choice gives a sheafy pair; for complete `A`, `Â = A` and this is
  the ring-level definition verbatim).
* `CompletionModel A P` — the project's completion `Â = 𝒪_X(X) = presheafValue
  (globalLocData P)` (Wedhorn Remark 8.3) with its **fully populated** instance stack
  (complete, T2, Huber, nonarchimedean; Tate when `A` is — all completeness-free in
  `A`), and `IsSheafyRing A` — the **literal general Definition 8.26**: every ring of
  integral elements of the completion gives a sheafy pair of the completion. No
  instance parameters remain.
* `isSheafyFor_of_stronglyNoetherianTate` / `isSheafyComplete_of_stronglyNoetherianTate`
  — **the principal theorems** (Wedhorn Theorem 8.28(b) in the genuine all-open
  vocabulary): a complete strongly noetherian Tate ring is sheafy for **every** valid
  ring of integral elements. `isSheafyRing_of_stronglyNoetherianTate` — the literal
  completion-based form, through the transport of the Tate/strongly-noetherian
  structure to `Â`. No `CompatiblePlusSubring`, no `HasLocLiftPowerBounded`, no
  `IsDomain` anywhere.
* `isSheafyFor_congr_of_stronglyNoetherianTate` — `A⁺`-independence at the 8.28(b)
  target scope (Kedlaya Remark 1.6.9's conclusion), with a non-definitionally-equal
  regression example; no identification of the `Spa` spaces is used, and **no
  nonanalytic independence is claimed** (Remark 1.6.10).
* `StandardCoverData` / `StandardSheafCondition` — the `A⁺`-free standard condition
  (`Spa`-uniform covers; populated by the generation construction in
  `StandardRefinement.lean`), with the provable comparison direction
  `standardSheafCondition_of_isSheafyComplete`. The converse for *generic* complete
  Tate rings is the standard-cover cofinality (Kedlaya Lemma 1.6.8) whose general
  branch is the recorded missing API (`WedhornStandardCoverRefinement.lean`) — not on
  the dependency path of anything here.

## Scope notes (honest boundaries)

The non-complete form of the ring-level 8.28(b) wrapper reduces to a **single**
missing transport: `IsStronglyNoetherian A → IsStronglyNoetherian (CompletionModel A P)`
for non-complete `A` (the project's `presheafValue_isStronglyNoetherian_faithful`
proves it inside the complete section; its `CompleteSpace A` hypothesis would need to
be discharged from its proof chain). Everything else — completeness, T2,
nonarchimedean, Huber, Tate — transports completeness-free (this file). See
`docs/SHEAFY-LIVE-AUDIT-2026-07-19.md`.
-/

noncomputable section

open TopologicalSpace

namespace ValuationSpectrum

universe u

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-! ### Pair-level sheafiness for an explicit valid choice -/

/-- **Pair-level sheafiness** (Wedhorn Definition 8.26 for one affinoid pair, in the
genuine all-open vocabulary): the pair `(A, Aplus)` — with `Aplus` a **bundled ring of
integral elements**, so invalid bare subrings cannot be supplied — is sheafy when the
genuine projective-limit structure presheaf on all opens of `Spa (A, Aplus)` is a
sheaf of topological rings (`IsLimitSheaf`: separation + gluing + the arbitrary-cover
topological-embedding condition of Wedhorn Remark 8.20).

Defined at the complete analytic scope, which is where the canonical restriction maps
exist (Wedhorn Prop 8.2 via 7.52(2)); their existence-and-continuity package is
**derived** here (`hasLocLiftPowerBounded_faithful` — a theorem, not an assumption),
so no `HasLocLiftPowerBounded` appears in this definition or anywhere downstream. -/
def IsSheafyFor (Aplus : RingOfIntegralElements A) : Prop :=
  letI := Aplus.toPlusSubring
  haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
  haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  IsLimitSheaf A

/-- **The complete-ring specialization of Wedhorn Definition 8.26**: `A` is sheafy
when *every* ring of integral elements of `A` gives a sheafy pair. For complete `A`
(the ambient scope) `Â = A`, so this is the ring-level definition verbatim; the
universal quantifier over valid choices is retained (handover P4). -/
def IsSheafyComplete : Prop :=
  ∀ Aplus : RingOfIntegralElements A, IsSheafyFor A Aplus

/-! ### The strongly noetherian Tate theorems (Wedhorn Theorem 8.28(b), complete case,
in the genuine all-open vocabulary) -/

variable {A}

/-- **The principal pair-level theorem**: a complete strongly noetherian Tate ring is
sheafy for **every explicit valid choice** of ring of integral elements — the genuine
all-open projective-limit structure presheaf of `Spa (A, Aplus)` is a sheaf of
topological rings. Assembled from the (instance-generic, axiom-clean)
`isSheafy_of_stronglyNoetherian_828b` and the C-phase equivalence
`isLimitSheaf_of_isSheafy`. No `CompatiblePlusSubring`, `HasLocLiftPowerBounded`,
or `IsDomain` hypotheses appear. -/
theorem isSheafyFor_of_stronglyNoetherianTate [IsStronglyNoetherian A]
    (Aplus : RingOfIntegralElements A) : IsSheafyFor A Aplus := by
  classical
  letI := Aplus.toPlusSubring
  haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
  letI : IsNoetherianRing A := IsStronglyNoetherian.isNoetherianRing A
  haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  haveI : IsSheafy A := isSheafy_of_stronglyNoetherian_828b
  show IsLimitSheaf A
  exact isLimitSheaf_of_isSheafy

/-- **The principal ring-level theorem** (Wedhorn Theorem 8.28(b), complete case): a
complete strongly noetherian Tate ring satisfies the universal (Definition 8.26)
sheafiness — *every* valid ring of integral elements gives a sheafy pair, with the
genuine structure presheaf and projective-limit topology. -/
theorem isSheafyComplete_of_stronglyNoetherianTate [IsStronglyNoetherian A] :
    IsSheafyComplete A :=
  fun Aplus => isSheafyFor_of_stronglyNoetherianTate Aplus

/-- **`A⁺`-independence at the 8.28(b) target scope** (Kedlaya Remark 1.6.9's
conclusion for complete strongly noetherian Tate rings): any two valid choices —
related by no hypothesis whatsoever, in particular non-definitionally-equal ones —
give equivalent pair-level sheafiness. No identification of the underlying
`Spa (A, Aplus₁)` and `Spa (A, Aplus₂)` is used or asserted. -/
theorem isSheafyFor_congr_of_stronglyNoetherianTate [IsStronglyNoetherian A]
    (Aplus Bplus : RingOfIntegralElements A) :
    IsSheafyFor A Aplus ↔ IsSheafyFor A Bplus :=
  iff_of_true (isSheafyFor_of_stronglyNoetherianTate Aplus)
    (isSheafyFor_of_stronglyNoetherianTate Bplus)

/-- Regression (handover P4 gate — non-definitionally-equal choices): the
independence statement applies to two choices assumed *distinct*. -/
example [IsStronglyNoetherian A] (Aplus Bplus : RingOfIntegralElements A)
    (_ : Aplus ≠ Bplus) :
    IsSheafyFor A Aplus ↔ IsSheafyFor A Bplus :=
  isSheafyFor_congr_of_stronglyNoetherianTate Aplus Bplus

end ValuationSpectrum

/-! ### The completion model and the literal Definition 8.26 -/

namespace ValuationSpectrum

universe v

section CompletionModel

variable (A : Type v) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A]

/-- **The completion `Â` of a Huber ring**, realized by the project's completion
functor at the whole-space datum: `Â = 𝒪_X(X) = presheafValue (globalLocData P)`
(Wedhorn Remark 8.3). All instances below are completeness-free in `A`. -/
def CompletionModel (P : PairOfDefinition A) : Type v :=
  presheafValue (globalLocData P)

instance (P : PairOfDefinition A) : CommRing (CompletionModel A P) :=
  inferInstanceAs (CommRing (presheafValue (globalLocData P)))

instance (P : PairOfDefinition A) : TopologicalSpace (CompletionModel A P) :=
  inferInstanceAs (TopologicalSpace (presheafValue (globalLocData P)))

instance (P : PairOfDefinition A) : IsTopologicalRing (CompletionModel A P) :=
  inferInstanceAs (IsTopologicalRing (presheafValue (globalLocData P)))

instance (P : PairOfDefinition A) : T2Space (CompletionModel A P) :=
  inferInstanceAs (T2Space (presheafValue (globalLocData P)))

/-- `Â` is Huber: the concrete pair of definition of the completed rational
localization (`presheafValue_concretePair`) — completeness-free in `A`. -/
instance (P : PairOfDefinition A) : IsHuberRing (CompletionModel A P) :=
  ⟨⟨presheafValue_concretePair (globalLocData P)⟩⟩

/-- `Â` is nonarchimedean (the completion of a nonarchimedean group). -/
instance (P : PairOfDefinition A) : NonarchimedeanRing (CompletionModel A P) :=
  { is_nonarchimedean :=
      ((globalLocData P).nonarchimedeanAddGroup_presheafValue).is_nonarchimedean }

/-- `Â` is complete for its canonical (right) uniformity. -/
instance (P : PairOfDefinition A) :
    letI : UniformSpace (CompletionModel A P) :=
      IsTopologicalAddGroup.rightUniformSpace (CompletionModel A P)
    CompleteSpace (CompletionModel A P) :=
  presheafValue_completeSpace_rightUniformSpace (globalLocData P)

/-- `Â` of a Tate ring is Tate — **completeness-free** restatement of the faithful
transport: the pair of definition is `presheafValue_concretePair` and the
topologically nilpotent unit is `presheafValue_topNilUnit`, both parameterised by the
datum alone. -/
instance [IsTateRing A] (P : PairOfDefinition A) : IsTateRing (CompletionModel A P) where
  exists_pairOfDefinition := ⟨presheafValue_concretePair (globalLocData P)⟩
  exists_topologicallyNilpotent_unit := presheafValue_topNilUnit (globalLocData P)

variable [IsTateRing A]

/-- **Wedhorn Definition 8.26, literal general form** (fully populated — no instance
parameters): a Tate ring `A` is *sheafy* when, for every pair of definition `P` and
every ring of integral elements `Bplus` of the completion `Â = CompletionModel A P`,
the pair `(Â, Bplus)` is sheafy — i.e. the genuine all-open structure presheaf of
`Spa (Â, Bplus)` is a sheaf of topological rings. Quantifying over `P` keeps the
definition choice-free; all models are the completion of `A` (Remark 8.3). -/
def IsSheafyRing : Prop :=
  ∀ (P : PairOfDefinition A) (Bplus : RingOfIntegralElements (CompletionModel A P)),
    IsSheafyFor (CompletionModel A P) Bplus

end CompletionModel

section CompletionTheorem

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [IsTateRing A] [IsNoetherianRing A]
  [IsStronglyNoetherian A] [T2Space A] [NonarchimedeanRing A]
  [HasLocLiftPowerBounded A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-- The strongly noetherian structure transports to the completion model (the
project's faithful transport at the whole-space datum; stated inside the complete
analytic scope — removing `CompleteSpace A` from this transport is the single
remaining input for the non-complete ring-level wrapper, see the module docstring). -/
theorem completionModel_isStronglyNoetherian (P : PairOfDefinition A) :
    IsStronglyNoetherian (CompletionModel A P) :=
  presheafValue_isStronglyNoetherian_faithful (globalLocData P)

/-- **The literal completion-based Theorem 8.28(b)** (Wedhorn Definition 8.26 over
`Â`): a complete strongly noetherian Tate ring is sheafy in the ring-level sense —
for every pair of definition and **every** ring of integral elements of the
completion, the completed pair is sheafy with the genuine all-open structure presheaf.
(Note this is a statement about the pairs of `Â`, not of `A`; it complements
`isSheafyComplete_of_stronglyNoetherianTate`, which handles the pairs of `A` itself.) -/
theorem isSheafyRing_of_stronglyNoetherianTate : IsSheafyRing A := by
  intro P Bplus
  haveI : IsStronglyNoetherian (CompletionModel A P) :=
    completionModel_isStronglyNoetherian P
  exact isSheafyFor_of_stronglyNoetherianTate Bplus

end CompletionTheorem

end ValuationSpectrum

/-! ### Standard covers and the `A⁺`-free standard sheaf condition -/

namespace ValuationSpectrum

universe w

variable {A : Type w} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- A finite rational cover datum whose subordination/covering conditions are
**`Spa`-uniform** (pointwise in the valuation, no `A⁺`-membership test) — Kedlaya's
standard rational coverings are of this form (`StandardRefinement.lean` provides the
generation construction). Consequently a standard datum instantiates as a
`RationalCovering` at **every** choice of `A⁺` simultaneously (`toCovering`) —
Kedlaya Remark 1.6.9's mechanism. -/
structure StandardCoverData (A : Type w) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] where
  /-- The base rational localization datum. -/
  base : RationalLocData A
  /-- The covering data. -/
  covers : Finset (RationalLocData A)
  /-- The base is valid (Wedhorn Definition 7.29). -/
  base_isRational : base.IsRational
  /-- The pieces are valid. -/
  covers_isRational : ∀ D ∈ covers, D.IsRational
  /-- Subordination, uniformly in the valuation. -/
  subset_uniform : ∀ D ∈ covers, ∀ v : Spv A,
    ((∀ t ∈ D.T, v.vle t D.s) ∧ ¬ v.vle D.s 0) →
    ((∀ t ∈ base.T, v.vle t base.s) ∧ ¬ v.vle base.s 0)
  /-- Covering, uniformly in the (continuous) valuation. -/
  cover_uniform : ∀ v : Spv A, v.IsContinuous →
    ((∀ t ∈ base.T, v.vle t base.s) ∧ ¬ v.vle base.s 0) →
    ∃ D ∈ covers, ((∀ t ∈ D.T, v.vle t D.s) ∧ ¬ v.vle D.s 0)

/-- A standard cover datum instantiates as a rational covering at **every** choice of
`A⁺` (the conditions were `Spa`-uniform). -/
def StandardCoverData.toCovering [PlusSubring A] (S : StandardCoverData A) :
    RationalCovering A where
  base := S.base
  covers := S.covers
  hsubset := fun D hD v hv =>
    ⟨hv.1, (S.subset_uniform D hD v ⟨hv.2.1, hv.2.2⟩).1,
      (S.subset_uniform D hD v ⟨hv.2.1, hv.2.2⟩).2⟩
  hcover := fun v hv => by
    obtain ⟨D, hD, hc⟩ := S.cover_uniform v hv.1.1 ⟨hv.2.1, hv.2.2⟩
    exact ⟨D, hD, hv.1, hc.1, hc.2⟩

theorem StandardCoverData.toCovering_isRational [PlusSubring A]
    (S : StandardCoverData A) : S.toCovering.IsRational :=
  ⟨S.base_isRational, S.covers_isRational⟩

variable (A) in
/-- **The `A⁺`-free standard sheaf condition** (Kedlaya Remarks 1.6.8/1.6.9, the
common middle term of the independence theorem): for every standard cover datum and
**every** valid integral subring, the instantiated covering satisfies the separation,
gluing, and topological-embedding assertions. The signature carries no `PlusSubring`,
`CompatiblePlusSubring`, `HasLocLiftPowerBounded`, or `Spa` parameter — the valid
subrings are quantified in the body and the restriction-map package is derived from
the analytic scope. The rings `presheafValue D`, the restriction maps, and the
standard covers themselves depend only on `A`. -/
def StandardSheafCondition [IsHuberRing A] [IsTateRing A] [T2Space A]
    [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A] : Prop :=
  ∀ (S : StandardCoverData A) (B : Subring A) (hB : IsRingOfIntegralElements B),
    letI : PlusSubring A := ⟨B⟩
    haveI : IsRingOfIntegralElements (A⁺ : Subring A) := hB
    haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
    Topology.IsEmbedding (productRestrictionSub A S.toCovering) ∧
    ∀ (f : ∀ D : ↥S.toCovering.covers, presheafValue D.1),
      S.toCovering.AllDataCompatible f →
      ∃ x : presheafValue S.toCovering.base, ∀ D : ↥S.toCovering.covers,
        restrictionMap S.toCovering.base D.1
          (S.toCovering.hsubset D.1 D.2) x = f D

variable (A) in
/-- **P3, provable direction**: universal pair-level sheafiness pushes to the
`A⁺`-free standard condition — each standard datum instantiates at each valid choice
(`toCovering`), where the pair's finite rational criterion (recovered from the
all-open sheaf by the C5 converse `isSheafy_of_isLimitSheaf`) supplies the fields.

The converse — recovering `IsSheafyFor` at one pair from the standard condition —
is standard-cover **cofinality** (Kedlaya Lemma 1.6.8, Wedhorn 7.54's general branch);
its generation-side ingredients are proved in `StandardRefinement.lean` and the
remaining descent branch is the missing API recorded in
`WedhornStandardCoverRefinement.lean`. It is *not* on the dependency path of the
strongly noetherian theorems, which quantify over all valid pairs directly. -/
theorem standardSheafCondition_of_isSheafyComplete [IsHuberRing A] [IsTateRing A]
    [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (h : IsSheafyComplete A) : StandardSheafCondition A := by
  classical
  intro S B hB
  letI : PlusSubring A := ⟨B⟩
  haveI : IsRingOfIntegralElements (A⁺ : Subring A) := hB
  haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  have hlimit : IsLimitSheaf A := h ⟨B, hB⟩
  haveI hSheafy : IsSheafy A := isSheafy_of_isLimitSheaf hlimit
  refine ⟨?_, ?_⟩
  · exact IsSheafy.embedding (A := A) S.toCovering (S.toCovering_isRational)
  · intro f hf
    exact IsSheafy.gluing (A := A) S.toCovering (S.toCovering_isRational) f hf

variable (A) in
/-- A complete strongly noetherian Tate ring satisfies the `A⁺`-free standard sheaf
condition. -/
theorem standardSheafCondition_of_stronglyNoetherianTate [IsHuberRing A] [IsTateRing A]
    [IsStronglyNoetherian A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A] : StandardSheafCondition A :=
  standardSheafCondition_of_isSheafyComplete A
    (isSheafyComplete_of_stronglyNoetherianTate)

end ValuationSpectrum
