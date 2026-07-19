/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».SheafyPair
import «Adic spaces».WedhornCechAcyclicity

/-!
# Pair-level and ring-level sheafiness; the strongly noetherian Tate theorem

The literature-facing sheafiness API (Wedhorn Definition 8.26, Kedlaya Remarks
1.6.8–1.6.10), on top of the C-phase equivalence `isSheafy_iff_isLimitSheaf`:

* `IsSheafyFor A Aplus` — **pair-level sheafiness** for an explicit **bundled valid**
  choice `Aplus : RingOfIntegralElements A`: the genuine all-open projective-limit
  structure presheaf of `Spa (A, Aplus)` is a sheaf of topological rings
  (`IsLimitSheaf` under the local-instance bridge). A bare `Subring A` cannot be
  supplied (handover gate F1); the restriction-map package `HasLocLiftPowerBounded`
  is existentially bundled, never a hypothesis of the public definition.
* `IsSheafyComplete A` — the **complete-ring specialization of Wedhorn Definition
  8.26**: *every* valid choice of integral subring of `A` gives a sheafy pair. (For
  complete `A`, `Â = A` and this is Wedhorn's ring-level definition verbatim.)
* `IsSheafyRing A` — the **literal general Definition 8.26**, quantifying over the
  rings of integral elements of the completion `Â` (stated over
  `UniformSpace.Completion A` for the canonical right uniformity; it takes the
  completion's Huber-ring package as instance parameters — the completion-of-Huber
  transport layer (Wedhorn 7.47, Tate/strong-noetherian transfer) is not yet in the
  project, see `docs/SHEAFY-LIVE-AUDIT-2026-07-19.md`).
* `isSheafyFor_of_stronglyNoetherianTate` / `isSheafyComplete_of_stronglyNoetherianTate`
  — **the principal theorem** (Wedhorn Theorem 8.28(b), complete case, in the genuine
  all-open vocabulary): a complete strongly noetherian Tate ring is sheafy for
  **every** valid ring of integral elements — with the genuine projective-limit
  presheaf and topology, not the chosen-pair rational criterion. No
  `CompatiblePlusSubring`, no `HasLocLiftPowerBounded`, no `IsDomain` hypotheses.
* `isSheafyFor_congr_of_stronglyNoetherianTate` — **`A⁺`-independence at the 8.28(b)
  target scope**: any two (in particular non-definitionally-equal) valid choices give
  equivalent pair-level sheafiness. This is Kedlaya Remark 1.6.9's conclusion for the
  Tate target of the theorem. The *generic*-Tate independence (through standard-cover
  cofinality, Kedlaya Lemma 1.6.8) is scoped by `StandardCoverData` /
  `StandardSheafCondition` below: the standard (`Spa`-uniformly covering) data
  instantiate at every valid pair (`StandardCoverData.toCovering`), pair-level
  sheafiness pushes to the standard condition (`standardSheafCondition_of_isSheafyFor`),
  and the converse direction for arbitrary rational covers awaits the general
  refinement branch recorded as missing API in `WedhornStandardCoverRefinement.lean`
  (not on the dependency path of any theorem here). **No nonanalytic independence is
  claimed** (Kedlaya Remark 1.6.10).
-/

noncomputable section

open TopologicalSpace

namespace ValuationSpectrum

universe u

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A]

/-! ### Pair-level sheafiness for an explicit valid choice -/

/-- **Pair-level sheafiness** (Wedhorn Definition 8.26 for one affinoid pair, in the
genuine all-open vocabulary): the pair `(A, Aplus)` — with `Aplus` a **bundled ring of
integral elements**, so invalid bare subrings cannot be supplied — is sheafy when the
canonical restriction-map package exists and the genuine projective-limit structure
presheaf on all opens of `Spa (A, Aplus)` is a sheaf of topological rings
(`IsLimitSheaf`: separation + gluing + the arbitrary-cover topological-embedding
condition of Wedhorn Remark 8.20). -/
def IsSheafyFor (Aplus : RingOfIntegralElements A) : Prop :=
  letI := Aplus.toPlusSubring
  ∃ hll : HasLocLiftPowerBounded A, @IsLimitSheaf A _ _ _ Aplus.toPlusSubring _ hll

variable {A}

/-- Under the definitional local instances, `IsSheafyFor` is exactly the bundled
all-open sheaf statement. -/
theorem isSheafyFor_iff_isLimitSheaf (Aplus : RingOfIntegralElements A) :
    IsSheafyFor A Aplus ↔
      (letI := Aplus.toPlusSubring
       ∃ hll : HasLocLiftPowerBounded A,
         @IsLimitSheaf A _ _ _ Aplus.toPlusSubring _ hll) :=
  Iff.rfl

/-! ### Ring-level sheafiness -/

variable (A) in
/-- **The complete-ring specialization of Wedhorn Definition 8.26**: `A` is sheafy
when *every* ring of integral elements of `A` gives a sheafy pair. For complete `A`
(the scope of every theorem below) `Â = A`, so this is the ring-level definition
verbatim; the universal quantifier over valid choices is retained (handover P4). -/
def IsSheafyComplete : Prop :=
  ∀ Aplus : RingOfIntegralElements A, IsSheafyFor A Aplus

variable (A) in
/-- **Wedhorn Definition 8.26, literal general form**: an f-adic ring `A` is sheafy
when every ring of integral elements of the completion `Â` gives a sheafy pair of
`Â`. Stated over `UniformSpace.Completion A` (right uniformity); the completion's
Huber package is taken as instance parameters — the transport layer producing them
from `A` (Wedhorn Lemma 7.47 and the Tate/strongly-noetherian transfer) is the
recorded next ticket and is **not** assumed proved here. -/
def IsSheafyRing
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CommRing (UniformSpace.Completion A)]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      TopologicalSpace (UniformSpace.Completion A)]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      IsTopologicalRing (UniformSpace.Completion A)]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      IsHuberRing (UniformSpace.Completion A)] : Prop :=
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  ∀ Aplus : RingOfIntegralElements (UniformSpace.Completion A),
    IsSheafyFor (UniformSpace.Completion A) Aplus

/-! ### The strongly noetherian Tate theorem (Wedhorn Theorem 8.28(b), complete case,
in the genuine all-open vocabulary) -/

variable [IsTateRing A] [IsStronglyNoetherian A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-- **The principal pair-level theorem**: a complete strongly noetherian Tate ring is
sheafy for **every explicit valid choice** of ring of integral elements — the genuine
all-open projective-limit structure presheaf of `Spa (A, Aplus)` is a sheaf of
topological rings. Assembled from the (instance-generic, axiom-clean)
`isSheafy_of_stronglyNoetherian_828b` and the C-phase equivalence
`isLimitSheaf_of_isSheafy`. No `CompatiblePlusSubring`, `HasLocLiftPowerBounded`,
or `IsDomain` hypotheses appear. -/
theorem isSheafyFor_of_stronglyNoetherianTate (Aplus : RingOfIntegralElements A) :
    IsSheafyFor A Aplus := by
  classical
  letI := Aplus.toPlusSubring
  haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
  letI : IsNoetherianRing A := IsStronglyNoetherian.isNoetherianRing A
  haveI hll : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
  haveI : IsSheafy A := isSheafy_of_stronglyNoetherian_828b
  exact ⟨hll, isLimitSheaf_of_isSheafy⟩

/-- **The principal ring-level theorem** (Wedhorn Theorem 8.28(b), complete case): a
complete strongly noetherian Tate ring satisfies the universal (Definition 8.26)
sheafiness — *every* valid ring of integral elements gives a sheafy pair, with the
genuine structure presheaf and projective-limit topology. -/
theorem isSheafyComplete_of_stronglyNoetherianTate : IsSheafyComplete A :=
  fun Aplus => isSheafyFor_of_stronglyNoetherianTate Aplus

/-- **`A⁺`-independence at the 8.28(b) target scope** (Kedlaya Remark 1.6.9's
conclusion for complete strongly noetherian Tate rings): any two valid choices —
related by no hypothesis whatsoever, in particular non-definitionally-equal ones —
give equivalent pair-level sheafiness. No identification of the underlying
`Spa (A, Aplus₁)` and `Spa (A, Aplus₂)` is used or asserted. -/
theorem isSheafyFor_congr_of_stronglyNoetherianTate
    (Aplus Bplus : RingOfIntegralElements A) :
    IsSheafyFor A Aplus ↔ IsSheafyFor A Bplus :=
  iff_of_true (isSheafyFor_of_stronglyNoetherianTate Aplus)
    (isSheafyFor_of_stronglyNoetherianTate Bplus)

/-- Regression (handover P4 gate — non-definitionally-equal choices): the
independence statement applies to two choices assumed *distinct*. -/
example (Aplus Bplus : RingOfIntegralElements A) (_ : Aplus ≠ Bplus) :
    IsSheafyFor A Aplus ↔ IsSheafyFor A Bplus :=
  isSheafyFor_congr_of_stronglyNoetherianTate Aplus Bplus

end ValuationSpectrum

namespace ValuationSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### Standard covers and the `A⁺`-free standard sheaf condition (Kedlaya 1.6.8/1.6.9)

A **standard cover datum** is a finite family of valid rational data whose
subordination and covering conditions hold **`Spa`-uniformly** — as pointwise
statements about the `vle`-inequalities, quantified over all (continuous) valuations,
with no `Spa (A, A⁺)`-membership test. The Laurent(-product) covers of Wedhorn §8.2
and Kedlaya's standard rational coverings are of this form: their covering property
is the sign dichotomy `v(f·d) ≤ v(d) ∨ v(d) ≤ v(f·d)`, valid for every valuation.
Consequently a standard datum instantiates as a `RationalCovering` at **every** choice
of `A⁺` simultaneously (`StandardCoverData.toCovering`) — Kedlaya Remark 1.6.9's
mechanism. -/

/-- A finite rational cover datum whose subordination/covering conditions are
`Spa`-uniform (pointwise in the valuation, no `A⁺`). -/
structure StandardCoverData (A : Type u) [CommRing A] [TopologicalSpace A]
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
`A⁺` (Kedlaya Remark 1.6.9's mechanism: the conditions were `Spa`-uniform). -/
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
`CompatiblePlusSubring`, or `Spa` parameter (the valid subrings are quantified in the
body); the rings `presheafValue D`, the restriction maps (whose `HasLocLiftPowerBounded`
witnesses are proof-irrelevant `Prop`-class instances), and the standard covers
themselves depend only on `A`. -/
def StandardSheafCondition [IsHuberRing A] : Prop :=
  ∀ (S : StandardCoverData A) (B : Subring A), IsRingOfIntegralElements B →
    letI : PlusSubring A := ⟨B⟩
    ∃ hll : HasLocLiftPowerBounded A,
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
requires standard-cover **cofinality** among rational covers (Kedlaya Lemma 1.6.8,
Wedhorn 7.54's general branch), recorded as missing API in
`WedhornStandardCoverRefinement.lean`; it is *not* on the dependency path of the
strongly noetherian theorems above, which quantify over all valid pairs directly. -/
theorem standardSheafCondition_of_isSheafyComplete [IsHuberRing A] [IsTateRing A]
    [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (h : IsSheafyComplete A) : StandardSheafCondition A := by
  classical
  intro S B hB
  letI : PlusSubring A := ⟨B⟩
  haveI : IsRingOfIntegralElements (A⁺ : Subring A) := hB
  obtain ⟨hll, hlimit⟩ := h ⟨B, hB⟩
  haveI := hll
  haveI hSheafy : IsSheafy A := isSheafy_of_isLimitSheaf hlimit
  refine ⟨hll, ?_, ?_⟩
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
