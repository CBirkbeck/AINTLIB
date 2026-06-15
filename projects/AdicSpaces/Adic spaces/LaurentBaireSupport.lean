/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».LaurentCoverTopology
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Pseudo-metrizability and BaireSpace support for the Laurent cover (T137–T140)

Continuation of the T136 BaireSupport section in
`«Adic spaces».LaurentCoverTopology`. The Mathlib metrizability and
Baire APIs (`Mathlib.Topology.Metrizable.CompletelyMetrizable`,
`Mathlib.Topology.Baire.CompleteMetrizable`) significantly expand the
typeclass-instance database; importing them directly into
`LaurentCoverTopology.lean` would slow down `infer_instance`-based
proofs there (notably the T135 `laurentTateAlgebra_t2Space` proof
times out under the default `synthInstance.maxHeartbeats=20000`).

This module isolates the metrizability/Baire imports plus the
follow-up lemmas, keeping `LaurentCoverTopology.lean` lean enough
to compile under default heartbeat budgets.

## Lemmas delivered

T137 (B₂-side):

* `B₂_gen_completeSpace` — `CompleteSpace (B₂_gen f)` under the
  canonical right uniform structure, delegating to the existing
  `TateAlgebra.quotient_oneSubfXIdeal_completeSpace` (`B₂_gen f`'s
  ideal is definitionally `oneSubfXIdeal f`).
* `B₂_gen_isCompletelyPseudoMetrizableSpace` — completely
  pseudo-metrizable, via Mathlib's auto-instance
  `IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable`
  fed by T136 `B₂_gen_uniformity_isCountablyGenerated` and
  `B₂_gen_completeSpace`.

T138 (B₁-side, consuming the upstream
`TateAlgebra.quotient_plusFSubXIdeal_completeSpace`):

* `B₁_gen_completeSpace` — analogous `CompleteSpace (B₁_gen f)`,
  delegating to the new
  `TateAlgebra.quotient_plusFSubXIdeal_completeSpace` declared
  upstream in `TateAlgebraTopology.lean`.
* `B₁_gen_isCompletelyPseudoMetrizableSpace` — completely
  pseudo-metrizable.

T139 (kernel-Baire chain consuming the B₁/B₂ CPS support and the T134
closed-kernel theorem):

* `B₁_gen_x_B₂_gen_isCompletelyPseudoMetrizableSpace` — the product
  `B₁_gen f × B₂_gen f` is completely pseudo-metrizable, via Mathlib's
  `IsCompletelyPseudoMetrizableSpace.prod` instance.
* `ker_deltaMap_gen_isCompletelyPseudoMetrizableSpace` — the closed
  kernel of `deltaMap_gen f` is completely pseudo-metrizable, via
  `IsClosed.isCompletelyPseudoMetrizableSpace` and the T134
  closed-kernel theorem.
* `ker_deltaMap_gen_baireSpace` — `BaireSpace
  ↥((deltaMap_gen f).ker : Set _)`, via Mathlib's auto-instance
  `BaireSpace.of_completelyPseudoMetrizable`. This discharges the
  `hBaire_ker` hypothesis of T134's `epsilonHom_gen_inducing`.

The kernel-Baire theorem takes the T134-style `hT2_B12 : T2Space (B₁₂_gen f)`
hypothesis directly, mirroring T134's signature, so callers can continue to
discharge it from `B₁₂_gen_t2Space` (T135) or any other available T2 witness
without forcing a specific bivariate noetherianity hypothesis at this layer.

T140 (final consolidation):

* `epsilonHom_gen_inducing_of_complete` — wraps T134's
  `epsilonHom_gen_inducing` with its target-side topology hypotheses
  (`hT2_B12`, `hT2_prod`, `hBaire_ker`) discharged from T135's T2
  supports and T139's kernel-Baire theorem. Source-side OMT
  prerequisites (`[UniformSpace A] [IsUniformAddGroup A]
  [CompleteSpace A] [SigmaCompactSpace A]` plus `htop` and
  `hf_nonunit`) remain explicit, as do the univariate +
  bivariate noetherian pair-subring hypotheses needed by the
  closed-ideal infrastructure.
-/

namespace LaurentCover

open TateAlgebra LaurentTateAlgebra Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

open scoped Uniformity

section BaireSupport

variable [IsTateRing A] [T2Space A] [IsNoetherianRing A] [IsDomain A] (f : A)

omit [IsNoetherianRing A] [IsDomain A] in
/-- `B₂_gen f` is `CompleteSpace` under the canonical right uniform structure.

Delegates to the existing `TateAlgebra.quotient_oneSubfXIdeal_completeSpace`
(`B₂_gen f`'s ideal is definitionally `oneSubfXIdeal f`). -/
theorem B₂_gen_completeSpace
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    @CompleteSpace (B₂_gen f) (B₂_gen_uniformSpace f) :=
  quotient_oneSubfXIdeal_completeSpace hA_complete hnoeth f

omit [IsNoetherianRing A] [IsDomain A] in
/-- `B₂_gen f` is completely pseudo-metrizable.
The Mathlib instance
`IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable`
fires from `[UniformSpace] [CompleteSpace] [IsCountablyGenerated 𝓤]`. -/
theorem B₂_gen_isCompletelyPseudoMetrizableSpace
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    TopologicalSpace.IsCompletelyPseudoMetrizableSpace (B₂_gen f) := by
  haveI : Filter.IsCountablyGenerated (𝓤 (B₂_gen f)) :=
    B₂_gen_uniformity_isCountablyGenerated f
  haveI : CompleteSpace (B₂_gen f) := B₂_gen_completeSpace f hA_complete hnoeth
  infer_instance

omit [IsNoetherianRing A] [IsDomain A] in
/-- `B₁_gen f` is `CompleteSpace` under the canonical right uniform structure.

Delegates to the upstream `TateAlgebra.quotient_plusFSubXIdeal_completeSpace`
(`B₁_gen f`'s ideal is definitionally `plusFSubXIdeal f`). -/
theorem B₁_gen_completeSpace
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    @CompleteSpace (B₁_gen f) (B₁_gen_uniformSpace f) :=
  quotient_plusFSubXIdeal_completeSpace hA_complete hnoeth f

omit [IsNoetherianRing A] [IsDomain A] in
/-- `B₁_gen f` is completely pseudo-metrizable. -/
theorem B₁_gen_isCompletelyPseudoMetrizableSpace
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    TopologicalSpace.IsCompletelyPseudoMetrizableSpace (B₁_gen f) := by
  haveI : Filter.IsCountablyGenerated (𝓤 (B₁_gen f)) :=
    B₁_gen_uniformity_isCountablyGenerated f
  haveI : CompleteSpace (B₁_gen f) := B₁_gen_completeSpace f hA_complete hnoeth
  infer_instance

omit [IsNoetherianRing A] [IsDomain A] in
/-- The product `B₁_gen f × B₂_gen f` is completely pseudo-metrizable.

This is the T139 step that combines `B₁_gen_isCompletelyPseudoMetrizableSpace`
and `B₂_gen_isCompletelyPseudoMetrizableSpace` via Mathlib's product
instance `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.prod`. -/
theorem B₁_gen_x_B₂_gen_isCompletelyPseudoMetrizableSpace
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    TopologicalSpace.IsCompletelyPseudoMetrizableSpace (B₁_gen f × B₂_gen f) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (B₁_gen f) :=
    B₁_gen_isCompletelyPseudoMetrizableSpace f hA_complete hnoeth
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (B₂_gen f) :=
    B₂_gen_isCompletelyPseudoMetrizableSpace f hA_complete hnoeth
  infer_instance

omit [IsNoetherianRing A] [IsDomain A] in
/-- The closed kernel of `deltaMap_gen f` in `B₁_gen f × B₂_gen f` is
completely pseudo-metrizable.

Combines `B₁_gen_x_B₂_gen_isCompletelyPseudoMetrizableSpace` (T139) with
the T134 `ker_deltaMap_gen_isClosed` via Mathlib's
`IsClosed.isCompletelyPseudoMetrizableSpace`. The `hT2_B12` hypothesis is
the same one consumed by T134's `epsilonHom_gen_inducing`; callers can
discharge it from T135's `B₁₂_gen_t2Space`. -/
theorem ker_deltaMap_gen_isCompletelyPseudoMetrizableSpace
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT2_B12 : @T2Space (B₁₂_gen f) (B₁₂_gen_topology f)) :
    TopologicalSpace.IsCompletelyPseudoMetrizableSpace
      ↥((deltaMap_gen f).ker : Set (B₁_gen f × B₂_gen f)) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (B₁_gen f × B₂_gen f) :=
    B₁_gen_x_B₂_gen_isCompletelyPseudoMetrizableSpace f hA_complete hnoeth
  exact (ker_deltaMap_gen_isClosed f hT2_B12).isCompletelyPseudoMetrizableSpace

omit [IsNoetherianRing A] [IsDomain A] in
/-- `BaireSpace` of the closed kernel of `deltaMap_gen f`. This discharges the
`hBaire_ker` hypothesis of T134's `epsilonHom_gen_inducing`.

The proof is via Mathlib's auto-instance `BaireSpace.of_completelyPseudoMetrizable`
fed by `ker_deltaMap_gen_isCompletelyPseudoMetrizableSpace`. -/
theorem ker_deltaMap_gen_baireSpace
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT2_B12 : @T2Space (B₁₂_gen f) (B₁₂_gen_topology f)) :
    BaireSpace ↥((deltaMap_gen f).ker : Set (B₁_gen f × B₂_gen f)) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace
      ↥((deltaMap_gen f).ker : Set (B₁_gen f × B₂_gen f)) :=
    ker_deltaMap_gen_isCompletelyPseudoMetrizableSpace f hA_complete hnoeth hT2_B12
  infer_instance

/-- **T140: `Topology.IsInducing (epsilonHom_gen f)` with target-side
hypotheses discharged.**

Wraps T134's `epsilonHom_gen_inducing` and discharges its target-side
topology obligations (`hT2_B12`, `hT2_prod`, `hBaire_ker`) using:

* T135 `B₁₂_gen_t2Space` for `hT2_B12`,
* T135 `B₁_gen_x_B₂_gen_t2Space` for `hT2_prod`,
* T139 `ker_deltaMap_gen_baireSpace` for `hBaire_ker`.

Source-side Banach open-mapping prerequisites
(`[UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
[SigmaCompactSpace A]`, `htop`, `hf_nonunit`) remain explicit, as does
the univariate + bivariate noetherian pair-subring infrastructure needed
by the closed-ideal lemmas underlying the T2 supports. -/
theorem epsilonHom_gen_inducing_of_complete
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [SigmaCompactSpace A]
    (htop : ‹TopologicalSpace A› = UniformSpace.toTopologicalSpace)
    (hf_nonunit : ¬IsUnit f)
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hnoeth₂ : IsNoetherianRing
      ↥(pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition)) :
    Topology.IsInducing (epsilonHom_gen f : A → B₁_gen f × B₂_gen f) := by
  have hT2_B12 : @T2Space (B₁₂_gen f) (B₁₂_gen_topology f) :=
    B₁₂_gen_t2Space f hA_complete hnoeth₂
  have hT2_prod : T2Space (B₁_gen f × B₂_gen f) :=
    B₁_gen_x_B₂_gen_t2Space f hA_complete hnoeth
  have hBaire_ker : BaireSpace
      ↥((deltaMap_gen f).ker : Set (B₁_gen f × B₂_gen f)) :=
    ker_deltaMap_gen_baireSpace f hA_complete hnoeth hT2_B12
  exact epsilonHom_gen_inducing f htop hf_nonunit hT2_B12 hT2_prod hBaire_ker

end BaireSupport

end LaurentCover
