/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Cor832
import «Adic spaces».IdealLocalization

/-!
# T001-PRIME-EXTENSION-CLOSED: conditional bridge for prime-extension closedness

This file provides a **conditional bridge** for the analytic residual in
the T001 Cor832 completion chain, parameterized by a pointwise Jacobson
containment hypothesis.

## Status (2026-04-24)

The two exported theorems take the pointwise Jacobson containment
`locIdeal ≤ Ideal.jacobson (primeExtensionContraction)` as an **explicit
caller hypothesis**. They are NOT unconditional closedness theorems.
Producing the Jacobson containment unconditionally (the
**T001-POINTWISE-JACOBSON** task) is open; see the module-end docblock
for the analysis and obstruction.

## Statement shape (conditional)

Given a Tate ring `A` with a pair of definition `P` and a rational
localization datum `D'`, for every non-open prime `p` of `A` with
`D'.s ∉ p`, IF `locIdeal D'.P D'.T D'.s ≤ Ideal.jacobson
(primeExtensionContraction D' p)` THEN the localization-prime extension
`Ideal.map (algebraMap A (Localization.Away D'.s)) p` is closed in
`D'.topology`.

## Strategy (assuming the pointwise Jacobson hypothesis)

1. **Transfer** (`isClosed_in_locTopology_of_contraction_isClosed_in_locSubring`):
   closedness in `D'.topology` of a proper ideal of `Loc.Away D'.s` follows
   from closedness of its `locSubring`-contraction in the subspace topology.

2. **Pointwise Jacobson** (`Ideal.isClosed_of_le_jacobson_pointwise`): the
   contraction `q := Ideal.comap locSubring.subtype (prime extension)` is
   closed in `locSubring`'s adic topology provided
   `locIdeal P T s ≤ Ideal.jacobson q` — supplied by the caller.

## What is NOT done here

The pointwise Jacobson containment `locIdeal ≤ Ideal.jacobson
(primeExtensionContraction)` itself is NOT proved. This is the same
residual class as T-IDEAL-JAC; its pointwise specialization requires
completion-level bridging that exceeds the current file's scope.

The **false** global containment `locIdeal ≤ Ideal.jacobson ⊥` is
explicitly avoided (would fail in degenerate cases where `locIdeal = ⊤`
per `Cor832.lean:1542-1546`).

## References

* `Adic spaces/IdealClosedness.lean:154` —
  `Ideal.isClosed_of_le_jacobson_pointwise` (pointwise Jacobson closedness).
* `Adic spaces/IdealLocalization.lean:163` —
  `Ideal.isClosed_in_locTopology_of_contraction_isClosed_in_locSubring`
  (transfer step).
* `Adic spaces/IdealLocalization.lean:339` —
  `locIdeal_forall_isTopologicallyNilpotent` (supporting fact, no
  completeness needed).
* `Adic spaces/Cor832.lean:1619` —
  `spa_point_nonOpen_of_rational_subset_tate_of_prime_extension_closed`
  (downstream consumer).
-/

namespace ValuationSpectrum

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- **The contraction of a prime extension** to `locSubring`. Parameterized
by an arbitrary `RationalLocData D'` and a prime `p` of `A`. -/
noncomputable def primeExtensionContraction (D' : RationalLocData A)
    (p : Ideal A) : Ideal (locSubring D'.P D'.T D'.s) :=
  Ideal.comap (locSubring D'.P D'.T D'.s).subtype
    (Ideal.map (algebraMap A (Localization.Away D'.s)) p)

omit [PlusSubring A] [IsHuberRing A] in
/-- **T001 PRIME-EXTENSION-CLOSED: closedness of prime extensions via
the pointwise Jacobson route.**

Given a Tate/Huber ring `A` with `[IsNoetherianRing (locSubring D'.P D'.T D'.s)]`,
a non-open prime `p` with `D'.s ∉ p`, and the pointwise Jacobson containment
`locIdeal ≤ Ideal.jacobson (primeExtensionContraction)`, the
prime-extension ideal in `Loc.Away D'.s` is closed in `D'.topology`.

The pointwise Jacobson containment is the **single remaining residual**;
it is strictly weaker than the false global `locIdeal ≤ Ideal.jacobson ⊥`
and holds under Huber/Tate structure at specific prime extensions. -/
theorem prime_extension_closed_from_Huber_Tate_of_jacobson_pointwise
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D' : RationalLocData A)
    [IsNoetherianRing (locSubring D'.P D'.T D'.s)]
    (p : Ideal A) (_hp : p.IsPrime) (_hD's : D'.s ∉ p)
    (_hp_notOpen : ¬IsOpen (p : Set A))
    (h_jacobson : locIdeal D'.P D'.T D'.s ≤
      Ideal.jacobson (primeExtensionContraction D' p)) :
    @IsClosed _ D'.topology
      ((Ideal.map (algebraMap A (Localization.Away D'.s)) p :
          Ideal (Localization.Away D'.s)) :
        Set (Localization.Away D'.s)) := by
  -- Pick a Tate pseudo-uniformizer in D'.P.A₀ (inlined helper: Tate rings have
  -- a topologically-nilpotent unit, and some power lives in D'.P.A₀ since A₀
  -- is open in A).
  have hπ_exists : ∃ π : A, IsTopologicallyNilpotent π ∧ IsUnit π ∧ π ∈ D'.P.A₀ := by
    obtain ⟨u, hu_nilp⟩ := ‹IsTateRing A›.exists_topologicallyNilpotent_unit
    have h_nhds : (D'.P.A₀ : Set A) ∈ nhds (0 : A) :=
      D'.P.isOpen.mem_nhds D'.P.A₀.zero_mem
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hu_nilp h_nhds)
    refine ⟨(u : A) ^ (K + 1),
      isTopologicallyNilpotent_pow hu_nilp (Nat.succ_pos K),
      u.isUnit.pow (K + 1),
      hK (K + 1) (Nat.le_succ K)⟩
  obtain ⟨π, hπ_nil, hπ_unit, hπ_A₀⟩ := hπ_exists
  -- Apply the locTopology transfer lemma.
  refine Ideal.isClosed_in_locTopology_of_contraction_isClosed_in_locSubring
    D'.P D'.T D'.s D'.hopen hπ_nil hπ_A₀ hπ_unit _ ?_
  -- Contraction closedness via pointwise Jacobson in the adic topology on locSubring.
  letI : TopologicalSpace (Localization.Away D'.s) := D'.topology
  haveI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : TopologicalSpace (locSubring D'.P D'.T D'.s) :=
    D'.topology.induced (locSubring D'.P D'.T D'.s).subtype
  haveI : IsTopologicalRing (locSubring D'.P D'.T D'.s) :=
    Subring.instIsTopologicalRing (locSubring D'.P D'.T D'.s)
  exact Ideal.isClosed_of_le_jacobson_pointwise
    (locSubring_isAdic D'.P D'.T D'.s D'.hopen)
    (primeExtensionContraction D' p) h_jacobson

omit [IsHuberRing A] in
/-- **T001 PRIME-EXTENSION-CLOSED: end-to-end Spa-point existence.**

Combines `prime_extension_closed_from_Huber_Tate_of_jacobson_pointwise`
with `Cor832.spa_point_nonOpen_of_rational_subset_tate_of_prime_extension_closed`
to produce the direct Spa-point existence consumed by
`Presheaf.mem_prime_of_rational_subset_nonOpen`. This closes the T001
chain conditional on the pointwise Jacobson residual. -/
theorem spa_point_nonOpen_of_rational_subset_via_jacobson_pointwise
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D D' : RationalLocData A)
    [IsNoetherianRing (locSubring D'.P D'.T D'.s)]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ D'.P.A₀)
    (hcanonicalMap_cont : Continuous D'.canonicalMap)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (p : Ideal A) (hp : p.IsPrime) (hDs : D.s ∈ p)
    (hD's : D'.s ∉ p) (hp_notOpen : ¬IsOpen (p : Set A))
    (h_jacobson : locIdeal D'.P D'.T D'.s ≤
      Ideal.jacobson (primeExtensionContraction D' p)) :
    ∃ v ∈ rationalOpen D'.T D'.s, p ≤ v.supp :=
  spa_point_nonOpen_of_rational_subset_tate_of_prime_extension_closed
    P D D' hAplus_le_A₀ hcanonicalMap_cont h p hDs hD's hp_notOpen
    (prime_extension_closed_from_Huber_Tate_of_jacobson_pointwise
      D' p hp hD's hp_notOpen h_jacobson)

end ValuationSpectrum

/-! ## T001-POINTWISE-JACOBSON: obstruction analysis (not implemented)

The natural target

```lean
theorem locIdeal_le_jacobson_primeExtensionContraction
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D' : RationalLocData A)
    [IsNoetherianRing (locSubring D'.P D'.T D'.s)]
    (p : Ideal A) (hp : p.IsPrime) (hD's : D'.s ∉ p)
    (hp_notOpen : ¬ IsOpen (p : Set A)) :
    locIdeal D'.P D'.T D'.s ≤
      Ideal.jacobson (primeExtensionContraction D' p)
```

is NOT proved in this file. Analysis of why the current hypotheses are
insufficient:

**Direct argument attempt via topologically-nilpotent-ness**: every `x ∈
locIdeal` is topologically nilpotent
(`IdealLocalization.locIdeal_forall_isTopologicallyNilpotent`, `:339`,
no completeness needed). For `x ∈ Ideal.jacobson q` we need `1 + x * y`
to be a unit modulo `q` in `locSubring / q` for every `y`. In a
**complete** topological ring, topologically-nilpotent `x*y` gives `1 +
x*y` a unit via Neumann series. But `locSubring` is NOT generally
complete in the `locIdeal`-adic topology — the project's known
completeness witness is on the **completion** `presheafValue D'`
(`Cor832.presheafValue_isAdicComplete`, `Cor832.lean:896`), not on
`locSubring`. This is the root of the obstruction.

**Completion-bridge attempt**: apply
`Ideal.le_jacobson_bot_of_isAdic_complete`
(`IdealClosedness.lean:331`) to `completedLocSubring` (where
`completedLocIdeal D' ⊆ Ideal.jacobson ⊥`). The containment
`locIdeal ⊆ Jacobson(primeExtensionContraction D' p)` would then need
to descend via the composition
`locSubring ↪ Loc.Away D'.s → presheafValue D'`. The descent fails
generically: neither inclusion `Jacobson(comap f I) ⊆ comap f
(Jacobson I)` nor the reverse is a generic ring-theoretic fact;
both require structural hypotheses on `f`. The two natural
structural hypotheses —

  (i) `locSubring/q ↪ completedLocSubring/q'` is an **isomorphism of
  topological rings** (up to completion), or
  (ii) `locSubring` is **directly adic-complete** (S-IDEAL-JAC
  hypothesis, known not to hold in degenerate cases) —

are each as strong as the global residual class that the manager
directive forbids.

**Degenerate case**: if `D'.s ∈ P.I`, then `locIdeal = ⊤` in `locSubring`
(via `Cor832.lean:1542-1546`), `D'.topology` becomes indiscrete, and
only `⊤` and `∅` are closed sets. The target prime extension is proper
(by `map_algebraMap_ne_top_of_notMem`, using `D'.s ∉ p`), hence not
closed. So the unconditional `prime_extension_closed_from_Huber_Tate`
is **FALSE** in the degenerate case.

**Minimal additional hypothesis** that would unblock the proof:
**either** `D'.s ∉ P.I` (non-degeneracy — rules out the `locIdeal = ⊤`
degenerate case) **plus** a completion-quotient bridge (closing
`locSubring/q ↪ completedLocSubring/q'` topologically, at the specific
`q`) **or** direct adic-completeness of `locSubring` (T-IDEAL-JAC via
`IsAdicComplete`, known residual).

**Conclusion**: the unconditional theorem requires
input beyond what the current Huber/Tate hypothesis bundle supplies.
The conditional bridge above is the cleanest exportable form until one
of the two auxiliary routes (non-degeneracy + completion-descent
argument, or S-IDEAL-JAC) is established.

**Precise missing lemma shape** (for downstream discharge, independent
of which route closes it):

```lean
theorem locIdeal_le_jacobson_primeExtensionContraction
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D' : RationalLocData A)
    [IsNoetherianRing (locSubring D'.P D'.T D'.s)]
    (p : Ideal A) (hp : p.IsPrime) (hD's : D'.s ∉ p)
    (hp_notOpen : ¬ IsOpen (p : Set A)) :
    locIdeal D'.P D'.T D'.s ≤
      Ideal.jacobson (primeExtensionContraction D' p)
```

As noted, this is **false** without a non-degeneracy hypothesis
`D'.s ∉ P.I`. With that non-degeneracy hypothesis added, the proof
needs a completion-descent lemma bridging `locSubring/q` and
`completedLocSubring/q'` — which is itself a substantial analytic
subtask.
-/
