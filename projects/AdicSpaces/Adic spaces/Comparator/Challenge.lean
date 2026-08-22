/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.Over.TateInstances
import «Adic spaces».MvTateAlgebraTopology
import «Adic spaces».SheafyRing
import «Adic spaces».Uniform

/-!
# Comparator challenge: [FJP] Theorem 1.1

The conclusions of the paper's headline theorem (`thm:main` of *Uniform sheafy Tate rings
that are not stably uniform*; Theorem 1.3 in the revision the library's docstrings cite),
stated with `sorry` proofs, for verification by
[leanprover/comparator](https://github.com/leanprover/comparator) against `Solution.lean`.

## The base

These are stated over a **general** base, not over the concrete witness field
`LaurentSeries F`: `K` is an arbitrary complete ultrametric nontrivially-normed field whose
valuation ring is a discrete valuation ring, matching the paper (§3: "The results in this
section and the next do not require the valuation on `k` to be discrete. They hold for any
complete ultrametric normed field `k`…", with discreteness entering in §5). The binder block
is the same as `WPChallenge.lean`'s, and `Theorem 1.1`'s own `<lean>` references in the
paper source point at these `FiniteJetOver.*_of_dvr` declarations.

## The trust boundary

This module imports only the **definition layer**:

* `FJP.Over.TateInstances` — the general-base `JetA` and the uniformizer-free
  `IsHuberRing`/`IsTateRing` instances the statements need in order to elaborate at all.
  Its closure is `Over/JetRings` → `FJP.CDVFBase` + `FJP.FiniteJetRings`, plus the
  base-agnostic `FaithfulLocLift`.
* `MvTateAlgebraTopology` — the base-agnostic Tate-extension topology stack, for the
  strong-sheafiness statement's instance telescope.
* `SheafyRing` (defines `IsSheafyComplete`) and `Uniform` (defines `IsUniform` /
  `IsStablyUniform`).

That closure contains **none** of the modules that prove these statements — none of
`Over/Chart`, `Over/UniformDomain`, `Over/StrictLocalization`, `Over/SheafTransfer`,
`Over/SheafyEndpoints`, `Over/StrongSheafy`, `Over/ExtendedMilnorInstance`, or
`Over/Functoriality` — so the statements here are independent restatements rather than
echoes of the proofs being judged.

The Huber/Tate instances were moved into `Over/TateInstances.lean` precisely for this: they
previously lived in `Over/Functoriality.lean`, whose closure contains `Over/Chart.lean` and
so the proof of `not_isStablyUniform_JetA`.

Excluded from the default build: the `«Adic spaces»` `lean_lib` declares no `globs`, so only
its root module is a build target and nothing imports this file.
-/

open FiniteJetOver ValuationSpectrum TopologicalRing MvTateAlgebra
open scoped NormedField Valued

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing 𝒪[K]]

/-- **[FJP] Theorem 1.1 (sheafy)**: `(𝓐, 𝓐°)` is sheafy. -/
theorem fjp_1_1_isSheafy : IsSheafy (JetA K) := sorry

/-- **[FJP] Theorem 1.1 (uniform)**: 𝓐 is uniform. -/
theorem fjp_1_1_isUniform : IsUniform (JetA K) := sorry

/-- **[FJP] Theorem 1.1 (domain)**: 𝓐 is an integral domain. -/
theorem fjp_1_1_isDomain : IsDomain (JetA K) := sorry

/-- **[FJP] Theorem 1.1 (nonnoetherian)**: 𝓐 is not noetherian. -/
theorem fjp_1_1_not_isNoetherianRing : ¬ IsNoetherianRing (JetA K) := sorry

/-- **[FJP] Theorem 1.1 (`𝓐° = 𝓐₀`)**. -/
theorem fjp_1_1_powerBounded_eq_unitBall :
    powerBoundedSubring (JetA K) = (FiniteJet.unitBall (JetA K) : Set (JetA K)) := sorry

/-- **[FJP] Theorem 1.1 (strongly sheafy)**: every finite Tate extension of 𝓐 is sheafy.

The instance telescope is spelled out from the base-agnostic `MvTateAlgebraTopology` stack
only; in particular the completeness slot is `mvTate_completeSpace … inferInstance` rather
than the library's one-line wrapper `FiniteJetOver.finiteJet_tateExt_completeSpace`, which
lives in `Over/StrongSheafy.lean` — a module this file must not see. -/
theorem fjp_1_1_stronglySheafy (n : ℕ) :
    letI := mvTateAlgebraTopology' (A := JetA K) n
    haveI := mvTate_isTateRing (A := JetA K) n
    haveI := mvTate_t2Space (A := JetA K) n
    haveI := mvTate_nonarchimedean (A := JetA K) n
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := JetA K) n
    haveI : @CompleteSpace ↥(restrictedMvPowerSeriesSubring n (JetA K))
      (IsTopologicalAddGroup.rightUniformSpace _) :=
        mvTate_completeSpace (A := JetA K) n inferInstance
    IsSheafyComplete ↥(restrictedMvPowerSeriesSubring n (JetA K)) := sorry

/-- **[FJP] Theorem 1.1 (not stably uniform)**: 𝓐 is not stably uniform. -/
theorem fjp_1_1_not_isStablyUniform : ¬ IsStablyUniform (JetA K) := sorry

/-- **[FJP] Theorem 1.1 (`𝓐°` is a ring of integral elements)**: the maximal plus ring
`ringPlus 𝓐 = 𝓐°` is open and integrally closed, hence a legitimate `A⁺`.

This is what stops `fjp_1_1_isSheafyComplete` being vacuous. `IsSheafyComplete 𝓐` quantifies
over `RingOfIntegralElements 𝓐`, a *subtype*; without an inhabitant the quantification says
nothing. Certifying this exhibits one, so sheafiness at `(𝓐, 𝓐°)` — the pair the paper
claims — follows by instantiating `fjp_1_1_isSheafyComplete` at `⟨𝓐°, this⟩`. -/
theorem fjp_1_1_powerBounded_isRingOfIntegralElements :
    IsRingOfIntegralElements ((ringPlus (JetA K) : Subring (JetA K))) := sorry

/-- **[FJP] Theorem 1.1 (the Tate extensions have a ring of integral elements)**: the maximal
plus ring of `𝓐⟨V₁,…,Vₙ⟩` is one, so `fjp_1_1_stronglySheafy` is not a vacuous quantification
either. The extension carries a basis-defined topology rather than a norm, so this does not
follow from the normed argument that covers `𝓐` itself. -/
theorem fjp_1_1_tateExt_powerBounded_isRingOfIntegralElements (n : ℕ) :
    letI := mvTateAlgebraTopology' (A := JetA K) n
    haveI := mvTate_isTateRing (A := JetA K) n
    haveI := mvTate_nonarchimedean (A := JetA K) n
    haveI := mvTateAlgebraTopology'_isTopologicalRing (A := JetA K) n
    IsRingOfIntegralElements
      (TopologicalRing.powerBoundedSubring.toSubring
        ↥(restrictedMvPowerSeriesSubring n (JetA K))) := sorry
