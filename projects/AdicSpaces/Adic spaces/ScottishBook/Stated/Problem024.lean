/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».Presheaf
import «Adic spaces».HuberRings
import «Adic spaces».FJP.FiniteJetScottishBook
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization

/-!
# Nonarchimedean Scottish Book — Problem 24

**Proposer:** Kiran Kedlaya
**Date:** 16 September 2016

## Problem Statement

Let (A, A+) → (B, B+) be a rational localization of Huber-Tate pairs. Is the morphism
A → B necessarily flat?

## Notes

- True in the strongly noetherian case (due to Huber).
- For stably uniform pairs, "pseudoflatness" is shown in [KL2].

## Status

**Answered negatively** (`problem24_completed_false`): the [FJP] finite-jet algebra `𝓐`
over `K = F((t))` — for any field `F` — is a complete **uniform sheafy** Tate domain,
only not strongly noetherian, exactly the case the problem leaves open, and its completed
rational localization at the chart datum `(W; ϖ)` is not flat.

The obstruction is the Problem-28 witness (see `Problem028.lean`): the element `f = Q²`
is a nonzerodivisor of `𝓐` (multiplication by it is an isometry), but its image in
`𝓐⟨W/ϖ⟩` is `0`. Flatness of `𝓐 → 𝓐⟨W/ϖ⟩` would force the nonzerodivisor `f` to act
injectively on `𝓐⟨W/ϖ⟩` (`Module.Flat.isSMulRegular_of_nonZeroDivisors`), whereas it acts
as multiplication by `0` on a nonzero ring.

Note the failure is invisible before completion: `ϖ` is a unit of the Tate ring `𝓐`, so
the algebraic localization `Localization.Away ϖ` is just `𝓐`. Accordingly the *algebraic*
form of the question (`problem24_algebraic`) is a triviality — every localization is flat
— and only the completed form has content.

## Definitions needed

- **Rational localization flatness**: whether the canonical map A → B arising from a
  rational localization (A, A⁺) → (B, B⁺) is a flat ring homomorphism.

## References

* Kedlaya, *The Nonarchimedean Scottish Book*, Problem 24
* Wedhorn, *Adic Spaces*, §8.1 (rational localizations)
* Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*
* [FJP] §3 (Proposition 3.1) — the chart `𝓐⟨W/ϖ⟩ ≅ K⟨X,Q⟩/(Q²)`
-/

open ValuationSpectrum

namespace ScottishBook

universe u

/-! ### The algebraic form: always true, and empty of content -/

/-- **Problem 24, algebraic version — true, but vacuous.** For any ring `A` and any
rational localization datum `D`, the *algebraic* localization `Localization.Away D.s` is
flat over `A`: every localization is. The content of Problem 24 lies entirely in the
completed localization (below); note that for a Tate ring one may always take `D.s` to be
a unit, in which case `Localization.Away D.s` is `A` itself. -/
theorem problem24_algebraic (A : Type u) [CommRing A] [TopologicalSpace A]
    [PlusSubring A] [IsTateRing A] (D : RationalLocData A) :
    Module.Flat A (Localization.Away D.s) :=
  inferInstance

/-! ### The completed form: false -/

/-- **Scottish Book Problem 24 — negative answer.**

*It is **not** the case that the completed rational localization `A → A⟨T/s⟩` of a Tate
pair is always flat* — not even for a **complete uniform sheafy** Tate domain `A` (the
only missing hypothesis being strong noetherianity, which is exactly what Huber's positive
result uses).

The counterexample is the [FJP] finite-jet algebra over the Laurent series field
`K = F((t))`, at its chart datum `(W; ϖ)` — for **every** field `F`, in every universe,
with no hypothesis on `F`. See `finiteJet_not_flat_canonicalMap` and the discussion in
`Problem028.lean`. -/
theorem problem24_completed_false (F : Type u) [Field F] :
    ¬ ∀ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : PlusSubring A) (_ : IsHuberRing A) (_ : IsTateRing A)
        (D : RationalLocData A),
        @Module.Flat A (presheafValue D) _ _ (RingHom.toModule D.canonicalMap) := by
  intro h
  exact FiniteJet.finiteJet_not_flat_canonicalMap F
    (h (FiniteJet.JetA F) inferInstance inferInstance inferInstance inferInstance
      inferInstance (FiniteJet.chartDatum F))

/-- The same statement in existential form: there is a Tate pair and a rational datum
whose completed rational localization is not flat. -/
theorem exists_rationalLoc_not_flat (F : Type u) [Field F] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : PlusSubring A) (_ : IsHuberRing A) (_ : IsTateRing A)
      (D : RationalLocData A),
      ¬ @Module.Flat A (presheafValue D) _ _ (RingHom.toModule D.canonicalMap) :=
  ⟨FiniteJet.JetA F, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, FiniteJet.chartDatum F, FiniteJet.finiteJet_not_flat_canonicalMap F⟩

end ScottishBook
