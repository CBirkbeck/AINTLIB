/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-GF* (generic flatness).
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Generic flatness (Stacks 051R) — building blocks

Towards Stacks Tag 051R (generic flatness, Noetherian case): a finite module `M` over a
finite-type algebra `S` over a Noetherian domain `R` is free after inverting a single
nonzero `f ∈ R`. This file collects the building blocks; the main dévissage and the
downstream flat-locus openness live alongside.

## Main results

* `exists_primeQuotient_injection`: a nonzero module over a Noetherian ring receives an
  injection from `R ⧸ 𝔭` for an associated prime `𝔭` (Stacks 10.62.1 building block).
-/

open Submodule LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Prime-quotient injection** (Stacks 10.62.1 building block): a nonzero module over a
Noetherian ring receives an injection from `R ⧸ 𝔭` for some prime `𝔭`. Take an associated
prime `𝔭 = Ann(x)`; then `r ↦ r • x` has kernel `𝔭` and descends to an injection. -/
theorem exists_primeQuotient_injection [IsNoetherianRing R] [Nontrivial M] :
    ∃ p : Ideal R, p.IsPrime ∧ ∃ f : (R ⧸ p) →ₗ[R] M, Function.Injective f := by
  obtain ⟨I, hI⟩ := associatedPrimes.nonempty R M
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hI
  obtain ⟨hIprime, x, hx⟩ := hI
  have hker : LinearMap.ker (toSpanSingleton R M x) = I := by
    ext r
    simp only [LinearMap.mem_ker, toSpanSingleton_apply, hx, mem_colon_singleton, mem_bot]
  refine ⟨I, hIprime, I.liftQ (toSpanSingleton R M x) hker.ge, ?_⟩
  rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot']
  exact hker.symm
