/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-D24.
-/
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Rank additivity in short exact sequences

For a short exact sequence `0 → M → N → P → 0` of `R`-modules:

* `Function.Exact.nonempty_linearEquiv_prod_of_projective`: if `P` is projective the
  sequence splits, `N ≃ₗ[R] M × P`.
* `Module.finrank_eq_add_of_exact`: if `M` and `P` are finite free,
  `finrank R N = finrank R M + finrank R P`.
* `Module.rankAtStalk_eq_add_of_exact`: if `M` and `P` are finite flat,
  `rankAtStalk N p = rankAtStalk M p + rankAtStalk P p` at every prime `p`
  (localize at `p`; finite flat over the local ring `R_p` is free).

This is the degree-additivity engine for sums of relative effective Cartier divisors
(KM 1.2.3: the ideal-product SES `0 → A/gA → A/fgA → A/fA → 0`).

Upstream candidates: mathlib has `Exact.splitSurjectiveEquiv` (splitting from a given
section), `Module.finrank_prod` and `Module.rankAtStalk_prod`, an Euler-characteristic
lemma over division rings, and the bundled single-universe analogue
`ModuleCat.free_shortExact_finrank_add` (`ShortComplex (ModuleCat R)`, one universe,
`Ring R`) — but none of the three statements above in unbundled, multi-universe,
Semiring/CommRing form.
-/

open Module

universe u v w x

section Split

variable {R : Type u} {M : Type v} {N : Type w} {P : Type x} [Semiring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]
  {f : M →ₗ[R] N} {g : N →ₗ[R] P}

/-- A short exact sequence `0 → M → N → P → 0` with `P` projective splits: `N ≅ M × P`. -/
theorem Function.Exact.nonempty_linearEquiv_prod_of_projective [Module.Projective R P]
    (h : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    Nonempty (N ≃ₗ[R] M × P) :=
  (projective_lifting_property g .id hg).elim fun l hl ↦ ⟨(h.splitSurjectiveEquiv hf ⟨l, hl⟩).1⟩

/-- Rank additivity in a short exact sequence `0 → M → N → P → 0` of modules with
`M` and `P` finite free. -/
theorem Module.finrank_eq_add_of_exact [StrongRankCondition R] [Module.Free R M] [Module.Finite R M]
    [Module.Free R P] [Module.Finite R P] (h : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) : finrank R N = finrank R M + finrank R P :=
  (h.nonempty_linearEquiv_prod_of_projective hf hg).elim fun e ↦ e.finrank_eq.trans finrank_prod

end Split

section RankAtStalk

variable {R : Type u} {M : Type v} {N : Type w} {P : Type x} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]
  {f : M →ₗ[R] N} {g : N →ₗ[R] P}

attribute [local instance] free_of_flat_of_isLocalRing in
/-- Pointwise rank additivity in a short exact sequence `0 → M → N → P → 0` with the
outer terms finite flat: `rank_p N = rank_p M + rank_p P` at every prime `p`. The middle
term needs no hypotheses. -/
theorem Module.rankAtStalk_eq_add_of_exact [Module.Finite R M] [Module.Flat R M] [Module.Finite R P]
    [Module.Flat R P] (h : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) (p : PrimeSpectrum R) :
    rankAtStalk N p = rankAtStalk M p + rankAtStalk P p := by
  simpa only [rankAtStalk_eq_finrank_tensorProduct] using finrank_eq_add_of_exact
    (f := f.baseChange (Localization.AtPrime p.asIdeal))
    (g := g.baseChange (Localization.AtPrime p.asIdeal)) (Flat.lTensor_exact _ h)
    (Flat.lTensor_preserves_injective_linearMap f hf) (LinearMap.lTensor_surjective _ hg)

end RankAtStalk
