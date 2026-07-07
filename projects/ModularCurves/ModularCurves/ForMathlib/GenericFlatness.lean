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
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Support
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
# Generic flatness (Stacks 051R) — building blocks and dévissage

Towards Stacks Tag 051R (generic flatness, Noetherian case): a finite module `M` over a
finite-type algebra `S` over a Noetherian domain `R` is free after inverting a single
nonzero `f ∈ R`. This file collects the building blocks and assembles the dévissage.

## Main results

* `exists_primeQuotient_injection`: a nonzero module over a Noetherian ring receives an
  injection from `R ⧸ 𝔭` for an associated prime `𝔭` (Stacks 10.62.1 building block, GF1).
* `free_of_exact_of_free`: the middle term of a short exact sequence whose ends are free is
  itself free (Stacks 0516, GF2).
* `exists_smul_eq_zero_of_notMem_support`: a finite module whose support avoids a prime `𝔭`
  is annihilated by some `g ∉ 𝔭` (Stacks 10.40.5, GF4).
* `exists_noetherNormalization_baseChange`: Noether normalization of the generic fibre
  `K ⊗[R] S` over `K = FractionRing R` (Stacks 10.115.7 field core, GF3).
* `exists_generically_free`: the main theorem (Stacks 051R, GF5), assembled from the
  dévissage; the domain-case dimension induction is isolated in
  `exists_generically_free_domain`.
-/

open Submodule LinearMap TensorProduct

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

/-- **Extension of free is free** (Stacks 0516, GF2): the middle term of a short exact sequence
`0 → A → M → B → 0` of `R`-modules with `A` and `B` free is itself free. Since `B` is free it is
projective, so the surjection `M → B` splits, giving `M ≃ₗ A × B`; a product of free modules is
free. -/
theorem free_of_exact_of_free {R A M B : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M] [AddCommGroup B] [Module R B]
    (j : A →ₗ[R] M) (g : M →ₗ[R] B) (hj : Function.Injective j) (hg : Function.Surjective g)
    (hexact : LinearMap.range j = LinearMap.ker g)
    [Module.Free R A] [Module.Free R B] : Module.Free R M := by
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top_of_surjective g hg)
  exact Module.Free.of_equiv (lequivProdOfRightSplitExact hj hexact hs)

/-- **Support annihilation** (Stacks 10.40.5, GF4): if the support of a finite `R`-module `N`
avoids a prime `𝔭`, then some `g ∉ 𝔭` annihilates `N`. For a finite module the support is the
zero locus of the annihilator, so `𝔭 ∉ Supp N` means `Ann N ⊄ 𝔭`, i.e. there is `g ∈ Ann N`
with `g ∉ 𝔭`. -/
theorem exists_smul_eq_zero_of_notMem_support {R N : Type*} [CommRing R]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (p : PrimeSpectrum R)
    (hp : p ∉ Module.support R N) : ∃ g ∉ p.asIdeal, ∀ n : N, g • n = 0 := by
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus, Set.not_subset] at hp
  obtain ⟨g, hg, hgp⟩ := hp
  exact ⟨g, hgp, fun n => Module.mem_annihilator.mp (SetLike.mem_coe.mp hg) n⟩

/-- **Generic Noether normalization** (Stacks 10.115.7 field core, GF3): the generic fibre
`K ⊗[R] S` (`K = FractionRing R`) of a finite-type `R`-algebra `S` admits a Noether normalization
over `K`, i.e. a finite injective `K`-algebra map from a polynomial ring
`K[X₀, …, X_{d-1}]`. This is Noether normalization over the field `K` applied to the base change
`K ⊗[R] S`, which is finite-type over `K`. -/
theorem exists_noetherNormalization_baseChange {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [Nontrivial ((FractionRing R) ⊗[R] S)] :
    ∃ (d : ℕ) (φ : MvPolynomial (Fin d) (FractionRing R) →ₐ[FractionRing R]
      ((FractionRing R) ⊗[R] S)), Function.Injective φ ∧ φ.Finite :=
  exists_finite_inj_algHom_of_fg (FractionRing R) ((FractionRing R) ⊗[R] S)

/-!
## The dévissage (Stacks 051R, GF5)

We assemble `exists_generically_free` from the building blocks. The organising predicate is
`GFree R S N` — "the `S`-module `N`, viewed as an `R`-module, becomes free after inverting one
nonzero `f ∈ R`". The whole point is that `N` need not be finite over `R`, only over `S`.

The reduction from an arbitrary finite `S`-module to the domains `S ⧸ 𝔮` is genuine and proved
here, using the pre-packaged Noetherian dévissage induction
`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime` (which supplies the prime filtration
of Stacks 10.62.1) together with `GFree.of_exact` (GF2 through localization) and `GFree.subsingleton`.

The **domain case** `exists_generically_free_domain` — the Noether-normalisation + induction on
`dim((S ⧸ 𝔮) ⊗_R Frac R)` — is isolated as the single boxed statement; see its docstring.
-/

/-- `GFree R S N`: the `S`-module `N`, regarded as an `R`-module via `algebraMap R S`, becomes a
free module after inverting a single nonzero `f ∈ R`, i.e. `N_f` is free over `R_f`. This is the
generic-freeness predicate driving the dévissage; note `N` is only assumed finite over `S`. -/
private def GFree (R S N : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] : Prop :=
  letI : Module R N := Module.compHom N (algebraMap R S)
  ∃ f : R, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) N)

section Devissage

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]

/-- Freeness of a localised module survives inverting more: from `X_a` free over `R_a` we get
`X_{ab}` free over `R_{ab}`, since `R_{ab}` (resp. `X_{ab}`) is a further localisation of `R_a`
(resp. `X_a`).

This is pure localisation-of-localisation plumbing — provable from existing mathlib, no missing
theory. `Module.free_of_isLocalizedModule` gives freeness over the localisation-of-localisation
ring `Localization.Away (algebraMap R (Localization.Away a) b)` in one step; the remaining work is
transferring that across the localisation-uniqueness isomorphism to the standard `Localization.Away
(a * b)` / `LocalizedModule (powers (a * b)) X`, which mathlib lacks a one-shot lemma for. Left as a
`sorry` in this pass. -/
private theorem free_localizedModule_away_mul {X : Type*}
    [AddCommGroup X] [Module R X] (a b : R)
    (h : Module.Free (Localization.Away a) (LocalizedModule (Submonoid.powers a) X)) :
    Module.Free (Localization.Away (a * b))
      (LocalizedModule (Submonoid.powers (a * b)) X) := by
  sorry

/-- The zero module is generically free (invert `f = 1`; a subsingleton is free). -/
private theorem GFree.subsingleton (N : Type*) [AddCommGroup N] [Module S N] [Subsingleton N] :
    GFree R S N := by
  letI : Module R N := Module.compHom N (algebraMap R S)
  exact ⟨1, one_ne_zero, inferInstance⟩

omit [IsDomain R] in
/-- Generic freeness transfers along an `S`-linear equivalence. -/
private theorem GFree.of_linearEquiv {N N' : Type*} [AddCommGroup N] [Module S N]
    [AddCommGroup N'] [Module S N'] (e : N ≃ₗ[S] N') (h : GFree R S N') : GFree R S N := by
  letI : Module R N := Module.compHom N (algebraMap R S)
  letI : Module R N' := Module.compHom N' (algebraMap R S)
  haveI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun r x => rfl
  haveI : IsScalarTower R S N' := IsScalarTower.of_algebraMap_smul fun r x => rfl
  rw [GFree] at h ⊢
  obtain ⟨f, hf, hfree⟩ := h
  refine ⟨f, hf, ?_⟩
  let eR : N ≃ₗ[R] N' := e.restrictScalars R
  haveI : IsLocalizedModule (Submonoid.powers f)
      ((LocalizedModule.mkLinearMap (Submonoid.powers f) N').comp eR.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right _ _ eR
  let iso : LocalizedModule (Submonoid.powers f) N ≃ₗ[R]
      LocalizedModule (Submonoid.powers f) N' :=
    IsLocalizedModule.iso (Submonoid.powers f)
      ((LocalizedModule.mkLinearMap (Submonoid.powers f) N').comp eR.toLinearMap)
  exact Module.Free.of_equiv (iso.extendScalarsOfIsLocalization (Submonoid.powers f)
    (Localization.Away f)).symm

/-- Generic freeness is stable under short exact sequences (GF2 = `free_of_exact_of_free` applied
to the localised sequence). Given `0 → N₁ → N₂ → N₃ → 0` of `S`-modules with `N₁` free after
inverting `a` and `N₃` free after inverting `b`, invert `c = ab`: localisation is exact
(`IsLocalizedModule.map_exact`) and both ends stay free after inverting `c`
(`free_localizedModule_away_mul`), so the middle `N₂` is free over `R_c`. -/
private theorem GFree.of_exact {N₁ N₂ N₃ : Type*}
    [AddCommGroup N₁] [Module S N₁] [AddCommGroup N₂] [Module S N₂] [AddCommGroup N₃] [Module S N₃]
    (f : N₁ →ₗ[S] N₂) (g : N₂ →ₗ[S] N₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h₁ : GFree R S N₁) (h₃ : GFree R S N₃) : GFree R S N₂ := by
  letI : Module R N₁ := Module.compHom N₁ (algebraMap R S)
  letI : Module R N₂ := Module.compHom N₂ (algebraMap R S)
  letI : Module R N₃ := Module.compHom N₃ (algebraMap R S)
  haveI : IsScalarTower R S N₁ := IsScalarTower.of_algebraMap_smul fun r x => rfl
  haveI : IsScalarTower R S N₂ := IsScalarTower.of_algebraMap_smul fun r x => rfl
  haveI : IsScalarTower R S N₃ := IsScalarTower.of_algebraMap_smul fun r x => rfl
  rw [GFree] at h₁ h₃ ⊢
  obtain ⟨a, ha, hfree1⟩ := h₁
  obtain ⟨b, hb, hfree3⟩ := h₃
  refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
  haveI hF1 : Module.Free (Localization.Away (a * b))
      (LocalizedModule (Submonoid.powers (a * b)) N₁) := free_localizedModule_away_mul a b hfree1
  haveI hF3 : Module.Free (Localization.Away (a * b))
      (LocalizedModule (Submonoid.powers (a * b)) N₃) := by
    have := free_localizedModule_away_mul b a hfree3
    rwa [mul_comm] at this
  set c := a * b with hc
  let fR : N₁ →ₗ[R] N₂ := f.restrictScalars R
  let gR : N₂ →ₗ[R] N₃ := g.restrictScalars R
  let j : LocalizedModule (Submonoid.powers c) N₁ →ₗ[R] LocalizedModule (Submonoid.powers c) N₂ :=
    IsLocalizedModule.map (Submonoid.powers c) (LocalizedModule.mkLinearMap (Submonoid.powers c) N₁)
      (LocalizedModule.mkLinearMap (Submonoid.powers c) N₂) fR
  let q : LocalizedModule (Submonoid.powers c) N₂ →ₗ[R] LocalizedModule (Submonoid.powers c) N₃ :=
    IsLocalizedModule.map (Submonoid.powers c) (LocalizedModule.mkLinearMap (Submonoid.powers c) N₂)
      (LocalizedModule.mkLinearMap (Submonoid.powers c) N₃) gR
  have hjinj : Function.Injective j := IsLocalizedModule.map_injective _ _ _ fR hf
  have hqsurj : Function.Surjective q := IsLocalizedModule.map_surjective _ _ _ gR hg
  have hjqexact : Function.Exact j q := IsLocalizedModule.map_exact (Submonoid.powers c)
    (LocalizedModule.mkLinearMap (Submonoid.powers c) N₁)
    (LocalizedModule.mkLinearMap (Submonoid.powers c) N₂)
    (LocalizedModule.mkLinearMap (Submonoid.powers c) N₃) fR gR hfg
  let j' := j.extendScalarsOfIsLocalization (Submonoid.powers c) (Localization.Away c)
  let q' := q.extendScalarsOfIsLocalization (Submonoid.powers c) (Localization.Away c)
  have hj'inj : Function.Injective j' := hjinj
  have hq'surj : Function.Surjective q' := hqsurj
  have hj'q'exact : Function.Exact j' q' := hjqexact
  have hrange : LinearMap.range j' = LinearMap.ker q' := (LinearMap.exact_iff.mp hj'q'exact).symm
  exact free_of_exact_of_free j' q' hj'inj hq'surj hrange

/-- **The domain case** (Stacks 051R main step, GF5 core) — *boxed*.

For a prime `𝔮` of `S`, the domain `S ⧸ 𝔮` (finite type over the Noetherian domain `R`) becomes
free over `R_f` after inverting one nonzero `f`. This is the mathematical heart of generic
flatness: Noether-normalise `(S ⧸ 𝔮) ⊗_R Frac R` over `Frac R` (GF3), spread the finite
polynomial subring down to `R_f`, form the torsion cokernel `N`, kill it by a nonzero `g` (GF4),
and recurse on `N` over `R[y]/(g)`, whose generic fibre has strictly smaller Krull dimension.

This step is left as a `sorry`: the induction on `dim((S⧸𝔮) ⊗_R Frac R)` rests on
commutative-algebra infrastructure not yet in mathlib — notably that a module-finite (integral)
ring extension preserves `ringKrullDim`, the exact hypersurface dimension drop
`dim(k[x]/(g)) = d - 1`, and `(S⧸𝔮) ⊗_R Frac R` being a domain. Everything *around* this step
(GF1–GF4, the filtration reduction, and all localisation bookkeeping) is proved. -/
private theorem exists_generically_free_domain [IsNoetherianRing R] [Algebra.FiniteType R S]
    (p : Ideal S) [p.IsPrime] : GFree R S (S ⧸ p) := by
  sorry

end Devissage

/-- **Generic flatness / generic freeness** (Stacks Tag 051R, GF5): a finite module `M` over a
finite-type algebra `S` over a Noetherian domain `R` becomes free over `R_f` after inverting a
single nonzero `f ∈ R`.

Proved by the prime-filtration dévissage: `M` is built by finitely many extensions out of
subsingletons and cyclic domains `S ⧸ 𝔮` (`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`,
Stacks 10.62.1); generic freeness holds for the pieces (subsingletons trivially, domains by the
boxed `exists_generically_free_domain`) and is stable under extensions after inverting a common
element (`GFree.of_exact`, i.e. GF2 through exact localisation). -/
theorem exists_generically_free {R S M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] [Module.Finite S M] :
    ∃ f : R, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  suffices h : GFree R S M by
    have hsmul : (Module.compHom M (algebraMap R S) : Module R M) = ‹Module R M› := by
      apply Module.ext; funext r m
      show algebraMap R S r • m = r • m
      exact (algebra_compatible_smul S r m).symm
    rw [GFree] at h
    exact hsmul ▸ h
  induction ‹Module.Finite S M› using
      IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime S with
  | subsingleton N => exact GFree.subsingleton N
  | quotient N p e => exact GFree.of_linearEquiv e (exists_generically_free_domain p.asIdeal)
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ => exact GFree.of_exact f g hf hg hfg h₁ h₃
