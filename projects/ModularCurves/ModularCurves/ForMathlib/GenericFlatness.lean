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
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Polynomial.Basic

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
## Transcendence-degree dimension theory (for the domain-case induction)

The domain-case induction of Stacks 051R is run on the transcendence degree
`Algebra.trdeg R (S ⧸ 𝔮)` (a well-defined natural number by `trdeg_lt_aleph0`). The mathematical
crux — that a nonzero element cuts transcendence degree down — is `trdeg_quotient_prime_lt`: for a
prime `𝔮'` of a polynomial ring `R[X₁,…,X_d]` (`d ≥ 1`) containing a nonzero `g`, the quotient
domain has strictly smaller transcendence degree. This is the "a hypersurface in `𝔸ᵈ` has
dimension `< d`" fact, proved here from scratch via algebraic independence (mathlib lacks the
`dim = trdeg` bridge and the field-polynomial hypersurface drop). -/

section PolynomialTrdeg
open scoped Polynomial
open Cardinal

/-- Evaluation of a multivariate polynomial at a `Fin.cons`ed point factors through
`finSuccEquiv`: evaluating `f` at `(y, s₀, …, s_{n-1})` equals evaluating the univariate image of
`f` (coefficients pushed through `aeval s`) at `y`. -/
private theorem aeval_cons_eq' {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
    (s : Fin n → B) (y : B) (f : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.aeval (Fin.cons y s : Fin (n + 1) → B) f
      = Polynomial.aeval y (Polynomial.mapAlgHom (MvPolynomial.aeval s)
          (MvPolynomial.finSuccEquiv R n f)) := by
  have key : (MvPolynomial.aeval (Fin.cons y s : Fin (n + 1) → B) :
        MvPolynomial (Fin (n + 1)) R →ₐ[R] B)
      = ((Polynomial.aeval y).restrictScalars R).comp
          ((Polynomial.mapAlgHom (MvPolynomial.aeval s)).comp
            (MvPolynomial.finSuccEquiv R n).toAlgHom) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [MvPolynomial.finSuccEquiv_X_zero]
    · simp [MvPolynomial.finSuccEquiv_X_succ]
  exact DFunLike.congr_fun key f

/-- If `g ≠ 0` in a domain and `q(g) = 0` for a univariate polynomial `q`, then `g` divides the
trailing coefficient of `q`. (Factor out `X ^ natTrailingDegree`, cancel `g ^ k`, then the constant
term of the cofactor is `≡ 0 mod g`.) -/
private theorem dvd_trailingCoeff_of_eval {B : Type*} [CommRing B] [IsDomain B] {g : B} (hg : g ≠ 0)
    {q : B[X]} (h : Polynomial.eval g q = 0) : g ∣ q.trailingCoeff := by
  set k := q.natTrailingDegree with hk
  have hdvd : (Polynomial.X : B[X]) ^ k ∣ q := by
    rw [Polynomial.X_pow_dvd_iff]; intro e he
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree he
  obtain ⟨q₁, hq₁⟩ := hdvd
  have heval : g ^ k * Polynomial.eval g q₁ = 0 := by
    have h2 := h; rw [hq₁] at h2; simpa [Polynomial.eval_mul, Polynomial.eval_pow] using h2
  have hq1eval : Polynomial.eval g q₁ = 0 := by
    rcases mul_eq_zero.mp heval with h1 | h1
    · exact absurd h1 (pow_ne_zero k hg)
    · exact h1
  have hcoeff : q.trailingCoeff = q₁.coeff 0 := by
    rw [Polynomial.trailingCoeff, ← hk, hq₁]; simpa using Polynomial.coeff_X_pow_mul q₁ k 0
  have hsub : g ∣ Polynomial.eval g q₁ - Polynomial.eval 0 q₁ := by
    simpa using Polynomial.sub_dvd_eval_sub g 0 q₁
  rw [hq1eval, zero_sub, dvd_neg] at hsub
  rw [hcoeff, Polynomial.coeff_zero_eq_eval_zero]; exact hsub

/-- **Hypersurface transcendence drop.** For `d ≥ 1`, a prime `𝔮'` of `R[X₀,…,X_{d-1}]` containing a
nonzero `g`, the quotient domain has transcendence degree strictly below that of the polynomial
ring. Proof: were there `d` algebraically independent elements in the quotient, lifting them and
adjoining `g` would give `d + 1` "almost independent" elements, but `g` satisfies a nontrivial
algebraic relation over the lift (trdeg of the polynomial ring is `d`), whose trailing coefficient
is a nonzero element of the lifted subring divisible by `g` — hence a nonzero relation among the
`d` elements in the quotient, a contradiction. -/
private theorem trdeg_quotient_prime_lt {R : Type*} [CommRing R] [IsDomain R] {d : ℕ} (hd : 1 ≤ d)
    {g : MvPolynomial (Fin d) R} (hg : g ≠ 0) (q' : Ideal (MvPolynomial (Fin d) R)) [q'.IsPrime]
    (hgq : g ∈ q') :
    Algebra.trdeg R (MvPolynomial (Fin d) R ⧸ q')
      < Algebra.trdeg R (MvPolynomial (Fin d) R) := by
  have hPd : Algebra.trdeg R (MvPolynomial (Fin d) R) = (d : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain]; simp
  rw [hPd]
  set C := MvPolynomial (Fin d) R ⧸ q' with hC
  haveI : IsDomain C := Ideal.Quotient.isDomain q'
  by_cases hinj : Function.Injective (algebraMap R C)
  · haveI : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).mpr hinj
    have hfin : Algebra.trdeg R C < ℵ₀ := trdeg_lt_aleph0
    by_contra hcon
    push_neg at hcon
    obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' R C
    have hmk : (#ι) = Algebra.trdeg R C := hx.cardinalMk_eq_trdeg
    haveI : Finite ι := Cardinal.lt_aleph0_iff_finite.mp (hmk ▸ hfin)
    haveI : Fintype ι := Fintype.ofFinite ι
    have hdcard : d ≤ Fintype.card ι := by
      have h2 : Cardinal.toNat (d : Cardinal) ≤ Cardinal.toNat (Algebra.trdeg R C) :=
        Cardinal.toNat_le_toNat hcon hfin
      rw [Cardinal.toNat_natCast] at h2
      rwa [← Cardinal.mk_toNat_eq_card, hmk]
    obtain ⟨emb⟩ : Nonempty (Fin d ↪ ι) := by
      apply Function.Embedding.nonempty_of_card_le; simpa using hdcard
    set f : Fin d → C := x ∘ emb with hf
    have hfai : AlgebraicIndependent R f := hx.1.comp emb emb.injective
    choose F hF using fun i => Ideal.Quotient.mk_surjective (f i)
    have hnotai :
        ¬ AlgebraicIndependent R (Fin.cons g F : Fin (d + 1) → MvPolynomial (Fin d) R) := by
      intro hai
      have hle : (d : ℕ) + 1 ≤ d := by
        have h3 := hai.lift_cardinalMk_le_trdeg
        rw [hPd] at h3
        simpa [Cardinal.mk_fin, Cardinal.lift_natCast] using h3
      omega
    rw [AlgebraicIndependent, Function.Injective] at hnotai
    push_neg at hnotai
    obtain ⟨a, b, hab, hne⟩ := hnotai
    have hPol0 : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hPolev :
        MvPolynomial.aeval (Fin.cons g F : Fin (d + 1) → MvPolynomial (Fin d) R) (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    rw [aeval_cons_eq' F g (a - b)] at hPolev
    set qB := Polynomial.mapAlgHom (MvPolynomial.aeval F) (MvPolynomial.finSuccEquiv R d (a - b))
      with hqB
    have hevalqB : Polynomial.eval g qB = 0 := by
      rw [← Polynomial.coe_aeval_eq_eval]; exact hPolev
    have haevalFinj : Function.Injective
        (MvPolynomial.aeval F : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R) := by
      have hFai : AlgebraicIndependent R F := by
        rw [AlgebraicIndependent]
        have hcompeq : (MvPolynomial.aeval f : MvPolynomial (Fin d) R →ₐ[R] C)
            = (Ideal.Quotient.mkₐ R q').comp (MvPolynomial.aeval F) := by
          rw [MvPolynomial.comp_aeval]; congr 1; funext i; exact (hF i).symm
        have hfinj : Function.Injective (MvPolynomial.aeval f) := hfai
        rw [hcompeq] at hfinj
        exact fun p1 p2 h12 => hfinj (by rw [AlgHom.comp_apply, AlgHom.comp_apply, h12])
      exact hFai
    have hcoeffqB : ∀ m, qB.coeff m
        = MvPolynomial.aeval F ((MvPolynomial.finSuccEquiv R d (a - b)).coeff m) := by
      intro m
      rw [hqB, show Polynomial.mapAlgHom (MvPolynomial.aeval F)
          (MvPolynomial.finSuccEquiv R d (a - b))
          = Polynomial.map (MvPolynomial.aeval F :
            MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R).toRingHom
            (MvPolynomial.finSuccEquiv R d (a - b)) from rfl, Polynomial.coeff_map]
      rfl
    have hqB0 : qB ≠ 0 := by
      rw [hqB, show Polynomial.mapAlgHom (MvPolynomial.aeval F)
          (MvPolynomial.finSuccEquiv R d (a - b))
          = Polynomial.map (MvPolynomial.aeval F :
            MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) R).toRingHom
            (MvPolynomial.finSuccEquiv R d (a - b)) from rfl]
      intro h0
      have h1 : MvPolynomial.finSuccEquiv R d (a - b) ≠ 0 := fun h =>
        hPol0 ((MvPolynomial.finSuccEquiv R d).injective (by rw [h]; simp))
      exact h1 (Polynomial.map_injective _ haevalFinj (by rw [h0]; simp))
    have hc0 : qB.trailingCoeff ≠ 0 := Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hqB0
    have hgc : g ∣ qB.trailingCoeff := dvd_trailingCoeff_of_eval hg hevalqB
    set Q' := (MvPolynomial.finSuccEquiv R d (a - b)).coeff qB.natTrailingDegree with hQ'
    have hcQ : MvPolynomial.aeval F Q' = qB.trailingCoeff := by
      rw [Polynomial.trailingCoeff]; exact (hcoeffqB _).symm
    have hQ'0 : Q' ≠ 0 := by
      intro h0; rw [h0, map_zero] at hcQ; exact hc0 hcQ.symm
    have hmem : MvPolynomial.aeval F Q' ∈ q' := by
      rw [hcQ]
      exact (Ideal.span_singleton_le_iff_mem q').mpr hgq (Ideal.mem_span_singleton.mpr hgc)
    have hfeval : MvPolynomial.aeval f Q' = 0 := by
      have hFf : (fun i => (Ideal.Quotient.mkₐ R q') (F i)) = f := by
        funext i; rw [Ideal.Quotient.mkₐ_eq_mk]; exact hF i
      have e1 : (Ideal.Quotient.mkₐ R q') (MvPolynomial.aeval F Q') = MvPolynomial.aeval f Q' := by
        rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, hFf]
      rw [← e1, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hmem
    exact hQ'0 (hfai (by rw [hfeval, map_zero]))
  · rw [trdeg_eq_zero_of_not_injective hinj]
    exact_mod_cast hd

end PolynomialTrdeg

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

omit [IsDomain R] in
/-- Freeness of a localised module survives inverting more: from `X_a` free over `R_a` we get
`X_{ab}` free over `R_{ab}`, since `R_{ab}` (resp. `X_{ab}`) is a further localisation of `R_a`
(resp. `X_a`).

`Module.free_of_isLocalizedModule` gives freeness over the iterated ring
`Localization.Away (algebraMap R (Localization.Away a) b)`; base change composes
(`IsBaseChange.comp`), so via `isLocalizedModule_iff_isBaseChange` the iterated module is a
localisation of `X` at `powers (a*b)`; then `IsLocalization.algEquiv` supplies the ring iso to the
standard `Localization.Away (a * b)` and `Module.Free.of_equiv` transports freeness across the
resulting semilinear equivalence. -/
private theorem free_localizedModule_away_mul {X : Type*}
    [AddCommGroup X] [Module R X] (a b : R)
    (h : Module.Free (Localization.Away a) (LocalizedModule (Submonoid.powers a) X)) :
    Module.Free (Localization.Away (a * b))
      (LocalizedModule (Submonoid.powers (a * b)) X) := by
  haveI := h
  -- Freeness over the iterated ring `T = Localization.Away (image of b in R_a)`.
  have hfreeT : Module.Free (Localization.Away (algebraMap R (Localization.Away a) b))
      (LocalizedModule (Submonoid.powers (algebraMap R (Localization.Away a) b))
        (LocalizedModule (Submonoid.powers a) X)) :=
    Module.free_of_isLocalizedModule (R := Localization.Away a)
      (Submonoid.powers (algebraMap R (Localization.Away a) b))
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R (Localization.Away a) b))
        (LocalizedModule (Submonoid.powers a) X))
  set mk_a := LocalizedModule.mkLinearMap (Submonoid.powers a) X with hmk_a
  set mk_bS := LocalizedModule.mkLinearMap
    (Submonoid.powers (algebraMap R (Localization.Away a) b))
    (LocalizedModule (Submonoid.powers a) X) with hmk_bS
  -- The composite `X → X_a → X_{ab}` is a localisation of `X` at `powers (a*b)` (base change
  -- composes).
  have hbc : IsBaseChange (Localization.Away (algebraMap R (Localization.Away a) b))
      ((mk_bS.restrictScalars R).comp mk_a) :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers a) (Localization.Away a) mk_a).comp
      (IsLocalizedModule.isBaseChange
        (Submonoid.powers (algebraMap R (Localization.Away a) b))
        (Localization.Away (algebraMap R (Localization.Away a) b)) mk_bS)
  have hLM : IsLocalizedModule (Submonoid.powers (a * b)) ((mk_bS.restrictScalars R).comp mk_a) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers (a * b))
      (Localization.Away (algebraMap R (Localization.Away a) b))
      ((mk_bS.restrictScalars R).comp mk_a)).mpr hbc
  have hLMab : IsLocalizedModule (Submonoid.powers (a * b))
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) X) := inferInstance
  -- `R`-linear equivalence between the two localisations of `X` at `powers (a*b)`.
  have φ := IsLocalizedModule.linearEquiv (Submonoid.powers (a * b))
    ((mk_bS.restrictScalars R).comp mk_a)
    (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) X)
  -- Ring iso `T ≃ₐ[R] R_{ab}` (both localise `R` at `powers (a*b)`).
  let σA : (Localization.Away (algebraMap R (Localization.Away a) b)) ≃ₐ[R]
      (Localization.Away (a * b)) :=
    IsLocalization.algEquiv (Submonoid.powers (a * b)) _ _
  -- `φ` is semilinear over `σA`.
  have hsl : ∀ (t : Localization.Away (algebraMap R (Localization.Away a) b))
      (y : LocalizedModule (Submonoid.powers (algebraMap R (Localization.Away a) b))
        (LocalizedModule (Submonoid.powers a) X)),
      φ (t • y) = σA t • φ y := by
    intro t y
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (Submonoid.powers (a * b)) t
    simp only at hrs
    have hu := IsLocalizedModule.map_units
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) X) s
    have eL : (↑s : R) • φ (t • y) = r • φ y := by
      rw [← map_smul φ,
        ← algebraMap_smul (A := Localization.Away (algebraMap R (Localization.Away a) b))
          (↑s : R) (t • y),
        smul_smul,
        mul_comm (algebraMap R (Localization.Away (algebraMap R (Localization.Away a) b)) (↑s : R)) t,
        hrs, algebraMap_smul, map_smul φ]
    have hsc : (↑s : R) • σA t = algebraMap R (Localization.Away (a * b)) r := by
      rw [← algebraMap_smul (A := Localization.Away (a * b)) (↑s : R) (σA t), smul_eq_mul,
        ← σA.commutes (↑s : R), ← map_mul,
        mul_comm (algebraMap R (Localization.Away (algebraMap R (Localization.Away a) b)) (↑s : R)) t,
        hrs, σA.commutes r]
    have eR : (↑s : R) • (σA t • φ y) = r • φ y := by
      rw [← smul_assoc, hsc, algebraMap_smul]
    apply ((Module.End.isUnit_iff _).mp hu).injective
    simp only [Module.algebraMap_end_apply]
    rw [eL, eR]
  -- Assemble the semilinear equivalence and transport freeness.
  haveI := hfreeT
  haveI := RingHomInvPair.of_ringEquiv σA.toRingEquiv
  haveI := RingHomInvPair.of_ringEquiv σA.toRingEquiv.symm
  let e₂ : (LocalizedModule (Submonoid.powers (algebraMap R (Localization.Away a) b))
        (LocalizedModule (Submonoid.powers a) X)) ≃ₛₗ[(σA.toRingEquiv :
        (Localization.Away (algebraMap R (Localization.Away a) b)) →+*
        (Localization.Away (a * b)))]
      (LocalizedModule (Submonoid.powers (a * b)) X) :=
    { toFun := φ
      map_add' := fun x y => φ.map_add x y
      map_smul' := fun t y => hsl t y
      invFun := φ.symm
      left_inv := φ.left_inv
      right_inv := φ.right_inv }
  exact Module.Free.of_equiv e₂

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

/-!
### `R`-module generic freeness `GF`

The domain-case induction switches the ambient algebra (from `S` to a polynomial ring `R[X]` and to
its prime quotients). To carry it out cleanly we work with the ambient-algebra-free predicate `GF N`
("`N`, as an `R`-module, is free after inverting one nonzero element"), which is exactly `GFree R S N`
with `S` forgotten. All the closure properties of `GFree` are re-established for `GF` (the proofs are
identical, only simpler as no `restrictScalars` is needed). -/

/-- `GF R N`: the `R`-module `N` becomes free after inverting a single nonzero `f ∈ R`. This is
`GFree R S N` with the ambient algebra `S` stripped away, so it is insensitive to how `N`'s
`R`-module structure arises. -/
private def GF (R N : Type*) [CommRing R] [AddCommGroup N] [Module R N] : Prop :=
  ∃ f : R, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) N)

/-- A free `R`-module is generically free (invert `1`; a localisation of a free module is free). -/
private theorem GF.of_free (N : Type*) [AddCommGroup N] [Module R N] [Module.Free R N] : GF R N :=
  ⟨1, one_ne_zero, Module.free_of_isLocalizedModule (Submonoid.powers (1 : R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (1 : R)) N)⟩

/-- A subsingleton `R`-module is generically free. -/
private theorem GF.of_subsingleton (N : Type*) [AddCommGroup N] [Module R N] [Subsingleton N] :
    GF R N :=
  ⟨1, one_ne_zero, inferInstance⟩

omit [IsDomain R] in
/-- Generic freeness transfers along an `R`-linear equivalence. -/
private theorem GF.of_linearEquiv {N N' : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (e : N ≃ₗ[R] N') (h : GF R N') : GF R N := by
  obtain ⟨f, hf, hfree⟩ := h
  refine ⟨f, hf, ?_⟩
  haveI : IsLocalizedModule (Submonoid.powers f)
      ((LocalizedModule.mkLinearMap (Submonoid.powers f) N').comp e.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right _ _ e
  let iso : LocalizedModule (Submonoid.powers f) N ≃ₗ[R]
      LocalizedModule (Submonoid.powers f) N' :=
    IsLocalizedModule.iso (Submonoid.powers f)
      ((LocalizedModule.mkLinearMap (Submonoid.powers f) N').comp e.toLinearMap)
  exact Module.Free.of_equiv (iso.extendScalarsOfIsLocalization (Submonoid.powers f)
    (Localization.Away f)).symm

/-- Generic freeness is stable under short exact sequences of `R`-modules. -/
private theorem GF.of_exact {N₁ N₂ N₃ : Type*}
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (h₁ : GF R N₁) (h₃ : GF R N₃) : GF R N₂ := by
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
  let j : LocalizedModule (Submonoid.powers c) N₁ →ₗ[R] LocalizedModule (Submonoid.powers c) N₂ :=
    IsLocalizedModule.map (Submonoid.powers c) (LocalizedModule.mkLinearMap (Submonoid.powers c) N₁)
      (LocalizedModule.mkLinearMap (Submonoid.powers c) N₂) f
  let q : LocalizedModule (Submonoid.powers c) N₂ →ₗ[R] LocalizedModule (Submonoid.powers c) N₃ :=
    IsLocalizedModule.map (Submonoid.powers c) (LocalizedModule.mkLinearMap (Submonoid.powers c) N₂)
      (LocalizedModule.mkLinearMap (Submonoid.powers c) N₃) g
  have hjinj : Function.Injective j := IsLocalizedModule.map_injective _ _ _ f hf
  have hqsurj : Function.Surjective q := IsLocalizedModule.map_surjective _ _ _ g hg
  have hjqexact : Function.Exact j q := IsLocalizedModule.map_exact (Submonoid.powers c)
    (LocalizedModule.mkLinearMap (Submonoid.powers c) N₁)
    (LocalizedModule.mkLinearMap (Submonoid.powers c) N₂)
    (LocalizedModule.mkLinearMap (Submonoid.powers c) N₃) f g hfg
  let j' := j.extendScalarsOfIsLocalization (Submonoid.powers c) (Localization.Away c)
  let q' := q.extendScalarsOfIsLocalization (Submonoid.powers c) (Localization.Away c)
  have hj'inj : Function.Injective j' := hjinj
  have hq'surj : Function.Surjective q' := hqsurj
  have hj'q'exact : Function.Exact j' q' := hjqexact
  have hrange : LinearMap.range j' = LinearMap.ker q' := (LinearMap.exact_iff.mp hj'q'exact).symm
  exact free_of_exact_of_free j' q' hj'inj hq'surj hrange

/-- `GFree R S N` follows from `GF N` when the `R`- and `S`-module structures are compatible
(`IsScalarTower R S N`): both express "`N_f` is free over `R_f` for one nonzero `f`", read off the
same `R`-module structure. -/
omit [IsDomain R] in
private theorem GFree.of_GF {N : Type*} [AddCommGroup N] [Module S N] [Module R N]
    [IsScalarTower R S N] (h : GF R N) : GFree R S N := by
  have hst : (Module.compHom N (algebraMap R S) : Module R N) = ‹Module R N› := by
    apply Module.ext; funext r m
    show algebraMap R S r • m = r • m
    exact (algebra_compatible_smul S r m).symm
  rw [GFree]
  exact hst.symm ▸ h

/-- Killed-by-a-scalar modules are generically free: if a nonzero `f : R` annihilates the
`R`-module `N`, then `GF R N` (invert `f`; the localisation `N_f` is a subsingleton — every
`mk x s = mk (f • x) (f * s) = 0` — hence free). This is the vanishing-fibre base case of the
domain induction (`R → B` not injective ⇒ `B` is `R`-torsion) and handles the torsion cokernel
killed by an element of `R`. -/
private theorem GF.of_smul_eq_zero {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    {f : R} (hf : f ≠ 0) (hann : ∀ x : N, f • x = 0) : GF R N := by
  refine ⟨f, hf, ?_⟩
  have hsub : Subsingleton (LocalizedModule (Submonoid.powers f) N) := by
    refine ⟨fun a b => ?_⟩
    have hz : ∀ y : LocalizedModule (Submonoid.powers f) N, y = 0 := by
      intro y
      induction y using LocalizedModule.induction_on with
      | _ x s =>
        have hu : IsUnit (algebraMap R (Localization.Away f) f) :=
          IsLocalization.Away.algebraMap_isUnit f
        rw [← hu.smul_eq_zero (x := LocalizedModule.mk x s), algebraMap_smul,
          LocalizedModule.smul'_mk, hann x, LocalizedModule.zero_mk]
    rw [hz a, hz b]
  infer_instance

universe u

/-- **The domain case, injective core** (Stacks 051R main step, GF5 heart) — *boxed*.

`B` is a domain, finite type over the Noetherian domain `R`, with `R ↪ B` (so `B` is
`R`-torsion-free). Then `B` is generically free over `R`, *given* generic freeness for every
domain of strictly smaller transcendence degree (the induction hypothesis `IH`).

Mathematically: Noether-normalise the generic fibre `B ⊗_R Frac R` over `Frac R`
(`exists_noetherNormalization_baseChange`, GF3) to get `Frac R[y₁,…,y_d] ↪ B ⊗_R Frac R` finite
with `d = trdeg R B`; clear denominators so the `yᵢ` lie in `B`, giving a polynomial subring
`P = R[y₁,…,y_d] ↪ B` (`trdeg R P = d`) over which `B` becomes module-finite after inverting a
single nonzero element of `R` (generic finiteness). A basis of `Frac B` over `Frac P` spans a
free `P`-submodule `P^r ↪ B` with finite torsion cokernel `N`, killed by a nonzero `g ∈ P`
(`exists_smul_eq_zero_of_notMem_support`, GF4). Since `P^r` is `R`-free (`GF.of_free`) and `N` —
filtered over `P ⧸ (g)` into prime quotients `P ⧸ 𝔮` with `𝔮 ∋ g`, each of transcendence degree
`< d` by `trdeg_quotient_prime_lt` — is generically free by `IH`, the defining short exact
sequence `0 → P^r → B → N → 0` gives `GF R B` via `GF.of_exact` (GF2).

Left as a `sorry`: the construction of this sequence rests on the generic-finiteness descent
(module-finiteness of `B` over `P` after inverting an element of `R`) plus the choice of the free
`P`-submodule with finite torsion cokernel — commutative-algebra input not yet in mathlib.
Everything the induction is assembled *from* (GF1–GF4, `trdeg_quotient_prime_lt`, the
transcendence induction, the non-injective base case, and all localisation bookkeeping) is
proved. -/
private theorem gf_of_injective_domain {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (B : Type u) [CommRing B] [IsDomain B] [Algebra R B] [Algebra.FiniteType R B]
    (hinj : Function.Injective (algebraMap R B))
    (IH : ∀ (C : Type u) [CommRing C] [IsDomain C] [Algebra R C] [Algebra.FiniteType R C],
      Algebra.trdeg R C < Algebra.trdeg R B → GF R C) :
    GF R B := by
  sorry

/-- **Domain-case transcendence induction** (Stacks 051R main step, GF5): every domain `B` of
finite type over the Noetherian domain `R` with `trdeg R B ≤ n` is generically free over `R`.
Strong induction on `n`: if `R → B` is not injective, `B` is `R`-torsion and `GF.of_smul_eq_zero`
finishes; otherwise `gf_of_injective_domain` runs the Noether-normalisation dévissage, whose
recursive pieces have strictly smaller transcendence degree and are supplied by the induction
hypothesis. -/
private theorem gf_of_trdeg_le {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] :
    ∀ (n : ℕ) (B : Type u) [CommRing B] [IsDomain B] [Algebra R B] [Algebra.FiniteType R B],
      Algebra.trdeg R B ≤ (n : Cardinal) → GF R B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro B _ _ _ _ hn
    by_cases hinj : Function.Injective (algebraMap R B)
    · refine gf_of_injective_domain B hinj (fun C _ _ _ _ hCB => ?_)
      have hm : Algebra.trdeg R C = ((Algebra.trdeg R C).toNat : Cardinal) :=
        (Cardinal.cast_toNat_of_lt_aleph0 trdeg_lt_aleph0).symm
      have hmn : (Algebra.trdeg R C).toNat < n := by
        have h1 : Algebra.trdeg R C < (n : Cardinal) := lt_of_lt_of_le hCB hn
        rw [hm] at h1; exact_mod_cast h1
      exact IH _ hmn C (le_of_eq hm)
    · rw [RingHom.injective_iff_ker_eq_bot] at hinj
      obtain ⟨f, hfker, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinj
      rw [RingHom.mem_ker] at hfker
      exact GF.of_smul_eq_zero hf0 (fun x => by rw [Algebra.smul_def, hfker, zero_mul])

/-- **The domain case** (Stacks 051R main step, GF5 core): for a prime `𝔮` of `S`, the domain
`S ⧸ 𝔮` (finite type over the Noetherian domain `R`) is generically free over `R`.

Assembled from the transcendence induction `gf_of_trdeg_le`: present `S ⧸ 𝔮` as a quotient
`R[X₁,…,X_m] ⧸ 𝔮₀` of a polynomial ring (`Algebra.FiniteType.iff_quotient_mvPolynomial''`, putting
the object in `R`'s universe so the polynomial-quotient recursion closes), run the induction there,
and transport freeness back along the resulting `R`-algebra equivalence (`GF.of_linearEquiv`), then
reconcile the `R`- and `S`-module structures (`GFree.of_GF`). -/
private theorem exists_generically_free_domain [IsNoetherianRing R] [Algebra.FiniteType R S]
    (p : Ideal S) [p.IsPrime] : GFree R S (S ⧸ p) := by
  haveI : IsDomain (S ⧸ p) := Ideal.Quotient.isDomain p
  obtain ⟨m, ψ, hψ⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := S ⧸ p)).mp inferInstance
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  haveI : IsDomain (MvPolynomial (Fin m) R ⧸ RingHom.ker ψ) := Ideal.Quotient.isDomain _
  haveI : Algebra.FiniteType R (MvPolynomial (Fin m) R ⧸ RingHom.ker ψ) := inferInstance
  have hfin : Algebra.trdeg R (MvPolynomial (Fin m) R ⧸ RingHom.ker ψ) < Cardinal.aleph0 :=
    trdeg_lt_aleph0
  have key : GF R (MvPolynomial (Fin m) R ⧸ RingHom.ker ψ) :=
    gf_of_trdeg_le (Algebra.trdeg R (MvPolynomial (Fin m) R ⧸ RingHom.ker ψ)).toNat _
      (le_of_eq (Cardinal.cast_toNat_of_lt_aleph0 hfin).symm)
  let e : (MvPolynomial (Fin m) R ⧸ RingHom.ker ψ) ≃ₐ[R] (S ⧸ p) :=
    Ideal.quotientKerAlgEquivOfSurjective hψ
  exact GFree.of_GF (GF.of_linearEquiv e.symm.toLinearEquiv key)

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
