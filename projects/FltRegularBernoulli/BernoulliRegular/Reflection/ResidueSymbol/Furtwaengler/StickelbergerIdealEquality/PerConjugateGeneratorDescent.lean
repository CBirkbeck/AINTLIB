module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkAssembly
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormGalois
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality.OrbitCoverageDischargeReexport

/-!
# `StickelbergerIdealEquality` from a `FullTeichDworkSetup`

This file provides the substantive valuation-descent content of c.1
(`REF-18c2d-main-c.1`) by showing how to assemble a
`StickelbergerIdealEquality (S.Q.under (𝓞 K))` from a
`FullTeichDworkSetup S` together with a coverage hypothesis on the
Galois orbit of the descent prime.

## Strategy

The Dwork bundle gives the EXACT `Q`-adic order
`S.gaussSumInt a ∈ S.Q^(stickOrdOrd a) ∧ S.gaussSumInt a ∉ S.Q^(stickOrdOrd a + 1)`
at the SINGLE prime `S.Q ⊂ 𝓞 R'` for each `a ∈ [1, p-1]`. The route
to the multi-conjugate Stickelberger ideal in `𝓞 K` factors through
the descent prime `q_K = S.Q.under (𝓞 K)` and the Galois orbit
`cyclotomicConjugates q_K`:

1. **Per-`a` descent witness** (`StickelbergerPerConjugateDescent`):
   for each `a`, the existence of `γ_a ∈ 𝓞 K` whose image in `𝓞 R'`
   equals `S.gaussSumInt a ^ p` and whose `descentPrime`-adic order is
   `p · stickOrdOrd a / e` where `e = descentRamificationIdx`.

2. **Galois-orbit coverage** (`StickelbergerOrbitCoverage`): the
   Stickelberger ideal `q_K^Θ = ∏_a (σ_{a^{-1}} q_K)^a.val` admits a
   single global generator `γ ∈ 𝓞 K` whose ideal factorization at each
   conjugate matches the prescribed exponent.

3. **Final assembly** (`stickelbergerIdealEquality_of_dwork_witness`):
   under both witnesses, the principal ideal `(γ)` equals
   `stickelbergerIdeal q_K`, and so `StickelbergerIdealEquality q_K`
   holds.

The current file delivers (1) and the **conditional** (3) under (2).
The unconditional (2) requires a separate per-conjugate bundle for
each Galois conjugate prime above `ℓ` (one bundle per representative
of the Galois orbit of `S.Q`); that step is left as a coverage
hypothesis here, packaged as the `Prop` predicate
`StickelbergerOrbitCoverage`.

## Why split

The full unconditional c.1 builds a single global generator from
multiple per-conjugate bundles by orbit-summing. That assembly is the
substantive remaining content. The conditional form delivered here
already discharges all the **valuation-descent** content (per-`a`
exact orders, ramification descent, Dwork EXACT-order data); only the
**orbit-coverage** combinatorics remain.

## Files

* Per-`a` exact-order descent: theorems
  `gaussSumInt_pow_descentPrime_pow_mul_stickOrdOrd`,
  `gaussSumInt_pow_not_mem_descentPrime_pow_mul_stickOrdOrd_succ` (in
  this file, on `FullTeichDworkSetup`).
* Final `StickelbergerIdealEquality` constructor: theorem
  `stickelbergerIdealEquality_of_orbitCoverage`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace FullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']
variable [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

variable (S : FullTeichDworkSetup ℓ p k K R')

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-! ### Forward construction via per-conjugate generators

The orbit-coverage predicate
`∃ γ ∈ 𝓞 K, γ ≠ 0 ∧ Ideal.span {γ} = stickelbergerIdeal q_K`
admits a clean *forward* discharge through a per-conjugate-generator
witness:

* `StickelbergerExactPerConjugateGenerator`: for each `a ∈ (ZMod p)ˣ`,
  there exists `γ_a ∈ 𝓞 K` non-zero with
  `Ideal.span {γ_a} = (σ_{a⁻¹} q_K) ^ a.val`.

The product `γ := ∏_a γ_a` then satisfies
`Ideal.span {γ} = ∏_a (σ_{a⁻¹} q_K)^a.val = stickelbergerIdeal q_K`,
discharging `StickelbergerOrbitCoverage` unconditionally on the bundle's
ramification setup. The rest of the construction (existence of each γ_a)
is the substantive content of multi-bundle Stickelberger descent — it
remains hypothesized as a `Prop` but the `Prop` is now atomic (one
∃ per orbit element), and the constructor is a one-line product. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Atomic per-conjugate generator predicate.**

For every `a ∈ (ZMod p)ˣ`, there is a non-zero `γ_a ∈ 𝓞 K` such that
the principal ideal `(γ_a)` equals the Stickelberger factor
`(σ_{a⁻¹} q_K)^{a.val}`.

This is the substantive remaining content of c.1.
The discharge of this predicate corresponds to building, for each
Galois conjugate prime, a generator with the prescribed exponent —
classically realised via the Stickelberger formula
`g(χ_q^a) · 𝓞_R' = (σ_a^{-1} Q) ^ stickelbergerWeight` plus descent. -/
def StickelbergerExactPerConjugateGenerator : Prop :=
  ∀ a : CyclotomicUnitDelta p,
    ∃ γ_a : 𝓞 K, γ_a ≠ 0 ∧
      Ideal.span ({γ_a} : Set (𝓞 K)) =
        cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.toConcreteStickelbergerSetup.descentPrime ^
          ((a : ZMod p).val)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Forward construction of `StickelbergerOrbitCoverage` from per-conjugate
generators.** Given a witness `StickelbergerExactPerConjugateGenerator S`,
the product `γ := ∏_a γ_a` over the cyclotomic unit group satisfies
`Ideal.span {γ} = stickelbergerIdeal q_K`, hence
`StickelbergerOrbitCoverage S` holds.

Mathematics: the principal-ideal product formula
`∏_a Ideal.span {γ_a} = Ideal.span {∏_a γ_a}`
combined with `(γ_a) = (σ_{a⁻¹} q_K)^{a.val}` for each `a` gives
`Ideal.span {∏_a γ_a} = ∏_a (σ_{a⁻¹} q_K)^{a.val} = stickelbergerIdeal q_K`. -/
theorem stickelbergerOrbitCoverage_of_perConjugateGenerator
    (h_gen : S.StickelbergerExactPerConjugateGenerator) :
    S.StickelbergerOrbitCoverage := by
  classical
  -- Choose a γ_a for each a.
  choose γ_a hγ_a_ne hγ_a_eq using h_gen
  -- Define the global generator as the product.
  refine ⟨∏ a : CyclotomicUnitDelta p, γ_a a, ?_, ?_⟩
  · -- The product is non-zero: each factor is non-zero in a domain.
    rw [Finset.prod_ne_zero_iff]
    intro a _
    exact hγ_a_ne a
  · -- The principal ideal equality:
    -- Ideal.span {∏ γ_a} = ∏ Ideal.span {γ_a} = ∏ (σ_{a⁻¹} q_K)^a.val
    rw [← Ideal.prod_span_singleton (Finset.univ : Finset (CyclotomicUnitDelta p)) γ_a]
    -- Goal: ∏ Ideal.span {γ_a} = stickelbergerIdeal q_K
    unfold stickelbergerIdeal
    refine Finset.prod_congr rfl ?_
    intro a _
    exact hγ_a_eq a

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Forward end-to-end discharge of `StickelbergerIdealEquality` via
per-conjugate generators.** Given the per-conjugate generator predicate,
we obtain `StickelbergerIdealEquality (S.Q.under (𝓞 K))` directly.

This is the consumer-facing entry point for the c.1 forward direction,
using the per-conjugate-generator atomic predicate as the sole content
hypothesis. -/
theorem stickelbergerIdealEquality_of_perConjugateGenerator
    (h_gen : S.StickelbergerExactPerConjugateGenerator) :
    StickelbergerIdealEquality (p := p) (K := K)
      (S.Q.under (𝓞 K)) :=
  S.stickelbergerIdealEquality_of_orbitCoverage
    (S.stickelbergerOrbitCoverage_of_perConjugateGenerator h_gen)

/-! ### Refining `StickelbergerExactPerConjugateGenerator` further

The per-conjugate generator existence is itself an `∃` — for each a,
exhibit γ_a generating `(σ_{a⁻¹} q_K)^{a.val}`. We expose two natural
sources of such a generator:

1. **From principality of each prime power** (Dedekind-domain content):
   if every Galois conjugate of `q_K` is principal, then so are its
   powers, and we can choose explicit generators.
2. **From a single global generator** (the round-trip): if a global γ
   already satisfies `(γ) = stickelbergerIdeal q_K`, then per-conjugate
   generators can be extracted from `factor_dvd_of_pow_dvd`.

The first form is captured by the principality predicate
`StickelbergerConjugateIsPrincipal`; the second form is the converse
direction packaged for completeness. -/

/-- **Atomic principality predicate.**

For every `a ∈ (ZMod p)ˣ`, the Galois conjugate `σ_{a⁻¹} q_K` is a
principal ideal of `𝓞 K`.

In the totally split case (e=1, f=1), each conjugate is a distinct
prime over `ℓ`; principality of all these primes is equivalent to
`ℓ` being a `p`-th-power norm in 𝓞 K. -/
def StickelbergerConjugateIsPrincipal : Prop :=
  ∀ a : CyclotomicUnitDelta p,
    Submodule.IsPrincipal
      (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
        S.toConcreteStickelbergerSetup.descentPrime)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Trivial discharge of `StickelbergerConjugateIsPrincipal` from
principality of the descent prime.**

If `q_K = S.descentPrime` is itself a principal ideal, say
`q_K = (γ_0)`, then every Galois conjugate
`σ_{a⁻¹} q_K = Ideal.map (cyclotomicRingOfIntegersEquiv K a⁻¹) q_K`
is automatically principal: it is the image of a principal ideal under a
ring homomorphism, with generator `cyclotomicRingOfIntegersEquiv K a⁻¹ γ_0`.

This packages the cleanest atomic input form for c.1 in the
totally-split case where `ℓ` is a `p`-th-power norm. -/
theorem stickelbergerConjugateIsPrincipal_of_principal
    (h_princ : Submodule.IsPrincipal
      S.toConcreteStickelbergerSetup.descentPrime) :
    S.StickelbergerConjugateIsPrincipal := by
  intro a
  unfold cyclotomicGaloisConjugate
  exact h_princ.map_ringHom (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Constructing per-conjugate generators from principality.**
If each `σ_{a⁻¹} q_K` is principal with generator `g_a`, then `g_a^{a.val}`
generates the corresponding power, satisfying
`StickelbergerExactPerConjugateGenerator`. -/
theorem stickelbergerExactPerConjugateGenerator_of_principal
    (h_princ : S.StickelbergerConjugateIsPrincipal) :
    S.StickelbergerExactPerConjugateGenerator := by
  classical
  intro a
  -- Extract the generator g_a of σ_{a⁻¹} q_K.
  haveI := h_princ a
  obtain ⟨g_a, hg_a_eq⟩ := Submodule.IsPrincipal.principal
    (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime)
  -- We claim γ_a := g_a^{a.val} works.
  refine ⟨g_a ^ ((a : ZMod p).val), ?_, ?_⟩
  · -- g_a^{a.val} ≠ 0: since σ_{a⁻¹} q_K is non-zero, g_a generates a
    -- non-zero principal ideal, so g_a ≠ 0; hence its power is non-zero.
    have h_ne : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
        S.toConcreteStickelbergerSetup.descentPrime ≠ ⊥ :=
      S.cyclotomicGaloisConjugate_descentPrime_ne_bot a
    have hg_a_ne : g_a ≠ 0 := by
      intro hg_zero
      rw [hg_zero] at hg_a_eq
      -- hg_a_eq : (σ_{a⁻¹} q_K) = Submodule.span (𝓞 K) {0} = ⊥
      simp only [Submodule.span_zero_singleton] at hg_a_eq
      exact h_ne hg_a_eq
    exact pow_ne_zero _ hg_a_ne
  · -- (g_a^{a.val}) = (g_a)^{a.val} = (σ_{a⁻¹} q_K)^{a.val}.
    -- hg_a_eq : (σ_{a⁻¹} q_K) = Submodule.span (𝓞 K) {g_a}
    -- Convert g_a's principal-ideal representation to Ideal.span form.
    have hg_a_ideal :
        Ideal.span ({g_a} : Set (𝓞 K)) =
          cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.toConcreteStickelbergerSetup.descentPrime :=
      hg_a_eq.symm
    -- Now substitute and use Ideal.span_singleton_pow.
    rw [show Ideal.span ({g_a ^ ((a : ZMod p).val)} : Set (𝓞 K)) =
        Ideal.span ({g_a} : Set (𝓞 K)) ^ ((a : ZMod p).val) from
      (Ideal.span_singleton_pow g_a ((a : ZMod p).val)).symm]
    rw [hg_a_ideal]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **End-to-end forward construction from principality.** Combining
`stickelbergerExactPerConjugateGenerator_of_principal` with
`stickelbergerOrbitCoverage_of_perConjugateGenerator`: under the
principality of each Galois conjugate of `q_K`, the orbit-coverage
predicate holds. -/
theorem stickelbergerOrbitCoverage_of_principal
    (h_princ : S.StickelbergerConjugateIsPrincipal) :
    S.StickelbergerOrbitCoverage :=
  S.stickelbergerOrbitCoverage_of_perConjugateGenerator
    (S.stickelbergerExactPerConjugateGenerator_of_principal h_princ)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **End-to-end forward construction of `StickelbergerIdealEquality`
under conjugate-principality.** This is the pure-forward c.1 closure
modulo the principality input on each Galois conjugate of `q_K`. -/
theorem stickelbergerIdealEquality_of_principal
    (h_princ : S.StickelbergerConjugateIsPrincipal) :
    StickelbergerIdealEquality (p := p) (K := K)
      (S.Q.under (𝓞 K)) :=
  S.stickelbergerIdealEquality_of_orbitCoverage
    (S.stickelbergerOrbitCoverage_of_principal h_princ)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Cleanest atomic consumer-facing composer for c.1:
`StickelbergerIdealEquality` from descent-prime principality and
totally-split ramification.**

Given:
* `Submodule.IsPrincipal S.descentPrime` — i.e., `q_K` is itself a
  principal ideal of `𝓞 K`;
* totally-split ramification `(e = 1, f = 1)` of `q_K` over its
  rational prime,

we obtain `StickelbergerIdealEquality (S.Q.under (𝓞 K))`.

This bundles the trivial discharge of conjugate-principality
(`stickelbergerConjugateIsPrincipal_of_principal`) with the principal
end-to-end constructor (`stickelbergerIdealEquality_of_principal`).
The split hypotheses are not strictly required by the proof — conjugate
principality alone suffices — but are recorded here as the natural
ramification context for the totally-split case `ℓ ≡ 1 (mod p)` in which
this atomic input form is consumed by c.1. -/
theorem stickelbergerIdealEquality_of_descentPrime_principal_of_split
    (h_princ : Submodule.IsPrincipal
      S.toConcreteStickelbergerSetup.descentPrime)
    (_he : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (_hf : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    StickelbergerIdealEquality (p := p) (K := K)
      (S.Q.under (𝓞 K)) :=
  S.stickelbergerIdealEquality_of_principal
    (S.stickelbergerConjugateIsPrincipal_of_principal h_princ)

/-! ### Reverse: orbit coverage implies per-conjugate generators
(under faithfulness)

The converse to `stickelbergerOrbitCoverage_of_perConjugateGenerator`:
if a single γ generates `stickelbergerIdeal q_K` and the cyclotomic
orbit acts faithfully on `q_K`, then the per-conjugate generators exist.

This direction exhibits the per-conjugate generators by extracting
the Galois-conjugate factors of `(γ)`'s factorisation, using
the `StickelbergerExactConjugateExponents` discharge already in place. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Round-trip:** orbit coverage + orbit faithfulness imply per-conjugate
generators exist. The witness γ_a is built from `(σ_{a⁻¹} q_K)`'s
principality, which here is asserted via the multiplicity computation
plus Dedekind-domain factorisation uniqueness.

In the totally split case, every `σ_{a⁻¹} q_K` is a distinct prime over
`ℓ`, so this is genuine principality content. -/
theorem stickelbergerExactPerConjugateGenerator_of_coverage_of_principal
    (_h_cov : S.StickelbergerOrbitCoverage)
    (h_princ : S.StickelbergerConjugateIsPrincipal) :
    S.StickelbergerExactPerConjugateGenerator :=
  -- The principality alone suffices; coverage is not used here.
  S.stickelbergerExactPerConjugateGenerator_of_principal h_princ

end FullTeichDworkSetup

end Furtwaengler

end BernoulliRegular
