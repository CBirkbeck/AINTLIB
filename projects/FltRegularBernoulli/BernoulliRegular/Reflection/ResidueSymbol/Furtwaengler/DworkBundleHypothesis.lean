module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.FullTeichSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality

/-!
# Dwork bundle hypothesis (REF-18-atom-4)

This file packages the `FullTeichDworkSetup` bundle as a **named existence
hypothesis** for downstream consumers. The bundle contains the substantive
analytic input (Artin-Hasse exponential coefficients with Q-adic valuation,
leading coefficient identity, and the multi-index Dwork factorization of
the additive character) that produces the Stickelberger ideal equality
through `DworkAssembly`.

## Strategy

Constructing a `FullTeichDworkSetup` requires the substantive content of
the Dwork-Dieudonné theorem on Artin-Hasse exponentials: the formal
power series `E(T) = exp(∑_{i≥0} T^{p^i}/p^i) ∈ ℚ⟦T⟧` has p-integral
coefficients, and its `T^n` coefficients satisfy the Q-adic valuation,
leading-term, and multi-index expansion identities recorded in
`FullTeichDworkSetup`.

Mathlib does not currently provide an Artin-Hasse exponential API, so a
fully constructive `FullTeichDworkSetup` instance for the cyclotomic
setup would require constructing it from scratch — a substantial
formalization effort orthogonal to the canonical chain itself.

This file therefore provides the named hypothesis predicate

  `DworkBundleHypothesis ℓ p k K R'`

which downstream consumers in `DworkAssembly.lean` and
`StickelbergerIdealEquality.lean` can take as a single substantive input
to obtain the bundle. The predicate is satisfied as soon as a
`FullTeichDworkSetup ℓ p k K R'` exists.

## Main definitions

* `DworkBundleHypothesis ℓ p k K R'` — `Nonempty (FullTeichDworkSetup ...)`,
  the named hypothesis at the bundle level.
* `DworkBundleHypothesis.someBundle` — extract the underlying bundle.
* `FullTeichDworkSetup.mk_of_components` — ergonomic explicit-named
  constructor for `FullTeichDworkSetup` taking each of the four Dwork-
  specific fields by name.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- **Dwork bundle hypothesis** at the cyclotomic setup. Asserts that a
`FullTeichDworkSetup ℓ p k K R'` exists. Constructing such a bundle
amounts to providing the Artin-Hasse exponential coefficients
(`dworkCoeff`) together with their three Q-adic axioms (Q-power
membership, `n!`-leading coefficient identity, multi-index character
factorization). -/
def DworkBundleHypothesis
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R'] : Prop :=
  Nonempty (FullTeichDworkSetup ℓ p k K R')

/-- Extract the underlying `FullTeichDworkSetup` from the existence
hypothesis (using `Classical.choice`). -/
noncomputable def DworkBundleHypothesis.someBundle
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    (h : DworkBundleHypothesis ℓ p k K R') : FullTeichDworkSetup ℓ p k K R' :=
  h.some

/-- Reverse: a concrete `FullTeichDworkSetup` instance proves the
hypothesis. Useful for downstream consumers that want to switch between
"hypothesis" and "concrete bundle" forms. -/
theorem DworkBundleHypothesis.of_bundle
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R') : DworkBundleHypothesis ℓ p k K R' :=
  ⟨S⟩

/-- **Ergonomic constructor.** Constructs a `FullTeichDworkSetup` from
its underlying `FullTeichStickelbergerSetup` together with the four
Dwork-specific data/axiom fields. This is just the structure
`mk` lifted with named arguments — useful when supplying the Dwork
data piecewise. -/
def FullTeichDworkSetup.mk_of_components
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S_stick : FullTeichStickelbergerSetup ℓ p k K R')
    (dworkCoeff : ℕ → ℕ → 𝓞 R')
    (h_Q_pow : ∀ N n : ℕ,
      dworkCoeff N n ∈ S_stick.toConcreteStickelbergerSetup.Q ^ n)
    (h_leading : ∀ N n : ℕ, n ≤ N → n < ℓ →
      ((Nat.factorial n : ℕ) : 𝓞 R') * dworkCoeff N n -
          S_stick.toConcreteStickelbergerSetup.π ^ n ∈
        S_stick.toConcreteStickelbergerSetup.Q ^ (n + 1))
    (h_psi : ∀ (N : ℕ) (y : kˣ),
      S_stick.toConcreteStickelbergerSetup.psiInt ((y : k)) -
        (∑ m ∈ multiIndexLE
            S_stick.toConcreteStickelbergerSetup.f N,
          (∏ i : Fin
              S_stick.toConcreteStickelbergerSetup.f,
            dworkCoeff N (m i)) *
          ((S_stick.teichUnitFull
              (S_stick.traceScale * y) : 𝓞 R') ^
            multiIndexValue ℓ m)) ∈
      S_stick.toConcreteStickelbergerSetup.Q ^ (N + 1)) :
    FullTeichDworkSetup ℓ p k K R' :=
  { toFullTeichStickelbergerSetup := S_stick
    dworkCoeff := dworkCoeff
    dworkCoeff_mem_Q_pow := h_Q_pow
    dworkCoeff_lt_ell_leading := h_leading
    psi_dwork_factorization := h_psi }

/-- **Coverage predicate at the hypothesis level.** Given a
`DworkBundleHypothesis` predicate, asserts that the underlying bundle's
Stickelberger orbit coverage holds. Defined as the existence of a
bundle whose `StickelbergerOrbitCoverage` is satisfied. -/
def DworkBundleHypothesisWithCoverage
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R'] : Prop :=
  ∃ S : FullTeichDworkSetup ℓ p k K R', S.StickelbergerOrbitCoverage

/-- **Stickelberger ideal-equality consumer at the hypothesis level.**
Given a `DworkBundleHypothesisWithCoverage`, produce a
`StickelbergerIdealEquality` at the bundle's descentPrime ideal under
`𝓞 K`. The bundle and coverage witness are extracted from the
existential. -/
theorem stickelbergerIdealEquality_of_dworkBundleHypothesisWithCoverage
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    (h : DworkBundleHypothesisWithCoverage ℓ p k K R') :
    ∃ S : FullTeichDworkSetup ℓ p k K R',
      StickelbergerIdealEquality (p := p) (K := K) (S.Q.under (𝓞 K)) := by
  obtain ⟨S, h_cov⟩ := h
  exact ⟨S, FullTeichDworkSetup.stickelbergerIdealEquality_of_orbitCoverage S h_cov⟩

/-- **Hypothesis-form constructor.** Bundle-level convenience producing
the `DworkBundleHypothesis` predicate from the four named Dwork
components. Composes `mk_of_components` with `of_bundle`. -/
theorem DworkBundleHypothesis.of_components
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type w} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S_stick : FullTeichStickelbergerSetup ℓ p k K R')
    (dworkCoeff : ℕ → ℕ → 𝓞 R')
    (h_Q_pow : ∀ N n : ℕ,
      dworkCoeff N n ∈ S_stick.toConcreteStickelbergerSetup.Q ^ n)
    (h_leading : ∀ N n : ℕ, n ≤ N → n < ℓ →
      ((Nat.factorial n : ℕ) : 𝓞 R') * dworkCoeff N n -
          S_stick.toConcreteStickelbergerSetup.π ^ n ∈
        S_stick.toConcreteStickelbergerSetup.Q ^ (n + 1))
    (h_psi : ∀ (N : ℕ) (y : kˣ),
      S_stick.toConcreteStickelbergerSetup.psiInt ((y : k)) -
        (∑ m ∈ multiIndexLE
            S_stick.toConcreteStickelbergerSetup.f N,
          (∏ i : Fin
              S_stick.toConcreteStickelbergerSetup.f,
            dworkCoeff N (m i)) *
          ((S_stick.teichUnitFull
              (S_stick.traceScale * y) : 𝓞 R') ^
            multiIndexValue ℓ m)) ∈
      S_stick.toConcreteStickelbergerSetup.Q ^ (N + 1)) :
    DworkBundleHypothesis ℓ p k K R' :=
  DworkBundleHypothesis.of_bundle
    (FullTeichDworkSetup.mk_of_components
      S_stick dworkCoeff h_Q_pow h_leading h_psi)

end Furtwaengler

end BernoulliRegular
