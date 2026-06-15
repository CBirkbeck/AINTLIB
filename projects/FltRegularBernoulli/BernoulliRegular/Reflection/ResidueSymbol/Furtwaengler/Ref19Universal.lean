module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiClassFunction

/-!
# Universal `Ref19UniversalHypothesis` from per-γ vanishing

This file provides a structural composer that builds the universal
`Ref19UniversalHypothesis η` predicate (the canonical residue symbol
of `η` vanishes on every nonzero principal ideal) from a per-`γ`
vanishing theorem.

## Strategy

For the universal hypothesis, we need `pthSymbolAtIdeal_canonical η ((γ)) = 0`
for every nonzero `γ ∈ 𝓞 K`.  This module is only the quantifier wrapper:
the arithmetic input must be supplied as an actual per-`γ` theorem.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **Ref19 chain input supplier**: for each nonzero `γ ∈ 𝓞 K`, provide
the per-`γ` chain inputs needed to fire the canonical REF-19 chain.

Producing such a supplier for the cyclotomic FLT-regular setup is the
substantive remaining work for `Ref19UniversalHypothesis η`. -/
def Ref19PerGammaSupplier (η : 𝓞 K) : Prop :=
  ∀ γ : 𝓞 K, γ ≠ 0 →
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({γ} : Set (𝓞 K))) = 0

/-- **Universal REF-19 from per-γ supplier**. The supplier directly
provides the universal hypothesis. (This is essentially an `iff`
relabelling — both predicates have the same content — but exposes the
structural shape consumers expect.) -/
theorem ref19UniversalHypothesis_of_supplier
    {η : 𝓞 K} (h_supplier : Ref19PerGammaSupplier (p := p) (K := K) η) :
    Ref19UniversalHypothesis (p := p) (K := K) η :=
  h_supplier

/-- **Reverse: universal hypothesis ⟹ supplier.** Trivial — they are
the same predicate. Exposed for ergonomic interconversion. -/
theorem ref19PerGammaSupplier_of_universalHypothesis
    {η : 𝓞 K} (h_univ : Ref19UniversalHypothesis (p := p) (K := K) η) :
    Ref19PerGammaSupplier (p := p) (K := K) η :=
  h_univ

/-- **Universal REF-19 from a chain-consumer supplier.**

Given a function that, for every nonzero `γ`, supplies the output
`pthSymbolAtIdeal_canonical η ((γ)) = 0`, produces
`Ref19UniversalHypothesis η`. -/
theorem ref19UniversalHypothesis_of_chainSupplier
    {η : 𝓞 K}
    (h_chain : ∀ γ : 𝓞 K, γ ≠ 0 →
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({γ} : Set (𝓞 K))) = 0) :
    Ref19UniversalHypothesis (p := p) (K := K) η :=
  h_chain

end Furtwaengler

end BernoulliRegular

end
