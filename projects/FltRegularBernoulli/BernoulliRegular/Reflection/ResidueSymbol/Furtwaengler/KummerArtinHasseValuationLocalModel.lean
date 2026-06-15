module

public import BernoulliRegular.TotallyRealSubfield.ZetaPrime
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Valuation-completion model for the lambda-local Kummer--Artin--Hasse trace

The existing `LambdaLocalIntegerRing` is an adic completion of the localized
cyclotomic integer ring.  It is the model already used by the principal-unit
filtration.  For the `Q_p`-linear trace in the explicit local correction,
mathlib's available field/DVR API is instead attached to
`HeightOneSpectrum.adicCompletion`.

This file exposes the valuation-completion model attached to the same prime
`lambda = zetaPrime p K`.  The final explicit Kummer--Artin--Hasse trace
source is routed through this valuation-completion model; the older
`LambdaLocalIntegerRing` stack is legacy infrastructure for the adic
principal-unit filtration, not the final trace API.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The height-one prime of `𝓞 K` corresponding to `lambda = zeta_p - 1`. -/
def lambdaHeightOneSpectrum :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := zetaPrime p K
  isPrime := zetaPrime_isPrime p K
  ne_bot := zetaPrime_ne_bot p K

@[simp]
theorem lambdaHeightOneSpectrum_asIdeal :
    (lambdaHeightOneSpectrum p K).asIdeal = zetaPrime p K :=
  rfl

/-- The valuation completion of `K` at `lambda`. -/
abbrev LambdaValuedCompletion : Type _ :=
  (lambdaHeightOneSpectrum p K).adicCompletion K

/-- The valuation-completion integer ring at `lambda`. -/
abbrev LambdaValuedIntegerRing : Type _ :=
  (lambdaHeightOneSpectrum p K).adicCompletionIntegers K

instance lambdaValuedCompletion_field :
    Field (LambdaValuedCompletion p K) :=
  inferInstance

theorem lambdaValuedIntegerRing_isDomain :
    IsDomain (LambdaValuedIntegerRing p K) :=
  inferInstance

theorem lambdaValuedIntegerRing_isDiscreteValuationRing :
    IsDiscreteValuationRing (LambdaValuedIntegerRing p K) :=
  inferInstance

theorem lambdaValuedIntegerRing_isPrincipalIdealRing :
    IsPrincipalIdealRing (LambdaValuedIntegerRing p K) :=
  inferInstance

/-- The global field embeds densely into the valuation completion. -/
theorem lambdaValuedCompletion_denseRange_algebraMap :
    DenseRange (algebraMap K (LambdaValuedCompletion p K)) :=
  (lambdaHeightOneSpectrum p K).denseRange_algebraMap K

end KummerArtinHasse
end Furtwaengler
end BernoulliRegular
