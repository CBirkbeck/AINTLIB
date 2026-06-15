module

public import BernoulliRegular.UnitQuotient.Components

/-!
# Unit quotients: final structure package

This file is the `T040c` layer.  It packages the explicit structure theorem
for the unit power quotient in the form used by reflection:

`E / E^(p^N) ≃ ℤ/p ⊕ (ℤ/p^N)^((p - 3) / 2)`.

The quotient is multiplicative, so the additive target is wrapped in
`Multiplicative`.  The package also records equivariance for the declared
`Δ = (ZMod p)ˣ` action and keeps the component-size data from `T040b`
available from the same object.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

set_option linter.unusedSectionVars false

variable (p N : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K]

/-- The free summand index set in the unit quotient structure theorem. -/
abbrev CyclotomicUnitQuotientFreeIndex : Type :=
  Fin ((p - 3) / 2)

/-- The additive model `ℤ/p ⊕ (ℤ/p^N)^((p - 3) / 2)`. -/
abbrev CyclotomicUnitQuotientAdditiveModel : Type :=
  ZMod p × (CyclotomicUnitQuotientFreeIndex p → ZMod (p ^ N))

/-- The multiplicative model for `E / E^(p^N)`. -/
abbrev CyclotomicUnitQuotientModel : Type :=
  Multiplicative (CyclotomicUnitQuotientAdditiveModel p N)

/-- The final structure package for `E / E^(p^N)`, including the `Δ`-component
sizes and an equivariant multiplicative isomorphism with the explicit model. -/
structure CyclotomicUnitQuotientStructure where
  componentStructure :
    CyclotomicUnitQuotientComponentStructure (p := p) (N := N) K
  modelAction : CyclotomicUnitDelta p →* MulAut (CyclotomicUnitQuotientModel p N)
  modelEquiv :
    CyclotomicUnitPowerQuotient (p := p) (N := N) K ≃*
      CyclotomicUnitQuotientModel p N
  equivariant :
    ∀ (a : CyclotomicUnitDelta p)
      (x : CyclotomicUnitPowerQuotient (p := p) (N := N) K),
      modelEquiv (componentStructure.action.act a x) = modelAction a (modelEquiv x)

namespace CyclotomicUnitQuotientStructure

variable {p N K}

/-- The `Δ`-action on the source quotient. -/
abbrev sourceAction (S : CyclotomicUnitQuotientStructure (p := p) (N := N) K) :
    CyclotomicUnitQuotientDeltaAction (p := p) (N := N) K :=
  S.componentStructure.action

/-- The character-tagged component package attached to a final structure
theorem. -/
abbrev components (S : CyclotomicUnitQuotientStructure (p := p) (N := N) K) :
    CyclotomicUnitQuotientComponentStructure (p := p) (N := N) K :=
  S.componentStructure

/-- The final multiplicative equivalence
`E/E^(p^N) ≃ ℤ/p ⊕ (ℤ/p^N)^((p - 3)/2)`. -/
def structureEquiv (S : CyclotomicUnitQuotientStructure (p := p) (N := N) K) :
    CyclotomicUnitPowerQuotient (p := p) (N := N) K ≃*
      CyclotomicUnitQuotientModel p N :=
  S.modelEquiv

/-- Equivariance of the final structure isomorphism for the declared
`Δ`-actions. -/
theorem structureEquiv_equivariant
    (S : CyclotomicUnitQuotientStructure (p := p) (N := N) K)
    (a : CyclotomicUnitDelta p)
    (x : CyclotomicUnitPowerQuotient (p := p) (N := N) K) :
    S.structureEquiv (S.sourceAction.act a x) =
      S.modelAction a (S.structureEquiv x) :=
  S.equivariant a x

/-- Component cardinality in the final structure package. -/
theorem component_natCard_eq_pow
    (S : CyclotomicUnitQuotientStructure (p := p) (N := N) K)
    (χ : MulChar (CyclotomicUnitDelta p) ℚ) :
    Nat.card (S.components.component χ).Carrier =
      p ^ (S.components.torsionContribution χ + N * S.components.freeContribution χ) :=
  CyclotomicUnitQuotientComponentStructure.component_natCard_eq_pow
    (p := p) (N := N) (K := K) S.components χ

end CyclotomicUnitQuotientStructure

/-- The `E/E^p` specialization used by the vanishing ticket. -/
abbrev CyclotomicUnitModPQuotient : Type _ :=
  CyclotomicUnitPowerQuotient (p := p) (N := 1) K

/-- The final structure package specialized to `E/E^p`. -/
abbrev CyclotomicUnitModPStructure : Type _ :=
  CyclotomicUnitQuotientStructure (p := p) (N := 1) K

end BernoulliRegular
