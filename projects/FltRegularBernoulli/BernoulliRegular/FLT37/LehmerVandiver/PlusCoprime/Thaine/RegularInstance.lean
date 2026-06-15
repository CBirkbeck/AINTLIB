import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Thaine.UnitClassBridge
import BernoulliRegular.Reflection.ClassGroupModP.AtomC

/-!
# Regular-prime instance of `FLT37UnitClassBridgeRefined`

For regular primes (`Subsingleton (ClassGroup (𝓞 K))`), the new
content-bearing `FLT37UnitClassBridgeRefined` admits a vacuous
construction: every component non-triviality assertion is false (since
the class group is trivial), so both the Pollaczek and Reflection
discharges hold automatically.

This file demonstrates that the Thaine-pivot architecture composes
correctly for regular primes; the irregular case (e.g., FLT37 at p=37)
needs the substantive Thaine annihilator content (T-THAINE-* substantive
bodies).

## References

* `BernoulliRegular.Reflection.ClassGroupModP.AtomC` —
  `ClassGroupComponentIdentification.ofSubsingleton`.
* T-PIVOT-1-REFINE — content-bearing
  `cor8_19Bridge_of_componentTrivialities`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **Regular-prime instance**: under `Subsingleton (ClassGroup (𝓞 K))`,
every `FLT37UnitClassBridgeRefined p K i` is vacuously constructible
because every eigenspace component is trivial.

This is the analog of `cor8_19Bridge_of_regular` (in
`Cor8_19Forward.lean`) routed through the refined Thaine-pivot
architecture. -/
def FLT37UnitClassBridgeRefined.ofSubsingleton
    [Subsingleton (ClassGroup (𝓞 K))] (i : ℕ) :
    FLT37UnitClassBridgeRefined p K i where
  identification := ClassGroupComponentIdentification.ofSubsingleton p hp_odd K
  pollaczekUnitComponent := fun _ h_nt => h_nt.elim
  reflectionOtherComponents := fun _ _ _ _ h_nt => h_nt.elim

/-- **Regular-prime Cor8_19 bridge via the refined chain**: composes the
regular-prime instance with `cor8_19Bridge_of_refined` to give a
`Cor8_19Bridge` parametric only on the regularity hypothesis. -/
def cor8_19Bridge_of_subsingleton_via_refined
    [Subsingleton (ClassGroup (𝓞 K))] (i : ℕ) :
    Cor8_19Bridge p K i :=
  cor8_19Bridge_of_refined (p := p) (K := K)
    (FLT37UnitClassBridgeRefined.ofSubsingleton p hp_odd K i)

end BernoulliRegular

end
