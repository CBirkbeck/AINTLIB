module

public import BernoulliRegular.Reflection.Final

/-!
# T044 contrapositive packaging (LV005d)

The reflection theorem T044a (`Reflection/Final.lean`,
`ReflectionMinusNontrivialityBridge.dvd_hMinus_of_dvd_hPlus_of_bridge`)
states `p ∣ hPlus K ⟹ p ∣ hMinus K` given the reflection bridge data.
LV005's final assembly consumes this in its contrapositive form
`¬ p ∣ hMinus K ⟹ ¬ p ∣ hPlus K`.

## References

* Washington, *Introduction to Cyclotomic Fields*, §10.3.
* Diekmann, *FLT for regular primes*, §6.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime]

variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- **T044 contrapositive (bridge-parametric form)**: given the reflection
bridge data, `¬ p ∣ hMinus K ⟹ ¬ p ∣ hPlus K`. Mirrors T044a's contrapositive
for downstream callers that already hold the bridge. -/
theorem not_dvd_hPlus_of_not_dvd_hMinus_of_bridge
    (B : ReflectionMinusNontrivialityBridge p K)
    (h_minus : ¬ (p : ℕ) ∣ hMinus K) :
    ¬ (p : ℕ) ∣ hPlus K :=
  fun h_plus => h_minus
    (B.dvd_hMinus_of_dvd_hPlus_of_bridge (p := p) (K := K) h_plus)

end BernoulliRegular

end
