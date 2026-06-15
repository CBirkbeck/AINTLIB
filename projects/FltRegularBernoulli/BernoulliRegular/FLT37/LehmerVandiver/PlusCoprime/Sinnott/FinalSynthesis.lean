import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.PollaczekFamilyDescent
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.PSaturation

/-!
# Cor 8.19 / Sinnott bridge: final synthesis

This file packages the FULLY PROVEN chain for the Cor 8.19 bridge
construction, with the remaining deferred content reduced to a SINGLE
Prop `PollaczekForward`.

## Chain summary

```
   PollaczekForward (deferred analytic Prop)
       │
       ▼  [cor8_19Bridge_of_pollaczekForward_full]
   Cor8_19Bridge p K i  (target)
```

## What is proven

* All cyclotomic-unit subgroup infrastructure (membership, σ-stability,
  family extraction).
* `pollaczekInFamily`: the K⁺-side preimage of `pollaczekUnitPlus` lies
  in the family-generated subgroup.
* `mem_of_pow_mem_of_index_coprime`: Bézout-based p-saturation lemma.
* `regOfFamily_cyclotomicUnitFamilyKplus_div_regulator`: index identity
  via mathlib's `regOfFamily_div_regulator`.
* `regOfFamily_cyclotomicUnitFamilyKplus_eq_det`: explicit determinant
  form for `regOfFamily(family)`.
* `cor8_19Bridge_of_pollaczekForward`: final bridge construction from
  PollaczekForward.
* `cor8_19Bridge_of_pollaczekForward_full`: synthesis combining all
  proven engines.

## What remains

* `PollaczekForward p K i`: the Pollaczek-Vandiver claim that under
  `p ∣ h⁺(K)`, the K⁺-side preimage of `pollaczekUnitPlus p K i` is a
  p-th power in the family subgroup. Its proof is the substantive
  analytic content combining:
  - `KummerDirichletDeterminant` / Sinnott's index formula.
  - The Pollaczek-construction property at the irregular index i.

## Application

Given `PollaczekForward p K i`, the Cor 8.19 bridge constructor
`cor8_19Bridge_of_pollaczekForward_full` produces `Cor8_19Bridge p K i`
directly. -/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **Final theorem**: with `PollaczekForward` proven, `Cor8_19Bridge`
follows. This is the closed chain. -/
theorem cor8_19Bridge_closed (i : ℕ) (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h_forward : PollaczekForward p K i hp_odd hp_three) :
    Cor8_19Bridge p K i :=
  cor8_19Bridge_of_pollaczekForward_full p K i hp_odd hp_three h_forward

end Sinnott

end FLT37

end BernoulliRegular

end
