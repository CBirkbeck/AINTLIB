module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekUnit

/-!
# σ-symmetrisation of `pollaczekUnit` (LV005b)

The Pollaczek unit `pollaczekUnit p K i ∈ (𝓞 K)ˣ` is **not** literally
`σ`-fixed under the unit-group complex conjugation `unitsComplexConj K`;
the factor-wise σ-twist
`σ((1 - ζ^b)/(1 - ζ)) = ζ^{1 - b} · (1 - ζ^b)/(1 - ζ)`
introduces an explicit ζ-power. The standard remedy is the symmetrised
real combination

  `pollaczekUnitPlus p K i := pollaczekUnit p K i · σ(pollaczekUnit p K i)`,

which **is** σ-fixed and underlies the descent to the maximal real
subfield `K⁺` consumed by Washington's Cor 8.19 / our LV005c
Kummer-pairing bridge.

This file packages just the bare arithmetic:

* `pollaczekUnitPlus` — the symmetrised unit in `(𝓞 K)ˣ`.
* `pollaczekUnitPlus_complexConj` — σ-fixedness (one-line repackage of
  `pollaczekUnit_complexConj`).
* `pollaczekUnitPlus_norm` — `Algebra.norm ℤ` is `1` (square of
  `pollaczekUnit_norm`, after using that `Algebra.norm` is fixed by
  Galois — equivalently, multiplicativity over the symmetrised product).

The full descent of `pollaczekUnitPlus` to `(𝓞 K⁺)ˣ` and the connection
between `IsPthPowerModPrime` predicates on `pollaczekUnit` vs.
`pollaczekUnitPlus` is the deeper LV005c work; defer to that ticket.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), §8.3 (Pollaczek units, p. 158); Corollary 8.19 (p. 158).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section PollaczekUnitPlus

variable (i : ℕ)

/-- The **symmetrised Pollaczek unit**
`pollaczekUnitPlus p K i := pollaczekUnit p K i · σ(pollaczekUnit p K i)`,
where `σ = unitsComplexConj K`. This is a unit of `𝓞 K` that is fixed by
complex conjugation (hence underlies a unit of `𝓞 K⁺`) and has integer
norm `1`. -/
noncomputable def pollaczekUnitPlus [IsCMField K] : (𝓞 K)ˣ :=
  pollaczekUnit p K i * unitsComplexConj K (pollaczekUnit p K i)

/-- **σ-fixedness of the symmetrised Pollaczek unit**: complex conjugation
fixes `pollaczekUnitPlus`. Direct repackage of `pollaczekUnit_complexConj`
behind the `pollaczekUnitPlus` definition. -/
theorem pollaczekUnitPlus_complexConj [IsCMField K] :
    unitsComplexConj K (pollaczekUnitPlus p K i) = pollaczekUnitPlus p K i :=
  pollaczekUnit_complexConj p K i

/-- The **integer norm** of `pollaczekUnitPlus` is `1`. The symmetrised unit
is a product of two `Algebra.norm ℤ`-trivial factors: `pollaczekUnit` and its
complex conjugate. The conjugate has the same `Algebra.norm ℤ` since
`ringOfIntegersComplexConj K` is a `𝓞 K⁺`-AlgEquiv (and a fortiori a
`ℤ`-AlgEquiv) of `𝓞 K`, so `Algebra.norm_eq_of_algEquiv` applies after
`restrictScalars`. -/
theorem pollaczekUnitPlus_norm [IsCMField K] (hp_odd : p ≠ 2) :
    Algebra.norm ℤ ((pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
  unfold pollaczekUnitPlus
  rw [Units.val_mul, map_mul]
  -- pollaczekUnit and its σ-image both have integer norm 1.
  have h_E := pollaczekUnit_norm p K i hp_odd
  have h_σE :
      Algebra.norm ℤ
        ((unitsComplexConj K (pollaczekUnit p K i) : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    rw [show ((unitsComplexConj K (pollaczekUnit p K i) :
          (𝓞 K)ˣ) : 𝓞 K) =
        ringOfIntegersComplexConj K
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) from rfl]
    -- Algebra.norm ℤ is preserved by ringOfIntegersComplexConj (a 𝓞 K⁺-AlgEquiv,
    -- hence ℤ-linear via restrictScalars).
    have h_alg :
        Algebra.norm ℤ
            ((ringOfIntegersComplexConj K).restrictScalars ℤ
              ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K)) =
          Algebra.norm ℤ ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) :=
      Algebra.norm_eq_of_algEquiv
        ((ringOfIntegersComplexConj K).restrictScalars ℤ) _
    -- (restrictScalars e) x = e x definitionally.
    exact h_alg.trans h_E
  rw [h_E, h_σE, mul_one]

end PollaczekUnitPlus

end FLT37

end BernoulliRegular

end
