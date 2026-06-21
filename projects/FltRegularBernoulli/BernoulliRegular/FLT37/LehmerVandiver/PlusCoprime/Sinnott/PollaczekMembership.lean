import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitGroup
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.SigmaPreservation
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Symmetrisation

/-!
# `pollaczekUnit` and `pollaczekUnitPlus` lie in `cyclotomicUnitsSubgroup`

The Pollaczek unit `pollaczekUnit p K i = ∏_{b=1}^{(p-1)/2} cyclotomicUnitUnit(b)^{b^{p-1-i}}`
is by construction a finite product of cyclotomic units. Hence it
lives in the cyclotomic-units subgroup `C ⊆ (𝓞 K)ˣ`.

Likewise the σ-symmetrised form `pollaczekUnitPlus = pollaczekUnit · σ(pollaczekUnit)`
lies in `C` (since σ preserves `C` — see
`unitsComplexConj_preserves_cyclotomicUnitsSubgroup`).

This is **Step (E)** of the Sinnott / Cor 8.19 bridge construction.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §8.3.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **`pollaczekUnit ∈ cyclotomicUnitsSubgroup`.** The Pollaczek unit
`pollaczekUnit p K i` is a product of natural-number powers of
cyclotomic-unit factors `pollaczekFactor p K b = cyclotomicUnitUnit p K b`,
each of which is in `cyclotomicUnitsSubgroup` by definition. The
subgroup is closed under finite products and integer powers, so the
Pollaczek unit is in it. -/
theorem pollaczekUnit_mem_cyclotomicUnitsSubgroup (hp_two : 2 ≤ p) (i : ℕ) :
    FLT37.pollaczekUnit p K i ∈ cyclotomicUnitsSubgroup p K hp_two := by
  unfold FLT37.pollaczekUnit
  apply Subgroup.prod_mem
  rintro ⟨b, hb⟩ _
  rw [FLT37.mem_pollaczek_range_iff] at hb
  obtain ⟨hb_pos, hb_le⟩ := hb
  apply Subgroup.pow_mem
  unfold FLT37.pollaczekFactor
  exact cyclotomicUnitUnit_mem_cyclotomicUnitsSubgroup p K _ hb_pos
    (FLT37.pollaczek_lt_of_le_half p hb_le) hp_two

variable [IsCMField K]

/-- **`pollaczekUnitPlus ∈ cyclotomicUnitsSubgroup`.** The σ-symmetrised
Pollaczek unit `pollaczekUnitPlus = pollaczekUnit · σ(pollaczekUnit)`
lies in `C` because:
* `pollaczekUnit ∈ C` (`pollaczekUnit_mem_cyclotomicUnitsSubgroup`).
* σ stabilises C (`unitsComplexConj_mem_cyclotomicUnitsSubgroup_of_mem`),
  so `σ(pollaczekUnit) ∈ C`.
* C is a subgroup, closed under products. -/
theorem pollaczekUnitPlus_mem_cyclotomicUnitsSubgroup (hp_two : 2 ≤ p) (i : ℕ) :
    FLT37.pollaczekUnitPlus p K i ∈ cyclotomicUnitsSubgroup p K hp_two := by
  unfold FLT37.pollaczekUnitPlus
  apply Subgroup.mul_mem
  · exact pollaczekUnit_mem_cyclotomicUnitsSubgroup (p := p) (K := K) hp_two i
  · exact unitsComplexConj_mem_cyclotomicUnitsSubgroup_of_mem (p := p) (K := K) hp_two
      (pollaczekUnit_mem_cyclotomicUnitsSubgroup (p := p) (K := K) hp_two i)

/-- **`pollaczekUnitPlus ∈ cyclotomicUnitsPlus`.** The symmetrised unit
is also in the real subgroup `C⁺ = C ∩ realUnits K`, since it is σ-fixed
by `pollaczekUnitPlus_complexConj`. -/
theorem pollaczekUnitPlus_mem_cyclotomicUnitsPlus (hp_two : 2 ≤ p) (i : ℕ) :
    FLT37.pollaczekUnitPlus p K i ∈ cyclotomicUnitsPlus p K hp_two := by
  refine ⟨pollaczekUnitPlus_mem_cyclotomicUnitsSubgroup (p := p) (K := K) hp_two i, ?_⟩
  change FLT37.pollaczekUnitPlus p K i ∈ realUnits K
  rw [← unitsComplexConj_eq_self_iff]
  exact FLT37.pollaczekUnitPlus_complexConj p K i

end Sinnott

end FLT37

end BernoulliRegular

end
