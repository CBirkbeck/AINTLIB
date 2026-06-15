import BernoulliRegular.CyclotomicUnits.IndexFormula
import BernoulliRegular.CyclotomicUnits.SaturationIndex

/-!
# Unit-side forward step (WF-814a): nontrivial `p`-torsion in `(𝓞 K⁺)ˣ / C⁺`

Washington §8.3, Theorem 8.14 forward direction, **unit side**, first leaf.

From Sinnott's index formula `[(𝓞 K⁺)ˣ : C⁺] = 2^((p-3)/2)·h⁺` (already proved
via `kummerDirichletDeterminant_of_deletedFourier`), divisibility `p ∣ h⁺`
forces `p` to divide the index `[(𝓞 K⁺)ˣ : C⁺]`, so Cauchy's theorem produces a
class of order `p` in the finite quotient `(𝓞 K⁺)ˣ / C⁺`.

This is the unit-side analogue of the class-side forward step; per the
`/expert-review` 2026-05-27 guidance it is proved **natively** from the index
formula, not transferred from the class group.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Thm 8.14.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **WF-814a.** If `p ∣ h⁺` (and `5 ≤ p`), the finite quotient `(𝓞 K⁺)ˣ / C⁺`
has an element of order `p`.

Proof: Sinnott's index formula gives `[(𝓞 K⁺)ˣ : C⁺] = 2^((p-3)/2)·h⁺`, so
`p ∣ h⁺ ⟹ p ∣` index (the `2`-power factor is coprime to the odd prime `p`);
Cauchy's theorem on the finite quotient yields the order-`p` class. -/
theorem exists_orderOf_eq_prime_unitQuotient_CPlus_of_dvd_hPlus
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p) (h : p ∣ hPlus K) :
    ∃ q : (𝓞 K⁺)ˣ ⧸ CPlus (p := p) (K := K) hp_three, orderOf q = p := by
  have hp_odd : p ≠ 2 := by omega
  have hp_two : 2 < p := by omega
  have hdet : FLT37.Sinnott.KummerDirichletDeterminant p K hp_odd hp_three :=
    kummerDirichletDeterminant_of_deletedFourier
      (p := p) (K := K) hp_odd hp_three hp_two hp_five
  have hidx : p ∣ (CPlus (p := p) (K := K) hp_three).index := by
    have hiff :=
      cyclotomicUnitIndex_primeConductor_pPrimary_of_kummerDirichletDeterminant
        (p := p) (K := K) hp_odd hp_three hdet
    have hsub :
        p ∣ (cyclotomicUnitIndexSubgroup (p := p) (K := K) hp_odd hp_three).index :=
      hiff.mpr h
    rwa [cyclotomicUnitIndexSubgroup_eq_CPlus (p := p) (K := K) hp_odd hp_three]
      at hsub
  haveI : (CPlus (p := p) (K := K) hp_three).FiniteIndex :=
    ⟨CPlus_index_ne_zero (p := p) (K := K) hp_three⟩
  have hcard : p ∣ Nat.card ((𝓞 K⁺)ˣ ⧸ CPlus (p := p) (K := K) hp_three) := by
    simpa [Subgroup.index_eq_card] using hidx
  exact exists_prime_orderOf_dvd_card'
    (G := (𝓞 K⁺)ˣ ⧸ CPlus (p := p) (K := K) hp_three) p hcard

end BernoulliRegular

end
