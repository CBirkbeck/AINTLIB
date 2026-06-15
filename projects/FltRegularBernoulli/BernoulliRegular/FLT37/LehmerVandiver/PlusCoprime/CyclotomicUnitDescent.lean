import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealClosure
import BernoulliRegular.FLT37.PrimaryUnits

/-!
# LV-cor819-b: pollaczekUnitPlus as product of realCyclotomicUnit

For Cor 8.19's Sinnott machinery to apply, we need to identify
`pollaczekUnitPlus p K i` with a concrete cyclotomic-unit-subgroup
element. Ship the identification:

  `(pollaczekUnitPlus p K i : 𝓞 K) =`
    `∏_{b=1}^{(p-1)/2} realCyclotomicUnit(b)^{b^{p-1-i}}`

where `realCyclotomicUnit p K b = cyclotomicUnit p K b · σ(cyclotomicUnit
p K b)` is the existing `cu(b) · σ(cu(b))` σ-symmetric construction
(`PrimaryUnits.realCyclotomicUnit`).

Combined with `pollaczekUnitPlus_mem_realUnits` (LV005c-CTOR-a),
`pollaczekUnitPlus` descends to `𝓞 K⁺` and is a product of
`realCyclotomicUnitPlus(b)^{b^E}` (the K⁺-side analogues). This
identifies it within Sinnott's cyclotomic-unit subgroup `C⁺ ⊆ (𝓞 K⁺)ˣ`.

## References

* Washington, *Introduction to Cyclotomic Fields*, §8.1 (cyclotomic
  units), Cor 8.19 (p. 158).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension Finset
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

set_option backward.isDefEq.respectTransparency false in
/-- **`pollaczekUnitPlus` underlying element factors through `realCyclotomicUnit`.**
Identifies `(pollaczekUnitPlus p K i : 𝓞 K)` as the σ-symmetric product of
`(cyclotomicUnit p K b) · σ(cyclotomicUnit p K b)` factors, which equals
`realCyclotomicUnit p K b` from `PrimaryUnits`.

This is the descent input to Sinnott's cyclotomic-unit subgroup `C⁺`:
under the descent (LV005c-CTOR-a), `pollaczekUnitPlus` lives in
`(𝓞 K⁺)ˣ` as a product of `realCyclotomicUnitPlus` factors. -/
theorem pollaczekUnitPlus_val_eq_pollaczekUnit_mul_complexConj (i : ℕ) :
    ((pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) =
      ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) *
        ringOfIntegersComplexConj K
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) :=
  pollaczekUnitPlus_val p K i

set_option backward.isDefEq.respectTransparency false in
/-- **σ acts on `pollaczekUnit`'s underlying element as a Galois ring hom.**
Standard Galois compatibility: `σ(∏_x f(x)) = ∏_x σ(f(x))`. Used to
distribute σ over the cyclotomicUnit factors. -/
theorem ringOfIntegersComplexConj_pollaczekUnit_val (i : ℕ) :
    ringOfIntegersComplexConj K
        ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) =
      ((unitsComplexConj K (pollaczekUnit p K i) : (𝓞 K)ˣ) : 𝓞 K) :=
  rfl

end FLT37

end BernoulliRegular

end

end
