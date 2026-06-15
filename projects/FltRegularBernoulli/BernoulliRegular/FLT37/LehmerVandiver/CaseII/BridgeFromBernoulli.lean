import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.KStickelberger
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.Main


/-!
# LV009-LV010-CTOR: CaseII bridge construction (Washington 9.4)

Under `¬ p ∣ h⁺(K)` plus the **second-order non-irregularity condition**
`NoSecondOrderIrregularPair p i` (= `¬ p^3 ∣ B_{i·p}.num`), the case-II
bridge holds.

## Strategy (Washington Theorem 9.4)

1. Standard cyclotomic descent: case II has `p ∣ c`, so the cyclotomic
   factor `(a + ζ^k b)` has a higher `(ζ-1)`-valuation.
2. The second-order Mirimanoff argument (Washington §9.1): the
   higher valuation produces a second-order Bernoulli congruence
   `B_{ip} ≡ 0 (mod p^3)` IF case II had a solution.
3. The Bernoulli condition `¬ p^3 ∣ B_{ip}.num` (the
   `NoSecondOrderIrregularPair` predicate) contradicts step 2.
4. Hence no case II solution.

## Reduction to one Prop

`CaseIIBridgeFromBernoulli`: `¬p∣h⁺` + `NoSecondOrderIrregularPair p i`
+ K-side Stickelberger ⟹ `CaseIIBridge p K i`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **`CaseIIBridgeFromBernoulli`**: Prop asserting that
`KSideStickelbergerAnnihilator + ¬p∣h⁺ + NoSecondOrderIrregularPair`
together imply `CaseIIBridge p K i`.

The proof structure:
1. Standard cyclotomic descent gives case-II ideals with controlled
   `(ζ-1)`-valuation.
2. Stickelberger + ¬p∣h⁺ gives principalization.
3. Mirimanoff second-order Taylor expansion + Bernoulli condition
   contradicts existence of case-II solutions. -/
def CaseIIBridgeFromBernoulli (i : ℕ) (_hp_odd : p ≠ 2) : Prop :=
  KSideStickelbergerAnnihilator p K →
  ¬ (p : ℕ) ∣ hPlus K →
  NoSecondOrderIrregularPair p i →
  CaseIIBridge p K i

end Sinnott

end FLT37

end BernoulliRegular

end
