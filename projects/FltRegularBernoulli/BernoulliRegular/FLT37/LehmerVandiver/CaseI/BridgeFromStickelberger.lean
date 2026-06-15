import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.KStickelberger
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.Bridge


/-!
# LV008-CTOR: CaseI bridge construction (Vandiver 1934)

Under `¬ p ∣ h⁺(K)` and the K-side Stickelberger annihilator
(`KSideStickelbergerAnnihilator`), the case-I cyclotomic factor ideals
become principal. Combined with the existing `_of_regular` Mirimanoff
chain (which uses principality, not full regularity), this discharges
`CaseIBridge`.

## Strategy (Vandiver 1934 Theorem 1)

1. Cyclotomic factor `(a + ζ^k b)` produces an ideal `I` with `[I]^p = 1`
   in `ClassGroup`.
2. By the structure `[I]` lives in `Cl(K)⁺ × Cl(K)⁻`.
3. Under `¬ p ∣ h⁺`, `Cl(K)⁺[p]` is trivial.
4. Under K-side Stickelberger, `[I]⁻` (the minus part) is annihilated.
5. So `[I]` is trivial in `ClassGroup`, hence `I` is principal.
6. With `I` principal, the existing `caseIBridge_of_classEqDischarge`
   chain applies.

## Reduction to one Prop

`CaseIBridgeFromStickelbergerAnnihilator`: under
`KSideStickelbergerAnnihilator` and `¬p∣h⁺`, the case-I bridge holds.
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

/-- **`CaseIBridgeFromStickelbergerAnnihilator`**: Prop asserting that
`KSideStickelbergerAnnihilator` + `¬ p ∣ hPlus K` ⟹ `CaseIBridge p K`.

This is the structural reduction: the K-side Stickelberger annihilator
combined with the `Cl(K)⁺` triviality (from `¬p∣h⁺`) gives principality
of cyclotomic factor ideals, hence case I closure via the existing
Mirimanoff chain. -/
def CaseIBridgeFromStickelbergerAnnihilator (_hp_odd : p ≠ 2) : Prop :=
  KSideStickelbergerAnnihilator p K →
  ¬ (p : ℕ) ∣ hPlus K →
  CaseIBridge p K

end Sinnott

end FLT37

end BernoulliRegular

end
