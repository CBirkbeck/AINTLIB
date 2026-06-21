import BernoulliRegular.FLT37.LehmerVandiver.CaseI.IdealConjugate
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.IsPrincipalUnderHPlus

/-!
# LV010-B: caseI `𝔞 · σ𝔞` is principal under `¬ p ∣ h⁺`

Building on LV008-CTOR-b (`(I·σI)^p` descends from K⁺) and the existing
project engine `Hilbert90.isPrincipal_mul_complexConj_of_pow_of_VC`, we
ship the Vandiver-style descent step:

  `(α) = 𝔞^p` + `¬ p ∣ h⁺(K)` ⟹ `𝔞 · σ𝔞` is principal in `𝓞 K`.

This says `[𝔞] · [σ𝔞] = 1` in `Cl(K)`, equivalently
`[σ𝔞] = [𝔞]⁻¹`. **Note**: this is NOT yet the Vandiver class equality
`[σ𝔞] = [𝔞]` (which is required by LV010-A's engine). The class
equality requires a primary-witness argument (Vandiver 1934 / Washington
9.3) that derives `[σ𝔞] = [𝔞]` from arithmetic primarity of the case-I
factor `(a + ζ b)`. That argument is the deepest piece of LV010 and
requires more work.

What we ship here is the half-step that the engine `isPrincipal_mul_…`
provides directly: under `¬ p ∣ h⁺`, the SYMMETRIC product `𝔞 · σ𝔞`
descends to a principal ideal of `𝓞 K`. The remaining gap to
`𝔞 itself principal` is precisely the class-equality input.

## References

* Project file `BernoulliRegular/FLT37/Hilbert90.lean` line 354
  (`isPrincipal_mul_complexConj_of_pow_of_VC`).
* Vandiver, Bull. AMS 40 (1934), Theorem 1.
* Washington, *Introduction to Cyclotomic Fields*, Theorem 9.3.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField Ideal

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **LV010-B: `𝔞 · σ𝔞` is principal under `¬ p ∣ h⁺`.** Direct wrapper
of `isPrincipal_mul_complexConj_of_pow_of_VC` (`Hilbert90.lean` line
354). Given `(α) = 𝔞^p` for nonzero `α`, the symmetric product
`𝔞 · σ𝔞` is principal in `𝓞 K`.

This says `[𝔞] · [σ𝔞] = 1` in `Cl(K)`. -/
theorem caseI_ideal_mul_conj_isPrincipal_of_not_dvd_hPlus
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    {α : 𝓞 K} (hα : α ≠ 0)
    {𝔞 : Ideal (𝓞 K)} (h𝔞_nz : 𝔞 ≠ ⊥)
    (h : Ideal.span ({α} : Set (𝓞 K)) = 𝔞 ^ p) :
    (𝔞 * 𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).IsPrincipal :=
  isPrincipal_mul_complexConj_of_pow_of_VC
    (p := p) (K := K)
    (coprime_card_classGroup_Kplus_of_not_dvd_hPlus h_not_dvd) hα h𝔞_nz h

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
