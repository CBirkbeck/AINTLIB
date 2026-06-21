import BernoulliRegular.FLT37.LehmerVandiver.CaseI.Main
import FltRegular.CaseI.Statement

/-!
# LV008-CTOR-a: case I factor ideals are `p`-th powers

Foundational ideal-theoretic input to the case-I bridge: under FLT case I
hypotheses (`a^p + b^p = c^p`, `gcd(a,b,c) = 1`, `p ∤ a·b·c`), each
cyclotomic factor `(a + ζ * b)` generates an ideal that is a `p`-th
power as a fractional ideal:

  `Ideal.span ({a + ζ * b} : Set (𝓞 K)) = I^p`   for some `I : Ideal (𝓞 K)`.

This is **regularity-free** — the proof uses only the polynomial
factorisation `a^p + b^p = ∏_ζ (a + ζ b)`, pairwise coprimality of the
factor ideals (`fltIdeals_coprime`), and unique factorisation in the
Dedekind domain `𝓞 K`. Available in flt-regular as
`FltRegular.exists_ideal`; this file provides a thin wrapper
matching the LV008 chain's surface.

The downstream step — going from "I^p principal" to "I principal" — is
the regularity-or-Vandiver step (case I, then needs the eigenspace
analysis under `p ∤ h⁺` to discharge without `IsRegularPrime`).

## References

* flt-regular's `FltRegular.CaseI.Statement.exists_ideal`.
* Washington, *Introduction to Cyclotomic Fields*, §9.1 (case I
  ideal-theoretic setup).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Ideal Polynomial

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

set_option backward.isDefEq.respectTransparency false in
/-- **Case I factor ideal is a `p`-th power.** Direct wrapper of
`FltRegular.exists_ideal`: under FLT case I hypotheses (with
`p ≥ 5`), each cyclotomic factor `(a + ζ b)` generates an ideal that is
a `p`-th power as a fractional ideal in `𝓞 (CyclotomicField p ℚ)`.

This is a *regularity-free* statement; only the LV-route's `¬ p ∣ h⁺`
hypothesis (unused here) enters at the descent step that converts
`I^p` principal into `I` principal. -/
theorem caseI_factor_idealSpan_eq_pow
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 (CyclotomicField p ℚ)}
    (hζ : ζ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))) :
    ∃ I : Ideal (𝓞 (CyclotomicField p ℚ)),
      Ideal.span ({(a : 𝓞 (CyclotomicField p ℚ)) + ζ *
        (b : 𝓞 (CyclotomicField p ℚ))} :
          Set (𝓞 (CyclotomicField p ℚ))) = I ^ p :=
  FltRegular.exists_ideal hp5 heq hgcd hcaseI hζ

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
