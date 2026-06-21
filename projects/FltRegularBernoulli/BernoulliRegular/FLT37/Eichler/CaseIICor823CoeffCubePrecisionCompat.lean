import BernoulliRegular.FLT37.Eichler.CaseIICor823ThirdOrderCoeff

/-!
# Precision compatibility of the mod-`p³` and mod-`p²` Dwork-coordinate functionals

This file proves the **unconditional precision-compatibility** of the third-order coordinate
`valuedLambdaQuotientDworkCoeffModCube` and the second-order coordinate
`valuedLambdaQuotientDworkCoeffModSq`: for any element `Q` of the mod-`p³` quotient
`ValuedIntegerRing p K ⧸ (lambdaIdeal p K)^(3(p-1))`,

  `castHom (p²∣p³) (valuedLambdaQuotientDworkCoeffModCube i Q) =
     valuedLambdaQuotientDworkCoeffModSq i (factorPow (p²∣p³) Q)`,

where `factorPow : ⧸(λ)^{3(p-1)} → ⧸(λ)^{2(p-1)}` is the canonical precision-lowering ring map.

Both coordinate functionals read the **same** Dwork power-basis coordinate
`(dworkParameterPowerBasis p K).repr (algebraMap x) i` of a representative `x`; the mod-`p³` one
reduces it with `rationalPadicIntegerToZModCube` and the mod-`p²` one with
`rationalPadicIntegerToZModSq`, and these are related by `castHom_rationalPadicIntegerToZModCube`
(`castHom ∘ toZModCube = toZModSq`).  No slice agreement is needed — this is the pure
coordinate-functional precision compatibility.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace BernoulliRegular
namespace CyclotomicUnits

open PadicLogSetup PadicLogSetup.DworkParameter
open Furtwaengler.KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]

omit [NumberField.IsCMField K] in
/-- **`factorPow (p²∣p³)` carries the mod-`p³` class of `x` to its mod-`p²` class** (proven): the
canonical precision-lowering ring map `⧸(λ)^{3(p-1)} → ⧸(λ)^{2(p-1)}` sends `mk_{3(p-1)} x` to
`mk_{2(p-1)} x`.  Direct application of `Ideal.Quotient.factor_mk`. -/
theorem factorPow_three_to_two_mk (x : ValuedIntegerRing p K) :
    (Ideal.Quotient.factorPow (lambdaIdeal p K)
        (by nlinarith : 2 * (p - 1) ≤ 3 * (p - 1)))
      (Ideal.Quotient.mk ((lambdaIdeal p K) ^ (3 * (p - 1))) x) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (2 * (p - 1))) x := by
  exact Ideal.Quotient.factor_mk _ x

omit [NumberField.IsCMField K] in
/-- **Precision compatibility of the mod-`p³` and mod-`p²` Dwork coordinate functionals** (proven,
axiom-clean): for any `Q` in the mod-`p³` quotient,

  `castHom (p²∣p³) (valuedLambdaQuotientDworkCoeffModCube i Q) =
     valuedLambdaQuotientDworkCoeffModSq i (factorPow (p²∣p³) Q)`.

Pick a representative `x` of `Q` (`mk_{3(p-1)} x = Q`).  Then `coordCube i Q =
toZModCube(repr(algebraMap x) i)` (`_mk`) and `castHom ∘ toZModCube = toZModSq`
(`castHom_rationalPadicIntegerToZModCube`); and `factorPow Q = mk_{2(p-1)} x`
(`factorPow_three_to_two_mk`), so `coordModSq i (factorPow Q) = toZModSq(repr(algebraMap x) i)`
(`_mk`).  Both sides are `toZModSq(repr(algebraMap x) i)`.  No slice agreement is needed; this is the
pure functional precision compatibility. -/
theorem castHom_valuedLambdaQuotientDworkCoeffModCube_eq_coeffModSq_factorPow
    (i : Fin (p - 1))
    (Q : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (3 * (p - 1))) :
    (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2)))
        (valuedLambdaQuotientDworkCoeffModCube (p := p) (K := K) i Q) =
      valuedLambdaQuotientDworkCoeffModSq (p := p) (K := K) i
        (Ideal.Quotient.factorPow (lambdaIdeal p K)
          (by nlinarith : 2 * (p - 1) ≤ 3 * (p - 1)) Q) := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective Q
  subst hx
  rw [valuedLambdaQuotientDworkCoeffModCube_mk, factorPow_three_to_two_mk,
    valuedLambdaQuotientDworkCoeffModSq_mk, castHom_rationalPadicIntegerToZModCube]

end CyclotomicUnits
end BernoulliRegular

end
