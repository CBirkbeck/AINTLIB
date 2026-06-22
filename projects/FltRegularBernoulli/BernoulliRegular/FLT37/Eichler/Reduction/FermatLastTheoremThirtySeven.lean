import BernoulliRegular.FLT37.Eichler.SecondOrderDescent.SquarePowerKernelAndAssumedII
import BernoulliRegular.FLT37.Eichler.CaseIIRealRootClassConjFixed

/-!
# Fermat's Last Theorem for `p = 37` via the **Theorem-9.4 / Corollary-8.23** Case-II route

This file assembles `FermatLastTheoremFor 37` on the genuine **Theorem-9.4** route to the irregular
half of the Case-II descent (the second-order Corollary-8.23 collapse), as the sound replacement for
the degenerate **Theorem-9.5** (Mirimanoff / mod-`𝔩`) route.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## What this changes vs the prior endpoint

`fermatLastTheoremFor_thirtyseven_of_genuineResiduals` (`FLT37GenuineResiduals.lean`) closes FLT37
from four residuals, the fourth being `Lemma98LocalPower37` — Washington Lemma 9.8's mod-`𝔩` Kummer
congruence (the Theorem-9.5 / Mirimanoff producer).  That producer **degenerates in the `ℓ ∣ z`
regime** (the proven `caseIISection91_real_form_vacuous_in_dvdZ_regime`), the only regime where the
descent applies it.

This endpoint replaces that single residual by the **two Theorem-9.4 residuals** of
`CaseIICor823SecondOrder.lean`:

* `Cor823DescentUnitModSqCongruence37` — Washington Theorem 9.4's producer-`μ` second-order
  congruence `(ε₁/ε₂)·(η̄_b/η̄_a)^{37} ≡` rational mod `37²`; and
* `Cor823PthPowerOfRationalModSq37` — Washington Theorem 8.22 / Corollary 8.23 (a unit `≡` rational
  mod `37²` is a `37`-th power, under `M ≤ 1`, whose single undischarged ingredient is Proposition
  8.12's single-unit `p`-adic-log valuation).

The Corollary-8.23 non-degeneracy `M ≤ 1` is **proven** (`caseII_cor823_valuation_input_proven`, from
the unconditional sharp valuation `v₃₇(B_{1,ω³¹}) = 1`).  Everything else — Case I (Eichler),
`¬ 37 ∣ h⁺` (Sinnott), the Case-II II1 (Lemma 9.2), R3 (Lemma 9.9 regular indices), and the
`37²`-power kernel — is proven.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Theorem 8.22, Corollary
  8.23, p. 171), §9.2 (Theorem 9.4, pp. 174–175).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-- **Fermat's Last Theorem for `37`, via the Theorem-9.4 / Corollary-8.23 Case-II route** (proven,
axiom-clean given the genuine residuals + the carried second-order Bernoulli Prop).

`FermatLastTheoremFor 37` from:

1. `caseII_classConjFixed : CaseIIRootClassConjFixed37` — **Case-II II1** (Washington Lemma 9.2,
   root-class conjugation-fixedness over real data);
2. `caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37` — **Case-II R2** (the
   reality-preserving single-root descent);
3. `caseII_modSq : Cor823DescentUnitModSqCongruence37` — **Theorem 9.4's producer-`μ` second-order
   congruence** `(ε₁/ε₂)·(η̄_b/η̄_a)^{37} ≡` rational mod `37²`;
4. `caseII_cor823 : Cor823PthPowerOfRationalModSq37` — **Corollary 8.23 / Theorem 8.22** (a unit
   `≡` rational mod `37²` is a `37`-th power, under the proven `M ≤ 1`);
5. `noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32` — the carried Kellner input.

Residuals 3+4 produce **Assumption II** via `caseIIOmega32_assumptionII_of_cor823` (the genuine
Theorem-9.4 route, **no** mod-`𝔩` / Theorem-9.5 / Mirimanoff input); residuals 1+2 then drive the
real-data descent to the Case-II contradiction.  Case I (Eichler), `¬ 37 ∣ h⁺` (Vandiver for `37`),
R3 (Washington Lemma 9.9 regular indices, proven `caseII_leadingExponentEigenCollapse37_proven` —
supplied internally by the Assumption-II producer), and the `37²`-power kernel are all proven.

Compared with `fermatLastTheoremFor_thirtyseven_of_genuineResiduals`, the degenerate
`Lemma98LocalPower37` is **removed**, replaced by the Theorem-9.4 residuals; this puts FLT37 on the
Theorem-9.4 route. -/
theorem fermatLastTheoremFor_thirtyseven_of_cor823
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_modSq : Cor823DescentUnitModSqCongruence37)
    (caseII_cor823 : Cor823PthPowerOfRationalModSq37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_rootClassConjFixed
    caseII_classConjFixed
    caseII_realDescent
    (caseIIOmega32_assumptionII_of_cor823 caseII_modSq caseII_cor823)
    noSecondOrderIrregular

/-- **Fermat's Last Theorem for `37`, via Corollary 8.23 from the *first-order* producer datum**
(proven, axiom-clean given the genuine residuals + the carried second-order Bernoulli Prop).

Identical to `fermatLastTheoremFor_thirtyseven_of_cor823`, but the mod-`37²` congruence residual
`Cor823DescentUnitModSqCongruence37` is replaced by the **strictly sharper** *first-order* producer
datum `Cor823CorrectedUnitPthPowerRationalModP37` — the corrected descent unit
`(ε₁/ε₂)·(η̄_b/η̄_a)^{37}` is a **global `37`-th power** `w^{37}` whose base `w = (μ_b/μ_a)^{37}` is
`≡` a rational integer mod `37` (Lemma 1.8).  The second-order mod-`37²` content is then supplied by
the **proven** `37²`-power kernel (`caseII_pow37_sub_intCast_pow37_mem_37sq`), not hypothesised.

So the genuine remaining Case-II irregular-index content is reduced to the *first-order* producer
structure (`Cor823CorrectedUnitPthPowerRationalModP37`) plus Washington Theorem 8.22 / Corollary 8.23
(`Cor823PthPowerOfRationalModSq37`, whose single undischarged ingredient is Proposition 8.12's
single-unit `p`-adic-log valuation), with the second-order non-degeneracy `M ≤ 1` and the `37²`-power
upgrade both **proven**.  No mod-`𝔩` / Theorem-9.5 / Mirimanoff input. -/
theorem fermatLastTheoremFor_thirtyseven_of_cor823_firstOrder
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_cor823 : Cor823PthPowerOfRationalModSq37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_rootClassConjFixed
    caseII_classConjFixed
    caseII_realDescent
    (caseIIOmega32_assumptionII_of_cor823_firstOrder caseII_pthPow caseII_cor823)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
