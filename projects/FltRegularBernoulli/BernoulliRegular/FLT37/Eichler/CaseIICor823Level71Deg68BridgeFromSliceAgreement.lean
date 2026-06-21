import BernoulliRegular.FLT37.Eichler.CaseIICor823Level71Deg68BridgeReduction
import BernoulliRegular.FLT37.Eichler.CaseIICor823Level71Deg68OnwardDischarge
import BernoulliRegular.FLT37.Eichler.CaseIICor823Deg68SliceLevelAgreement

/-!
# FLT37 II2 (route B), with the mod-`37³` precision bridge replaced by the clean same-level deg-`68`
# slice-coordinate agreement

The precision-bridge residual `CaseIICor823Level71Deg68ModCubePrecisionBridge37` is **provably reduced**
(via the unconditional coordinate precision-compatibility
`castHom_valuedLambdaQuotientDworkCoeffModCube_eq_coeffModSq_factorPow`,
`CaseIICor823CoeffCubePrecisionCompat.lean`) to the single same-level (`ZMod 37²`) statement

  `CaseIICor823Level71Deg68SliceCoordAgreement37`:
    `coordModSq 32 (factorPow (72≤108) (deg-68 slice @ 107)) = unscaled32SliceCoord 68`.

This file threads that reduction (`caseII_precisionBridge_of_sliceCoordAgreement`) into the FLT37
endpoint, so the mod-`37³` connective tissue of the deg-`68` second digit `c₆₈ = 4` is carried by the
clean **same-level** slice-coordinate agreement rather than the mod-`37³` precision bridge.

## Mathematical status of the slice-coordinate agreement

`CaseIICor823Level71Deg68SliceCoordAgreement37` is the assertion that the level-`107` deg-`68` Dwork
slice, folded to precision `72`, has the same `varpi^{32}` coordinate as the level-`71` deg-`68` slice.
Its complete mathematical content is **proven** in `CaseIICor823Deg68SliceLevelAgreement.lean`:

* the slices' Artin-Hasse numerators agree mod `(λ)^{108}` (`deg68_numerator_level_diff_mem`, from the
  homogeneity `…_pow_coeff_eq_mul_pow` and `x₁₀₇^{68} − x₇₁^{68} ∈ (λ)^{139}`);
* the abstract `samePrimeNatDivEval_level72_eq_of_sub_mem`: a `(λ)^{108}` numerator difference forces
  the `samePrimeNatDivEval` (and hence the `varpi^{32}` coordinate) to agree at level `72` (the `a =
  37` Frobenius `/37` keeps the agreement at `(λ)^{72}`).

The concrete instantiation at the deg-`68` numerators is mathematically complete but hits the
documented Lean `adicCompletionIntegers` `isDefEq` elaboration wall (the `Classical.choose` numerator
in a concrete `samePrimeNatDivEval` cannot be type-checked); it is carried as the residual hypothesis
`caseII_sliceCoordAgreement` here, strictly **cleaner** (a single `ZMod 37²` equation) than the
mod-`37³` precision bridge it replaces.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 100000

open NumberField
open scoped BigOperators

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with R4's deg-`68` content reduced to the clean same-level
slice-coordinate agreement + the deg-`≠32,68` slice vanishing + the finite-log identity** (proven,
axiom-clean given the genuine residuals + the Kellner Prop).

The mod-`37³` precision-bridge residual
`CaseIICor823Level71Deg68ModCubePrecisionBridge37` of
`fermatLastTheoremFor_thirtyseven_of_modCubePrecisionBridgeAndFiniteLog` is replaced by the **proven
reduction** `caseII_precisionBridge_of_sliceCoordAgreement` applied to the clean same-level residual
`CaseIICor823Level71Deg68SliceCoordAgreement37`.  By the unconditional precision-compatibility
(`castHom ∘ coordCube = coordModSq ∘ factorPow`, proven), this same-level `ZMod 37²` equation **is**
the mod-`37³` bridge; the deg-`68` second digit `c₆₈ = 4` it yields is grounded in the proven mod-`37³`
relation (source: the proven exact Artin-Hasse rational `formalSum68 = N/120`).  Discharging the
genuine residuals leaves FLT37 on R2 (the descent) + Kellner alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_sliceCoordAgreementAndFiniteLog
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_finiteLogIdentity : CaseIICor823Level71UnitFiniteLogIdentity37)
    (caseII_sliceCoordAgreement : CaseIICor823Level71Deg68SliceCoordAgreement37)
    (caseII_otherSlices : CaseIICor823Level71Deg68OtherSlicesVanish37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_modCubePrecisionBridgeAndFiniteLog
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    caseII_finiteLogIdentity
    (caseII_precisionBridge_of_sliceCoordAgreement caseII_sliceCoordAgreement)
    caseII_otherSlices
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
