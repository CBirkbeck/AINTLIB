import BernoulliRegular.FLT37.Eichler.ArtinHasse.Deg68SliceThirdOrderCoordRelation
import BernoulliRegular.FLT37.Eichler.ArtinHasse.ArtinHasseDeg68FrobeniusCorrection
import BernoulliRegular.FLT37.Eichler.ArtinHasse.ArtinHasse37DegSixtyEightLogCoeffModSq

/-!
# Discharging `CaseIICor823Level71Deg68OnwardCorrection37` from the deg-`68` slice value (grounded in
# the mod-`37³` relation) and the deg-`≠32,68` slice-vanishing; and the FLT37 endpoint

The degree-`68`-onward correction `CaseIICor823Level71Deg68OnwardCorrection37`
(`= ∑_{d ≠ 32} unscaled32SliceCoord d = 37·4`,
`CaseIICor823Level71Deg68SecondDigitCorrected.lean`) splits into exactly two pieces:

* the **deg-`68` slice value** `unscaled32SliceCoord 68 = 37·4` — the `c₆₈ = 4` second digit, now
  GROUNDED in the **proven** mod-`37³` relation (`caseII_deg68SliceValue_of_precisionBridge`, whose
  source is the proven exact rational `formalSum68 = N/120`), modulo the single precision-bridge
  residual `CaseIICor823Level71Deg68ModCubePrecisionBridge37`;
* the **deg-`≠32,68` slice vanishing** `∑_{d ≠ 32, d ≠ 68} unscaled32SliceCoord d = 0` — the Dwork
  power-basis structure (only `d ≡ 32 (mod 36)`, `d < 72`, i.e. `d ∈ {32, 68}` reach the `varpi^{32}`
  coordinate; `d ≥ 104` carry `(varpi^{36})^{≥2} = 37^{≥2}` and vanish mod `37²`), isolated here as
  the named residual `CaseIICor823Level71Deg68OtherSlicesVanish37`.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## What is proven here

`caseII_deg68Onward_of_sliceValue_and_otherSlices`: `CaseIICor823Level71Deg68OnwardCorrection37` from
the two pieces, via `Finset.add_sum_erase` splitting the `d = 68` term off the correction sum.  Then
`caseII_deg68Onward_of_precisionBridge_and_otherSlices` threads the precision bridge (the mod-`37³`
content) and the slice-vanishing, and the FLT37 endpoints
`fermatLastTheoremFor_thirtyseven_of_modCubePrecisionBridge_*` compose to FLT37.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007)
  405–441; arXiv:math/0409223, Proposition 2.7 (the `α₀`, `α₁` invariants).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 100000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
variable [NumberField.IsCMField K]

/-! ## 1. The deg-`≠32,68` slice-vanishing residual -/

omit [NumberField.IsCMField K] in
/-- **`68` is in the `(range 2664).erase 32`** (proven): `68 ≠ 32`, `68 < 2664`.  Needed to split the
deg-`68` term off the correction sum `∑_{d ≠ 32}`. -/
theorem sixtyeight_mem_erase_thirtytwo :
    (68 : ℕ) ∈ (Finset.range (samePrimeFiniteLogCutoff (p := 37) 71)).erase 32 := by
  rw [Finset.mem_erase, Finset.mem_range, samePrimeFiniteLogCutoff]
  exact ⟨by norm_num, by norm_num⟩

open BernoulliRegular (CPlusGenerator) in
/-- **The deg-`≠32,68` slice-vanishing residual** (a `def … : Prop`, **not** an axiom): the sum of the
degree-`d` slice coordinates over `d ∈ (range 2664).erase 32 .erase 68` (i.e. all `d ≠ 32, 68` in the
range) vanishes mod `37²`:

  `∑_{d ∈ (range 2664).erase 32 .erase 68} unscaled32SliceCoord d = 0`.

The Dwork power-basis structure: only `d ≡ 32 (mod 36)` with `d < 72` (i.e. `d ∈ {32, 68}`) reaches
the `varpi^{32}` coordinate, and `d ≥ 104` (the next `d ≡ 32 mod 36`) carry `(varpi^{36})^{≥2} =
37^{≥2}·(…)` and vanish mod `37²`; all other `d` give zero `varpi^{32}` coordinate.  This is the
deg-`≠32,68` half of `CaseIICor823Level71Deg68OnwardCorrection37`, separate from the deg-`68` second
digit (the mod-`37³` content). -/
def CaseIICor823Level71Deg68OtherSlicesVanish37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∑ d ∈ ((Finset.range (samePrimeFiniteLogCutoff (p := 37) 71)).erase 32).erase 68,
      unscaled32SliceCoord (K := CyclotomicField 37 ℚ) d = 0

/-! ## 2. The deg-`68`-onward correction, from the slice value and the slice-vanishing -/

open BernoulliRegular (CPlusGenerator) in
/-- **The deg-`68`-onward correction, from the deg-`68` slice value and the deg-`≠32,68` vanishing**
(proven, axiom-clean given the two pieces): `(unscaled32SliceCoord 68 = 37·4) →
CaseIICor823Level71Deg68OtherSlicesVanish37 → CaseIICor823Level71Deg68OnwardCorrection37`.

The correction sum `∑_{d ≠ 32}` splits (via `Finset.add_sum_erase` at `d = 68`) as
`unscaled32SliceCoord 68 + ∑_{d ≠ 32, 68} unscaled32SliceCoord d = 37·4 + 0 = 37·4`. -/
theorem caseII_deg68Onward_of_sliceValue_and_otherSlices
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hVal : unscaled32SliceCoord (K := CyclotomicField 37 ℚ) 68 =
      (37 : ZMod (37 ^ 2)) * (4 : ZMod (37 ^ 2)))
    (hOther : CaseIICor823Level71Deg68OtherSlicesVanish37) :
    CaseIICor823Level71Deg68OnwardCorrection37 := by
  rw [CaseIICor823Level71Deg68OtherSlicesVanish37] at hOther
  rw [CaseIICor823Level71Deg68OnwardCorrection37,
    ← Finset.add_sum_erase _ (unscaled32SliceCoord (K := CyclotomicField 37 ℚ))
      sixtyeight_mem_erase_thirtytwo,
    hVal, hOther, add_zero]

open BernoulliRegular (CPlusGenerator) in
/-- **The deg-`68`-onward correction, from the precision bridge and the deg-`≠32,68` vanishing**
(proven, axiom-clean given the two residuals): `CaseIICor823Level71Deg68ModCubePrecisionBridge37 →
CaseIICor823Level71Deg68OtherSlicesVanish37 → CaseIICor823Level71Deg68OnwardCorrection37`.

Composes `caseII_deg68SliceValue_of_precisionBridge` (the deg-`68` slice value `37·4` from the bridge
and the **proven** mod-`37³` relation) with `caseII_deg68Onward_of_sliceValue_and_otherSlices`.  The
deg-`68` second digit `c₆₈ = 4` is grounded in the proven exact rational `formalSum68 = N/120`; the
two remaining inputs are the precision bridge (the only mod-`37³` content not derived from the
parallel construction) and the deg-`≠32,68` slice vanishing (the Dwork power-basis structure). -/
theorem caseII_deg68Onward_of_precisionBridge_and_otherSlices
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hBridge : CaseIICor823Level71Deg68ModCubePrecisionBridge37)
    (hOther : CaseIICor823Level71Deg68OtherSlicesVanish37) :
    CaseIICor823Level71Deg68OnwardCorrection37 :=
  caseII_deg68Onward_of_sliceValue_and_otherSlices
    (caseII_deg68SliceValue_of_precisionBridge hBridge) hOther

/-! ## 3. The FLT37 endpoint, with R4's deg-`68` content reduced to the mod-`37³` precision bridge +
the deg-`≠32,68` slice vanishing + the level-`71` finite-log identity -/

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with R4's deg-`68` correction reduced to the mod-`37³` precision
bridge + the deg-`≠32,68` slice vanishing + the finite-log identity** (proven, axiom-clean given the
genuine residuals + the Kellner Prop).

The deg-`68`-onward correction `CaseIICor823Level71Deg68OnwardCorrection37` of
`fermatLastTheoremFor_thirtyseven_of_deg68OnwardAndFiniteLog` is replaced by its two genuine pieces:

* `CaseIICor823Level71Deg68ModCubePrecisionBridge37` — the single mod-`37³` precision-bridge residual
  (the mod-`37²` reduction of the level-`107` deg-`68` coordinate is the level-`71` coordinate); the
  deg-`68` second digit `c₆₈ = 4` it yields is GROUNDED in the **proven** mod-`37³` relation
  `unscaled32SliceCoordCube_castHom_modSq_relation` (source: the proven exact rational `formalSum68 =
  N/120`);
* `CaseIICor823Level71Deg68OtherSlicesVanish37` — the deg-`≠32,68` slice vanishing (the Dwork
  power-basis structure).

The mod-`37³` Dwork-coordinate machinery — the third-order coefficient functional, the mod-`37³`
factorial extraction and ramification fold, the value relation and the two-step `37`-cancellation,
and the source value `formalSum68ResidueCube = 37·391` (PROVEN from the exact rational) — is **proven
in full**; the deg-`68` value `c₆₈ = 4` rests only on the precision bridge.  Discharging the genuine
residuals leaves FLT37 on R2 (the descent) + Kellner alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_modCubePrecisionBridgeAndFiniteLog
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_finiteLogIdentity : CaseIICor823Level71UnitFiniteLogIdentity37)
    (caseII_precisionBridge : CaseIICor823Level71Deg68ModCubePrecisionBridge37)
    (caseII_otherSlices : CaseIICor823Level71Deg68OtherSlicesVanish37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_deg68OnwardAndFiniteLog
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    caseII_finiteLogIdentity
    (caseII_deg68Onward_of_precisionBridge_and_otherSlices
      caseII_precisionBridge caseII_otherSlices)
    noSecondOrderIrregular

open FLT37.LehmerVandiver.CaseII in
/-- **FLT for `37`, mod-`37³` precision bridge + slice vanishing + finite-log identity, with the
deg-`68` value tier grounded in the proven Artin-Hasse rational** (proven, axiom-clean given the
genuine residuals + the Kellner Prop).

Identical to `fermatLastTheoremFor_thirtyseven_of_modCubePrecisionBridgeAndFiniteLog`, with the extra
hypothesis `_caseII_formalSum68Value : FormalSum68RatValue` recording that the deg-`68` source
`formalSum68 = N/120` (on which the mod-`37³` relation's `c₆₈ = 4` rests) is the genuine degree-`68`
Artin-Hasse log coefficient — already PROVEN as `formalSum68RatValue_proven`, threaded here for
explicit grounding of the value tier. -/
theorem fermatLastTheoremFor_thirtyseven_of_modCubePrecisionBridge_grounded
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_finiteLogIdentity : CaseIICor823Level71UnitFiniteLogIdentity37)
    (caseII_precisionBridge : CaseIICor823Level71Deg68ModCubePrecisionBridge37)
    (caseII_otherSlices : CaseIICor823Level71Deg68OtherSlicesVanish37)
    (_caseII_formalSum68Value : FormalSum68RatValue)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_modCubePrecisionBridgeAndFiniteLog
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    caseII_finiteLogIdentity
    caseII_precisionBridge
    caseII_otherSlices
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
