import BernoulliRegular.FLT37.Eichler.CaseIICor823SecondOrderColumnCoeff

/-!
# The level-`72` mod-`37²` Dwork column-coordinate value: the genuine atomic residual of R4

This file isolates the **single atomic scalar** behind the per-single-column second-order
coefficient identity `CaseIICor823SecondOrderColumnCoeff37`
(`CaseIICor823SecondOrderColumnCoeff.lean`).  It imports only; it does **not** modify any
existing file.  No `sorry`, no `axiom`.

## What is genuinely left, and what this file proves

The proven `ϖ ↔ λ` single-column bridge `caseIICor823SecondOrder_columnCoeffModSq_eq_evalₐ`
identifies the per-column left side of `CaseIICor823SecondOrderColumnCoeff37` (the
`rationalPadicIntegerToZModSq 37 (repr (concreteKummerLogVector a) (idx 15))`) with the `λ`-adic
level-`72` Dwork coordinate

  `valuedLambdaQuotientDworkCoeffModSq 32 (evalₐ 72 (kummerLogCompletedColumn a))`.

So `CaseIICor823SecondOrderColumnCoeff37` follows from the per-column `evalₐ`-coordinate statement
`CaseIICor823SecondOrderColumnCoordValue37` recorded below — that level-`72` coordinate equals
`factor · (((a+2)²)^{16} − 1)`.  We prove this reduction
(`caseIICor823SecondOrderColumnCoeff37_of_columnCoordValue`) via the proven bridge, then thread it
to the FLT37 endpoint (`fermatLastTheoremFor_thirtyseven_of_columnCoordValue`).

This restates R4 as a **single, fully explicit, atomic scalar computation**: the value of the
level-`72` mod-`37²` even-degree-`32` Dwork coordinate of one completed real cyclotomic-unit
logarithm column.  That is the second-order analog of the proven first-order single-column value
`valuedLambdaQuotientDworkCoeffModP_unscaledNormalizedFiniteLog_even_eq_formal` /
`concreteSquaredKummerLogMatrixEntry_congr` — the mod-`37²` level-`72` re-run of the entire
`KummerLogFormalEvaluator` chain (the first-order chain is hard-coded at level `p − 1 = 36`
throughout; see `KummerLogFormalEvaluator/Homogeneous.lean`).  No level-`72` analog of that chain
exists in the project yet; this coordinate value is the `p`-adic-`L` content that remains.

## The first-order structure, and the scalar discrepancy with the stated factor (machine-checked)

The proven first-order single-column value is, mod `37`,

  `concreteKummerLogMatrix 15 a = (2·(-(32!)⁻¹)) · bernoulliFactor 16 · ((a+2)^{32} − 1)`

(`concreteSquaredKummerLogMatrixEntry_congr`, with `squaredKummerLogUnitFactor 16 = 2·(-(32!)⁻¹)`
and `bernoulliFactor 16 = ratReductionZMod (B₃₂/32)`).  At `j = 15` this is `0` because
`37 ∣ B₃₂.num`.  Lifting that normalization to mod `37²` — replacing the mod-`37` reduction
`bernoulliFactor 16` by the `37`-adic value `(B₃₂/32) mod 37²` — gives the structurally-expected
level-`72` coordinate factor

  `firstOrderStructureLiftFactor := (2 : ZMod 37²) · (-(32!)⁻¹) · (B₃₂.num · (32·B₃₂.den)⁻¹)`.

We record (`firstOrderStructureLiftFactor_eq`, by `decide`) that this evaluates to `407 = 37·11`,
whereas the stated `caseIICor823SecondOrderBernoulliFactorModSq = B₃₂.num · 32⁻¹` evaluates to
`1073 = 37·29` (`caseIICor823SecondOrderBernoulliFactorModSq_eq_val`), and we prove
(`firstOrderStructureLiftFactor_ne_bernoulliFactor`, by `decide`) that

  `firstOrderStructureLiftFactor ≠ caseIICor823SecondOrderBernoulliFactorModSq`   (in `ZMod 37²`).

Both are of the form `37·(unit mod 37)` — which is all the downstream collapse
`cor823Omega32SecondOrderCollapse37_of_secondOrderCoeff` actually consumes (it uses only
`factor = 37·r`, `r` a unit, and the Teichmüller-Vandermonde shape `(((a+2)²)^{16} − 1)`) — but
they are **different** units: `11 ≢ 29 (mod 37)`, off by the unit
`2·(-(32!)⁻¹)·B₃₂.den⁻¹ ≡ 31 (mod 37)`.

So the level-`72` column coordinate equals the stated `factor · (((a+2)²)^{16} − 1)` **iff** the
level-`72` finite-`p`-adic-log truncation contributes the exact second-order correction
`37·18 (mod 37²)` on top of the first-order-structure lift; otherwise it equals
`firstOrderStructureLiftFactor · (((a+2)²)^{16} − 1) = 407 · (((a+2)²)^{16} − 1)` and the stated
identity fails.  Determining which requires the level-`72` evaluator computation itself; this file
isolates the residual to that single scalar and records the discrepancy as a machine-checked fact.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12,
  Theorem 8.22, Corollary 8.23, p. 171).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The atomic level-`72` column-coordinate residual

`CaseIICor823SecondOrderColumnCoordValue37` is the per-single-column `evalₐ`-coordinate form of the
target `CaseIICor823SecondOrderColumnCoeff37`: the level-`72` mod-`37²` even-degree-`32` Dwork
coordinate of one completed real cyclotomic-unit logarithm column equals the second-order Bernoulli
factor times the column's Teichmüller-Vandermonde factor `(((a+2)²)^{16} − 1)`.  It is strictly the
single-scalar core (no `repr`, no `dworkFixedEvenPowerBasis`), the genuine `p`-adic-`L` content. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The atomic level-`72` mod-`37²` Dwork column-coordinate residual** (a `def … : Prop`, **not**
an axiom — the genuine `p`-adic-`L` content of Proposition 8.12 at `i = 32`).

For every cyclotomic column `a`, the `λ`-adic level-`72` even-degree-`32` Dwork coordinate of the
completed real cyclotomic-unit logarithm column `kummerLogCompletedColumn a` equals
`caseIICor823SecondOrderBernoulliFactorModSq` (`= B₃₂.num·32⁻¹ mod 37²`) times the column's
Teichmüller-Vandermonde factor `(((a+2)²)^{16} − 1)`:

  `valuedLambdaQuotientDworkCoeffModSq 32 (evalₐ 72 (kummerLogCompletedColumn a))`
    `= caseIICor823SecondOrderBernoulliFactorModSq · ((((a+2)²)^{16} − 1) : ZMod 37²)`.

This is the single-scalar core of `CaseIICor823SecondOrderColumnCoeff37`, yielding it via the proven
`ϖ ↔ λ` bridge (`caseIICor823SecondOrderColumnCoeff37_of_columnCoordValue`).  It is the mod-`37²`
level-`72` re-run of the proven first-order single-column value
`valuedLambdaQuotientDworkCoeffModP_unscaledNormalizedFiniteLog_even_eq_formal`. -/
def CaseIICor823SecondOrderColumnCoordValue37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ a : Fin (kummerLogRank 37),
    valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
        (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
        (AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
          (kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a)) =
      caseIICor823SecondOrderBernoulliFactorModSq *
        (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)

/-! ## 2. The proven `ϖ ↔ λ` reduction: the target follows from the atomic coordinate residual -/

set_option maxHeartbeats 1600000 in
-- The `ϖ ↔ λ` bridge `caseIICor823SecondOrder_columnCoeffModSq_eq_evalₐ` is applied pointwise; its
-- statement carries the heavy `adicCompletionIntegers` `evalₐ`.  We `rw` the small
-- `rationalPadicIntegerToZModSq`-head left side and discharge the residue with `convert … using 3`,
-- which peels the application so the heavy `evalₐ` argument is matched syntactically, never forcing
-- a full `whnf`/`isDefEq` of the `adicCompletionIntegers` quotient transport (the wall).
open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIICor823SecondOrderColumnCoeff37` from the atomic level-`72` coordinate residual
`CaseIICor823SecondOrderColumnCoordValue37`** (proven, axiom-clean).

The proven single-column `ϖ ↔ λ` bridge `caseIICor823SecondOrder_columnCoeffModSq_eq_evalₐ`
identifies, for each column `a`, the per-column left side of `CaseIICor823SecondOrderColumnCoeff37`
(`rationalPadicIntegerToZModSq 37 (repr (concreteKummerLogVector a) (idx 15))`) with the level-`72`
`evalₐ` coordinate `valuedLambdaQuotientDworkCoeffModSq 32 (evalₐ 72 (kummerLogCompletedColumn a))`.
Both are set equal to the same right side `factor · (((a+2)²)^{16} − 1)`, so the per-column
coordinate residual `hVal a` gives each column of the target. -/
theorem caseIICor823SecondOrderColumnCoeff37_of_columnCoordValue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hVal : CaseIICor823SecondOrderColumnCoordValue37) :
    CaseIICor823SecondOrderColumnCoeff37 := by
  intro a
  rw [caseIICor823SecondOrder_columnCoeffModSq_eq_evalₐ a]
  convert hVal a using 3

/-- **`Prop812DescentCoeff37` from the atomic level-`72` coordinate residual** (proven, axiom-clean
given `CaseIICor823SecondOrderColumnCoordValue37`).  Composes the proven reduction with the proven
`e`-linearity reduction `prop812DescentCoeff37_of_columnCoeff`. -/
theorem prop812DescentCoeff37_of_columnCoordValue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hVal : CaseIICor823SecondOrderColumnCoordValue37) :
    Prop812DescentCoeff37 :=
  prop812DescentCoeff37_of_columnCoeff
    (caseIICor823SecondOrderColumnCoeff37_of_columnCoordValue hVal)

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the atomic level-`72` Dwork
column-coordinate value `CaseIICor823SecondOrderColumnCoordValue37`** (proven, axiom-clean given the
genuine residuals + the carried Kellner Prop).

Supplies the atomic per-single-column level-`72` mod-`37²` Dwork coordinate value to
`fermatLastTheoremFor_thirtyseven_of_columnCoeff` through the proven `ϖ ↔ λ` reduction — Washington
Proposition 8.12 at `i = 32` reduced to one explicit scalar: the level-`72` even-degree-`32` Dwork
coordinate of a single completed real cyclotomic-unit logarithm column. -/
theorem fermatLastTheoremFor_thirtyseven_of_columnCoordValue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_columnCoordValue : CaseIICor823SecondOrderColumnCoordValue37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_columnCoeff
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (caseIICor823SecondOrderColumnCoeff37_of_columnCoordValue caseII_columnCoordValue)
    noSecondOrderIrregular

/-! ## 3. The first-order-structure lift, and the scalar discrepancy with the stated factor

The proven first-order single-column value `concreteSquaredKummerLogMatrixEntry_congr` reads, mod
`37`, as `(2·(-(32!)⁻¹)) · bernoulliFactor 16 · ((a+2)^{32} − 1) = 0`.  Lifting that exact
normalization to mod `37²` (replacing the mod-`37` reduction `bernoulliFactor 16` by the `37`-adic
value `(B₃₂/32) mod 37² = B₃₂.num·(32·B₃₂.den)⁻¹`) gives the structurally-expected level-`72`
coordinate factor `firstOrderStructureLiftFactor`.  We record, by `decide`, its value `407 = 37·11`,
the stated factor's value `1073 = 37·29`, and that they **differ** in `ZMod 37²` — both `37·(unit)`
but with different units (`11 ≢ 29 (mod 37)`). -/

/-- **The first-order-structure lift of the level-`72` column coordinate factor**: the mod-`37²`
value obtained by lifting the proven first-order single-column normalization
`squaredKummerLogUnitFactor 16 · bernoulliFactor 16 = (2·(-(32!)⁻¹)) · (B₃₂/32)` from its mod-`37`
reduction to the `37`-adic value `(B₃₂/32) mod 37² = B₃₂.num·(32·B₃₂.den)⁻¹`.  Stated with the
genuine `(bernoulli 32)` numerator and denominator. -/
def firstOrderStructureLiftFactor : ZMod (37 ^ 2) :=
  (2 : ZMod (37 ^ 2)) * (-(((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) *
    ((((bernoulli 32).num : ℤ) : ZMod (37 ^ 2)) *
      ((32 * ((bernoulli 32).den : ℕ) : ℕ) : ZMod (37 ^ 2))⁻¹)

/-- **The first-order-structure lift evaluates to `407 = 37·11`** (proven).  This is the
structurally-expected value of the level-`72` even-degree-`32` Dwork column coordinate factor (the
scalar multiplying `((a+2)^{32} − 1)`), if the level-`72` finite-`p`-adic-log truncation contributes
no second-order correction beyond the first-order normalization.  We rewrite `(bernoulli 32)`'s
numerator/denominator to their proven values (`bernoulli_thirtytwo_num_eq`,
`bernoulli_thirtytwo_den_eq`) so the residue is a `decide` over numerals. -/
theorem firstOrderStructureLiftFactor_eq : firstOrderStructureLiftFactor = 407 := by
  unfold firstOrderStructureLiftFactor
  rw [bernoulli_thirtytwo_num_eq, bernoulli_thirtytwo_den_eq]
  decide +kernel

/-- **The stated second-order Bernoulli factor evaluates to `1073 = 37·29`** (proven).
`caseIICor823SecondOrderBernoulliFactorModSq = B₃₂.num·32⁻¹` (note: no `B₃₂.den`, no `(32!)`, no `2`
— it is a chosen `37·(unit)` representative, not the lifted coordinate value).  We rewrite the
symbolic numerator `(bernoulli 32).num` to its proven value `-7709321041217`
(`bernoulli_thirtytwo_num_eq`) so the residue is a `decide` over numerals. -/
theorem caseIICor823SecondOrderBernoulliFactorModSq_eq_val :
    caseIICor823SecondOrderBernoulliFactorModSq = 1073 := by
  unfold caseIICor823SecondOrderBernoulliFactorModSq
  rw [bernoulli_thirtytwo_num_eq]
  decide +kernel

/-- **The first-order-structure lift differs from the stated factor** (proven by `decide`):
`firstOrderStructureLiftFactor ≠ caseIICor823SecondOrderBernoulliFactorModSq` in `ZMod 37²`
(`407 ≠ 1073`; both `37·(unit)`, but the units differ — `11 ≢ 29 (mod 37)`, off by the unit
`2·(-(32!)⁻¹)·B₃₂.den⁻¹ ≡ 31 (mod 37)`).

Consequently the atomic residual `CaseIICor823SecondOrderColumnCoordValue37` — whose right side is
`caseIICor823SecondOrderBernoulliFactorModSq · (((a+2)²)^{16} − 1)` — holds for a column `a` with
`(((a+2)²)^{16} − 1) ≠ 0` **iff** the level-`72` finite-log truncation supplies the exact
second-order correction `37·18 (mod 37²)` on top of the first-order-structure lift; with no such
correction the level-`72` coordinate is `firstOrderStructureLiftFactor · (((a+2)²)^{16} − 1)` and
the stated residual fails.  This isolates the remaining `p`-adic-`L` content of R4 to that single
mod-`37²` correction scalar. -/
theorem firstOrderStructureLiftFactor_ne_bernoulliFactor :
    firstOrderStructureLiftFactor ≠ caseIICor823SecondOrderBernoulliFactorModSq := by
  rw [firstOrderStructureLiftFactor_eq, caseIICor823SecondOrderBernoulliFactorModSq_eq_val]
  decide

end BernoulliRegular.FLT37.Eichler

end
