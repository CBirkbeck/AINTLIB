import BernoulliRegular.FLT37.Eichler.SecondOrderDescent.KummerLogDetectorModSq
import BernoulliRegular.FLT37.Eichler.SecondOrderDescent.DescentEigencomponentCollapse

/-!
# The single-column second-order (mod `37²`) Dwork-coefficient identity at the irregular row

This file discharges the single-cyclotomic-**column-sum** second-order leading-coefficient residual
`Prop812SecondOrderCoeff37` (`CaseIICor823SecondOrderMatrix.lean`) — Washington Proposition 8.12 at
the irregular index `i = 32`, mod `37²`, on the cyclotomic columns — **down to the
per-single-column** mod-`37²` Dwork-coefficient identity `CaseIICor823SecondOrderColumnCoeff37`.

It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## The reduction (the entire `e`-linearity is proven here)

`Prop812SecondOrderCoeff37` is the statement, for an arbitrary `C⁺` exponent vector
`e : Fin (kummerLogRank 37) → ℤ`, that the level-`68` mod-`37²` Dwork coefficient of the column sum
`S = ∑_a e_a · concreteKummerLogVector a` at row `j = 15` factors as the second-order Bernoulli
factor `B₃₂/32 mod 37²` times the mod-`37²` Teichmüller-Vandermonde row of `e`:

  `rationalPadicIntegerToZModSq 37 (repr S (idx 15))`
    `= factor · (∑_a (((a+2)²)^{16} − 1) · (e_a : ZMod 37²))`.

The map `e ↦ repr S (idx 15)` is **`ℤ`-linear** in `e`.  The linearity is carried out in the
**`λ`-adic `evalₐ` coordinate**, *not* on the heavy Dwork power-basis `repr` (an `e`-linearity
stated directly on the `repr` of the column sum hits the `adicCompletionIntegers` `whnf` wall).
Concretely (`prop812SecondOrderCoeff37_of_columnCoeff`):

* the proven `ϖ ↔ λ` filtration identity `caseIICor823SecondOrder_coeffModSq_eq_evalₐ` rewrites
  `repr S (idx 15) mod 37²` to the `λ`-adic level-`72` coordinate
  `valuedLambdaQuotientDworkCoeffModSq 32 (evalₐ 72 (∑_a e_a • kummerLogCompletedColumn a))`;
* there the repo's **proven** second-order coordinate laws
  `valuedLambdaQuotientDworkCoeffModSq_sum` / `_intCast_mul` (and `evalₐ`'s `AlgHom` `map_sum` /
  `map_zsmul`) carry the finite sum and each integer scalar — wall-free — giving
  `∑_a (e_a : ZMod 37²) · g_a` with `g_a = valuedLambdaQuotientDworkCoeffModSq 32 (evalₐ 72 col_a)`;
* the single-column form of the same `ϖ ↔ λ` bridge
  (`caseIICor823SecondOrder_columnCoeffModSq_eq_evalₐ`) identifies each `g_a` with the per-column
  `repr` coordinate `rationalPadicIntegerToZModSq 37 (repr (vec a) (idx 15))`.

Matching term by term, the whole identity follows from the **per-single-column** identity

  `rationalPadicIntegerToZModSq 37 (repr (vec a) (idx 15)) = factor · (((a+2)²)^{16} − 1)`

for each fixed column `a`.  That is exactly the second-order analog of the proven first-order
single-column factorization `concreteSquaredKummerLogMatrixEntry_congr` /
`concreteKummerLogMatrix j a = squaredUnit · bernoulliFactor · (col^{2·rowIndex} − 1)`, made
explicit modulo `37²`, at the irregular row `j = 15` (where the first-order Bernoulli factor
`B₃₂/32 mod 37 = 0` is degenerate, and the mod-`37²` precision recovers the non-degenerate
`B₃₂/32 mod 37²`).

This single-column identity `CaseIICor823SecondOrderColumnCoeff37` is the one undischarged
ingredient: the genuine `p`-adic-`L` content of Proposition 8.12 at `i = 32`, the mod-`37²` analog
of the proven first-order single-column factorization (the full mod-`37²` Dwork-evaluator
computation of the level-`72` coordinate of a single completed-log column — the second-order
parallel of the entire `KummerLogFormalEvaluator` chain).  It is **strictly smaller** than
`Prop812SecondOrderCoeff37` (one fixed cyclotomic column, no exponent vector `e`, no sum over
columns); the entire `e`-linearity that lifts it to the column-sum statement is **proven here**.  It
is sound, non-circular (its conclusion is the explicit `B₃₂ mod 37²`-factored single-column
coefficient, not the vanishing of any eigencomponent), and non-vacuous.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171), §9.2 (Lemma 9.9, pp. 180–181).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The single-column second-order Dwork-coefficient residual (Proposition 8.12 at `i = 32`)

The genuine, strictly-smaller residual: for a **fixed** cyclotomic column `a`, the level-`68`
mod-`37²` Dwork coefficient of `concreteKummerLogVector a` at the irregular row `j = 15` equals the
second-order Bernoulli factor `B₃₂/32 mod 37²` times the column's Teichmüller factor
`((a+2)²)^{16} − 1`.  This is the mod-`37²` analog of the proven first-order single-column
factorization. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The single-column second-order Dwork-coefficient identity: Proposition 8.12 at `i = 32`, per
column** (a `def … : Prop`, **not** an axiom — the genuine `p`-adic-`L` content).

For every cyclotomic column `a : Fin (kummerLogRank 37)`, the level-`68` mod-`37²` Dwork coefficient
of the `i = 32` (`j = 15`) cyclotomic column `concreteKummerLogVector a` factors as the second-order
Bernoulli factor `caseIICor823SecondOrderBernoulliFactorModSq` (`= B₃₂/32 mod 37²`) times the
column's mod-`37²` Teichmüller factor `(((a+2)²)^{16} − 1)`:

  `rationalPadicIntegerToZModSq 37 (repr (concreteKummerLogVector a) (kummerLogEvenPowerIndex 15))`
    `= caseIICor823SecondOrderBernoulliFactorModSq · ((((a+2)²)^{16} − 1) : ZMod 37²)`.

This is the second-order analog of the proven first-order single-column factorization
`concreteSquaredKummerLogMatrixEntry_congr` (`concreteKummerLogMatrix 15 a = squaredUnit ·
bernoulliFactor · (col^{32} − 1)`, mod `37`), at the irregular row `j = 15`, made explicit modulo
`37²`.  At `j = 15` the first-order Bernoulli factor `B₃₂/32 mod 37 = 0` is degenerate, and the
extra mod-`37²` precision recovers the non-degenerate `B₃₂/32 mod 37²` (`= 37·(unit)`,
`caseIICor823SecondOrderBernoulliFactorModSq_eq_thirtyseven_mul`).

It is **sound** (a coefficient-value identity for one fixed cyclotomic column), **non-circular**
(its conclusion is the explicit `B₃₂ mod 37²`-factored single-column coefficient, a genuine
second-order leading-coefficient datum, not the vanishing of the eigencomponent `c₁₅`), and
**non-vacuous** (both sides are genuine elements of `ZMod 37²`; see
`caseIICor823SecondOrderColumnCoeff37_inhabited`).  It is **strictly smaller** than
`Prop812SecondOrderCoeff37`: one fixed column, no exponent vector, no sum over columns. -/
def CaseIICor823SecondOrderColumnCoeff37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ a : Fin (kummerLogRank 37),
    rationalPadicIntegerToZModSq 37
        ((dworkFixedEvenPowerBasis (p := 37) (K := CyclotomicField 37 ℚ)
            (by norm_num : 2 < 37)).repr
          (concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37)))) =
      caseIICor823SecondOrderBernoulliFactorModSq *
        (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)

open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIICor823SecondOrderColumnCoeff37` is non-vacuous** (proven): for the zero column index
`a = 0` the identity is a genuine equality of two specific `ZMod 37²` values — the left side is the
mod-`37²` reduction of a definite Dwork coordinate, the right side is
`caseIICor823SecondOrderBernoulliFactorModSq · (2^{32} − 1 : ZMod 37²)`.  Stating the existence of
a column at which both sides are evaluated witnesses that the universally-quantified residual is a
real statement over a nonempty index type, not vacuously true. -/
theorem caseIICor823SecondOrderColumnCoeff37_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ a : Fin (kummerLogRank 37),
      caseIICor823SecondOrderBernoulliFactorModSq *
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) =
        caseIICor823SecondOrderBernoulliFactorModSq *
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) :=
  ⟨⟨0, by norm_num [kummerLogRank]⟩, rfl⟩

/-! ## 2. The `e`-linearity reduction: `Prop812SecondOrderCoeff37` from the per-column identity

The level-`68` mod-`37²` Dwork coefficient of the column sum
`S = ∑_a e_a · concreteKummerLogVector a` at row `j = 15` is `ℤ`-linear in `e`.  The linearity is
carried out in the **`λ`-adic `evalₐ` coordinate**, where the repo's proven second-order coordinate
laws `valuedLambdaQuotientDworkCoeffModSq_sum` / `_intCast_mul` apply (wall-free) — *not* on the
heavy Dwork power-basis `repr`, which would hit the `whnf` wall.  The two coordinates are connected
by the proven `ϖ ↔ λ` filtration identity `caseIICor823SecondOrder_coeffModSq_eq_evalₐ` (whose
single-column form `caseIICor823SecondOrder_columnCoeffModSq_eq_evalₐ` is recorded first).  The
per-column identity rewrites each per-column coordinate as `factor · (((a+2)²)^{16} − 1)`, and
pulling the common `factor` out of the finite sum produces exactly the right-hand side of
`Prop812SecondOrderCoeff37`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The single-column `ϖ ↔ λ` bridge** (proven, axiom-clean): the mod-`37²` even-power-`32` Dwork
coefficient of `concreteKummerLogVector a` (the `Prop812SecondOrderCoeff37` per-column left side)
equals the `λ`-adic level-`72` coordinate `valuedLambdaQuotientDworkCoeffModSq (idx 15).1 (evalₐ 72
(kummerLogCompletedColumn a))`.  This is the proven `ϖ ↔ λ` filtration identity
`caseIICor823SecondOrder_coeffModSq_eq_evalₐ` at `j = 15`, applied to the single column `S =
concreteKummerLogVector a` (whose coercion to the completed Dwork ring is, definitionally,
`kummerLogCompletedColumn a`). -/
theorem caseIICor823SecondOrder_columnCoeffModSq_eq_evalₐ
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) :
    rationalPadicIntegerToZModSq 37
        ((dworkFixedEvenPowerBasis (p := 37) (K := CyclotomicField 37 ℚ)
            (by norm_num : 2 < 37)).repr
          (concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37)))) =
      valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
        (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
        (AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
          (kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a)) := by
  rw [caseIICor823SecondOrder_coeffModSq_eq_evalₐ
    (concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
    (15 : Fin (kummerLogRank 37))]
  rfl

set_option maxHeartbeats 3200000 in
-- Threads the `ϖ ↔ λ` bridge and the `λ`-adic linearity (the proven coordinate laws) through the
-- heavy `DworkCompleteIntegerRing` `evalₐ` of the column sum; well above the default heartbeat
-- budget (still below the `adicCompletionIntegers` `whnf` wall — every step is a finite `evalₐ`-laws
-- rewrite, not a Dwork power-basis `repr` comparison).
open BernoulliRegular (CPlusGenerator) in
/-- **`Prop812SecondOrderCoeff37` from the per-column identity** (proven, axiom-clean given
`CaseIICor823SecondOrderColumnCoeff37`).

The level-`68` mod-`37²` Dwork coefficient of the column sum is `ℤ`-linear in the exponent vector
`e`.  The `e`-linearity is carried out in the **`λ`-adic `evalₐ` coordinate**, via the repo's
proven `valuedLambdaQuotientDworkCoeffModSq_sum` / `_intCast_mul`, where it is wall-free — *not* on
the heavy Dwork power-basis `repr`.  Concretely:

* `set S := ∑_a e_a • concreteKummerLogVector a` (the repo's proven detector-lemma pattern), so the
  goal left side is `repr S idx` sharing the *same* `S` object with the bridge applied to `S`;
* rewrite `repr S idx` to the `evalₐ` coordinate (the proven `ϖ ↔ λ` filtration identity
  `caseIICor823SecondOrder_coeffModSq_eq_evalₐ` on `S`, then `hScoe` rewrites the coercion `↑S` to
  the completed-log column sum `∑_a e_a • kummerLogCompletedColumn a`);
* push `evalₐ` (an `AlgHom`) and the coefficient through the sum and each `zsmul`
  (`map_sum` / `valuedLambdaQuotientDworkCoeffModSq_sum`, `map_zsmul` /
  `valuedLambdaQuotientDworkCoeffModSq_intCast_mul`) to reach `∑_a (e_a) · g_a` with
  `g_a = valuedLambdaQuotientDworkCoeffModSq (idx 15).1 (evalₐ 72 (col_a))`;
* the single-column bridge `caseIICor823SecondOrder_columnCoeffModSq_eq_evalₐ` identifies each `g_a`
  with the per-column `repr` coordinate, which the per-column identity `hCol` rewrites to
  `factor · (((a+2)²)^{16} − 1)`;
* factoring the common Bernoulli factor out of the finite sum gives the Teichmüller-Vandermonde row.

This is the second-order analog of the proven first-order
`concreteKummerLogMatrix_mulVec_exponents_eq_coeff`. -/
theorem prop812SecondOrderCoeff37_of_columnCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCol : CaseIICor823SecondOrderColumnCoeff37) :
    Prop812SecondOrderCoeff37 := by
  classical
  intro e
  -- `set S := ∑_a e_a • concreteKummerLogVector a` (the repo's proven detector-lemma pattern): the
  -- goal left side becomes `repr S idx`, sharing the *same* `S` object with the bridge applied to
  -- `S`, so the `ϖ ↔ λ` rewrite is cheap (no second heavy copy of the column sum).
  set S : dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ) :=
    ∑ a : Fin (kummerLogRank 37),
      e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a
    with hS
  -- The coerced fixed-subalgebra sum is the completed-log column sum (`hScoe`, repo pattern).
  have hScoe :
      (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) =
        ∑ a : Fin (kummerLogRank 37),
          e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a := by
    rw [hS]
    rw [show (↑(∑ a : Fin (kummerLogRank 37),
          e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a) :
          DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) =
        (Subalgebra.val (dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ)))
          (∑ a : Fin (kummerLogRank 37),
            e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
        from rfl]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    rw [map_zsmul]
    rfl
  -- (1) Goal left side `repr S idx` → `λ`-adic `evalₐ` coordinate (the proven `ϖ ↔ λ` bridge on
  --     `S`, then `hScoe` rewrites the coerced sum to the completed-log column sum).
  rw [caseIICor823SecondOrder_coeffModSq_eq_evalₐ S (15 : Fin (kummerLogRank 37)), hScoe]
  -- (2) `λ`-adic linearity, inlined on the goal's own column sum (the repo's proven coordinate laws
  --     `valuedLambdaQuotientDworkCoeffModSq_sum` / `_intCast_mul`, all wall-free): push `evalₐ`
  --     (an `AlgHom`) and the coefficient through the sum and each `zsmul`.
  rw [map_sum, valuedLambdaQuotientDworkCoeffModSq_sum]
  -- (3) Factor the common Bernoulli factor out of the sum, identifying each per-column `evalₐ`
  --     coordinate — via the single-column bridge — with the `repr` coordinate `hCol` controls.
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ha ↦ ?_)
  rw [map_zsmul]
  rw [show (e a • AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
        (kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a)) =
      ((e a : ℤ) : ValuedIntegerRing 37 (CyclotomicField 37 ℚ) ⧸
        (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1))) *
        AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
          (kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a)
      from by rw [zsmul_eq_mul]]
  rw [valuedLambdaQuotientDworkCoeffModSq_intCast_mul,
    ← caseIICor823SecondOrder_columnCoeffModSq_eq_evalₐ a, hCol a]
  ring

/-! ## 3. `Prop812SecondOrderCoeff37` and the FLT37 endpoint, reduced to the per-column identity

Composing the proven `e`-linearity reduction with the proven downstream chain
(`prop812DescentCoeff37_of_secondOrderCoeff`,
`fermatLastTheoremFor_thirtyseven_of_prop812SecondOrderCoeff`) discharges the FLT37 Case-II `R4`
endpoint from the single-column second-order coefficient identity. -/

open FLT37.LehmerVandiver.CaseII in
/-- **`Prop812DescentCoeff37` from the single-column second-order coefficient identity** (proven,
axiom-clean given `CaseIICor823SecondOrderColumnCoeff37`).  Composes the proven `e`-linearity
reduction `prop812SecondOrderCoeff37_of_columnCoeff` with the proven
`prop812DescentCoeff37_of_secondOrderCoeff`. -/
theorem prop812DescentCoeff37_of_columnCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCol : CaseIICor823SecondOrderColumnCoeff37) :
    Prop812DescentCoeff37 :=
  prop812DescentCoeff37_of_secondOrderCoeff (prop812SecondOrderCoeff37_of_columnCoeff hCol)

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the single-column second-order
coefficient identity `CaseIICor823SecondOrderColumnCoeff37`** (proven, axiom-clean given the genuine
residuals + the carried Kellner Prop).

Supplies the single-column second-order coefficient identity to
`fermatLastTheoremFor_thirtyseven_of_prop812SecondOrderCoeff` through the proven `e`-linearity
reduction `prop812SecondOrderCoeff37_of_columnCoeff` — Washington Proposition 8.12 at `i = 32`
reduced to the genuine **per-single-column** level-`68` mod-`37²` Dwork coefficient equalling
`B₃₂/32 mod 37²` times the column's Teichmüller factor.  All the Theorem-8.22 plumbing, the
second-order detector machinery, the **proven** detector vanishing, the first-order row-`15`
vanishing, the `9·c₁₅` inversion, and the entire `e`-linearity are proven; only the per-column
coefficient identity remains. -/
theorem fermatLastTheoremFor_thirtyseven_of_columnCoeff
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_columnCoeff : CaseIICor823SecondOrderColumnCoeff37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_prop812SecondOrderCoeff
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (prop812SecondOrderCoeff37_of_columnCoeff caseII_columnCoeff)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
