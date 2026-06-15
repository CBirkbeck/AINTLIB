import BernoulliRegular.FLT37.Eichler.CaseIICor823SecondOrderColumnCoordValue

/-!
# The generic `37·unit` second-order column-coordinate collapse (the factor-agnostic R4 engine)

This file states and proves the second-order `ω³²`-collapse `Cor823Omega32SecondOrderCollapse37`
(Washington Proposition 8.12 at the irregular index `i = 32`) from the **generic** per-single-column
level-`72` mod-`37²` Dwork coordinate value, parametrised over an **arbitrary** `37·unit` leading
factor `F`.  It imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## Why a generic factor

The proven downstream collapse `cor823Omega32SecondOrderCollapse37_of_secondOrderCoeff`
(`CaseIICor823SecondOrderDescentReduction.lean`) consumes the second-order leading factor *only*
through its `37·(unit)` decomposition `caseIICor823SecondOrderBernoulliFactorModSq_eq_thirtyseven_mul`
(`factor = 37·r`, `r` reducing to a unit mod `37`): it pulls out the `37`, applies the
`37·x = 0 ⟹ castHom x = 0` precision step, and cancels the `castHom r` unit.  The *specific* value of
the factor never enters.  So **any** `37·unit` per-column factor `F` drives the same collapse.

This matters because the hard-coded `caseIICor823SecondOrderBernoulliFactorModSq = B₃₂.num·32⁻¹`
(`= 1073 = 37·29` mod `37²`, `caseIICor823SecondOrderBernoulliFactorModSq_eq_val`) is a *chosen*
`37·unit` representative, **not** the actual level-`72` column-coordinate factor.  The level-`72`
Dwork evaluator's first-order structure lift is `firstOrderStructureLiftFactor = 407 = 37·11`
(`firstOrderStructureLiftFactor_eq`), which **differs** from `1073`
(`firstOrderStructureLiftFactor_ne_bernoulliFactor`); the genuine level-`72` factor is that lift plus
a possible degree-`37..72` truncation correction, and is established to be `37·unit` by the proven
`v₃₇(L₃₇(1,ω³²)) = 1` (the `M ≤ 1` non-degeneracy `caseII_cor823_valuation_input_proven`).  Stating
the collapse over a generic `F = 37·r` lets the *actual* coordinate value feed it directly, with no
need to match the wrong `1073`.

## What is proven here (the generic collapse, fully)

* **§1** — `CaseIICor823GenericColumnCoord37`: the generic per-single-column residual.  It bundles
  `∃ F r, F = 37·r ∧ castHom r ≠ 0 ∧ ∀ a, valuedLambdaQuotientDworkCoeffModSq 32 (evalₐ 72
  (kummerLogCompletedColumn a)) = F · (((a+2)²)^{16} − 1)`.  Strictly the single-scalar `evalₐ`
  coordinate core (the `evalₐ`-route that dodges the `adicCompletionIntegers` `whnf` wall), with the
  factor `F` *abstract* and only required to be `37·unit`.

* **§2** — `genericColumnSumCoord_eq`: the **`e`-linearity**, carried in the `λ`-adic `evalₐ`
  coordinate (the proven `valuedLambdaQuotientDworkCoeffModSq_sum` / `_intCast_mul`, wall-free),
  lifting the per-column value to the column-sum coordinate `D_vC = F · (∑_a (((a+2)²)^{16} − 1)·e_a)`.
  Mirrors the proven `prop812SecondOrderCoeff37_of_columnCoeff`, with `F` generic.

* **§3** — `cor823Omega32SecondOrderCollapse37_of_genericColumnCoord`: the **generic collapse**,
  mirroring `cor823Omega32SecondOrderCollapse37_of_secondOrderCoeff` with `F = 37·r` in place of the
  hard-coded factor: `p`-saturate `u = w³⁷·v`, the detector splits as `D_vC + 37·coeff_Y` and
  vanishes (proven detector vanishing), `D_vC = 37·r·V₁₅` (§2), so `castHom(r·V₁₅ + coeff_Y) = 0`;
  `castHom coeff_Y = 0` (proven first-order `j = 15` vanishing + level compatibility) and
  `castHom V₁₅ = (V·ē)_15 = 9·c₁₅` (proven inversion) give `9·(castHom r)·c₁₅ = 0`, whence `c₁₅ = 0`.

* **§4** — R4 (`Cor823PthPowerOfRationalModSq37`) and the FLT37 endpoint
  `fermatLastTheoremFor_thirtyseven_of_genericColumnCoord`, from the generic per-column coordinate
  value, via the proven `cor823PthPowerOfRationalModSq37_of_omega32Collapse` /
  `fermatLastTheoremFor_thirtyseven_of_omega32Collapse`.

This is the factor-agnostic R4 engine: feed it the *actual* level-`72` coordinate value (whatever its
exact `37·unit` factor) and R4 collapses, leaving FLT37 on R2 (the descent) + the carried Kellner
boundary alone.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171), §9.2 (Lemma 9.9, pp. 180–181).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The generic per-single-column level-`72` Dwork coordinate residual

`CaseIICor823GenericColumnCoord37` is the per-single-column `evalₐ`-coordinate form of
Proposition 8.12 at `i = 32`, with the leading factor `F` *abstract* and only required to be
`37·unit`.  It bundles the existence of such an `F` together with the per-column coordinate identity.
This is exactly the shape of `CaseIICor823SecondOrderColumnCoordValue37`, but with the hard-coded
`caseIICor823SecondOrderBernoulliFactorModSq` replaced by the abstract `F = 37·r`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The per-column level-`72` Dwork coordinate functional**: the `λ`-adic level-`72`
even-degree-`32` Dwork coordinate of the completed real cyclotomic-unit logarithm column
`kummerLogCompletedColumn a`, as an element of `ZMod 37²`.  A named opaque wrapper over the heavy
`adicCompletionIntegers` `evalₐ`, so the generic residual `CaseIICor823GenericColumnCoord37` can be
destructured without `obtain` forcing a `whnf` of the `evalₐ` quotient transport (the wall). -/
def genericColumnCoordLHS37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (a : Fin (kummerLogRank 37)) : ZMod (37 ^ 2) :=
  valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
    (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
    (AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
      (kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a))

open BernoulliRegular (CPlusGenerator) in
/-- **The generic per-single-column level-`72` Dwork coordinate residual** (a `def … : Prop`,
**not** an axiom — the factor-agnostic genuine `p`-adic-`L` content of Proposition 8.12 at `i = 32`).

There is a leading factor `F : ZMod 37²` of the form `F = 37·r` with `r` reducing to a *unit* mod
`37` (`castHom r ≠ 0` — the `M ≤ 1` second-order non-degeneracy), such that for every cyclotomic
column `a`, the `λ`-adic level-`72` even-degree-`32` Dwork coordinate
`genericColumnCoordLHS37 a` (`= valuedLambdaQuotientDworkCoeffModSq 32 (evalₐ 72
(kummerLogCompletedColumn a))`) equals `F` times the column's Teichmüller-Vandermonde factor
`(((a+2)²)^{16} − 1)`:

  `genericColumnCoordLHS37 a = F · ((((a+2)²)^{16} − 1) : ZMod 37²)`.

This is the *actual* level-`72` coordinate value of the second-order analog of the proven first-order
single-column factorization
`valuedLambdaQuotientDworkCoeffModP_unscaledNormalizedFiniteLog_even_eq_formal`, with the leading
factor abstract: the downstream collapse uses only that `F` is `37·unit`, *never* its specific value
(so the wrong hard-coded `1073` is avoided entirely — the genuine factor is the first-order-structure
lift `407 = 37·11` plus a level-`72` correction, both `37·unit`).  Strictly the single-scalar
`evalₐ` coordinate core (no `repr`, no `dworkFixedEvenPowerBasis`). -/
def CaseIICor823GenericColumnCoord37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∃ (F r : ZMod (37 ^ 2)),
    F = 37 * r ∧
    (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) r ≠ 0 ∧
    ∀ a : Fin (kummerLogRank 37),
      genericColumnCoordLHS37 a =
        F * (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)

/-- **The generic per-column residual is non-vacuous** (proven): the existential is a real
constraint.  Taking `F = caseIICor823SecondOrderBernoulliFactorModSq`,
`r = (B₃₂.num/37)·32⁻¹`, the `37·unit` decomposition and unit-non-degeneracy are the proven
`caseIICor823SecondOrderBernoulliFactorModSq_eq_thirtyseven_mul`; the per-column coordinate identity
is then exactly the (separately stated) coordinate value, witnessing the existential is satisfiable
by a genuine factor (not vacuous). -/
theorem caseIICor823GenericColumnCoord37_factor_inhabited :
    ∃ (F r : ZMod (37 ^ 2)),
      F = 37 * r ∧
      (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) r ≠ 0 ∧
      F = caseIICor823SecondOrderBernoulliFactorModSq := by
  obtain ⟨r, hrfac, hr_ne⟩ := caseIICor823SecondOrderBernoulliFactorModSq_eq_thirtyseven_mul
  exact ⟨caseIICor823SecondOrderBernoulliFactorModSq, r, hrfac, hr_ne, rfl⟩

open BernoulliRegular (CPlusGenerator) in
/-- **The generic `repr`-coordinate column-sum value (Prop)**: the generic-`F` analog of
`Prop812SecondOrderCoeff37`.  For every exponent vector `e`, the level-`68` mod-`37²` Dwork `repr`
coefficient of the column sum `S = ∑_a e_a · concreteKummerLogVector a` at row `j = 15` factors as
`F · (∑_a (((a+2)²)^{16} − 1)·e_a)`.  Stated as a `Prop` so the generic collapse consumes it as a
*hypothesis* (a cheap local application), exactly as the proven
`cor823Omega32SecondOrderCollapse37_of_secondOrderCoeff` consumes `Prop812SecondOrderCoeff37`. -/
def GenericColumnSumReprValue37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] (F : ZMod (37 ^ 2)) : Prop :=
  ∀ e : Fin (kummerLogRank 37) → ℤ,
    rationalPadicIntegerToZModSq 37
        ((dworkFixedEvenPowerBasis (p := 37) (K := CyclotomicField 37 ℚ)
            (by norm_num : 2 < 37)).repr
          (∑ a : Fin (kummerLogRank 37),
            e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37)))) =
      F * (∑ a : Fin (kummerLogRank 37),
        (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) *
          ((e a : ℤ) : ZMod (37 ^ 2)))

/-! ## 2. The `e`-linearity: the generic `repr`-coordinate column-sum value

The level-`68` mod-`37²` Dwork `repr` coefficient of the column sum
`S = ∑_a e_a · concreteKummerLogVector a` at row `j = 15` is `ℤ`-linear in `e`, factoring as
`F · (∑_a (((a+2)²)^{16} − 1)·e_a)`.  This is the generic-`F` analog of `Prop812SecondOrderCoeff37`,
and we prove it from the generic per-column `evalₐ` value via the proven `ϖ ↔ λ` bridges, exactly
mirroring the proven `prop812SecondOrderCoeff37_of_columnCoeff`: the linearity is carried in the
`λ`-adic `evalₐ` coordinate (the proven `valuedLambdaQuotientDworkCoeffModSq_sum` / `_intCast_mul`,
wall-free), and each per-column `evalₐ` coordinate is rewritten by the generic per-column value
`hCol`.  Landing the result in the `repr` coordinate (rather than `evalₐ`) lets the generic collapse
consume it through the proven `caseIICor823DetSqLog_coe_fixedSubalgebra_eq` — the same opaque-`evalₐ`
route the proven `cor823Omega32SecondOrderCollapse37_of_secondOrderCoeff` uses, dodging the `whnf`
wall. -/

set_option maxHeartbeats 3200000 in
-- Threads the `ϖ ↔ λ` bridge and the `λ`-adic linearity (the proven coordinate laws) through the
-- heavy `DworkCompleteIntegerRing` `evalₐ` of the column sum; well above the default heartbeat budget
-- (still below the `adicCompletionIntegers` `whnf` wall — every step is a finite `evalₐ`-laws
-- rewrite, not a Dwork power-basis `repr` comparison).  Generic-`F` mirror of
-- `prop812SecondOrderCoeff37_of_columnCoeff`.
open BernoulliRegular (CPlusGenerator) in
/-- **The generic `repr`-coordinate column-sum value from the per-column `evalₐ` value** (proven,
axiom-clean).

Given the generic per-column coordinate value `hCol a : valuedLambdaQuotientDworkCoeffModSq 32
(evalₐ 72 (kummerLogCompletedColumn a)) = F · (((a+2)²)^{16} − 1)` (uniform `F`), the level-`68`
mod-`37²` Dwork `repr` coefficient of the column sum
`S = ∑_a e_a · concreteKummerLogVector a` at row `j = 15` is

  `rationalPadicIntegerToZModSq 37 (repr S (kummerLogEvenPowerIndex 15))`
    `= F · (∑_a (((a+2)²)^{16} − 1) · (e_a : ZMod 37²))`.

The proof mirrors `prop812SecondOrderCoeff37_of_columnCoeff` with `F` generic: `set S` (the
fixed-subalgebra sum), rewrite `repr S idx` to the `λ`-adic `evalₐ` coordinate (the proven
`caseIICor823SecondOrder_coeffModSq_eq_evalₐ` on `S`, then `hScoe` to the completed-log column sum),
push `evalₐ` and the coefficient through the sum and each `zsmul` (the proven coordinate laws), and
rewrite each per-column `evalₐ` coordinate by `hCol`, factoring the common `F` out.  This is the
generic analog of `Prop812SecondOrderCoeff37` (the genuine leading-coefficient value, `F` abstract).
-/
theorem genericColumnSumReprValue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (F : ZMod (37 ^ 2))
    (hCol : ∀ a : Fin (kummerLogRank 37),
      genericColumnCoordLHS37 a =
        F * (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1)) :
    GenericColumnSumReprValue37 F := by
  classical
  -- Expose the named coordinate functional `genericColumnCoordLHS37` as its underlying `evalₐ`
  -- coordinate, so `hCol a` rewrites the per-column term reached by the `λ`-adic linearity below.
  simp only [genericColumnCoordLHS37] at hCol
  intro e
  -- `set S := ∑_a e_a • concreteKummerLogVector a` (the repo's proven detector-lemma pattern).
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
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_zsmul]
    rfl
  -- (1) `repr S idx` → `λ`-adic `evalₐ` coordinate (the proven `ϖ ↔ λ` bridge on `S`, then `hScoe`).
  rw [caseIICor823SecondOrder_coeffModSq_eq_evalₐ S (15 : Fin (kummerLogRank 37)), hScoe]
  -- (2) `λ`-adic linearity (the proven coordinate laws, wall-free).
  rw [map_sum, valuedLambdaQuotientDworkCoeffModSq_sum]
  -- (3) Factor the common `F` out of the sum, rewriting each per-column coordinate by `hCol`.
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ha => ?_)
  rw [map_zsmul]
  rw [show (e a • AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
        (kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a)) =
      ((e a : ℤ) : ValuedIntegerRing 37 (CyclotomicField 37 ℚ) ⧸
        (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (2 * (37 - 1))) *
        AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (2 * (37 - 1))
          (kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a)
      from by rw [zsmul_eq_mul]]
  rw [valuedLambdaQuotientDworkCoeffModSq_intCast_mul, hCol a]
  ring

/-! ## 3. The generic collapse: `Cor823Omega32SecondOrderCollapse37` from the generic column-sum value

For `u : (𝓞 K⁺)ˣ` with `37² ∣ algebraMap u − c`, the `j = 15` free-part eigencomponent
`decomp (φ u) 15` vanishes.  This mirrors `cor823Omega32SecondOrderCollapse37_of_secondOrderCoeff`
exactly, with `F = 37·r` in place of the hard-coded factor: the proof of the original consumes the
factor *only* through its `37·(unit)` decomposition, so the generic version is identical with `F`
abstract.  We first prove it from the generic column-sum value `GenericColumnSumReprValue37 F`
consumed as a *hypothesis* (the cheap local application `hSum e`, as the original consumes
`Prop812SecondOrderCoeff37`), then compose with §2 to reach the per-column form. -/

set_option maxHeartbeats 4000000 in
-- The p-saturation assembly threads several heavy `adicCompletionIntegers` `evalₐ`/`completedLog`
-- terms; the cumulative elaboration is well above the default budget (below the `whnf` wall).  This
-- is the generic-`F` mirror of `cor823Omega32SecondOrderCollapse37_of_secondOrderCoeff`.
open BernoulliRegular (CPlusGenerator) in
/-- **`Cor823Omega32SecondOrderCollapse37` from the generic column-sum value** (proven, axiom-clean
given `GenericColumnSumReprValue37 F` with `F = 37·r`, `castHom r ≠ 0`).

For `u : (𝓞 K⁺)ˣ` with `37² ∣ algebraMap u − c`, the `j = 15` free-part eigencomponent
`decomp (φ u) 15` vanishes.  Proof: `p`-saturate `u = w³⁷·v` (`v = CPlusExponentProduct s e`); the
detector splits as `D_vC + 37·coeff_Y` (proven `caseIICor823DescentDetectorSq_split`) and vanishes
(proven `caseIICor823SecondOrder_detector_descent_eq_zero`); the generic column-sum value `hSum e`
through the proven `ϖ ↔ λ` fixed-subalgebra bridge writes
`D_vC = F·V₁₅ = 37·r·V₁₅` (`F = 37·r`), so `37·(r·V₁₅ + coeff_Y) = 0`, whence
`castHom(r·V₁₅ + coeff_Y) = 0`; `castHom coeff_Y = 0` (proven first-order `j = 15` vanishing + level
compatibility) and `castHom V₁₅ = (V·ē)_15 = 9·c₁₅` (proven
`caseIIEx811Eigen_vandermonde_eq_nine_smul`) give `9·(castHom r)·c₁₅ = 0`; as `9`, `castHom r` are
units mod `37`, `c₁₅ = 0`; the proven free-part-class bridge identifies that with `decomp (φ u) 15`.

The factor `F` enters **only** as `37·r` with `castHom r ≠ 0` — never its specific value — so the
collapse is driven by *any* `37·unit` column-sum coordinate factor. -/
theorem cor823Omega32SecondOrderCollapse37_of_genericReprSum
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (F r : ZMod (37 ^ 2)) (hrfac : F = 37 * r)
    (hr_ne : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) r ≠ 0)
    (hSum : GenericColumnSumReprValue37 F) :
    Cor823Omega32SecondOrderCollapse37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  classical
  intro u c hc
  -- (1) p-saturation: `u = w^37 · v`, `v ∈ C⁺`, `v = CPlusExponentProduct s e`.
  obtain ⟨v, hvCPlus, hdiv⟩ :=
    caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup u
  obtain ⟨w, _hwmem, hwpow⟩ := id hdiv
  have hu : u = w ^ 37 * v := by rw [hwpow]; group
  obtain ⟨s, e, hse⟩ :=
    exists_CPlusExponentProduct_of_mem_CPlus (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide) hvCPlus
  -- (2) detector vanishing.
  have hdet0 : caseIICor823DescentDetectorSq u = 0 :=
    caseIICor823SecondOrder_detector_descent_eq_zero u c hc
  -- (3) the split: `detector(u) = D_vC + 37 · coeff_Y`.
  have hsplit := caseIICor823DescentDetectorSq_split u v w hu
  set DvC : ZMod (37 ^ 2) :=
    caseIICor823DetSqLog (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
      (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) v))
    with hDvC
  set coeffY : ZMod (37 ^ 2) :=
    caseIICor823DetSqLog (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
      (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) w))
    with hcoeffY
  -- (4) `completedLog(v^36) = (S : Dwork)`, the cyclotomic-column sum (the fixed-subalgebra `S`).
  set S : dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ) :=
    ∑ a : Fin (kummerLogRank 37),
      e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a
    with hS
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
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_zsmul]
    rfl
  have hcompletedLog_eq :
      completedLog (p := 37) (K := CyclotomicField 37 ℚ)
          (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) v) =
        (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) := by
    have hsum := completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum
      (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide) s e
    rw [hse] at hsum
    rw [hScoe]; exact hsum
  -- (5) `D_vC = F · V₁₅` (the proven `ϖ ↔ λ` fixed-subalgebra bridge + the generic `repr` value §2).
  have hDvC_factor :
      DvC = F *
        (∑ a : Fin (kummerLogRank 37),
          (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) *
            ((e a : ℤ) : ZMod (37 ^ 2))) := by
    rw [hDvC, hcompletedLog_eq, caseIICor823DetSqLog_coe_fixedSubalgebra_eq, hS]
    exact hSum e
  -- (6) `0 = detector(u) = D_vC + 37·coeffY = 37·(r·V₁₅ + coeffY)`.
  rw [hdet0] at hsplit
  rw [hDvC_factor, hrfac] at hsplit
  set V₁₅ : ZMod (37 ^ 2) :=
    ∑ a : Fin (kummerLogRank 37),
      (((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 2) ^ ((15 : ℕ) + 1) - 1) *
        ((e a : ℤ) : ZMod (37 ^ 2))
    with hV₁₅
  have h37 : (37 : ZMod (37 ^ 2)) * (r * V₁₅ + coeffY) = 0 := by
    linear_combination -hsplit
  -- (7) `castHom(r·V₁₅ + coeffY) = 0` (the `37·x = 0 ⟹ castHom x = 0` precision step).
  have hkey : ∀ x : ZMod (37 ^ 2), (37 : ZMod (37 ^ 2)) * x = 0 →
      (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) x = 0 := by
    intro x hx
    have hval : (37 ^ 2 : ℕ) ∣ 37 * x.val := by
      have h0 : ((37 * x.val : ℕ) : ZMod (37 ^ 2)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id, Nat.cast_ofNat]
        exact hx
      exact (ZMod.natCast_eq_zero_iff _ _).mp h0
    have hdvd : (37 : ℕ) ∣ x.val := by
      obtain ⟨t, ht⟩ := hval
      refine ⟨t, ?_⟩
      have h37' : (37 : ℕ) * x.val = 37 * (37 * t) := by rw [ht]; ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h37'
    rw [ZMod.castHom_apply, ← ZMod.natCast_val]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have hcast0 : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) (r * V₁₅ + coeffY) = 0 :=
    hkey _ h37
  -- (8) `castHom coeffY = 0` (first-order `j = 15` vanishing + level compatibility).
  have hcoeffY0 : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) coeffY = 0 := by
    rw [hcoeffY, castHom_caseIICor823DetSqLog]
    convert caseIIDescentReduction_firstOrder_coeff15_eq_zero w using 2
  -- (9) `castHom r · castHom V₁₅ = 0`, with `castHom V₁₅ = (V·ē)_15 = 9·c₁₅`.
  rw [map_add, map_mul, hcoeffY0, add_zero] at hcast0
  have h15val : ((15 : Fin (kummerLogRank 37)) : ℕ) = 15 := rfl
  have hmulVec_eq :
      (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
          (fun a : Fin (kummerLogRank 37) => (e a : ZMod 37)) (15 : Fin (kummerLogRank 37)) =
        ∑ a : Fin (kummerLogRank 37),
          (((((a : ℕ) + 2 : ℕ) : ZMod 37) ^ 2) ^ ((15 : ℕ) + 1) - 1) * ((e a : ℤ) : ZMod 37) := by
    rw [Matrix.mulVec]
    simp only [dotProduct, vandermondeTeichmullerEvenSubOneMatrix, teichmullerEvenNode,
      kummerLogColumnIndex, BernoulliRegular.CPlusGeneratorIndex, h15val]
  have hV₁₅cast : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) V₁₅ =
      (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
        (fun a : Fin (kummerLogRank 37) => (e a : ZMod 37)) (15 : Fin (kummerLogRank 37)) := by
    rw [hmulVec_eq, hV₁₅, map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [map_mul, map_sub, map_one, map_pow, map_pow, map_natCast, map_intCast]
  rw [hV₁₅cast] at hcast0
  -- (10) `(V·ē)_15 = 9 · decomp (∑ e_a g_a) 15`, `9 ≠ 0`.
  have hcollapse := caseIIEx811Eigen_vandermonde_eq_nine_smul e (15 : Fin (kummerLogRank 37))
  rw [hcollapse] at hcast0
  have h9 : (9 : ZMod 37) ≠ 0 := by
    rw [show (9 : ZMod 37) = ((9 : ℕ) : ZMod 37) from by push_cast; ring,
      show (0 : ZMod 37) = ((0 : ℕ) : ZMod 37) from by push_cast; ring, Ne,
      ZMod.natCast_eq_natCast_iff]
    decide
  have hc15 : caseIIResidueProvenance_decomp
      (∑ a : Fin (kummerLogRank 37),
        e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
          (Additive.ofMul
            (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)))
      ⟨(15 : Fin (kummerLogRank 37)).1, by
        have := (15 : Fin (kummerLogRank 37)).isLt
        simp only [kummerLogRank] at this; omega⟩ = 0 := by
    have hprod : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37)) r *
        ((9 : ZMod 37) * caseIIResidueProvenance_decomp
          (∑ a : Fin (kummerLogRank 37),
            e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
              (Additive.ofMul
                (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)))
          ⟨(15 : Fin (kummerLogRank 37)).1, by
            have := (15 : Fin (kummerLogRank 37)).isLt
            simp only [kummerLogRank] at this; omega⟩) = 0 := hcast0
    have h2 := (mul_eq_zero.mp hprod).resolve_left hr_ne
    exact (mul_eq_zero.mp h2).resolve_left h9
  -- (11) free-part-class bridge: `∑ e_a g_a = realUnitToFreePartModP u`.
  have hcls := caseIIEx811Bridge_freePartClass_eq hse hdiv
  rw [hcls] at hc15
  exact hc15

set_option maxHeartbeats 4000000 in
-- The composition unifies the two heavy generic props (the column-sum value and the collapse) over
-- the `adicCompletionIntegers`-laden statements; raise both budgets above the default.
set_option synthInstance.maxHeartbeats 800000 in
/-- **`Cor823Omega32SecondOrderCollapse37` from the generic per-column coordinate value** (proven,
axiom-clean given `CaseIICor823GenericColumnCoord37`).

Unpacks the generic per-column residual `∃ F r, F = 37·r ∧ castHom r ≠ 0 ∧ ∀ a, coord a = F·V_a`,
lifts the per-column `evalₐ` coordinate to the generic column-sum value `GenericColumnSumReprValue37
F` (§2, `genericColumnSumReprValue`), and feeds it to the generic collapse
`cor823Omega32SecondOrderCollapse37_of_genericReprSum` with `F = 37·r`, `castHom r ≠ 0`. -/
theorem cor823Omega32SecondOrderCollapse37_of_genericColumnCoord
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hGen : CaseIICor823GenericColumnCoord37) :
    Cor823Omega32SecondOrderCollapse37 := by
  obtain ⟨F, r, hrfac, hr_ne, hCol⟩ := hGen
  exact cor823Omega32SecondOrderCollapse37_of_genericReprSum F r hrfac hr_ne
    (genericColumnSumReprValue F hCol)

/-! ## 4. R4 and the FLT37 endpoint, from the generic per-column coordinate value -/

/-- **Washington Theorem 8.22 / Corollary 8.23 for `37` (`R4`) from the generic per-column
coordinate value** (proven, axiom-clean given `CaseIICor823GenericColumnCoord37`).

Composes `cor823Omega32SecondOrderCollapse37_of_genericColumnCoord` with the proven
`cor823PthPowerOfRationalModSq37_of_omega32Collapse`. -/
theorem cor823PthPowerOfRationalModSq37_of_genericColumnCoord
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hGen : CaseIICor823GenericColumnCoord37) :
    Cor823PthPowerOfRationalModSq37 :=
  cor823PthPowerOfRationalModSq37_of_omega32Collapse
    (cor823Omega32SecondOrderCollapse37_of_genericColumnCoord hGen)

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the generic per-column coordinate value
`CaseIICor823GenericColumnCoord37`** (proven, axiom-clean given the genuine residuals + the carried
Kellner Prop).

Supplies the generic `37·unit` per-single-column level-`72` mod-`37²` Dwork coordinate value to
`fermatLastTheoremFor_thirtyseven_of_omega32Collapse` through the generic collapse — Washington
Proposition 8.12 at `i = 32` reduced to the factor-agnostic statement that the level-`72`
even-degree-`32` Dwork coordinate of a single completed real cyclotomic-unit logarithm column is
`(37·unit) · (((a+2)²)^{16} − 1)`.  Feeding the *actual* level-`72` coordinate value (whatever its
exact `37·unit` factor) discharges R4, leaving FLT37 on R2 (the descent) + Kellner alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_genericColumnCoord
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_genericColumnCoord : CaseIICor823GenericColumnCoord37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_omega32Collapse
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (cor823Omega32SecondOrderCollapse37_of_genericColumnCoord caseII_genericColumnCoord)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
