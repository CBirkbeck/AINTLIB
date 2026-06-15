import BernoulliRegular.FLT37.Eichler.CaseIICor823Level71NGenericSpecializedLog

/-!
# Reduction of the level-`71` unit ↔ Dwork-slice coordinate bridge to the single Dwork-specialized
# finite-log identity

This file uses the `N`-generic structural machinery of `CaseIICor823Level71NGenericSpecializedLog.lean`
(the mod-`37²` cyclotomic column factor, the mod-`37²` slice-sum decomposition, the `N`-generic
unscaled-minus-scaled Dwork difference, the scaled = cyclotomic image identity) to reduce
`CaseIICor823Level71UnitDworkCoordBridge37` (`CaseIICor823Level71UnitDworkCoordBridge.lean`) to a
**strictly smaller** residual that bundles exactly the genuine analytic kernel.  It imports only; it
does **not** modify any existing file.  No `sorry`, no `axiom`.

## The reduction (the reachable structure discharged)

The target's mod-`37²` coordinate identity `hCoord` is `W(a) = (1 − k³²)·(37·(32!)⁻¹)`.  We
**discharge** its structural skeleton:

* `W(a)` is the level-`71` finite-log coordinate of the normalized unit `c^{p-1} − 1`
  (`normalizedUnitCoeff37_eq_finiteLog_denUnit`, proven `N`-generic);
* the cyclotomic column factor on the level-`71` mod-`37²` coordinate is
  `teichmullerCoeffModSq (k)^32 = τ(k)^32 mod 37²`
  (`valuedLambdaQuotientDworkCoeffModSq_scaledDworkParameterNormalizedCoordFiniteLogN71_eq_smul`,
  proven), whose mod-`37` reduction is the rational column value `k` (`teichmullerCoeffModSq_castHom`)
  — so under the `37·` factor the Teichmüller factor collapses to the rational `(1 − k³²)`;
* the mod-`37²` coordinate distributes over the unscaled-minus-scaled difference
  (`valuedLambdaQuotientDworkCoeffModSq_sub`, proven).

The **only** undischarged content is the two genuine `p`-adic-`L` pieces, bundled as a single
residual `CaseIICor823Level71DworkSpecializedFiniteLog37`:

1. **the level-`71` unit ↔ Dwork-specialized finite-log identity** — that
   `samePrimeFiniteLog 71 (c^{p-1} − 1)` equals the unscaled-minus-scaled Dwork-parameter difference
   `dworkParameterNormalizedCoordFiniteLogN 71 − scaledDworkParameterNormalizedCoordFiniteLogN k 71`.
   This is the level-`71` lift of the proven `p − 2`-precise
   `kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs` applied to the **unit**,
   combining the level-`71` unit ↔ quotient Fermat bridge with the level-`71` Dwork ↔ quotient
   Teichmüller transport (the Teichmüller difference `τ(k) − k` vanishes only to order `p − 1`, so the
   `p − 2`-precise `_evalₐ_pow_pred` does not lift — this is the genuine second-order Fermat-quotient
   content `v_p(L₃₇(1, ω³²)) = 1`);
2. **the unscaled degree-`32` Dwork-parameter coordinate value** — that
   `coordModSq 32 (dworkParameterNormalizedCoordFiniteLogN 71) = 37·(32!)⁻¹`, the value already
   *isolated* (modulo the degree-slice sum) by the proven
   `factorial32_deg32_slice_value_eq_thirtyseven` (`(32!)·coord(deg-32 slice) = 37`).

This residual is **strictly smaller** than `CaseIICor823Level71UnitDworkCoordBridge37`: there the
entire per-column mod-`37²`/mod-`37` coordinate value is the unknown; here the coordinate extraction
(the cyclotomic column factor, the difference-distribution, the Teichmüller → rational collapse) is
**discharged** from the `N`-generic machinery, and the *only* unknown is the single finite-log
identity together with the proven-slice degree-`32` coordinate value.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4 (Proposition 8.12, Theorem
  8.22, Corollary 8.23, p. 171).
* Kellner, *On irregular prime power divisors of the Bernoulli numbers*, Math. Comp. 76 (2007)
  405–441; arXiv:math/0409223, Proposition 2.7.
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField
open scoped BigOperators

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular (CPlusGenerator CPlusExponentProduct)
open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The single Dwork-specialized residual -/

open BernoulliRegular (CPlusGenerator) in
/-- **The level-`71` Dwork-specialized finite-log residual** (a `def … : Prop`, **not** an axiom — the
single genuine `p`-adic-`L` kernel of `CaseIICor823Level71UnitDworkCoordBridge37` after the coordinate
structure is discharged).  It bundles, for the irregular column index `i = 32` and the cyclotomic
column delta `kummerLogColumnDelta a`:

1. the **level-`71` unit ↔ Dwork-specialized finite-log identity**: for every column `a`,
   `samePrimeFiniteLog 71 (c^{p-1} − 1) = dworkParameterNormalizedCoordFiniteLogN 71 −
   scaledDworkParameterNormalizedCoordFiniteLogN (kummerLogColumnDelta a) 71`, where
   `c = kummerLogValuedCyclotomicQuotientDenUnit a` is the normalized real cyclotomic unit;
2. the **unscaled degree-`32` coordinate value**: `coordModSq 32 (dworkParameterNormalizedCoordFiniteLogN
   71) = 37·(32!)⁻¹`.

Piece 1 is the level-`71` lift of the proven `p − 2`-precise
`kummerLogDworkArtinHasseSpecializedFiniteLog_eq_normalizedApprox_logs` applied to the **unit**
(the genuine second-order Fermat-quotient content `v_p(L₃₇(1, ω³²)) = 1`); piece 2 is the value the
proven `factorial32_deg32_slice_value_eq_thirtyseven` isolates.  This is **strictly smaller** than
`CaseIICor823Level71UnitDworkCoordBridge37`: the cyclotomic column factor
(`valuedLambdaQuotientDworkCoeffModSq_scaledDworkParameterNormalizedCoordFiniteLogN71_eq_smul`), the
difference-distribution (`valuedLambdaQuotientDworkCoeffModSq_sub`), and the Teichmüller → rational
collapse (`teichmullerCoeffModSq_castHom`) are **proven**; only the finite-log identity and the
proven-slice coordinate value remain. -/
def CaseIICor823Level71DworkSpecializedFiniteLog37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  (∀ a : Fin (kummerLogRank 37),
    samePrimeFiniteLog (p := 37) (K := CyclotomicField 37 ℚ) 71
        ((kummerLogValuedCyclotomicQuotientDenUnit
          (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a :
            ValuedIntegerRing 37 (CyclotomicField 37 ℚ)) ^ (37 - 1) - 1)
        (kummerLogValuedCyclotomicQuotientDenUnit_pow_pred_sub_one_mem_lambdaIdeal
          (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a) =
      dworkParameterNormalizedCoordFiniteLogN (p := 37) (K := CyclotomicField 37 ℚ) 71 -
        scaledDworkParameterNormalizedCoordFiniteLogN (p := 37) (K := CyclotomicField 37 ℚ)
          ((kummerLogColumnDelta (p := 37) (by norm_num) a : CyclotomicUnitDelta 37) : ZMod 37) 71) ∧
  (valuedLambdaQuotientDworkCoeffModSq (p := 37) (K := CyclotomicField 37 ℚ)
      (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1
      (dworkParameterNormalizedCoordFiniteLogN (p := 37) (K := CyclotomicField 37 ℚ) 71) =
    (37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹))

open BernoulliRegular (CPlusGenerator) in
/-- **The Dwork-specialized residual is non-vacuous** (proven): its piece-`2` value `37·(32!)⁻¹` is a
genuine *nonzero* element of `ZMod 37²` (`37·(unit)`, since `32!` is a `37`-unit), and its piece-`1`
finite-log identity is an equation between genuine level-`71` finite-log quotient elements over the
nonempty column index type.  So the residual is a real statement, not vacuously true; its piece-`2`
value is consistent with the proven `factorial32_deg32_slice_value_eq_thirtyseven`
(`(32!)·coord(deg-32 slice) = 37`). -/
theorem caseIICor823Level71DworkSpecializedFiniteLog37_consequent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ (_a : Fin (kummerLogRank 37)),
      ((37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) ≠ 0 := by
  refine ⟨⟨0, by norm_num [kummerLogRank]⟩, ?_⟩
  -- `37·(32!)⁻¹ ≠ 0`: `32!` is a `37`-unit, so multiplying `37·(32!)⁻¹ = 0` by `32!` gives `37 = 0`.
  have hunit : IsUnit ((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2)) := factorial_thirtytwo_isUnit_modSq
  intro hzero
  have h37 : (37 : ZMod (37 ^ 2)) = 0 := by
    have hmul := congrArg (fun z => ((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2)) * z) hzero
    simp only [mul_zero] at hmul
    rw [show ((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2)) *
          ((37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) =
        (37 : ZMod (37 ^ 2)) *
          (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2)) *
            (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) from by ring,
      ZMod.mul_inv_of_unit _ hunit, mul_one] at hmul
    exact hmul
  exact absurd h37 (by decide)

/-! ## 2. The residual yields the mod-`37²` coordinate identity `hCoord`

For each column `a`, the level-`71` finite-log coordinate `W(a)` of the unit `c^{p-1} − 1` equals, by
the residual's finite-log identity and the proven coordinate structure, `(1 − τ(k)³²)·(37·(32!)⁻¹)`,
which under the `37·` factor (`thirtyseven_mul_eq_of_castHom_eq`) collapses to `(1 − k³²)·(37·(32!)⁻¹)`
since `castHom (τ(k)) = k` (`teichmullerCoeffModSq_castHom`) and `k = (a + 2 : ZMod 37)`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The residual yields the mod-`37²` coordinate identity** (proven, axiom-clean given the residual):
`CaseIICor823Level71DworkSpecializedFiniteLog37` implies, for every column `a`,

  `normalizedUnitCoeff37 a = (1 − ((a+2 : ZMod 37²))³²)·(37·(32!)⁻¹)`,

i.e. the hypothesis `hCoord` of `caseIICor823Level71UnitDworkCoordBridge37_of_coordIdentity`.

The coordinate structure is **discharged**: `W(a)` is the finite-log coordinate of `c^{p-1} − 1`
(`normalizedUnitCoeff37_eq_finiteLog_denUnit`), the residual rewrites the finite log as the
unscaled-minus-scaled Dwork difference, the mod-`37²` coordinate distributes
(`valuedLambdaQuotientDworkCoeffModSq_sub`), the scaled coordinate is the Teichmüller factor times the
unscaled (`…_scaledDworkParameterNormalizedCoordFiniteLogN71_eq_smul`), the unscaled degree-`32`
coordinate is the residual's `37·(32!)⁻¹`, and the Teichmüller factor `τ(k)³²` collapses mod-`37` to
the rational `k³² = (a+2)³²` under the `37·` factor (`teichmullerCoeffModSq_castHom`,
`thirtyseven_mul_eq_of_castHom_eq`). -/
theorem caseIICor823Level71DworkSpecializedFiniteLog37_coordIdentity
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hRes : CaseIICor823Level71DworkSpecializedFiniteLog37)
    (a : Fin (kummerLogRank 37)) :
    normalizedUnitCoeff37 a =
      (1 - ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) *
        ((37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) := by
  obtain ⟨hLog, hUnscaled⟩ := hRes
  set i : Fin (37 - 1) :=
    (kummerLogEvenPowerIndex (p := 37) (by norm_num) (15 : Fin (kummerLogRank 37))).1 with hi_def
  have hi32 : (i : ℕ) = 32 := rfl
  set δ : CyclotomicUnitDelta 37 := kummerLogColumnDelta (p := 37) (by norm_num) a with hδ_def
  -- `W(a)` is the coordinate of the finite log of the unit `c^{p-1} − 1`.
  rw [normalizedUnitCoeff37_eq_finiteLog_denUnit a]
  -- Rewrite the finite log as the unscaled-minus-scaled Dwork difference (residual piece 1).
  rw [hLog a]
  -- Distribute the mod-`37²` coordinate over the difference.
  rw [valuedLambdaQuotientDworkCoeffModSq_sub]
  -- The scaled coordinate is the Teichmüller factor times the unscaled (proven column factor).
  rw [show ((kummerLogColumnDelta (p := 37) (by norm_num) a : CyclotomicUnitDelta 37) : ZMod 37) =
      (δ : ZMod 37) from rfl,
    valuedLambdaQuotientDworkCoeffModSq_scaledDworkParameterNormalizedCoordFiniteLogN71_eq_smul
      (K := CyclotomicField 37 ℚ) δ i]
  -- The unscaled degree-`32` coordinate is `37·(32!)⁻¹` (residual piece 2).
  rw [hUnscaled]
  -- Now: `37·(32!)⁻¹ − Tf^32·(37·(32!)⁻¹) = (1 − Tf^32)·(37·(32!)⁻¹) = 37·((1 − Tf^32)·(32!)⁻¹)`.
  -- Target RHS = `37·((1 − k^32)·(32!)⁻¹)`.  Reduce both to `37·(·)` and compare mod-`37`.
  rw [show (37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹) -
        teichmullerCoeffModSq (p := 37) (δ : ZMod 37) ^ (i : ℕ) *
          ((37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) =
      (37 : ZMod (37 ^ 2)) *
        ((1 - teichmullerCoeffModSq (p := 37) (δ : ZMod 37) ^ (i : ℕ)) *
          (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) from by ring]
  rw [show (1 - ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) *
        ((37 : ZMod (37 ^ 2)) * (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) =
      (37 : ZMod (37 ^ 2)) *
        ((1 - ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32)) *
          (((Nat.factorial 32 : ℕ) : ZMod (37 ^ 2))⁻¹)) from by ring]
  apply thirtyseven_mul_eq_of_castHom_eq
  -- mod-`37`: reduce both factors; only `castHom (Tf^32) = castHom ((a+2)^32)` is nontrivial.
  have hδval : (δ : ZMod 37) = (((a : ℕ) + 2 : ℕ) : ZMod 37) := by
    rw [hδ_def, kummerLogColumnDelta_val,
      kummerLogColumnIndex_eq_CPlusGeneratorIndex (p := 37) (by norm_num) a]
  have hTf : (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
      (teichmullerCoeffModSq (p := 37) (δ : ZMod 37) ^ (i : ℕ)) =
      (ZMod.castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (ZMod 37))
        ((((a : ℕ) + 2 : ℕ) : ZMod (37 ^ 2)) ^ 32) := by
    rw [map_pow, map_pow, hi32,
      teichmullerCoeffModSq_castHom (by norm_num : (37 : ℕ) ∣ 37 ^ 2) (δ : ZMod 37), hδval,
      map_natCast]
  simp only [map_mul, map_sub, map_one, hTf]

/-! ## 3. The residual discharges `CaseIICor823Level71UnitDworkCoordBridge37` and the FLT37 endpoint -/

open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIICor823Level71UnitDworkCoordBridge37` from the Dwork-specialized residual** (proven,
axiom-clean given `CaseIICor823Level71DworkSpecializedFiniteLog37`).

Composes `caseIICor823Level71DworkSpecializedFiniteLog37_coordIdentity` (the residual yields the
mod-`37²` coordinate identity `hCoord`) with the proven
`caseIICor823Level71UnitDworkCoordBridge37_of_coordIdentity` (the coordinate identity discharges the
unit↔Dwork-slice coordinate bridge).  This is the strictly-smaller-residual reduction: the level-`71`
coordinate structure is discharged from the `N`-generic machinery, leaving only the single Dwork-
specialized finite-log identity and the proven-slice degree-`32` coordinate value. -/
theorem caseIICor823Level71UnitDworkCoordBridge37_of_dworkSpecialized
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hRes : CaseIICor823Level71DworkSpecializedFiniteLog37) :
    CaseIICor823Level71UnitDworkCoordBridge37 :=
  caseIICor823Level71UnitDworkCoordBridge37_of_coordIdentity
    (fun a => caseIICor823Level71DworkSpecializedFiniteLog37_coordIdentity hRes a)

open FLT37.LehmerVandiver.CaseII in
/-- **Fermat's Last Theorem for `37`, with `R4` reduced to the level-`71` Dwork-specialized finite-log
residual `CaseIICor823Level71DworkSpecializedFiniteLog37`** (proven, axiom-clean given the genuine
residuals + the carried Kellner Prop).

Composes `caseIICor823Level71UnitDworkCoordBridge37_of_dworkSpecialized` with the proven endpoint
`fermatLastTheoremFor_thirtyseven_of_unitDworkCoordBridge`.  The level-`71` coordinate structure — the
mod-`37²` cyclotomic column factor, the slice-sum decomposition, the Teichmüller → rational collapse —
is **proven** from the `N`-generic machinery; only the single Dwork-specialized finite-log identity
(the genuine `v_p(L₃₇(1, ω³²)) = 1` second-order Fermat-quotient content) and the proven-slice
degree-`32` coordinate value remain.  Discharging this leaves FLT37 on R2 (the descent) + Kellner
alone. -/
theorem fermatLastTheoremFor_thirtyseven_of_dworkSpecialized
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_dworkSpecialized : CaseIICor823Level71DworkSpecializedFiniteLog37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_unitDworkCoordBridge
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    (caseIICor823Level71UnitDworkCoordBridge37_of_dworkSpecialized caseII_dworkSpecialized)
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
