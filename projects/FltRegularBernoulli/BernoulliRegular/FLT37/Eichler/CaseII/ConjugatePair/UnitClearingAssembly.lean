import BernoulliRegular.FLT37.Eichler.CaseII.ConjugatePair.SymmetricUnitClearing
import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.AssumptionIIFromR3

/-!
# [FLT37-CASEII-R2] Assembling the ε₁-37th-power resolution into the unit-clearing step

This file assembles the two **proved** algebraic cores of the ε₁-37th-power resolution
(`CaseIIConjPairEpsPower.lean`) — the `37`-th-power combination
`unit_isPow_of_prod_isPow_of_quotient_isPow` (§1) and the symmetric clearing
`caseII_conjPair_symmetric_clear` (§2) — with the **assembled Assumption II**
(`caseIIOmega32_assumptionII_of_section91Ident_dvdZ`, R3-proven, modulo R4(i)+R4(ii)+Kellner) into
the σ-conjugate-pair unit-clearing step `CaseIIConjPairUnitClearingStep37`
(`CaseIIConjPairThreeTermDescent.lean`, §4) — the structural heart R2 of the FLT37 Case-II descent.

## The reduction performed here

`caseIIConjPairUnitClearingStep37_of_sigmaEquivariant_and_normPower` proves
`CaseIIConjPairUnitClearingStep37` from exactly **two** inputs (plus the assembled Assumption II,
which is itself proven modulo R4(i)+R4(ii)+Kellner):

1. **σ-equivariance of the descent equation** (`CaseIIConjPairSigmaEquivariantDescent37`):
   the σ-conjugate-pair 6-unit descent equation can be chosen with `σx' = y'` and `σε₁ = ε₂` (the
   descent variables form a σ-conjugate pair and the leading units are σ-conjugate).  This is the
   precise content that the *swap*-structured descent over the conjugate-paired generators produces
   (it is **proved** over individually-real data — `caseII_conjPair_descent_vars` gives `σx' = y'`;
   the unit σ-pairing `σε₁ = ε₂` is the remaining sub-step, B2-logged `R2-thetaFixed`).

2. **the norm is a `37`-th power** (`CaseIIConjPairNormPthPower37`): the `K/K⁺` relative norm
   `ε₁·σ(ε₁)` of the leading descent unit is a `37`-th power.  This is **Kummer's lemma for the plus
   part** (`37 ∤ h⁺`): a real unit congruent to a rational integer mod `37` is a `37`-th power.

Given these, the proof:
* gets `ε₁/ε₂` a `37`-th power from Assumption II (Core (b), no σ-pairing needed);
* with `σε₁ = ε₂`, rewrites this as `ε₁/σ(ε₁)` a `37`-th power;
* combines with `ε₁·σ(ε₁)` a `37`-th power (Core (a)) via §1 to get `ε₁ = δ₁^37`;
* feeds `σx' = y'`, `σε₁ = ε₂`, `ε₁ = δ₁^37` into §2 (`caseII_conjPair_symmetric_clear`) to produce
  the clean σ-conjugate-pair solution.

It imports only; it does **not** modify any existing file.

## Honest status of the two inputs (soundness-first)

Both inputs are `def … : Prop` (not axioms), kept as explicit hypotheses of the *conditional*
clearing-step reduction.  They are **not** discharged here.  The σ-equivariance input is the
B2-logged `R2-thetaFixed` open sub-step (the unit σ-pairing `σε₁ = ε₂`); over **ConjPair** data the
descent produces individually-σ-stable variables (`σx' = ζ^a·x'`, `caseII_conjPair_zeta_twist_real`)
rather than the σ-conjugate pair, so the σ-equivariant equation is genuinely the *swap*-structured
(individually-real-data) output, not a free consequence.  The norm-power input is Kummer's lemma for
the plus part, which is **not** available in flt-regular (its `eq_pow_prime_of_unit_of_congruent`
needs `37 ∤ h`, false for the irregular `p = 37`); the `37 ∤ h⁺` real-unit version is the genuine
analytic residual.  See `.mathlib-quality/b2_log.jsonl` (`R2-thetaFixed`) and the session report.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (the descent, Lemma 9.2), Thm 9.4;
  §5.6 (Kummer's lemma / Theorem 5.36 — the `p ∤ h⁺` real-unit version).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The two precise residual inputs -/

/-- **[FLT37-CASEII-CONJPAIR-σ-EQUIVARIANT-DESCENT] The σ-equivariant descent equation.**

For every σ-conjugate-pair datum `D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m`, the next
descent equation can be chosen **σ-equivariantly**: there exist `x' y' z' : 𝓞 K`,
`ε₁ ε₂ ε₃ : (𝓞 K)ˣ` with

* `(ζ-1) ∤ x', y', z'`,
* `σx' = y'`  (the descent variables form a σ-conjugate pair),
* `σε₁ = ε₂`  (the leading descent units are σ-conjugate),
* `ε₁·x'^37 + ε₂·y'^37 = ε₃·((ζ-1)^m·z')^37`.

This is the *swap*-structured descent output (over conjugate-paired generators at the inversion-
symmetric root pair).  `σx' = y'` is **proved** at the variable level
(`caseII_conjPair_descent_vars` over real data); the unit σ-pairing `σε₁ = ε₂` is the
remaining sub-step (B2-logged `R2-thetaFixed`).  A `def … : Prop` (not an axiom). -/
def CaseIIConjPairSigmaEquivariantDescent37 : Prop :=
  ∀ {m : ℕ} (D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m),
    ∃ (x' y' z' : 𝓞 (CyclotomicField 37 ℚ)) (ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ¬ (D.hζ.unit'.1 - 1) ∣ x' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ y' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ z' ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) x' = y' ∧
      unitsComplexConj (CyclotomicField 37 ℚ) ε₁ = ε₂ ∧
      (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 + (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37

/-- **[FLT37-CASEII-CONJPAIR-NORM-PTHPOWER] The descent-unit relative norm is a `37`-th power.**

For every σ-conjugate-pair datum and every σ-equivariant descent equation produced from it, the
`K/K⁺` relative norm `ε₁·σ(ε₁)` of the leading descent unit is a `37`-th power.

This is **Kummer's lemma for the plus part** (`37 ∤ h⁺`): `ε₁·σ(ε₁)` is a *real* unit
(fixed by `σ`) and (in the Case-II configuration) congruent to a rational integer mod
`37`, so by Kummer's lemma over the real subfield it is a `37`-th power.  A
`def … : Prop` (not an axiom). -/
def CaseIIConjPairNormPthPower37 : Prop :=
  ∀ {m : ℕ} (D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m)
    (x' y' z' : 𝓞 (CyclotomicField 37 ℚ)) (ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ),
    ¬ (D.hζ.unit'.1 - 1) ∣ x' →
    ¬ (D.hζ.unit'.1 - 1) ∣ y' →
    ¬ (D.hζ.unit'.1 - 1) ∣ z' →
    unitsComplexConj (CyclotomicField 37 ℚ) ε₁ = ε₂ →
    (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 + (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37 →
    ∃ w : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      ε₁ * unitsComplexConj (CyclotomicField 37 ℚ) ε₁ = w ^ 37

/-! ## 2. The unit-clearing step from the two residuals + assembled Assumption II -/

/-- **`CaseIIConjPairUnitClearingStep37` from σ-equivariance + the norm being a `37`-th power +
Assumption II** (fully proved reduction).

Given the σ-equivariant descent equation residual `CaseIIConjPairSigmaEquivariantDescent37`, the
norm-`37`-th-power residual `CaseIIConjPairNormPthPower37`, Assumption II
`WashingtonCaseIIExactQuotientUnitPower37Source` (assembled, R3-proven, modulo
R4(i)+R4(ii)), and the carried Kellner second-order input, the σ-conjugate-pair
unit-clearing step `CaseIIConjPairUnitClearingStep37` holds.

This is a genuine reduction: the proof produces `ε₁ = δ₁^37` via the §1 combination
(`unit_isPow_of_prod_isPow_of_quotient_isPow`) from `ε₁σε₁` a `37`-th power (the norm residual) and
`ε₁/ε₂ = ε₁/σε₁` a `37`-th power (Assumption II + the σ-pairing `σε₁ = ε₂`), then performs the
symmetric clearing (§2 `caseII_conjPair_symmetric_clear`). -/
theorem caseIIConjPairUnitClearingStep37_of_sigmaEquivariant_and_normPower
    (h_sigma : CaseIIConjPairSigmaEquivariantDescent37)
    (h_norm : CaseIIConjPairNormPthPower37)
    (h_assumptionII : WashingtonCaseIIExactQuotientUnitPower37Source)
    (h_kellner : NoSecondOrderIrregularPair 37 32) :
    CaseIIConjPairUnitClearingStep37 := by
  intro m D _x'₀ _y'₀ _z'₀ _ε₁₀ _ε₂₀ _ε₃₀ _hx₀ _hy₀ _hz₀ _e₀
  -- Replace the *given* (arbitrary) 6-unit equation by the **σ-equivariant** one for the same datum
  -- `D` (the clearing-step conclusion only needs *some* clean σ-conjugate-pair solution).
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', hx'_conj, hε_conj, e'⟩ := h_sigma D
  -- (b) `ε₁/ε₂` is a `37`-th power — Assumption II, over the underlying bare `CaseIIData37`.
  obtain ⟨v, hv⟩ :=
    h_assumptionII Sinnott.flt37_not_dvd_hPlus h_kellner D.toCaseIIData37 hx' hy' hz' e'
  -- (a) `ε₁·σ(ε₁)` is a `37`-th power — the norm residual.
  obtain ⟨w, hw⟩ := h_norm D x' y' z' ε₁ ε₂ ε₃ hx' hy' hz' hε_conj e'
  -- Combine via §1: `ε₁/σ(ε₁) = ε₁/ε₂` (using `σε₁ = ε₂`) is a `37`-th power, and `ε₁·σ(ε₁)` is a
  -- `37`-th power, so `ε₁ = δ₁^37`.
  obtain ⟨δ₁, hδ₁⟩ :=
    unit_isPow_of_prod_isPow_of_quotient_isPow
      (a := ε₁) (b := unitsComplexConj (CyclotomicField 37 ℚ) ε₁)
      ⟨w, hw⟩
      ⟨v, hε_conj ▸ hv⟩
  -- §2: the symmetric clearing produces the clean σ-conjugate-pair solution.
  exact caseII_conjPair_symmetric_clear D.hζ hy' hz' hx'_conj hε_conj hδ₁ e'

/-! ## 3. Composition: no σ-conjugate-pair Case-II datum, from the genuine R4 inputs

The σ-conjugate-pair descent residual `CaseIIConjPairDescentSolution37` (hence the absence of any
σ-conjugate-pair Case-II datum) follows from the σ-equivariance residual + the norm-`37`-th-power
residual, the two genuine R4 residuals (which **assemble** Assumption II via the R3-proven
`caseIIOmega32_assumptionII_of_section91Ident_dvdZ`), and the carried Kellner input.  This wires the
ε₁-`37`-th-power resolution down to the Case-II ConjPair contradiction. -/

/-- **`CaseIIConjPairDescentSolution37` from σ-equivariance + the norm power + the genuine R4
inputs** (assembled Assumption II), fully proved.

Composes `caseIIConjPairUnitClearingStep37_of_sigmaEquivariant_and_normPower` (Assumption II
assembled from R4(i)+R4(ii) via `caseIIOmega32_assumptionII_of_section91Ident_dvdZ`) with the proved
strictly-shrinking reduction `caseIIConjPairDescentSolution37_of_unitClearingStep`. -/
theorem caseIIConjPairDescentSolution37_of_sigmaEquivariant_normPower_R4
    (h_sigma : CaseIIConjPairSigmaEquivariantDescent37)
    (h_norm : CaseIIConjPairNormPthPower37)
    (caseII_section91Ident : CaseIISection91DescentUnitIdentification37)
    (caseII_dvdZ : CaseIILehmerVandiverDvdZ37)
    (h_kellner : NoSecondOrderIrregularPair 37 32) :
    CaseIIConjPairDescentSolution37 :=
  caseIIConjPairDescentSolution37_of_unitClearingStep
    (caseIIConjPairUnitClearingStep37_of_sigmaEquivariant_and_normPower h_sigma h_norm
      (caseIIOmega32_assumptionII_of_section91Ident_dvdZ caseII_section91Ident caseII_dvdZ)
      h_kellner)

/-- **No σ-conjugate-pair Case-II datum, from the ε₁-`37`-th-power resolution** (fully proved).

The Case-II ConjPair contradiction (`¬ ∃ m, Nonempty (ConjPairCaseIIData37 K m)`) from the two
ε₁-resolution residuals (σ-equivariance + norm power), the genuine R4 inputs (assembled Assumption
II), and Kellner.  Composes `caseIIConjPairDescentSolution37_of_sigmaEquivariant_normPower_R4` with
the proved minimality wrapper `no_conjPairCaseIIData37_of_descentSolution`. -/
theorem no_conjPairCaseIIData37_of_sigmaEquivariant_normPower_R4
    (h_sigma : CaseIIConjPairSigmaEquivariantDescent37)
    (h_norm : CaseIIConjPairNormPthPower37)
    (caseII_section91Ident : CaseIISection91DescentUnitIdentification37)
    (caseII_dvdZ : CaseIILehmerVandiverDvdZ37)
    (h_kellner : NoSecondOrderIrregularPair 37 32) :
    ¬ ∃ m : ℕ, Nonempty (ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m) :=
  no_conjPairCaseIIData37_of_descentSolution
    (caseIIConjPairDescentSolution37_of_sigmaEquivariant_normPower_R4 h_sigma h_norm
      caseII_section91Ident caseII_dvdZ h_kellner)

end BernoulliRegular.FLT37.Eichler

end

end
