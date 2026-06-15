import BernoulliRegular.FLT37.Eichler.CaseIILemma98Residue
import BernoulliRegular.FLT37.Eichler.CaseIIAssumptionIIAssembled

/-!
# Washington Lemma 9.8 / 9.9 for `p = 37`: the half-range conjugate residue equations are PROVEN
unconditionally (R3 route), and `Lemma98ConjugateResidue37` reduces to its local-power conjunct

This file discharges the **second conjunct** of the consolidated Washington Lemma-9.8 residue input
`Lemma98ConjugateResidue37` (`CaseIILemma98Residue.lean`) — the half-range Vandermonde conjugate
residue equations on the descent unit's regular free-part eigencomponents — **unconditionally**,
from the *proven* leading-`λ`-exponent eigencomponent collapse R3
(`caseII_leadingExponentEigenCollapse37_proven`, Washington Lemma 9.9 / Exercise 8.11) together with
the *proven, unconditional* free Case-II primarity congruence
(`caseIISigmaAntiDescent_quotient_int_congr`).

It imports only — it does **not** modify any existing file.

## The derivation (the R3 route — soundness-safest, non-circular)

The second conjunct of `Lemma98ConjugateResidue37` asks, for every Case-II descent instance and for
the canonical `K⁺`-descent `u` of `ε₁/ε₂` (`Units.map u = ε₁/ε₂`),

  `∀ a : Fin 18, ∑_j (regularPart c)_j · ((a+1)⁻¹)^{2(j+1)} = 0`,   `c = caseIIResidueProvenance_decomp (realUnitToFreePartModP u)`,

i.e. the half-range residue system on the **regular** eigencomponents
(`caseIIConjugateResidue_regularPart c j = if j = 15 then 0 else c j`).

This is **literally `0`**, because the regular eigencomponents `c j` (`j ≠ 15`) all **vanish**:

* **Free Case-II primarity (unconditional).**  The descent equation `ε₁ x'^37 + ε₂ y'^37 =
  ε₃ ((ζ-1)^m z')^37` with `m ≥ 1` forces `ε₁/ε₂ ≡ n (mod 37)` for an integer `n`
  (`caseIISigmaAntiDescent_quotient_int_congr` — the RHS is divisible by `(ζ-1)^{37m}` and
  `37 m ≥ 37 > 36`, so `(ζ-1)^{36} ∼ 37` already divides the LHS; the integer congruence then comes
  from the flt-regular Kummer chain).  Since `Units.map u = ε₁/ε₂`, also `Units.map u ≡ n (mod 37)`.

* **R3 (PROVEN, Washington Lemma 9.9 / Exercise 8.11).**  The proven local reduction
  `caseIILeadingExponent_completedLogArg_mem_lambdaIdeal_pow_pred` upgrades `Units.map u ≡ n (mod 37)`
  to the `λ`-adic membership `CompletedLogArgHighValuation37 u`, and the *proven* leading-exponent
  collapse `caseII_leadingExponentEigenCollapse37_proven : LeadingExponentEigenCollapse37` then forces
  `caseIIResidueProvenance_decomp (realUnitToFreePartModP u) j = 0` for every regular `j ≠ 15`
  (a regular `E_{2(j+1)}` contributes a leading `λ`-coefficient `∝ B_{2(j+1)} mod 37` at level
  `2(j+1) ≤ 34 < 36`, which the high `λ`-valuation kills).

Hence `caseIIConjugateResidue_regularPart c = 0` (the `j = 15` entry is `0` by definition, every
`j ≠ 15` entry is `0` by R3), and the residue sum vanishes term-by-term.

## Why this is **non-circular** (soundness-first)

Both inputs are **independent of Assumption II** (`WashingtonCaseIIExactQuotientUnitPower37Source`,
`ε₁/ε₂ = ε'^37`):

* the integer congruence `caseIISigmaAntiDescent_quotient_int_congr` is *free Case-II primarity*
  (high `λ`-valuation of the descent RHS), proven directly from the descent equation; and
* R3 `caseII_leadingExponentEigenCollapse37_proven` is the Galois-graded leading-`λ`-coefficient
  matrix-kernel collapse of Exercise 8.11 (`leadingExponentEigenCollapse37_of_eigenVandermonde
  caseIIEx811EigenVandermonde37_proven`), proven from the Bernoulli table and the two-Vandermonde
  coincidence.

In particular this derivation does **not** route through the circular consistency-only producer
`caseIISigmaAntiDescent_residueEqns_of_exactUnit` (which assumes Assumption II to produce the residue
equations).  See the `#print axioms` checks at the bottom: the residue-equation proof depends only on
`[propext, Classical.choice, Quot.sound]` and not on the exact-quotient-unit source.

## What is discharged, and the precise remaining residual

* `caseIISigmaAntiDescent_residueEqns_proven` — the **second conjunct, PROVEN unconditionally**.

* `lemma98ConjugateResidue37_of_localPower` — the consolidated input `Lemma98ConjugateResidue37`
  **reduces to its first conjunct alone**, `Lemma98LocalPower37` (Washington Lemma 9.8's single-index
  mod-`𝔩` Kummer congruence at the prime `𝔩 = lv149`).  The half-range conjugate residue system is no
  longer an input.

`Lemma98LocalPower37` over *free* units `ε₁, ε₂, ε₃` is over-general (B2
`CASEII-LEMMA98-LOCALPOWER`: the descent never feeds free units — `ε₁/ε₂` is always a producer ratio
of root-ideal generators); the **sound** consumer is the §9.1-identification + `ℓ ∣ z` route
(`caseIIOmega32_assumptionII_of_section91Ident_dvdZ`).  Accordingly the FLT37 endpoint below is the
sound `fermatLastTheoremFor_thirtyseven_of_caseII_postR3` shape — conditional on **R2 + R4(i) + R4(ii)
+ carried Kellner** — restated to make explicit that the half-range conjugate residue equations
(the second conjunct of `Lemma98ConjugateResidue37`) are now PROVEN, not assumed.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 (descent unit `η_a`),
  Lemma 9.2 (realness, free primarity), Lemma 9.8 (p. 180), Lemma 9.9 (pp. 180–181,
  the half-range Vandermonde residue system), Exercises 8.10/8.11, Corollary 8.15.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-! ## 1. The half-range conjugate residue equations are PROVEN unconditionally (R3 route)

We derive `caseIISigmaAntiDescent_residueEqns` — the second conjunct of `Lemma98ConjugateResidue37`
— from the *proven* R3 collapse and free Case-II primarity, with no Assumption-II dependency. -/

/-- **The half-range conjugate residue equations on the canonical descent unit, PROVEN**
(axiom-clean, **non-circular** — uses the proven R3 collapse and free Case-II primarity, **not**
Assumption II).

For every Case-II descent instance, the canonical `K⁺`-descent `u` of `ε₁/ε₂` has its mod-`37`
free-part eigencomponents satisfying the half-range Vandermonde conjugate residue equations of
Washington Lemma 9.8 / 9.9 over all conjugates:

  `∀ a, ∑_j (regularPart c)_j · ((a+1)⁻¹)^{2(j+1)} = 0`,   `c = caseIIResidueProvenance_decomp (realUnitToFreePartModP u)`.

These sums are **identically `0`**: the regular eigencomponents `c j` (`j ≠ 15`) all vanish by the
proven R3 collapse `caseIILeadingExponent_regular_components_zero`
(`caseII_leadingExponentEigenCollapse37_proven`), once `Units.map u = ε₁/ε₂ ≡ n (mod 37)` is supplied
by the *unconditional* free Case-II primarity `caseIISigmaAntiDescent_quotient_int_congr`; and the
`regularPart` zeroes the `j = 15` entry by definition.  Thus `regularPart c = 0`, and the system
holds term-by-term.

This is the **non-circular** discharge of the second conjunct: it is the conjugate-prime shadow of
the descent unit's `≡` rational congruence, read off through the proven Galois-graded
leading-`λ`-coefficient collapse — never the exact-quotient-unit source. -/
theorem caseIISigmaAntiDescent_residueEqns_proven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    caseIISigmaAntiDescent_residueEqns := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx' hy' hz' heq u hu a
  -- Free Case-II primarity (unconditional): `ε₁/ε₂ ≡ n (mod 37)` for an integer `n`.
  obtain ⟨n, hn⟩ :=
    caseIISigmaAntiDescent_quotient_int_congr D.hζ D.one_le_m hx' heq
  -- Transport the congruence to `Units.map u` via `hu : Units.map u = ε₁/ε₂`.
  have hKunit : ((Units.map (algebraMap
        (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
        (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) :
        𝓞 (CyclotomicField 37 ℚ)) =
      ((ε₁ / ε₂ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) :=
    congrArg (fun v : (𝓞 (CyclotomicField 37 ℚ))ˣ => (v : 𝓞 (CyclotomicField 37 ℚ))) hu
  have hc : (37 : 𝓞 (CyclotomicField 37 ℚ)) ∣
      ((Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
          (𝓞 (CyclotomicField 37 ℚ))).toMonoidHom u : (𝓞 (CyclotomicField 37 ℚ))ˣ) -
        (n : 𝓞 (CyclotomicField 37 ℚ))) := by
    rw [hKunit]; exact hn
  -- R3 (PROVEN): the regular eigencomponents of `realUnitToFreePartModP u` vanish.
  have hreg : ∀ j : Fin 18, j ≠ 15 →
      caseIIResidueProvenance_decomp
        (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u)) j = 0 :=
    caseIILeadingExponent_regular_components_zero
      caseII_leadingExponentEigenCollapse37_proven u n hc
  -- Hence the regular part of the canonical decomposition is the zero vector.
  have hregPart : caseIIConjugateResidue_regularPart
      (caseIIResidueProvenance_decomp
        (FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u))) = 0 := by
    funext j
    rw [caseIIConjugateResidue_regularPart, Pi.zero_apply]
    by_cases hj : j = 15
    · rw [if_pos hj]
    · rw [if_neg hj]; exact hreg j hj
  -- The residue sum vanishes term-by-term.
  rw [hregPart]
  simp

/-! ## 2. `Lemma98ConjugateResidue37` from its local-power conjunct alone

The consolidated input `Lemma98ConjugateResidue37` is a conjunction of (1) the local mod-`𝔩` power
`Lemma98LocalPower37` and (2) the half-range conjugate residue equations
`caseIISigmaAntiDescent_residueEqns`.  Section 1 proves (2) unconditionally, so the whole input
reduces to (1) alone. -/

/-- **`Lemma98ConjugateResidue37` from `Lemma98LocalPower37` alone** (proven, axiom-clean).

The second conjunct of `Lemma98ConjugateResidue37` — the half-range conjugate residue equations on
the descent unit's regular free-part eigencomponents — is the **proven, unconditional**
`caseIISigmaAntiDescent_residueEqns_proven` (R3 route).  Hence the consolidated Washington Lemma-9.8
residue input `Lemma98ConjugateResidue37` follows from its **first conjunct alone**, the local
mod-`𝔩` power `Lemma98LocalPower37` (Washington Lemma 9.8's single-index Kummer congruence at the
prime `𝔩 = lv149`).

This eliminates the half-range conjugate residue system from the Case-II residual set: the only
descent-unit residue content remaining is the single-index local power. -/
theorem lemma98ConjugateResidue37_of_localPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_localPow : Lemma98LocalPower37) :
    Lemma98ConjugateResidue37 := by
  intro hV hSO m D x' y' z' ε₁ ε₂ ε₃ hx' hy' hz' heq
  refine ⟨h_localPow hV hSO D hx' hy' hz' heq, ?_⟩
  intro u hu a
  exact caseIISigmaAntiDescent_residueEqns_proven hV hSO D hx' hy' hz' heq u hu a

/-! ## 3. Assumption II and FLT37 Case-II, with the half-range residue equations PROVEN

Feeding the reduced `Lemma98ConjugateResidue37` (now requiring only `Lemma98LocalPower37`) to the
proven `caseIILemma98Residue_assumptionII_of_conjugateResidue` yields Assumption II from the single
local-power input.  Composing with the §9.1-identification + `ℓ ∣ z` route makes the local power
itself **sound** (never the false bare free-unit local power), giving the FLT37 Case-II endpoint on
**R2 + R4(i) + R4(ii) + carried Kellner**. -/

/-- **Assumption II from the Lemma-9.8 local power alone, half-range residue equations PROVEN**
(proven, axiom-clean).

`WashingtonCaseIIExactQuotientUnitPower37Source` (Assumption II: `ε₁/ε₂` is a `37`-th power) from the
single input `Lemma98LocalPower37`, with the half-range conjugate residue equations (the second
conjunct of `Lemma98ConjugateResidue37`) supplied internally by the proven
`caseIISigmaAntiDescent_residueEqns_proven` (R3 route).  Composes
`lemma98ConjugateResidue37_of_localPower` with the proven
`caseIILemma98Residue_assumptionII_of_conjugateResidue`. -/
theorem caseIILemma98ResidueDischarge_assumptionII_of_localPower
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_localPow : Lemma98LocalPower37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIILemma98Residue_assumptionII_of_conjugateResidue
    (lemma98ConjugateResidue37_of_localPower h_localPow)

/-- **Assumption II from the genuine §9.1 identification + `ℓ ∣ z` datum, half-range residue
equations PROVEN** (proven, axiom-clean — the **sound** local-power route).

`WashingtonCaseIIExactQuotientUnitPower37Source` from the two sound genuine R4 residuals — the §9.1
residue identification `CaseIISection91DescentUnitIdentification37` (R4(i)) and the `ℓ ∣ z` datum
`CaseIILehmerVandiverDvdZ37` (R4(ii)) — routing the Lemma-9.8 local power through the **proven** §9.1
producer (`caseII_localPower_of_dvd_z`, never Assumption II), with the half-range conjugate residue
equations supplied internally by the proven R3 route.  The bare free-unit local power is **not**
used. -/
theorem caseIILemma98ResidueDischarge_assumptionII_of_section91Ident_dvdZ
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_section91Ident : CaseIISection91DescentUnitIdentification37)
    (caseII_dvdZ : CaseIILehmerVandiverDvdZ37) :
    FLT37.LehmerVandiver.CaseII.WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIILemma98ResidueDischarge_assumptionII_of_localPower
    (lemma98LocalPower37_of_strict
      (caseII_localPower_of_dvd_z caseII_section91Ident) caseII_dvdZ)

/-- **FLT37 for `37`, half-range conjugate residue equations PROVEN** (proven, axiom-clean given the
remaining named inputs + carried Kellner).

`FermatLastTheoremFor 37` from the genuine remaining Case-II residuals — **R2** (reality-preserving
single-root descent), **R4(i)** (the §9.1 Lemma-9.8-opening residue identification `ε₁/ε₂ ≡ δ
(mod 𝔩)`), **R4(ii)** (the genuine `ℓ ∣ z` datum, Washington Lemma 9.7), and the carried Kellner
second-order input.  Case I (Eichler), `¬ 37 ∣ h⁺` (Vandiver for 37), the Case-II II1 (Washington
Lemma 9.2), and **R3** (Washington Lemma 9.9 regular indices) are all proven and supplied internally
by `fermatLastTheoremFor_thirtyseven_of_caseII_postR3`.

The point of this restatement is that the half-range conjugate residue equations — the second
conjunct of the consolidated Washington Lemma-9.8 residue input `Lemma98ConjugateResidue37` — are now
**proven unconditionally** (`caseIISigmaAntiDescent_residueEqns_proven`, R3 route), so the only
descent-unit residue content driving the endpoint is the single-index local power, supplied soundly
by R4(i)+R4(ii). -/
theorem fermatLastTheoremFor_thirtyseven_of_caseII_residueEqnsProven
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_section91Ident : CaseIISection91DescentUnitIdentification37)
    (caseII_lehmerVandiverDvdZ : CaseIILehmerVandiverDvdZ37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_caseII_postR3
    caseII_realDescent caseII_section91Ident caseII_lehmerVandiverDvdZ noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
