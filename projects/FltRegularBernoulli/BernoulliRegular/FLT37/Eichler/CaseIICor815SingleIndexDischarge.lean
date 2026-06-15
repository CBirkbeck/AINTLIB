import BernoulliRegular.FLT37.Eichler.CaseIILemma98Residue

/-!
# Washington Corollary 8.15 single-index expansion for `p = 37`, discharged at the
single-index level

This file **discharges `Cor815SingleIndexExpansion37`** (Washington Corollary 8.15, the
single-index cyclotomic-unit expansion `ε₁/ε₂ = E₃₂^{d}·α^{37}` of the Case-II descent unit)
down to a *single* precise residue input, by composing the already-proven membership-free
eigenspace collapse chain.  It imports only — it does **not** modify any existing file.

## The result

`Cor815SingleIndexExpansion37` (`CaseIIAssumptionII.lean`) is the named hypothesis that the
Case-II descent-equation quotient unit `ε₁/ε₂` equals `E₃₂^{d}·α^{37}` (`E₃₂ =
pollaczekUnitPlus 37 K 32`, the sole irregular Pollaczek unit, the regular indices dropped via
the Bernoulli table).  We prove it follows from

* `caseIISigmaAntiDescent_residueEqns` — Washington Lemma 9.8 / 9.9's half-range Vandermonde
  residue equations on the *canonical* `K⁺`-descent of `ε₁/ε₂` (over all conjugate primes
  `σ_α(𝔩)`); equivalently (`caseII_corollary815_expansion_of_conjugateResidue`) from the single
  consolidated input `Lemma98ConjugateResidue37` (Washington Lemma 9.8 over all conjugates),

and nothing else.

## The unit subtlety, resolved

`Cor815SingleIndexExpansion37` is stated for the **descent-equation quotient unit** `ε₁/ε₂`
(Washington's `η_a/η_b`).  The question "is `ε₁/ε₂` a *real cyclotomic* unit modulo `37`-th
powers (in `E⁺·(units)^{37}`)?" splits into two facts, and the membership-free chain
(`CaseIIExplicitDescent.lean`) shows precisely which are needed:

* **Realness** (the `(𝓞 K⁺)ˣ`-descent: `∃ u : (𝓞 K⁺)ˣ, Units.map (algebraMap (𝓞 K⁺) (𝓞 K)) u =
  ε₁/ε₂`) is the **unconditional** free-Case-II-primarity result `caseIISigmaAntiDescent_quotient_
  unitsMap` (`CaseIISigmaAntiDescent.lean §2`).  This is what makes `ε₁/ε₂` a unit whose
  single-index expansion can even be *stated* on the K⁺ side.

* **Cyclotomic membership** of that descent (`u ∈ C⁺ = caseIICPlus37`, Washington §9.1's explicit
  `(1-ζ^a)/(1-ζ)`-form `caseIICyclotomicIdentification_quotient_isCPlusExponentProduct`) is, by
  the membership-free §1 of `CaseIIExplicitDescent.lean`
  (`caseIIExplicitDescent_eigenCollapseData_of_residueEqns`), **not used** by the single-index
  expansion: the K-side expansion `caseIICor815_algebraMap_singleIndexExpansion` only needs the
  K⁺-preimage to be *some* real unit carrying the eigenspace collapse (`Cor815EigenCollapseAt`),
  *not* a `C⁺`-member, and the eigenspace collapse upgrades the `37`-th root through the
  *kernel-vanishing* collapse `caseIIGaloisEigen_isPow37_of_realUnitToFreePartModP_eq_zero` (which
  bypasses the Sinnott `C⁺`-saturation that needed membership + `SinnottIndexFormula 37`).

So `ε₁/ε₂` need **not** be manifestly a `C⁺`-cyclotomic unit modulo `37`-th powers for
`Cor815SingleIndexExpansion37`; its realness is unconditional, and the only descent-unit input is
the Lemma-9.8 residue equations.  This is the precise resolution of the "`ε₁/ε₂` vs `η_a/η_b`"
subtlety: they coincide (`η_a/η_b = ε₁/ε₂` is the *definition* of the descent unit), `ε₁/ε₂` *is*
real (its K⁺-descent exists unconditionally), and `Cor815SingleIndexExpansion37` (for `ε₁/ε₂`) is
exactly the object the descent's Route-A `caseIIThm95_assumptionII_of_corollary815_lemma98`
consumes.

## What is proven and reused (the basis + R3 + `37 ∤ h⁺` + eigenspace, all banked)

Everything between the residue equations and `Cor815SingleIndexExpansion37` is *proven*, and the
composition here wires it explicitly at the single-index level:

* **the cyclotomic-unit basis** `CPlusGenerator` of `E⁺/(E⁺)^{37}`
  (`CPlusGenerator_image_span_eq_top` + `CPlusGenerator_image_linearIndependent`,
  `Washington814ForwardD.lean`) — driving the kernel-vanishing collapse
  `caseIIGaloisEigen_isPow37_of_realUnitToFreePartModP_eq_zero` and the automatic eigencomponent
  decomposition `caseIIResidueProvenance_decomp_spec`;
* **`37 ∤ h⁺`** (`Sinnott.flt37_not_dvd_hPlus`) and **R3** (the regular eigencomponents collapse
  via the half-range Vandermonde `caseIIThm95_coeff_collapse_even` +
  `caseIIGaloisEigen_pollaczekClasses_ne_zero`, the same data proving Vandiver for `37`), leaving
  only the irregular `i = 32` (`Sinnott.flt37_bernoulli_table`);
* the **Galois `Δ`-action eigenvalue** `caseIIGaloisEigen_omega32_eigenvalue` placing the surviving
  class in the single irregular `ω^{32}`-eigenspace, and the `1`-dimensionality of that eigenspace
  forcing the `E₃₂`-monomial residue form
  (`caseIIGaloisEigen_E32_monomial_of_mem_omega32_eigenspace`);
* the **K⁺ → K lift** `caseIICor815_algebraMap_singleIndexExpansion` (via
  `algebraMapPollaczekUnitPlusKplus_eq`).

The collapse is **first order** (mod `37`): R3 forces the regular coordinates `d_i ≡ 0 (mod 37)`,
a `ZMod 37` statement matching the single-index expansion's `ε₁/ε₂ ≡ E₃₂^{d} (mod (units)^{37})`;
no second-order / level-`72` content is involved (that was the dead Route (b)).

## Soundness

`Cor815SingleIndexExpansion37` quantifies over Case-II descent instances whose `ε₁, ε₂, ε₃` are
**unconstrained** units (`CaseIIData37` constrains only `x, y, z, ε` via the Fermat equation, not
the expansion-equation's `ε₁, ε₂, ε₃`).  So the single-index expansion is **not** a formal
consequence of the equation shape: a generic `ε₁/ε₂` (e.g. a regular cyclotomic unit `E₂`) is
*not* an `E₃₂`-monomial modulo `37`-th powers (it lies in the `ω^2`-eigenspace, not `ω^{32}`).
The residue equations `caseIISigmaAntiDescent_residueEqns` (Washington Lemma 9.8 over all
conjugates) are the genuine arithmetic input that forces the `ω^{32}`-eigenspace placement; they
are asserted only for the *specific* descent unit's eigencomponents, never as an `E₃₂`-monomial
property of an arbitrary unit.  They are **sound** (implied by Assumption II itself,
`caseIISigmaAntiDescent_residueEqns_of_exactUnit`) and **non-circular** at the residue level
(`Lemma98ConjugateResidue37` is a statement about residues mod `𝔩`, not the global power-ness).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Springer GTM 83: Corollary 8.15
  (p. 153), Proposition 8.18 / Corollary 8.19 (p. 158), Lemma 9.8 (p. 180), Lemma 9.9
  (pp. 180–181), §8.2 (Sinnott), §9.1 (descent unit `η_a`, pp. 169–172).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

/-! ## The single-index expansion from the bare residue equations

The membership-free chain of `CaseIIExplicitDescent.lean` gives, *proven*:

* `caseIIExplicitDescent_eigenCollapseData_of_residueEqns` :
  `caseIISigmaAntiDescent_residueEqns → Cor815EigenCollapseDescentData37`
  (realness unconditional, residue equations ⟹ `ω^{32}`-membership ⟹ membership-free eigenspace
  collapse `Cor815EigenCollapseAt`); and
* `caseIIExplicitDescent_singleIndexExpansion_of_eigenCollapseData` :
  `Cor815EigenCollapseDescentData37 → Cor815SingleIndexExpansion37`
  (the K-side single-index expansion from the eigenspace collapse, no Sinnott, no membership).

Composing them discharges `Cor815SingleIndexExpansion37` from the bare residue equations alone. -/

/-- **`Cor815SingleIndexExpansion37` from the bare Lemma-9.8 residue equations** (proven,
axiom-clean — **no** cyclotomic membership `w ∈ C⁺`, **no** `SinnottIndexFormula 37`).

The Corollary-8.15 single-index expansion `ε₁/ε₂ = E₃₂^{d}·α^{37}` of the Case-II descent unit
follows from the *single* descent-unit input

* `caseIISigmaAntiDescent_residueEqns` — Washington Lemma 9.8 / 9.9's half-range Vandermonde
  residue equations on the canonical `K⁺`-descent of `ε₁/ε₂` (over all conjugate primes).

Composition (all steps *proven*):

* `caseIIExplicitDescent_eigenCollapseData_of_residueEqns` — the **unconditional** realness §2 of
  `CaseIISigmaAntiDescent.lean` supplies the canonical descent unit `u` with `Units.map u =
  ε₁/ε₂`; the residue equations put `realUnitToFreePartModP u` in the irregular
  `ω^{32}`-eigenspace (R3 / half-range Vandermonde collapse + the `Δ`-eigenvalue); the
  membership-free kernel-vanishing collapse turns that into `Cor815EigenCollapseAt u`;
* `caseIIExplicitDescent_singleIndexExpansion_of_eigenCollapseData` — the K-side single-index
  expansion `ε₁/ε₂ = E₃₂^{d}·α^{37}` from the eigenspace collapse (via the K⁺ → K lift).

The descent unit's **realness** is unconditional; the cyclotomic membership `w ∈ C⁺` (the §9.1
target `caseIICyclotomicIdentification_quotient_isCPlusExponentProduct`) and the analytic
`SinnottIndexFormula 37` are **not** required — the membership-free chain bypasses the Sinnott
`C⁺`-saturation in favour of the basis-driven kernel-vanishing collapse. -/
theorem caseII_corollary815_singleIndexExpansion_of_residueEqns
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_res : caseIISigmaAntiDescent_residueEqns) :
    Cor815SingleIndexExpansion37 :=
  caseIIExplicitDescent_singleIndexExpansion_of_eigenCollapseData
    (caseIIExplicitDescent_eigenCollapseData_of_residueEqns h_res)

/-! ## The single-index expansion from the consolidated conjugate-residue input

`Lemma98ConjugateResidue37` (`CaseIILemma98Residue.lean`) is the *single* Washington Lemma-9.8
residue input consumed by the actual FLT37 Case-II endpoint
(`fermatLastTheoremFor_thirtyseven_of_caseIUnramified_realIdealDescent_conjugateResidue_noSO`):
its first conjunct is the mod-`𝔩` power-ness `Lemma98LocalPower37` and its second conjunct is the
all-conjugate residue equations.  The proven projection
`caseIILemma98Residue_residueEqns_of_conjugateResidue` extracts exactly
`caseIISigmaAntiDescent_residueEqns`, so `Cor815SingleIndexExpansion37` reduces to the *same*
residue input the endpoint uses. -/

/-- **`Cor815SingleIndexExpansion37` from the consolidated conjugate-residue input** (proven,
axiom-clean).

The single Washington Lemma-9.8 residue input `Lemma98ConjugateResidue37` (over all conjugate
primes `σ_α(𝔩)`) discharges `Cor815SingleIndexExpansion37`: its all-conjugate residue conjunct is
exactly `caseIISigmaAntiDescent_residueEqns` (the proven projection
`caseIILemma98Residue_residueEqns_of_conjugateResidue`), from which
`caseII_corollary815_singleIndexExpansion_of_residueEqns` gives the single-index expansion.

This routes `Cor815SingleIndexExpansion37` through the **same** residue input
(`Lemma98ConjugateResidue37`) that the actual FLT37 Case-II endpoint consumes — making explicit
that the Corollary-8.15 single-index expansion carries *no* descent-unit content beyond the
Washington Lemma-9.8 residue equations (the realness being unconditional, the basis/R3/`37 ∤
h⁺`/eigenspace machinery proven). -/
theorem caseII_corollary815_singleIndexExpansion_of_conjugateResidue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_conj : Lemma98ConjugateResidue37) :
    Cor815SingleIndexExpansion37 :=
  caseII_corollary815_singleIndexExpansion_of_residueEqns
    (caseIILemma98Residue_residueEqns_of_conjugateResidue h_conj)

/-! ## Assumption II at the single-index level, from the consolidated residue input

For completeness we re-express the downstream §4 collapse
(`caseIIThm95_assumptionII_of_corollary815_lemma98`: single-index expansion + `Lemma98LocalPower37`
⟹ Assumption II, whose operative core is `caseIIThm95_residueInd37_E32_ne_zero`,
`ind₃₇ E₃₂ ≠ 0`) composed with the single-index discharge above, all from the single consolidated
`Lemma98ConjugateResidue37` (whose mod-`𝔩` power-ness conjunct supplies `Lemma98LocalPower37`). -/

open FLT37.LehmerVandiver.CaseII in
/-- **Assumption II via the Corollary-8.15 single-index route, from the single conjugate-residue
input** (proven, axiom-clean).

Combines `caseII_corollary815_singleIndexExpansion_of_conjugateResidue` (this file) with the proven
§4 collapse `caseIIThm95_assumptionII_of_corollary815_lemma98` (the discrete-log single-index
`residueInd37` collapse, operative core `ind₃₇ E₃₂ ≠ 0`) and the proven projection
`caseIILemma98Residue_localPower_of_conjugateResidue` (the mod-`𝔩` power-ness conjunct of
`Lemma98ConjugateResidue37` is `Lemma98LocalPower37`).

So **Assumption II** (`WashingtonCaseIIExactQuotientUnitPower37Source`, the descent unit `ε₁/ε₂` is
a global `37`-th power) follows — *via the explicit Corollary-8.15 single-index expansion* — from
the lone Washington Lemma-9.8 residue input `Lemma98ConjugateResidue37`, with the descent unit's
realness unconditional and the entire basis / R3 / `37 ∤ h⁺` / eigenspace / single-index
discrete-log apparatus proven. -/
theorem caseII_corollary815_assumptionII_of_conjugateResidue
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_conj : Lemma98ConjugateResidue37) :
    WashingtonCaseIIExactQuotientUnitPower37Source :=
  caseIIThm95_assumptionII_of_corollary815_lemma98
    (caseII_corollary815_singleIndexExpansion_of_conjugateResidue h_conj)
    (caseIILemma98Residue_localPower_of_conjugateResidue h_conj)

end BernoulliRegular.FLT37.Eichler

end
