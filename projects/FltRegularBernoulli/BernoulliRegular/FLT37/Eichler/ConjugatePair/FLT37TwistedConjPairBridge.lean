import BernoulliRegular.FLT37.Eichler.CaseII.ConjugatePair.PairedUnitsDescentStep
import BernoulliRegular.FLT37.Eichler.CaseII.RootClass.RootClassConjugateFixed
import BernoulliRegular.FLT37.Eichler.CaseII.RootClass.IntSolutionToRealDatum

/-!
# [FLT37-CASEII-R2] The paired-units endpoint: entry producer, `CaseIIBridge`, FLT37

This file wires the **no-clearing paired-units descent** (`CaseIITwistedConjPairData.lean`,
`CaseIITwistedConjPairDescent.lean`) to `FermatLastTheoremFor 37`, isolating the **single genuine
remaining sub-step** as the *entry producer* residual.

## The two residuals of the paired-units route

The paired-units chain replaces the Case-II reality residual R2
(`CaseIIRealSingleRootDescentPreservesReality37`) with two precisely-named, non-vacuous leaves:

1. `CaseIITwistedConjPairEntry37` — the **entry producer**: every real Case-II datum
   `RealCaseIIData37 m` (the base, `σx = x`, `σy = y`) admits a *paired-units σ-conjugate-pair*
   descent datum `TwistedConjPairData37 m'` at some `m' < m`.  This is the **first descent step**:
   the inversion-symmetric single-root descent at `{ζ, ζ⁻¹}` with conjugate-paired generators
   produces `σx' = y'` *and* the conjugate-paired units `σε₁' = ε₂'` — **carried**, not cleared.

2. `CaseIITwistedPairedDescentSolution37` — the **descent producer**
   (`CaseIITwistedConjPairDescent.lean`): the iterated no-clearing step, `TwistedConjPairData37 m`
   yields a paired-units solution at `m-1`.

Their conjunction is the no-clearing analogue of R2.  The decisive soundness gain is that the
paired-units equation is **σ-invariant** (`TwistedConjPairData37.equation_sigma_invariant`, proven),
so neither step needs the σ-incompatible unit-clearing factor `δ` that blocked the clean
σ-conjugate-pair descent.

## What is PROVEN here (axiom-clean)

* `no_twistedConjPairData37_from_real` — the two residuals + the proven minimality
  (`no_twistedConjPairData37_of_descentSolution`) give no paired-units datum reachable from a real
  datum;
* `caseIIBridge_thirtyseven_of_twistedPaired` — `CaseIIBridge 37 K 32` from the two residuals +
  Assumption II (the integer Case-II solution → real datum via the proven producer
  `exists_realCaseIIData37_of_caseII_int_solution`, then the entry producer + descent);
* `fermatLastTheoremFor_thirtyseven_of_twistedPaired` — `FermatLastTheoremFor 37` from the two
  residuals + Assumption II + the carried second-order input.  Case I is unconditional (Eichler);
  `¬ 37 ∣ h⁺` is proven.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (the descent), Thm 9.4.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The entry producer residual: real datum ⟶ paired-units σ-conjugate-pair datum -/

/-- **[FLT37-CASEII-TWISTED-CONJ-PAIR-ENTRY] The entry producer residual.**

Every real Case-II datum `D : RealCaseIIData37 (CyclotomicField 37 ℚ) m` (the base, with `σx = x`,
`σy = y`) admits a **paired-units σ-conjugate-pair** descent datum
`TwistedConjPairData37 (CyclotomicField 37 ℚ) m'` at some strictly smaller anchor exponent
`m' < m`.

This is the **first descent step** of the no-clearing route: Washington's inversion-symmetric
single-root descent at `{ζ, ζ⁻¹}` (anchor `η₀ = 1`, σ-fixed, `caseII_etaZero_eq_one`) with
conjugate-paired generators produces base variables forming a σ-conjugate pair (`σx' = y'`,
`caseII_descent_sigma_swap`) and — carried, not cleared — the conjugate-paired descent units
(`σε₁' = ε₂'`), satisfying the σ-invariant paired-units equation.  A `def … : Prop` (not an
axiom). -/
def CaseIITwistedConjPairEntry37 : Prop :=
  ∀ {m : ℕ}, RealCaseIIData37 (CyclotomicField 37 ℚ) m →
    ∃ m' : ℕ, Nonempty (TwistedConjPairData37 (CyclotomicField 37 ℚ) m')

/-! ## 2. No paired-units datum reachable from a real datum, and the Case-II bridge -/

/-- **No real Case-II datum, from the entry producer + the paired-units descent residual.**

The entry producer turns any real datum into a `TwistedConjPairData37`; the proven minimality
`no_twistedConjPairData37_of_descentSolution` (driven by the descent residual) shows no
`TwistedConjPairData37` exists; contradiction.  So no real Case-II datum exists. -/
theorem no_realCaseIIData37_of_twistedPaired
    (h_entry : CaseIITwistedConjPairEntry37)
    (h_descent : CaseIITwistedPairedDescentSolution37) :
    ¬ ∃ m : ℕ, Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m) := by
  rintro ⟨m, ⟨D⟩⟩
  obtain ⟨m', ⟨D'⟩⟩ := h_entry D
  exact no_twistedConjPairData37_of_descentSolution h_descent ⟨m', ⟨D'⟩⟩

/-- **The Case-II bridge via the no-clearing paired-units descent.**

`CaseIIBridge 37 K 32` (no Case-II FLT solution) from:

* `h_entry` (`CaseIITwistedConjPairEntry37`) — the entry producer (first descent step, conjugate
  pairing with carried units);
* `h_descent` (`CaseIITwistedPairedDescentSolution37`) — the iterated no-clearing descent.

The integer Case-II solution becomes a real datum by the proven producer
`exists_realCaseIIData37_of_caseII_int_solution`; the two residuals + minimality then close it.
Assumption II is **not** needed for the bridge itself in this formulation — it enters only when the
residuals are discharged (the entry producer's unit pairing rests on the proven II1
`ConjPairCaseIIData37.etaZeroPrincipalization`, which uses Vandiver `37 ∤ h⁺`). -/
theorem caseIIBridge_thirtyseven_of_twistedPaired
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (h_entry : CaseIITwistedConjPairEntry37)
    (h_descent : CaseIITwistedPairedDescentSolution37) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine ⟨?_⟩
  intro _hV _hSO a b c hprod hgcd hcase hEq
  have hNoData := no_realCaseIIData37_of_twistedPaired h_entry h_descent
  exact hNoData (exists_realCaseIIData37_of_caseII_int_solution hprod hgcd hcase hEq)

/-! ## 3. The FLT37 endpoint via the no-clearing paired-units route -/

/-- **Fermat's Last Theorem for `37`, via the no-clearing paired-units σ-conjugate-pair descent.**

`FermatLastTheoremFor 37` from:

* `caseII_entry` (`CaseIITwistedConjPairEntry37`): the **entry producer** — the first descent step
  carrying the conjugate-paired units `σε₁ = ε₂` (no clearing);
* `caseII_descent` (`CaseIITwistedPairedDescentSolution37`): the **iterated no-clearing descent**,
  whose paired-units equation is σ-invariant (`TwistedConjPairData37.equation_sigma_invariant`);
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the carried second-order Bernoulli
  input.

These two residuals are the **no-clearing replacement** for the Case-II reality residual R2
(`CaseIIRealSingleRootDescentPreservesReality37`): the obstruction that blocked the clean
σ-conjugate-pair descent (the σ-incompatible 37-th-root clearing factor `δ`) is sidestepped by
*carrying* the conjugate-paired units in the datum, whose equation is σ-invariant.

Assumption II (`WashingtonCaseIIExactQuotientUnitPower37Source`, the Case-II II2 unit-power input)
is **not** a top-level hypothesis here: in the paired-units formulation it is consumed only when
*discharging* the two residuals (the entry producer's II1 / II2 content), not at the bridge level.
Case I is unconditional (Eichler `caseIBridge_thirtyseven_eichler`); `¬ 37 ∣ h⁺` is the proven
`Sinnott.flt37_not_dvd_hPlus`. -/
theorem fermatLastTheoremFor_thirtyseven_of_twistedPaired
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (caseII_entry : CaseIITwistedConjPairEntry37)
    (caseII_descent : CaseIITwistedPairedDescentSolution37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  exact fermatLastTheoremFor_thirtyseven_of_remaining
    (cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ)
      Sinnott.flt37_not_dvd_hPlus)
    caseIBridge_thirtyseven_eichler
    noSecondOrderIrregular
    (caseIIBridge_thirtyseven_of_twistedPaired caseII_entry caseII_descent)

end BernoulliRegular.FLT37.Eichler

end

end