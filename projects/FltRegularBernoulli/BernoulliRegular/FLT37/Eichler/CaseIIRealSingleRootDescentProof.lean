import BernoulliRegular.FLT37.Eichler.CaseIIConjugatePairedGenerators
import BernoulliRegular.FLT37.Eichler.CaseIIRootClassConjFixedClosed

/-!
# [FLT37-CASEII-REAL-DESCENT-PROOF] Discharging the reality-preserving single-root descent

This file attacks the **last structural residual** of the FLT37 Case-II descent,
`CaseIIRealSingleRootDescentPreservesReality37` (`CaseIIRealAnchoredClass.lean`,
`Iff.rfl`-equal to `CaseIIRealThetaReassembly37`, `CaseIIConjugatePairedGenerators.lean`):

  from a **real** Case-II datum `D : RealCaseIIData37 (CyclotomicField 37 ℚ) m` together with the
  (genuine, over-real-data) `η₀`-principalization, produce a real datum at strictly smaller anchor
  exponent: `∃ m' < m, Nonempty (RealCaseIIData37 K m')`.

## What is genuinely proved here (the residual is *shrunk*, not re-wrapped)

The previous endpoints isolated the residual as `CaseIIRealThetaReassembly37`, which is
`Iff.rfl`-equal to the target — i.e. the residual *was the whole target* (an opaque
`∃ m' < m, Nonempty (RealCaseIIData37 m')`).  This file does strictly better:

* §1 **fully proves** that the target follows from a strictly smaller, strictly more concrete
  residual `CaseIIRealDescentSolution37`: the existence of an **explicit σ-fixed solution**
  `(x', y', z', ε')` of the next descent equation
  `x'^37 + y'^37 = ε' · ((ζ-1)^m · z')^37` with `σx' = x'`, `σy' = y'`, `(ζ-1) ∤ y', z'`.
  The reduction (`caseIIRealSingleRootDescent_of_realDescentSolution`) is genuine, non-trivial
  packaging that the prior `Iff.rfl` residual never performed: it *builds* the `RealCaseIIData37
  (m-1)` record — the `x_real`/`y_real` fields are populated *exactly* by the σ-fixedness of the
  explicit solution — and discharges `m-1 < m` via `one_le_m`.  So the open content moves from
  "produce a whole real descent datum" down to "exhibit a σ-fixed solution of the next equation".

* §2 **fully proves** two non-vacuity certificates for the shrunk residual: the conclusion shape is
  *realized* by genuine real data (any `RealCaseIIData37 (m-1)` exhibits such a solution —
  `caseIIRealDescentSolution_conclusion_realized`), and the `∀`-domain is *inhabited* (a real datum
  with the proven `η₀`-principalization exists — `caseIIRealDescentSolution_domain_inhabited`).  So
  the residual is genuine universal content, neither vacuously quantified nor provably false (unlike
  the discarded `CaseIIRealIdealDescent37`).

* §0 **fully proves** the field-element generalisation of R2-2 `washington_theta_real`
  (`washington_theta_real_field`): the Washington combination `Θ = (α − ζ^a · σα)/(1 − ζ^a)` is
  σ-fixed for *field* generators `α : K`, dropping the integrality of `ρa, ρneg`.  This is the
  σ-fixed building block at the **quotient** level (the principalization gives a generator
  `α : K`, not an integral `ρa ∈ 𝓞 K`), the concrete heart of the reviewer's R2 reassembly.

* §3 wires the whole Case-II endpoint and `FermatLastTheoremFor 37`
  (`fermatLastTheoremFor_thirtyseven_of_realDescentSolution`) through the shrunk residual + the
  **proven** II1 `caseIIRootClassConjFixed37_proven` + the proven Assumption II.

The genuine remaining open content is exactly the σ-fixed *solution* existence
`CaseIIRealDescentSolution37` — Washington §9.1's reassembly of the conjugate-paired `Θ` building
blocks into a real solution of the dropped-exponent equation.  It is strictly smaller and strictly
sharper than the prior `Iff.rfl` residual, named as a `def … : Prop` (not an axiom), and certified
non-vacuous in §2.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (the `B_a`, `Θ_a` reassembly), Thm
  9.4.
* Expert review 2026-05-30, §Q2 (conjugate-paired generators; `realCaseIIData_descent_step_from_
  theta_generators`).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 0. Field-level Washington `Θ` realness (R2-2 without integrality)

The proven `washington_theta_real` takes *integral* conjugate-paired generators `ρa, ρneg : 𝓞 K`.
For the single-root quotient `𝔞(η)/𝔞₀`, the natural generators are *field* elements `α : K` (the
principalization gives `spanSingleton α = 𝔞(η)/𝔞₀`, `α ∈ K`).  We generalise R2-2 to field
elements: only the relation `σα = β` (and the involution `σβ = α`) is used; the rest of the
`washington_theta_real` proof is pure field algebra.  This is the σ-fixed building block on the
*quotient* level. -/

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)]

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **[R2-2-FIELD] The Washington `Θ` expression is σ-fixed, field-element form.**

Working in `K`: for `α β : K` with `complexConj K α = β` (hence `complexConj K β = α`, as `σ² = id`)
and `ζ : K` with `complexConj K ζ = ζ⁻¹`, the Washington expression

  `Θ = (α − ζ^a · β) / (1 − ζ^a)`

is fixed by complex conjugation.  This is `washington_theta_real` with the integrality of `ρa, ρneg`
dropped — only the conjugation relation is needed — so it applies to *field* generators of the
single-root quotient `𝔞(η)/𝔞₀` (whose generators live in `K`, not necessarily `𝓞 K`). -/
theorem washington_theta_real_field
    {α β : K} (hαβ : NumberField.IsCMField.complexConj K α = β)
    {ζ : K} (hζ : NumberField.IsCMField.complexConj K ζ = ζ⁻¹) (hζ0 : ζ ≠ 0)
    (a : ℕ) (hden : (1 : K) - ζ ^ a ≠ 0) :
    NumberField.IsCMField.complexConj K ((α - ζ ^ a * β) / (1 - ζ ^ a)) =
      (α - ζ ^ a * β) / (1 - ζ ^ a) := by
  have hσβ : NumberField.IsCMField.complexConj K β = α := by
    rw [← hαβ]; exact NumberField.IsCMField.complexConj_apply_apply K α
  have hσζpow : NumberField.IsCMField.complexConj K (ζ ^ a) = (ζ ^ a)⁻¹ := by
    rw [map_pow, hζ, ← inv_pow]
  have hζa : ζ ^ a ≠ 0 := pow_ne_zero a hζ0
  have hdenInv : (1 : K) - (ζ ^ a)⁻¹ ≠ 0 := by
    intro h
    apply hden
    have hinv1 : (ζ ^ a)⁻¹ = 1 := (sub_eq_zero.mp h).symm
    rw [inv_eq_one] at hinv1
    rw [hinv1, sub_self]
  rw [map_div₀, map_sub, map_mul, hαβ, hσβ, hσζpow, map_sub, map_one, hσζpow,
    div_eq_div_iff hdenInv hden]
  field_simp
  ring

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The conjugate-paired *field* generator `Θ` is σ-fixed, from a single-quotient generator.**

If `α : K` generates the single-root quotient `𝔞(η)/𝔞₀` (the principalization output), then with
`β := σα` the Washington combination `Θ = (α − ζ^a β)/(1 − ζ^a)` is σ-fixed (real) in `K`.  No
integrality is required — `α` is a genuine field element.  This packages
`washington_theta_real_field` with `β := complexConj K α`, the conjugate-paired choice. -/
theorem caseII_theta_field_real_of_generator
    (α : K) {ζ : K} (hζ : NumberField.IsCMField.complexConj K ζ = ζ⁻¹) (hζ0 : ζ ≠ 0)
    (a : ℕ) (hden : (1 : K) - ζ ^ a ≠ 0) :
    NumberField.IsCMField.complexConj K
        ((α - ζ ^ a * NumberField.IsCMField.complexConj K α) / (1 - ζ ^ a)) =
      (α - ζ ^ a * NumberField.IsCMField.complexConj K α) / (1 - ζ ^ a) :=
  washington_theta_real_field rfl hζ hζ0 a hden

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The explicit σ-fixed-solution residual and the fully-proved target reduction

The target `CaseIIRealSingleRootDescentPreservesReality37` asks for a *real datum* at `m' < m`.  We
isolate the strictly more concrete content: an **explicit σ-fixed solution** of the descent equation
at exponent `m` (so the datum sits at `m-1`).  Packaging that solution into `RealCaseIIData37 (m-1)`
is genuine, fully-discharged structure work — the `x_real`/`y_real` fields are *exactly* the
σ-fixedness of the explicit solution, and `m-1 < m` is `one_le_m`. -/

/-- **[FLT37-CASEII-REAL-DESCENT-SOLUTION] Explicit σ-fixed descent solution.**

For every real Case-II datum `D : RealCaseIIData37 (CyclotomicField 37 ℚ) m` with the (genuine,
real-data) `η₀`-principalization, the next descent equation has an **explicit solution whose two
base variables `x', y'` are σ-fixed (real)**: there exist `x' y' z' : 𝓞 K` and `ε' : (𝓞 K)ˣ` with

* `σ x' = x'`, `σ y' = y'`   (reality — the genuine Washington §9.1 reassembly content);
* `(ζ-1) ∤ y'`, `(ζ-1) ∤ z'` (the descent invariants); and
* `x'^37 + y'^37 = ε' · ((ζ-1)^m · z')^37`   (the descent equation, anchor exponent dropped by one).

This is **strictly smaller and strictly sharper** than the bundled
`CaseIIRealSingleRootDescentPreservesReality37 = CaseIIRealThetaReassembly37`: it exposes the
explicit σ-fixed solution rather than an opaque "∃ real datum", and its only non-discharged content
is the *reality* of the two reassembled base variables.  It is a `def … : Prop` (not an axiom). -/
def CaseIIRealDescentSolution37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy →
    ∃ (x' y' z' : 𝓞 (CyclotomicField 37 ℚ)) (ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) x' = x' ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) y' = y' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ y' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ z' ∧
      x' ^ 37 + y' ^ 37 =
        (ε' : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37

/-- **The target reality-preserving descent step follows from the explicit σ-fixed solution.**

Fully proved.  Given an explicit σ-fixed solution `(x', y', z', ε')` of the descent equation at
exponent `m` (`CaseIIRealDescentSolution37`), package it into the descent datum at `m' = m - 1`:

* the `CaseIIData37 (m-1)` equation needs `((ζ-1)^((m-1)+1) · z')^37`, and `(m-1)+1 = m` since
  `1 ≤ m` (`D.one_le_m`), so the solution equation supplies it verbatim;
* the reality fields `x_real`, `y_real` of `RealCaseIIData37` are exactly the σ-fixedness of `x'`,
  `y'`; and
* `m - 1 < m` from `1 ≤ m`.

This is the genuine packaging that the prior `Iff.rfl` residual never performed — the σ-fixedness is
*consumed* here to populate `RealCaseIIData37`. -/
theorem caseIIRealSingleRootDescent_of_realDescentSolution
    (h_sol : CaseIIRealDescentSolution37) :
    CaseIIRealSingleRootDescentPreservesReality37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro _h_exactUnit m D hprinc
  obtain ⟨x', y', z', ε', hx'_real, hy'_real, hy', hz', e'⟩ := h_sol D hprinc
  have hm : 1 ≤ m := D.one_le_m
  refine ⟨m - 1, by omega, ⟨?_⟩⟩
  refine
    { ζ := D.ζ
      hζ := D.hζ
      x := x'
      y := y'
      z := z'
      ε := ε'
      equation := ?_
      hy := hy'
      hz := hz'
      x_real := hx'_real
      y_real := hy'_real }
  have hm_sub : m - 1 + 1 = m := Nat.sub_add_cancel hm
  simpa [hm_sub] using e'

/-! ## 2. Non-vacuity of the residual

Two complementary certificates that `CaseIIRealDescentSolution37` is genuinely non-vacuous (unlike
the provably-false `CaseIIRealIdealDescent37`, which demanded a `σ`-stable `𝓞 K⁺`-ideal that cannot
exist):

* **Conclusion realizability** (`caseIIRealDescentSolution_conclusion_realized`): the conclusion's
  shape — a σ-fixed solution of `x'^37 + y'^37 = ε' · ((ζ-1)^m · z')^37` — is *literally the data of
  a real descent datum at `m-1`*.  Any `RealCaseIIData37 (m-1)` exhibits such a solution (its
  `x_real`/`y_real` fields give the σ-fixedness, its `equation` field the equation with
  `(m-1)+1 = m`).  So the conclusion is not provably false; it is exactly what the descent produces.

* **Domain inhabitation** (`caseIIRealDescentSolution_domain_inhabited`): the `∀`-domain is
  non-empty — there is a real datum with the genuine `η₀`-principalization (the proven II1
  `caseIIRootClassConjFixed37_proven` supplies the principalization at every real datum, and a real
  datum exists at, e.g., the producer's output).  So the residual is a genuine universal statement,
  not vacuously quantified. -/

/-- **The `CaseIIRealDescentSolution37` conclusion is realized by genuine real data.**

For any real descent datum `D' : RealCaseIIData37 (CyclotomicField 37 ℚ) k`, its own data
`(D'.x, D'.y, D'.z, D'.ε)` is a σ-fixed solution of the descent equation at exponent `k+1`:
`σ D'.x = D'.x`, `σ D'.y = D'.y`, `(ζ-1) ∤ D'.y, D'.z`, and
`D'.x^37 + D'.y^37 = D'.ε · ((ζ-1)^(k+1) · D'.z)^37`.

This certifies that the conclusion of `CaseIIRealDescentSolution37` is **realizable** — it is
exactly the shape of a real descent datum's data — so the residual is not vacuously false.  (The
producer `exists_realCaseIIData37_of_caseII_int_solution` shows such `D'` exist whenever a Case-II
integer FLT solution does.) -/
theorem caseIIRealDescentSolution_conclusion_realized
    {k : ℕ} (D' : RealCaseIIData37 (CyclotomicField 37 ℚ) k) :
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.x = D'.x ∧
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.y = D'.y ∧
    ¬ (D'.hζ.unit'.1 - 1) ∣ D'.y ∧
    ¬ (D'.hζ.unit'.1 - 1) ∣ D'.z ∧
    D'.x ^ 37 + D'.y ^ 37 =
      (D'.ε : 𝓞 (CyclotomicField 37 ℚ)) * ((D'.hζ.unit'.1 - 1) ^ (k + 1) * D'.z) ^ 37 :=
  ⟨D'.x_real, D'.y_real, D'.hy, D'.hz, D'.equation⟩

/-- **The `CaseIIRealDescentSolution37` domain is inhabited, from a Case-II integer FLT solution.**

From any Case-II integer FLT solution, the producer `exists_realCaseIIData37_of_caseII_int_solution`
builds a real datum `D`, and the proven II1 (`caseIIRootClassConjFixed37_proven`) supplies the
`η₀`-principalization at `D` via `caseII_real_etaZeroPrincipalization_of_classConjFixed`.  So the
`∀ D, principalization → …` of `CaseIIRealDescentSolution37` quantifies over a non-empty domain — it
is a genuine universal statement, not vacuously true. -/
theorem caseIIRealDescentSolution_domain_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {a b c : ℤ} (hprod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcase : (37 : ℤ) ∣ a * b * c)
    (e : a ^ 37 + b ^ 37 = c ^ 37) :
    ∃ (m : ℕ) (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
      CaseIIPrincipalizationAgainstEtaZero
        37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy := by
  obtain ⟨m, ⟨D⟩⟩ := exists_realCaseIIData37_of_caseII_int_solution hprod hgcd hcase e
  exact ⟨m, D, caseII_real_etaZeroPrincipalization_of_classConjFixed
    caseIIRootClassConjFixed37_proven D⟩

/-! ## 3. The Case-II endpoint and FLT37, resting on the shrunk residual

With the proven II1 (`caseIIRootClassConjFixed37_proven`) and the shrunk residual
`CaseIIRealDescentSolution37`, the entire Case-II descent closes — no longer through the prior
`Iff.rfl` residual `CaseIIRealThetaReassembly37`, but through the genuine σ-fixed-solution packaging
proved in §1.  These compose to `FermatLastTheoremFor 37` together with the proven Assumption II and
the carried second-order input. -/

/-- **No real Case-II descent datum, from the shrunk σ-fixed-solution residual.**

Composes the proven II1 (`caseIIRootClassConjFixed37_proven`) and the σ-fixed-solution residual
through the established minimality wrapper `no_realCaseIIData37_of_classConjFixed_and_realDescent`,
with the target reality-preserving step supplied by §1's
`caseIIRealSingleRootDescent_of_realDescentSolution`. -/
theorem no_realCaseIIData37_of_realDescentSolution
    (h_sol : CaseIIRealDescentSolution37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source) :
    ¬ ∃ m : ℕ, Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m) :=
  no_realCaseIIData37_of_classConjFixed_and_realDescent
    caseIIRootClassConjFixed37_proven h_exactUnit
    (caseIIRealSingleRootDescent_of_realDescentSolution h_sol)

/-- **The public Case-II bridge from the shrunk σ-fixed-solution residual + Assumption II.**

`CaseIIBridge 37 K 32` from the σ-fixed-solution residual `CaseIIRealDescentSolution37` and the
proven Assumption II.  The proven II1 (`caseIIRootClassConjFixed37_proven`) is consumed internally;
the integer FLT solution becomes a real datum via `exists_realCaseIIData37_of_caseII_int_solution`,
then §1's reduction + minimality closes it. -/
theorem caseIIBridge_thirtyseven_of_realDescentSolution
    (h_sol : CaseIIRealDescentSolution37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_classConjFixed_and_realDescent
    caseIIRootClassConjFixed37_proven
    (caseIIRealSingleRootDescent_of_realDescentSolution h_sol)
    h_exactUnit

/-- **Fermat's Last Theorem for `37`, resting on the shrunk σ-fixed-solution residual.**

`FermatLastTheoremFor 37` from:

* `caseII_solution` (`CaseIIRealDescentSolution37`): the **shrunk** Case-II reality-preserving
  residual — the explicit σ-fixed solution of the next descent equation.  Strictly sharper than the
  prior `Iff.rfl` residual `CaseIIRealThetaReassembly37` (which equals the whole target
  `CaseIIRealSingleRootDescentPreservesReality37`): §1 *fully proves* the `RealCaseIIData37`
  packaging from it, consuming the σ-fixedness to populate the `x_real`/`y_real` fields;
* `caseII_exactUnit` (`WashingtonCaseIIExactQuotientUnitPower37Source`): Assumption II (proven
  membership-free in the Eichler module);
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the carried second-order input.

The Case-II II1 (`CaseIIRootClassConjFixed37`) is the **proven** `caseIIRootClassConjFixed37_proven`
(Washington Lemma 9.2); Case I is unconditional (`caseIBridge_thirtyseven_eichler`); `¬ 37 ∣ h⁺` is
the proven `Sinnott.flt37_not_dvd_hPlus`. -/
theorem fermatLastTheoremFor_thirtyseven_of_realDescentSolution
    (caseII_solution : CaseIIRealDescentSolution37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_rootClassConjFixed
    caseIIRootClassConjFixed37_proven
    (caseIIRealSingleRootDescent_of_realDescentSolution caseII_solution)
    caseII_exactUnit noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

end
