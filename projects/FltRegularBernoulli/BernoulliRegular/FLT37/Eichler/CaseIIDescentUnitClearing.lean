import BernoulliRegular.FLT37.Eichler.CaseIIConjPairThreeTermDescent

/-!
# [FLT37-CASEII] Discharging the Case-II descent **unit clearing** via Assumption II

This file isolates and **fully discharges** the *unit-clearing* sub-step of the Case-II descent —
the step the project tracking variously calls "single-unit reduction", "clearing the two leading
units `ε₁, ε₂`", and the `h_unit` hypothesis of `exists_solution'_of_etaZeroSpanSingletons` — and
pins down, with the `η ↔ ε` identification **verified against the actual descent-equation
construction**, exactly what remains after the clearing.

## What is PROVEN here

* §1 — `caseII_clearLeadingUnits` : the pure-algebra clearing.  For *any* six-unit Case-II
  descent equation `ε₁·X³⁷ + ε₂·Y³⁷ = ε₃·W³⁷` over `𝓞 K` together with a `37`-th root `δ` of the
  leading-unit quotient `ε₁/ε₂ = δ³⁷` (this is *exactly* the conclusion of Assumption II,
  `WashingtonCaseIIExactQuotientUnitPower37Source`), the equation collapses to the **single-unit**
  form
    `(δ·X)³⁷ + Y³⁷ = (ε₃/ε₂)·W³⁷`.
  No descent structure is used — this is the literal algebra of `exists_solution'`.

* §2 — `ConjPairCaseIIData37.exists_clean_descent_equation` : assembling §1 with the **proven**
  six-unit equation (`ConjPairCaseIIData37.exists_sixUnit_descent_equation`) and **Assumption II**
  (applied to `D.toCaseIIData37`), over *every* σ-conjugate-pair datum the next descent equation
  exists in the **clean single-unit form**
    `X³⁷ + Y³⁷ = ε'·((ζ−1)^m·Z)³⁷`,  `(ζ−1) ∤ X, Y, Z`.
  This is the task's "clean form": the two leading descent units **are cleared by Assumption II**.
  It is genuinely new (it removes the leading units from the equation), unconditional on the
  σ-conjugate-pair structure modulo the single hypothesis
  `WashingtonCaseIIExactQuotientUnitPower37Source`.

## The `η ↔ ε` identification (verified, soundness-critical)

The task's clearing rests on the claim that Assumption II's "`η_a/η_b` are `37`-th powers" is the
same statement as "`ε₁/ε₂` is a `37`-th power".  This is **correct and verified** here against the
construction:

* The six-unit equation is built by `exists_solution_of_etaZeroPrincipalization`
  (`SpecificChain.lean`) via `formula_of_etaZeroSpanSingletons`.  There the leading unit on `X³⁷`
  is `ε₁ = (η₂−η₀)·U₁·u₁` and on `Y³⁷` is `ε₂ = (η₀−η₁)·U₂·u₂`, where `Uᵢ =
  associated_eta_zero_unit_of_spanSingleton … ηᵢ` is the associate-witness unit packaging the
  generator relation `𝔞(ηᵢ)·(bᵢ) = 𝔞₀·(aᵢ)` (Washington's `ηᵢ = aᵢ/bᵢ`-content unit), and `uᵢ` is
  the root-difference associate unit.  Thus `ε₁/ε₂` is precisely the ratio of the two anchored
  generator units — Washington's `η_a/η_b` (the per-root unit of `x+ζᵃy = η_a·λ^{c_a}·ρ_a³⁷`).
  Assumption II `WashingtonCaseIIExactQuotientUnitPower37Source` states **exactly** this ratio is a
  `37`-th power.  We do **not** re-derive it; we consume its conclusion `∃ δ, ε₁/ε₂ = δ³⁷`
  verbatim, which is why §1 takes `ε₁/ε₂ = δ³⁷` as a hypothesis and §2 supplies it from
  Assumption II.  No over-statement: the clearing is *only* the algebra; the `37`-th-power content
  is Assumption II's, applied at the genuine descent units.

## What REMAINS after the clearing (the precise TRUE residual)

The clean equation `X³⁷ + Y³⁷ = ε'·((ζ−1)^m·Z)³⁷` is at the **linear** measure `(ζ−1)^m`.  To
package it into a descent datum at `m−1` one needs a **reality**/σ-structure on the cleared pair
`(X, Y) = (δ·x', y')`:

* For a σ-conjugate-pair datum (`ConjPairCaseIIData37`, the `of_conjPairSolution` constructor) one
  needs `σX = Y`, `σY = X`.
* For an individually-real datum (`RealCaseIIData37`) one needs `σX = X`, `σY = Y`.

Neither holds for the cleared `(δ·x', y')` *as produced*: the descent equation's variables
`x' = a₁b₂`, `y' = a₂b₁` are built from generators of `𝔞(η₁)/𝔞₀`, `𝔞(η₂)/𝔞₀` at the **adjacent
non-inversion roots** `η₁ = η₀ζ`, `η₂ = η₀ζ²` (`exists_solution_of_etaZeroPrincipalization`), which
are *not* an inversion-symmetric pair `{η, η⁻¹}` — so there is no σ-swap relating `x'` and `y'`, and
the clearing factor `δ` (a `37`-th root of a unit) carries no canonical σ-action either.  This is
the genuine remaining content — the reality reconciliation — isolated cleanly as
`CaseIIDescentCleanRealityResidual37` (§3).  It is **not** the unit clearing (that is discharged
here); it is the σ-structure of the cleared variables, which the project elsewhere tracks as the
"structural heart" R2 and which the proven measure certificate
`caseII_realCaseIIData37_lambda_content_mul_p` shows cannot be met in the `RealCaseIIData37` frame
at the conjugate-norm (doubled) measure.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (the descent), Thm 9.4.
* `exists_solution'_of_etaZeroSpanSingletons` (`SpecificChain.lean`): the `exists_solution'`
  clearing whose `h_unit` hypothesis is the `37`-th-power-of-`ε₁/ε₂` content.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The pure-algebra clearing of the two leading descent units

The single piece of genuine algebra in `exists_solution'`: given the six-unit equation and a
`37`-th root `δ` of `ε₁/ε₂`, fold `δ` into `X` and `ε₂⁻¹` through, landing the single-unit form. -/

/-- **`(ζ−1)` does not divide a unit multiple of a `(ζ−1)`-coprime element.**  Since `δ` is a unit
and `ζ−1` is prime, `(ζ−1) ∤ δ·x` follows from `(ζ−1) ∤ x` (a prime dividing `δ·x` would divide one
factor, but it cannot divide the unit `δ`).  The coprimality of the cleared first variable
`δ·x'`. -/
theorem caseII_zeta_sub_one_not_dvd_unit_mul {m : ℕ}
    (D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m)
    (δ : (𝓞 (CyclotomicField 37 ℚ))ˣ) {x : 𝓞 (CyclotomicField 37 ℚ)}
    (hx : ¬ (D.hζ.unit'.1 - 1) ∣ x) :
    ¬ (D.hζ.unit'.1 - 1) ∣ (δ : 𝓞 (CyclotomicField 37 ℚ)) * x := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact (D.hζ.zeta_sub_one_prime').not_dvd_mul
    (fun h => absurd (isUnit_of_dvd_unit h δ.isUnit) (D.hζ.zeta_sub_one_prime').not_unit) hx

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **Clearing the two leading units of a six-unit Case-II descent equation.**

For any `X Y W : 𝓞 K`, units `ε₁ ε₂ ε₃ δ : (𝓞 K)ˣ` with the six-unit equation
`ε₁·X³⁷ + ε₂·Y³⁷ = ε₃·W³⁷` and the `37`-th-power identity `ε₁/ε₂ = δ³⁷` (the conclusion of
Assumption II at the genuine descent units), the equation collapses to the single-unit form

  `(δ·X)³⁷ + Y³⁷ = (ε₃/ε₂)·W³⁷`.

Pure algebra: divide the equation by `ε₂` (a unit) and substitute `ε₁/ε₂ = δ³⁷`, then
`δ³⁷·X³⁷ = (δX)³⁷`.  This is exactly the `exists_solution'` reduction
(`exists_solution'_of_etaZeroSpanSingletons`), abstracted away from the descent so that the `η ↔ ε`
identification (see the module docstring) is the *only* place Assumption II enters. -/
theorem caseII_clearLeadingUnits {K : Type} [Field K] [NumberField K]
    {X Y W : 𝓞 K} {ε₁ ε₂ ε₃ δ : (𝓞 K)ˣ}
    (heq : (ε₁ : 𝓞 K) * X ^ 37 + (ε₂ : 𝓞 K) * Y ^ 37 = (ε₃ : 𝓞 K) * W ^ 37)
    (hδ : ε₁ / ε₂ = δ ^ 37) :
    ((δ : 𝓞 K) * X) ^ 37 + Y ^ 37 = ((ε₃ / ε₂ : (𝓞 K)ˣ) : 𝓞 K) * W ^ 37 := by
  -- `(δX)³⁷ = δ³⁷·X³⁷ = (ε₁/ε₂)·X³⁷`.
  have hδpow : ((δ : 𝓞 K) * X) ^ 37 = ((ε₁ / ε₂ : (𝓞 K)ˣ) : 𝓞 K) * X ^ 37 := by
    rw [mul_pow, ← Units.val_pow_eq_pow_val, ← hδ]
  rw [hδpow]
  -- Divide `heq` through by `ε₂` (a unit); same rewrite sequence as the proven `exists_solution'`
  -- clearing (`SpecificChain.lean`).
  rw [← mul_right_inj' ε₂.isUnit.ne_zero, mul_add, ← mul_assoc,
    ← Units.val_mul, mul_div_cancel, ← mul_assoc, ← Units.val_mul,
    mul_div_cancel]
  exact heq

/-! ## 2. The clean single-unit descent equation over a σ-conjugate-pair datum, via Assumption II

Assembling §1 with the **proven** six-unit equation and **Assumption II**, the next descent equation
exists in the clean single-unit form over every σ-conjugate-pair datum.  This is the task's
"clean form" `X³⁷ + Y³⁷ = ε'·((ζ−1)^m·Z)³⁷` — the two leading units **cleared by Assumption II**. -/

/-- **The clean (single-unit) Case-II descent equation over `ConjPairCaseIIData37`, via
Assumption II.**

For every σ-conjugate-pair datum `D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m`, assuming
Assumption II (`WashingtonCaseIIExactQuotientUnitPower37Source`), the next descent equation has a
solution in **clean single-unit form**:

  `∃ X Y Z (ε' : units), (ζ−1) ∤ X, Y, Z ∧ X³⁷ + Y³⁷ = ε'·((ζ−1)^m·Z)³⁷`.

Proof: the **proven** `ConjPairCaseIIData37.exists_sixUnit_descent_equation` supplies
`ε₁·x'³⁷ + ε₂·y'³⁷ = ε₃·((ζ−1)^m·z')³⁷` with `(ζ−1) ∤ x', y', z'`; **Assumption II** (applied to
`D.toCaseIIData37`, the genuine descent units — see the `η ↔ ε` paragraph in the module docstring)
gives `δ` with `ε₁/ε₂ = δ³⁷`; and `caseII_clearLeadingUnits` collapses to
`(δ·x')³⁷ + y'³⁷ = (ε₃/ε₂)·((ζ−1)^m·z')³⁷`.  Coprimality `(ζ−1) ∤ δ·x'` holds since `δ` is a unit.

This **fully discharges the unit clearing** — the step the task identifies as "the missing link".
What remains (the reality/σ-structure of `(X, Y) = (δx', y')`) is isolated in §3. -/
theorem ConjPairCaseIIData37.exists_clean_descent_equation
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32) :
    ∃ (X Y Z : 𝓞 (CyclotomicField 37 ℚ)) (ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ¬ (D.hζ.unit'.1 - 1) ∣ X ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ Y ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ Z ∧
      X ^ 37 + Y ^ 37 =
        (ε' : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * Z) ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- The proven six-unit descent equation over the σ-conjugate pair.
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ := D.exists_sixUnit_descent_equation
  -- Assumption II at the genuine descent units `ε₁/ε₂`.
  obtain ⟨δ, hδ⟩ :=
    caseII_exact_quotient_unitPower37 h_exactUnit hV hSO D.toCaseIIData37 hx' hy' hz' e'
  -- Clear the two leading units (pure algebra).
  exact ⟨(δ : 𝓞 (CyclotomicField 37 ℚ)) * x', y', z', ε₃ / ε₂,
    caseII_zeta_sub_one_not_dvd_unit_mul D δ hx', hy', hz', caseII_clearLeadingUnits e' hδ⟩

/-! ## 3. The precise residual remaining after the clearing: reality of the cleared pair

The clearing of §2 leaves a clean single-unit equation at linear measure `(ζ−1)^m`.  Packaging it
into a descent datum at `m−1` requires a reality/σ-structure on the cleared pair `(X, Y)`.  We name
this residual precisely, and certify it is genuine (its hypothesis is exactly the **proven** §2
clean equation; its conclusion is the σ-conjugate-pair reality the `of_conjPairSolution` constructor
consumes). -/

/-- **[FLT37-CASEII-CLEAN-REALITY-RESIDUAL] The reality residual after unit clearing.**

*Given* a clean single-unit Case-II descent equation `X³⁷ + Y³⁷ = ε'·((ζ−1)^m·Z)³⁷` with
`(ζ−1) ∤ X, Y, Z` over a σ-conjugate-pair datum `D` (exactly the data the **proven**
`ConjPairCaseIIData37.exists_clean_descent_equation` produces from Assumption II), the cleared pair
can be put into σ-conjugate-pair form: there exist `X'' Y'' Z''`, `ε''` with `σX'' = Y''`,
`σY'' = X''`, `(ζ−1) ∤ Y'', Z''`, and `X''³⁷ + Y''³⁷ = ε''·((ζ−1)^m·Z'')³⁷`.

This residual is **strictly smaller** than `CaseIIConjPairUnitClearingStep37`
(`CaseIIConjPairThreeTermDescent.lean`): its hypothesis is the *already-unit-cleared*
single-unit equation (no leading `ε₁, ε₂`), so the unit clearing is **removed** from the residual —
it is supplied by §2.  The only remaining content is the σ-structure of the cleared variables (the
"structural heart" R2).  A `def … : Prop` (**not** an axiom). -/
def CaseIIDescentCleanRealityResidual37 : Prop :=
  ∀ {m : ℕ} (D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m)
    (X Y Z : 𝓞 (CyclotomicField 37 ℚ)) (ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
    ¬ (D.hζ.unit'.1 - 1) ∣ X →
    ¬ (D.hζ.unit'.1 - 1) ∣ Y →
    ¬ (D.hζ.unit'.1 - 1) ∣ Z →
    X ^ 37 + Y ^ 37 =
      (ε' : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * Z) ^ 37 →
    ∃ (X'' Y'' Z'' : 𝓞 (CyclotomicField 37 ℚ)) (ε'' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) X'' = Y'' ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) Y'' = X'' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ Y'' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ Z'' ∧
      X'' ^ 37 + Y'' ^ 37 =
        (ε'' : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * Z'') ^ 37

/-- **`CaseIIConjPairUnitClearingStep37` from the clean-reality residual + Assumption II.**

The σ-conjugate-pair unit-clearing step of `CaseIIConjPairThreeTermDescent.lean` follows from the
**strictly-smaller** clean-reality residual `CaseIIDescentCleanRealityResidual37` together with
Assumption II: given a six-unit equation, Assumption II + `caseII_clearLeadingUnits` produce the
clean single-unit equation (the unit clearing, **discharged here**), which the clean-reality
residual then puts into σ-conjugate-pair form.

This is a *genuine* reduction: the leading units `ε₁, ε₂` are removed (cleared by Assumption II), so
the open content shrinks from "clear units **and** reconcile reality" to "reconcile reality of the
already-cleared pair". -/
theorem caseIIConjPairUnitClearingStep37_of_cleanReality
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (h_reality : CaseIIDescentCleanRealityResidual37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32) :
    CaseIIConjPairUnitClearingStep37 := by
  intro m D x' y' z' ε₁ ε₂ ε₃ hx' hy' hz' e'
  -- Assumption II clears the leading units into the clean single-unit equation.
  obtain ⟨δ, hδ⟩ :=
    caseII_exact_quotient_unitPower37 h_exactUnit hV hSO D.toCaseIIData37 hx' hy' hz' e'
  -- The clean-reality residual reconciles the cleared pair into σ-conjugate-pair form.
  exact h_reality D _ y' z' (ε₃ / ε₂)
    (caseII_zeta_sub_one_not_dvd_unit_mul D δ hx') hy' hz' (caseII_clearLeadingUnits e' hδ)

/-! ## 4. Non-vacuity of the clean-reality residual

The residual's **hypothesis** (the clean single-unit equation) is satisfiable — it is the **proven**
§2 output, contingent only on Assumption II — and its **conclusion** shape (a σ-conjugate-pair clean
solution) is realized by genuine σ-conjugate-pair data at `m`.  So the residual is neither vacuously
true (its `∀`-domain is inhabited under Assumption II) nor provably false. -/

/-- **Hypothesis satisfiable.**  Under Assumption II, the clean single-unit equation quantified over
by `CaseIIDescentCleanRealityResidual37` is exhibited by the **proven**
`ConjPairCaseIIData37.exists_clean_descent_equation`.  Certifies the residual genuinely consumes
inhabited input. -/
theorem caseIIDescentCleanRealityResidual37_hyp_satisfiable
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32) :
    ∃ (X Y Z : 𝓞 (CyclotomicField 37 ℚ)) (ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ¬ (D.hζ.unit'.1 - 1) ∣ X ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ Y ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ Z ∧
      X ^ 37 + Y ^ 37 =
        (ε' : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * Z) ^ 37 :=
  D.exists_clean_descent_equation h_exactUnit hV hSO

/-- **Conclusion realized.**  The σ-conjugate-pair clean-solution shape of
`CaseIIDescentCleanRealityResidual37` is realized by any σ-conjugate-pair datum `D'` at level `k`
(its own `(x, y, z, ε)` with the `x_conj`/`y_conj` σ-swap fields).  Certifies the conclusion is not
provably false.  Reuses `caseIIConjPairDescentSolution_conclusion_realized`. -/
theorem caseIIDescentCleanRealityResidual37_conclusion_realized
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {k : ℕ} (D' : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) k) :
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.x = D'.y ∧
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.y = D'.x ∧
    ¬ (D'.hζ.unit'.1 - 1) ∣ D'.y ∧
    ¬ (D'.hζ.unit'.1 - 1) ∣ D'.z ∧
    D'.x ^ 37 + D'.y ^ 37 =
      (D'.ε : 𝓞 (CyclotomicField 37 ℚ)) * ((D'.hζ.unit'.1 - 1) ^ (k + 1) * D'.z) ^ 37 :=
  caseIIConjPairDescentSolution_conclusion_realized D'

end BernoulliRegular.FLT37.Eichler

end

end
