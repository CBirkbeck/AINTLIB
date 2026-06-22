import BernoulliRegular.FLT37.Eichler.CaseII.ConjugatePair.ConjPairDescentMinimality

/-!
# [FLT37-CASEII-R2] The σ-conjugate-pair 3-term descent: equation, σ-action, residual

This file attacks `CaseIIConjPairDescentSolution37`
(`CaseIIConjPairDescent.lean`) — the σ-conjugate-pair linear-measure Case-II descent
(Washington, *Cyclotomic Fields*, GTM 83, §9.1, the standard Kummer 3-term descent).

It builds, over a σ-conjugate-pair Case-II datum `D : ConjPairCaseIIData37 K m` (`σx = y`,
`σy = x`):

* §1 — **the 3-term Vandermonde algebraic identity** on the σ-symmetric root triple `{1, ζ, ζ⁻¹}`:
  `(ζ-ζ⁻¹)(x+y) + (ζ⁻¹-1)(x+ζy) + (1-ζ)(x+ζ⁻¹y) = 0` (cofactors of `x` and of `y` each sum to
  `0`).  Pure `ring`.

* §2 — **the descent equation in 6-unit form**, *unconditionally* over `ConjPairCaseIIData37`:
  the proven, clean ConjPair η₀-principalization (`ConjPairCaseIIData37.etaZeroPrincipalization`,
  from Vandiver `37 ∤ h⁺` with **no Lemma-9.2 input**, `CaseIIConjPairII1.lean`) feeds
  `exists_solution_of_etaZeroPrincipalization` to yield
  `ε₁·x'^37 + ε₂·y'^37 = ε₃·((ζ-1)^m·z')^37`, `(ζ-1) ∤ x', y', z'`.  This is genuinely new content
  for the σ-conjugate-pair structure: the descent equation at the dropped exponent `m` exists
  with **no Assumption-II input**.

* §3 — **the σ-action on the Washington radical over a σ-conjugate pair** (the soundness heart):
  `σ(x + y·η) = η⁻¹·(x + y·η)` (`ConjPairCaseIIData37.conj_x_add_y_eta`, already proven), so each
  radical `x + y·η` is *individually* σ-stable up to the unit `η⁻¹` — equivalently `σ𝔞(η) = 𝔞(η)`
  (`ConjPairCaseIIData37.map_rootIdeal`).

* §4 — **the precise residual** `CaseIIConjPairDescentSingleUnitClearing37` (`def … : Prop`, not an
  axiom) isolating the single genuine open sub-step — clearing the descent units `ε₁, ε₂` into the
  σ-conjugate-pair shape demanded by `CaseIIConjPairDescentSolution37` — and the **fully-proved**
  implication `… ⟹ CaseIIConjPairDescentSolution37`, together with non-vacuity.

## The structural soundness finding (recorded honestly; see also the session report)

Over **individually-real** data `RealCaseIIData37` the linear single-root descent at the
inversion-symmetric pair `{η, η⁻¹}` produces a σ-**conjugate** pair `σx' = y'` *because*
`σ𝔞(η) = 𝔞(η⁻¹)` **swaps** the two root ideals (`caseII_map_rootIdeal`,
`caseII_conjPair_descent_vars`).  Over a σ-conjugate **pair** the situation is the *opposite*:
`σ𝔞(η) = 𝔞(η)` is **self-fixed** (`ConjPairCaseIIData37.map_rootIdeal`), so the conjugate of a
generator of `𝔞(η)/𝔞₀` generates the **same** quotient `𝔞(η)/𝔞₀` — not `𝔞(η⁻¹)/𝔞₀`.  Hence the
two descent variables `x' ∼ ρ_{ζ}`, `y' ∼ ρ_{ζ⁻¹}` sit at *distinct* self-fixed root ideals
`𝔞(ζ) ≠ 𝔞(ζ⁻¹)`, each *individually* σ-stable **up to a root of unity** (`σx' = η·x'`, `η³⁷ = 1`):
the natural output of the self-fixed descent is *individually real* (via the **root-of-unity
twist** `caseII_conjPair_zeta_twist_real` of §3′: `σα = η·α ⟹ η¹⁹·α` is real, `2·19 ≡ 1 mod 37`),
**not** the σ-conjugate pair `σx' = y'`.  The conjugate-pairing `σx' = y'` is the *swap*-structure
output and is **not** reachable from self-fixed `ConjPairCaseIIData37` data via the
conjugate-generator route (this is *proved* impossible: `σ(a₁/b₁)` generates `𝔞(η₁)/𝔞₀`, forcing
`η₂ = η₁`, contradicting the descent's `η₁ ≠ η₂`).  So the genuine open content
`CaseIIConjPairUnitClearingStep37` (§4) is exactly
the conjugate-pairing reconstruction on top of the proved 6-unit descent equation — the descent
derivation itself, the 3-term Vandermonde, the σ-self-stability, and the twist realisation are all
discharged here.  The natural self-fixed descent instead lands in *individually-real*
(`RealCaseIIData37`) form — the Real↔ConjPair 2-cycle partner of the first step
(`CaseIIConjPairFirstStep.lean`).

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (the 3-term descent), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The 3-term Vandermonde identity on the σ-symmetric root triple `{1, ζ, ζ⁻¹}`

The cleanest expression of the Case-II linear descent: a single algebraic identity relating the
three radicals `x+y`, `x+ζy`, `x+ζ⁻¹y` with cofactors built from the roots `{1, ζ, ζ⁻¹}` that
**sum to zero on both `x` and `y`**.  This is the σ-symmetric Vandermonde underlying the descent;
it is a pure `ring` identity, valid for any `ζ` with `ζ³⁷ = 1` (in fact for any ring elements).  It
specialises the abstract 3-term Vandermonde to the inversion-symmetric triple so that the σ-action
`σ(x+yζᵃ) = ζ⁻ᵃ(x+yζᵃ)` (§3) acts cleanly. -/

omit [NumberField K] [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] in
/-- **The σ-symmetric 3-term Vandermonde (linear-dependence) identity.**  For *any* ring elements
`x, y, ζ, ζ'`, the three radicals at `{1, ζ, ζ'}` satisfy

  `(ζ - ζ')·(x + y) + (ζ' - 1)·(x + ζ·y) + (1 - ζ)·(x + ζ'·y) = 0`.

The cofactors `(ζ-ζ'), (ζ'-1), (1-ζ)` are the Cramer/Vandermonde cofactors of the three roots
`{1, ζ, ζ'}`; being three linear forms in the two variables `x, y`, the radicals are linearly
dependent with exactly these cofactors.  Cofactor of `x`: `(ζ-ζ') + (ζ'-1) + (1-ζ) = 0`; cofactor of
`y`: `(ζ-ζ')·1 + (ζ'-1)·ζ + (1-ζ)·ζ' = 0` (`ζ'ζ - ζζ' = 0` in a commutative ring).  Pure `ring`. -/
theorem caseII_conjPair_three_term_vandermonde (x y ζ ζ' : 𝓞 K) :
    (ζ - ζ') * (x + y) + (ζ' - 1) * (x + ζ * y) + (1 - ζ) * (x + ζ' * y) = 0 := by
  ring

/-- **The 3-term Vandermonde for a σ-conjugate-pair datum at the inversion triple `{1, ζ, ζ⁻¹}`.**

Specialises `caseII_conjPair_three_term_vandermonde` with `ζ = D.hζ.unit'` (a primitive 37-th root)
and `ζ' = ζ³⁶ = ζ⁻¹`.  The three radicals are `D.x + D.y` (root `1`), `D.x + D.y·ζ` (root `ζ`),
`D.x + D.y·ζ⁻¹` (root `ζ⁻¹`); the triple `{1, ζ, ζ⁻¹}` is the σ-symmetric one (`σ` fixes `1` and
swaps `ζ ↔ ζ⁻¹`).  This is the concrete linear-dependence relation among the σ-symmetric radicals.
(No claim that the anchor `D.etaZero = 1`; the identity is purely algebraic.) -/
theorem ConjPairCaseIIData37.three_term_vandermonde {m : ℕ} (D : ConjPairCaseIIData37 K m) :
    ((D.hζ.unit'.1 : 𝓞 K) - D.hζ.unit'.1 ^ 36) * (D.x + D.y) +
        ((D.hζ.unit'.1 ^ 36 : 𝓞 K) - 1) * (D.x + D.hζ.unit'.1 * D.y) +
      ((1 : 𝓞 K) - D.hζ.unit'.1) * (D.x + D.hζ.unit'.1 ^ 36 * D.y) = 0 := by
  -- The abstract identity has `ζ·y` ordering; the concrete goal has `ζ·y` too — match by `ring`.
  have := caseII_conjPair_three_term_vandermonde (K := K) D.x D.y D.hζ.unit'.1
    (D.hζ.unit'.1 ^ 36)
  linear_combination this

/-! ## 2. The descent equation in 6-unit form, unconditional over `ConjPairCaseIIData37`

The proven ConjPair η₀-principalization (`ConjPairCaseIIData37.etaZeroPrincipalization`, clean,
Vandiver `37 ∤ h⁺`, **no Lemma-9.2 input**) is exactly the input
`exists_solution_of_etaZeroPrincipalization` needs.  So the next descent equation at the dropped
exponent `m` exists — in the 6-unit form `ε₁·x'^37 + ε₂·y'^37 = ε₃·((ζ-1)^m·z')^37` — over **every**
σ-conjugate-pair datum, with no Assumption-II input.  This is genuinely new content for the
σ-conjugate-pair structure (the existing `caseII_descent_equation` is the *pair-product* /
norm-doubled form; this is the *linear* form). -/

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **The 6-unit Case-II descent equation, unconditional over `ConjPairCaseIIData37`.**

For every σ-conjugate-pair datum `D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m`, the next
descent equation has a solution in 6-unit form:

  `∃ x' y' z' (ε₁ ε₂ ε₃ : units), (ζ-1) ∤ x', y', z' ∧
     ε₁·x'^37 + ε₂·y'^37 = ε₃·((ζ-1)^m·z')^37`.

Proof: the proven ConjPair η₀-principalization (`ConjPairCaseIIData37.etaZeroPrincipalization`)
supplies `CaseIIPrincipalizationAgainstEtaZero`, the exact hypothesis of
`exists_solution_of_etaZeroPrincipalization` (the flt-regular descent reassembly at the three
adjacent roots `η₀, η₀ζ, η₀ζ²`).  No reality, no Assumption-II, no Lemma-9.2 input. -/
theorem ConjPairCaseIIData37.exists_sixUnit_descent_equation
    {m : ℕ} (D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m) :
    ∃ (x' y' z' : 𝓞 (CyclotomicField 37 ℚ)) (ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ¬ (D.hζ.unit'.1 - 1) ∣ x' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ y' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ z' ∧
      (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 + (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero (37 : ℕ) := ⟨by decide⟩
  exact exists_solution_of_etaZeroPrincipalization (p := 37) (K := CyclotomicField 37 ℚ)
    (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy D.hz D.etaZeroPrincipalization

/-! ## 3. The σ-action over a σ-conjugate pair: the Washington radical is self-stable

The central soundness fact, already proved as `ConjPairCaseIIData37.conj_x_add_y_eta`:
`σ(x + y·η) = η⁻¹·(x + y·η)`, so the radical is *individually* σ-stable up to the root of unity
`η⁻¹`.  At the ideal level this is the self-fixedness `σ𝔞(η) = 𝔞(η)`
(`ConjPairCaseIIData37.map_rootIdeal`).  We record the element-level associate explicitly, then
(§3′) the **root-of-unity twist** that turns any σ-self-stable element into a σ-fixed (real) one:
this shows the self-fixed descent's variables are individually σ-stable up to a `ζ`-power, hence
*individually real* after twisting — precisely *why* the σ-conjugate-pair relation `σx' = y'` is
not the natural output and the conjugate-pairing must be reconstructed by the unit clearing (§4). -/

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **The Washington radical of a σ-conjugate pair is self-associate under σ.**  `σ(x+yη)` and
`x+yη` generate the same principal ideal: `σ(x+yη) = η³⁶·(x+yη)` with `η³⁶` a unit.  Element-level
restatement of `ConjPairCaseIIData37.conj_x_add_y_eta` packaged as `Associated`. -/
theorem ConjPairCaseIIData37.associated_conj_x_add_y_eta {m : ℕ} (D : ConjPairCaseIIData37 K m)
    {η : 𝓞 K} (hη : η ^ 37 = 1) :
    Associated (ringOfIntegersComplexConj K (D.x + D.y * η)) (D.x + D.y * η) := by
  rw [D.conj_x_add_y_eta hη]
  -- `η³⁶` is a unit (inverse `η`, since `η³⁶·η = η³⁷ = 1`).
  have hu : IsUnit ((η : 𝓞 K) ^ 36) :=
    IsUnit.of_mul_eq_one η (by rw [← pow_succ, hη])
  exact associated_unit_mul_left (D.x + D.y * η) (η ^ 36) hu

/-! ### 3′. The root-of-unity twist: a σ-self-stable element is *real* after a `ζ`-power twist

The decisive elementary mechanism for the σ-conjugate-pair descent.  If `σα = η·α` for a 37-th root
of unity `η` (the σ-self-stability of §3 at the element level — every descent variable satisfies
this), then the twist `η¹⁹·α` is **σ-fixed (real)**, because `2·19 ≡ 1 (mod 37)` (so `19 = 2⁻¹` in
`ℤ/37`).  Concretely `σ(η¹⁹·α) = η⁻¹⁹·(η·α) = η¹⁻¹⁹·α`, and re-expressing `α = η⁻¹⁹·(η¹⁹α)` gives
`σ(η¹⁹·α) = η¹⁻³⁸·(η¹⁹α) = η⁻³⁷·(η¹⁹α) = η¹⁹α` (as `η³⁷ = 1`).

This is what converts the σ-self-stable descent variables (`σx' = η·x'`) into the *individually
real* form — the genuine output the self-fixed-ideal descent produces (the Real↔ConjPair 2-cycle
partner of the first step), as opposed to the σ-conjugate pair `σx' = y'` produced by the
*swap*-structured individually-real descent.  No deep input: pure root-of-unity arithmetic. -/

omit [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **The `ζ`-power twist realises a σ-self-stable element.**  For a 37-th root of unity `η`
(`η^37 = 1`) and `α : 𝓞 K` with `σα = η·α`, the twist `η^19·α` is σ-fixed:
`σ(η^19·α) = η^19·α`.  Pure root-of-unity arithmetic (`2·19 ≡ 1 mod 37`, `η^37 = 1`). -/
theorem caseII_conjPair_zeta_twist_real {η α : 𝓞 K} (hη : η ^ 37 = 1)
    (hα : ringOfIntegersComplexConj K α = η * α) :
    ringOfIntegersComplexConj K (η ^ 19 * α) = η ^ 19 * α := by
  -- `σ(η) = η^36 = η⁻¹`, so `σ(η^19) = η^{36·19}`.
  have hση : ringOfIntegersComplexConj K η = η ^ 36 :=
    caseII_ringOfIntegersComplexConj_root_of_unity hη
  rw [map_mul, map_pow, hση, hα]
  -- Goal: `(η^36)^19 * (η * α) = η^19 * α`, i.e. `η^{36·19+1} * α = η^19 * α`.
  -- `36·19 + 1 = 685 = 37·18 + 19`, so `η^685 = η^19`.
  rw [← pow_mul]
  rw [show (η : 𝓞 K) ^ (36 * 19) * (η * α) = η ^ (36 * 19 + 1) * α from by ring]
  rw [show (36 * 19 + 1 : ℕ) = 37 * 18 + 19 from by norm_num, pow_add, pow_mul, hη, one_pow,
    one_mul]

/-! ## 4. The precise single-unit-clearing residual and the *strictly-shrinking* reduction

The 6-unit descent equation (§2) is `ε₁·x'^37 + ε₂·y'^37 = ε₃·((ζ-1)^m·z')^37`, **proved** over
every σ-conjugate-pair datum.  The genuine remaining content of `CaseIIConjPairDescentSolution37` is
*only* the clearing of the two leading units `ε₁, ε₂` into the clean σ-conjugate-pair shape.  We
isolate that clearing as a residual whose hypothesis is **exactly the proved 6-unit equation**, so
the descent derivation is *removed* from the residual — it is strictly smaller than the def (it no
longer re-derives the equation), and the reduction `… ⟹ CaseIIConjPairDescentSolution37` feeds in
the §2 equation.

This split is faithful to Washington §9.1: the descent (the 6-unit equation) is the structural step,
and the single-unit-clearing (`flt37_antiFixed_radical_isPthPower` / Assumption II — `ηₐ/η_b` are
37th powers, §3 σ-self-stability) is the remaining analytic content. -/

/-- **[FLT37-CASEII-CONJPAIR-UNIT-CLEARING-STEP] The σ-conjugate-pair unit-clearing step.**

Hypothesis-form residual: *given* a 6-unit Case-II descent equation
`ε₁·x'^37 + ε₂·y'^37 = ε₃·((ζ-1)^m·z')^37` with `(ζ-1) ∤ x', y', z'` over a σ-conjugate-pair datum
`D` (exactly the data the **proved** `ConjPairCaseIIData37.exists_sixUnit_descent_equation` gives),
the two leading units can be cleared into a clean σ-conjugate-pair solution: there exist
`x'' y'' z''`, `ε''` with `σx'' = y''`, `σy'' = x''`, `(ζ-1) ∤ y'', z''`, and
`x''^37 + y''^37 = ε''·((ζ-1)^m·z'')^37`.

**Strictly smaller** than `CaseIIConjPairDescentSolution37`: the descent derivation is supplied as a
*hypothesis* (the 6-unit equation), so this residual contains *only* the unit clearing — it does not
re-derive the descent equation (which §2 proves).  A `def … : Prop` (not an axiom). -/
def CaseIIConjPairUnitClearingStep37 : Prop :=
  ∀ {m : ℕ} (D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m)
    (x' y' z' : 𝓞 (CyclotomicField 37 ℚ)) (ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ),
    ¬ (D.hζ.unit'.1 - 1) ∣ x' →
    ¬ (D.hζ.unit'.1 - 1) ∣ y' →
    ¬ (D.hζ.unit'.1 - 1) ∣ z' →
    (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 + (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
      (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37 →
    ∃ (x'' y'' z'' : 𝓞 (CyclotomicField 37 ℚ)) (ε'' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) x'' = y'' ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) y'' = x'' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ y'' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ z'' ∧
      x'' ^ 37 + y'' ^ 37 =
        (ε'' : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z'') ^ 37

/-- **`CaseIIConjPairDescentSolution37` from the unit-clearing step — the strictly-shrinking
reduction (fully proved).**

Given the unit-clearing step `CaseIIConjPairUnitClearingStep37`, the full descent residual
`CaseIIConjPairDescentSolution37` follows: for every σ-conjugate-pair datum `D`, the **proved** §2
descent equation `ConjPairCaseIIData37.exists_sixUnit_descent_equation` supplies the exact 6-unit
hypothesis the clearing step consumes, and the clearing step delivers the clean σ-conjugate-pair
solution.

This is a *genuine* reduction (not an `Iff.rfl` re-wrap): the proved 6-unit equation is consumed, so
the open content shrinks to the single-unit-clearing step alone. -/
theorem caseIIConjPairDescentSolution37_of_unitClearingStep
    (h_clear : CaseIIConjPairUnitClearingStep37) :
    CaseIIConjPairDescentSolution37 := by
  intro m D
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ := D.exists_sixUnit_descent_equation
  exact h_clear D x' y' z' ε₁ ε₂ ε₃ hx' hy' hz' e'

/-- **No σ-conjugate-pair Case-II datum, from the unit-clearing step.**  Composes the
strictly-shrinking reduction `caseIIConjPairDescentSolution37_of_unitClearingStep` with the
established minimality wrapper `no_conjPairCaseIIData37_of_descentSolution`. -/
theorem no_conjPairCaseIIData37_of_unitClearingStep
    (h_clear : CaseIIConjPairUnitClearingStep37) :
    ¬ ∃ m : ℕ, Nonempty (ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m) :=
  no_conjPairCaseIIData37_of_descentSolution
    (caseIIConjPairDescentSolution37_of_unitClearingStep h_clear)

/-! ## 5. Non-vacuity of the unit-clearing step

The unit-clearing step is genuinely non-vacuous: its **hypothesis** (the 6-unit equation) is
satisfiable (the proved §2 equation), and its **conclusion** shape is realized by genuine
σ-conjugate-pair data at `m-1`. -/

/-- **The unit-clearing step's hypothesis is satisfiable** — the proved §2 6-unit descent equation
exhibits the exact data the step quantifies over.  Certifies the step is not vacuously true (its
`∀`-domain is inhabited). -/
theorem caseIIConjPairUnitClearingStep_hypothesis_satisfiable
    {m : ℕ} (D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m) :
    ∃ (x' y' z' : 𝓞 (CyclotomicField 37 ℚ)) (ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ¬ (D.hζ.unit'.1 - 1) ∣ x' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ y' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ z' ∧
      (ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 + (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37 :=
  D.exists_sixUnit_descent_equation

/-- **The unit-clearing step's conclusion shape is realized by genuine σ-conjugate-pair data.**  Any
`D' : ConjPairCaseIIData37 k` exhibits a clean σ-conjugate-pair solution at exponent `k+1` (its own
`(x, y, z, ε)` with the `x_conj`/`y_conj` fields).  Certifies the conclusion is not provably false.
Reuses `caseIIConjPairDescentSolution_conclusion_realized`. -/
theorem caseIIConjPairUnitClearingStep_conclusion_realized
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
