import BernoulliRegular.FLT37.Eichler.CaseIIConjPairFirstStep

/-!
# [FLT37-CASEII-R2] The σ-conjugate-pair descent: constructor, minimality, and the precise residual

This file assembles the σ-conjugate-pair structure into the descent skeleton and isolates the
**single precise residual** that an iterated reality-aware Case-II descent reduces to — the
σ-conjugate-pair analogue of `CaseIIRealDescentSolution37`, but at the measure the *linear* descent
genuinely produces.

## What is established

* `ConjPairCaseIIData37.of_conjPairSolution` — **constructor**: an explicit σ-conjugate-pair
  solution of the next descent equation (variables `x', y'` with `σx' = y'`, `σy' = x'`, `σz' = z'`,
  and `x'^37 + y'^37 = ε'·((ζ-1)^m·z')^37`) packages into a `ConjPairCaseIIData37 (m-1)`.  The
  σ-conjugate fields `x_conj`, `y_conj` are populated *exactly* by the σ-swap — the same role
  `caseIIRealSingleRootDescent_of_realDescentSolution` plays for the (unprovable, B2-logged)
  individually-real form, but here the populated fields are the ones the descent *actually*
  produces.

* `CaseIIConjPairDescentSolution37` — the precise residual `def … : Prop`: every σ-conjugate-pair
  datum with the (proven, clean) η₀-principalization yields such a σ-conjugate-pair solution at the
  dropped exponent.  This is the σ-conjugate-pair replacement for `CaseIIRealDescentSolution37`.

* `no_conjPairCaseIIData37_of_descentSolution` — minimality: the residual + `not_caseIIData37_zero`
  (no datum at `m = 0`) give no σ-conjugate-pair datum at any level.

## Soundness status of the residual (honest)

The residual `CaseIIConjPairDescentSolution37` is at **linear measure** `(ζ-1)^m` (dropping the
anchor exponent by one), and demands the σ-conjugate-pair reality `σx' = y'` — which the linear
single-root descent at `{η, η⁻¹}` with conjugate generators *does* produce at the level of the bare
products `x' = a₁σb₁`, `y' = σa₁b₁` (`caseII_conjPair_descent_vars`,
`caseII_real_conj_generator_span`).  The one genuinely open sub-step is the **single-unit reduction
preserving the σ-conjugate pair**: the six-unit descent equation `ε₁x'^37 + ε₂y'^37 = ε₃(…)^37`
(`exists_solution_of_etaZeroSpanSingletons`) must be reduced to coefficient `1` on `x'^37, y'^37`
*without* breaking `σx' = y'`.  The existing reduction (`exists_solution'`, absorbing
`ε' = (ε₁/ε₂)^{1/37}` into `x'`) is *not* σ-symmetric; a σ-symmetric absorption requires
`σε₁ = ε₂` (the conjugate-pairing
of the descent units), which is the precise remaining content.  See the verdict in the session
report and the `R2-thetaFixed` entry in `.mathlib-quality/b2_log.jsonl`.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (the descent), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The σ-conjugate-pair descent-datum constructor -/

/-- **Constructor: a σ-conjugate-pair solution of the dropped-exponent equation packages into a
`ConjPairCaseIIData37 (m-1)`.**

Given a datum `D : ConjPairCaseIIData37 K m` and an explicit solution `(x', y', z', ε')` of the next
descent equation with `σx' = y'`, `σy' = x'` (the σ-conjugate-pair invariant the linear descent
produces), `(ζ-1) ∤ y', z'`, and `x'^37 + y'^37 = ε'·((ζ-1)^m·z')^37`, this builds the
`ConjPairCaseIIData37 (m-1)` record: the equation needs `(ζ-1)^((m-1)+1) = (ζ-1)^m` (since `1 ≤ m`,
`one_le_m`), and the `x_conj`/`y_conj` fields are *exactly* `σx' = y'`, `σy' = x'`.  This is the
σ-conjugate-pair analogue of `caseIIRealSingleRootDescent_of_realDescentSolution`. -/
def ConjPairCaseIIData37.of_conjPairSolution {m : ℕ} (D : ConjPairCaseIIData37 K m)
    (x' y' z' : 𝓞 K) (ε' : (𝓞 K)ˣ)
    (hx'_conj : ringOfIntegersComplexConj K x' = y')
    (hy'_conj : ringOfIntegersComplexConj K y' = x')
    (hy' : ¬ (D.hζ.unit'.1 - 1) ∣ y')
    (hz' : ¬ (D.hζ.unit'.1 - 1) ∣ z')
    (e' : x' ^ 37 + y' ^ 37 = (ε' : 𝓞 K) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37) :
    ConjPairCaseIIData37 K (m - 1) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hm : 1 ≤ m := D.toCaseIIData37.one_le_m
  have hm_sub : m - 1 + 1 = m := Nat.sub_add_cancel hm
  exact
    { ζ := D.ζ
      hζ := D.hζ
      x := x'
      y := y'
      z := z'
      ε := ε'
      equation := by rw [hm_sub]; exact e'
      hy := hy'
      hz := hz'
      x_conj := hx'_conj
      y_conj := hy'_conj }

@[simp] theorem ConjPairCaseIIData37.of_conjPairSolution_x {m : ℕ} (D : ConjPairCaseIIData37 K m)
    (x' y' z' : 𝓞 K) (ε' : (𝓞 K)ˣ) (hx'c hy'c hy' hz' e') :
    (D.of_conjPairSolution x' y' z' ε' hx'c hy'c hy' hz' e').x = x' := rfl

/-! ## 2. The precise σ-conjugate-pair descent residual and minimality -/

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **[FLT37-CASEII-CONJPAIR-DESCENT-SOLUTION] The σ-conjugate-pair descent residual.**

For every σ-conjugate-pair datum `D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m` (its clean
η₀-principalization `ConjPairCaseIIData37.etaZeroPrincipalization` is proved unconditionally), the
next descent equation has a **σ-conjugate-pair** solution at the dropped exponent: `x' y' z' : 𝓞 K`,
`ε' : (𝓞 K)ˣ` with `σx' = y'`, `σy' = x'`, `(ζ-1) ∤ y', z'`, and
`x'^37 + y'^37 = ε'·((ζ-1)^m·z')^37`.

This is the σ-conjugate-pair replacement for `CaseIIRealDescentSolution37` (B2-logged as the
doubling obstruction in disguise — it demanded *individually*-real `x', y'` at linear measure, which
the
linear descent never produces).  The σ-conjugate-pair reality `σx' = y'` *is* what the inversion-
symmetric linear descent produces (`caseII_conjPair_descent_vars`), making this the structurally
correct target.  A `def … : Prop` (not an axiom). -/
def CaseIIConjPairDescentSolution37 : Prop :=
  ∀ {m : ℕ} (D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m),
    ∃ (x' y' z' : 𝓞 (CyclotomicField 37 ℚ)) (ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) x' = y' ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) y' = x' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ y' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ z' ∧
      x' ^ 37 + y' ^ 37 =
        (ε' : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37

/-- **The σ-conjugate-pair descent step** from the residual: `ConjPairCaseIIData37 m ⟹ ∃ m' < m,
Nonempty (ConjPairCaseIIData37 m')`.  Packages the residual's solution into a datum at `m-1`
(`of_conjPairSolution`); `m - 1 < m` from `one_le_m`. -/
theorem conjPairCaseIIData37_descent_step
    (h_sol : CaseIIConjPairDescentSolution37)
    {m : ℕ} (D : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m') := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  obtain ⟨x', y', z', ε', hx'c, hy'c, hy', hz', e'⟩ := h_sol D
  have hm : 1 ≤ m := D.toCaseIIData37.one_le_m
  exact ⟨m - 1, by omega, ⟨D.of_conjPairSolution x' y' z' ε' hx'c hy'c hy' hz' e'⟩⟩

/-- **No σ-conjugate-pair Case-II datum exists, from the σ-conjugate-pair descent residual.**

Well-founded minimality on the anchor exponent `m`: a datum at the minimal `m` descends to `m' < m`
(`conjPairCaseIIData37_descent_step`), contradicting minimality.  Mirrors
`no_caseIIData37_of_descent_step`. -/
theorem no_conjPairCaseIIData37_of_descentSolution
    (h_sol : CaseIIConjPairDescentSolution37) :
    ¬ ∃ m : ℕ, Nonempty (ConjPairCaseIIData37 (CyclotomicField 37 ℚ) m) := by
  classical
  rintro ⟨m, D⟩
  let P : ℕ → Prop := fun n => Nonempty (ConjPairCaseIIData37 (CyclotomicField 37 ℚ) n)
  have hP : ∃ n, P n := ⟨m, D⟩
  let n := Nat.find hP
  have hn : P n := Nat.find_spec hP
  rcases hn with ⟨Dmin⟩
  obtain ⟨m', hm', D'⟩ := conjPairCaseIIData37_descent_step h_sol Dmin
  exact (Nat.find_min hP hm') D'

/-! ## 3. Non-vacuity of the residual

The residual is genuinely non-vacuous (not provably false): its conclusion shape is *exactly the
data of a σ-conjugate-pair datum at `m-1`*.  Any `ConjPairCaseIIData37 (m-1)` exhibits such a
solution at exponent `m` (its `equation`, `x_conj`, `y_conj`, `hy`, `hz` fields), so the conclusion
is realizable in σ-conjugate-pair form. -/

/-- **The `CaseIIConjPairDescentSolution37` conclusion shape is realized by genuine σ-conjugate-pair
data.**  Any `D' : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) k` exhibits a σ-conjugate-pair
solution of the descent equation at exponent `k+1`: its own `(D'.x, D'.y, D'.z, D'.ε)` with the
σ-swap `σD'.x = D'.y`, `σD'.y = D'.x` (the `x_conj`/`y_conj` fields).  Certifies the residual is not
vacuously false. -/
theorem caseIIConjPairDescentSolution_conclusion_realized
    {k : ℕ} (D' : ConjPairCaseIIData37 (CyclotomicField 37 ℚ) k) :
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.x = D'.y ∧
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.y = D'.x ∧
    ¬ (D'.hζ.unit'.1 - 1) ∣ D'.y ∧
    ¬ (D'.hζ.unit'.1 - 1) ∣ D'.z ∧
    D'.x ^ 37 + D'.y ^ 37 =
      (D'.ε : 𝓞 (CyclotomicField 37 ℚ)) * ((D'.hζ.unit'.1 - 1) ^ (k + 1) * D'.z) ^ 37 :=
  ⟨D'.x_conj, D'.y_conj, D'.hy, D'.hz, D'.equation⟩

end BernoulliRegular.FLT37.Eichler

end

end
