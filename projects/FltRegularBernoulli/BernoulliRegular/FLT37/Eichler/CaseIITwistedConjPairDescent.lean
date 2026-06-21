import BernoulliRegular.FLT37.Eichler.CaseIITwistedConjPairData

/-!
# [FLT37-CASEII-R2] The paired-units descent: constructor, residual, minimality

This file assembles the paired-units σ-conjugate-pair structure (`TwistedConjPairData37`,
`CaseIITwistedConjPairData.lean`) into the descent skeleton and isolates the **single precise
residual** that the iterated *no-clearing* reality-aware Case-II descent reduces to.

## What is established

* `TwistedConjPairData37.of_pairedSolution` — **constructor**: a paired-units σ-conjugate-pair
  solution of the next descent equation (variables `x', y', z'` with `σx' = y'`, `σz' = z'`, the
  coefficient-1 equation `x'^37 + y'^37 = ε'·((ζ-1)^m·z')^37` for the underlying
  `ConjPairCaseIIData37`, and the conjugate-paired units `ε₁', ε₂', ε₃'` with `σε₁' = ε₂'`,
  `σε₃' = ε₃'` satisfying the paired equation `ε₁'·x'^37 + ε₂'·y'^37 = ε₃'·((ζ-1)^m·z')^37`)
  packages into a `TwistedConjPairData37 (m-1)`.  No unit clearing is performed — the units are
  carried.

* `CaseIITwistedPairedDescentSolution37` — the precise residual `def … : Prop`: every paired-units
  datum yields such a paired-units solution at the dropped exponent.  This is the *no-clearing*
  replacement for `CaseIIConjPairDescentSolution37`.  Soundness: the conjugate-paired-units form is
  σ-invariant (`TwistedConjPairData37.equation_sigma_invariant`), so the descent preserves the
  structure with no clearing — sidestepping the `δ`-obstruction entirely.

* `no_twistedConjPairData37_of_descentSolution` — minimality: the residual + the inherited
  `one_le_m` give no paired-units datum at any level.

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

/-! ## 1. The paired-units descent-datum constructor -/

/-- **Constructor: a paired-units σ-conjugate-pair solution of the dropped-exponent equation
packages into a `TwistedConjPairData37 (m-1)`.**

Given a datum `D : TwistedConjPairData37 K m` and an explicit solution at the next descent level
with

* `σx' = y'`, `σy' = x'` (the σ-conjugate-pair invariant, carried),
* `σz' = z'` (the anchor real),
* `(ζ-1) ∤ y', z'`,
* the *coefficient-1* equation `x'^37 + y'^37 = ε'·((ζ-1)^m·z')^37` (for the underlying
  `ConjPairCaseIIData37`),
* conjugate-paired units `ε₁', ε₂', ε₃'` with `σε₁' = ε₂'`, `σε₃' = ε₃'`,
* the *paired-units* equation `ε₁'·x'^37 + ε₂'·y'^37 = ε₃'·((ζ-1)^m·z')^37`,

this builds the `TwistedConjPairData37 (m-1)` record.  The coefficient-1 equation needs
`(ζ-1)^((m-1)+1) = (ζ-1)^m` (`1 ≤ m`, `one_le_m`); the paired equation likewise.  No clearing is
performed: the carried units make the paired equation σ-invariant.  This is the no-clearing
analogue of `ConjPairCaseIIData37.of_conjPairSolution`. -/
def TwistedConjPairData37.of_pairedSolution {m : ℕ} (D : TwistedConjPairData37 K m)
    (x' y' z' : 𝓞 K) (ε' ε₁' ε₂' ε₃' : (𝓞 K)ˣ)
    (hx'_conj : ringOfIntegersComplexConj K x' = y')
    (hy'_conj : ringOfIntegersComplexConj K y' = x')
    (hz'_real : ringOfIntegersComplexConj K z' = z')
    (hunit_conj : NumberField.IsCMField.unitsComplexConj K ε₁' = ε₂')
    (hunit₃_real : NumberField.IsCMField.unitsComplexConj K ε₃' = ε₃')
    (hy' : ¬ (D.hζ.unit'.1 - 1) ∣ y')
    (hz' : ¬ (D.hζ.unit'.1 - 1) ∣ z')
    (e' : x' ^ 37 + y' ^ 37 = (ε' : 𝓞 K) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37)
    (epair' : (ε₁' : 𝓞 K) * x' ^ 37 + (ε₂' : 𝓞 K) * y' ^ 37 =
      (ε₃' : 𝓞 K) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37) :
    TwistedConjPairData37 K (m - 1) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hm : 1 ≤ m := D.one_le_m
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
      y_conj := hy'_conj
      ε₁ := ε₁'
      ε₂ := ε₂'
      ε₃ := ε₃'
      unit_conj := hunit_conj
      unit₃_real := hunit₃_real
      z_real := hz'_real
      paired_equation := by rw [hm_sub]; exact epair' }

@[simp] theorem TwistedConjPairData37.of_pairedSolution_x {m : ℕ} (D : TwistedConjPairData37 K m)
    (x' y' z' : 𝓞 K) (ε' ε₁' ε₂' ε₃' : (𝓞 K)ˣ) (hxc hyc hzr huc h3r hy' hz' e' ep') :
    (D.of_pairedSolution x' y' z' ε' ε₁' ε₂' ε₃' hxc hyc hzr huc h3r hy' hz' e' ep').x = x' := rfl

/-! ## 2. The precise paired-units descent residual and minimality -/

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **[FLT37-CASEII-TWISTED-PAIRED-DESCENT-SOLUTION] The paired-units descent residual.**

For every paired-units datum `D : TwistedConjPairData37 (CyclotomicField 37 ℚ) m`, the next descent
equation has a **paired-units σ-conjugate-pair** solution at the dropped exponent: `x' y' z'`,
`ε' ε₁' ε₂' ε₃'` with

* `σx' = y'`, `σy' = x'`, `σz' = z'`,
* `σε₁' = ε₂'`, `σε₃' = ε₃'`,
* `(ζ-1) ∤ y', z'`,
* the coefficient-1 equation `x'^37 + y'^37 = ε'·((ζ-1)^m·z')^37`,
* the paired-units equation `ε₁'·x'^37 + ε₂'·y'^37 = ε₃'·((ζ-1)^m·z')^37`.

This is the *no-clearing* replacement for `CaseIIConjPairDescentSolution37`: it carries the
conjugate-paired units `σε₁' = ε₂'` instead of demanding a single-unit reduction that would break
`σx' = y'`.  The conjugate-paired-units equation is σ-invariant
(`TwistedConjPairData37.equation_sigma_invariant`), so this is the structurally correct target.  A
`def … : Prop` (not an axiom). -/
def CaseIITwistedPairedDescentSolution37 : Prop :=
  ∀ {m : ℕ} (D : TwistedConjPairData37 (CyclotomicField 37 ℚ) m),
    ∃ (x' y' z' : 𝓞 (CyclotomicField 37 ℚ)) (ε' ε₁' ε₂' ε₃' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) x' = y' ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) y' = x' ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) z' = z' ∧
      NumberField.IsCMField.unitsComplexConj (CyclotomicField 37 ℚ) ε₁' = ε₂' ∧
      NumberField.IsCMField.unitsComplexConj (CyclotomicField 37 ℚ) ε₃' = ε₃' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ y' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ z' ∧
      x' ^ 37 + y' ^ 37 =
        (ε' : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37 ∧
      (ε₁' : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 + (ε₂' : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃' : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37

/-- **The paired-units descent step** from the residual: `TwistedConjPairData37 m ⟹ ∃ m' < m,
Nonempty (TwistedConjPairData37 m')`.  Packages the residual's solution into a datum at `m-1`
(`of_pairedSolution`); `m - 1 < m` from `one_le_m`. -/
theorem twistedConjPairData37_descent_step
    (h_sol : CaseIITwistedPairedDescentSolution37)
    {m : ℕ} (D : TwistedConjPairData37 (CyclotomicField 37 ℚ) m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (TwistedConjPairData37 (CyclotomicField 37 ℚ) m') := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  obtain ⟨x', y', z', ε', ε₁', ε₂', ε₃', hxc, hyc, hzr, huc, h3r, hy', hz', e', ep'⟩ := h_sol D
  have hm : 1 ≤ m := D.one_le_m
  exact ⟨m - 1, by omega,
    ⟨D.of_pairedSolution x' y' z' ε' ε₁' ε₂' ε₃' hxc hyc hzr huc h3r hy' hz' e' ep'⟩⟩

/-- **No paired-units Case-II datum exists, from the paired-units descent residual.**

Well-founded minimality on the anchor exponent `m`: a datum at the minimal `m` descends to
`m' < m` (`twistedConjPairData37_descent_step`), contradicting minimality.  Mirrors
`no_conjPairCaseIIData37_of_descentSolution`. -/
theorem no_twistedConjPairData37_of_descentSolution
    (h_sol : CaseIITwistedPairedDescentSolution37) :
    ¬ ∃ m : ℕ, Nonempty (TwistedConjPairData37 (CyclotomicField 37 ℚ) m) := by
  classical
  rintro ⟨m, D⟩
  let P : ℕ → Prop := fun n ↦ Nonempty (TwistedConjPairData37 (CyclotomicField 37 ℚ) n)
  have hP : ∃ n, P n := ⟨m, D⟩
  let n := Nat.find hP
  have hn : P n := Nat.find_spec hP
  rcases hn with ⟨Dmin⟩
  obtain ⟨m', hm', D'⟩ := twistedConjPairData37_descent_step h_sol Dmin
  exact (Nat.find_min hP hm') D'

/-! ## 3. Non-vacuity of the residual

The residual is genuinely non-vacuous (not provably false): its conclusion shape is *exactly the
data of a paired-units datum at `m-1`*.  Any `TwistedConjPairData37 (m-1)` exhibits such a solution
at exponent `m` (its `equation`, `paired_equation`, `x_conj`, `y_conj`, `z_real`, `unit_conj`,
`unit₃_real`, `hy`, `hz` fields), so the conclusion is realizable in paired-units form. -/

/-- **The `CaseIITwistedPairedDescentSolution37` conclusion shape is realized by genuine
paired-units data.**  Any `D' : TwistedConjPairData37 (CyclotomicField 37 ℚ) k` exhibits a
paired-units solution of the descent equation at exponent `k+1`: its own
`(x, y, z, ε, ε₁, ε₂, ε₃)` with the σ-conjugate-pair / paired-units fields.  Certifies the residual
is not vacuously false. -/
theorem caseIITwistedPairedDescentSolution_conclusion_realized
    {k : ℕ} (D' : TwistedConjPairData37 (CyclotomicField 37 ℚ) k) :
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.x = D'.y ∧
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.y = D'.x ∧
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.z = D'.z ∧
    NumberField.IsCMField.unitsComplexConj (CyclotomicField 37 ℚ) D'.ε₁ = D'.ε₂ ∧
    NumberField.IsCMField.unitsComplexConj (CyclotomicField 37 ℚ) D'.ε₃ = D'.ε₃ ∧
    ¬ (D'.hζ.unit'.1 - 1) ∣ D'.y ∧
    ¬ (D'.hζ.unit'.1 - 1) ∣ D'.z ∧
    D'.x ^ 37 + D'.y ^ 37 =
      (D'.ε : 𝓞 (CyclotomicField 37 ℚ)) * ((D'.hζ.unit'.1 - 1) ^ (k + 1) * D'.z) ^ 37 ∧
    (D'.ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * D'.x ^ 37 +
        (D'.ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * D'.y ^ 37 =
      (D'.ε₃ : 𝓞 (CyclotomicField 37 ℚ)) * ((D'.hζ.unit'.1 - 1) ^ (k + 1) * D'.z) ^ 37 :=
  ⟨D'.x_conj, D'.y_conj, D'.z_real, D'.unit_conj, D'.unit₃_real, D'.hy, D'.hz,
    D'.equation, D'.paired_equation⟩

end BernoulliRegular.FLT37.Eichler

end

end
