import BernoulliRegular.FLT37.Eichler.CaseIIEx811Bridge
import BernoulliRegular.UnitQuotient.Washington816

/-!
# Washington Exercise 8.11 for `p = 37`: the matrix-kernel half of `LeadingExponentEx811Core37`

This file attacks the genuine analytic core `LeadingExponentEx811Core37`
(`CaseIIEx811Bridge.lean`) — the last sub-step of Washington Exercise 8.11 (R3) — by
**proving the matrix-kernel half** that the obstruction docstrings of `CaseIIEx811.lean` /
`CaseIILeadingExponentCollapse.lean` described as the missing *Dwork-`ϖ`-basis ↔ `λ`-adic
graded-coordinate identification*.

It imports only; it does **not** modify any existing file.

## The key fact the obstruction docstrings missed

The Dwork parameter `ϖ` is a *uniformizer* with `(ϖ) = (λ)` and `ϖ ≡ λ (mod λ²)`
(`dworkParameterIdeal_eq_dworkCompleteLambdaIdeal`,
`dworkCompleteLambda_sub_dworkParameter_mem_parameterIdeal_sq`), so the Dwork-`ϖ`-power
filtration and the `λ`-adic filtration **coincide**.  Consequently the Dwork-basis matrix
entry is *computed from the `λ`-adic graded coordinate*: the proven
`concreteKummerLogMatrix_eq_two_mul_specializedFiniteLogCoeffModP` already reads the matrix
entry off `AdicCompletion.evalₐ (λ) (p-1)` of the completed-log column.  We package the
fully-general consequence:

* `caseIIEx811Core_coeffModP_eq_evalₐ` — for any conjugation-fixed Dwork element `S`, the
  mod-`p` even-power-`2(j+1)` Dwork coefficient of `S` equals
  `valuedLambdaQuotientDworkCoeffModP (2(j+1)) (evalₐ (λ) (p-1) S)` (`ϖ ↔ λ` filtration
  identity, from `dworkFixedEvenPowerBasis_repr_eq_powerBasis_repr` +
  `valuedLambdaQuotientDworkCoeffModP_evalₐ`); and

* `caseIIEx811Core_mulVec_eq_zero_of_evalₐ_eq_zero` — **bridge (i)**: if the cyclotomic
  local logarithm `∑_a e_a • kummerLogCompletedColumn a` vanishes through `λ`-level `36`
  (the `LeadingExponentEx811Core37` hypothesis), then `concreteKummerLogMatrix.mulVec ē = 0`
  (`ē a = e a mod 37`).  Proof: the level-`36` coordinate of `∑_a e_a •
  kummerLogCompletedColumn a` is `0`, and the matrix row `j` is
  `valuedLambdaQuotientDworkCoeffModP (2(j+1))` of exactly that coordinate (linear in the
  column sum, by the `valuedLambdaQuotientDworkCoeffModP` sum/`zsmul` laws and `evalₐ`
  linearity).

* `caseIIEx811Core_vandermonde_mulVec_regular_eq_zero` — **the collapse**: feeding bridge (i)
  through the proven `diag(B)·V` factorization (`concreteKummerLogMatrix_mulVec_apply`),
  for every **regular** row `j` (`37 ∤ B_{2(j+1)}`, i.e. `kummerLogDetRowFactor j ≠ 0`) the
  Vandermonde row vanishes: `(vandermondeTeichmullerEvenSubOneMatrix.mulVec ē) j = 0`.

## What remains: the eigenbasis ↔ Vandermonde identification (bridge (ii))

The conclusion of `LeadingExponentEx811Core37` is the vanishing of the **mod-`37` free-part
eigencomponent** `caseIIResidueProvenance_decomp (∑_a e_a • φ(CPlusGenerator a)) j` (`j ≠ 15`).
What this file's collapse produces is the vanishing of the **Dwork-log Vandermonde row**
`(V·ē)_j = ∑_a ((a+2)²)^{j+1} ē_a`.  These agree up to a fixed nonzero scalar — that is
Washington's coincidence that the Dwork-log eigenvalue and the Galois `Δ`-action eigenvalue
on the cyclotomic units are *the same* `a^i` — but the identification of the canonical
eigenbasis coordinate `caseIIResidueProvenance_decomp x j` with the Dwork-log Vandermonde
row is genuinely a *second* Vandermonde change-of-basis (the Galois-eigenspace one, from
`pollaczekUnit = ∏_b realCyclotomicUnit(b)^{b^{p-1-i}}`) and is **not** a single existing
repo lemma.  It is isolated as the named residual `CaseIIEx811EigenVandermonde37` below — a
`def … : Prop`, **not** an axiom — with `leadingExponentEx811Core37_of_eigenVandermonde`
discharging the full core from it together with this file's proven matrix-kernel collapse.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.2 Lemma 9.9
  (pp. 180–181), Exercises 8.10/8.11 (p. 166), Corollary 8.15 (p. 153).
-/

@[expose] public section

noncomputable section

set_option maxRecDepth 4000

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-! ## 1. The `ϖ ↔ λ` filtration coefficient identity (general fixed element)

The mod-`p` even-power-`2(j+1)` Dwork coefficient of a conjugation-fixed element `S` is the
`λ`-adic level-`(p-1)` coordinate read by `valuedLambdaQuotientDworkCoeffModP`.  This is the
fully-general form of the single-column identity inside
`concreteKummerLogMatrix_eq_two_mul_specializedFiniteLogCoeffModP`. -/

/-- **The mod-`p` even-power Dwork coefficient is the `λ`-adic level-`(p-1)` coordinate**
(proven).  For any conjugation-fixed Dwork element `S : dworkFixedSubalgebra 37 K` and any
row `j`, the mod-`37` coefficient of `S` on the even-power Dwork basis vector
`ϖ^{2(j+1)}` equals `valuedLambdaQuotientDworkCoeffModP (2(j+1)) (evalₐ (λ) 36 S)`.

This is the `ϖ ↔ λ` filtration identification (`(ϖ) = (λ)`,
`dworkFixedEvenPowerBasis_repr_eq_powerBasis_repr` + `valuedLambdaQuotientDworkCoeffModP_evalₐ`):
the level-`36 = p-1` `λ`-adic graded coordinate carries every even Dwork coefficient with
index `≤ 34 < 36` exactly. -/
theorem caseIIEx811Core_coeffModP_eq_evalₐ
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (S : dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ))
    (j : Fin (kummerLogRank 37)) :
    rationalPadicIntegerToZMod 37
        ((dworkFixedEvenPowerBasis (p := 37) (K := CyclotomicField 37 ℚ)
            (by norm_num : 2 < 37)).repr S
          (kummerLogEvenPowerIndex (p := 37) (by norm_num) j)) =
      valuedLambdaQuotientDworkCoeffModP (p := 37) (K := CyclotomicField 37 ℚ)
        (kummerLogEvenPowerIndex (p := 37) (by norm_num) j).1
        (AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (37 - 1)
          (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ))) := by
  rw [valuedLambdaQuotientDworkCoeffModP_evalₐ]
  exact congrArg (rationalPadicIntegerToZMod 37)
    (dworkFixedEvenPowerBasis_repr_eq_powerBasis_repr (p := 37)
      (K := CyclotomicField 37 ℚ) (by norm_num : 2 < 37) S
      (kummerLogEvenPowerIndex (p := 37) (by norm_num) j))

/-! ## 2. Bridge (i): the matrix kernel from `λ`-level-`36` vanishing

If the cyclotomic local logarithm `∑_a e_a • kummerLogCompletedColumn a` vanishes through
`λ`-level `36`, then `concreteKummerLogMatrix.mulVec ē = 0` (`ē a = e a mod 37`).  The matrix
row `j` is `valuedLambdaQuotientDworkCoeffModP (2(j+1))` of the level-`36` coordinate
(§1 + the `valuedLambdaQuotientDworkCoeffModP` linearity laws), which the hypothesis kills. -/

/-- **`valuedLambdaQuotientDworkCoeffModP` kills `0`** (proven). -/
theorem caseIIEx811Core_coeffModP_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    (i : Fin (37 - 1)) :
    valuedLambdaQuotientDworkCoeffModP (p := 37) (K := CyclotomicField 37 ℚ) i
        (0 : ValuedIntegerRing 37 (CyclotomicField 37 ℚ) ⧸
          (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (37 - 1)) = 0 := by
  have h := valuedLambdaQuotientDworkCoeffModP_add (p := 37) (K := CyclotomicField 37 ℚ) i
    (0 : ValuedIntegerRing 37 (CyclotomicField 37 ℚ) ⧸
      (lambdaIdeal 37 (CyclotomicField 37 ℚ)) ^ (37 - 1)) 0
  simpa using h

set_option maxHeartbeats 1600000 in
-- The completed-log-column sum lives in the heavy `DworkCompleteIntegerRing`; unifying the
-- `evalₐ`-of-coerced-sum with the column sum exceeds the default heartbeat budget.
/-- **Bridge (i): the matrix kernel from the `λ`-level-`36` vanishing** (proven, axiom-clean).

If the cyclotomic local logarithm `∑_a e_a • kummerLogCompletedColumn a` vanishes through
`λ`-level `36` — `AdicCompletion.evalₐ (λ) N (∑_a e_a • kummerLogCompletedColumn a) = 0` for
all `N ≤ 36` (the `LeadingExponentEx811Core37` hypothesis) — then the Kummer-log matrix
annihilates the mod-`37` exponent vector:

  `concreteKummerLogMatrix.mulVec (fun a ↦ (e a : ZMod 37)) = 0`.

Proof: by `concreteKummerLogMatrix_mulVec_exponents_eq_coeff`, the row `j` is the mod-`37`
even-power-`2(j+1)` Dwork coefficient of `S = ∑_a e_a • concreteKummerLogVector a`; by §1 this
equals `valuedLambdaQuotientDworkCoeffModP (2(j+1)) (evalₐ (λ) 36 (S : Dwork))`.  The coerced
sum `(S : Dwork) = ∑_a e_a • kummerLogCompletedColumn a`, whose `evalₐ 36` is `0` by
hypothesis; and `valuedLambdaQuotientDworkCoeffModP _ 0 = 0`. -/
theorem caseIIEx811Core_mulVec_eq_zero_of_evalₐ_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (e : Fin (kummerLogRank 37) → ℤ)
    (hvan : ∀ N : ℕ, N ≤ 36 →
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (∑ a : Fin (kummerLogRank 37),
            e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
              (by decide) a) = 0) :
    Matrix.mulVec
        (concreteKummerLogMatrix (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) (by norm_num))
        (fun a : Fin (kummerLogRank 37) ↦ (e a : ZMod 37)) = 0 := by
  classical
  -- The coerced fixed-subalgebra sum equals the completed-log column sum.
  set S : dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ) :=
    ∑ a : Fin (kummerLogRank 37),
      e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a
    with hS
  have hScoe :
      (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) =
        ∑ a : Fin (kummerLogRank 37),
          e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a := by
    rw [hS]
    rw [show (↑(∑ a : Fin (kummerLogRank 37),
          e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a) :
          DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) =
        (Subalgebra.val (dworkFixedSubalgebra 37 (CyclotomicField 37 ℚ)))
          (∑ a : Fin (kummerLogRank 37),
            e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a)
        from rfl]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun a _ ↦ ?_)
    rw [map_zsmul]
    rfl
  have hevalS :
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) (37 - 1)
          (S : DworkCompleteIntegerRing 37 (CyclotomicField 37 ℚ)) = 0 := by
    rw [hScoe]
    exact hvan 36 (by norm_num)
  ext j
  rw [Pi.zero_apply,
    concreteKummerLogMatrix_mulVec_exponents_eq_coeff
      (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) (by norm_num) e j]
  rw [show (∑ a : Fin (kummerLogRank 37),
        e a • concreteKummerLogVector (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a) = S
      from hS.symm]
  rw [caseIIEx811Core_coeffModP_eq_evalₐ S j, hevalS, caseIIEx811Core_coeffModP_zero]

/-! ## 3. The collapse: the Vandermonde row vanishes at the regular rows

`concreteKummerLogMatrix = diag(kummerLogDetRowFactor)·V` (the proven
`concreteKummerLogMatrix_mulVec_apply`), so the bridge-(i) kernel `mulVec ē = 0` gives, at each
**regular** row `j` (`j ≠ 15`, `2(j+1) ≠ 32`, `37 ∤ B_{2(j+1)}`, hence
`kummerLogDetRowFactor j ≠ 0`), the Vandermonde row equation `(V·ē) j = 0`. -/

/-- **The matrix row factor is nonzero at the regular rows** (proven, from `flt37_bernoulli_table`).
For `j : Fin (kummerLogRank 37)` with `(j : ℕ) ≠ 15` (i.e. `2(j+1) ≠ 32`), the diagonal factor
`kummerLogDetRowFactor j` is nonzero, because `37 ∤ B_{2(j+1)}` (the only irregular even index
`≤ 34` is `32`). -/
theorem caseIIEx811Core_rowFactor_ne_zero
    (j : Fin (kummerLogRank 37)) (hj : (j : ℕ) ≠ 15) :
    kummerLogDetRowFactor (p := 37) j ≠ 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  rw [kummerLogDetRowFactor_ne_zero_iff_bernoulliFactor_ne_zero (p := 37) (by norm_num)]
  rw [bernoulliFactor_ne_zero_iff_not_dvd_bernoulli_num (p := 37)
    (j := kummerLogRowIndex (p := 37) j)
    (kummerLogRowIndex_one_le (p := 37) j)
    (two_mul_kummerLogRowIndex_le_sub_three (p := 37) j)]
  rw [kummerLogRowIndex_eq]
  -- `2(j+1) ≠ 32`, even, `2 ≤ 2(j+1) ≤ 34`: `flt37_bernoulli_table`.
  have hjlt : (j : ℕ) < 17 := j.isLt
  refine FLT37.Sinnott.flt37_bernoulli_table (2 * ((j : ℕ) + 1)) ⟨(j : ℕ) + 1, by ring⟩
    (by omega) (by omega) ?_
  omega

/-- **The collapse: the Vandermonde row vanishes at the regular rows** (proven, axiom-clean).
Under the `λ`-level-`36` vanishing hypothesis, the half-range Teichmüller Vandermonde matrix
annihilates the mod-`37` exponent vector at every regular row `j` (`(j : ℕ) ≠ 15`):

  `(vandermondeTeichmullerEvenSubOneMatrix.mulVec (fun a ↦ (e a : ZMod 37))) j = 0`.

Proof: bridge (i) gives `concreteKummerLogMatrix.mulVec ē = 0`; the proven factorization
`concreteKummerLogMatrix.mulVec ē j = kummerLogDetRowFactor j · (V·ē) j` and the nonzero row
factor at regular `j` (`caseIIEx811Core_rowFactor_ne_zero`) force `(V·ē) j = 0`. -/
theorem caseIIEx811Core_vandermonde_mulVec_regular_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (e : Fin (kummerLogRank 37) → ℤ)
    (hvan : ∀ N : ℕ, N ≤ 36 →
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (∑ a : Fin (kummerLogRank 37),
            e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
              (by decide) a) = 0)
    (j : Fin (kummerLogRank 37)) (hj : (j : ℕ) ≠ 15) :
    (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
        (fun a : Fin (kummerLogRank 37) ↦ (e a : ZMod 37)) j = 0 := by
  have hker := caseIIEx811Core_mulVec_eq_zero_of_evalₐ_eq_zero e hvan
  have hrow := congrFun hker j
  rw [Pi.zero_apply, concreteKummerLogMatrix_mulVec_apply
    (K := CyclotomicField 37 ℚ) (fun a ↦ (e a : ZMod 37)) j] at hrow
  exact (mul_eq_zero.mp hrow).resolve_left (caseIIEx811Core_rowFactor_ne_zero j hj)

/-! ## 4. The remaining residual: the eigenbasis coordinate ↔ Dwork-log Vandermonde row

What §1–§3 prove is the vanishing of the **Dwork-log Vandermonde row**
`(vandermondeTeichmullerEvenSubOneMatrix.mulVec ē) j = ∑_a ((a+2)²)^{j+1} ē_a` at the regular
rows `j : Fin (kummerLogRank 37)`.  What `LeadingExponentEx811Core37` asks for is the vanishing
of the **canonical mod-`37` free-part eigenbasis coordinate**
`caseIIResidueProvenance_decomp (∑_a e_a • φ(CPlusGenerator a)) j` at the regular indices
`j : Fin 18`, `j ≠ 15`.

These agree up to a fixed nonzero scalar per index — Washington's coincidence that the Dwork-log
eigenvalue and the Galois `Δ`-action eigenvalue on the cyclotomic units are *the same* `a^i` — but
the identification of `caseIIResidueProvenance_decomp x j` (the coordinate in the
*Galois-eigenbasis* `[pollaczekUnit(2(j+1))]`, whose change-of-basis to the generators
`[realCyclotomicUnit(a+2)]` is the *second* Vandermonde from
`pollaczekUnit = ∏_b realCyclotomicUnit(b)^{b^{p-1-i}}`) with the Dwork-log Vandermonde row is
genuinely a separate two-Vandermonde compatibility, **not** a single existing repo lemma.  We
isolate it as the named residual below.

It is **sound** and **non-circular**: it is a hypothesis on the *specific* exponent vector `e` whose
Dwork-log Vandermonde rows vanish (not on an arbitrary class), and it is **non-vacuous** — `e = 0`
satisfies both the hypothesis and the conclusion (`caseIIResidueProvenance_decomp_zero`-style),
see `caseIIEx811EigenVandermonde37_antecedent_inhabited`. -/

open BernoulliRegular (CPlusGenerator) in
/-- **The eigenbasis ↔ Dwork-log Vandermonde identification** (a `def … : Prop`, **not** an axiom).

For every `C⁺` exponent vector `e : Fin (kummerLogRank 37) → ℤ` whose **Dwork-log Vandermonde
rows vanish at every regular row** — `(vandermondeTeichmullerEvenSubOneMatrix.mulVec ē) j = 0`
(`ē a = e a mod 37`) for all `j : Fin (kummerLogRank 37)` with `(j : ℕ) ≠ 15` (the half-range
Teichmüller Vandermonde of the matrix factorization) — the canonical mod-`37` free-part
eigenbasis coordinate of `∑_a e_a • φ(CPlusGenerator a)` vanishes at every regular index
`j : Fin 18`, `j ≠ 15`:

  `caseIIResidueProvenance_decomp (∑_a e_a • φ(CPlusGenerator a)) j = 0`.

This is the Galois-eigenbasis vs Dwork-log-Vandermonde change-of-basis compatibility of Washington
Exercise 8.11.  It is **sound** (a property of the specific `e` whose Dwork-log Vandermonde rows
vanish), **non-circular** (the hypothesis is the genuine Dwork-log Vandermonde datum, *proved* from
the `λ`-adic vanishing in §1–§3, not the free-part eigencoordinate itself), and **non-vacuous**
(`e = 0`, see `caseIIEx811EigenVandermonde37_antecedent_inhabited`). -/
def CaseIIEx811EigenVandermonde37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ e : Fin (kummerLogRank 37) → ℤ,
    (∀ j : Fin (kummerLogRank 37), (j : ℕ) ≠ 15 →
      (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
          (fun a : Fin (kummerLogRank 37) ↦ (e a : ZMod 37)) j = 0) →
    ∀ j : Fin 18, j ≠ 15 →
      caseIIResidueProvenance_decomp
        (∑ a : Fin (kummerLogRank 37),
          e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
            (Additive.ofMul
              (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a))) j =
        0

open BernoulliRegular (CPlusGenerator) in
/-- **`CaseIIEx811EigenVandermonde37` has an inhabited antecedent** (non-vacuity, proven): the zero
exponent vector `e = 0` satisfies the hypothesis — the Dwork-log Vandermonde of the zero vector is
`0` — so the residual is a real implication, not vacuously true. -/
theorem caseIIEx811EigenVandermonde37_antecedent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ e : Fin (kummerLogRank 37) → ℤ,
      ∀ j : Fin (kummerLogRank 37), (j : ℕ) ≠ 15 →
        (vandermondeTeichmullerEvenSubOneMatrix (p := 37) (by norm_num)).mulVec
            (fun a : Fin (kummerLogRank 37) ↦ (e a : ZMod 37)) j = 0 := by
  refine ⟨0, fun j _hj ↦ ?_⟩
  rw [show (fun a : Fin (kummerLogRank 37) ↦ ((0 : Fin (kummerLogRank 37) → ℤ) a : ZMod 37)) =
      (0 : Fin (kummerLogRank 37) → ZMod 37) from by funext a; simp]
  rw [Matrix.mulVec_zero, Pi.zero_apply]

/-! ## 5. `LeadingExponentEx811Core37` from the matrix-kernel collapse + the residual

`leadingExponentEx811Core37_of_eigenVandermonde`: the `λ`-level-`36` vanishing hypothesis of
`LeadingExponentEx811Core37` forces, by the proven matrix-kernel collapse §1–§3
(`caseIIEx811Core_vandermonde_mulVec_regular_eq_zero`), the Dwork-log Vandermonde rows to vanish at
every regular row; the residual `CaseIIEx811EigenVandermonde37` then converts that into the
regular-index eigencoordinate vanishing demanded by the core.  Discharging
`CaseIIEx811EigenVandermonde37` therefore closes `LeadingExponentEx811Core37`, hence (via the proven
`leadingExponentEigenCollapse37_of_ex811Core`) the leaf `LeadingExponentEigenCollapse37`.

The high `maxHeartbeats` on the assembly is because checking the term against
`LeadingExponentEx811Core37` reconciles two copies of the heavy `kummerLogCompletedColumn` `evalₐ`
sum (an `isDefEq` above the default budget, below the `adicCompletionIntegers` `whnf` wall). -/

set_option maxHeartbeats 8000000 in
-- Checking the assembled term against `LeadingExponentEx811Core37` reconciles two copies of the
-- heavy `kummerLogCompletedColumn` `evalₐ` sum, an `isDefEq` above the default heartbeat budget
-- (well below the `adicCompletionIntegers` `whnf` wall), hence the raised limit.
theorem leadingExponentEx811Core37_of_eigenVandermonde
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hEig : CaseIIEx811EigenVandermonde37) :
    LeadingExponentEx811Core37 :=
  fun e hvan j hj ↦
    hEig e (fun k hk ↦ caseIIEx811Core_vandermonde_mulVec_regular_eq_zero e hvan k hk) j hj

/-- **`LeadingExponentEigenCollapse37` from the eigenbasis ↔ Vandermonde identification** (proven,
axiom-clean given `CaseIIEx811EigenVandermonde37`): chaining
`leadingExponentEx811Core37_of_eigenVandermonde` with the proven
`leadingExponentEigenCollapse37_of_ex811Core`.  This shows the *entire* remaining content of R3 for
`p = 37` is the single named residual `CaseIIEx811EigenVandermonde37` — the Galois-eigenbasis vs
Dwork-log-Vandermonde change-of-basis compatibility — the `λ`-adic matrix-kernel half having been
discharged in §1–§3. -/
theorem leadingExponentEigenCollapse37_of_eigenVandermonde
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hEig : CaseIIEx811EigenVandermonde37) :
    LeadingExponentEigenCollapse37 :=
  leadingExponentEigenCollapse37_of_ex811Core
    (leadingExponentEx811Core37_of_eigenVandermonde hEig)

end BernoulliRegular.FLT37.Eichler

end
