import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.Determinant
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.LDerivative
import BernoulliRegular.LValueAtOne.Defs

/-!
# LV-SIN-D: Composition into `SinnottAnalyticIdentity`

Combines:
* LV-SIN-A: `regOfFamily = |det(M)|` with explicit log-embedding entries.
* LV-SIN-B: determinant evaluation as character-product.
* LV-SIN-C: `L'(0,χ)` = log-sum formula.
* Analytic CNF for K⁺ (already shipped: `hPlus_formula_of_evenLValues`).

Yields `SinnottAnalyticIdentity`, hence `SinnottRegulatorIdentity`,
hence `SinnottIndexFormula`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **`KummerDirichletDeterminantSum`**: determinant evaluation in
explicit `log|sin|` form.

The matrix `M[i, w] = log|w'(realCyclotomicUnit (j+2))|` factors as

  `M[i, w] = 2 (log|2 sin(π(j+2)·a_w/p)| - log|2 sin(πa_w/p)|)`

where `a_w` is the embedding-index of place `w`. The determinant
evaluates by character orthogonality to a product of Dirichlet
log-sums.

This Prop captures the resulting evaluation as a product over
even nontrivial Dirichlet characters χ mod p. -/
def KummerDirichletDeterminantSum (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  ∃ (factor : ℝ) (charSet : Finset (DirichletCharacter ℂ p)),
    factor ≠ 0 ∧
    (∀ χ ∈ charSet, χ.Even ∧ χ ≠ 1) ∧
    NumberField.Units.regOfFamily
        (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
      |factor| * ∏ χ ∈ charSet, (DirichletLogSum p χ).re

/-- **Composition step**: combining `KummerDirichletDeterminantSum`
(LV-SIN-B+C) with the analytic CNF for K⁺ (`hPlus_formula_of_evenLValues`)
gives `SinnottAnalyticIdentity`. The composition is the substantive
LV-SIN-D content. -/
def CompositionToSinnottAnalytic (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  KummerDirichletDeterminantSum p K hp_odd hp_three →
  SinnottAnalyticIdentity p K hp_odd hp_three

/-- **χ-eigenvalue identity in `evenLValueLogSum` form**: PROVEN.

For the matrix entry shape `M[k, a] = log‖1 − stdAddChar(a · k)‖
− log‖1 − stdAddChar(a)‖` (which is the cyclotomic-unit log embedding shape
on `ZMod p`), the χ⁻¹-row sum evaluates as

  `∑ a, χ⁻¹(a) · M[k, a] = (χ(k) − 1) · evenLValueLogSum p χ`.

Direct application of `dirichletCharacter_sum_matrix_eigenvalue` with
character `χ⁻¹` and `g(a) := log‖1 − stdAddChar(a)‖`, plus the identity
`χ⁻¹((k⁻¹ : Mˣ)) = χ(k)` via `MulChar.inv_apply` and `Ring.inverse_unit`.

This bridges the abstract LV-SIN-B eigenvalue identity to the existing
project infrastructure `evenLValueLogSum` (which is the K⁺-side D_χ used
in `hPlus_formula_of_evenLValues`). -/
theorem dirichletCharacter_inv_matrix_eigenvalue_evenLValueLogSum
    (χ : DirichletCharacter ℂ p) (k : (ZMod p)ˣ) :
    ∑ a : ZMod p, χ⁻¹ a *
        ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) (a * (↑k : ZMod p))‖ : ℝ) -
          (Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ) =
      (χ (↑k : ZMod p) - 1) * BernoulliRegular.evenLValueLogSum p χ := by
  set g : ZMod p → ℂ := fun a =>
    ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ)
  have h_abs := dirichletCharacter_sum_matrix_eigenvalue χ⁻¹ k g
  have h_lhs_eq : ∀ a : ZMod p,
      χ⁻¹ a *
        ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) (a * (↑k : ZMod p))‖ : ℝ) -
          (Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ) =
        χ⁻¹ a * (g (a * (↑k : ZMod p)) - g a) := by
    intro a
    push_cast [g]
    ring
  rw [Finset.sum_congr rfl (fun a _ => h_lhs_eq a), h_abs]
  have h_inv : χ⁻¹ (↑(k⁻¹ : (ZMod p)ˣ) : ZMod p) = χ ((↑k : ZMod p)) := by
    rw [MulChar.inv_apply, Ring.inverse_unit (k⁻¹)]
    simp [inv_inv]
  rw [h_inv]
  rfl

/-- **Second-kind orthogonality** for Dirichlet characters: for χ, ψ
distinct Dirichlet characters mod p,

  `∑ a : ZMod p, χ(a) · ψ⁻¹(a) = 0`.

Direct from `MulChar.sum_eq_zero_of_ne_one` applied to the product
character `χ · ψ⁻¹` (which is ≠ 1 since χ ≠ ψ).

For Sinnott's matrix diagonalization, this is the χ ↔ ψ orthogonality
that collapses the (F^* M F)_{χ, ψ} block to be diagonal: when χ ≠ ψ
the sum vanishes; when χ = ψ the sum is the cardinality of `(ZMod p)ˣ`
(treated by the companion lemma `sum_charProd_self_eq_card_units`). -/
theorem dirichletCharacter_orthogonality_ne
    (χ ψ : DirichletCharacter ℂ p) (h : χ ≠ ψ) :
    ∑ a : ZMod p, χ a * ψ⁻¹ a = 0 := by
  have h_prod_ne : (χ * ψ⁻¹) ≠ 1 := mul_inv_eq_one.not.mpr h
  simpa [MulChar.coeToFun_mul] using MulChar.sum_eq_zero_of_ne_one h_prod_ne

/-- **Self-orthogonality** for Dirichlet characters: for any χ,

  `∑ a : ZMod p, χ(a) · χ⁻¹(a) = (Fintype.card (ZMod p)ˣ : ℂ)`.

Direct from `MulChar.sum_one_eq_card_units` applied to `χ · χ⁻¹ = 1`. -/
theorem dirichletCharacter_orthogonality_self
    (χ : DirichletCharacter ℂ p) :
    ∑ a : ZMod p, χ a * χ⁻¹ a = (Fintype.card (ZMod p)ˣ : ℂ) := by
  simp_rw [← MulChar.mul_apply, mul_inv_cancel]
  exact_mod_cast MulChar.sum_one_eq_card_units (R := ZMod p) (R' := ℂ)

/-- **Matrix χ⁻¹-eigenvalue in `DirichletLogSum` form**: composing
`dirichletCharacter_inv_matrix_eigenvalue_evenLValueLogSum` with the K-side
bridge `evenLValueLogSum_eq_neg_DirichletLogSum_inv` flips the sign on the
χ-eigenvalue factor: `(χ(k) − 1) · evenLValueLogSum = (1 − χ(k)) ·
DirichletLogSum p χ⁻¹`.

This is the direct K-side form used by the Frobenius-determinant evaluation:
each row's χ⁻¹-weighted sum is `(1 − χ(k)) · D_{χ⁻¹}`. -/
theorem dirichletCharacter_inv_matrix_eigenvalue_DirichletLogSum
    (χ : DirichletCharacter ℂ p) (k : (ZMod p)ˣ) :
    ∑ a : ZMod p, χ⁻¹ a *
        ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) (a * (↑k : ZMod p))‖ : ℝ) -
          (Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ) =
      (1 - χ ((↑k : ZMod p))) * DirichletLogSum p χ⁻¹ := by
  have h := dirichletCharacter_inv_matrix_eigenvalue_evenLValueLogSum (p := p) χ k
  rw [evenLValueLogSum_eq_neg_DirichletLogSum_inv] at h
  rw [h]
  ring

end Sinnott

end FLT37

end BernoulliRegular

end
