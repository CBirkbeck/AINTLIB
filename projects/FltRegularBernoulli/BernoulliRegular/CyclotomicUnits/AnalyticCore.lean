import BernoulliRegular.LValueAtOne.Even
import BernoulliRegular.GaussSum.Basic
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.DetBridge
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Analytic core for the cyclotomic-unit route

This file exposes the proved analytic ingredients needed for the
cyclotomic-unit index formula in the notation used by
`BernoulliRegular/CyclotomicUnits`.

It deliberately does not assume a bundled Sinnott target. The downstream
matrix-restriction bridge from the Sinnott regulator matrix to the deleted
Fourier determinant is proved separately in `IndexDeterminant.lean`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace CyclotomicUnits

variable (p : ℕ) [Fact p.Prime]

/-- The even primitive `L(1, χ)` formula in the `DirichletLogSum`
normalization used by the Sinnott determinant computation. -/
theorem even_LFunction_one_eq_gaussSum_inv_mul_DirichletLogSum
    {χ : DirichletCharacter ℂ p} (hχ_prim : χ.IsPrimitive) (hχ_even : χ.Even)
    (hχ_ne_one : χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 =
      (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ *
        FLT37.Sinnott.DirichletLogSum p χ⁻¹ := by
  calc
    DirichletCharacter.LFunction χ 1 = evenLValueRhs p χ :=
      BernoulliRegular.even_LFunction_one_eq_evenLValueRhs (p := p)
        hχ_prim hχ_even hχ_ne_one
    _ = (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ *
          FLT37.Sinnott.DirichletLogSum p χ⁻¹ :=
      FLT37.Sinnott.evenLValueRhs_eq_gaussSum_inv_mul_DirichletLogSum p χ

/-- The `DirichletLogSum` factor attached to an even nontrivial character is
nonzero. This is the nonvanishing part of the even `L(1, χ)` formula, using
mathlib's nonvanishing theorem for `L(1, χ)`. -/
theorem DirichletLogSum_inv_ne_zero_of_even_nontrivial
    {χ : DirichletCharacter ℂ p} (hχ_even : χ.Even) (hχ_ne_one : χ ≠ 1) :
    FLT37.Sinnott.DirichletLogSum p χ⁻¹ ≠ 0 := by
  have hχ_prim : χ.IsPrimitive :=
    DirichletCharacter.isPrimitive_of_ne_one (p := p) hχ_ne_one
  have hL : DirichletCharacter.LFunction χ 1 ≠ 0 :=
    DirichletCharacter.LFunction_apply_one_ne_zero hχ_ne_one
  rw [even_LFunction_one_eq_gaussSum_inv_mul_DirichletLogSum
    (p := p) hχ_prim hχ_even hχ_ne_one] at hL
  exact (mul_ne_zero_iff.mp hL).2

/-- Nonvanishing of the `DirichletLogSum` factor, without the inverse in the
statement. -/
theorem DirichletLogSum_ne_zero_of_even_nontrivial
    {χ : DirichletCharacter ℂ p} (hχ_even : χ.Even) (hχ_ne_one : χ ≠ 1) :
    FLT37.Sinnott.DirichletLogSum p χ ≠ 0 := by
  have hχ_inv_even : (χ⁻¹).Even := by
    rw [DirichletCharacter.Even] at hχ_even ⊢
    rw [MulChar.inv_apply_eq_inv', hχ_even]
    norm_num
  have hχ_inv_ne_one : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ_ne_one
    calc
      χ = χ⁻¹⁻¹ := (inv_inv χ).symm
      _ = 1 := by simp [h]
  simpa using
    DirichletLogSum_inv_ne_zero_of_even_nontrivial (p := p)
      hχ_inv_even hχ_inv_ne_one

/-- Nontrivial quotient characters have nonzero Frobenius eigenvalue. -/
theorem quotientEigenvalue_ne_zero_of_ne_one
    {ξ : MulChar (CyclotomicEvenDelta p) ℂ} (hp_two : 2 < p) (hξ_ne_one : ξ ≠ 1) :
    FLT37.Sinnott.quotientEigenvalue p ξ ≠ 0 := by
  have hχ_even :
      (FLT37.Sinnott.dirichletOfQuotientChar p ξ).Even :=
    FLT37.Sinnott.dirichletOfQuotientChar_even p ξ
  have hχ_ne_one :
      FLT37.Sinnott.dirichletOfQuotientChar p ξ ≠ 1 := by
    intro h_one
    apply hξ_ne_one
    have h_eq :
        FLT37.Sinnott.dirichletOfQuotientChar p ξ =
          FLT37.Sinnott.dirichletOfQuotientChar p 1 := by
      rw [FLT37.Sinnott.dirichletOfQuotientChar_one]
      exact h_one
    exact FLT37.Sinnott.dirichletOfQuotientChar_injective p h_eq
  have hD :
      FLT37.Sinnott.DirichletLogSum p
          (FLT37.Sinnott.dirichletOfQuotientChar p ξ) ≠ 0 :=
    DirichletLogSum_ne_zero_of_even_nontrivial (p := p) hχ_even hχ_ne_one
  intro hqe
  have h := FLT37.Sinnott.two_mul_quotientEigenvalue_eq_neg_DLS p ξ hp_two
  rw [hqe, mul_zero] at h
  exact hD (neg_eq_zero.mp h.symm)

/-- Frobenius' group-determinant formula on the even quotient, after
extracting the trivial character. This is the proved finite determinant
calculation behind the Sinnott regulator comparison. -/
theorem evenFrobeniusDet_sq_eq_log_p_sq_mul_nontrivial_DirichletLogSum_sq
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    haveI : DecidableEq (MulChar (CyclotomicEvenDelta p) ℂ) :=
      Classical.decEq _
    (FLT37.Sinnott.convolutionMatrixLogNormEven p).det ^ 2 =
      (((Real.log p : ℝ) : ℂ)) ^ 2 *
        (∏ ξ ∈ (Finset.univ : Finset
            (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1,
          FLT37.Sinnott.DirichletLogSum p
            (FLT37.Sinnott.dirichletOfQuotientChar p ξ)) ^ 2 /
      4 ^ (Fintype.card (MulChar (CyclotomicEvenDelta p) ℂ)) :=
  FLT37.Sinnott.det_convolutionMatrixLogNormEven_sq_eq_log_p_sq_mul_nontrivial_DLS_sq
    p hp_two

/-- The analytic class-number-formula side in the same `DirichletLogSum`
normalization as the finite determinant calculation. -/
theorem hPlus_mul_regulator_sq_eq_DirichletLogSum
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    (((hPlus K : ℕ) : ℂ) *
        ((NumberField.Units.regulator (NumberField.maximalRealSubfield K) : ℝ) : ℂ)) ^ 2 =
      (∏ χ ∈ evenNontrivialCharacters (p := p),
          FLT37.Sinnott.DirichletLogSum p χ⁻¹) ^ 2 / (2 : ℂ) ^ (p - 3) :=
  FLT37.Sinnott.hPlus_mul_regulator_sq_eq (p := p) K hp_odd hp_three

end CyclotomicUnits
end BernoulliRegular

end
