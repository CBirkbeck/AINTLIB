import BernoulliRegular.CyclotomicUnits.AnalyticCore
import BernoulliRegular.CyclotomicUnits.DeletedFourier

/-!
# Deleted Fourier determinant on the even cyclotomic quotient

This file specializes the abstract deleted Fourier determinant identity to
`CyclotomicEvenDelta p = (ZMod p)ˣ / {±1}` and identifies the `hk` convention
with the existing `FLT37.Sinnott.quotientEigenvalue` normalization.
-/

noncomputable section

namespace BernoulliRegular
namespace CyclotomicUnits

variable (p : ℕ) [Fact p.Prime]

/-- A noncanonical equivalence between nontrivial characters of the even
quotient and non-identity elements of the even quotient.  It is used only for
determinant reindexing; the determinant statements below are independent of
which equivalence is chosen. -/
def cyclotomicEvenNontrivCharEquivNonidentity (hp_two : 2 < p) :
    NontrivChar (CyclotomicEvenDelta p) ≃ Nonidentity (CyclotomicEvenDelta p) := by
  letI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  letI : DecidableEq (MulChar (CyclotomicEvenDelta p) ℂ) := Classical.decEq _
  refine Fintype.equivOfCardEq ?_
  have hχ := FLT37.Sinnott.card_nontriv_mulChar_eq p hp_two
  have hG := FLT37.Sinnott.fintype_card_nonTrivialCE_eq p hp_two
  rw [hχ, hG]
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rcases hp_odd with ⟨k, hk⟩
  omega

/-- The deleted determinant identity on `CyclotomicEvenDelta p`, in the
`hk⁻¹` convention. -/
theorem det_cyclotomicEven_deletedConvolution_eq_prod_erase
    (hp_two : 2 < p) (q : CyclotomicEvenDelta p → ℂ) :
    haveI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
    haveI : DecidableEq (MulChar (CyclotomicEvenDelta p) ℂ) := Classical.decEq _
    (deletedConvolutionMatrixOnNonidentity
      (G := CyclotomicEvenDelta p) q).det =
      ∏ χ ∈ (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1,
        deletedFourierCoeff (G := CyclotomicEvenDelta p) q χ := by
  classical
  letI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  exact det_deletedConvolutionMatrixOnNonidentity_eq_prod_erase
    (G := CyclotomicEvenDelta p)
    (cyclotomicEvenNontrivCharEquivNonidentity (p := p) hp_two) q

/-- The arbitrary omitted-row deleted determinant identity on
`CyclotomicEvenDelta p`, with rows ordered as `h = h₀ * r`,
`r ∈ H \ {1}`. -/
theorem det_cyclotomicEven_deletedConvolutionAtReindexed_eq_charFactor_mul_prod_erase
    (hp_two : 2 < p) (h₀ : CyclotomicEvenDelta p)
    (q : CyclotomicEvenDelta p → ℂ) :
    haveI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
    haveI : DecidableEq (MulChar (CyclotomicEvenDelta p) ℂ) := Classical.decEq _
    (deletedConvolutionMatrixAtReindexed
      (G := CyclotomicEvenDelta p) h₀ q).det =
      (∏ χ ∈ (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1,
        χ h₀) *
        ∏ χ ∈ (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1,
          deletedFourierCoeff (G := CyclotomicEvenDelta p) q χ := by
  classical
  letI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  exact det_deletedConvolutionMatrixAtReindexed_eq_charFactor_mul_prod_erase
    (G := CyclotomicEvenDelta p)
    (cyclotomicEvenNontrivCharEquivNonidentity (p := p) hp_two) h₀ q

/-- The `hk` deleted determinant for the descended cyclotomic log-norm equals,
after squaring, the product of the existing quotient eigenvalues. -/
theorem det_cyclotomicEven_logNorm_deletedMul_sq_eq_prod_quotientEigenvalue_sq
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
    haveI : DecidableEq (MulChar (CyclotomicEvenDelta p) ℂ) := Classical.decEq _
    (deletedConvolutionMulMatrixOnNonidentity
      (G := CyclotomicEvenDelta p)
      (FLT37.Sinnott.convolutionLogNormDescended p)).det ^ 2 =
      (∏ ξ ∈ (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1,
        FLT37.Sinnott.quotientEigenvalue p ξ) ^ 2 := by
  classical
  letI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  rw [det_deletedConvolutionMulMatrixOnNonidentity_sq_eq_prod_deletedFourierCoeffMul_sq
    (G := CyclotomicEvenDelta p)
    (cyclotomicEvenNontrivCharEquivNonidentity (p := p) hp_two)
    (FLT37.Sinnott.convolutionLogNormDescended p)]
  congr 1
  rw [Finset.prod_subtype
    (p := fun ξ : MulChar (CyclotomicEvenDelta p) ℂ ↦ ξ ≠ 1)
    (s := (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1)
    (f := fun ξ ↦ FLT37.Sinnott.quotientEigenvalue p ξ)]
  · refine Finset.prod_congr rfl ?_
    intro ξ _
    unfold deletedFourierCoeffMul FLT37.Sinnott.quotientEigenvalue
    rfl
  · intro ξ
    simp [Finset.mem_erase]

/-- The arbitrary omitted-row `hk` determinant for the descended cyclotomic
log-norm.  The explicit character factor records the arbitrary omitted
embedding; it is a harmless sign in regulator applications. -/
theorem
    det_cyclotomicEven_logNorm_deletedMulAtReindexed_sq_eq_charFactor_mul_prod_quotientEigenvalue_sq
    (hp_two : 2 < p) (h₀ : CyclotomicEvenDelta p) :
    haveI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
    haveI : DecidableEq (MulChar (CyclotomicEvenDelta p) ℂ) := Classical.decEq _
    (deletedConvolutionMulMatrixAtReindexed
      (G := CyclotomicEvenDelta p) h₀
      (FLT37.Sinnott.convolutionLogNormDescended p)).det ^ 2 =
      ((∏ ξ ∈ (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1,
          (ξ h₀)⁻¹) *
        ∏ ξ ∈ (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1,
          FLT37.Sinnott.quotientEigenvalue p ξ) ^ 2 := by
  classical
  letI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  rw [det_deletedConvolutionMulMatrixAtReindexed_sq_eq_charFactor_mul_prod_sq
    (G := CyclotomicEvenDelta p)
    (cyclotomicEvenNontrivCharEquivNonidentity (p := p) hp_two) h₀
    (FLT37.Sinnott.convolutionLogNormDescended p)]
  have hfactor :
      (∏ χ : NontrivChar (CyclotomicEvenDelta p), (χ.val h₀)⁻¹) =
        ∏ ξ ∈ (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1,
          (ξ h₀)⁻¹ := by
    rw [Finset.prod_subtype
      (p := fun ξ : MulChar (CyclotomicEvenDelta p) ℂ ↦ ξ ≠ 1)
      (s := (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1)
      (f := fun ξ ↦ (ξ h₀)⁻¹)]
    intro ξ
    simp [Finset.mem_erase]
  have hprod :
      (∏ χ : NontrivChar (CyclotomicEvenDelta p),
          deletedFourierCoeffMul (G := CyclotomicEvenDelta p)
            (FLT37.Sinnott.convolutionLogNormDescended p) χ.val) =
        ∏ ξ ∈ (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1,
          FLT37.Sinnott.quotientEigenvalue p ξ := by
    rw [Finset.prod_subtype
      (p := fun ξ : MulChar (CyclotomicEvenDelta p) ℂ ↦ ξ ≠ 1)
      (s := (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1)
      (f := fun ξ ↦ FLT37.Sinnott.quotientEigenvalue p ξ)]
    · refine Finset.prod_congr rfl ?_
      intro ξ _
      unfold deletedFourierCoeffMul FLT37.Sinnott.quotientEigenvalue
      rfl
    · intro ξ
      simp [Finset.mem_erase]
  rw [hfactor, hprod]

/-- The arbitrary omitted-row `hk` determinant for the descended cyclotomic
log-norm, with the harmless character factor removed after squaring. -/
theorem det_cyclotomicEven_logNorm_deletedMulAtReindexed_sq_eq_prod_quotientEigenvalue_sq
    (hp_two : 2 < p) (h₀ : CyclotomicEvenDelta p) :
    haveI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
    haveI : DecidableEq (MulChar (CyclotomicEvenDelta p) ℂ) := Classical.decEq _
    (deletedConvolutionMulMatrixAtReindexed
      (G := CyclotomicEvenDelta p) h₀
      (FLT37.Sinnott.convolutionLogNormDescended p)).det ^ 2 =
      (∏ ξ ∈ (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1,
        FLT37.Sinnott.quotientEigenvalue p ξ) ^ 2 := by
  classical
  letI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  rw [det_deletedConvolutionMulMatrixAtReindexed_sq_eq_prod_deletedFourierCoeffMul_sq
    (G := CyclotomicEvenDelta p)
    (cyclotomicEvenNontrivCharEquivNonidentity (p := p) hp_two) h₀
    (FLT37.Sinnott.convolutionLogNormDescended p)]
  congr 1
  rw [Finset.prod_subtype
    (p := fun ξ : MulChar (CyclotomicEvenDelta p) ℂ ↦ ξ ≠ 1)
    (s := (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1)
    (f := fun ξ ↦ FLT37.Sinnott.quotientEigenvalue p ξ)]
  · refine Finset.prod_congr rfl ?_
    intro ξ _
    unfold deletedFourierCoeffMul FLT37.Sinnott.quotientEigenvalue
    rfl
  · intro ξ
    simp [Finset.mem_erase]

end CyclotomicUnits
end BernoulliRegular
