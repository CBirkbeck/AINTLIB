import BernoulliRegular.CyclotomicUnits.DeletedFourierCyclotomic
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.DetBridge

/-!
# Deleted Fourier determinant for Sinnott's cyclotomic-unit matrix

This file connects the CU-08 deleted Fourier determinant with the matrix
`sinnottMatrixA - sinnottMatrixB` used by the existing FLT37 Sinnott pipeline.
The point is to prove the determinant input from the concrete deleted Fourier
identity, instead of assuming the named determinant source proposition.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open NumberField

namespace BernoulliRegular
namespace CyclotomicUnits

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Reindexing rows and columns by unrelated equivalences can only change a
complex determinant by a sign; after squaring the determinant is unchanged. -/
theorem det_submatrix_equiv_equiv_sq
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e₁ e₂ : κ ≃ ι) (A : Matrix ι ι ℂ) :
    (A.submatrix e₁ e₂).det ^ 2 = A.det ^ 2 := by
  classical
  have hdet := Matrix.det_reindex e₁.symm e₂.symm A
  change (((Matrix.reindex e₁.symm e₂.symm) A).det) ^ 2 = A.det ^ 2
  rw [hdet, mul_pow]
  have hsign :
      ((↑↑(Equiv.Perm.sign (e₂.symm.trans e₁.symm.symm)) : ℂ)) ^ 2 = 1 := by
    let σ : Equiv.Perm ι := e₂.symm.trans e₁.symm.symm
    have hunit : (Equiv.Perm.sign σ) ^ 2 = 1 :=
      Int.units_pow_two _
    have hcast := congrArg (fun u : ℤˣ => ((u : ℂ))) hunit
    push_cast at hcast
    simpa [σ] using hcast
  rw [hsign, one_mul]

/-- The shifted infinite-place indexing, restricted away from the distinguished
Dirichlet place, as an equivalence with the non-identity even quotient. -/
noncomputable def kplusPlaceStarEquivNonidentityShifted
    (hp_two : 2 < p) :
    {w : InfinitePlace K⁺ // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ≃
      Nonidentity (CyclotomicEvenDelta p) := by
  classical
  let e :=
    FLT37.Sinnott.KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted
      (p := p) K hp_two
  have h_w₀ : e NumberField.Units.dirichletUnitTheorem.w₀ = 1 :=
    FLT37.Sinnott.KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted_apply_w₀
      (p := p) K hp_two
  exact e.subtypeEquiv (fun v => by
    constructor
    · intro hv h_eq
      apply hv
      rw [← h_w₀] at h_eq
      exact e.injective h_eq
    · intro hv h_eq
      apply hv
      rw [h_eq, h_w₀])

@[simp]
theorem kplusPlaceStarEquivNonidentityShifted_apply
    (hp_two : 2 < p)
    (w : {w : InfinitePlace K⁺ // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (kplusPlaceStarEquivNonidentityShifted (p := p) (K := K) hp_two w).val =
      FLT37.Sinnott.kplusEmbeddingIndexQuotientShifted (p := p) K w.val := by
  rfl

/-- Sinnott's `(A - B)` determinant is the CU-08 deleted Fourier determinant,
after transposing and reindexing rows and columns. This is the matrix-level
replacement for the old `DetASubBSqEqProdNontrivialQeSq` source assumption.

The proof currently uses `5 ≤ p` only for the existing API that identifies the
finite cyclotomic-unit family indices with the non-identity even quotient. -/
theorem detASubB_sq_eq_deletedFourier_sq
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p) (hp_ge_five : 5 ≤ p) :
    haveI : DecidableEq (InfinitePlace K⁺) := Classical.decEq _
    haveI : DecidablePred (fun w : InfinitePlace K⁺ =>
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀) := fun _ => instDecidableNot
    haveI : Fintype {w : InfinitePlace K⁺ //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
      Subtype.fintype (fun w : InfinitePlace K⁺ =>
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀)
    haveI : DecidableEq {w : InfinitePlace K⁺ //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := fun a b => a.instDecidableEq b
    (((((FLT37.Sinnott.sinnottMatrixA p K -
      FLT37.Sinnott.sinnottMatrixB p K).det : ℝ) : ℂ)) ^ 2 : ℂ) =
      (deletedConvolutionMulMatrixAtReindexed
        (G := CyclotomicEvenDelta p)
        (FLT37.Sinnott.kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀)
        (FLT37.Sinnott.convolutionLogNormDescended p)).det ^ 2 := by
  classical
  letI : DecidableEq (InfinitePlace K⁺) := Classical.decEq _
  letI : DecidablePred (fun w : InfinitePlace K⁺ =>
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀) := fun _ => instDecidableNot
  letI : Fintype {w : InfinitePlace K⁺ //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
    Subtype.fintype (fun w : InfinitePlace K⁺ =>
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀)
  letI : DecidableEq {w : InfinitePlace K⁺ //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := fun a b => a.instDecidableEq b
  let rowEquiv :=
    kplusPlaceStarEquivNonidentityShifted (p := p) (K := K) hp_two
  let colEquiv :=
    FLT37.Sinnott.familyIndexAsCEnotOneEquiv
      (p := p) K hp_odd hp_three hp_ge_five hp_two
  let D :=
    deletedConvolutionMulMatrixAtReindexed
      (G := CyclotomicEvenDelta p)
      (FLT37.Sinnott.kplusEmbeddingIndexQuotient (p := p) K
        NumberField.Units.dirichletUnitTheorem.w₀)
      (FLT37.Sinnott.convolutionLogNormDescended p)
  have hcast :
      (((FLT37.Sinnott.sinnottMatrixA p K -
          FLT37.Sinnott.sinnottMatrixB p K).det : ℝ) : ℂ) =
        (Matrix.of fun
          (i : {w : InfinitePlace K⁺ //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (w : {w : InfinitePlace K⁺ //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((FLT37.Sinnott.sinnottMatrixA p K -
              FLT37.Sinnott.sinnottMatrixB p K) i w : ℝ) : ℂ)).det := by
    rw [show (((FLT37.Sinnott.sinnottMatrixA p K -
        FLT37.Sinnott.sinnottMatrixB p K).det : ℝ) : ℂ) =
        (Complex.ofRealHom ((FLT37.Sinnott.sinnottMatrixA p K -
          FLT37.Sinnott.sinnottMatrixB p K).det) : ℂ) from rfl]
    rw [Complex.ofRealHom.map_det]
    rfl
  have hmatrix :
      (Matrix.of fun
          (w : {w : InfinitePlace K⁺ //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (i : {w : InfinitePlace K⁺ //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((FLT37.Sinnott.sinnottMatrixA p K -
              FLT37.Sinnott.sinnottMatrixB p K) i w : ℝ) : ℂ)) =
        D.submatrix rowEquiv colEquiv := by
    ext w i
    rw [Matrix.of_apply, Matrix.submatrix_apply]
    rw [FLT37.Sinnott.sinnottMatrix_A_sub_B_apply_eq_sub_shifted
      (p := p) K hp_odd hp_three i w]
    simp only [FLT37.Sinnott.convolutionMatrixLogNormEven, Matrix.of_apply, D,
      deletedConvolutionMulMatrixAtReindexed]
    rw [kplusPlaceStarEquivNonidentityShifted_apply
      (p := p) (K := K) hp_two w]
    rw [FLT37.Sinnott.familyIndexAsCEnotOneEquiv_apply
      (p := p) K hp_odd hp_three hp_ge_five hp_two i]
    congr 2
    · simp [mul_comm]
    · simp [mul_comm]
  rw [hcast]
  rw [← Matrix.det_transpose]
  change
    (Matrix.of fun
      (w : {w : InfinitePlace K⁺ //
          w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
      (i : {w : InfinitePlace K⁺ //
          w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        (((FLT37.Sinnott.sinnottMatrixA p K -
          FLT37.Sinnott.sinnottMatrixB p K) i w : ℝ) : ℂ)).det ^ 2 =
      D.det ^ 2
  rw [hmatrix]
  exact det_submatrix_equiv_equiv_sq rowEquiv colEquiv D

/-- The old matrix-level determinant proposition follows from the concrete
CU-08 deleted Fourier determinant, for the `p ≥ 5` branch. -/
theorem detASubBSqEqProdNontrivialQeSq_of_deletedFourier
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p) (hp_ge_five : 5 ≤ p) :
    haveI : DecidableEq (InfinitePlace K⁺) := Classical.decEq _
    haveI : DecidablePred (fun w : InfinitePlace K⁺ =>
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀) := fun _ => instDecidableNot
    haveI : Fintype {w : InfinitePlace K⁺ //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
      Subtype.fintype (fun w : InfinitePlace K⁺ =>
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀)
    haveI : DecidableEq {w : InfinitePlace K⁺ //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := fun a b => a.instDecidableEq b
    FLT37.Sinnott.DetASubBSqEqProdNontrivialQeSq (p := p) K := by
  classical
  letI : DecidableEq (InfinitePlace K⁺) := Classical.decEq _
  letI : DecidablePred (fun w : InfinitePlace K⁺ =>
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀) := fun _ => instDecidableNot
  letI : Fintype {w : InfinitePlace K⁺ //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
    Subtype.fintype (fun w : InfinitePlace K⁺ =>
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀)
  letI : DecidableEq {w : InfinitePlace K⁺ //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := fun a b => a.instDecidableEq b
  unfold FLT37.Sinnott.DetASubBSqEqProdNontrivialQeSq
  rw [detASubB_sq_eq_deletedFourier_sq
    (p := p) (K := K) hp_odd hp_three hp_two hp_ge_five]
  exact det_cyclotomicEven_logNorm_deletedMulAtReindexed_sq_eq_prod_quotientEigenvalue_sq
    (p := p) hp_two
    (FLT37.Sinnott.kplusEmbeddingIndexQuotient (p := p) K
      NumberField.Units.dirichletUnitTheorem.w₀)

end CyclotomicUnits
end BernoulliRegular

end
