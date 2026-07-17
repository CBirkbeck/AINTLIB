/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import
  BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.DetBridge.CharacterActionRankOneDecomposition

/-!
# Sinnott determinant factorization discharge

This file factors the nontrivial diagonal eigenvalue matrix into its quotient-eigenvalue
diagonal and a shifted character matrix. It then applies the rank-one determinant lemma and
reduces the final Sinnott Frobenius determinant identity to named character-matrix and
nonvanishing hypotheses.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

open Classical in
/-- Relates the character-matrix and `A - B` determinants to a rank-one perturbation. -/
theorem det_charMatrix_nontriv_sq_mul_det_A_sub_B
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [Finite {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀}] :
    (charMatrix_K_plus_nontriv_sq (p := p) K hp_two).det *
        (Matrix.of fun (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
            (w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)).det =
      (sinnottDiagonalEigenvalueMatrix_nontriv_sq p K hp_odd hp_three hp_two -
        Matrix.of (fun (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
            (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
          sinnottCorrectionColVec (p := p) K
              ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val *
          sinnottCorrectionRowVec (p := p) K hp_odd hp_three i)).det := by
  rw [show (Matrix.of fun (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
            (w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)).det =
      (Matrix.of fun (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
            (w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)).transpose.det
    from (Matrix.det_transpose _).symm]
  rw [← Matrix.det_mul]
  congr 1
  exact charMatrix_nontriv_sq_mul_A_sub_B_transpose_eq_D_nontriv_sq_sub_rank_one
    (p := p) K hp_odd hp_three hp_two

/-- The shifted character matrix with entries `ξ(q(famIdx i))⁻¹ - 1`. -/
noncomputable def sinnottShiftedCharMatrix_nontriv
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    Matrix {ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ // ξ ≠ 1}
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℂ :=
  Matrix.of fun ξ i ↦
    ξ.val (BernoulliRegular.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i))⁻¹ - 1

/-- The square reindexing of `sinnottShiftedCharMatrix_nontriv`. -/
noncomputable def sinnottShiftedCharMatrix_nontriv_sq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)] :
    Matrix {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℂ :=
  (sinnottShiftedCharMatrix_nontriv p K hp_odd hp_three).submatrix
    (equivNontrivCharKplusNeW₀ p K hp_two).symm id

open Classical in
/-- Factors the square diagonal eigenvalue matrix into a diagonal and shifted matrix. -/
theorem sinnottDiagonalEigenvalueMatrix_nontriv_sq_eq_diag_mul_shifted
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] :
    sinnottDiagonalEigenvalueMatrix_nontriv_sq p K hp_odd hp_three hp_two =
      Matrix.diagonal (fun w ↦ quotientEigenvalue p
          ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val) *
        sinnottShiftedCharMatrix_nontriv_sq p K hp_odd hp_three hp_two := by
  ext w i
  simp only [sinnottDiagonalEigenvalueMatrix_nontriv_sq,
    sinnottShiftedCharMatrix_nontriv_sq,
    sinnottDiagonalEigenvalueMatrix_nontriv,
    sinnottShiftedCharMatrix_nontriv,
    Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, id_eq]
  rw [Finset.sum_eq_single w]
  · simp only [cyclotomicEvenDeltaQuotient_apply, map_inv, ↓reduceIte]
    ring
  · intros b _ hb
    rw [if_neg hb.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ w) h

open Classical in
/-- Extracts the product of quotient eigenvalues from the diagonal determinant. -/
theorem det_sinnottDiagonalEigenvalueMatrix_nontriv_sq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] :
    (sinnottDiagonalEigenvalueMatrix_nontriv_sq p K hp_odd hp_three hp_two).det =
      (∏ ξ ∈ (Finset.univ : Finset
          (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1,
        quotientEigenvalue p ξ) *
        (sinnottShiftedCharMatrix_nontriv_sq p K hp_odd hp_three hp_two).det := by
  rw [sinnottDiagonalEigenvalueMatrix_nontriv_sq_eq_diag_mul_shifted
    (p := p) K hp_odd hp_three hp_two, Matrix.det_mul, Matrix.det_diagonal]
  congr 1
  rw [← Equiv.prod_comp (equivNontrivCharKplusNeW₀ p K hp_two)
    (fun w ↦ quotientEigenvalue p
      ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val)]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.prod_subtype (p := fun ξ : MulChar
      (BernoulliRegular.CyclotomicEvenDelta p) ℂ => ξ ≠ 1)
    (s := Finset.univ.erase (1 : MulChar
      (BernoulliRegular.CyclotomicEvenDelta p) ℂ))
    (fun ξ ↦ by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true])]

open Classical in
/-- The character-matrix identity required by the final determinant discharge. -/
def SinnottCharMatrixDetIdentity
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] : Prop :=
  (sinnottShiftedCharMatrix_nontriv_sq p K hp_odd hp_three hp_two).det *
      ((1 : Matrix PUnit.{1} PUnit.{1} ℂ) +
        Matrix.replicateRow PUnit.{1} (fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
          sinnottCorrectionRowVec (p := p) K hp_odd hp_three i) *
        (sinnottDiagonalEigenvalueMatrix_nontriv_sq
          p K hp_odd hp_three hp_two)⁻¹ *
        Matrix.replicateCol PUnit.{1} (fun (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
          -sinnottCorrectionColVec (p := p) K
            ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val)).det =
    (charMatrix_K_plus_nontriv_sq (p := p) K hp_two).det
  ∨
  (sinnottShiftedCharMatrix_nontriv_sq p K hp_odd hp_three hp_two).det *
      ((1 : Matrix PUnit.{1} PUnit.{1} ℂ) +
        Matrix.replicateRow PUnit.{1} (fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
          sinnottCorrectionRowVec (p := p) K hp_odd hp_three i) *
        (sinnottDiagonalEigenvalueMatrix_nontriv_sq
          p K hp_odd hp_three hp_two)⁻¹ *
        Matrix.replicateCol PUnit.{1} (fun (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
          -sinnottCorrectionColVec (p := p) K
            ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val)).det =
    -(charMatrix_K_plus_nontriv_sq (p := p) K hp_two).det

open Classical in
/-- The assertion that the nontrivial character-matrix determinant is a unit. -/
def CharMatrixKplusNontrivDetUnit
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)] : Prop :=
  IsUnit (charMatrix_K_plus_nontriv_sq (p := p) K hp_two).det

open Classical in
/-- The assertion that the nontrivial diagonal eigenvalue determinant is a unit. -/
def SinnottDiagonalEigenvalueDetUnit
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] : Prop :=
  IsUnit (sinnottDiagonalEigenvalueMatrix_nontriv_sq
    p K hp_odd hp_three hp_two).det

open Classical in
/-- Applies the rank-one determinant lemma to the diagonal eigenvalue matrix. -/
theorem det_D_nontriv_sq_sub_rank_one_via_matrix_det_lemma
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    (hD : SinnottDiagonalEigenvalueDetUnit (p := p) K hp_odd hp_three hp_two) :
    (sinnottDiagonalEigenvalueMatrix_nontriv_sq p K hp_odd hp_three hp_two +
      Matrix.replicateCol PUnit.{1} (fun (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
          -sinnottCorrectionColVec (p := p) K
            ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val) *
        Matrix.replicateRow PUnit.{1} (fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
          sinnottCorrectionRowVec (p := p) K hp_odd hp_three i)).det =
      (sinnottDiagonalEigenvalueMatrix_nontriv_sq p K hp_odd hp_three hp_two).det *
        ((1 : Matrix PUnit.{1} PUnit.{1} ℂ) +
          Matrix.replicateRow PUnit.{1} (fun (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            sinnottCorrectionRowVec (p := p) K hp_odd hp_three i) *
          (sinnottDiagonalEigenvalueMatrix_nontriv_sq
            p K hp_odd hp_three hp_two)⁻¹ *
          Matrix.replicateCol PUnit.{1} (fun (w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            -sinnottCorrectionColVec (p := p) K
              ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val)).det := by
  simp only [SinnottDiagonalEigenvalueDetUnit] at hD
  exact Matrix.det_add_replicateCol_mul_replicateRow hD _ _

/-- Expresses a vector outer product using `replicateCol` and `replicateRow`. -/
theorem matrix_of_col_row_eq_replicate
    {α : Type*} [NonUnitalNonAssocSemiring α] {m n : Type*}
    (f : m → α) (g : n → α) :
    (Matrix.of (fun (w : m) (i : n) ↦ f w * g i)) =
      Matrix.replicateCol PUnit.{1} f * Matrix.replicateRow PUnit.{1} g := by
  exact Matrix.vecMulVec_eq PUnit.{1} f g

open Classical in
/-- Rewrites the rank-one determinant into the form used by the determinant lemma. -/
theorem det_D_nontriv_sq_sub_rank_one_apply
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    (hD : SinnottDiagonalEigenvalueDetUnit (p := p) K hp_odd hp_three hp_two) :
    (sinnottDiagonalEigenvalueMatrix_nontriv_sq p K hp_odd hp_three hp_two -
      Matrix.of (fun (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        sinnottCorrectionColVec (p := p) K
            ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val *
          sinnottCorrectionRowVec (p := p) K hp_odd hp_three i)).det =
      (sinnottDiagonalEigenvalueMatrix_nontriv_sq p K hp_odd hp_three hp_two).det *
        ((1 : Matrix PUnit.{1} PUnit.{1} ℂ) +
          Matrix.replicateRow PUnit.{1} (fun (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            sinnottCorrectionRowVec (p := p) K hp_odd hp_three i) *
          (sinnottDiagonalEigenvalueMatrix_nontriv_sq
            p K hp_odd hp_three hp_two)⁻¹ *
          Matrix.replicateCol PUnit.{1} (fun (w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            -sinnottCorrectionColVec (p := p) K
              ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val)).det := by
  have h_eq : (sinnottDiagonalEigenvalueMatrix_nontriv_sq p K hp_odd hp_three hp_two -
      Matrix.of (fun (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        sinnottCorrectionColVec (p := p) K
            ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val *
          sinnottCorrectionRowVec (p := p) K hp_odd hp_three i)) =
      sinnottDiagonalEigenvalueMatrix_nontriv_sq p K hp_odd hp_three hp_two +
        Matrix.replicateCol PUnit.{1} (fun (w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            -sinnottCorrectionColVec (p := p) K
              ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val) *
          Matrix.replicateRow PUnit.{1} (fun (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            sinnottCorrectionRowVec (p := p) K hp_odd hp_three i) := by
    rw [← matrix_of_col_row_eq_replicate]
    ext w i
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply]
    ring
  rw [h_eq]
  exact det_D_nontriv_sq_sub_rank_one_via_matrix_det_lemma
    (p := p) K hp_odd hp_three hp_two hD

open Classical in
/-- Combines the shifted-matrix factorization with the rank-one determinant identity. -/
theorem det_charMatrix_sq_mul_det_A_sub_B_eq_prod_qe_mul_det_D'_mul_scalar
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [Finite {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀}]
    (h_diagDet : SinnottDiagonalEigenvalueDetUnit
      (p := p) K hp_odd hp_three hp_two) :
    (charMatrix_K_plus_nontriv_sq (p := p) K hp_two).det *
        (Matrix.of fun (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
            (w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)).det =
      (∏ ξ ∈ (Finset.univ : Finset
          (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1,
        quotientEigenvalue p ξ) *
        ((sinnottShiftedCharMatrix_nontriv_sq p K hp_odd hp_three hp_two).det *
        ((1 : Matrix PUnit.{1} PUnit.{1} ℂ) +
          Matrix.replicateRow PUnit.{1} (fun (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            sinnottCorrectionRowVec (p := p) K hp_odd hp_three i) *
          (sinnottDiagonalEigenvalueMatrix_nontriv_sq
            p K hp_odd hp_three hp_two)⁻¹ *
          Matrix.replicateCol PUnit.{1} (fun (w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            -sinnottCorrectionColVec (p := p) K
              ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val)).det) := by
  rw [det_charMatrix_nontriv_sq_mul_det_A_sub_B (p := p) K hp_odd hp_three hp_two,
    det_D_nontriv_sq_sub_rank_one_apply (p := p) K hp_odd hp_three hp_two h_diagDet,
    det_sinnottDiagonalEigenvalueMatrix_nontriv_sq
      (p := p) K hp_odd hp_three hp_two, mul_assoc]

/-- Cancels a nonzero factor from an equality with a sign ambiguity. -/
theorem _root_.BernoulliRegular.FLT37.Sinnott.cancel_disjunction_helper
    {a b c q : ℂ} (h_chain : c * b = q * a) (h_disj : a = c ∨ a = -c)
    (h_c_ne : c ≠ 0) :
    b = q ∨ b = -q := by
  rcases h_disj with h_pos | h_neg
  · left
    rw [h_pos, show q * c = c * q by ring] at h_chain
    exact mul_left_cancel₀ h_c_ne h_chain
  · right
    rw [h_neg, show q * -c = c * -q by ring] at h_chain
    exact mul_left_cancel₀ h_c_ne h_chain

open Classical in
/-- Derives `DetASubBEqProdNontrivialQe` from the three named hypotheses. -/
theorem detASubBEqProdNontrivialQe_of_named_hypotheses
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [Finite {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀}]
    (h_charDet : IsUnit (charMatrix_K_plus_nontriv_sq (p := p) K hp_two).det)
    (h_diagDet : SinnottDiagonalEigenvalueDetUnit
      (p := p) K hp_odd hp_three hp_two)
    (h_sinnott : SinnottCharMatrixDetIdentity
      (p := p) K hp_odd hp_three hp_two) :
    DetASubBEqProdNontrivialQe (p := p) K := by
  have h_chain := det_charMatrix_sq_mul_det_A_sub_B_eq_prod_qe_mul_det_D'_mul_scalar
    (p := p) K hp_odd hp_three hp_two h_diagDet
  have h_unit_ne : (charMatrix_K_plus_nontriv_sq p K hp_two).det ≠ 0 :=
    IsUnit.ne_zero h_charDet
  have h_cast_det :
      (((sinnottMatrixA p K - sinnottMatrixB p K).det : ℝ) : ℂ) =
      (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
          (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)).det := by
    rw [show (((sinnottMatrixA p K - sinnottMatrixB p K).det : ℝ) : ℂ) =
        Complex.ofRealHom (sinnottMatrixA p K - sinnottMatrixB p K).det by rfl,
      Complex.ofRealHom.map_det]
    rfl
  rcases cancel_disjunction_helper h_chain h_sinnott h_unit_ne with h_pos | h_neg
  · refine Or.inl ?_
    rw [h_cast_det]
    convert h_pos using 3
    congr 1
    exact Subsingleton.elim _ _
  · refine Or.inr ?_
    rw [h_cast_det]
    convert h_neg using 4
    congr 1
    exact Subsingleton.elim _ _

end Sinnott

end FLT37

end BernoulliRegular

end
