import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.DetBridge.CharacterActionRankOneDecomposition

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in
open Classical in
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
  classical
  -- det((A-B)) = det((A-B)^T)
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

/-! ## Factorization of D_nontriv_sq: `D = diag(qe) · D'`

The diagonal eigenvalue matrix factors as `diag(qe) · D'` where
`D'[ξ, i] = ξ(b)⁻¹ - 1` (the "shifted" character matrix). This
allows extraction of `∏_{χ ≠ 1} qe(χ)` from `det(D_nontriv_sq)`. -/

open Classical in
/-- **The "shifted" character matrix `D'`**: `D'[ξ, i] = ξ(q(famIdx i))⁻¹ - 1`. -/
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

open Classical in
/-- **Square version of `sinnottShiftedCharMatrix_nontriv`**: reindexed via
`equivNontrivCharKplusNeW₀.symm`. -/
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

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- **D_nontriv_sq factors as `diag(qe) · D'_nontriv_sq`**:

  `sinnottDiagonalEigenvalueMatrix_nontriv_sq =
   Matrix.diagonal (fun w ↦ qe(...) · ξ-factor) · sinnottShiftedCharMatrix_nontriv_sq`

The diagonal factor is `qe(ξ)` (after reindexing w → ξ via equiv). -/
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
  · simp
    ring
  · intros b _ hb
    simp [hb.symm]
  · intro h
    exact absurd (Finset.mem_univ w) h

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- **`det(D_nontriv_sq) = (∏_{χ ≠ 1} qe(χ)) · det(D'_nontriv_sq)`**:
direct consequence of the diag(qe) · D' factorization. The reindex
of the product via `equivNontrivCharKplusNeW₀.symm` translates the
Pi over `{w ≠ w₀}` to a Pi over `{ξ ≠ 1}`. -/
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
  classical
  rw [sinnottDiagonalEigenvalueMatrix_nontriv_sq_eq_diag_mul_shifted
    (p := p) K hp_odd hp_three hp_two]
  rw [Matrix.det_mul, Matrix.det_diagonal]
  congr 1
  -- ∏ w : T_w, qe((equiv.symm w).val) = ∏ ξ ∈ univ.erase 1, qe ξ
  -- Use Equiv.prod_comp directly: ∏ w, f w = ∏ ξ, f (equiv ξ) for any equiv.
  rw [← Equiv.prod_comp (equivNontrivCharKplusNeW₀ p K hp_two)
    (fun w ↦ quotientEigenvalue p
      ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val)]
  -- Goal: ∏ ξ : {ξ // ξ ≠ 1}, qe(((equiv.symm) (equiv ξ)).val) = ∏ ...erase 1, qe
  simp only [Equiv.symm_apply_apply]
  -- Goal: ∏ ξ : {ξ // ξ ≠ 1}, qe(ξ.val) = ∏ ξ ∈ univ.erase 1, qe ξ
  rw [Finset.prod_subtype (p := fun ξ : MulChar
      (BernoulliRegular.CyclotomicEvenDelta p) ℂ => ξ ≠ 1)
    (s := Finset.univ.erase (1 : MulChar
      (BernoulliRegular.CyclotomicEvenDelta p) ℂ))
    (fun ξ ↦ by simp [Finset.mem_erase])]

/-! ## Substantive sub-named-hypothesis: pure character-algebra identity

Combining everything above, `DetASubBEqProdNontrivialQe` reduces (under
parametric IsUnit hypotheses on `det(D_nontriv_sq)` and Dirichlet
non-vanishing) to a **purely character-matrix-algebra identity**:

  `det(D'_nontriv_sq) · scalar = ±det(charMatrix_nontriv_sq)`

where:
- `D'_nontriv_sq` is the "shifted character matrix" (no qe factors).
- `charMatrix_nontriv_sq` is the standard character matrix on K⁺ places.
- `scalar = 1 - row_corr · D_nontriv_sq⁻¹ · col_kw0` (from matrix det lemma).

All `qe(χ)` factors have been extracted; this is a clean character-orthogonality
identity. -/

open Classical in
/-- **Substantive pure character-matrix Sinnott identity** (named Prop):
   `det(D'_nontriv_sq) · scalar = ±det(charMatrix_K_plus_nontriv_sq)`

where `scalar = (1 - rowCorr · D_nontriv_sq⁻¹ · colKw0).det` (PUnit-1×1
scalar correction from matrix det lemma).

The squared form follows from the linear form. The full Sinnott Frobenius
identity reduces to this single character-algebra equation. -/
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
/-- **`IsUnit (det charMatrix_K_plus_nontriv_sq)` (named Prop)**: equivalent
to the character matrix being non-singular, which by character orthogonality
follows from the Pontryagin-duality `det ≠ 0` of the full character matrix
plus a sub-minor non-vanishing condition. -/
def CharMatrixKplusNontrivDetUnit
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)] : Prop :=
  IsUnit (charMatrix_K_plus_nontriv_sq (p := p) K hp_two).det

open Classical in
/-- **`IsUnit (det D_nontriv_sq)` (named Prop)**: the diagonal eigenvalue
matrix is non-singular, equivalent to `qe(χ) ≠ 0` for all `χ ≠ 1`
(Dirichlet L-value non-vanishing) AND `IsUnit (det D'_nontriv_sq)`. -/
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

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- **Matrix det lemma applied to `D_nontriv_sq - col · row`**:
under `SinnottDiagonalEigenvalueDetUnit`:

  `det(D_nontriv_sq - col · row) = det(D_nontriv_sq) · (1 + row · D⁻¹ · col_neg).det`

where the rank-1 perturbation is packaged in mathlib's `replicateCol/replicateRow`
form. -/
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
  unfold SinnottDiagonalEigenvalueDetUnit at hD
  exact Matrix.det_add_replicateCol_mul_replicateRow hD _ _

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- **Bridge between `Matrix.of (fun w i ↦ f w · g i)` and
`replicateCol PUnit f * replicateRow PUnit g`**: the (outer product)
rank-1 matrix in two equivalent forms. -/
theorem matrix_of_col_row_eq_replicate
    {α : Type*} [NonUnitalNonAssocSemiring α] {m n : Type*}
    (f : m → α) (g : n → α) :
    (Matrix.of (fun (w : m) (i : n) ↦ f w * g i)) =
      Matrix.replicateCol PUnit.{1} f * Matrix.replicateRow PUnit.{1} g := by
  ext w i
  simp [Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- **`(D_nontriv_sq - Matrix.of (col · row)).det` via matrix det lemma form**:
the form shipped by `charMatrix_nontriv_sq_mul_A_sub_B_transpose_eq_...`
(`Matrix.of (col · row)`) translates to the matrix-det-lemma form
(`replicateCol * replicateRow`) by the identity above. -/
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
  -- Rewrite the `Matrix.of (col * row)` form as `replicateCol (-col) * replicateRow row`
  -- (note the sign goes to the col, making it `+ (replicateCol_neg * replicateRow)`).
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

set_option maxHeartbeats 4000000 in
-- This composed determinant identity elaborates several matrix reductions at once.
set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- **Composed identity: `det(charMat_sq) · det(A-B) = (∏ qe) · det(D'_sq) · scalar`**.
Combines all shipped pieces (det_mul on matrix equation + matrix det lemma +
diag-D' factorization). -/
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
  classical
  rw [det_charMatrix_nontriv_sq_mul_det_A_sub_B (p := p) K hp_odd hp_three hp_two]
  rw [det_D_nontriv_sq_sub_rank_one_apply
    (p := p) K hp_odd hp_three hp_two h_diagDet]
  rw [det_sinnottDiagonalEigenvalueMatrix_nontriv_sq
    (p := p) K hp_odd hp_three hp_two, mul_assoc]

open Classical in
/-- **Generic cancellation lemma for the final discharge**: abstract
algebraic step `c · b = q · a` and `a = ±c` imply `b = ±q`. Used to
avoid whnf on the massive matrix expressions in the Sinnott chain. -/
theorem _root_.BernoulliRegular.FLT37.Sinnott.cancel_disjunction_helper
    {a b c q : ℂ} (h_chain : c * b = q * a) (h_disj : a = c ∨ a = -c)
    (h_c_ne : c ≠ 0) :
    b = q ∨ b = -q := by
  rcases h_disj with h_pos | h_neg
  · left
    rw [h_pos] at h_chain
    rw [show q * c = c * q from by ring] at h_chain
    exact mul_left_cancel₀ h_c_ne h_chain
  · right
    rw [h_neg] at h_chain
    rw [show q * -c = c * -q from by ring] at h_chain
    exact mul_left_cancel₀ h_c_ne h_chain

set_option maxHeartbeats 8000000 in
-- The final determinant discharge unfolds named hypotheses and needs a larger heartbeat budget.
set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- **Final discharge: `DetASubBEqProdNontrivialQe` from the three named
hypotheses** — using `IsUnit (...).det` directly to avoid expensive whnf
through the named-Prop defs. -/
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
        Complex.ofRealHom (sinnottMatrixA p K - sinnottMatrixB p K).det from rfl]
    rw [Complex.ofRealHom.map_det]
    rfl
  -- Apply cancel_disjunction_helper to get the matrix-det form of the conclusion.
  have h_disj := cancel_disjunction_helper h_chain h_sinnott h_unit_ne
  -- h_disj : (det matrix_of_complex_entries = ∏ qe) ∨ (... = -∏ qe)
  -- Goal: DetASubBEqProdNontrivialQe — which unfolds to the same with (det A_sub_B : ℝ : ℂ).
  -- Use h_cast_det to bridge.
  rcases h_disj with h_pos | h_neg
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

/-! ## Summary: PF-1 substantive content reduced to three named hypotheses

`DetASubBEqProdNontrivialQe` (the substantive Sinnott Frobenius identity)
follows from the conjunction:

  1. `SinnottCharMatrixDetIdentity` — pure character-matrix-algebra identity.
  2. `SinnottDiagonalEigenvalueDetUnit` — Dirichlet non-vanishing.
  3. `CharMatrixKplusNontrivDetUnit` — character-matrix non-singularity.

All three are standard Frobenius/Dirichlet-theory facts but require
substantial development to discharge in Lean.

Once `DetASubBEqProdNontrivialQe` is discharged, the shipped
`kummerDirichletDeterminant_of_detASubBEqProdNontrivialQe` gives
`KummerDirichletDeterminant` (PF-1 target). -/

end Sinnott

end FLT37

end BernoulliRegular

end
