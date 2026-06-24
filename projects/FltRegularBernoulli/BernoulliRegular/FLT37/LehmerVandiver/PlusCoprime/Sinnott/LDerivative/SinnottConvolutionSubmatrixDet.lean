import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.SinnottRankOnePerturbation

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Subtype sum equals Finset.erase sum**: for any Fintype `α`, decidable
equality, fixed `a₀ : α`, and function `f : α → ℂ`,

  `∑ x : {x // x ≠ a₀}, f x.val = ∑ x ∈ univ.erase a₀, f x`.

Bridges the subtype-restricted sum to the explicit Finset-erase form. -/
theorem sum_subtype_ne_eq_sum_erase
    {α : Type*} [Fintype α] [DecidableEq α] (a₀ : α) (f : α → ℂ)
    [Fintype {x : α // x ≠ a₀}] :
    ∑ x : {x : α // x ≠ a₀}, f x.val =
      ∑ x ∈ (Finset.univ : Finset α).erase a₀, f x :=
  (Finset.sum_subtype ((Finset.univ : Finset α).erase a₀)
    (fun x => by simp [Finset.mem_erase]) f).symm

/-- **Character-eigenvalue of `(A - B)` along columns**:

For any character `ξ : MulChar (CyclotomicEvenDelta p) ℂ` and family index `i`,

  `∑_{w ≠ w₀} ξ(k(w)) · ((A-B)[i,w] : ℂ)
    = (ξ(q(famIdx i))⁻¹ - 1) · qe(ξ)
        - ξ(k(w₀)) · (M_even[k(w₀), q(famIdx i)] - M_even[k(w₀), 1])`.

Composes the K⁺/CE bridge with the restricted char-orthogonality identity
via the subtype-to-Finset.erase translation. -/
theorem sum_char_sinnottMatrix_A_sub_B_eigenvalue
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    [Fintype {w : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [Finite {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀}]
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    ∑ w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
      ξ (kplusEmbeddingIndexQuotient (p := p) K w.val) *
        ((((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)) =
    (ξ (BernoulliRegular.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i))⁻¹ - 1) *
        quotientEigenvalue p ξ -
      ξ (kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀) *
        (convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotient (p := p) K
            NumberField.Units.dirichletUnitTheorem.w₀)
          (BernoulliRegular.cyclotomicEvenDeltaQuotient p
            (familyIndexAsUnit p K hp_odd hp_three i)) -
        convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotient (p := p) K
            NumberField.Units.dirichletUnitTheorem.w₀) 1) := by
  letI : Fintype {c : BernoulliRegular.CyclotomicEvenDelta p //
      c ≠ kplusEmbeddingIndexQuotient (p := p) K
        NumberField.Units.dirichletUnitTheorem.w₀} :=
    Fintype.ofFinite _
  rw [sum_kplus_not_w₀_char_sinnottMatrix_A_sub_B (p := p) K hp_odd hp_three hp_two ξ i,
    sum_subtype_ne_eq_sum_erase
      (kplusEmbeddingIndexQuotient (p := p) K
        NumberField.Units.dirichletUnitTheorem.w₀)
      (fun c => ξ c * (convolutionMatrixLogNormEven p c
          (BernoulliRegular.cyclotomicEvenDeltaQuotient p
            (familyIndexAsUnit p K hp_odd hp_three i)) -
        convolutionMatrixLogNormEven p c 1))]
  exact sum_char_convolutionMatrixLogNormEven_col_diff_restricted (p := p) ξ
    (BernoulliRegular.cyclotomicEvenDeltaQuotient p
      (familyIndexAsUnit p K hp_odd hp_three i))
    (kplusEmbeddingIndexQuotient (p := p) K
      NumberField.Units.dirichletUnitTheorem.w₀)

/-- **Unweighted row-sum of `(A - B)` is the w₀-correction term**:

  `∑_{w ≠ w₀} ((A-B)[i,w] : ℂ)
    = -(M_even[k(w₀), q(famIdx i)] - M_even[k(w₀), 1])`.

Direct corollary of `sum_char_sinnottMatrix_A_sub_B_eigenvalue` at the
trivial character ξ = 1: `(1((q(famIdx i))⁻¹) - 1) · qe(1) = 0`, leaving
only the correction term. This captures the rank-deficiency of `A - B`
at the trivial character. -/
theorem sum_sinnottMatrix_A_sub_B_trivial
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    [Fintype {w : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [Finite {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀}]
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    ∑ w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
      ((((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)) =
    -(convolutionMatrixLogNormEven p
        (kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀)
        (BernoulliRegular.cyclotomicEvenDeltaQuotient p
          (familyIndexAsUnit p K hp_odd hp_three i)) -
      convolutionMatrixLogNormEven p
        (kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀) 1) := by
  have h := sum_char_sinnottMatrix_A_sub_B_eigenvalue (p := p) K hp_odd hp_three hp_two
    (1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) i
  have h_one_apply : ∀ c : BernoulliRegular.CyclotomicEvenDelta p,
      (1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) c = 1 := fun c =>
    MulChar.one_apply (Group.isUnit c)
  simp only [h_one_apply, one_mul] at h
  rw [h]
  ring

/-- **Sinnott `(A - B)` entry via shifted bijection**:
`(A - B)[i, w]` re-expressed using `kplusEmbeddingIndexQuotientShifted` (which
sends w₀ → 1). The entry's column reference shifts to
`k_shifted(w) * k(w₀)` (compensating for the shift). -/
theorem sinnottMatrix_A_sub_B_apply_eq_sub_shifted
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ) =
      convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotientShifted (p := p) K w.val *
            kplusEmbeddingIndexQuotient (p := p) K
              NumberField.Units.dirichletUnitTheorem.w₀)
          (BernoulliRegular.cyclotomicEvenDeltaQuotient p
            (familyIndexAsUnit p K hp_odd hp_three i)) -
        convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotientShifted (p := p) K w.val *
            kplusEmbeddingIndexQuotient (p := p) K
              NumberField.Units.dirichletUnitTheorem.w₀) 1 := by
  rw [sinnottMatrix_A_sub_B_apply_eq_sub p K hp_odd hp_three i w]
  unfold kplusEmbeddingIndexQuotientShifted
  rw [show (kplusEmbeddingIndexQuotient p K w.val *
      (kplusEmbeddingIndexQuotient p K
        NumberField.Units.dirichletUnitTheorem.w₀)⁻¹) *
      kplusEmbeddingIndexQuotient p K
        NumberField.Units.dirichletUnitTheorem.w₀ =
      kplusEmbeddingIndexQuotient p K w.val by group]

/-- **Inverse of `kplusEmbeddingIndexQuotient` at `w₀` is its own inverse**:
algebraic identity `k(w₀)⁻¹ · k(w₀) = 1`. -/
@[simp]
theorem kplusEmbeddingIndexQuotient_w₀_inv_mul
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    (kplusEmbeddingIndexQuotient (p := p) K
        NumberField.Units.dirichletUnitTheorem.w₀)⁻¹ *
      kplusEmbeddingIndexQuotient (p := p) K
        NumberField.Units.dirichletUnitTheorem.w₀ = 1 :=
  inv_mul_cancel _

/-- **Row 1 of `convolutionMatrixLogNormEven` equals `convolutionLogNormDescended`**.

This is the structural fact identifying the "B-row" structure: the row at
index 1 of `M_even` is just the descended log-norm function. -/
@[simp]
theorem convolutionMatrixLogNormEven_one_apply
    (b : BernoulliRegular.CyclotomicEvenDelta p) :
    convolutionMatrixLogNormEven p 1 b = convolutionLogNormDescended p b :=
  convolutionMatrixLogNormEven_row_one p b

/-- **`sinnottMatrix(A) - sinnottMatrix(B)` as rank-1 perturbation of a
"shifted convolution submatrix"** — both casts to ℂ. The B-matrix is rank-1
because rows are all equal (= the row-1 of M_even at the column-side
embedding-index).

Specifically:
`(((sinnottMatrixA - sinnottMatrixB)[i, w] : ℝ) : ℂ) =
  Matrix.of (fun i w => M_even[k(w), q(famIdx i)])[i, w] -
  (Matrix.of (fun i w => M_even[k(w), 1]))[i, w]`

The 2nd matrix has rows independent of i (rank ≤ 1). -/
theorem sinnottMatrix_A_sub_B_as_rank_one_perturbation
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ) =
      (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotient (p := p) K w.val)
          (BernoulliRegular.cyclotomicEvenDeltaQuotient p
            (familyIndexAsUnit p K hp_odd hp_three i))) i w -
      (Matrix.of fun (_ : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotient (p := p) K w.val) 1) i w := by
  rw [sinnottMatrix_A_sub_B_apply_eq_sub p K hp_odd hp_three i w]
  rfl

/-- **The 'shifted-convolution sub-matrix' U for `(A - B)`'s rank-1 decomposition**:
the matrix `U[i, w] := M_even[k(w), q(famIdx i)]`. This is the "non-constant"
part of `(A - B)` — the rank-1 perturbation has form `(A - B) = U - 1·v^T`
where `v(w) = M_even[k(w), 1]`. -/
noncomputable def sinnottShiftedConvolutionMatrix
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    Matrix {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℂ :=
  Matrix.of fun i w =>
    convolutionMatrixLogNormEven p
      (kplusEmbeddingIndexQuotient (p := p) K w.val)
      (BernoulliRegular.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i))

/-- **The rank-1 perturbation row vector for `(A - B)`'s decomposition**:
`v(w) := M_even[k(w), 1]`. -/
noncomputable def sinnottRankOnePerturbationVec
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) : ℂ :=
  convolutionMatrixLogNormEven p
    (kplusEmbeddingIndexQuotient (p := p) K w.val) 1

/-- **Matrix-level decomposition `(A - B) = U - 1·v^T`**:

The ℂ-cast `(A - B)` matrix decomposes as a rank-1 perturbation of
the shifted-convolution submatrix:

  `((A - B) : Matrix _ _ ℝ → ℂ) = sinnottShiftedConvolutionMatrix - 1·v^T`

where `1` is the all-ones column vector, `v^T` the row of
`sinnottRankOnePerturbationVec`. -/
theorem sinnottMatrix_A_sub_B_eq_U_sub_rank_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    (fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)) =
      fun i w =>
        sinnottShiftedConvolutionMatrix p K hp_odd hp_three i w -
          sinnottRankOnePerturbationVec p K w := by
  funext i w
  rw [sinnottMatrix_A_sub_B_apply_eq_sub p K hp_odd hp_three i w]
  rfl

/-- **`sinnottRankOnePerturbationVec` simp**: unwinds to the convolution-matrix entry. -/
@[simp]
theorem sinnottRankOnePerturbationVec_apply
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    sinnottRankOnePerturbationVec p K w =
      convolutionMatrixLogNormEven p
        (kplusEmbeddingIndexQuotient (p := p) K w.val) 1 :=
  rfl

/-- **`sinnottShiftedConvolutionMatrix` simp**: unwinds to the convolution-matrix entry. -/
@[simp]
theorem sinnottShiftedConvolutionMatrix_apply
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    sinnottShiftedConvolutionMatrix p K hp_odd hp_three i w =
      convolutionMatrixLogNormEven p
        (kplusEmbeddingIndexQuotient (p := p) K w.val)
        (BernoulliRegular.cyclotomicEvenDeltaQuotient p
          (familyIndexAsUnit p K hp_odd hp_three i)) :=
  rfl

/-- **`sinnottShiftedConvolutionMatrix` is the transpose of a submatrix of
`convolutionMatrixLogNormEven`**:

  `sinnottShiftedConvolutionMatrix p K hp_odd hp_three =
   ((convolutionMatrixLogNormEven p).submatrix
     (fun w => kplusEmbeddingIndexQuotient K w.val)
     (fun i => q (familyIndexAsUnit i)))ᵀ`. -/
theorem sinnottShiftedConvolutionMatrix_eq_submatrix_transpose
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    sinnottShiftedConvolutionMatrix p K hp_odd hp_three =
      Matrix.transpose ((convolutionMatrixLogNormEven p).submatrix
        (fun (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
          kplusEmbeddingIndexQuotient (p := p) K w.val)
        (fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
          BernoulliRegular.cyclotomicEvenDeltaQuotient p
            (familyIndexAsUnit p K hp_odd hp_three i))) :=
  rfl

/-- **Sinnott convolution matrix non-vanishing (named Prop)**: the determinant
of the shifted-convolution sub-matrix `U` is a unit in ℂ.

Equivalent to: for all `χ : MulChar (CyclotomicEvenDelta p) ℂ`, the quotient
eigenvalue `qe(χ)` is non-zero. For `χ = 1`: `qe(1) = log(p)/2 ≠ 0` (shipped).
For `χ ≠ 1`: `qe(χ) = -DLS(dχ χ)/2`; non-vanishing is equivalent to
`L(1, dχ χ) ≠ 0` (Dirichlet non-vanishing). -/
def SinnottConvolutionMatrixDetUnit
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    [Fintype {w : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] : Prop :=
  IsUnit (sinnottShiftedConvolutionMatrix p K hp_odd hp_three).det

/-- **`sinnottRankOnePerturbationVec` in `convolutionLogNormDescended` form**:
`v(w) = convolutionLogNormDescended p (kplusEmbeddingIndexQuotient w.val)`. -/
theorem sinnottRankOnePerturbationVec_eq_convolutionLogNormDescended
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    sinnottRankOnePerturbationVec p K w =
      convolutionLogNormDescended p
        (kplusEmbeddingIndexQuotient (p := p) K w.val) :=
  convolutionMatrixLogNormEven_col_one p _

/-- **Determinant of Sinnott matrix in `2^((p-3)/2) · det(A-B)` form**: the
factor-of-2 extraction at the determinant level. -/
theorem det_sinnottMatrix_eq_pow_two_mul_det
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    [Fintype {w : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] :
    (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        Real.log
          (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
            ((FLT37.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (NumberField.maximalRealSubfield K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))).det =
      (2 : ℝ) ^ Fintype.card {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀} *
        (sinnottMatrixA p K - sinnottMatrixB p K).det := by
  rw [sinnottMatrix_eq_two_smul_A_sub_B p K hp_odd hp_three]
  exact Matrix.det_smul (sinnottMatrixA p K - sinnottMatrixB p K) 2

end Sinnott

end FLT37

end BernoulliRegular

end
