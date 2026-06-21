import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.LDerivative

/-!
# Bridge from substantive matrix content to RegOf-squared form

The corrected `RegOfFamilySqEqProdNontrivialQeSq` requires the factor
`2^(p-3)`. This file ships the algebraic bridge:

  `(det(A − B) : ℂ)² = (∏_{ξ ≠ 1} qe(ξ))²` ⟹
    `regOfFamily² = 2^(p-3) · (∏_{ξ ≠ 1} qe(ξ))²`

via `regOfFamily = |det M_Sinnott|` and `det M_Sinnott = 2^N · det(A − B)`. -/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace FLT37

namespace Sinnott


variable (p : ℕ) [hp : Fact p.Prime]

open Classical in
/-- **Cardinality of non-w₀ K⁺-places equals `(p-3)/2`**. -/
theorem card_kplus_ne_w₀_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (_hp_two : 2 < p) :
    Fintype.card {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} =
      (p - 3) / 2 := by
  have h_rank_eq : NumberField.Units.rank
      (NumberField.maximalRealSubfield K) = (p - 3) / 2 := by
    rw [NumberField.IsCMField.units_rank_eq_units_rank (K := K)]
    exact BernoulliRegular.units_rank_eq_prime_sub_three_div_two (p := p) (K := K)
  have h_rank_def : NumberField.Units.rank
      (NumberField.maximalRealSubfield K) =
      Fintype.card (NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K)) - 1 := rfl
  have h_card_compl :=
    Fintype.card_subtype_compl (α := NumberField.InfinitePlace
      (NumberField.maximalRealSubfield K)) (p := fun w =>
      w = NumberField.Units.dirichletUnitTheorem.w₀)
  rw [Fintype.card_subtype_eq] at h_card_compl
  have h_eq : Fintype.card {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} =
      Fintype.card {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) // ¬ w =
        NumberField.Units.dirichletUnitTheorem.w₀} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
  rw [h_eq, h_card_compl]
  omega

open Classical in
/-- **`regOfFamily² = 2^(p-3) · det(A-B)²` in ℝ**. -/
theorem regOfFamily_sq_eq_two_pow_mul_det_A_sub_B_sq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p) :
    (NumberField.Units.regOfFamily
        (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ^ 2 =
      (2 : ℝ) ^ (p - 3) *
        ((sinnottMatrixA p K - sinnottMatrixB p K).det) ^ 2 := by
  have h_card := card_kplus_ne_w₀_eq (p := p) K hp_two
  have h_reg_eq_abs_det := regOfFamily_cyclotomicUnitFamilyKplus_eq_det
    (p := p) (K := K) hp_odd hp_three
  have h_det_eq_two_pow := det_sinnottMatrix_eq_pow_two_mul_det
    (p := p) K hp_odd hp_three
  have h_reg_combined : NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
      |(2 : ℝ) ^ Fintype.card {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀} *
        (sinnottMatrixA p K - sinnottMatrixB p K).det| :=
    h_reg_eq_abs_det.trans (congr_arg abs h_det_eq_two_pow)
  have h_two_pow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ Fintype.card
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := by positivity
  rw [h_reg_combined, abs_mul, abs_of_nonneg h_two_pow_nn, mul_pow, sq_abs]
  congr 1
  rw [← pow_mul, h_card]
  congr 1
  have h_p_odd : Odd p := hp.out.odd_of_ne_two hp_odd
  rcases h_p_odd with ⟨k, hk⟩
  omega

open Classical in
/-- **`RegOfFamilySqEqProdNontrivialQeSq` from `DetASubBSqEqProdNontrivialQeSq`**:
the corrected squared form follows from the substantive matrix-level
identity by extracting the `2^(p-3)` factor algebraically.

This reduces PF-1's substantive content to the rank-1 Frobenius
identity on `(A − B)`. -/
theorem regOfFamilySqEqProdNontrivialQeSq_of_detASubBSqEqProdQeSq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h : DetASubBSqEqProdNontrivialQeSq (p := p) K) :
    RegOfFamilySqEqProdNontrivialQeSq (p := p) K hp_odd hp_three := by
  unfold RegOfFamilySqEqProdNontrivialQeSq
  unfold DetASubBSqEqProdNontrivialQeSq at h
  have h_reg_sq_R := regOfFamily_sq_eq_two_pow_mul_det_A_sub_B_sq
    (p := p) K hp_odd hp_three hp_two
  have h_reg_sq_C : ((NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) : ℝ) : ℂ) ^ 2 =
      (2 : ℂ) ^ (p - 3) *
        (((sinnottMatrixA p K - sinnottMatrixB p K).det : ℝ) : ℂ) ^ 2 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) h_reg_sq_R
    push_cast at this
    exact this
  rw [h_reg_sq_C, h]

/-! ## Matrix determinant lemma for the rank-1 perturbation

The matrix `(A - B) = U - 1·v^T` is a rank-1 perturbation of the
shifted-convolution submatrix `U = sinnottShiftedConvolutionMatrix`.
Apply mathlib's `Matrix.det_add_replicateCol_mul_replicateRow` under
`SinnottConvolutionMatrixDetUnit` (i.e., `IsUnit (U.det)`). -/

open Classical in
/-- **Matrix-level rank-1 form of `(A - B)`**: cast to ℂ, the matrix
`(A - B)` equals `U + replicateCol PUnit.{1} (-1) * replicateRow PUnit.{1} v`
where `U = sinnottShiftedConvolutionMatrix` and `v = sinnottRankOnePerturbationVec`.

This packages the shipped `sinnottMatrix_A_sub_B_eq_U_sub_rank_one`
into the precise form `A + replicateCol PUnit.{1} u * replicateRow PUnit.{1} v`
expected by mathlib's matrix determinant lemma. -/
theorem sinnottMatrix_A_sub_B_as_replicateCol_replicateRow_perturbation
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)) =
      sinnottShiftedConvolutionMatrix p K hp_odd hp_three +
        Matrix.replicateCol PUnit.{1} (fun _ => (-1 : ℂ)) *
          Matrix.replicateRow PUnit.{1} (fun w =>
            sinnottRankOnePerturbationVec p K w) := by
  ext i w
  have h_app := congrFun (congrFun
    (sinnottMatrix_A_sub_B_eq_U_sub_rank_one (p := p) K hp_odd hp_three) i) w
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.replicateCol_apply, Matrix.replicateRow_apply]
  rw [h_app, Fintype.sum_unique]
  ring

open Classical in
/-- **Matrix determinant lemma for `(A − B)`**: under
`SinnottConvolutionMatrixDetUnit`, the determinant of `(A − B)` (cast
to ℂ) factors as `det(U) · (1 + replicateRow v · U⁻¹ · replicateCol (-1))`
where the latter is a PUnit.{1}-indexed 1×1 determinant (essentially a scalar
correction). -/
theorem det_sinnottMatrix_A_sub_B_via_rank_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    (hU : SinnottConvolutionMatrixDetUnit (p := p) K hp_odd hp_three) :
    (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)).det =
      (sinnottShiftedConvolutionMatrix p K hp_odd hp_three).det *
        ((1 : Matrix PUnit.{1} PUnit.{1} ℂ) +
          Matrix.replicateRow PUnit.{1} (fun w =>
              sinnottRankOnePerturbationVec p K w) *
            (sinnottShiftedConvolutionMatrix p K hp_odd hp_three)⁻¹ *
            Matrix.replicateCol PUnit.{1} (fun _ => (-1 : ℂ))).det := by
  unfold SinnottConvolutionMatrixDetUnit at hU
  rw [sinnottMatrix_A_sub_B_as_replicateCol_replicateRow_perturbation
    (p := p) K hp_odd hp_three]
  exact Matrix.det_add_replicateCol_mul_replicateRow hU _ _

/-! ## Scalar-correction reduction (named hypothesis)

After applying the matrix determinant lemma, `det(A - B) = det(U) · ε`
where `ε = (1 + replicateRow v · U⁻¹ · replicateCol (-1)).det` is the
PUnit.{1}-indexed 1×1 scalar correction.

The remaining substantive content (`DetASubBSqEqProdNontrivialQeSq`)
reduces to: `(det(U) · ε)² = (∏_{χ ≠ 1} qe(χ))²`. This is the cleanest
isolation of Sinnott's matrix-level identity. -/

open Classical in
/-- **Substantive scalar-correction identity** (named Prop): the squared
product of `det(U)` and the PUnit.{1}-1×1 scalar correction equals the
squared product of nontrivial eigenvalues:

  `(det(U) · ε)² = (∏_{χ ≠ 1} qe(χ))²`

where `ε = (1 + replicateRow v · U⁻¹ · replicateCol (-1)).det`.

This packages the remaining substantive Sinnott content (after the
matrix-det-lemma application) as a single named hypothesis. The proof
requires computing `det(U)` via the Jacobi cofactor / Frobenius
diagonalization of `M_even` and verifying that the scalar correction
absorbs the mismatch into a single product. -/
def DetUMulScalarSqEqProdNontrivialQeSq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] : Prop :=
  haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  haveI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  ((sinnottShiftedConvolutionMatrix p K hp_odd hp_three).det *
    ((1 : Matrix PUnit.{1} PUnit.{1} ℂ) +
      Matrix.replicateRow PUnit.{1} (fun w =>
          sinnottRankOnePerturbationVec p K w) *
        (sinnottShiftedConvolutionMatrix p K hp_odd hp_three)⁻¹ *
        Matrix.replicateCol PUnit.{1} (fun _ => (-1 : ℂ))).det) ^ 2 =
  (∏ ξ ∈ (Finset.univ : Finset
      (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1,
    quotientEigenvalue p ξ) ^ 2

open Classical in
/-- **`DetASubBSqEqProdNontrivialQeSq` from `DetUMulScalarSqEqProdNontrivialQeSq`**:
under `SinnottConvolutionMatrixDetUnit` (the IsUnit hypothesis allowing
matrix det lemma) and the corrected scalar-product identity, the
substantive matrix-level Frobenius identity holds.

Composition: `det(A − B) = det(U) · scalar` (by matrix det lemma)
gives `det(A − B)² = (det(U) · scalar)²`, matching the named hypothesis
to discharge `DetASubBSqEqProdNontrivialQeSq`. -/
theorem detASubBSqEqProdNontrivialQeSq_of_detUMulScalar_named
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    (hU : SinnottConvolutionMatrixDetUnit (p := p) K hp_odd hp_three)
    (h : DetUMulScalarSqEqProdNontrivialQeSq (p := p) K hp_odd hp_three) :
    DetASubBSqEqProdNontrivialQeSq (p := p) K := by
  classical
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  letI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  unfold DetASubBSqEqProdNontrivialQeSq
  unfold DetUMulScalarSqEqProdNontrivialQeSq at h
  have h_det := det_sinnottMatrix_A_sub_B_via_rank_one
    (p := p) K hp_odd hp_three hU
  -- Goal: (((det(A - B) : ℝ)) : ℂ)² = (∏ qe)²
  -- h_det: det((A - B) cast to ℂ as 2D matrix) = det(U) · scalar
  have h_cast_det : (((sinnottMatrixA p K - sinnottMatrixB p K).det : ℝ) : ℂ) =
      (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)).det := by
    rw [show (((sinnottMatrixA p K - sinnottMatrixB p K).det : ℝ) : ℂ) =
        Complex.ofRealHom (sinnottMatrixA p K - sinnottMatrixB p K).det from rfl,
      Complex.ofRealHom.map_det]
    rfl
  rw [h_cast_det, h_det, h]

open Classical in
/-- **Scalar correction in explicit numerical form**: the PUnit-1×1
determinant `(1 + replicateRow v · U⁻¹ · replicateCol (-1)).det` equals
the single scalar `1 - ∑_{w, w'} v(w) · U⁻¹[w, w']`. -/
theorem rank_one_scalar_correction_explicit
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] :
    ((1 : Matrix PUnit.{1} PUnit.{1} ℂ) +
      Matrix.replicateRow PUnit.{1} (fun w =>
          sinnottRankOnePerturbationVec p K w) *
        (sinnottShiftedConvolutionMatrix p K hp_odd hp_three)⁻¹ *
        Matrix.replicateCol PUnit.{1} (fun _ => (-1 : ℂ))).det =
      1 - ∑ w : {w : NumberField.InfinitePlace
          (NumberField.maximalRealSubfield K) //
          w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
        ∑ w' : {w : NumberField.InfinitePlace
          (NumberField.maximalRealSubfield K) //
          w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
          sinnottRankOnePerturbationVec p K w *
            (sinnottShiftedConvolutionMatrix p K hp_odd hp_three)⁻¹ w w' := by
  classical
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply,
    Matrix.replicateRow_apply, Matrix.replicateCol_apply, mul_neg_one,
    Finset.sum_neg_distrib]
  -- Goal: 1 + -∑ ... = 1 - ∑ ... (with sums in opposite order, Fubini).
  rw [Finset.sum_comm]
  ring

open Classical in
/-- **`det(A - B)` in explicit Frobenius-style form** (combining the
matrix det lemma application with the scalar simplification):

  `det((A - B) cast to ℂ) =
    det(U) · (1 - ∑_{w, w'} v(w) · U⁻¹[w, w'])`

where `U = sinnottShiftedConvolutionMatrix` and
`v = sinnottRankOnePerturbationVec`.

Combines `det_sinnottMatrix_A_sub_B_via_rank_one` (matrix det lemma)
with `rank_one_scalar_correction_explicit` (PUnit-1×1 simplification). -/
theorem det_sinnottMatrix_A_sub_B_explicit
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    (hU : SinnottConvolutionMatrixDetUnit (p := p) K hp_odd hp_three) :
    (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)).det =
      (sinnottShiftedConvolutionMatrix p K hp_odd hp_three).det *
        (1 - ∑ w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
          ∑ w' : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
            sinnottRankOnePerturbationVec p K w *
              (sinnottShiftedConvolutionMatrix p K hp_odd hp_three)⁻¹ w w') := by
  rw [det_sinnottMatrix_A_sub_B_via_rank_one (p := p) K hp_odd hp_three hU,
    rank_one_scalar_correction_explicit (p := p) K hp_odd hp_three]

/-! ## Reduction of squared content to linear form

`DetASubBSqEqProdNontrivialQeSq` (squared form) follows directly from
the linear form `det(A − B) = ε · ∏_{χ ≠ 1} qe(χ)` for any
`ε² = 1` (i.e., `ε ∈ {±1}`). Squaring absorbs the sign.

This is the cleanest formulation since Sinnott's identity is naturally
stated as `det(A − B) = ±∏ qe`, and the choice of sign depends on
enumeration conventions in the proof. -/

open Classical in
/-- **Linear form of `DetASubBSqEqProdNontrivialQeSq`**: the substantive
matrix-level identity stated in linear (not squared) form. The
`Or` allows both signs since the convention-dependent sign affects
neither the squared form nor the downstream `regOfFamily² = 2^(p-3) · (∏ qe)²`. -/
def DetASubBEqProdNontrivialQe
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] : Prop :=
  haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  haveI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  (((sinnottMatrixA p K - sinnottMatrixB p K).det : ℝ) : ℂ) =
    ∏ ξ ∈ (Finset.univ : Finset
        (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1,
      quotientEigenvalue p ξ
  ∨
  (((sinnottMatrixA p K - sinnottMatrixB p K).det : ℝ) : ℂ) =
    -∏ ξ ∈ (Finset.univ : Finset
        (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1,
      quotientEigenvalue p ξ

open Classical in
/-- **Squared form follows from linear form**: `DetASubBSqEqProdNontrivialQeSq`
follows from `DetASubBEqProdNontrivialQe` by squaring (the sign disappears). -/
theorem detASubBSqEqProdNontrivialQeSq_of_detASubBEqProdNontrivialQe
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    (h : DetASubBEqProdNontrivialQe (p := p) K) :
    DetASubBSqEqProdNontrivialQeSq (p := p) K := by
  classical
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  letI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  unfold DetASubBSqEqProdNontrivialQeSq
  unfold DetASubBEqProdNontrivialQe at h
  rcases h with h | h
  · rw [h]
  · rw [h]; ring

/-! ## Full PF-1 discharge from two parametric hypotheses

Composing all shipped reductions, the entire PF-1 chain `KummerDirichletDeterminant`
follows from just two parametric hypotheses:

1. `SinnottConvolutionMatrixDetUnit`: `IsUnit (det U)` (Dirichlet non-vanishing).
2. `DetASubBEqProdNontrivialQe`: `det(A − B) = ±∏_{χ ≠ 1} qe(χ)` (substantive Sinnott).

Note: the matrix-det-lemma chain `det_sinnottMatrix_A_sub_B_via_rank_one` is
SUFFICIENT but NOT NECESSARY for `DetASubBEqProdNontrivialQe` — the
substantive identity can be proven directly without going through U.
Hence `SinnottConvolutionMatrixDetUnit` may not be needed in the discharge
of `DetASubBEqProdNontrivialQe`. -/

open Classical in
/-- **PF-1 (`KummerDirichletDeterminant`) from substantive Sinnott identity**:
the complete chain `DetASubBEqProdNontrivialQe → KummerDirichletDeterminant`
via shipped reductions. -/
theorem kummerDirichletDeterminant_of_detASubBEqProdNontrivialQe
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h : DetASubBEqProdNontrivialQe (p := p) K) :
    BernoulliRegular.FLT37.Sinnott.KummerDirichletDeterminant p K hp_odd hp_three := by
  have h_sq := detASubBSqEqProdNontrivialQeSq_of_detASubBEqProdNontrivialQe
    (p := p) K h
  have h_reg := regOfFamilySqEqProdNontrivialQeSq_of_detASubBSqEqProdQeSq
    (p := p) K hp_odd hp_three hp_two h_sq
  exact KummerDirichletDeterminant_of_regOfFamilySqEqProdNontrivialQeSq
    (p := p) K hp_odd hp_three hp_two h_reg

/-! ## Character matrix action on (A − B): matrix-equation form

Wrap the shipped per-row eigenvalue identity
`sum_char_sinnottMatrix_A_sub_B_eigenvalue` into a single matrix equation:

  `(charMatrix · (A − B)^T)[ξ, i] = eigenvalue formula`

This is the entry-wise statement; by `Matrix.ext`, equivalent to a
matrix-level identity. Useful for downstream determinant computations. -/

open Classical in
/-- **`charMatrix_K_plus`**: the |G|×(|G|-1) "character action" matrix on
K⁺-places. Rows indexed by `MulChar(CyclotomicEvenDelta p)`, columns by
`{w : InfinitePlace K⁺ // w ≠ w₀}`. Entry `(ξ, w) ↦ ξ(k(w))`.

Used to package the character-orthogonality action on `(A − B)`. -/
noncomputable def charMatrix_K_plus
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    Matrix (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℂ :=
  Matrix.of fun ξ w => ξ (kplusEmbeddingIndexQuotient (p := p) K w.val)

open Classical in
/-- **Character action on `(A − B)` matrix-level identity** (eigenvalue form):
the matrix product `charMatrix_K_plus · ((A − B) cast to ℂ)^T` has explicit
entries given by the shipped eigenvalue formula:

  `(charMatrix · (A − B)^T)[ξ, i] = (ξ(q(famIdx i))⁻¹ - 1) · qe(ξ)
                                  − ξ(k(w₀)) · corr(i)`

where `corr(i) = M_even[k(w₀), q(famIdx i)] - M_even[k(w₀), 1]`.

Direct lift of `sum_char_sinnottMatrix_A_sub_B_eigenvalue` to a matrix
product. -/
theorem charMatrix_K_plus_mul_A_sub_B_apply
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [Finite {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀}]
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (charMatrix_K_plus (p := p) K *
        Matrix.transpose (Matrix.of fun (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
            (w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)))
        ξ i =
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
  classical
  simp only [Matrix.mul_apply, charMatrix_K_plus, Matrix.of_apply,
    Matrix.transpose_apply]
  exact sum_char_sinnottMatrix_A_sub_B_eigenvalue (p := p) K hp_odd hp_three
    hp_two ξ i

/-! ## "Diagonal" eigenvalue matrix `D` for the rank-1 decomposition

After the character action, the matrix `charMatrix · (A − B)^T` decomposes as

  `charMatrix · (A − B)^T = D - col · row`

where:
- `D[ξ, i] = (ξ(q(famIdx i))⁻¹ - 1) · qe(ξ)`. (Note: D has row ξ = 1 zero
  since (1 - 1) · qe(1) = 0.)
- `col(ξ) = ξ(k(w₀))`.
- `row(i) = corr(i) = M_even[k(w₀), q(famIdx i)] - M_even[k(w₀), 1]`.

This is a clean rank-1 perturbation structure, suitable for matrix det
lemma application restricted to ξ ≠ 1. -/

open Classical in
/-- **Eigenvalue "diagonal" matrix `D`**: `D[ξ, i] = (ξ(q(famIdx i))⁻¹ - 1) · qe(ξ)`.

Has row `ξ = 1` zero (since `(1 - 1) · qe(1) = 0`). Reindexed via
`b = q(famIdx i) ∈ CED \ {1}`, this becomes the standard "ξ(b)⁻¹ - 1"
times `qe(ξ)` matrix. -/
noncomputable def sinnottDiagonalEigenvalueMatrix
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    Matrix (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℂ :=
  Matrix.of fun ξ i =>
    (ξ (BernoulliRegular.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i))⁻¹ - 1) *
      quotientEigenvalue p ξ

open Classical in
/-- **`sinnottDiagonalEigenvalueMatrix` simp**: unwinds to the eigenvalue formula. -/
@[simp]
theorem sinnottDiagonalEigenvalueMatrix_apply
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    sinnottDiagonalEigenvalueMatrix p K hp_odd hp_three ξ i =
      (ξ (BernoulliRegular.cyclotomicEvenDeltaQuotient p
          (familyIndexAsUnit p K hp_odd hp_three i))⁻¹ - 1) *
        quotientEigenvalue p ξ :=
  rfl

/-- **Correction column vector** (`ξ ↦ ξ(k(w₀))`): the `ξ`-side weight in
the rank-1 perturbation of `charMatrix · (A − B)^T`. -/
noncomputable def sinnottCorrectionColVec
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) : ℂ :=
  ξ (kplusEmbeddingIndexQuotient (p := p) K
    NumberField.Units.dirichletUnitTheorem.w₀)

open Classical in
/-- **Correction row vector** (`i ↦ corr(i)`): the per-`i` correction at
position `w₀`. -/
noncomputable def sinnottCorrectionRowVec
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) : ℂ :=
  convolutionMatrixLogNormEven p
      (kplusEmbeddingIndexQuotient (p := p) K
        NumberField.Units.dirichletUnitTheorem.w₀)
      (BernoulliRegular.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i)) -
    convolutionMatrixLogNormEven p
      (kplusEmbeddingIndexQuotient (p := p) K
        NumberField.Units.dirichletUnitTheorem.w₀) 1

open Classical in
/-- **Rank-1 decomposition of `charMatrix · (A − B)^T`**:

  `charMatrix · (A − B)^T = D - col · row`

(matrix-level form via the shipped per-entry eigenvalue identity). -/
theorem charMatrix_mul_A_sub_B_transpose_eq_D_sub_rank_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [Finite {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀}] :
    charMatrix_K_plus (p := p) K *
        Matrix.transpose (Matrix.of fun (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
            (w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)) =
      sinnottDiagonalEigenvalueMatrix p K hp_odd hp_three -
        Matrix.of (fun ξ i => sinnottCorrectionColVec (p := p) K ξ *
          sinnottCorrectionRowVec (p := p) K hp_odd hp_three i) := by
  ext ξ i
  rw [charMatrix_K_plus_mul_A_sub_B_apply (p := p) K hp_odd hp_three hp_two ξ i]
  simp only [Matrix.sub_apply, Matrix.of_apply,
    sinnottDiagonalEigenvalueMatrix_apply,
    sinnottCorrectionColVec, sinnottCorrectionRowVec]

/-! ## Restriction to ξ ≠ 1: the substantive square case

Restricting the row index to ξ ≠ 1 makes `charMatrix · (A − B)^T` square
of size (|G|-1) × (|G|-1), and the diagonal matrix `D` (which has row
ξ = 1 vanishing) becomes invertible (assuming Dirichlet non-vanishing
of `qe(ξ)` for ξ ≠ 1). -/

open Classical in
/-- **`charMatrix_K_plus_nontriv`**: restriction of `charMatrix_K_plus`
to non-trivial characters ξ ≠ 1. Square (|G|-1) × (|G|-1) under the
bijection `{ξ : MulChar // ξ ≠ 1} ↔ {w // w ≠ w₀}` (cardinality match). -/
noncomputable def charMatrix_K_plus_nontriv
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    Matrix {ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ // ξ ≠ 1}
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℂ :=
  Matrix.of fun ξ w => ξ.val
    (kplusEmbeddingIndexQuotient (p := p) K w.val)

open Classical in
/-- **`sinnottDiagonalEigenvalueMatrix_nontriv`**: restriction of `D`
to non-trivial characters ξ ≠ 1. The non-trivial diagonal-like matrix
with `D[ξ, i] = (ξ(q(famIdx i))⁻¹ - 1) · qe(ξ)`. -/
noncomputable def sinnottDiagonalEigenvalueMatrix_nontriv
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    Matrix {ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ // ξ ≠ 1}
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℂ :=
  Matrix.of fun ξ i =>
    (ξ.val (BernoulliRegular.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i))⁻¹ - 1) *
      quotientEigenvalue p ξ.val

open Classical in
/-- **Rank-1 decomposition restricted to ξ ≠ 1**:

  `charMatrix_nontriv · (A − B)^T = D_nontriv - col_nontriv · row_corr`

where `col_nontriv(ξ) = ξ.val(k(w₀))` and `row_corr(i) = corr(i)`. -/
theorem charMatrix_nontriv_mul_A_sub_B_transpose_eq_D_nontriv_sub_rank_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [Finite {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀}] :
    charMatrix_K_plus_nontriv (p := p) K *
        Matrix.transpose (Matrix.of fun (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
            (w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)) =
      sinnottDiagonalEigenvalueMatrix_nontriv p K hp_odd hp_three -
        Matrix.of (fun ξ i =>
          sinnottCorrectionColVec (p := p) K ξ.val *
          sinnottCorrectionRowVec (p := p) K hp_odd hp_three i) := by
  ext ξ i
  simp only [Matrix.mul_apply, charMatrix_K_plus_nontriv, Matrix.of_apply,
    Matrix.transpose_apply, Matrix.sub_apply,
    sinnottDiagonalEigenvalueMatrix_nontriv, sinnottCorrectionColVec,
    sinnottCorrectionRowVec]
  exact sum_char_sinnottMatrix_A_sub_B_eigenvalue (p := p) K hp_odd hp_three
    hp_two ξ.val i

/-! ## Cardinality match for character-matrix det reindexing

To take `det(charMatrix_K_plus_nontriv)`, we need a square matrix; the
rectangular `Matrix {ξ ≠ 1} {w ≠ w₀}` is bridged via `Fintype.equivOfCardEq`
between the row and column index sets (both of cardinality `(p-3)/2`). -/

open Classical in
/-- **Cardinality of non-trivial characters**: `(p-1)/2 - 1 = (p-3)/2`. -/
theorem card_nontriv_mulChar_eq
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    Fintype.card {ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ // ξ ≠ 1} =
      (p - 3) / 2 := by
  classical
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  have h_card_mc :
      Fintype.card (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) =
      (p - 1) / 2 := by
    have h1 : Fintype.card (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) =
        Nat.card (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Nat.card_eq_fintype_card.symm
    rw [h1, nat_card_mulChar_cyclotomicEvenDelta_eq p]
    rw [Nat.card_eq_fintype_card]
    exact BernoulliRegular.cyclotomicEvenDelta_card (p := p) hp_two
  have h_card_compl :=
    Fintype.card_subtype_compl
      (α := MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
      (p := fun ξ => ξ = 1)
  rw [Fintype.card_subtype_eq] at h_card_compl
  have h_eq :
      Fintype.card {ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ // ξ ≠ 1} =
      Fintype.card {ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ // ¬ ξ = 1} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
  rw [h_eq, h_card_compl, h_card_mc]
  have h_p_odd : Odd p := hp.out.odd_of_ne_two (by omega)
  rcases h_p_odd with ⟨k, hk⟩
  omega

open Classical in
/-- **Card equality** between `{ξ ≠ 1}` and `{w ≠ w₀}`: both have cardinality
`(p-3)/2`. Enables `Fintype.equivOfCardEq` for reindexing. -/
theorem card_nontriv_mulChar_eq_card_kplus_ne_w₀
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    Fintype.card {ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ // ξ ≠ 1} =
      Fintype.card {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := by
  classical
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  rw [card_nontriv_mulChar_eq p hp_two,
      ← card_kplus_ne_w₀_eq p K hp_two]

open Classical in
/-- **Equiv between `{ξ ≠ 1}` and `{w ≠ w₀}`** (non-canonical, via cardinality match).
Used to reindex the rectangular `charMatrix_K_plus_nontriv` to a square matrix
suitable for `Matrix.det`. Stated using `Fintype.card` equality (so callers can
pass the instance explicitly). -/
noncomputable def equivNontrivCharKplusNeW₀
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)] :
    {ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ // ξ ≠ 1} ≃
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := by
  refine Fintype.equivOfCardEq ?_
  classical
  have h := card_nontriv_mulChar_eq_card_kplus_ne_w₀ p K hp_two
  convert h

/-! ## Reindexed (square) versions of charMatrix_nontriv and D_nontriv

Applying `equivNontrivCharKplusNeW₀.symm` on rows gives a square matrix
indexed by `{w ≠ w₀}` on both sides, enabling `Matrix.det`. -/

open Classical in
/-- **Square version of `charMatrix_K_plus_nontriv`**: reindexed via
`equivNontrivCharKplusNeW₀.symm` on rows. Now `Matrix {w ≠ w₀} {w ≠ w₀} ℂ`. -/
noncomputable def charMatrix_K_plus_nontriv_sq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)] :
    Matrix {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℂ :=
  (charMatrix_K_plus_nontriv (p := p) K).submatrix
    (equivNontrivCharKplusNeW₀ p K hp_two).symm id

open Classical in
/-- **Square version of `sinnottDiagonalEigenvalueMatrix_nontriv`**: reindexed
via `equivNontrivCharKplusNeW₀.symm` on rows. -/
noncomputable def sinnottDiagonalEigenvalueMatrix_nontriv_sq
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
  (sinnottDiagonalEigenvalueMatrix_nontriv p K hp_odd hp_three).submatrix
    (equivNontrivCharKplusNeW₀ p K hp_two).symm id

open Classical in
/-- **Reindexed rank-1 decomposition**:

  `charMatrix_nontriv_sq · (A − B)^T = D_nontriv_sq - (col · row)_sq`

The square (|G|-1) × (|G|-1) version of the rank-1 decomposition,
enabling `Matrix.det` application. -/
theorem charMatrix_nontriv_sq_mul_A_sub_B_transpose_eq_D_nontriv_sq_sub_rank_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_two : 2 < p)
    [Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)]
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [Finite {c : BernoulliRegular.CyclotomicEvenDelta p //
        c ≠ kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀}] :
    charMatrix_K_plus_nontriv_sq (p := p) K hp_two *
        Matrix.transpose (Matrix.of fun (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
            (w : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)) =
      sinnottDiagonalEigenvalueMatrix_nontriv_sq p K hp_odd hp_three hp_two -
        Matrix.of (fun (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
            (i : {w : NumberField.InfinitePlace
              (NumberField.maximalRealSubfield K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
          sinnottCorrectionColVec (p := p) K
              ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val *
            sinnottCorrectionRowVec (p := p) K hp_odd hp_three i) := by
  classical
  unfold charMatrix_K_plus_nontriv_sq sinnottDiagonalEigenvalueMatrix_nontriv_sq
  ext w i
  -- Use Matrix.submatrix_apply and Matrix.mul_apply to unfold both sides entry-wise.
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.sub_apply, Matrix.of_apply, charMatrix_K_plus_nontriv,
    sinnottDiagonalEigenvalueMatrix_nontriv, sinnottCorrectionColVec,
    sinnottCorrectionRowVec]
  -- Goal: ∑_x (xi.val(k(x.val)) * (A-B)[i, x]) = D[xi, i] - col*row
  exact sum_char_sinnottMatrix_A_sub_B_eigenvalue (p := p) K hp_odd hp_three
    hp_two ((equivNontrivCharKplusNeW₀ p K hp_two).symm w).val i

end Sinnott

end FLT37

end BernoulliRegular

end
