module

public import Mathlib.LinearAlgebra.Vandermonde
public import BernoulliRegular.GaussSum.SignInvariant.Operator

/-!
# Finite-Fourier sign invariants for quadratic Gauss sums

This file contains the Vandermonde and cyclotomic normalization side of the
finite-Fourier sign-invariant package.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

/-!
## Determinant / Vandermonde scaffold for `T023d1g2b`

This section isolates the matrix-level reductions for the determinant route:

1. express `normalizedDft` as an explicit normalized Fourier matrix;
2. reindex that matrix by `Fin p`, so the remaining algebra is on a standard
   square matrix type;
3. package the Vandermonde product that should eventually evaluate the
   determinant.
-/

/-- The distinguished Fourier root whose powers enumerate the Vandermonde nodes. -/
noncomputable def fourierBaseRoot : ℂ :=
  ZMod.stdAddChar (N := p) (-(1 : ZMod p))

/-- The `p` Fourier nodes expected to appear in the Vandermonde description. -/
noncomputable def fourierVandermondeNodes : Fin p → ℂ :=
  fun i => ZMod.stdAddChar (N := p) (-((zmodEquivFin (p := p)).symm i))

/-- The candidate Vandermonde matrix for the determinant computation. -/
noncomputable def fourierVandermonde : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.vandermonde (fourierVandermondeNodes (p := p))

/-- The explicit Vandermonde product attached to the Fourier nodes. -/
noncomputable def fourierVandermondeProduct : ℂ :=
  ∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
    (fourierVandermondeNodes (p := p) j - fourierVandermondeNodes (p := p) i)

/-- The cyclotomic difference product that remains after factoring each
Vandermonde term by the lower Fourier power. -/
noncomputable def fourierCyclotomicDifferenceProduct : ℂ :=
  ∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
    ((fourierBaseRoot (p := p)) ^ ((j : ℕ) - (i : ℕ)) - 1)

/-- The same cyclotomic difference product, reindexed by the single difference
`d = j - i` and grouped by multiplicity. -/
noncomputable def fourierCyclotomicSingleDifferenceProduct : ℂ :=
  ∏ d ∈ Finset.range (p - 1),
    ((fourierBaseRoot (p := p)) ^ (d + 1) - 1) ^ (p - 1 - d)

/-- Legacy goal alias for the matrix-identification step. -/
def fourierMatrixFin_eq_vandermondeGoal : Prop :=
  fourierMatrixFin p = fourierVandermonde p

theorem fourierMatrixFin_apply (i j : Fin p) :
    fourierMatrixFin p i j =
      ZMod.stdAddChar (N := p) (-((i : ZMod p) * (j : ZMod p))) := by
  rw [fourierMatrixFin, Matrix.reindex_apply]
  simp [fourierMatrix, zmodEquivFin_symm_apply]

/-- The reindexed Fourier matrix is exactly the Vandermonde matrix on the
Fourier nodes. This closes ticket `T023d1g2b1`. -/
theorem fourierMatrixFin_eq_fourierVandermonde :
    fourierMatrixFin p = fourierVandermonde p := by
  ext i j
  rw [fourierMatrixFin_apply (p := p), fourierVandermonde, Matrix.vandermonde_apply]
  simp only [fourierVandermondeNodes, zmodEquivFin_symm_apply]
  calc
    ZMod.stdAddChar (N := p) (-((i : ZMod p) * (j : ZMod p))) =
        ZMod.stdAddChar (N := p) ((j : ℕ) • (-(i : ZMod p))) := by
          congr
          rw [nsmul_eq_mul]
          ring
    _ = ZMod.stdAddChar (N := p) (-(i : ZMod p)) ^ (j : ℕ) :=
          AddChar.map_nsmul_eq_pow _ _ _

/-- Each Fourier node is a natural power of the distinguished base root. -/
theorem fourierVandermondeNodes_eq_pow_fourierBaseRoot (i : Fin p) :
    fourierVandermondeNodes (p := p) i = fourierBaseRoot (p := p) ^ (i : ℕ) := by
  rw [fourierVandermondeNodes, fourierBaseRoot]
  simp only [zmodEquivFin_symm_apply]
  calc
    ZMod.stdAddChar (N := p) (-(i : ZMod p)) =
        ZMod.stdAddChar (N := p) ((i : ℕ) • (-(1 : ZMod p))) := by
          congr
          rw [nsmul_eq_mul]
          ring
    _ = ZMod.stdAddChar (N := p) (-(1 : ZMod p)) ^ (i : ℕ) :=
          AddChar.map_nsmul_eq_pow _ _ _

/-- The Vandermonde product on the Fourier nodes is the usual product on the
powers of the distinguished Fourier root. -/
theorem fourierVandermondeProduct_eq_rootPowerProduct :
    fourierVandermondeProduct p =
      ∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
        ((fourierBaseRoot (p := p)) ^ (j : ℕ) - (fourierBaseRoot (p := p)) ^ (i : ℕ)) := by
  unfold fourierVandermondeProduct
  refine Finset.prod_congr rfl ?_
  intro i _
  refine Finset.prod_congr rfl ?_
  intro j _
  rw [fourierVandermondeNodes_eq_pow_fourierBaseRoot (p := p),
    fourierVandermondeNodes_eq_pow_fourierBaseRoot (p := p)]

/-- Factor a difference of two Fourier powers by the smaller power. -/
theorem fourierRootPowerDiff_eq_factor (i j : Fin p) (hij : i < j) :
    (fourierBaseRoot (p := p)) ^ (j : ℕ) - (fourierBaseRoot (p := p)) ^ (i : ℕ) =
      (fourierBaseRoot (p := p)) ^ (i : ℕ) *
        ((fourierBaseRoot (p := p)) ^ ((j : ℕ) - (i : ℕ)) - 1) := by
  set ζ : ℂ := fourierBaseRoot (p := p)
  have hij' : (i : ℕ) ≤ (j : ℕ) :=
    Nat.le_of_lt (show (i : ℕ) < (j : ℕ) by simpa using hij)
  have hnat : (j : ℕ) = (i : ℕ) + ((j : ℕ) - (i : ℕ)) :=
    (Nat.add_sub_of_le hij').symm
  calc
    ζ ^ (j : ℕ) - ζ ^ (i : ℕ) = ζ ^ ((i : ℕ) + ((j : ℕ) - (i : ℕ))) - ζ ^ (i : ℕ) := by
      conv_lhs => rw [hnat]
    _ = ζ ^ (i : ℕ) * ζ ^ ((j : ℕ) - (i : ℕ)) - ζ ^ (i : ℕ) := by
      rw [pow_add]
    _ = ζ ^ (i : ℕ) * (ζ ^ ((j : ℕ) - (i : ℕ)) - 1) := by
      ring

/-- First cyclotomic normalization of the Vandermonde product: isolate the
power-of-`ζ` contribution from the genuine root-of-unity differences. -/
theorem fourierRootPowerProduct_eq_weightedRootProduct_mul_fourierCyclotomicDifferenceProduct :
    (∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
      ((fourierBaseRoot (p := p)) ^ (j : ℕ) - (fourierBaseRoot (p := p)) ^ (i : ℕ))) =
      (∏ i : Fin p, ((fourierBaseRoot (p := p)) ^ (i : ℕ)) ^ (Finset.Ioi i).card) *
        fourierCyclotomicDifferenceProduct p := by
  unfold fourierCyclotomicDifferenceProduct
  have hsplit :
      (∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
          ((fourierBaseRoot (p := p)) ^ (j : ℕ) - (fourierBaseRoot (p := p)) ^ (i : ℕ))) =
        ∏ i : Fin p,
          (((fourierBaseRoot (p := p)) ^ (i : ℕ)) ^ (Finset.Ioi i).card *
            ∏ j ∈ Finset.Ioi i,
              ((fourierBaseRoot (p := p)) ^ ((j : ℕ) - (i : ℕ)) - 1)) := by
    refine Finset.prod_congr rfl ?_
    intro i _
    calc
      (∏ j ∈ Finset.Ioi i,
          ((fourierBaseRoot (p := p)) ^ (j : ℕ) -
            (fourierBaseRoot (p := p)) ^ (i : ℕ))) =
          ∏ j ∈ Finset.Ioi i,
            ((fourierBaseRoot (p := p)) ^ (i : ℕ) *
              ((fourierBaseRoot (p := p)) ^ ((j : ℕ) - (i : ℕ)) - 1)) := by
              refine Finset.prod_congr rfl ?_
              intro j hj
              exact fourierRootPowerDiff_eq_factor (p := p) i j (by simpa using hj)
      _ = (∏ _j ∈ Finset.Ioi i, (fourierBaseRoot (p := p)) ^ (i : ℕ)) *
          ∏ j ∈ Finset.Ioi i,
            ((fourierBaseRoot (p := p)) ^ ((j : ℕ) - (i : ℕ)) - 1) := by
              rw [Finset.prod_mul_distrib]
      _ = (((fourierBaseRoot (p := p)) ^ (i : ℕ)) ^ (Finset.Ioi i).card) *
          ∏ j ∈ Finset.Ioi i,
            ((fourierBaseRoot (p := p)) ^ ((j : ℕ) - (i : ℕ)) - 1) := by
              simp
  rw [hsplit, Finset.prod_mul_distrib]

/-- The Fourier Vandermonde product splits into a weighted root power and a
cyclotomic difference product. -/
theorem fourierVandermondeProduct_eq_weightedCyclotomicForm :
    fourierVandermondeProduct p =
      (∏ i : Fin p, (fourierBaseRoot (p := p)) ^ ((i : ℕ) * (p - 1 - (i : ℕ)))) *
        fourierCyclotomicDifferenceProduct p := by
  calc
    fourierVandermondeProduct p =
        (∏ i : Fin p, ((fourierBaseRoot (p := p)) ^ (i : ℕ)) ^ (Finset.Ioi i).card) *
          fourierCyclotomicDifferenceProduct p := by
            rw [fourierVandermondeProduct_eq_rootPowerProduct (p := p),
              fourierRootPowerProduct_eq_weightedRootProduct_mul_fourierCyclotomicDifferenceProduct
                (p := p)]
    _ = (∏ i : Fin p, (fourierBaseRoot (p := p)) ^ ((i : ℕ) * (p - 1 - (i : ℕ)))) *
          fourierCyclotomicDifferenceProduct p := by
            congr 1
            refine Finset.prod_congr rfl ?_
            intro i _
            rw [show (Finset.Ioi i).card = p - 1 - (i : ℕ) by simp,
              ← pow_mul]

omit hp in
/-- The weighted exponent appearing in the Fourier root factor is the cubic
binomial coefficient `n.choose 3`. -/
theorem sum_range_weightedRootExponent_eq_choose_three (n : ℕ) :
    ∑ i ∈ Finset.range n, i * (n - 1 - i) = n.choose 3 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.succ_sub_one, tsub_self, mul_zero, add_zero]
      calc
        ∑ i ∈ Finset.range n, i * (n - i) =
            ∑ i ∈ Finset.range n, (i * (n - 1 - i) + i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hi' : i < n := Finset.mem_range.mp hi
              have hsub : n - i = (n - 1 - i) + 1 := by
                omega
              rw [hsub, mul_add, mul_one]
        _ = (∑ i ∈ Finset.range n, i * (n - 1 - i)) + ∑ i ∈ Finset.range n, i := by
              rw [Finset.sum_add_distrib]
        _ = n.choose 3 + n.choose 2 := by
              rw [ih, Finset.sum_range_id, Nat.choose_two_right]
        _ = (n + 1).choose 3 := by
              rw [Nat.choose_succ_succ' n 2, add_comm]

/-- The weighted Fourier-root factor collapses to a single explicit power. -/
theorem weightedFourierRootProduct_eq_baseRoot_pow_choose_three :
    (∏ i : Fin p, (fourierBaseRoot (p := p)) ^ ((i : ℕ) * (p - 1 - (i : ℕ)))) =
      (fourierBaseRoot (p := p)) ^ (p.choose 3) := by
  have hprod :
      (∏ i : Fin p, (fourierBaseRoot (p := p)) ^ ((i : ℕ) * (p - 1 - (i : ℕ)))) =
        ∏ i ∈ Finset.range p, (fourierBaseRoot (p := p)) ^ (i * (p - 1 - i)) := by
          simpa using
            (Fin.prod_univ_eq_prod_range
              (f := fun i => (fourierBaseRoot (p := p)) ^ (i * (p - 1 - i))) (n := p))
  rw [hprod, Finset.prod_pow_eq_pow_sum, sum_range_weightedRootExponent_eq_choose_three]

/-- The Fourier Vandermonde product with the weighted root contribution
collapsed to a single power. This is the endpoint of `T023d1g2b2b1`. -/
theorem fourierVandermondeProduct_eq_chooseThreeCyclotomicForm :
    fourierVandermondeProduct p =
      (fourierBaseRoot (p := p)) ^ (p.choose 3) * fourierCyclotomicDifferenceProduct p := by
  rw [fourierVandermondeProduct_eq_weightedCyclotomicForm (p := p),
    weightedFourierRootProduct_eq_baseRoot_pow_choose_three (p := p)]

/-- Multiplying one copy of each cyclotomic factor increments the exponent in
the grouped single-difference product by `1`. -/
theorem prod_range_singleDifference_mul_shiftedPowers (n : ℕ) (ζ : ℂ) :
    (∏ d ∈ Finset.range n, (ζ ^ (d + 1) - 1)) *
        (∏ d ∈ Finset.range n, (ζ ^ (d + 1) - 1) ^ (n - d)) =
      ∏ d ∈ Finset.range n, (ζ ^ (d + 1) - 1) ^ (n + 1 - d) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro d hd
  have hd' : d < n := Finset.mem_range.mp hd
  have hshift : n + 1 - d = (n - d) + 1 := by
    omega
  simpa [hshift] using (pow_succ' (ζ ^ (d + 1) - 1) (n - d)).symm

/-- Reindex the two-variable `i < j` cyclotomic difference product by the
single difference `d = j - i`. -/
theorem finCyclotomicDifferenceProduct_eq_singleDifferenceProduct (n : ℕ) (ζ : ℂ) :
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (ζ ^ ((j : ℕ) - (i : ℕ)) - 1)) =
      ∏ d ∈ Finset.range n, (ζ ^ (d + 1) - 1) ^ (n - d) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
      have hsucc :
          (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i.succ, (ζ ^ ((j : ℕ) - (i.succ : ℕ)) - 1)) =
            ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (ζ ^ ((j : ℕ) - (i : ℕ)) - 1) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        rw [Fin.prod_Ioi_succ]
        refine Finset.prod_congr rfl ?_
        intro j hj
        simp [Fin.val_succ]
      rw [hsucc]
      have hfirst :
          (∏ j : Fin (n + 1), (ζ ^ ((j : ℕ) + 1) - 1)) =
            ∏ d ∈ Finset.range (n + 1), (ζ ^ (d + 1) - 1) := by
        simpa using
          (Fin.prod_univ_eq_prod_range (f := fun d => (ζ ^ (d + 1) - 1)) (n := n + 1))
      have hfirst' :
          (∏ j : Fin (n + 1),
              (ζ ^ (((j.succ : Fin (n + 2)) : ℕ) - (((0 : Fin (n + 2)) : Fin (n + 2)) : ℕ)) - 1)) =
            ∏ d ∈ Finset.range (n + 1), (ζ ^ (d + 1) - 1) := by
        simpa [Fin.val_succ] using hfirst
      rw [ih, hfirst', Finset.prod_range_succ]
      let a : ℕ → ℂ := fun d => ζ ^ (d + 1) - 1
      calc
        ((∏ d ∈ Finset.range n, a d) * a n) * (∏ d ∈ Finset.range n, a d ^ (n - d)) =
            ((∏ d ∈ Finset.range n, a d) * (∏ d ∈ Finset.range n, a d ^ (n - d))) * a n := by
              ac_rfl
        _ = (∏ d ∈ Finset.range n, a d ^ (n + 1 - d)) * a n := by
              rw [prod_range_singleDifference_mul_shiftedPowers (n := n) (ζ := ζ)]
        _ = (∏ d ∈ Finset.range n, a d ^ (n + 1 - d)) * a n ^ ((n + 1) - n) := by
              simp
        _ = ∏ d ∈ Finset.range (n + 1), a d ^ (n + 1 - d) := by
              rw [Finset.prod_range_succ]

/-- The Fourier cyclotomic difference product in one-variable grouped form. -/
theorem fourierCyclotomicDifferenceProduct_eq_singleDifferenceProduct :
    fourierCyclotomicDifferenceProduct p = fourierCyclotomicSingleDifferenceProduct p := by
  have hbase :
      (∏ i : Fin ((p - 1) + 1), ∏ j ∈ Finset.Ioi i,
          (fourierBaseRoot (p := p) ^ ((j : ℕ) - (i : ℕ)) - 1)) =
        ∏ d ∈ Finset.range (p - 1),
          (fourierBaseRoot (p := p) ^ (d + 1) - 1) ^ (p - 1 - d) :=
    finCyclotomicDifferenceProduct_eq_singleDifferenceProduct
      (n := p - 1) (ζ := fourierBaseRoot (p := p))
  have hp_pred : (p - 1) + 1 = p := Nat.succ_pred_eq_of_pos hp.out.pos
  have hcast :
      (∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
          (fourierBaseRoot (p := p) ^ ((j : ℕ) - (i : ℕ)) - 1)) =
        ∏ d ∈ Finset.range (p - 1),
          (fourierBaseRoot (p := p) ^ (d + 1) - 1) ^ (p - 1 - d) := by
    let P : ℕ → Prop := fun m =>
      (∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
          (fourierBaseRoot (p := p) ^ ((j : ℕ) - (i : ℕ)) - 1)) =
        ∏ d ∈ Finset.range (p - 1),
          (fourierBaseRoot (p := p) ^ (d + 1) - 1) ^ (p - 1 - d)
    have hP : P ((p - 1) + 1) := by
      simpa [P] using hbase
    change P p
    exact hp_pred ▸ hP
  simpa [fourierCyclotomicDifferenceProduct, fourierCyclotomicSingleDifferenceProduct] using hcast

/-- The Fourier Vandermonde product with both the weighted root factor and the
cyclotomic-difference multiplicities made explicit. -/
theorem fourierVandermondeProduct_eq_chooseThreeSingleDifferenceForm :
    fourierVandermondeProduct p =
      (fourierBaseRoot (p := p)) ^ (p.choose 3) * fourierCyclotomicSingleDifferenceProduct p := by
  rw [fourierVandermondeProduct_eq_chooseThreeCyclotomicForm (p := p),
    fourierCyclotomicDifferenceProduct_eq_singleDifferenceProduct (p := p)]

/-- Mathlib's Vandermonde determinant formula, specialized to the Fourier
nodes. This is the explicit product that remains to be simplified. -/
theorem det_fourierVandermonde_eq_fourierVandermondeProduct :
    Matrix.det (fourierVandermonde p) = fourierVandermondeProduct p := by
  simp [fourierVandermonde, fourierVandermondeProduct, Matrix.det_vandermonde]

/-- With the Fourier/Vandermonde identification in hand, the determinant route
reduces `normalizedDft` to the explicit product over Fourier nodes. -/
theorem det_normalizedFourierMatrixFin_eq_scale_mul_fourierVandermondeProduct :
    Matrix.det (normalizedFourierMatrixFin p) =
      ((Real.sqrt p : ℂ)⁻¹) ^ p * fourierVandermondeProduct p := by
  rw [normalizedFourierMatrixFin_eq_smul_fourierMatrixFin (p := p), Matrix.det_smul,
    fourierMatrixFin_eq_fourierVandermonde (p := p),
    det_fourierVandermonde_eq_fourierVandermondeProduct]
  simp

/-- Packaged determinant skeleton for `T023d1g2b`: the remaining work is
exactly the final simplification of the explicit cyclotomic product. -/
theorem det_normalizedDft_eq_scale_mul_fourierVandermondeProduct :
    LinearMap.det (normalizedDft p) =
      ((Real.sqrt p : ℂ)⁻¹) ^ p * fourierVandermondeProduct p := by
  rw [det_normalizedDft_eq_det_normalizedFourierMatrix (p := p),
    det_normalizedFourierMatrix_eq_det_normalizedFourierMatrixFin (p := p)]
  exact det_normalizedFourierMatrixFin_eq_scale_mul_fourierVandermondeProduct (p := p)

/-- Packaged cyclotomic form for the determinant route. This is the endpoint of
`T023d1g2b2a`; the remaining work is to evaluate the weighted root powers and
the cyclotomic difference product explicitly. -/
theorem det_normalizedDft_eq_weightedCyclotomicForm :
    LinearMap.det (normalizedDft p) =
      ((Real.sqrt p : ℂ)⁻¹) ^ p *
        ((∏ i : Fin p, (fourierBaseRoot (p := p)) ^ ((i : ℕ) * (p - 1 - (i : ℕ)))) *
          fourierCyclotomicDifferenceProduct p) := by
  rw [det_normalizedDft_eq_scale_mul_fourierVandermondeProduct (p := p),
    fourierVandermondeProduct_eq_weightedCyclotomicForm (p := p)]

/-- Packaged determinant form after collapsing the weighted Fourier-root
contribution to a single exponent. -/
theorem det_normalizedDft_eq_chooseThreeCyclotomicForm :
    LinearMap.det (normalizedDft p) =
      ((Real.sqrt p : ℂ)⁻¹) ^ p *
        ((fourierBaseRoot (p := p)) ^ (p.choose 3) * fourierCyclotomicDifferenceProduct p) := by
  rw [det_normalizedDft_eq_scale_mul_fourierVandermondeProduct (p := p),
    fourierVandermondeProduct_eq_chooseThreeCyclotomicForm (p := p)]

/-- Packaged determinant form with the cyclotomic-difference product grouped by
the single difference `d = j - i`. This is the endpoint of `T023d1g2b2b2`. -/
theorem det_normalizedDft_eq_chooseThreeSingleDifferenceForm :
    LinearMap.det (normalizedDft p) =
      ((Real.sqrt p : ℂ)⁻¹) ^ p *
        ((fourierBaseRoot (p := p)) ^ (p.choose 3) *
          fourierCyclotomicSingleDifferenceProduct p) := by
  rw [det_normalizedDft_eq_chooseThreeCyclotomicForm (p := p),
    fourierCyclotomicDifferenceProduct_eq_singleDifferenceProduct (p := p)]

end SignInvariant

end BernoulliRegular
