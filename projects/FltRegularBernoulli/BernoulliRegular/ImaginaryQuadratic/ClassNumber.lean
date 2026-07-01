module

public import BernoulliRegular.ImaginaryQuadratic.Foundations

@[expose] public section

noncomputable section

open Complex NumberField

namespace BernoulliRegular

section ClassNumberRouteIntegration

variable (p : ℕ) [hp : Fact p.Prime]

/-- The classical integer sum associated to `B_{1, legendreDirichlet p}`:
`p · B_{1,η}.re = ∑_{a=0}^{p-1} (a/p)_L · a` (as a real number). -/
theorem cast_mul_BernoulliGen_re_eq (hp_odd : p ≠ 2) :
    (p : ℝ) * (BernoulliGen (legendreDirichlet p) 1).re =
      ∑ a : ZMod p, ((quadraticChar (ZMod p) a : ℤ) : ℝ) * (a.val : ℝ) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_ne_one : legendreDirichlet p ≠ 1 := legendreDirichlet_ne_one p hp_odd
  have h_formula := natCast_mul_BernoulliGen_one_of_ne_one (R := ℂ) h_ne_one
  -- Take real parts of both sides of h_formula.
  have h_lhs_re : ((p : ℂ) * BernoulliGen (legendreDirichlet p) 1).re =
      (p : ℝ) * (BernoulliGen (legendreDirichlet p) 1).re := by
    rw [Complex.mul_re]
    have hp_cast_im : ((p : ℂ)).im = 0 := by
      rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) from by push_cast; rfl, Complex.ofReal_im]
    have hp_cast_re : ((p : ℂ)).re = (p : ℝ) := by
      rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) from by push_cast; rfl, Complex.ofReal_re]
    rw [hp_cast_im, hp_cast_re, zero_mul, sub_zero]
  have h_rhs_re : (∑ a : ZMod p, (legendreDirichlet p) a * (a.val : ℂ)).re =
      ∑ a : ZMod p, ((quadraticChar (ZMod p) a : ℤ) : ℝ) * (a.val : ℝ) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [legendreDirichlet_apply, Complex.mul_re]
    have h_eta_im : (((quadraticChar (ZMod p) a : ℤ) : ℂ)).im = 0 := by
      rw [show (((quadraticChar (ZMod p) a : ℤ) : ℂ)) =
          (((quadraticChar (ZMod p) a : ℤ) : ℝ) : ℂ) from by push_cast; rfl,
        Complex.ofReal_im]
    have h_a_im : ((a.val : ℂ)).im = 0 := by
      rw [show ((a.val : ℂ)) = ((a.val : ℝ) : ℂ) from by push_cast; rfl, Complex.ofReal_im]
    have h_eta_re : (((quadraticChar (ZMod p) a : ℤ) : ℂ)).re =
        ((quadraticChar (ZMod p) a : ℤ) : ℝ) := by
      rw [show (((quadraticChar (ZMod p) a : ℤ) : ℂ)) =
          (((quadraticChar (ZMod p) a : ℤ) : ℝ) : ℂ) from by push_cast; rfl,
        Complex.ofReal_re]
    have h_a_re : ((a.val : ℂ)).re = (a.val : ℝ) := by
      rw [show ((a.val : ℂ)) = ((a.val : ℝ) : ℂ) from by push_cast; rfl, Complex.ofReal_re]
    rw [h_eta_im, h_a_im, h_eta_re, h_a_re, mul_zero, sub_zero]
  have h_re := congrArg Complex.re h_formula
  rw [h_lhs_re, h_rhs_re] at h_re
  exact h_re

/-- `B_{1,η}.re < 0` follows from the integer character sum being negative.
This reduces CN-09 to the classical fact
`∑_{a=1}^{p-1} (a/p)_L · a < 0` for `p ≡ 3 mod 4` (Dirichlet's identity). -/
theorem BernoulliGen_re_neg_of_sum_neg (hp_odd : p ≠ 2)
    (h_sum_neg :
      (∑ a : ZMod p, ((quadraticChar (ZMod p) a : ℤ) : ℝ) * (a.val : ℝ)) < 0) :
    (BernoulliGen (legendreDirichlet p) 1).re < 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h := cast_mul_BernoulliGen_re_eq p hp_odd
  have hp_pos_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  -- p · B.re = sum < 0, and p > 0, so B.re < 0.
  nlinarith [h, h_sum_neg, hp_pos_real]

/-- `B_{1,η}.re < 0` follows from the (integer-valued) character sum being
negative. This is a cleaner reduction using only integer/natural arithmetic. -/
theorem BernoulliGen_re_neg_of_int_sum_neg (hp_odd : p ≠ 2)
    (h_sum_int_neg :
      (∑ a : ZMod p, (quadraticChar (ZMod p) a : ℤ) * (a.val : ℤ)) < 0) :
    (BernoulliGen (legendreDirichlet p) 1).re < 0 := by
  apply BernoulliGen_re_neg_of_sum_neg p hp_odd
  have h_cast : ∑ a : ZMod p, ((quadraticChar (ZMod p) a : ℤ) : ℝ) * (a.val : ℝ) =
      ((∑ a : ZMod p, (quadraticChar (ZMod p) a : ℤ) * (a.val : ℤ) : ℤ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun a _ ↦ by ring
  rw [h_cast]
  exact_mod_cast h_sum_int_neg

/-- `BernoulliGen (legendreDirichlet p) 1` has imaginary part zero, since
`legendreDirichlet p` takes only values in `ℤ ⊂ ℝ`. -/
theorem BernoulliGen_legendreDirichlet_one_im_zero (hp_odd : p ≠ 2) :
    (BernoulliGen (legendreDirichlet p) 1).im = 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- Use the formula: p · B_{1,η} = ∑ η(a) · a (both sides real-valued).
  have h_ne_one : legendreDirichlet p ≠ 1 := legendreDirichlet_ne_one p hp_odd
  have h_formula := natCast_mul_BernoulliGen_one_of_ne_one (R := ℂ) h_ne_one
  have hp_cast_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  -- Show RHS has zero imaginary part.
  have h_rhs_im : (∑ a : ZMod p, (legendreDirichlet p) a * (a.val : ℂ)).im = 0 := by
    rw [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro a _
    -- legendreDirichlet p a is real (cast from ℤ)
    rw [legendreDirichlet_apply, Complex.mul_im]
    have h_eta_re : (((quadraticChar (ZMod p) a : ℤ) : ℂ)).im = 0 := by
      rw [show (((quadraticChar (ZMod p) a : ℤ) : ℂ)) =
          (((quadraticChar (ZMod p) a : ℤ) : ℝ) : ℂ) from by push_cast; rfl,
        Complex.ofReal_im]
    have h_a_re : ((a.val : ℂ)).im = 0 := by
      rw [show ((a.val : ℂ)) = ((a.val : ℝ) : ℂ) from by push_cast; rfl,
        Complex.ofReal_im]
    rw [h_eta_re, h_a_re]; ring
  -- Now use h_formula: p · B = ∑ ..., and take imaginary parts.
  have h_lhs_im : ((p : ℂ) * BernoulliGen (legendreDirichlet p) 1).im = 0 := by
    rw [h_formula]; exact h_rhs_im
  rw [Complex.mul_im] at h_lhs_im
  have hp_cast_im : ((p : ℂ)).im = 0 := by
    rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) from by push_cast; rfl, Complex.ofReal_im]
  have hp_cast_re : ((p : ℂ)).re = (p : ℝ) := by
    rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) from by push_cast; rfl, Complex.ofReal_re]
  rw [hp_cast_im, hp_cast_re, zero_mul, add_zero] at h_lhs_im
  have hp_ne_zero_real : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp.out.ne_zero
  exact (mul_eq_zero.mp h_lhs_im).resolve_left hp_ne_zero_real

/-- **CN-10 (conditional on CN-09)**: For `p ≡ 3 mod 4`, if `B_{1,η} < 0` (as a
real number, with zero imaginary part), then `rootNumber η = 1`.

Proof: combine with existing `rootNumber_B1_product_neg` (gives
`(W_η · B_{1,η}).re < 0`) and `rootNumber_legendreDirichlet_eq_one_or_neg_one`
(gives `W_η ∈ {1, -1}`). If `W_η = -1`, then `W_η · B_{1,η}` has positive real
part (since both negative), contradicting the product being negative. -/
theorem rootNumber_eq_one_of_B_neg
    (hp_three_mod_four : p % 4 = 3)
    (h_B_re_neg : (BernoulliGen (legendreDirichlet p) 1).re < 0) :
    DirichletCharacter.rootNumber (legendreDirichlet p) = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_prod_neg := rootNumber_B1_product_neg p hp_three_mod_four
  obtain ⟨h_z_im, h_z_re⟩ := h_prod_neg
  have h_W_cases : DirichletCharacter.rootNumber (legendreDirichlet p) = 1 ∨
      DirichletCharacter.rootNumber (legendreDirichlet p) = -1 :=
    rootNumber_legendreDirichlet_eq_one_or_neg_one p hp_three_mod_four
  rcases h_W_cases with h_W_pos | h_W_neg
  · exact h_W_pos
  · -- Case W = -1: derive contradiction from h_z_re < 0.
    exfalso
    have h_z_eq : ((DirichletCharacter.rootNumber (legendreDirichlet p)) *
        BernoulliGen (legendreDirichlet p) 1).re =
        -(BernoulliGen (legendreDirichlet p) 1).re := by
      rw [h_W_neg]
      simp
    rw [h_z_eq] at h_z_re
    linarith

/-- **CN-11 (conditional on CN-09)**: For `p ≡ 3 mod 4`, if `B_{1,η} < 0`, then
`gaussSum η stdAddChar = I · √p`. -/
theorem gaussSum_eq_I_mul_sqrt_of_B_neg
    (hp_three_mod_four : p % 4 = 3)
    (h_B_re_neg : (BernoulliGen (legendreDirichlet p) 1).re < 0) :
    gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_W_one := rootNumber_eq_one_of_B_neg p hp_three_mod_four h_B_re_neg
  have hp_odd : p ≠ 2 := by omega
  have h_odd : (legendreDirichlet p).Odd := legendreDirichlet_odd p hp_three_mod_four
  have h_not_even : ¬ (legendreDirichlet p).Even := h_odd.not_even
  have h_def : DirichletCharacter.rootNumber (legendreDirichlet p) =
      gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) /
        Complex.I / ((p : ℂ) ^ (1 / 2 : ℂ)) := by
    unfold DirichletCharacter.rootNumber
    rw [if_neg h_not_even, pow_one]
  rw [h_W_one] at h_def
  have hp_ne_zero : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp_cpow_ne_zero : (p : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hp_ne_zero)
  have h_I_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp at h_def
  linear_combination -h_def

/-- **CN-12 (conditional on CN-09)**: For `p ≡ 3 mod 4`, if `B_{1,η} < 0`, then
`∏_{χ ∈ nontrivialCharacters p} rootNumber χ = 1`. -/
theorem prod_rootNumber_eq_one_of_B_neg
    (hp_three_mod_four : p % 4 = 3)
    (h_B_re_neg : (BernoulliGen (legendreDirichlet p) 1).re < 0) :
    ∏ χ ∈ nontrivialCharacters p, DirichletCharacter.rootNumber χ = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_odd : p ≠ 2 := by omega
  have h_W_one := rootNumber_eq_one_of_B_neg p hp_three_mod_four h_B_re_neg
  rw [prod_rootNumber_ne_one_eq_rootNumber_legendre p hp_odd, h_W_one]

/-- **CN-13 (conditional on CN-09)**: For `p ≡ 3 mod 4`, if `B_{1,η} < 0`, then
the clean Dedekind functional equation for `ℚ(ζ_p)` holds:
`Λ_K(1-s) = p^{(p-2)(s-1/2)} · Λ_K(s)`. -/
theorem completedDedekindZetaCyclotomic_cleanFE_of_B_neg
    (hp_three_mod_four : p % 4 = 3)
    (h_B_re_neg : (BernoulliGen (legendreDirichlet p) 1).re < 0) (s : ℂ) :
    completedDedekindZetaCyclotomic p (1 - s) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        completedDedekindZetaCyclotomic p s :=
  completedDedekindZetaCyclotomic_one_sub_of_prod_rootNumber_eq_one p
    (prod_rootNumber_eq_one_of_B_neg p hp_three_mod_four h_B_re_neg) s

/-- **Final capstone (conditional on CN-09)**: All the explicit Gauss sum
identities become unconditional once `B_{1,η} < 0` is established. -/
theorem gaussSum_oddCharacters_prod_signed_explicit_of_B_neg
    (hp_three_mod_four : p % 4 = 3)
    (h_B_re_neg : (BernoulliGen (legendreDirichlet p) 1).re < 0) :
    ∏ χ ∈ oddCharacters p,
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) * (-(p : ℂ)) ^ ((p - 3) / 4) :=
  gaussSum_oddCharacters_prod_signed_explicit p hp_three_mod_four
    (gaussSum_eq_I_mul_sqrt_of_B_neg p hp_three_mod_four h_B_re_neg)

/-! ### Fully chained theorems — reduce everything to the integer sum being negative

The following theorems reduce the entire chain to the single classical fact
`∑_{a=0}^{p-1} (a/p)_L · a < 0` for `p ≡ 3 mod 4`.  This is Dirichlet's identity
(class number formula consequence). -/

/-- **CN chain (full)**: For `p ≡ 3 mod 4`, if the integer character sum is
negative, then `rootNumber η = 1`. -/
theorem rootNumber_eq_one_of_sum_neg
    (hp_three_mod_four : p % 4 = 3)
    (h_sum_neg :
      (∑ a : ZMod p, ((quadraticChar (ZMod p) a : ℤ) : ℝ) * (a.val : ℝ)) < 0) :
    DirichletCharacter.rootNumber (legendreDirichlet p) = 1 := by
  have hp_odd : p ≠ 2 := by omega
  exact rootNumber_eq_one_of_B_neg p hp_three_mod_four
    (BernoulliGen_re_neg_of_sum_neg p hp_odd h_sum_neg)

/-- **Full Gauss sign theorem, conditional on integer sum**: For `p ≡ 3 mod 4`,
if `∑ (a/p) · a < 0`, then `τ(η) = I · √p`. -/
theorem gaussSum_eq_I_mul_sqrt_of_sum_neg
    (hp_three_mod_four : p % 4 = 3)
    (h_sum_neg :
      (∑ a : ZMod p, ((quadraticChar (ZMod p) a : ℤ) : ℝ) * (a.val : ℝ)) < 0) :
    gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) := by
  have hp_odd : p ≠ 2 := by omega
  exact gaussSum_eq_I_mul_sqrt_of_B_neg p hp_three_mod_four
    (BernoulliGen_re_neg_of_sum_neg p hp_odd h_sum_neg)

/-- **Full clean Dedekind FE, conditional on integer sum**. -/
theorem completedDedekindZetaCyclotomic_cleanFE_of_sum_neg
    (hp_three_mod_four : p % 4 = 3)
    (h_sum_neg :
      (∑ a : ZMod p, ((quadraticChar (ZMod p) a : ℤ) : ℝ) * (a.val : ℝ)) < 0)
    (s : ℂ) :
    completedDedekindZetaCyclotomic p (1 - s) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        completedDedekindZetaCyclotomic p s := by
  have hp_odd : p ≠ 2 := by omega
  exact completedDedekindZetaCyclotomic_cleanFE_of_B_neg p hp_three_mod_four
    (BernoulliGen_re_neg_of_sum_neg p hp_odd h_sum_neg) s

/-! ### Integer-valued (decidable) versions of the chain -/

/-- Integer version of `rootNumber_eq_one_of_sum_neg`. Takes the integer sum
being negative as hypothesis (which is decidable for concrete `p`). -/
theorem rootNumber_eq_one_of_int_sum_neg
    (hp_three_mod_four : p % 4 = 3)
    (h_sum_int_neg :
      (∑ a : ZMod p, (quadraticChar (ZMod p) a : ℤ) * (a.val : ℤ)) < 0) :
    DirichletCharacter.rootNumber (legendreDirichlet p) = 1 := by
  have hp_odd : p ≠ 2 := by omega
  exact rootNumber_eq_one_of_B_neg p hp_three_mod_four
    (BernoulliGen_re_neg_of_int_sum_neg p hp_odd h_sum_int_neg)

/-- Integer version of the Gauss sign theorem. -/
theorem gaussSum_eq_I_mul_sqrt_of_int_sum_neg
    (hp_three_mod_four : p % 4 = 3)
    (h_sum_int_neg :
      (∑ a : ZMod p, (quadraticChar (ZMod p) a : ℤ) * (a.val : ℤ)) < 0) :
    gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) := by
  have hp_odd : p ≠ 2 := by omega
  exact gaussSum_eq_I_mul_sqrt_of_B_neg p hp_three_mod_four
    (BernoulliGen_re_neg_of_int_sum_neg p hp_odd h_sum_int_neg)

/-- Integer version of the clean Dedekind FE. -/
theorem completedDedekindZetaCyclotomic_cleanFE_of_int_sum_neg
    (hp_three_mod_four : p % 4 = 3)
    (h_sum_int_neg :
      (∑ a : ZMod p, (quadraticChar (ZMod p) a : ℤ) * (a.val : ℤ)) < 0)
    (s : ℂ) :
    completedDedekindZetaCyclotomic p (1 - s) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        completedDedekindZetaCyclotomic p s := by
  have hp_odd : p ≠ 2 := by omega
  exact completedDedekindZetaCyclotomic_cleanFE_of_B_neg p hp_three_mod_four
    (BernoulliGen_re_neg_of_int_sum_neg p hp_odd h_sum_int_neg) s

end ClassNumberRouteIntegration

/-! ### CN-05..CN-08 preliminaries: place counts and unit rank for `Kminus p`

Infrastructure lemmas needed for the class-number route analytics (CN-06..CN-08):
- `nrComplexPlaces_Kminus = 1`.
- `Units.rank (Kminus p) = 0`.

These follow from `finrank_Kminus = 2` and `nrRealPlaces_Kminus = 0` via the
identities `r₁ + 2·r₂ = n` (degree formula) and `rank = r₁ + r₂ - 1` (Dirichlet
unit theorem).

The downstream analytic pieces (CN-05 factorization, CN-06 residue, CN-07/CN-08
L-value and Bernoulli formulas) are substantial and deferred. -/
section CN0X_preliminaries

variable (p : ℕ) [hp : Fact p.Prime]

/-- The number of complex places of `Kminus p` is `1`. -/
lemma nrComplexPlaces_Kminus :
    NumberField.InfinitePlace.nrComplexPlaces (Kminus p) = 1 := by
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := Kminus p)
  rw [nrRealPlaces_Kminus, finrank_Kminus] at h
  omega

/-- The total number of infinite places of `Kminus p` is `1`. -/
lemma card_infinitePlace_Kminus :
    Fintype.card (NumberField.InfinitePlace (Kminus p)) = 1 := by
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_Kminus, nrComplexPlaces_Kminus]

/-- The unit rank of `Kminus p` is `0` (imaginary quadratic fields have trivial
unit group modulo torsion). -/
lemma rank_Kminus : NumberField.Units.rank (Kminus p) = 0 := by
  rw [show NumberField.Units.rank (Kminus p) =
    Fintype.card (NumberField.InfinitePlace (Kminus p)) - 1 from rfl,
    card_infinitePlace_Kminus]

/-- The regulator of `Kminus p` is `1`. Follows from `rank = 0` (the fundamental
matrix in `regulator_eq_det'` becomes `0 × 0`, whose determinant is `1`). -/
lemma regulator_Kminus : NumberField.Units.regulator (Kminus p) = 1 := by
  classical
  rw [NumberField.Units.regulator_eq_det']
  haveI : IsEmpty { w : NumberField.InfinitePlace (Kminus p) //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀ } := by
    rw [isEmpty_subtype]
    intro w
    push Not
    have hsub : Subsingleton (NumberField.InfinitePlace (Kminus p)) :=
      Fintype.card_le_one_iff_subsingleton.mp (card_infinitePlace_Kminus p).le
    exact Subsingleton.elim _ _
  rw [Matrix.det_isEmpty, abs_one]

/-- **CN-06**: The residue of `dedekindZeta (Kminus p)` at `s = 1` is
`(2π · h(-p)) / (w · √p)`, where `h(-p) = classNumber (Kminus p)` and
`w = Units.torsionOrder (Kminus p)`. For `p > 3` we additionally have `w = 2`
(see CN-04), which gives the standard `π · h / √p` form.

Derivation: instantiate `NumberField.dedekindZeta_residue_def` with
  r₁ = 0 (nrRealPlaces_Kminus),
  r₂ = 1 (nrComplexPlaces_Kminus),
  Reg = 1 (regulator_Kminus),
  |disc| = p (discr_Kminus_natAbs_eq from CN-03). -/
theorem dedekindZeta_residue_Kminus (hp3 : p % 4 = 3) :
    NumberField.dedekindZeta_residue (Kminus p) =
      (2 * Real.pi * (NumberField.classNumber (Kminus p) : ℝ)) /
        ((NumberField.Units.torsionOrder (Kminus p) : ℝ) * Real.sqrt p) := by
  rw [NumberField.dedekindZeta_residue_def, nrRealPlaces_Kminus,
    nrComplexPlaces_Kminus p, regulator_Kminus p, pow_zero, pow_one, one_mul, mul_one]
  congr 2
  have h_discr : (NumberField.discr (Kminus p)).natAbs = p := discr_Kminus_natAbs_eq p hp3
  have h_abs : |((NumberField.discr (Kminus p) : ℤ) : ℝ)| = (p : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, h_discr]
    simp
  rw [h_abs]

/-- **CN-07** (conditional on CN-05): Given the Dedekind factorization
`ζ_{Kminus p}(s) = ζ(s) · L(η, s)` on `Re(s) > 1`, the L-value at 1
equals the ζ-residue:

  `L(legendreDirichlet p, 1) = dedekindZeta_residue (Kminus p)`.

Combined with CN-06, this gives `L(η, 1) = 2π h / (w √p)`.

Proof: take the limit `(s-1) · ζ_K(s) → residue` on one side, and
`(s-1) · ζ(s) · L(η, s) → 1 · L(η, 1)` on the other. Uniqueness of
limits gives the identity. -/
theorem LFunction_one_eq_dedekindZeta_residue_of_CN05 (hp3 : p % 4 = 3)
    (h_CN05 : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta (Kminus p) s =
        riemannZeta s * DirichletCharacter.LFunction (legendreDirichlet p) s) :
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    ((NumberField.dedekindZeta_residue (Kminus p) : ℝ) : ℂ) =
      DirichletCharacter.LFunction (legendreDirichlet p) 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_tendsto_dedekind := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT (Kminus p)
  -- The product side: (s-1) · ζ(s) · L(η, s) → L(η, 1).
  have h_embed : Filter.Tendsto (fun s : ℝ ↦ (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds,
        by filter_upwards [self_mem_nhdsWithin] with s hs h
           exact absurd (Complex.ofReal_injective h) (ne_of_gt hs)⟩
  have h_zeta : Filter.Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * riemannZeta (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp h_embed
  -- L(η, ·) is continuous at 1 (L(η) is entire for nontrivial χ).
  have h_L_cont : ContinuousAt (DirichletCharacter.LFunction (legendreDirichlet p)) 1 := by
    have hp_odd : p ≠ 2 := by omega
    have h_ne_one : legendreDirichlet p ≠ 1 := legendreDirichlet_ne_one p hp_odd
    exact (DirichletCharacter.differentiable_LFunction h_ne_one).continuous.continuousAt
  have h_L_tendsto : Filter.Tendsto
      (fun s : ℝ ↦ DirichletCharacter.LFunction (legendreDirichlet p) (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (DirichletCharacter.LFunction (legendreDirichlet p) 1)) :=
    h_L_cont.tendsto.comp (h_embed.mono_right nhdsWithin_le_nhds)
  have h_product := h_zeta.mul h_L_tendsto
  rw [one_mul] at h_product
  -- Rewrite the product as (s-1) · ζ_K(s) via CN-05.
  have h_tendsto_product :
      Filter.Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * NumberField.dedekindZeta (Kminus p) (s : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (DirichletCharacter.LFunction (legendreDirichlet p) 1)) := by
    refine (Filter.tendsto_congr' ?_).mp h_product
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs_re : 1 < ((s : ℂ) : ℂ).re := by
      change 1 < (s : ℝ)
      exact_mod_cast hs
    rw [h_CN05 _ hs_re]
    ring
  -- Uniqueness of limits.
  exact tendsto_nhds_unique h_tendsto_dedekind h_tendsto_product

/-- **CN-08** (conditional on CN-05 via CN-07): Given the Dedekind factorization,
the Bernoulli number and root number satisfy
  `W_η · B_{1,η} = -(2h / w : ℂ)`,
where `W_η := rootNumber (legendreDirichlet p)`, `h := classNumber (Kminus p)`,
`w := Units.torsionOrder (Kminus p)`.

For `p > 3` (where `w = 2` via CN-04), this simplifies to `W_η · B = -h`.
Since `W_η² = 1` (`rootNumber_legendreDirichlet_sq`), we have `W_η ∈ {±1}` and
thus `|B_{1,η}| = h`.

Derivation: from the bridge identity `L(η,1)·√p + π·W_η·B = 0`,
substitute CN-07 `L(η,1) = residue` and CN-06 `residue = 2π h / (w √p)` to get
`(2π h / w) + π·W_η·B = 0`, hence `W_η·B = -2h/w`. -/
theorem rootNumber_mul_BernoulliGen_of_CN05 (hp_three_mod_four : p % 4 = 3)
    (h_CN05 : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta (Kminus p) s =
        riemannZeta s * DirichletCharacter.LFunction (legendreDirichlet p) s) :
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    (DirichletCharacter.rootNumber (legendreDirichlet p)) *
        BernoulliGen (legendreDirichlet p) 1 =
      -((2 * (NumberField.classNumber (Kminus p) : ℝ) /
          (NumberField.Units.torsionOrder (Kminus p) : ℝ) : ℝ) : ℂ) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_odd : p ≠ 2 := by omega
  -- Bridge identity.
  have h_bridge := legendreDirichlet_L1_rootNumber_relation p hp_three_mod_four
  -- CN-07: L(η, 1) = residue.
  have h_CN07 := LFunction_one_eq_dedekindZeta_residue_of_CN05 p hp_three_mod_four h_CN05
  -- CN-06: residue = 2πh/(w√p).
  have h_CN06 := dedekindZeta_residue_Kminus p hp_three_mod_four
  -- Substitute.
  rw [← h_CN07] at h_bridge
  rw [h_CN06] at h_bridge
  -- h_bridge: ((2πh/(w√p) : ℝ) : ℂ) * (p : ℂ)^(1/2 : ℂ) + π · W · B = 0.
  -- Simplify (p : ℂ)^(1/2) = √p (we need to coerce).
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have h_sqrt : ((p : ℂ) ^ (1 / 2 : ℂ)) = ((Real.sqrt p : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) from by push_cast; rfl]
    rw [show ((1 : ℂ) / 2) = ((1 / 2 : ℝ) : ℂ) from by push_cast; rfl]
    rw [← Complex.ofReal_cpow hp_pos.le]
  rw [h_sqrt] at h_bridge
  -- Now h_bridge is in ℂ. Convert the real-coerced product to a real number
  -- times I-in-ℂ wait - it's just real arithmetic via coercion.
  have h_w_pos : (0 : ℝ) < (NumberField.Units.torsionOrder (Kminus p) : ℝ) := by
    exact_mod_cast NumberField.Units.torsionOrder_pos (Kminus p)
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hp_pos
  have h_sqrt_ne : (Real.sqrt p : ℝ) ≠ 0 := h_sqrt_pos.ne'
  have h_pi_ne : (Real.pi : ℂ) ≠ 0 := by
    have : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    exact_mod_cast this
  -- Manipulate h_bridge into the desired form.
  -- LHS: (2πh/(w√p) : ℂ) · (√p : ℂ) + π · W · B = 0.
  -- Factor: (2πh/w : ℂ) + π · W · B = 0 (since √p · 1/√p = 1).
  -- Hence π · W · B = -(2πh/w : ℂ), so W · B = -(2h/w : ℂ).
  have h_real : (2 * Real.pi * (NumberField.classNumber (Kminus p) : ℝ) /
        ((NumberField.Units.torsionOrder (Kminus p) : ℝ) * Real.sqrt p) : ℝ) *
        Real.sqrt p =
      (2 * Real.pi * (NumberField.classNumber (Kminus p) : ℝ) /
        (NumberField.Units.torsionOrder (Kminus p) : ℝ) : ℝ) := by
    field_simp
  have h_step1 : ((2 * Real.pi * (NumberField.classNumber (Kminus p) : ℝ) /
          ((NumberField.Units.torsionOrder (Kminus p) : ℝ) * Real.sqrt p) : ℝ) : ℂ) *
          ((Real.sqrt p : ℝ) : ℂ) =
        ((2 * Real.pi * (NumberField.classNumber (Kminus p) : ℝ) /
          (NumberField.Units.torsionOrder (Kminus p) : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast h_real
  rw [h_step1] at h_bridge
  -- h_bridge: ((2πh/w : ℝ) : ℂ) + π · W · B = 0.
  -- Rearrange: π · W · B = -(2πh/w : ℝ) in ℂ.
  have h_pi_cast : ((Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) := rfl
  have h_WB_eq : (Real.pi : ℂ) *
      ((DirichletCharacter.rootNumber (legendreDirichlet p)) *
        BernoulliGen (legendreDirichlet p) 1) =
      -((2 * Real.pi * (NumberField.classNumber (Kminus p) : ℝ) /
          (NumberField.Units.torsionOrder (Kminus p) : ℝ) : ℝ) : ℂ) := by
    linear_combination h_bridge
  -- Divide by π.
  have h_final : (DirichletCharacter.rootNumber (legendreDirichlet p)) *
      BernoulliGen (legendreDirichlet p) 1 =
      -((2 * (NumberField.classNumber (Kminus p) : ℝ) /
          (NumberField.Units.torsionOrder (Kminus p) : ℝ) : ℝ) : ℂ) := by
    have h_div : ((Real.pi : ℂ))⁻¹ *
        ((Real.pi : ℂ) *
          ((DirichletCharacter.rootNumber (legendreDirichlet p)) *
            BernoulliGen (legendreDirichlet p) 1)) =
        ((Real.pi : ℂ))⁻¹ *
          (-((2 * Real.pi * (NumberField.classNumber (Kminus p) : ℝ) /
              (NumberField.Units.torsionOrder (Kminus p) : ℝ) : ℝ) : ℂ)) := by
      rw [h_WB_eq]
    rw [← mul_assoc, inv_mul_cancel₀ h_pi_ne, one_mul] at h_div
    rw [h_div]
    push_cast
    field_simp
  exact h_final

end CN0X_preliminaries

end BernoulliRegular
