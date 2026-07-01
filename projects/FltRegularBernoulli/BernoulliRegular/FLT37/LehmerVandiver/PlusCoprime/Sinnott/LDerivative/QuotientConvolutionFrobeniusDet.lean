import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.Determinant
import BernoulliRegular.LValueAtOne.Defs
import BernoulliRegular.HMinus.KplusLocalCharacters
import BernoulliRegular.HMinus.LValueReduction.LValues
import BernoulliRegular.UnitQuotient.PermutationCharacters
import BernoulliRegular.UnitQuotient.FreeCharacterProfile
import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.RingTheory.RootsOfUnity.Lemmas

/-!
# LV-SIN-C: `L'(0, χ)` formula via cyclotomic-unit logs

For an even nontrivial Dirichlet character χ mod p, the classical
**Dirichlet/Kummer formula**:

  `L'(0, χ̄) = -∑_{a=1}^{p-1} χ(a) · log|1 - ζ^a|`
            = `-∑_{a=1}^{p-1} χ(a) · log|2 sin(πa/p)|`

connects the L-function derivative at zero to logs of cyclotomic units.

This is the analytic content of LV-SIN-C: deriving the explicit form
that feeds the Kummer-Dirichlet determinant evaluation.

## Structure

Mathlib has `LFunction` (analytic continuation), `Even.LFunction_neg_two_mul_nat`
(zero at negative even integers), and `LFunction_modOne_eq`.

What's needed: the closed-form of `L(0, χ)` (= `-B_{1,χ}`) and
`deriv (LFunction χ) 0` connecting to log-cyclotomic-unit sums.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §4.2
  (L-functions and Bernoulli polynomials).
* Mathlib `Mathlib.NumberTheory.LSeries.DirichletContinuation`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

/-- **L-derivative at zero formula (Prop)**: for an even nontrivial
Dirichlet character χ mod p,

  `deriv (LFunction χ̄) 0 = -∑_{a=1}^{p-1} χ(a) · log(2 sin(πa/p))`

This is the Dirichlet derivative formula at zero, the analytic content
required to express `Reg(C⁺)` (the regulator of cyclotomic units) as
a product of L'(0, χ).

The proof uses the Hurwitz-zeta connection + Bernoulli polynomial
explicit formula. -/
def LDerivativeAtZero (χ : DirichletCharacter ℂ p) : Prop :=
  χ.Even → χ ≠ 1 →
  deriv (DirichletCharacter.LFunction χ⁻¹) 0 =
    -∑ a ∈ Finset.Ico 1 p,
      χ a * Real.log (2 * |Real.sin (Real.pi * a / p)|)

/-- **Dirichlet sum form**: an alternative formulation that directly
relates the L-derivative to a sum over cyclotomic units. -/
def DirichletLogSum (χ : DirichletCharacter ℂ p) : ℂ :=
  -∑ a ∈ Finset.Ico 1 p,
    χ a * Real.log (2 * |Real.sin (Real.pi * a / p)|)

/-- **DLS vanishes for odd characters**: for any odd Dirichlet character `χ`
mod `p` (prime, `p ≠ 2`), `DirichletLogSum p χ = 0`.

The cancellation is via the `a ↔ p - a` involution on `Finset.Ico 1 p`:
- `χ(↑(p-a) : ZMod p) = χ(-↑a) = χ(-1) · χ(↑a) = -χ(↑a)` (odd character),
- `Real.sin (π(p-a)/p) = Real.sin (π - πa/p) = Real.sin (πa/p)` (since
  `sin(π - x) = sin(x)`), so the `log` factor is invariant.

Summing across the pair gives `χ(↑a) · L + (-χ(↑a)) · L = 0`, hence the
total sum is 0.

This is the **structural rank deficiency** of the full convolution
log-norm matrix `convolutionMatrixLogNorm p`: its eigenvalues at odd
characters are all 0 (paired against an even-under-negation function),
making `det = 0`. The substantive matrix-restriction step for PF-1 must
use the even-character quotient matrix (size `(p-1)/2`) rather than the
full matrix. -/
theorem DirichletLogSum_eq_zero_of_odd (hp_odd : p ≠ 2)
    (χ : DirichletCharacter ℂ p) (hχ : χ.Odd) :
    DirichletLogSum p χ = 0 := by
  unfold DirichletLogSum
  rw [neg_eq_zero]
  have hp_prime : Nat.Prime p := hp.out
  have hp_pos : 0 < p := hp_prime.pos
  have hp_ne_zero : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp_pos.ne'
  have hp_odd_nat : Odd p := hp_prime.odd_of_ne_two hp_odd
  refine Finset.sum_involution (fun a _ ↦ p - a) ?_ ?_ ?_ ?_
  · -- f(a) + f(p - a) = 0
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.mp ha
    -- χ ↑(p - a) = -χ ↑a (via χ.Odd)
    have h_cast : ((p - a : ℕ) : ZMod p) = -((a : ℕ) : ZMod p) := by
      have h_sum : ((p - a : ℕ) : ZMod p) + ((a : ℕ) : ZMod p) = 0 := by
        rw [← Nat.cast_add, Nat.sub_add_cancel ha2.le]
        exact_mod_cast ZMod.natCast_self p
      linear_combination h_sum
    have h_chi_neg : χ ((p - a : ℕ) : ZMod p) = -χ ((a : ℕ) : ZMod p) := by
      rw [h_cast]
      have h_prod : (-((a : ℕ) : ZMod p)) = (-1 : ZMod p) * ((a : ℕ) : ZMod p) := by
        ring
      rw [h_prod, map_mul]
      have h_odd : χ ((-1 : ZMod p)) = -1 := hχ
      rw [h_odd]
      ring
    -- sin(π(p-a)/p) = sin(πa/p)
    have h_sin_eq :
        Real.sin (Real.pi * (p - a : ℕ) / p) = Real.sin (Real.pi * a / p) := by
      have h_pa : Real.pi * (p - a : ℕ) / p = Real.pi - Real.pi * a / p := by
        push_cast [Nat.cast_sub ha2.le]
        field_simp
      rw [h_pa]
      exact Real.sin_pi_sub _
    -- Combine
    rw [h_chi_neg, h_sin_eq]
    ring
  · -- p - a ≠ a for a ∈ Ico 1 p (always, since p is odd)
    intro a ha _ h
    have ha2 : a < p := (Finset.mem_Ico.mp ha).2
    have h' : p - a = a := h
    have h_canc : p - a + a = p := Nat.sub_add_cancel ha2.le
    rw [h'] at h_canc
    rcases hp_odd_nat with ⟨k, hk⟩
    omega
  · -- p - a ∈ Finset.Ico 1 p
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Ico.mp ha).1
    have ha2 : a < p := (Finset.mem_Ico.mp ha).2
    rw [Finset.mem_Ico]
    refine ⟨Nat.sub_pos_of_lt ha2, Nat.sub_lt_self ha1 ha2.le⟩
  · -- p - (p - a) = a
    intro a ha
    have ha2 : a < p := (Finset.mem_Ico.mp ha).2
    exact Nat.sub_sub_self ha2.le

/-- **The norm of `1 - stdAddChar(↑(-a))` equals `1 - stdAddChar(↑a)`**:
direct from `stdAddChar(-x) = conj(stdAddChar(x))` (shipped in
`BernoulliRegular.stdAddChar_neg_eq_conj`) plus `‖conj z‖ = ‖z‖` and
`conj(1 - z) = 1 - conj(z)`. This is the even-under-negation property of
the cyclotomic log-norm, foundational for descending to the
`(ZMod p)ˣ ⧸ ⟨-1⟩` quotient convolution matrix. -/
theorem norm_one_sub_stdAddChar_neg (a : ZMod p) :
    ‖(1 : ℂ) - ZMod.stdAddChar (N := p) (-a)‖ =
      ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ := by
  rw [BernoulliRegular.stdAddChar_neg_eq_conj]
  -- Goal: ‖1 - conj (stdAddChar a)‖ = ‖1 - stdAddChar a‖
  rw [show (1 : ℂ) - (starRingEnd ℂ) (ZMod.stdAddChar (N := p) a) =
        (starRingEnd ℂ) (1 - ZMod.stdAddChar (N := p) a) from by
    rw [map_sub]; simp]
  exact Complex.norm_conj _

/-- **The log-norm function is even under negation of the unit argument**:
for `a : (ZMod p)ˣ`, `log‖1 - stdAddChar(↑(-a))‖ = log‖1 - stdAddChar(↑a)‖`.
Foundation for descending the convolution log-norm to the quotient. -/
theorem log_norm_one_sub_stdAddChar_unit_neg (a : (ZMod p)ˣ) :
    Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((↑(-a) : ZMod p))‖ =
      Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((↑a : ZMod p))‖ := by
  have h_cast : ((-a : (ZMod p)ˣ) : ZMod p) = -((a : (ZMod p)ˣ) : ZMod p) := by
    push_cast; rfl
  rw [h_cast, norm_one_sub_stdAddChar_neg]

/-- **Descended convolution log-norm**: the log-norm function
`f(a) = log‖1 - stdAddChar(↑a)‖` (for `a : (ZMod p)ˣ`) descends to a
function on the `{±1}`-quotient `CyclotomicEvenDelta p` via
`evenFunctionDescend`. This is the function whose convolution matrix
on the quotient gives the non-singular Frobenius determinant formula
for PF-1's matrix-restriction. -/
noncomputable def convolutionLogNormDescended :
    BernoulliRegular.CyclotomicEvenDelta p → ℂ :=
  BernoulliRegular.evenFunctionDescend (p := p)
    (fun a : BernoulliRegular.CyclotomicUnitDelta p ↦
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ))
    (fun a ↦ by
      have h := log_norm_one_sub_stdAddChar_unit_neg (p := p) a
      exact_mod_cast h)

/-- **Quotient convolution log-norm matrix**: the convolution matrix on
`CyclotomicEvenDelta p = (ZMod p)ˣ ⧸ ⟨-1⟩` (size `(p-1)/2`) with entries
`M[ā, b̄] = convolutionLogNormDescended (ā · b̄)`.

This is the **non-singular** matrix (in contrast to the full
`convolutionMatrixLogNorm p` which has det = 0): odd characters are
quotiented out, leaving only even-character contributions which don't
structurally vanish.

By the Frobenius determinant formula for cyclic abelian groups, the
square determinant of this matrix equals the squared product of
eigenvalues over the characters of `CyclotomicEvenDelta p`, which by
the pullback bijection are exactly the **even Dirichlet characters** of
`(ZMod p)ˣ`. -/
noncomputable def convolutionMatrixLogNormEven :
    Matrix (BernoulliRegular.CyclotomicEvenDelta p)
           (BernoulliRegular.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun a b ↦ convolutionLogNormDescended p (a * b)

/-- **Generic convolution matrix on `CyclotomicEvenDelta p`**: for a function
`f : CyclotomicEvenDelta p → ℂ`, the multiplication-convolution matrix with
entries `M[a, b] = f(a · b)`. This is the abstract version of which
`convolutionMatrixLogNormEven` is the special case at the descended log-norm. -/
noncomputable def convolutionMatrixOnEven
    (f : BernoulliRegular.CyclotomicEvenDelta p → ℂ) :
    Matrix (BernoulliRegular.CyclotomicEvenDelta p)
           (BernoulliRegular.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun a b ↦ f (a * b)

/-- **`convolutionMatrixLogNormEven` is `convolutionMatrixOnEven` applied to
the descended log-norm**: the specific quotient log-norm matrix is just the
generic convolution applied to `convolutionLogNormDescended`. -/
theorem convolutionMatrixLogNormEven_eq_convolutionMatrixOnEven :
    convolutionMatrixLogNormEven p =
      convolutionMatrixOnEven p (convolutionLogNormDescended p) := by
  rfl

/-- **Character matrix on `CyclotomicEvenDelta p`**: the matrix indexed by
characters of the quotient and elements of the quotient, with entries
`F[ξ, a] = ξ(a)`. This is the discrete Fourier transform matrix on the
quotient, the analog of `characterMatrix` for the full group. -/
noncomputable def characterMatrixOnEven :
    Matrix (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
           (BernoulliRegular.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun ξ a ↦ ξ a

/-- **Inverse character matrix on `CyclotomicEvenDelta p`**: with entries
`F'[ξ, b] = ξ(b⁻¹)`. The analog of `inverseCharacterMatrix` for the quotient. -/
noncomputable def inverseCharacterMatrixOnEven :
    Matrix (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
           (BernoulliRegular.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun ξ b ↦ ξ (b⁻¹)

/-- **Pontryagin cardinality on the quotient**:
`#{MulChar (CyclotomicEvenDelta p) ℂ} = #(CyclotomicEvenDelta p)`.
Direct from `MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity` (using that
ℂ has all roots of unity) + `toUnits.symm.toEquiv` (units of a group = the
group cardinality-wise). -/
theorem nat_card_mulChar_cyclotomicEvenDelta_eq :
    Nat.card (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) =
      Nat.card (BernoulliRegular.CyclotomicEvenDelta p) := by
  haveI : NeZero (Monoid.exponent (BernoulliRegular.CyclotomicEvenDelta p)ˣ) := by
    constructor
    haveI : Fintype (BernoulliRegular.CyclotomicEvenDelta p)ˣ := Fintype.ofFinite _
    exact Monoid.exponent_ne_zero_of_finite
  rw [MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity]
  exact Nat.card_congr toUnits.symm.toEquiv

/-- **Pontryagin equivalence on the quotient**: a non-canonical bijection
between `MulChar (CyclotomicEvenDelta p) ℂ` and `CyclotomicEvenDelta p`.
Used to reindex the character matrix as a square matrix for determinant
computations. -/
noncomputable def quotCharEquivQuot :
    MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ ≃
      BernoulliRegular.CyclotomicEvenDelta p := by
  classical
  haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  exact nat_card_mulChar_cyclotomicEvenDelta_eq p

/-- **Matrix-level eigenvalue formula on the quotient**: for the multiplicative
convolution matrix `convolutionMatrixOnEven f`:

  `(characterMatrixOnEven · convolutionMatrixOnEven f)[ξ, b] =
    ξ(b⁻¹) · (∑_a ξ(a) · f(a))`.

Direct parallel of `characterMatrix_mul_convolutionMatrix_apply` on the
quotient: reindex via `a ↦ a · b⁻¹` and use character multiplicativity. -/
theorem characterMatrixOnEven_mul_convolutionMatrixOnEven_apply
    (f : BernoulliRegular.CyclotomicEvenDelta p → ℂ)
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)
    (b : BernoulliRegular.CyclotomicEvenDelta p) :
    (characterMatrixOnEven p * convolutionMatrixOnEven p f) ξ b =
      ξ (b⁻¹) * ∑ a : BernoulliRegular.CyclotomicEvenDelta p, ξ a * f a := by
  classical
  simp only [Matrix.mul_apply, characterMatrixOnEven, convolutionMatrixOnEven,
    Matrix.of_apply]
  have h_reindex : ∑ a : BernoulliRegular.CyclotomicEvenDelta p, ξ a * f (a * b) =
      ∑ a : BernoulliRegular.CyclotomicEvenDelta p, ξ (a * b⁻¹) * f a := by
    apply (Fintype.sum_equiv (Equiv.mulRight b⁻¹) _ _ _).symm
    intro a
    rw [Equiv.coe_mulRight]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [h_reindex]
  have h_factor : ∀ a : BernoulliRegular.CyclotomicEvenDelta p,
      ξ (a * b⁻¹) * f a = ξ b⁻¹ * (ξ a * f a) := by
    intro a
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl (fun a _ ↦ h_factor a)]
  rw [← Finset.mul_sum]

/-- **Matrix factorisation on the quotient** `F · M = D · F'`:

  characterMatrixOnEven · convolutionMatrixOnEven f =
    Matrix.diagonal (fun ξ ↦ ∑ a, ξ a · f a) · inverseCharacterMatrixOnEven.

Parallel of `characterMatrix_mul_convolutionMatrix_eq_diag_mul_inverseCharacterMatrix`. -/
theorem characterMatrixOnEven_mul_convolutionMatrixOnEven_eq_diag_mul_inverse
    (f : BernoulliRegular.CyclotomicEvenDelta p → ℂ) :
    haveI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Classical.decEq _
    haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    characterMatrixOnEven p * convolutionMatrixOnEven p f =
      (Matrix.diagonal (fun ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ ↦
        ∑ a : BernoulliRegular.CyclotomicEvenDelta p, ξ a * f a)) *
      inverseCharacterMatrixOnEven p := by
  letI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  ext ξ b
  rw [characterMatrixOnEven_mul_convolutionMatrixOnEven_apply, Matrix.diagonal_mul]
  simp only [inverseCharacterMatrixOnEven, Matrix.of_apply]
  ring

/-- **Square character matrix on `CyclotomicEvenDelta p`**: the
`((p-1)/2) × ((p-1)/2)` matrix indexed by `CyclotomicEvenDelta p × CyclotomicEvenDelta p`
with entries `(quotCharEquivQuot.symm k)(a)`, i.e., row `k` is the character
corresponding to `k` under the Pontryagin equivalence. Square form of
`characterMatrixOnEven` for determinant computations. -/
noncomputable def characterMatrixSquareOnEven :
    Matrix (BernoulliRegular.CyclotomicEvenDelta p)
           (BernoulliRegular.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun k a ↦ ((quotCharEquivQuot p).symm k) a

/-- **Square inverse character matrix on `CyclotomicEvenDelta p`**:
`F'[k, b] = (quotCharEquivQuot.symm k)(b⁻¹)`. -/
noncomputable def inverseCharacterMatrixSquareOnEven :
    Matrix (BernoulliRegular.CyclotomicEvenDelta p)
           (BernoulliRegular.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun k b ↦ ((quotCharEquivQuot p).symm k) b⁻¹

/-- **Square eigenvalue formula on the quotient**:
`(characterMatrixSquareOnEven · convolutionMatrixOnEven f)[k, b]
= (quotCharEquivQuot.symm k)(b⁻¹) · (∑_a (e.symm k)(a) · f(a))`. -/
theorem characterMatrixSquareOnEven_mul_convolutionMatrixOnEven_apply
    (f : BernoulliRegular.CyclotomicEvenDelta p → ℂ)
    (k b : BernoulliRegular.CyclotomicEvenDelta p) :
    (characterMatrixSquareOnEven p * convolutionMatrixOnEven p f) k b =
      ((quotCharEquivQuot p).symm k) b⁻¹ *
        ∑ a : BernoulliRegular.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a := by
  simp only [characterMatrixSquareOnEven]
  exact characterMatrixOnEven_mul_convolutionMatrixOnEven_apply
    (p := p) f ((quotCharEquivQuot p).symm k) b

/-- **Square matrix factorisation on the quotient** `F_square · M = D · F'_square`. -/
theorem characterMatrixSquareOnEven_mul_convolutionMatrixOnEven_eq_diag_mul_inv
    (f : BernoulliRegular.CyclotomicEvenDelta p → ℂ) :
    characterMatrixSquareOnEven p * convolutionMatrixOnEven p f =
      Matrix.diagonal (fun k : BernoulliRegular.CyclotomicEvenDelta p ↦
        ∑ a : BernoulliRegular.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) *
      inverseCharacterMatrixSquareOnEven p := by
  classical
  ext k b
  rw [characterMatrixSquareOnEven_mul_convolutionMatrixOnEven_apply, Matrix.diagonal_mul]
  simp only [inverseCharacterMatrixSquareOnEven, Matrix.of_apply]
  ring

/-- **Square determinant identity on the quotient**:

  det(F_square) · det(M) = (∏ k, λ_{e.symm k}) · det(F'_square),

where `λ_χ = ∑ a, χ(a) · f(a)`. -/
theorem det_characterMatrixSquareOnEven_mul_convolutionMatrixOnEven
    (f : BernoulliRegular.CyclotomicEvenDelta p → ℂ) :
    (characterMatrixSquareOnEven p).det * (convolutionMatrixOnEven p f).det =
      (∏ k : BernoulliRegular.CyclotomicEvenDelta p,
        ∑ a : BernoulliRegular.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) *
      (inverseCharacterMatrixSquareOnEven p).det := by
  classical
  rw [← Matrix.det_mul,
    characterMatrixSquareOnEven_mul_convolutionMatrixOnEven_eq_diag_mul_inv,
    Matrix.det_mul, Matrix.det_diagonal]

/-- **`inverseCharacterMatrixSquareOnEven` as a column-inversion submatrix of
`characterMatrixSquareOnEven`**: `F'` is `F` with columns reindexed via the
inversion permutation `b ↦ b⁻¹`. Parallel to `inverseCharacterMatrixSquare_eq_submatrix`. -/
theorem inverseCharacterMatrixSquareOnEven_eq_submatrix :
    inverseCharacterMatrixSquareOnEven p =
      (characterMatrixSquareOnEven p).submatrix id
        (Equiv.inv (BernoulliRegular.CyclotomicEvenDelta p)) := by
  ext k b
  simp only [inverseCharacterMatrixSquareOnEven, characterMatrixSquareOnEven,
    Matrix.submatrix_apply, Matrix.of_apply, id_def, Equiv.inv_apply]

/-- **Determinants squared agree** for `characterMatrixSquareOnEven` and
`inverseCharacterMatrixSquareOnEven`: the column-inversion permutation has
determinant sign ±1, which squares to 1. -/
theorem det_inverseCharacterMatrixSquareOnEven_sq_eq_det_characterMatrixSquareOnEven_sq :
    (inverseCharacterMatrixSquareOnEven p).det ^ 2 =
      (characterMatrixSquareOnEven p).det ^ 2 := by
  rw [inverseCharacterMatrixSquareOnEven_eq_submatrix]
  rw [Matrix.det_permute' (Equiv.inv (BernoulliRegular.CyclotomicEvenDelta p))
      (characterMatrixSquareOnEven p)]
  rw [mul_pow]
  rw [show ((↑↑(Equiv.Perm.sign
      (Equiv.inv (BernoulliRegular.CyclotomicEvenDelta p))) : ℂ)) ^ 2 = 1 from ?_]
  · ring
  · have h_sign : (Equiv.Perm.sign
        (Equiv.inv (BernoulliRegular.CyclotomicEvenDelta p))) ^ 2 = 1 :=
      Int.units_pow_two _
    have h_cast : (((Equiv.Perm.sign
        (Equiv.inv (BernoulliRegular.CyclotomicEvenDelta p))) ^ 2 : ℤˣ) : ℂ) =
        ((1 : ℤˣ) : ℂ) := by
      rw [h_sign]
    push_cast at h_cast ⊢
    exact_mod_cast h_cast

/-- **Squared Frobenius determinant identity on the quotient (conditional
on `det F ≠ 0`)**:

  det(convolutionMatrixOnEven f)² = (∏_k λ_{e.symm k})²

where `λ_χ = ∑ a, χ(a) · f(a)`. Parallel of
`det_convolutionMatrix_sq_eq_prod_lambda_sq`. -/
theorem det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq
    (f : BernoulliRegular.CyclotomicEvenDelta p → ℂ)
    (h_det_F_ne : (characterMatrixSquareOnEven p).det ≠ 0) :
    (convolutionMatrixOnEven p f).det ^ 2 =
      (∏ k : BernoulliRegular.CyclotomicEvenDelta p,
        ∑ a : BernoulliRegular.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) ^ 2 := by
  have h_det := det_characterMatrixSquareOnEven_mul_convolutionMatrixOnEven (p := p) f
  have h_det_sq : ((characterMatrixSquareOnEven p).det *
      (convolutionMatrixOnEven p f).det) ^ 2 =
      ((∏ k : BernoulliRegular.CyclotomicEvenDelta p,
        ∑ a : BernoulliRegular.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) *
      (inverseCharacterMatrixSquareOnEven p).det) ^ 2 := by
    rw [h_det]
  rw [mul_pow, mul_pow] at h_det_sq
  rw [det_inverseCharacterMatrixSquareOnEven_sq_eq_det_characterMatrixSquareOnEven_sq]
    at h_det_sq
  have h_det_F_sq_ne : (characterMatrixSquareOnEven p).det ^ 2 ≠ 0 :=
    pow_ne_zero _ h_det_F_ne
  have h_mul_cancel : (characterMatrixSquareOnEven p).det ^ 2 *
      (convolutionMatrixOnEven p f).det ^ 2 =
      (characterMatrixSquareOnEven p).det ^ 2 *
      (∏ k : BernoulliRegular.CyclotomicEvenDelta p,
          ∑ a : BernoulliRegular.CyclotomicEvenDelta p,
            ((quotCharEquivQuot p).symm k) a * f a) ^ 2 := by
    linear_combination h_det_sq
  exact (mul_left_cancel₀ h_det_F_sq_ne h_mul_cancel)

/-- **Character orthogonality at the matrix level on the quotient**:
`characterMatrixSquareOnEven · inverseCharacterMatrixSquareOnEvenᵀ =
(card G) · I` where G = CyclotomicEvenDelta p. The classical orthogonality
`∑_a χ(a) · ψ(a⁻¹) = card · δ_{χ=ψ}` at the matrix level. -/
theorem characterMatrixSquareOnEven_mul_inverseCharacterMatrixSquareOnEven_transpose :
    characterMatrixSquareOnEven p *
        Matrix.transpose (inverseCharacterMatrixSquareOnEven p) =
      ((Fintype.card (BernoulliRegular.CyclotomicEvenDelta p) : ℕ) : ℂ) •
        (1 : Matrix (BernoulliRegular.CyclotomicEvenDelta p)
                    (BernoulliRegular.CyclotomicEvenDelta p) ℂ) := by
  classical
  ext k k'
  simp only [characterMatrixSquareOnEven, inverseCharacterMatrixSquareOnEven,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have h_inv : ∀ a : BernoulliRegular.CyclotomicEvenDelta p,
      ((quotCharEquivQuot p).symm k) a *
          ((quotCharEquivQuot p).symm k') a⁻¹ =
        (((quotCharEquivQuot p).symm k) *
          ((quotCharEquivQuot p).symm k')⁻¹) a := by
    intro a
    rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv']
    rw [map_inv]
  rw [Finset.sum_congr rfl (fun a _ ↦ h_inv a)]
  by_cases hkk : k = k'
  · subst hkk
    rw [if_pos rfl, mul_one]
    rw [show ((quotCharEquivQuot p).symm k) *
        ((quotCharEquivQuot p).symm k)⁻¹ =
        (1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) from mul_inv_cancel _]
    have h_one := MulChar.sum_one_eq_card_units
      (R := BernoulliRegular.CyclotomicEvenDelta p) (R' := ℂ)
    rw [h_one]
    -- Need: ↑(card Gˣ) = ↑(card G) for G a group.
    have h_card : Fintype.card (BernoulliRegular.CyclotomicEvenDelta p)ˣ =
        Fintype.card (BernoulliRegular.CyclotomicEvenDelta p) :=
      Fintype.card_congr toUnits.symm.toEquiv
    rw [h_card]
  · rw [if_neg hkk, mul_zero]
    have h_ne : ((quotCharEquivQuot p).symm k) *
        ((quotCharEquivQuot p).symm k')⁻¹ ≠
        (1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) := by
      intro h_eq
      apply hkk
      have h_inv_cancel : ((quotCharEquivQuot p).symm k) =
          ((quotCharEquivQuot p).symm k') := by
        have := congrArg (· * ((quotCharEquivQuot p).symm k')) h_eq
        rw [mul_assoc, inv_mul_cancel, mul_one, one_mul] at this
        exact this
      exact (quotCharEquivQuot p).symm.injective h_inv_cancel
    exact MulChar.sum_eq_zero_of_ne_one h_ne

/-- **`characterMatrixSquareOnEven` has nonzero determinant**: from the
orthogonality `F · F'ᵀ = (card G) · I`, taking determinants gives
`det(F) · det(F'ᵀ) = (card G)^(card G)`, non-zero for card G > 0.
Hence `det(F) ≠ 0`. -/
theorem det_characterMatrixSquareOnEven_ne_zero (hp_two : 2 < p) :
    (characterMatrixSquareOnEven p).det ≠ 0 := by
  classical
  intro h_det_zero
  have h_orth :=
    characterMatrixSquareOnEven_mul_inverseCharacterMatrixSquareOnEven_transpose
      (p := p)
  have h_det_orth := congrArg Matrix.det h_orth
  rw [Matrix.det_mul, h_det_zero, zero_mul] at h_det_orth
  rw [Matrix.det_smul, Matrix.det_one, mul_one] at h_det_orth
  -- h_det_orth : 0 = card^(card)
  have h_card_pos : 0 < Fintype.card (BernoulliRegular.CyclotomicEvenDelta p) := by
    rw [BernoulliRegular.cyclotomicEvenDelta_card (p := p) hp_two]
    omega
  have h_card_ne : ((Fintype.card (BernoulliRegular.CyclotomicEvenDelta p) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr h_card_pos.ne'
  have h_pow_ne : ((Fintype.card (BernoulliRegular.CyclotomicEvenDelta p) : ℕ) : ℂ) ^
      Fintype.card (BernoulliRegular.CyclotomicEvenDelta p) ≠ 0 := pow_ne_zero _ h_card_ne
  exact h_pow_ne h_det_orth.symm

/-- **Unconditional squared Frobenius determinant formula on the quotient**:
combining `det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq` with
`det_characterMatrixSquareOnEven_ne_zero`, the squared determinant of the
convolution matrix on `CyclotomicEvenDelta p` equals the squared product
of eigenvalues:

  det(convolutionMatrixOnEven p f)² = (∏_k λ_{e.symm k})²

where `λ_χ = ∑ a, χ(a) · f(a)`. Unconditional for `p > 2`. -/
theorem det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq_unconditional
    (f : BernoulliRegular.CyclotomicEvenDelta p → ℂ) (hp_two : 2 < p) :
    (convolutionMatrixOnEven p f).det ^ 2 =
      (∏ k : BernoulliRegular.CyclotomicEvenDelta p,
        ∑ a : BernoulliRegular.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) ^ 2 :=
  det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq (p := p) f
    (det_characterMatrixSquareOnEven_ne_zero (p := p) hp_two)

/-- **Symmetry of the quotient convolution matrix**: since the quotient group
`CyclotomicEvenDelta p` is abelian, the convolution matrix is symmetric. -/
theorem convolutionMatrixLogNormEven_symm
    (a b : BernoulliRegular.CyclotomicEvenDelta p) :
    convolutionMatrixLogNormEven p a b = convolutionMatrixLogNormEven p b a := by
  unfold convolutionMatrixLogNormEven
  rw [Matrix.of_apply, Matrix.of_apply, mul_comm]

/-- **Matrix dimension of `convolutionMatrixLogNormEven`**: the matrix has
`(p-1)/2 × (p-1)/2` size, matching the rank of the cyclotomic-unit family
on `K⁺` (after removing the trivial-character contribution). Direct from
`BernoulliRegular.cyclotomicEvenDelta_card`. -/
theorem fintype_card_cyclotomicEvenDelta_eq (hp_two : 2 < p) :
    Fintype.card (BernoulliRegular.CyclotomicEvenDelta p) = (p - 1) / 2 :=
  BernoulliRegular.cyclotomicEvenDelta_card (p := p) hp_two

/-- **Descended log-norm at identity**: the value of the descended log-norm
function at the identity `1 : CyclotomicEvenDelta p` equals the original
log-norm at `1 : (ZMod p)ˣ`, i.e.,
`log‖1 - stdAddChar(1)‖ = log(2|sin(π/p)|)`. -/
@[simp]
theorem convolutionLogNormDescended_one :
    convolutionLogNormDescended p (1 : BernoulliRegular.CyclotomicEvenDelta p) =
      ((Real.log ‖(1 : ℂ) -
        ZMod.stdAddChar (N := p) ((1 : (ZMod p)ˣ) : ZMod p)‖ : ℝ) : ℂ) := by
  have h_one : (1 : BernoulliRegular.CyclotomicEvenDelta p) =
      BernoulliRegular.cyclotomicEvenDeltaQuotient p 1 := by
    rw [BernoulliRegular.cyclotomicEvenDeltaQuotient_apply]
    rfl
  rw [h_one]
  unfold convolutionLogNormDescended
  rfl

/-- **Diagonal entry of the quotient convolution matrix at identity**: the
`(1, 1)` entry equals `convolutionLogNormDescended p 1` (since `1 · 1 = 1`
in the abelian group `CyclotomicEvenDelta p`). -/
@[simp]
theorem convolutionMatrixLogNormEven_one_one :
    convolutionMatrixLogNormEven p 1 1 = convolutionLogNormDescended p 1 := by
  unfold convolutionMatrixLogNormEven
  rw [Matrix.of_apply, mul_one]

/-- **Quotient eigenvalue at character `ξ`**: for
`ξ : MulChar (CyclotomicEvenDelta p) ℂ`,
the eigenvalue of `convolutionMatrixLogNormEven` at the descended character is
`∑ ā : CyclotomicEvenDelta p, ξ(ā) · convolutionLogNormDescended(ā)`. This is
the natural Frobenius eigenvalue on the quotient. -/
noncomputable def quotientEigenvalue
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) : ℂ :=
  ∑ ā : BernoulliRegular.CyclotomicEvenDelta p,
    ξ ā * convolutionLogNormDescended p ā

/-- **Eigenvalues in `quotientEigenvalue` form**: the Frobenius eigenvalue
at the `k`-th character (via `quotCharEquivQuot.symm k`) equals
`quotientEigenvalue` at that character, applied to `convolutionLogNormDescended`. -/
theorem prod_lambda_eq_prod_quotientEigenvalue :
    (∏ k : BernoulliRegular.CyclotomicEvenDelta p,
      ∑ a : BernoulliRegular.CyclotomicEvenDelta p,
        ((quotCharEquivQuot p).symm k) a * convolutionLogNormDescended p a) =
    ∏ k : BernoulliRegular.CyclotomicEvenDelta p,
      quotientEigenvalue p ((quotCharEquivQuot p).symm k) := by
  refine Finset.prod_congr rfl (fun k _ ↦ ?_)
  rfl

/-- **Squared det of `convolutionMatrixLogNormEven` in eigenvalue product form**:
combining the unconditional Frobenius det formula with `quotientEigenvalue`. -/
theorem det_convolutionMatrixLogNormEven_sq_eq_prod_quotientEigenvalue_sq
    (hp_two : 2 < p) :
    (convolutionMatrixLogNormEven p).det ^ 2 =
      (∏ k : BernoulliRegular.CyclotomicEvenDelta p,
        quotientEigenvalue p ((quotCharEquivQuot p).symm k)) ^ 2 := by
  rw [convolutionMatrixLogNormEven_eq_convolutionMatrixOnEven]
  rw [det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq_unconditional p _ hp_two]
  rw [prod_lambda_eq_prod_quotientEigenvalue]

/-- **Product reindexed via the Pontryagin equivalence**: the product over
`k : CyclotomicEvenDelta p` of a function evaluated at `(quotCharEquivQuot.symm k)`
equals the product over `ξ : MulChar (CyclotomicEvenDelta p) ℂ` directly. -/
theorem prod_quot_eq_prod_mulChar
    (f : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ → ℂ) :
    haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    ∏ k : BernoulliRegular.CyclotomicEvenDelta p,
        f ((quotCharEquivQuot p).symm k) =
      ∏ ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ, f ξ := by
  classical
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  exact (Fintype.prod_equiv (quotCharEquivQuot p)
    (fun ξ ↦ f ξ)
    (fun k ↦ f ((quotCharEquivQuot p).symm k))
    (fun ξ ↦ by simp only [Equiv.symm_apply_apply])).symm

/-- **Half-sum identity**: for any even function `f : (ZMod p)ˣ → ℂ`
(with `f(-a) = f(a)`), summing over the full group gives twice the sum
over the `{±1}`-quotient `CyclotomicEvenDelta p` (for `p > 2`).

Proof: rewrite `f(a) = f̄(q(a))` via `evenFunctionDescend_apply_mk`,
then use `Finset.sum_comp` to rewrite the full sum as a sum over the
image with fiber-cardinality weights. The image is the whole quotient
(by surjectivity of `q`), and each fiber has cardinality `2` (by the
size-2 subgroup `⟨-1⟩` acting freely for `p > 2`). -/
theorem sum_full_eq_two_mul_sum_descended (f : BernoulliRegular.CyclotomicUnitDelta p → ℂ)
    (hf_even : ∀ a, f (-a) = f a) (hp_two : 2 < p) :
    ∑ a : BernoulliRegular.CyclotomicUnitDelta p, f a =
      2 * ∑ b : BernoulliRegular.CyclotomicEvenDelta p,
            BernoulliRegular.evenFunctionDescend (p := p) f hf_even b := by
  classical
  -- Step 1: rewrite f(a) as f̄(q(a))
  have h_step1 : ∀ a, f a =
      BernoulliRegular.evenFunctionDescend (p := p) f hf_even
        (BernoulliRegular.cyclotomicEvenDeltaQuotient p a) := by
    intro a
    rw [BernoulliRegular.cyclotomicEvenDeltaQuotient_apply,
        BernoulliRegular.evenFunctionDescend_apply_mk]
  simp_rw [h_step1]
  -- Step 2: apply Finset.sum_comp
  rw [Finset.sum_comp _ (BernoulliRegular.cyclotomicEvenDeltaQuotient p)]
  -- Step 3: image of q over univ is univ (q surjective)
  have h_image : Finset.image (BernoulliRegular.cyclotomicEvenDeltaQuotient p)
        (Finset.univ : Finset (BernoulliRegular.CyclotomicUnitDelta p)) =
      Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro b
    rw [Finset.mem_image]
    refine ⟨Quotient.out b, Finset.mem_univ _, ?_⟩
    rw [BernoulliRegular.cyclotomicEvenDeltaQuotient_apply]
    exact Quotient.out_eq b
  rw [h_image]
  -- Step 4: each fiber has cardinality 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ ↦ ?_)
  have h_card : ({a ∈ (Finset.univ : Finset (BernoulliRegular.CyclotomicUnitDelta p)) |
      BernoulliRegular.cyclotomicEvenDeltaQuotient p a = b}).card = 2 := by
    -- The fiber over b is in bijection with the subgroup ⟨-1⟩ of size 2.
    have h_equiv := QuotientGroup.preimageMkEquivSubgroupProdSet
      (BernoulliRegular.CyclotomicEvenDeltaSubgroup p) ({b} : Set _)
    have h_card_eq :
        Fintype.card (QuotientGroup.mk ⁻¹' ({b} : Set _) :
            Set (BernoulliRegular.CyclotomicUnitDelta p)) =
        Fintype.card (BernoulliRegular.CyclotomicEvenDeltaSubgroup p) * 1 := by
      rw [Fintype.card_congr h_equiv, Fintype.card_prod]
      simp
    rw [BernoulliRegular.cyclotomicEvenDeltaSubgroup_card (p := p) hp_two] at h_card_eq
    rw [show ({a ∈ Finset.univ | BernoulliRegular.cyclotomicEvenDeltaQuotient p a = b} :
        Finset _).card =
        Fintype.card (QuotientGroup.mk ⁻¹' ({b} : Set _) :
            Set (BernoulliRegular.CyclotomicUnitDelta p)) from ?_]
    · omega
    · rw [Fintype.card_ofFinset]
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage,
        Set.mem_singleton_iff]
      rfl
  rw [h_card]
  ring

/-- **Twice quotient eigenvalue = full-group sum at the pullback character**:
for `ξ : MulChar (CyclotomicEvenDelta p) ℂ` and `p > 2`,
`2 · quotientEigenvalue p ξ = ∑_a (pullback ξ)(a) · log‖1 - stdAddChar(↑a)‖`,
summing over `a : (ZMod p)ˣ` (the unit-group). Direct application of the
half-sum identity `sum_full_eq_two_mul_sum_descended` to the even function
`f(a) = (pullback ξ)(a) · log-norm(↑a)`. -/
theorem two_mul_quotientEigenvalue_eq_sum_full
    (ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) (hp_two : 2 < p) :
    2 * quotientEigenvalue p ξ =
      ∑ a : BernoulliRegular.CyclotomicUnitDelta p,
        BernoulliRegular.evenDeltaCharacterPullback (p := p) ξ a *
          ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) := by
  set f : BernoulliRegular.CyclotomicUnitDelta p → ℂ := fun a ↦
    BernoulliRegular.evenDeltaCharacterPullback (p := p) ξ a *
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) with hf_def
  have hf_even : ∀ a : BernoulliRegular.CyclotomicUnitDelta p, f (-a) = f a := by
    intro a
    simp only [hf_def]
    rw [log_norm_one_sub_stdAddChar_unit_neg (p := p) a]
    congr 1
    change ξ (BernoulliRegular.cyclotomicEvenDeltaQuotient p (-a)) =
        ξ (BernoulliRegular.cyclotomicEvenDeltaQuotient p a)
    rw [BernoulliRegular.cyclotomicEvenDeltaQuotient_neg]
  have h_half := sum_full_eq_two_mul_sum_descended (p := p) f hf_even hp_two
  -- h_half : ∑ a, f a = 2 * ∑ b, evenFunctionDescend f hf_even b
  -- Show: quotientEigenvalue p ξ = ∑ b, evenFunctionDescend f hf_even b
  have h_quot_eq : quotientEigenvalue p ξ =
      ∑ b : BernoulliRegular.CyclotomicEvenDelta p,
        BernoulliRegular.evenFunctionDescend (p := p) f hf_even b := by
    unfold quotientEigenvalue
    refine Finset.sum_congr rfl (fun b _ ↦ ?_)
    obtain ⟨a, rfl⟩ : ∃ a : BernoulliRegular.CyclotomicUnitDelta p,
        BernoulliRegular.cyclotomicEvenDeltaQuotient p a = b :=
      ⟨Quotient.out b,
        by rw [BernoulliRegular.cyclotomicEvenDeltaQuotient_apply]; exact Quotient.out_eq b⟩
    -- Convert q a to QuotientGroup.mk a so evenFunctionDescend_apply_mk fires.
    rw [BernoulliRegular.cyclotomicEvenDeltaQuotient_apply]
    rw [BernoulliRegular.evenFunctionDescend_apply_mk]
    simp only [hf_def]
    -- Goal: ξ ↑a * convolutionLogNormDescended ↑a =
    --       pullback ξ a * log-norm a
    unfold convolutionLogNormDescended
    rw [BernoulliRegular.evenFunctionDescend_apply_mk]
    -- Use pullback def: `ξ ↑a = pullback ξ a`.
    rfl
  rw [h_quot_eq, ← h_half]

/-- **Sum reindex `(ZMod p)ˣ → Finset.Ico 1 p`**: for any function `F : ℕ → ℂ`,
the sum over the unit group equals the sum over `{1, ..., p-1}` via the
bijection `a ↦ a.val`. Standard reindexing for prime `p`. -/
theorem sum_units_val_eq_sum_Ico (F : ℕ → ℂ) :
    ∑ a : (ZMod p)ˣ, F ((a : ZMod p).val) = ∑ n ∈ Finset.Ico 1 p, F n := by
  have hp_pos : 0 < p := hp.out.pos
  refine Finset.sum_bij (fun (a : (ZMod p)ˣ) _ ↦ (a : ZMod p).val)
    (fun a _ ↦ ?_) (fun a _ b _ heq ↦ ?_) (fun n hn ↦ ?_) (fun _ _ ↦ rfl)
  · rw [Finset.mem_Ico]
    refine ⟨?_, ZMod.val_lt _⟩
    have h_ne : (a : ZMod p).val ≠ 0 := by
      intro h
      rw [ZMod.val_eq_zero] at h
      exact a.ne_zero h
    exact Nat.one_le_iff_ne_zero.mpr h_ne
  · apply Units.ext
    apply ZMod.val_injective _ heq
  · rw [Finset.mem_Ico] at hn
    refine ⟨ZMod.unitOfCoprime n
      (Nat.coprime_comm.mp (Nat.coprime_of_lt_prime (by omega) hn.2 hp.out)),
      Finset.mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hn.2

/-- **Quotient eigenvalue at the trivial character (sum form)**: at the
trivial MulChar `1 : MulChar (CyclotomicEvenDelta p) ℂ`,
`2 · quotientEigenvalue p 1 = ∑ a : (ZMod p)ˣ, log‖1 - stdAddChar(↑a)‖`.

Direct from `two_mul_quotientEigenvalue_eq_sum_full` + the fact that
`(pullback 1)(a) = 1` for `a : (ZMod p)ˣ` (since every group element is a unit). -/
theorem two_mul_quotientEigenvalue_trivial_eq_sum_logNorm (hp_two : 2 < p) :
    2 * quotientEigenvalue p (1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) =
      ∑ a : BernoulliRegular.CyclotomicUnitDelta p,
        ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) := by
  rw [two_mul_quotientEigenvalue_eq_sum_full p 1 hp_two]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  have h_unit : IsUnit
      (BernoulliRegular.cyclotomicEvenDeltaQuotient p a) := Group.isUnit _
  change (1 : MulChar _ _) (BernoulliRegular.cyclotomicEvenDeltaQuotient p a) *
      _ = _
  rw [MulChar.one_apply h_unit, one_mul]

/-- **Entry evaluation on quotient representatives**: for any `a b : (ZMod p)ˣ`,
the entry of `convolutionMatrixLogNormEven p` at `(q(a), q(b))` is the
log-norm at the representative `a · b`. Direct from the quotient map being
a homomorphism + `evenFunctionDescend_apply_mk`. -/
@[simp]
theorem convolutionMatrixLogNormEven_apply_quotient
    (a b : BernoulliRegular.CyclotomicUnitDelta p) :
    convolutionMatrixLogNormEven p
        (BernoulliRegular.cyclotomicEvenDeltaQuotient p a)
        (BernoulliRegular.cyclotomicEvenDeltaQuotient p b) =
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p)
          (((a * b : BernoulliRegular.CyclotomicUnitDelta p) : ZMod p))‖ : ℝ) : ℂ) := by
  unfold convolutionMatrixLogNormEven
  rw [Matrix.of_apply]
  rw [BernoulliRegular.cyclotomicEvenDeltaQuotient_apply,
      BernoulliRegular.cyclotomicEvenDeltaQuotient_apply]
  rw [show (QuotientGroup.mk a : BernoulliRegular.CyclotomicEvenDelta p) *
        QuotientGroup.mk b = QuotientGroup.mk (a * b) from rfl]
  unfold convolutionLogNormDescended
  rfl

/-- **∏ over odd characters of DLS = 0** (when there exists at least one odd
character, equivalently when `p ≠ 2`): immediate corollary of
`DirichletLogSum_eq_zero_of_odd` since `oddCharacters p` is nonempty
for `p ≠ 2` (the quadratic character is always odd; or more generally
half of the `(p-1)` Dirichlet characters mod `p > 2` are odd). -/
theorem prod_oddCharacters_DirichletLogSum_eq_zero
    (hp_odd : p ≠ 2)
    (hodd_nonempty : (BernoulliRegular.oddCharacters p).Nonempty) :
    ∏ χ ∈ BernoulliRegular.oddCharacters p, DirichletLogSum p χ = 0 := by
  classical
  obtain ⟨χ, hχ_mem⟩ := hodd_nonempty
  refine Finset.prod_eq_zero hχ_mem ?_
  have hχ_odd : χ.Odd := by
    unfold BernoulliRegular.oddCharacters at hχ_mem
    exact (Finset.mem_filter.mp hχ_mem).2
  exact DirichletLogSum_eq_zero_of_odd (p := p) hp_odd χ hχ_odd

/-- **L-value at 0 = -B_{1,χ}**: classical Dirichlet formula for non-trivial
even χ mod p. Stated as a Prop to capture the deferred analytic identity. -/
def LValueAtZeroFormula (χ : DirichletCharacter ℂ p) : Prop :=
  χ.Even → χ ≠ 1 →
  DirichletCharacter.LFunction χ 0 = 0 -- L(0, χ) = 0 for even nontrivial χ

end Sinnott

end FLT37

end BernoulliRegular

end
