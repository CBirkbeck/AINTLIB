import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# LeanBridge issue #56: totally positive elements

The definition is stated using the infinite-place API: every real infinite place sends the element
to a positive real number.
-/

namespace NumberField

variable {K : Type*} [Field K]

/-- An element is totally positive if it is positive under every real infinite place. -/
def IsTotallyPositive (x : K) : Prop :=
  ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < InfinitePlace.embedding_of_isReal hw x

lemma isTotallyPositive_iff {x : K} :
    IsTotallyPositive x ↔
      ∀ (w : InfinitePlace K) (hw : w.IsReal), 0 < InfinitePlace.embedding_of_isReal hw x :=
  Iff.rfl

namespace IsTotallyPositive

lemma add {x y : K} (hx : IsTotallyPositive x) (hy : IsTotallyPositive y) :
    IsTotallyPositive (x + y) := by
  intro w hw
  simpa using add_pos (hx w hw) (hy w hw)

lemma mul {x y : K} (hx : IsTotallyPositive x) (hy : IsTotallyPositive y) :
    IsTotallyPositive (x * y) := by
  intro w hw
  simpa using mul_pos (hx w hw) (hy w hw)

lemma pow_two {x : K} (hx : x ≠ 0) : IsTotallyPositive (x ^ 2) := by
  intro w hw
  have hxw : InfinitePlace.embedding_of_isReal hw x ≠ 0 := by
    exact (map_ne_zero (InfinitePlace.embedding_of_isReal hw)).mpr hx
  simpa [pow_two] using sq_pos_of_ne_zero hxw

lemma inv {x : K} (hx : IsTotallyPositive x) : IsTotallyPositive x⁻¹ := by
  intro w hw
  simpa using inv_pos.mpr (hx w hw)

lemma div {x y : K} (hx : IsTotallyPositive x) (hy : IsTotallyPositive y) :
    IsTotallyPositive (x / y) := by
  simpa [div_eq_mul_inv] using hx.mul hy.inv

end IsTotallyPositive

lemma isTotallyPositive_unit_square (u : Kˣ) : IsTotallyPositive ((u : K) ^ 2) :=
  IsTotallyPositive.pow_two u.ne_zero

noncomputable section

open scoped QuadraticAlgebra

namespace Issue56Examples

abbrev Qsqrt2 := QuadraticAlgebra ℚ (2 : ℚ) 0

lemma qsqrt2_no_rat_root : ∀ r : ℚ, r ^ 2 ≠ (2 : ℚ) + 0 * r := by
  intro r hr
  norm_num at hr
  have hreal : ((r : ℝ) ^ 2) = (2 : ℝ) := by exact_mod_cast hr
  have hsq : ((r : ℝ) ^ 2) = (Real.sqrt 2) ^ 2 := by
    rw [hreal, Real.sq_sqrt (by norm_num)]
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
  · exact irrational_sqrt_two ⟨r, h⟩
  · exact irrational_sqrt_two ⟨-r, by simp [h]⟩

local instance : Fact (∀ r : ℚ, r ^ 2 ≠ (2 : ℚ) + 0 * r) :=
  ⟨qsqrt2_no_rat_root⟩

abbrev sqrtTwo : Qsqrt2 :=
  QuadraticAlgebra.omega

abbrev threePlusTwoSqrtTwo : Qsqrt2 :=
  ⟨3, 2⟩

lemma one_add_sqrtTwo_sq : (1 + sqrtTwo) ^ 2 = threePlusTwoSqrtTwo := by
  ext <;> norm_num [sqrtTwo, threePlusTwoSqrtTwo, pow_two]

lemma threePlusTwoSqrtTwo_eq_one_add_sq :
    threePlusTwoSqrtTwo = (1 + sqrtTwo) ^ 2 :=
  one_add_sqrtTwo_sq.symm

example : IsTotallyPositive threePlusTwoSqrtTwo := by
  rw [threePlusTwoSqrtTwo_eq_one_add_sq]
  exact IsTotallyPositive.pow_two (by
    intro h
    have him := congrArg QuadraticAlgebra.im h
    norm_num [sqrtTwo] at him)

noncomputable def negSqrt2AlgHom : Qsqrt2 →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨-Real.sqrt 2, by
    rw [neg_mul_neg, ← pow_two (Real.sqrt 2), Real.sq_sqrt (by norm_num)]
    norm_num⟩

lemma negSqrt2AlgHom_sqrtTwo : negSqrt2AlgHom sqrtTwo = -Real.sqrt 2 := by
  dsimp [negSqrt2AlgHom, sqrtTwo, QuadraticAlgebra.lift]
  change (QuadraticAlgebra.omega : Qsqrt2).re • (1 : ℝ) +
      (QuadraticAlgebra.omega : Qsqrt2).im • (-Real.sqrt 2) = -Real.sqrt 2
  norm_num

noncomputable def negSqrt2Embedding : Qsqrt2 →+* ℂ :=
  Complex.ofRealHom.comp negSqrt2AlgHom.toRingHom

lemma negSqrt2Embedding_isReal : ComplexEmbedding.IsReal negSqrt2Embedding := by
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp [negSqrt2Embedding]

lemma neg_place_sqrtTwo :
    let w := InfinitePlace.mk negSqrt2Embedding
    let hw : w.IsReal := InfinitePlace.isReal_mk_iff.mpr negSqrt2Embedding_isReal
    InfinitePlace.embedding_of_isReal hw sqrtTwo = -Real.sqrt 2 := by
  dsimp only
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_mk_eq_of_isReal negSqrt2Embedding_isReal]
  simp [negSqrt2Embedding, negSqrt2AlgHom_sqrtTwo]

example : ¬ IsTotallyPositive sqrtTwo := by
  intro h
  let w := InfinitePlace.mk negSqrt2Embedding
  let hw : w.IsReal := InfinitePlace.isReal_mk_iff.mpr negSqrt2Embedding_isReal
  have hω : InfinitePlace.embedding_of_isReal hw sqrtTwo = -Real.sqrt 2 := neg_place_sqrtTwo
  have hsqrt_pos : 0 < Real.sqrt 2 := by positivity
  have hnot : ¬ 0 < InfinitePlace.embedding_of_isReal hw sqrtTwo := by
    rw [hω]
    linarith
  exact hnot (h w hw)

end Issue56Examples

end

end NumberField
