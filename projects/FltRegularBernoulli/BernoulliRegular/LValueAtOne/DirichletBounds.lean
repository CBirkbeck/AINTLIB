module

public import Common.Analysis.DirichletBounds
public import BernoulliRegular.LValueAtOne.Defs

/-!
# Dirichlet-test bounds for `LValueAtOne`

These generic summation-by-parts estimates are shared by the cosine and sine
boundary-value packages.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Topology

namespace BernoulliRegular

/-- Summation by parts bound for a weighted series with bounded partial sums. -/
lemma norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℕ → ℝ} {z : ℕ → E} {B : ℝ}
    (ha : Antitone a) (ha_nonneg : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, a i • z i‖ ≤ B * a 0 :=
  _root_.norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded
    ha ha_nonneg hbound n

/-- Partial sums over a shifted sequence are controlled by the same bound up to a factor `2`. -/
lemma norm_sum_range_shift_le_of_bounded
    {E : Type*} [NormedAddCommGroup E]
    {z : ℕ → E} {B : ℝ}
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (m n : ℕ) :
    ‖∑ i ∈ Finset.range n, z (m + i)‖ ≤ 2 * B :=
  _root_.norm_sum_range_shift_le_of_bounded hbound m n

/-- Tail sums of a weighted series inherit the same summation-by-parts bound. -/
lemma norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℕ → ℝ} {z : ℕ → E} {B : ℝ}
    (ha : Antitone a) (ha_nonneg : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (m n : ℕ) :
    ‖∑ i ∈ Finset.range n, a (m + i) • z (m + i)‖ ≤ (2 * B) * a m :=
  _root_.norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded
    ha ha_nonneg hbound m n

end BernoulliRegular
