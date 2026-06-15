module

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
    ‖∑ i ∈ Finset.range n, a i • z i‖ ≤ B * a 0 := by
  have hB : 0 ≤ B := by
    simpa using hbound 0
  rcases n.eq_zero_or_pos with rfl | hn
  · have : 0 ≤ B * a 0 := mul_nonneg hB (ha_nonneg 0)
    simpa using this
  · rw [Finset.sum_range_by_parts (f := a) (g := z) (n := n)]
    have hsum_le :
        ‖∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖ ≤
          B * (a 0 - a (n - 1)) := by
      calc
        ‖∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖
            ≤ ∑ i ∈ Finset.range (n - 1),
                ‖(a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖ := by
              simpa using norm_sum_le (Finset.range (n - 1))
                (fun i => (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j)
        _ ≤ ∑ i ∈ Finset.range (n - 1), B * (a i - a (i + 1)) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hdiff_nonpos : a (i + 1) - a i ≤ 0 := sub_nonpos.mpr (ha (Nat.le_succ i))
              calc
                ‖(a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖
                    = |a (i + 1) - a i| * ‖∑ j ∈ Finset.range (i + 1), z j‖ := by
                        rw [norm_smul, Real.norm_eq_abs]
                _ = (a i - a (i + 1)) * ‖∑ j ∈ Finset.range (i + 1), z j‖ := by
                      rw [abs_of_nonpos hdiff_nonpos]
                      ring
                _ ≤ (a i - a (i + 1)) * B := by
                      gcongr
                      · exact sub_nonneg.mpr (ha (Nat.le_succ i))
                      · exact hbound (i + 1)
                _ = B * (a i - a (i + 1)) := by ring
        _ = B * (a 0 - a (n - 1)) := by
              rw [← Finset.mul_sum]
              have htel' := Finset.sum_range_sub (f := a) (n := n - 1)
              have htel : ∑ i ∈ Finset.range (n - 1), (a i - a (i + 1)) = a 0 - a (n - 1) := by
                calc
                  ∑ i ∈ Finset.range (n - 1), (a i - a (i + 1))
                      = ∑ i ∈ Finset.range (n - 1), -((a (i + 1) - a i)) := by
                          refine Finset.sum_congr rfl fun i hi => by ring
                  _ = -∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) := by
                        rw [Finset.sum_neg_distrib]
                  _ = a 0 - a (n - 1) := by linarith
              rw [htel]
    have hfirst : ‖a (n - 1) • ∑ i ∈ Finset.range n, z i‖ ≤ B * a (n - 1) := by
      calc
        ‖a (n - 1) • ∑ i ∈ Finset.range n, z i‖ = |a (n - 1)| * ‖∑ i ∈ Finset.range n, z i‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ = a (n - 1) * ‖∑ i ∈ Finset.range n, z i‖ := by
          rw [abs_of_nonneg (ha_nonneg _)]
        _ ≤ a (n - 1) * B := by
          gcongr
          · exact ha_nonneg _
          · exact hbound n
        _ = B * a (n - 1) := by ring
    calc
      ‖a (n - 1) • ∑ i ∈ Finset.range n, z i -
          ∑ i ∈ Finset.range (n - 1),
            (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖
          ≤ ‖a (n - 1) • ∑ i ∈ Finset.range n, z i‖ +
              ‖∑ i ∈ Finset.range (n - 1),
                  (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖ := by
              simpa [sub_eq_add_neg] using
                (norm_sub_le (a (n - 1) • ∑ i ∈ Finset.range n, z i)
                  (∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j))
      _ ≤ B * a (n - 1) + B * (a 0 - a (n - 1)) := add_le_add hfirst hsum_le
      _ = B * a 0 := by ring

/-- Partial sums over a shifted sequence are controlled by the same bound up to a factor `2`. -/
lemma norm_sum_range_shift_le_of_bounded
    {E : Type*} [NormedAddCommGroup E]
    {z : ℕ → E} {B : ℝ}
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (m n : ℕ) :
    ‖∑ i ∈ Finset.range n, z (m + i)‖ ≤ 2 * B := by
  have hshift :
      ∑ i ∈ Finset.range n, z (m + i) =
        ∑ i ∈ Finset.range (m + n), z i - ∑ i ∈ Finset.range m, z i := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm, add_left_comm, add_assoc] using (Finset.sum_range_add z m n).symm
  rw [hshift]
  calc
    ‖∑ i ∈ Finset.range (m + n), z i - ∑ i ∈ Finset.range m, z i‖
        ≤ ‖∑ i ∈ Finset.range (m + n), z i‖ + ‖∑ i ∈ Finset.range m, z i‖ := by
            simpa [sub_eq_add_neg] using
              (norm_sub_le (∑ i ∈ Finset.range (m + n), z i) (∑ i ∈ Finset.range m, z i))
    _ ≤ B + B := add_le_add (hbound _) (hbound _)
    _ = 2 * B := by ring

/-- Tail sums of a weighted series inherit the same summation-by-parts bound. -/
lemma norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℕ → ℝ} {z : ℕ → E} {B : ℝ}
    (ha : Antitone a) (ha_nonneg : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (m n : ℕ) :
    ‖∑ i ∈ Finset.range n, a (m + i) • z (m + i)‖ ≤ (2 * B) * a m := by
  simpa [two_mul, add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_comm, mul_left_comm,
    mul_assoc] using
    (norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded
      (a := fun k => a (m + k)) (z := fun k => z (m + k)) (B := 2 * B)
      (ha := fun i j hij => ha (Nat.add_le_add_left hij m))
      (ha_nonneg := fun k => ha_nonneg (m + k))
      (hbound := fun k => norm_sum_range_shift_le_of_bounded (z := z) (B := B) hbound m k) n)

end BernoulliRegular
