import HasseWeil.DegreeQuadraticForm
import HasseWeil.Frobenius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Discriminant bounds for the trace of Frobenius

The pure-algebra core underlying the Hasse bound: from the non-negativity of the binary
quadratic form `q · r² - t · r · s + s²` (the degree form on `End E`, Silverman III.6.3) we
deduce `t² ≤ 4q`, and hence `|t| ≤ 2√q`.

These two lemmas are the algebraic input to the Hasse bound proper,
`HasseWeil.WeilPairing.hasse_bound_unconditional` (in `HasseWeil/WeilPairing/HasseBound.lean`,
proven axiom-clean), which supplies the geometric facts (`deg π = q`, `#E(𝔽_q) = q + 1 - t`) and
the non-negativity of the quadratic form.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, Theorem V.1.1
* Sutherland, *18.783 Elliptic Curves*, Lecture 7, Theorem 7.17
-/

open WeierstrassCurve Real

namespace HasseWeil

/-! ### Pure algebra: the discriminant bound -/

/-- If a binary quadratic form `q · r² - t · r · s + s²` is non-negative for all
    integers `r, s`, then `t² ≤ 4q`. -/
theorem trace_sq_le_four_mul_deg (q : ℕ) (t : ℤ) (hq : 0 < q)
    (h : ∀ r s : ℤ, 0 ≤ (q : ℤ) * r ^ 2 - t * r * s + s ^ 2) :
    t ^ 2 ≤ 4 * (q : ℤ) := by
  by_contra habs
  push Not at habs
  have h₁ := h t (2 * (q : ℤ))
  have hq' : (0 : ℤ) < q := Int.natCast_pos.mpr hq
  nlinarith [sq_nonneg t, sq_nonneg (q : ℤ), mul_self_nonneg (q : ℤ)]

/-- The integer absolute value bound: if `t² ≤ 4q`, then `|t| ≤ 2√q`. -/
theorem abs_le_two_sqrt_of_sq_le (q : ℕ) (t : ℤ)
    (ht : t ^ 2 ≤ 4 * (q : ℤ)) :
    |(t : ℝ)| ≤ 2 * sqrt (q : ℝ) := by
  have hq_nn : (0 : ℝ) ≤ q := Nat.cast_nonneg' q
  have hsq_nn : (0 : ℝ) ≤ 2 * sqrt q := by positivity
  have ht_real : (t : ℝ) ^ 2 ≤ 4 * (q : ℝ) := by exact_mod_cast ht
  have key : (t : ℝ) ^ 2 ≤ (2 * sqrt (q : ℝ)) ^ 2 := by
    rw [mul_pow, sq_sqrt hq_nn]; linarith
  rw [abs_le]
  exact abs_le_of_sq_le_sq' key hsq_nn

end HasseWeil
