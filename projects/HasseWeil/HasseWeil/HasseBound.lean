import HasseWeil.DegreeQuadraticForm
import HasseWeil.Frobenius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Hasse Bound for Elliptic Curves

We prove Hasse's theorem: for an elliptic curve `E` over a finite field `𝔽_q`,

  `|#E(𝔽_q) - q - 1| ≤ 2√q`.

The proof decomposes into:
1. **Algebraic input**: The degree map on End(E) is a positive semidefinite (nonnegative) quadratic
   form (Silverman III.6.3), the Frobenius has degree `q` (III.4.6), and
   `#E(𝔽_q) = q + 1 - t` where `t = tr(π)` (V.1.1).
2. **Pure algebra** (fully proved): From the non-negativity of the quadratic form,
   we deduce `t² ≤ 4q`, hence `|t| ≤ 2√q`.

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
  push_neg at habs
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

/-! ### The Hasse bound

**[2026-05-28 — placeholder removal, Strategy B].** The theorems
`traceOfFrobenius_sq_le`, `hasse_bound`, and `hasse_bound_sq` previously lived
here. They were built on the placeholder `oneSubFrobeniusIsog` (whose
`pullback := AlgHom.id` forces `degree = 1`, hence `traceOfFrobenius = q` and
the false `q² ≤ 4q`), so they asserted universally-false statements
(`#E(F_q) = 1`, `q² ≤ 4q` for `q ≥ 5`). They have been **deleted**.

The live, honest Hasse-bound API is
`HasseWeil.WeilPairing.hasse_bound_unconditional`
(`HasseWeil/WeilPairing/HasseBound.lean`), PROVEN axiom-clean; it routes through
the genuine `isogOneSub_negFrobenius` and the Weil-pairing assembly
(`WeilPairing/HasseAssembly.lean`, with `hasse_bound_of_full_qf_nonneg_witnesses`
/ `traceOfFrobenius_sq_le_of_qf_nonneg` in `Hasse/QuadraticForm.lean`).
(The intermediate `hasse_bound_skeleton` milestone and its sorried skeleton chain
were retired 2026-06-11.) The pure-algebra discriminant lemmas above
(`trace_sq_le_four_mul_deg`, `abs_le_two_sqrt_of_sq_le`) are correct and are
consumed by that live chain. -/

end HasseWeil
