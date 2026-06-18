import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Positivity

/-!
# Silverman IV.6.2: bound on the p-adic valuation of `n!`

This file records the elementary estimate

  `v_p(n!) ≤ (n - 1) / (p - 1)`   for `n ≥ 1`,

which is used in Silverman's treatment of the formal logarithm (Silverman,
"Arithmetic of Elliptic Curves", Chapter IV, Lemma IV.6.2).

Mathlib already provides the sharper Legendre identity
`sub_one_mul_padicValNat_factorial` stating
`(p - 1) * v_p(n!) = n - s_p(n)` where `s_p(n)` is the sum of the base-`p`
digits of `n`, together with the strict inequality
`sub_one_mul_padicValNat_factorial_lt_of_ne_zero`:
`(p - 1) * v_p(n!) < n` for `n ≠ 0`.

We simply repackage these as a bound in `ℝ`, which is the form needed for
convergence arguments about the formal logarithm.

## Main results

* `HasseWeil.FormalGroup.padicValNat_factorial_le` — for `n ≥ 1`,
  `(v_p(n!) : ℝ) ≤ (n - 1) / (p - 1)`.
* `HasseWeil.FormalGroup.padicValNat_factorial_div_le` — a form without the
  `n ≥ 1` hypothesis, bounding by `n / (p - 1)` (slightly looser, but vacuous
  for `n = 0`).
-/

namespace HasseWeil.FormalGroup

open Nat

/-- **Silverman IV.6.2**: For a prime `p` and `n ≥ 1`,
`v_p(n!) ≤ (n - 1) / (p - 1)`.

The classical Legendre formula `v_p(n!) = (n - s_p(n)) / (p - 1)`, where
`s_p(n)` is the sum of the base-`p` digits of `n`, implies this bound since
`s_p(n) ≥ 1` for `n ≥ 1`. We state the inequality in `ℝ` to avoid divisibility
issues. -/
theorem padicValNat_factorial_le (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) :
    (padicValNat p n.factorial : ℝ) ≤ (n - 1 : ℝ) / (p - 1) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp1_posR : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
    linarith
  -- Mathlib strict inequality in ℕ: `(p - 1) * v_p(n!) < n` for `n ≠ 0`.
  have hn_ne : n ≠ 0 := by omega
  have hlt : (p - 1) * padicValNat p n.factorial < n :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn_ne
  -- In ℕ, strict `<` gives `≤ n - 1`.
  have hle_nat : (p - 1) * padicValNat p n.factorial ≤ n - 1 := by omega
  -- Cast to ℝ.
  have hp1_cast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
  have hn1_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; push_cast; ring
  have hle_real :
      ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) - 1 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hle_nat
    push_cast at h
    rw [hp1_cast, hn1_cast] at h
    exact h
  -- Divide by `(p - 1) > 0`.
  rw [le_div_iff₀ hp1_posR, mul_comm]
  exact hle_real

/-- Coarser bound without the hypothesis `1 ≤ n`: `v_p(n!) ≤ n / (p - 1)`. -/
theorem padicValNat_factorial_div_le (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) / (p - 1) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp1_posR : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
    linarith
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    simp
  · have hmain := padicValNat_factorial_le p (n := n) hn1
    have hsub : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
    have hdiv : ((n : ℝ) - 1) / ((p : ℝ) - 1) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
      apply div_le_div_of_nonneg_right hsub hp1_posR.le
    exact le_trans hmain hdiv

end HasseWeil.FormalGroup
