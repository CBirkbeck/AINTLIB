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
  have hlt : (p - 1) * padicValNat p n.factorial < n :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega)
  -- In ℕ, strict `<` gives `≤ n - 1`; cast to ℝ and divide by `(p - 1) > 0`.
  have hle_nat : (p - 1) * padicValNat p n.factorial ≤ n - 1 := by omega
  rw [le_div_iff₀ hp1_posR, mul_comm]
  calc ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ)
      = ((p - 1 : ℕ) : ℝ) * (padicValNat p n.factorial : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
    _ ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hle_nat
    _ = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; push_cast; ring

/-- Coarser bound without the hypothesis `1 ≤ n`: `v_p(n!) ≤ n / (p - 1)`. -/
theorem padicValNat_factorial_div_le (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) / (p - 1) := by
  have hp1_posR : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
    linarith
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    simp
  · refine (padicValNat_factorial_le p (n := n) hn1).trans ?_
    gcongr
    linarith

end HasseWeil.FormalGroup
