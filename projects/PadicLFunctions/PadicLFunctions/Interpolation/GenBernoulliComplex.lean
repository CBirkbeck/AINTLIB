/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import PadicLFunctions.Interpolation.GenBernoulli
import PadicLFunctions.Interpolation.Sawtooth

/-!
# The complex bridge: `L(χ, −k) = −B_{k+1,χ}/(k+1)`

Quarantined complex-analytic comparison (the §5 analogue of
`ZetaValuesComplex.lean`): mathlib's analytically-continued Dirichlet
L-function agrees at negative integers with the generalised Bernoulli values
used by the `p`-adic statements. mathlib defines
`DirichletCharacter.LFunction χ s = N^{−s} ∑_j χ(j)·hurwitzZeta (j/N) s`, so
this follows from the Bernoulli-polynomial values of the Hurwitz zeta
function: `hurwitzZeta_neg_nat` for `k ≠ 0`, and its `k = 0` extension
`hurwitzZeta_neg_nat_of_mem_Ioo` (`Sawtooth.lean` — the sawtooth boundary
value, where `χ(0) = 0` confines the sum to the open interval). PR candidate.

Source: RJW Lem 5.5 / Lem 5.9 (TeX 1702–1740, 1801–1807), whose proofs go
through the §2 Mellin theory; the value identity itself is classical
(Washington Thm 4.2).
-/

namespace PadicLFunctions

open DirichletCharacter

/-- L5.2.9: values of the (analytically continued) Dirichlet L-function at
negative integers, via generalised Bernoulli numbers. -/
theorem LFunction_neg_nat {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ) :
    LFunction χ (-(k : ℂ)) = -(χ.genBernoulli (k + 1)) / (k + 1) := by
  rcases eq_or_ne N 1 with rfl | hN1
  · -- level one: the Riemann zeta function and `B_k(1) = bernoulli' k`
    have hχ : χ = 1 := DirichletCharacter.level_one χ
    rw [hχ, LFunction_modOne_eq, riemannZeta_neg_nat_eq_bernoulli', genBernoulli_one,
      Algebra.smul_def, mul_one, eq_ratCast (algebraMap ℚ ℂ)]
  · -- level `N > 1`: expand into Hurwitz zeta values; `χ(0) = 0` confines the
    -- sum to the interior of `(0,1)` where the Bernoulli values apply
    haveI : Fact (1 < N) := ⟨by have := NeZero.pos N; omega⟩
    have hχ0 : χ (0 : ZMod N) = 0 := χ.map_nonunit not_isUnit_zero
    have hNR : (0 : ℝ) < (N : ℝ) := mod_cast NeZero.pos N
    have hterm : ∀ j : ZMod N,
        χ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) (-(k : ℂ))
          = χ j * (-1 / (k + 1) *
              ((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval
                (((j.val : ℕ) : ℂ) / (N : ℂ))) := by
      intro j
      rcases eq_or_ne j 0 with rfl | hj
      · rw [hχ0, zero_mul, zero_mul]
      · have hx₀ : (0 : ℝ) < (j.val : ℝ) / (N : ℝ) := by
          have := ZMod.val_pos.mpr hj; positivity
        have hx₁ : ((j.val : ℝ) / (N : ℝ)) < 1 := by
          rw [div_lt_one hNR]
          exact_mod_cast ZMod.val_lt j
        rw [ZMod.toAddCircle_apply, hurwitzZeta_neg_nat_of_mem_Ioo k hx₀ hx₁]
        congr 2
        push_cast
        ring
    simp only [LFunction, ZMod.LFunction]
    rw [neg_neg, Complex.cpow_natCast, Finset.sum_congr rfl fun j _ => hterm j,
      genBernoulli_eq_zmod_sum χ (k + 1),
      show (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) by push_cast; ring, zpow_natCast,
      Finset.mul_sum, Finset.mul_sum]
    have hk1 : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
    rw [eq_div_iff hk1, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp

end PadicLFunctions
