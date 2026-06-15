/-
Copyright (c) 2026 Bernoulli-Regular project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernoulli-Regular project contributors
-/
import BernoulliRegular.BernoulliFast.Tactic

/-!
# Tests for the `Cbv.bernoulliFrac`-backed `bernoulli_decide`
-/

namespace BernoulliRegular.BernoulliFast

-- Full rational value in ℚ
example : (bernoulli 12 : ℚ) = -691 / 2730 := by bernoulli_decide
example : (bernoulli 34 : ℚ) = 2577687858367 / 6 := by bernoulli_decide

-- Numerator goals
example : (bernoulli 12).num = -691 := by bernoulli_decide
example : (bernoulli 34).num = 2577687858367 := by bernoulli_decide
example : (bernoulli 12).den = 2730 := by bernoulli_decide

-- Divisibility goals
example : (691 : ℤ) ∣ (bernoulli 12).num := by bernoulli_decide
example : ¬ (5 : ℤ) ∣ (bernoulli 32).num := by bernoulli_decide

end BernoulliRegular.BernoulliFast
