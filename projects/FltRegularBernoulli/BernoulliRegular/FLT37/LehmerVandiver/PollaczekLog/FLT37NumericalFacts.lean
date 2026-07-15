/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.FLT37.LehmerVandiver.Certificate

/-!
# FLT37-specific numerical residue facts

For the FLT37 certificate tuple `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`, this file
provides the two numerical facts in `ZMod 149` used to prove the Pollaczek unit is
not a `p`-th power.

## Main results

* `lehmerVandiverProduct_thirtyseven_ne_one`: the FLT37 Lehmer--Vandiver product is
  not one.
* `one_sub_two_pow_four_pow_kS_eq_one`: the denominator power in the FLT37 residue
  calculation is one.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Section 8.3.
-/

@[expose] public section

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

section FLT37NumericalFacts

set_option maxRecDepth 2000

/-- The FLT37 Lehmer--Vandiver product is not one in `ZMod 149`. -/
theorem lehmerVandiverProduct_thirtyseven_ne_one :
    lehmerVandiverProduct 37 32 149 2 4 ≠ 1 := by
  simp only [lehmerVandiverProduct]
  decide

/-- The denominator power in the FLT37 residue calculation is one in `ZMod 149`. -/
theorem one_sub_two_pow_four_pow_kS_eq_one :
    ((1 : ZMod 149) - 2 ^ 4) ^ (4 * 432345) = 1 := by
  have h148 : ((1 : ZMod 149) - 2 ^ 4) ^ 148 = 1 := by decide
  rw [show (4 * 432345 : ℕ) = 148 * 11685 by decide, pow_mul, h148, one_pow]

end FLT37NumericalFacts

end LehmerVandiver

end FLT37

end BernoulliRegular

end
