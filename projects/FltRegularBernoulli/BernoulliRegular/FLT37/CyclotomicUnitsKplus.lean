module

public import BernoulliRegular.FLT37.Hilbert90
public import BernoulliRegular.FLT37.PrimaryUnits

/-!
# K⁺-relative integer norm of cyclotomic units

This file packages the identification

  `Algebra.intNorm (𝓞 K⁺) (𝓞 K) (cyclotomicUnit p K k) = realCyclotomicUnitPlus p K k`

linking the K-side `cyclotomicUnit` and the K⁺-side `realCyclotomicUnitPlus`
through the relative integer norm. Both the LHS and RHS have the same image
under `algebraMap (𝓞 K⁺) (𝓞 K)` (the `σ`-fixed product
`cyclotomicUnit · σ(cyclotomicUnit) = realCyclotomicUnit`), so the
identification follows by injectivity of `algebraMap`.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The K⁺-relative integer norm of a cyclotomic unit equals the descended
real cyclotomic combination. -/
theorem intNorm_cyclotomicUnit_eq_realCyclotomicUnitPlus [IsCMField K] (k : ℕ) :
    Algebra.intNorm (𝓞 K⁺) (𝓞 K) (cyclotomicUnit p K k) =
      realCyclotomicUnitPlus p K k := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K⁺) (𝓞 K)
  rw [algebraMap_intNorm_eq_self_mul_complexConj, algebraMap_realCyclotomicUnitPlus,
    realCyclotomicUnit]

/-- **Absolute integer norm of `realCyclotomicUnitPlus` is `1`.** Combining
the intNorm identification with `cyclotomicUnit_norm_int = 1` and the
norm-tower formula `intNorm_intNorm`. -/
theorem realCyclotomicUnitPlus_norm_int_eq_one [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_odd : p ≠ 2) :
    Algebra.norm ℤ (realCyclotomicUnitPlus p K k) = (1 : ℤ) := by
  -- intNorm ℤ (𝓞 K⁺) (intNorm (𝓞 K⁺) (𝓞 K) cyclotomicUnit) = intNorm ℤ (𝓞 K) cyclotomicUnit
  rw [← Algebra.intNorm_eq_norm, ← intNorm_cyclotomicUnit_eq_realCyclotomicUnitPlus,
    Algebra.intNorm_intNorm,
    Algebra.intNorm_eq_norm, cyclotomicUnit_norm_int p K k hk hp_odd]

end FLT37

end BernoulliRegular

end
