module

public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Symmetrisation
public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.FLT37Closure

/-!
# Residue certificates for the real Pollaczek unit

This file proves the explicit quartic residue computation for `pollaczekUnitPlus`
at the Lehmer–Vandiver prime over `149` and records that this unit does not belong
to the prime.
-/

@[expose] public section

open NumberField
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

set_option maxRecDepth 2000 in
/-- The quartic power of the explicit residue of `pollaczekUnitPlus` in `ZMod 149`
is nontrivial. -/
theorem flt37_pollaczekUnitPlus_residue_pow_four_ne_one :
    (∏ b ∈ Finset.Ico 1 19,
        ((2 - (16 : ZMod 149)^b - (28 : ZMod 149)^b) * 39 : ZMod 149) ^
          ((4 * b^4) % 148)) ≠ 1 := by
  decide

set_option backward.isDefEq.respectTransparency false in
/-- The real Pollaczek unit does not belong to the Lehmer–Vandiver prime. -/
theorem pollaczekUnitPlus_notMem_lehmerVandiverPrime
    (p ℓ k : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (i : ℕ)
    [IsCMField (CyclotomicField p ℚ)] :
    ((pollaczekUnitPlus p (CyclotomicField p ℚ) i :
        (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ∉
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne := by
  letI : (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).IsPrime :=
    lehmerVandiverPrime_isPrime p ℓ k hℓ ht_coprime ht_ne
  exact Ideal.notMem_of_isUnit _
    (pollaczekUnitPlus p (CyclotomicField p ℚ) i).isUnit

end FLT37

end BernoulliRegular

end
