module

public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Symmetrisation
public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.FLT37Closure

/-!
# Real-form local certificate for FLT37

The σ-symmetrised real Pollaczek unit `pollaczekUnitPlus 37 K 32 =
pollaczekUnit · σ(pollaczekUnit)` is, modulo the LV-prime `𝔩`, the
explicit ZMod 149 element

  `∏_{b=1}^{18} ((2 - 16^b - 28^b) · 107⁻¹)^{b^4}` in `ZMod 149`,

since `ζ ↦ 16` mod `𝔩` and `σ(ζ) = ζ⁻¹ ↦ 28 = 16⁻¹ (mod 149)`. The
quartic power of this element corresponds to `(ℓ-1)/p = 148/37 = 4`,
which is the cyclic-criterion exponent.

The KEY NUMERICAL FACT is that this quartic power is non-trivial — i.e.,
`(pollaczekUnitPlus mod 𝔩)^4 ≠ 1` in ZMod 149. By the cyclic criterion
(LV004f), this means `pollaczekUnitPlus` is NOT a `p`-th power modulo
`𝔩`.

This file ships the numerical fact via kernel `decide` (with
Fermat-reduction of the exponents mod `(ℓ-1) = 148`). The full
connection to `IsPthPowerModPrime` predicate via the residue iso
mirrors LV004g's structure for the bare unit and is a future deliverable.
-/

@[expose] public section

noncomputable section

open NumberField Finset
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

set_option maxRecDepth 4000000
set_option linter.style.setOption false in
set_option maxHeartbeats 4000000

/-- **FLT37 real-form residue cyclic-criterion fact**: the quartic power
of the numerical residue of `pollaczekUnitPlus 37 K 32` in `ZMod 149`
(via `ζ ↦ 16`, `σ(ζ) = 28 = 16⁻¹`) is non-trivial.

Concretely: `∏_{b=1}^{18} ((2 - 16^b - 28^b) · 39)^{4·b^4 mod 148} ≠ 1`
in `ZMod 149`, where `39 = 107⁻¹` (since `(1-ζ)(1-ζ⁻¹) = 2-ζ-ζ⁻¹ = 2-16-28
= -42 ≡ 107` mod 149).

The exponent reduction `mod 148` is by Fermat's little theorem (since
`(ZMod 149)ˣ` has order `148 = 4·37`). Without reduction, the direct
quartic power overflows kernel `decide` due to b=18's exponent
`4·b^4 = 419904`. -/
theorem flt37_pollaczekUnitPlus_residue_pow_four_ne_one :
    (∏ b ∈ Finset.Ico 1 19,
        ((2 - (16 : ZMod 149)^b - (28 : ZMod 149)^b) * 39 : ZMod 149) ^
          ((4 * b^4) % 148)) ≠ 1 := by
  decide

set_option backward.isDefEq.respectTransparency false in
/-- **`pollaczekUnitPlus ∉ lehmerVandiverPrime`** (auxiliary). Since
`pollaczekUnitPlus p K i : (𝓞 K)ˣ` is a unit in `𝓞 K`, its underlying
element is not in any proper ideal — in particular, not in
`lehmerVandiverPrime`. Direct analog of
`pollaczekUnit_notMem_lehmerVandiverPrime`. -/
theorem pollaczekUnitPlus_notMem_lehmerVandiverPrime
    (p ℓ k : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hℓ : ℓ = k * p + 1) {t : ℕ}
    (ht_coprime : t.Coprime ℓ) (ht_ne : (t : ZMod ℓ) ^ k ≠ 1) (i : ℕ)
    [IsCMField (CyclotomicField p ℚ)] :
    ((pollaczekUnitPlus p (CyclotomicField p ℚ) i :
        (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ∉
      lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne := by
  intro hmem
  -- A unit in a ring cannot lie in a proper ideal.
  have hunit : IsUnit ((pollaczekUnitPlus p (CyclotomicField p ℚ) i :
      (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) :=
    ⟨pollaczekUnitPlus p (CyclotomicField p ℚ) i, rfl⟩
  have htop := (lehmerVandiverPrime p ℓ k hℓ ht_coprime ht_ne).eq_top_of_isUnit_mem
    hmem hunit
  have hprime := lehmerVandiverPrime_isPrime p ℓ k hℓ ht_coprime ht_ne
  exact hprime.ne_top htop

end FLT37

end BernoulliRegular

end
