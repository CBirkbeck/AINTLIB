import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.KummerLift.Bridge
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.PthPowerLift
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Symmetrisation
import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.FLT37Closure
import BernoulliRegular.FLT37.Final

/-!
# LV005 main: `¬ IsPthPowerModPrime pollaczekUnitPlus ⇒ ¬ p ∣ hPlus`

LV005e — final assembly chaining LV005a (p-th-power lift) with the
Cor 8.19 bridge `Cor8_19Bridge` (real form, LV005c).

The chain:
1. `¬ IsPthPowerModPrime pollaczekUnitPlus` (lifted from LV004g via the
   real-cert bridge).
2. LV005a: `¬ IsPthPowerModPrime → ¬ ∃ α : (𝓞 K)ˣ, pollaczekUnitPlus = α^p`.
3. Cor 8.19 bridge contrapositive: `¬ IsPthPower → ¬ p ∣ hPlus K`.

This file packages the chain as a parametric theorem; LV011 will
instantiate it with the FLT37 bundle.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), Corollary 8.19 (p. 158).
-/

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **LV005 main (parametric)**: chain
`¬ IsPthPowerModPrime pollaczekUnitPlus ⟹ ¬ p ∣ hPlus K` via LV005a +
Cor 8.19 bridge.

Takes:
- `B`: `Cor8_19Bridge p K i` (LV005c content, on the real form).
- `𝔩`: a prime ideal.
- `h`: `¬ IsPthPowerModPrime p 𝔩 (pollaczekUnitPlus p K i)` — the
  real-form local certificate (lifted from LV004g via the real-cert
  transfer, which is itself a bundle field).

Concludes `¬ p ∣ hPlus K`. -/
theorem not_dvd_hPlus_of_not_isPthPowerModPrime_pollaczekUnitPlus
    (i : ℕ) (B : Cor8_19Bridge p K i) (𝔩 : Ideal (𝓞 K))
    (h : ¬ IsPthPowerModPrime p 𝔩
      ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K)) :
    ¬ (p : ℕ) ∣ hPlus K := by
  -- LV005a: ¬ IsPthPowerModPrime → ¬ ∃ α : (𝓞 K)ˣ, pollaczekUnitPlus = α^p.
  have h_lift : ∀ α : (𝓞 K)ˣ,
      ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) ≠
        ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p :=
    not_isPthPower_unit_of_not_isPthPowerModPrime h
  -- Apply Cor 8.19 bridge.
  exact B.not_dvd_hPlus_of_not_isPthPower h_lift

/-- **LV006 (FLT37 specialisation, parametric)**: applying LV005's main
theorem to the FLT37 certificate tuple `(p, i, ℓ, t, k) = (37, 32, 149, 2, 4)`
yields `Vandiver37PlusCoprime` as a theorem (parametric on the Cor 8.19
bridge AND on a real-form certificate hypothesis).

The `h_realCert` hypothesis is the real-form local certificate
`¬ IsPthPowerModPrime 37 𝔩 (pollaczekUnitPlus 37 K_37 32)`, to be
provided either by:
- recomputing the LV004g `decide`-based residue check on the real form,
- or transferring the bare-form certificate (LV004g) via an explicit
  bare-to-real lift lemma.

Both options are tractable and shipped separately as bundle fields. -/
theorem FLT37.vandiver37PlusCoprime_of_bridge
    (B : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (h_realCert : ¬ IsPthPowerModPrime 37
      (FLT37.lehmerVandiverPrime 37 149 4
        (by decide : (149 : ℕ) = 4 * 37 + 1)
        (by decide : (2 : ℕ).Coprime 149)
        (by decide : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1))
      ((FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
        (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ))) :
    FLT37.Vandiver37PlusCoprime := by
  rw [FLT37.vandiver37PlusCoprime_iff_not_dvd_hPlus]
  exact not_dvd_hPlus_of_not_isPthPowerModPrime_pollaczekUnitPlus
    (p := 37) (CyclotomicField 37 ℚ) 32 B _ h_realCert

end BernoulliRegular

end
