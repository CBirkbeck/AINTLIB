import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealBundle
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.PthPowerLift
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.PollaczekFamilyDescent

/-!
# T-PIVOT-3: Certificate audit — σ-symmetric Pollaczek targeting

Audit of the existing `realLocalCert` chain (LV001 → LV004g → LV004g-* →
double-squared bridge → ZMod ℓ residue → `flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete`)
against the reviewer's Caution 2 (2026-05-06): the certificate must be for
the σ-symmetric form `pollaczekUnitPlus = pollaczekUnit · σ(pollaczekUnit)`,
not the bare `pollaczekUnit`.

## Audit conclusion

✓ **PASSED.** The existing chain is structurally σ-symmetric from the
start. The key construction
`zeta_pow_sub_one_double_prod_eq_pollaczekUnitPlus_pow_four`
(in `RealClosure.lean`) builds the bridge directly with
`pollaczekUnitPlus^4` on the RHS by multiplying the bare squared LV004g-1
bridge by its σ-applied version (in `𝓞 K` via
`ringOfIntegersComplexConj K`). There is no implicit "bare ⟹ σ-symmetric"
transfer — the chain is σ-symmetric by construction. The certificate
`flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete` therefore
targets `pollaczekUnitPlus` natively.

The lift from "mod 𝔩 not a p-th power" to "global ∀α, ≠ α^p" is the
existing `not_isPthPower_unit_of_not_isPthPowerModPrime` (in
`PthPowerLift.lean`), which composes with the realLocalCert to give
the global form consumed by `T-PIVOT-1`'s `pollaczekUnitComponent`
field.

## Convenience theorem

`flt37_realLocalCert_global` packages the audit's positive outcome:
the existing certificate, lifted to the global form, is a witness for the
hypothesis side of `Cor8_19Bridge.not_dvd_hPlus_of_not_isPthPower` and
equivalently of `T-PIVOT-1`'s `pollaczekUnitComponent` input.

`flt37_pollaczekUnitPlusKplus_not_isPthPower` transfers that obstruction
across the proven K⁺ algebra-map identity for the canonical Pollaczek
preimage. This gives the exact contradiction target for any future
Thaine/Sinnott theorem proving that the K⁺ preimage is a 37th power under
`37 ∣ h⁺`.

## References

* Reviewer reply, 2026-05-06, Caution 2.
* `BernoulliRegular.FLT37.flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete`
  (the concrete realLocalCert, σ-symmetric by construction).
* `BernoulliRegular.not_isPthPower_unit_of_not_isPthPowerModPrime` (the
  local-to-global lift).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

/-- **T-PIVOT-3 audit confirmation**: the existing `realLocalCert`
chain, lifted to the global form via
`not_isPthPower_unit_of_not_isPthPowerModPrime`, gives:

  `∀ α : (𝓞 K)ˣ, pollaczekUnitPlus ≠ α^p`

for `(p, K, i) = (37, ℚ(ζ_37), 32)`. This is exactly the hypothesis form
required by `Cor8_19Bridge.not_dvd_hPlus_of_not_isPthPower` and by
`T-PIVOT-1`'s `pollaczekUnitComponent`. -/
theorem flt37_realLocalCert_global
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∀ α : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      ((FLT37.pollaczekUnitPlus 37 (CyclotomicField 37 ℚ) 32 :
          (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) ≠
        ((α : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 :=
  not_isPthPower_unit_of_not_isPthPowerModPrime
    flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete

/-- **K⁺ Pollaczek preimage is not a 37-th power.**

The concrete real local certificate already proves that the K-side
`pollaczekUnitPlus 37 K 32` is not a 37-th power in `(𝓞 K)ˣ`. The proven
identity
`algebraMapPollaczekUnitPlusKplus_eq` identifies the image of the canonical
K⁺ preimage with that K-side unit. Therefore a 37-th root in K⁺ would map
to a 37-th root in K, contradicting the certificate. -/
theorem flt37_pollaczekUnitPlusKplus_not_isPthPower
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∀ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
      β ^ 37 ≠
        Sinnott.pollaczekUnitPlusKplus 37 (CyclotomicField 37 ℚ) 32
          (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37) := by
  intro β hβ
  let K := CyclotomicField 37 ℚ
  let Kplus := NumberField.maximalRealSubfield K
  let f : 𝓞 Kplus →+* 𝓞 K := algebraMap (𝓞 Kplus) (𝓞 K)
  let α : (𝓞 K)ˣ := Units.map f β
  have h_map_pow :
      f (((β ^ 37 :
          (𝓞 Kplus)ˣ) : 𝓞 Kplus)) =
        (((α : (𝓞 K)ˣ) : 𝓞 K) ^ 37) := by
    simp [α, f]
  have h_map_eq :
      f ((Sinnott.pollaczekUnitPlusKplus 37 K 32
          (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37) :
          (𝓞 Kplus)ˣ) : 𝓞 Kplus) =
        ((pollaczekUnitPlus 37 K 32 : (𝓞 K)ˣ) : 𝓞 K) :=
    Sinnott.algebraMapPollaczekUnitPlusKplus_eq 37 K 32
      (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37)
  have h_root :
      ((pollaczekUnitPlus 37 K 32 : (𝓞 K)ˣ) : 𝓞 K) =
        (((α : (𝓞 K)ˣ) : 𝓞 K) ^ 37) := by
    rw [← h_map_eq, ← h_map_pow]
    exact (congrArg (fun u : (𝓞 Kplus)ˣ =>
      f ((u : (𝓞 Kplus)ˣ) : 𝓞 Kplus)) hβ).symm
  exact flt37_realLocalCert_global α h_root

/-- **No K⁺ 37-th root exists for the canonical Pollaczek preimage.** -/
theorem flt37_pollaczekUnitPlusKplus_not_exists_pthPower
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ¬ ∃ β : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ,
      β ^ 37 =
        Sinnott.pollaczekUnitPlusKplus 37 (CyclotomicField 37 ℚ) 32
          (by decide : (37 : ℕ) ≠ 2) (by decide : 3 ≤ 37) := by
  rintro ⟨β, hβ⟩
  exact flt37_pollaczekUnitPlusKplus_not_isPthPower β hβ

end FLT37

end BernoulliRegular

end
