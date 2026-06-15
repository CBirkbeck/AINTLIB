import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummerCaseI
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealBundleViaKellner

/-!
# FLT37 consumer wrapper using the AK chain

## The `CaseIAntiKummerLKUnramified` predicate

The universal "L/K unramified for the σ-anti Kummer extension at every case-I FLT
data" condition is the key remaining residual for the AK chain to fire
unconditionally on FLT37. It encapsulates the per-case-I primarity argument
(via FLT case-I structure + primarity at the prime above p).

Composes `flt37_stage2_via_AK_chain` (the end-to-end Stage2 discharge via the σ-anti
Kummer chain) with `fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseII` to
derive `FermatLastTheoremFor 37` from:
- `h_VC` (¬ 37 ∣ hPlus K),
- `h_LK_unram_per_case` (universal IsUnramified L/K from primarity of α₀ per case-I data),
- `caseII` (CaseIIBridge from Washington 9.4).

The remaining substantive content for the unconditional FLT37 is the universal
primarity argument for `h_LK_unram_per_case` and the Sinnott content for cor8_19
(extraction from VC).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.LehmerVandiver.CaseI

/-- **`CaseIAntiKummerLKUnramified`**: the universal hypothesis "for every case-I
FLT *solution* (a, b, c, ζ, hab) with `a^37 + b^37 = c^37`, the σ-anti Kummer
extension L/K is unramified".

The `heq : a^37 + b^37 = c^37` hypothesis is essential: without it the universal
Prop would be too strong, e.g., for `(a, b, c) = (1, 1, 2)` the antiRadical is
just `ζ` (since `(1+ζ)/(1+ζ⁻¹) = ζ`) and `K(ζ^(1/37)) = ℚ(ζ_{37²})/K` is
ramified at `(1-ζ)`, contradicting any universal IsUnramified claim.

With the FLT equation, case-I primary form `(a+ζb) = I^p` holds (LV008-CTOR-a),
and the AK chain reduces IsUnramified to:
- For primes not above p: automatic from `(α₀) = (I/σI)^p` fractional ideal structure.
- For the prime above p: per-case-I primarity argument (Stage 1 weak primarity +
  refinement to `(ζ-1)^p` strong primarity via AK-5c Wieferich lifting). -/
def CaseIAntiKummerLKUnramified : Prop :=
  ∀ {a b c : ℤ}
    (_heq : a ^ 37 + b ^ 37 = c ^ 37)
    (_hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
    {ζ : 𝓞 (CyclotomicField 37 ℚ)} (_hζ : IsPrimitiveRoot ζ 37)
    (hab : ¬ (a = 0 ∧ b = 0)),
    Algebra.Unramified (𝓞 (CyclotomicField 37 ℚ))
      (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
        (p := 37) (CyclotomicField 37 ℚ)
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
          (CyclotomicField 37 ℚ) a b ζ hab)
        (caseI_antiRadical_ne_zero (K := CyclotomicField 37 ℚ)
          (by decide : (37 : ℕ) ≠ 2) _hcaseI _hζ hab)))

/-- **FLT37 via the AK chain**: composes Stage2 discharge via AK chain with the
existing consumer pipeline. The `h_LK_unram_per_case` hypothesis now requires
the FLT case-I equation `a^37 + b^37 = c^37`, matching the actual scope of the
AK chain (the universal IsUnramified is only sound for FLT-satisfying data). -/
theorem fermatLastTheoremFor_thirtyseven_via_AK_chain
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (h_VC : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (h_LK_unram_per_case : ∀ {a b c : ℤ}
      (_heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0)),
      Algebra.Unramified (𝓞 (CyclotomicField 37 ℚ))
        (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
          (p := 37) (CyclotomicField 37 ℚ)
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab)
          (caseI_antiRadical_ne_zero (K := CyclotomicField 37 ℚ)
            (by decide : (37 : ℕ) ≠ 2) hcaseI hζ hab))))
    (kellner : KellnerProp27_thirtyseven_thirtytwo)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have stage2 : FLT37.LehmerVandiver.CaseI.Stage2KummerRatioK 37 (CyclotomicField 37 ℚ) :=
    flt37_stage2_via_AK_chain (K := CyclotomicField 37 ℚ) (p := 37)
      (by decide : (37 : ℕ) ≠ 2) (by decide : (37 : ℕ) ≠ 3) h_VC
      (fun {_ _ _} heq hcaseI {_} hζ hab => h_LK_unram_per_case heq hcaseI hζ hab)
  exact fermatLastTheoremFor_thirtyseven_of_cor8_19_stage2_caseII cor8_19 stage2 kellner caseII

/-- **`¬ 37 ∣ h⁺` from the Cor 8.19 bridge and the shipped local certificate.**
This is the standard LV005/LV006 composition specialized to FLT37: the concrete
Pollaczek local non-power certificate feeds the `Cor8_19Bridge` to produce
`Vandiver37PlusCoprime`, hence the non-divisibility of the plus class number. -/
theorem not_dvd_hPlus_thirtyseven_of_cor8_19
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32) :
    ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
  FLT37.not_dvd_hPlus_thirtyseven_of_vandiver37PlusCoprime
    (FLT37.vandiver37PlusCoprime_of_bridge cor8_19
      FLT37.flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete)

/-- **Hilbert 94 obstruction for the FLT37 real subfield, from Cor 8.19.**

Once Cor 8.19 gives `37 ∤ h⁺(K_37)`, no unramified cyclic extension of
`K_37⁺` of degree `37` can exist.  This is the endpoint contradiction used by
the real Kummer lift part of Stage 2; the remaining work there is to construct
such an extension from the Kummer radical when the lifted real unit is not a
37-th power. -/
theorem no_h94_extension_thirtyseven_of_cor8_19
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (Lplus : Type) [Field Lplus]
    [Algebra (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)) Lplus]
    [NumberField Lplus]
    [FiniteDimensional (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)) Lplus]
    [IsGalois (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)) Lplus]
    [Algebra.Unramified
      (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))) (𝓞 Lplus)]
    [IsCyclic
      (Lplus ≃ₐ[NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)] Lplus)]
    (hKL : Module.finrank (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))
      Lplus = 37) :
    False :=
  no_h94_extension_of_Kplus_under_VC 37 (CyclotomicField 37 ℚ)
    (by decide : (37 : ℕ) ≠ 2)
    (not_dvd_hPlus_thirtyseven_of_cor8_19 cor8_19) Lplus hKL

/-- **FLT37 via the AK chain from Cor 8.19 alone.**
Compared with `fermatLastTheoremFor_thirtyseven_via_AK_chain`, this form does
not ask callers to provide `¬ 37 ∣ hPlus` separately; it derives that fact from
the Cor 8.19 bridge and the shipped real Pollaczek local certificate. -/
theorem fermatLastTheoremFor_thirtyseven_via_AK_chain_of_cor8_19
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (h_LK_unram_per_case : ∀ {a b c : ℤ}
      (_heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0)),
      Algebra.Unramified (𝓞 (CyclotomicField 37 ℚ))
        (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
          (p := 37) (CyclotomicField 37 ℚ)
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab)
          (caseI_antiRadical_ne_zero (K := CyclotomicField 37 ℚ)
            (by decide : (37 : ℕ) ≠ 2) hcaseI hζ hab))))
    (kellner : KellnerProp27_thirtyseven_thirtytwo)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_via_AK_chain cor8_19
    (not_dvd_hPlus_thirtyseven_of_cor8_19 cor8_19)
    h_LK_unram_per_case kellner caseII

/-- **FLT37 via the AK chain from Cor 8.19, with the second-order Bernoulli
input explicit.**

This is the Bernoulli-clean version of
`fermatLastTheoremFor_thirtyseven_via_AK_chain_of_cor8_19`: the caller supplies
`NoSecondOrderIrregularPair 37 32`, so this theorem does not depend on the
repository's current `B_1184` placeholder. -/
theorem fermatLastTheoremFor_thirtyseven_via_AK_chain_of_cor8_19_and_noSecondOrder
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (h_LK_unram_per_case : ∀ {a b c : ℤ}
      (_heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0)),
      Algebra.Unramified (𝓞 (CyclotomicField 37 ℚ))
        (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
          (p := 37) (CyclotomicField 37 ℚ)
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab)
          (caseI_antiRadical_ne_zero (K := CyclotomicField 37 ℚ)
            (by decide : (37 : ℕ) ≠ 2) hcaseI hζ hab))))
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h_VC : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    not_dvd_hPlus_thirtyseven_of_cor8_19 cor8_19
  have stage2 : FLT37.LehmerVandiver.CaseI.Stage2KummerRatioK 37
      (CyclotomicField 37 ℚ) :=
    flt37_stage2_via_AK_chain (K := CyclotomicField 37 ℚ) (p := 37)
      (by decide : (37 : ℕ) ≠ 2) (by decide : (37 : ℕ) ≠ 3) h_VC
      (fun {_ _ _} heq hcaseI {_} hζ hab => h_LK_unram_per_case heq hcaseI hζ hab)
  exact fermatLastTheoremFor_thirtyseven_of_stage2
    cor8_19 stage2 noSecondOrderIrregular caseII

/-- **FLT37 via the AK chain (from VC)**: simplified form taking only VC.
Derives cor8_19 from VC via `cor8_19Bridge_of_not_dvd_hPlus`. -/
theorem fermatLastTheoremFor_thirtyseven_via_AK_chain_of_VC
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_VC : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (h_LK_unram_per_case : ∀ {a b c : ℤ}
      (_heq : a ^ 37 + b ^ 37 = c ^ 37)
      (hcaseI : ¬ (37 : ℤ) ∣ a * b * c)
      {ζ : 𝓞 (CyclotomicField 37 ℚ)} (hζ : IsPrimitiveRoot ζ 37)
      (hab : ¬ (a = 0 ∧ b = 0)),
      Algebra.Unramified (𝓞 (CyclotomicField 37 ℚ))
        (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
          (p := 37) (CyclotomicField 37 ℚ)
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            (CyclotomicField 37 ℚ) a b ζ hab)
          (caseI_antiRadical_ne_zero (K := CyclotomicField 37 ℚ)
            (by decide : (37 : ℕ) ≠ 2) hcaseI hζ hab))))
    (kellner : KellnerProp27_thirtyseven_thirtytwo)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact fermatLastTheoremFor_thirtyseven_via_AK_chain
    (cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ) h_VC)
    h_VC h_LK_unram_per_case kellner caseII

/-- **FLT37 via the AK chain with named residual**: cleanest API form using the
`CaseIAntiKummerLKUnramified` predicate as the single substantive hypothesis. -/
theorem fermatLastTheoremFor_thirtyseven_via_AK_chain_with_named_residual
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_VC : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (h_LK_unram : CaseIAntiKummerLKUnramified)
    (kellner : KellnerProp27_thirtyseven_thirtytwo)
    (caseII : CaseIIBridge 37 (CyclotomicField 37 ℚ) 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_via_AK_chain_of_VC h_VC
    (fun {_ _ _} heq hcaseI {_} hζ hab => h_LK_unram heq hcaseI hζ hab) kellner caseII

end BernoulliRegular.FLT37.LehmerVandiver.CaseI

end
