import BernoulliRegular.FLT37.LehmerVandiver.CaseI.Main
import BernoulliRegular.FLT37.Hilbert90

/-!
# LV010-A: caseI ideal-principalization under `¬ p ∣ h⁺`

Drop-in replacement for flt-regular's `is_principal_aux` (which uses
`p.Coprime |Cl(K)|` = `IsRegularPrime p`). Under `¬ p ∣ h⁺(K)` plus a
class-equality input `[σ𝔞] = [𝔞]`, the case-I factor ideal `𝔞` is
principal in `𝓞 K`.

**Mathematical content.** From `(α) = 𝔞^p`, the class `[𝔞]` is
`p`-torsion. The class equality `[σ𝔞] = [𝔞]` puts `[𝔞]·[σ𝔞]^{-1} = 1`,
combined with `[𝔞]^p = 1` gives `[𝔞]^{p+1} = [𝔞]·[σ𝔞]^{-1}·[σ𝔞]^{p+1} =
1·[σ𝔞]^{p+1}`. Working through the (p+1)/2 trick and the
`relNorm`-descent of `𝔞·σ𝔞`, the existing engine
`isPrincipal_of_pow_principal_of_class_eq_complexConj_of_VC` (in
`Hilbert90.lean`) discharges principality from the K⁺-side.

This lemma is the LV-route's drop-in for `is_principal_aux`,
factoring out the regularity-vs-VC distinction. Combined with
LV010-B (`[σI] = [I]` discharge from primary witness or eigenspace) and
LV010-C (`is_principal` reassembly), this completes the case-I proof.

## References

* Diekmann (2023), §4 (Vandiver descent).
* Project file `BernoulliRegular/FLT37/Hilbert90.lean` line 375
  (`isPrincipal_of_pow_principal_of_class_eq_complexConj_of_VC`).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension Ideal

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

set_option backward.isDefEq.respectTransparency false in
omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`¬ p ∣ h⁺` is the same as `p.Coprime |Cl(K⁺)|`.** Direct via
`Nat.Prime.coprime_iff_not_dvd`. The cardinality unfolds to `hPlus K`. -/
theorem coprime_card_classGroup_Kplus_of_not_dvd_hPlus (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K) :
    p.Coprime (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))) :=
  (Nat.Prime.coprime_iff_not_dvd hp.out).mpr h_not_dvd

set_option backward.isDefEq.respectTransparency false in
/-- **LV010-A: case-I ideal principalization under `¬ p ∣ h⁺`.**
Drop-in replacement for `isPrincipal_of_isPrincipal_pow_of_coprime`
(flt-regular's regularity-based principalization).

Given the case-I factor identity `Ideal.span {α} = 𝔞^p` for `α ∈ 𝓞 K`,
plus `¬ p ∣ h⁺(K)` and the class equality `[σ𝔞] = [𝔞]` in
`ClassGroup (𝓞 K)`, the ideal `𝔞` is principal in `𝓞 K`.

The class equality `h_class_eq` is the LV010-B input — it captures
Vandiver's descent that `[𝔞]·[σ𝔞]` lands in the σ-fixed part of
`Cl(K)`. -/
theorem caseI_ideal_isPrincipal_of_not_dvd_hPlus
    (hp_odd : p ≠ 2)
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    {α : 𝓞 K} (hα : α ≠ 0)
    {𝔞 : Ideal (𝓞 K)} (h𝔞_nz : 𝔞 ≠ ⊥)
    (h : Ideal.span ({α} : Set (𝓞 K)) = 𝔞 ^ p)
    (h_class_eq :
      ClassGroup.mk0
          (⟨𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              ((map_ne_bot_iff_complexConj K 𝔞).mpr h𝔞_nz)⟩
            : nonZeroDivisors (Ideal (𝓞 K))) =
        ClassGroup.mk0
          (⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩
            : nonZeroDivisors (Ideal (𝓞 K)))) :
    𝔞.IsPrincipal :=
  isPrincipal_of_pow_principal_of_class_eq_complexConj_of_VC
    (p := p) (K := K) hp_odd
    (coprime_card_classGroup_Kplus_of_not_dvd_hPlus h_not_dvd) hα h𝔞_nz h h_class_eq

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
