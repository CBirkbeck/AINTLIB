import BernoulliRegular.FLT37.LehmerVandiver.CaseI.IdealFactorisation
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.IsPrincipalUnderHPlus
import BernoulliRegular.FLT37.CaseI

/-!
# LV010-C: caseI `is_principal` analogue under `¬ p ∣ h⁺`

Drop-in replacement for flt-regular's `is_principal` (`FltRegular.CaseI.
Statement` line 165), but using `¬ p ∣ h⁺(K)` plus a class-equality
input instead of `IsRegularPrime p`.

The class-equality input (Vandiver's `[σI] = [I]`) remains an explicit
parameter — Vandiver's primary-witness argument (Washington 9.3)
discharges it but is the deepest piece of LV010, deferred to a
follow-up. This file's role is to wire the structural plumbing so that
once the class equality is shipped, the case-I `is_principal` follows
immediately.

## References

* flt-regular's `FltRegular.is_principal` (line 165), regularity-based.
* Vandiver 1934 / Washington 9.3 for the deep class-equality input.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension Ideal Polynomial
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

set_option backward.isDefEq.respectTransparency false in
/-- **LV010-C: caseI `is_principal` under `¬ p ∣ h⁺` + class equality.**
Mirror of flt-regular's `is_principal` but with `IsRegularPrime` replaced
by `¬ p ∣ h⁺` and a class-equality input.

Given:
- FLT case I hypotheses on `(a, b, c, p, ζ)`
- `5 ≤ p`, `p ≠ 2`
- `¬ p ∣ h⁺(K)`
- A factor-nonvanishing hypothesis (cyclotomic-side technicality)
- A class-equality input `[σI] = [I]` for the ideal `I` from `exists_ideal`

Conclude: `∃ u, α : ↑u * α^p = a + ζ b`. -/
theorem caseI_is_principal_of_not_dvd_hPlus
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hp_odd : p ≠ 2)
    [IsCMField (CyclotomicField p ℚ)]
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus (CyclotomicField p ℚ))
    {a b c : ℤ}
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    (heq : a ^ p + b ^ p = c ^ p)
    {ζ : 𝓞 (CyclotomicField p ℚ)} (hζ : IsPrimitiveRoot ζ p)
    (h_factor_ne : (a : 𝓞 (CyclotomicField p ℚ)) + ζ *
        (b : 𝓞 (CyclotomicField p ℚ)) ≠ 0)
    (h_class_eq_input :
      ∀ {I : Ideal (𝓞 (CyclotomicField p ℚ))} (h𝔞_nz : I ≠ ⊥),
        Ideal.span ({(a : 𝓞 (CyclotomicField p ℚ)) + ζ *
            (b : 𝓞 (CyclotomicField p ℚ))} : Set _) = I ^ p →
        ClassGroup.mk0
            (⟨I.map (ringOfIntegersComplexConj _).toRingEquiv.toRingHom,
              mem_nonZeroDivisors_iff_ne_zero.mpr
                ((map_ne_bot_iff_complexConj _ I).mpr h𝔞_nz)⟩
              : nonZeroDivisors (Ideal (𝓞 (CyclotomicField p ℚ)))) =
          ClassGroup.mk0
            (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩
              : nonZeroDivisors (Ideal (𝓞 (CyclotomicField p ℚ))))) :
    ∃ (u : (𝓞 (CyclotomicField p ℚ))ˣ) (α : 𝓞 (CyclotomicField p ℚ)),
      ↑u * α ^ p = (a : 𝓞 (CyclotomicField p ℚ)) + ζ *
        (b : 𝓞 (CyclotomicField p ℚ)) := by
  -- Step 1: LV008-CTOR-a — get the p-th root ideal I.
  have hζ_mem := hζ.mem_nthRootsFinset hp.1.pos
  obtain ⟨I, hI⟩ := caseI_factor_idealSpan_eq_pow hp5 heq hgcd hcaseI hζ_mem
  -- Step 2: I ≠ ⊥ from the factor being nonzero.
  have hI_ne : I ≠ ⊥ := by
    intro h
    apply h_factor_ne
    have hzero_pow : (⊥ : Ideal (𝓞 (CyclotomicField p ℚ))) ^ p = ⊥ :=
      zero_pow (by omega : p ≠ 0)
    rw [h, hzero_pow] at hI
    rw [Ideal.span_singleton_eq_bot] at hI
    exact hI
  -- Step 3: Apply LV010-A with the class-equality input.
  have hI_principal : I.IsPrincipal :=
    caseI_ideal_isPrincipal_of_not_dvd_hPlus hp_odd h_not_dvd
      h_factor_ne hI_ne hI (h_class_eq_input hI_ne hI)
  -- Step 4: From I principal + I^p = (a + ζ b), extract α and u.
  obtain ⟨α, hα⟩ := hI_principal
  have hα_pow : (Ideal.span ({α} : Set _)) ^ p = Ideal.span ({α ^ p} : Set _) :=
    Ideal.span_singleton_pow α p
  -- Now hI : Ideal.span {a + ζ b} = I^p. From hα : I = Ideal.span {α}, get
  -- I^p = Ideal.span {α^p}. So Ideal.span {a + ζ b} = Ideal.span {α^p}.
  -- Hence ∃ u, u * α^p = a + ζ b (or its associate).
  have hαp_span : Ideal.span ({(a : 𝓞 (CyclotomicField p ℚ)) + ζ *
      (b : 𝓞 (CyclotomicField p ℚ))} : Set _) = Ideal.span ({α ^ p} : Set _) := by
    rw [hI]
    rw [show I = Ideal.span ({α} : Set _) from hα]
    exact hα_pow
  rw [Ideal.span_singleton_eq_span_singleton] at hαp_span
  obtain ⟨u, hu⟩ := hαp_span
  refine ⟨u⁻¹, α, ?_⟩
  -- hu : α^p * u = a + ζ * b (or similar — extract precisely)
  -- u⁻¹ * (a + ζ * b) = u⁻¹ * (α^p * u) = α^p, hence u⁻¹ * (a + ζ * b) = α^p,
  -- so ↑u⁻¹ * α^p = α^p · u⁻¹ ⁻¹ = ... we want ↑u⁻¹ * α^p = a + ζ * b.
  -- Actually we have α^p * u = a + ζ b, so a + ζ b = α^p * u, so ↑u⁻¹ * (a + ζ b) = α^p.
  -- We want ↑u⁻¹ * α^p = a + ζ b. Hmm rearrange:
  -- ↑u⁻¹ * α^p needs to equal a + ζ b. From hu : α^p * u = a + ζ b (Associated.symm form).
  rw [show (u⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ).val * α ^ p =
      α ^ p * (u⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ).val by ring]
  rw [← hu]
  rw [mul_assoc]
  simp [Units.mul_inv]

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
