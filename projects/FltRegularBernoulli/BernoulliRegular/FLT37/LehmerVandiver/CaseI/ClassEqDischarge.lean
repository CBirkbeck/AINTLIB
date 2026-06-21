import BernoulliRegular.FLT37.LehmerVandiver.CaseI.IsPrincipalUnderHPlus

/-!
# LV010-D: case-I class-equality discharge predicate

The case-I `is_principal` reduction under `¬ p ∣ h⁺` (LV010-C) requires a
class-equality input `[σI] = [I]` for the case-I factor ideal `I` from
`exists_ideal`. Once Vandiver's Stage 1 + Stage 2 (primary normalization
and Kummer's lemma `α/σα = β^p`) are shipped, this hypothesis is
discharged unconditionally.

This file packages the discharge as a `Prop` so that LV010-D's bridge
ships parametrically: once `CaseIClassEqDischarge p K` is provided,
`CaseIBridge p K` follows, and FLT case I closes for `p`.

## References

* `caseI_is_principal_of_not_dvd_hPlus` (LV010-C).
* Vandiver 1934, Theorem 1.
* Washington, *Introduction to Cyclotomic Fields*, §9.3.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension Ideal

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

/-- **LV010-D class-equality discharge predicate.** Captures Vandiver's
descent: under FLT case-I hypotheses on `(a, b, c, p)`, the case-I
factor ideal `I` (with `(a + ζ b) = I^p`) satisfies `[σI] = [I]` in
`Cl(𝓞 K)`.

Once filled by Stage 1 + Stage 2 (primary normalization + Kummer's
lemma), `CaseIBridge p K` is constructible (via LV010-D). The predicate
is universally quantified over `(a, b, c)` and `ζ` so that it can be
instantiated at any case-I scenario. -/
def CaseIClassEqDischarge (p : ℕ) [Fact p.Prime] (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] :
    Prop :=
  ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
    ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
    ∀ {ζ : 𝓞 K}, IsPrimitiveRoot ζ p →
    ∀ {I : Ideal (𝓞 K)} (hI_nz : I ≠ ⊥),
      Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p →
      ClassGroup.mk0
          (⟨I.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              ((map_ne_bot_iff_complexConj K I).mpr hI_nz)⟩
            : nonZeroDivisors (Ideal (𝓞 K))) =
        ClassGroup.mk0
          (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_nz⟩
            : nonZeroDivisors (Ideal (𝓞 K)))

/-- **Regular-prime fill of `CaseIClassEqDischarge`.** Under regularity
(p coprime to |Cl(K)|), the case-I factor ideal `I` is principal,
hence `[σI] = [I] = 1` trivially. Direct repackaging via
flt-regular's `isPrincipal_of_isPrincipal_pow_of_coprime`.

For irregular primes (like `p = 37`), this does NOT apply directly;
the predicate must be filled via the substantive Vandiver/Washington
9.3 program (Stage 2 + class-equality conversion). -/
theorem caseIClassEqDischarge_of_regular {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K]
    [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K)) :
    CaseIClassEqDischarge p K := by
  intro a b c _ _ _ ζ _ I hI_nz hI
  have hI_principal : I.IsPrincipal :=
    isPrincipal_of_isPrincipal_pow_of_coprime hreg ⟨_, hI.symm⟩
  have h_class_I :
      ClassGroup.mk0
        (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_nz⟩
          : nonZeroDivisors (Ideal (𝓞 K))) = 1 :=
    (ClassGroup.mk0_eq_one_iff _).mpr hI_principal
  have hσI_principal :
      (I.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).IsPrincipal := by
    obtain ⟨a, ha⟩ := hI_principal
    refine ⟨⟨ringOfIntegersComplexConj K a, ?_⟩⟩
    have h_map_span : (Ideal.span ({a} : Set (𝓞 K))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span ({ringOfIntegersComplexConj K a} : Set (𝓞 K)) := by
      rw [Ideal.map_span]
      simp
    rw [ha, h_map_span]
  have h_class_σI :
      ClassGroup.mk0
        (⟨I.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            ((map_ne_bot_iff_complexConj K I).mpr hI_nz)⟩
          : nonZeroDivisors (Ideal (𝓞 K))) = 1 :=
    (ClassGroup.mk0_eq_one_iff _).mpr hσI_principal
  rw [h_class_I, h_class_σI]

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
