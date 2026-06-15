module

public import BernoulliRegular.Reflection.ResidueSymbol.IdealAvoidance
public import BernoulliRegular.Reflection.SingularKummer.LocalizationKernel

/-!
# Singular Kummer: integral normalization

This file records the REF-14 normalization step.  Multiplying a singular pair
by a principal pair changes its generator by a global `p`-th power and leaves
its singular-group class unchanged.  Choosing the principal factor to clear
denominators makes the fractional ideal an integral ideal.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace SingularPair

set_option linter.unusedSectionVars false

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- A fractional-ideal unit can be made integral after multiplying by a
principal fractional ideal. -/
theorem exists_integralIdeal_mul_toPrincipalIdeal
    (I : (FractionalIdeal R⁰ K)ˣ) :
    ∃ (gamma : Kˣ) (J : (Ideal R)⁰),
      I * toPrincipalIdeal R K gamma = FractionalIdeal.mk0 K J := by
  obtain ⟨a, J, ha, hI⟩ :=
    FractionalIdeal.exists_eq_spanSingleton_mul (I : FractionalIdeal R⁰ K)
  have hmapa : algebraMap R K a ≠ 0 :=
    mt IsFractionRing.to_map_eq_zero_iff.mp ha
  let gamma : Kˣ := Units.mk0 (algebraMap R K a) hmapa
  have hJne : J ≠ ⊥ :=
    FractionalIdeal.ideal_factor_ne_zero
      (I := (I : FractionalIdeal R⁰ K)) (Units.ne_zero I) hI
  let J0 : (Ideal R)⁰ := ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJne⟩
  refine ⟨gamma, J0, ?_⟩
  apply Units.ext
  change
    (I : FractionalIdeal R⁰ K) *
        (toPrincipalIdeal R K gamma : FractionalIdeal R⁰ K) =
      (FractionalIdeal.mk0 K J0 : FractionalIdeal R⁰ K)
  rw [hI, FractionalIdeal.coe_mk0, coe_toPrincipalIdeal]
  dsimp [J0]
  simp only [gamma, Units.val_mk0]
  rw [mul_assoc,
    mul_comm (J : FractionalIdeal R⁰ K)
      (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)),
    ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton,
    inv_mul_cancel₀ hmapa, FractionalIdeal.spanSingleton_one, one_mul]

variable {p : ℕ}

/-- Multiply a singular pair by a principal pair so that its ideal is an
integral ideal.  The quotient singular class is unchanged. -/
theorem exists_integral_normalization
    (s : SingularPair R K p) :
    ∃ (t : SingularPair R K p) (gamma : Kˣ) (J : (Ideal R)⁰),
      ideal t = FractionalIdeal.mk0 K J ∧
      generator t = generator s * gamma ^ p ∧
      (QuotientGroup.mk t : SingularGroup (R := R) (K := K) p) =
        QuotientGroup.mk s ∧
      toPrincipalIdeal R K (generator t) = (FractionalIdeal.mk0 K J) ^ p := by
  obtain ⟨gamma, J, hIJ⟩ :=
    exists_integralIdeal_mul_toPrincipalIdeal (R := R) (K := K) (ideal s)
  let t : SingularPair R K p := s * principalPair (R := R) (K := K) p gamma
  have ht_ideal : ideal t = FractionalIdeal.mk0 K J := by
    simpa [t, principalPair, ideal] using hIJ
  refine ⟨t, gamma, J, ht_ideal, ?_, ?_, ?_⟩
  · simp [t, principalPair, generator]
  · have hprincipal :
        (QuotientGroup.mk (principalPair (R := R) (K := K) p gamma) :
            SingularGroup (R := R) (K := K) p) = 1 :=
      (QuotientGroup.eq_one_iff
        (N := principalPairSubgroup (R := R) (K := K) p)
        (principalPair (R := R) (K := K) p gamma)).2 ⟨gamma, rfl⟩
    change
      (QuotientGroup.mk
          (s * principalPair (R := R) (K := K) p gamma) :
        SingularGroup (R := R) (K := K) p) =
        QuotientGroup.mk s
    rw [QuotientGroup.mk_mul, hprincipal, mul_one]
  · simpa [ht_ideal] using
      (principal_eq_ideal_pow (R := R) (K := K) (s := t))

/-- Integral normalization with a prescribed coprime condition.

After first clearing denominators, ideal avoidance replaces the integral ideal
by another representative in the same class that is coprime to the maximal
ideal `P`.  The replacement is absorbed into the singular pair by multiplying
by a principal pair, so the singular-group class is unchanged. -/
theorem exists_integral_normalization_coprime
    (s : SingularPair R K p) (P : Ideal R) [P.IsMaximal] :
    ∃ (t : SingularPair R K p) (gamma : Kˣ) (J : (Ideal R)⁰),
      ideal t = FractionalIdeal.mk0 K J ∧
      IsCoprime (J : Ideal R) P ∧
      generator t = generator s * gamma ^ p ∧
      (QuotientGroup.mk t : SingularGroup (R := R) (K := K) p) =
        QuotientGroup.mk s ∧
      toPrincipalIdeal R K (generator t) = (FractionalIdeal.mk0 K J) ^ p := by
  obtain ⟨t₀, gamma₀, J₀, ht₀_ideal, ht₀_generator, hclass₀, _ht₀_principal⟩ :=
    exists_integral_normalization (R := R) (K := K) (p := p) s
  obtain ⟨J, hJ_class, hJ_coprime⟩ :=
    ResidueSymbol.IdealAvoidance.exists_class_representative_coprime_singleton
      (R := R) (c := ClassGroup.mk0 J₀) P
  obtain ⟨delta, hdelta_ne, hdelta⟩ :=
    (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring
      (R := R) (K := K) (I := J₀) (J := J)).mp hJ_class.symm
  let deltaUnit : Kˣ := Units.mk0 delta hdelta_ne
  let t : SingularPair R K p := t₀ * principalPair (R := R) (K := K) p deltaUnit
  have ht_ideal : ideal t = FractionalIdeal.mk0 K J := by
    calc
      ideal t = ideal t₀ * toPrincipalIdeal R K deltaUnit := by
        simp [t, principalPair, ideal]
      _ = FractionalIdeal.mk0 K J := by
        apply Units.ext
        rw [ht₀_ideal]
        change
          (FractionalIdeal.mk0 K J₀ : FractionalIdeal R⁰ K) *
              ((toPrincipalIdeal R K deltaUnit : (FractionalIdeal R⁰ K)ˣ) :
                FractionalIdeal R⁰ K) =
            (FractionalIdeal.mk0 K J : FractionalIdeal R⁰ K)
        rw [coe_toPrincipalIdeal]
        change
          (FractionalIdeal.mk0 K J₀ : FractionalIdeal R⁰ K) *
              FractionalIdeal.spanSingleton R⁰ delta =
            (FractionalIdeal.mk0 K J : FractionalIdeal R⁰ K)
        rw [mul_comm]
        simpa [FractionalIdeal.coe_mk0] using hdelta
  refine ⟨t, gamma₀ * deltaUnit, J, ht_ideal, hJ_coprime, ?_, ?_, ?_⟩
  · calc
      generator t = generator t₀ * deltaUnit ^ p := by
        simp [t, principalPair, generator]
      _ = (generator s * gamma₀ ^ p) * deltaUnit ^ p := by rw [ht₀_generator]
      _ = generator s * (gamma₀ * deltaUnit) ^ p := by
        rw [mul_pow]
        ac_rfl
  · have hprincipal :
        (QuotientGroup.mk (principalPair (R := R) (K := K) p deltaUnit) :
            SingularGroup (R := R) (K := K) p) = 1 :=
      (QuotientGroup.eq_one_iff
        (N := principalPairSubgroup (R := R) (K := K) p)
        (principalPair (R := R) (K := K) p deltaUnit)).2 ⟨deltaUnit, rfl⟩
    change
      (QuotientGroup.mk
          (t₀ * principalPair (R := R) (K := K) p deltaUnit) :
        SingularGroup (R := R) (K := K) p) =
        QuotientGroup.mk s
    rw [QuotientGroup.mk_mul, hprincipal, mul_one, hclass₀]
  · simpa [ht_ideal] using
      (principal_eq_ideal_pow (R := R) (K := K) (s := t))

/-- If a principal fractional ideal generated by `g : Kˣ` is equal to the
`p`-th power of an integral ideal, then `g` is represented by an element of
the base ring and that element has the corresponding principal ideal.

This is the algebraic extraction needed after integral normalization of a
singular pair: it turns the field-unit generator into an integral numerator
for the residue-symbol API. -/
theorem exists_integral_generator_of_principal_eq_mk0_pow
    {g : Kˣ} {J : (Ideal R)⁰}
    (hprincipal : toPrincipalIdeal R K g = (FractionalIdeal.mk0 K J) ^ p) :
    ∃ η : R,
      algebraMap R K η = (g : K) ∧
      Ideal.span ({η} : Set R) = (J : Ideal R) ^ p := by
  have hspan :
      FractionalIdeal.spanSingleton R⁰ (g : K) =
        (((J : Ideal R) ^ p : Ideal R) : FractionalIdeal R⁰ K) := by
    have hval := congrArg (fun I : (FractionalIdeal R⁰ K)ˣ =>
      (I : FractionalIdeal R⁰ K)) hprincipal
    simpa [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_pow] using hval
  have hJpow_le :
      (((J : Ideal R) ^ p : Ideal R) : FractionalIdeal R⁰ K) ≤ 1 :=
    FractionalIdeal.coeIdeal_le_one
  have hg_mem_one : (g : K) ∈ (1 : FractionalIdeal R⁰ K) := by
    apply hJpow_le
    rw [← hspan]
    exact FractionalIdeal.mem_spanSingleton_self R⁰ (g : K)
  obtain ⟨η, hη⟩ := (FractionalIdeal.mem_one_iff (S := R⁰)).mp hg_mem_one
  refine ⟨η, hη, ?_⟩
  apply FractionalIdeal.coeIdeal_injective (K := K)
  calc
    ((Ideal.span ({η} : Set R) : Ideal R) : FractionalIdeal R⁰ K)
        = FractionalIdeal.spanSingleton R⁰ (algebraMap R K η) :=
            FractionalIdeal.coeIdeal_span_singleton η
    _ = FractionalIdeal.spanSingleton R⁰ (g : K) := by rw [hη]
    _ = (((J : Ideal R) ^ p : Ideal R) : FractionalIdeal R⁰ K) := hspan

/-- Two nonzero fractional ideals of a Dedekind domain are equal if all their
height-one valuations agree. -/
theorem fractionalIdeal_eq_of_forall_count_eq
    {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hcount : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  classical
  calc
    I = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R,
        (v.asIdeal : FractionalIdeal R⁰ K) ^ FractionalIdeal.count K v I :=
          (FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) hI).symm
    _ = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R,
        (v.asIdeal : FractionalIdeal R⁰ K) ^ FractionalIdeal.count K v J := by
          apply finprod_congr
          intro v
          rw [hcount v]
    _ = J := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) hJ

/-- Nonzero fractional ideals are torsion-free under positive natural powers. -/
theorem fractionalIdeal_pow_left_injective_of_ne_zero
    {n : ℕ} (hn : n ≠ 0) {I J : FractionalIdeal R⁰ K}
    (hI : I ≠ 0) (hJ : J ≠ 0) (hpow : I ^ n = J ^ n) :
    I = J := by
  apply fractionalIdeal_eq_of_forall_count_eq (K := K) hI hJ
  intro v
  have hcount := congrArg (FractionalIdeal.count K v) hpow
  rw [FractionalIdeal.count_pow, FractionalIdeal.count_pow] at hcount
  exact mul_left_cancel₀ (by exact_mod_cast hn : (n : ℤ) ≠ 0) hcount

/-- The unit group of nonzero fractional ideals is torsion-free under positive
natural powers. -/
theorem fractionalIdealUnit_pow_left_injective
    {n : ℕ} (hn : n ≠ 0) {I J : (FractionalIdeal R⁰ K)ˣ}
    (hpow : I ^ n = J ^ n) :
    I = J :=
  Units.ext <| fractionalIdeal_pow_left_injective_of_ne_zero (K := K) hn
    (Units.ne_zero I) (Units.ne_zero J)
    (congrArg (fun U : (FractionalIdeal R⁰ K)ˣ => (U : FractionalIdeal R⁰ K)) hpow)

/-- If the generator of a singular pair is a global `p`-th power, then the
singular-group class of the pair is trivial. -/
theorem singularGroup_mk_eq_one_of_generator_eq_pow
    (hp_ne : p ≠ 0) (s : SingularPair R K p) {γ : Kˣ}
    (hγ : generator s = γ ^ p) :
    (QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) = 1 := by
  have hideal_pow : ideal s ^ p = (toPrincipalIdeal R K γ) ^ p := by
    calc
      ideal s ^ p = toPrincipalIdeal R K (generator s) :=
        (principal_eq_ideal_pow (R := R) (K := K) s).symm
      _ = toPrincipalIdeal R K (γ ^ p) := by rw [hγ]
      _ = (toPrincipalIdeal R K γ) ^ p := map_pow (toPrincipalIdeal R K) γ p
  have hideal : ideal s = toPrincipalIdeal R K γ :=
    fractionalIdealUnit_pow_left_injective (R := R) (K := K) hp_ne hideal_pow
  have hs_eq : s = principalPair (R := R) (K := K) p γ := by
    apply Subtype.ext
    apply Prod.ext
    · exact hideal
    · exact hγ
  rw [hs_eq]
  exact
    (QuotientGroup.eq_one_iff
      (N := principalPairSubgroup (R := R) (K := K) p)
      (principalPair (R := R) (K := K) p γ)).2 ⟨γ, rfl⟩

/-- A nontrivial singular-group class has generator nontrivial in
`Kˣ / Kˣ^p`. -/
theorem not_isPow_generator_of_singularGroup_mk_ne_one
    (hp_ne : p ≠ 0) (s : SingularPair R K p)
    (hs_ne :
      (QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) ≠ 1) :
    ¬ ∃ β : K, β ^ p = (generator s : K) := by
  rintro ⟨β, hβ⟩
  have hβ_ne : β ≠ 0 := by
    intro hβ_zero
    have hpow_zero : β ^ p = 0 := by
      rw [hβ_zero]
      exact zero_pow hp_ne
    rw [hpow_zero] at hβ
    exact (generator s).ne_zero hβ.symm
  let γ : Kˣ := Units.mk0 β hβ_ne
  have hγ : generator s = γ ^ p :=
    Units.ext <| hβ.symm
  exact hs_ne (singularGroup_mk_eq_one_of_generator_eq_pow
    (R := R) (K := K) hp_ne s hγ)

section Cyclotomic

variable (K : Type*) [Field K] [NumberField K]
variable (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]

/-- REF-14: the REF-13 singular pair can be replaced by a representative whose
ideal is an integral ideal, without changing the singular class, localization
kernel condition, or `i`-th character eigenspace relation. -/
theorem exists_integral_normalized_singularPair_in_concrete_completed_localization_kernel
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p))]
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥) :
    ∃ s : SingularPair (𝓞 K) K p,
      ∃ t : SingularPair (𝓞 K) K p,
      ∃ gamma : Kˣ,
      ∃ J : (Ideal (𝓞 K))⁰,
        generator t = generator s * gamma ^ p ∧
        ideal t = FractionalIdeal.mk0 K J ∧
        toPrincipalIdeal (𝓞 K) K (generator t) =
          (FractionalIdeal.mk0 K J) ^ p ∧
        (QuotientGroup.mk t :
            SingularGroup (R := 𝓞 K) (K := K) p) =
          QuotientGroup.mk s ∧
        ∃ _ht_component :
          Additive.ofMul
              (QuotientGroup.mk t :
                SingularGroup (R := 𝓞 K) (K := K) p) ∈
            singularGroupCharacterProjectionComponent (K := K) (p := p) i
              (cyclotomicSingularGroupAction K p),
          (QuotientGroup.mk t :
              SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
          singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
            (Additive.ofMul
              (QuotientGroup.mk t :
                SingularGroup (R := 𝓞 K) (K := K) p)) = 0 ∧
          ∀ b : CharacterProjection.Delta p,
            Additive.ofMul
                (cyclotomicSingularGroupAction K p b
                  (QuotientGroup.mk t :
                    SingularGroup (R := 𝓞 K) (K := K) p)) =
              ((b : ZMod p) ^ i) •
                Additive.ofMul
                  (QuotientGroup.mk t :
                    SingularGroup (R := 𝓞 K) (K := K) p) := by
  obtain ⟨s, hs_component, hs_ne, hs_loc, _hs_principal, hs_eigen⟩ :=
    exists_singularPair_in_concrete_completed_localization_kernel
      (K := K) (p := p) hp_gt_two hi_even hi_low hi_high hA_ne_bot
  obtain ⟨t, gamma, J, ht_ideal, ht_generator, hclass, ht_principal⟩ :=
    exists_integral_normalization (R := 𝓞 K) (K := K) (p := p) s
  refine ⟨s, t, gamma, J, ht_generator, ht_ideal, ht_principal, hclass, ?_⟩
  have ht_component :
      Additive.ofMul
          (QuotientGroup.mk t :
            SingularGroup (R := 𝓞 K) (K := K) p) ∈
        singularGroupCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicSingularGroupAction K p) := by
    simpa [hclass] using hs_component
  refine ⟨ht_component, ?_, ?_, ?_⟩
  · intro ht_one
    exact hs_ne (hclass.symm.trans ht_one)
  · simpa [hclass] using hs_loc
  · intro b
    simpa [hclass] using hs_eigen b

/-- REF-14 with ideal avoidance at a chosen maximal ideal.

This is the same completed-localization-kernel representative as
`exists_integral_normalized_singularPair_in_concrete_completed_localization_kernel`,
but the integral ideal is additionally chosen coprime to `P`. -/
theorem exists_integral_coprime_normalized_singularPair_in_concrete_completed_localization_kernel
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hp_gt_two : 2 < p) {i : ℕ}
    (hi_even : Even i) (hi_low : 2 ≤ i) (hi_high : i ≤ p - 3)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p))]
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥) :
    ∃ s : SingularPair (𝓞 K) K p,
      ∃ t : SingularPair (𝓞 K) K p,
      ∃ gamma : Kˣ,
      ∃ J : (Ideal (𝓞 K))⁰,
        generator t = generator s * gamma ^ p ∧
        ideal t = FractionalIdeal.mk0 K J ∧
        IsCoprime (J : Ideal (𝓞 K)) P ∧
        toPrincipalIdeal (𝓞 K) K (generator t) =
          (FractionalIdeal.mk0 K J) ^ p ∧
        (QuotientGroup.mk t :
            SingularGroup (R := 𝓞 K) (K := K) p) =
          QuotientGroup.mk s ∧
        ∃ _ht_component :
          Additive.ofMul
              (QuotientGroup.mk t :
                SingularGroup (R := 𝓞 K) (K := K) p) ∈
            singularGroupCharacterProjectionComponent (K := K) (p := p) i
              (cyclotomicSingularGroupAction K p),
          (QuotientGroup.mk t :
              SingularGroup (R := 𝓞 K) (K := K) p) ≠ 1 ∧
          singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
            (Additive.ofMul
              (QuotientGroup.mk t :
                SingularGroup (R := 𝓞 K) (K := K) p)) = 0 ∧
          ∀ b : CharacterProjection.Delta p,
            Additive.ofMul
                (cyclotomicSingularGroupAction K p b
                  (QuotientGroup.mk t :
                    SingularGroup (R := 𝓞 K) (K := K) p)) =
              ((b : ZMod p) ^ i) •
                Additive.ofMul
                  (QuotientGroup.mk t :
                    SingularGroup (R := 𝓞 K) (K := K) p) := by
  obtain ⟨s, hs_component, hs_ne, hs_loc, _hs_principal, hs_eigen⟩ :=
    exists_singularPair_in_concrete_completed_localization_kernel
      (K := K) (p := p) hp_gt_two hi_even hi_low hi_high hA_ne_bot
  obtain ⟨t, gamma, J, ht_ideal, hJ_coprime, ht_generator, hclass, ht_principal⟩ :=
    exists_integral_normalization_coprime (R := 𝓞 K) (K := K) (p := p) s P
  refine ⟨s, t, gamma, J, ht_generator, ht_ideal, hJ_coprime, ht_principal, hclass, ?_⟩
  have ht_component :
      Additive.ofMul
          (QuotientGroup.mk t :
            SingularGroup (R := 𝓞 K) (K := K) p) ∈
        singularGroupCharacterProjectionComponent (K := K) (p := p) i
          (cyclotomicSingularGroupAction K p) := by
    simpa [hclass] using hs_component
  refine ⟨ht_component, ?_, ?_, ?_⟩
  · intro ht_one
    exact hs_ne (hclass.symm.trans ht_one)
  · simpa [hclass] using hs_loc
  · intro b
    simpa [hclass] using hs_eigen b

end Cyclotomic

end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end

end
