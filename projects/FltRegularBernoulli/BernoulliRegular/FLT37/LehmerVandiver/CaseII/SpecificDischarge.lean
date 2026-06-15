import BernoulliRegular.FLT37.LehmerVandiver.CaseII.PrincipalDischarge
import FltRegular.CaseII.InductionStep
import FltRegular.NumberTheory.KummersLemma.KummersLemma


/-!
# LV-CaseII specific principalization discharge (refined)

The general predicate `CaseIIPrincipalDischarge` (every fractional
ideal `I` with `(I^p)` principal is itself principal) is mathematically
**too strong** for irregular primes (where `Cl(K)⁻[p]` is non-trivial,
witnessing fractional ideals of order `p` whose `p`-th power is
principal but which are themselves non-principal).

This file provides a refined predicate
`CaseIIPrincipalDischargeOnSpecific` that quantifies only over the
fractional ideals appearing in flt-regular's case-II setup
(`𝔞 η₁ / 𝔞 η₂` for specific case-II data). Filling this refined
predicate is genuinely tractable under `¬ p ∣ h⁺(K)` + the
second-order Bernoulli condition (Washington Theorem 9.4 content).

Plus a wrapper showing that the refined predicate suffices for the
case-II inductive descent (everywhere that the general predicate is
applied in the case-II chain, the refined predicate suffices).

## References

* `CaseIIPrincipalDischarge` (the general predicate, in `PrincipalDischarge.lean`).
* `a_div_principal_of_discharge` (the consumer in the case-II chain).
* Washington, *Introduction to Cyclotomic Fields*, Theorem 9.4.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseII

variable (p : ℕ) [Fact p.Prime] [NeZero p]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **Refined case-II principalization discharge**: principalization
restricted to the specific fractional ideals appearing in
flt-regular's case-II setup.

Under `¬ p ∣ h⁺(K)` + second-order Bernoulli condition, this is
provable (Washington Theorem 9.4). The general
`CaseIIPrincipalDischarge` is too strong for irregular primes.

The predicate quantifies over case-II data `(ζ, x, y, z, ε, m, hy, η₁, η₂)`
and asserts that the auxiliary fractional ideal `𝔞 η₁ / 𝔞 η₂` is
principal. -/
def CaseIIPrincipalDischargeOnSpecific : Prop :=
  ∀ (hp_ne_two : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p =
      ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.toInteger - 1 ∣ y)
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)),
    Submodule.IsPrincipal
      (((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₁) /
        (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₂)
        : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

omit [NumberField.IsCMField K] in
/-- **General → specific.** Trivial direction: the general predicate
implies the specific one, by instantiation. -/
theorem caseIIPrincipalDischargeOnSpecific_of_general (h : CaseIIPrincipalDischarge p K) :
    CaseIIPrincipalDischargeOnSpecific p K := by
  intro hp_ne_two ζ hζ x y z ε m e hy η₁ η₂
  apply h
  rw [div_pow, ← FractionalIdeal.coeIdeal_pow, ← FractionalIdeal.coeIdeal_pow,
    root_div_zeta_sub_one_dvd_gcd_spec, root_div_zeta_sub_one_dvd_gcd_spec]
  exact c_div_principal hp_ne_two hζ e hy η₁ η₂

omit [Fact p.Prime] [NeZero p] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- The diagonal quotient of a fractional ideal by itself is principal. -/
lemma fractionalIdeal_div_self_isPrincipal (I : FractionalIdeal (𝓞 K)⁰ K) :
    Submodule.IsPrincipal ((I / I : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) := by
  by_cases hI : I = 0
  · rw [hI, zero_div]
    rw [FractionalIdeal.isPrincipal_iff]
    exact ⟨0, by simp⟩
  · have hdiv : I / I = 1 := by
      rw [div_eq_mul_inv]
      exact mul_inv_cancel₀ hI
    rw [hdiv]
    rw [FractionalIdeal.isPrincipal_iff]
    exact ⟨1, by simp⟩

omit [Fact p.Prime] [NeZero p] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- A nonzero integral generator from the real subfield gives the real-ideal
model required by the case-II principalization machinery.

This is pure ideal bookkeeping.  The Washington 9.4 source work still has to
prove that the concrete expression is integral, nonzero, and generates the
specific quotient; once that is available, this lemma turns it into the
`J.map _` witness consumed by
`caseII_specificQuotient_principal_of_realIdealModel`. -/
theorem realIdealModel_of_integral_real_generator
    (F : FractionalIdeal (𝓞 K)⁰ K)
    (b : 𝓞 (K⁺)) (hb : b ≠ 0)
    (hF : F =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K
          (algebraMap (𝓞 (K⁺)) (𝓞 K) b))) :
    ∃ J : Ideal (𝓞 (K⁺)), J ≠ ⊥ ∧
      F = (J.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) := by
  refine ⟨Ideal.span ({b} : Set (𝓞 (K⁺))), ?_, ?_⟩
  · intro hbot
    exact hb (Ideal.span_singleton_eq_bot.mp hbot)
  · rw [hF, Ideal.map_span, Set.image_singleton,
      FractionalIdeal.coeIdeal_span_singleton]

omit [NumberField.IsCMField K] in
/-- The `p`-th power of a specific case-II auxiliary quotient is principal.

This is the formalized "standard quotient" input in the real-ideal descent:
`c_div_principal` supplies principality after expanding the quotient power and
using the defining `root_div_zeta_sub_one_dvd_gcd_spec` identities. -/
theorem caseII_specificQuotient_pow_isPrincipal
    (hp_ne_two : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p =
      ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.toInteger - 1 ∣ y)
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) :
    ((((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₁ :
          FractionalIdeal (𝓞 K)⁰ K) /
        (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₂ :
          FractionalIdeal (𝓞 K)⁰ K)) ^ p :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal := by
  rw [div_pow, ← FractionalIdeal.coeIdeal_pow, ← FractionalIdeal.coeIdeal_pow,
    root_div_zeta_sub_one_dvd_gcd_spec, root_div_zeta_sub_one_dvd_gcd_spec]
  exact c_div_principal hp_ne_two hζ e hy η₁ η₂

/-- A real-model witness for a specific case-II quotient gives a plus-side
`p`-torsion ideal class.

This isolates the class-group payload of the real-descent step: once the
quotient is identified with `J.map _`, the standard principal quotient identity
shows `(J.map _)^p` is principal, Diekmann Prop. 55 descends this to `J^p`, and
therefore `[J]^p = 1` in `Cl(𝓞 K⁺)`. -/
theorem caseII_realIdealModel_plusClass_pow_eq_one
    (hp_ne_two : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p =
      ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.toInteger - 1 ∣ y)
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K))
    {J : Ideal (𝓞 (K⁺))} (hJ_ne : J ≠ ⊥)
    (hJ_model :
      (((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₁) /
        (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₂)
        : FractionalIdeal (𝓞 K)⁰ K) =
        (J.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K))) :
    (ClassGroup.mk0
      (⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne⟩ :
        nonZeroDivisors (Ideal (𝓞 (K⁺))))) ^ p = 1 := by
  have h_ratio_pow_principal :
      ((((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₁ :
            FractionalIdeal (𝓞 K)⁰ K) /
          (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₂ :
            FractionalIdeal (𝓞 K)⁰ K)) ^ p :
          FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal :=
    caseII_specificQuotient_pow_isPrincipal p K hp_ne_two hζ e hy η₁ η₂
  have hJ_pow_submodule :
      ((((J.map (algebraMap (𝓞 (K⁺)) (𝓞 K))) ^ p :
          Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K).IsPrincipal := by
    simpa [hJ_model, FractionalIdeal.coeIdeal_pow] using h_ratio_pow_principal
  have hJ_pow_principal :
      ((J.map (algebraMap (𝓞 (K⁺)) (𝓞 K))) ^ p : Ideal (𝓞 K)).IsPrincipal :=
    (IsFractionRing.coeSubmodule_isPrincipal
      (R := 𝓞 K) (K := K)
      (I := (J.map (algebraMap (𝓞 (K⁺)) (𝓞 K))) ^ p)).mp
      (by simpa using hJ_pow_submodule)
  have hJp_principal : (J ^ p).IsPrincipal := by
    rw [show ((J.map (algebraMap (𝓞 (K⁺)) (𝓞 K))) ^ p) =
        (J ^ p).map (algebraMap (𝓞 (K⁺)) (𝓞 K)) from
      (Ideal.map_pow (algebraMap (𝓞 (K⁺)) (𝓞 K)) J p).symm] at hJ_pow_principal
    exact isPrincipal_of_isPrincipal_map_Kplus (p := p) (hp_odd := hp_ne_two)
      (K := K) (J ^ p) hJ_pow_principal
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hJp_ne : J ^ p ≠ ⊥ := by
    intro h
    apply hJ_ne
    rcases pow_eq_zero_iff hp_pos.ne' |>.mp h with rfl
    rfl
  have hJ_ne0 : J ∈ nonZeroDivisors (Ideal (𝓞 (K⁺))) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne
  have hJp_ne0 : J ^ p ∈ nonZeroDivisors (Ideal (𝓞 (K⁺))) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hJp_ne
  have hJpow_class :
      ClassGroup.mk0 ⟨J ^ p, hJp_ne0⟩ =
        (ClassGroup.mk0 ⟨J, hJ_ne0⟩) ^ p := by
    rw [← map_pow]
    rfl
  rw [← hJpow_class]
  exact (ClassGroup.mk0_eq_one_iff hJp_ne0).mpr hJp_principal

/-- One case-II quotient is principal if it descends from a nonzero plus-side
ideal and its `p`-th power is the standard principal quotient. -/
theorem caseII_specificQuotient_principal_of_realIdealModel
    (hp_ne_two : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p =
      ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.toInteger - 1 ∣ y)
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K))
    {J : Ideal (𝓞 (K⁺))} (hJ_ne : J ≠ ⊥)
    (hJ_model :
      (((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₁) /
        (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₂)
        : FractionalIdeal (𝓞 K)⁰ K) =
        (J.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K))) :
    Submodule.IsPrincipal
      (((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₁) /
        (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₂)
        : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  have h_ratio_pow_principal :
      ((((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₁ :
            FractionalIdeal (𝓞 K)⁰ K) /
          (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₂ :
            FractionalIdeal (𝓞 K)⁰ K)) ^ p :
          FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal :=
    caseII_specificQuotient_pow_isPrincipal p K hp_ne_two hζ e hy η₁ η₂
  have hJ_pow_submodule :
      ((((J.map (algebraMap (𝓞 (K⁺)) (𝓞 K))) ^ p :
          Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K).IsPrincipal := by
    simpa [hJ_model, FractionalIdeal.coeIdeal_pow] using h_ratio_pow_principal
  have hJ_pow_principal :
      ((J.map (algebraMap (𝓞 (K⁺)) (𝓞 K))) ^ p : Ideal (𝓞 K)).IsPrincipal :=
    (IsFractionRing.coeSubmodule_isPrincipal
      (R := 𝓞 K) (K := K)
      (I := (J.map (algebraMap (𝓞 (K⁺)) (𝓞 K))) ^ p)).mp
      (by simpa using hJ_pow_submodule)
  have hJ_map_principal :
      (J.map (algebraMap (𝓞 (K⁺)) (𝓞 K))).IsPrincipal :=
    map_isPrincipal_of_pow_principal_of_not_dvd_hPlus
      (K := K) hp_ne_two h_not_dvd hJ_ne hJ_pow_principal
  have hJ_map_submodule :
      (((J.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) :
          Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :
        Submodule (𝓞 K) K).IsPrincipal :=
    (IsFractionRing.coeSubmodule_isPrincipal
      (R := 𝓞 K) (K := K)
      (I := J.map (algebraMap (𝓞 (K⁺)) (𝓞 K)))).mpr hJ_map_principal
  simpa [hJ_model] using hJ_map_submodule

/-- A real-model witness for the single quotient `𝔞 η / 𝔞 η₀` gives the
principalization actually consumed by the case-II descent, namely
`𝔞 η / 𝔞₀`.

This avoids asking for a full pairwise principalization predicate at the first
descent step: the only extra input is the explicit real-side model for the
quotient against the distinguished root `η₀`. -/
theorem caseII_a_div_a_zero_isPrincipal_of_realIdealModel
    (hp_ne_two : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p =
      ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.toInteger - 1 ∣ y)
    (η : nthRootsFinset p (1 : 𝓞 K))
    {J : Ideal (𝓞 (K⁺))} (hJ_ne : J ≠ ⊥)
    (hJ_model :
      (((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η) /
        (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy
          (zetaSubOneDvdRoot hp_ne_two hζ e hy))
        : FractionalIdeal (𝓞 K)⁰ K) =
        (J.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K))) :
    Submodule.IsPrincipal
      ((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η /
        aEtaZeroDvdPPow hp_ne_two hζ e hy
        : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  have h_pair :=
    caseII_specificQuotient_principal_of_realIdealModel p K hp_ne_two h_not_dvd
      hζ e hy η (zetaSubOneDvdRoot hp_ne_two hζ e hy) hJ_ne hJ_model
  rw [← a_eta_zero_dvd_p_pow_spec, mul_comm, FractionalIdeal.coeIdeal_mul,
      ← div_div, FractionalIdeal.isPrincipal_iff] at h_pair
  obtain ⟨a, ha⟩ := h_pair
  rw [div_eq_iff, Ideal.span_singleton_pow, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton] at ha
  · rw [FractionalIdeal.isPrincipal_iff]
    exact ⟨_, ha⟩
  · rw [← FractionalIdeal.coeIdeal_bot,
      (FractionalIdeal.coeIdeal_injective' (le_rfl : (𝓞 K)⁰ ≤ (𝓞 K)⁰)).ne_iff]
    apply mt eq_zero_of_pow_eq_zero
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero (Fact.out : Nat.Prime p).one_lt

/-- Fixed-data principalization target for the case-II descent.

For a single case-II equation, this asks only for the principalization of the
quotients `𝔞 η / 𝔞₀` with `η ≠ η₀`. These are precisely the quotients used to
build the next descent equation. -/
def CaseIIPrincipalizationAgainstEtaZero
    (hp_ne_two : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p =
      ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.toInteger - 1 ∣ y) : Prop :=
  ∀ η : nthRootsFinset p (1 : 𝓞 K),
    η ≠ zetaSubOneDvdRoot hp_ne_two hζ e hy →
      Submodule.IsPrincipal
        ((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η /
          aEtaZeroDvdPPow hp_ne_two hζ e hy
          : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)

/-- Real models only against the distinguished root `η₀` imply the fixed-data
principalization target consumed by the descent. -/
theorem caseIIPrincipalizationAgainstEtaZero_of_realIdealModel
    (hp_ne_two : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p =
      ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.toInteger - 1 ∣ y)
    (h_model_base : ∀ η : nthRootsFinset p (1 : 𝓞 K),
      η ≠ zetaSubOneDvdRoot hp_ne_two hζ e hy →
        ∃ J : Ideal (𝓞 (K⁺)), J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η) /
            (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy
              (zetaSubOneDvdRoot hp_ne_two hζ e hy))
            : FractionalIdeal (𝓞 K)⁰ K) =
            (J.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) :
              FractionalIdeal (𝓞 K)⁰ K))) :
    CaseIIPrincipalizationAgainstEtaZero p K hp_ne_two hζ e hy := by
  intro η hη
  obtain ⟨J, hJ_ne, hJ_model⟩ := h_model_base η hη
  exact caseII_a_div_a_zero_isPrincipal_of_realIdealModel p K hp_ne_two h_not_dvd
    hζ e hy η hJ_ne hJ_model

/-- Global anchored principalization provider for the specific case-II ideals.

Compared with `CaseIIPrincipalDischargeOnSpecific`, this asks only for the
principalizations of `𝔞 η / 𝔞₀` for each concrete case-II datum. -/
def CaseIIPrincipalizationAgainstEtaZeroOnSpecific (hp_ne_two : p ≠ 2) : Prop :=
  ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p =
      ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.toInteger - 1 ∣ y),
      CaseIIPrincipalizationAgainstEtaZero p K hp_ne_two hζ e hy

/-- Anchored real models supply the global anchored principalization provider. -/
theorem caseIIPrincipalizationAgainstEtaZeroOnSpecific_of_realIdealModel
    (hp_ne_two : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (h_model_base : ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p)
      {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
      (e : x ^ p + y ^ p =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η : nthRootsFinset p (1 : 𝓞 K)),
      η ≠ zetaSubOneDvdRoot hp_ne_two hζ e hy →
        ∃ J : Ideal (𝓞 (K⁺)), J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η) /
            (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy
              (zetaSubOneDvdRoot hp_ne_two hζ e hy))
            : FractionalIdeal (𝓞 K)⁰ K) =
            (J.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) :
              FractionalIdeal (𝓞 K)⁰ K))) :
    CaseIIPrincipalizationAgainstEtaZeroOnSpecific p K hp_ne_two := by
  intro ζ hζ x y z ε m e hy
  exact caseIIPrincipalizationAgainstEtaZero_of_realIdealModel
    p K hp_ne_two h_not_dvd hζ e hy (h_model_base hζ e hy)

/-- Anchored integral real generators supply the global anchored
principalization provider.

This is the generator-level version of
`caseIIPrincipalizationAgainstEtaZeroOnSpecific_of_realIdealModel`: the source
side only has to construct a nonzero integral real generator for
`𝔞 η / 𝔞₀`; the real-ideal model is then pure bookkeeping. -/
theorem caseIIPrincipalizationAgainstEtaZeroOnSpecific_of_integral_real_generators
    (hp_ne_two : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (hgen_base : ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p)
      {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
      (e : x ^ p + y ^ p =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η : nthRootsFinset p (1 : 𝓞 K)),
      η ≠ zetaSubOneDvdRoot hp_ne_two hζ e hy →
        ∃ b : 𝓞 (K⁺), b ≠ 0 ∧
          (((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η) /
            (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy
              (zetaSubOneDvdRoot hp_ne_two hζ e hy))
            : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰
              (algebraMap (𝓞 K) K
                (algebraMap (𝓞 (K⁺)) (𝓞 K) b)))) :
    CaseIIPrincipalizationAgainstEtaZeroOnSpecific p K hp_ne_two := by
  refine caseIIPrincipalizationAgainstEtaZeroOnSpecific_of_realIdealModel
    p K hp_ne_two h_not_dvd ?_
  intro ζ hζ x y z ε m e hy η hη
  obtain ⟨b, hb, hgen⟩ := hgen_base hζ e hy η hη
  exact realIdealModel_of_integral_real_generator
    (K := K)
    (((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η) /
      (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy
        (zetaSubOneDvdRoot hp_ne_two hζ e hy))
      : FractionalIdeal (𝓞 K)⁰ K)) b hb hgen

/-- **Specific principalization from real ideal descent.**

This is the narrow class-group bridge for the case-II principalization target.
For each actual case-II quotient
`𝔞 η₁ / 𝔞 η₂`, assume only an explicit descent witness: the quotient is the
extension to `K` of a nonzero ideal of `K⁺`.  The regularity-free identity
`(𝔞 η₁ / 𝔞 η₂)^p` principal is already supplied by `c_div_principal`; the
existing plus-class-number argument then kills the descended `p`-torsion class
under `¬ p ∣ hPlus K`.

This theorem does not prove the descent witness.  That witness is precisely the
remaining Washington 9.4 "specific ideal is real" source step. -/
theorem caseIIPrincipalDischargeOnSpecific_of_realIdealModel
    (hp_ne_two : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (h_model : ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p)
      {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
      (e : x ^ p + y ^ p =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)),
      ∃ J : Ideal (𝓞 (K⁺)), J ≠ ⊥ ∧
        (((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₁) /
          (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₂)
          : FractionalIdeal (𝓞 K)⁰ K) =
          (J.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) :
            FractionalIdeal (𝓞 K)⁰ K))) :
    CaseIIPrincipalDischargeOnSpecific p K := by
  intro _hp_ne_two ζ hζ x y z ε m e hy η₁ η₂
  obtain ⟨J, hJ_ne, hJ_model⟩ := h_model hζ e hy η₁ η₂
  exact caseII_specificQuotient_principal_of_realIdealModel p K hp_ne_two h_not_dvd
    hζ e hy η₁ η₂ hJ_ne hJ_model

/-- **Specific principalization from real ideal descent away from the diagonal.**

The diagonal case `η₁ = η₂` has quotient `1`, hence is already principal.  Thus
the remaining real-descent source only has to handle distinct roots. -/
theorem caseIIPrincipalDischargeOnSpecific_of_realIdealModel_ne
    (hp_ne_two : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (h_model_ne : ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ p)
      {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
      (e : x ^ p + y ^ p =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)),
      η₁ ≠ η₂ →
      ∃ J : Ideal (𝓞 (K⁺)), J ≠ ⊥ ∧
        (((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₁) /
          (rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₂)
          : FractionalIdeal (𝓞 K)⁰ K) =
          (J.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) :
            FractionalIdeal (𝓞 K)⁰ K))) :
    CaseIIPrincipalDischargeOnSpecific p K := by
  intro _hp_ne_two ζ hζ x y z ε m e hy η₁ η₂
  by_cases hη : η₁ = η₂
  · subst η₂
    exact fractionalIdeal_div_self_isPrincipal K
      (((rootDivZetaSubOneDvdGcd hp_ne_two hζ e hy η₁) :
        FractionalIdeal (𝓞 K)⁰ K))
  · obtain ⟨J, hJ_ne, hJ_model⟩ := h_model_ne hζ e hy η₁ η₂ hη
    exact caseII_specificQuotient_principal_of_realIdealModel p K hp_ne_two h_not_dvd
      hζ e hy η₁ η₂ hJ_ne hJ_model

-- The tightened `AdaptedKummersLemmaOnSpecific` predicate and the
-- compatibility helper `adaptedKummersLemmaOnSpecific_of_general` have
-- been moved to `SpecificChain.lean`. The tightened predicate quantifies
-- over the case-II structural data (including `h_specific`) and
-- references `associated_eta_zero_unit_of_specific_discharge`, which is
-- only available after `SpecificChain.lean`. See ticket C2-1 in
-- `.mathlib-quality/flt37-final-phase-tickets.md`.

set_option backward.isDefEq.respectTransparency false in
omit [NeZero p] [NumberField.IsCMField K] in
/-- **Regular-prime fill**: under regularity, `AdaptedKummersLemma`
holds. This is a direct repackaging of flt-regular's
`eq_pow_prime_of_unit_of_congruent`.

For irregular primes (like `p = 37`), this does NOT apply; the
predicate must be filled via the substantive Vandiver/Washington 9.4
program (or its refined `OnSpecific` variant). -/
theorem adaptedKummersLemma_of_regular [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
    (hp_ne_two : p ≠ 2) :
    AdaptedKummersLemma p K := fun u hcong =>
  eq_pow_prime_of_unit_of_congruent (K := K) hp_ne_two hreg u hcong

set_option backward.isDefEq.respectTransparency false in
omit [Fact p.Prime] [NeZero p] [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- **Regular-prime fill of `CaseIIPrincipalDischarge`**: under
regularity (p coprime to |Cl(K)|), the principalization predicate
holds. Direct repackaging of flt-regular's
`isPrincipal_of_isPrincipal_pow_of_Coprime'`.

For irregular primes (like `p = 37`), this does NOT apply directly;
the predicate must be filled via class-equality analysis on the
specific case-II ideals (`CaseIIPrincipalDischargeOnSpecific`). -/
theorem caseIIPrincipalDischarge_of_regular [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K)) :
    CaseIIPrincipalDischarge p K := fun I hIp =>
  isPrincipal_of_isPrincipal_pow_of_Coprime' p hreg I hIp

set_option backward.isDefEq.respectTransparency false in
omit [NeZero p] [NumberField.IsCMField K] in
/-- **Both case-II discharges hold under regularity.** Combined fact:
under regularity, both `CaseIIPrincipalDischarge` and
`AdaptedKummersLemma` hold, so the case-II parametric bridge is fully
fillable from regularity alone (mirroring flt-regular's caseII). -/
theorem caseII_discharges_of_regular
    [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
    (hp_ne_two : p ≠ 2) :
    CaseIIPrincipalDischarge p K ∧ AdaptedKummersLemma p K :=
  ⟨caseIIPrincipalDischarge_of_regular p K hreg,
   adaptedKummersLemma_of_regular p K hreg hp_ne_two⟩

set_option backward.isDefEq.respectTransparency false in
omit [NumberField.IsCMField K] in
/-- **Regular-prime fill of `CaseIIPrincipalDischargeOnSpecific`.**
Trivial composition: under regularity, the specific predicate is also
implied (via `caseIIPrincipalDischargeOnSpecific_of_general`). -/
theorem caseIIPrincipalDischargeOnSpecific_of_regular
    [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K)) :
    CaseIIPrincipalDischargeOnSpecific p K :=
  caseIIPrincipalDischargeOnSpecific_of_general p K
    (caseIIPrincipalDischarge_of_regular p K hreg)

end CaseII

end LehmerVandiver

end FLT37

end BernoulliRegular

end
