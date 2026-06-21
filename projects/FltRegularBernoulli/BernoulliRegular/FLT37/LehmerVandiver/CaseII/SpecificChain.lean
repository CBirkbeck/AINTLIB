import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummerCaseI
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.ProvedAuxiliaries
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.ADivPrincipal
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.SpecificDischarge
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Main
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.RealClosure
import BernoulliRegular.TotallyRealSubfield.FixedAssociate

/-!
# LV-CaseII parallel chain using `CaseIIPrincipalDischargeOnSpecific`

The case-II inductive descent in `ADivPrincipal.lean` uses the
**general** `CaseIIPrincipalDischarge` predicate as input. Since that
form is unfillable for irregular primes, we provide a parallel entry
point: `a_div_principal_of_specific_discharge` directly consumes
`CaseIIPrincipalDischargeOnSpecific`.

For the rest of the chain (downstream of `a_div_principal_of_discharge`),
the existing chain in `ADivPrincipal.lean` is reused via the
general → specific implication.

Combined with the regular-prime fill
`caseIIPrincipalDischargeOnSpecific_of_regular`, this provides a
"specific" entry to the case-II bridge for regular primes, mirroring
the structure for irregular primes.

## References

* `CaseIIPrincipalDischargeOnSpecific` (the refined predicate).
* `a_div_principal_of_discharge` (consumer using general predicate).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseII

private instance : Fact (Nat.Prime 37) := ⟨by decide⟩
private instance : NeZero (37 : ℕ) := ⟨by decide⟩

variable {p : ℕ} [hpri : Fact p.Prime] [NeZero p]
  {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x y z : 𝓞 K} {ε : (𝓞 K)ˣ}
variable {m : ℕ} (e : x ^ p + y ^ p =
  ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
variable (hy : ¬ hζ.toInteger - 1 ∣ y)

include hp hy in
/-- **`a_div_principal` from specific discharge.** Direct consumer of
`CaseIIPrincipalDischargeOnSpecific`. The conclusion of
`a_div_principal_of_discharge` from `ADivPrincipal.lean` is exactly
the body of `CaseIIPrincipalDischargeOnSpecific` at the right
arguments — so this theorem is a one-liner that unfolds the predicate.

Mirrors `a_div_principal_of_discharge` but uses the SPECIFIC
(fillable for irregular primes) predicate instead of the general
(unfillable for irregular primes) one. -/
theorem a_div_principal_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) :
    Submodule.IsPrincipal
      (((rootDivZetaSubOneDvdGcd hp hζ e hy η₁) /
        (rootDivZetaSubOneDvdGcd hp hζ e hy η₂)
        : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
  h_specific hp hζ e hy η₁ η₂

include hp hy in
/-- **`a_div_principal` from specific discharge** (alternative form
quantified over all `(η₁, η₂)`). Mirrors `a_div_principal_of_discharge`
in conclusion, parametric on the specific predicate. -/
theorem a_div_principal_of_specific_discharge_uniform
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K) :
    ∀ (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)),
    Submodule.IsPrincipal
      (((rootDivZetaSubOneDvdGcd hp hζ e hy η₁) /
        (rootDivZetaSubOneDvdGcd hp hζ e hy η₂)
        : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
  h_specific hp hζ e hy

variable (hz : ¬ hζ.toInteger - 1 ∣ z)

include hp hy in
/-- **`isPrincipal_a_div_a_zero` from specific discharge.** Mirror of
`isPrincipal_a_div_a_zero_of_discharge` but using the specific
predicate. Composes `a_div_principal_of_specific_discharge` with the
downstream ideal arithmetic. -/
theorem isPrincipal_a_div_a_zero_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η : nthRootsFinset p (1 : 𝓞 K)) :
    Submodule.IsPrincipal
      ((rootDivZetaSubOneDvdGcd hp hζ e hy η /
        aEtaZeroDvdPPow hp hζ e hy
        : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  have := a_div_principal_of_specific_discharge hp hζ e hy h_specific η
    (zetaSubOneDvdRoot hp hζ e hy)
  rw [← a_eta_zero_dvd_p_pow_spec, mul_comm, FractionalIdeal.coeIdeal_mul,
      ← div_div, FractionalIdeal.isPrincipal_iff] at this
  obtain ⟨a, ha⟩ := this
  rw [div_eq_iff, Ideal.span_singleton_pow, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton] at ha
  · rw [FractionalIdeal.isPrincipal_iff]
    exact ⟨_, ha⟩
  · rw [← FractionalIdeal.coeIdeal_bot,
      (FractionalIdeal.coeIdeal_injective' (le_rfl : (𝓞 K)⁰ ≤ (𝓞 K)⁰)).ne_iff]
    apply mt eq_zero_of_pow_eq_zero
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt

include hp hy hz in
/-- **`exists_not_dvd_spanSingleton_eq_a_div_a_zero` from specific
discharge.** Continues the parallel chain. Mirror of the
`_of_discharge` version using the specific predicate. -/
theorem exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ∃ a b : 𝓞 K, ¬ (hζ.toInteger - 1) ∣ a ∧ ¬ (hζ.toInteger - 1) ∣ b ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / b : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η /
        aEtaZeroDvdPPow hp hζ e hy :=
  exists_not_dvd_spanSingleton_eq hζ.zeta_sub_one_prime'
    _ _ ((p_dvd_a_iff hp hζ e hy η).not.mpr hη) (not_p_div_a_zero hp hζ e hy hz)
      (isPrincipal_a_div_a_zero_of_specific_discharge hp hζ e hy h_specific η)

/-- **α numerator from specific discharge.** -/
noncomputable
def a_div_a_zero_num_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) : 𝓞 K :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_specific_discharge
    hp hζ e hy hz h_specific η hη).choose

/-- **β denominator from specific discharge.** -/
noncomputable
def a_div_a_zero_denom_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) : 𝓞 K :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_specific_discharge
    hp hζ e hy hz h_specific η hη).choose_spec.choose

/-- **α numerator π-non-divisibility (specific discharge).** -/
theorem a_div_a_zero_num_spec_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ¬ (hζ.toInteger - 1) ∣
      a_div_a_zero_num_of_specific_discharge hp hζ e hy hz h_specific η hη :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_specific_discharge
    hp hζ e hy hz h_specific η hη).choose_spec.choose_spec.1

/-- **β denominator π-non-divisibility (specific discharge).** -/
theorem a_div_a_zero_denom_spec_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ¬ (hζ.toInteger - 1) ∣
      a_div_a_zero_denom_of_specific_discharge hp hζ e hy hz h_specific η hη :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_specific_discharge
    hp hζ e hy hz h_specific η hη).choose_spec.choose_spec.2.1

/-- **α/β = 𝔞 η / 𝔞₀ identity (specific discharge).** -/
theorem a_div_a_zero_eq_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (a_div_a_zero_num_of_specific_discharge hp hζ e hy hz h_specific η hη /
         a_div_a_zero_denom_of_specific_discharge hp hζ e hy hz h_specific η hη
          : K) =
      rootDivZetaSubOneDvdGcd hp hζ e hy η /
        aEtaZeroDvdPPow hp hζ e hy :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_specific_discharge
    hp hζ e hy hz h_specific η hη).choose_spec.choose_spec.2.2

include hp hy hz in
/-- **Cross-multiplied ideal identity from an explicit anchored quotient
generator.**

This is the generator-level form of
`a_mul_denom_eq_a_zero_mul_num_of_etaZeroPrincipalization`: instead of asking
for a principalization provider and then taking its chosen numerator and
denominator, it starts from concrete `a / b` generating
`𝔞η / 𝔞₀`. -/
theorem a_mul_denom_eq_a_zero_mul_num_of_spanSingleton
    (η : nthRootsFinset p (1 : 𝓞 K)) {a b : 𝓞 K}
    (hb : ¬ (hζ.toInteger - 1) ∣ b)
    (hspan :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / b : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η /
          aEtaZeroDvdPPow hp hζ e hy) :
    rootDivZetaSubOneDvdGcd hp hζ e hy η *
        Ideal.span ({b} : Set (𝓞 K)) =
      aEtaZeroDvdPPow hp hζ e hy *
        Ideal.span ({a} : Set (𝓞 K)) := by
  apply FractionalIdeal.coeIdeal_injective (K := K)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  rw [mul_comm (aEtaZeroDvdPPow hp hζ e hy : FractionalIdeal (𝓞 K)⁰ K),
    ← div_eq_div_iff,
    ← hspan, FractionalIdeal.spanSingleton_div_spanSingleton]
  · intro ha
    rw [FractionalIdeal.coeIdeal_eq_zero] at ha
    apply not_p_div_a_zero hp hζ e hy hz
    rw [ha]
    exact dvd_zero _
  · rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff,
      ← (algebraMap (𝓞 K) K).map_zero,
      (IsFractionRing.injective (𝓞 K) K).eq_iff]
    intro hb_zero
    apply hb
    rw [hb_zero]
    exact dvd_zero _

include hp hy hz in
/-- **Associated identity from an explicit anchored quotient generator.**

If `a / b` generates `𝔞η / 𝔞₀`, then the usual case-II associated element
identity follows without passing through a global principalization predicate. -/
theorem associated_eta_zero_of_spanSingleton
    (η : nthRootsFinset p (1 : 𝓞 K)) {a b : 𝓞 K}
    (hb : ¬ (hζ.toInteger - 1) ∣ b)
    (hspan :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / b : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η /
          aEtaZeroDvdPPow hp hζ e hy) :
    Associated ((x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) *
        a ^ p)
      ((x + y * (η : 𝓞 K)) * (hζ.toInteger - 1) ^ (m * p) * b ^ p) := by
  simp_rw [← Ideal.span_singleton_eq_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
    ← m_mul_c_mul_p hp hζ e hy, ← root_div_zeta_sub_one_dvd_gcd_spec,
    ← a_eta_zero_dvd_p_pow_spec]
  rw [mul_comm _ (aEtaZeroDvdPPow hp hζ e hy), mul_pow]
  simp only [mul_assoc, mul_left_comm _ (Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)))]
  rw [mul_left_comm (rootDivZetaSubOneDvdGcd hp hζ e hy η ^ p),
    mul_left_comm (aEtaZeroDvdPPow hp hζ e hy ^ p),
    ← pow_mul, ← mul_pow, ← mul_pow,
    a_mul_denom_eq_a_zero_mul_num_of_spanSingleton
      hp hζ e hy hz η hb hspan]

/-- **Associated-unit witness from an explicit anchored quotient generator.** -/
noncomputable
def associated_eta_zero_unit_of_spanSingleton
    (η : nthRootsFinset p (1 : 𝓞 K)) {a b : 𝓞 K}
    (hb : ¬ (hζ.toInteger - 1) ∣ b)
    (hspan :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / b : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η /
          aEtaZeroDvdPPow hp hζ e hy) : (𝓞 K)ˣ :=
  (associated_eta_zero_of_spanSingleton
    hp hζ e hy hz η hb hspan).choose

include hp hy hz in
/-- **Associated-unit specification from an explicit anchored quotient
generator.** -/
theorem associated_eta_zero_unit_spec_of_spanSingleton
    (η : nthRootsFinset p (1 : 𝓞 K)) {a b : 𝓞 K}
    (hb : ¬ (hζ.toInteger - 1) ∣ b)
    (hspan :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / b : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η /
          aEtaZeroDvdPPow hp hζ e hy) :
    (associated_eta_zero_unit_of_spanSingleton
        hp hζ e hy hz η hb hspan : 𝓞 K) *
        (x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) * a ^ p =
      (x + y * (η : 𝓞 K)) * (hζ.toInteger - 1) ^ (m * p) * b ^ p := by
  rw [mul_assoc,
    mul_comm (associated_eta_zero_unit_of_spanSingleton
      hp hζ e hy hz η hb hspan : 𝓞 K)]
  exact (associated_eta_zero_of_spanSingleton
    hp hζ e hy hz η hb hspan).choose_spec

include hp hy hz in
/-- **Case-II formula from two explicit anchored quotient generators.**

This is the pair-level version of `formula_of_etaZeroPrincipalization`; it
keeps only the two quotient generators that the descent equation actually
uses. -/
theorem formula_of_etaZeroSpanSingletons
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) {a₁ b₁ a₂ b₂ : 𝓞 K}
    (hb₁ : ¬ (hζ.toInteger - 1) ∣ b₁)
    (hb₂ : ¬ (hζ.toInteger - 1) ∣ b₂)
    (hspan₁ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₁ / b₁ : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η₁ /
          aEtaZeroDvdPPow hp hζ e hy)
    (hspan₂ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₂ / b₂ : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η₂ /
          aEtaZeroDvdPPow hp hζ e hy) :
    ((η₂ : 𝓞 K) - (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) *
        (associated_eta_zero_unit_of_spanSingleton
          hp hζ e hy hz η₁ hb₁ hspan₁ : 𝓞 K) *
        (a₁ * b₂) ^ p +
      ((zetaSubOneDvdRoot hp hζ e hy : 𝓞 K) - (η₁ : 𝓞 K)) *
        (associated_eta_zero_unit_of_spanSingleton
          hp hζ e hy hz η₂ hb₂ hspan₂ : 𝓞 K) *
        (a₂ * b₁) ^ p =
      ((η₂ : 𝓞 K) - (η₁ : 𝓞 K)) *
        ((hζ.toInteger - 1) ^ m * (b₁ * b₂)) ^ p := by
  rw [← mul_right_inj' (x_plus_y_mul_ne_zero hp hζ e hz
    (zetaSubOneDvdRoot hp hζ e hy)), mul_add]
  simp_rw [mul_left_comm (x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)),
    mul_pow, mul_assoc,
    mul_left_comm ((η₂ : 𝓞 K) - (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)),
    mul_left_comm ((zetaSubOneDvdRoot hp hζ e hy : 𝓞 K) - (η₁ : 𝓞 K)),
    ← mul_assoc,
    associated_eta_zero_unit_spec_of_spanSingleton hp hζ e hy hz,
    mul_assoc,
    ← mul_left_comm ((η₂ : 𝓞 K) - (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)),
    ← mul_left_comm ((zetaSubOneDvdRoot hp hζ e hy : 𝓞 K) - (η₁ : 𝓞 K)),
    pow_mul, ← mul_pow, mul_comm b₂, ← mul_assoc]
  rw [← add_mul]
  congr 1
  ring

include hp hy e hz in
/-- **`exists_solution` from two explicit anchored quotient generators.**

This is the smallest already-formalized algebraic payload of the case-II
descent: two concrete quotients `𝔞η₁ / 𝔞₀` and `𝔞η₂ / 𝔞₀`, together with
nondivisible generators, give the next six-unit equation. -/
theorem exists_solution_of_etaZeroSpanSingletons
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K))
    (hη₁ : η₁ ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη₂ : η₂ ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη : η₂ ≠ η₁)
    {a₁ b₁ a₂ b₂ : 𝓞 K}
    (ha₁ : ¬ (hζ.toInteger - 1) ∣ a₁)
    (hb₁ : ¬ (hζ.toInteger - 1) ∣ b₁)
    (ha₂ : ¬ (hζ.toInteger - 1) ∣ a₂)
    (hb₂ : ¬ (hζ.toInteger - 1) ∣ b₂)
    (hspan₁ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₁ / b₁ : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η₁ /
          aEtaZeroDvdPPow hp hζ e hy)
    (hspan₂ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₂ / b₂ : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η₂ /
          aEtaZeroDvdPPow hp hζ e hy) :
    ∃ (x' y' z' : 𝓞 K) (ε₁ ε₂ ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ x' ∧
      ¬ (hζ.toInteger - 1) ∣ y' ∧
      ¬ (hζ.toInteger - 1) ∣ z' ∧
      (ε₁ : 𝓞 K) * x' ^ p + (ε₂ : 𝓞 K) * y' ^ p =
        (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p := by
  set η₀ := zetaSubOneDvdRoot hp hζ e hy
  obtain ⟨u₁, hu₁⟩ :=
    hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out
    η₂.prop (η₀ : _).prop (Subtype.coe_injective.ne_iff.mpr hη₂)
  obtain ⟨u₂, hu₂⟩ :=
    hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out
    (η₀ : _).prop η₁.prop (Subtype.coe_injective.ne_iff.mpr hη₁.symm)
  obtain ⟨u₃, hu₃⟩ :=
    hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out
    η₂.prop (η₁ : _).prop (Subtype.coe_injective.ne_iff.mpr hη)
  have := formula_of_etaZeroSpanSingletons
    hp hζ e hy hz η₁ η₂ hb₁ hb₂ hspan₁ hspan₂
  rw [← hu₁, ← hu₂, ← hu₃,
    mul_assoc _ (u₁ : 𝓞 K), mul_assoc _ (u₂ : 𝓞 K), mul_assoc _ (u₃ : 𝓞 K),
    mul_assoc (hζ.toInteger - 1), mul_assoc (hζ.toInteger - 1), ← mul_add,
    mul_right_inj' (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt),
    ← Units.val_mul, ← Units.val_mul] at this
  refine ⟨_, _, _, _, _, _, ?_, ?_, ?_, this⟩
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul ha₁ hb₂
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul ha₂ hb₁
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul hb₁ hb₂

omit hpri [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
private theorem caseII_solution_lower_of_unit_quotient_pow
    {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ}
    (hy' : ¬ (hζ.toInteger - 1) ∣ y') (hz' : ¬ (hζ.toInteger - 1) ∣ z')
    (e' : (ε₁ : 𝓞 K) * x' ^ p + (ε₂ : 𝓞 K) * y' ^ p =
      (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p)
    (hpow : ∃ ε' : (𝓞 K)ˣ, ε₁ / ε₂ = ε' ^ p) :
    ∃ (x'' y'' z'' : 𝓞 K) (ε₄ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ y'' ∧ ¬ (hζ.toInteger - 1) ∣ z'' ∧
      x'' ^ p + y'' ^ p = (ε₄ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z'') ^ p := by
  obtain ⟨ε', hε'⟩ := hpow
  refine ⟨ε' * x', y', z', ε₃ / ε₂, hy', hz', ?_⟩
  rwa [mul_pow, ← Units.val_pow_eq_pow_val, ← hε', ← mul_right_inj' ε₂.isUnit.ne_zero,
    mul_add, ← mul_assoc, ← Units.val_mul, mul_div_cancel,
    ← mul_assoc, ← Units.val_mul, mul_div_cancel]

include hp hy e hz in
/-- **`exists_solution'` from two anchored quotient generators and a
datum-specific unit-power discharge.**

This is the algebraic core of the adapted Kummer step: after
`exists_solution_of_etaZeroSpanSingletons` constructs the descent equation
with units `ε₁`, `ε₂`, `ε₃`, it is enough to prove the specific unit
`ε₁ / ε₂` is a `p`-th power.  The broader
`AdaptedKummersLemmaOnSpecific` predicate is one way to prove that unit-power
fact, but it is not needed by the remaining algebra. -/
theorem exists_solution'_of_etaZeroSpanSingletons_and_unitPower
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K))
    (hη₁ : η₁ ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη₂ : η₂ ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη : η₂ ≠ η₁)
    {a₁ b₁ a₂ b₂ : 𝓞 K}
    (ha₁ : ¬ (hζ.toInteger - 1) ∣ a₁)
    (hb₁ : ¬ (hζ.toInteger - 1) ∣ b₁)
    (ha₂ : ¬ (hζ.toInteger - 1) ∣ a₂)
    (hb₂ : ¬ (hζ.toInteger - 1) ∣ b₂)
    (hspan₁ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₁ / b₁ : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η₁ /
          aEtaZeroDvdPPow hp hζ e hy)
    (hspan₂ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₂ / b₂ : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η₂ /
          aEtaZeroDvdPPow hp hζ e hy)
    (h_unit :
      ∀ {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ},
        ¬ (hζ.toInteger - 1) ∣ x' →
        ¬ (hζ.toInteger - 1) ∣ y' →
        ¬ (hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 K) * x' ^ p + (ε₂ : 𝓞 K) * y' ^ p =
          (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p) →
        ∃ ε' : (𝓞 K)ˣ, ε₁ / ε₂ = ε' ^ p) :
    ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ y' ∧ ¬ (hζ.toInteger - 1) ∣ z' ∧
      x' ^ p + y' ^ p = (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p := by
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ :=
    exists_solution_of_etaZeroSpanSingletons
      hp hζ e hy hz η₁ η₂ hη₁ hη₂ hη
      ha₁ hb₁ ha₂ hb₂ hspan₁ hspan₂
  exact caseII_solution_lower_of_unit_quotient_pow hζ hy' hz' e' (h_unit hx' hy' hz' e')

include hp hy hz in
/-- **𝔞 η · (β) = 𝔞₀ · (α) (specific discharge).** Ideal-level
factorisation. Mirror of `a_mul_denom_eq_a_zero_mul_num_of_discharge`. -/
theorem a_mul_denom_eq_a_zero_mul_num_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    rootDivZetaSubOneDvdGcd hp hζ e hy η *
        Ideal.span
          {a_div_a_zero_denom_of_specific_discharge hp hζ e hy hz h_specific η hη} =
      aEtaZeroDvdPPow hp hζ e hy *
        Ideal.span
          {a_div_a_zero_num_of_specific_discharge hp hζ e hy hz h_specific η hη} :=
  a_mul_denom_eq_a_zero_mul_num_of_spanSingleton hp hζ e hy hz η
    (a_div_a_zero_denom_spec_of_specific_discharge hp hζ e hy hz h_specific η hη)
    (a_div_a_zero_eq_of_specific_discharge hp hζ e hy hz h_specific η hη)

include hp hy hz in
/-- **Associated identity (specific discharge).** Element-level
associate identity: `(x + y η₀) · α^p ~ (x + y η) · π^(m·p) · β^p`. -/
theorem associated_eta_zero_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    Associated ((x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) *
        a_div_a_zero_num_of_specific_discharge hp hζ e hy hz h_specific η hη ^ p)
      ((x + y * (η : 𝓞 K)) * (hζ.toInteger - 1) ^ (m * p) *
        a_div_a_zero_denom_of_specific_discharge hp hζ e hy hz h_specific η hη ^ p) :=
  associated_eta_zero_of_spanSingleton hp hζ e hy hz η
    (a_div_a_zero_denom_spec_of_specific_discharge hp hζ e hy hz h_specific η hη)
    (a_div_a_zero_eq_of_specific_discharge hp hζ e hy hz h_specific η hη)

/-- **Unit ε η witnessing associate identity (specific discharge).** -/
noncomputable
def associated_eta_zero_unit_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) : (𝓞 K)ˣ :=
  (associated_eta_zero_of_specific_discharge hp hζ e hy hz h_specific η hη).choose

/-- **ε η spec (specific discharge).** -/
theorem associated_eta_zero_unit_spec_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    (associated_eta_zero_unit_of_specific_discharge
      hp hζ e hy hz h_specific η hη : 𝓞 K) *
        (x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) *
        a_div_a_zero_num_of_specific_discharge hp hζ e hy hz h_specific η hη ^ p =
      (x + y * (η : 𝓞 K)) * (hζ.toInteger - 1) ^ (m * p) *
        a_div_a_zero_denom_of_specific_discharge hp hζ e hy hz h_specific η hη ^ p := by
  rw [mul_assoc,
    mul_comm (associated_eta_zero_unit_of_specific_discharge
      hp hζ e hy hz h_specific η hη : 𝓞 K)]
  exact (associated_eta_zero_of_specific_discharge
    hp hζ e hy hz h_specific η hη).choose_spec

include hp hy hz in
/-- **case-II `formula` from specific discharge.** Mirror of
`formula_of_discharge` using the `_of_specific_discharge` chain. -/
theorem formula_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K))
    (hη₁ : η₁ ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη₂ : η₂ ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ((η₂ : 𝓞 K) - (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) *
        (associated_eta_zero_unit_of_specific_discharge
          hp hζ e hy hz h_specific η₁ hη₁ : 𝓞 K) *
        (a_div_a_zero_num_of_specific_discharge hp hζ e hy hz h_specific η₁ hη₁ *
         a_div_a_zero_denom_of_specific_discharge hp hζ e hy hz h_specific η₂ hη₂) ^ p +
      ((zetaSubOneDvdRoot hp hζ e hy : 𝓞 K) - (η₁ : 𝓞 K)) *
        (associated_eta_zero_unit_of_specific_discharge
          hp hζ e hy hz h_specific η₂ hη₂ : 𝓞 K) *
        (a_div_a_zero_num_of_specific_discharge hp hζ e hy hz h_specific η₂ hη₂ *
         a_div_a_zero_denom_of_specific_discharge hp hζ e hy hz h_specific η₁ hη₁) ^ p =
      ((η₂ : 𝓞 K) - (η₁ : 𝓞 K)) *
        ((hζ.toInteger - 1) ^ m *
          (a_div_a_zero_denom_of_specific_discharge hp hζ e hy hz h_specific η₁ hη₁ *
            a_div_a_zero_denom_of_specific_discharge
              hp hζ e hy hz h_specific η₂ hη₂)) ^ p :=
  formula_of_etaZeroSpanSingletons hp hζ e hy hz η₁ η₂
    (a_div_a_zero_denom_spec_of_specific_discharge hp hζ e hy hz h_specific η₁ hη₁)
    (a_div_a_zero_denom_spec_of_specific_discharge hp hζ e hy hz h_specific η₂ hη₂)
    (a_div_a_zero_eq_of_specific_discharge hp hζ e hy hz h_specific η₁ hη₁)
    (a_div_a_zero_eq_of_specific_discharge hp hζ e hy hz h_specific η₂ hη₂)

omit [IsCyclotomicExtension {p} ℚ K] in
include hp hζ in
private theorem exists_adjacent_ne_nthRoots (η₀ : nthRootsFinset p (1 : 𝓞 K)) :
    ∃ η₁ η₂ : nthRootsFinset p (1 : 𝓞 K), η₁ ≠ η₀ ∧ η₂ ≠ η₀ ∧ η₂ ≠ η₁ := by
  have h₁ := mul_mem_nthRootsFinset (η₀ : _).prop
    (hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset hpri.out.pos)
  rw [one_mul] at h₁
  let η₁ : nthRootsFinset p (1 : 𝓞 K) := ⟨(η₀ : 𝓞 K) * hζ.toInteger, h₁⟩
  have h₂ := mul_mem_nthRootsFinset (η₁ : _).prop
    (hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset hpri.out.pos)
  rw [one_mul] at h₂
  refine ⟨η₁, ⟨(η₀ : 𝓞 K) * hζ.toInteger * hζ.toInteger, h₂⟩, ?_, ?_, ?_⟩
  · rw [← Subtype.coe_injective.ne_iff]
    change ((η₀ : 𝓞 K) * hζ.toInteger : 𝓞 K) ≠ (η₀ : 𝓞 K)
    rw [Ne, mul_right_eq_self₀, not_or]
    exact ⟨hζ.toInteger_isPrimitiveRoot.ne_one hpri.out.one_lt,
      ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop⟩
  · rw [← Subtype.coe_injective.ne_iff]
    change ((η₀ : 𝓞 K) * hζ.toInteger * hζ.toInteger : 𝓞 K) ≠ (η₀ : 𝓞 K)
    rw [Ne, mul_assoc, ← pow_two, mul_right_eq_self₀, not_or]
    exact ⟨hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega)
      (hpri.out.two_le.lt_or_eq.resolve_right hp.symm),
      ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop⟩
  · rw [← Subtype.coe_injective.ne_iff]
    change ((η₀ : 𝓞 K) * hζ.toInteger * hζ.toInteger : 𝓞 K) ≠ (η₀ : 𝓞 K) * hζ.toInteger
    rw [Ne, mul_right_eq_self₀, not_or]
    exact ⟨hζ.toInteger_isPrimitiveRoot.ne_one hpri.out.one_lt,
      mul_ne_zero (ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop)
      (hζ.toInteger_isPrimitiveRoot.ne_zero hpri.out.ne_zero)⟩

include hp hy e hz in
/-- **`exists_solution` from specific discharge.** Mirror of
`exists_solution_of_discharge` using the `_of_specific_discharge`
chain. -/
theorem exists_solution_of_specific_discharge
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K) :
    ∃ (x' y' z' : 𝓞 K) (ε₁ ε₂ ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ x' ∧
      ¬ (hζ.toInteger - 1) ∣ y' ∧
      ¬ (hζ.toInteger - 1) ∣ z' ∧
      (ε₁ : 𝓞 K) * x' ^ p + (ε₂ : 𝓞 K) * y' ^ p =
        (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p := by
  obtain ⟨η₁, η₂, hη₁, hη₂, hη⟩ :=
    exists_adjacent_ne_nthRoots hp hζ (zetaSubOneDvdRoot hp hζ e hy)
  exact exists_solution_of_etaZeroSpanSingletons hp hζ e hy hz η₁ η₂ hη₁ hη₂ hη
    (a_div_a_zero_num_spec_of_specific_discharge hp hζ e hy hz h_specific η₁ hη₁)
    (a_div_a_zero_denom_spec_of_specific_discharge hp hζ e hy hz h_specific η₁ hη₁)
    (a_div_a_zero_num_spec_of_specific_discharge hp hζ e hy hz h_specific η₂ hη₂)
    (a_div_a_zero_denom_spec_of_specific_discharge hp hζ e hy hz h_specific η₂ hη₂)
    (a_div_a_zero_eq_of_specific_discharge hp hζ e hy hz h_specific η₁ hη₁)
    (a_div_a_zero_eq_of_specific_discharge hp hζ e hy hz h_specific η₂ hη₂)

include hp hy hz in
/-- **`exists_not_dvd_spanSingleton_eq_a_div_a_zero` from fixed-data
principalization against `η₀`.** This is the consumer-facing form of the
narrowed case-II principalization target. -/
theorem exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ∃ a b : 𝓞 K, ¬ (hζ.toInteger - 1) ∣ a ∧ ¬ (hζ.toInteger - 1) ∣ b ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / b : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η /
        aEtaZeroDvdPPow hp hζ e hy :=
  exists_not_dvd_spanSingleton_eq hζ.zeta_sub_one_prime'
    _ _ ((p_dvd_a_iff hp hζ e hy η).not.mpr hη) (not_p_div_a_zero hp hζ e hy hz)
      (h_principal η hη)

/-- **α numerator from fixed-data `η₀` principalization.** -/
noncomputable
def a_div_a_zero_num_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) : 𝓞 K :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_etaZeroPrincipalization
    hp hζ e hy hz h_principal η hη).choose

/-- **β denominator from fixed-data `η₀` principalization.** -/
noncomputable
def a_div_a_zero_denom_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) : 𝓞 K :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_etaZeroPrincipalization
    hp hζ e hy hz h_principal η hη).choose_spec.choose

/-- **α numerator π-non-divisibility (fixed-data `η₀` principalization).** -/
theorem a_div_a_zero_num_spec_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ¬ (hζ.toInteger - 1) ∣
      a_div_a_zero_num_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_etaZeroPrincipalization
    hp hζ e hy hz h_principal η hη).choose_spec.choose_spec.1

/-- **β denominator π-non-divisibility (fixed-data `η₀` principalization).** -/
theorem a_div_a_zero_denom_spec_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ¬ (hζ.toInteger - 1) ∣
      a_div_a_zero_denom_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_etaZeroPrincipalization
    hp hζ e hy hz h_principal η hη).choose_spec.choose_spec.2.1

/-- **α/β = 𝔞 η / 𝔞₀ identity (fixed-data `η₀` principalization).** -/
theorem a_div_a_zero_eq_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (a_div_a_zero_num_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη /
         a_div_a_zero_denom_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη
          : K) =
      rootDivZetaSubOneDvdGcd hp hζ e hy η /
        aEtaZeroDvdPPow hp hζ e hy :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_etaZeroPrincipalization
    hp hζ e hy hz h_principal η hη).choose_spec.choose_spec.2.2

include hp hy hz in
/-- **𝔞 η · (β) = 𝔞₀ · (α) (fixed-data `η₀` principalization).** -/
theorem a_mul_denom_eq_a_zero_mul_num_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    rootDivZetaSubOneDvdGcd hp hζ e hy η *
        Ideal.span
          {a_div_a_zero_denom_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη} =
      aEtaZeroDvdPPow hp hζ e hy *
        Ideal.span
          {a_div_a_zero_num_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη} :=
  a_mul_denom_eq_a_zero_mul_num_of_spanSingleton hp hζ e hy hz η
    (a_div_a_zero_denom_spec_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη)
    (a_div_a_zero_eq_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη)

include hp hy hz in
/-- **Associated identity (fixed-data `η₀` principalization).** -/
theorem associated_eta_zero_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    Associated ((x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) *
        a_div_a_zero_num_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη ^ p)
      ((x + y * (η : 𝓞 K)) * (hζ.toInteger - 1) ^ (m * p) *
        a_div_a_zero_denom_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη ^ p) :=
  associated_eta_zero_of_spanSingleton hp hζ e hy hz η
    (a_div_a_zero_denom_spec_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη)
    (a_div_a_zero_eq_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη)

/-- **Associated-unit witness (fixed-data `η₀` principalization).** -/
noncomputable
def associated_eta_zero_unit_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) : (𝓞 K)ˣ :=
  (associated_eta_zero_of_etaZeroPrincipalization
    hp hζ e hy hz h_principal η hη).choose

/-- **Associated-unit specification (fixed-data `η₀` principalization).** -/
theorem associated_eta_zero_unit_spec_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    (associated_eta_zero_unit_of_etaZeroPrincipalization
        hp hζ e hy hz h_principal η hη : 𝓞 K) *
        (x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) *
        a_div_a_zero_num_of_etaZeroPrincipalization hp hζ e hy hz h_principal η hη ^ p =
      (x + y * (η : 𝓞 K)) * (hζ.toInteger - 1) ^ (m * p) *
        a_div_a_zero_denom_of_etaZeroPrincipalization
          hp hζ e hy hz h_principal η hη ^ p := by
  rw [mul_assoc,
    mul_comm (associated_eta_zero_unit_of_etaZeroPrincipalization
      hp hζ e hy hz h_principal η hη : 𝓞 K)]
  exact (associated_eta_zero_of_etaZeroPrincipalization
    hp hζ e hy hz h_principal η hη).choose_spec

include hp hy hz in
/-- **Case-II formula from fixed-data `η₀` principalization.** -/
theorem formula_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy)
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K))
    (hη₁ : η₁ ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη₂ : η₂ ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ((η₂ : 𝓞 K) - (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) *
        (associated_eta_zero_unit_of_etaZeroPrincipalization
          hp hζ e hy hz h_principal η₁ hη₁ : 𝓞 K) *
        (a_div_a_zero_num_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₁ hη₁ *
         a_div_a_zero_denom_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₂ hη₂) ^ p +
      ((zetaSubOneDvdRoot hp hζ e hy : 𝓞 K) - (η₁ : 𝓞 K)) *
        (associated_eta_zero_unit_of_etaZeroPrincipalization
          hp hζ e hy hz h_principal η₂ hη₂ : 𝓞 K) *
        (a_div_a_zero_num_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₂ hη₂ *
         a_div_a_zero_denom_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₁ hη₁) ^ p =
      ((η₂ : 𝓞 K) - (η₁ : 𝓞 K)) *
        ((hζ.toInteger - 1) ^ m *
          (a_div_a_zero_denom_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₁ hη₁ *
           a_div_a_zero_denom_of_etaZeroPrincipalization
            hp hζ e hy hz h_principal η₂ hη₂)) ^ p :=
  formula_of_etaZeroSpanSingletons hp hζ e hy hz η₁ η₂
    (a_div_a_zero_denom_spec_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₁ hη₁)
    (a_div_a_zero_denom_spec_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₂ hη₂)
    (a_div_a_zero_eq_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₁ hη₁)
    (a_div_a_zero_eq_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₂ hη₂)

include hp hy e hz in
/-- **`exists_solution` from fixed-data principalization against `η₀`.** -/
theorem exists_solution_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy) :
    ∃ (x' y' z' : 𝓞 K) (ε₁ ε₂ ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ x' ∧
      ¬ (hζ.toInteger - 1) ∣ y' ∧
      ¬ (hζ.toInteger - 1) ∣ z' ∧
      (ε₁ : 𝓞 K) * x' ^ p + (ε₂ : 𝓞 K) * y' ^ p =
        (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p := by
  obtain ⟨η₁, η₂, hη₁, hη₂, hη⟩ :=
    exists_adjacent_ne_nthRoots hp hζ (zetaSubOneDvdRoot hp hζ e hy)
  exact exists_solution_of_etaZeroSpanSingletons hp hζ e hy hz η₁ η₂ hη₁ hη₂ hη
    (a_div_a_zero_num_spec_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₁ hη₁)
    (a_div_a_zero_denom_spec_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₁ hη₁)
    (a_div_a_zero_num_spec_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₂ hη₂)
    (a_div_a_zero_denom_spec_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₂ hη₂)
    (a_div_a_zero_eq_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₁ hη₁)
    (a_div_a_zero_eq_of_etaZeroPrincipalization hp hζ e hy hz h_principal η₂ hη₂)

/-- **Tightened adapted Kummer's lemma on case-II descent structure**.

For every case-II descent setup `(hζ, m, u, x', y', z', ε', e_descent)`
with `(ζ-1) ∤ x'`, `(ζ-1) ∤ y'`, `(ζ-1) ∤ z'`, and the descent equation
`u · x'^p + y'^p = ε' · ((ζ-1)^m · z')^p`, if `u` is congruent to an
integer modulo `p`, then `u` is a `p`-th power in `(𝓞 K)ˣ`.

This is the **case-II-specific form** of the adapted Kummer's lemma.
The general `AdaptedKummersLemma p K` (universal over arbitrary units)
is too strong at irregular `p` — it is mathematically false there; this
tightening restricts the quantification to units arising in the case-II
descent chain via the explicit descent equation (the form arising in
flt-regular's case-II inductive descent step
`exists_solution'_of_discharges`).

The restriction makes the predicate fillable for irregular primes (like
`p = 37`) under `¬ p ∣ h⁺` + the second-order Bernoulli condition
(Washington Theorem 9.4 content): units arising in the case-II descent
are genuinely constrained (the Diophantine equation rules out the
`Cl(K)⁻[p]` counterexamples that defeat the universal form).

Ticket: C2-1 (v2, descent-equation form) in
`.mathlib-quality/flt37-final-phase-tickets.md`. -/
def AdaptedKummersLemmaOnSpecific : Prop :=
  ∀ {ζ_loc : K} (hζ_loc : IsPrimitiveRoot ζ_loc p) {m_loc : ℕ}
    (u : (𝓞 K)ˣ) {x' y' z' : 𝓞 K} {ε' : (𝓞 K)ˣ},
    ¬ (hζ_loc.toInteger - 1 : 𝓞 K) ∣ x' →
    ¬ (hζ_loc.toInteger - 1 : 𝓞 K) ∣ y' →
    ¬ (hζ_loc.toInteger - 1 : 𝓞 K) ∣ z' →
    ((u : 𝓞 K) * x' ^ p + y' ^ p =
      (ε' : 𝓞 K) * ((hζ_loc.toInteger - 1) ^ m_loc * z') ^ p) →
    (∃ n : ℤ, ((p : ℕ) : 𝓞 K) ∣ ((u : 𝓞 K) - (n : 𝓞 K))) →
    ∃ v : (𝓞 K)ˣ, u = v ^ p

include hp hy e hz in
private theorem caseII_unit_quotient_pow_of_adaptedKummer
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := p) (K := K))
    {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ}
    (hx' : ¬ (hζ.toInteger - 1) ∣ x') (hy' : ¬ (hζ.toInteger - 1) ∣ y')
    (hz' : ¬ (hζ.toInteger - 1) ∣ z')
    (e' : (ε₁ : 𝓞 K) * x' ^ p + (ε₂ : 𝓞 K) * y' ^ p =
      (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p) :
    ∃ ε'' : (𝓞 K)ˣ, ε₁ / ε₂ = ε'' ^ p := by
  have e_descent : ((ε₁ / ε₂ : (𝓞 K)ˣ) : 𝓞 K) * x' ^ p + y' ^ p =
      ((ε₃ / ε₂ : (𝓞 K)ˣ) : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p := by
    rw [← mul_right_inj' ε₂.isUnit.ne_zero, mul_add, ← mul_assoc, ← Units.val_mul,
        mul_div_cancel, ← mul_assoc, ← Units.val_mul, mul_div_cancel]
    exact e'
  apply h_kummer hζ (ε₁ / ε₂) hx' hy' hz' e_descent
  have hp_le : p - 1 ≤ m * p := (Nat.sub_le _ _).trans
    ((le_of_eq (one_mul _).symm).trans (Nat.mul_le_mul_right p (one_le_m hp hζ e hy hz)))
  rw [mul_pow, ← pow_mul, mul_comm (ε₃ : 𝓞 K), mul_assoc, ← Nat.sub_add_cancel hp_le,
    add_comm _ (p - 1), pow_add, mul_assoc] at e'
  apply_fun Ideal.Quotient.mk (Ideal.span <| singleton ((p : ℕ) : 𝓞 K)) at e'
  rw [map_mul, (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr
    (associated_zeta_sub_one_pow_prime hζ).symm.dvd, zero_mul,
    Ideal.Quotient.eq_zero_iff_dvd] at e'
  obtain ⟨a, ha⟩ := exists_solution'_aux hp hζ hx' e'
  obtain ⟨b, hb⟩ := exists_dvd_pow_sub_Int_pow hp a
  have hcong := dvd_add ha hb
  rw [sub_add_sub_cancel, ← Int.cast_pow] at hcong
  exact ⟨b ^ p, hcong⟩

include hp hy e hz in
/-- **`exists_solution'` from two explicit anchored quotient generators.**

This composes `exists_solution_of_etaZeroSpanSingletons` with the tightened
case-II Kummer step, lowering the exponent from `m + 1` to `m`. -/
theorem exists_solution'_of_etaZeroSpanSingletons
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K))
    (hη₁ : η₁ ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη₂ : η₂ ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη : η₂ ≠ η₁)
    {a₁ b₁ a₂ b₂ : 𝓞 K}
    (ha₁ : ¬ (hζ.toInteger - 1) ∣ a₁)
    (hb₁ : ¬ (hζ.toInteger - 1) ∣ b₁)
    (ha₂ : ¬ (hζ.toInteger - 1) ∣ a₂)
    (hb₂ : ¬ (hζ.toInteger - 1) ∣ b₂)
    (hspan₁ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₁ / b₁ : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η₁ /
          aEtaZeroDvdPPow hp hζ e hy)
    (hspan₂ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₂ / b₂ : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η₂ /
          aEtaZeroDvdPPow hp hζ e hy)
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := p) (K := K)) :
    ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ y' ∧ ¬ (hζ.toInteger - 1) ∣ z' ∧
      x' ^ p + y' ^ p = (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p := by
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ :=
    exists_solution_of_etaZeroSpanSingletons
      hp hζ e hy hz η₁ η₂ hη₁ hη₂ hη
      ha₁ hb₁ ha₂ hb₂ hspan₁ hspan₂
  exact caseII_solution_lower_of_unit_quotient_pow hζ hy' hz' e'
    (caseII_unit_quotient_pow_of_adaptedKummer hp hζ e hy hz h_kummer hx' hy' hz' e')

/-- **Realness of units congruent to integers modulo `p`.**

If a unit `u` is congruent to an integer modulo `p`, then its root-of-unity
factor in the standard Kummer unit decomposition is trivial, so `u` descends
from the maximal real subfield.  The case-II descent data are included in the
signature so this lemma can be used directly inside the specific Kummer step. -/
theorem caseII_discharge_unit_is_real
    (hp_two : 2 < p)
    {ζ_loc : K} (hζ_loc : IsPrimitiveRoot ζ_loc p) {m_loc : ℕ}
    (u : (𝓞 K)ˣ) {x' y' z' : 𝓞 K} {ε' : (𝓞 K)ˣ}
    (_hx' : ¬ (hζ_loc.toInteger - 1 : 𝓞 K) ∣ x')
    (_hy' : ¬ (hζ_loc.toInteger - 1 : 𝓞 K) ∣ y')
    (_hz' : ¬ (hζ_loc.toInteger - 1 : 𝓞 K) ∣ z')
    (_he : (u : 𝓞 K) * x' ^ p + y' ^ p =
        (ε' : 𝓞 K) * ((hζ_loc.toInteger - 1) ^ m_loc * z') ^ p)
    (hu_cong : ∃ n : ℤ, ((p : ℕ) : 𝓞 K) ∣ ((u : 𝓞 K) - (n : 𝓞 K))) :
    ∃ u_real : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (u_real : 𝓞 (NumberField.maximalRealSubfield K)) =
      (u : 𝓞 K) := by
  haveI : NumberField.IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_two.ne'
  obtain ⟨n, hn⟩ := hu_cong
  suffices h_sigma_u_eq_u : unitsComplexConj K u = u from
    (mem_realUnits_iff K u).mp ((unitsComplexConj_eq_self_iff K u).mp h_sigma_u_eq_u)
  apply Units.ext
  have h_conj_hn : ((p : ℕ) : 𝓞 K) ∣
      (ringOfIntegersComplexConj K (u : 𝓞 K) - (n : 𝓞 K)) := by
    obtain ⟨w, hw⟩ := hn
    refine ⟨ringOfIntegersComplexConj K w, ?_⟩
    have h := congr_arg (ringOfIntegersComplexConj K) hw
    rwa [map_sub, map_intCast, map_mul, map_natCast] at h
  have h_p_dvd_diff : ((p : ℕ) : 𝓞 K) ∣
      (ringOfIntegersComplexConj K (u : 𝓞 K) - (u : 𝓞 K)) := by
    simpa [sub_sub_sub_cancel_right] using h_conj_hn.sub hn
  obtain ⟨m, hm⟩ := unit_inv_conj_is_root_of_unity (zeta_spec p ℚ K) u hp_two
  set zU : (𝓞 K)ˣ :=
    ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hpri.out.ne_zero).unit
  have h_zU_pow_p : zU ^ p = 1 :=
    ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit_unit hpri.out.ne_zero).pow_eq_one
  have h_u_eq : u = zU ^ (2 * m) * unitsComplexConj K u := by
    rw [← pow_mul, mul_comm m 2] at hm
    rw [← hm, mul_assoc, inv_mul_cancel, mul_one]
  have h_zU_prod_one : zU ^ (2 * m * (p - 1)) * zU ^ (2 * m) = 1 := by
    rw [← pow_add, show 2 * m * (p - 1) + 2 * m = p * (2 * m) by
        conv_rhs => rw [show p = p - 1 + 1 from (Nat.sub_add_cancel hpri.out.one_le).symm]
        ring,
      pow_mul, h_zU_pow_p, one_pow]
  have h_sigma_eq : unitsComplexConj K u = zU ^ (2 * m * (p - 1)) * u := by
    conv_rhs => rw [h_u_eq, ← mul_assoc, h_zU_prod_one, one_mul]
  have h_diff_eq : ringOfIntegersComplexConj K (u : 𝓞 K) - (u : 𝓞 K) =
      (u : 𝓞 K) * ((zU : 𝓞 K) ^ (2 * m * (p - 1)) - 1) := by
    change (unitsComplexConj K u : 𝓞 K) - (u : 𝓞 K) = _
    rw [h_sigma_eq, Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  rw [h_diff_eq] at h_p_dvd_diff
  have h_zU_pow_eq_one : (zU : 𝓞 K) ^ (2 * m * (p - 1)) = 1 :=
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.p_dvd_zeta_pow_sub_one_implies_eq_one
      (p := p) (K := K) (zeta_spec p ℚ K).toInteger_isPrimitiveRoot hp_two _
      (Units.dvd_mul_left.mp h_p_dvd_diff)
  change ringOfIntegersComplexConj K (u : 𝓞 K) = (u : 𝓞 K)
  exact sub_eq_zero.mp (by rw [h_diff_eq, h_zU_pow_eq_one, sub_self, mul_zero])

omit hpri [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **General → tightened-specific (Kummer side).** The general
`AdaptedKummersLemma p K` (universal over all units) implies the
tightened `AdaptedKummersLemmaOnSpecific` by ignoring the
descent-equation context and applying the general predicate at the
input unit `u` with its congruence. -/
theorem adaptedKummersLemmaOnSpecific_of_general (h : AdaptedKummersLemma p K) :
    AdaptedKummersLemmaOnSpecific (p := p) (K := K) := by
  intro _ _ _ u _ _ _ _ _ _ _ _ hcong
  exact h u hcong

/-- **Regular-prime fill of the tightened `AdaptedKummersLemmaOnSpecific`.**
Under regularity (`p` coprime to `|Cl(K)|`) and `p ≠ 2`, the tightened
OnSpecific predicate holds. Composition of `adaptedKummersLemma_of_regular`
(flt-regular's regularity-based Kummer's lemma) with
`adaptedKummersLemmaOnSpecific_of_general`. -/
theorem adaptedKummersLemmaOnSpecific_of_regular
    [Fintype (ClassGroup (𝓞 K))]
    [NumberField.IsCMField K]
    (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
    (hp_ne_two : p ≠ 2) :
    AdaptedKummersLemmaOnSpecific (p := p) (K := K) :=
  adaptedKummersLemmaOnSpecific_of_general
    (adaptedKummersLemma_of_regular p K hreg hp_ne_two)

include hp hy e hz in
/-- **`exists_solution'` from two specific discharges.** Mirror of
`exists_solution'_of_discharges` using the OnSpecific predicate (v2,
descent-equation form) for the Kummer step.

The descent: from `x^p + y^p = ε * ((ζ-1)^(m+1) * z)^p`, derive
`x'^p + y'^p = ε₃ * ((ζ-1)^m * z')^p` (multiplicity m instead of m+1)
under `CaseIIPrincipalDischargeOnSpecific` + `AdaptedKummersLemmaOnSpecific`. -/
theorem exists_solution'_of_specific_discharges
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := p) (K := K)) :
    ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ y' ∧ ¬ (hζ.toInteger - 1) ∣ z' ∧
      x' ^ p + y' ^ p = (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p := by
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ :=
    exists_solution_of_specific_discharge hp hζ e hy hz h_specific
  exact caseII_solution_lower_of_unit_quotient_pow hζ hy' hz' e'
    (caseII_unit_quotient_pow_of_adaptedKummer hp hζ e hy hz h_kummer hx' hy' hz' e')

include hp hy e hz in
/-- **`exists_solution'` from anchored principalization and specific Kummer.**

This is the same descent step as `exists_solution'_of_specific_discharges`, but
it consumes only the global provider for principalizations `𝔞η / 𝔞₀`. -/
theorem exists_solution'_of_etaZeroPrincipalizationOnSpecific
    (h_principal : CaseIIPrincipalizationAgainstEtaZeroOnSpecific p K hp)
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := p) (K := K)) :
    ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ y' ∧ ¬ (hζ.toInteger - 1) ∣ z' ∧
      x' ^ p + y' ^ p = (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p := by
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ :=
    exists_solution_of_etaZeroPrincipalization hp hζ e hy hz (h_principal hζ e hy)
  exact caseII_solution_lower_of_unit_quotient_pow hζ hy' hz' e'
    (caseII_unit_quotient_pow_of_adaptedKummer hp hζ e hy hz h_kummer hx' hy' hz' e')

include hp hy e hz in
/-- **`exists_solution'` from fixed-data anchored principalization.**

This is the datum-local version of
`exists_solution'_of_etaZeroPrincipalizationOnSpecific`: the principalization
input is only for the current case-II equation, not a global provider for all
case-II data. -/
theorem exists_solution'_of_etaZeroPrincipalization
    (h_principal : CaseIIPrincipalizationAgainstEtaZero p K hp hζ e hy)
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := p) (K := K)) :
    ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ y' ∧ ¬ (hζ.toInteger - 1) ∣ z' ∧
      x' ^ p + y' ^ p = (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p := by
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ :=
    exists_solution_of_etaZeroPrincipalization hp hζ e hy hz h_principal
  exact caseII_solution_lower_of_unit_quotient_pow hζ hy' hz' e'
    (caseII_unit_quotient_pow_of_adaptedKummer hp hζ e hy hz h_kummer hx' hy' hz' e')

include hp in
/-- **`not_exists_solution` from specific discharges.** Mirror of
`not_exists_solution_of_discharges` using the OnSpecific predicates.
For all `n ≥ 1`, no solution exists to the case-II Kummer-form
equation `x^p + y^p = ε₃ * ((ζ-1)^n * z)^p` with `(ζ-1) ∤ y`, `(ζ-1) ∤ z`. -/
theorem not_exists_solution_of_specific_discharges
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := p) (K := K))
    {n : ℕ} (hn : 1 ≤ n) :
    ¬∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ y' ∧
      ¬ (hζ.toInteger - 1) ∣ z' ∧
      x' ^ p + y' ^ p = (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ n * z') ^ p := by
  induction n, hn using Nat.le_induction with
  | base =>
      rintro ⟨x'', y'', z'', ε₃'', hy'', hz'', e''⟩
      exact zero_lt_one.not_ge (one_le_m hp hζ e'' hy'' hz'')
  | succ m' _ IH =>
      rintro ⟨x'', y'', z'', ε₃'', hy'', hz'', e''⟩
      exact IH
        (exists_solution'_of_specific_discharges hp hζ e'' hy'' hz'' h_specific h_kummer)

include hp in
/-- **`not_exists_solution` from anchored principalization.** -/
theorem not_exists_solution_of_etaZeroPrincipalizationOnSpecific
    (h_principal : CaseIIPrincipalizationAgainstEtaZeroOnSpecific p K hp)
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := p) (K := K))
    {n : ℕ} (hn : 1 ≤ n) :
    ¬∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ y' ∧
      ¬ (hζ.toInteger - 1) ∣ z' ∧
      x' ^ p + y' ^ p = (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ n * z') ^ p := by
  induction n, hn using Nat.le_induction with
  | base =>
      rintro ⟨x'', y'', z'', ε₃'', hy'', hz'', e''⟩
      exact zero_lt_one.not_ge (one_le_m hp hζ e'' hy'' hz'')
  | succ m' _ IH =>
      rintro ⟨x'', y'', z'', ε₃'', hy'', hz'', e''⟩
      exact IH
        (exists_solution'_of_etaZeroPrincipalizationOnSpecific
          hp hζ e'' hy'' hz'' h_principal h_kummer)

private theorem exists_pos_pow_mul_of_zeta_sub_one_dvd {z' : 𝓞 K}
    (hdvd : (hζ.toInteger - 1) ∣ z') (hz_ne : z' ≠ 0) :
    ∃ n z'', 1 ≤ n ∧ ¬ (hζ.toInteger - 1) ∣ z'' ∧ z' = (hζ.toInteger - 1) ^ n * z'' := by
  letI : WfDvdMonoid (𝓞 K) := IsNoetherianRing.wfDvdMonoid
  obtain ⟨n, z'', hz_n, rfl⟩ :=
    WfDvdMonoid.max_power_factor hz_ne hζ.zeta_sub_one_prime'.irreducible
  refine ⟨n, z'', ?_, hz_n, rfl⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, one_mul] at hdvd
    exact absurd hdvd hz_n
  · exact hn

include hp in
/-- **`not_exists_solution'` from specific discharges.** Mirror of
`not_exists_solution'_of_discharges`. From `x^p + y^p = z^p` with
`(ζ-1) ∣ z`, derive a contradiction by extracting the multiplicity of
`(ζ-1)` in `z` and applying `not_exists_solution_of_specific_discharges`. -/
theorem not_exists_solution'_of_specific_discharges
    (h_specific : CaseIIPrincipalDischargeOnSpecific p K)
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := p) (K := K)) :
    ¬∃ (x y z : 𝓞 K),
      ¬ (hζ.toInteger - 1) ∣ y ∧
      (hζ.toInteger - 1) ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  rintro ⟨x', y', z', hy', hz', hz_ne', e'⟩
  obtain ⟨n, z'', hn, hz_n, rfl⟩ := exists_pos_pow_mul_of_zeta_sub_one_dvd hζ hz' hz_ne'
  refine not_exists_solution_of_specific_discharges hp hζ h_specific h_kummer hn
    ⟨x', y', z'', 1, hy', hz_n, ?_⟩
  rwa [Units.val_one, one_mul]

include hp in
/-- **`not_exists_solution'` from anchored principalization.** -/
theorem not_exists_solution'_of_etaZeroPrincipalizationOnSpecific
    (h_principal : CaseIIPrincipalizationAgainstEtaZeroOnSpecific p K hp)
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := p) (K := K)) :
    ¬∃ (x y z : 𝓞 K),
      ¬ (hζ.toInteger - 1) ∣ y ∧
      (hζ.toInteger - 1) ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  rintro ⟨x', y', z', hy', hz', hz_ne', e'⟩
  obtain ⟨n, z'', hn, hz_n, rfl⟩ := exists_pos_pow_mul_of_zeta_sub_one_dvd hζ hz' hz_ne'
  refine not_exists_solution_of_etaZeroPrincipalizationOnSpecific
      hp hζ h_principal h_kummer hn
    ⟨x', y', z'', 1, hy', hz_n, ?_⟩
  rwa [Units.val_one, one_mul]

end CaseII

end LehmerVandiver

end FLT37

end BernoulliRegular

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseII

private theorem caseII_not_dvd_snd_of_gcd_eq_one {p : ℕ} [hpri : Fact p.Prime]
    {x y z : ℤ} (hgcd : ({x, y, z} : Finset ℤ).gcd id = 1) (hz : (p : ℤ) ∣ z)
    (e : x ^ p + y ^ p = z ^ p) : ¬ (p : ℤ) ∣ y := by
  intro hy
  have h_dvd : (p : ℤ) ∣ x ^ p := by
    have := dvd_sub (dvd_pow hz hpri.out.ne_zero) (dvd_pow hy hpri.out.ne_zero)
    rwa [← e, add_sub_cancel_right] at this
  have hp_x : (p : ℤ) ∣ x :=
    (Nat.prime_iff_prime_int.mp hpri.out).dvd_of_dvd_pow h_dvd
  apply (Nat.prime_iff_prime_int.mp hpri.out).not_unit
  rw [isUnit_iff_dvd_one, ← hgcd]
  simp [dvd_gcd_iff, hz, hy, hp_x]

private theorem exists_caseII_Int_normal_form {p : ℕ} [hpri : Fact p.Prime] (hodd : p ≠ 2)
    {a b c : ℤ} (hprod : a * b * c ≠ 0) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcase : (p : ℤ) ∣ a * b * c) (e : a ^ p + b ^ p = c ^ p) :
    ∃ x y z : ℤ, ({x, y, z} : Finset ℤ).gcd id = 1 ∧ (p : ℤ) ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  simp only [ne_eq, mul_eq_zero, not_or] at hprod
  obtain ⟨⟨a0, b0⟩, c0⟩ := hprod
  have hodd' := Nat.Prime.odd_of_ne_two hpri.out hodd
  obtain hab | hc := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd hcase
  · obtain ha | hb := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd hab
    · refine ⟨b, -c, -a, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
          ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ a]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hodd'.neg_pow, ← e]
    · refine ⟨-c, a, -b, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
          ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ c]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hodd'.neg_pow, ← e]
  · exact ⟨a, b, c, hgcd, hc, c0, e⟩

set_option backward.isDefEq.respectTransparency false in
/-- **`not_exists_Int_solution` from specific discharges.** Mirror of
`not_exists_Int_solution_of_discharges`, parametric on the OnSpecific
predicates at `K = CyclotomicField p ℚ`. -/
theorem not_exists_Int_solution_of_specific_discharges
    {p : ℕ} [hpri : Fact p.Prime]
    (h_specific : CaseIIPrincipalDischargeOnSpecific p (CyclotomicField p ℚ))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := p) (K := CyclotomicField p ℚ))
    (hodd : p ≠ 2) :
    ¬∃ (x y z : ℤ),
      ¬ (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by
  haveI := CyclotomicField.isCyclotomicExtension p ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    ℚ (B := (CyclotomicField p ℚ)) (Set.mem_singleton p) hpri.1.ne_zero
  have h_dvd_iff := fun n ↦
    zeta_sub_one_dvd_Int_iff (K := CyclotomicField p ℚ) hζ (n := n)
  simp_rw [← h_dvd_iff]
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  refine not_exists_solution'_of_specific_discharges (K := CyclotomicField p ℚ)
    hodd hζ h_specific h_kummer
    ⟨x, y, z, hy, hz, ?_, ?_⟩
  · rwa [ne_eq, Int.cast_eq_zero]
  · simp_rw [← Int.cast_pow, ← Int.cast_add, e]

set_option backward.isDefEq.respectTransparency false in
/-- **`not_exists_Int_solution'` from specific discharges.** Mirror of
`not_exists_Int_solution'_of_discharges`. -/
theorem not_exists_Int_solution'_of_specific_discharges
    {p : ℕ} [hpri : Fact p.Prime]
    (h_specific : CaseIIPrincipalDischargeOnSpecific p (CyclotomicField p ℚ))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := p) (K := CyclotomicField p ℚ))
    (hodd : p ≠ 2) :
    ¬∃ (x y z : ℤ),
      ({x, y, z} : Finset ℤ).gcd id = 1 ∧ (p : ℤ) ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  rintro ⟨x, y, z, hgcd, hz, hz', e⟩
  exact not_exists_Int_solution_of_specific_discharges h_specific h_kummer hodd
    ⟨x, y, z, caseII_not_dvd_snd_of_gcd_eq_one hgcd hz e, hz, hz', e⟩

set_option backward.isDefEq.respectTransparency false in
/-- **`not_exists_Int_solution` from anchored principalization.** -/
theorem not_exists_Int_solution_of_etaZeroPrincipalizationOnSpecific
    {p : ℕ} [hpri : Fact p.Prime]
    (hodd : p ≠ 2)
    (h_principal : CaseIIPrincipalizationAgainstEtaZeroOnSpecific
      p (CyclotomicField p ℚ) hodd)
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := p) (K := CyclotomicField p ℚ)) :
    ¬∃ (x y z : ℤ),
      ¬ (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by
  haveI := CyclotomicField.isCyclotomicExtension p ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    ℚ (B := (CyclotomicField p ℚ)) (Set.mem_singleton p) hpri.1.ne_zero
  have h_dvd_iff := fun n ↦
    zeta_sub_one_dvd_Int_iff (K := CyclotomicField p ℚ) hζ (n := n)
  simp_rw [← h_dvd_iff]
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  refine not_exists_solution'_of_etaZeroPrincipalizationOnSpecific
    (K := CyclotomicField p ℚ) hodd hζ h_principal h_kummer
    ⟨x, y, z, hy, hz, ?_, ?_⟩
  · rwa [ne_eq, Int.cast_eq_zero]
  · simp_rw [← Int.cast_pow, ← Int.cast_add, e]

set_option backward.isDefEq.respectTransparency false in
/-- **`not_exists_Int_solution'` from anchored principalization.** -/
theorem not_exists_Int_solution'_of_etaZeroPrincipalizationOnSpecific
    {p : ℕ} [hpri : Fact p.Prime]
    (hodd : p ≠ 2)
    (h_principal : CaseIIPrincipalizationAgainstEtaZeroOnSpecific
      p (CyclotomicField p ℚ) hodd)
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := p) (K := CyclotomicField p ℚ)) :
    ¬∃ (x y z : ℤ),
      ({x, y, z} : Finset ℤ).gcd id = 1 ∧ (p : ℤ) ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  rintro ⟨x, y, z, hgcd, hz, hz', e⟩
  exact not_exists_Int_solution_of_etaZeroPrincipalizationOnSpecific
    hodd h_principal h_kummer
    ⟨x, y, z, caseII_not_dvd_snd_of_gcd_eq_one hgcd hz e, hz, hz', e⟩

set_option backward.isDefEq.respectTransparency false in
/-- **`caseII` from specific discharges (integer form).** Mirror of
`caseII_of_discharges`. -/
theorem caseII_of_specific_discharges
    {a b c : ℤ} {p : ℕ} [hpri : Fact p.Prime]
    (h_specific : CaseIIPrincipalDischargeOnSpecific p (CyclotomicField p ℚ))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := p) (K := CyclotomicField p ℚ))
    (hodd : p ≠ 2)
    (hprod : a * b * c ≠ 0) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcase : (p : ℤ) ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p := by
  intro e
  exact not_exists_Int_solution'_of_specific_discharges h_specific h_kummer hodd
    (exists_caseII_Int_normal_form hodd hprod hgcd hcase e)

set_option backward.isDefEq.respectTransparency false in
/-- **`caseII` from anchored principalization (integer form).** -/
theorem caseII_of_etaZeroPrincipalizationOnSpecific
    {a b c : ℤ} {p : ℕ} [hpri : Fact p.Prime]
    (hodd : p ≠ 2)
    (h_principal : CaseIIPrincipalizationAgainstEtaZeroOnSpecific
      p (CyclotomicField p ℚ) hodd)
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := p) (K := CyclotomicField p ℚ))
    (hprod : a * b * c ≠ 0) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcase : (p : ℤ) ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p := by
  intro e
  exact not_exists_Int_solution'_of_etaZeroPrincipalizationOnSpecific
    hodd h_principal h_kummer (exists_caseII_Int_normal_form hodd hprod hgcd hcase e)

set_option backward.isDefEq.respectTransparency false in
/-- **`caseIIBridge_of_specificDischarges`**: build a `CaseIIBridge p K i`
term parametric on the OnSpecific predicates
`CaseIIPrincipalDischargeOnSpecific` and `AdaptedKummersLemmaOnSpecific`
(the tightened forms suitable for irregular primes). -/
theorem caseIIBridge_of_specificDischarges
    {p : ℕ} [hpri : Fact p.Prime] (hodd : p ≠ 2) (i : ℕ)
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    (h_specific : CaseIIPrincipalDischargeOnSpecific p (CyclotomicField p ℚ))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := p) (K := CyclotomicField p ℚ)) :
    BernoulliRegular.CaseIIBridge p (CyclotomicField p ℚ) i where
  no_caseII_solution := fun _ _ _ _ _ hprod hgcd hcase =>
    caseII_of_specific_discharges h_specific h_kummer hodd hprod hgcd hcase

set_option backward.isDefEq.respectTransparency false in
/-- **`caseIIBridge_of_etaZeroPrincipalizationOnSpecific`**: case-II bridge
from anchored principalization and the tightened Kummer predicate. -/
theorem caseIIBridge_of_etaZeroPrincipalizationOnSpecific
    {p : ℕ} [hpri : Fact p.Prime] (hodd : p ≠ 2) (i : ℕ)
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    (h_principal : CaseIIPrincipalizationAgainstEtaZeroOnSpecific
      p (CyclotomicField p ℚ) hodd)
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := p) (K := CyclotomicField p ℚ)) :
    BernoulliRegular.CaseIIBridge p (CyclotomicField p ℚ) i where
  no_caseII_solution := fun _ _ _ _ _ hprod hgcd hcase =>
    caseII_of_etaZeroPrincipalizationOnSpecific hodd h_principal h_kummer
      hprod hgcd hcase

set_option backward.isDefEq.respectTransparency false in
/-- **Case-II bridge from anchored real-ideal models.**

This is the currently narrowest formal case-II principalization route: the
source theorem only has to identify each quotient `𝔞 η / 𝔞 η₀` with the
extension of a nonzero ideal from the maximal real subfield. -/
theorem caseIIBridge_of_realIdealModel_base_and_specificKummer
    {p : ℕ} [hpri : Fact p.Prime] [NeZero p] (hodd : p ≠ 2) (i : ℕ)
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus (CyclotomicField p ℚ))
    (h_model_base : ∀ {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
      {x y z : 𝓞 (CyclotomicField p ℚ)}
      {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
      (e : x ^ p + y ^ p =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))),
      η ≠ zetaSubOneDvdRoot hodd hζ e hy →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField p ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd hodd hζ e hy η) /
            (rootDivZetaSubOneDvdGcd hodd hζ e hy
              (zetaSubOneDvdRoot hodd hζ e hy))
            : FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰
                (CyclotomicField p ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField p ℚ)))
              (𝓞 (CyclotomicField p ℚ))) :
              FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰
                (CyclotomicField p ℚ))))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := p) (K := CyclotomicField p ℚ)) :
    BernoulliRegular.CaseIIBridge p (CyclotomicField p ℚ) i :=
  caseIIBridge_of_etaZeroPrincipalizationOnSpecific hodd i
    (caseIIPrincipalizationAgainstEtaZeroOnSpecific_of_realIdealModel
      p (CyclotomicField p ℚ) hodd h_not_dvd h_model_base)
    h_kummer

set_option backward.isDefEq.respectTransparency false in
/-- **Case-II bridge from the real-ideal model.** This composes the narrow
principalization bridge
`caseIIPrincipalDischargeOnSpecific_of_realIdealModel` with the already wired
case-II descent chain.

The remaining principalization source theorem is exactly `h_model`: every
actual case-II quotient `𝔞 η₁ / 𝔞 η₂` descends from an ideal of `K⁺`.  This
lemma does not hide that source theorem inside a new final hypothesis; it just
connects the proved plus-class-number principalization step to the existing
`CaseIIBridge` consumer. -/
theorem caseIIBridge_of_realIdealModel_and_specificKummer
    {p : ℕ} [hpri : Fact p.Prime] [NeZero p] (hodd : p ≠ 2) (i : ℕ)
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus (CyclotomicField p ℚ))
    (h_model : ∀ {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
      {x y z : 𝓞 (CyclotomicField p ℚ)}
      {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
      (e : x ^ p + y ^ p =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))),
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField p ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd hodd hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd hodd hζ e hy η₂)
            : FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰
                (CyclotomicField p ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField p ℚ)))
              (𝓞 (CyclotomicField p ℚ))) :
              FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰
                (CyclotomicField p ℚ))))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := p) (K := CyclotomicField p ℚ)) :
    BernoulliRegular.CaseIIBridge p (CyclotomicField p ℚ) i :=
  caseIIBridge_of_specificDischarges hodd i
    (caseIIPrincipalDischargeOnSpecific_of_realIdealModel
      p (CyclotomicField p ℚ) hodd h_not_dvd h_model)
    h_kummer

set_option backward.isDefEq.respectTransparency false in
/-- **Case-II bridge from the off-diagonal real-ideal model.**

The equal-root quotient `𝔞 η / 𝔞 η` is principal without any descent theorem, so
the remaining principalization source only has to provide the real-ideal model
for distinct roots. -/
theorem caseIIBridge_of_realIdealModel_ne_and_specificKummer
    {p : ℕ} [hpri : Fact p.Prime] [NeZero p] (hodd : p ≠ 2) (i : ℕ)
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus (CyclotomicField p ℚ))
    (h_model_ne : ∀ {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
      {x y z : 𝓞 (CyclotomicField p ℚ)}
      {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
      (e : x ^ p + y ^ p =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))),
      η₁ ≠ η₂ →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField p ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd hodd hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd hodd hζ e hy η₂)
            : FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰
                (CyclotomicField p ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField p ℚ)))
              (𝓞 (CyclotomicField p ℚ))) :
              FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰
                (CyclotomicField p ℚ))))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := p) (K := CyclotomicField p ℚ)) :
    BernoulliRegular.CaseIIBridge p (CyclotomicField p ℚ) i :=
  caseIIBridge_of_specificDischarges hodd i
    (caseIIPrincipalDischargeOnSpecific_of_realIdealModel_ne
      p (CyclotomicField p ℚ) hodd h_not_dvd h_model_ne)
    h_kummer

/-- **FLT37 case-II bridge from Cor 8.19 plus the specific source inputs.**
This specializes `caseIIBridge_of_realIdealModel_and_specificKummer` at `p = 37`
and derives the needed `¬ 37 ∣ hPlus` internally from the Cor 8.19 bridge and
the shipped real Pollaczek local certificate.

The remaining source inputs stay explicit:
* `h_model`: the Washington 9.4 real-descent witness for the actual quotient
  `𝔞 η₁ / 𝔞 η₂`;
* `h_kummer`: the case-II-specific adapted Kummer lemma. -/
theorem caseIIBridge_thirtyseven_of_cor8_19_realIdealModel_and_specificKummer
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (h_model : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₂)
            : FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ))))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ)) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  have h_not_dvd :
      ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.not_dvd_hPlus_thirtyseven_of_vandiver37PlusCoprime
      (FLT37.vandiver37PlusCoprime_of_bridge cor8_19
        FLT37.flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete)
  exact caseIIBridge_of_realIdealModel_and_specificKummer
    (p := 37) (by decide : (37 : ℕ) ≠ 2) 32
    h_not_dvd h_model h_kummer

/-- **FLT37 case-II bridge from Cor 8.19 plus off-diagonal real descent.**

This is the narrowest current case-II principalization surface: the real-descent
witness is required only when `η₁ ≠ η₂`; the diagonal quotient is discharged by
`fractionalIdeal_div_self_isPrincipal`. -/
theorem caseIIBridge_thirtyseven_of_cor8_19_realIdealModel_ne_and_specificKummer
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (h_model_ne : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η₁ ≠ η₂ →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₂)
            : FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ))))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ)) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  have h_not_dvd :
      ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.not_dvd_hPlus_thirtyseven_of_vandiver37PlusCoprime
      (FLT37.vandiver37PlusCoprime_of_bridge cor8_19
        FLT37.flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete)
  exact caseIIBridge_of_realIdealModel_ne_and_specificKummer
    (p := 37) (by decide : (37 : ℕ) ≠ 2) 32
    h_not_dvd h_model_ne h_kummer

/-- **FLT37 case-II bridge from Cor 8.19 plus anchored real descent.**

This version only asks for the real-ideal model of the anchored quotients
`𝔞 η / 𝔞 η₀`, which are the quotients used to build the next descent equation.
-/
theorem caseIIBridge_thirtyseven_of_cor8_19_realIdealModel_base_and_specificKummer
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (cor8_19 : Cor8_19Bridge 37 (CyclotomicField 37 ℚ) 32)
    (h_model_base : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η ≠ zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) hζ e hy →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy
              (zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) hζ e hy))
            : FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ))))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ)) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  have h_not_dvd :
      ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ) :=
    FLT37.not_dvd_hPlus_thirtyseven_of_vandiver37PlusCoprime
      (FLT37.vandiver37PlusCoprime_of_bridge cor8_19
        FLT37.flt37_not_isPthPowerModPrime_pollaczekUnitPlus_concrete)
  exact caseIIBridge_of_realIdealModel_base_and_specificKummer
    (p := 37) (by decide : (37 : ℕ) ≠ 2) 32
    h_not_dvd h_model_base h_kummer

/-- Complex conjugation on the ring of integers of a CM field is involutive. -/
theorem ringOfIntegersComplexConj_apply_apply
    {K : Type} [Field K] [NumberField K] [NumberField.IsCMField K]
    (a : 𝓞 K) :
    ringOfIntegersComplexConj K (ringOfIntegersComplexConj K a) = a := by
  apply RingOfIntegers.ext
  simp [NumberField.IsCMField.coe_ringOfIntegersComplexConj,
    NumberField.IsCMField.complexConj_apply_apply]

/-- If one algebraic integer is the conjugate of another, the reverse
conjugacy follows from involutivity. -/
theorem ringOfIntegersComplexConj_eq_symm_of_eq
    {K : Type} [Field K] [NumberField K] [NumberField.IsCMField K]
    {a b : 𝓞 K} (h : ringOfIntegersComplexConj K a = b) :
    ringOfIntegersComplexConj K b = a := by
  rw [← h]
  exact ringOfIntegersComplexConj_apply_apply (K := K) a

/-- An element with a non-divisor is nonzero. -/
theorem ne_zero_of_not_dvd {R : Type} [Semiring R] {r a : R} (h : ¬ r ∣ a) : a ≠ 0 :=
  fun ha => h (ha ▸ dvd_zero r)

/-- **Conjugation fixedness of Washington's Case-II real expression.**

The hard Washington 9.4 source step is to construct concrete integral
elements `rho_a` and `rho_-a` and prove that this expression generates the
specific root-ideal quotient.  This lemma isolates the pure algebraic part:
once the two `rho` terms are conjugate and `σ(ζ) = ζ⁻¹`, the quotient

`(rho_a - ζ * rho_-a) / (1 - ζ)`

is fixed by complex conjugation. -/
theorem washington_real_expression_fixed_of_conj_pair
    {K : Type} [Field K] [NumberField K] [NumberField.IsCMField K]
    {ζ rho_a rho_neg_a : K}
    (hζ_ne_zero : ζ ≠ 0) (hζ_ne_one : ζ ≠ 1)
    (hζ_conj : NumberField.IsCMField.complexConj K ζ = ζ⁻¹)
    (hrho_a : NumberField.IsCMField.complexConj K rho_a = rho_neg_a)
    (hrho_neg_a : NumberField.IsCMField.complexConj K rho_neg_a = rho_a) :
    NumberField.IsCMField.complexConj K
        ((rho_a - ζ * rho_neg_a) / (1 - ζ)) =
      (rho_a - ζ * rho_neg_a) / (1 - ζ) := by
  have hden : (1 - ζ) ≠ 0 := sub_ne_zero.mpr fun h => hζ_ne_one h.symm
  have hden_zeta : (ζ - 1) ≠ 0 := sub_ne_zero.mpr hζ_ne_one
  have hden_inv : (1 - ζ⁻¹) ≠ 0 :=
    sub_ne_zero.mpr fun h => hζ_ne_one (inv_eq_one.mp h.symm)
  simp only [map_div₀, map_sub, map_one, map_mul, hζ_conj, hrho_a, hrho_neg_a]
  field_simp [hden, hden_zeta, hden_inv, hζ_ne_zero]
  ring

/-- Primitive-root wrapper for
`washington_real_expression_fixed_of_conj_pair`.

This is the form used by `CaseIIData37`: the primitive root lives in `K`, and
`IsPrimitiveRoot.toInteger` supplies the corresponding algebraic integer root used
by the existing cyclotomic conjugation lemma. -/
theorem washington_real_expression_fixed_of_primitive_conj_pair
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    {ζ rho_a rho_neg_a : K} (hζ : IsPrimitiveRoot ζ 37)
    (hrho_a : NumberField.IsCMField.complexConj K rho_a = rho_neg_a)
    (hrho_neg_a : NumberField.IsCMField.complexConj K rho_neg_a = rho_a) :
    NumberField.IsCMField.complexConj K
        ((rho_a - ζ * rho_neg_a) / (1 - ζ)) =
      (rho_a - ζ * rho_neg_a) / (1 - ζ) := by
  refine washington_real_expression_fixed_of_conj_pair
    (K := K)
    (hζ.ne_zero (by decide : (37 : ℕ) ≠ 0))
    (hζ.ne_one (by decide : 1 < 37)) ?_ hrho_a hrho_neg_a
  simpa using
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.complexConj_K_apply_primRoot_eq_inv
      (K := K) (p := 37) (ζ := (hζ.toInteger : 𝓞 K)) hζ.toInteger_isPrimitiveRoot

/-- Integral form of `washington_real_expression_fixed_of_primitive_conj_pair`.

If Washington's expression is represented by an algebraic integer `a`, and the
two `rho` terms are conjugate algebraic integers, then `a` is fixed by
complex conjugation.  This is the exact fixed-generator side condition needed
by the `CaseIIData37` descent consumers below. -/
theorem washington_integral_expression_fixed_of_primitive_integer_conj_pair
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    {ζ : K} {rho_a rho_neg_a a : 𝓞 K} (hζ : IsPrimitiveRoot ζ 37)
    (ha :
      (a : K) =
        ((rho_a : K) - ζ * (rho_neg_a : K)) / (1 - ζ))
    (hrho_a : ringOfIntegersComplexConj K rho_a = rho_neg_a)
    (hrho_neg_a : ringOfIntegersComplexConj K rho_neg_a = rho_a) :
    ringOfIntegersComplexConj K a = a := by
  have hrho_a_K :
      NumberField.IsCMField.complexConj K (rho_a : K) =
        (rho_neg_a : K) := by
    rw [← NumberField.IsCMField.coe_ringOfIntegersComplexConj (K := K) rho_a]
    exact congrArg (algebraMap (𝓞 K) K) hrho_a
  have hrho_neg_a_K :
      NumberField.IsCMField.complexConj K (rho_neg_a : K) =
        (rho_a : K) := by
    rw [← NumberField.IsCMField.coe_ringOfIntegersComplexConj (K := K) rho_neg_a]
    exact congrArg (algebraMap (𝓞 K) K) hrho_neg_a
  apply RingOfIntegers.ext
  rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj]
  rw [ha]
  exact
    washington_real_expression_fixed_of_primitive_conj_pair
      (K := K) (ζ := ζ) (rho_a := (rho_a : K))
      (rho_neg_a := (rho_neg_a : K)) hζ hrho_a_K hrho_neg_a_K

/-- Integral Washington expression fixedness with only one conjugacy
orientation.

The reverse relation `σ(rho_neg_a) = rho_a` is a formal consequence of
involutivity, so it should not remain as a separate source obligation. -/
theorem washington_integral_expression_fixed_of_primitive_integer_conj
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    {ζ : K} {rho_a rho_neg_a a : 𝓞 K} (hζ : IsPrimitiveRoot ζ 37)
    (ha :
      (a : K) =
        ((rho_a : K) - ζ * (rho_neg_a : K)) / (1 - ζ))
    (hrho_a : ringOfIntegersComplexConj K rho_a = rho_neg_a) :
    ringOfIntegersComplexConj K a = a :=
  washington_integral_expression_fixed_of_primitive_integer_conj_pair
    (K := K) hζ ha hrho_a
    (ringOfIntegersComplexConj_eq_symm_of_eq (K := K) hrho_a)

/-- Case-II descent datum for the FLT37 Washington 9.4 route.

The final FLT37 path consumes Washington's Case-II descent theorem on this
datum rather than exposing the two intermediate endpoint placeholders
`CaseIIPrincipalDischargeOnSpecific` and `AdaptedKummersLemmaOnSpecific`.
The datum records the equation convention used by the flt-regular descent:
the exponent on `(ζ - 1)` is written as `m + 1`.

The Lean-facing descent theorem returns a smaller nonempty datum rather than
treating this structure itself as a proposition.  The fields deliberately stay
close to the actual flt-regular equation; any additional normalization needed
by the Washington construction should be added as concrete fields here, not as
a bundled opaque source assumption. -/
structure CaseIIData37 (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {37} ℚ K] [NumberField.IsCMField K] (m : ℕ) where
  ζ : K
  hζ : IsPrimitiveRoot ζ 37
  x : 𝓞 K
  y : 𝓞 K
  z : 𝓞 K
  ε : (𝓞 K)ˣ
  equation :
    x ^ 37 + y ^ 37 =
      (ε : 𝓞 K) * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37
  hy : ¬ hζ.toInteger - 1 ∣ y
  hz : ¬ hζ.toInteger - 1 ∣ z

/-- A `CaseIIData37` descent datum cannot sit at exponent level `m = 0`.

This is the datum-level form of the standard `one_le_m` valuation obstruction:
the equation with both `y` and `z` not divisible by `ζ - 1` forces the descent
index `m` to be positive. -/
theorem CaseIIData37.one_le_m
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m) :
    1 ≤ m :=
  _root_.one_le_m (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2)
    D.hζ D.equation D.hy D.hz

/-- There is no `CaseIIData37` datum at level zero. -/
theorem not_caseIIData37_zero
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] :
    ¬ Nonempty (CaseIIData37 K 0) :=
  fun ⟨D⟩ => Nat.not_succ_le_zero 0 D.one_le_m

private theorem CaseIIData37.descend_of_exists_solution'
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (sol : ∃ (x' y' z' : 𝓞 K) (ε' : (𝓞 K)ˣ),
      ¬ (D.hζ.toInteger - 1) ∣ y' ∧ ¬ (D.hζ.toInteger - 1) ∣ z' ∧
      x' ^ 37 + y' ^ 37 = (ε' : 𝓞 K) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') := by
  obtain ⟨x', y', z', ε', hy', hz', e'⟩ := sol
  have hm : 1 ≤ m := D.one_le_m
  exact ⟨m - 1, by omega,
    ⟨{ ζ := D.ζ, hζ := D.hζ, x := x', y := y', z := z', ε := ε',
       equation := by simpa [Nat.sub_add_cancel hm] using e', hy := hy', hz := hz' }⟩⟩

/-- The distinguished root `η₀` attached to a `CaseIIData37` datum. -/
noncomputable def CaseIIData37.etaZero
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m) :
    nthRootsFinset 37 (1 : 𝓞 K) :=
  zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy

/-- The Washington case-II auxiliary ideal `A_η` attached to a
`CaseIIData37` datum. -/
noncomputable def CaseIIData37.rootIdeal
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) : Ideal (𝓞 K) :=
  rootDivZetaSubOneDvdGcd (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy η

/-- The first adjacent root `η₀ζ` used by the concrete case-II descent
formula. -/
noncomputable def CaseIIData37.etaOne
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m) :
    nthRootsFinset 37 (1 : 𝓞 K) := by
  have hmem := mul_mem_nthRootsFinset (D.etaZero : _).prop
    (D.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37))
  rw [one_mul] at hmem
  exact ⟨(D.etaZero : 𝓞 K) * D.hζ.toInteger, hmem⟩

/-- The second adjacent root `η₀ζ²` used by the concrete case-II descent
formula. -/
noncomputable def CaseIIData37.etaTwo
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m) :
    nthRootsFinset 37 (1 : 𝓞 K) := by
  have hmem := mul_mem_nthRootsFinset (D.etaOne : _).prop
    (D.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37))
  rw [one_mul] at hmem
  exact ⟨(D.etaOne : 𝓞 K) * D.hζ.toInteger, hmem⟩

/-- `η₀ζ` is distinct from `η₀`. -/
theorem CaseIIData37.etaOne_ne_etaZero
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m) :
    D.etaOne ≠ D.etaZero := by
  rw [← Subtype.coe_injective.ne_iff]
  change ((D.etaZero : 𝓞 K) * D.hζ.toInteger : 𝓞 K) ≠ (D.etaZero : 𝓞 K)
  rw [Ne, mul_right_eq_self₀, not_or]
  exact ⟨D.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37),
    ne_zero_of_mem_nthRootsFinset one_ne_zero (D.etaZero : _).prop⟩

/-- `η₀ζ²` is distinct from `η₀`. -/
theorem CaseIIData37.etaTwo_ne_etaZero
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m) :
    D.etaTwo ≠ D.etaZero := by
  rw [← Subtype.coe_injective.ne_iff]
  change (((D.etaZero : 𝓞 K) * D.hζ.toInteger) * D.hζ.toInteger : 𝓞 K) ≠
    (D.etaZero : 𝓞 K)
  rw [Ne, mul_assoc, ← pow_two, mul_right_eq_self₀, not_or]
  exact ⟨D.hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by decide : 2 < 37),
    ne_zero_of_mem_nthRootsFinset one_ne_zero (D.etaZero : _).prop⟩

/-- `η₀ζ²` is distinct from `η₀ζ`. -/
theorem CaseIIData37.etaTwo_ne_etaOne
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m) :
    D.etaTwo ≠ D.etaOne := by
  rw [← Subtype.coe_injective.ne_iff]
  change (((D.etaZero : 𝓞 K) * D.hζ.toInteger) * D.hζ.toInteger : 𝓞 K) ≠
    (D.etaZero : 𝓞 K) * D.hζ.toInteger
  rw [Ne, mul_right_eq_self₀, not_or]
  exact ⟨D.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37),
    mul_ne_zero (ne_zero_of_mem_nthRootsFinset one_ne_zero (D.etaZero : _).prop)
      (D.hζ.toInteger_isPrimitiveRoot.ne_zero (by decide : 37 ≠ 0))⟩

/-- The `37`-th power of the concrete quotient `A_η₁ / A_η₂` is principal. -/
theorem CaseIIData37.rootIdeal_quotient_pow_isPrincipal
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)) :
    ((((D.rootIdeal η₁ : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal η₂ : FractionalIdeal (𝓞 K)⁰ K)) ^ 37 :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal := by
  simpa [CaseIIData37.rootIdeal] using
    (caseII_specificQuotient_pow_isPrincipal
      (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2)
      D.hζ D.equation D.hy η₁ η₂)

/-- Anchored form of the standard quotient identity, with denominator `A_η₀`. -/
theorem CaseIIData37.anchored_rootIdeal_quotient_pow_isPrincipal
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    ((((D.rootIdeal η : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal D.etaZero : FractionalIdeal (𝓞 K)⁰ K)) ^ 37 :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal :=
  D.rootIdeal_quotient_pow_isPrincipal η D.etaZero

/-- If a concrete quotient `A_η₁ / A_η₂` is generated by a nonzero integral
element from the real subfield, then it has the real-ideal model required by
the plus-class principalization step.

This is the `CaseIIData37`-native wrapper around the pure ideal bookkeeping
lemma in `SpecificDischarge.lean`; the source work remains the construction of
the integral real generator. -/
theorem CaseIIData37.rootIdeal_quotient_realIdealModel_of_integral_real_generator
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    (b : 𝓞 (NumberField.maximalRealSubfield K)) (hb : b ≠ 0)
    (hgen :
      (((D.rootIdeal η₁ : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal η₂ : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b)))) :
    ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield K)), J ≠ ⊥ ∧
      (((D.rootIdeal η₁ : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal η₂ : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) =
        (J.map (algebraMap
          (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K)) :=
  realIdealModel_of_integral_real_generator
    (K := K)
    (((D.rootIdeal η₁ : FractionalIdeal (𝓞 K)⁰ K) /
      (D.rootIdeal η₂ : FractionalIdeal (𝓞 K)⁰ K) :
      FractionalIdeal (𝓞 K)⁰ K)) b hb hgen

/-- Anchored version of
`CaseIIData37.rootIdeal_quotient_realIdealModel_of_integral_real_generator`,
with denominator `A_η₀`. -/
theorem CaseIIData37.anchored_rootIdeal_quotient_realIdealModel_of_integral_real_generator
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (b : 𝓞 (NumberField.maximalRealSubfield K)) (hb : b ≠ 0)
    (hgen :
      (((D.rootIdeal η : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal D.etaZero : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K
            (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b)))) :
    ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield K)), J ≠ ⊥ ∧
      (((D.rootIdeal η : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal D.etaZero : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) =
        (J.map (algebraMap
          (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K)) :=
  D.rootIdeal_quotient_realIdealModel_of_integral_real_generator
    η D.etaZero b hb hgen

/-- If the concrete quotient `A_η₁ / A_η₂` descends from a nonzero real ideal,
then Vandiver principalizes that quotient.  This is the `CaseIIData37`-native
form of the already-proved plus-class-number argument. -/
theorem CaseIIData37.rootIdeal_quotient_isPrincipal_of_realIdealModel
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus K)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    {J : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ_ne : J ≠ ⊥)
    (hJ_model :
      (((D.rootIdeal η₁ : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal η₂ : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) =
        (J.map (algebraMap
          (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K))) :
    Submodule.IsPrincipal
      (((D.rootIdeal η₁ : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal η₂ : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  simpa [CaseIIData37.rootIdeal] using
    (caseII_specificQuotient_principal_of_realIdealModel
      (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2)
      h_not_dvd D.hζ D.equation D.hy η₁ η₂ hJ_ne
      (by simpa [CaseIIData37.rootIdeal] using hJ_model))

/-- Anchored form of
`CaseIIData37.rootIdeal_quotient_isPrincipal_of_realIdealModel`, with
denominator `A_η₀`. -/
theorem CaseIIData37.anchored_rootIdeal_quotient_isPrincipal_of_realIdealModel
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus K)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    {J : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ_ne : J ≠ ⊥)
    (hJ_model :
      (((D.rootIdeal η : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal D.etaZero : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) =
        (J.map (algebraMap
          (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K))) :
    Submodule.IsPrincipal
      (((D.rootIdeal η : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal D.etaZero : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
  D.rootIdeal_quotient_isPrincipal_of_realIdealModel
    h_not_dvd η D.etaZero hJ_ne hJ_model

/-- A real-ideal model for `A_η / A_η₀` principalizes the exact anchored
quotient consumed by the existing case-II descent equation. -/
theorem CaseIIData37.rootIdeal_div_etaZeroPow_isPrincipal_of_realIdealModel
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus K)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    {J : Ideal (𝓞 (NumberField.maximalRealSubfield K))} (hJ_ne : J ≠ ⊥)
    (hJ_model :
      (((D.rootIdeal η : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal D.etaZero : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) =
        (J.map (algebraMap
          (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K))) :
    Submodule.IsPrincipal
      ((D.rootIdeal η /
        aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
          D.hζ D.equation D.hy
        : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  simpa [CaseIIData37.rootIdeal, CaseIIData37.etaZero] using
    (caseII_a_div_a_zero_isPrincipal_of_realIdealModel
      (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2)
      h_not_dvd D.hζ D.equation D.hy η hJ_ne
      (by simpa [CaseIIData37.rootIdeal, CaseIIData37.etaZero] using hJ_model))

/-- Fixed-datum anchored principalization plus the specific adapted Kummer step
construct a smaller `CaseIIData37` datum.

This is the datum-local form of the existing global descent combinator.  It is
the right consumer for Washington 9.4 internals: once the concrete quotients
attached to `D` are principalized, the already-formalized descent-equation
machinery lowers the exponent. -/
theorem CaseIIData37.descent_step_of_etaZeroPrincipalization_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (h_principal :
      CaseIIPrincipalizationAgainstEtaZero 37 K
        (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy)
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K)) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descend_of_exists_solution' <|
    exists_solution'_of_etaZeroPrincipalization
      (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2)
      D.hζ D.equation D.hy D.hz h_principal h_kummer

/-- Fixed-datum explicit quotient generators plus the specific adapted Kummer
step construct a smaller `CaseIIData37` datum.

This is the pair-level source consumer for Washington's concrete
`ρ`-expression: it asks only for the two anchored generators used by the
already-formalized descent equation, rather than a full principalization
provider for all roots. -/
theorem CaseIIData37.descent_step_of_etaZeroSpanSingletons_and_unitPower
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    (hη₁ : η₁ ≠ D.etaZero)
    (hη₂ : η₂ ≠ D.etaZero)
    (hη : η₂ ≠ η₁)
    {a₁ b₁ a₂ b₂ : 𝓞 K}
    (ha₁ : ¬ (D.hζ.toInteger - 1) ∣ a₁)
    (hb₁ : ¬ (D.hζ.toInteger - 1) ∣ b₁)
    (ha₂ : ¬ (D.hζ.toInteger - 1) ∣ a₂)
    (hb₂ : ¬ (D.hζ.toInteger - 1) ∣ b₂)
    (hspan₁ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₁ / b₁ : K) =
        (D.rootIdeal η₁ /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K))
    (hspan₂ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₂ / b₂ : K) =
        (D.rootIdeal η₂ /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K))
    (h_unit :
      ∀ {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 =
          (ε₃ : 𝓞 K) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 K)ˣ, ε₁ / ε₂ = ε' ^ 37) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descend_of_exists_solution' <|
    exists_solution'_of_etaZeroSpanSingletons_and_unitPower
      (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2)
      D.hζ D.equation D.hy D.hz η₁ η₂
      (by simpa [CaseIIData37.etaZero] using hη₁)
      (by simpa [CaseIIData37.etaZero] using hη₂)
      hη ha₁ hb₁ ha₂ hb₂
      (by simpa [CaseIIData37.rootIdeal] using hspan₁)
      (by simpa [CaseIIData37.rootIdeal] using hspan₂)
      h_unit

theorem CaseIIData37.descent_step_of_etaZeroSpanSingletons_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K))
    (hη₁ : η₁ ≠ D.etaZero)
    (hη₂ : η₂ ≠ D.etaZero)
    (hη : η₂ ≠ η₁)
    {a₁ b₁ a₂ b₂ : 𝓞 K}
    (ha₁ : ¬ (D.hζ.toInteger - 1) ∣ a₁)
    (hb₁ : ¬ (D.hζ.toInteger - 1) ∣ b₁)
    (ha₂ : ¬ (D.hζ.toInteger - 1) ∣ a₂)
    (hb₂ : ¬ (D.hζ.toInteger - 1) ∣ b₂)
    (hspan₁ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₁ / b₁ : K) =
        (D.rootIdeal η₁ /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K))
    (hspan₂ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₂ / b₂ : K) =
        (D.rootIdeal η₂ /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K)) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descend_of_exists_solution' <|
    exists_solution'_of_etaZeroSpanSingletons
      (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2)
      D.hζ D.equation D.hy D.hz η₁ η₂
      (by simpa [CaseIIData37.etaZero] using hη₁)
      (by simpa [CaseIIData37.etaZero] using hη₂)
      hη ha₁ hb₁ ha₂ hb₂
      (by simpa [CaseIIData37.rootIdeal] using hspan₁)
      (by simpa [CaseIIData37.rootIdeal] using hspan₂)
      h_kummer

/-- Adjacent-root version of
`CaseIIData37.descent_step_of_etaZeroSpanSingletons_and_adaptedKummer`.

The two quotients are exactly those used by the descent formula:
`η₀ζ / η₀` and `η₀ζ² / η₀`. -/
theorem CaseIIData37.descent_step_of_adjacent_etaZeroSpanSingletons_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    {a₁ b₁ a₂ b₂ : 𝓞 K}
    (ha₁ : ¬ (D.hζ.toInteger - 1) ∣ a₁)
    (hb₁ : ¬ (D.hζ.toInteger - 1) ∣ b₁)
    (ha₂ : ¬ (D.hζ.toInteger - 1) ∣ a₂)
    (hb₂ : ¬ (D.hζ.toInteger - 1) ∣ b₂)
    (hspan₁ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₁ / b₁ : K) =
        (D.rootIdeal D.etaOne /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K))
    (hspan₂ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₂ / b₂ : K) =
        (D.rootIdeal D.etaTwo /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K)) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descent_step_of_etaZeroSpanSingletons_and_adaptedKummer
    D.etaOne D.etaTwo D.etaOne_ne_etaZero D.etaTwo_ne_etaZero
    D.etaTwo_ne_etaOne ha₁ hb₁ ha₂ hb₂ hspan₁ hspan₂ h_kummer

/-- Adjacent-root version of
`CaseIIData37.descent_step_of_etaZeroSpanSingletons_and_unitPower`.

This is the same adjacent anchored-quotient descent, with the adapted unit
source narrowed to the exact quotient unit produced by the two-generator
formula. -/
theorem CaseIIData37.descent_step_of_adjacent_etaZeroSpanSingletons_and_unitPower
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    {a₁ b₁ a₂ b₂ : 𝓞 K}
    (ha₁ : ¬ (D.hζ.toInteger - 1) ∣ a₁)
    (hb₁ : ¬ (D.hζ.toInteger - 1) ∣ b₁)
    (ha₂ : ¬ (D.hζ.toInteger - 1) ∣ a₂)
    (hb₂ : ¬ (D.hζ.toInteger - 1) ∣ b₂)
    (hspan₁ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₁ / b₁ : K) =
        (D.rootIdeal D.etaOne /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K))
    (hspan₂ :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₂ / b₂ : K) =
        (D.rootIdeal D.etaTwo /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K))
    (h_unit :
      ∀ {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 =
          (ε₃ : 𝓞 K) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 K)ˣ, ε₁ / ε₂ = ε' ^ 37) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descent_step_of_etaZeroSpanSingletons_and_unitPower
    D.etaOne D.etaTwo D.etaOne_ne_etaZero D.etaTwo_ne_etaZero
    D.etaTwo_ne_etaOne ha₁ hb₁ ha₂ hb₂ hspan₁ hspan₂ h_unit

/-- Adjacent integral real generators also give the datum-local descent step.

This is tailored to Washington's concrete expression: once the two adjacent
anchored quotients are generated by nonzero elements of `𝓞 K⁺` whose images in
`𝓞 K` are not divisible by `ζ - 1`, the existing pair-level algebra applies
with denominator `1`. -/
theorem CaseIIData37.descent_step_of_adjacent_integral_real_generators_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (hgens :
      ∃ b₁ b₂ : 𝓞 (NumberField.maximalRealSubfield K),
        b₁ ≠ 0 ∧ b₂ ≠ 0 ∧
        ¬ (D.hζ.toInteger - 1) ∣
          algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣
          algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₁)) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₂)) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K)) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') := by
  obtain ⟨b₁, b₂, _hb₁_ne, _hb₂_ne, hb₁_ndvd, hb₂_ndvd, hspan₁, hspan₂⟩ :=
    hgens
  let c₁ : 𝓞 K :=
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₁
  let c₂ : 𝓞 K :=
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₂
  have h_one_not_dvd : ¬ (D.hζ.toInteger - 1 : 𝓞 K) ∣ (1 : 𝓞 K) :=
    D.hζ.zeta_sub_one_prime'.not_dvd_one
  refine
    D.descent_step_of_adjacent_etaZeroSpanSingletons_and_adaptedKummer
      (a₁ := c₁) (b₁ := 1) (a₂ := c₂) (b₂ := 1)
      ?_ h_one_not_dvd ?_ h_one_not_dvd ?_ ?_ h_kummer
  · simpa [c₁] using hb₁_ndvd
  · simpa [c₂] using hb₂_ndvd
  · simpa [c₁] using hspan₁
  · simpa [c₂] using hspan₂

/-- Adjacent integral real generators with the exact unit-power discharge. -/
theorem CaseIIData37.descent_step_of_adjacent_integral_real_generators_and_unitPower
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (hgens :
      ∃ b₁ b₂ : 𝓞 (NumberField.maximalRealSubfield K),
        b₁ ≠ 0 ∧ b₂ ≠ 0 ∧
        ¬ (D.hζ.toInteger - 1) ∣
          algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣
          algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₁)) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₂)) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_unit :
      ∀ {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 =
          (ε₃ : 𝓞 K) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 K)ˣ, ε₁ / ε₂ = ε' ^ 37) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') := by
  obtain ⟨b₁, b₂, _hb₁_ne, _hb₂_ne, hb₁_ndvd, hb₂_ndvd, hspan₁, hspan₂⟩ :=
    hgens
  let c₁ : 𝓞 K :=
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₁
  let c₂ : 𝓞 K :=
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₂
  have h_one_not_dvd : ¬ (D.hζ.toInteger - 1 : 𝓞 K) ∣ (1 : 𝓞 K) :=
    D.hζ.zeta_sub_one_prime'.not_dvd_one
  refine
    D.descent_step_of_adjacent_etaZeroSpanSingletons_and_unitPower
      (a₁ := c₁) (b₁ := 1) (a₂ := c₂) (b₂ := 1)
      ?_ h_one_not_dvd ?_ h_one_not_dvd ?_ ?_ h_unit
  · simpa [c₁] using hb₁_ndvd
  · simpa [c₂] using hb₂_ndvd
  · simpa [c₁] using hspan₁
  · simpa [c₂] using hspan₂

/-- Adjacent fixed integral generators descend to the real subfield and give
the datum-local Case-II descent step.

This is the Lean-facing shape of Washington's real expression before choosing
coordinates in `𝓞 K⁺`: it is enough to prove the two adjacent quotient
generators are nonzero, fixed by conjugation, not divisible by `ζ - 1`, and
generate the desired anchored quotients as principal fractional ideals. -/
theorem CaseIIData37.descent_step_of_adjacent_fixed_integral_generators_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (hgens :
      ∃ a₁ a₂ : 𝓞 K,
        a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        ringOfIntegersComplexConj K a₁ = a₁ ∧
        ringOfIntegersComplexConj K a₂ = a₂ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₁) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₂) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K)) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') := by
  obtain ⟨a₁, a₂, ha₁_ne, ha₂_ne, hfix₁, hfix₂, ha₁_ndvd, ha₂_ndvd,
    hspan₁, hspan₂⟩ := hgens
  obtain ⟨b₁, hb₁⟩ :=
    mem_ringOfIntegers_of_conj_eq_self (K := K) a₁ hfix₁
  obtain ⟨b₂, hb₂⟩ :=
    mem_ringOfIntegers_of_conj_eq_self (K := K) a₂ hfix₂
  refine D.descent_step_of_adjacent_integral_real_generators_and_adaptedKummer ?_ h_kummer
  refine ⟨b₁, b₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hb
    exact ha₁_ne (by simpa [hb] using hb₁.symm)
  · intro hb
    exact ha₂_ne (by simpa [hb] using hb₂.symm)
  · simpa [hb₁] using ha₁_ndvd
  · simpa [hb₂] using ha₂_ndvd
  · simpa [hb₁] using hspan₁
  · simpa [hb₂] using hspan₂

/-- Adjacent Washington expressions give the datum-local Case-II descent step.

This is the checked consumer closest to Washington 9.4's real-expression
construction.  The remaining source work is now stated as concrete data:
integral conjugate `rho` pairs, their quotient-expression identities, the
nonzero/nondivisibility side conditions, and the two principal-fractional-ideal
span identities for the adjacent quotients.  The proof below supplies the
conjugation-fixedness automatically from the expression formula. -/
theorem CaseIIData37.descent_step_of_adjacent_washington_integral_expressions_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (hgens :
      ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg : 𝓞 K,
        a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        (a₁ : K) =
          ((rho₁ : K) - D.ζ * (rho₁_neg : K)) / (1 - D.ζ) ∧
        (a₂ : K) =
          ((rho₂ : K) - D.ζ * (rho₂_neg : K)) / (1 - D.ζ) ∧
        ringOfIntegersComplexConj K rho₁ = rho₁_neg ∧
        ringOfIntegersComplexConj K rho₁_neg = rho₁ ∧
        ringOfIntegersComplexConj K rho₂ = rho₂_neg ∧
        ringOfIntegersComplexConj K rho₂_neg = rho₂ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₁) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₂) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K)) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') := by
  obtain ⟨a₁, a₂, rho₁, rho₁_neg, rho₂, rho₂_neg,
    ha₁_ne, ha₂_ne, hexpr₁, hexpr₂, hconj₁, hconj₁_neg,
    hconj₂, hconj₂_neg, ha₁_ndvd, ha₂_ndvd, hspan₁, hspan₂⟩ := hgens
  refine
    D.descent_step_of_adjacent_fixed_integral_generators_and_adaptedKummer
      ?_ h_kummer
  refine ⟨a₁, a₂, ha₁_ne, ha₂_ne, ?_, ?_, ha₁_ndvd, ha₂_ndvd, hspan₁, hspan₂⟩
  · exact
      washington_integral_expression_fixed_of_primitive_integer_conj_pair
        (K := K) (ζ := D.ζ) (rho_a := rho₁) (rho_neg_a := rho₁_neg)
        (a := a₁) D.hζ hexpr₁ hconj₁ hconj₁_neg
  · exact
      washington_integral_expression_fixed_of_primitive_integer_conj_pair
        (K := K) (ζ := D.ζ) (rho_a := rho₂) (rho_neg_a := rho₂_neg)
        (a := a₂) D.hζ hexpr₂ hconj₂ hconj₂_neg

/-- A datum-local real-ideal model plus the specific adapted Kummer step
constructs a smaller `CaseIIData37` datum.

The only source input here is the concrete real-ideal model for the quotients
`A_η / A_η₀` attached to this datum.  Principalization under `37 ∤ h⁺` and the
exponent-lowering algebra are already formalized. -/
theorem CaseIIData37.descent_step_of_realIdealModel_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus K)
    (h_model : ∀ η : nthRootsFinset 37 (1 : 𝓞 K),
      η ≠ D.etaZero →
        ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield K)),
          J ≠ ⊥ ∧
            (((D.rootIdeal η : FractionalIdeal (𝓞 K)⁰ K) /
              (D.rootIdeal D.etaZero : FractionalIdeal (𝓞 K)⁰ K) :
              FractionalIdeal (𝓞 K)⁰ K) =
              (J.map (algebraMap
                (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :
                FractionalIdeal (𝓞 K)⁰ K)))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K)) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') := by
  have h_principal :
      CaseIIPrincipalizationAgainstEtaZero 37 K
        (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy := by
    intro η hη
    obtain ⟨J, hJ_ne, hJ_model⟩ := h_model η hη
    exact
      D.rootIdeal_div_etaZeroPow_isPrincipal_of_realIdealModel
        h_not_dvd η hJ_ne hJ_model
  exact
    D.descent_step_of_etaZeroPrincipalization_and_adaptedKummer
      h_principal h_kummer

/-- Integral real generators for the anchored quotients, plus the specific
adapted Kummer step, construct a smaller `CaseIIData37` datum.

This is a sharper Washington-facing consumer than
`CaseIIData37.descent_step_of_realIdealModel_and_adaptedKummer`: the remaining
real-model source input is just the construction of the concrete nonzero
integral real generator for each quotient `A_η / A_η₀`. -/
theorem CaseIIData37.descent_step_of_integral_real_generators_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus K)
    (hgen : ∀ η : nthRootsFinset 37 (1 : 𝓞 K),
      η ≠ D.etaZero →
        ∃ b : 𝓞 (NumberField.maximalRealSubfield K), b ≠ 0 ∧
          (((D.rootIdeal η : FractionalIdeal (𝓞 K)⁰ K) /
            (D.rootIdeal D.etaZero : FractionalIdeal (𝓞 K)⁰ K) :
            FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰
              (algebraMap (𝓞 K) K
                (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b))))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K)) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') := by
  refine D.descent_step_of_realIdealModel_and_adaptedKummer h_not_dvd ?_ h_kummer
  intro η hη
  obtain ⟨b, hb, hgenη⟩ := hgen η hη
  exact
    D.anchored_rootIdeal_quotient_realIdealModel_of_integral_real_generator
      η b hb hgenη

/-- Off-diagonal datum-local real-ideal models also construct a smaller
`CaseIIData37` datum.

This is the same as
`CaseIIData37.descent_step_of_realIdealModel_and_adaptedKummer`, but with the
Washington-facing source input stated for every distinct pair of roots. -/
theorem CaseIIData37.descent_step_of_realIdealModel_ne_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus K)
    (h_model_ne : ∀ η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K),
      η₁ ≠ η₂ →
        ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield K)),
          J ≠ ⊥ ∧
            (((D.rootIdeal η₁ : FractionalIdeal (𝓞 K)⁰ K) /
              (D.rootIdeal η₂ : FractionalIdeal (𝓞 K)⁰ K) :
              FractionalIdeal (𝓞 K)⁰ K) =
              (J.map (algebraMap
                (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :
                FractionalIdeal (𝓞 K)⁰ K)))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K)) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descent_step_of_realIdealModel_and_adaptedKummer h_not_dvd
    (fun η hη => h_model_ne η D.etaZero hη) h_kummer

/-- Off-diagonal integral real generators for quotient pairs also construct a
smaller `CaseIIData37` datum.

This is the datum-local form closest to Washington's expression
`(ρ_a - ζρ_{-a}) / (1 - ζ)`: once that expression is shown to be a nonzero
integral real generator for each concrete quotient, the existing plus-side and
descent-equation machinery lowers the measure. -/
theorem CaseIIData37.descent_step_of_integral_real_generators_ne_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus K)
    (hgen_ne : ∀ η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K),
      η₁ ≠ η₂ →
        ∃ b : 𝓞 (NumberField.maximalRealSubfield K), b ≠ 0 ∧
          (((D.rootIdeal η₁ : FractionalIdeal (𝓞 K)⁰ K) /
            (D.rootIdeal η₂ : FractionalIdeal (𝓞 K)⁰ K) :
            FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰
              (algebraMap (𝓞 K) K
                (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b))))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K)) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descent_step_of_integral_real_generators_and_adaptedKummer h_not_dvd
    (fun η hη => hgen_ne η D.etaZero hη) h_kummer

/-- Extract a `CaseIIData37` datum from the integer second-case normal form
`37 ∤ y`, `37 ∣ z`, `z ≠ 0`, `x^37 + y^37 = z^37`.

This is the same multiplicity extraction used by flt-regular's
`not_exists_Int_solution`: factor the image of `z` by the highest power of
`ζ - 1`.  Since `37 ∣ z`, that exponent is at least one, so it is written as
`m + 1` in the `CaseIIData37` convention. -/
theorem exists_caseIIData37_of_Int_solution
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (∃ (x y z : ℤ), ¬ (37 : ℤ) ∣ y ∧ (37 : ℤ) ∣ z ∧ z ≠ 0 ∧
      x ^ 37 + y ^ 37 = z ^ 37) →
    ∃ m : ℕ, Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m) := by
  intro h
  haveI := CyclotomicField.isCyclotomicExtension 37 ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    ℚ (B := (CyclotomicField 37 ℚ)) (Set.mem_singleton 37)
    (by decide : (37 : ℕ) ≠ 0)
  have h_dvd_iff := fun n ↦
    zeta_sub_one_dvd_Int_iff (K := CyclotomicField 37 ℚ) hζ (n := n)
  rcases h with ⟨x, y, z, hy_int, hz_int, hz_ne, e⟩
  have hy : ¬ (hζ.toInteger - 1) ∣ (y : 𝓞 (CyclotomicField 37 ℚ)) := by
    intro hdiv
    exact hy_int ((h_dvd_iff y).mp hdiv)
  have hz : (hζ.toInteger - 1) ∣ (z : 𝓞 (CyclotomicField 37 ℚ)) :=
    (h_dvd_iff z).mpr hz_int
  have hz_ne_OK : (z : 𝓞 (CyclotomicField 37 ℚ)) ≠ 0 := by
    rwa [ne_eq, Int.cast_eq_zero]
  have eOK :
      (x : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 +
        (y : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 =
        (z : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 := by
    simp_rw [← Int.cast_pow, ← Int.cast_add, e]
  obtain ⟨n, z', hn, hz_n, hz_eq⟩ :=
    exists_pos_pow_mul_of_zeta_sub_one_dvd hζ hz hz_ne_OK
  refine ⟨n - 1, ⟨?_⟩⟩
  refine
    { ζ := ζ
      hζ := hζ
      x := (x : 𝓞 (CyclotomicField 37 ℚ))
      y := (y : 𝓞 (CyclotomicField 37 ℚ))
      z := z'
      ε := 1
      equation := ?_
      hy := hy
      hz := hz_n }
  have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hz_eq] at eOK
  simpa [hn_eq] using eOK

/-- Extract a `CaseIIData37` datum from the usual coprime integer second-case
normal form. -/
theorem exists_caseIIData37_of_Int_solution'
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    (∃ (x y z : ℤ), ({x, y, z} : Finset ℤ).gcd id = 1 ∧
      (37 : ℤ) ∣ z ∧ z ≠ 0 ∧ x ^ 37 + y ^ 37 = z ^ 37) →
    ∃ m : ℕ, Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m) := by
  rintro ⟨x, y, z, hgcd, hz, hz_ne, e⟩
  exact exists_caseIIData37_of_Int_solution
    ⟨x, y, z, caseII_not_dvd_snd_of_gcd_eq_one hgcd hz e, hz, hz_ne, e⟩

/-- An actual integer Case-II FLT solution supplies some `CaseIIData37`
datum, after the standard permutation that moves the divisible variable to
the `z` slot. -/
theorem exists_caseIIData37_of_caseII_int_solution
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {a b c : ℤ}
    (hprod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcase : (37 : ℤ) ∣ a * b * c)
    (e : a ^ 37 + b ^ 37 = c ^ 37) :
    ∃ m : ℕ, Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m) :=
  exists_caseIIData37_of_Int_solution'
    (exists_caseII_Int_normal_form (by decide : (37 : ℕ) ≠ 2) hprod hgcd hcase e)

/-- The already formalized anchored-principalization chain plus the tightened
case-II Kummer step really does construct a smaller `CaseIIData37` datum.

This is the Lean version of the final "build the next descent equation" part
of Washington 9.4.  It does not prove the Washington source inputs; it proves
that once those internal inputs are available for the concrete datum, the
public descent measure strictly decreases. -/
theorem caseII_descent_step_of_etaZeroPrincipalizationOnSpecific_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (h_principal : CaseIIPrincipalizationAgainstEtaZeroOnSpecific
      37 K (by decide : (37 : ℕ) ≠ 2))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K))
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descend_of_exists_solution' <|
    exists_solution'_of_etaZeroPrincipalizationOnSpecific
      (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2)
      D.hζ D.equation D.hy D.hz h_principal h_kummer

/-- Anchored real-ideal models plus the specific adapted Kummer step construct
the strict `CaseIIData37` descent step.

This is the descent-step form of the already-proved real-model principalization
bridge: the source input is still the concrete Washington real-ideal model for
`𝔞 η / 𝔞₀`; this theorem only composes it with the existing plus-side
principalization and descent-equation machinery. -/
theorem caseII_descent_step_of_realIdealModel_base_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus K)
    (h_model_base : ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η : nthRootsFinset 37 (1 : 𝓞 K)),
      η ≠ zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) hζ e hy →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield K)),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy
                (zetaSubOneDvdRoot
                  (by decide : (37 : ℕ) ≠ 2) hζ e hy))
            : FractionalIdeal (𝓞 K)⁰ K) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :
              FractionalIdeal (𝓞 K)⁰ K)))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K))
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  caseII_descent_step_of_etaZeroPrincipalizationOnSpecific_and_adaptedKummer
    (K := K)
    (caseIIPrincipalizationAgainstEtaZeroOnSpecific_of_realIdealModel
      37 K (by decide : (37 : ℕ) ≠ 2) h_not_dvd h_model_base)
    h_kummer D

/-- Off-diagonal real-ideal models plus the specific adapted Kummer step
construct the strict `CaseIIData37` descent step.

This is the same descent route as
`caseII_descent_step_of_realIdealModel_base_and_adaptedKummer`, but with the
source input stated in the more Washington-facing off-diagonal form
`η₁ ≠ η₂`.  The anchored quotient is obtained by taking `η₂ = η₀`. -/
theorem caseII_descent_step_of_realIdealModel_ne_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus K)
    (h_model_ne : ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)),
      η₁ ≠ η₂ →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield K)),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₂)
            : FractionalIdeal (𝓞 K)⁰ K) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :
              FractionalIdeal (𝓞 K)⁰ K)))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K))
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  caseII_descent_step_of_realIdealModel_base_and_adaptedKummer
    (K := K) h_not_dvd
    (fun {ζ} hζ {x} {y} {z} {ε} {m} e hy η hη =>
      h_model_ne (ζ := ζ) hζ (x := x) (y := y) (z := z) (ε := ε)
        (m := m) e hy η
        (zetaSubOneDvdRoot (by decide : (37 : ℕ) ≠ 2) hζ e hy) hη)
    h_kummer D

/-- Integral real generators for the off-diagonal concrete quotients, plus the
specific adapted Kummer step, construct the strict `CaseIIData37` descent step.

This removes the intermediate real-ideal existential from the source-facing
descent consumer: Washington's real expression only has to be proved to be a
nonzero integral real generator of the concrete quotient. -/
theorem caseII_descent_step_of_integral_real_generators_ne_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus K)
    (hgen_ne : ∀ {ζ : K} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)),
      η₁ ≠ η₂ →
      ∃ b : 𝓞 (NumberField.maximalRealSubfield K), b ≠ 0 ∧
        (((rootDivZetaSubOneDvdGcd
            (by decide : (37 : ℕ) ≠ 2) hζ e hy η₁) /
          (rootDivZetaSubOneDvdGcd
            (by decide : (37 : ℕ) ≠ 2) hζ e hy η₂)
          : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (algebraMap
                (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b))))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K))
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descent_step_of_integral_real_generators_ne_and_adaptedKummer
    h_not_dvd
    (fun η₁ η₂ hη =>
      hgen_ne (ζ := D.ζ) D.hζ (x := D.x) (y := D.y) (z := D.z)
        (ε := D.ε) (m := m) D.equation D.hy η₁ η₂ hη)
    h_kummer

/-- Adjacent explicit quotient generators plus the specific adapted Kummer
step construct the strict `CaseIIData37` descent step.

This is the narrowest checked Case-II descent consumer currently available:
for each datum it asks only for generators of the two quotients actually used
by the descent formula, namely `A_{η₀ζ} / A₀` and `A_{η₀ζ²} / A₀`, with the
usual nondivisibility side conditions. -/
theorem caseII_descent_step_of_adjacent_etaZeroSpanSingletons_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (hgens : ∀ {m : ℕ} (D : CaseIIData37 K m),
      ∃ a₁ b₁ a₂ b₂ : 𝓞 K,
        ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣ b₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
        ¬ (D.hζ.toInteger - 1) ∣ b₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₁ / b₁ : K) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₂ / b₂ : K) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K))
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') := by
  obtain ⟨a₁, b₁, a₂, b₂, ha₁, hb₁, ha₂, hb₂, hspan₁, hspan₂⟩ := hgens D
  exact
    D.descent_step_of_adjacent_etaZeroSpanSingletons_and_adaptedKummer
      ha₁ hb₁ ha₂ hb₂ hspan₁ hspan₂ h_kummer

/-- Adjacent explicit quotient generators plus the exact quotient-unit
power source construct the strict `CaseIIData37` descent step.

This is the unit-power analogue of
`caseII_descent_step_of_adjacent_etaZeroSpanSingletons_and_adaptedKummer`:
after the two anchored quotient generators are supplied, the remaining
Case-II source is only that the exact unit `ε₁ / ε₂` produced by the
two-generator descent formula is a 37-th power. -/
theorem caseII_descent_step_of_adjacent_etaZeroSpanSingletons_and_unitPower
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (hgens : ∀ {m : ℕ} (D : CaseIIData37 K m),
      ∃ a₁ b₁ a₂ b₂ : 𝓞 K,
        ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣ b₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
        ¬ (D.hζ.toInteger - 1) ∣ b₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₁ / b₁ : K) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (a₂ / b₂ : K) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_unit :
      ∀ {m : ℕ} (D : CaseIIData37 K m)
        {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 =
          (ε₃ : 𝓞 K) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 K)ˣ, ε₁ / ε₂ = ε' ^ 37)
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') := by
  obtain ⟨a₁, b₁, a₂, b₂, ha₁, hb₁, ha₂, hb₂, hspan₁, hspan₂⟩ := hgens D
  exact
    D.descent_step_of_adjacent_etaZeroSpanSingletons_and_unitPower
      ha₁ hb₁ ha₂ hb₂ hspan₁ hspan₂ (h_unit D)

/-- Adjacent integral real generators plus the specific adapted Kummer step
construct the strict `CaseIIData37` descent step.

This is the source-facing version of
`CaseIIData37.descent_step_of_adjacent_integral_real_generators_and_adaptedKummer`.
It asks only for the two real generators used by the adjacent quotient descent
formula. -/
theorem caseII_descent_step_of_adjacent_integral_real_generators_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (hgens : ∀ {m : ℕ} (D : CaseIIData37 K m),
      ∃ b₁ b₂ : 𝓞 (NumberField.maximalRealSubfield K),
        b₁ ≠ 0 ∧ b₂ ≠ 0 ∧
        ¬ (D.hζ.toInteger - 1) ∣
          algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣
          algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₁)) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₂)) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K))
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descent_step_of_adjacent_integral_real_generators_and_adaptedKummer
    (hgens D) h_kummer

/-- Adjacent real generators plus the exact quotient-unit power source
construct the strict `CaseIIData37` descent step. -/
theorem caseII_descent_step_of_adjacent_integral_real_generators_and_unitPower
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (hgens : ∀ {m : ℕ} (D : CaseIIData37 K m),
      ∃ b₁ b₂ : 𝓞 (NumberField.maximalRealSubfield K),
        b₁ ≠ 0 ∧ b₂ ≠ 0 ∧
        ¬ (D.hζ.toInteger - 1) ∣
          algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣
          algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₁)) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰
            (algebraMap (𝓞 K) K
              (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) b₂)) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_unit :
      ∀ {m : ℕ} (D : CaseIIData37 K m)
        {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 =
          (ε₃ : 𝓞 K) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 K)ˣ, ε₁ / ε₂ = ε' ^ 37)
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descent_step_of_adjacent_integral_real_generators_and_unitPower
    (hgens D) (h_unit D)

/-- Adjacent fixed integral generators plus the specific adapted Kummer step
construct the strict `CaseIIData37` descent step.

This is one level closer to Washington's expression than the `K⁺`-valued
generator theorem: the source expression may be built in `𝓞 K` and proved
fixed by conjugation; the descent to `𝓞 K⁺` is handled by the existing maximal
real subfield API. -/
theorem caseII_descent_step_of_adjacent_fixed_integral_generators_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (hgens : ∀ {m : ℕ} (D : CaseIIData37 K m),
      ∃ a₁ a₂ : 𝓞 K,
        a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        ringOfIntegersComplexConj K a₁ = a₁ ∧
        ringOfIntegersComplexConj K a₂ = a₂ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₁) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₂) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K))
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descent_step_of_adjacent_fixed_integral_generators_and_adaptedKummer
    (hgens D) h_kummer

/-- Adjacent Washington expressions plus the specific adapted Kummer step
construct the strict `CaseIIData37` descent step.

This top-level consumer exposes the exact real-expression source surface:
Washington's task is to construct the two adjacent integral generators from
conjugate `rho` pairs and prove their two span identities.  Fixedness is no
longer a separate assumption. -/
theorem caseII_descent_step_of_adjacent_washington_integral_expressions_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (hgens : ∀ {m : ℕ} (D : CaseIIData37 K m),
      ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg : 𝓞 K,
        a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        (a₁ : K) =
          ((rho₁ : K) - D.ζ * (rho₁_neg : K)) / (1 - D.ζ) ∧
        (a₂ : K) =
          ((rho₂ : K) - D.ζ * (rho₂_neg : K)) / (1 - D.ζ) ∧
        ringOfIntegersComplexConj K rho₁ = rho₁_neg ∧
        ringOfIntegersComplexConj K rho₁_neg = rho₁ ∧
        ringOfIntegersComplexConj K rho₂ = rho₂_neg ∧
        ringOfIntegersComplexConj K rho₂_neg = rho₂ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₁) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₂) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K))
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  D.descent_step_of_adjacent_washington_integral_expressions_and_adaptedKummer
    (hgens D) h_kummer

/-- Adjacent Washington expressions with only one conjugacy orientation, plus
the specific adapted Kummer step, construct the strict `CaseIIData37` descent
step.

The reverse conjugacy equations are derived internally from
`ringOfIntegersComplexConj_apply_apply`; they are not independent Washington
source obligations. -/
theorem caseII_descent_step_of_adjacent_washington_oneConj_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (hgens : ∀ {m : ℕ} (D : CaseIIData37 K m),
      ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg : 𝓞 K,
        a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        (a₁ : K) =
          ((rho₁ : K) - D.ζ * (rho₁_neg : K)) / (1 - D.ζ) ∧
        (a₂ : K) =
          ((rho₂ : K) - D.ζ * (rho₂_neg : K)) / (1 - D.ζ) ∧
        ringOfIntegersComplexConj K rho₁ = rho₁_neg ∧
        ringOfIntegersComplexConj K rho₂ = rho₂_neg ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₁) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₂) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K))
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  caseII_descent_step_of_adjacent_washington_integral_expressions_and_adaptedKummer
    (K := K)
    (fun {m} D => by
      rcases hgens D with
        ⟨a₁, a₂, rho₁, rho₁_neg, rho₂, rho₂_neg, ha₁, ha₂,
          heq₁, heq₂, hρ₁, hρ₂, hnot₁, hnot₂, hspan₁, hspan₂⟩
      refine
        ⟨a₁, a₂, rho₁, rho₁_neg, rho₂, rho₂_neg, ha₁, ha₂,
          heq₁, heq₂, hρ₁, ?_, hρ₂, ?_, hnot₁, hnot₂, hspan₁, hspan₂⟩
      · exact ringOfIntegersComplexConj_eq_symm_of_eq (K := K) hρ₁
      · exact ringOfIntegersComplexConj_eq_symm_of_eq (K := K) hρ₂)
    h_kummer D

/-- Adjacent Washington expressions with one conjugacy orientation, with
nonzero derived from the `ζ - 1` nondivisibility side conditions.

This is the narrowest current source-facing Case-II descent consumer: the
caller supplies the integral expressions, their one-way conjugacy equations,
their `ζ - 1` nondivisibility, and the span identities. -/
theorem caseII_descent_step_of_adjacent_washington_oneConj_noNonzero_and_adaptedKummer
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (hgens : ∀ {m : ℕ} (D : CaseIIData37 K m),
      ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg : 𝓞 K,
        (a₁ : K) =
          ((rho₁ : K) - D.ζ * (rho₁_neg : K)) / (1 - D.ζ) ∧
        (a₂ : K) =
          ((rho₂ : K) - D.ζ * (rho₂_neg : K)) / (1 - D.ζ) ∧
        ringOfIntegersComplexConj K rho₁ = rho₁_neg ∧
        ringOfIntegersComplexConj K rho₂ = rho₂_neg ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₁) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₂) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K))
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') :=
  caseII_descent_step_of_adjacent_washington_oneConj_and_adaptedKummer
    (K := K)
    (fun {m} D => by
      rcases hgens D with
        ⟨a₁, a₂, rho₁, rho₁_neg, rho₂, rho₂_neg,
          heq₁, heq₂, hρ₁, hρ₂, hnot₁, hnot₂, hspan₁, hspan₂⟩
      refine
        ⟨a₁, a₂, rho₁, rho₁_neg, rho₂, rho₂_neg,
          ne_zero_of_not_dvd hnot₁, ne_zero_of_not_dvd hnot₂,
          heq₁, heq₂, hρ₁, hρ₂, hnot₁, hnot₂, hspan₁, hspan₂⟩)
    h_kummer D

/-- Adjacent Washington expressions with one conjugacy orientation, with the
adapted-unit source narrowed to the exact quotient unit `ε₁ / ε₂` produced by
the two-generator descent formula. -/
theorem caseII_descent_step_of_adjacent_washington_oneConj_noNonzero_and_unitPower
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (hgens : ∀ {m : ℕ} (D : CaseIIData37 K m),
      ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg : 𝓞 K,
        (a₁ : K) =
          ((rho₁ : K) - D.ζ * (rho₁_neg : K)) / (1 - D.ζ) ∧
        (a₂ : K) =
          ((rho₂ : K) - D.ζ * (rho₂_neg : K)) / (1 - D.ζ) ∧
        ringOfIntegersComplexConj K rho₁ = rho₁_neg ∧
        ringOfIntegersComplexConj K rho₂ = rho₂_neg ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
        ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₁) =
          (D.rootIdeal D.etaOne /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K) ∧
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₂) =
          (D.rootIdeal D.etaTwo /
            aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
              D.hζ D.equation D.hy :
            FractionalIdeal (𝓞 K)⁰ K))
    (h_unit :
      ∀ {m : ℕ} (D : CaseIIData37 K m)
        {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 =
          (ε₃ : 𝓞 K) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 K)ˣ, ε₁ / ε₂ = ε' ^ 37)
    {m : ℕ} (D : CaseIIData37 K m) :
    ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m') := by
  rcases hgens D with
    ⟨a₁, a₂, rho₁, rho₁_neg, rho₂, rho₂_neg,
      _heq₁, _heq₂, _hρ₁, _hρ₂, hnot₁, hnot₂, hspan₁, hspan₂⟩
  have h_one_not_dvd : ¬ (D.hζ.toInteger - 1 : 𝓞 K) ∣ (1 : 𝓞 K) :=
    D.hζ.zeta_sub_one_prime'.not_dvd_one
  refine
    D.descent_step_of_adjacent_etaZeroSpanSingletons_and_unitPower
      (a₁ := a₁) (b₁ := 1) (a₂ := a₂) (b₂ := 1)
      hnot₁ h_one_not_dvd hnot₂ h_one_not_dvd ?_ ?_ (h_unit D)
  · simpa using hspan₁
  · simpa using hspan₂

/-- A single Washington real-expression generator for one anchored Case-II
quotient.

For a datum `D` and a root `η`, this records exactly the source data needed
from Washington's construction for the quotient
`D.rootIdeal η / aEtaZeroDvdPPow ...`: an integral element of the form
`(ρ - ζρ⁻)/(1 - ζ)`, one conjugacy equation for the two `ρ` terms, the local
nondivisibility, and the anchored span identity against the coprime part of
`D.rootIdeal D.etaZero`.

This is only a data shape.  Constructing it from `D` is the remaining
Washington §9.4 source work. -/
structure CaseIIWashingtonRootGenerator37
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ}
    (D : CaseIIData37 K m) (η : nthRootsFinset 37 (1 : 𝓞 K)) where
  a : 𝓞 K
  rho : 𝓞 K
  rhoNeg : 𝓞 K
  theta_eq :
    (a : K) = ((rho : K) - D.ζ * (rhoNeg : K)) / (1 - D.ζ)
  conj_eq :
    ringOfIntegersComplexConj K rho = rhoNeg
  not_zetaSubOne_dvd :
    ¬ (D.hζ.toInteger - 1) ∣ a
  span_eq :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a) =
      (D.rootIdeal η /
        aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
          D.hζ D.equation D.hy :
        FractionalIdeal (𝓞 K)⁰ K)

/-- A fixed integral generator for one anchored Case-II quotient.

This is a Type-valued data package because it is used to build the
Type-valued `CaseIIWashingtonRootGenerator37` structure. -/
structure CaseIIWashingtonFixedIntegralGenerator37
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ}
    (D : CaseIIData37 K m) (η : nthRootsFinset 37 (1 : 𝓞 K)) where
  a : 𝓞 K
  fixed_eq :
    ringOfIntegersComplexConj K a = a
  not_zetaSubOne_dvd :
    ¬ (D.hζ.toInteger - 1) ∣ a
  span_eq :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a) =
      (D.rootIdeal η /
        aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
          D.hζ D.equation D.hy :
        FractionalIdeal (𝓞 K)⁰ K)

/-- The two adjacent fixed integral generators used by the FLT37 Case-II
descent.  This is the final-path Washington generator shape: the descent only
uses the quotients at `η₀ζ` and `η₀ζ²`, so the source boundary should not ask
for a generator at every non-anchor root. -/
structure CaseIIWashingtonAdjacentFixedIntegralGenerators37
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ}
    (D : CaseIIData37 K m) where
  atEtaOne : CaseIIWashingtonFixedIntegralGenerator37 D D.etaOne
  atEtaTwo : CaseIIWashingtonFixedIntegralGenerator37 D D.etaTwo

/-- A fixed integral generator of the anchored quotient gives a Washington
root-generator package.

This proves the formal `ρ`/`ρ⁻` expression part directly: if the generator is
already fixed by conjugation, taking `ρ = ρ⁻ = a` gives
`(ρ - ζρ⁻) / (1 - ζ) = a`.  The remaining source content is therefore only the
existence of such a fixed integral generator with the stated span identity and
local nondivisibility. -/
def caseII_washington_rootGenerator37_of_fixedIntegralGenerator
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ}
    (D : CaseIIData37 K m) (η : nthRootsFinset 37 (1 : 𝓞 K))
    (a : 𝓞 K)
    (hfixed : ringOfIntegersComplexConj K a = a)
    (hnot : ¬ (D.hζ.toInteger - 1) ∣ a)
    (hspan :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a) =
        (D.rootIdeal η /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K)) :
    CaseIIWashingtonRootGenerator37 D η := by
  refine
    { a := a
      rho := a
      rhoNeg := a
      theta_eq := ?_
      conj_eq := hfixed
      not_zetaSubOne_dvd := hnot
      span_eq := hspan }
  have hden : (1 : K) - D.ζ ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (D.hζ.ne_one (by decide : 1 < 37)))
  field_simp [hden]

/-- Two single-root Washington generators at `η₀ζ` and `η₀ζ²` assemble the
adjacent generator package consumed by the descent theorem. -/
theorem caseII_washington_adjacent_generators37_of_rootGenerators
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ}
    (D : CaseIIData37 K m)
    (G₁ : CaseIIWashingtonRootGenerator37 D D.etaOne)
    (G₂ : CaseIIWashingtonRootGenerator37 D D.etaTwo) :
    ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg : 𝓞 K,
      (a₁ : K) =
        ((rho₁ : K) - D.ζ * (rho₁_neg : K)) / (1 - D.ζ) ∧
      (a₂ : K) =
        ((rho₂ : K) - D.ζ * (rho₂_neg : K)) / (1 - D.ζ) ∧
      ringOfIntegersComplexConj K rho₁ = rho₁_neg ∧
      ringOfIntegersComplexConj K rho₂ = rho₂_neg ∧
      ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
      ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₁) =
        (D.rootIdeal D.etaOne /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K) ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₂) =
        (D.rootIdeal D.etaTwo /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K) :=
  ⟨G₁.a, G₂.a, G₁.rho, G₁.rhoNeg, G₂.rho, G₂.rhoNeg,
    G₁.theta_eq, G₂.theta_eq, G₁.conj_eq, G₂.conj_eq,
    G₁.not_zetaSubOne_dvd, G₂.not_zetaSubOne_dvd,
    G₁.span_eq, G₂.span_eq⟩

/-- A uniform one-root Washington generator construction supplies the two
adjacent generators used by the FLT37 Case-II descent. -/
theorem caseII_washington_adjacent_generators37_of_forall_rootGenerator
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ}
    (D : CaseIIData37 K m)
    (hroot : ∀ η : nthRootsFinset 37 (1 : 𝓞 K), η ≠ D.etaZero →
      CaseIIWashingtonRootGenerator37 D η) :
    ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg : 𝓞 K,
      (a₁ : K) =
        ((rho₁ : K) - D.ζ * (rho₁_neg : K)) / (1 - D.ζ) ∧
      (a₂ : K) =
        ((rho₂ : K) - D.ζ * (rho₂_neg : K)) / (1 - D.ζ) ∧
      ringOfIntegersComplexConj K rho₁ = rho₁_neg ∧
      ringOfIntegersComplexConj K rho₂ = rho₂_neg ∧
      ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
      ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₁) =
        (D.rootIdeal D.etaOne /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K) ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a₂) =
        (D.rootIdeal D.etaTwo /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 K)⁰ K) :=
  caseII_washington_adjacent_generators37_of_rootGenerators
    D (hroot D.etaOne D.etaOne_ne_etaZero)
    (hroot D.etaTwo D.etaTwo_ne_etaZero)

/-- **Washington 9.4 adjacent fixed-generator source boundary (named Prop).**

This is the narrowed mathematical source statement still to be formalised for the
real expression part of Washington's Case-II descent: produce the two adjacent
conjugation-fixed integral generators for the anchored quotients actually used
by the descent.  The formal `ρ`/`ρ⁻` expression is proved by
`caseII_washington_rootGenerator37_of_fixedIntegralGenerator`.

Kept as a named hypothesis (`def`), **not** as a project axiom, so the FLT37
endpoint that consumes it stays explicitly conditional and axiom-clean.  The
source produces *data* (the conjugation-fixed generators), so it is `Type`-
valued rather than `Prop`-valued. -/
def WashingtonCaseIIAdjacentFixedGenerators37Source
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Type :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m),
    CaseIIWashingtonAdjacentFixedIntegralGenerators37 D

/-- The adjacent root-generator package, consuming the adjacent fixed-generator
source as an explicit hypothesis. -/
def washington_caseII_adjacentRootGenerators37_source
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_adjGens : WashingtonCaseIIAdjacentFixedGenerators37Source)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m) :
    CaseIIWashingtonRootGenerator37 D D.etaOne ×
      CaseIIWashingtonRootGenerator37 D D.etaTwo :=
  let G := h_adjGens hV hSO D
  ⟨caseII_washington_rootGenerator37_of_fixedIntegralGenerator D D.etaOne
      G.atEtaOne.a G.atEtaOne.fixed_eq
      G.atEtaOne.not_zetaSubOne_dvd G.atEtaOne.span_eq,
    caseII_washington_rootGenerator37_of_fixedIntegralGenerator D D.etaTwo
      G.atEtaTwo.a G.atEtaTwo.fixed_eq
      G.atEtaTwo.not_zetaSubOne_dvd G.atEtaTwo.span_eq⟩

/-- **Washington 9.4 adjacent real-expression generators for FLT37 Case II.**

This is the concrete real-expression/quotient-generation source.  It is
strictly narrower than the descent theorem: it only constructs the two
adjacent quotient generators around
`(ρ - ζ * ρ⁻) / (1 - ζ)` and proves their span identities. -/
theorem caseII_washington_adjacent_generators37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_adjGens : WashingtonCaseIIAdjacentFixedGenerators37Source)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m) :
    ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
        𝓞 (CyclotomicField 37 ℚ),
      (a₁ : CyclotomicField 37 ℚ) =
        ((rho₁ : CyclotomicField 37 ℚ) - D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) /
          (1 - D.ζ) ∧
      (a₂ : CyclotomicField 37 ℚ) =
        ((rho₂ : CyclotomicField 37 ℚ) - D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) /
          (1 - D.ζ) ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
      ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
      ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
      FractionalIdeal.spanSingleton (𝓞 (CyclotomicField 37 ℚ))⁰
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) a₁) =
        (D.rootIdeal D.etaOne /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ)) ∧
      FractionalIdeal.spanSingleton (𝓞 (CyclotomicField 37 ℚ))⁰
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) a₂) =
        (D.rootIdeal D.etaTwo /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
            D.hζ D.equation D.hy :
          FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ)) :=
  let G := washington_caseII_adjacentRootGenerators37_source h_adjGens hV hSO D
  caseII_washington_adjacent_generators37_of_rootGenerators D G.1 G.2

/-- The tightened adapted Kummer predicate proves the exact quotient-unit
power statement used by the adjacent-generator descent.

The only work here is local algebra: divide the descent equation by `ε₂`, then
derive the required integer congruence for `ε₁ / ε₂` from the same
`exists_solution'_aux` congruence argument used in the flt-regular descent. -/
theorem CaseIIData37.exact_quotient_unitPower_of_adaptedKummersLemmaOnSpecific
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ}
    (D : CaseIIData37 K m)
    (h_kummer : AdaptedKummersLemmaOnSpecific (p := 37) (K := K))
    {x' y' z' : 𝓞 K} {ε₁ ε₂ ε₃ : (𝓞 K)ˣ}
    (hx' : ¬ (D.hζ.toInteger - 1) ∣ x')
    (hy' : ¬ (D.hζ.toInteger - 1) ∣ y')
    (hz' : ¬ (D.hζ.toInteger - 1) ∣ z')
    (heq : (ε₁ : 𝓞 K) * x' ^ 37 + (ε₂ : 𝓞 K) * y' ^ 37 =
      (ε₃ : 𝓞 K) * ((D.hζ.toInteger - 1) ^ m * z') ^ 37) :
    ∃ ε' : (𝓞 K)ˣ, ε₁ / ε₂ = ε' ^ 37 :=
  caseII_unit_quotient_pow_of_adaptedKummer (by decide : (37 : ℕ) ≠ 2) D.hζ
    D.equation D.hy D.hz h_kummer hx' hy' hz' heq

/-- **Temporary Washington exact quotient-unit source boundary.**

This is Washington's adapted Case-II unit theorem in the exact form consumed by
the FLT37 descent: the unit quotient `ε₁ / ε₂` arising from the two-generator
descent equation is a `37`th power.  It avoids exposing a generic
`AdaptedKummersLemmaOnSpecific` source for arbitrary units. -/
def WashingtonCaseIIExactQuotientUnitPower37Source
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (_hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
    ¬ (D.hζ.toInteger - 1) ∣ x' →
    ¬ (D.hζ.toInteger - 1) ∣ y' →
    ¬ (D.hζ.toInteger - 1) ∣ z' →
    ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
      (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
    ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37

/-- **Washington adapted-unit source for the exact Case-II quotient unit.**

This is the unit-power part of the Case-II descent only for the unit
`ε₁ / ε₂` arising from the descent equation.  It does not assert an arbitrary
generic Kummer-unit lemma. -/
theorem caseII_exact_quotient_unitPower37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
    {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
    {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ} :
    ¬ (D.hζ.toInteger - 1) ∣ x' →
    ¬ (D.hζ.toInteger - 1) ∣ y' →
    ¬ (D.hζ.toInteger - 1) ∣ z' →
    ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
      (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
        (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
          ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
    ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37 :=
  h_exactUnit hV hSO D

/-- **Washington 9.4 descent step for FLT37 Case II.**

This is the source-faithful Case-II boundary recommended by the expert review:
principalisation of the concrete quotients and the adapted Kummer unit step are
internal to this theorem.  The public statement only exposes the descent
measure, not the normalization-sensitive formula used to construct `m'`. -/
theorem caseII_descent_step_under_vandiver37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_adjGens : WashingtonCaseIIAdjacentFixedGenerators37Source)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m) :
    ∃ m' : ℕ, m' < m ∧
      Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m') :=
  caseII_descent_step_of_adjacent_washington_oneConj_noNonzero_and_unitPower
    (K := CyclotomicField 37 ℚ)
    (fun {_m} D => caseII_washington_adjacent_generators37 h_adjGens hV hSO D)
    (fun {_m} D => caseII_exact_quotient_unitPower37 h_exactUnit hV hSO D)
    D

/-- A pure minimality wrapper: a strict descent step rules out all Case-II
data.  This is independent of the cyclotomic mathematics. -/
theorem no_caseIIData37_of_descent_step
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K]
    (step : ∀ {m : ℕ}, CaseIIData37 K m →
      ∃ m' : ℕ, m' < m ∧ Nonempty (CaseIIData37 K m')) :
    ¬ ∃ m : ℕ, Nonempty (CaseIIData37 K m) := by
  classical
  rintro ⟨m, D⟩
  have hP : ∃ n, Nonempty (CaseIIData37 K n) := ⟨m, D⟩
  obtain ⟨Dmin⟩ := Nat.find_spec hP
  obtain ⟨m', hm', D'⟩ := step Dmin
  exact Nat.find_min hP hm' D'

/-- No FLT37 Case-II descent datum can exist under Vandiver plus the
second-order condition. -/
theorem no_caseIIData37_under_vandiver37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_adjGens : WashingtonCaseIIAdjacentFixedGenerators37Source)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32) :
    ¬ ∃ m : ℕ,
      Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m) :=
  no_caseIIData37_of_descent_step
    (K := CyclotomicField 37 ℚ)
    (fun {_m} D => caseII_descent_step_under_vandiver37 h_adjGens h_exactUnit hV hSO D)

/-- Build the public FLT37 Case-II bridge from a Vandiver/second-order
descent-step family.  This theorem is just bookkeeping: the source input is
the strict descent on concrete `CaseIIData37` values. -/
theorem caseIIBridge_thirtyseven_of_descent_step
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (step :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32) {m : ℕ},
        CaseIIData37 (CyclotomicField 37 ℚ) m →
          ∃ m' : ℕ, m' < m ∧
            Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m')) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  refine ⟨?_⟩
  intro hV hSO a b c hprod hgcd hcase hEq
  have hNoData :
      ¬ ∃ m : ℕ,
        Nonempty (CaseIIData37 (CyclotomicField 37 ℚ) m) :=
    no_caseIIData37_of_descent_step
      (K := CyclotomicField 37 ℚ)
      (fun {_m} D => step hV hSO D)
  exact hNoData
    (exists_caseIIData37_of_caseII_int_solution hprod hgcd hcase hEq)

/-- The anchored-principalization and tightened-Kummer internals also feed the
refactored public Case-II bridge through the `CaseIIData37` descent route.

This checks that the old internal discharges connect to the reviewer-requested
descent boundary, rather than only to the older direct no-solution wrapper. -/
theorem caseIIBridge_thirtyseven_of_etaZeroPrincipalizationOnSpecific_and_adaptedKummer_via_descent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_principal : CaseIIPrincipalizationAgainstEtaZeroOnSpecific
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ)) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_descent_step
    (fun _ _ {_m} D =>
      caseII_descent_step_of_etaZeroPrincipalizationOnSpecific_and_adaptedKummer
        h_principal h_kummer D)

/-- The off-diagonal real-ideal model and tightened Kummer internals also feed
the refactored public Case-II bridge through the strict `CaseIIData37` descent
route. -/
theorem caseIIBridge_thirtyseven_of_realIdealModel_ne_and_adaptedKummer_via_descent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (h_model_ne : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η₁ ≠ η₂ →
      ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))),
        J ≠ ⊥ ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₂)
            : FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) =
            (J.map (algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ))) :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ))))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ)) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_descent_step
    (fun _ _ {_m} D =>
      caseII_descent_step_of_realIdealModel_ne_and_adaptedKummer
        h_not_dvd h_model_ne h_kummer D)

/-- Integral real generators for Washington's concrete quotients and the
tightened Kummer internals feed the refactored public Case-II bridge through
the strict `CaseIIData37` descent route. -/
theorem caseIIBridge_thirtyseven_of_integral_real_generators_ne_and_adaptedKummer_via_descent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hgen_ne : ∀ {ζ : CyclotomicField 37 ℚ} (hζ : IsPrimitiveRoot ζ 37)
      {x y z : 𝓞 (CyclotomicField 37 ℚ)}
      {ε : (𝓞 (CyclotomicField 37 ℚ))ˣ} {m : ℕ}
      (e : x ^ 37 + y ^ 37 =
        ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ 37)
      (hy : ¬ hζ.toInteger - 1 ∣ y)
      (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
      η₁ ≠ η₂ →
      ∃ b : 𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)),
        b ≠ 0 ∧
          (((rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₁) /
            (rootDivZetaSubOneDvdGcd
              (by decide : (37 : ℕ) ≠ 2) hζ e hy η₂)
            : FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) =
            FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ)
                (algebraMap
                  (𝓞 (NumberField.maximalRealSubfield
                    (CyclotomicField 37 ℚ)))
                  (𝓞 (CyclotomicField 37 ℚ)) b))))
    (h_kummer : AdaptedKummersLemmaOnSpecific
      (p := 37) (K := CyclotomicField 37 ℚ)) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_descent_step
    (fun _ _ {_m} D =>
      caseII_descent_step_of_integral_real_generators_ne_and_adaptedKummer
        h_not_dvd hgen_ne h_kummer D)

/-- Adjacent anchored quotient generators and the tightened Kummer internals
feed the refactored public Case-II bridge through the strict
`CaseIIData37` descent route.

This is the narrowest currently checked Case-II consumer: for each datum it
uses only generators of `A_{η₀ζ} / A_η₀` and `A_{η₀ζ²} / A_η₀`, rather than a
real-ideal model for every root pair. -/
theorem caseIIBridge_thirtyseven_of_adjacent_etaZeroSpanSingletons_and_adaptedKummer_via_descent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m),
        ∃ a₁ b₁ a₂ b₂ : 𝓞 (CyclotomicField 37 ℚ),
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ b₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          ¬ (D.hζ.toInteger - 1) ∣ b₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (a₁ / b₁ : CyclotomicField 37 ℚ) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (a₂ / b₂ : CyclotomicField 37 ℚ) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ)) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_descent_step
    (fun hV hSO {_m} D =>
      caseII_descent_step_of_adjacent_etaZeroSpanSingletons_and_adaptedKummer
        (hgens hV hSO) (h_kummer hV hSO) D)

/-- Adjacent anchored quotient generators and the exact quotient-unit power
source feed the refactored public Case-II bridge through the strict
`CaseIIData37` descent route. -/
theorem caseIIBridge_thirtyseven_of_adjacent_etaZeroSpanSingletons_and_unitPower_via_descent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m),
        ∃ a₁ b₁ a₂ b₂ : 𝓞 (CyclotomicField 37 ℚ),
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ b₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          ¬ (D.hζ.toInteger - 1) ∣ b₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (a₁ / b₁ : CyclotomicField 37 ℚ) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (a₂ / b₂ : CyclotomicField 37 ℚ) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_unit :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
        {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
        {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
            (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
          (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
            ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_descent_step
    (fun hV hSO {_m} D =>
      caseII_descent_step_of_adjacent_etaZeroSpanSingletons_and_unitPower
        (hgens hV hSO) (fun {_m'} D' => h_unit hV hSO D') D)

/-- Adjacent integral real generators and the specific adapted Kummer step feed
the refactored public Case-II bridge through the strict `CaseIIData37` descent
route.

This is the closest checked consumer to the Washington real-expression target:
the source input is only the two real integral generators for the adjacent
anchored quotients. -/
theorem caseIIBridge_thirtyseven_of_adjacent_integral_real_generators_and_adaptedKummer_via_descent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m),
        ∃ b₁ b₂ : 𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)),
          b₁ ≠ 0 ∧ b₂ ≠ 0 ∧
          ¬ (D.hζ.toInteger - 1) ∣
            algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ)) b₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣
            algebraMap
              (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
              (𝓞 (CyclotomicField 37 ℚ)) b₂ ∧
          FractionalIdeal.spanSingleton (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
                (algebraMap
                  (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
                  (𝓞 (CyclotomicField 37 ℚ)) b₁)) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
                (algebraMap
                  (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))
                  (𝓞 (CyclotomicField 37 ℚ)) b₂)) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ)) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_descent_step
    (fun hV hSO {_m} D =>
      caseII_descent_step_of_adjacent_integral_real_generators_and_adaptedKummer
        (hgens hV hSO) (h_kummer hV hSO) D)

/-- Adjacent fixed integral generators and the specific adapted Kummer step
feed the refactored public Case-II bridge through the strict `CaseIIData37`
descent route.

This lets the Washington real-expression source be stated directly in `𝓞 K`:
prove the two adjacent generator expressions are fixed by conjugation and
generate the anchored quotients; the real-subfield descent is checked here. -/
theorem caseIIBridge_thirtyseven_of_adjacent_fixed_integral_generators_and_adaptedKummer_via_descent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ : 𝓞 (CyclotomicField 37 ℚ),
          a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) a₁ = a₁ ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) a₂ = a₂ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ)) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_descent_step
    (fun hV hSO {_m} D =>
      caseII_descent_step_of_adjacent_fixed_integral_generators_and_adaptedKummer
        (hgens hV hSO) (h_kummer hV hSO) D)

/-- Adjacent Washington expressions and the specific adapted Kummer step feed
the refactored public Case-II bridge through the strict `CaseIIData37` descent
route.

This is the source-facing version of
`caseIIBridge_thirtyseven_of_adjacent_fixed_integral_generators_and_adaptedKummer_via_descent`.
For each concrete datum it asks for the two integral Washington expressions
`(rho - ζ rho') / (1 - ζ)` and their span identities; fixedness is checked by
`washington_integral_expression_fixed_of_primitive_integer_conj_pair`. -/
theorem caseIIBridge37_of_adjacent_washingtonExpr_and_adaptedKummer_via_descent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rho₁_neg = rho₁ ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rho₂_neg = rho₂ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ)) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_descent_step
    (fun hV hSO {_m} D =>
      caseII_descent_step_of_adjacent_washington_integral_expressions_and_adaptedKummer
        (hgens hV hSO) (h_kummer hV hSO) D)

/-- Adjacent Washington expressions with one conjugacy orientation and the
specific adapted Kummer step feed the refactored public Case-II bridge.

Compared with `caseIIBridge37_of_adjacent_washingtonExpr_and_adaptedKummer_via_descent`,
this only asks for `σ(rho) = rho'` for each adjacent expression; the reverse
relations follow from involutivity. -/
theorem caseIIBridge37_of_adjacent_washingtonExpr_oneConj_via_descent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ)) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_descent_step
    (fun hV hSO {_m} D =>
      caseII_descent_step_of_adjacent_washington_oneConj_and_adaptedKummer
        (hgens hV hSO) (h_kummer hV hSO) D)

/-- Adjacent Washington expressions with one conjugacy orientation and no
separate nonzero assumptions feed the public Case-II bridge.

Nonzero is derived from the `ζ - 1` nondivisibility conditions, so the caller
only proves the Washington expression identities, one-way conjugacy,
nondivisibility, span identities, and the adapted Kummer step. -/
theorem caseIIBridge37_of_adjacent_washingtonExpr_oneConj_noNonzero_via_descent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_kummer :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32),
        AdaptedKummersLemmaOnSpecific
          (p := 37) (K := CyclotomicField 37 ℚ)) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_descent_step
    (fun hV hSO {_m} D =>
      caseII_descent_step_of_adjacent_washington_oneConj_noNonzero_and_adaptedKummer
        (hgens hV hSO) (h_kummer hV hSO) D)

/-- Adjacent Washington expressions with one conjugacy orientation and no
separate nonzero assumptions feed the public Case-II bridge, using the exact
quotient-unit p-th-power source instead of the broader
`AdaptedKummersLemmaOnSpecific`.

This is the source-facing public bridge corresponding to
`caseII_descent_step_of_adjacent_washington_oneConj_noNonzero_and_unitPower`:
the Washington construction supplies the two adjacent generators, and the unit
input only proves that the specific quotient unit `ε₁ / ε₂` produced by the
descent formula is a 37-th power. -/
theorem caseIIBridge37_of_adjacent_washingtonExpr_oneConj_noNonzero_unitPower_via_descent
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hgens :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m),
        ∃ a₁ a₂ rho₁ rho₁_neg rho₂ rho₂_neg :
            𝓞 (CyclotomicField 37 ℚ),
          (a₁ : CyclotomicField 37 ℚ) =
            ((rho₁ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₁_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          (a₂ : CyclotomicField 37 ℚ) =
            ((rho₂ : CyclotomicField 37 ℚ) -
                D.ζ * (rho₂_neg : CyclotomicField 37 ℚ)) / (1 - D.ζ) ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rho₁ = rho₁_neg ∧
          ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rho₂ = rho₂_neg ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₁ ∧
          ¬ (D.hζ.toInteger - 1) ∣ a₂ ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₁) =
            (D.rootIdeal D.etaOne /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)) ∧
          FractionalIdeal.spanSingleton
              (𝓞 (CyclotomicField 37 ℚ))⁰
              (algebraMap (𝓞 (CyclotomicField 37 ℚ))
                (CyclotomicField 37 ℚ) a₂) =
            (D.rootIdeal D.etaTwo /
              aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2)
                D.hζ D.equation D.hy :
              FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰
                (CyclotomicField 37 ℚ)))
    (h_unit :
      ∀ (_hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
        (_hSO : NoSecondOrderIrregularPair 37 32)
        {m : ℕ} (D : CaseIIData37 (CyclotomicField 37 ℚ) m)
        {x' y' z' : 𝓞 (CyclotomicField 37 ℚ)}
        {ε₁ ε₂ ε₃ : (𝓞 (CyclotomicField 37 ℚ))ˣ},
        ¬ (D.hζ.toInteger - 1) ∣ x' →
        ¬ (D.hζ.toInteger - 1) ∣ y' →
        ¬ (D.hζ.toInteger - 1) ∣ z' →
        ((ε₁ : 𝓞 (CyclotomicField 37 ℚ)) * x' ^ 37 +
            (ε₂ : 𝓞 (CyclotomicField 37 ℚ)) * y' ^ 37 =
          (ε₃ : 𝓞 (CyclotomicField 37 ℚ)) *
            ((D.hζ.toInteger - 1) ^ m * z') ^ 37) →
        ∃ ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ, ε₁ / ε₂ = ε' ^ 37) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_descent_step
    (fun hV hSO {_m} D =>
      caseII_descent_step_of_adjacent_washington_oneConj_noNonzero_and_unitPower
        (hgens hV hSO) (fun {_m'} D' => h_unit hV hSO D') D)

/-- **FLT37 Case-II bridge from Washington 9.4 descent.**

This is the final bridge consumed by the private FLT37 assembly.  It supersedes
the previous final-path endpoints consisting of a generic `RealKummerLemma`, an
anchored real-ideal-model placeholder, and a standalone adapted-Kummer
placeholder. -/
theorem caseIIBridge_thirtyseven_of_descent_under_vandiver37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_adjGens : WashingtonCaseIIAdjacentFixedGenerators37Source)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (hV : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (hSO : NoSecondOrderIrregularPair 37 32) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_descent_step
    (fun _ _ {_m} D => caseII_descent_step_under_vandiver37 h_adjGens h_exactUnit hV hSO D)

set_option backward.isDefEq.respectTransparency false in
/-- **`caseIIBridge_of_specificDischarges_of_regular`** — sanity check.
Under regularity, the OnSpecific path also recovers the case-II bridge.
Composition of the OnSpecific bridge constructor with the regular-prime
fills of both OnSpecific predicates. Mirrors `caseIIBridge_of_regular`
but routes through the OnSpecific predicates instead of the general
ones, confirming the OnSpecific chain is a valid alternative for
regular primes. -/
theorem caseIIBridge_of_specificDischarges_of_regular
    {p : ℕ} [hpri : Fact p.Prime] (hodd : p ≠ 2) (i : ℕ)
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    [Fintype (ClassGroup (𝓞 (CyclotomicField p ℚ)))]
    (hreg : p.Coprime <|
      Fintype.card <| ClassGroup (𝓞 (CyclotomicField p ℚ))) :
    BernoulliRegular.CaseIIBridge p (CyclotomicField p ℚ) i :=
  caseIIBridge_of_specificDischarges hodd i
    (caseIIPrincipalDischargeOnSpecific_of_regular
      p (CyclotomicField p ℚ) hreg)
    (adaptedKummersLemmaOnSpecific_of_regular
      (p := p) (K := CyclotomicField p ℚ) hreg hodd)

end CaseII

end LehmerVandiver

end FLT37

end BernoulliRegular

end
