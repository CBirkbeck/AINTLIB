import BernoulliRegular.FLT37.LehmerVandiver.CaseII.PrincipalDischarge
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.SpecificDischarge
import FltRegular.CaseII.InductionStep

/-!
# LV-CaseII parametric `a_div_principal`

Mirror of flt-regular's `FltRegular.CaseII.InductionStep.a_div_principal`,
with regularity replaced by `CaseIIPrincipalDischarge p K`.

The regularity-free part of the case II setup gives:
`((𝔞 η₁)/(𝔞 η₂))^p` is principal (as a fractional ideal in `K`).

Under regularity, flt-regular concludes `(𝔞 η₁)/(𝔞 η₂)` is principal
itself via `isPrincipal_of_isPrincipal_pow_of_Coprime'`. Under
`CaseIIPrincipalDischarge p K`, we make the same conclusion
parametrically.

This is the LV-route's parametric form of the case II
principalization step. Combined with `AdaptedKummersLemma p K`, it
parametrises flt-regular's case-II inductive descent.

## References

* flt-regular's `FltRegular.CaseII.InductionStep.a_div_principal`.
* `CaseIIPrincipalDischarge` (this project).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseII

variable {p : ℕ} [hpri : Fact p.Prime] [NeZero p]
  {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x y z : 𝓞 K} {ε : (𝓞 K)ˣ}
variable {m : ℕ} (e : x ^ p + y ^ p =
  ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
variable (hy : ¬ hζ.toInteger - 1 ∣ y)
variable (hz : ¬ hζ.toInteger - 1 ∣ z)

include hp hy

/-- **`a_div_principal` adapted to `CaseIIPrincipalDischarge`.** Mirror of
flt-regular's `a_div_principal` but parametric on the principalization
discharge predicate.

The regularity-free input is `(𝔞 η₁/𝔞 η₂)^p` principal (from
`c_div_principal`). The discharge predicate then concludes the
fractional ideal itself is principal. -/
theorem a_div_principal_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K)
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) :
    Submodule.IsPrincipal
      (((rootDivZetaSubOneDvdGcd hp hζ e hy η₁) /
        (rootDivZetaSubOneDvdGcd hp hζ e hy η₂)
        : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  apply h_discharge
  rw [div_pow, ← FractionalIdeal.coeIdeal_pow, ← FractionalIdeal.coeIdeal_pow,
    root_div_zeta_sub_one_dvd_gcd_spec, root_div_zeta_sub_one_dvd_gcd_spec]
  exact c_div_principal hp hζ e hy η₁ η₂

include hz in
omit hz in
/-- **`isPrincipal_a_div_a_zero` adapted to `CaseIIPrincipalDischarge`.**
Mirror of flt-regular's `isPrincipal_a_div_a_zero` using the parametric
`a_div_principal_of_discharge` instead of the regularity-based version.

For any `p`-th root `η`, the fractional ideal `𝔞 η / 𝔞₀` is principal,
where `𝔞₀ = aEtaZeroDvdPPow ...`. -/
theorem isPrincipal_a_div_a_zero_of_discharge (h_discharge : CaseIIPrincipalDischarge p K)
    (η : nthRootsFinset p (1 : 𝓞 K)) :
    Submodule.IsPrincipal
      ((rootDivZetaSubOneDvdGcd hp hζ e hy η /
        aEtaZeroDvdPPow hp hζ e hy
        : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  have := a_div_principal_of_discharge hp hζ e hy h_discharge η
    (zetaSubOneDvdRoot hp hζ e hy)
  rw [← a_eta_zero_dvd_p_pow_spec, mul_comm, FractionalIdeal.coeIdeal_mul, ← div_div,
   FractionalIdeal.isPrincipal_iff] at this
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

include hz in
/-- **`exists_not_dvd_spanSingleton_eq_a_div_a_zero` adapted.** Mirror
of flt-regular's lemma with the parametric `isPrincipal_a_div_a_zero_of_discharge`. -/
theorem exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ∃ a b : 𝓞 K, ¬ (hζ.toInteger - 1) ∣ a ∧ ¬ (hζ.toInteger - 1) ∣ b ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / b : K) =
        rootDivZetaSubOneDvdGcd hp hζ e hy η /
        aEtaZeroDvdPPow hp hζ e hy :=
  exists_not_dvd_spanSingleton_eq hζ.zeta_sub_one_prime'
    _ _ ((p_dvd_a_iff hp hζ e hy η).not.mpr hη) (not_p_div_a_zero hp hζ e hy hz)
      (isPrincipal_a_div_a_zero_of_discharge hp hζ e hy h_discharge η)

/-- Numerator from `exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_discharge`. -/
noncomputable
def a_div_a_zero_num_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) : 𝓞 K :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_discharge
    hp hζ e hy hz h_discharge η hη).choose

/-- Denominator from `exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_discharge`. -/
noncomputable
def a_div_a_zero_denom_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) : 𝓞 K :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_discharge
    hp hζ e hy hz h_discharge η hη).choose_spec.choose

/-- Numerator is not divisible by `(ζ-1)`. -/
theorem a_div_a_zero_num_spec_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ¬ (hζ.toInteger - 1) ∣ a_div_a_zero_num_of_discharge hp hζ e hy hz h_discharge η hη :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_discharge
    hp hζ e hy hz h_discharge η hη).choose_spec.choose_spec.1

/-- Denominator is not divisible by `(ζ-1)`. -/
theorem a_div_a_zero_denom_spec_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ¬ (hζ.toInteger - 1) ∣ a_div_a_zero_denom_of_discharge hp hζ e hy hz h_discharge η hη :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_discharge
    hp hζ e hy hz h_discharge η hη).choose_spec.choose_spec.2.1

/-- `α/β = 𝔞 η / 𝔞₀` as fractional ideals. -/
theorem a_div_a_zero_eq_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (a_div_a_zero_num_of_discharge hp hζ e hy hz h_discharge η hη /
         a_div_a_zero_denom_of_discharge hp hζ e hy hz h_discharge η hη : K) =
      rootDivZetaSubOneDvdGcd hp hζ e hy η /
        aEtaZeroDvdPPow hp hζ e hy :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero_of_discharge
    hp hζ e hy hz h_discharge η hη).choose_spec.choose_spec.2.2

/-- Ideal-level factorisation `𝔞 η · (β) = 𝔞₀ · (α)`. -/
theorem a_mul_denom_eq_a_zero_mul_num_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    rootDivZetaSubOneDvdGcd hp hζ e hy η *
        Ideal.span {a_div_a_zero_denom_of_discharge hp hζ e hy hz h_discharge η hη} =
      aEtaZeroDvdPPow hp hζ e hy *
        Ideal.span {a_div_a_zero_num_of_discharge hp hζ e hy hz h_discharge η hη} := by
  apply FractionalIdeal.coeIdeal_injective (K := K)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  rw [mul_comm (aEtaZeroDvdPPow hp hζ e hy : FractionalIdeal (𝓞 K)⁰ K),
    ← div_eq_div_iff,
    ← a_div_a_zero_eq_of_discharge hp hζ e hy hz h_discharge η hη,
    FractionalIdeal.spanSingleton_div_spanSingleton]
  · intro ha
    rw [FractionalIdeal.coeIdeal_eq_zero] at ha
    apply not_p_div_a_zero hp hζ e hy hz
    rw [ha]
    exact dvd_zero _
  · rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff, ← (algebraMap (𝓞 K) K).map_zero,
      (IsFractionRing.injective (𝓞 K) K).eq_iff]
    intro hβ
    apply a_div_a_zero_denom_spec_of_discharge hp hζ e hy hz h_discharge η hη
    rw [hβ]
    exact dvd_zero _

/-- Element-level associate identity (eqn 7.9 of Borevich-Shafarevich). -/
theorem associated_eta_zero_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    Associated ((x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) *
        a_div_a_zero_num_of_discharge hp hζ e hy hz h_discharge η hη ^ p)
      ((x + y * (η : 𝓞 K)) * (hζ.toInteger - 1) ^ (m * p) *
        a_div_a_zero_denom_of_discharge hp hζ e hy hz h_discharge η hη ^ p) := by
  simp_rw [← Ideal.span_singleton_eq_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
    ← m_mul_c_mul_p hp hζ e hy, ← root_div_zeta_sub_one_dvd_gcd_spec,
    ← a_eta_zero_dvd_p_pow_spec]
  rw [mul_comm _ (aEtaZeroDvdPPow hp hζ e hy), mul_pow]
  simp only [mul_assoc, mul_left_comm _ (Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)))]
  rw [mul_left_comm (rootDivZetaSubOneDvdGcd hp hζ e hy η ^ p),
    mul_left_comm (aEtaZeroDvdPPow hp hζ e hy ^ p),
    ← pow_mul, ← mul_pow, ← mul_pow,
    a_mul_denom_eq_a_zero_mul_num_of_discharge hp hζ e hy hz h_discharge η hη]

/-- Unit `ε η` witnessing the associate identity. -/
noncomputable
def associated_eta_zero_unit_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) : (𝓞 K)ˣ :=
  (associated_eta_zero_of_discharge hp hζ e hy hz h_discharge η hη).choose

/-- Specification of `ε η`: the explicit equation
`ε η · (x + y η₀) · α^p = (x + y η) · π^(m·p) · β^p`. -/
theorem associated_eta_zero_unit_spec_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    (associated_eta_zero_unit_of_discharge hp hζ e hy hz h_discharge η hη : 𝓞 K) *
        (x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) *
        a_div_a_zero_num_of_discharge hp hζ e hy hz h_discharge η hη ^ p =
      (x + y * (η : 𝓞 K)) * (hζ.toInteger - 1) ^ (m * p) *
        a_div_a_zero_denom_of_discharge hp hζ e hy hz h_discharge η hη ^ p := by
  rw [mul_assoc,
    mul_comm (associated_eta_zero_unit_of_discharge hp hζ e hy hz h_discharge η hη : 𝓞 K)]
  exact (associated_eta_zero_of_discharge hp hζ e hy hz h_discharge η hη).choose_spec

/-- The case II `formula` (Vandiver): combining two pairs `(η₁, η₂)`
with both ≠ η₀, derives a sum equation involving the α, β, ε data. -/
theorem formula_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K)
    (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K))
    (hη₁ : η₁ ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη₂ : η₂ ≠ zetaSubOneDvdRoot hp hζ e hy) :
    ((η₂ : 𝓞 K) - (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) *
        (associated_eta_zero_unit_of_discharge hp hζ e hy hz h_discharge η₁ hη₁ : 𝓞 K) *
        (a_div_a_zero_num_of_discharge hp hζ e hy hz h_discharge η₁ hη₁ *
         a_div_a_zero_denom_of_discharge hp hζ e hy hz h_discharge η₂ hη₂) ^ p +
      ((zetaSubOneDvdRoot hp hζ e hy : 𝓞 K) - (η₁ : 𝓞 K)) *
        (associated_eta_zero_unit_of_discharge hp hζ e hy hz h_discharge η₂ hη₂ : 𝓞 K) *
        (a_div_a_zero_num_of_discharge hp hζ e hy hz h_discharge η₂ hη₂ *
         a_div_a_zero_denom_of_discharge hp hζ e hy hz h_discharge η₁ hη₁) ^ p =
      ((η₂ : 𝓞 K) - (η₁ : 𝓞 K)) *
        ((hζ.toInteger - 1) ^ m *
          (a_div_a_zero_denom_of_discharge hp hζ e hy hz h_discharge η₁ hη₁ *
           a_div_a_zero_denom_of_discharge hp hζ e hy hz h_discharge η₂ hη₂)) ^ p := by
  rw [← mul_right_inj' (x_plus_y_mul_ne_zero hp hζ e hz
    (zetaSubOneDvdRoot hp hζ e hy)), mul_add]
  simp_rw [mul_left_comm (x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)),
    mul_pow, mul_assoc,
    mul_left_comm ((η₂ : 𝓞 K) - (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)),
    mul_left_comm ((zetaSubOneDvdRoot hp hζ e hy : 𝓞 K) - (η₁ : 𝓞 K)),
    ← mul_assoc,
    associated_eta_zero_unit_spec_of_discharge hp hζ e hy hz h_discharge,
    mul_assoc,
    ← mul_left_comm ((η₂ : 𝓞 K) - (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)),
    ← mul_left_comm ((zetaSubOneDvdRoot hp hζ e hy : 𝓞 K) - (η₁ : 𝓞 K)),
    pow_mul, ← mul_pow,
    mul_comm (a_div_a_zero_denom_of_discharge hp hζ e hy hz h_discharge η₂ hη₂),
    ← mul_assoc]
  rw [← add_mul]
  congr 1
  ring

include hp e hz in
/-- **`exists_solution` adapted to `CaseIIPrincipalDischarge`.** Mirror
of flt-regular's `exists_solution` using the parametric `formula` and
related ports.

From the case-II Kummer-form equation
`x^p + y^p = ε * ((ζ-1)^(m+1) * z)^p`, derives a smaller equation
of similar shape with three units `ε₁, ε₂, ε₃` and elements
`x', y', z'` not divisible by `π = ζ-1`. -/
theorem exists_solution_of_discharge
    (h_discharge : CaseIIPrincipalDischarge p K) :
    ∃ (x' y' z' : 𝓞 K) (ε₁ ε₂ ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ x' ∧
      ¬ (hζ.toInteger - 1) ∣ y' ∧
      ¬ (hζ.toInteger - 1) ∣ z' ∧
      (ε₁ : 𝓞 K) * x' ^ p + (ε₂ : 𝓞 K) * y' ^ p =
        (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p := by
  set η₀ := zetaSubOneDvdRoot hp hζ e hy
  have h₁ := mul_mem_nthRootsFinset (η₀ : _).prop
    (hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset hpri.out.pos)
  rw [one_mul] at h₁
  let η₁ : nthRootsFinset p (1 : 𝓞 K) := ⟨(η₀ : 𝓞 K) * hζ.toInteger, h₁⟩
  have h₂ := mul_mem_nthRootsFinset (η₁ : _).prop
    (hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset hpri.out.pos)
  rw [one_mul] at h₂
  let η₂ : nthRootsFinset p (1 : 𝓞 K) := ⟨(η₀ : 𝓞 K) * hζ.toInteger * hζ.toInteger, h₂⟩
  have hη₁ : η₁ ≠ η₀ := by
    rw [← Subtype.coe_injective.ne_iff]
    change ((η₀ : 𝓞 K) * hζ.toInteger : 𝓞 K) ≠ (η₀ : 𝓞 K)
    rw [Ne, mul_right_eq_self₀, not_or]
    exact ⟨hζ.toInteger_isPrimitiveRoot.ne_one hpri.out.one_lt,
      ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop⟩
  have hη₂ : η₂ ≠ η₀ := by
    rw [← Subtype.coe_injective.ne_iff]
    change ((η₀ : 𝓞 K) * hζ.toInteger * hζ.toInteger : 𝓞 K) ≠ (η₀ : 𝓞 K)
    rw [Ne, mul_assoc, ← pow_two, mul_right_eq_self₀, not_or]
    exact ⟨hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega)
      (hpri.out.two_le.lt_or_eq.resolve_right hp.symm),
      ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop⟩
  have hη : η₂ ≠ η₁ := by
    rw [← Subtype.coe_injective.ne_iff]
    change ((η₀ : 𝓞 K) * hζ.toInteger * hζ.toInteger : 𝓞 K) ≠ (η₀ : 𝓞 K) * hζ.toInteger
    rw [Ne, mul_right_eq_self₀, not_or]
    exact ⟨hζ.toInteger_isPrimitiveRoot.ne_one hpri.out.one_lt,
      mul_ne_zero (ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop)
      (hζ.toInteger_isPrimitiveRoot.ne_zero hpri.out.ne_zero)⟩
  obtain ⟨u₁, hu₁⟩ :=
    hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out η₂.prop (η₀ : _).prop (Subtype.coe_injective.ne_iff.mpr hη₂)
  obtain ⟨u₂, hu₂⟩ :=
    hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out (η₀ : _).prop η₁.prop (Subtype.coe_injective.ne_iff.mpr hη₁.symm)
  obtain ⟨u₃, hu₃⟩ :=
    hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out η₂.prop (η₁ : _).prop (Subtype.coe_injective.ne_iff.mpr hη)
  have := formula_of_discharge hp hζ e hy hz h_discharge η₁ η₂ hη₁ hη₂
  rw [← hu₁, ← hu₂, ← hu₃,
    mul_assoc _ (u₁ : 𝓞 K), mul_assoc _ (u₂ : 𝓞 K), mul_assoc _ (u₃ : 𝓞 K),
    mul_assoc (hζ.toInteger - 1), mul_assoc (hζ.toInteger - 1), ← mul_add,
    mul_right_inj' (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt),
    ← Units.val_mul, ← Units.val_mul] at this
  refine ⟨_, _, _, _, _, _, ?_, ?_, ?_, this⟩
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul
      (a_div_a_zero_num_spec_of_discharge hp hζ e hy hz h_discharge η₁ hη₁)
      (a_div_a_zero_denom_spec_of_discharge hp hζ e hy hz h_discharge η₂ hη₂)
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul
      (a_div_a_zero_num_spec_of_discharge hp hζ e hy hz h_discharge η₂ hη₂)
      (a_div_a_zero_denom_spec_of_discharge hp hζ e hy hz h_discharge η₁ hη₁)
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul
      (a_div_a_zero_denom_spec_of_discharge hp hζ e hy hz h_discharge η₁ hη₁)
      (a_div_a_zero_denom_spec_of_discharge hp hζ e hy hz h_discharge η₂ hη₂)

include hp e hy hz in
/-- **`exists_solution'` adapted to two discharges.** Mirror of
flt-regular's `exists_solution'` using the parametric
`exists_solution_of_discharge` and `AdaptedKummersLemma` instead of
regularity-based versions.

Reduces the case-II Kummer-form equation
`x^p + y^p = ε * ((ζ-1)^(m+1) * z)^p` to a strictly smaller form
`x'^p + y'^p = ε₃ * ((ζ-1)^m * z')^p` (with multiplicity `m` instead
of `m+1`). This is the inductive descent. -/
theorem exists_solution'_of_discharges
    (h_discharge : CaseIIPrincipalDischarge p K)
    (h_kummer : AdaptedKummersLemma p K) :
    ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬ (hζ.toInteger - 1) ∣ y' ∧ ¬ (hζ.toInteger - 1) ∣ z' ∧
      x' ^ p + y' ^ p = (ε₃ : 𝓞 K) * ((hζ.toInteger - 1) ^ m * z') ^ p := by
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ :=
    exists_solution_of_discharge hp hζ e hy hz h_discharge
  obtain ⟨ε', hε'⟩ : ∃ ε', ε₁ / ε₂ = ε' ^ p := by
    apply h_kummer
    have hp_le : p - 1 ≤ m * p := (Nat.sub_le _ _).trans
      ((le_of_eq (one_mul _).symm).trans (Nat.mul_le_mul_right p (one_le_m hp hζ e hy hz)))
    obtain ⟨u, hu⟩ := (associated_zeta_sub_one_pow_prime hζ).symm
    rw [mul_pow, ← pow_mul, mul_comm (ε₃ : 𝓞 K), mul_assoc, ← Nat.sub_add_cancel hp_le,
      add_comm _ (p - 1), pow_add, mul_assoc] at e'
    apply_fun Ideal.Quotient.mk (Ideal.span <| singleton ((p : ℕ) : 𝓞 K)) at e'
    rw [map_mul, (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr
      (associated_zeta_sub_one_pow_prime hζ).symm.dvd, zero_mul,
      Ideal.Quotient.eq_zero_iff_dvd] at e'
    obtain ⟨a, ha⟩ := exists_solution'_aux hp hζ hx' e'
    obtain ⟨b, hb⟩ := exists_dvd_pow_sub_Int_pow hp a
    have := dvd_add ha hb
    rw [sub_add_sub_cancel, ← Int.cast_pow] at this
    exact ⟨b ^ p, this⟩
  refine ⟨ε' * x', y', z', ε₃ / ε₂, hy', hz', ?_⟩
  rwa [mul_pow, ← Units.val_pow_eq_pow_val, ← hε', ← mul_right_inj' ε₂.isUnit.ne_zero,
    mul_add, ← mul_assoc, ← Units.val_mul, mul_div_cancel,
    ← mul_assoc, ← Units.val_mul, mul_div_cancel]

include hp in
omit hy in
/-- **`not_exists_solution` adapted to two discharges.** Mirror of
flt-regular's `not_exists_solution` using the parametric
`exists_solution'_of_discharges`.

For all multiplicities `m ≥ 1`, no solution exists to the case-II
Kummer-form equation
`x^p + y^p = ε₃ * ((ζ-1)^m * z)^p` with `ζ-1 ∤ y`, `ζ-1 ∤ z`. -/
theorem not_exists_solution_of_discharges (h_discharge : CaseIIPrincipalDischarge p K)
    (h_kummer : AdaptedKummersLemma p K)
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
        (exists_solution'_of_discharges hp hζ e'' hy'' hz'' h_discharge h_kummer)

include hp in
omit hy in
/-- **`not_exists_solution'` adapted.** From `x^p + y^p = z^p` with
`(ζ-1) ∣ z`, derive a contradiction by extracting the multiplicity of
`(ζ-1)` in `z` and applying `not_exists_solution_of_discharges`. -/
theorem not_exists_solution'_of_discharges (h_discharge : CaseIIPrincipalDischarge p K)
    (h_kummer : AdaptedKummersLemma p K) :
    ¬∃ (x y z : 𝓞 K),
      ¬ (hζ.toInteger - 1) ∣ y ∧
      (hζ.toInteger - 1) ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  letI : Fact (Nat.Prime p) := hpri
  letI : WfDvdMonoid (𝓞 K) := IsNoetherianRing.wfDvdMonoid
  rintro ⟨x', y', z', hy', hz', hz_ne', e'⟩
  obtain ⟨n, z'', hn, hz_n, rfl⟩ :
    ∃ n z'', 1 ≤ n ∧ ¬ ((hζ.toInteger - 1) ∣ z'') ∧
      z' = (hζ.toInteger - 1) ^ n * z'' := by
    classical
    have H : FiniteMultiplicity (hζ.toInteger - 1) z' :=
      FiniteMultiplicity.of_not_isUnit hζ.zeta_sub_one_prime'.not_unit hz_ne'
    obtain ⟨z'', h⟩ := pow_multiplicity_dvd (hζ.toInteger - 1) z'
    refine ⟨_, _, ?_, ?_, h⟩
    · rwa [← Nat.cast_le (α := ENat),
        ← FiniteMultiplicity.emultiplicity_eq_multiplicity H,
        ← pow_dvd_iff_le_emultiplicity, pow_one]
    · intro h_dvd
      have := mul_dvd_mul_left
        ((hζ.toInteger - 1) ^ multiplicity (hζ.toInteger - 1) z') h_dvd
      rw [← pow_succ, ← h] at this
      refine not_pow_dvd_of_emultiplicity_lt ?_ this
      rw [FiniteMultiplicity.emultiplicity_eq_multiplicity H, Nat.cast_lt]
      exact Nat.lt_succ_self _
  refine not_exists_solution_of_discharges hp hζ h_discharge h_kummer hn
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

set_option backward.isDefEq.respectTransparency false in
/-- **`not_exists_Int_solution` adapted to two discharges.** Mirror of
flt-regular's lemma, parametric on
`CaseIIPrincipalDischarge p (CyclotomicField p ℚ)` and
`AdaptedKummersLemma p (CyclotomicField p ℚ)`. -/
theorem not_exists_Int_solution_of_discharges
    {p : ℕ} [hpri : Fact p.Prime]
    (h_discharge : CaseIIPrincipalDischarge p (CyclotomicField p ℚ))
    (h_kummer : AdaptedKummersLemma p (CyclotomicField p ℚ))
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
  refine not_exists_solution'_of_discharges (K := CyclotomicField p ℚ)
    hodd hζ h_discharge h_kummer
    ⟨x, y, z, hy, hz, ?_, ?_⟩
  · rwa [ne_eq, Int.cast_eq_zero]
  · simp_rw [← Int.cast_pow, ← Int.cast_add, e]

set_option backward.isDefEq.respectTransparency false in
/-- **`not_exists_Int_solution'` adapted.** Standard transformation
from `gcd = 1 + p ∣ z + z ≠ 0 + ...` to the form expected by
`not_exists_Int_solution_of_discharges`. -/
theorem not_exists_Int_solution'_of_discharges
    {p : ℕ} [hpri : Fact p.Prime]
    (h_discharge : CaseIIPrincipalDischarge p (CyclotomicField p ℚ))
    (h_kummer : AdaptedKummersLemma p (CyclotomicField p ℚ))
    (hodd : p ≠ 2) :
    ¬∃ (x y z : ℤ),
      ({x, y, z} : Finset ℤ).gcd id = 1 ∧ (p : ℤ) ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  rintro ⟨x, y, z, hgcd, hz, hz', e⟩
  refine not_exists_Int_solution_of_discharges h_discharge h_kummer hodd
    ⟨x, y, z, ?_, hz, hz', e⟩
  intro hy
  have h_dvd : (p : ℤ) ∣ x ^ p := by
    have := dvd_sub (dvd_pow hz hpri.out.ne_zero) (dvd_pow hy hpri.out.ne_zero)
    rw [← e, add_sub_cancel_right] at this
    exact this
  have hp_x : (p : ℤ) ∣ x :=
    (Nat.prime_iff_prime_int.mp hpri.out).dvd_of_dvd_pow h_dvd
  apply (Nat.prime_iff_prime_int.mp hpri.out).not_unit
  rw [isUnit_iff_dvd_one, ← hgcd]
  simp [dvd_gcd_iff, hz, hy, hp_x]

set_option backward.isDefEq.respectTransparency false in
/-- **`caseII` adapted to two discharges (integer form).** Mirror of
flt-regular's `caseII` with parametric inputs. -/
theorem caseII_of_discharges
    {a b c : ℤ} {p : ℕ} [hpri : Fact p.Prime]
    (h_discharge : CaseIIPrincipalDischarge p (CyclotomicField p ℚ))
    (h_kummer : AdaptedKummersLemma p (CyclotomicField p ℚ))
    (hodd : p ≠ 2)
    (hprod : a * b * c ≠ 0) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcase : (p : ℤ) ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p := by
  intro e
  simp only [ne_eq, mul_eq_zero, not_or] at hprod
  obtain ⟨⟨a0, b0⟩, c0⟩ := hprod
  have hodd' := Nat.Prime.odd_of_ne_two hpri.out hodd
  obtain hab | hc := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd hcase
  · obtain ha | hb := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd hab
    · refine not_exists_Int_solution'_of_discharges h_discharge h_kummer hodd
        ⟨b, -c, -a, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
          ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ a]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hodd'.neg_pow, ← e]
    · refine not_exists_Int_solution'_of_discharges h_discharge h_kummer hodd
        ⟨-c, a, -b, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
          ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ c]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hodd'.neg_pow, ← e]
  · exact not_exists_Int_solution'_of_discharges h_discharge h_kummer hodd
      ⟨a, b, c, hgcd, hc, c0, e⟩

set_option backward.isDefEq.respectTransparency false in
/-- **`caseIIBridge_of_discharges`**: build a `CaseIIBridge p K i` term
parametric on `CaseIIPrincipalDischarge` and `AdaptedKummersLemma`.

The hypothesis arguments `¬ p ∣ hPlus K` and `NoSecondOrderIrregularPair p i`
in the underlying `CaseIIBridge` structure are accepted but not used:
the discharges already encapsulate the deep CFT content under
`¬ p ∣ h⁺` + Kellner condition. -/
def caseIIBridge_of_discharges
    {p : ℕ} [hpri : Fact p.Prime] (hodd : p ≠ 2) (i : ℕ)
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    (h_discharge : CaseIIPrincipalDischarge p (CyclotomicField p ℚ))
    (h_kummer : AdaptedKummersLemma p (CyclotomicField p ℚ)) :
    BernoulliRegular.CaseIIBridge p (CyclotomicField p ℚ) i where
  no_caseII_solution := fun _ _ _ _ _ hprod hgcd hcase ↦
    caseII_of_discharges h_discharge h_kummer hodd hprod hgcd hcase

set_option backward.isDefEq.respectTransparency false in
/-- **`caseIIBridge_of_regular` — compatibility check.** Direct
constructor of `CaseIIBridge` from regularity: under regularity, both
`CaseIIPrincipalDischarge` and `AdaptedKummersLemma` hold (via the
regular-prime fills), so the bridge is fully constructible.

Sanity check: the LV-route's parametric structure recovers
flt-regular's case-II bridge for regular primes. -/
def caseIIBridge_of_regular
    {p : ℕ} [hpri : Fact p.Prime] (hodd : p ≠ 2) (i : ℕ)
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    [Fintype (ClassGroup (𝓞 (CyclotomicField p ℚ)))]
    (hreg : p.Coprime <|
      Fintype.card <| ClassGroup (𝓞 (CyclotomicField p ℚ))) :
    BernoulliRegular.CaseIIBridge p (CyclotomicField p ℚ) i :=
  caseIIBridge_of_discharges hodd i
    (caseIIPrincipalDischarge_of_regular p (CyclotomicField p ℚ) hreg)
    (adaptedKummersLemma_of_regular p (CyclotomicField p ℚ) hreg hodd)

end CaseII

end LehmerVandiver

end FLT37

end BernoulliRegular

end
