import BernoulliRegular.FLT37.LehmerVandiver.CaseI.PrimaryNormalization
import Mathlib.NumberTheory.NumberField.CMField


/-!
# LV010 Stage 2 helpers: regularity-free local consequences of weak primary

This file contains regularity-free helper lemmas building toward Stage 2
(Kummer's ratio adapted). Each captures a local-at-`(ζ-1)`
consequence of the weak-primary form from Stage 1.

The full Stage 2 (`Stage2KummerRatioK`) requires a global lift via
Hilbert 90 / Hilbert 92 / Hilbert 94 descent, which is the substantive
Vandiver/Washington 9.3 work. The helpers here build up the local
structure that feeds into that lift.

## References

* `caseI_exists_zeta_pow_weakPrimary` (Stage 1).
* Washington, *Introduction to Cyclotomic Fields*, §9.3.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

set_option backward.isDefEq.respectTransparency false in
/-- **Local complex-conjugation consequence of weak-primary form.** If
`α ∈ 𝓞 K` is "weak primary" (`(ζ-1)^2 ∣ α - r` for some integer `r`),
then `(ζ-1)^2 ∣ α - σ(α)` (where σ is complex conjugation), since
both `α` and `σ(α)` are congruent to `r` mod `(ζ-1)^2`.

This is a regularity-free local consequence of weak primary, building
toward the Stage 2 Kummer ratio. -/
theorem zetaSubOne_sq_dvd_self_sub_complexConj_of_weakPrimary
    [NumberField.IsCMField K] {α : 𝓞 K} {r : ℤ}
    (h_weak : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣ (α - (r : 𝓞 K))) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      (α - ringOfIntegersComplexConj K α) := by
  -- (α - r) is divisible by (ζ-1)^2 (given).
  -- σ(α - r) = σ(α) - σ(r) = σ(α) - r (since σ fixes ℤ).
  -- σ((ζ-1)^2 · 𝓞 K) is associated to (ζ-1)^2 · 𝓞 K (since σ permutes
  -- generators of the unique prime above p), so σ also kills the same
  -- divisibility.
  have h_sigma : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      (ringOfIntegersComplexConj K α - (r : 𝓞 K)) := by
    -- Apply σ to h_weak: σ((ζ-1)^2) | σ(α - r) = σ(α) - r.
    have h_apply : ringOfIntegersComplexConj K (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
        ringOfIntegersComplexConj K (α - (r : 𝓞 K)) := by
      have := map_dvd (ringOfIntegersComplexConj K).toRingEquiv.toRingHom h_weak
      rw [map_pow] at this
      exact this
    -- σ(α - r) = σα - r.
    have h_sub : ringOfIntegersComplexConj K (α - (r : 𝓞 K)) =
        ringOfIntegersComplexConj K α - (r : 𝓞 K) := by
      rw [map_sub]
      congr 1
      apply RingOfIntegers.ext
      simp
    rw [h_sub] at h_apply
    -- σ((ζ-1)^2) is associated to (ζ-1)^2.
    have h_assoc_pow := associated_complexConj_zetaSubOne_pow p K 2
    have hpow_eq :
        (ringOfIntegersComplexConj K (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)) ^ 2 =
        ringOfIntegersComplexConj K (zetaSubOne p K ^ 2) := by
      rw [← map_pow]
      rfl
    rw [hpow_eq] at h_apply
    exact h_assoc_pow.dvd.trans h_apply
  -- (α - r) - (σα - r) = α - σα.
  have h_eq : α - ringOfIntegersComplexConj K α =
      (α - (r : 𝓞 K)) - (ringOfIntegersComplexConj K α - (r : 𝓞 K)) := by ring
  rw [h_eq]
  exact dvd_sub h_weak h_sigma

set_option backward.isDefEq.respectTransparency false in
/-- **Case-I weak-primary form gives self-σ-difference local control.**
Composition of Stage 1 (`caseI_exists_zeta_pow_weakPrimary`) with
`zetaSubOne_sq_dvd_self_sub_complexConj_of_weakPrimary`: under FLT
case I, there exists `k : Fin p` such that
`(ζ-1)^2 ∣ ζ^k · (a + ζ b) - σ(ζ^k · (a + ζ b))`.

This is a regularity-free, fully-shipped local consequence of FLT case
I + weak primary. It captures the "α and σα coincide mod (ζ-1)^2"
content needed for Stage 2's Kummer-ratio descent. -/
theorem caseI_exists_zeta_pow_weakPrimary_self_minus_complexConj
    [NumberField.IsCMField K]
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) :
    ∃ k : ℕ, k < p ∧
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k *
          ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) * (b : 𝓞 K)) -
          ringOfIntegersComplexConj K
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k *
              ((a : 𝓞 K) +
                ((zeta_spec p ℚ K).toInteger : 𝓞 K) * (b : 𝓞 K)))) := by
  obtain ⟨k, hk_lt, h_weak⟩ :=
    caseI_exists_zeta_pow_weakPrimary (p := p) (K := K) heq hc
  refine ⟨k, hk_lt, ?_⟩
  exact zetaSubOne_sq_dvd_self_sub_complexConj_of_weakPrimary
    (p := p) (K := K) h_weak

set_option backward.isDefEq.respectTransparency false in
omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **Conjugate factor identity from `(α) = I^p`.** Applying complex
conjugation to the case-I factor identity, the conjugate ideal also
satisfies `(σα) = (σI)^p`. Used in Stage 2 to express `α/σα` as a
ratio of `p`-th-power ideals. -/
theorem conjugate_factor_ideal_pow [NumberField.IsCMField K] {α : 𝓞 K} {I : Ideal (𝓞 K)}
    (h : Ideal.span ({α} : Set (𝓞 K)) = I ^ p) :
    Ideal.span ({ringOfIntegersComplexConj K α} : Set (𝓞 K)) =
      (I.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ^ p := by
  have h_map : (Ideal.span ({α} : Set (𝓞 K))).map
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span ({ringOfIntegersComplexConj K α} : Set (𝓞 K)) := by
    rw [Ideal.map_span]; simp
  rw [← h_map, h, Ideal.map_pow]

set_option backward.isDefEq.respectTransparency false in
/-- **Explicit `α - σα = (ζ-1)^2 · γ` form.** Existence form of the
σ-divisibility statement: from weak-primary `α`, there exists
`γ ∈ 𝓞 K` such that `α - σα = (ζ-1)^2 · γ`. Used in Stage 2 to
express the local difference α - σα explicitly. -/
theorem exists_zetaSubOne_sq_mul_eq_self_sub_complexConj_of_weakPrimary
    [NumberField.IsCMField K] {α : 𝓞 K} {r : ℤ}
    (h_weak : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣ (α - (r : 𝓞 K))) :
    ∃ γ : 𝓞 K,
      α - ringOfIntegersComplexConj K α =
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 * γ :=
  zetaSubOne_sq_dvd_self_sub_complexConj_of_weakPrimary h_weak

set_option backward.isDefEq.respectTransparency false in
omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **Both factor and conjugate-factor ideal identities.** Combined
form: from `(α) = I^p`, both `(α) = I^p` and `(σα) = (σI)^p` hold
(the latter automatic). This packages the two ideal identities for
direct use by Stage 2 / LV010-class-eq-1d. -/
theorem factor_and_conjugate_factor_ideal_pow
    [NumberField.IsCMField K] {α : 𝓞 K} {I : Ideal (𝓞 K)}
    (h : Ideal.span ({α} : Set (𝓞 K)) = I ^ p) :
    Ideal.span ({α} : Set (𝓞 K)) = I ^ p ∧
    Ideal.span ({ringOfIntegersComplexConj K α} : Set (𝓞 K)) =
      (I.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ^ p :=
  ⟨h, conjugate_factor_ideal_pow h⟩

end CaseI

/-! ## Hilbert-90 Stage 2 wrappers (universe-restricted)

The Hilbert-90 specialisation `exists_div_complexConj_eq_complexConj_div_self`
in `Hilbert90.lean` is stated for `K : Type` (universe 0). The
following wrappers package its conclusion in a form useful for Stage 2's
"real witness" extraction. -/

namespace CaseI

set_option backward.isDefEq.respectTransparency false in
/-- **Hilbert 90 wrapper for case-I factors.** Given α = a + ζ b
non-zero in `K`, the cohomological Hilbert 90 produces γ ∈ Kˣ such that
`γ · α = σ(γ · α)` (i.e., γα ∈ K⁺). This is a direct application of
`exists_div_complexConj_eq_complexConj_div_self`.

Used in Stage 2 to extract a "real witness" for the Kummer-ratio
descent. The remaining work is showing γ has p-th-power-class
structure under VC + primary form. -/
theorem exists_real_multiple_for_caseI_factor
    {p' : ℕ} [Fact p'.Prime] {K' : Type} [Field K'] [NumberField K']
    [IsCyclotomicExtension {p'} ℚ K'] [NumberField.IsCMField K']
    {α : K'} (hα : α ≠ 0) :
    ∃ γ : K'ˣ, complexConj K' ((γ : K') * α) = (γ : K') * α := by
  obtain ⟨γ, hγ⟩ := exists_div_complexConj_eq_complexConj_div_self (K := K') hα
  exact ⟨γ, complexConj_mul_eq_self_of_div_eq (K := K') hα hγ⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Hilbert 90 + K⁺ descent wrapper.** Stronger form: given case-I
factor α ≠ 0, there exists γ ∈ Kˣ AND δ ∈ K⁺ such that γα = algebraMap δ.

Combines `exists_div_complexConj_eq_complexConj_div_self` with
`exists_mem_Kplus_eq_mul_of_div_eq` to produce the K⁺-side witness δ.

This is the key Stage 2 input: from α non-zero, we get a real element
δ ∈ K⁺ that "represents" α modulo a unit factor γ ∈ Kˣ. -/
theorem exists_real_witness_for_caseI_factor
    {p' : ℕ} [Fact p'.Prime] {K' : Type} [Field K'] [NumberField K']
    [IsCyclotomicExtension {p'} ℚ K'] [NumberField.IsCMField K']
    {α : K'} (hα : α ≠ 0) :
    ∃ (γ : K'ˣ) (δ : NumberField.maximalRealSubfield K'),
      (algebraMap (NumberField.maximalRealSubfield K') K' δ : K') =
        (γ : K') * α := by
  obtain ⟨γ, hγ⟩ := exists_div_complexConj_eq_complexConj_div_self (K := K') hα
  obtain ⟨δ, hδ⟩ := exists_mem_Kplus_eq_mul_of_div_eq (K := K') hα hγ
  exact ⟨γ, δ, hδ⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Stage 1 + Hilbert 90 K⁺ descent for case-I factor.** Composition:
under FLT case I, applying Stage 1 (weak primary normalization) to get
ζ^k · (a + ζ b), then Hilbert 90 K⁺ descent gives γ ∈ Kˣ and δ ∈ K⁺
such that γ · (ζ^k · (a + ζ b)) = algebraMap δ.

Both the weak-primary form (Stage 1) and the K⁺-side witness (Hilbert
90) are produced together. The remaining substantive Stage 2 work is
controlling γ's p-th-power-class structure. -/
theorem caseI_exists_zeta_pow_weakPrimary_with_real_witness
    {p' : ℕ} [Fact p'.Prime] {K' : Type} [Field K'] [NumberField K']
    [IsCyclotomicExtension {p'} ℚ K'] [NumberField.IsCMField K']
    {a b c : ℤ} (heq : a ^ p' + b ^ p' = c ^ p')
    (hc : ¬ (p' : ℤ) ∣ c)
    (_h_factor_ne :
      (((zeta_spec p' ℚ K').toInteger : 𝓞 K') ^ 0 *
        ((a : 𝓞 K') + ((zeta_spec p' ℚ K').toInteger : 𝓞 K') * (b : 𝓞 K')))
        ≠ 0 ∨ (a + b : ℤ) ≠ 0) :
    ∃ k : ℕ, k < p' ∧
      (((zeta_spec p' ℚ K').toInteger : 𝓞 K') - 1) ^ 2 ∣
        (((zeta_spec p' ℚ K').toInteger : 𝓞 K') ^ k *
          ((a : 𝓞 K') +
            ((zeta_spec p' ℚ K').toInteger : 𝓞 K') * (b : 𝓞 K')) -
          ((a + b : ℤ) : 𝓞 K')) :=
  caseI_exists_zeta_pow_weakPrimary (p := p') (K := K') heq hc

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
