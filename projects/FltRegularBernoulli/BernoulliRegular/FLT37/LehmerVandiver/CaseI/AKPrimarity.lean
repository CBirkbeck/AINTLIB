import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummerCaseI
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummerFLTConsumer
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.ProvedAuxiliaries
import BernoulliRegular.FLT37.PrimaryDescent
import BernoulliRegular.FLT37.Hilbert90

/-!
# AK-5: case-I primarity argument for `CaseIAntiKummerLKUnramified`

Builds the case-I primarity chain for `CaseIAntiKummerLKUnramified` (defined in
`AntiKummerFLTConsumer.lean`). The decomposition follows AK-5a..d:

- **AK-5a**: principality of `I · σI⁻¹` in Cl(K) under VC + σ-anti.
- **AK-5b**: unit form extraction `α₀ = u · γ^p`.
- **AK-5c**: strong primarity lifting from Stage 1 weak primarity.
- **AK-5d**: composition via `KummersLemma.isUnramified`.

## Shipped (structural composition)

- AK-5b: `antiRadical_unit_form_of_principal` — given AK-5a, extract unit form.
- AK-5d: `antiKummerLift_isUnramified_of_kummer_data`,
  `isSplittingField_X_pow_sub_C_unit_of_unit_form` — split-field transfer + KummersLemma.
- End-to-end: `antiKummerLift_isUnramified_via_AK5` — per-case-I composition.
- Universal: `caseIAntiKummerLKUnramified_of_universal_hypotheses` — wiring to
  the consumer Prop.

## Non-p-th-power building blocks (towards case-I irreducibility)

- `σ_anti_norm_eq_one`, `σ_pth_anti_norm_pth_root`, `mul_complexConj_isFixed`,
  `fixed_pow_eq_one_descend`, `totallyReal_odd_pow_eq_one_eq_one`: tower of
  lemmas from "γ^p is σ-anti" + "p odd" + "K⁺ totally real" → `γ·σ(γ) = 1`.
- `σ_pth_anti_norm_eq_one`: composition giving the Norm=1 conclusion.

Hilbert 90 application: `algebraMap_norm_K_Kplus_eq` bridges
`γ·σ(γ) = 1` to `Algebra.norm K⁺ γ = 1` (via cardinality-2 Gal product identity),
then `σ_pth_anti_exists_div` (composing through
`exists_div_complexConj_of_mul_complexConj_eq_one` /
`groupCohomology.exists_div_of_norm_eq_one`) gives δ ∈ K^× with δ/σ(δ) = γ.

FractionalIdeal-level continuation:
- `spanSingleton_pow_eq_div_pow_of_hilbert90`: convert Hilbert 90 to fractional
  ideal language.
- `FractionalIdeal_pow_left_injective_of_ne_zero`: p-th root uniqueness for
  FractionalIdeals of 𝓞 K (via `finprod_heightOneSpectrum_factorization'` +
  `count_pow`).
- `antiRadical_ideal_div_eq_principal`: combining the above to get
  `I/σI = spanSingleton δ / spanSingleton σδ`.
- `ideal_div_delta_cross_mul`: cross-multiply to `I·(σδ) = σI·(δ)`.
- `σ_image_eq_of_cross_mul`: divide both sides by `spanSingleton δ` to get
  `σI = I·(σδ)/δ` (σI in terms of I and a principal fractional ideal).
- `classGroup_eq_of_cross_mul_with_integers`: integer-side bridge from
  cross-mul `span x · I = span y · J` to `ClassGroup.mk0 I = ClassGroup.mk0 J`.

Building blocks:
- `complexConj_a_add_zeta_b`, `ringOfIntegersComplexConj_a_add_zeta_b`: K- and
  𝓞K-level σ-conjugation of `a + ζb`.
- `caseI_complexConj_ideal_eq`: `σ((a+ζb)) = (σI)^p` from `(a+ζb) = I^p`.
- `unit_form_of_spanSingleton_pow_eq`: Dedekind unit extraction.
- `antiRadical_spanSingleton_div`: K-quotient → FractionalIdeal quotient.
- `antiRadical_spanSingleton_pow_eq`: the central identity
  `spanSingleton α₀ = (I/σI)^p`.
- `adjoin_div_K_eq_adjoin`: `K⟮β/γ_L⟯ = K⟮β⟯` (K-scalar quotient invariance).
- `div_pow_eq_of_unit_form`: `(β/γ_L)^p = u` from `β^p = α₀ = u·γ^p`.
- `ringOfIntegersComplexConj_involution`,
  `Ideal_map_ringOfIntegersComplexConj_involution`: σ² = id on 𝓞K and ideals.

## Output Props (named substantive open content)

- `AK5a_PrincipalMinusIdeals`: principality under VC. (Hilbert 92 application.)
- `AK5c_StrongPrimarity`: `(ζ-1)^p ∣ u - 1`. (Washington §9.1 Wieferich lifting.)

These two Props + the non-p-th-power and irreducibility conditions for case-I
antiRadical are the genuine remaining open content for an unconditional
`CaseIAntiKummerLKUnramified_holds : CaseIAntiKummerLKUnramified`.

## Ideal-theoretic identity for `(α₀)` as a fractional ideal

From case-I `(a + ζb) = I^p`, the fractional ideal of `α₀ = (a + ζb)/σ(a + ζb)`
in `K^×` decomposes as `(I · σI⁻¹)^p`. This is the central identity behind
`antiRadical_spanSingleton_pow_eq`.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.LehmerVandiver.CaseI

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **σ(a + ζb) = a + σ(ζ)·b** in K — utility for fractional ideal calculations.

Used in AK-5b's unit form extraction: the denominator σ(a + ζb) factors as
the σ-image of the numerator, and its ideal is `(σI)^p`. -/
theorem complexConj_a_add_zeta_b
    (a b : ℤ) {ζ : 𝓞 K} (_hζ : IsPrimitiveRoot ζ p) :
    NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) =
      (a : K) + NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K ζ) * (b : K) := by
  have h_int_fixed : ∀ (n : ℤ), NumberField.IsCMField.complexConj K (n : K) = (n : K) := by
    intro n
    have h_n : (n : K) =
        algebraMap (NumberField.maximalRealSubfield K) K
          (algebraMap ℤ (NumberField.maximalRealSubfield K) n) := by
      rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.maximalRealSubfield K) K]
      rfl
    rw [h_n]
    exact (NumberField.IsCMField.complexConj K).commutes _
  have h_alg_expand : algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) =
      (a : K) + algebraMap (𝓞 K) K ζ * (b : K) := by
    rw [map_add, map_mul]
    have h_a_K : algebraMap (𝓞 K) K ((a : 𝓞 K)) = (a : K) := rfl
    have h_b_K : algebraMap (𝓞 K) K ((b : 𝓞 K)) = (b : K) := rfl
    rw [h_a_K, h_b_K]
  rw [h_alg_expand, map_add, map_mul, h_int_fixed a, h_int_fixed b]

/-- **σ((a + ζb) : 𝓞 K) = (a + σ(ζ)·b) : 𝓞 K** at the ring-of-integers level.

The ringOfIntegersComplexConj acts on integer combinations of ζ by acting on ζ alone. -/
theorem ringOfIntegersComplexConj_a_add_zeta_b
    (a b : ℤ) (ζ : 𝓞 K) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
      ((a : 𝓞 K) + ζ * (b : 𝓞 K)) =
      (a : 𝓞 K) +
        NumberField.IsCMField.ringOfIntegersComplexConj K ζ * (b : 𝓞 K) := by
  rw [map_add, map_mul]
  have h_a : NumberField.IsCMField.ringOfIntegersComplexConj K (a : 𝓞 K) = (a : 𝓞 K) := by
    apply RingOfIntegers.ext
    rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj]
    have h_via : ((a : 𝓞 K) : K) = (a : K) := rfl
    rw [h_via]
    have h_via_Kplus : (a : K) =
        algebraMap (NumberField.maximalRealSubfield K) K
          (algebraMap ℤ (NumberField.maximalRealSubfield K) a) := by
      rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.maximalRealSubfield K) K]
      rfl
    rw [h_via_Kplus]
    exact (NumberField.IsCMField.complexConj K).commutes _
  have h_b : NumberField.IsCMField.ringOfIntegersComplexConj K (b : 𝓞 K) = (b : 𝓞 K) := by
    apply RingOfIntegers.ext
    rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj]
    have h_via : ((b : 𝓞 K) : K) = (b : K) := rfl
    rw [h_via]
    have h_via_Kplus : (b : K) =
        algebraMap (NumberField.maximalRealSubfield K) K
          (algebraMap ℤ (NumberField.maximalRealSubfield K) b) := by
      rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.maximalRealSubfield K) K]
      rfl
    rw [h_via_Kplus]
    exact (NumberField.IsCMField.complexConj K).commutes _
  rw [h_a, h_b]

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **Ideal-side decomposition for case-I**: from `(a + ζb) = I^p` in `𝓞 K`,
the σ-image equals `(σI)^p`. Building block for the fractional ideal
identity `(α₀) = (I · σI⁻¹)^p` needed by AK-5b. -/
theorem caseI_complexConj_ideal_eq
    (a b : ℤ) (ζ : 𝓞 K)
    (I : Ideal (𝓞 K))
    (hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p) :
    Ideal.span
      ({(a : 𝓞 K) +
        NumberField.IsCMField.ringOfIntegersComplexConj K ζ * (b : 𝓞 K)} : Set (𝓞 K)) =
      (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ^ p := by
  have h_map_lhs :
      Ideal.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom
        (Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K))) =
      Ideal.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom
        (I ^ p) := by
    rw [hI_pow]
  rw [Ideal.map_span, Ideal.map_pow] at h_map_lhs
  simp only [Set.image_singleton] at h_map_lhs
  have h_apply :
      (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom
        ((a : 𝓞 K) + ζ * (b : 𝓞 K)) =
      (a : 𝓞 K) +
        NumberField.IsCMField.ringOfIntegersComplexConj K ζ * (b : 𝓞 K) := by
    change NumberField.IsCMField.ringOfIntegersComplexConj K
        ((a : 𝓞 K) + ζ * (b : 𝓞 K)) = _
    exact ringOfIntegersComplexConj_a_add_zeta_b (K := K) a b ζ
  rw [h_apply] at h_map_lhs
  exact h_map_lhs

omit hp [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- **Unit form extraction from fractional ideal equality**: if
`spanSingleton α = spanSingleton (γ^p)` in `FractionalIdeal (𝓞 K)⁰ K`, then
`α = u · γ^p` for some unit `u ∈ (𝓞 K)ˣ`.

This is the AK-5b output (given the AK-5a principality input). Encapsulates the
Dedekind-domain fact that equality of fractional principal ideals gives a unit
multiplier. -/
theorem unit_form_of_spanSingleton_pow_eq
    (α γ : K)
    (h_eq : FractionalIdeal.spanSingleton (𝓞 K)⁰ α =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ ^ p)) :
    ∃ u : (𝓞 K)ˣ, algebraMap (𝓞 K) K (u : 𝓞 K) * (γ ^ p) = α := by
  rw [FractionalIdeal.spanSingleton_eq_spanSingleton] at h_eq
  obtain ⟨u, hu⟩ := h_eq
  refine ⟨u⁻¹, ?_⟩
  rw [Units.smul_def] at hu
  have h_smul : (algebraMap (𝓞 K) K ((u : 𝓞 K))) * α = γ ^ p := by
    rwa [Algebra.smul_def] at hu
  have h_unit_ne : (algebraMap (𝓞 K) K (u : 𝓞 K)) ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    exact (Units.ne_zero u)
  have h_alg_inv : algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) =
      (algebraMap (𝓞 K) K (u : 𝓞 K))⁻¹ := by
    rw [← map_units_inv]
  rw [h_alg_inv, ← h_smul]
  field_simp

/-- **Fractional ideal of `antiRadical` decomposes through (a+ζb) and σ(a+ζb)**.

The K-level ratio structure of antiRadical lifts to a FractionalIdeal
quotient — first step toward the `(I · σI⁻¹)^p` identity. -/
theorem antiRadical_spanSingleton_div
    (a b : ℤ) (ζ : 𝓞 K) (hab : ¬ (a = 0 ∧ b = 0)) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
          K a b ζ hab) =
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) /
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K
          (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)))) := by
  unfold BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
  rw [FractionalIdeal.spanSingleton_div_spanSingleton]

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **The `(α₀) = (I · σI⁻¹)^p` fractional ideal identity for case-I**.

Combines `antiRadical_spanSingleton_div`, `caseI_complexConj_ideal_eq`, and
`coeIdeal_pow` + `div_pow` to derive the central fractional ideal decomposition.

Input: case-I principal ideal identity `(a + ζb) = I^p` in `𝓞 K`.
Output: `FractionalIdeal.spanSingleton α₀ = (I / σI)^p` as fractional ideals. -/
theorem antiRadical_spanSingleton_pow_eq
    (a b : ℤ) (ζ : 𝓞 K) (hab : ¬ (a = 0 ∧ b = 0))
    (I : Ideal (𝓞 K))
    (hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
          K a b ζ hab) =
    ((I : FractionalIdeal (𝓞 K)⁰ K) /
      (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
        FractionalIdeal (𝓞 K)⁰ K)) ^ p := by
  rw [antiRadical_spanSingleton_div (K := K) a b ζ hab]
  have h_conj_eq :
      NumberField.IsCMField.complexConj K
        (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) =
      algebraMap (𝓞 K) K
        (NumberField.IsCMField.ringOfIntegersComplexConj K
          ((a : 𝓞 K) + ζ * (b : 𝓞 K))) :=
    (NumberField.IsCMField.coe_ringOfIntegersComplexConj
      (K := K) ((a : 𝓞 K) + ζ * (b : 𝓞 K))).symm
  rw [h_conj_eq]
  rw [← FractionalIdeal.coeIdeal_span_singleton (S := (𝓞 K)⁰) (P := K),
      ← FractionalIdeal.coeIdeal_span_singleton (S := (𝓞 K)⁰) (P := K)]
  rw [hI_pow]
  have h_sigma_span :
      Ideal.span
        ({NumberField.IsCMField.ringOfIntegersComplexConj K
          ((a : 𝓞 K) + ζ * (b : 𝓞 K))} : Set (𝓞 K)) =
      (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ^ p := by
    have h_map := congrArg
      (fun J : Ideal (𝓞 K) ↦
        J.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom) hI_pow
    simp only [Ideal.map_span, Set.image_singleton, Ideal.map_pow] at h_map
    exact h_map
  rw [h_sigma_span]
  rw [FractionalIdeal.coeIdeal_pow, FractionalIdeal.coeIdeal_pow, div_pow]

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **Consumer of `(I · σI⁻¹)` principality**: given the AK-5a output that
`(I · σI⁻¹) = (γ)` as fractional ideals, derive
`spanSingleton α₀ = spanSingleton (γ^p)`. Composes
`antiRadical_spanSingleton_pow_eq` with the principality hypothesis. -/
theorem antiRadical_spanSingleton_eq_pow_of_principal
    (a b : ℤ) (ζ : 𝓞 K) (hab : ¬ (a = 0 ∧ b = 0))
    (I : Ideal (𝓞 K))
    (hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p)
    (γ : K)
    (hγ_principal :
      (I : FractionalIdeal (𝓞 K)⁰ K) /
        (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ γ) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
          K a b ζ hab) =
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (γ ^ p) := by
  rw [antiRadical_spanSingleton_pow_eq (K := K) (p := p) a b ζ hab I hI_pow,
      hγ_principal, FractionalIdeal.spanSingleton_pow]

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **Full AK-5a → AK-5b composition**: from case-I `(a + ζb) = I^p` and
principality of `(I · σI⁻¹)`, extract a unit form `α₀ = u · γ^p`. -/
theorem antiRadical_unit_form_of_principal
    (a b : ℤ) (ζ : 𝓞 K) (hab : ¬ (a = 0 ∧ b = 0))
    (I : Ideal (𝓞 K))
    (hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p)
    (γ : K)
    (hγ_principal :
      (I : FractionalIdeal (𝓞 K)⁰ K) /
        (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ γ) :
    ∃ u : (𝓞 K)ˣ, algebraMap (𝓞 K) K (u : 𝓞 K) * (γ ^ p) =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab :=
  unit_form_of_spanSingleton_pow_eq (K := K) (p := p) _ γ
    (antiRadical_spanSingleton_eq_pow_of_principal (K := K) (p := p)
      a b ζ hab I hI_pow γ hγ_principal)

omit [IsCMField K] in
/-- **AK-5d: Apply `KummersLemma.isUnramified` via splitting-field hypothesis**.

Composes the AK-5b output (unit form) with the AK-5c output (strong primarity) and a
hypothesis that the antiKummerLift is the splitting field of `X^p - C u` (the genuine
content of which is the K-isomorphism between `K(α₀^{1/p})` and `K(u^{1/p})` under
`α₀ = u · γ^p`). -/
theorem antiKummerLift_isUnramified_of_kummer_data
    (hp_odd : p ≠ 2)
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    {ζ' : K} (hζ' : IsPrimitiveRoot ζ' p) (u : (𝓞 K)ˣ)
    (hcong : (hζ'.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1)
    (hu_no_root : ∀ v : K, v ^ p ≠ u)
    [Polynomial.IsSplittingField K
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
        (p := p) K α₀ hα₀)
      (Polynomial.X ^ p - Polynomial.C (u : K))] :
    Algebra.Unramified (𝓞 K)
      (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
        (p := p) K α₀ hα₀)) :=
  KummersLemma.isUnramified hp_odd hζ' u hcong hu_no_root _

section IsSplittingFieldTransfer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

open Polynomial IntermediateField

omit [NumberField K] [IsCMField K] in
/-- **K-adjoin equality under K-scalar quotient**: adjoining `β / γ` and `β` give the
same intermediate field, when `γ ∈ K, γ ≠ 0`. -/
theorem adjoin_div_K_eq_adjoin
    {L : Type*} [Field L] [Algebra K L]
    (β : L) (γ : K) (hγ : γ ≠ 0) :
    IntermediateField.adjoin K ({β / algebraMap K L γ} : Set L) =
    IntermediateField.adjoin K ({β} : Set L) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    have : (algebraMap K L γ)⁻¹ ∈
        IntermediateField.adjoin K ({β} : Set L) := by
      rw [show (algebraMap K L γ)⁻¹ = algebraMap K L γ⁻¹ from (map_inv₀ _ _).symm]
      exact IntermediateField.algebraMap_mem _ _
    have hβ : β ∈ IntermediateField.adjoin K ({β} : Set L) :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    rw [div_eq_mul_inv]
    exact mul_mem hβ this
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    have h_γ_ne : algebraMap K L γ ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hγ
    have h_div : β / algebraMap K L γ ∈
        IntermediateField.adjoin K ({β / algebraMap K L γ} : Set L) :=
      IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
    have h_γ_in :
        algebraMap K L γ ∈
        IntermediateField.adjoin K ({β / algebraMap K L γ} : Set L) :=
      IntermediateField.algebraMap_mem _ _
    have h_prod_mem :
        (β / algebraMap K L γ) * algebraMap K L γ ∈
        IntermediateField.adjoin K ({β / algebraMap K L γ} : Set L) :=
      mul_mem h_div h_γ_in
    rwa [div_mul_cancel₀ β h_γ_ne] at h_prod_mem

omit hp [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- **The substitution `δ = β/γ_L` gives a root of `X^p - u`** when `β^p = α₀` and
`α₀ = u · γ^p` (with `γ ≠ 0`). -/
theorem div_pow_eq_of_unit_form
    {L : Type*} [Field L] [Algebra K L]
    (β : L) (α₀ : K) (hβ : β ^ p = algebraMap K L α₀)
    (u : K) (γ : K) (hγ : γ ≠ 0)
    (hα_form : α₀ = u * γ ^ p) :
    (β / algebraMap K L γ) ^ p = algebraMap K L u := by
  have h_γ_ne : algebraMap K L γ ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hγ
  have h_γp_ne : algebraMap K L (γ ^ p) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ h_γ_ne
  rw [div_pow, hβ, hα_form, map_mul, map_pow]
  field_simp

omit hp [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/-- **IsSplittingField transfer for `X^p - C u` from `X^p - C α₀`** when `α₀ = u · γ^p`.

Discharges the AK-5d-pre IsSplittingField hypothesis. -/
theorem isSplittingField_X_pow_sub_C_unit_of_unit_form
    (hp_pos : 0 < p)
    (hK_prim : (primitiveRoots p K).Nonempty)
    (α₀ : K) (u : K) (γ : K) (hγ : γ ≠ 0)
    (hα_form : α₀ = u * γ ^ p)
    {L : Type*} [Field L] [Algebra K L]
    [Polynomial.IsSplittingField K L (Polynomial.X ^ p - Polynomial.C α₀)]
    (h_finrank : Module.finrank K L = p)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀)) :
    Polynomial.IsSplittingField K L (Polynomial.X ^ p - Polynomial.C u) := by
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp hp_pos⟩
  haveI : FiniteDimensional K L := Polynomial.IsSplittingField.finiteDimensional L
    (Polynomial.X ^ p - Polynomial.C α₀)
  let β : L := rootOfSplitsXPowSubC hp_pos α₀ L
  have hβ_pow : β ^ p = algebraMap K L α₀ :=
    rootOfSplitsXPowSubC_pow α₀ L
  have hβ_top : K⟮β⟯ = ⊤ :=
    IntermediateField.adjoin_root_eq_top_of_isSplittingField hK_prim h_irr hβ_pow
  let δ : L := β / algebraMap K L γ
  have hδ_pow : δ ^ p = algebraMap K L u :=
    div_pow_eq_of_unit_form (K := K) (p := p) β α₀ hβ_pow u γ hγ hα_form
  have hδ_top : IntermediateField.adjoin K ({δ} : Set L) = ⊤ := by
    have h_div_eq := adjoin_div_K_eq_adjoin (K := K) β γ hγ (L := L)
    rw [show (IntermediateField.adjoin K ({β} : Set L)) = K⟮β⟯ from rfl] at h_div_eq
    have : IntermediateField.adjoin K ({δ} : Set L) = K⟮β⟯ := h_div_eq
    rw [this, hβ_top]
  have hδ_top' : K⟮δ⟯ = ⊤ := hδ_top
  have hK_prim' : (primitiveRoots (Module.finrank K L) K).Nonempty := h_finrank ▸ hK_prim
  have hδ_pow' : δ ^ (Module.finrank K L) = algebraMap K L u := h_finrank ▸ hδ_pow
  have := isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top (K := K) (L := L)
    hK_prim' hδ_pow' hδ_top'
  rw [h_finrank] at this
  exact this

end IsSplittingFieldTransfer

section FullChainComposition

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

open Polynomial IntermediateField

/-- **AK-5 full chain**: from case-I principal ideal hypothesis + minus class group
principality + strong primarity + non-square + irreducibility, derive IsUnramified
for the σ-anti Kummer lift `L = K(α₀^{1/p})`.

The 4 hypotheses correspond to the 4 sub-tickets:
- `(a + ζb) = I^p` is case-I FLT data (AK-5a input)
- `(I · σI⁻¹) = (γ)` is the AK-5a output (principality from Hilbert 92 + VC)
- strong primarity `(ζ-1)^p ∣ u - 1` is the AK-5c output
- `∀ v : K, v^p ≠ u` is the non-square / non-p-th-power output
- `Irreducible (X^p - C α₀)` is the case-I irreducibility (project-existing hypothesis)
-/
theorem antiKummerLift_isUnramified_via_AK5
    (hp_odd : p ≠ 2) (hp_pos : 0 < p)
    (hK_prim : (primitiveRoots p K).Nonempty)
    (a b : ℤ) (ζ : 𝓞 K) (hab : ¬ (a = 0 ∧ b = 0))
    (hα₀_ne : BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab ≠ 0)
    (γ : K) (hγ_ne : γ ≠ 0)
    {ζ' : K} (hζ' : IsPrimitiveRoot ζ' p)
    (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * (γ ^ p) =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
    (hcong : (hζ'.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1)
    (hu_no_root : ∀ v : K, v ^ p ≠ u)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab))) :
    Algebra.Unramified (𝓞 K)
      (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
        (p := p) K
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
        hα₀_ne)) := by
  have h_finrank :
      Module.finrank K (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
        (p := p) K
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
        hα₀_ne) = p :=
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift_finrank_of_irreducible
      (K := K) (p := p)
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
      hα₀_ne h_irr
  haveI : IsCyclic
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift (p := p) K
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
        hα₀_ne ≃ₐ[K]
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift (p := p) K
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
        hα₀_ne) :=
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift_isCyclic_of_irreducible
      (K := K) (p := p)
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
      hα₀_ne h_irr
  haveI : Polynomial.IsSplittingField K
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift (p := p) K
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
        hα₀_ne)
      (Polynomial.X ^ p - Polynomial.C
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)) := by
    unfold BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
    infer_instance
  haveI : Polynomial.IsSplittingField K
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift (p := p) K
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
        hα₀_ne)
      (Polynomial.X ^ p - Polynomial.C (algebraMap (𝓞 K) K (u : 𝓞 K))) :=
    isSplittingField_X_pow_sub_C_unit_of_unit_form (K := K) (p := p)
      hp_pos hK_prim
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
      (algebraMap (𝓞 K) K (u : 𝓞 K)) γ hγ_ne h_unit_form.symm h_finrank h_irr
  exact antiKummerLift_isUnramified_of_kummer_data (K := K) (p := p)
    hp_odd _ hα₀_ne hζ' u hcong hu_no_root

end FullChainComposition

section AK5OutputProps

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- **AK-5a output Prop**: principality of the minus-direction ideal `I · σI⁻¹`
for every actual case-I FLT factor ideal.

The substantive content of AK-5a is: under VC (¬p ∣ hPlus K), for every case-I FLT
solution `(a, b, c)` with primary decomposition `(a + ζb) = I^p`, the fractional
ideal `I · σI⁻¹` is principal in K. The argument uses Hilbert 92's contrapositive
applied to the structure of class groups + Vandiver's assumption. -/
def AK5a_PrincipalMinusIdeals : Prop :=
  ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
    ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
    ∀ {ζ : 𝓞 K}, IsPrimitiveRoot ζ p →
    (_hab : ¬ (a = 0 ∧ b = 0)) →
    ∀ {I : Ideal (𝓞 K)}, I ≠ ⊥ →
    Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p →
    ∃ γ : K, γ ≠ 0 ∧
      (I : FractionalIdeal (𝓞 K)⁰ K) /
        (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ γ

/-- If the case-I factor ideal `I` itself is principal, then the
minus-direction quotient `I / σI` has an explicit nonzero principal generator.

This is pure ideal arithmetic: if `I = (x)`, then `σI = (σx)` and
`I / σI = (x / σx)`. -/
theorem principal_ideal_div_conj_isPrincipal
    {I : Ideal (𝓞 K)} (hI_ne : I ≠ ⊥) (hI_principal : I.IsPrincipal) :
    ∃ γ : K, γ ≠ 0 ∧
      (I : FractionalIdeal (𝓞 K)⁰ K) /
        (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ γ := by
  obtain ⟨x, hx⟩ := hI_principal
  have hx_ne : x ≠ 0 := by
    intro hx0
    apply hI_ne
    rw [hx, hx0]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  let σ := NumberField.IsCMField.ringOfIntegersComplexConj K
  have hσ_span :
      Ideal.map σ.toRingEquiv.toRingHom (𝓞 K ∙ x) = 𝓞 K ∙ σ x := by
    rw [Ideal.map_span]
    simp
  have hσx_ne : σ x ≠ 0 := by
    intro hσx
    apply hx_ne
    exact σ.injective (by simpa using hσx)
  have hxK_ne : (x : K) ≠ 0 := by exact_mod_cast hx_ne
  have hσxK_ne : ((σ x : 𝓞 K) : K) ≠ 0 := by exact_mod_cast hσx_ne
  refine ⟨(x : K) / ((σ x : 𝓞 K) : K), ?_, ?_⟩
  · exact div_ne_zero hxK_ne hσxK_ne
  · rw [hx, hσ_span, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton]
    rw [FractionalIdeal.spanSingleton_div_spanSingleton]

/-- If the case-I factor ideal `I` is principal, then the Hilbert-90
cross-multiplication witness is explicit.

For `I = (x)`, take `δ = x` as an element of `Kˣ`.  Then
`I · (σδ) = σI · (δ)` follows from commutativity of singleton fractional
ideals. -/
theorem cross_mul_witness_of_factorIdeal_isPrincipal
    {I : Ideal (𝓞 K)} (hI_ne : I ≠ ⊥) (hI_principal : I.IsPrincipal) :
    ∃ δ : Kˣ,
      ((I : FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰
            (NumberField.IsCMField.complexConj K (δ : K)) =
        ((I.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K))) := by
  obtain ⟨x, hx⟩ := hI_principal
  have hx_ne : x ≠ 0 := by
    intro hx0
    apply hI_ne
    rw [hx, hx0]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  let σ := NumberField.IsCMField.ringOfIntegersComplexConj K
  have hσ_span :
      Ideal.map σ.toRingEquiv.toRingHom (𝓞 K ∙ x) = 𝓞 K ∙ σ x := by
    rw [Ideal.map_span]
    simp
  have hxK_ne : (x : K) ≠ 0 := by exact_mod_cast hx_ne
  let δ : Kˣ := Units.mk0 (x : K) hxK_ne
  refine ⟨δ, ?_⟩
  have h_conj_eq :
      NumberField.IsCMField.complexConj K (x : K) = (σ x : K) := by
    exact (NumberField.IsCMField.coe_ringOfIntegersComplexConj (K := K) x).symm
  change
    ((I : FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (NumberField.IsCMField.complexConj K (x : K)) =
      ((I.map σ.toRingEquiv.toRingHom :
        FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)))
  rw [hx, hσ_span, h_conj_eq, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton, mul_comm]

/-- If the class of the case-I factor ideal is trivial, then the
Hilbert-90 cross-multiplication witness exists. -/
theorem cross_mul_witness_of_factorIdeal_class_eq_one
    {I : Ideal (𝓞 K)} (hI_ne : I ≠ ⊥)
    (hI_class :
      ClassGroup.mk0
        (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne⟩ :
          nonZeroDivisors (Ideal (𝓞 K))) = 1) :
    ∃ δ : Kˣ,
      ((I : FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰
            (NumberField.IsCMField.complexConj K (δ : K)) =
        ((I.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K))) := by
  exact cross_mul_witness_of_factorIdeal_isPrincipal (K := K) hI_ne
    ((ClassGroup.mk0_eq_one_iff
      (mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne)).mp hI_class)

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- AK-5a follows from principality of each actual case-I factor ideal.

This is a reduction lemma, not a source discharge: the input is the concrete
per-factor assertion `I.IsPrincipal` for the same FLT data quantified by
`AK5a_PrincipalMinusIdeals`.  The proof only converts principality of `I` into
principality of the minus quotient `I / σI`. -/
theorem AK5a_PrincipalMinusIdeals_of_factorIdeal_isPrincipal
    (h_principal :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
        ∀ {ζ : 𝓞 K}, IsPrimitiveRoot ζ p →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 K)}, I ≠ ⊥ →
        Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p →
        I.IsPrincipal) :
    AK5a_PrincipalMinusIdeals (p := p) (K := K) := by
  intro a b c hgcd hcaseI heq ζ hζ hab I hI_ne hI_pow
  exact principal_ideal_div_conj_isPrincipal (K := K) hI_ne
    (h_principal hgcd hcaseI heq hζ hab hI_ne hI_pow)

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- AK-5a follows from triviality of the class of each actual case-I factor
ideal.

This is the class-group version of
`AK5a_PrincipalMinusIdeals_of_factorIdeal_isPrincipal`.  The remaining
mathematical source is exposed as the explicit equality
`ClassGroup.mk0 I = 1` for the actual factor ideal `I`. -/
theorem AK5a_PrincipalMinusIdeals_of_factorIdeal_class_eq_one
    (h_class_one :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
        ∀ {ζ : 𝓞 K}, IsPrimitiveRoot ζ p →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 K)}, (hI_ne : I ≠ ⊥) →
        (hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p) →
        ClassGroup.mk0
          (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne⟩ :
            nonZeroDivisors (Ideal (𝓞 K))) = 1) :
    AK5a_PrincipalMinusIdeals (p := p) (K := K) := by
  refine AK5a_PrincipalMinusIdeals_of_factorIdeal_isPrincipal (K := K) ?_
  intro a b c hgcd hcaseI heq ζ hζ hab I hI_ne hI_pow
  exact (ClassGroup.mk0_eq_one_iff
    (mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne)).mp
    (h_class_one hgcd hcaseI heq hζ hab hI_ne hI_pow)

/-- A class-equality discharge plus `¬ p ∣ h⁺` supplies exactly the AK-5a
principal-minus-ideal output.

The class-equality source remains explicit: this theorem only composes the
already formalized Vandiver descent lemma with
`principal_ideal_div_conj_isPrincipal`. -/
theorem AK5a_PrincipalMinusIdeals_of_classEqDischarge_and_not_dvd_hPlus
    (hp_odd : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (h_class : CaseIClassEqDischarge p K) :
    AK5a_PrincipalMinusIdeals (p := p) (K := K) := by
  intro a b c hgcd hcaseI heq ζ hζ hab I hI_ne hI_pow
  have hα_ne : ((a : 𝓞 K) + ζ * (b : 𝓞 K)) ≠ 0 := by
    intro hα
    apply hI_ne
    have h_span_zero :
        Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = ⊥ := by
      rw [hα]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    rw [h_span_zero] at hI_pow
    exact pow_eq_zero_iff (Fact.out : Nat.Prime p).pos.ne' |>.mp hI_pow.symm
  have h_VC : p.Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))) := by
    simpa [hPlus] using
      (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)
        (n := hPlus K)).mpr h_not_dvd
  have h_class_eq := h_class hgcd hcaseI heq hζ hI_ne hI_pow
  have hI_principal : I.IsPrincipal :=
    BernoulliRegular.FLT37.isPrincipal_of_pow_principal_of_class_eq_complexConj_of_VC
      (p := p) (hp_odd := hp_odd) (K := K) h_VC hα_ne hI_ne hI_pow h_class_eq
  exact principal_ideal_div_conj_isPrincipal (K := K) hI_ne hI_principal

/-- AK-5a follows from the concrete square-class target for the actual Case-I
factor ideals, together with `¬ p ∣ h⁺`.

This keeps the substantive Case-I source visible: the new input is exactly
`[σI]^2 = [I]^2` for the factor ideal appearing in the FLT case-I
factorisation.  The p-torsion part is already proved from `(a + ζ b) = I^p`,
and the downstream principalization is the existing plus-class-number
argument. -/
theorem AK5a_PrincipalMinusIdeals_of_factor_class_square_eq_and_not_dvd_hPlus
    (hp_odd : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (h_sq :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
        ∀ {ζ : 𝓞 K}, IsPrimitiveRoot ζ p →
        ∀ {I : Ideal (𝓞 K)}, (hI_nz : I ≠ ⊥) →
          Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p →
          (ClassGroup.mk0
              (⟨I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
                mem_nonZeroDivisors_iff_ne_zero.mpr
                  ((map_ne_bot_iff_complexConj K I).mpr hI_nz)⟩
                : nonZeroDivisors (Ideal (𝓞 K)))) ^ 2 =
            (ClassGroup.mk0
              (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_nz⟩
                : nonZeroDivisors (Ideal (𝓞 K)))) ^ 2) :
    AK5a_PrincipalMinusIdeals (p := p) (K := K) := by
  exact AK5a_PrincipalMinusIdeals_of_classEqDischarge_and_not_dvd_hPlus
    (p := p) (K := K) hp_odd h_not_dvd
    (caseIClassEqDischarge_of_factor_class_square_eq
      (p := p) (K := K) hp_odd h_sq)

/-- **AK-5c output Prop**: strong primarity for the extracted unit `u`.

Given `α₀ = u · γ^p` (AK-5b output), the strong primarity says `(ζ-1)^p ∣ u - 1`
in `𝓞 K`. The substantive content is the Wieferich-style lifting from Stage 1's
weak primarity (Washington §9.1). -/
def AK5c_StrongPrimarity (ζ' : K) (hζ' : IsPrimitiveRoot ζ' p) (u : (𝓞 K)ˣ) : Prop :=
  (hζ'.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1

/-- **Case-I non-p-th-power**: for case-I FLT data, the σ-anti radical is not a
p-th power in K. Equivalent to `Irreducible (X^p - C antiRadical)` in the
cyclotomic setting. The substantive content is a case-I structural argument
(p > 3 prime, σ-anti structure, FLT case-I coprimality). -/
def CaseI_AntiRadical_NotPthPower : Prop :=
  ∀ (_hp_odd : p ≠ 2)
    {a b c : ℤ}
    (_hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    (_h_a_plus_b : ¬ (p : ℤ) ∣ (a + b))
    {ζ : 𝓞 K} (_hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0)),
    ∀ v : K,
      v ^ p ≠
        BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab

end AK5OutputProps

/-- Cyclotomic-field direct form of the square-class route to AK-5a.

For `K = ℚ(ζ_p)`, plus-coprime already proves `[I] * [σI] = 1`.  Combined
with the concrete square-class target `[σI]^2 = [I]^2` and the factor-relation
`p`-torsion of `[I]`, the class of `I` is trivial; the existing class-one
consumer then supplies the principal-minus AK-5a output. -/
theorem AK5a_PrincipalMinusIdeals_of_factor_class_square_eq_and_not_dvd_hPlus_cyclotomic
    {p : ℕ} [Fact p.Prime]
    [NumberField.IsCMField (CyclotomicField p ℚ)]
    (hp_odd : p ≠ 2)
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus (CyclotomicField p ℚ))
    (h_sq :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
        ∀ {ζ : 𝓞 (CyclotomicField p ℚ)}, IsPrimitiveRoot ζ p →
        ∀ {I : Ideal (𝓞 (CyclotomicField p ℚ))}, (hI_nz : I ≠ ⊥) →
          Ideal.span ({(a : 𝓞 (CyclotomicField p ℚ)) +
            ζ * (b : 𝓞 (CyclotomicField p ℚ))} :
              Set (𝓞 (CyclotomicField p ℚ))) = I ^ p →
          (ClassGroup.mk0
              (⟨Ideal.map
                (NumberField.IsCMField.ringOfIntegersComplexConj
                  (CyclotomicField p ℚ)).toRingHom I,
                mem_nonZeroDivisors_iff_ne_zero.mpr
                  ((Ideal.map_eq_bot_iff_of_injective
                    (f := (NumberField.IsCMField.ringOfIntegersComplexConj
                      (CyclotomicField p ℚ)).toRingHom)
                    (NumberField.IsCMField.ringOfIntegersComplexConj
                      (CyclotomicField p ℚ)).injective).not.mpr hI_nz)⟩ :
                nonZeroDivisors (Ideal (𝓞 (CyclotomicField p ℚ)))) ^ 2) =
            (ClassGroup.mk0
              (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_nz⟩ :
                nonZeroDivisors (Ideal (𝓞 (CyclotomicField p ℚ)))) ^ 2)) :
    AK5a_PrincipalMinusIdeals (p := p) (K := CyclotomicField p ℚ) := by
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  intro a b c hgcd hcaseI heq ζ hζ _hab I hI_ne hI_pow
  have h_class_one :
      ClassGroup.mk0
        (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne⟩ :
          nonZeroDivisors (Ideal (𝓞 (CyclotomicField p ℚ)))) = 1 :=
    caseI_factor_class_eq_one_of_square_and_not_dvd_hPlus
      (p := p) hp_odd h_not_dvd hI_ne hI_pow
      (h_sq hgcd hcaseI heq hζ hI_ne hI_pow)
  exact principal_ideal_div_conj_isPrincipal
    (K := CyclotomicField p ℚ) hI_ne
    ((ClassGroup.mk0_eq_one_iff
      (mem_nonZeroDivisors_iff_ne_zero.mpr hI_ne)).mp h_class_one)

section AK5cWieferich

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **AK-5c Wieferich-style lifting** (unconditional). If a unit `u ∈ (𝓞 K)ˣ`
is congruent to `1` modulo `p` in the integer form `u = 1 + p • x` (`x ∈ 𝓞 K`),
then `(ζ-1)^p ∣ u - 1` in `𝓞 K`.

This is the substantive lifting: from divisibility by `p`, conclude divisibility
by `(ζ-1)^p`. The proof composes:
- `norm_add_one_smul_of_isUnit`: `Norm(1 + p • x) = 1` for `p` odd, `1 + p • x` a unit;
- `zeta_sub_one_pow_dvd_norm_sub_pow`: `(ζ-1)^p ∣ Norm(1 + p • x) - 1 + p • x`. -/
theorem AK5c_Wieferich_lifting (hp_odd : p ≠ 2)
    {u : (𝓞 K)ˣ}
    {x : 𝓞 K} (hux : (↑u : 𝓞 K) = 1 + p • x)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1 := by
  have h_unit : IsUnit ((1 + p • x : 𝓞 K)) := by rw [← hux]; exact u.isUnit
  have h_norm := norm_add_one_smul_of_isUnit hp.out hp_odd x h_unit
  have h_div := zeta_sub_one_pow_dvd_norm_sub_pow hζ x
  rw [h_norm] at h_div
  have h_eq : (↑u : 𝓞 K) - 1 = ((1 : ℤ) : 𝓞 K) - 1 + p • x := by
    rw [hux]; push_cast; ring
  rw [h_eq]
  exact h_div

/-- **AK-5c lifting from `p ∣ u-1` divisibility**: discharges `AK5c_StrongPrimarity`
from the hypothesis `(p : 𝓞 K) ∣ (u - 1)`. The integer-form hypothesis
`u = 1 + p • x` is extracted from divisibility. -/
theorem AK5c_Wieferich_lifting_of_p_dvd (hp_odd : p ≠ 2)
    {u : (𝓞 K)ˣ}
    (hcong_p : (p : 𝓞 K) ∣ ((↑u : 𝓞 K) - 1))
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1 := by
  obtain ⟨x, hx⟩ := hcong_p
  have hux : (↑u : 𝓞 K) = 1 + p • x := by
    have : (↑u : 𝓞 K) = 1 + (p : 𝓞 K) * x := by linear_combination hx
    rw [this]
    congr 1
    rw [nsmul_eq_mul]
  exact AK5c_Wieferich_lifting (K := K) hp_odd hux hζ

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **AK-5c converse (trivial direction)**: `(ζ-1)^p ∣ u - 1 ⟹ (p : 𝓞 K) ∣ u - 1`.
Composes `pow_dvd_pow` with `associated_zeta_sub_one_pow_prime`. -/
theorem p_dvd_of_AK5c_StrongPrimarity {u : (𝓞 K)ˣ}
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (h_strong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1) :
    (p : 𝓞 K) ∣ ((↑u : 𝓞 K) - 1) := by
  have h_p_le : p - 1 ≤ p := Nat.sub_le p 1
  have h_pow : (hζ.toInteger - 1 : 𝓞 K) ^ (p - 1) ∣ (↑u : 𝓞 K) - 1 :=
    dvd_trans (pow_dvd_pow _ h_p_le) h_strong
  obtain ⟨v, hv⟩ := (associated_zeta_sub_one_pow_prime hζ).symm
  rw [← hv] at h_pow
  exact dvd_trans ⟨v, rfl⟩ h_pow

/-- **AK-5c characterization (Wieferich-Kummer iff)**: for `u ∈ (𝓞 K)ˣ` and `p ≠ 2`,
the strong primarity `(ζ-1)^p ∣ u - 1` is equivalent to `p ∣ u - 1`. -/
theorem AK5c_StrongPrimarity_iff_p_dvd (hp_odd : p ≠ 2)
    {u : (𝓞 K)ˣ}
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ ((↑u : 𝓞 K) - 1) ↔
      (p : 𝓞 K) ∣ ((↑u : 𝓞 K) - 1) :=
  ⟨p_dvd_of_AK5c_StrongPrimarity (K := K) hζ,
    fun h ↦ AK5c_Wieferich_lifting_of_p_dvd (K := K) hp_odd h hζ⟩

/-- **AK-5c Wieferich lifting from Hensel-style integer congruence on `u`**: if a unit
`u ∈ (𝓞 K)ˣ` is congruent to *some* integer `n` modulo `p` in `𝓞 K`, then
`(ζ-1)^p ∣ u^(p-1) - 1`.

The Fermat-lift step uses `Int.ModEq.pow_card_sub_one_eq_one`: `n^(p-1) ≡ 1 (mod p)`
when `p ∤ n` (and `p ∤ n` because `u` is a unit and `u ≡ n (mod p)`, so any prime
divisor of `(p : 𝓞 K)` annihilating `n` would also annihilate `u`, contradicting
`u` being a unit). Then `u^(p-1) ≡ n^(p-1) ≡ 1 (mod p)` in `𝓞 K`. Apply
`AK5c_Wieferich_lifting_of_p_dvd` to `u^(p-1)`.

This is the standard Wieferich-Kummer lift, generalising the chain inside
`FltRegular.eq_pow_prime_of_unit_of_congruent` so it's independent of regularity. -/
theorem AK5c_Wieferich_lifting_of_int_congr (hp_odd : p ≠ 2)
    {u : (𝓞 K)ˣ}
    (hcong : ∃ n : ℤ, (p : 𝓞 K) ∣ ((↑u : 𝓞 K) - (n : 𝓞 K)))
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (↑(u ^ (p - 1)) : 𝓞 K) - 1 := by
  have hp_dvd : (p : 𝓞 K) ∣ (↑(u ^ (p - 1)) : 𝓞 K) - 1 := by
    obtain ⟨n, hn⟩ := hcong
    have hn' : (p : ℤ) ∣ n ^ (p - 1) - 1 := by
      refine Int.modEq_iff_dvd.mp (Int.ModEq.pow_card_sub_one_eq_one hp.out ?_).symm
      rw [isCoprime_comm, (Nat.prime_iff_prime_int.mp hp.out).coprime_iff_not_dvd]
      intro h
      replace h := Int.cast_dvd_cast (α := 𝓞 K) _ _ h
      simp only [Int.cast_natCast, ← dvd_iff_dvd_of_dvd_sub hn] at h
      refine hζ.zeta_sub_one_prime'.not_unit ((isUnit_pow_iff ?_).mp
        (isUnit_of_dvd_unit ((associated_zeta_sub_one_pow_prime hζ).dvd.trans h) u.isUnit))
      simpa only [ne_eq, tsub_eq_zero_iff_le, not_le] using hp.out.one_lt
    replace hn' := Int.cast_dvd_cast (α := 𝓞 K) _ _ hn'
    simp only [Int.cast_natCast, Int.cast_sub, Int.cast_pow, Int.cast_one] at hn'
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
      RingHom.map_sub, sub_eq_zero] at hn hn' ⊢
    rw [Units.val_pow_eq_pow_val, RingHom.map_pow, hn, ← RingHom.map_pow, hn']
  exact AK5c_Wieferich_lifting_of_p_dvd (K := K) hp_odd hp_dvd hζ

end AK5cWieferich

section AK5cDischarge

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

omit [IsCMField K] in
/-- **AK-5c discharge of the named Prop**: produces `AK5c_StrongPrimarity ζ' hζ' u`
from the hypothesis `(p : 𝓞 K) ∣ u - 1`. Direct discharge mechanism for the named Prop. -/
theorem AK5c_StrongPrimarity_of_p_dvd (hp_odd : p ≠ 2)
    {ζ' : K} (hζ' : IsPrimitiveRoot ζ' p)
    {u : (𝓞 K)ˣ}
    (hcong_p : (p : 𝓞 K) ∣ ((↑u : 𝓞 K) - 1)) :
    AK5c_StrongPrimarity (p := p) (K := K) ζ' hζ' u :=
  AK5c_Wieferich_lifting_of_p_dvd (K := K) hp_odd hcong_p hζ'

end AK5cDischarge

section AK5aBuilding

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- **`ringOfIntegersComplexConj` is an involution**: `σ ∘ σ = id` on `𝓞 K`. -/
theorem ringOfIntegersComplexConj_involution (x : 𝓞 K) :
    NumberField.IsCMField.ringOfIntegersComplexConj K
      (NumberField.IsCMField.ringOfIntegersComplexConj K x) = x := by
  apply RingOfIntegers.ext
  rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj,
      NumberField.IsCMField.coe_ringOfIntegersComplexConj]
  exact NumberField.IsCMField.complexConj_apply_apply K _

/-- **σ²(I) = I** on ideals: `Ideal.map σ (Ideal.map σ I) = I`. -/
theorem Ideal_map_ringOfIntegersComplexConj_involution
    (I : Ideal (𝓞 K)) :
    (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom).map
      (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom = I := by
  rw [Ideal.map_map]
  have h_comp : (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom.comp
      (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      RingHom.id (𝓞 K) := by
    ext x
    have h_inv : NumberField.IsCMField.ringOfIntegersComplexConj K
        (NumberField.IsCMField.ringOfIntegersComplexConj K x) = x :=
      ringOfIntegersComplexConj_involution (K := K) x
    exact_mod_cast h_inv
  rw [h_comp, Ideal.map_id]

end AK5aBuilding

section AntiRadicalNonPthPower

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- **σ-anti element has Norm 1**: if `complexConj K (x) = x⁻¹` and `x ≠ 0`, then
`x · complexConj K (x) = 1`. This is the norm-1 condition for the σ-anti property. -/
theorem σ_anti_norm_eq_one
    (x : K) (hx : x ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K x = x⁻¹) :
    x * NumberField.IsCMField.complexConj K x = 1 := by
  rw [h_anti, mul_inv_cancel₀ hx]

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **σ-anti property of `γ^p` implies σ-anti of γ (up to a p-th root of unity)**:
if `γ^p` is σ-anti and γ ≠ 0, then `γ · σ(γ)` is a p-th root of 1 in K⁺. -/
theorem σ_pth_anti_norm_pth_root
    (γ : K) (hγ : γ ≠ 0)
    (h_pth_anti : NumberField.IsCMField.complexConj K (γ ^ p) = (γ ^ p)⁻¹) :
    (γ * NumberField.IsCMField.complexConj K γ) ^ p = 1 := by
  have h_norm := σ_anti_norm_eq_one (K := K) (γ ^ p) (pow_ne_zero _ hγ) h_pth_anti
  rw [mul_pow,
    show NumberField.IsCMField.complexConj K γ ^ p =
      NumberField.IsCMField.complexConj K (γ ^ p) from (map_pow _ _ _).symm]
  exact h_norm

/-- **`γ · σ(γ)` is σ-fixed**: σ(γ · σ(γ)) = σ(γ) · σ²(γ) = σ(γ) · γ = γ · σ(γ). -/
theorem mul_complexConj_isFixed (γ : K) :
    NumberField.IsCMField.complexConj K (γ * NumberField.IsCMField.complexConj K γ) =
      γ * NumberField.IsCMField.complexConj K γ := by
  rw [map_mul, NumberField.IsCMField.complexConj_apply_apply, mul_comm]

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **σ-fixed element with p-th power 1 lies in `K⁺` and corresponds to a p-th root
of 1 in `K⁺`.** Sets up the Kronecker-style argument for the case-I non-p-th-power
conclusion. -/
theorem fixed_pow_eq_one_descend
    (x : K) (hx_fixed : NumberField.IsCMField.complexConj K x = x)
    (hxp : x ^ p = 1) :
    ∃ y : NumberField.maximalRealSubfield K,
      algebraMap (NumberField.maximalRealSubfield K) K y = x ∧ y ^ p = 1 := by
  have h_mem : x ∈ NumberField.maximalRealSubfield K :=
    (NumberField.IsCMField.complexConj_eq_self_iff K x).mp hx_fixed
  refine ⟨⟨x, h_mem⟩, ?_, ?_⟩
  · rfl
  · have h_inj : Function.Injective
        (algebraMap (NumberField.maximalRealSubfield K) K) :=
      FaithfulSMul.algebraMap_injective _ _
    apply h_inj
    rw [map_pow, map_one]
    exact hxp

omit hp in
/-- **In a totally real number field, p-th roots of unity for p odd are trivial**. -/
theorem totallyReal_odd_pow_eq_one_eq_one
    {K' : Type*} [Field K'] [NumberField K'] [NumberField.IsTotallyReal K']
    (hp_odd : Odd p) (y : K') (hy : y ^ p = 1) :
    y = 1 := by
  obtain ⟨φ⟩ := (inferInstance : Nonempty (K' →+* ℂ))
  have hφ_real : NumberField.ComplexEmbedding.IsReal φ :=
    NumberField.IsTotallyReal.complexEmbedding_isReal _
  let ψ : K' →+* ℝ := NumberField.ComplexEmbedding.IsReal.embedding hφ_real
  have hψ_pow : ψ y ^ p = 1 := by
    rw [← map_pow, hy, map_one]
  have hψ_y : ψ y = 1 := by
    rcases (pow_eq_one_iff_of_ne_zero hp_odd.pos.ne' (a := ψ y)).mp hψ_pow with h | ⟨h, h_even⟩
    · exact h
    · exact absurd h_even (Nat.not_even_iff_odd.mpr hp_odd)
  have hψ_inj : Function.Injective ψ := RingHom.injective ψ
  apply hψ_inj
  rw [hψ_y, map_one]

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **Norm = 1 from σ-anti p-th power**: if `γ^p` is σ-anti in K (i.e.,
`σ(γ^p) = (γ^p)⁻¹`) and γ ≠ 0 and p is odd, then `γ · σ(γ) = 1` (Norm 1). -/
theorem σ_pth_anti_norm_eq_one
    (hp_odd : Odd p)
    (γ : K) (hγ : γ ≠ 0)
    (h_pth_anti : NumberField.IsCMField.complexConj K (γ ^ p) = (γ ^ p)⁻¹) :
    γ * NumberField.IsCMField.complexConj K γ = 1 := by
  have h_pow_one : (γ * NumberField.IsCMField.complexConj K γ) ^ p = 1 :=
    σ_pth_anti_norm_pth_root (K := K) (p := p) γ hγ h_pth_anti
  have h_fixed : NumberField.IsCMField.complexConj K
      (γ * NumberField.IsCMField.complexConj K γ) =
      γ * NumberField.IsCMField.complexConj K γ :=
    mul_complexConj_isFixed (K := K) γ
  obtain ⟨y, hy_eq, hy_pow⟩ := fixed_pow_eq_one_descend (K := K) (p := p)
    _ h_fixed h_pow_one
  have hy_eq_one : y = 1 :=
    totallyReal_odd_pow_eq_one_eq_one (p := p) (K' := NumberField.maximalRealSubfield K)
      hp_odd y hy_pow
  rw [← hy_eq, hy_eq_one, map_one]

/-- **Algebra.norm formula for K/K⁺**: `algebraMap K⁺ K (Algebra.norm K⁺ x) = x · σ(x)`. -/
theorem algebraMap_norm_K_Kplus_eq
    (x : K) :
    algebraMap (NumberField.maximalRealSubfield K) K
      (Algebra.norm (NumberField.maximalRealSubfield K) x) =
      x * NumberField.IsCMField.complexConj K x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  have h_ne : (1 : K ≃ₐ[NumberField.maximalRealSubfield K] K) ≠
      NumberField.IsCMField.complexConj K :=
    (NumberField.IsCMField.complexConj_ne_one K).symm
  have h_card_eq :
      Fintype.card (K ≃ₐ[NumberField.maximalRealSubfield K] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact Algebra.IsQuadraticExtension.finrank_eq_two
      (NumberField.maximalRealSubfield K) K
  have h_univ :
      (Finset.univ : Finset (K ≃ₐ[NumberField.maximalRealSubfield K] K)) =
      {(1 : K ≃ₐ[NumberField.maximalRealSubfield K] K),
        NumberField.IsCMField.complexConj K} := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · exact Finset.subset_univ _
    · rw [Finset.card_univ, h_card_eq]
      have h_pair_card :
          ({(1 : K ≃ₐ[NumberField.maximalRealSubfield K] K),
            NumberField.IsCMField.complexConj K} :
            Finset (K ≃ₐ[NumberField.maximalRealSubfield K] K)).card = 2 :=
        Finset.card_pair h_ne
      omega
  rw [h_univ, Finset.prod_pair h_ne, AlgEquiv.one_apply]

/-- **Norm K⁺ γ = 1 from γ·σ(γ) = 1**: bridge from the σ-conjugation product
to the standard Algebra.norm. -/
theorem norm_Kplus_eq_one_of_mul_complexConj_eq_one
    (γ : K) (hγ : γ * NumberField.IsCMField.complexConj K γ = 1) :
    Algebra.norm (NumberField.maximalRealSubfield K) γ = 1 := by
  have h_inj : Function.Injective
      (algebraMap (NumberField.maximalRealSubfield K) K) :=
    FaithfulSMul.algebraMap_injective _ _
  apply h_inj
  rw [algebraMap_norm_K_Kplus_eq, hγ, map_one]

/-- **Hilbert 90 for K/K⁺**: if γ·σ(γ) = 1, then ∃ δ : K^×, δ/σ(δ) = γ. -/
theorem exists_div_complexConj_of_mul_complexConj_eq_one
    (γ : K) (hγ : γ * NumberField.IsCMField.complexConj K γ = 1) :
    ∃ δ : Kˣ, (δ : K) / NumberField.IsCMField.complexConj K (δ : K) = γ := by
  haveI : IsCyclic (K ≃ₐ[NumberField.maximalRealSubfield K] K) := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    exact ⟨NumberField.IsCMField.complexConj K,
      NumberField.IsCMField.zpowers_complexConj_eq_top K⟩
  have h_norm : Algebra.norm (NumberField.maximalRealSubfield K) γ = 1 :=
    norm_Kplus_eq_one_of_mul_complexConj_eq_one (K := K) γ hγ
  exact groupCohomology.exists_div_of_norm_eq_one
    (g := NumberField.IsCMField.complexConj K)
    (fun x ↦ by
      rw [NumberField.IsCMField.zpowers_complexConj_eq_top]
      trivial)
    h_norm

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **Full σ-anti p-th power Hilbert 90 composition**: if γ ≠ 0 and γ^p is σ-anti
in K (i.e., σ(γ^p) = (γ^p)⁻¹) with p odd, then ∃ δ ∈ K^×, δ/σ(δ) = γ. -/
theorem σ_pth_anti_exists_div
    (hp_odd : Odd p)
    (γ : K) (hγ : γ ≠ 0)
    (h_pth_anti : NumberField.IsCMField.complexConj K (γ ^ p) = (γ ^ p)⁻¹) :
    ∃ δ : Kˣ, (δ : K) / NumberField.IsCMField.complexConj K (δ : K) = γ :=
  exists_div_complexConj_of_mul_complexConj_eq_one (K := K) γ
    (σ_pth_anti_norm_eq_one (K := K) (p := p) hp_odd γ hγ h_pth_anti)

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **Ideal-side identity from Hilbert 90 + γ^p = α₀**: if γ^p = α₀ (in K)
and γ = δ/σ(δ) (from Hilbert 90 applied to γ·σ(γ) = 1), then as fractional
ideals, `spanSingleton α₀ = (spanSingleton δ / spanSingleton (σ δ))^p`. -/
theorem spanSingleton_pow_eq_div_pow_of_hilbert90
    (α₀ γ : K) (δ : Kˣ)
    (h_pow : γ ^ p = α₀)
    (h_hilbert : (δ : K) / NumberField.IsCMField.complexConj K (δ : K) = γ) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ α₀ =
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K) /
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (NumberField.IsCMField.complexConj K (δ : K))) ^ p := by
  rw [FractionalIdeal.spanSingleton_div_spanSingleton,
      FractionalIdeal.spanSingleton_pow, h_hilbert, h_pow]

omit [IsCMField K] in
/-- **FractionalIdeal p-th root uniqueness for Dedekind domains**: if `I^p = J^p`
for nonzero I, J fractional ideals of 𝓞 K, then I = J. -/
theorem FractionalIdeal_pow_left_injective_of_ne_zero
    {p : ℕ} (hp_pos : 0 < p)
    {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h_eq : I ^ p = J ^ p) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  apply finprod_congr
  intro v
  congr 1
  have h_count_pow_I : FractionalIdeal.count K v (I ^ p) = p * FractionalIdeal.count K v I :=
    FractionalIdeal.count_pow (K := K) v p I
  have h_count_pow_J : FractionalIdeal.count K v (J ^ p) = p * FractionalIdeal.count K v J :=
    FractionalIdeal.count_pow (K := K) v p J
  have h_count_eq : FractionalIdeal.count K v (I ^ p) = FractionalIdeal.count K v (J ^ p) := by
    rw [h_eq]
  rw [h_count_pow_I, h_count_pow_J] at h_count_eq
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hp_pos.ne') h_count_eq

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **Combined ideal-side equality after Hilbert 90 + p-th root uniqueness**.
Non-zero hypotheses provided explicitly. -/
theorem antiRadical_ideal_div_eq_principal
    (hp_pos : 0 < p)
    (a b : ℤ) (ζ : 𝓞 K) (hab : ¬ (a = 0 ∧ b = 0))
    (I : Ideal (𝓞 K))
    (hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p)
    (γ : K)
    (h_pow : γ ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
    (δ : Kˣ) (h_hilbert : (δ : K) / NumberField.IsCMField.complexConj K (δ : K) = γ)
    (h_LHS_ne :
      ((I : FractionalIdeal (𝓞 K)⁰ K) /
        (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K)) ≠ 0)
    (h_RHS_ne :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K) /
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (NumberField.IsCMField.complexConj K (δ : K)) ≠ 0) :
    ((I : FractionalIdeal (𝓞 K)⁰ K) /
      (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
        FractionalIdeal (𝓞 K)⁰ K)) =
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K) /
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K (δ : K)) := by
  apply FractionalIdeal_pow_left_injective_of_ne_zero (K := K) (p := p) hp_pos
    h_LHS_ne h_RHS_ne
  rw [← antiRadical_spanSingleton_pow_eq (K := K) (p := p) a b ζ hab I hI_pow]
  exact spanSingleton_pow_eq_div_pow_of_hilbert90 (K := K) (p := p) _ γ δ h_pow h_hilbert

/-- **σ-fixed fractional ideal from the Hilbert 90 conclusion**: from
`I / σI = (δ)/(σδ)` with non-zero hypotheses, cross-multiplying gives
`I · (σδ) = σI · (δ)`. -/
theorem ideal_div_delta_cross_mul
    (I : Ideal (𝓞 K)) (δ : Kˣ)
    (h_σI_ne : (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
      FractionalIdeal (𝓞 K)⁰ K) ≠ 0)
    (h_div_eq :
      ((I : FractionalIdeal (𝓞 K)⁰ K) /
        (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K)) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K) /
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (NumberField.IsCMField.complexConj K (δ : K))) :
    ((I : FractionalIdeal (𝓞 K)⁰ K) *
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K (δ : K))) =
    ((I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
        FractionalIdeal (𝓞 K)⁰ K) *
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K)) := by
  have h_σδ_ne : NumberField.IsCMField.complexConj K (δ : K) ≠ 0 := by
    have hδ : (δ : K) ≠ 0 := Units.ne_zero δ
    intro h
    apply hδ
    have := congrArg (NumberField.IsCMField.complexConj K) h
    rwa [NumberField.IsCMField.complexConj_apply_apply, map_zero] at this
  have h_sσδ_ne : FractionalIdeal.spanSingleton (𝓞 K)⁰
      (NumberField.IsCMField.complexConj K (δ : K)) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr h_σδ_ne
  rw [div_eq_div_iff h_σI_ne h_sσδ_ne] at h_div_eq
  rw [h_div_eq, mul_comm]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Cross-multiplication witness from a σ-anti p-th root of the case-I radical.**

If the case-I anti-radical is itself a `p`-th power `γ ^ p`, then the
σ-anti property of the radical gives `γ = δ / σδ` by Hilbert 90, and the
standard fractional-ideal root-cancellation lemma produces the exact
cross-multiplication witness for the factor ideal `I`.

This is a checked algebraic consumer, not a source theorem: the mathematical
input is the explicit p-th-root statement `γ ^ p = antiRadical ...`. -/
theorem cross_mul_witness_of_antiRadical_pth_power
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) (hab : ¬ (a = 0 ∧ b = 0))
    {I : Ideal (𝓞 K)} (hI_ne : I ≠ ⊥)
    (hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p)
    (γ : K) (hγ_ne : γ ≠ 0)
    (hγ_pow :
      γ ^ p =
        BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
          K a b ζ hab) :
    ∃ δ : Kˣ,
      ((I : FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰
            (NumberField.IsCMField.complexConj K (δ : K)) =
        ((I.map
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K))) := by
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp_odd' : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp_odd
  have hα_anti :
      NumberField.IsCMField.complexConj K
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            K a b ζ hab) =
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
          K a b ζ hab)⁻¹ :=
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical_sigma_inv
      (K := K) a b ζ hab
      (caseI_antiRadical_denom_K_ne_zero (K := K) hp_odd hcaseI hζ)
  have h_pth_anti :
      NumberField.IsCMField.complexConj K (γ ^ p) = (γ ^ p)⁻¹ := by
    rw [hγ_pow, hα_anti]
  obtain ⟨δ, hδ⟩ := σ_pth_anti_exists_div (K := K) (p := p)
    hp_odd' γ hγ_ne h_pth_anti
  refine ⟨δ, ?_⟩
  have hσI_ne_ideal :
      I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom ≠ ⊥ :=
    (map_ne_bot_iff_complexConj K I).mpr hI_ne
  have hI_fi_ne : (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_bot,
      (FractionalIdeal.coeIdeal_injective' (le_rfl : (𝓞 K)⁰ ≤ (𝓞 K)⁰)).ne_iff]
    simpa [Ideal.zero_eq_bot] using hI_ne
  have hσI_fi_ne :
      (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
        FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_bot,
      (FractionalIdeal.coeIdeal_injective' (le_rfl : (𝓞 K)⁰ ≤ (𝓞 K)⁰)).ne_iff]
    simpa [Ideal.zero_eq_bot] using hσI_ne_ideal
  have hδ_ne : (δ : K) ≠ 0 := Units.ne_zero δ
  have hσδ_ne : NumberField.IsCMField.complexConj K (δ : K) ≠ 0 := by
    intro hσδ
    apply hδ_ne
    have := congrArg (NumberField.IsCMField.complexConj K) hσδ
    rwa [NumberField.IsCMField.complexConj_apply_apply, map_zero] at this
  have h_LHS_ne :
      ((I : FractionalIdeal (𝓞 K)⁰ K) /
        (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 :=
    div_ne_zero hI_fi_ne hσI_fi_ne
  have h_RHS_ne :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K) /
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (NumberField.IsCMField.complexConj K (δ : K)) ≠ 0 :=
    div_ne_zero
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hδ_ne)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hσδ_ne)
  exact ideal_div_delta_cross_mul (K := K) I δ hσI_fi_ne
    (antiRadical_ideal_div_eq_principal (K := K) (p := p) hp_pos
      a b ζ hab I hI_pow γ hγ_pow δ hδ h_LHS_ne h_RHS_ne)

/-- **From cross-multiplication to σ-fixed**: `I·(σδ) = σI·(δ)` rewritten as
`I·(spanSingleton (σδ)) = σI · (spanSingleton δ)`, then dividing both sides by
`spanSingleton δ` (non-zero) and `spanSingleton σδ` cancellations gives the
σ-fixed form `(I · spanSingleton (σδ) / spanSingleton δ) = σI`. -/
theorem σ_image_eq_of_cross_mul
    (I : Ideal (𝓞 K)) (δ : Kˣ)
    (h_cross :
      ((I : FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (NumberField.IsCMField.complexConj K (δ : K))) =
      ((I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K))) :
    ((I : FractionalIdeal (𝓞 K)⁰ K) *
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K (δ : K)) /
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K)) =
    (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
        FractionalIdeal (𝓞 K)⁰ K) := by
  have hδ : (δ : K) ≠ 0 := Units.ne_zero δ
  have h_sδ_ne : FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hδ
  rw [h_cross, mul_div_assoc]
  rw [div_self h_sδ_ne, mul_one]

omit [IsCMField K] in
/-- **Class equality for I and σI via the principal multiplier**: from
`I·(σδ) = σI·(δ)` with non-zero integer-side witnesses for `δ`, derive
`[I] = [σI]` in `ClassGroup (𝓞 K)`. -/
theorem classGroup_eq_of_cross_mul_with_integers
    (I J : (Ideal (𝓞 K))⁰)
    (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0)
    (h_eq : Ideal.span ({x} : Set (𝓞 K)) * I.1 = Ideal.span ({y} : Set (𝓞 K)) * J.1) :
    ClassGroup.mk0 I = ClassGroup.mk0 J := by
  rw [ClassGroup.mk0_eq_mk0_iff]
  exact ⟨x, y, hx, hy, h_eq⟩

omit [IsCMField K] in
/-- **K-element as ratio of integers**: for δ ∈ K^×, write δ = r/s for r ∈ 𝓞 K
and s ∈ (𝓞 K)⁰. Concretely: ∃ r ∈ 𝓞 K, s ∈ (𝓞 K)⁰, δ · algebraMap s = algebraMap r.

This is `IsLocalization.surj (𝓞 K)⁰ K` specialized. Useful for integer-side
translation of FractionalIdeal equations. -/
theorem exists_integer_num_denom_of_K_unit
    (δ : Kˣ) :
    ∃ (r : 𝓞 K) (s : (𝓞 K)⁰),
      (δ : K) * algebraMap (𝓞 K) K (s : 𝓞 K) = algebraMap (𝓞 K) K r := by
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj (𝓞 K)⁰ (δ : K)
  exact ⟨r, s, h⟩

omit [IsCMField K] in
/-- **Principal multiplier from K-element**: a useful K-equation lemma. If
`z₁ * spanSingleton z₂ = z₃ * spanSingleton z₄` as fractional ideals where all
`zᵢ` are in K and the equation involves an ideal-times-singleton structure, the
integer-side translation via `spanSingleton_mul_coeIdeal_eq_coeIdeal` produces
`Ideal.span {a} · I = Ideal.span {b} · J` for `a, b ∈ 𝓞 K`. This is the
existing mathlib machinery; we use it indirectly via the AK chain. -/
theorem spanSingleton_mul_coeIdeal_translates :
    ∀ {z : K} {I J : Ideal (𝓞 K)},
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ z * (I : FractionalIdeal (𝓞 K)⁰ K) =
        (J : FractionalIdeal (𝓞 K)⁰ K)) ↔
      Ideal.span ({((IsLocalization.sec (𝓞 K)⁰ z).1 : 𝓞 K)} : Set (𝓞 K)) * I =
        Ideal.span ({((IsLocalization.sec (𝓞 K)⁰ z).2 : 𝓞 K)} : Set (𝓞 K)) * J := by
  intros
  exact FractionalIdeal.spanSingleton_mul_coeIdeal_eq_coeIdeal

omit [IsCMField K] in
/-- **Singleton-multiplier form** (auxiliary): if for `z ∈ K^×` we have
`I · sp(c) = J · sp(z)`, then `sp(c · z⁻¹) · I = J`. -/
theorem singleton_multiplier_form
    (I J : FractionalIdeal (𝓞 K)⁰ K) (c : K) (z : Kˣ)
    (h : I * FractionalIdeal.spanSingleton (𝓞 K)⁰ c =
          J * FractionalIdeal.spanSingleton (𝓞 K)⁰ (z : K)) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (c * ((z : K))⁻¹) * I = J := by
  have hz : (z : K) ≠ 0 := Units.ne_zero z
  have h_sz_ne : FractionalIdeal.spanSingleton (𝓞 K)⁰ (z : K) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hz
  have h_cancel : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((z : K))⁻¹ *
      (I * FractionalIdeal.spanSingleton (𝓞 K)⁰ c) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((z : K))⁻¹ *
      (J * FractionalIdeal.spanSingleton (𝓞 K)⁰ (z : K)) := by
    rw [h]
  calc FractionalIdeal.spanSingleton (𝓞 K)⁰ (c * ((z : K))⁻¹) * I
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ ((z : K))⁻¹ *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ c * I := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton, mul_comm c _]
    _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ ((z : K))⁻¹ *
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ c * I) := by ring
    _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ ((z : K))⁻¹ *
          (I * FractionalIdeal.spanSingleton (𝓞 K)⁰ c) := by rw [mul_comm I _]
    _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ ((z : K))⁻¹ *
          (J * FractionalIdeal.spanSingleton (𝓞 K)⁰ (z : K)) := by rw [h]
    _ = J * (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((z : K))⁻¹ *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (z : K)) := by ring
    _ = J * FractionalIdeal.spanSingleton (𝓞 K)⁰ (((z : K))⁻¹ * (z : K)) := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
    _ = J * FractionalIdeal.spanSingleton (𝓞 K)⁰ 1 := by rw [inv_mul_cancel₀ hz]
    _ = J * 1 := by rw [FractionalIdeal.spanSingleton_one]
    _ = J := by rw [mul_one]

/-- **σI = sp(σδ/δ) · I as fractional ideals**: composition of
`ideal_div_delta_cross_mul` + `singleton_multiplier_form`. -/
theorem σI_eq_singleton_mul_I
    (I : Ideal (𝓞 K)) (δ : Kˣ)
    (h_cross :
      ((I : FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (NumberField.IsCMField.complexConj K (δ : K))) =
      ((I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K))) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹) *
      (I : FractionalIdeal (𝓞 K)⁰ K) =
      (I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
        FractionalIdeal (𝓞 K)⁰ K) :=
  singleton_multiplier_form (K := K) _ _ _ δ h_cross

/-- **Integer-side equation from cross-mul + Hilbert 90 conclusion**: given the
FractionalIdeal cross-mul, derive `Ideal.span {x} · I = Ideal.span {y} · σI`
in (𝓞 K)-ideals for x = sec.1, y = sec.2 of z = σδ · δ⁻¹. -/
theorem integer_cross_mul_from_FractionalIdeal
    (I : Ideal (𝓞 K)) (δ : Kˣ)
    (h_cross :
      ((I : FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (NumberField.IsCMField.complexConj K (δ : K))) =
      ((I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K))) :
    Ideal.span ({((IsLocalization.sec (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹)).1 : 𝓞 K)}
        : Set (𝓞 K)) * I =
      Ideal.span ({((IsLocalization.sec (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹)).2 : 𝓞 K)}
        : Set (𝓞 K)) *
        I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :=
  spanSingleton_mul_coeIdeal_translates.mp (σI_eq_singleton_mul_I (K := K) I δ h_cross)

/-- **`[I] = [σI]` in ClassGroup from cross-mul + Hilbert 90 conclusion**.

Final composition of the non-p-th-power chain: given that `γ^p = antiRadical`
(via the σ-anti chain) leads to the cross-mul equation, derive that `I` and `σI`
have the same class in `ClassGroup (𝓞 K)`.

Takes the non-zero hypotheses for `I`, `σI`, and the cross-mul witnesses
explicitly. -/
theorem classGroup_mk0_I_eq_σI_of_cross_mul
    (I σI : (Ideal (𝓞 K))⁰)
    (h_σI : (σI : Ideal (𝓞 K)) =
      (I : Ideal (𝓞 K)).map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
    (δ : Kˣ)
    (h_cross :
      ((I : Ideal (𝓞 K)) * FractionalIdeal.spanSingleton (𝓞 K)⁰
          (NumberField.IsCMField.complexConj K (δ : K)) =
        ((I : Ideal (𝓞 K)).map
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K)))
    (hx_ne :
      ((IsLocalization.sec (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹)).1 : 𝓞 K) ≠ 0)
    (hy_ne :
      ((IsLocalization.sec (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹)).2 : 𝓞 K) ≠ 0) :
    ClassGroup.mk0 I = ClassGroup.mk0 σI := by
  have h_int := integer_cross_mul_from_FractionalIdeal (K := K) (I : Ideal (𝓞 K)) δ h_cross
  rw [← h_σI] at h_int
  exact classGroup_eq_of_cross_mul_with_integers (K := K) I σI _ _ hx_ne hy_ne h_int

/-- **Full non-pth-power chain to isPrincipal under VC + descent witness**.

Final composition: from the assumption `γ^p = antiRadical` (along with the
chain's intermediate inputs) plus VC + descent witness, conclude `I.IsPrincipal`.

This is the AK-5a-output (`I/σI = (γ)`) given the non-pth-power negation, via:
1. `classGroup_mk0_I_eq_σI_of_cross_mul`: derive `[I] = [σI]` in Cl(𝓞 K).
2. `isPrincipal_of_class_eq_complexConj_of_VC` (from PrimaryDescent.lean):
   compose with `[I]^p = 1` + VC + descent to get `I.IsPrincipal`. -/
theorem isPrincipal_of_cross_mul_under_VC
    [Fact (p ≠ 2)]
    (h_VC : p.Coprime (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (I σI : (Ideal (𝓞 K))⁰)
    (h𝔞_nz : (I : Ideal (𝓞 K)) ≠ ⊥)
    (h_σI : (σI : Ideal (𝓞 K)) =
      (I : Ideal (𝓞 K)).map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
    (h_pow_one : ClassGroup.mk0 I ^ p = 1)
    (δ : Kˣ)
    (h_cross :
      ((I : Ideal (𝓞 K)) * FractionalIdeal.spanSingleton (𝓞 K)⁰
          (NumberField.IsCMField.complexConj K (δ : K)) =
        ((I : Ideal (𝓞 K)).map
          (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K)))
    (hx_ne :
      ((IsLocalization.sec (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹)).1 : 𝓞 K) ≠ 0)
    (hy_ne :
      ((IsLocalization.sec (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹)).2 : 𝓞 K) ≠ 0)
    (h_sq_in_image : ∃ 𝔠₀ : ClassGroup (𝓞 (NumberField.maximalRealSubfield K)),
      classGroupMap K 𝔠₀ = ClassGroup.mk0 I ^ 2) :
    (I : Ideal (𝓞 K)).IsPrincipal := by
  have h_class_eq : ClassGroup.mk0 I = ClassGroup.mk0 σI :=
    classGroup_mk0_I_eq_σI_of_cross_mul (K := K) I σI h_σI δ h_cross hx_ne hy_ne
  have hp_odd_fact : p ≠ 2 := Fact.out
  have h_match : (⟨(I : Ideal (𝓞 K)), mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩ :
      (Ideal (𝓞 K))⁰) = I := Subtype.ext rfl
  rw [← h_match] at h_pow_one h_sq_in_image
  exact isPrincipal_of_class_eq_complexConj_of_VC
    (p := p) (hp_odd := hp_odd_fact) (K := K) h_VC h𝔞_nz h_pow_one h_sq_in_image

/-- **σ-fixed ideal descent Prop**: for every σ-fixed ideal `J` of `𝓞 K`
(meaning `J.map σ = J` where σ = ringOfIntegersComplexConj), there exists
`J' : Ideal (𝓞 K⁺)` with `J = J'.map (algebraMap 𝓞 K⁺ 𝓞 K)`.

This is the open "FLT37b2b2-d-descent" content: Galois descent for σ-fixed
ideals over the degree-2 unramified extension K/K⁺. The class-group
consequence (`[J] = classGroupMap [J']`) follows immediately. -/
def SigmaFixedIdealDescends : Prop :=
  ∀ (J : Ideal (𝓞 K)),
    J.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom = J →
    ∃ J' : Ideal (𝓞 (NumberField.maximalRealSubfield K)),
      J = J'.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))

/-- **Stronger closure under VC**: composition with the project's
`isPrincipal_of_pow_principal_of_class_eq_complexConj_of_VC` from `Hilbert90.lean`,
which doesn't need a separate descent witness (it derives `[I·σI] = 1` internally
via `map_relNorm_eq_mul_complexConj_of_pow` + VC).

From the non-pth-power chain's `[I] = [σI]` output + the case-I primary structure
`(a+ζb) = I^p` + VC, derive `I.IsPrincipal`. -/
theorem isPrincipal_of_cross_mul_via_relNorm_under_VC
    [Fact (p ≠ 2)]
    (h_VC : p.Coprime (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (a b : ℤ) (ζ : 𝓞 K)
    (h_α_ne : ((a : 𝓞 K) + ζ * (b : 𝓞 K)) ≠ 0)
    (I : Ideal (𝓞 K)) (h𝔞_nz : I ≠ ⊥)
    (h_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p)
    (h_class_eq :
      ClassGroup.mk0
          (⟨I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              ((map_ne_bot_iff_complexConj K I).mpr h𝔞_nz)⟩
            : nonZeroDivisors (Ideal (𝓞 K))) =
        ClassGroup.mk0
          (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩
            : nonZeroDivisors (Ideal (𝓞 K)))) :
    I.IsPrincipal := by
  exact isPrincipal_of_pow_principal_of_class_eq_complexConj_of_VC
    (p := p) (hp_odd := Fact.out) (K := K)
    h_VC h_α_ne h𝔞_nz h_pow h_class_eq

/-- **End-to-end closure: non-pth-power chain + case-I primary + VC → I principal**.

The cleanest statement combining:
1. classGroup_mk0_I_eq_σI_of_cross_mul (cross-mul from γ^p = antiRadical hypothesis)
2. isPrincipal_of_pow_principal_of_class_eq_complexConj_of_VC (Hilbert90.lean)

Conclusion: I.IsPrincipal, assuming case-I primary `(a+ζb) = I^p`, VC, cross-mul
witness from Hilbert 90 + non-pth-power, non-zero hypotheses. -/
theorem isPrincipal_end_to_end_chain
    [Fact (p ≠ 2)]
    (h_VC : p.Coprime (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (a b : ℤ) (ζ : 𝓞 K)
    (h_α_ne : ((a : 𝓞 K) + ζ * (b : 𝓞 K)) ≠ 0)
    (I : Ideal (𝓞 K)) (h𝔞_nz : I ≠ ⊥)
    (h_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p)
    (σI : (Ideal (𝓞 K))⁰)
    (h_σI : (σI : Ideal (𝓞 K)) =
      I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
    (δ : Kˣ)
    (h_cross :
      ((I : FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰
          (NumberField.IsCMField.complexConj K (δ : K)) =
        ((I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
          FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K))))
    (hx_ne :
      ((IsLocalization.sec (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹)).1 : 𝓞 K) ≠ 0)
    (hy_ne :
      ((IsLocalization.sec (𝓞 K)⁰
        (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹)).2 : 𝓞 K) ≠ 0) :
    I.IsPrincipal := by
  have h_class_eq_swap : ClassGroup.mk0
      (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩ : nonZeroDivisors (Ideal (𝓞 K))) =
      ClassGroup.mk0 σI := by
    have h_match :
        (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩ : nonZeroDivisors (Ideal (𝓞 K))) =
        ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩ := rfl
    rw [h_match]
    exact classGroup_mk0_I_eq_σI_of_cross_mul (K := K)
      ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩ σI h_σI δ h_cross hx_ne hy_ne
  have h_class_eq : ClassGroup.mk0
      (⟨I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          ((map_ne_bot_iff_complexConj K I).mpr h𝔞_nz)⟩
        : nonZeroDivisors (Ideal (𝓞 K))) =
      ClassGroup.mk0
        (⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩ :
          nonZeroDivisors (Ideal (𝓞 K))) := by
    have h_σI_eq : (⟨I.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          ((map_ne_bot_iff_complexConj K I).mpr h𝔞_nz)⟩ : nonZeroDivisors (Ideal (𝓞 K))) =
        σI := Subtype.ext h_σI.symm
    rw [h_σI_eq, ← h_class_eq_swap]
  exact isPrincipal_of_pow_principal_of_class_eq_complexConj_of_VC
    (p := p) (hp_odd := Fact.out) (K := K)
    h_VC h_α_ne h𝔞_nz h_pow h_class_eq

/-- The localization numerator for `σδ / δ` is nonzero. -/
theorem caseI_cross_mul_sec_num_ne_zero
    (δ : Kˣ) :
    ((IsLocalization.sec (𝓞 K)⁰
      (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹)).1 :
        𝓞 K) ≠ 0 := by
  apply IsLocalization.sec_fst_ne_zero
  exact mul_ne_zero
    (by
      intro h
      have hδ : (δ : K) ≠ 0 := Units.ne_zero δ
      apply hδ
      have := congrArg (NumberField.IsCMField.complexConj K) h
      rwa [NumberField.IsCMField.complexConj_apply_apply, map_zero] at this)
    (inv_ne_zero (Units.ne_zero δ))

/-- The localization denominator for `σδ / δ` is nonzero. -/
theorem caseI_cross_mul_sec_den_ne_zero
    (δ : Kˣ) :
    ((IsLocalization.sec (𝓞 K)⁰
      (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹)).2 :
        𝓞 K) ≠ 0 := by
  apply IsLocalization.sec_snd_ne_zero
  exact le_rfl

/-- **AK-5a from concrete Hilbert-90 cross-multiplication data.**

This is the Prop-level consumer for the AK-1..AK-4 route: if the actual Case-I
factor ideal supplies a Hilbert-90 witness `δ` with
`I · (σδ) = σI · (δ)` and nonzero localization numerators/denominators, then
the already proved class-group descent chain makes `I` principal under
`¬ p ∣ h⁺`, and hence the AK-5a minus quotient is principal.

The theorem does not construct the cross-multiplication witness; that remains
the mathematical AK source target.  It only wires the existing Lean plumbing
into the exact `AK5a_PrincipalMinusIdeals` surface. -/
theorem AK5a_PrincipalMinusIdeals_of_cross_mul_data_and_not_dvd_hPlus
    (hp_odd : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (h_cross_data :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
        ∀ {ζ : 𝓞 K}, IsPrimitiveRoot ζ p →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 K)}, (hI_ne : I ≠ ⊥) →
        (hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} :
          Set (𝓞 K)) = I ^ p) →
        ∃ δ : Kˣ,
          ((I : FractionalIdeal (𝓞 K)⁰ K) *
              FractionalIdeal.spanSingleton (𝓞 K)⁰
                (NumberField.IsCMField.complexConj K (δ : K)) =
            ((I.map
              (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
              FractionalIdeal (𝓞 K)⁰ K) *
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K))) ∧
          ((IsLocalization.sec (𝓞 K)⁰
            (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹)).1 :
              𝓞 K) ≠ 0 ∧
          ((IsLocalization.sec (𝓞 K)⁰
            (NumberField.IsCMField.complexConj K (δ : K) * ((δ : K))⁻¹)).2 :
              𝓞 K) ≠ 0) :
    AK5a_PrincipalMinusIdeals (p := p) (K := K) := by
  intro a b c hgcd hcaseI heq ζ hζ hab I hI_ne hI_pow
  have hα_ne : ((a : 𝓞 K) + ζ * (b : 𝓞 K)) ≠ 0 := by
    intro hα
    apply hI_ne
    have h_span_zero :
        Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = ⊥ := by
      rw [hα]
      exact Ideal.span_singleton_eq_bot.mpr rfl
    rw [h_span_zero] at hI_pow
    exact pow_eq_zero_iff (Fact.out : Nat.Prime p).pos.ne' |>.mp hI_pow.symm
  have h_VC : p.Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))) := by
    simpa [hPlus] using
      (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)
        (n := hPlus K)).mpr h_not_dvd
  obtain ⟨δ, h_cross, hx_ne, hy_ne⟩ :=
    h_cross_data hgcd hcaseI heq hζ hab hI_ne hI_pow
  have hI_principal : I.IsPrincipal := by
    haveI : Fact (p ≠ 2) := ⟨hp_odd⟩
    let σI : (Ideal (𝓞 K))⁰ :=
      ⟨I.map
        (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
        mem_nonZeroDivisors_iff_ne_zero.mpr
          ((map_ne_bot_iff_complexConj K I).mpr hI_ne)⟩
    exact isPrincipal_end_to_end_chain
      (p := p) (K := K) h_VC a b ζ hα_ne I hI_ne hI_pow σI rfl
      δ h_cross hx_ne hy_ne
  exact principal_ideal_div_conj_isPrincipal (K := K) hI_ne hI_principal

/-- **AK-5a from a concrete Hilbert-90 cross-multiplication witness.**

This is the same consumer as
`AK5a_PrincipalMinusIdeals_of_cross_mul_data_and_not_dvd_hPlus`, but with the
nonzero localization side conditions removed from the source surface: they are
automatic for `δ : Kˣ`.  The remaining Case-I source is therefore only the
actual cross-multiplication identity
`I · (σδ) = σI · (δ)` for each factor ideal. -/
theorem AK5a_PrincipalMinusIdeals_of_cross_mul_witness_and_not_dvd_hPlus
    (hp_odd : p ≠ 2) (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (h_cross_data :
      ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
        ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p = c ^ p →
        ∀ {ζ : 𝓞 K}, IsPrimitiveRoot ζ p →
        (_hab : ¬ (a = 0 ∧ b = 0)) →
        ∀ {I : Ideal (𝓞 K)}, (hI_ne : I ≠ ⊥) →
        (hI_pow : Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} :
          Set (𝓞 K)) = I ^ p) →
        ∃ δ : Kˣ,
          ((I : FractionalIdeal (𝓞 K)⁰ K) *
              FractionalIdeal.spanSingleton (𝓞 K)⁰
                (NumberField.IsCMField.complexConj K (δ : K)) =
            ((I.map
              (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom :
              FractionalIdeal (𝓞 K)⁰ K) *
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (δ : K)))) :
    AK5a_PrincipalMinusIdeals (p := p) (K := K) := by
  exact AK5a_PrincipalMinusIdeals_of_cross_mul_data_and_not_dvd_hPlus
    (p := p) (K := K) hp_odd h_not_dvd
    (fun {a} {b} {c} hgcd hcaseI heq {ζ} hζ hab {I} hI_ne hI_pow ↦ by
      obtain ⟨δ, h_cross⟩ :=
        h_cross_data (a := a) (b := b) (c := c) hgcd hcaseI heq
          (ζ := ζ) hζ hab (I := I) hI_ne hI_pow
      exact ⟨δ, h_cross,
        caseI_cross_mul_sec_num_ne_zero (K := K) δ,
        caseI_cross_mul_sec_den_ne_zero (K := K) δ⟩)

/-- **AK-5a from the AK-chain unramified source under Vandiver.**

This is a source-facing Case-I reducer.  It does not prove the AK-chain
unramified input; it shows that this input is strong enough to supply the
reviewer-preferred `AK5a_PrincipalMinusIdeals` endpoint:

* if the case-I anti-radical is a `p`-th power, Hilbert 90 gives the concrete
  cross-multiplication witness already consumed by AK-5a;
* if it is not a `p`-th power, the supplied unramified AK extension contradicts
  Hilbert 94 under `¬ p ∣ h⁺`, so that case is vacuous.
-/
theorem AK5a_PrincipalMinusIdeals_of_AK_unramified_and_not_dvd_hPlus
    (hp_odd : p ≠ 2) (hp_ne_three : p ≠ 3)
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    (h_LK_unram_per_case : ∀ {a b c : ℤ}
      (_heq : a ^ p + b ^ p = c ^ p)
      (_hcaseI : ¬ (p : ℤ) ∣ a * b * c)
      {ζ : 𝓞 K} (_hζ : IsPrimitiveRoot ζ p)
      (hab : ¬ (a = 0 ∧ b = 0)),
      Algebra.Unramified (𝓞 K)
        (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
          (p := p) K
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            K a b ζ hab)
          (caseI_antiRadical_ne_zero (K := K) hp_odd _hcaseI _hζ hab)))) :
    AK5a_PrincipalMinusIdeals (p := p) (K := K) := by
  refine AK5a_PrincipalMinusIdeals_of_cross_mul_witness_and_not_dvd_hPlus
    (p := p) (K := K) hp_odd h_not_dvd ?_
  intro a b c _hgcd hcaseI heq ζ hζ hab I hI_ne hI_pow
  by_cases h_pow :
      ∃ γ : K,
        γ ^ p =
          BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
            K a b ζ hab
  · obtain ⟨γ, hγ_pow⟩ := h_pow
    have hγ_ne : γ ≠ 0 := by
      intro hγ
      have hα_ne :=
        caseI_antiRadical_ne_zero (K := K) hp_odd hcaseI hζ hab
      apply hα_ne
      rw [← hγ_pow, hγ]
      exact zero_pow (Fact.out : Nat.Prime p).pos.ne'
    exact
      cross_mul_witness_of_antiRadical_pth_power
        (K := K) (p := p) hp_odd hcaseI hζ hab hI_ne hI_pow
        γ hγ_ne hγ_pow
  · have h_irr : Irreducible (Polynomial.X ^ p -
          Polynomial.C
            (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
              K a b ζ hab)
          : Polynomial K) := by
      rw [X_pow_sub_C_irreducible_iff_not_pth_power (K := K) hp_odd]
      intro γ hγ
      exact h_pow ⟨γ, hγ⟩
    exfalso
    exact
      caseI_FLT_false_of_h_irr_h_LK_unram_VC
        (K := K) hp_odd hp_ne_three h_not_dvd hcaseI hζ hab h_irr
        (h_LK_unram_per_case heq hcaseI hζ hab)

end AntiRadicalNonPthPower

/-- FLT37-specialized named form of
`AK5a_PrincipalMinusIdeals_of_AK_unramified_and_not_dvd_hPlus`.

This theorem consumes the existing `CaseIAntiKummerLKUnramified` source
predicate directly, instead of exposing the full anti-Kummer lift type at each
use site.  The substantive source remains exactly the named unramifiedness
predicate; this is only a packaging adapter to the reviewer-preferred AK5a
surface. -/
theorem AK5a_PrincipalMinusIdeals_of_CaseIAntiKummerLKUnramified_and_not_dvd_hPlus
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_not_dvd : ¬ (37 : ℕ) ∣ hPlus (CyclotomicField 37 ℚ))
    (h_LK : CaseIAntiKummerLKUnramified) :
    AK5a_PrincipalMinusIdeals (p := 37) (K := CyclotomicField 37 ℚ) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  unfold AK5a_PrincipalMinusIdeals
  intro a b c hgcd hcaseI heq ζ hζ hab I hI_ne hI_pow
  exact
    (AK5a_PrincipalMinusIdeals_of_AK_unramified_and_not_dvd_hPlus
      (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide : (37 : ℕ) ≠ 2) (by decide : (37 : ℕ) ≠ 3)
      h_not_dvd
      (fun {_a _b _c} heq hcaseI {_ζ} hζ hab ↦
        h_LK heq hcaseI hζ hab))
      hgcd hcaseI heq hζ hab hI_ne hI_pow

section CaseIAntiKummerLKUnramifiedComposition

open Polynomial

/-- **`CaseIAntiKummerLKUnramified` follows from the universal forms of the AK-5
substantive outputs.** The hypothesis includes `_heq : a^37 + b^37 = c^37`,
matching the soundness restriction on `CaseIAntiKummerLKUnramified`. -/
theorem caseIAntiKummerLKUnramified_of_universal_hypotheses
    (h : ∀ {a b c : ℤ}
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
              (by decide : (37 : ℕ) ≠ 2) hcaseI hζ hab)))) :
    CaseIAntiKummerLKUnramified := fun {_ _ _} heq hcaseI {_} hζ hab ↦
  h heq hcaseI hζ hab

end CaseIAntiKummerLKUnramifiedComposition

end BernoulliRegular.FLT37.LehmerVandiver.CaseI

end
