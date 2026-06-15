module

public import BernoulliRegular.TotallyRealSubfield.FixedAssociate

/-!
# Class-group descent for the totally real subfield

This file finishes the descent from `𝒪_K` to `𝒪_{K⁺}`, proves injectivity of
`Cl(𝒪_{K⁺}) → Cl(𝒪_K)`, and packages `h⁻`.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular

section CyclotomicSetup

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- `𝓞 L` is faithfully flat over `𝓞(L⁺)`. -/
theorem ringOfIntegers_faithfullyFlat_maximalRealSubfield
    (L : Type*) [Field L] [NumberField L] :
    Module.FaithfullyFlat (𝓞 (NumberField.maximalRealSubfield L)) (𝓞 L) := by
  let R := 𝓞 (NumberField.maximalRealSubfield L)
  let S := 𝓞 L
  haveI : Module.Flat R S := inferInstance
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) := by
    intro q
    obtain ⟨⟨Q, hQprime, hQover⟩⟩ := q.asIdeal.nonempty_primesOver (S := S)
    refine ⟨⟨Q, hQprime⟩, ?_⟩
    exact PrimeSpectrum.ext (((Ideal.liesOver_iff _ _).mp hQover).symm)
  exact Module.FaithfullyFlat.of_comap_surjective hsurj

/-- Extending and contracting ideals along `𝓞(L⁺) ⊆ 𝓞 L` is the identity. -/
theorem map_comap_eq_ringOfIntegers
    (L : Type*) [Field L] [NumberField L]
    (J : Ideal (𝓞 (NumberField.maximalRealSubfield L))) :
    (J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield L)) (𝓞 L))).comap
        (algebraMap (𝓞 (NumberField.maximalRealSubfield L)) (𝓞 L)) = J := by
  let R := 𝓞 (NumberField.maximalRealSubfield L)
  let S := 𝓞 L
  letI : Module.FaithfullyFlat R S := ringOfIntegers_faithfullyFlat_maximalRealSubfield L
  simpa using Ideal.comap_map_eq_self_of_faithfullyFlat (A := R) (B := S) J

/-- If `I · 𝒪_K = (b)` with `b` descending from `𝒪_{K⁺}`, then `I` is principal. -/
theorem isPrincipal_of_map_eq_span_singleton_of_mem
    (I : Ideal (𝓞 (K⁺)))
    (b₀ : 𝓞 (K⁺))
    (hb : I.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) =
      Ideal.span {algebraMap (𝓞 (K⁺)) (𝓞 K) b₀}) :
    I.IsPrincipal := by
  refine ⟨b₀, ?_⟩
  let f : 𝓞 (K⁺) →+* 𝓞 K := algebraMap (𝓞 (K⁺)) (𝓞 K)
  have hbc := congrArg (Ideal.comap f) hb
  have hspan : Ideal.comap f (Ideal.span {f b₀}) = Ideal.span {b₀} := by
    calc
      Ideal.comap f (Ideal.span {f b₀}) = Ideal.comap f ((Ideal.span {b₀}).map f) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.span {b₀} := map_comap_eq_ringOfIntegers K (Ideal.span {b₀})
  calc
    I = Ideal.comap f (I.map f) := (map_comap_eq_ringOfIntegers K I).symm
    _ = Ideal.comap f (Ideal.span {f b₀}) := hbc
    _ = Ideal.span {b₀} := hspan

include hp_odd in
/-- Assembled proof of Diekmann Prop. 55 / Washington Thm. 4.14. -/
theorem isPrincipal_of_isPrincipal_map_Kplus' [IsCMField K]
    (I : Ideal (𝓞 (K⁺)))
    (hI : (I.map (algebraMap (𝓞 (K⁺)) (𝓞 K))).IsPrincipal) :
    I.IsPrincipal := by
  obtain ⟨a, ha⟩ := hI
  by_cases hzero : a = 0
  · have : I = ⊥ := by
      rw [← Ideal.map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective (𝓞 (K⁺)) (𝓞 K)), ha, hzero]
      simp
    exact this ▸ bot_isPrincipal
  have hIa : I.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) = Ideal.span {a} := ha
  have hIcon := ideal_map_conj_eq (K := K) I
  have hIca : I.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) =
      Ideal.span {ringOfIntegersComplexConj K a} := by
    rw [← hIcon, hIa, conj_map_span_singleton]
  obtain ⟨u, hu⟩ := conj_generator_associated (K := K) a hzero I hIa hIca
  have hanti := conj_unit_mul_eq_one (K := K) a hzero u hu
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  obtain ⟨n, k, hclass⟩ :=
    antisymmetric_unit_eq_neg_one_pow_mul_zeta_pow
      (p := p) (hp_odd := hp_odd) (K := K) (hζ := hζ) u hanti
  obtain ⟨b, hb_conj, hb_span⟩ :=
    exists_conj_fixed_associate_of_classification
      (p := p) (hp_odd := hp_odd) (K := K) (hζ := hζ) I a u hIa hu ⟨n, k, hclass⟩
  obtain ⟨b₀, hb₀⟩ := mem_ringOfIntegers_of_conj_eq_self (K := K) b hb_conj
  have hspan : I.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) = Ideal.span {b} := by
    rw [hIa, ← hb_span]
  rw [← hb₀] at hspan
  exact isPrincipal_of_map_eq_span_singleton_of_mem K I b₀ hspan

include hp_odd in
/-- **Diekmann Prop. 55** (cf. Washington Thm. 4.14).

If an ideal of `𝒪_{K⁺}` becomes principal after extension to `𝒪_K`, then it
was already principal. -/
theorem isPrincipal_of_isPrincipal_map_Kplus [IsCMField K]
    (I : Ideal (𝓞 (K⁺)))
    (hI : (I.map (algebraMap (𝓞 (K⁺)) (𝓞 K))).IsPrincipal) :
    I.IsPrincipal :=
  isPrincipal_of_isPrincipal_map_Kplus' (p := p) (hp_odd := hp_odd) (K := K) I hI

/-- The natural monoid homomorphism `Cl(𝒪_{K⁺}) → Cl(𝒪_K)` induced by the
inclusion `𝒪_{K⁺} ↪ 𝒪_K`. -/
abbrev classGroupMap [IsCMField K] :
    ClassGroup (𝓞 (K⁺)) →* ClassGroup (𝓞 K) :=
  ClassGroup.extensionMap (𝓞 (K⁺)) (𝓞 K)

include hp_odd in
/-- **Diekmann Prop 55**, monoid-hom form. The class-group map
`Cl(𝒪_{K⁺}) → Cl(𝒪_K)` is injective for `K = ℚ(ζ_p)`. -/
theorem classGroupMap_injective [IsCMField K] :
    Function.Injective (classGroupMap K) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [ClassGroup.mk0_eq_one_iff I.2]
  refine isPrincipal_of_isPrincipal_map_Kplus (p := p) (hp_odd := hp_odd) (K := K) I.1 ?_
  have hne : I.1.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective _ _)).not.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
  rw [← ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hne),
    ← ClassGroup.extensionMap_mk0]
  exact hc

local notation3 "h" => BernoulliRegular.h K
local notation3 "h⁺" => BernoulliRegular.hPlus K

include hp_odd in
/-- The class number of `K⁺` divides the class number of `K`. -/
theorem hPlus_dvd_h [IsCMField K] : h⁺ ∣ h := by
  rw [BernoulliRegular.hPlus, BernoulliRegular.h,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_injective (classGroupMap K)
    (classGroupMap_injective p hp_odd K)

/-- The *relative class number* `h⁻ := h / h⁺`, written locally as `h⁻`. -/
noncomputable def hMinus [IsCMField K] : ℕ := h / h⁺

local notation3 "h⁻" => BernoulliRegular.hMinus K

include hp_odd in
theorem h_eq_hPlus_mul_hMinus [IsCMField K] : h = h⁺ * h⁻ := by
  rw [hMinus, Nat.mul_div_cancel' (hPlus_dvd_h p hp_odd K)]

include hp_odd in
/-- The relative class number is positive. -/
theorem hMinus_pos [IsCMField K] : 0 < h⁻ :=
  Nat.div_pos (Nat.le_of_dvd Fintype.card_pos (hPlus_dvd_h p hp_odd K)) Fintype.card_pos

end CyclotomicSetup

end BernoulliRegular

end
