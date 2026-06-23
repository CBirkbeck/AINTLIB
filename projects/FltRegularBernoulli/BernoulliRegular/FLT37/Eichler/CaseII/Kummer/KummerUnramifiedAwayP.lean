import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Localization.AtPrime.Extension

import BernoulliRegular.FLT37.Eichler.CaseII.Kummer.KummerDifferentTrivial

/-!
# [FLT37-CASEII-LEMMA-9.1-AWAY] The "away from 37" half of Washington Lemma 9.1

This file **proves** `CaseIIKummerUnramifiedAway37` (stated in
`CaseIIIdealKummerUnramifiedProof.lean`), the tame Kummer-extension unramifiedness away from the
prime `37`: for a radical `α : K = ℚ(ζ₃₇)` whose fractional ideal is a `37`-th power
`(α) = 𝔟^{37}`, every prime `P` of `𝓞 L` (`L = K(α^{1/37})`) **not** lying over
`37` is unramified over `𝓞 K`.

## The local statement (genuine local algebraic number theory)

mathlib has no tame-ramification API, so the local content is built here from the per-prime
separable-residue-minpoly criterion `isUnramifiedAt_of_Separable_minpoly` (flt-regular's entry
point, the one `KummersLemma.isUnramified` uses).

The mathematics: for a prime `P` of `𝓞 L` with `37 ∉ P`, set `q := P ∩ 𝓞 K`.
Then `37 ∉ q`, so `37` is a unit in the residue field `κ(P)`.  From `(α) = 𝔟^{37}`
we get `v_q(α) = 37·v_q(𝔟) ≡ 0` `(mod 37)`.  Localizing at `q` (a DVR
`A := (𝓞 K)_q`), write `α = ϖ^{37k}·u` with `u` a `q`-unit and `ϖ` a
`q`-uniformizer; then `θ' := θ/ϖ^k` satisfies `(θ')^{37} = u ∈ Aˣ`, so the residue
minimal polynomial of `θ'` is `X^{37} - ū` with `ū ≠ 0` and `37` a unit — hence
**separable** (`Polynomial.separable_X_pow_sub_C`).  The separable-residue-minpoly
criterion gives `P` unramified.

The clean self-contained engine is `isUnramifiedAt_dvr_of_pow_eq_unit`: over an abstract DVR `A`
with `n` a unit, a root `θ` of `X^n - u` (`u : Aˣ`) generates an extension unramified at the
maximal ideal of `A`.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (Lemma 9.1, away-from-`p` half).
* flt-regular `FltRegular.NumberTheory.Unramified.isUnramifiedAt_of_Separable_minpoly`.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section DVREngine

open IsLocalRing

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
variable {L : Type*} [Field L] [Algebra A L]
variable {S : Type*} [CommRing S] [Algebra A S] [Algebra S L]
  [IsScalarTower A S L] [IsIntegralClosure S A L]

omit [IsDedekindDomain A] in
/-- `θ` (root of `X^n - u`, `u : Aˣ`, `n ≥ 1`) is integral over `A`. -/
theorem isIntegral_of_pow_eq_unit {n : ℕ} (hn1 : n ≠ 0) (u : Aˣ) {θ : L}
    (e : θ ^ n = algebraMap A L (u : A)) : IsIntegral A θ := by
  refine ⟨X ^ n - C (u : A), monic_X_pow_sub_C (u : A) hn1, ?_⟩
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C, e, sub_self]

/-- `minpoly A θ` divides `X^n - C u` over `A`.  Uses `minpoly.isIntegrallyClosed_dvd` (`A` is a
DVR, hence integrally closed). -/
theorem minpoly_dvd_X_pow_sub_C_of_pow_eq_unit (K' : Type*) [Field K'] [Algebra A K']
    [IsFractionRing A K'] [Algebra K' L] [IsScalarTower A K' L]
    {n : ℕ} (hn1 : n ≠ 0) (u : Aˣ) {θ : L}
    (e : θ ^ n = algebraMap A L (u : A)) :
    minpoly A θ ∣ (X ^ n - C (u : A)) := by
  have hAL_inj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K' L]
    exact (algebraMap K' L).injective.comp (IsFractionRing.injective A K')
  haveI : Module.IsTorsionFree A L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hAL_inj
  refine minpoly.isIntegrallyClosed_dvd (isIntegral_of_pow_eq_unit hn1 u e) ?_
  simp only [map_sub, aeval_X_pow, aeval_C, e, sub_self]

/-- **The separable residue minimal polynomial of a Kummer generator over a DVR.**

Let `A` be a Dedekind domain, `p` a nonzero prime of `A` with `n` a unit in the
residue field `A ⧸ p`.  If `θ : L` is a root of `X^n - u` for a unit `u : Aˣ`,
then the residue minimal polynomial `(minpoly A θ).map (mk p)` is separable: it
divides `X^n - ū`, which is separable since `ū ≠ 0` (`u` a unit) and `↑n ≠ 0`
in the residue field. -/
theorem separable_minpoly_map_of_pow_eq_unit (K' : Type*) [Field K'] [Algebra A K']
    [IsFractionRing A K'] [Algebra K' L] [IsScalarTower A K' L]
    (p : Ideal A) [hp : p.IsPrime] (hpbot : p ≠ ⊥)
    {n : ℕ} (hn : ((n : A) : A ⧸ p) ≠ 0) (u : Aˣ) {θ : L}
    (e : θ ^ n = algebraMap A L (u : A)) :
    Polynomial.Separable ((minpoly A θ).map (Ideal.Quotient.mk p)) := by
  haveI := hp.isMaximal hpbot
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  have hn1 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hu_ne : (Ideal.Quotient.mk p (u : A)) ≠ 0 := by
    have : IsUnit (Ideal.Quotient.mk p (u : A)) := u.isUnit.map (Ideal.Quotient.mk p)
    exact this.ne_zero
  have hsep : Polynomial.Separable
      (X ^ n - C (Ideal.Quotient.mk p (u : A)) : Polynomial (A ⧸ p)) :=
    separable_X_pow_sub_C _ (by simpa using hn) hu_ne
  have hdvd : (minpoly A θ).map (Ideal.Quotient.mk p) ∣
      (X ^ n - C (Ideal.Quotient.mk p (u : A)) : Polynomial (A ⧸ p)) := by
    have h := Polynomial.map_dvd (Ideal.Quotient.mk p)
      (minpoly_dvd_X_pow_sub_C_of_pow_eq_unit (A := A) (L := L) K' hn1 u e)
    rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] at h
  exact hsep.of_dvd hdvd

/-- **The local tame-Kummer unramifiedness over a DVR.**

Let `A` be a Dedekind domain with fraction field `K`, `L/K` finite separable, `S` the integral
closure of `A` in `L`.  Let `P` be a nonzero prime of `S` lying over the (nonzero) prime
`P.under A`, with `n` a unit in `A ⧸ (P.under A)`.  If `θ : L` generates `L` over `K`
(`Algebra.adjoin K {θ} = ⊤`) and `θ^n = u` for a unit `u : Aˣ`, then `P` is unramified over `A`
(mathlib's `Algebra.IsUnramifiedAt A P`).

This is the tame Kummer unramifiedness, the genuine local content of Washington Lemma 9.1 away from
the ramified prime.  Proof: the residue minimal polynomial `(minpoly A θ).map (mk (P.under A)) =
X^n - ū` is separable (`separable_minpoly_map_of_pow_eq_unit`), so
`isUnramifiedAt_of_Separable_minpoly` applies. -/
theorem isUnramifiedAt_dvr_of_pow_eq_unit (K' : Type*) [Field K'] [Algebra A K']
    [IsFractionRing A K'] [Algebra K' L] [IsScalarTower A K' L]
    [FiniteDimensional K' L] [Algebra.IsSeparable K' L]
    (P : Ideal S) [hP : P.IsPrime] (hPbot : P ≠ ⊥)
    (hpbot : P.under A ≠ ⊥)
    {n : ℕ} (hn : ((n : A) : A ⧸ P.under A) ≠ 0) (u : Aˣ) {θ : L}
    (hθ_gen : Algebra.adjoin K' {θ} = ⊤)
    (e : θ ^ n = algebraMap A L (u : A)) :
    Algebra.IsUnramifiedAt A P := by
  have hn1 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hθ_int : IsIntegral A θ := isIntegral_of_pow_eq_unit hn1 u e
  haveI : (P.under A).IsPrime := Ideal.IsPrime.under A P
  exact isUnramifiedAt_of_Separable_minpoly (R := A) K' (S := S) L P hPbot θ hθ_int hθ_gen
    (separable_minpoly_map_of_pow_eq_unit (A := A) (L := L) K' (P.under A) hpbot hn u e)

end DVREngine

section Generator

open FLT37.LehmerVandiver.CaseI.AntiKummer

/-- **The canonical root generates the Kummer extension over `K`** (unconditionally, no
irreducibility hypothesis), because `K` contains the `p`-th roots of unity.

`L = antiKummerLift K α = SplittingField (X^p - C α)` is generated by the full root
set of `X^p - C α`. Each such root `r` satisfies `r^p = α = θ^p` (where
`θ = antiKummerLiftRoot`), so `(r·θ⁻¹)^p = 1`; since `K` contains a primitive
`p`-th root of unity, every `p`-th root of unity in `L` is the image of one in `K`,
hence `r·θ⁻¹ ∈ K` and `r = (r·θ⁻¹) • θ ∈ K[θ]`. Therefore the whole root set lies
in `K[θ]`, so `K[θ] = ⊤`. -/
theorem antiKummerLiftRoot_adjoin_K_eq_top
    (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]
    (α : K) (hα : α ≠ 0) :
    Algebra.adjoin K {antiKummerLiftRoot (p := p) K α hα} = ⊤ := by
  set L := antiKummerLift (p := p) K α hα
  set θ := antiKummerLiftRoot (p := p) K α hα
  have hp_pos : 0 < p := hp.out.pos
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hζ_prim : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  have hθ_pow : θ ^ p = algebraMap K L α := antiKummerLiftRoot_pow_eq (p := p) K α hα
  have hθ_ne : θ ≠ 0 := antiKummerLiftRoot_ne_zero (p := p) K α hα
  rw [eq_top_iff, ← Polynomial.IsSplittingField.adjoin_rootSet L
      (Polynomial.X ^ p - Polynomial.C α), Algebra.adjoin_le_iff]
  intro r hr
  rw [Polynomial.mem_rootSet] at hr
  obtain ⟨_, hr_eval⟩ := hr
  have hr_pow : r ^ p = algebraMap K L α := by
    have := hr_eval
    rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero] at this
    simpa using this
  have hquot_pow : (r * θ⁻¹) ^ p = 1 := by
    rw [mul_pow, hr_pow, ← hθ_pow, inv_pow,
      mul_inv_cancel₀ (pow_ne_zero p hθ_ne)]
  have hmem_range : (r * θ⁻¹) ∈ (algebraMap K L).range := by
    have hr_in_nth : r * θ⁻¹ ∈ (Polynomial.nthRoots p (1 : L)) := by
      rw [Polynomial.mem_nthRoots hp_pos]
      exact hquot_pow
    have hζL : IsPrimitiveRoot (algebraMap K L (IsCyclotomicExtension.zeta p ℚ K)) p :=
      hζ_prim.map_of_injective (algebraMap K L).injective
    rw [hζL.nthRoots_eq (a := (1 : L)) (α := (1 : L)) (by rw [one_pow])] at hr_in_nth
    simp only [Multiset.mem_map, Multiset.mem_range, mul_one] at hr_in_nth
    obtain ⟨i, _, hi⟩ := hr_in_nth
    refine ⟨IsCyclotomicExtension.zeta p ℚ K ^ i, ?_⟩
    rw [← hi, map_pow]
  obtain ⟨k, hk⟩ := hmem_range
  have hr_eq : r = algebraMap K L k * θ := by
    rw [hk, mul_assoc, inv_mul_cancel₀ hθ_ne, mul_one]
  rw [hr_eq]
  exact mul_mem (Subalgebra.algebraMap_mem _ k) (Algebra.self_mem_adjoin_singleton K θ)

end Generator

section LocalUnit

open FractionalIdeal IsLocalization

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (q : Ideal R) [q.IsPrime]

/-- The lifted `(𝓞 K)_q`-algebra structure on the fraction field `K`. -/
noncomputable abbrev atPrimeAlgebraField : Algebra (Localization.AtPrime q) K :=
  (IsLocalization.lift (M := q.primeCompl) (g := algebraMap R K)
    (fun ⟨y, hy⟩ ↦ by
      simpa using IsLocalization.map_units (M := R⁰) K
        ⟨y, q.primeCompl_le_nonZeroDivisors hy⟩)).toAlgebra

attribute [local instance] atPrimeAlgebraField

instance atPrime_isScalarTower_field : IsScalarTower R (Localization.AtPrime q) K :=
  IsScalarTower.of_algebraMap_eq'
    (RingHom.ext fun x ↦ by simp [RingHom.algebraMap_toAlgebra])

instance atPrime_isFractionRing_field : IsFractionRing (Localization.AtPrime q) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl _ _

/-- The extension-of-fractional-ideals ring homomorphism along the localization map
`R → Localization.AtPrime q` fixes `spanSingleton`. -/
theorem extendedHom'_spanSingleton_atPrime
    (hf :
      R⁰ ≤ Submonoid.comap (algebraMap R (Localization.AtPrime q)) (Localization.AtPrime q)⁰)
    (x : K) :
    (extendedHom' (M := R⁰) (N := (Localization.AtPrime q)⁰)
        (f := algebraMap R (Localization.AtPrime q)) K hf (spanSingleton R⁰ x)) =
      spanSingleton (Localization.AtPrime q)⁰ x := by
  have hmap : (IsLocalization.map (S := K) K (algebraMap R (Localization.AtPrime q)) hf) =
      RingHom.id K := by
    refine IsLocalization.ringHom_ext R⁰ ?_
    ext y
    rw [RingHom.comp_apply, IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply,
      RingHom.comp_apply, RingHom.id_apply]
  rw [extendedHom'_apply]
  apply coeToSubmodule_injective
  change (extended K hf (spanSingleton R⁰ x) : Submodule (Localization.AtPrime q) K) =
    (spanSingleton (Localization.AtPrime q)⁰ x : Submodule (Localization.AtPrime q) K)
  rw [coe_extended_eq_span, hmap]
  have himg : (RingHom.id K) '' ((spanSingleton R⁰ x : FractionalIdeal R⁰ K) : Set K) =
      ((Submodule.span R {x} : Submodule R K) : Set K) := by
    rw [RingHom.coe_id, Set.image_id]
    ext y
    simp only [mem_spanSingleton, SetLike.mem_coe, Submodule.mem_span_singleton]
  rw [himg, Submodule.span_span_of_tower R (Localization.AtPrime q) ({x} : Set K)]
  exact (coe_spanSingleton (S := (Localization.AtPrime q)⁰) x).symm

/-- **The local `p`-th-root unit.**  If `α ≠ 0` and `(α) = 𝔟^p` as fractional ideals
of `R`, then in the PID `A := R_q` there is `γ : K` and `u : Aˣ` with `α = u·γ^p`. -/
theorem exists_unit_mul_pow_of_spanSingleton_eq_pow
    [IsDedekindDomain R] {α : K} {p : ℕ}
    {𝔟 : FractionalIdeal R⁰ K} (h𝔟 : spanSingleton R⁰ α = 𝔟 ^ p) :
    ∃ (γ : K) (u : (Localization.AtPrime q)ˣ),
      α = (algebraMap (Localization.AtPrime q) K (u : Localization.AtPrime q)) * γ ^ p := by
  have hf : R⁰ ≤ Submonoid.comap (algebraMap R (Localization.AtPrime q))
      (Localization.AtPrime q)⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective R (Localization.AtPrime q))
  have hpush : spanSingleton (Localization.AtPrime q)⁰ α =
      (extendedHom' (M := R⁰) (N := (Localization.AtPrime q)⁰)
        (f := algebraMap R (Localization.AtPrime q)) K hf 𝔟) ^ p := by
    rw [← extendedHom'_spanSingleton_atPrime (R := R) (K := K) q hf α, h𝔟, map_pow]
  have hprinc : (extendedHom' (M := R⁰) (N := (Localization.AtPrime q)⁰)
      (f := algebraMap R (Localization.AtPrime q)) K hf 𝔟 :
      Submodule (Localization.AtPrime q) K).IsPrincipal :=
    FractionalIdeal.isPrincipal _
  obtain ⟨γ, hγ⟩ := (isPrincipal_iff _).mp hprinc
  rw [hγ, spanSingleton_pow] at hpush
  obtain ⟨u, hu⟩ :=
    (spanSingleton_eq_spanSingleton (R := Localization.AtPrime q) (P := K)).mp hpush.symm
  exact ⟨γ, u, by rw [← hu, Units.smul_def, Algebra.smul_def]⟩

end LocalUnit

section Assembly

open FLT37.LehmerVandiver.CaseI.AntiKummer IsLocalRing Polynomial IsLocalization IsScalarTower

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **[FLT37-CASEII-LEMMA-9.1-AWAY] `CaseIIKummerUnramifiedAway37` is proven.**

For a radical `α : K = ℚ(ζ₃₇)` whose fractional ideal is a `37`-th power, every prime `P` of
`𝓞 L` (`L = K(α^{1/37})`) not lying over `37` is unramified over `𝓞 K`. -/
theorem caseIIKummerUnramifiedAway37_proven : CaseIIKummerUnramifiedAway37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro α hα h_ideal P hP_prime hP_bot h37
  obtain ⟨𝔟, h𝔟⟩ := h_ideal
  set L := antiKummerLift (p := 37) (CyclotomicField 37 ℚ) α hα
  set q : Ideal (𝓞 (CyclotomicField 37 ℚ)) := P.under (𝓞 (CyclotomicField 37 ℚ)) with hq
  haveI : P.LiesOver q := ⟨rfl⟩
  haveI : q.IsPrime := Ideal.IsPrime.under (𝓞 (CyclotomicField 37 ℚ)) P
  haveI : FiniteDimensional (CyclotomicField 37 ℚ) L :=
    Polynomial.IsSplittingField.finiteDimensional L (X ^ 37 - C α)
  haveI : Algebra.IsSeparable (CyclotomicField 37 ℚ) L :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsScalarTower (𝓞 (CyclotomicField 37 ℚ)) (𝓞 L) L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hq_bot : q ≠ ⊥ := Ideal.under_ne_bot (𝓞 (CyclotomicField 37 ℚ)) hP_bot
  letI A := Localization.AtPrime q
  letI Sₚ := Localization (Algebra.algebraMapSubmonoid (𝓞 L) q.primeCompl)
  letI : Algebra A Sₚ := localizationAlgebra q.primeCompl (𝓞 L)
  haveI : IsScalarTower (𝓞 (CyclotomicField 37 ℚ)) A Sₚ := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 L) q.primeCompl) Sₚ :=
    Localization.isLocalization
  have hqle : Algebra.algebraMapSubmonoid (𝓞 L) q.primeCompl ≤ (𝓞 L)⁰ :=
    Submonoid.map_le_of_le_comap _ <| q.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  haveI : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hqle
  haveI : Module.IsTorsionFree A Sₚ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot,
      RingHom.ker_eq_bot_iff_eq_zero]
    simp
  haveI : Module.Finite A Sₚ :=
    Module.Finite.of_isLocalization (𝓞 (CyclotomicField 37 ℚ)) (𝓞 L) q.primeCompl
  haveI : IsIntegrallyClosed Sₚ := isIntegrallyClosed_of_isLocalization _ _ hqle
  haveI : Algebra.IsIntegral A Sₚ := Algebra.isIntegral_def.mpr
    (IsLocalization.algebraMap_eq_map_map_submonoid q.primeCompl (𝓞 L) A Sₚ ▸
      isIntegral_localization : (algebraMap A Sₚ).IsIntegral)
  letI : Algebra A (CyclotomicField 37 ℚ) := atPrimeAlgebraField q
  haveI : IsScalarTower (𝓞 (CyclotomicField 37 ℚ)) A (CyclotomicField 37 ℚ) :=
    atPrime_isScalarTower_field q
  letI : Algebra Sₚ L :=
    (IsLocalization.map (S := Sₚ) L (T := (𝓞 L)⁰) (RingHom.id (𝓞 L)) hqle).toAlgebra
  haveI : IsScalarTower (𝓞 L) Sₚ L :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hqle
  haveI : IsFractionRing Sₚ L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Algebra.algebraMapSubmonoid (𝓞 L) q.primeCompl) _ _
  haveI hAKL : IsScalarTower (𝓞 (CyclotomicField 37 ℚ)) A L := IsScalarTower.of_algebraMap_eq
    (fun x => by
      rw [IsScalarTower.algebraMap_apply (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) L,
        IsScalarTower.algebraMap_apply (𝓞 (CyclotomicField 37 ℚ)) A (CyclotomicField 37 ℚ),
        ← IsScalarTower.algebraMap_apply A (CyclotomicField 37 ℚ) L])
  haveI hOLSₚ : IsScalarTower (𝓞 (CyclotomicField 37 ℚ)) (𝓞 L) Sₚ :=
    inferInstanceAs (IsScalarTower (𝓞 (CyclotomicField 37 ℚ)) (𝓞 L)
      (Localization (Algebra.algebraMapSubmonoid (𝓞 L) q.primeCompl)))
  haveI : IsScalarTower A Sₚ L := by
    refine IsScalarTower.of_algebraMap_eq' <| IsLocalization.ringHom_ext q.primeCompl ?_
    rw [RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq (𝓞 (CyclotomicField 37 ℚ)) A Sₚ,
      IsScalarTower.algebraMap_eq (𝓞 (CyclotomicField 37 ℚ)) (𝓞 L) Sₚ,
      ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq (𝓞 L) Sₚ L,
      IsScalarTower.algebraMap_eq A (CyclotomicField 37 ℚ) L,
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  haveI : IsIntegralClosure Sₚ A L := IsIntegralClosure.of_isIntegrallyClosed Sₚ A L
  obtain ⟨γ, u, hαγu⟩ := exists_unit_mul_pow_of_spanSingleton_eq_pow
    (R := 𝓞 (CyclotomicField 37 ℚ)) (K := CyclotomicField 37 ℚ) q h𝔟
  have hγ_ne : γ ≠ 0 := by
    rintro rfl
    apply hα
    rw [hαγu, zero_pow (by norm_num), mul_zero]
  have hγL_ne0 : algebraMap (CyclotomicField 37 ℚ) L γ ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hγ_ne
  have hγL_ne : (algebraMap (CyclotomicField 37 ℚ) L γ) ^ 37 ≠ 0 := pow_ne_zero 37 hγL_ne0
  have hθpow : antiKummerLiftRoot (p := 37) (CyclotomicField 37 ℚ) α hα ^ 37 =
      algebraMap (CyclotomicField 37 ℚ) L α :=
    antiKummerLiftRoot_pow_eq (p := 37) (CyclotomicField 37 ℚ) α hα
  have hθ'_pow : (antiKummerLiftRoot (p := 37) (CyclotomicField 37 ℚ) α hα *
      (algebraMap (CyclotomicField 37 ℚ) L γ)⁻¹) ^ 37 = algebraMap A L (u : A) := by
    have key : (antiKummerLiftRoot (p := 37) (CyclotomicField 37 ℚ) α hα *
        (algebraMap (CyclotomicField 37 ℚ) L γ)⁻¹) ^ 37 *
        (algebraMap (CyclotomicField 37 ℚ) L γ) ^ 37 =
        algebraMap A L (u : A) * (algebraMap (CyclotomicField 37 ℚ) L γ) ^ 37 := by
      have hlhs : (antiKummerLiftRoot (p := 37) (CyclotomicField 37 ℚ) α hα *
          (algebraMap (CyclotomicField 37 ℚ) L γ)⁻¹) ^ 37 *
          (algebraMap (CyclotomicField 37 ℚ) L γ) ^ 37 =
          algebraMap (CyclotomicField 37 ℚ) L α := by
        rw [mul_pow, inv_pow, mul_assoc, inv_mul_cancel₀ hγL_ne, mul_one]
        exact hθpow
      have hrhs : algebraMap A L (u : A) * (algebraMap (CyclotomicField 37 ℚ) L γ) ^ 37 =
          algebraMap (CyclotomicField 37 ℚ) L α := by
        rw [IsScalarTower.algebraMap_apply A (CyclotomicField 37 ℚ) L (u : A), ← map_pow,
          ← map_mul]
        exact (congrArg (algebraMap (CyclotomicField 37 ℚ) L) hαγu).symm
      rw [hlhs, hrhs]
    exact mul_right_cancel₀ hγL_ne key
  have h37q : (37 : 𝓞 (CyclotomicField 37 ℚ)) ∉ q := by
    rw [hq, Ideal.under_def, Ideal.mem_comap,
      map_ofNat (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (𝓞 L)) 37]
    exact h37
  have h37unit :
      IsUnit (algebraMap (𝓞 (CyclotomicField 37 ℚ)) A
        (37 : 𝓞 (CyclotomicField 37 ℚ))) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff A q _).mpr h37q
  have h37A : (37 : A) = algebraMap (𝓞 (CyclotomicField 37 ℚ)) A
      (37 : 𝓞 (CyclotomicField 37 ℚ)) :=
    (map_ofNat (algebraMap (𝓞 (CyclotomicField 37 ℚ)) A) 37).symm
  have hn : ((37 : A) : A ⧸ IsLocalRing.maximalIdeal A) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      not_not, h37A]
    exact h37unit
  have hgen : Algebra.adjoin (CyclotomicField 37 ℚ)
      {antiKummerLiftRoot (p := 37) (CyclotomicField 37 ℚ) α hα *
        (algebraMap (CyclotomicField 37 ℚ) L γ)⁻¹} = ⊤ := by
    have hθgen : Algebra.adjoin (CyclotomicField 37 ℚ)
        {antiKummerLiftRoot (p := 37) (CyclotomicField 37 ℚ) α hα} = ⊤ :=
      antiKummerLiftRoot_adjoin_K_eq_top 37 (CyclotomicField 37 ℚ) α hα
    have hθ_mem : antiKummerLiftRoot (p := 37) (CyclotomicField 37 ℚ) α hα ∈
        Algebra.adjoin (CyclotomicField 37 ℚ)
          {antiKummerLiftRoot (p := 37) (CyclotomicField 37 ℚ) α hα *
            (algebraMap (CyclotomicField 37 ℚ) L γ)⁻¹} := by
      have hθ_eq : antiKummerLiftRoot (p := 37) (CyclotomicField 37 ℚ) α hα =
          (antiKummerLiftRoot (p := 37) (CyclotomicField 37 ℚ) α hα *
            (algebraMap (CyclotomicField 37 ℚ) L γ)⁻¹) *
            algebraMap (CyclotomicField 37 ℚ) L γ := by
        rw [mul_assoc, inv_mul_cancel₀ hγL_ne0, mul_one]
      have hmul : (antiKummerLiftRoot (p := 37) (CyclotomicField 37 ℚ) α hα *
          (algebraMap (CyclotomicField 37 ℚ) L γ)⁻¹) *
          algebraMap (CyclotomicField 37 ℚ) L γ ∈
          Algebra.adjoin (CyclotomicField 37 ℚ)
            {antiKummerLiftRoot (p := 37) (CyclotomicField 37 ℚ) α hα *
              (algebraMap (CyclotomicField 37 ℚ) L γ)⁻¹} :=
        mul_mem (Algebra.self_mem_adjoin_singleton (CyclotomicField 37 ℚ) _)
          (Subalgebra.algebraMap_mem _ γ)
      rwa [← hθ_eq] at hmul
    rw [eq_top_iff, ← hθgen, Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact hθ_mem
  haveI hA_dvr : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (𝓞 (CyclotomicField 37 ℚ)) hq_bot A
  haveI : (IsLocalRing.maximalIdeal A).IsPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  have hmA_bot : IsLocalRing.maximalIdeal A ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  set Pₚ : Ideal Sₚ := P.map (algebraMap (𝓞 L) Sₚ)
  haveI : Pₚ.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver (𝓞 L) q Sₚ P
  haveI hPₚ_lo : Pₚ.LiesOver (IsLocalRing.maximalIdeal A) :=
    IsLocalization.AtPrime.liesOver_map_of_liesOver q A Sₚ P
  have hPₚ_under : Pₚ.under A = IsLocalRing.maximalIdeal A := (Ideal.LiesOver.over).symm
  have hPₚ_bot : Pₚ ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hmA_bot Pₚ
  have hpunder_bot : Pₚ.under A ≠ ⊥ := by rw [hPₚ_under]; exact hmA_bot
  have hn' : ((37 : A) : A ⧸ Pₚ.under A) ≠ 0 := by rw [hPₚ_under]; exact hn
  haveI hunram_local : Algebra.IsUnramifiedAt A Pₚ :=
    isUnramifiedAt_dvr_of_pow_eq_unit (A := A) (L := L) (S := Sₚ) (CyclotomicField 37 ℚ)
      Pₚ hPₚ_bot hpunder_bot hn' u hgen hθ'_pow
  haveI : IsNoetherianRing Sₚ := IsLocalization.isNoetherianRing
    (Algebra.algebraMapSubmonoid (𝓞 L) q.primeCompl) Sₚ inferInstance
  have hePₚ : Ideal.ramificationIdx (IsLocalRing.maximalIdeal A) Pₚ = 1 := by
    have h := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := A) (S := Sₚ) hPₚ_bot
    rwa [hPₚ_under] at h
  have heq : Ideal.ramificationIdx q P = 1 := by
    rw [← IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx q A Sₚ P hq_bot]
    exact hePₚ
  refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := 𝓞 (CyclotomicField 37 ℚ))
    (S := 𝓞 L) hP_bot).mpr ?_
  rw [show P.under (𝓞 (CyclotomicField 37 ℚ)) = q from rfl]
  exact heq

end Assembly

end BernoulliRegular.FLT37.Eichler

end
