import FltRegular.NumberTheory.Unramified

/-!
# Localized Galois descent of ideals (away from the ramified primes)

flt-regular's `comap_map_eq_of_isUnramified` proves `(I ∩ R)·S = I` for a `Gal(L/K)`-stable
ideal `I`, but requires the extension `S/R` to be unramified at **every** finite prime
(`[IsUnramified R S]`). For the CM extension `K = ℚ(ζ₃₇) / K⁺` this is false: `K/K⁺` ramifies at
the prime above `37`.

This file weakens the global unramifiedness to a **per-prime** hypothesis: it is enough that
`S/R` be unramified at the primes in the support of `I ∩ R`. The reviewer-recommended route for
the Case-II II1 real-ideal descent (a `Gal(K/K⁺)`-stable ideal coprime to `𝔭` descends to
`𝒪_{K⁺}`) consumes the specialization.

## References
* flt-regular `FltRegular.NumberTheory.Unramified` (`comap_map_eq_of_isUnramified`,
  `prod_primesOverFinset_of_isUnramified`), which this file localizes.
* Reviewer reply 2026-05-27 (Q5): localized Galois descent for a stable ideal supported away
  from the ramified primes.
-/

@[expose] public section

open UniqueFactorizationMonoid Ideal

attribute [local instance] FractionRing.liftAlgebra

namespace BernoulliRegular.FLT37.LehmerVandiver.CaseII

variable {R K L S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]

/-- **`S/R` is unramified at a single downstairs prime `p`.** Every prime `P` of `S` lying over
`p` has ramification index `1`.

This is the per-prime predicate localizing global unramifiedness (mathlib's
`Algebra.Unramified R S`); it replaces the old flt-regular `IsUnramifiedAt` (top ring, downstairs
prime), whose role mathlib's `Algebra.IsUnramifiedAt` (base ring, *upstairs* prime) does not
directly fill. -/
def IsUnramifiedAt (S : Type*) [CommRing S] {R : Type*} [CommRing R] [Algebra R S]
    (p : Ideal R) : Prop :=
  ∀ P, P ∈ primesOver p S → Ideal.ramificationIdx p P = 1

/-- **Per-prime version of `prod_primesOverFinset_of_isUnramified`.** If `S/R` is unramified at
the single prime `p` (every prime over `p` has ramification index `1`), then the product of the
primes over `p` is `p·S`. Weakens flt-regular's global `[Algebra.Unramified R S]` to
`IsUnramifiedAt`. -/
lemma prod_primesOverFinset_of_isUnramifiedAt [IsDedekindDomain S]
    [Module.IsTorsionFree R S] (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
    (hunram : IsUnramifiedAt S p) :
    ∏ P ∈ IsDedekindDomain.primesOverFinset p S, P = p.map (algebraMap R S) := by
  classical
  have hpbot' : p.map (algebraMap R S) ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective
      (Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)).not.mpr hp
  rw [← associated_iff_eq.mp (factors_pow_count_prod hpbot')]
  apply Finset.prod_congr rfl
  intros P hP
  convert (pow_one _).symm
  have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp ‹_›
  rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hp] at hP
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count hpbot' hP.1
    (ne_bot_of_mem_primesOver hp hP)]
  exact hunram _ hP

/-- **Localized Galois descent of ideals.** If `L/K` is Galois, `I` is an ideal of `S` fixed by
`Gal(L/K)`, and `S/R` is unramified at every prime in the support of `I ∩ R`, then `(I ∩ R)·S = I`.
This is flt-regular's `comap_map_eq_of_isUnramified` with the global `[IsUnramified R S]` weakened
to per-support-prime unramifiedness — exactly what is available for `K/K⁺` (unramified away from the
prime above `p`) when `I` is coprime to that prime. -/
lemma comap_map_eq_of_unramifiedAt_support [IsGalois K L] [IsDedekindDomain S]
    [Module.IsTorsionFree R S] [Module.Finite R S] (I : Ideal S)
    (hI : ∀ σ : L ≃ₐ[K] L, I.comap (galRestrict R K L S σ) = I)
    (hunram : ∀ p ∈ (factors (I.comap (algebraMap R S))).toFinset, IsUnramifiedAt S p) :
    (I.comap (algebraMap R S)).map (algebraMap R S) = I := by
  classical
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have hRS : Function.Injective (algebraMap R S) := by
    refine Function.Injective.of_comp (f := algebraMap S L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hRS
  by_cases hIbot : I = ⊥
  · rw [hIbot, Ideal.comap_bot_of_injective _ hRS, Ideal.map_bot]
  have : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  have hIbot' : I.comap (algebraMap R S) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hIbot
  have : ∀ p, (p.IsPrime ∧ I.comap (algebraMap R S) ≤ p) → ∃ P ≥ I, P ∈ primesOver p S := by
    intro p ⟨hp₁, hp₂⟩
    obtain ⟨P, hP1, hP2, hP3⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ _ hp₂
    exact ⟨P, hP1, hP2, ⟨hP3.symm⟩⟩
  choose 𝔓 h𝔓 h𝔓' using this
  suffices I = ∏ p ∈ (factors (I.comap <| algebraMap R S)).toFinset,
    (p.map (algebraMap R S)) ^ (if h : _ then (factors I).count (𝔓 p h) else 0) by
    simp_rw [← Ideal.mapHom_apply, ← map_pow, ← map_prod, Ideal.mapHom_apply] at this
    rw [this, Ideal.map_comap_map]
  conv_lhs => rw [← associated_iff_eq.mp (factors_pow_count_prod hIbot)]
  rw [← Finset.prod_fiberwise_of_maps_to (g := (Ideal.comap (algebraMap R S) : Ideal S → Ideal R))
    (t := (factors (I.comap (algebraMap R S))).toFinset)]
  · apply Finset.prod_congr rfl
    intros p hp
    have hp_mem := hp
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot'] at hp
    have hpbot : p ≠ ⊥ := fun hp' => hIbot' (eq_bot_iff.mpr (hp.2.trans_eq hp'))
    have hpbot' : p.map (algebraMap R S) ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective hRS).not.mpr
      hpbot
    have := hp.1
    rw [← prod_primesOverFinset_of_isUnramifiedAt p hpbot (hunram p hp_mem), ← Finset.prod_pow]
    have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hpbot this
    apply Finset.prod_congr
    · ext P
      rw [factors_eq_normalizedFactors, Finset.mem_filter, Multiset.mem_toFinset,
        Ideal.mem_normalizedFactors_iff hIbot, ← Finset.mem_coe,
          IsDedekindDomain.coe_primesOverFinset hpbot S]
      refine ⟨fun H => ⟨H.1.1, ⟨H.2.symm⟩⟩, fun H => ⟨⟨H.1, ?_⟩, ?_⟩⟩
      · have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S (h𝔓' _ hp) H
        rw [← hσ, ← hI σ]
        exact Ideal.comap_mono (h𝔓 _ hp)
      · have := H.2.1
        rw [Ideal.under_def] at this
        exact this.symm
    · intro P hP
      rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hpbot S] at hP
      congr
      rw [dif_pos hp, ← Nat.cast_inj (R := ENat), ← normalize_eq P, factors_eq_normalizedFactors,
        ← emultiplicity_eq_count_normalizedFactors
          (prime_of_mem_primesOver hpbot hP).irreducible hIbot,
        ← normalize_eq (𝔓 p hp), ← emultiplicity_eq_count_normalizedFactors
          (prime_of_mem_primesOver hpbot <| h𝔓' p hp).irreducible hIbot,
          emultiplicity_eq_emultiplicity_iff]
      intro n
      have ⟨σ, hσ⟩ := exists_comap_galRestrict_eq R K L S (h𝔓' _ hp) hP
      rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le]
      conv_lhs => rw [← hI σ, ← hσ,
        Ideal.comap_le_iff_le_map _ (AlgEquiv.bijective _), Ideal.map_pow,
        Ideal.map_comap_of_surjective _ (AlgEquiv.surjective _)]
  · intro P hP
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot] at hP
    simp only [factors_eq_normalizedFactors, Multiset.mem_toFinset,
      Ideal.mem_normalizedFactors_iff hIbot']
    exact ⟨hP.1.comap _, Ideal.comap_mono hP.2⟩

end BernoulliRegular.FLT37.LehmerVandiver.CaseII

end
