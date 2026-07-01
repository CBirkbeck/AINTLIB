module

import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.Ideal.GoingUp
public import BernoulliRegular.HMinus.KplusLocalCharacters


/-!
# `K⁺` prime arithmetic above `ℓ ≠ p` (T023b2a2)

Arithmetic half of the local `K⁺` package:

- `primesOverFinsetPlus` and its cardinality / membership lemmas for the finite
  set of primes of `𝓞 K⁺` above `(ℓ)`.
- `primesOverFinsetContractionToPlus`, the contraction map from primes of
  `𝓞 K` over `(ℓ)` to primes of `𝓞 K⁺` over `(ℓ)`.
- The CM-fiber dichotomy showing those fibers have size `1` or `2`, according
  to whether complex conjugation fixes the prime.
- `map_ringOfIntegersComplexConj_eq_self_iff_even_localResidueDegree` and its
  half-degree reformulation, relating the fixed-prime case to
  `localResidueDegreePlus`.
- `primesOver_inertiaDeg_eq_localResidueDegreePlus`, the inertia-degree formula
  for primes of `K⁺` above unramified rational primes `ℓ ≠ p`.

This file is the arithmetic continuation of the old monolithic
`BernoulliRegular.HMinus.KplusLocalResidue`; the even-character local-factor
algebra now lives in `BernoulliRegular.HMinus.KplusLocalCharacters`.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open scoped BigOperators Pointwise

namespace BernoulliRegular

section KplusPrimeArithmetic

variable (p : ℕ) [hp : Fact p.Prime]

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The finite set of prime ideals of `𝓞 K⁺` lying above the rational prime
ideal `(ℓ)`. -/
noncomputable def primesOverFinsetPlus (ℓ : ℕ) : Finset (Ideal (𝓞 (K⁺))) :=
  IsDedekindDomain.primesOverFinset (rationalPrimeIdeal ℓ) (𝓞 (K⁺))

lemma primesOverFinsetPlus_card_eq_ncard (ℓ : ℕ) [Fact ℓ.Prime] :
    (primesOverFinsetPlus (K := K) ℓ).card =
      (Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺))).ncard := by
  classical
  haveI : (rationalPrimeIdeal ℓ).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  unfold primesOverFinsetPlus
  rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hne]

lemma mem_primesOverFinsetPlus_iff {ℓ : ℕ} [Fact ℓ.Prime] {P : Ideal (𝓞 (K⁺))} :
    P ∈ primesOverFinsetPlus (K := K) ℓ ↔
      P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺)) := by
  haveI : (rationalPrimeIdeal ℓ).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  exact IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 (K⁺))

noncomputable def primesOverSubtypeEquivFinsetPlus (ℓ : ℕ) [Fact ℓ.Prime] :
    {P : Ideal (𝓞 (K⁺)) // P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺))} ≃
      {P : Ideal (𝓞 (K⁺)) // P ∈ primesOverFinsetPlus (K := K) ℓ} :=
  Equiv.subtypeEquivProp (funext fun _ ↦ propext
    (mem_primesOverFinsetPlus_iff (K := K) (ℓ := ℓ)).symm)

lemma under_mem_primesOverFinsetPlus {ℓ : ℕ} [Fact ℓ.Prime] {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOverFinset K ℓ) :
    P.under (𝓞 (K⁺)) ∈ primesOverFinsetPlus (K := K) ℓ := by
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) :=
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hP
  letI : P.IsPrime := hP_over.1
  rw [mem_primesOverFinsetPlus_iff]
  refine ⟨Ideal.IsPrime.under (𝓞 (K⁺)) P, ?_⟩
  rw [Ideal.liesOver_iff, Ideal.under_under]
  exact (Ideal.liesOver_iff _ _).1 hP_over.2

/-- The contraction map from primes of `𝓞 K` above `(ℓ)` to primes of
`𝓞 K⁺` above `(ℓ)`. -/
noncomputable def primesOverFinsetContractionToPlus (ℓ : ℕ) [Fact ℓ.Prime] :
    {P : Ideal (𝓞 K) // P ∈ primesOverFinset K ℓ} →
      {PPlus : Ideal (𝓞 (K⁺)) // PPlus ∈ primesOverFinsetPlus (K := K) ℓ}
  | ⟨P, hP⟩ => ⟨P.under (𝓞 (K⁺)), under_mem_primesOverFinsetPlus (K := K) hP⟩

@[simp] lemma primesOverFinsetContractionToPlus_coe {ℓ : ℕ} [Fact ℓ.Prime]
    (P : {P : Ideal (𝓞 K) // P ∈ primesOverFinset K ℓ}) :
    (primesOverFinsetContractionToPlus (K := K) ℓ P : Ideal (𝓞 (K⁺))) =
      P.1.under (𝓞 (K⁺)) := rfl

lemma existsUnique_primesOverFinsetPlus_of_mem_primesOverFinset
    {ℓ : ℕ} [Fact ℓ.Prime] {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOverFinset K ℓ) :
    ∃! PPlus : Ideal (𝓞 (K⁺)),
      PPlus ∈ primesOverFinsetPlus (K := K) ℓ ∧ P.under (𝓞 (K⁺)) = PPlus := by
  refine ⟨P.under (𝓞 (K⁺)), ?_, ?_⟩
  · exact ⟨under_mem_primesOverFinsetPlus (K := K) hP, rfl⟩
  · intro Q hQ
    exact hQ.2.symm

variable [IsCMField K]

lemma algEquiv_eq_one_or_complexConj (σ : K ≃ₐ[K⁺] K) :
    σ = 1 ∨ σ = complexConj K := by
  by_cases hσ : σ = 1
  · exact Or.inl hσ
  · right
    have hcard : Nat.card (K ≃ₐ[K⁺] K) = 2 :=
      (IsGalois.card_aut_eq_finrank K⁺ K).trans (finrank_K_over_Kplus (K := K))
    rw [Nat.card_eq_two_iff' (1 : K ≃ₐ[K⁺] K)] at hcard
    exact ExistsUnique.unique hcard hσ (complexConj_ne_one K)

lemma toRingHom_complexConj_eq_ringOfIntegersComplexConj :
    MulSemiringAction.toRingHom (K ≃ₐ[K⁺] K) (𝓞 K) (complexConj K) =
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  ext x
  change (((complexConj K) • x : 𝓞 K) : K) = ((ringOfIntegersComplexConj K x : 𝓞 K) : K)
  rfl

lemma pointwise_smul_complexConj_eq_map (P : Ideal (𝓞 K)) :
    complexConj K • P = P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  rw [Ideal.pointwise_smul_def, toRingHom_complexConj_eq_ringOfIntegersComplexConj (K := K)]

lemma map_ringOfIntegersComplexConj_mem_primesOverFinset {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom ∈ primesOverFinset K ℓ := by
  let PPlus : Ideal (𝓞 (K⁺)) := P.under (𝓞 (K⁺))
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) :=
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hP
  have hPPlus_mem : PPlus ∈ primesOverFinsetPlus (K := K) ℓ := by
    simpa [PPlus] using under_mem_primesOverFinsetPlus (K := K) hP
  have hPPlus_over : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺)) :=
    (mem_primesOverFinsetPlus_iff (K := K) (ℓ := ℓ)).1 hPPlus_mem
  letI : P.IsPrime := hP_over.1
  letI : PPlus.IsPrime := hPPlus_over.1
  letI : P.LiesOver PPlus := by simp [Ideal.liesOver_iff, PPlus]
  have hmap_liesOver_PPlus :
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver PPlus :=
    Ideal.LiesOver.of_eq_map_equiv PPlus (ringOfIntegersComplexConj K) rfl
  letI : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPPlus_over.2
  have hmap_liesOver :
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver
        (rationalPrimeIdeal ℓ) :=
    Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 (K⁺)) (C := 𝓞 K)
      (𝔓 := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
      (P := PPlus) (p := rationalPrimeIdeal ℓ)
  letI : (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).IsPrime :=
    Ideal.map_isPrime_of_equiv (ringOfIntegersComplexConj K).toRingEquiv
  rw [mem_primesOverFinset_iff (K := K) (ℓ := ℓ)]
  exact ⟨inferInstance, hmap_liesOver⟩

lemma under_map_ringOfIntegersComplexConj_eq_under (P : Ideal (𝓞 K)) :
    (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).under (𝓞 (K⁺)) =
      P.under (𝓞 (K⁺)) := by
  let PPlus : Ideal (𝓞 (K⁺)) := P.under (𝓞 (K⁺))
  letI : P.LiesOver PPlus := by simp [Ideal.liesOver_iff, PPlus]
  have hmap_liesOver_PPlus :
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver PPlus :=
    Ideal.LiesOver.of_eq_map_equiv PPlus (ringOfIntegersComplexConj K) rfl
  simpa [PPlus] using
    (Ideal.over_def
      (P := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
      (A := 𝓞 (K⁺)) (p := PPlus)).symm

lemma eq_or_eq_map_ringOfIntegersComplexConj_of_under_eq {ℓ : ℕ} [Fact ℓ.Prime]
    {P Q : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) (hQ : Q ∈ primesOverFinset K ℓ)
    (hunder : P.under (𝓞 (K⁺)) = Q.under (𝓞 (K⁺))) :
    Q = P ∨ Q = P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  let PPlus : Ideal (𝓞 (K⁺)) := P.under (𝓞 (K⁺))
  have hP_over : P ∈ Ideal.primesOver PPlus (𝓞 K) := by
    refine ⟨((mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hP).1,
      by simp [Ideal.liesOver_iff, PPlus]⟩
  have hQ_over : Q ∈ Ideal.primesOver PPlus (𝓞 K) := by
    refine ⟨((mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hQ).1,
      by simpa [Ideal.liesOver_iff, PPlus] using hunder⟩
  letI : P.IsPrime := hP_over.1
  letI : P.LiesOver PPlus := hP_over.2
  letI : Q.IsPrime := hQ_over.1
  letI : Q.LiesOver PPlus := hQ_over.2
  let _ : MulSemiringAction Gal(K/K⁺) (𝓞 K) := inferInstance
  have _ : IsGaloisGroup Gal(K/K⁺) (𝓞 (K⁺)) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/K⁺)) (𝓞 (K⁺)) (𝓞 K) (K⁺) K
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (A := 𝓞 (K⁺)) (B := 𝓞 K) (p := PPlus) (P := P) (Q := Q) (G := Gal(K/K⁺))
  rcases algEquiv_eq_one_or_complexConj (K := K) σ with rfl | rfl
  · left
    simpa using hσ.symm
  · right
    rw [pointwise_smul_complexConj_eq_map (K := K) P] at hσ
    exact hσ.symm

lemma primesOverFinsetContractionToPlus_fiber_eq_singleton_or_pair {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    let Pconj := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
    let fiber := (primesOverFinset K ℓ).filter
      (fun Q ↦ Q.under (𝓞 (K⁺)) = P.under (𝓞 (K⁺)))
    (Pconj = P ∧ fiber = ({P} : Finset (Ideal (𝓞 K)))) ∨
      (Pconj ≠ P ∧ fiber = {P, Pconj}) := by
  classical
  let Pconj : Ideal (𝓞 K) := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
  let fiber : Finset (Ideal (𝓞 K)) := (primesOverFinset K ℓ).filter
    (fun Q ↦ Q.under (𝓞 (K⁺)) = P.under (𝓞 (K⁺)))
  have hPconj : Pconj ∈ primesOverFinset K ℓ := by
    simpa [Pconj] using map_ringOfIntegersComplexConj_mem_primesOverFinset (K := K) hP
  have hunder_conj : Pconj.under (𝓞 (K⁺)) = P.under (𝓞 (K⁺)) := by
    simpa [Pconj] using under_map_ringOfIntegersComplexConj_eq_under (K := K) P
  have hP_fiber : P ∈ fiber := by
    simp [fiber, hP]
  have hPconj_fiber : Pconj ∈ fiber := by
    simp [fiber, hPconj, hunder_conj]
  have hfiber_subset {Q : Ideal (𝓞 K)} (hQ : Q ∈ fiber) : Q = P ∨ Q = Pconj := by
    have hQ_mem : Q ∈ primesOverFinset K ℓ := (Finset.mem_filter.1 hQ).1
    have hQ_under : Q.under (𝓞 (K⁺)) = P.under (𝓞 (K⁺)) := (Finset.mem_filter.1 hQ).2
    rcases eq_or_eq_map_ringOfIntegersComplexConj_of_under_eq (K := K) hP hQ_mem hQ_under.symm with
      hQP | hQconj
    · exact Or.inl hQP
    · exact Or.inr (by simpa [Pconj] using hQconj)
  by_cases hfix : Pconj = P
  · left
    refine ⟨hfix, Finset.ext fun Q ↦ ?_⟩
    constructor
    · intro hQ
      rcases hfiber_subset hQ with hQP | hQconj
      · rw [hQP]
        simp
      · rw [hQconj, hfix]
        simp
    · intro hQ
      have hQP : Q = P := by simpa using hQ
      subst hQP
      exact hP_fiber
  · right
    refine ⟨hfix, Finset.ext fun Q ↦ ?_⟩
    constructor
    · intro hQ
      rcases hfiber_subset hQ with hQP | hQconj
      · rw [hQP]
        simp
      · rw [hQconj]
        simp [Pconj]
    · intro hQ
      have hQ' : Q = P ∨ Q = Pconj := by
        rwa [Finset.mem_insert, Finset.mem_singleton] at hQ
      rcases hQ' with hQP | hQconj
      · rw [hQP]
        exact hP_fiber
      · rw [hQconj]
        exact hPconj_fiber

lemma primesOverFinsetContractionToPlus_fiber_card_eq_one_or_two {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    let fiber := (primesOverFinset K ℓ).filter
      (fun Q ↦ Q.under (𝓞 (K⁺)) = P.under (𝓞 (K⁺)))
    fiber.card = 1 ∨ fiber.card = 2 := by
  classical
  let Pconj : Ideal (𝓞 K) := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
  let fiber : Finset (Ideal (𝓞 K)) := (primesOverFinset K ℓ).filter
    (fun Q ↦ Q.under (𝓞 (K⁺)) = P.under (𝓞 (K⁺)))
  rcases primesOverFinsetContractionToPlus_fiber_eq_singleton_or_pair (K := K) hP with
    ⟨hfix, hfiber⟩ | ⟨hfix, hfiber⟩
  · left
    have hcard : ({P} : Finset (Ideal (𝓞 K))).card = 1 := by simp
    rw [hfiber, hcard]
  · right
    have hcard : ({P, Pconj} : Finset (Ideal (𝓞 K))).card = 2 := by
      rw [Finset.card_eq_two]
      exact ⟨P, Pconj, hfix.symm, rfl⟩
    rw [hfiber, hcard]

noncomputable def complexConjRat (hp_odd : p ≠ 2) : Gal(K/ℚ) := by
  letI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  exact
    { (complexConj K).toRingEquiv with
      commutes' := fun q ↦ by
        exact map_ratCast ((complexConj K).toRingEquiv.toRingHom) q }

@[simp] private lemma complexConjRat_apply (hp_odd : p ≠ 2) (x : K) :
    complexConjRat (p := p) (K := K) hp_odd x = complexConj K x := by
  rfl

lemma toRingHom_complexConjRat_eq_ringOfIntegersComplexConj (hp_odd : p ≠ 2) :
    MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K)
        (complexConjRat (p := p) (K := K) hp_odd) =
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  haveI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  ext x
  change complexConjRat (p := p) (K := K) hp_odd x =
      ((ringOfIntegersComplexConj K x : 𝓞 K) : K)
  simp [complexConjRat_apply, coe_ringOfIntegersComplexConj]

lemma pointwise_smul_complexConjRat_eq_map (hp_odd : p ≠ 2) (P : Ideal (𝓞 K)) :
    (complexConjRat (p := p) (K := K) hp_odd • P) =
      P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  haveI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  rw [Ideal.pointwise_smul_def, toRingHom_complexConjRat_eq_ringOfIntegersComplexConj
    (p := p) (K := K) hp_odd]

omit [IsCMField K] in
lemma galEquivZMod_complexConj_eq_neg_one (hp_odd : p ≠ 2) :
    IsCyclotomicExtension.Rat.galEquivZMod p K
        (complexConjRat (p := p) (K := K) hp_odd) = -1 := by
  haveI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  let c : Gal(K/ℚ) := complexConjRat (p := p) (K := K) hp_odd
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have hc :
      c (IsCyclotomicExtension.zeta p ℚ K) =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := by
    have hc' := congrArg (fun x : 𝓞 K ↦ (x : K)) (complexConj_apply_zeta (p := p) (K := K))
    simpa [c, complexConjRat_apply, coe_ringOfIntegersComplexConj] using hc'
  have hpow :
      (IsCyclotomicExtension.zeta p ℚ K) ^ (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := by
    calc
      (IsCyclotomicExtension.zeta p ℚ K) ^ (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val
          = c (IsCyclotomicExtension.zeta p ℚ K) := by
              symm
              exact IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
                (n := p) (K := K) c hζ.pow_eq_one
      _ = (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := hc
  apply Units.ext
  have hpow' := hpow
  rw [(hζ.isOfFinOrder (NeZero.ne p)).pow_inj_mod, ← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_val, Nat.cast_sub hp.out.one_le,
    ZMod.natCast_self, zero_sub, Nat.cast_one] at hpow'
  simpa [c] using hpow'

lemma unitOfPrimeNe_pow_localResidueDegreePlus_eq_neg_one_of_even
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (hd_even : Even (localResidueDegree (p := p) ℓ hℓp)) :
    unitOfPrimeNe (p := p) ℓ hℓp ^ localResidueDegreePlus (p := p) ℓ hℓp =
      (-1 : (ZMod p)ˣ) := by
  let u : (ZMod p)ˣ := unitOfPrimeNe (p := p) ℓ hℓp
  let d : ℕ := localResidueDegree (p := p) ℓ hℓp
  rcases unitOfPrimeNe_pow_localResidueDegreePlus_eq_one_or_neg_one (p := p) hℓp with hpow | hpow
  · have hpow_units : u ^ localResidueDegreePlus (p := p) ℓ hℓp = 1 := by
      apply Units.ext
      simpa [u, Units.val_pow_eq_pow_val] using hpow
    have hdvd : d ∣ localResidueDegreePlus (p := p) ℓ hℓp := by
      simpa [d, localResidueDegree, u] using (orderOf_dvd_iff_pow_eq_one (x := u)).2 hpow_units
    have hd_pos : 0 < d := by
      dsimp [d, localResidueDegree, u]
      exact orderOf_pos u
    have hhalf : localResidueDegreePlus (p := p) ℓ hℓp = d / 2 := by
      simpa [d] using localResidueDegreePlus_eq_half (p := p) hℓp hd_even
    have hhalf_pos : 0 < d / 2 := by
      rcases hd_even with ⟨k, hk⟩
      rw [show d = 2 * k by omega]
      omega
    have hle : d ≤ d / 2 := by
      rw [hhalf] at hdvd
      exact Nat.le_of_dvd hhalf_pos hdvd
    omega
  · apply Units.ext
    simpa [u, Units.val_pow_eq_pow_val] using hpow

lemma neg_one_mem_zpowers_unitOfPrimeNe_iff_even_localResidueDegree
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (-1 : (ZMod p)ˣ) ∈ Subgroup.zpowers (unitOfPrimeNe (p := p) ℓ hℓp) ↔
      Even (localResidueDegree (p := p) ℓ hℓp) := by
  let u : (ZMod p)ˣ := unitOfPrimeNe (p := p) ℓ hℓp
  constructor
  · intro hneg
    have htwo : 2 ∣ orderOf u := by
      have horder_neg : orderOf (-1 : (ZMod p)ˣ) = 2 := by
        rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod p) p,
          if_neg hp_odd]
      exact horder_neg ▸ orderOf_dvd_of_mem_zpowers hneg
    simpa [u, localResidueDegree, even_iff_two_dvd] using htwo
  · intro hd_even
    refine Subgroup.mem_zpowers_iff.mpr ⟨localResidueDegreePlus (p := p) ℓ hℓp, ?_⟩
    rw [zpow_natCast]
    exact unitOfPrimeNe_pow_localResidueDegreePlus_eq_neg_one_of_even (p := p) hℓp hd_even

omit [IsCMField K] in
lemma complexConjRat_mem_stabilizer_iff_even_localResidueDegree
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    (complexConjRat (p := p) (K := K) hp_odd ∈ MulAction.stabilizer Gal(K/ℚ) P) ↔
      Even (localResidueDegree (p := p) ℓ hℓp) := by
  let c : Gal(K/ℚ) := complexConjRat (p := p) (K := K) hp_odd
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) :=
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hP
  letI : P.IsPrime := hP_over.1
  letI : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hP_over.2
  haveI : (rationalPrimeIdeal ℓ).IsMaximal := by
    simpa [rationalPrimeIdeal] using Int.ideal_span_isMaximal_of_prime ℓ
  letI : P.IsMaximal := Ideal.isMaximal_of_mem_primesOver hP_over
  constructor
  · intro hc
    have hmem_map : IsCyclotomicExtension.Rat.galEquivZMod p K c ∈
        (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P) := ⟨c, hc, rfl⟩
    rw [IsCyclotomicExtension.Rat.galEquivZMod_stabilizer (n := p) (K := K) (p := ℓ) (P := P)
      ((coprime_of_prime_ne (p := p) hℓp).symm), galEquivZMod_complexConj_eq_neg_one
      (p := p) (K := K) hp_odd] at hmem_map
    simpa [unitOfPrimeNe] using
      (neg_one_mem_zpowers_unitOfPrimeNe_iff_even_localResidueDegree (p := p) hp_odd hℓp).1 hmem_map
  · intro h_even
    have hneg_mem : (-1 : (ZMod p)ˣ) ∈ Subgroup.zpowers (unitOfPrimeNe (p := p) ℓ hℓp) :=
      (neg_one_mem_zpowers_unitOfPrimeNe_iff_even_localResidueDegree (p := p) hp_odd hℓp).2 h_even
    have hmem_map : IsCyclotomicExtension.Rat.galEquivZMod p K c ∈
        (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P) := by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_stabilizer (n := p) (K := K) (p := ℓ) (P := P)
        ((coprime_of_prime_ne (p := p) hℓp).symm), galEquivZMod_complexConj_eq_neg_one
        (p := p) (K := K) hp_odd]
      simpa [unitOfPrimeNe] using hneg_mem
    rcases hmem_map with ⟨σ, hσ, hσeq⟩
    have hc_eq : σ = c := (IsCyclotomicExtension.Rat.galEquivZMod p K).injective hσeq
    subst hc_eq
    exact hσ

lemma map_ringOfIntegersComplexConj_eq_self_iff_even_localResidueDegree
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = P ↔
      Even (localResidueDegree (p := p) ℓ hℓp) := by
  haveI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  let c : Gal(K/ℚ) := complexConjRat (p := p) (K := K) hp_odd
  constructor
  · intro hmap
    have hsmul : c • P = P := by
      rw [pointwise_smul_complexConjRat_eq_map (p := p) (K := K) hp_odd]
      exact hmap
    have hc : c ∈ MulAction.stabilizer Gal(K/ℚ) P := by simpa [c] using hsmul
    exact (complexConjRat_mem_stabilizer_iff_even_localResidueDegree
      (p := p) (K := K) hp_odd hℓp hP).1 hc
  · intro h_even
    have hc : c ∈ MulAction.stabilizer Gal(K/ℚ) P :=
      (complexConjRat_mem_stabilizer_iff_even_localResidueDegree
        (p := p) (K := K) hp_odd hℓp hP).2 h_even
    have hsmul : c • P = P := by simpa [c] using hc
    rw [pointwise_smul_complexConjRat_eq_map (p := p) (K := K) hp_odd] at hsmul
    exact hsmul

lemma map_ringOfIntegersComplexConj_eq_self_iff_localResidueDegreePlus_eq_half
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = P ↔
      localResidueDegreePlus (p := p) ℓ hℓp = localResidueDegree (p := p) ℓ hℓp / 2 := by
  rw [map_ringOfIntegersComplexConj_eq_self_iff_even_localResidueDegree
    (p := p) (K := K) hp_odd hℓp hP]
  constructor
  · exact localResidueDegreePlus_eq_half (p := p) hℓp
  · intro hhalf
    by_contra hodd
    have hself := localResidueDegreePlus_eq_self (p := p) hℓp hodd
    have hpos : 0 < localResidueDegree (p := p) ℓ hℓp := by
      unfold localResidueDegree unitOfPrimeNe
      exact orderOf_pos _
    rw [hself] at hhalf
    omega

omit [IsCMField K] in
lemma primesOverFinsetContractionToPlus_fiber_card_eq_ncard_primesOver {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ)
    {PPlus : Ideal (𝓞 (K⁺))} (hPPlus : P.under (𝓞 (K⁺)) = PPlus) :
    let fiber := (primesOverFinset K ℓ).filter
      (fun Q ↦ Q.under (𝓞 (K⁺)) = PPlus)
    fiber.card = (Ideal.primesOver PPlus (𝓞 K)).ncard := by
  classical
  let fiber : Finset (Ideal (𝓞 K)) := (primesOverFinset K ℓ).filter
    (fun Q ↦ Q.under (𝓞 (K⁺)) = PPlus)
  have hPPlus_mem : PPlus ∈ primesOverFinsetPlus (K := K) ℓ := by
    simpa [hPPlus] using under_mem_primesOverFinsetPlus (K := K) hP
  have hPPlus_over : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺)) :=
    (mem_primesOverFinsetPlus_iff (K := K) (ℓ := ℓ)).1 hPPlus_mem
  letI : PPlus.IsPrime := hPPlus_over.1
  letI : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPPlus_over.2
  have hfiber : (↑fiber : Set (Ideal (𝓞 K))) = Ideal.primesOver PPlus (𝓞 K) := by
    ext Q
    constructor
    · intro hQ
      rw [Finset.mem_coe, Finset.mem_filter] at hQ
      rcases hQ with ⟨hQ_fin, hQ_under⟩
      have hQ_over : Q ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) :=
        (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hQ_fin
      letI : Q.IsPrime := hQ_over.1
      exact ⟨inferInstance, (Ideal.liesOver_iff _ _).2 hQ_under.symm⟩
    · intro hQ
      letI : Q.IsPrime := hQ.1
      letI : Q.LiesOver PPlus := hQ.2
      have hQ_over : Q.LiesOver (rationalPrimeIdeal ℓ) :=
        Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 (K⁺)) (C := 𝓞 K)
          (𝔓 := Q) (P := PPlus) (p := rationalPrimeIdeal ℓ)
      have hQ_fin : Q ∈ primesOverFinset K ℓ := by
        rw [mem_primesOverFinset_iff (K := K) (ℓ := ℓ)]
        exact ⟨inferInstance, hQ_over⟩
      have hQ_under : Q.under (𝓞 (K⁺)) = PPlus :=
        ((Ideal.liesOver_iff _ _).1 (show Q.LiesOver PPlus from inferInstance)).symm
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨hQ_fin, hQ_under⟩
  simpa [fiber] using (show fiber.card = (Ideal.primesOver PPlus (𝓞 K)).ncard from by
    rw [← Set.ncard_coe_finset, hfiber])

omit [IsCMField K] in
lemma primesOver_inertiaDeg_eq_localResidueDegreePlus
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (PPlus : Ideal (𝓞 (K⁺)))
    (hPPlus : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺))) :
    (rationalPrimeIdeal ℓ).inertiaDeg PPlus = localResidueDegreePlus (p := p) ℓ hℓp := by
  classical
  haveI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  haveI : (rationalPrimeIdeal ℓ).IsMaximal := by
    simpa [rationalPrimeIdeal] using Int.ideal_span_isMaximal_of_prime ℓ
  letI : PPlus.IsPrime := hPPlus.1
  letI : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPPlus.2
  letI : PPlus.IsMaximal := Ideal.isMaximal_of_mem_primesOver hPPlus
  obtain ⟨⟨P, hP_prime, hP_over_PPlus⟩⟩ := PPlus.nonempty_primesOver (S := 𝓞 K)
  letI : P.IsPrime := hP_prime
  letI : P.LiesOver PPlus := hP_over_PPlus
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) := by
    refine ⟨hP_prime, ?_⟩
    exact Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 (K⁺)) (C := 𝓞 K)
      (𝔓 := P) (P := PPlus) (p := rationalPrimeIdeal ℓ)
  have hP_fin : P ∈ primesOverFinset K ℓ :=
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).2 hP_over
  letI : P.IsMaximal := Ideal.isMaximal_of_mem_primesOver hP_over
  have hPPlus_eq : P.under (𝓞 (K⁺)) = PPlus :=
    ((Ideal.liesOver_iff _ _).1 (show P.LiesOver PPlus from inferInstance)).symm
  let fiber : Finset (Ideal (𝓞 K)) := (primesOverFinset K ℓ).filter
    (fun Q ↦ Q.under (𝓞 (K⁺)) = PPlus)
  have hfiber_ncard : fiber.card = (Ideal.primesOver PPlus (𝓞 K)).ncard := by
    simpa [fiber] using primesOverFinsetContractionToPlus_fiber_card_eq_ncard_primesOver
      (K := K) hP_fin hPPlus_eq
  have hram_tower :
      (rationalPrimeIdeal ℓ).ramificationIdx P =
        (rationalPrimeIdeal ℓ).ramificationIdx PPlus * PPlus.ramificationIdx P := by
    simpa using Ideal.ramificationIdx_algebra_tower'
      (p := rationalPrimeIdeal ℓ) (P := PPlus) (Q := P)
  have hram_rel : PPlus.ramificationIdx P = 1 := by
    apply Nat.eq_one_of_dvd_one
    refine ⟨(rationalPrimeIdeal ℓ).ramificationIdx PPlus, ?_⟩
    rw [mul_comm, ← hram_tower,
      primesOver_ramificationIdx_eq_one (p := p) (K := K) hℓp P hP_over]
  have hPPlus_ne_bot : PPlus ≠ ⊥ := by
    intro hbot
    have hlie : PPlus.LiesOver (rationalPrimeIdeal ℓ) := inferInstance
    have hover := (Ideal.liesOver_iff _ _).1 hlie
    have hcomap_bot : Ideal.comap (algebraMap ℤ (𝓞 (K⁺))) (⊥ : Ideal (𝓞 (K⁺))) = ⊥ := by
      ext x
      simp
    have hneq : rationalPrimeIdeal ℓ ≠ ⊥ := by
      rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    exact hneq (by simpa [Ideal.under_def, hbot, hcomap_bot] using hover)
  have _ : IsGaloisGroup Gal(K/K⁺) (𝓞 (K⁺)) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/K⁺)) (𝓞 (K⁺)) (𝓞 K) (K⁺) K
  have hquad : (Ideal.primesOver PPlus (𝓞 K)).ncard * PPlus.inertiaDeg P = 2 := by
    have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := PPlus)
      (B := 𝓞 K) (G := Gal(K/K⁺))
    have hcard_gal : Nat.card Gal(K/K⁺) = 2 :=
      (IsGalois.card_aut_eq_finrank K⁺ K).trans (finrank_K_over_Kplus (K := K))
    have hram_in : PPlus.ramificationIdxIn (𝓞 K) = 1 := by
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx (p := PPlus) (P := P) (G := Gal(K/K⁺))]
      rw [← Ideal.ramificationIdx_eq_ramificationIdx' (q := P) (p := PPlus) (hp := hPPlus_ne_bot)]
      exact hram_rel
    have hinertia_in : PPlus.inertiaDegIn (𝓞 K) = PPlus.inertiaDeg P := by
      rw [Ideal.inertiaDegIn_eq_inertiaDeg (p := PPlus) (P := P) (G := Gal(K/K⁺))]
      rw [← Ideal.inertiaDeg_eq_inertiaDeg' (p := PPlus) (q := P)]
    rw [hcard_gal, hram_in, hinertia_in, one_mul] at hfund
    exact hfund
  have hinertia_tower :
      (rationalPrimeIdeal ℓ).inertiaDeg P =
        (rationalPrimeIdeal ℓ).inertiaDeg PPlus * PPlus.inertiaDeg P := by
    simpa using Ideal.inertiaDeg_algebra_tower
      (p := rationalPrimeIdeal ℓ) (P := PPlus) (I := P)
  have hP_inertia :
      (rationalPrimeIdeal ℓ).inertiaDeg P = localResidueDegree (p := p) ℓ hℓp :=
    primesOver_inertiaDeg_eq_localResidueDegree (p := p) (K := K) hℓp P hP_over
  by_cases hfix : P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = P
  · have hfiber_card : fiber.card = 1 := by
      rcases primesOverFinsetContractionToPlus_fiber_eq_singleton_or_pair (K := K) hP_fin with
        hsingle | hpair
      · have hsingle_fiber : fiber = ({P} : Finset (Ideal (𝓞 K))) := by
          simpa [fiber, hPPlus_eq] using hsingle.2
        rw [hsingle_fiber]
        simp
      · exact (hpair.1 hfix).elim
    have hcard_primes : (Ideal.primesOver PPlus (𝓞 K)).ncard = 1 := by
      rw [← hfiber_ncard]
      exact hfiber_card
    have hrel_inertia : PPlus.inertiaDeg P = 2 := by
      rw [hcard_primes] at hquad
      simpa using hquad
    have hhalf : localResidueDegreePlus (p := p) ℓ hℓp =
        localResidueDegree (p := p) ℓ hℓp / 2 :=
      (map_ringOfIntegersComplexConj_eq_self_iff_localResidueDegreePlus_eq_half
        (p := p) (K := K) hp_odd hℓp hP_fin).1 hfix
    rw [hhalf]
    rw [hP_inertia, hrel_inertia] at hinertia_tower
    omega
  · have hfiber_card : fiber.card = 2 := by
      rcases primesOverFinsetContractionToPlus_fiber_eq_singleton_or_pair (K := K) hP_fin with
        hsingle | hpair
      · exact (hfix hsingle.1).elim
      · have hpair_fiber :
            fiber =
              ({P, P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom} :
                Finset (Ideal (𝓞 K))) := by
          simpa [fiber, hPPlus_eq] using hpair.2
        rw [hpair_fiber]
        rw [Finset.card_eq_two]
        exact ⟨P, P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
          by simpa [eq_comm] using hpair.1, rfl⟩
    have hcard_primes : (Ideal.primesOver PPlus (𝓞 K)).ncard = 2 := by
      rw [← hfiber_ncard]
      exact hfiber_card
    have hrel_inertia : PPlus.inertiaDeg P = 1 := by
      rw [hcard_primes] at hquad
      omega
    have hnot_even : ¬ Even (localResidueDegree (p := p) ℓ hℓp) := fun h_even ↦
      hfix
        ((map_ringOfIntegersComplexConj_eq_self_iff_even_localResidueDegree
          (p := p) (K := K) hp_odd hℓp hP_fin).2 h_even)
    have hself : localResidueDegreePlus (p := p) ℓ hℓp =
        localResidueDegree (p := p) ℓ hℓp :=
      localResidueDegreePlus_eq_self (p := p) hℓp hnot_even
    rw [hself]
    rw [hP_inertia, hrel_inertia] at hinertia_tower
    omega

omit [IsCMField K] in
lemma primesOverPlus_ramificationIdx_eq_one {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (PPlus : Ideal (𝓞 (K⁺)))
    (hPPlus : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺))) :
    (rationalPrimeIdeal ℓ).ramificationIdx PPlus = 1 := by
  haveI : (rationalPrimeIdeal ℓ).IsMaximal := by
    simpa [rationalPrimeIdeal] using Int.ideal_span_isMaximal_of_prime ℓ
  letI : PPlus.IsPrime := hPPlus.1
  letI : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPPlus.2
  letI : PPlus.IsMaximal := Ideal.isMaximal_of_mem_primesOver hPPlus
  obtain ⟨⟨P, hP_prime, hP_over_PPlus⟩⟩ := PPlus.nonempty_primesOver (S := 𝓞 K)
  letI : P.IsPrime := hP_prime
  letI : P.LiesOver PPlus := hP_over_PPlus
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) := by
    refine ⟨hP_prime, ?_⟩
    exact Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 (K⁺)) (C := 𝓞 K)
      (𝔓 := P) (P := PPlus) (p := rationalPrimeIdeal ℓ)
  have hram_tower :
      (rationalPrimeIdeal ℓ).ramificationIdx P =
        (rationalPrimeIdeal ℓ).ramificationIdx PPlus * PPlus.ramificationIdx P := by
    simpa using Ideal.ramificationIdx_algebra_tower'
      (p := rationalPrimeIdeal ℓ) (P := PPlus) (Q := P)
  have hram_abs : (rationalPrimeIdeal ℓ).ramificationIdx P = 1 :=
    BernoulliRegular.primesOver_ramificationIdx_eq_one (p := p) (K := K) hℓp P hP_over
  apply Nat.eq_one_of_dvd_one
  refine ⟨PPlus.ramificationIdx P, ?_⟩
  rw [← hram_tower, hram_abs]

lemma ncard_primesOverPlus_eq_localPrimeCountPlus (hp_odd : p ≠ 2)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺))).ncard =
      localPrimeCountPlus (p := p) ℓ hℓp := by
  haveI : (rationalPrimeIdeal ℓ).IsMaximal := by
    simpa [rationalPrimeIdeal] using Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hsum :
      ∑ PPlus ∈ primesOverFinsetPlus (K := K) ℓ,
          (rationalPrimeIdeal ℓ).ramificationIdx PPlus *
            (rationalPrimeIdeal ℓ).inertiaDeg PPlus = Module.finrank ℚ (K⁺) := by
    simpa [primesOverFinsetPlus] using
      (Ideal.sum_ramification_inertia (S := 𝓞 (K⁺)) (K := ℚ) (L := K⁺)
        (p := rationalPrimeIdeal ℓ) hne)
  have hsum_const :
      (primesOverFinsetPlus (K := K) ℓ).card * localResidueDegreePlus (p := p) ℓ hℓp =
        Module.finrank ℚ (K⁺) := by
    calc
      (primesOverFinsetPlus (K := K) ℓ).card * localResidueDegreePlus (p := p) ℓ hℓp
          = ∑ PPlus ∈ primesOverFinsetPlus (K := K) ℓ,
              localResidueDegreePlus (p := p) ℓ hℓp := by
              simp
      _ = ∑ PPlus ∈ primesOverFinsetPlus (K := K) ℓ,
              (rationalPrimeIdeal ℓ).ramificationIdx PPlus *
                (rationalPrimeIdeal ℓ).inertiaDeg PPlus := by
              refine Finset.sum_congr rfl ?_
              intro PPlus hPPlus_fin
              have hPPlus : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺)) :=
                (mem_primesOverFinsetPlus_iff (K := K) (ℓ := ℓ)).1 hPPlus_fin
              simp [primesOverPlus_ramificationIdx_eq_one (p := p) (K := K) hℓp PPlus hPPlus,
                primesOver_inertiaDeg_eq_localResidueDegreePlus (p := p) (K := K)
                  hp_odd hℓp PPlus hPPlus]
      _ = Module.finrank ℚ (K⁺) := hsum
  rw [primesOverFinsetPlus_card_eq_ncard (K := K) (ℓ := ℓ),
    finrank_Kplus_over_rat (p := p) (K := K)] at hsum_const
  have hlocal := localPrimeCountPlus_mul_localResidueDegreePlus (p := p) hp_odd hℓp
  rw [card_even_characters_kplus (p := p) hp_odd] at hlocal
  have hd_pos : 0 < localResidueDegree (p := p) ℓ hℓp := by
    dsimp [localResidueDegree]
    exact orderOf_pos (unitOfPrimeNe (p := p) ℓ hℓp)
  have hfd_pos : 0 < localResidueDegreePlus (p := p) ℓ hℓp := by
    by_cases hde : Even (localResidueDegree (p := p) ℓ hℓp)
    · rcases hde with ⟨k, hk⟩
      rw [localResidueDegreePlus_eq_half (p := p) hℓp ⟨k, hk⟩]
      omega
    · rw [localResidueDegreePlus_eq_self (p := p) hℓp hde]
      exact hd_pos
  have hmul :
      (Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺))).ncard *
        localResidueDegreePlus (p := p) ℓ hℓp =
          localPrimeCountPlus (p := p) ℓ hℓp * localResidueDegreePlus (p := p) ℓ hℓp := by
    omega
  exact Nat.eq_of_mul_eq_mul_right hfd_pos (by simpa [Nat.mul_comm] using hmul)

lemma primesOverPlus_prime_ne_p_package (hp_odd : p ≠ 2)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (∀ PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺)),
      (rationalPrimeIdeal ℓ).inertiaDeg PPlus = localResidueDegreePlus (p := p) ℓ hℓp) ∧
    (∀ PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺)),
      (rationalPrimeIdeal ℓ).ramificationIdx PPlus = 1) ∧
    (Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺))).ncard =
      localPrimeCountPlus (p := p) ℓ hℓp :=
  ⟨primesOver_inertiaDeg_eq_localResidueDegreePlus (p := p) (K := K) hp_odd hℓp,
   primesOverPlus_ramificationIdx_eq_one (p := p) (K := K) hℓp,
   ncard_primesOverPlus_eq_localPrimeCountPlus (p := p) (K := K) hp_odd hℓp⟩

lemma dedekindLocalFactor_eq_pow_localResidueDegreePlus (hp_odd : p ≠ 2)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) {s : ℂ} :
    dedekindLocalFactor K⁺ ℓ s =
      (1 - (ℓ : ℂ) ^ (-(localResidueDegreePlus (p := p) ℓ hℓp : ℂ) * s)) ^
        localPrimeCountPlus (p := p) ℓ hℓp := by
  classical
  have hcard_eq : (primesOverFinsetPlus (K := K) ℓ).card = localPrimeCountPlus (p := p) ℓ hℓp := by
    rw [primesOverFinsetPlus_card_eq_ncard (K := K) (ℓ := ℓ)]
    exact ncard_primesOverPlus_eq_localPrimeCountPlus (p := p) (K := K) hp_odd hℓp
  unfold dedekindLocalFactor
  change Finset.prod (primesOverFinsetPlus (K := K) ℓ) (fun PPlus ↦
      (1 - (Ideal.absNorm PPlus : ℂ) ^ (-s))) =
        (1 - (ℓ : ℂ) ^ (-(localResidueDegreePlus (p := p) ℓ hℓp : ℂ) * s)) ^
          localPrimeCountPlus (p := p) ℓ hℓp
  have hprod_eq : ∀ PPlus ∈ primesOverFinsetPlus (K := K) ℓ,
      (1 - (Ideal.absNorm PPlus : ℂ) ^ (-s)) =
        1 - (ℓ : ℂ) ^ (-(localResidueDegreePlus (p := p) ℓ hℓp : ℂ) * s) := by
    intro PPlus hP
    have hPmem : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 (K⁺)) :=
      (mem_primesOverFinsetPlus_iff (K := K) (ℓ := ℓ)).1 hP
    haveI : PPlus.IsPrime := hPmem.1
    haveI : PPlus.LiesOver (Ideal.span {(ℓ : ℤ)}) := hPmem.2
    have habsNorm : Ideal.absNorm PPlus = ℓ ^ (localResidueDegreePlus (p := p) ℓ hℓp) := by
      rw [← primesOver_inertiaDeg_eq_localResidueDegreePlus (p := p) (K := K)
        hp_odd hℓp PPlus hPmem]
      exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus (Fact.out : ℓ.Prime)
    rw [habsNorm]
    push_cast
    have := Complex.natCast_cpow_natCast_mul ℓ (localResidueDegreePlus (p := p) ℓ hℓp) (-s)
    rw [show -((localResidueDegreePlus (p := p) ℓ hℓp : ℂ)) * s =
        ((localResidueDegreePlus (p := p) ℓ hℓp : ℕ) : ℂ) * (-s) by ring,
      this]
  rw [Finset.prod_congr rfl hprod_eq, Finset.prod_const, hcard_eq]

omit [IsCMField K] in
lemma zetaPrime_mem_primesOver_at_p :
    zetaPrime p K ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K) := by
  refine ⟨zetaPrime_isPrime p K, ?_⟩
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  simpa [zetaPrime, rationalPrimeIdeal] using
    (IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one (p := p) (k := 0)
      (K := K) (hζ := IsCyclotomicExtension.zeta_spec (p ^ (0 + 1)) ℚ K))

omit [IsCMField K] in
lemma primesOver_at_p_eq_singleton_zetaPrime :
    Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K) = {zetaPrime p K} := by
  classical
  obtain ⟨P, hP⟩ :=
    Set.ncard_eq_one.mp (ncard_primesOver_at_p_eq_one (p := p) (K := K))
  have hzeta : zetaPrime p K = P := by
    have hzeta_mem := zetaPrime_mem_primesOver_at_p (p := p) (K := K)
    rw [hP] at hzeta_mem
    simpa using hzeta_mem
  simpa [hzeta] using hP

lemma zetaPrimePlus_mem_primesOver_at_p :
    zetaPrimePlus p K ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (K⁺)) := by
  refine ⟨inferInstance, ?_⟩
  haveI : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hzeta_over : (zetaPrime p K).LiesOver (rationalPrimeIdeal p) := by
    simpa [zetaPrime, rationalPrimeIdeal] using
      (IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one (p := p) (k := 0)
        (K := K) (hζ := IsCyclotomicExtension.zeta_spec (p ^ (0 + 1)) ℚ K))
  letI : (zetaPrime p K).LiesOver (rationalPrimeIdeal p) := hzeta_over
  rw [Ideal.liesOver_iff, zetaPrimePlus, Ideal.under_under]
  exact Ideal.over_def (P := zetaPrime p K) (A := ℤ) (p := rationalPrimeIdeal p)

lemma primesOverPlus_at_p_eq_singleton_zetaPrimePlus :
    Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (K⁺)) = {zetaPrimePlus p K} := by
  classical
  ext PPlus
  constructor
  · intro hPPlus
    haveI : (rationalPrimeIdeal p).IsMaximal := by
      simpa [rationalPrimeIdeal] using Int.ideal_span_isMaximal_of_prime p
    letI : PPlus.IsPrime := hPPlus.1
    letI : PPlus.LiesOver (rationalPrimeIdeal p) := hPPlus.2
    letI : PPlus.IsMaximal := Ideal.isMaximal_of_mem_primesOver hPPlus
    obtain ⟨⟨P, hP_prime, hP_over_PPlus⟩⟩ := PPlus.nonempty_primesOver (S := 𝓞 K)
    letI : P.IsPrime := hP_prime
    letI : P.LiesOver PPlus := hP_over_PPlus
    have hP : P ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K) := by
      refine ⟨hP_prime, ?_⟩
      exact Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 (K⁺)) (C := 𝓞 K)
        (𝔓 := P) (P := PPlus) (p := rationalPrimeIdeal p)
    have hP_eq : P = zetaPrime p K := by
      rw [primesOver_at_p_eq_singleton_zetaPrime (p := p) (K := K)] at hP
      simpa using hP
    have hPPlus_eq : PPlus = zetaPrimePlus p K := by
      simpa [zetaPrimePlus, hP_eq] using
        (Ideal.liesOver_iff _ _).1 (show P.LiesOver PPlus from inferInstance)
    simp [hPPlus_eq]
  · intro hPPlus
    rw [Set.mem_singleton_iff] at hPPlus
    simpa [hPPlus] using zetaPrimePlus_mem_primesOver_at_p (p := p) (K := K)

lemma ncard_primesOverPlus_at_p_eq_one :
    (Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (K⁺))).ncard = 1 := by
  rw [primesOverPlus_at_p_eq_singleton_zetaPrimePlus (p := p) (K := K)]
  simp

lemma zetaPrimePlus_inertiaDeg_eq_one_at_p :
    (rationalPrimeIdeal p).inertiaDeg (zetaPrimePlus p K) = 1 := by
  haveI : (rationalPrimeIdeal p).IsMaximal := by
    simpa [rationalPrimeIdeal] using Int.ideal_span_isMaximal_of_prime p
  haveI : (zetaPrimePlus p K).LiesOver (rationalPrimeIdeal p) :=
    (zetaPrimePlus_mem_primesOver_at_p (p := p) (K := K)).2
  haveI : (zetaPrimePlus p K).IsMaximal :=
    Ideal.isMaximal_of_mem_primesOver
      (zetaPrimePlus_mem_primesOver_at_p (p := p) (K := K))
  have hinertia_tower :
      (rationalPrimeIdeal p).inertiaDeg (zetaPrime p K) =
        (rationalPrimeIdeal p).inertiaDeg (zetaPrimePlus p K) *
          (zetaPrimePlus p K).inertiaDeg (zetaPrime p K) := by
    simpa using Ideal.inertiaDeg_algebra_tower
      (p := rationalPrimeIdeal p) (P := zetaPrimePlus p K) (I := zetaPrime p K)
  have hzeta_inertia :
      (rationalPrimeIdeal p).inertiaDeg (zetaPrime p K) = 1 :=
    primesOver_inertiaDeg_eq_one_at_p (p := p) (K := K) (zetaPrime p K)
      (zetaPrime_mem_primesOver_at_p (p := p) (K := K))
  rw [hzeta_inertia] at hinertia_tower
  exact Nat.eq_one_of_dvd_one <| ⟨(zetaPrimePlus p K).inertiaDeg (zetaPrime p K), hinertia_tower⟩

lemma primesOverPlus_inertiaDeg_eq_one_at_p (PPlus : Ideal (𝓞 (K⁺)))
    (hPPlus : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (K⁺))) :
    (rationalPrimeIdeal p).inertiaDeg PPlus = 1 := by
  have hPPlus_eq : PPlus = zetaPrimePlus p K := by
    rw [primesOverPlus_at_p_eq_singleton_zetaPrimePlus (p := p) (K := K)] at hPPlus
    simpa using hPPlus
  simpa [hPPlus_eq] using zetaPrimePlus_inertiaDeg_eq_one_at_p (p := p) (K := K)

lemma zetaPrimePlus_ramificationIdx_eq_prime_sub_one_div_two_at_p (hp_odd : p ≠ 2) :
    (rationalPrimeIdeal p).ramificationIdx (zetaPrimePlus p K) = (p - 1) / 2 := by
  haveI : (zetaPrimePlus p K).LiesOver (rationalPrimeIdeal p) :=
    (zetaPrimePlus_mem_primesOver_at_p (p := p) (K := K)).2
  have hram_tower :
      (rationalPrimeIdeal p).ramificationIdx (zetaPrime p K) =
        (rationalPrimeIdeal p).ramificationIdx (zetaPrimePlus p K) *
          (zetaPrimePlus p K).ramificationIdx (zetaPrime p K) := by
    simpa using Ideal.ramificationIdx_algebra_tower'
      (p := rationalPrimeIdeal p) (P := zetaPrimePlus p K) (Q := zetaPrime p K)
  have hzeta_ram :
      (rationalPrimeIdeal p).ramificationIdx (zetaPrime p K) = p - 1 :=
    primesOver_ramificationIdx_eq_prime_sub_one_at_p (p := p) (K := K) (zetaPrime p K)
      (zetaPrime_mem_primesOver_at_p (p := p) (K := K))
  rw [hzeta_ram,
    ramificationIdx_zetaPrimePlus_eq_two (p := p) (hp_odd := hp_odd) (K := K)] at hram_tower
  have hram_tower' : p - 1 = 2 * (rationalPrimeIdeal p).ramificationIdx (zetaPrimePlus p K) := by
    simpa [Nat.mul_comm] using hram_tower
  exact (Nat.div_eq_of_eq_mul_right (by decide : 0 < 2) hram_tower').symm

lemma primesOverPlus_ramificationIdx_eq_prime_sub_one_div_two_at_p
  (hp_odd : p ≠ 2)
    (PPlus : Ideal (𝓞 (K⁺)))
    (hPPlus : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (K⁺))) :
    (rationalPrimeIdeal p).ramificationIdx PPlus = (p - 1) / 2 := by
  have hPPlus_eq : PPlus = zetaPrimePlus p K := by
    rw [primesOverPlus_at_p_eq_singleton_zetaPrimePlus (p := p) (K := K)] at hPPlus
    simpa using hPPlus
  simpa [hPPlus_eq] using
    zetaPrimePlus_ramificationIdx_eq_prime_sub_one_div_two_at_p
      (p := p) (hp_odd := hp_odd) (K := K)

lemma primesOverPlus_at_p_package (hp_odd : p ≠ 2) :
    (∀ PPlus ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (K⁺)),
      (rationalPrimeIdeal p).inertiaDeg PPlus = 1) ∧
    (∀ PPlus ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (K⁺)),
      (rationalPrimeIdeal p).ramificationIdx PPlus = (p - 1) / 2) ∧
    (Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (K⁺))).ncard = 1 :=
  ⟨primesOverPlus_inertiaDeg_eq_one_at_p (p := p) (K := K),
    primesOverPlus_ramificationIdx_eq_prime_sub_one_div_two_at_p
      (p := p) (K := K) hp_odd,
    ncard_primesOverPlus_at_p_eq_one (p := p) (K := K)⟩

lemma dedekindLocalFactorPlus_at_p {s : ℂ} :
    dedekindLocalFactor K⁺ p s = 1 - (p : ℂ) ^ (-s) := by
  classical
  unfold dedekindLocalFactor primesOverFinset rationalPrimeIdeal
  have hne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have hcoe :=
    IsDedekindDomain.coe_primesOverFinset (p := (Ideal.span {(p : ℤ)} : Ideal ℤ)) hne
      (𝓞 (K⁺))
  have hcard : (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)} : Ideal ℤ)
      (𝓞 (K⁺))).card = 1 := by
    have hncard : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 (K⁺))).ncard = 1 := by
      simpa [rationalPrimeIdeal] using ncard_primesOverPlus_at_p_eq_one (p := p) (K := K)
    rw [← hcoe] at hncard
    simpa using hncard
  obtain ⟨PPlus, hPPlus⟩ := Finset.card_eq_one.mp hcard
  rw [hPPlus, Finset.prod_singleton]
  have hPPlus_mem : PPlus ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 (K⁺)) := by
    rw [← hcoe]
    rw [hPPlus]
    exact Finset.mem_singleton_self PPlus
  haveI : PPlus.IsPrime := hPPlus_mem.1
  haveI : PPlus.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hPPlus_mem.2
  have habsNorm : Ideal.absNorm PPlus = p ^ (1 : ℕ) := by
    rw [← primesOverPlus_inertiaDeg_eq_one_at_p (p := p) (K := K) PPlus]
    · exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus hp.out
    · simpa [rationalPrimeIdeal] using hPPlus_mem
  rw [habsNorm]
  push_cast
  rw [pow_one]

end KplusPrimeArithmetic

end BernoulliRegular
