module

public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import BernoulliRegular.NumberFieldEulerProduct

/-!
# `K⁺` Euler product and residue bridge

This module closes the analytic `K⁺` side of the T023b2a chain.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators Topology nonZeroDivisors

namespace BernoulliRegular

section KplusEulerProduct

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

abbrev NonzeroIdealNF (L : Type*) [Field L] [NumberField L] : Type _ := NonzeroIdeal L

abbrev idealNormMultiplicityNF (L : Type*) [Field L] [NumberField L] (n : ℕ) : ℕ :=
  idealNormMultiplicity L n

lemma dedekindZeta_eq_tprod_primePowerSeriesNF
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏' q : Nat.Primes,
        (∑' k : ℕ, (idealNormMultiplicityNF L ((q : ℕ) ^ k) : ℂ) *
          ((((q : ℕ) ^ k : ℕ) : ℂ) ^ (-s))) := by
  simpa [idealNormMultiplicityNF] using
    (dedekindZeta_eq_tprod_primePowerSeries (L := L) hs)

lemma idealNormMultiplicityNF_p_pow_eq_one_plus (hp_odd : p ≠ 2) (k : ℕ) :
    idealNormMultiplicityNF K⁺ (p ^ k) = 1 := by
  classical
  haveI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  have hcard : (primesOverFinsetPlus (K := K) p).card = 1 := by
    rw [primesOverFinsetPlus_card_eq_ncard (K := K) (ℓ := p)]
    exact ncard_primesOverPlus_at_p_eq_one (p := p) (K := K)
  obtain ⟨PPlus, hPPlus⟩ := Finset.card_eq_one.mp hcard
  have hPPlusmem : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K⁺) := by
    have hPPlus_fin : PPlus ∈ primesOverFinsetPlus (K := K) p := by
      rw [hPPlus]
      exact Finset.mem_singleton_self PPlus
    exact (mem_primesOverFinsetPlus_iff (K := K) (ℓ := p)).1 hPPlus_fin
  have hPPlus_ne : PPlus ≠ ⊥ := by
    intro hPPlus_bot
    have hunder := hPPlusmem.2
    rw [Ideal.liesOver_iff, Ideal.under_def, hPPlus_bot,
      Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 K⁺))
        (FaithfulSMul.algebraMap_injective ℤ (𝓞 K⁺))] at hunder
    have hne : (rationalPrimeIdeal p) ≠ ⊥ := by
      rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.out.ne_zero
    exact hne hunder
  haveI : PPlus.IsPrime := hPPlusmem.1
  haveI : PPlus.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hPPlus_ne hPPlusmem.1
  haveI : PPlus.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hPPlusmem.2
  have habsNormPPlus : Ideal.absNorm PPlus = p := by
    calc
      Ideal.absNorm PPlus = p ^ (1 : ℕ) := by
        rw [← primesOverPlus_inertiaDeg_eq_one_at_p (p := p) (K := K) PPlus hPPlusmem]
        exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus hp.out
      _ = p := by simp
  unfold idealNormMultiplicityNF idealNormMultiplicity
  haveI : Unique {I : NonzeroIdealNF K⁺ // Ideal.absNorm I.1 = p ^ k} :=
    { default := ⟨⟨PPlus ^ k, pow_ne_zero k hPPlus_ne⟩, by
          rw [map_pow, habsNormPPlus]⟩
      uniq := by
        rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
        let m : ℕ := Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I)
        obtain ⟨Q, hPQ, hIeq⟩ := Ideal.eq_prime_pow_mul_coprime hI_ne PPlus
        have hQ_top : Q = ⊤ := by
          by_contra hQ_ne_top
          have hQ_ne : Q ≠ ⊥ := by
            intro hQ_bot
            apply hI_ne
            rw [hIeq, hQ_bot, Ideal.mul_bot]
          have hnf_ne : UniqueFactorizationMonoid.normalizedFactors Q ≠ 0 := by
            intro hnf
            apply hQ_ne_top
            rw [← Ideal.prod_normalizedFactors_eq_self hQ_ne, hnf]
            simp
          obtain ⟨R, hRmem⟩ := Multiset.exists_mem_of_ne_zero hnf_ne
          have hRfac := (Ideal.mem_normalizedFactors_iff hQ_ne).1 hRmem
          have hRprime : R.IsPrime := hRfac.1
          have hQ_le_R : Q ≤ R := hRfac.2
          haveI : R.IsPrime := hRprime
          have hR_ne : R ≠ ⊥ := fun hR_bot =>
            hQ_ne (le_bot_iff.mp (hQ_le_R.trans_eq hR_bot))
          haveI : NeZero R := ⟨hR_ne⟩
          have hI_le_Q : I ≤ Q := by
            rw [hIeq]
            exact Ideal.mul_le_left
          have hR_dvd_I : Ideal.absNorm R ∣ p ^ k := by
            rw [← hI_norm]
            exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ_le_R)
              (Ideal.absNorm_dvd_absNorm_of_le hI_le_Q)
          have hunder_dvd : Ideal.absNorm (Ideal.under ℤ R) ∣ p ^ k :=
            dvd_trans (Int.absNorm_under_dvd_absNorm R) hR_dvd_I
          have hunder_prime : (Ideal.absNorm (Ideal.under ℤ R)).Prime := Nat.absNorm_under_prime R
          have hunder_dvd_p : Ideal.absNorm (Ideal.under ℤ R) ∣ p :=
            hunder_prime.dvd_of_dvd_pow hunder_dvd
          have hunder_eq_p : Ideal.absNorm (Ideal.under ℤ R) = p :=
            (Nat.prime_dvd_prime_iff_eq hunder_prime hp.out).1 hunder_dvd_p
          have hunder_eq_span_p : Ideal.under ℤ R = Ideal.span {(p : ℤ)} := by
            rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ R)]
            simp [hunder_eq_p]
          have hR_lies : R.LiesOver (Ideal.span {(p : ℤ)}) := by
            rw [Ideal.liesOver_iff, hunder_eq_span_p]
          have hRmem_p : R ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K⁺) := by
            refine ⟨hRprime, ?_⟩
            simpa [rationalPrimeIdeal] using hR_lies
          have hRmem_fin : R ∈ primesOverFinsetPlus (K := K) p :=
            (mem_primesOverFinsetPlus_iff (K := K) (ℓ := p)).2 hRmem_p
          have hR_eq_PPlus : R = PPlus := by
            rw [hPPlus] at hRmem_fin
            exact Finset.mem_singleton.mp hRmem_fin
          have hQ_le_PPlus : Q ≤ PPlus := by
            simpa [hR_eq_PPlus] using hQ_le_R
          have htop_le_PPlus : (⊤ : Ideal (𝓞 K⁺)) ≤ PPlus := by
            calc
              ⊤ = PPlus ⊔ Q := hPQ.symm
              _ ≤ PPlus := sup_le le_rfl hQ_le_PPlus
          exact hPPlusmem.1.ne_top (top_le_iff.mp htop_le_PPlus)
        have hI_pow : I = PPlus ^ m := by
          simpa [m, hQ_top] using hIeq
        have hm : m = k := by
          apply Nat.pow_right_injective hp.out.one_lt
          calc
            p ^ m = Ideal.absNorm I := by
              rw [hI_pow, map_pow, habsNormPPlus]
            _ = p ^ k := hI_norm
        refine Subtype.ext (Subtype.ext ?_)
        simpa [m, hm] using hI_pow }
  exact Nat.card_unique

lemma normalizedFactors_subset_primesOverFinsetPlus_of_absNorm_prime_pow
    {q : Nat.Primes} {I : Ideal (𝓞 K⁺)} (hI_ne : I ≠ ⊥)
    {k : ℕ} (hI_norm : Ideal.absNorm I = (q : ℕ) ^ k) :
    (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆
      primesOverFinsetPlus (K := K) (q : ℕ) := by
  classical
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  intro PPlus hPPlus
  have hPPlus_mem : PPlus ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    Multiset.mem_toFinset.1 hPPlus
  have hPPlus_fac := (Ideal.mem_normalizedFactors_iff hI_ne).1 hPPlus_mem
  have hPPlus_prime : PPlus.IsPrime := hPPlus_fac.1
  have hI_le_PPlus : I ≤ PPlus := hPPlus_fac.2
  haveI : PPlus.IsPrime := hPPlus_prime
  have hPPlus_ne : PPlus ≠ ⊥ := fun hPPlus_bot =>
    hI_ne (le_bot_iff.mp (hPPlus_bot ▸ hI_le_PPlus))
  haveI : NeZero PPlus := ⟨hPPlus_ne⟩
  have hPPlus_dvd : Ideal.absNorm PPlus ∣ (q : ℕ) ^ k := by
    rw [← hI_norm]
    exact Ideal.absNorm_dvd_absNorm_of_le hI_le_PPlus
  have hunder_dvd : Ideal.absNorm (Ideal.under ℤ PPlus) ∣ (q : ℕ) ^ k :=
    dvd_trans (Int.absNorm_under_dvd_absNorm PPlus) hPPlus_dvd
  have hunder_prime : (Ideal.absNorm (Ideal.under ℤ PPlus)).Prime := Nat.absNorm_under_prime PPlus
  have hunder_dvd_q : Ideal.absNorm (Ideal.under ℤ PPlus) ∣ (q : ℕ) :=
    hunder_prime.dvd_of_dvd_pow hunder_dvd
  have hunder_eq_q : Ideal.absNorm (Ideal.under ℤ PPlus) = (q : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq hunder_prime q.2).1 hunder_dvd_q
  have hunder_eq_span_q : Ideal.under ℤ PPlus = Ideal.span {((q : ℕ) : ℤ)} := by
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ PPlus)]
    simp [hunder_eq_q]
  have hPPlus_lies : PPlus.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) := by
    rw [Ideal.liesOver_iff, hunder_eq_span_q]
  have hPPlus_over : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal (q : ℕ)) (𝓞 K⁺) := by
    refine ⟨hPPlus_prime, ?_⟩
    simpa [rationalPrimeIdeal] using hPPlus_lies
  exact (mem_primesOverFinsetPlus_iff (K := K) (ℓ := (q : ℕ))).2 hPPlus_over

lemma absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
    (hp_odd : p ≠ 2) {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p)
    {PPlus : Ideal (𝓞 K⁺)}
    (hPPlus : PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)) :
    Ideal.absNorm PPlus = (q : ℕ) ^ localResidueDegreePlus (p := p) (q : ℕ) hq := by
  have hPPlus_over : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal (q : ℕ)) (𝓞 K⁺) :=
    (mem_primesOverFinsetPlus_iff (K := K) (ℓ := (q : ℕ))).1 hPPlus
  haveI : PPlus.IsPrime := hPPlus_over.1
  haveI : PPlus.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hPPlus_over.2
  rw [← primesOver_inertiaDeg_eq_localResidueDegreePlus
    (p := p) (K := K) hp_odd hq PPlus hPPlus_over]
  exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus q.2

lemma normalizedFactors_card_mul_localResidueDegreePlus_of_absNorm_prime_pow
    (hp_odd : p ≠ 2) {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p)
    {I : Ideal (𝓞 K⁺)} (hI_ne : I ≠ ⊥) {k : ℕ}
    (hI_norm : Ideal.absNorm I = (q : ℕ) ^ k) :
    localResidueDegreePlus (p := p) (q : ℕ) hq *
        (UniqueFactorizationMonoid.normalizedFactors I).card = k := by
  classical
  set d := localResidueDegreePlus (p := p) (q : ℕ) hq with hd
  set m := UniqueFactorizationMonoid.normalizedFactors I with hm
  have hsubset : m.toFinset ⊆ primesOverFinsetPlus (K := K) (q : ℕ) := by
    simpa [hm] using
      normalizedFactors_subset_primesOverFinsetPlus_of_absNorm_prime_pow (K := K) hI_ne hI_norm
  have hsum_count : ∑ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), m.count PPlus = m.card :=
    Multiset.sum_count_eq_card fun PPlus hPPlus => hsubset (Multiset.mem_toFinset.2 hPPlus)
  have hnorm_factors : Ideal.absNorm m.prod = (q : ℕ) ^ (d * m.card) := by
    rw [Finset.prod_multiset_count_of_subset m (primesOverFinsetPlus (K := K) (q : ℕ)) hsubset,
      map_prod]
    calc
      ∏ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), Ideal.absNorm (PPlus ^ m.count PPlus)
          = ∏ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), ((q : ℕ) ^ d) ^ m.count PPlus := by
              apply Finset.prod_congr rfl
              intro PPlus hPPlus
              rw [map_pow]
              rw [absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
                (p := p) (K := K) hp_odd hq hPPlus, hd]
      _ = (q : ℕ) ^ (d * ∑ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), m.count PPlus) := by
              rw [Finset.prod_pow_eq_pow_sum]
              simp [Nat.pow_mul]
      _ = (q : ℕ) ^ (d * m.card) := by rw [hsum_count]
  have hpow : (q : ℕ) ^ (d * m.card) = (q : ℕ) ^ k := by
    calc
      (q : ℕ) ^ (d * m.card) = Ideal.absNorm m.prod := hnorm_factors.symm
      _ = Ideal.absNorm I := by rw [hm, Ideal.prod_normalizedFactors_eq_self hI_ne]
      _ = (q : ℕ) ^ k := hI_norm
  exact Nat.pow_right_injective q.2.one_lt hpow

lemma idealNormMultiplicityNF_prime_pow_eq_zero_of_not_dvd_plus
    (hp_odd : p ≠ 2) {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p)
    {k : ℕ} (hk : ¬ localResidueDegreePlus (p := p) (q : ℕ) hq ∣ k) :
    idealNormMultiplicityNF K⁺ ((q : ℕ) ^ k) = 0 := by
  unfold idealNormMultiplicityNF idealNormMultiplicity
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
  apply hk
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors I).card, ?_⟩
  simpa [mul_comm] using
    (normalizedFactors_card_mul_localResidueDegreePlus_of_absNorm_prime_pow
      (p := p) (K := K) hp_odd hq hI_ne hI_norm).symm

lemma idealNormMultiplicityNF_prime_pow_mul_localResidueDegreePlus_eq_card_sym
    (hp_odd : p ≠ 2) {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p) (n : ℕ) :
    idealNormMultiplicityNF K⁺
        ((q : ℕ) ^ (localResidueDegreePlus (p := p) (q : ℕ) hq * n)) =
      Fintype.card (Sym {PPlus : Ideal (𝓞 K⁺) //
        PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)} n) := by
  classical
  set d := localResidueDegreePlus (p := p) (q : ℕ) hq with hd
  let α : Type _ := {PPlus : Ideal (𝓞 K⁺) // PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)}
  letI : Fintype α := Fintype.ofFinset (primesOverFinsetPlus (K := K) (q : ℕ)) fun PPlus => by
    simp
  let β : Type _ := {I : NonzeroIdealNF K⁺ // Ideal.absNorm I.1 = (q : ℕ) ^ (d * n)}
  have hd_raw_pos : 0 < localResidueDegree (p := p) (q : ℕ) hq := by
    dsimp [localResidueDegree]
    exact orderOf_pos (unitOfPrimeNe (p := p) (q : ℕ) hq)
  have hd_pos : 0 < d := by
    rw [hd]
    by_cases hde : Even (localResidueDegree (p := p) (q : ℕ) hq)
    · rcases hde with ⟨k, hk⟩
      rw [localResidueDegreePlus_eq_half (p := p) hq ⟨k, hk⟩, hk]
      omega
    · rw [localResidueDegreePlus_eq_self (p := p) hq hde]
      exact hd_raw_pos
  have hpmap_val :
      ∀ {m : Multiset (Ideal (𝓞 K⁺))}
        (H : ∀ PPlus, PPlus ∈ m → PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)),
        (Multiset.pmap (fun PPlus hPPlus => (⟨PPlus, hPPlus⟩ : α)) m H).map Subtype.val = m := by
    intro m H
    rw [Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id']
  let toSym : β → Sym α n := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ =>
    let m := UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ PPlus, PPlus ∈ m → PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ) := by
      intro PPlus hPPlus
      have hsubset : m.toFinset ⊆ primesOverFinsetPlus (K := K) (q : ℕ) := by
        simpa [m] using
          normalizedFactors_subset_primesOverFinsetPlus_of_absNorm_prime_pow (K := K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hPPlus)
    have hm_card : m.card = n := by
      have hmul : d * m.card = d * n := by
        simpa [m, hd] using
          normalizedFactors_card_mul_localResidueDegreePlus_of_absNorm_prime_pow
            (p := p) (K := K) hp_odd hq hI_ne hI_norm
      exact Nat.eq_of_mul_eq_mul_left hd_pos hmul
    ⟨Multiset.pmap (fun PPlus hPPlus => (⟨PPlus, hPPlus⟩ : α)) m H, by
      simp [hm_card]⟩
  let ofSym : Sym α n → β := fun s =>
    let m : Multiset (Ideal (𝓞 K⁺)) := s.1.map Subtype.val
    have hm_card : m.card = n := by
      simp [m]
    have hm_subset : m.toFinset ⊆ primesOverFinsetPlus (K := K) (q : ℕ) := by
      intro PPlus hPPlus
      rcases Multiset.mem_toFinset.1 hPPlus with hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus, hQPlus, rfl⟩
      exact QPlus.2
    have hm_prime : ∀ PPlus ∈ m, Prime PPlus := by
      intro PPlus hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus, hQPlus, rfl⟩
      have hQPlus_ne : (QPlus : Ideal (𝓞 K⁺)) ≠ ⊥ := by
        intro hQPlus_bot
        have hQPlus_norm :=
          absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
            (p := p) (K := K) hp_odd hq QPlus.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQPlus_bot, ← hd] at hQPlus_norm
        exact pow_ne_zero d q.2.ne_zero hQPlus_norm.symm
      exact (Ideal.prime_iff_isPrime hQPlus_ne).2
        ((mem_primesOverFinsetPlus_iff (K := K) (ℓ := (q : ℕ))).1 QPlus.2).1
    have hm_prod_ne : m.prod ≠ ⊥ := Multiset.prod_ne_zero_of_prime m hm_prime
    have hm_norm : Ideal.absNorm m.prod = (q : ℕ) ^ (d * n) := by
      have hsum_count :
          ∑ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), m.count PPlus = m.card :=
        Multiset.sum_count_eq_card fun PPlus hPPlus =>
          hm_subset (Multiset.mem_toFinset.2 hPPlus)
      rw [Finset.prod_multiset_count_of_subset m (primesOverFinsetPlus (K := K) (q : ℕ)) hm_subset,
        map_prod]
      calc
        ∏ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), Ideal.absNorm (PPlus ^ m.count PPlus)
            = ∏ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), ((q : ℕ) ^ d) ^ m.count PPlus := by
                apply Finset.prod_congr rfl
                intro PPlus hPPlus
                rw [map_pow]
                rw [absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
                  (p := p) (K := K) hp_odd hq hPPlus, hd]
        _ = (q : ℕ) ^ (d * ∑ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), m.count PPlus) := by
                rw [Finset.prod_pow_eq_pow_sum]
                simp [Nat.pow_mul]
        _ = (q : ℕ) ^ (d * m.card) := by rw [hsum_count]
        _ = (q : ℕ) ^ (d * n) := by rw [hm_card]
    ⟨⟨m.prod, hm_prod_ne⟩, hm_norm⟩
  have htoSym_map_val :
      ∀ b : β, (toSym b).1.map Subtype.val = UniqueFactorizationMonoid.normalizedFactors b.1.1 := by
    rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
    dsimp [toSym]
    let m := UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ PPlus, PPlus ∈ m → PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ) := by
      intro PPlus hPPlus
      have hsubset : m.toFinset ⊆ primesOverFinsetPlus (K := K) (q : ℕ) := by
        simpa [m] using
          normalizedFactors_subset_primesOverFinsetPlus_of_absNorm_prime_pow (K := K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hPPlus)
    change (Multiset.pmap (fun PPlus hPPlus => (⟨PPlus, hPPlus⟩ : α)) m H).map Subtype.val = m
    rw [hpmap_val H]
  have hofSym_nfactors :
      ∀ s : Sym α n,
        UniqueFactorizationMonoid.normalizedFactors (ofSym s).1.1 = s.1.map Subtype.val := by
    intro s
    dsimp [ofSym]
    let m : Multiset (Ideal (𝓞 K⁺)) := s.1.map Subtype.val
    have hm_prime : ∀ PPlus ∈ m, Prime PPlus := by
      intro PPlus hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus, hQPlus, rfl⟩
      have hQPlus_ne : (QPlus : Ideal (𝓞 K⁺)) ≠ ⊥ := by
        intro hQPlus_bot
        have hQPlus_norm :=
          absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
            (p := p) (K := K) hp_odd hq QPlus.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQPlus_bot, ← hd] at hQPlus_norm
        exact pow_ne_zero d q.2.ne_zero hQPlus_norm.symm
      exact (Ideal.prime_iff_isPrime hQPlus_ne).2
        ((mem_primesOverFinsetPlus_iff (K := K) (ℓ := (q : ℕ))).1 QPlus.2).1
    change UniqueFactorizationMonoid.normalizedFactors m.prod = m
    exact UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hm_prime
  have hleft : Function.LeftInverse ofSym toSym := by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    change ((toSym b).1.map Subtype.val).prod = b.1.1
    rw [htoSym_map_val, Ideal.prod_normalizedFactors_eq_self b.1.2]
  have hright : Function.RightInverse ofSym toSym := by
    intro s
    apply Subtype.ext
    apply Multiset.map_injective Subtype.val_injective
    simpa [hofSym_nfactors s] using htoSym_map_val (ofSym s)
  let e : β ≃ Sym α n :=
    ⟨toSym, ofSym, hleft, hright⟩
  unfold idealNormMultiplicityNF idealNormMultiplicity
  simpa [β, α, hd, Nat.card_eq_fintype_card] using Nat.card_congr e

lemma dedekind_prime_power_series_eq_localFactorPlus_at_p
    (hp_odd : p ≠ 2) {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, (idealNormMultiplicityNF K⁺ (p ^ k) : ℂ) *
      (((p ^ k : ℕ) : ℂ) ^ (-s))) =
      (dedekindLocalFactor K⁺ p s)⁻¹ := by
  haveI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    have hle : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
      Complex.norm_prime_cpow_le_one_half ⟨p, hp.out⟩ hs
    exact hle.trans_lt (by norm_num)
  rw [dedekindLocalFactorPlus_at_p (p := p) (K := K)]
  trans ∑' k : ℕ, ((p : ℂ) ^ (-s)) ^ k
  · refine tsum_congr fun k => ?_
    rw [idealNormMultiplicityNF_p_pow_eq_one_plus (p := p) (K := K) hp_odd k]
    simp only [Nat.cast_one, one_mul]
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul p k (-s), mul_comm,
      Complex.cpow_mul_nat]
  · simpa using tsum_geometric_of_norm_lt_one hnorm

lemma dedekind_prime_power_series_eq_localFactorPlus
    (hp_odd : p ≠ 2) {q : Nat.Primes} {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, (idealNormMultiplicityNF K⁺ ((q : ℕ) ^ k) : ℂ) *
      ((((q : ℕ) ^ k : ℕ) : ℂ) ^ (-s))) =
      (dedekindLocalFactor K⁺ (q : ℕ) s)⁻¹ := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  by_cases hq : (q : ℕ) = p
  · have hq' : q = ⟨p, Fact.out⟩ := by
      apply Subtype.ext
      simpa using hq
    subst hq'
    simpa using dedekind_prime_power_series_eq_localFactorPlus_at_p
      (p := p) (K := K) hp_odd hs
  · classical
    haveI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
    set d := localResidueDegreePlus (p := p) (q : ℕ) hq with hd
    let α : Type _ := {PPlus : Ideal (𝓞 K⁺) //
      PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)}
    letI : Fintype α :=
      Fintype.ofFinset (primesOverFinsetPlus (K := K) (q : ℕ)) fun PPlus => by simp
    let f : ℕ → ℂ := fun k =>
      (idealNormMultiplicityNF K⁺ ((q : ℕ) ^ k) : ℂ) * ((((q : ℕ) ^ k : ℕ) : ℂ) ^ (-s))
    let g : ℕ → ℂ := fun n =>
      (idealNormMultiplicityNF K⁺ ((q : ℕ) ^ (d * n)) : ℂ) *
        ((((q : ℕ) ^ (d * n) : ℕ) : ℂ) ^ (-s))
    let z : ℂ := (q : ℂ) ^ (-((d : ℂ) * s))
    have hd_raw_pos : 0 < localResidueDegree (p := p) (q : ℕ) hq := by
      dsimp [localResidueDegree]
      exact orderOf_pos (unitOfPrimeNe (p := p) (q : ℕ) hq)
    have hd_pos : 0 < d := by
      rw [hd]
      by_cases hde : Even (localResidueDegree (p := p) (q : ℕ) hq)
      · rcases hde with ⟨k, hk⟩
        rw [localResidueDegreePlus_eq_half (p := p) hq ⟨k, hk⟩, hk]
        omega
      · rw [localResidueDegreePlus_eq_self (p := p) hq hde]
        exact hd_raw_pos
    have hs_d : 1 < (((d : ℂ) * s).re) := by
      rw [Complex.mul_re]
      simp
      have hd_ge : (1 : ℝ) ≤ d := by
        exact_mod_cast Nat.succ_le_of_lt hd_pos
      nlinarith [hs, hd_ge]
    have hz : ‖z‖ < 1 := by
      have hle : ‖z‖ ≤ 1 / 2 := by
        dsimp [z]
        exact Complex.norm_prime_cpow_le_one_half ⟨q, q.2⟩ hs_d
      exact hle.trans_lt (by norm_num)
    have hg_term : ∀ n : ℕ, g n = (Fintype.card (Sym α n) : ℂ) * z ^ n := by
      intro n
      dsimp [g, z]
      rw [show idealNormMultiplicityNF K⁺ ((q : ℕ) ^ (d * n)) = Fintype.card (Sym α n) by
        simpa [α, hd] using
          idealNormMultiplicityNF_prime_pow_mul_localResidueDegreePlus_eq_card_sym
            (p := p) (K := K) hp_odd hq n]
      rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul (q : ℕ) (d * n) (-s)]
      have hexp : (((d * n : ℕ) : ℂ) * (-s)) = (-((d : ℂ) * s)) * n := by
        push_cast
        ring
      rw [hexp, Complex.cpow_mul_nat]
    have hg_eq : g = fun n : ℕ => (Fintype.card (Sym α n) : ℂ) * z ^ n := funext hg_term
    have hg_hasSum0 : HasSum (fun n : ℕ => (Fintype.card (Sym α n) : ℂ) * z ^ n)
        (((1 - z)⁻¹) ^ Fintype.card α) := by
      rw [← tsum_symGeometric α hz]
      exact (summable_tsum_symGeometric α hz).1.hasSum
    have hg_hasSum : HasSum g (((1 - z)⁻¹) ^ Fintype.card α) := by
      simpa [hg_eq] using hg_hasSum0
    have hf_hasSum : HasSum f (((1 - z)⁻¹) ^ Fintype.card α) := by
      refine (hasSum_iff_hasSum_of_ne_zero_bij
        (f := f) (g := g) (i := fun x : Function.support g => d * x.1) ?_ ?_ ?_).2 hg_hasSum
      · intro x y hxy
        exact Subtype.ext <| Nat.eq_of_mul_eq_mul_left hd_pos hxy
      · intro k hk
        have hk_mult : idealNormMultiplicityNF K⁺ ((q : ℕ) ^ k) ≠ 0 := fun hk_zero =>
          hk (by simp [f, hk_zero])
        have hk_dvd : d ∣ k := by
          by_contra hk_ndvd
          exact hk_mult <|
            idealNormMultiplicityNF_prime_pow_eq_zero_of_not_dvd_plus
              (p := p) (K := K) hp_odd hq hk_ndvd
        obtain ⟨n, rfl⟩ := hk_dvd
        refine ⟨⟨n, ?_⟩, rfl⟩
        simpa [f, g, mul_comm] using hk
      · intro x
        simp [f, g, mul_comm]
    have hcard_finset :
        (primesOverFinsetPlus (K := K) (q : ℕ)).card =
          localPrimeCountPlus (p := p) (q : ℕ) hq := by
      rw [primesOverFinsetPlus_card_eq_ncard (K := K) (ℓ := (q : ℕ))]
      exact ncard_primesOverPlus_eq_localPrimeCountPlus (p := p) (K := K) hp_odd hq
    have hα_card : Fintype.card α = localPrimeCountPlus (p := p) (q : ℕ) hq := by
      calc
        Fintype.card α = (primesOverFinsetPlus (K := K) (q : ℕ)).card :=
          Fintype.card_of_finset' (primesOverFinsetPlus (K := K) (q : ℕ)) fun PPlus => by simp
        _ = localPrimeCountPlus (p := p) (q : ℕ) hq := hcard_finset
    have hf_hasSum' : HasSum f ((dedekindLocalFactor K⁺ (q : ℕ) s)⁻¹) := by
      rw [dedekindLocalFactor_eq_pow_localResidueDegreePlus (p := p) (K := K) hp_odd hq, ← inv_pow]
      simpa [z, hd, hα_card] using hf_hasSum
    simpa [f] using hf_hasSum'.tsum_eq

lemma dedekindZetaPlus_eq_eulerProduct (hp_odd : p ≠ 2) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K⁺ s =
      ∏' q : Nat.Primes, (dedekindLocalFactor K⁺ (q : ℕ) s)⁻¹ := by
  rw [dedekindZeta_eq_tprod_primePowerSeriesNF (L := K⁺) hs]
  exact tprod_congr fun q =>
    dedekind_prime_power_series_eq_localFactorPlus (p := p) (K := K) hp_odd hs

lemma evenLProduct_eq_tprod_localFactors {s : ℂ} (hs : 1 < s.re) :
    evenLProduct p s =
      ∏' q : Nat.Primes,
        ∏ χ ∈ evenNontrivialCharacters (p := p),
          (1 - χ ((q : ℕ) : ZMod p) * ((q : ℕ) : ℂ) ^ (-s))⁻¹ := by
  classical
  unfold evenLProduct
  rw [Finset.prod_congr rfl (fun χ _ => LFunction_eq_prime_tprod_of_localFactors p χ hs)]
  exact (Multipliable.tprod_finsetProd
    (s := evenNontrivialCharacters (p := p))
    (fun χ _ => (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable)).symm

lemma evenLProduct_eq_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    evenLProduct p s =
      ∏' q : Nat.Primes, (evenCharLocalFactor (p := p) (q : ℕ) s)⁻¹ := by
  classical
  rw [evenLProduct_eq_tprod_localFactors (p := p) hs]
  refine tprod_congr fun q => ?_
  unfold evenCharLocalFactor
  rw [Finset.prod_inv_distrib]

lemma evenCharLocalFactor_at_p {s : ℂ} :
    evenCharLocalFactor (p := p) p s = 1 := by
  classical
  exact Finset.prod_eq_one fun χ _ => by
    rw [ZMod.natCast_self, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, sub_zero]

lemma localFactorsPlus_agree_prime_ne_p (hp_odd : p ≠ 2)
    {q : Nat.Primes} (hq : (q : ℕ) ≠ p) {s : ℂ} :
    dedekindLocalFactor K⁺ (q : ℕ) s =
      (1 - ((q : ℕ) : ℂ) ^ (-s)) * evenCharLocalFactor (p := p) (q : ℕ) s := by
  haveI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  rw [dedekindLocalFactor_eq_pow_localResidueDegreePlus (p := p) (K := K) hp_odd hq]
  symm
  simpa [neg_mul] using
    (trivial_mul_evenCharLocalFactor_eq_pow_localResidueDegreePlus
      (p := p) hp_odd hq (s := s))

lemma localFactorsPlus_agree_at_p (hp_odd : p ≠ 2) {s : ℂ} :
    dedekindLocalFactor K⁺ p s =
      (1 - (p : ℂ) ^ (-s)) * evenCharLocalFactor (p := p) p s := by
  haveI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  rw [evenCharLocalFactor_at_p (p := p), mul_one, dedekindLocalFactorPlus_at_p (p := p) (K := K)]

lemma localFactorsPlus_agree (hp_odd : p ≠ 2) {q : Nat.Primes} {s : ℂ} :
    dedekindLocalFactor K⁺ (q : ℕ) s =
      (1 - ((q : ℕ) : ℂ) ^ (-s)) * evenCharLocalFactor (p := p) (q : ℕ) s := by
  by_cases hq : (q : ℕ) = p
  · have hq' : q = ⟨p, Fact.out⟩ := by
      apply Subtype.ext
      simpa using hq
    subst hq'
    exact localFactorsPlus_agree_at_p (p := p) (K := K) hp_odd
  · exact localFactorsPlus_agree_prime_ne_p (p := p) (K := K) hp_odd hq

theorem dedekindZeta_eq_riemannZeta_mul_evenLProduct_of_one_lt_re
    (hp_odd : p ≠ 2) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K⁺ s = riemannZeta s * evenLProduct p s := by
  have hmul_riem :
      Multipliable (fun q : Nat.Primes => (1 - ((q : ℕ) : ℂ) ^ (-s))⁻¹) :=
    (riemannZeta_eulerProduct_hasProd hs).multipliable
  have hmul_even :
      Multipliable (fun q : Nat.Primes => (evenCharLocalFactor (p := p) (q : ℕ) s)⁻¹) := by
    classical
    have h1 :
        (fun q : Nat.Primes => (evenCharLocalFactor (p := p) (q : ℕ) s)⁻¹) =
          (fun q : Nat.Primes =>
            ∏ χ ∈ evenNontrivialCharacters (p := p),
              (1 - χ ((q : ℕ) : ZMod p) * ((q : ℕ) : ℂ) ^ (-s))⁻¹) := by
      funext q
      unfold evenCharLocalFactor
      rw [Finset.prod_inv_distrib]
    rw [h1]
    exact multipliable_prod (s := evenNontrivialCharacters (p := p)) fun χ _ =>
      (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  calc
    NumberField.dedekindZeta K⁺ s
        = ∏' q : Nat.Primes, (dedekindLocalFactor K⁺ (q : ℕ) s)⁻¹ :=
            dedekindZetaPlus_eq_eulerProduct (p := p) (K := K) hp_odd hs
    _ = ∏' q : Nat.Primes,
          ((1 - ((q : ℕ) : ℂ) ^ (-s))⁻¹ *
            (evenCharLocalFactor (p := p) (q : ℕ) s)⁻¹) := by
            refine tprod_congr fun q => ?_
            rw [localFactorsPlus_agree (p := p) (K := K) hp_odd, mul_inv_rev, mul_comm]
    _ = (∏' q : Nat.Primes, (1 - ((q : ℕ) : ℂ) ^ (-s))⁻¹) *
          (∏' q : Nat.Primes, (evenCharLocalFactor (p := p) (q : ℕ) s)⁻¹) := by
            rw [Multipliable.tprod_mul hmul_riem hmul_even]
    _ = riemannZeta s * evenLProduct p s := by
            rw [riemannZeta_eulerProduct_tprod hs, evenLProduct_eq_eulerProduct (p := p) hs]

theorem tendsto_sub_one_mul_riemannZeta_mul_evenLProduct :
    Filter.Tendsto
      (fun s : ℝ ↦ (s - 1) * (riemannZeta (s : ℂ) * evenLProduct p (s : ℂ)))
      (𝓝[>] 1)
      (𝓝 (evenLProduct p (1 : ℂ))) := by
  classical
  have h_cont : Continuous (evenLProduct p) :=
    continuous_finsetProd _ fun χ hχ =>
      (DirichletCharacter.differentiable_LFunction (Finset.mem_filter.mp hχ).2.2).continuous
  have h_embed : Filter.Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds,
        by
          filter_upwards [self_mem_nhdsWithin] with s hs h
          exact absurd (Complex.ofReal_injective h) (ne_of_gt hs)⟩
  have h_zeta : Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 1) :=
    riemannZeta_residue_one.comp h_embed
  have h_lprod : Filter.Tendsto (fun s : ℝ => evenLProduct p (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (evenLProduct p 1)) :=
    (h_cont.tendsto 1).comp (h_embed.mono_right nhdsWithin_le_nhds)
  have h_prod := h_zeta.mul h_lprod
  rw [one_mul] at h_prod
  refine (Filter.tendsto_congr' ?_).mp h_prod
  filter_upwards [self_mem_nhdsWithin] with s _
  ring

theorem tendsto_sub_one_mul_dedekindZetaPlus_via_evenLProducts (hp_odd : p ≠ 2) :
    Filter.Tendsto
      (fun s : ℝ ↦ (s - 1) * NumberField.dedekindZeta K⁺ (s : ℂ))
      (𝓝[>] 1)
      (𝓝 (evenLProduct p (1 : ℂ))) := by
  refine (Filter.tendsto_congr' ?_).mp
    (tendsto_sub_one_mul_riemannZeta_mul_evenLProduct (p := p))
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [dedekindZeta_eq_riemannZeta_mul_evenLProduct_of_one_lt_re
    (p := p) (K := K) hp_odd (by exact_mod_cast hs)]

theorem maximalRealSubfield_residue_ready_factorization (hp_odd : p ≠ 2) :
    NumberField.dedekindZeta_residue K⁺ = (evenLProduct p (1 : ℂ)).re := by
  have heq : ((NumberField.dedekindZeta_residue K⁺ : ℝ) : ℂ) = evenLProduct p (1 : ℂ) :=
    tendsto_nhds_unique (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K⁺)
      (tendsto_sub_one_mul_dedekindZetaPlus_via_evenLProducts (p := p) (K := K) hp_odd)
  rw [← heq, Complex.ofReal_re]

theorem complex_maximalRealSubfield_residue_eq_evenLProduct_one (hp_odd : p ≠ 2) :
    ((NumberField.dedekindZeta_residue K⁺ : ℝ) : ℂ) = evenLProduct p (1 : ℂ) :=
  tendsto_nhds_unique (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K⁺)
    (tendsto_sub_one_mul_dedekindZetaPlus_via_evenLProducts (p := p) (K := K) hp_odd)

end KplusEulerProduct

end BernoulliRegular
