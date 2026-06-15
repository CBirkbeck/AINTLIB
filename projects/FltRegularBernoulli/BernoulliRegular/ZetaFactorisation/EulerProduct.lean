module

public import BernoulliRegular.ZetaFactorisation.Basic
public import BernoulliRegular.NumberFieldEulerProduct

/-!
# Euler-product assembly for cyclotomic zeta factorisation

This module contains the global Euler-product arguments for
`BernoulliRegular.ZetaFactorisation`.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped Topology nonZeroDivisors

namespace BernoulliRegular

section ZetaFactorisation

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Step E — Euler-product assembly skeleton -/

lemma idealNormMultiplicity_p_pow_eq_one (k : ℕ) :
    idealNormMultiplicity K (p ^ k) = 1 := by
  classical
  have hne : (rationalPrimeIdeal p) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  haveI : (rationalPrimeIdeal p).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hcoe := IsDedekindDomain.coe_primesOverFinset (p := rationalPrimeIdeal p) hne (𝓞 K)
  have hcard : (primesOverFinset K p).card = 1 := by
    have hncard : (Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K)).ncard = 1 :=
      ncard_primesOver_at_p_eq_one (p := p) (K := K)
    rw [← hcoe, Set.ncard_coe_finset] at hncard
    rw [primesOverFinset]
    exact hncard
  obtain ⟨P, hP⟩ := Finset.card_eq_one.mp hcard
  have hPmem : P ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K) := by
    have hPfin : P ∈ primesOverFinset K p := by
      rw [hP]
      exact Finset.mem_singleton_self P
    exact (mem_primesOverFinset_iff (K := K) (ℓ := p)).1 hPfin
  have hP_ne : P ≠ ⊥ := by
    intro hP_bot
    have hunder := hPmem.2
    rw [Ideal.liesOver_iff, Ideal.under_def, hP_bot,
      Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 K))
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))] at hunder
    exact hne hunder
  haveI : P.IsPrime := hPmem.1
  haveI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP_ne hPmem.1
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hPmem.2
  have habsNormP : Ideal.absNorm P = p := by
    calc
      Ideal.absNorm P = p ^ (1 : ℕ) := by
        rw [← primesOver_inertiaDeg_eq_one_at_p (p := p) (K := K) P hPmem]
        exact Ideal.absNorm_eq_pow_inertiaDeg' P hp.out
      _ = p := by simp
  unfold idealNormMultiplicity
  haveI : Unique {I : NonzeroIdeal K // Ideal.absNorm I.1 = p ^ k} :=
    { default := ⟨⟨P ^ k, pow_ne_zero k hP_ne⟩, by
          rw [map_pow, habsNormP]⟩
      uniq := by
        rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
        let m : ℕ := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors I)
        obtain ⟨Q, hPQ, hIeq⟩ := Ideal.eq_prime_pow_mul_coprime hI_ne P
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
          have hRmem_p : R ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K) := by
            refine ⟨hRprime, ?_⟩
            simpa [rationalPrimeIdeal] using hR_lies
          have hRmem_fin : R ∈ primesOverFinset K p :=
            (mem_primesOverFinset_iff (K := K) (ℓ := p)).2 hRmem_p
          have hR_eq_P : R = P := by
            rw [hP] at hRmem_fin
            exact Finset.mem_singleton.mp hRmem_fin
          have hQ_le_P : Q ≤ P := by
            simpa [hR_eq_P] using hQ_le_R
          have htop_le_P : (⊤ : Ideal (𝓞 K)) ≤ P := by
            calc
              ⊤ = P ⊔ Q := hPQ.symm
              _ ≤ P := sup_le le_rfl hQ_le_P
          exact hPmem.1.ne_top (top_le_iff.mp htop_le_P)
        have hI_pow : I = P ^ m := by
          simpa [m, hQ_top] using hIeq
        have hm : m = k := by
          apply Nat.pow_right_injective hp.out.one_lt
          calc
            p ^ m = Ideal.absNorm I := by
              rw [hI_pow, map_pow, habsNormP]
            _ = p ^ k := hI_norm
        refine Subtype.ext (Subtype.ext ?_)
        simpa [m, hm] using hI_pow }
  exact Nat.card_unique

lemma normalizedFactors_subset_primesOverFinset_of_absNorm_prime_pow
  {q : Nat.Primes} {I : Ideal (𝓞 K)} (hI_ne : I ≠ ⊥)
    {k : ℕ} (hI_norm : Ideal.absNorm I = (q : ℕ) ^ k) :
    (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆ primesOverFinset K (q : ℕ) := by
  classical
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  intro P hP
  have hP_mem : P ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    Multiset.mem_toFinset.1 hP
  have hP_fac := (Ideal.mem_normalizedFactors_iff hI_ne).1 hP_mem
  have hP_prime : P.IsPrime := hP_fac.1
  have hI_le_P : I ≤ P := hP_fac.2
  haveI : P.IsPrime := hP_prime
  have hP_ne : P ≠ ⊥ := fun hP_bot =>
    hI_ne (le_bot_iff.mp (hP_bot ▸ hI_le_P))
  haveI : NeZero P := ⟨hP_ne⟩
  have hP_dvd : Ideal.absNorm P ∣ (q : ℕ) ^ k := by
    rw [← hI_norm]
    exact Ideal.absNorm_dvd_absNorm_of_le hI_le_P
  have hunder_dvd : Ideal.absNorm (Ideal.under ℤ P) ∣ (q : ℕ) ^ k :=
    dvd_trans (Int.absNorm_under_dvd_absNorm P) hP_dvd
  have hunder_prime : (Ideal.absNorm (Ideal.under ℤ P)).Prime := Nat.absNorm_under_prime P
  have hunder_dvd_q : Ideal.absNorm (Ideal.under ℤ P) ∣ (q : ℕ) :=
    hunder_prime.dvd_of_dvd_pow hunder_dvd
  have hunder_eq_q : Ideal.absNorm (Ideal.under ℤ P) = (q : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq hunder_prime q.2).1 hunder_dvd_q
  have hunder_eq_span_q : Ideal.under ℤ P = Ideal.span {((q : ℕ) : ℤ)} := by
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ P)]
    simp [hunder_eq_q]
  have hP_lies : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) := by
    rw [Ideal.liesOver_iff, hunder_eq_span_q]
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal (q : ℕ)) (𝓞 K) := by
    refine ⟨hP_prime, ?_⟩
    simpa [rationalPrimeIdeal] using hP_lies
  exact (mem_primesOverFinset_iff (K := K) (ℓ := (q : ℕ))).2 hP_over

lemma absNorm_eq_q_pow_localResidueDegree_of_mem_primesOverFinset
    {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p) {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOverFinset K (q : ℕ)) :
    Ideal.absNorm P = (q : ℕ) ^ localResidueDegree (p := p) (q : ℕ) hq := by
  classical
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal (q : ℕ)) (𝓞 K) :=
    (mem_primesOverFinset_iff (K := K) (ℓ := (q : ℕ))).1 hP
  haveI : P.IsPrime := hP_over.1
  haveI : P.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hP_over.2
  rw [← primesOver_inertiaDeg_eq_localResidueDegree p K hq P hP_over]
  exact Ideal.absNorm_eq_pow_inertiaDeg' P q.2

lemma normalizedFactors_card_mul_localResidueDegree_of_absNorm_prime_pow
  {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p) {I : Ideal (𝓞 K)} (hI_ne : I ≠ ⊥)
    {k : ℕ} (hI_norm : Ideal.absNorm I = (q : ℕ) ^ k) :
    localResidueDegree (p := p) (q : ℕ) hq *
        (UniqueFactorizationMonoid.normalizedFactors I).card = k := by
  classical
  set d := localResidueDegree (p := p) (q : ℕ) hq with hd
  set m := UniqueFactorizationMonoid.normalizedFactors I with hm
  have hsubset : m.toFinset ⊆ primesOverFinset K (q : ℕ) := by
    simpa [hm] using
      normalizedFactors_subset_primesOverFinset_of_absNorm_prime_pow (K := K) hI_ne
        hI_norm
  have hsum_count : ∑ P ∈ primesOverFinset K (q : ℕ), m.count P = m.card :=
    Multiset.sum_count_eq_card fun P hP => hsubset (Multiset.mem_toFinset.2 hP)
  have hnorm_factors : Ideal.absNorm m.prod = (q : ℕ) ^ (d * m.card) := by
    rw [Finset.prod_multiset_count_of_subset m (primesOverFinset K (q : ℕ)) hsubset,
      map_prod]
    calc
      ∏ P ∈ primesOverFinset K (q : ℕ), Ideal.absNorm (P ^ m.count P)
          = ∏ P ∈ primesOverFinset K (q : ℕ), ((q : ℕ) ^ d) ^ m.count P := by
              apply Finset.prod_congr rfl
              intro P hP
              rw [map_pow]
              rw [absNorm_eq_q_pow_localResidueDegree_of_mem_primesOverFinset
                (p := p) (K := K) hq hP, hd]
      _ = (q : ℕ) ^ (d * ∑ P ∈ primesOverFinset K (q : ℕ), m.count P) := by
              rw [Finset.prod_pow_eq_pow_sum]
              simp [Nat.pow_mul]
      _ = (q : ℕ) ^ (d * m.card) := by rw [hsum_count]
  have hpow : (q : ℕ) ^ (d * m.card) = (q : ℕ) ^ k := by
    calc
      (q : ℕ) ^ (d * m.card) = Ideal.absNorm m.prod := hnorm_factors.symm
      _ = Ideal.absNorm I := by rw [hm, Ideal.prod_normalizedFactors_eq_self hI_ne]
      _ = (q : ℕ) ^ k := hI_norm
  exact Nat.pow_right_injective q.2.one_lt hpow

lemma idealNormMultiplicity_prime_pow_eq_zero_of_not_dvd
    {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p) {k : ℕ}
    (hk : ¬ localResidueDegree (p := p) (q : ℕ) hq ∣ k) :
    idealNormMultiplicity K ((q : ℕ) ^ k) = 0 := by
  unfold idealNormMultiplicity
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
  apply hk
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors I).card, ?_⟩
  simpa [mul_comm] using
    normalizedFactors_card_mul_localResidueDegree_of_absNorm_prime_pow
      (p := p) (K := K) hq hI_ne hI_norm |>.symm

lemma idealNormMultiplicity_prime_pow_mul_localResidueDegree_eq_card_sym
    {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p) (n : ℕ) :
    idealNormMultiplicity K
        ((q : ℕ) ^ (localResidueDegree (p := p) (q : ℕ) hq * n)) =
      Fintype.card (Sym {P : Ideal (𝓞 K) // P ∈ primesOverFinset K (q : ℕ)} n) := by
  classical
  set d := localResidueDegree (p := p) (q : ℕ) hq with hd
  let α : Type _ := {P : Ideal (𝓞 K) // P ∈ primesOverFinset K (q : ℕ)}
  letI : Fintype α := Fintype.ofFinset (primesOverFinset K (q : ℕ)) fun P => by
    simp
  let β : Type _ := {I : NonzeroIdeal K // Ideal.absNorm I.1 = (q : ℕ) ^ (d * n)}
  have hd_pos : 0 < d := by
    rw [hd]
    exact orderOf_pos _
  have hpmap_val :
      ∀ {m : Multiset (Ideal (𝓞 K))}
        (H : ∀ P, P ∈ m → P ∈ primesOverFinset K (q : ℕ)),
        (Multiset.pmap (fun P hP => (⟨P, hP⟩ : α)) m H).map Subtype.val = m := by
    intro m H
    rw [Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id']
  let toSym : β → Sym α n := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ =>
    let m := UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ P, P ∈ m → P ∈ primesOverFinset K (q : ℕ) := by
      intro P hP
      have hsubset : m.toFinset ⊆ primesOverFinset K (q : ℕ) := by
        simpa [m] using
          normalizedFactors_subset_primesOverFinset_of_absNorm_prime_pow (K := K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hP)
    have hm_card : m.card = n := by
      have hmul : d * m.card = d * n := by
        simpa [m, hd] using
          normalizedFactors_card_mul_localResidueDegree_of_absNorm_prime_pow
            (p := p) (K := K) hq hI_ne hI_norm
      exact Nat.eq_of_mul_eq_mul_left hd_pos hmul
    ⟨Multiset.pmap (fun P hP => (⟨P, hP⟩ : α)) m H, by
      simp [hm_card]⟩
  let ofSym : Sym α n → β := fun s =>
    let m : Multiset (Ideal (𝓞 K)) := s.1.map Subtype.val
    have hm_card : m.card = n := by
      simp [m]
    have hm_subset : m.toFinset ⊆ primesOverFinset K (q : ℕ) := by
      intro P hP
      rcases Multiset.mem_toFinset.1 hP with hP
      rcases Multiset.mem_map.1 hP with ⟨Q, hQ, rfl⟩
      exact Q.2
    have hm_prime : ∀ P ∈ m, Prime P := by
      intro P hP
      rcases Multiset.mem_map.1 hP with ⟨Q, hQ, rfl⟩
      have hQ_ne : (Q : Ideal (𝓞 K)) ≠ ⊥ := by
        intro hQ_bot
        have hQ_norm :=
          absNorm_eq_q_pow_localResidueDegree_of_mem_primesOverFinset
            (p := p) (K := K) hq Q.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQ_bot, ← hd] at hQ_norm
        exact pow_ne_zero d q.2.ne_zero hQ_norm.symm
      exact (Ideal.prime_iff_isPrime hQ_ne).2
        ((mem_primesOverFinset_iff (K := K) (ℓ := (q : ℕ))).1 Q.2).1
    have hm_prod_ne : m.prod ≠ ⊥ := Multiset.prod_ne_zero_of_prime m hm_prime
    have hm_norm : Ideal.absNorm m.prod = (q : ℕ) ^ (d * n) := by
      have hsum_count : ∑ P ∈ primesOverFinset K (q : ℕ), m.count P = m.card :=
        Multiset.sum_count_eq_card fun P hP => hm_subset (Multiset.mem_toFinset.2 hP)
      rw [Finset.prod_multiset_count_of_subset m (primesOverFinset K (q : ℕ)) hm_subset,
        map_prod]
      calc
        ∏ P ∈ primesOverFinset K (q : ℕ), Ideal.absNorm (P ^ m.count P)
            = ∏ P ∈ primesOverFinset K (q : ℕ), ((q : ℕ) ^ d) ^ m.count P := by
                apply Finset.prod_congr rfl
                intro P hP
                rw [map_pow]
                rw [absNorm_eq_q_pow_localResidueDegree_of_mem_primesOverFinset
                  (p := p) (K := K) hq hP, hd]
        _ = (q : ℕ) ^ (d * ∑ P ∈ primesOverFinset K (q : ℕ), m.count P) := by
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
    let H : ∀ P, P ∈ m → P ∈ primesOverFinset K (q : ℕ) := by
      intro P hP
      have hsubset : m.toFinset ⊆ primesOverFinset K (q : ℕ) := by
        simpa [m] using
          normalizedFactors_subset_primesOverFinset_of_absNorm_prime_pow (K := K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hP)
    change (Multiset.pmap (fun P hP => (⟨P, hP⟩ : α)) m H).map Subtype.val = m
    rw [hpmap_val H]
  have hofSym_nfactors :
      ∀ s : Sym α n,
        UniqueFactorizationMonoid.normalizedFactors (ofSym s).1.1 = s.1.map Subtype.val := by
    intro s
    dsimp [ofSym]
    let m : Multiset (Ideal (𝓞 K)) := s.1.map Subtype.val
    have hm_prime : ∀ P ∈ m, Prime P := by
      intro P hP
      rcases Multiset.mem_map.1 hP with ⟨Q, hQ, rfl⟩
      have hQ_ne : (Q : Ideal (𝓞 K)) ≠ ⊥ := by
        intro hQ_bot
        have hQ_norm :=
          absNorm_eq_q_pow_localResidueDegree_of_mem_primesOverFinset
            (p := p) (K := K) hq Q.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQ_bot, ← hd] at hQ_norm
        exact pow_ne_zero d q.2.ne_zero hQ_norm.symm
      exact (Ideal.prime_iff_isPrime hQ_ne).2
        ((mem_primesOverFinset_iff (K := K) (ℓ := (q : ℕ))).1 Q.2).1
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
  unfold idealNormMultiplicity
  simpa [β, α, hd, Nat.card_eq_fintype_card] using Nat.card_congr e

lemma dedekind_prime_power_series_eq_localFactor_at_p {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, (idealNormMultiplicity K (p ^ k) : ℂ) *
      (((p ^ k : ℕ) : ℂ) ^ (-s))) =
      (dedekindLocalFactor K p s)⁻¹ := by
  have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    have hle : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
      Complex.norm_prime_cpow_le_one_half ⟨p, hp.out⟩ hs
    exact hle.trans_lt (by norm_num)
  rw [dedekindLocalFactor_at_p]
  trans ∑' k : ℕ, ((p : ℂ) ^ (-s)) ^ k
  · refine tsum_congr fun k => ?_
    rw [idealNormMultiplicity_p_pow_eq_one (p := p) (K := K) k]
    simp only [Nat.cast_one, one_mul]
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul p k (-s), mul_comm,
      Complex.cpow_mul_nat]
  · simpa using tsum_geometric_of_norm_lt_one hnorm

lemma dedekind_prime_power_series_eq_localFactor
  (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {q : Nat.Primes} {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, (idealNormMultiplicity K ((q : ℕ) ^ k) : ℂ) *
      (((q : ℕ) ^ k : ℕ) : ℂ) ^ (-s)) =
      (dedekindLocalFactor K (q : ℕ) s)⁻¹ := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  by_cases hq : (q : ℕ) = p
  · have hq' : q = ⟨p, Fact.out⟩ := by
      apply Subtype.ext
      simpa using hq
    subst hq'
    simpa using dedekind_prime_power_series_eq_localFactor_at_p (p := p) (K := K) hs
  · classical
    set d := localResidueDegree (p := p) (q : ℕ) hq with hd
    let α : Type _ := {P : Ideal (𝓞 K) // P ∈ primesOverFinset K (q : ℕ)}
    letI : Fintype α := Fintype.ofFinset (primesOverFinset K (q : ℕ)) fun P => by
      simp
    let f : ℕ → ℂ := fun k =>
      (idealNormMultiplicity K ((q : ℕ) ^ k) : ℂ) * ((((q : ℕ) ^ k : ℕ) : ℂ) ^ (-s))
    let g : ℕ → ℂ := fun n =>
      (idealNormMultiplicity K ((q : ℕ) ^ (d * n)) : ℂ) *
        ((((q : ℕ) ^ (d * n) : ℕ) : ℂ) ^ (-s))
    let z : ℂ := (q : ℂ) ^ (-((d : ℂ) * s))
    have hd_pos : 0 < d := by
      rw [hd]
      exact orderOf_pos _
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
      rw [show idealNormMultiplicity K ((q : ℕ) ^ (d * n)) = Fintype.card (Sym α n) by
        simpa [α, hd] using
          idealNormMultiplicity_prime_pow_mul_localResidueDegree_eq_card_sym
            (p := p) (K := K) hq n]
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
        have hk_mult : idealNormMultiplicity K ((q : ℕ) ^ k) ≠ 0 := fun hk_zero =>
          hk (by simp [f, hk_zero])
        have hk_dvd : d ∣ k := by
          by_contra hk_ndvd
          exact hk_mult <|
            idealNormMultiplicity_prime_pow_eq_zero_of_not_dvd (p := p) (K := K) hq hk_ndvd
        obtain ⟨n, rfl⟩ := hk_dvd
        refine ⟨⟨n, ?_⟩, rfl⟩
        simpa [f, g, mul_comm] using hk
      · intro x
        simp [f, g, mul_comm]
    have hcard_finset :
        (primesOverFinset K (q : ℕ)).card = localPrimeCount (p := p) (q : ℕ) hq := by
      haveI : (rationalPrimeIdeal (q : ℕ)).IsMaximal :=
        Int.ideal_span_isMaximal_of_prime (q : ℕ)
      have hne : (rationalPrimeIdeal (q : ℕ)) ≠ ⊥ := by
        simp [rationalPrimeIdeal, q.2.ne_zero]
      have hcoe := IsDedekindDomain.coe_primesOverFinset (p := rationalPrimeIdeal (q : ℕ)) hne (𝓞 K)
      have h1 := ncard_primesOver_eq_localPrimeCount (p := p) (K := K) hq
      rw [← hcoe, Set.ncard_coe_finset] at h1
      exact h1
    have hα_card : Fintype.card α = localPrimeCount (p := p) (q : ℕ) hq := by
      calc
        Fintype.card α = (primesOverFinset K (q : ℕ)).card :=
          Fintype.card_of_finset' (primesOverFinset K (q : ℕ)) fun P => by simp
        _ = localPrimeCount (p := p) (q : ℕ) hq := hcard_finset
    have hf_hasSum' : HasSum f ((dedekindLocalFactor K (q : ℕ) s)⁻¹) := by
      rw [dedekindLocalFactor_eq_pow_localResidueDegree (p := p) (K := K) hq, ← inv_pow]
      simpa [z, hd, hα_card] using hf_hasSum
    simpa [f] using hf_hasSum'.tsum_eq

lemma LFunction_eq_prime_tprod_of_localFactors (χ : DirichletCharacter ℂ p) {s : ℂ}
    (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s =
      ∏' q : Nat.Primes, (1 - χ ((q : ℕ) : ZMod p) * ((q : ℕ) : ℂ) ^ (-s))⁻¹ := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.LSeries_eulerProduct_tprod χ hs]

omit hp in
lemma finite_character_product_tprod_swap (f : DirichletCharacter ℂ p → Nat.Primes → ℂ)
    (hmul : ∀ χ : DirichletCharacter ℂ p, Multipliable (f χ)) :
    (∏ χ : DirichletCharacter ℂ p, ∏' q : Nat.Primes, f χ q) =
      ∏' q : Nat.Primes, ∏ χ : DirichletCharacter ℂ p, f χ q :=
  (Multipliable.tprod_finsetProd (fun χ _ => hmul χ)).symm

lemma LProduct_eq_tprod_localFactors {s : ℂ} (hs : 1 < s.re) :
    LProduct (p := p) s =
      ∏' q : Nat.Primes, ∏ χ : DirichletCharacter ℂ p,
        (1 - χ ((q : ℕ) : ZMod p) * ((q : ℕ) : ℂ) ^ (-s))⁻¹ := by
  unfold LProduct
  rw [Finset.prod_congr rfl (fun χ _ => LFunction_eq_prime_tprod_of_localFactors p χ hs)]
  exact finite_character_product_tprod_swap (p := p)
    (fun χ q => (1 - χ ((q : ℕ) : ZMod p) * ((q : ℕ) : ℂ) ^ (-s))⁻¹)
    (fun χ => (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable)

lemma localFactors_agree_prime_ne_p {q : Nat.Primes} (hq : (q : ℕ) ≠ p) {s : ℂ} :
    dedekindLocalFactor K (q : ℕ) s = charLocalFactor (p := p) (q : ℕ) s := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  rw [dedekindLocalFactor_eq_pow_localResidueDegree (p := p) (K := K) hq,
    charLocalFactor_eq_pow_localResidueDegree (p := p) hq]

/-- At the ramified prime `ℓ = p`, the Dedekind local factor `1 - p^{-s}` and
the character local factor `1` differ by exactly `(1 - p^{-s})`: -/
lemma localFactors_agree_at_p {s : ℂ} :
    dedekindLocalFactor K p s = (1 - (p : ℂ) ^ (-s)) * charLocalFactor (p := p) p s := by
  rw [charLocalFactor_at_p, mul_one, dedekindLocalFactor_at_p]

lemma LProduct_eq_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    LProduct (p := p) s =
      ∏' q : Nat.Primes, (charLocalFactor (p := p) (q : ℕ) s)⁻¹ := by
  rw [LProduct_eq_tprod_localFactors p hs]
  refine tprod_congr fun q => ?_
  unfold charLocalFactor
  rw [Finset.prod_inv_distrib]

lemma dedekindZeta_eq_eulerProduct
  (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s =
      ∏' q : Nat.Primes, (dedekindLocalFactor K (q : ℕ) s)⁻¹ := by
  rw [dedekindZeta_eq_tprod_primePowerSeries K hs]
  exact tprod_congr fun _ => dedekind_prime_power_series_eq_localFactor (p := p) (K := K) hs

/-- For `K = ℚ(ζ_p)` with `p` prime, the product of Dirichlet `L`-functions of
all characters mod `p` equals `(1 - p^{-s}) · ζ_K(s)`.

The extra `(1 - p^{-s})` factor arises because `LFunctionTrivChar p s =
(1 - p^{-s}) · ζ(s)` uses the imprimitive convention for the trivial character
mod `p`, whereas the classical `ζ_K(s) = ∏_χ L(s, χ̃)` (Washington Thm 4.3)
uses the *primitive* `L`-function `ζ(s)` for the trivial character. -/
theorem LProduct_eq_one_sub_p_neg_s_mul_dedekindZeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    LProduct (p := p) s = (1 - (p : ℂ) ^ (-s)) * NumberField.dedekindZeta K s := by
  classical
  have hp_prime : Nat.Prime p := hp.out
  set p₀ : Nat.Primes := ⟨p, hp_prime⟩
  have h_mul_cf :
      Multipliable (fun q : Nat.Primes => (charLocalFactor (p := p) (q : ℕ) s)⁻¹) := by
    have h1 : (fun q : Nat.Primes => (charLocalFactor (p := p) (q : ℕ) s)⁻¹) =
        (fun q : Nat.Primes => ∏ χ : DirichletCharacter ℂ p,
          (1 - χ ((q : ℕ) : ZMod p) * ((q : ℕ) : ℂ) ^ (-s))⁻¹) := by
      funext q; unfold charLocalFactor; rw [Finset.prod_inv_distrib]
    rw [h1]
    exact multipliable_prod (s := Finset.univ) fun χ _ =>
      (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  let h : Nat.Primes → ℂ := Pi.mulSingle p₀ ((1 - (p : ℂ) ^ (-s))⁻¹)
  have h_mul_h : Multipliable h := multipliable_of_hasFiniteMulSupport <|
    Set.Finite.subset (Set.finite_singleton p₀) Pi.mulSupport_mulSingle_subset
  have h_pointwise : ∀ q : Nat.Primes,
      (charLocalFactor (p := p) (q : ℕ) s)⁻¹ * h q =
        (dedekindLocalFactor K (q : ℕ) s)⁻¹ := fun q => by
    by_cases hq : q = p₀
    · subst hq
      simp only [h, Pi.mulSingle_eq_same]
      rw [charLocalFactor_at_p, inv_one, one_mul, dedekindLocalFactor_at_p]
    · simp only [h, Pi.mulSingle_eq_of_ne hq, mul_one]
      have hq' : (q : ℕ) ≠ p := fun heq => hq (Subtype.ext heq)
      exact (localFactors_agree_prime_ne_p (p := p) (K := K) hq').symm ▸ rfl
  rw [LProduct_eq_eulerProduct p hs, dedekindZeta_eq_eulerProduct (p := p) (K := K) hs]
  have h_combine : ∏' q : Nat.Primes, (dedekindLocalFactor K (q : ℕ) s)⁻¹ =
      (∏' q : Nat.Primes, (charLocalFactor (p := p) (q : ℕ) s)⁻¹) *
        (1 - (p : ℂ) ^ (-s))⁻¹ := by
    rw [← tprod_pi_single p₀ ((1 - (p : ℂ) ^ (-s))⁻¹),
      ← Multipliable.tprod_mul h_mul_cf h_mul_h]
    exact tprod_congr fun q => (h_pointwise q).symm
  rw [h_combine]
  have h_ne : (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have hpp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
    have hpnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [show ((p : ℂ) ^ (-s)) = ((p : ℝ) : ℂ) ^ (-s) from by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hpp]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp_prime.one_lt)
        (by simp only [Complex.neg_re]; linarith)
    rw [← heq, norm_one] at hpnorm
    exact lt_irrefl 1 hpnorm
  field_simp

lemma LProduct_eq_trivial_mul_nontrivial {s : ℂ} :
    LProduct (p := p) s =
      DirichletCharacter.LFunctionTrivChar p s * nontrivialLProduct p s := by
  classical
  unfold LProduct nontrivialLProduct
  rw [show nontrivialCharacters (p := p) = Finset.univ.erase 1 from rfl,
    ← Finset.mul_prod_erase Finset.univ (fun χ => DirichletCharacter.LFunction χ s)
      (Finset.mem_univ 1)]

lemma nontrivialLProduct_eq_even_mul_odd {s : ℂ} :
    nontrivialLProduct p s = evenLProduct p s * oddLProduct p s := by
  classical
  unfold nontrivialLProduct evenLProduct oddLProduct
    nontrivialCharacters evenNontrivialCharacters oddCharacters
  have hdisj : Disjoint
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even ∧ χ ≠ 1)
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Odd) := by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχe hχo
    rw [Finset.mem_filter] at hχe hχo
    exact DirichletCharacter.Odd.not_even χ hχo.2 hχe.2.1
  have hunion : Finset.univ.erase (1 : DirichletCharacter ℂ p) =
      Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even ∧ χ ≠ 1) ∪
        Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd) := by
    ext χ
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      and_true, true_and]
    refine ⟨fun hne => ?_, ?_⟩
    · rcases DirichletCharacter.even_or_odd χ with he | ho
      · exact Or.inl ⟨he, hne⟩
      · exact Or.inr ho
    · rintro (⟨_, hne⟩ | ho)
      · exact hne
      · rintro rfl
        exact DirichletCharacter.Odd.not_even _ ho (by
          change (1 : DirichletCharacter ℂ p) (-1) = 1
          rw [MulChar.one_apply (isUnit_one.neg)])
  rw [hunion, Finset.prod_union hdisj]

/-- The classical Washington Thm 4.3 formula: `ζ_K(s) = ζ(s) · ∏_{χ≠1} L(s, χ)`
for `K = ℚ(ζ_p)`. -/
theorem dedekindZeta_eq_riemannZeta_mul_nontrivialLProduct_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    NumberField.dedekindZeta K s = riemannZeta s * nontrivialLProduct p s := by
  have hs_ne : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have h1 : LProduct (p := p) s = (1 - (p : ℂ) ^ (-s)) * NumberField.dedekindZeta K s :=
    LProduct_eq_one_sub_p_neg_s_mul_dedekindZeta_of_one_lt_re p K hs
  have h2 : LProduct (p := p) s =
      (1 - (p : ℂ) ^ (-s)) * (riemannZeta s * nontrivialLProduct p s) := by
    rw [LProduct_eq_trivial_mul_nontrivial p, LFunction_trivial_eq_mul_riemannZeta p hs_ne,
      mul_assoc]
  have hne : (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have hpp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
    have hpnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [show ((p : ℂ) ^ (-s)) = ((p : ℝ) : ℂ) ^ (-s) from by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hpp]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.out.one_lt)
        (by simp; linarith)
    rw [← heq, norm_one] at hpnorm
    exact lt_irrefl 1 hpnorm
  exact mul_left_cancel₀ hne (h1.symm.trans h2)

theorem dedekindZeta_eq_even_odd_split_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s = riemannZeta s * evenLProduct p s * oddLProduct p s := by
  rw [dedekindZeta_eq_riemannZeta_mul_nontrivialLProduct_of_one_lt_re p K hs,
    nontrivialLProduct_eq_even_mul_odd p, ← mul_assoc]

end ZetaFactorisation

end BernoulliRegular
