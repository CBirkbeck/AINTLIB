module

public import BernoulliRegular.ImaginaryQuadratic.CN05.Alpha

@[expose] public section

noncomputable section

open Complex NumberField

namespace BernoulliRegular

section CN05_statement

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Inert case, odd k**: `idealNormMultiplicity (Kminus p) (q^k) = 0` for odd k
when `q` is inert. Reason: the unique prime has norm `q²`, so ideals of norm `q^k`
only exist for even `k`. -/
theorem idealNormMultiplicity_at_q_inert_odd (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p)
    (h_not_sq : ∀ s : ZMod q, s ^ 2 ≠ -(p : ZMod q))
    {k : ℕ} (hk_odd : Odd k) :
    idealNormMultiplicity (Kminus p) (q ^ k) = 0 := by
  classical
  have hne : (Ideal.span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  haveI : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime q
  -- Extract the unique prime above q.
  have h_set_card := ncard_primesOver_at_q_inert p hp3 q hq_odd hqp h_not_sq
  rw [Set.ncard_eq_one] at h_set_card
  obtain ⟨P, hP_eq_set⟩ := h_set_card
  have hP_mem : P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)) := by
    rw [hP_eq_set]; rfl
  have hP_ne : P ≠ ⊥ := by
    intro hP_bot
    have hunder := hP_mem.2
    rw [Ideal.liesOver_iff, Ideal.under_def, hP_bot,
      Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 (Kminus p)))
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 (Kminus p)))] at hunder
    exact hne hunder
  haveI : P.IsPrime := hP_mem.1
  haveI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP_ne hP_mem.1
  haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := hP_mem.2
  have habsNormP : Ideal.absNorm P = q ^ 2 :=
    absNorm_primeOver_at_q_inert p hp3 q hq_odd hqp h_not_sq P hP_mem
  -- Show the set {I : NonzeroIdeal (Kminus p) // absNorm I = q^k} is empty.
  unfold idealNormMultiplicity
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
  -- Show any such I would give a contradiction to k being odd.
  -- I decomposes via eq_prime_pow_mul_coprime.
  obtain ⟨Q, hPQ, hIeq⟩ := Ideal.eq_prime_pow_mul_coprime hI_ne P
  -- Let m = count P in factors of I. Show Q = ⊤ (similar to q = p case).
  let m : ℕ := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors I)
  have hQ_top : Q = ⊤ := by
    by_contra hQ_ne_top
    have hQ_ne : Q ≠ ⊥ := fun hQ_bot ↦ hI_ne (by rw [hIeq, hQ_bot, Ideal.mul_bot])
    have hnf_ne : UniqueFactorizationMonoid.normalizedFactors Q ≠ 0 := by
      intro hnf
      apply hQ_ne_top
      rw [← Ideal.prod_normalizedFactors_eq_self hQ_ne, hnf]; simp
    obtain ⟨R, hRmem⟩ := Multiset.exists_mem_of_ne_zero hnf_ne
    have hRfac := (Ideal.mem_normalizedFactors_iff hQ_ne).1 hRmem
    have hRprime : R.IsPrime := hRfac.1
    have hQ_le_R : Q ≤ R := hRfac.2
    haveI : R.IsPrime := hRprime
    have hR_ne : R ≠ ⊥ :=
      fun hR_bot ↦ hQ_ne (le_bot_iff.mp (hQ_le_R.trans_eq hR_bot))
    haveI : NeZero R := ⟨hR_ne⟩
    have hI_le_Q : I ≤ Q := by rw [hIeq]; exact Ideal.mul_le_left
    have hR_dvd_I : Ideal.absNorm R ∣ q ^ k := by
      rw [← hI_norm]
      exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ_le_R)
        (Ideal.absNorm_dvd_absNorm_of_le hI_le_Q)
    have hunder_dvd : Ideal.absNorm (Ideal.under ℤ R) ∣ q ^ k :=
      dvd_trans (Int.absNorm_under_dvd_absNorm R) hR_dvd_I
    have hunder_prime : (Ideal.absNorm (Ideal.under ℤ R)).Prime :=
      Nat.absNorm_under_prime R
    have hunder_dvd_q : Ideal.absNorm (Ideal.under ℤ R) ∣ q :=
      hunder_prime.dvd_of_dvd_pow hunder_dvd
    have hunder_eq_q : Ideal.absNorm (Ideal.under ℤ R) = q :=
      (Nat.prime_dvd_prime_iff_eq hunder_prime (Fact.out : q.Prime)).1 hunder_dvd_q
    have hunder_eq_span_q : Ideal.under ℤ R = Ideal.span {(q : ℤ)} := by
      rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ R)]; simp [hunder_eq_q]
    have hR_lies : R.LiesOver (Ideal.span {(q : ℤ)}) := by
      rw [Ideal.liesOver_iff, hunder_eq_span_q]
    have hR_mem_set : R ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)) :=
      ⟨hRprime, hR_lies⟩
    have hR_eq_P : R = P := by rw [hP_eq_set] at hR_mem_set; exact hR_mem_set
    have hQ_le_P : Q ≤ P := by simpa [hR_eq_P] using hQ_le_R
    have htop_le_P : (⊤ : Ideal (𝓞 (Kminus p))) ≤ P :=
      calc ⊤ = P ⊔ Q := hPQ.symm
        _ ≤ P := sup_le le_rfl hQ_le_P
    exact hP_mem.1.ne_top (top_le_iff.mp htop_le_P)
  -- Now I = P^m.
  have hI_pow : I = P ^ m := by simpa [m, hQ_top] using hIeq
  -- absNorm I = q^(2m) = q^k. Since q prime, k = 2m (even).
  have hI_norm_val : Ideal.absNorm I = q ^ k := hI_norm
  have hI_norm_eq : q ^ (2 * m) = q ^ k := by
    have := hI_norm_val
    rw [hI_pow, map_pow, habsNormP, ← pow_mul] at this
    exact this
  have hq_gt_one : 1 < q := (Fact.out : q.Prime).one_lt
  have h_k_eq : 2 * m = k := Nat.pow_right_injective hq_gt_one hI_norm_eq
  -- But k is odd. Contradiction.
  have : Even k := ⟨m, by omega⟩
  exact (Nat.not_even_iff_odd.mpr hk_odd) this

/-- In the split case at `q ≠ p, 2`, both primes above q have inertiaDeg = 1. -/
theorem inertiaDeg_at_q_split (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p) {r : ZMod q} (hr : r ^ 2 = -(p : ZMod q))
    (P : Ideal (𝓞 (Kminus p)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p))) :
    (Ideal.span {(q : ℤ)}).inertiaDeg P = 1 := by
  classical
  have h_exp : ¬ (q : ℕ) ∣ RingOfIntegers.exponent (alphaInOK p hp3) :=
    not_dvd_exponent_alphaInOK p hp3 q
  set e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := Kminus p) h_exp
  -- P corresponds to one of the 2 linear factors, both having natDegree 1.
  set P_sub : ↥(Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p))) := ⟨P, hP⟩
  set Qfactor := (e P_sub : Polynomial (ZMod q))
  have hQ_mem : Qfactor ∈ RingOfIntegers.monicFactorsMod (alphaInOK p hp3) q :=
    (e P_sub).prop
  have hP_from : P = (e.symm ⟨Qfactor, hQ_mem⟩ : Ideal (𝓞 (Kminus p))) := by
    have : e.symm ⟨Qfactor, hQ_mem⟩ = P_sub := by
      change e.symm (e P_sub) = P_sub
      exact e.symm_apply_apply P_sub
    change (P_sub : Ideal (𝓞 (Kminus p))) = _
    rw [this]
  rw [hP_from]
  rw [NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      h_exp hQ_mem]
  -- Qfactor is one of the two linear factors {X - Cu, X - Cv}, so natDegree = 1.
  rw [monicFactorsMod_alpha_at_q_split p hp3 q hq_odd hqp hr] at hQ_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hQ_mem
  rcases hQ_mem with hQ | hQ
  · simpa [hQ] using
      (Polynomial.natDegree_X_sub_C ((1 + r) * (2 : ZMod q)⁻¹) :
        (Polynomial.X - Polynomial.C ((1 + r) * (2 : ZMod q)⁻¹) :
          Polynomial (ZMod q)).natDegree = 1)
  · simpa [hQ] using
      (Polynomial.natDegree_X_sub_C ((1 - r) * (2 : ZMod q)⁻¹) :
        (Polynomial.X - Polynomial.C ((1 - r) * (2 : ZMod q)⁻¹) :
          Polynomial (ZMod q)).natDegree = 1)

/-- In the split case at `q ≠ p, 2`, each prime above q has absNorm = q. -/
theorem absNorm_primeOver_at_q_split (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p) {r : ZMod q} (hr : r ^ 2 = -(p : ZMod q))
    (P : Ideal (𝓞 (Kminus p)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p))) :
    Ideal.absNorm P = q := by
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := hP.2
  have h_ine : (Ideal.span {(q : ℤ)}).inertiaDeg P = 1 :=
    inertiaDeg_at_q_split p hp3 q hq_odd hqp hr P hP
  calc Ideal.absNorm P
      = q ^ ((Ideal.span {(q : ℤ)}).inertiaDeg P) :=
        Ideal.absNorm_eq_pow_inertiaDeg' P (Fact.out : q.Prime)
    _ = q ^ (1 : ℕ) := by rw [h_ine]
    _ = q := pow_one q

/-- **Inert case, even k**: `idealNormMultiplicity (Kminus p) (q^(2m)) = 1` when `q`
is inert, with the unique ideal of norm `q^(2m)` being `𝔮^m`. -/
theorem idealNormMultiplicity_at_q_inert_even (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p)
    (h_not_sq : ∀ s : ZMod q, s ^ 2 ≠ -(p : ZMod q))
    (m : ℕ) :
    idealNormMultiplicity (Kminus p) (q ^ (2 * m)) = 1 := by
  classical
  have hne : (Ideal.span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  haveI : (Ideal.span {(q : ℤ)} : Ideal ℤ).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime q
  have h_set_card := ncard_primesOver_at_q_inert p hp3 q hq_odd hqp h_not_sq
  rw [Set.ncard_eq_one] at h_set_card
  obtain ⟨P, hP_eq_set⟩ := h_set_card
  have hP_mem : P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)) := by
    rw [hP_eq_set]; rfl
  have hP_ne : P ≠ ⊥ := by
    intro hP_bot
    have hunder := hP_mem.2
    rw [Ideal.liesOver_iff, Ideal.under_def, hP_bot,
      Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 (Kminus p)))
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 (Kminus p)))] at hunder
    exact hne hunder
  haveI : P.IsPrime := hP_mem.1
  haveI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP_ne hP_mem.1
  haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := hP_mem.2
  have habsNormP : Ideal.absNorm P = q ^ 2 :=
    absNorm_primeOver_at_q_inert p hp3 q hq_odd hqp h_not_sq P hP_mem
  have hq_gt_one : 1 < q := (Fact.out : q.Prime).one_lt
  unfold idealNormMultiplicity
  haveI : Unique {I : NonzeroIdeal (Kminus p) // Ideal.absNorm I.1 = q ^ (2 * m)} :=
    { default := ⟨⟨P ^ m, pow_ne_zero m hP_ne⟩, by
          rw [map_pow, habsNormP, ← pow_mul]⟩
      uniq := by
        rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
        obtain ⟨Q, hPQ, hIeq⟩ := Ideal.eq_prime_pow_mul_coprime hI_ne P
        let mI : ℕ := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors I)
        have hQ_top : Q = ⊤ := by
          by_contra hQ_ne_top
          have hQ_ne : Q ≠ ⊥ := fun hQ_bot ↦ hI_ne (by rw [hIeq, hQ_bot, Ideal.mul_bot])
          have hnf_ne : UniqueFactorizationMonoid.normalizedFactors Q ≠ 0 := by
            intro hnf
            apply hQ_ne_top
            rw [← Ideal.prod_normalizedFactors_eq_self hQ_ne, hnf]; simp
          obtain ⟨R, hRmem⟩ := Multiset.exists_mem_of_ne_zero hnf_ne
          have hRfac := (Ideal.mem_normalizedFactors_iff hQ_ne).1 hRmem
          have hRprime : R.IsPrime := hRfac.1
          have hQ_le_R : Q ≤ R := hRfac.2
          haveI : R.IsPrime := hRprime
          have hR_ne : R ≠ ⊥ :=
            fun hR_bot ↦ hQ_ne (le_bot_iff.mp (hQ_le_R.trans_eq hR_bot))
          haveI : NeZero R := ⟨hR_ne⟩
          have hI_le_Q : I ≤ Q := by rw [hIeq]; exact Ideal.mul_le_left
          have hR_dvd_I : Ideal.absNorm R ∣ q ^ (2 * m) := by
            rw [← hI_norm]
            exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ_le_R)
              (Ideal.absNorm_dvd_absNorm_of_le hI_le_Q)
          have hunder_dvd : Ideal.absNorm (Ideal.under ℤ R) ∣ q ^ (2 * m) :=
            dvd_trans (Int.absNorm_under_dvd_absNorm R) hR_dvd_I
          have hunder_prime : (Ideal.absNorm (Ideal.under ℤ R)).Prime :=
            Nat.absNorm_under_prime R
          have hunder_dvd_q : Ideal.absNorm (Ideal.under ℤ R) ∣ q :=
            hunder_prime.dvd_of_dvd_pow hunder_dvd
          have hunder_eq_q : Ideal.absNorm (Ideal.under ℤ R) = q :=
            (Nat.prime_dvd_prime_iff_eq hunder_prime (Fact.out : q.Prime)).1 hunder_dvd_q
          have hunder_eq_span_q : Ideal.under ℤ R = Ideal.span {(q : ℤ)} := by
            rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ R)]; simp [hunder_eq_q]
          have hR_lies : R.LiesOver (Ideal.span {(q : ℤ)}) := by
            rw [Ideal.liesOver_iff, hunder_eq_span_q]
          have hR_mem_set : R ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)) :=
            ⟨hRprime, hR_lies⟩
          have hR_eq_P : R = P := by rw [hP_eq_set] at hR_mem_set; exact hR_mem_set
          have hQ_le_P : Q ≤ P := by simpa [hR_eq_P] using hQ_le_R
          have htop_le_P : (⊤ : Ideal (𝓞 (Kminus p))) ≤ P :=
            calc ⊤ = P ⊔ Q := hPQ.symm
              _ ≤ P := sup_le le_rfl hQ_le_P
          exact hP_mem.1.ne_top (top_le_iff.mp htop_le_P)
        have hI_pow : I = P ^ mI := by simpa [mI, hQ_top] using hIeq
        have hmI_eq : mI = m := by
          have hI_norm_val : Ideal.absNorm I = q ^ (2 * m) := hI_norm
          have : q ^ (2 * mI) = q ^ (2 * m) := by
            rw [hI_pow, map_pow, habsNormP, ← pow_mul] at hI_norm_val
            ring_nf at hI_norm_val ⊢
            exact hI_norm_val
          have := Nat.pow_right_injective hq_gt_one this
          omega
        refine Subtype.ext (Subtype.ext ?_)
        simpa [mI, hmI_eq] using hI_pow }
  exact Nat.card_unique

/-- For `p ≡ 3 (mod 4)` prime and `q` odd prime ≠ p, `legendreDirichletNat p q = 1`
iff `q` is a QR mod p. -/
lemma legendreDirichletNat_eq_one_iff_isSquare (q : ℕ) [hq : Fact q.Prime] (hqp : q ≠ p) :
    legendreDirichletNat p q = 1 ↔ IsSquare ((q : ℕ) : ZMod p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hq_ne : ((q : ℕ) : ZMod p) ≠ 0 := by
    intro h_zero
    have hp_dvd : (p : ℕ) ∣ q := (ZMod.natCast_eq_zero_iff q p).mp h_zero
    rcases (Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp hp_dvd with h
    exact hqp h.symm
  change legendreDirichlet p ((q : ℕ) : ZMod p) = 1 ↔ _
  rw [legendreDirichlet_apply]
  have h_iff : ((quadraticChar (ZMod p) ((q : ℕ) : ZMod p) : ℤ) : ℂ) = 1 ↔
      quadraticChar (ZMod p) ((q : ℕ) : ZMod p) = 1 := by
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; simp⟩
    have : (quadraticChar (ZMod p) ((q : ℕ) : ZMod p) : ℤ) = 1 := by exact_mod_cast h
    exact this
  rw [h_iff]
  exact quadraticChar_one_iff_isSquare hq_ne

/-- For `p ≡ 3 (mod 4)` prime and `q` odd prime ≠ p, `legendreDirichletNat p q = -1`
iff `q` is NOT a QR mod p. -/
lemma legendreDirichletNat_eq_neg_one_iff_not_isSquare (q : ℕ) [hq : Fact q.Prime]
    (hqp : q ≠ p) :
    legendreDirichletNat p q = -1 ↔ ¬ IsSquare ((q : ℕ) : ZMod p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hq_ne : ((q : ℕ) : ZMod p) ≠ 0 := by
    intro h_zero
    have hp_dvd : (p : ℕ) ∣ q := (ZMod.natCast_eq_zero_iff q p).mp h_zero
    rcases (Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp hp_dvd with h
    exact hqp h.symm
  change legendreDirichlet p ((q : ℕ) : ZMod p) = -1 ↔ _
  rw [legendreDirichlet_apply]
  have h_iff : ((quadraticChar (ZMod p) ((q : ℕ) : ZMod p) : ℤ) : ℂ) = -1 ↔
      quadraticChar (ZMod p) ((q : ℕ) : ZMod p) = -1 := by
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; simp⟩
    have : (quadraticChar (ZMod p) ((q : ℕ) : ZMod p) : ℤ) = -1 := by exact_mod_cast h
    exact this
  rw [h_iff]
  exact quadraticChar_neg_one_iff_not_isSquare

/-- **QR linkage**: for `p ≡ 3 (mod 4)` prime and `q` odd prime ≠ p,
`IsSquare (-(p : ZMod q)) ↔ IsSquare ((q : ZMod p))`. -/
lemma isSquare_neg_p_iff_isSquare_q (hp3 : p % 4 = 3) (q : ℕ) [hq : Fact q.Prime]
    (hq_odd : q ≠ 2) (hqp : q ≠ p) :
    IsSquare (-(p : ZMod q)) ↔ IsSquare ((q : ℕ) : ZMod p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  have hp_odd : p ≠ 2 := by omega
  -- Use legendreSym values.
  -- legendreSym q (-p) = quadraticChar (ZMod q) (-p : ZMod q)
  -- legendreSym p q = quadraticChar (ZMod p) (q : ZMod p)
  -- We'll show legendreSym q (-p) = legendreSym p q via QR + (-1/q) calculation.
  have hneg_p_ne : (-(p : ZMod q)) ≠ 0 := by
    intro h_zero
    rw [neg_eq_zero] at h_zero
    have hq_dvd : (q : ℕ) ∣ p := (ZMod.natCast_eq_zero_iff p q).mp h_zero
    rcases (Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp hq_dvd with h
    exact hqp h
  have hq_ne : ((q : ℕ) : ZMod p) ≠ 0 := by
    intro h_zero
    have hp_dvd : (p : ℕ) ∣ q := (ZMod.natCast_eq_zero_iff q p).mp h_zero
    rcases (Nat.prime_dvd_prime_iff_eq hp.out hq.out).mp hp_dvd with h
    exact hqp h.symm
  -- Convert IsSquare to quadraticChar via _iff lemma.
  rw [← quadraticChar_one_iff_isSquare hneg_p_ne, ← quadraticChar_one_iff_isSquare hq_ne]
  -- Now show quadraticChar (ZMod q) (-p) = quadraticChar (ZMod p) q.
  -- legendreSym q (-p : ℤ) = quadraticChar (ZMod q) ((-p : ℤ) : ZMod q) = qc(-p)
  -- legendreSym p (q : ℤ) = quadraticChar (ZMod p) ((q : ℤ) : ZMod p) = qc(q)
  have h_L_neg_p : legendreSym q (-(p : ℤ)) = quadraticChar (ZMod q) (-(p : ZMod q)) := by
    unfold legendreSym
    congr 1; push_cast; rfl
  have h_L_q : legendreSym p (q : ℤ) = quadraticChar (ZMod p) ((q : ℕ) : ZMod p) := by
    unfold legendreSym
    congr 1; push_cast; rfl
  -- The target: `quadraticChar (ZMod q) (-(p : ZMod q)) = 1`
  -- iff `quadraticChar (ZMod p) (q : ZMod p) = 1`.
  -- This follows if legendreSym q (-p) = legendreSym p q.
  have h_QR : legendreSym q (-(p : ℤ)) = legendreSym p (q : ℤ) := by
    -- legendreSym q (-p) = legendreSym q (-1) * legendreSym q p.
    have h_mul : legendreSym q (-(p : ℤ)) = legendreSym q (-1 : ℤ) * legendreSym q (p : ℤ) := by
      rw [show (-(p : ℤ)) = (-1 : ℤ) * (p : ℤ) from by ring]
      exact map_mul (legendreSym.hom q) _ _
    rw [h_mul]
    -- Compute legendreSym q (-1) based on q mod 4.
    rw [legendreSym.at_neg_one hq_odd]
    -- q is odd prime, so q % 4 ∈ {1, 3}.
    have hq_mod_2 : q % 2 = 1 := by
      rcases Nat.Prime.eq_two_or_odd hq.out with h | h
      · exact absurd h hq_odd
      · exact h
    have hq_mod_4_lt : q % 4 < 4 := Nat.mod_lt _ (by decide)
    have hq_mod_options : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rcases hq_mod_options with hq_mod | hq_mod
    · rw [ZMod.χ₄_nat_one_mod_four hq_mod, one_mul]
      exact (@legendreSym.quadratic_reciprocity_one_mod_four q p _ _ hq_mod hp_odd).symm
    · rw [ZMod.χ₄_nat_three_mod_four hq_mod,
        @legendreSym.quadratic_reciprocity_three_mod_four q p _ _ hq_mod hp3]
      ring
  -- Combine: qc(-p : ZMod q) = legendreSym q (-p) = legendreSym p q = qc(q : ZMod p).
  have h_eq :
      quadraticChar (ZMod q) (-(p : ZMod q)) =
        quadraticChar (ZMod p) ((q : ℕ) : ZMod p) := by
    rw [← h_L_neg_p, ← h_L_q]; exact h_QR
  rw [h_eq]

theorem CN05CoeffEq_at_prime_pow_inert (hp3 : p % 4 = 3) (q : ℕ) [Fact q.Prime]
    (hq_odd : q ≠ 2) (hqp : q ≠ p)
    (h_not_sq : ∀ s : ZMod q, s ^ 2 ≠ -(p : ZMod q))
    (hη : legendreDirichletNat p q = -1) (k : ℕ) :
    ((idealNormMultiplicity (Kminus p) (q ^ k)) : ℂ) =
      LSeries.convolution (fun _ : ℕ ↦ (1 : ℂ)) (legendreDirichletNat p) (q ^ k) := by
  rw [convolution_one_legendreNat_at_prime_pow_inert p q (Fact.out : q.Prime) k hη]
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨m, hm⟩ := hk
    rw [hm, show m + m = 2 * m from by ring,
      idealNormMultiplicity_at_q_inert_even p hp3 q hq_odd hqp h_not_sq m]
    rw [if_pos ⟨m, by ring⟩]
    simp
  · rw [idealNormMultiplicity_at_q_inert_odd p hp3 q hq_odd hqp h_not_sq hk]
    rw [if_neg (Nat.not_even_iff_odd.mpr hk)]
    simp

/-- **CN-05 at q odd ≠ p inert** (only η hypothesis via QR): LHS = RHS when
`η(q) = -1`, with the no-QR condition derived from QR. -/
theorem CN05CoeffEq_at_prime_pow_inert_via_eta (hp3 : p % 4 = 3) (q : ℕ)
    [hq : Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p)
    (hη : legendreDirichletNat p q = -1) (k : ℕ) :
    ((idealNormMultiplicity (Kminus p) (q ^ k)) : ℂ) =
      LSeries.convolution (fun _ : ℕ ↦ (1 : ℂ)) (legendreDirichletNat p) (q ^ k) := by
  -- η(q) = -1 ⟺ ¬ IsSquare (q : ZMod p) ⟺ ¬ IsSquare (-p : ZMod q) via QR.
  have h_not_sq_q_p : ¬ IsSquare ((q : ℕ) : ZMod p) :=
    (legendreDirichletNat_eq_neg_one_iff_not_isSquare p q hqp).mp hη
  have h_not_sq : ¬ IsSquare (-(p : ZMod q)) :=
    fun h ↦ h_not_sq_q_p ((isSquare_neg_p_iff_isSquare_q p hp3 q hq_odd hqp).mp h)
  have h_not_sq_all : ∀ s : ZMod q, s ^ 2 ≠ -(p : ZMod q) :=
    fun s h_sq_eq ↦ h_not_sq ⟨s, by rw [← h_sq_eq]; ring⟩
  exact CN05CoeffEq_at_prime_pow_inert p hp3 q hq_odd hqp h_not_sq_all hη k

/-- Helper: `P ≠ ⊥` for a prime above `q` in `𝒪 (Kminus p)`. -/
lemma primeOver_ne_bot (q : ℕ) [Fact q.Prime] (P : Ideal (𝓞 (Kminus p)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p))) :
    P ≠ ⊥ := by
  have hne : (Ideal.span {(q : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  intro hP_bot
  have hunder := hP.2
  rw [Ideal.liesOver_iff, Ideal.under_def, hP_bot,
    Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 (Kminus p)))
    (FaithfulSMul.algebraMap_injective ℤ (𝓞 (Kminus p)))] at hunder
  exact hne hunder

/-- In the split case, any prime R of `𝒪 (Kminus p)` with `|R|` dividing `q^k` and
`R ≠ ⊥` must be one of the two primes `P₁, P₂` above `q`. -/
lemma prime_factor_of_q_pow_is_above_q (_hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (_hqp : q ≠ p) {k : ℕ}
    (R : Ideal (𝓞 (Kminus p))) [hR_prime : R.IsPrime] (hR_ne : R ≠ ⊥)
    (hR_dvd : Ideal.absNorm R ∣ q ^ k) :
    R ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)) := by
  haveI : NeZero R := ⟨hR_ne⟩
  have hunder_dvd : Ideal.absNorm (Ideal.under ℤ R) ∣ q ^ k :=
    dvd_trans (Int.absNorm_under_dvd_absNorm R) hR_dvd
  have hunder_prime : (Ideal.absNorm (Ideal.under ℤ R)).Prime :=
    Nat.absNorm_under_prime R
  have hunder_dvd_q : Ideal.absNorm (Ideal.under ℤ R) ∣ q :=
    hunder_prime.dvd_of_dvd_pow hunder_dvd
  have hunder_eq_q : Ideal.absNorm (Ideal.under ℤ R) = q :=
    (Nat.prime_dvd_prime_iff_eq hunder_prime (Fact.out : q.Prime)).1 hunder_dvd_q
  have hunder_eq_span_q : Ideal.under ℤ R = Ideal.span {(q : ℤ)} := by
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ R)]; simp [hunder_eq_q]
  have hR_lies : R.LiesOver (Ideal.span {(q : ℤ)}) := by
    rw [Ideal.liesOver_iff, hunder_eq_span_q]
  exact ⟨hR_prime, hR_lies⟩

/-- For an odd prime `p`, `(2 : ZMod p) ≠ 0`. -/
lemma two_ne_zero_in_ZMod_p (hp_odd : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h2_zero
  have hp_dvd : (p : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2_zero)
  have h_prime := hp.out
  have hp_one : 1 < p := h_prime.one_lt
  have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) hp_dvd
  omega

/-- For `p ≡ 3 (mod 4)` prime, `((p+1)/4 : ZMod p) = (1/2)²` (where `1/2 = 2⁻¹`). -/
lemma pSuccDivFour_eq_half_sq_mod_p (hp3 : p % 4 = 3) :
    (((p + 1) / 4 : ℕ) : ZMod p) = ((2 : ZMod p)⁻¹)^2 := by
  have hp_odd : p ≠ 2 := by omega
  have h2_ne : (2 : ZMod p) ≠ 0 := two_ne_zero_in_ZMod_p p hp_odd
  have h_lhs : (4 : ZMod p) * (((p + 1) / 4 : ℕ) : ZMod p) = 1 :=
    four_mul_pSuccDivFour_eq_one_mod_p p hp3
  have h4_ne : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2_ne h2_ne
  have h_rhs : (4 : ZMod p) * ((2 : ZMod p)⁻¹)^2 = 1 := by
    have h_expand : (4 : ZMod p) * ((2 : ZMod p)⁻¹)^2 =
        ((2 : ZMod p) * (2 : ZMod p)⁻¹) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) := by
      have : (4 : ZMod p) = 2 * 2 := by norm_num
      rw [this, sq]
      ring
    rw [h_expand, mul_inv_cancel₀ h2_ne, mul_one]
  rw [← h_rhs] at h_lhs
  exact mul_left_cancel₀ h4_ne h_lhs

/-- For `p` an odd prime, `X - C (2⁻¹)` is irreducible in `(ZMod p)[X]`. -/
lemma irreducible_X_sub_C_half (_hp_odd : p ≠ 2) :
    Irreducible (Polynomial.X - Polynomial.C ((2 : ZMod p)⁻¹) : Polynomial (ZMod p)) :=
  Polynomial.irreducible_X_sub_C _

/-- For `p ≡ 3 (mod 4)` prime, the reduction of `minpoly α mod p` factors as `(X - 2⁻¹)²`. -/
theorem alphaInOK_minpoly_factor_mod_p (hp3 : p % 4 = 3) :
    Polynomial.map (Int.castRingHom (ZMod p)) (minpoly ℤ (alphaInOK p hp3)) =
      (Polynomial.X - Polynomial.C ((2 : ZMod p)⁻¹))^2 := by
  have hp_odd : p ≠ 2 := by omega
  have h2_ne : (2 : ZMod p) ≠ 0 := two_ne_zero_in_ZMod_p p hp_odd
  have h2_inv_mul : (2 : ZMod p)⁻¹ * (2 : ZMod p) = 1 := inv_mul_cancel₀ h2_ne
  rw [alphaInOK_minpoly_int_mod_q p hp3 p, pSuccDivFour_eq_half_sq_mod_p p hp3]
  -- Simplify: 2⁻¹ · 2 = 1 and C(a²) = (C a)² at the polynomial level.
  have h2_mul : (Polynomial.C ((2 : ZMod p)⁻¹) * (2 : Polynomial (ZMod p))) =
      (1 : Polynomial (ZMod p)) := by
    have h2 : (2 : Polynomial (ZMod p)) = Polynomial.C (2 : ZMod p) :=
      (Polynomial.C_eq_natCast 2).symm
    rw [h2, ← Polynomial.C_mul, h2_inv_mul, Polynomial.C_1]
  have h_C_sq : Polynomial.C (((2 : ZMod p)⁻¹)^2) =
      (Polynomial.C ((2 : ZMod p)⁻¹))^2 := by rw [Polynomial.C_pow]
  linear_combination (Polynomial.X : Polynomial (ZMod p)) * h2_mul + h_C_sq

/-- For `p ≡ 3 (mod 4)` prime, the set of monic irreducible factors of `minpoly α mod p`
is exactly `{X - 2⁻¹}` (a singleton). -/
theorem monicFactorsMod_alpha_at_p (hp3 : p % 4 = 3) :
    RingOfIntegers.monicFactorsMod (alphaInOK p hp3) p =
      {Polynomial.X - Polynomial.C ((2 : ZMod p)⁻¹)} := by
  classical
  unfold RingOfIntegers.monicFactorsMod
  rw [alphaInOK_minpoly_factor_mod_p p hp3,
      UniqueFactorizationMonoid.normalizedFactors_pow]
  have h_irred : Irreducible (Polynomial.X - Polynomial.C ((2 : ZMod p)⁻¹) :
      Polynomial (ZMod p)) := Polynomial.irreducible_X_sub_C _
  have h_monic : (Polynomial.X - Polynomial.C ((2 : ZMod p)⁻¹) :
      Polynomial (ZMod p)).Monic := Polynomial.monic_X_sub_C _
  have h_norm : UniqueFactorizationMonoid.normalizedFactors
      (Polynomial.X - Polynomial.C ((2 : ZMod p)⁻¹) : Polynomial (ZMod p)) =
      {Polynomial.X - Polynomial.C ((2 : ZMod p)⁻¹)} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible h_irred]
    simp [h_monic.normalize_eq_self]
  rw [h_norm]
  simp

/-- For `p ≡ 3 (mod 4)` prime, the number of monic irreducible factors mod p is 1. -/
theorem monicFactorsMod_alpha_at_p_card (hp3 : p % 4 = 3) :
    (RingOfIntegers.monicFactorsMod (alphaInOK p hp3) p).card = 1 := by
  rw [monicFactorsMod_alpha_at_p p hp3]
  simp

/-- For `p ≡ 3 (mod 4)` prime, there is exactly one prime above `p` in `𝒪 (Kminus p)`. -/
theorem ncard_primesOver_at_p (hp3 : p % 4 = 3) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kminus p))).ncard = 1 := by
  classical
  have h_exp : ¬ (p : ℕ) ∣ RingOfIntegers.exponent (alphaInOK p hp3) :=
    not_dvd_exponent_alphaInOK p hp3 p
  have h_equiv :=
    NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := Kminus p) h_exp
  rw [← Nat.card_coe_set_eq, Nat.card_congr h_equiv, Nat.card_eq_finsetCard,
    monicFactorsMod_alpha_at_p_card p hp3]

/-- For `p ≡ 3 (mod 4)` prime, the unique prime above `p` has inertia degree 1. -/
theorem inertiaDeg_at_p (hp3 : p % 4 = 3) (P : Ideal (𝓞 (Kminus p)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kminus p))) :
    (Ideal.span {(p : ℤ)}).inertiaDeg P = 1 := by
  classical
  have h_exp : ¬ (p : ℕ) ∣ RingOfIntegers.exponent (alphaInOK p hp3) :=
    not_dvd_exponent_alphaInOK p hp3 p
  -- P corresponds to the unique factor X - 2⁻¹, which has natDegree 1.
  set e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := Kminus p) h_exp
  set Qfactor : Polynomial (ZMod p) := Polynomial.X - Polynomial.C ((2 : ZMod p)⁻¹)
  have hQ_mem : Qfactor ∈ RingOfIntegers.monicFactorsMod (alphaInOK p hp3) p := by
    rw [monicFactorsMod_alpha_at_p p hp3]; exact Finset.mem_singleton.mpr rfl
  have hP_eq : P = (e.symm ⟨Qfactor, hQ_mem⟩ : Ideal (𝓞 (Kminus p))) := by
    -- Since there's only one prime, both are equal.
    have h_sub : Subsingleton ↥(Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kminus p))) := by
      have h_card := ncard_primesOver_at_p p hp3
      rw [Set.ncard_eq_one] at h_card
      obtain ⟨x, hx⟩ := h_card
      refine ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ?_⟩
      have ha_eq : a = x := by rw [hx] at ha; exact ha
      have hb_eq : b = x := by rw [hx] at hb; exact hb
      subst ha_eq; subst hb_eq; rfl
    have hP_set : (⟨P, hP⟩ : ↥(Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kminus p)))) =
                  e.symm ⟨Qfactor, hQ_mem⟩ := h_sub.elim _ _
    exact congrArg (fun (x : ↥(Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kminus p)))) ↦
      (x : Ideal (𝓞 (Kminus p)))) hP_set
  rw [hP_eq]
  -- Apply the inertiaDeg formula from Kummer-Dedekind.
  -- Qfactor = Polynomial.map (Int.castRingHom (ZMod p)) (X - C 2⁻¹ lifted to ℤ[X])
  -- For cleanliness, we use the ZMod version of the lemma.
  rw [NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      h_exp hQ_mem]
  -- Goal: natDegree (X - C (2⁻¹)) = 1
  exact Polynomial.natDegree_X_sub_C _

/-- Ideal norm of the unique prime above `p` in `𝒪 (Kminus p)` is `p`. -/
theorem absNorm_primeOver_at_p (hp3 : p % 4 = 3) (P : Ideal (𝓞 (Kminus p)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kminus p))) :
    Ideal.absNorm P = p := by
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  have h_ine : (Ideal.span {(p : ℤ)}).inertiaDeg P = 1 := inertiaDeg_at_p p hp3 P hP
  calc Ideal.absNorm P
      = p ^ ((Ideal.span {(p : ℤ)}).inertiaDeg P) := Ideal.absNorm_eq_pow_inertiaDeg' P hp.out
    _ = p ^ (1 : ℕ) := by rw [h_ine]
    _ = p := pow_one p

/-- For `p ≡ 3 (mod 4)` prime, `idealNormMultiplicity (Kminus p) (p^k) = 1`.
Proof: there's exactly one prime `𝔭` above `p` (with |𝒪/𝔭| = p), and every
ideal of norm `p^k` is `𝔭^k`. -/
theorem idealNormMultiplicity_at_p_eq_one (hp3 : p % 4 = 3) (k : ℕ) :
    idealNormMultiplicity (Kminus p) (p ^ k) = 1 := by
  classical
  have hne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  haveI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  -- Extract the unique prime above p.
  have h_set_card := ncard_primesOver_at_p p hp3
  rw [Set.ncard_eq_one] at h_set_card
  obtain ⟨P, hP_eq_set⟩ := h_set_card
  have hP_mem : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kminus p)) := by
    rw [hP_eq_set]; rfl
  have hP_ne : P ≠ ⊥ := by
    intro hP_bot
    have hunder := hP_mem.2
    rw [Ideal.liesOver_iff, Ideal.under_def, hP_bot,
      Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 (Kminus p)))
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 (Kminus p)))] at hunder
    exact hne hunder
  haveI : P.IsPrime := hP_mem.1
  haveI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP_ne hP_mem.1
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hP_mem.2
  have habsNormP : Ideal.absNorm P = p := absNorm_primeOver_at_p p hp3 P hP_mem
  unfold idealNormMultiplicity
  haveI : Unique {I : NonzeroIdeal (Kminus p) // Ideal.absNorm I.1 = p ^ k} :=
    { default := ⟨⟨P ^ k, pow_ne_zero k hP_ne⟩, by rw [map_pow, habsNormP]⟩
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
          have hR_ne : R ≠ ⊥ := fun hR_bot ↦
            hQ_ne (le_bot_iff.mp (hQ_le_R.trans_eq hR_bot))
          haveI : NeZero R := ⟨hR_ne⟩
          have hI_le_Q : I ≤ Q := by
            rw [hIeq]; exact Ideal.mul_le_left
          have hR_dvd_I : Ideal.absNorm R ∣ p ^ k := by
            rw [← hI_norm]
            exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ_le_R)
              (Ideal.absNorm_dvd_absNorm_of_le hI_le_Q)
          have hunder_dvd : Ideal.absNorm (Ideal.under ℤ R) ∣ p ^ k :=
            dvd_trans (Int.absNorm_under_dvd_absNorm R) hR_dvd_I
          have hunder_prime : (Ideal.absNorm (Ideal.under ℤ R)).Prime :=
            Nat.absNorm_under_prime R
          have hunder_dvd_p : Ideal.absNorm (Ideal.under ℤ R) ∣ p :=
            hunder_prime.dvd_of_dvd_pow hunder_dvd
          have hunder_eq_p : Ideal.absNorm (Ideal.under ℤ R) = p :=
            (Nat.prime_dvd_prime_iff_eq hunder_prime hp.out).1 hunder_dvd_p
          have hunder_eq_span_p : Ideal.under ℤ R = Ideal.span {(p : ℤ)} := by
            rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ R)]
            simp [hunder_eq_p]
          have hR_lies : R.LiesOver (Ideal.span {(p : ℤ)}) := by
            rw [Ideal.liesOver_iff, hunder_eq_span_p]
          have hR_mem_set : R ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Kminus p)) :=
            ⟨hRprime, hR_lies⟩
          have hR_eq_P : R = P := by
            rw [hP_eq_set] at hR_mem_set
            exact hR_mem_set
          have hQ_le_P : Q ≤ P := by simpa [hR_eq_P] using hQ_le_R
          have htop_le_P : (⊤ : Ideal (𝓞 (Kminus p))) ≤ P := by
            calc ⊤ = P ⊔ Q := hPQ.symm
              _ ≤ P := sup_le le_rfl hQ_le_P
          exact hP_mem.1.ne_top (top_le_iff.mp htop_le_P)
        have hI_pow : I = P ^ m := by simpa [m, hQ_top] using hIeq
        have hm : m = k := by
          apply Nat.pow_right_injective hp.out.one_lt
          calc p ^ m = Ideal.absNorm I := by rw [hI_pow, map_pow, habsNormP]
            _ = p ^ k := hI_norm
        refine Subtype.ext (Subtype.ext ?_)
        simpa [m, hm] using hI_pow }
  exact Nat.card_unique

/-- **CN-05 coefficient equality at q = p** (the ramified case): LHS = RHS = 1. -/
theorem CN05CoeffEq_at_prime_pow_p (hp3 : p % 4 = 3) (k : ℕ) :
    ((idealNormMultiplicity (Kminus p) (p ^ k)) : ℂ) =
      LSeries.convolution (fun _ : ℕ ↦ (1 : ℂ)) (legendreDirichletNat p) (p ^ k) := by
  rw [idealNormMultiplicity_at_p_eq_one p hp3 k, convolution_one_legendreNat_at_prime_pow_p p k]
  simp

/-- **Split counting helper**: any ideal I with absNorm I = q^k in the split case
has the form P₁^a * P₂^(k-a) for some a ≤ k, where P₁, P₂ are the 2 primes above q. -/
lemma ideal_decomp_at_q_split (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p) {r : ZMod q} (hr : r ^ 2 = -(p : ZMod q))
    {P₁ P₂ : Ideal (𝓞 (Kminus p))}
    (hP₁_mem : P₁ ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)))
    (hP₂_mem : P₂ ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)))
    (hP_eq : Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)) = {P₁, P₂})
    {k : ℕ} {I : Ideal (𝓞 (Kminus p))} (hI_ne : I ≠ ⊥)
    (hI_norm : Ideal.absNorm I = q ^ k) :
    ∃ a ≤ k, I = P₁ ^ a * P₂ ^ (k - a) := by
  classical
  have hP₁_ne : P₁ ≠ ⊥ := primeOver_ne_bot p q P₁ hP₁_mem
  have hP₂_ne : P₂ ≠ ⊥ := primeOver_ne_bot p q P₂ hP₂_mem
  haveI : P₁.IsPrime := hP₁_mem.1
  haveI : P₂.IsPrime := hP₂_mem.1
  haveI : P₁.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₁_ne hP₁_mem.1
  haveI : P₂.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₂_ne hP₂_mem.1
  have habsNormP₁ : Ideal.absNorm P₁ = q :=
    absNorm_primeOver_at_q_split p hp3 q hq_odd hqp hr P₁ hP₁_mem
  have habsNormP₂ : Ideal.absNorm P₂ = q :=
    absNorm_primeOver_at_q_split p hp3 q hq_odd hqp hr P₂ hP₂_mem
  have hq_gt_one : 1 < q := (Fact.out : q.Prime).one_lt
  -- Apply eq_prime_pow_mul_coprime with P₁: I = P₁^a * Q₁ with P₁ ⊔ Q₁ = ⊤.
  obtain ⟨Q₁, hP₁Q₁, hIeq₁⟩ := Ideal.eq_prime_pow_mul_coprime hI_ne P₁
  set a : ℕ := Multiset.count P₁ (UniqueFactorizationMonoid.normalizedFactors I)
  have hQ₁_ne : Q₁ ≠ ⊥ := fun h ↦ hI_ne (by rw [hIeq₁, h, Ideal.mul_bot])
  -- Apply again with P₂ on Q₁: Q₁ = P₂^b * Q₂ with P₂ ⊔ Q₂ = ⊤.
  obtain ⟨Q₂, hP₂Q₂, hQ₁eq⟩ := Ideal.eq_prime_pow_mul_coprime hQ₁_ne P₂
  set b : ℕ := Multiset.count P₂ (UniqueFactorizationMonoid.normalizedFactors Q₁)
  have hQ₂_ne : Q₂ ≠ ⊥ := fun h ↦ hQ₁_ne (by rw [hQ₁eq, h, Ideal.mul_bot])
  -- I = P₁^a * P₂^b * Q₂.
  have hI_decomp : I = P₁ ^ a * P₂ ^ b * Q₂ := by rw [hIeq₁, hQ₁eq]; ring
  -- Derive coprimality of Q₂ with P₁ from P₁ ⊔ Q₁ = ⊤ and Q₁ = P₂^b * Q₂.
  have hP₁Q₂ : P₁ ⊔ Q₂ = ⊤ := by
    -- Since P₁ ⊔ Q₁ = ⊤ and Q₁ = P₂^b * Q₂, we have P₁ ⊔ (P₂^b * Q₂) = ⊤.
    -- Then P₁ ⊔ Q₂ ≥ P₁ ⊔ P₂^b * Q₂ = ⊤ (since P₂^b * Q₂ ≤ Q₂ when Q₂ is an ideal... wait).
    -- Actually, P₂^b * Q₂ ≤ Q₂, so P₁ ⊔ Q₂ ≥ P₁ ⊔ (P₂^b * Q₂) = ⊤.
    refine top_le_iff.mp ?_
    calc ⊤ = P₁ ⊔ Q₁ := hP₁Q₁.symm
      _ = P₁ ⊔ (P₂ ^ b * Q₂) := by rw [hQ₁eq]
      _ ≤ P₁ ⊔ Q₂ := sup_le_sup_left Ideal.mul_le_left _
  -- Show Q₂ = ⊤.
  have hQ₂_top : Q₂ = ⊤ := by
    by_contra hQ₂_ne_top
    have hQ₂_nf_ne : UniqueFactorizationMonoid.normalizedFactors Q₂ ≠ 0 := by
      intro hnf
      apply hQ₂_ne_top
      rw [← Ideal.prod_normalizedFactors_eq_self hQ₂_ne, hnf]; simp
    obtain ⟨R, hRmem⟩ := Multiset.exists_mem_of_ne_zero hQ₂_nf_ne
    have hRfac := (Ideal.mem_normalizedFactors_iff hQ₂_ne).1 hRmem
    have hRprime : R.IsPrime := hRfac.1
    have hQ₂_le_R : Q₂ ≤ R := hRfac.2
    have hR_ne : R ≠ ⊥ := fun h ↦ hQ₂_ne (le_bot_iff.mp (hQ₂_le_R.trans_eq h))
    haveI : NeZero R := ⟨hR_ne⟩
    -- absNorm R divides absNorm Q₂ divides absNorm I = q^k.
    have hQ₂_dvd_I : Ideal.absNorm Q₂ ∣ Ideal.absNorm I := by
      rw [hI_decomp, map_mul]; exact dvd_mul_left _ _
    have hR_dvd_qk : Ideal.absNorm R ∣ q ^ k := by
      rw [← hI_norm]
      exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ₂_le_R) hQ₂_dvd_I
    have hR_in : R ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)) :=
      prime_factor_of_q_pow_is_above_q p hp3 q hqp R hR_ne hR_dvd_qk
    rw [hP_eq] at hR_in
    -- R is P₁ or P₂, but Q₂ is coprime to both.
    rcases Set.mem_insert_iff.mp hR_in with hR | hR
    · -- R = P₁, Q₂ ⊆ P₁, contradicting hP₁Q₂.
      have hQ₂_le_P₁ : Q₂ ≤ P₁ := hR ▸ hQ₂_le_R
      have : P₁ ⊔ Q₂ = P₁ := sup_of_le_left hQ₂_le_P₁
      rw [this] at hP₁Q₂
      exact (inferInstance : P₁.IsMaximal).ne_top hP₁Q₂
    · -- R = P₂, Q₂ ⊆ P₂, contradicting hP₂Q₂.
      rw [Set.mem_singleton_iff] at hR
      have hQ₂_le_P₂ : Q₂ ≤ P₂ := hR ▸ hQ₂_le_R
      have : P₂ ⊔ Q₂ = P₂ := sup_of_le_left hQ₂_le_P₂
      rw [this] at hP₂Q₂
      exact (inferInstance : P₂.IsMaximal).ne_top hP₂Q₂
  -- I = P₁^a * P₂^b.
  have hI_prod : I = P₁ ^ a * P₂ ^ b := by rw [hI_decomp, hQ₂_top]; exact Ideal.mul_top _
  -- absNorm I = q^a · q^b = q^(a+b) = q^k, so a + b = k.
  have hab_eq : a + b = k := by
    have h : q ^ (a + b) = q ^ k := by
      rw [← hI_norm, hI_prod, map_mul, map_pow, map_pow, habsNormP₁, habsNormP₂, ← pow_add]
    exact Nat.pow_right_injective hq_gt_one h
  refine ⟨a, by omega, ?_⟩
  rw [hI_prod]
  congr 2
  omega

/-- **Split case counting**: for `q ≠ p, 2` with `-p = r²` in `ZMod q`, the number
of ideals `I` of `𝒪 (Kminus p)` with `absNorm I = q^k` is `k + 1`. -/
theorem idealNormMultiplicity_at_q_split_eq (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p) {r : ZMod q} (hr : r ^ 2 = -(p : ZMod q))
    (k : ℕ) :
    idealNormMultiplicity (Kminus p) (q ^ k) = k + 1 := by
  classical
  -- Extract the 2 primes above q.
  have h_set_card := ncard_primesOver_at_q_split p hp3 q hq_odd hqp hr
  rw [Set.ncard_eq_two] at h_set_card
  obtain ⟨P₁, P₂, hP₁₂_ne, hP_eq⟩ := h_set_card
  have hP₁_mem : P₁ ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)) := by
    rw [hP_eq]; exact Set.mem_insert _ _
  have hP₂_mem : P₂ ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)) := by
    rw [hP_eq]; exact Set.mem_insert_of_mem _ rfl
  have hP₁_ne : P₁ ≠ ⊥ := primeOver_ne_bot p q P₁ hP₁_mem
  have hP₂_ne : P₂ ≠ ⊥ := primeOver_ne_bot p q P₂ hP₂_mem
  haveI : P₁.IsPrime := hP₁_mem.1
  haveI : P₂.IsPrime := hP₂_mem.1
  haveI : P₁.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₁_ne hP₁_mem.1
  haveI : P₂.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₂_ne hP₂_mem.1
  have habsNormP₁ : Ideal.absNorm P₁ = q :=
    absNorm_primeOver_at_q_split p hp3 q hq_odd hqp hr P₁ hP₁_mem
  have habsNormP₂ : Ideal.absNorm P₂ = q :=
    absNorm_primeOver_at_q_split p hp3 q hq_odd hqp hr P₂ hP₂_mem
  have hq_gt_one : 1 < q := (Fact.out : q.Prime).one_lt
  -- Build the bijection with Fin (k+1).
  unfold idealNormMultiplicity
  -- Helper: for a ≤ k, P₁^a * P₂^(k-a) has absNorm q^k and is ≠ ⊥.
  have h_ideal_ne : ∀ a : ℕ, P₁ ^ a * P₂ ^ (k - a) ≠ ⊥ :=
    fun a ↦ mul_ne_zero (pow_ne_zero _ hP₁_ne) (pow_ne_zero _ hP₂_ne)
  have h_ideal_norm : ∀ a ≤ k, Ideal.absNorm (P₁ ^ a * P₂ ^ (k - a)) = q ^ k := by
    intro a ha
    rw [map_mul, map_pow, map_pow, habsNormP₁, habsNormP₂, ← pow_add]
    congr 1; omega
  -- Extract a from I: a = count P₁ in normalizedFactors I.
  -- For any (a, b, c : ℕ) with a + b = k and b + c = k, we have a = c. So the two forms
  -- P₁^a · P₂^(k-a) and P₁^a' · P₂^(k-a') give different ideals when a ≠ a'.
  have h_uniqueness : ∀ (a₁ a₂ : ℕ), a₁ ≤ k → a₂ ≤ k →
      P₁ ^ a₁ * P₂ ^ (k - a₁) = P₁ ^ a₂ * P₂ ^ (k - a₂) → a₁ = a₂ := by
    intro a₁ a₂ ha₁ ha₂ h_eq
    have h_prime_P₁ : Prime P₁ := Ideal.prime_of_isPrime hP₁_ne inferInstance
    have h_prime_P₂ : Prime P₂ := Ideal.prime_of_isPrime hP₂_ne inferInstance
    have h_count : Multiset.count P₁ (UniqueFactorizationMonoid.normalizedFactors
        (P₁ ^ a₁ * P₂ ^ (k - a₁))) =
        Multiset.count P₁ (UniqueFactorizationMonoid.normalizedFactors
        (P₁ ^ a₂ * P₂ ^ (k - a₂))) := by rw [h_eq]
    rw [UniqueFactorizationMonoid.normalizedFactors_mul (pow_ne_zero _ hP₁_ne)
        (pow_ne_zero _ hP₂_ne),
      UniqueFactorizationMonoid.normalizedFactors_mul (pow_ne_zero _ hP₁_ne)
        (pow_ne_zero _ hP₂_ne),
      UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible h_prime_P₁.irreducible,
      UniqueFactorizationMonoid.normalizedFactors_irreducible h_prime_P₂.irreducible,
      normalize_eq, normalize_eq] at h_count
    simp only [Multiset.count_add, Multiset.count_nsmul, Multiset.count_singleton_self,
      Multiset.count_singleton, if_neg hP₁₂_ne, mul_zero, mul_one, add_zero] at h_count
    exact h_count
  -- Now build the equivalence.
  set S := {I : NonzeroIdeal (Kminus p) // Ideal.absNorm I.1 = q ^ k}
  let forward : S → Fin (k + 1) := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ ↦
    ⟨(ideal_decomp_at_q_split p hp3 q hq_odd hqp hr hP₁_mem hP₂_mem hP_eq hI_ne
        hI_norm).choose,
      Nat.lt_succ_of_le
        (ideal_decomp_at_q_split p hp3 q hq_odd hqp hr hP₁_mem hP₂_mem hP_eq hI_ne
          hI_norm).choose_spec.1⟩
  let backward : Fin (k + 1) → S := fun ⟨a, ha⟩ ↦
    ⟨⟨P₁ ^ a * P₂ ^ (k - a), h_ideal_ne a⟩, h_ideal_norm a (Nat.lt_succ_iff.mp ha)⟩
  have h_equiv : S ≃ Fin (k + 1) :=
    { toFun := forward
      invFun := backward
      left_inv := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ ↦ by
        simp only [forward, backward]
        refine Subtype.ext (Subtype.ext ?_)
        simp only
        exact (ideal_decomp_at_q_split p hp3 q hq_odd hqp hr hP₁_mem hP₂_mem hP_eq hI_ne
          hI_norm).choose_spec.2.symm
      right_inv := fun ⟨a, ha⟩ ↦ by
        simp only [forward, backward]
        refine Fin.ext ?_
        simp only
        have ha_le : a ≤ k := Nat.lt_succ_iff.mp ha
        -- The decomp of P₁^a · P₂^(k-a) gives some a' with P₁^a' · P₂^(k-a') = P₁^a · P₂^(k-a).
        set decomp := ideal_decomp_at_q_split p hp3 q hq_odd hqp hr hP₁_mem hP₂_mem hP_eq
          (h_ideal_ne a) (h_ideal_norm a ha_le)
        have ha'_le : decomp.choose ≤ k := decomp.choose_spec.1
        have h_eq : P₁ ^ decomp.choose * P₂ ^ (k - decomp.choose) = P₁ ^ a * P₂ ^ (k - a) :=
          decomp.choose_spec.2.symm
        exact h_uniqueness _ _ ha'_le ha_le h_eq }
  rw [Nat.card_congr h_equiv, Nat.card_fin]

/-- **CN-05 coefficient equality at q ≠ p, 2 split** — LHS = k+1 = RHS when η(q) = 1. -/
theorem CN05CoeffEq_at_prime_pow_split (hp3 : p % 4 = 3) (q : ℕ) [Fact q.Prime]
    (hq_odd : q ≠ 2) (hqp : q ≠ p) {r : ZMod q} (hr : r ^ 2 = -(p : ZMod q))
    (hη : legendreDirichletNat p q = 1) (k : ℕ) :
    ((idealNormMultiplicity (Kminus p) (q ^ k)) : ℂ) =
      LSeries.convolution (fun _ : ℕ ↦ (1 : ℂ)) (legendreDirichletNat p) (q ^ k) := by
  rw [idealNormMultiplicity_at_q_split_eq p hp3 q hq_odd hqp hr,
    convolution_one_legendreNat_at_prime_pow_split p q (Fact.out : q.Prime) k hη]

/-- **CN-05 at q odd ≠ p split** (only η hypothesis via QR): LHS = RHS when
`η(q) = 1`, with the QR witness r derived from QR. -/
theorem CN05CoeffEq_at_prime_pow_split_via_eta (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p)
    (hη : legendreDirichletNat p q = 1) (k : ℕ) :
    ((idealNormMultiplicity (Kminus p) (q ^ k)) : ℂ) =
      LSeries.convolution (fun _ : ℕ ↦ (1 : ℂ)) (legendreDirichletNat p) (q ^ k) := by
  -- η(q) = 1 ⟺ IsSquare (q : ZMod p) ⟺ IsSquare (-p : ZMod q) via QR.
  have h_sq_q : IsSquare ((q : ℕ) : ZMod p) :=
    (legendreDirichletNat_eq_one_iff_isSquare p q hqp).mp hη
  have h_sq : IsSquare (-(p : ZMod q)) :=
    (isSquare_neg_p_iff_isSquare_q p hp3 q hq_odd hqp).mpr h_sq_q
  obtain ⟨r, hr_eq⟩ := h_sq
  have hr : r ^ 2 = -(p : ZMod q) := by rw [hr_eq]; ring
  exact CN05CoeffEq_at_prime_pow_split p hp3 q hq_odd hqp hr hη k

end CN05_statement

end BernoulliRegular
