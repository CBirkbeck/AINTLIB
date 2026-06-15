module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolPrincipalCanonical
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerFurtwaengler

/-!
# Ideal-level Galois action of `pthSymbolAtIdeal_canonical` (Atom D core)

This file lifts `pthSymbolAtPrime_canonical_galoisAction` from primes to
arbitrary integer ideals, via the multiset of normalized factors.

## Main theorem

```
pthSymbolAtIdeal_canonical (σ_a α) (σ_a • I) = (a : ZMod p) * pthSymbolAtIdeal_canonical α I
```
under hypotheses on each prime factor of `I`.

This is the **substantive ideal-level content of Atom D** (without the
specialisation to a Δ-character of η, which controls the final Galois weight `k`).
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Multiset bijection on normalized factors -/

/-- The cyclotomic Galois conjugate sends `(normalizedFactors I).map σ_a`
to `normalizedFactors (σ_a I)` — they are equal as multisets. -/
theorem normalizedFactors_cyclotomicGaloisConjugate
    (a : CyclotomicUnitDelta p) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    (normalizedFactors I).map
        (cyclotomicGaloisConjugate (p := p) (K := K) a) =
      normalizedFactors (cyclotomicGaloisConjugate (p := p) (K := K) a I) := by
  classical
  set m := (normalizedFactors I).map
    (cyclotomicGaloisConjugate (p := p) (K := K) a) with hm_def
  set σI := cyclotomicGaloisConjugate (p := p) (K := K) a I with hσI_def
  have hσI_ne : σI ≠ ⊥ := cyclotomicGaloisConjugate_ne_bot a hI
  -- Step 1: each P in m is irreducible (= prime, in 𝓞 K).
  have h_m_irreducible : ∀ P ∈ m, Irreducible P := by
    intro P hP
    rw [hm_def, Multiset.mem_map] at hP
    obtain ⟨Q, hQ_mem, hQ_eq⟩ := hP
    have hQ_prime : Prime Q := prime_of_normalized_factor Q hQ_mem
    have hQ_ne : Q ≠ ⊥ := hQ_prime.ne_zero
    haveI hQ_isPrime : Q.IsPrime := (Ideal.prime_iff_isPrime hQ_ne).mp hQ_prime
    haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a Q).IsPrime :=
      cyclotomicGaloisConjugate_isPrime a Q
    have hP_ne_bot : P ≠ ⊥ := by
      rw [← hQ_eq]
      exact cyclotomicGaloisConjugate_ne_bot a hQ_ne
    have : Prime P := by
      rw [← hQ_eq]
      exact (Ideal.prime_iff_isPrime
        (cyclotomicGaloisConjugate_ne_bot a hQ_ne)).mpr inferInstance
    exact this.irreducible
  -- Step 2: each P in normalizedFactors σI is irreducible.
  have h_nf_irreducible : ∀ P ∈ normalizedFactors σI, Irreducible P :=
    fun P hP => irreducible_of_normalized_factor P hP
  -- Step 3: m.prod ~ᵤ σI (in fact equal since ideals).
  have h_m_prod : m.prod = σI := by
    rw [hm_def, hσI_def]
    -- σ_a (∏ Pᵢ) = ∏ σ_a Pᵢ via multiplicativity of σ_a on ideals.
    have h_eq : (normalizedFactors I).prod = I := by
      have h_norm := prod_normalizedFactors_eq hI
      rw [normalize_eq] at h_norm
      exact h_norm
    have h_map_prod : ((normalizedFactors I).map
        (cyclotomicGaloisConjugate (p := p) (K := K) a)).prod =
        cyclotomicGaloisConjugate (p := p) (K := K) a (normalizedFactors I).prod := by
      -- σ_a is multiplicative on ideals; prod of map = σ_a of prod.
      induction (normalizedFactors I) using Multiset.induction_on with
      | empty =>
        change (1 : Ideal _) = cyclotomicGaloisConjugate (p := p) (K := K) a 1
        rw [Ideal.one_eq_top, cyclotomicGaloisConjugate_top]
      | cons P S ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, ih,
          ← cyclotomicGaloisConjugate_mul_ideal]
    rw [h_map_prod, h_eq]
  -- Step 4: associated.
  have h_assoc : Associated m.prod (normalizedFactors σI).prod := by
    rw [h_m_prod]
    exact (prod_normalizedFactors hσI_ne).symm
  -- Step 5: factors_unique gives Multiset.Rel Associated.
  have h_rel : Multiset.Rel Associated m (normalizedFactors σI) :=
    factors_unique h_m_irreducible h_nf_irreducible h_assoc
  -- Step 6: For ideals, Subsingleton (Ideal R)ˣ, so Associated = Eq.
  rw [associated_eq_eq, Multiset.rel_eq] at h_rel
  exact h_rel

/-! ### Ideal-level Galois action -/

/-- **Ideal-level Galois action of `pthSymbolAtIdeal_canonical`**:

```
pthSymbolAtIdeal_canonical (σ_a α) (σ_a • I) = (a : ZMod p) * pthSymbolAtIdeal_canonical α I
```

under the hypotheses that, for every prime factor `Q` of `I`:
* `α ∉ Q`,
* `(p : 𝓞 K) ∉ Q`,
* `Q.IsMaximal`,
* `p ∣ #(𝓞 K / Q) - 1`.

This lifts `pthSymbolAtPrime_canonical_galoisAction` from primes to ideals
via the multiset bijection `normalizedFactors_cyclotomicGaloisConjugate`. -/
theorem pthSymbolAtIdeal_canonical_galoisAction
    (a : CyclotomicUnitDelta p) (α : 𝓞 K) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hα : ∀ Q ∈ normalizedFactors I, α ∉ Q)
    (hp_in : ∀ Q ∈ normalizedFactors I, (p : 𝓞 K) ∉ Q)
    (hmax : ∀ Q ∈ normalizedFactors I, Q.IsMaximal)
    (hdiv : ∀ Q ∈ normalizedFactors I,
      p ∣ Nat.card (𝓞 K ⧸ Q) - 1) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a α)
        (cyclotomicGaloisConjugate (p := p) (K := K) a I) =
      (a : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  classical
  unfold pthSymbolAtIdeal_canonical
  -- Use the multiset bijection.
  rw [← normalizedFactors_cyclotomicGaloisConjugate a hI, Multiset.map_map]
  -- Show pointwise equality of the mapped functions.
  rw [show ((normalizedFactors I).map
        ((fun P => pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a α) P) ∘
          (cyclotomicGaloisConjugate (p := p) (K := K) a))).sum =
      ((normalizedFactors I).map
        (fun P => (a : ZMod p) * pthSymbolAtPrime_canonical (p := p) (K := K) α P)).sum
    from ?_]
  · rw [← Multiset.sum_map_mul_left]
  · -- Pointwise equality.
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro Q hQ
    change pthSymbolAtPrime_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a α)
        (cyclotomicGaloisConjugate (p := p) (K := K) a Q) =
      (a : ZMod p) * pthSymbolAtPrime_canonical (p := p) (K := K) α Q
    have hQ_prime_orig : Prime Q := prime_of_normalized_factor Q hQ
    have hQ_ne : Q ≠ ⊥ := hQ_prime_orig.ne_zero
    haveI : Q.IsPrime := (Ideal.prime_iff_isPrime hQ_ne).mp hQ_prime_orig
    haveI : Q.IsMaximal := hmax Q hQ
    haveI : NeZero Q := ⟨hQ_ne⟩
    have h_card_eq : Nat.card (𝓞 K ⧸ Q) = Fintype.card (𝓞 K ⧸ Q) :=
      Nat.card_eq_fintype_card
    have hdiv_Q : p ∣ Fintype.card (𝓞 K ⧸ Q) - 1 := by
      rw [← h_card_eq]; exact hdiv Q hQ
    exact pthSymbolAtPrime_canonical_galoisAction
      (p := p) (K := K) a α hQ_ne ‹Q.IsMaximal›
      (hα Q hQ) (hp_in Q hQ) hdiv_Q

/-! ### Principal-ideal version -/

/-- The cyclotomic Galois conjugate sends `Ideal.span {β}` to `Ideal.span {σ_a β}`. -/
theorem cyclotomicGaloisConjugate_span_singleton
    (a : CyclotomicUnitDelta p) (β : 𝓞 K) :
    cyclotomicGaloisConjugate (p := p) (K := K) a (Ideal.span ({β} : Set (𝓞 K))) =
      Ideal.span ({cyclotomicRingOfIntegersEquiv (p := p) K a β} : Set (𝓞 K)) := by
  unfold cyclotomicGaloisConjugate
  rw [Ideal.map_span]
  congr 1
  ext x
  simp

/-- **Principal-ideal Galois action of `pthSymbolAtPrincipal_canonical`**:

```
pthSymbolAtPrincipal_canonical (σ_a α) (σ_a β)
  = (a : ZMod p) * pthSymbolAtPrincipal_canonical α β
```
under hypotheses on prime factors of `Ideal.span {β}`. -/
theorem pthSymbolAtPrincipal_canonical_galoisAction
    (a : CyclotomicUnitDelta p) (α β : 𝓞 K) (hβ : β ≠ 0)
    (hα : ∀ Q ∈ normalizedFactors (Ideal.span ({β} : Set (𝓞 K))), α ∉ Q)
    (hp_in : ∀ Q ∈ normalizedFactors (Ideal.span ({β} : Set (𝓞 K))),
      (p : 𝓞 K) ∉ Q)
    (hmax : ∀ Q ∈ normalizedFactors (Ideal.span ({β} : Set (𝓞 K))),
      Q.IsMaximal)
    (hdiv : ∀ Q ∈ normalizedFactors (Ideal.span ({β} : Set (𝓞 K))),
      p ∣ Nat.card (𝓞 K ⧸ Q) - 1) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a α)
        (cyclotomicRingOfIntegersEquiv (p := p) K a β) =
      (a : ZMod p) *
        pthSymbolAtPrincipal_canonical (p := p) (K := K) α β := by
  unfold pthSymbolAtPrincipal_canonical
  rw [← cyclotomicGaloisConjugate_span_singleton]
  apply pthSymbolAtIdeal_canonical_galoisAction a α
  · -- I ≠ ⊥.
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hβ
  · exact hα
  · exact hp_in
  · exact hmax
  · exact hdiv

/-! ### Unconditional prime-level Galois action (case-analysis on hypotheses) -/

/-- **Unconditional prime-level Galois action**: drops all hypotheses by
case-analysis. In every "bad" case (q not prime/maximal/nonzero, α ∈ q,
p ∈ q, p ∤ #(𝓞 K / q) − 1), both sides of the formula vanish. -/
theorem pthSymbolAtPrime_canonical_galoisAction_unconditional
    (a : CyclotomicUnitDelta p) (α : 𝓞 K) (q : Ideal (𝓞 K)) :
    pthSymbolAtPrime_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a α)
        (cyclotomicGaloisConjugate (p := p) (K := K) a q) =
      (a : ZMod p) * pthSymbolAtPrime_canonical (p := p) (K := K) α q := by
  classical
  by_cases hbot : q = ⊥
  · -- q = ⊥: σ_a ⊥ = ⊥, both sides vanish.
    subst hbot
    rw [cyclotomicGaloisConjugate_bot]
    rw [pthSymbolAtPrime_canonical_eq_zero_of_eq_bot,
      pthSymbolAtPrime_canonical_eq_zero_of_eq_bot, mul_zero]
  by_cases hmax : q.IsMaximal
  · -- q is maximal.
    haveI : q.IsMaximal := hmax
    haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a q).IsMaximal :=
      cyclotomicGaloisConjugate_isMaximal a q
    have hbot_σ : cyclotomicGaloisConjugate (p := p) (K := K) a q ≠ ⊥ :=
      cyclotomicGaloisConjugate_ne_bot a hbot
    by_cases hα : α ∈ q
    · -- α ∈ q: σ_a α ∈ σ_a q, both sides vanish.
      have hα_σ : cyclotomicRingOfIntegersEquiv (p := p) K a α ∈
          cyclotomicGaloisConjugate (p := p) (K := K) a q :=
        (mem_cyclotomicGaloisConjugate_iff a).mpr hα
      rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hbot_σ
        ‹(cyclotomicGaloisConjugate (p := p) (K := K) a q).IsMaximal› hα_σ,
        pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hα, mul_zero]
    · -- α ∉ q.
      have hα_σ : cyclotomicRingOfIntegersEquiv (p := p) K a α ∉
          cyclotomicGaloisConjugate (p := p) (K := K) a q :=
        (notMem_cyclotomicGaloisConjugate_iff a).mpr hα
      -- Need Fintype to talk about cardinality.
      haveI : NeZero q := ⟨hbot⟩
      haveI : NeZero (cyclotomicGaloisConjugate (p := p) (K := K) a q) :=
        ⟨hbot_σ⟩
      -- Cardinality preserved.
      have h_card_eq :
          Fintype.card (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) =
            Fintype.card (𝓞 K ⧸ q) :=
        cyclotomicGaloisConjugate_quotient_card_eq a hbot
      by_cases hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1
      · -- Good divisibility on q (and σ_a q via h_card_eq).
        have hdiv_σ : p ∣ Fintype.card
            (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) - 1 := by
          rw [h_card_eq]; exact hdiv
        by_cases hp_in : (p : 𝓞 K) ∈ q
        · -- p ∈ q: p ∈ σ_a q (by σ_a fixing natCast), both sides vanish.
          have hp_σ : (p : 𝓞 K) ∈ cyclotomicGaloisConjugate (p := p) (K := K) a q := by
            have h_fix : cyclotomicRingOfIntegersEquiv (p := p) K a (p : 𝓞 K) =
                (p : 𝓞 K) := by
              change (cyclotomicRingOfIntegersEquiv (p := p) K a).toRingHom (p : 𝓞 K) =
                (p : 𝓞 K)
              rw [map_natCast]
            rw [← h_fix]
            exact (mem_cyclotomicGaloisConjugate_iff a).mpr hp_in
          rw [pthSymbolAtPrime_canonical_eq_zero_of_p_mem hbot_σ
            ‹(cyclotomicGaloisConjugate (p := p) (K := K) a q).IsMaximal›
            hα_σ hdiv_σ hp_σ,
            pthSymbolAtPrime_canonical_eq_zero_of_p_mem hbot hmax hα hdiv hp_in,
            mul_zero]
        · -- All "good" hypotheses: apply existing theorem.
          exact pthSymbolAtPrime_canonical_galoisAction
            (p := p) (K := K) a α hbot hmax hα hp_in hdiv
      · -- p ∤ #(𝓞 K / q) - 1: same for σ_a q, both sides vanish.
        have hdiv_σ : ¬ p ∣ Fintype.card
            (𝓞 K ⧸ cyclotomicGaloisConjugate (p := p) (K := K) a q) - 1 := by
          rw [h_card_eq]; exact hdiv
        rw [pthSymbolAtPrime_canonical_eq_zero_of_not_dvd hbot_σ
          ‹(cyclotomicGaloisConjugate (p := p) (K := K) a q).IsMaximal›
          hα_σ hdiv_σ,
          pthSymbolAtPrime_canonical_eq_zero_of_not_dvd hbot hmax hα hdiv,
          mul_zero]
  · -- q not maximal: σ_a q not maximal either.
    have hmax_σ : ¬ (cyclotomicGaloisConjugate (p := p) (K := K) a q).IsMaximal := by
      intro h
      apply hmax
      -- σ_a^{-1} (σ_a q) = q is maximal because σ_a q is maximal.
      have h_inv :
          cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            (cyclotomicGaloisConjugate (p := p) (K := K) a q) = q := by
        rw [← cyclotomicGaloisConjugate_mul, inv_mul_cancel,
          cyclotomicGaloisConjugate_one]
      rw [← h_inv]
      exact cyclotomicGaloisConjugate_isMaximal a⁻¹ _
    have hbot_σ : cyclotomicGaloisConjugate (p := p) (K := K) a q ≠ ⊥ :=
      cyclotomicGaloisConjugate_ne_bot a hbot
    rw [pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot_σ hmax_σ,
      pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax, mul_zero]

/-! ### Unconditional ideal-level Galois action -/

/-- **Unconditional ideal-level Galois action of `pthSymbolAtIdeal_canonical`**:
no hypotheses on prime factors needed. The formula
```
pthSymbolAtIdeal_canonical (σ_a α) (σ_a I) = (a : ZMod p) * pthSymbolAtIdeal_canonical α I
```
holds unconditionally (each prime factor case is handled by
`pthSymbolAtPrime_canonical_galoisAction_unconditional`). -/
theorem pthSymbolAtIdeal_canonical_galoisAction_unconditional
    (a : CyclotomicUnitDelta p) (α : 𝓞 K) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a α)
        (cyclotomicGaloisConjugate (p := p) (K := K) a I) =
      (a : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  classical
  unfold pthSymbolAtIdeal_canonical
  rw [← normalizedFactors_cyclotomicGaloisConjugate a hI, Multiset.map_map]
  rw [show ((normalizedFactors I).map
        ((fun P => pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a α) P) ∘
          (cyclotomicGaloisConjugate (p := p) (K := K) a))).sum =
      ((normalizedFactors I).map
        (fun P => (a : ZMod p) * pthSymbolAtPrime_canonical (p := p) (K := K) α P)).sum
    from ?_]
  · rw [← Multiset.sum_map_mul_left]
  · apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro Q _
    change pthSymbolAtPrime_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a α)
        (cyclotomicGaloisConjugate (p := p) (K := K) a Q) =
      (a : ZMod p) * pthSymbolAtPrime_canonical (p := p) (K := K) α Q
    exact pthSymbolAtPrime_canonical_galoisAction_unconditional
      (p := p) (K := K) a α Q

/-- **Unconditional Galois weight 1**: when `σ_a α = α`, the residue-symbol's
ideal slot transforms by the cyclotomic character `(a : ZMod p)`,
unconditionally on prime factors of `I`. -/
theorem pthSymbolAtIdeal_canonical_galoisAction_of_fixed_unconditional
    (a : CyclotomicUnitDelta p) (α : 𝓞 K)
    (hα_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a α = α)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α
        (cyclotomicGaloisConjugate (p := p) (K := K) a I) =
      (a : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  have h := pthSymbolAtIdeal_canonical_galoisAction_unconditional
    (p := p) (K := K) a α hI
  rwa [hα_fixed] at h

/-! ### Galois weight 1 specialization (η fixed pointwise by σ_a)

When the residue-symbol numerator `α` is fixed by every cyclotomic Galois
automorphism — `σ_a α = α` for all a — the Galois weight of the symbol's
ideal slot is `1`:

```
pthSymbolAtIdeal_canonical α (σ_a I) = (a : ZMod p) * pthSymbolAtIdeal_canonical α I
```

This is the cleanest case of Atom D's transformation rule. -/

/-- **Galois weight 1**: when `σ_a α = α` (σ_a fixes α), the symbol's ideal
slot transforms by the cyclotomic character `(a : ZMod p)`. -/
theorem pthSymbolAtIdeal_canonical_galoisAction_of_fixed
    (a : CyclotomicUnitDelta p) (α : 𝓞 K)
    (hα_fixed : cyclotomicRingOfIntegersEquiv (p := p) K a α = α)
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hα : ∀ Q ∈ normalizedFactors I, α ∉ Q)
    (hp_in : ∀ Q ∈ normalizedFactors I, (p : 𝓞 K) ∉ Q)
    (hmax : ∀ Q ∈ normalizedFactors I, Q.IsMaximal)
    (hdiv : ∀ Q ∈ normalizedFactors I,
      p ∣ Nat.card (𝓞 K ⧸ Q) - 1) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α
        (cyclotomicGaloisConjugate (p := p) (K := K) a I) =
      (a : ZMod p) *
        pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  have h := pthSymbolAtIdeal_canonical_galoisAction
    (p := p) (K := K) a α hI hα hp_in hmax hdiv
  rwa [hα_fixed] at h

end Furtwaengler

end BernoulliRegular

end
