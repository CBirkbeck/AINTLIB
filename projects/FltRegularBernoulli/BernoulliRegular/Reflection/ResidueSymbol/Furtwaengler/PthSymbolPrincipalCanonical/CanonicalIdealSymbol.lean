module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolCanonical

/-!
# Canonical `pthSymbolAtIdeal` / `pthSymbolAtPrincipal` and the unconditional c.3 closed form

This file mirrors the `pthSymbolAtIdeal` / `pthSymbolAtPrincipal` API on top
of `pthSymbolAtPrime_canonical`, and uses the explicit Galois-action
transformation from `PthSymbolCanonical.lean` to derive the
**unconditional c.3 closed form**:

```
pthSymbolAtPrincipal_canonical α h_stick.gen =
  ∑ a : CyclotomicUnitDelta p,
    pthSymbolAtPrime_canonical (σ_a α) q_K
```

Compared to the conditional theorem
`pthSymbolAtPrincipal_eq_galois_sum_of_hypothesis` (in
`KummerFurtwaengler.lean`), the canonical version is *unconditional*:
the explicit `(a : ZMod p)` factor in the Galois-action transformation
cancels the digit-sum `a.val` factor, so the closed form eliminates
both the `a.val` weights and the `StickelbergerGaloisHypothesis` input.

## Main definitions and theorems

* `pthSymbolAtIdeal_canonical α I` — the canonical residue symbol at an
  integral ideal, defined as the multiset sum of
  `pthSymbolAtPrime_canonical α P` over the prime factors `P` of `I`.
* `pthSymbolAtPrincipal_canonical α β` — the canonical principal symbol,
  defined as `pthSymbolAtIdeal_canonical α (Ideal.span {β})`.
* `pthSymbolAtPrincipal_canonical_eq_galois_sum` — the **c.3 unconditional
  closed form** taking only `StickelbergerIdealEquality q_K`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-! ### Canonical `pthSymbolAtIdeal`

Mirrors `pthSymbolAtIdeal` but uses `pthSymbolAtPrime_canonical` as the
prime-level building block. -/

/-- The canonical `p`-th-power residue symbol `(α/I)_p` extended to integral
ideals by multiplicativity over the prime factorization of `I`. Same shape
as `pthSymbolAtIdeal`, but with `pthSymbolAtPrime_canonical` (which uses the
canonical primitive `p`-th root, eliminating the `Classical.choose`). -/
noncomputable def pthSymbolAtIdeal_canonical
    (α : 𝓞 K) (I : Ideal (𝓞 K)) : ZMod p :=
  ((UniqueFactorizationMonoid.normalizedFactors I).map
    (fun P => pthSymbolAtPrime_canonical (p := p) α P)).sum

/-- `pthSymbolAtIdeal_canonical α 1 = 0`. -/
@[simp] theorem pthSymbolAtIdeal_canonical_one
    (α : 𝓞 K) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α (1 : Ideal (𝓞 K)) = 0 := by
  unfold pthSymbolAtIdeal_canonical
  rw [UniqueFactorizationMonoid.normalizedFactors_one]
  simp

/-- `pthSymbolAtIdeal_canonical α ⊤ = 0`. -/
@[simp] theorem pthSymbolAtIdeal_canonical_top
    (α : 𝓞 K) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α (⊤ : Ideal (𝓞 K)) = 0 := by
  rw [← Ideal.one_eq_top]
  exact pthSymbolAtIdeal_canonical_one α

/-- `pthSymbolAtIdeal_canonical α ⊥ = 0`. -/
@[simp] theorem pthSymbolAtIdeal_canonical_bot
    (α : 𝓞 K) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α (⊥ : Ideal (𝓞 K)) = 0 := by
  unfold pthSymbolAtIdeal_canonical
  rw [← Ideal.zero_eq_bot, UniqueFactorizationMonoid.normalizedFactors_zero]
  simp

/-- Multiplicativity in the ideal slot for non-zero `I, J`. -/
theorem pthSymbolAtIdeal_canonical_mul_ideal
    (α : 𝓞 K) {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α (I * J) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α I +
        pthSymbolAtIdeal_canonical (p := p) (K := K) α J := by
  unfold pthSymbolAtIdeal_canonical
  have hI' : (I : Ideal (𝓞 K)) ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  have hJ' : (J : Ideal (𝓞 K)) ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hI' hJ',
      Multiset.map_add, Multiset.sum_add]

/-- Power form in the ideal slot: `pthSymbolAtIdeal_canonical α (I^n) =
n · pthSymbolAtIdeal_canonical α I`. -/
theorem pthSymbolAtIdeal_canonical_pow_ideal
    (α : 𝓞 K) (I : Ideal (𝓞 K)) (n : ℕ) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α (I ^ n) =
      n * pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  unfold pthSymbolAtIdeal_canonical
  rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      Multiset.map_nsmul, Multiset.sum_nsmul, nsmul_eq_mul]

/-- The canonical residue symbol on a `p`-th power ideal vanishes:
`pthSymbolAtIdeal_canonical α (I^p) = 0` in `ZMod p`. -/
@[simp] theorem pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero
    (α : 𝓞 K) (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α (I ^ p) = 0 := by
  rw [pthSymbolAtIdeal_canonical_pow_ideal α I p, ZMod.natCast_self, zero_mul]

/-- Multiplicativity over a `Finset.prod` of non-zero ideals. -/
theorem pthSymbolAtIdeal_canonical_finset_prod {ι : Type*}
    (s : Finset ι) (f : ι → Ideal (𝓞 K)) (α : 𝓞 K)
    (hf : ∀ i ∈ s, f i ≠ ⊥) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α (∏ i ∈ s, f i) =
      ∑ i ∈ s, pthSymbolAtIdeal_canonical (p := p) (K := K) α (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, pthSymbolAtIdeal_canonical_one, Finset.sum_empty]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hfi : f i ≠ ⊥ := hf i (Finset.mem_insert_self _ _)
    have hprod_ne : (∏ j ∈ s, f j) ≠ ⊥ := by
      rw [Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
      push Not
      intro j hj
      rw [Ideal.zero_eq_bot]
      exact hf j (Finset.mem_insert_of_mem hj)
    rw [pthSymbolAtIdeal_canonical_mul_ideal _ hfi hprod_ne]
    congr 1
    exact ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- For a non-zero prime ideal `P`, the canonical ideal symbol agrees
with the canonical prime symbol. -/
theorem pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical
    (α : 𝓞 K) {P : Ideal (𝓞 K)} [hP_prime : P.IsPrime] (hP_ne : P ≠ ⊥) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α P =
      pthSymbolAtPrime_canonical (p := p) (K := K) α P := by
  unfold pthSymbolAtIdeal_canonical
  have hP_prime_in_R : Prime P := (Ideal.prime_iff_isPrime hP_ne).mpr hP_prime
  have hP_irreducible : Irreducible P := hP_prime_in_R.irreducible
  have h_factors :
      UniqueFactorizationMonoid.normalizedFactors P = ({P} : Multiset _) := by
    have h_assoc :=
      UniqueFactorizationMonoid.normalizedFactors_irreducible hP_irreducible
    rw [show normalize P = P from normalize_eq P] at h_assoc
    exact h_assoc
  rw [h_factors]
  simp

/-- For a non-zero prime ideal containing `(p)`, the canonical ideal symbol
with that prime as denominator vanishes. -/
theorem pthSymbolAtIdeal_canonical_eq_zero_of_p_mem_prime
    (α : 𝓞 K) {P : Ideal (𝓞 K)} [hP_prime : P.IsPrime] (hP_ne : P ≠ ⊥)
    (hp_in : (p : 𝓞 K) ∈ P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α P = 0 := by
  rw [pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical α hP_ne]
  exact pthSymbolAtPrime_canonical_eq_zero_of_p_mem_uncond hP_ne
    (Ideal.IsPrime.isMaximal hP_prime hP_ne) hp_in

/-! ### Canonical `pthSymbolAtPrincipal` -/

/-- The canonical principal-symbol `(α/(β))_p`, defined as
`pthSymbolAtIdeal_canonical α (Ideal.span {β})`. -/
noncomputable def pthSymbolAtPrincipal_canonical
    (α β : 𝓞 K) : ZMod p :=
  pthSymbolAtIdeal_canonical (p := p) (K := K) α (Ideal.span ({β} : Set (𝓞 K)))

/-- Unfolding lemma. -/
@[simp] theorem pthSymbolAtPrincipal_canonical_eq_atIdeal_span
    (α β : 𝓞 K) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α β =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α
        (Ideal.span ({β} : Set (𝓞 K))) := rfl

/-! ### c.3 unconditional half (consequence of c.1 only)

Mirror of `pthSymbolAtPrincipal_eq_stickelberger_sum`: from the
`StickelbergerIdealEquality` (c.1) we expand the canonical principal
symbol into the digit sum
`∑ a, ↑a.val * pthSymbolAtPrime_canonical α (σ_{a⁻¹} q_K)`. -/

theorem pthSymbolAtPrincipal_canonical_eq_stickelberger_sum
    {q_K : Ideal (𝓞 K)} [q_K.IsPrime] (hq_ne : q_K ≠ ⊥)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) q_K)
    (α : 𝓞 K) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α h_stick.gen =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K) α
            (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K) := by
  classical
  unfold pthSymbolAtPrincipal_canonical
  rw [h_stick.span_gen]
  unfold stickelbergerIdeal
  rw [pthSymbolAtIdeal_canonical_finset_prod (p := p) Finset.univ
    (fun a : CyclotomicUnitDelta p =>
      cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K ^ ((a : ZMod p).val))
    α (fun a _ => pow_ne_zero _ (cyclotomicGaloisConjugate_ne_bot a⁻¹ hq_ne))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [pthSymbolAtIdeal_canonical_pow_ideal α
    (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K) ((a : ZMod p).val)]
  congr 1
  set P := cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K with hP_def
  haveI : P.IsPrime := cyclotomicGaloisConjugate_isPrime a⁻¹ q_K
  have hP_ne : P ≠ ⊥ := cyclotomicGaloisConjugate_ne_bot a⁻¹ hq_ne
  exact pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical α hP_ne

/-! ### c.3 unconditional Galois transformation per term

The key lemma: for a non-bot prime `q_K` and any `a, α`, the term
`↑a.val * pthSymbolAtPrime_canonical α (σ_{a⁻¹} q_K)`
equals the Galois-translated term
`pthSymbolAtPrime_canonical (σ_a α) q_K`.

Proof: the canonical Galois-action lemma
`pthSymbolAtPrime_canonical_galoisAction` gives, for the inverse direction,
```
pthSymbolAtPrime_canonical (σ_a α) (σ_a • σ_{a⁻¹} q_K) =
  (a : ZMod p) * pthSymbolAtPrime_canonical α (σ_{a⁻¹} q_K).
```
Since `σ_a (σ_{a⁻¹} q_K) = q_K`, this reads
```
pthSymbolAtPrime_canonical (σ_a α) q_K =
  (a : ZMod p) * pthSymbolAtPrime_canonical α (σ_{a⁻¹} q_K).
```
Now `↑a.val = (a : ZMod p)` in `ZMod p`. The hypotheses on `α` and `p`
in `pthSymbolAtPrime_canonical_galoisAction` rule out the bad cases;
we case-split to handle them via the `_eq_zero` lemmas. -/

/-- Per-term unconditional Galois transformation. -/
theorem pthSymbolAtPrime_canonical_term_eq
    (a : CyclotomicUnitDelta p) (α : 𝓞 K)
    {q_K : Ideal (𝓞 K)} [q_K.IsPrime] (hq_ne : q_K ≠ ⊥) :
    ((a : ZMod p).val : ZMod p) *
        pthSymbolAtPrime_canonical (p := p) (K := K) α
          (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K) =
      pthSymbolAtPrime_canonical (p := p) (K := K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a α) q_K := by
  classical
  haveI hp_ne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- Set up the conjugate ideal q := σ_{a⁻¹} q_K.
  set q : Ideal (𝓞 K) := cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q_K
    with hq_def
  -- σ_a • q = q_K.
  have hσ_q : cyclotomicGaloisConjugate (p := p) (K := K) a q = q_K := by
    rw [hq_def, ← cyclotomicGaloisConjugate_mul, mul_inv_cancel,
      cyclotomicGaloisConjugate_one]
  -- Standard data on q.
  haveI hq_K_max : q_K.IsMaximal := Ideal.IsPrime.isMaximal ‹q_K.IsPrime› hq_ne
  haveI hq_prime : q.IsPrime := cyclotomicGaloisConjugate_isPrime a⁻¹ q_K
  have hq_ne_bot : q ≠ ⊥ := cyclotomicGaloisConjugate_ne_bot a⁻¹ hq_ne
  haveI hq_max : q.IsMaximal := cyclotomicGaloisConjugate_isMaximal a⁻¹ q_K
  -- Case-split on α ∈ q.
  by_cases hα : α ∈ q
  · -- α ∈ q ⟹ σ_a α ∈ σ_a • q = q_K. Both symbols are 0.
    have hα' : cyclotomicRingOfIntegersEquiv (p := p) K a α ∈ q_K := by
      rw [← hσ_q]
      exact (mem_cyclotomicGaloisConjugate_iff a).mpr hα
    rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hq_ne_bot hq_max hα,
      pthSymbolAtPrime_canonical_eq_zero_of_mem hq_ne hq_K_max hα']
    ring
  -- Case: α ∉ q. Now case-split on (p : 𝓞 K) ∈ q_K.
  by_cases hp_in_qK : (p : 𝓞 K) ∈ q_K
  · -- (p : 𝓞 K) ∈ q_K ⟺ (p : 𝓞 K) ∈ q (via σ_a fixing (p : 𝓞 K)).
    have hp_in_q : (p : 𝓞 K) ∈ q := by
      rw [← hσ_q] at hp_in_qK
      have h_fix :
          cyclotomicRingOfIntegersEquiv (p := p) K a (p : 𝓞 K) = (p : 𝓞 K) := by
        change (cyclotomicRingOfIntegersEquiv (p := p) K a).toRingHom (p : 𝓞 K) =
          (p : 𝓞 K)
        rw [map_natCast]
      rw [← h_fix] at hp_in_qK
      exact (mem_cyclotomicGaloisConjugate_iff a).mp hp_in_qK
    -- σ_a α ∉ q_K (since α ∉ q and σ_a α ∉ σ_a q = q_K).
    have hα' : cyclotomicRingOfIntegersEquiv (p := p) K a α ∉ q_K := by
      rw [← hσ_q]
      exact (notMem_cyclotomicGaloisConjugate_iff a).mpr hα
    -- Both symbols are 0 by the p_mem case (when divisibility fails too)
    -- or by the p_mem case directly.
    -- We use pthSymbolAtPrime_canonical_eq_zero_of_p_mem when `hdiv` and
    -- `α ∉ q` hold; otherwise, the unfolding needs a different branch.
    -- But the cleanest is: just case-split on hdiv.
    by_cases hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1
    · -- Apply _eq_zero_of_p_mem on both sides.
      have hdiv' : p ∣ Fintype.card (𝓞 K ⧸ q_K) - 1 := by
        have h_card_q'q :
            Fintype.card (𝓞 K ⧸ q) = Fintype.card (𝓞 K ⧸ q_K) := by
          have := cyclotomicGaloisConjugate_quotient_card_eq a⁻¹ hq_ne
          simpa [hq_def] using this
        rw [← h_card_q'q]; exact hdiv
      rw [pthSymbolAtPrime_canonical_eq_zero_of_p_mem hq_ne_bot hq_max hα hdiv hp_in_q,
        pthSymbolAtPrime_canonical_eq_zero_of_p_mem hq_ne hq_K_max hα' hdiv' hp_in_qK]
      ring
    · -- ¬hdiv: unfold canonical symbol directly to 0 via the bad-case branch.
      -- pthSymbolAtPrime_canonical α q with hdiv false yields 0 by definition.
      have h_lhs_zero : pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
        unfold pthSymbolAtPrime_canonical
        rw [dif_neg hq_ne_bot, dif_pos hq_max, dif_neg hα, dif_neg hdiv]
      have hdiv' : ¬ p ∣ Fintype.card (𝓞 K ⧸ q_K) - 1 := by
        intro h
        apply hdiv
        have h_card_q'q :
            Fintype.card (𝓞 K ⧸ q) = Fintype.card (𝓞 K ⧸ q_K) := by
          have := cyclotomicGaloisConjugate_quotient_card_eq a⁻¹ hq_ne
          simpa [hq_def] using this
        rw [h_card_q'q]; exact h
      have h_rhs_zero :
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a α) q_K = 0 := by
        unfold pthSymbolAtPrime_canonical
        rw [dif_neg hq_ne, dif_pos hq_K_max, dif_neg hα', dif_neg hdiv']
      rw [h_lhs_zero, h_rhs_zero]; ring
  · -- (p : 𝓞 K) ∉ q_K. Then (p : 𝓞 K) ∉ q either.
    have hp_in_q : (p : 𝓞 K) ∉ q := by
      intro h
      apply hp_in_qK
      rw [← hσ_q]
      have h_fix :
          cyclotomicRingOfIntegersEquiv (p := p) K a (p : 𝓞 K) = (p : 𝓞 K) := by
        change (cyclotomicRingOfIntegersEquiv (p := p) K a).toRingHom (p : 𝓞 K) =
          (p : 𝓞 K)
        rw [map_natCast]
      rw [← h_fix]
      exact (mem_cyclotomicGaloisConjugate_iff a).mpr h
    by_cases hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1
    · -- Good case: apply pthSymbolAtPrime_canonical_galoisAction.
      have h_galois :=
        pthSymbolAtPrime_canonical_galoisAction (p := p) (K := K) a α
          hq_ne_bot hq_max hα hp_in_q hdiv
      -- h_galois : pthSymbolAtPrime_canonical (σ_a α) (σ_a • q) =
      --              (a : ZMod p) * pthSymbolAtPrime_canonical α q
      -- σ_a • q = q_K.
      rw [show cyclotomicGaloisConjugate (p := p) (K := K) a q = q_K from hσ_q]
        at h_galois
      -- h_galois : pthSymbolAtPrime_canonical (σ_a α) q_K =
      --              (a : ZMod p) * pthSymbolAtPrime_canonical α q
      rw [h_galois]
      -- Goal: ↑a.val * x = (a : ZMod p) * x. Use ZMod.natCast_zmod_val.
      congr 1
      exact ZMod.natCast_zmod_val (a : ZMod p)
    · -- ¬hdiv: both sides are 0.
      have h_lhs_zero : pthSymbolAtPrime_canonical (p := p) (K := K) α q = 0 := by
        unfold pthSymbolAtPrime_canonical
        rw [dif_neg hq_ne_bot, dif_pos hq_max, dif_neg hα, dif_neg hdiv]
      have hdiv' : ¬ p ∣ Fintype.card (𝓞 K ⧸ q_K) - 1 := by
        intro h
        apply hdiv
        have h_card_q'q :
            Fintype.card (𝓞 K ⧸ q) = Fintype.card (𝓞 K ⧸ q_K) := by
          have := cyclotomicGaloisConjugate_quotient_card_eq a⁻¹ hq_ne
          simpa [hq_def] using this
        rw [h_card_q'q]; exact h
      have hα' : cyclotomicRingOfIntegersEquiv (p := p) K a α ∉ q_K := by
        rw [← hσ_q]
        exact (notMem_cyclotomicGaloisConjugate_iff a).mpr hα
      have h_rhs_zero :
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (cyclotomicRingOfIntegersEquiv (p := p) K a α) q_K = 0 := by
        unfold pthSymbolAtPrime_canonical
        rw [dif_neg hq_ne, dif_pos hq_K_max, dif_neg hα', dif_neg hdiv']
      rw [h_lhs_zero, h_rhs_zero]; ring

/-! ### c.3 unconditional closed form

The main theorem: combining the digit-sum expansion with the per-term
Galois transformation yields the unconditional closed form
```
pthSymbolAtPrincipal_canonical α γ = ∑_a pthSymbolAtPrime_canonical (σ_a α) q_K.
```
No `StickelbergerGaloisHypothesis` is needed: the explicit `(a : ZMod p)`
factor in the canonical Galois-action lemma cancels the `a.val` weight in
the digit sum. -/

/-- **c.3 unconditional closed form.** Given the c.1 input
`StickelbergerIdealEquality q_K`, the canonical principal symbol of `α`
at the Stickelberger generator equals the Galois-translated sum
```
∑_a pthSymbolAtPrime_canonical (σ_a α) q_K.
```
This is the c.3 closed-form theorem **without** any
`StickelbergerGaloisHypothesis` — the canonical version's explicit
Galois factor cancels the digit weights, eliminating the c.2 input.
This is the main payoff of using `pthSymbolAtPrime_canonical`. -/
theorem pthSymbolAtPrincipal_canonical_eq_galois_sum
    {q_K : Ideal (𝓞 K)} [q_K.IsPrime] (hq_ne : q_K ≠ ⊥)
    (h_stick : StickelbergerIdealEquality (p := p) (K := K) q_K)
    (α : 𝓞 K) :
    pthSymbolAtPrincipal_canonical (p := p) (K := K) α h_stick.gen =
      ∑ a : CyclotomicUnitDelta p,
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (cyclotomicRingOfIntegersEquiv (p := p) K a α) q_K := by
  classical
  rw [pthSymbolAtPrincipal_canonical_eq_stickelberger_sum (p := p) hq_ne h_stick α]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact pthSymbolAtPrime_canonical_term_eq a α hq_ne

/-! ### REF-19 canonical: principal symbol vanishing for hyperprimary singular

Combining the canonical KFR with `(η) = b^p` (singular η) gives that the
canonical residue symbol of η on any principal ideal `(γ)` (with γ
coprime to (η, p)) vanishes. This is the consumer-facing form for REF-19. -/

/-- **REF-19 canonical**: principal symbol triviality for singular hyperprimary `η`.

Given:
* `(η) = b^p` for some ideal `b` (singularity);
* a canonical KFR input `(η/(γ))_canonical = (γ/(η))_canonical`;
* `γ ≠ 0`,

the canonical residue symbol `(η/(γ))_canonical` vanishes in `ZMod p`.

Proof: by KFR canonical, `(η/(γ))_canonical = (γ/(η))_canonical = (γ/b^p)_canonical
= p · (γ/b)_canonical = 0`. -/
theorem pthSymbolAtPrincipal_canonical_eq_zero_of_kfr_singular
    {η γ : 𝓞 K} (B : Ideal (𝓞 K))
    (hsing : Ideal.span ({η} : Set (𝓞 K)) = B ^ p)
    (h_kfr : pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({γ} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) γ
        (Ideal.span ({η} : Set (𝓞 K)))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({γ} : Set (𝓞 K))) = 0 := by
  rw [h_kfr, hsing,
      pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero]

/-! ### Ideal-level canonical symbol API for `α`

These mirror the corresponding `pthSymbolAtIdeal` API lemmas
(`pthSymbolAtIdeal_one_alpha`, `_zero_alpha`, `_pow`, `_mul`) but for the
canonical symbol. Each one reduces, term-by-term over the prime factorization
of `I`, to the corresponding `pthSymbolAtPrime_canonical` lemma. -/

/-- **The canonical symbol of `1` at any ideal is `0`**. Each prime factor of
`I` is maximal and non-zero, so `pthSymbolAtPrime_canonical 1 P = 0`
term-by-term. -/
@[simp] theorem pthSymbolAtIdeal_canonical_one_alpha
    (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (1 : 𝓞 K) I = 0 := by
  unfold pthSymbolAtIdeal_canonical
  rw [show
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K) (1 : 𝓞 K) P)) =
      ((UniqueFactorizationMonoid.normalizedFactors I).map (fun _ => (0 : ZMod p)))
        from ?_]
  · simp
  · refine Multiset.map_congr rfl fun P hP => ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact pthSymbolAtPrime_canonical_one (p := p) (K := K) hP_ne_bot hP_max

/-- **The canonical symbol of `0` at any ideal is `0`**. For non-trivial primes,
`0 ∈ P` so `pthSymbolAtPrime_canonical 0 P = 0`; for `I = ⊥`, the sum is
empty. -/
@[simp] theorem pthSymbolAtIdeal_canonical_zero_alpha
    (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (0 : 𝓞 K) I = 0 := by
  unfold pthSymbolAtIdeal_canonical
  rw [show
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K) (0 : 𝓞 K) P)) =
      ((UniqueFactorizationMonoid.normalizedFactors I).map (fun _ => (0 : ZMod p)))
        from ?_]
  · simp
  · refine Multiset.map_congr rfl fun P hP => ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact pthSymbolAtPrime_canonical_eq_zero_of_mem (p := p) (K := K)
      hP_ne_bot hP_max P.zero_mem

/-- **Multiplicativity in `α` at the ideal level.** For non-zero `I` with
`α, β` coprime to every prime factor of `I`, the canonical symbol is
additive in the numerator. Reduces, term-by-term, to
`pthSymbolAtPrime_canonical_mul`. -/
theorem pthSymbolAtIdeal_canonical_mul_α
    {α β : 𝓞 K} {I : Ideal (𝓞 K)}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, α ∉ P)
    (hβ : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, β ∉ P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (α * β) I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α I +
        pthSymbolAtIdeal_canonical (p := p) (K := K) β I := by
  unfold pthSymbolAtIdeal_canonical
  have hmap :
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K) (α * β) P)) =
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K) α P +
          pthSymbolAtPrime_canonical (p := p) (K := K) β P)) := by
    refine Multiset.map_congr rfl fun P hP => ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact pthSymbolAtPrime_canonical_mul (p := p) (K := K)
      hP_ne_bot hP_max (hα P hP) (hβ P hP)
  rw [hmap, Multiset.sum_map_add]

/-- **Power form in the `α` slot at the ideal level.** Reduces, term-by-term,
to `pthSymbolAtPrime_canonical_pow`. -/
theorem pthSymbolAtIdeal_canonical_pow_α
    {α : 𝓞 K} {I : Ideal (𝓞 K)}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, α ∉ P)
    (n : ℕ) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (α ^ n) I =
      (n : ZMod p) * pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  unfold pthSymbolAtIdeal_canonical
  have hmap :
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K) (α ^ n) P)) =
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => (n : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K) α P)) := by
    refine Multiset.map_congr rfl fun P hP => ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    exact pthSymbolAtPrime_canonical_pow (p := p) (K := K)
      hP_ne_bot hP_max (hα P hP) n
  rw [hmap, Multiset.sum_map_mul_left]

/-- **Unconditional power form in the `α` slot**: holds without
coprimality. At primes where α ∈ P, both sides vanish (α^n ∈ P, so
pthSymbolAtPrime (α^n) P = 0; and pthSymbolAtPrime α P = 0 directly). -/
theorem pthSymbolAtIdeal_canonical_pow_α_uncond
    (α : 𝓞 K) (I : Ideal (𝓞 K)) (n : ℕ) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (α ^ n) I =
      (n : ZMod p) * pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  classical
  unfold pthSymbolAtIdeal_canonical
  have hmap :
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => pthSymbolAtPrime_canonical (p := p) (K := K) (α ^ n) P)) =
      ((UniqueFactorizationMonoid.normalizedFactors I).map
        (fun P => (n : ZMod p) *
          pthSymbolAtPrime_canonical (p := p) (K := K) α P)) := by
    refine Multiset.map_congr rfl fun P hP => ?_
    obtain ⟨_, hP_ne_bot, hP_max⟩ := isPrime_of_mem_normalizedFactors hP
    by_cases hα : α ∈ P
    · -- Both sides 0.
      haveI hP_prime : P.IsPrime := hP_max.isPrime
      have hα_pow : α ^ n ∈ P ∨ n = 0 := by
        by_cases hn : n = 0
        · right; exact hn
        · left; exact P.pow_mem_of_mem hα n (Nat.pos_of_ne_zero hn)
      rcases hα_pow with hα_pow | hn_zero
      · rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hP_ne_bot hP_max hα_pow,
          pthSymbolAtPrime_canonical_eq_zero_of_mem hP_ne_bot hP_max hα, mul_zero]
      · subst hn_zero
        rw [pow_zero, pthSymbolAtPrime_canonical_one hP_ne_bot hP_max,
          Nat.cast_zero, zero_mul]
    · exact pthSymbolAtPrime_canonical_pow (p := p) (K := K)
        hP_ne_bot hP_max hα n
  rw [hmap, Multiset.sum_map_mul_left]

/-- **Vanishing engine, ideal-pow-p in `α`.** `pthSymbolAtIdeal_canonical
(α^p) I = 0` whenever α is coprime to every prime factor of `I`. -/
theorem pthSymbolAtIdeal_canonical_pow_p_α_eq_zero
    {α : 𝓞 K} {I : Ideal (𝓞 K)}
    (hα : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, α ∉ P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (α ^ p) I = 0 := by
  rw [pthSymbolAtIdeal_canonical_pow_α (p := p) hα p, ZMod.natCast_self, zero_mul]

/-- **Unconditional ideal-level vanishing at `α^p`**: regardless of any
coprimality, `pthSymbolAtIdeal_canonical (α^p) I = 0` since each per-prime
contribution `pthSymbolAtPrime_canonical (α^p) P = 0`. -/
theorem pthSymbolAtIdeal_canonical_pow_p_α_eq_zero_uncond
    (α : 𝓞 K) (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (α ^ p) I = 0 := by
  unfold pthSymbolAtIdeal_canonical
  refine Multiset.sum_eq_zero ?_
  intro x hx
  obtain ⟨P, _, rfl⟩ := Multiset.mem_map.mp hx
  exact pthSymbolAtPrime_canonical_pow_p_eq_zero_uncond α P

/-- **Singular η: per-prime symbol vanishes at primes containing η**.
For η ∈ P (e.g., when P is a factor of `(η)` ideal, in particular when
`(η) = b^p` and P is a factor of b), the per-prime symbol vanishes. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_eta_mem
    {η : 𝓞 K} {P : Ideal (𝓞 K)} (hη : η ∈ P) :
    pthSymbolAtPrime_canonical (p := p) (K := K) η P = 0 := by
  by_cases hbot : P = ⊥
  · subst hbot; exact pthSymbolAtPrime_canonical_eq_zero_of_eq_bot _
  by_cases hmax : P.IsMaximal
  · exact pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hη
  · exact pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax

/-- **Symbol vanishes at any prime containing both `α` and `(η)` factor**.
Combines the in-prime case (η ∈ P) with the bot/non-maximal cases. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_eta_factor
    {η : 𝓞 K} {b P : Ideal (𝓞 K)}
    (h_eta : Ideal.span ({η} : Set (𝓞 K)) = b ^ p)
    (hP_b : b ≤ P) :
    pthSymbolAtPrime_canonical (p := p) (K := K) η P = 0 := by
  refine pthSymbolAtPrime_canonical_eq_zero_of_eta_mem ?_
  -- η ∈ P from b ≤ P + (η) ⊆ b^p ⊆ b ⊆ P.
  have hη_in_span : η ∈ Ideal.span ({η} : Set (𝓞 K)) :=
    Ideal.mem_span_singleton_self η
  rw [h_eta] at hη_in_span
  -- η ∈ b^p ⊆ b ⊆ P.
  have hb_pow_le : b ^ p ≤ b := by
    have hp_pos : 0 < p := (Fact.out : p.Prime).pos
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0) with ⟨k, hk⟩
    rw [hk, pow_succ]
    exact Ideal.mul_le_left
  exact hP_b (hb_pow_le hη_in_span)

/-- **Unconditional ideal-level vanishing at `-α^p` for odd p**: rewrites
`-α^p = (-α)^p` and applies the unconditional pow-p engine. -/
theorem pthSymbolAtIdeal_canonical_neg_pow_p_α_eq_zero_uncond_of_odd
    (hp_odd : Odd p) (α : 𝓞 K) (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (-α ^ p) I = 0 := by
  rw [show (-α ^ p) = (-α) ^ p from (Odd.neg_pow hp_odd α).symm]
  exact pthSymbolAtIdeal_canonical_pow_p_α_eq_zero_uncond (-α) I

/-- **Unit-times-α absorption at the ideal level**: if every per-prime
symbol of u vanishes (e.g., u is a `p`-th power, or u = ±1 for odd p),
then `pthSymbolAtIdeal_canonical (α · u) I = pthSymbolAtIdeal_canonical α I`.
The unit factor is absorbed term-by-term. -/
theorem pthSymbolAtIdeal_canonical_mul_unit_α_eq_self
    (α : 𝓞 K) {u : 𝓞 K} (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (α * u) I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  unfold pthSymbolAtIdeal_canonical
  refine congrArg Multiset.sum ?_
  refine Multiset.map_congr rfl fun P _ => ?_
  -- pthSymbolAtPrime_canonical (α · u) P = pthSymbolAtPrime_canonical α P
  -- via the canonical-symbol's behavior at each P:
  by_cases hbot : P = ⊥
  · subst hbot
    rw [pthSymbolAtPrime_canonical_eq_zero_of_eq_bot,
        pthSymbolAtPrime_canonical_eq_zero_of_eq_bot]
  by_cases hmax : P.IsMaximal
  · by_cases hα_in : α ∈ P
    · -- α ∈ P: both α and α·u are in P (since P is an ideal closed under mult).
      have hαu : α * u ∈ P := P.mul_mem_right u hα_in
      rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hα_in,
          pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hαu]
    · -- α ∉ P: need u ∉ P. Then mul splits.
      have hu_not : u ∉ P := fun h_in =>
        hmax.ne_top (Ideal.eq_top_of_isUnit_mem P h_in hu)
      rw [pthSymbolAtPrime_canonical_mul (p := p) (K := K) hbot hmax hα_in hu_not,
          hu_zero P, add_zero]
  · rw [pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax,
        pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax]

/-- **Unit times p-th-power local vanishing**: if a unit `u` has zero
canonical symbol at every prime, then `u · β^p` also has zero canonical symbol
at every prime. No unit hypothesis is needed on `β`; when `β ∈ P`, the
product is in `P`, and otherwise multiplicativity splits off the p-th power. -/
theorem pthSymbolAtPrime_canonical_unit_mul_pow_p_eq_zero
    {u β : 𝓞 K} (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (P : Ideal (𝓞 K)) :
    pthSymbolAtPrime_canonical (p := p) (K := K) (u * β ^ p) P = 0 := by
  by_cases hbot : P = ⊥
  · subst hbot
    exact pthSymbolAtPrime_canonical_eq_zero_of_eq_bot _
  by_cases hmax : P.IsMaximal
  · by_cases hβ_in : β ∈ P
    · have hβ_pow_in : β ^ p ∈ P := by
        have hp_pos : 0 < p := (Fact.out : p.Prime).pos
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0) with ⟨k, hk⟩
        rw [hk, pow_succ]
        exact Ideal.mul_mem_left _ _ hβ_in
      exact pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax
        (P.mul_mem_left u hβ_pow_in)
    · have hu_not : u ∉ P := fun h_in =>
        hmax.ne_top (Ideal.eq_top_of_isUnit_mem P h_in hu)
      have hβ_pow_not : β ^ p ∉ P := fun hβ_pow_in =>
        hβ_in (hmax.isPrime.mem_of_pow_mem p hβ_pow_in)
      rw [pthSymbolAtPrime_canonical_mul (p := p) (K := K)
        hbot hmax hu_not hβ_pow_not,
        hu_zero P, pthSymbolAtPrime_canonical_pow_p_eq_zero_uncond β P,
        zero_add]
  · exact pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax

/-- **Unit-pow-p numerator absorption at the ideal level**: multiplying the
numerator by `u · β^p` does not change the canonical ideal symbol when `u` and
`β` are units and the local symbols of `u` vanish everywhere. -/
theorem pthSymbolAtIdeal_canonical_mul_unit_pow_p_unit_α_eq_self
    (α : 𝓞 K) {u β : 𝓞 K} (hu : IsUnit u) (hβ : IsUnit β)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (α * (u * β ^ p)) I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α I :=
  pthSymbolAtIdeal_canonical_mul_unit_α_eq_self α (hu.mul (hβ.pow p))
    (fun P => pthSymbolAtPrime_canonical_unit_mul_pow_p_eq_zero hu hu_zero P) I

/-- **Support-controlled unit/p-th-power numerator absorption.**

The `β` factor need not be a unit. It is enough that every prime containing
`β` also contains `α`: at those primes the symbol of `α` already vanishes; at
the remaining primes, multiplicativity splits off the `p`-th power. -/
theorem pthSymbolAtIdeal_canonical_mul_unit_pow_p_of_support_subset_α_eq_self
    (α : 𝓞 K) {u β : 𝓞 K} (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (hβ_support : ∀ P : Ideal (𝓞 K), P.IsPrime → β ∈ P → α ∈ P)
    (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) (α * (u * β ^ p)) I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  unfold pthSymbolAtIdeal_canonical
  refine congrArg Multiset.sum ?_
  refine Multiset.map_congr rfl fun P _ => ?_
  by_cases hbot : P = ⊥
  · subst hbot
    rw [pthSymbolAtPrime_canonical_eq_zero_of_eq_bot,
      pthSymbolAtPrime_canonical_eq_zero_of_eq_bot]
  by_cases hmax : P.IsMaximal
  · by_cases hα_in : α ∈ P
    · have hα_mul : α * (u * β ^ p) ∈ P := P.mul_mem_right (u * β ^ p) hα_in
      rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hα_mul,
        pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hα_in]
    · have hβ_not : β ∉ P := fun hβ_in => hα_in (hβ_support P hmax.isPrime hβ_in)
      have hu_not : u ∉ P := fun hu_in =>
        hmax.ne_top (Ideal.eq_top_of_isUnit_mem P hu_in hu)
      have hβ_pow_not : β ^ p ∉ P := fun hβ_pow_in =>
        hβ_not (hmax.isPrime.mem_of_pow_mem p hβ_pow_in)
      have hunit_pow_not : u * β ^ p ∉ P := by
        intro hmul
        rcases hmax.isPrime.mem_or_mem hmul with hu_in | hβp_in
        · exact hu_not hu_in
        · exact hβ_pow_not hβp_in
      rw [pthSymbolAtPrime_canonical_mul (p := p) (K := K)
        hbot hmax hα_in hunit_pow_not,
        pthSymbolAtPrime_canonical_unit_mul_pow_p_eq_zero hu hu_zero P,
        add_zero]
  · rw [pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax,
      pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax]

omit [NumberField K] in
/-- A divisibility/radical-style sufficient condition for prime support:
if `(α^n) ≤ (β)`, then every prime containing `β` contains `α`. -/
theorem prime_support_subset_of_span_pow_le_span
    {α β : 𝓞 K} {n : ℕ}
    (hspan : Ideal.span ({α ^ n} : Set (𝓞 K)) ≤
      Ideal.span ({β} : Set (𝓞 K))) :
    ∀ P : Ideal (𝓞 K), P.IsPrime → β ∈ P → α ∈ P := by
  intro P hP_prime hβ_in
  have hβ_le : Ideal.span ({β} : Set (𝓞 K)) ≤ P :=
    (Ideal.span_singleton_le_iff_mem (I := P)).mpr hβ_in
  have hα_pow_in : α ^ n ∈ P :=
    hβ_le (hspan (Ideal.mem_span_singleton_self (α ^ n)))
  exact hP_prime.mem_of_pow_mem n hα_pow_in

/-- Left-associated form of
`pthSymbolAtIdeal_canonical_mul_unit_pow_p_unit_α_eq_self`. -/
theorem pthSymbolAtIdeal_canonical_mul_unit_mul_pow_p_unit_α_eq_self
    (α : 𝓞 K) {u β : 𝓞 K} (hu : IsUnit u) (hβ : IsUnit β)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (I : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) ((α * u) * β ^ p) I =
      pthSymbolAtIdeal_canonical (p := p) (K := K) α I := by
  simpa [mul_assoc] using
    pthSymbolAtIdeal_canonical_mul_unit_pow_p_unit_α_eq_self
      (p := p) (K := K) α hu hβ hu_zero I

/-- **Canonical symbol of the inverse of a unit**: at every prime, the symbol
of `u⁻¹` is the negative of the symbol of `u`. -/
theorem pthSymbolAtPrime_canonical_isUnit_inv_eq_neg
    {u : 𝓞 K} (hu : IsUnit u) (P : Ideal (𝓞 K)) :
    pthSymbolAtPrime_canonical (p := p) (K := K)
        (((hu.unit⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) P =
      -pthSymbolAtPrime_canonical (p := p) (K := K) u P := by
  by_cases hbot : P = ⊥
  · subst hbot
    rw [pthSymbolAtPrime_canonical_eq_zero_of_eq_bot,
      pthSymbolAtPrime_canonical_eq_zero_of_eq_bot, neg_zero]
  by_cases hmax : P.IsMaximal
  · have hu_not : u ∉ P := fun h_in =>
      hmax.ne_top (Ideal.eq_top_of_isUnit_mem P h_in hu)
    have hinv_not : (((hu.unit⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) ∉ P := fun h_in =>
      hmax.ne_top
        (Ideal.eq_top_of_isUnit_mem P h_in (hu.unit⁻¹).isUnit)
    have hmul :=
      pthSymbolAtPrime_canonical_mul (p := p) (K := K)
        hbot hmax hu_not hinv_not
    have hmul_one : u * (((hu.unit⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) = 1 :=
      IsUnit.mul_val_inv hu
    rw [hmul_one, pthSymbolAtPrime_canonical_one (p := p) (K := K) hbot hmax] at hmul
    rw [eq_neg_iff_add_eq_zero]
    simpa [add_comm] using hmul.symm
  · rw [pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax,
      pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal _ hbot hmax, neg_zero]

/-- If a unit has trivial canonical symbol at every prime, so does its inverse. -/
theorem pthSymbolAtPrime_canonical_isUnit_inv_eq_zero
    {u : 𝓞 K} (hu : IsUnit u)
    (hu_zero : ∀ P : Ideal (𝓞 K),
      pthSymbolAtPrime_canonical (p := p) (K := K) u P = 0)
    (P : Ideal (𝓞 K)) :
    pthSymbolAtPrime_canonical (p := p) (K := K)
      (((hu.unit⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) P = 0 := by
  rw [pthSymbolAtPrime_canonical_isUnit_inv_eq_neg (p := p) (K := K) hu P,
    hu_zero P, neg_zero]

/-! ### Principal-level canonical symbol API

Mirror of the principal-level API in `KummerFurtwaengler.lean`. These lemmas
directly reduce to the ideal-level versions, since
`pthSymbolAtPrincipal_canonical α β = pthSymbolAtIdeal_canonical α (Ideal.span {β})`. -/

end Furtwaengler

end BernoulliRegular
