/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Molteni's linear-independence lemma for multiplicative functions

This file proves a purely arithmetic linear-independence theorem, due in essence to
G. Molteni (*L-functions for GL_n*, and folklore for Hecke eigensystems): **pairwise
non-equivalent multiplicative functions `ℕ → ℂ` are `ℂ`-linearly independent.**

The notion of *equivalence* is the right one for Hecke eigensystems: two multiplicative
functions are equivalent if they agree on `p^a` (`a ≥ 1`) for **all but finitely many**
primes `p`.  This is exactly the hypothesis that survives the inductive "delete one prime"
step in Molteni's argument, and is what Strong Multiplicity One supplies for genuine Hecke
eigensystems (distinct eigensystems differ at infinitely many primes).

Note that *bare* multiplicativity is insufficient for linear independence (e.g. over a single
prime `p` the multiplicative functions with values `1,2,3` at `p` and `5,7,9` at `p²`, `1`
elsewhere, satisfy `f₁ − 2f₂ + f₃ = 0`); the non-equivalence hypothesis is essential.

## Main definitions

* `IsMultiplicative'` — `F 1 = 1` and `F (m*n) = F m * F n` for coprime `m, n`.
* `Equiv'` — `F` and `G` agree at every prime power outside a finite set of primes.

## Main result

* `linearIndependent_of_pairwise_not_equiv'` — pairwise non-`Equiv'` multiplicative functions
  are `ℂ`-linearly independent (in the zero-extended `∑ cᵢ Fᵢ n = 0 ∀ n ⟹ cᵢ = 0` form).
-/

namespace HeckeRing.GL2.Molteni

open scoped BigOperators

/-- A function `F : ℕ → ℂ` is *multiplicative* (in the elementary sense used here): `F 1 = 1`
and `F (m * n) = F m * F n` whenever `m, n` are coprime. -/
def IsMultiplicative' (F : ℕ → ℂ) : Prop :=
  F 1 = 1 ∧ ∀ m n : ℕ, Nat.Coprime m n → F (m * n) = F m * F n

namespace IsMultiplicative'

theorem one {F : ℕ → ℂ} (hF : IsMultiplicative' F) : F 1 = 1 := hF.1

theorem map_mul_of_coprime {F : ℕ → ℂ} (hF : IsMultiplicative' F) {m n : ℕ}
    (h : Nat.Coprime m n) : F (m * n) = F m * F n := hF.2 m n h

/-- The *prime restriction* `F^{(p)}` of `F`: equal to `F n` when `p ∤ n` and `0` otherwise.
It is again multiplicative, and deleting the single prime `p` is the inductive step in
Molteni's argument. -/
def primeRestrict (p : ℕ) (F : ℕ → ℂ) : ℕ → ℂ :=
  fun n => if p ∣ n then 0 else F n

@[simp] theorem primeRestrict_of_dvd {p : ℕ} {F : ℕ → ℂ} {n : ℕ} (h : p ∣ n) :
    primeRestrict p F n = 0 := if_pos h

theorem primeRestrict_of_not_dvd {p : ℕ} {F : ℕ → ℂ} {n : ℕ} (h : ¬ p ∣ n) :
    primeRestrict p F n = F n := if_neg h

/-- The prime restriction of a multiplicative function is multiplicative. -/
theorem isMultiplicative'_primeRestrict {p : ℕ} (hp : p.Prime) {F : ℕ → ℂ}
    (hF : IsMultiplicative' F) :
    IsMultiplicative' (primeRestrict p F) := by
  refine ⟨?_, ?_⟩
  · rw [primeRestrict_of_not_dvd (by simpa using hp.one_lt.ne'), hF.one]
  · intro m n h
    by_cases hmn : p ∣ m * n
    · rw [IsMultiplicative'.primeRestrict_of_dvd hmn]
      rcases (hp.dvd_mul.mp hmn) with hm | hn
      · rw [IsMultiplicative'.primeRestrict_of_dvd hm, zero_mul]
      · rw [IsMultiplicative'.primeRestrict_of_dvd hn, mul_zero]
    · have hm : ¬ p ∣ m := fun h' => hmn (h'.mul_right n)
      have hn : ¬ p ∣ n := fun h' => hmn (h'.mul_left m)
      rw [primeRestrict_of_not_dvd hmn, primeRestrict_of_not_dvd hm,
        primeRestrict_of_not_dvd hn, hF.map_mul_of_coprime h]

end IsMultiplicative'

/-- Two functions are *equivalent* if they agree at every prime power `p^a` (`a ≥ 1`) for all
but finitely many primes `p`.  Equivalently, the set of "bad" primes (those `p` at which some
positive power `p^a` separates `F` and `G`) is finite. -/
def Equiv' (F G : ℕ → ℂ) : Prop :=
  {p : ℕ | p.Prime ∧ ∃ a : ℕ, 1 ≤ a ∧ F (p ^ a) ≠ G (p ^ a)}.Finite

/-- The set of "bad" primes separating `F` and `G`. -/
def badPrimes (F G : ℕ → ℂ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ ∃ a : ℕ, 1 ≤ a ∧ F (p ^ a) ≠ G (p ^ a)}

theorem equiv'_iff (F G : ℕ → ℂ) : Equiv' F G ↔ (badPrimes F G).Finite := Iff.rfl

theorem not_equiv'_iff (F G : ℕ → ℂ) : ¬ Equiv' F G ↔ (badPrimes F G).Infinite := by
  rw [equiv'_iff, Set.not_infinite.symm]; tauto

/-- Two multiplicative functions that agree on all positive powers of all primes are equal
on every positive natural. -/
theorem eq_of_eq_on_prime_powers {F G : ℕ → ℂ} (hF : IsMultiplicative' F)
    (hG : IsMultiplicative' G)
    (h : ∀ p : ℕ, p.Prime → ∀ a : ℕ, 1 ≤ a → F (p ^ a) = G (p ^ a)) :
    ∀ n : ℕ, 1 ≤ n → F n = G n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_lt_of_le hn with h1 | h1
    · rw [← h1, hF.one, hG.one]
    -- `n ≥ 2`: factor off the smallest prime power.
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    -- write `n = p^a * m` with `p ∤ m`, `a = v_p(n) ≥ 1`.
    set a := n.factorization p with ha
    have ha1 : 1 ≤ a := by
      rw [ha, ← Nat.Prime.dvd_iff_one_le_factorization hp (by omega)]; exact hpn
    set m := n / p ^ a with hm
    have hpa_dvd : p ^ a ∣ n := Nat.ordProj_dvd n p
    have hm_pos : 1 ≤ m := by
      rw [hm]; exact Nat.one_le_div_iff (pow_pos hp.pos a) |>.mpr (Nat.le_of_dvd (by omega) hpa_dvd)
    have hfac : p ^ a * m = n := Nat.mul_div_cancel' hpa_dvd
    have hn0 : n ≠ 0 := by omega
    have hcop : Nat.Coprime (p ^ a) m := by
      have := (Nat.coprime_ordCompl hp hn0).pow_left a
      rw [ha, hm]; exact this
    by_cases hm1 : m = 1
    · -- `n = p^a`.
      rw [hm1, mul_one] at hfac
      rw [← hfac]; exact h p hp a ha1
    · -- proper factorisation: both factors are smaller, apply IH multiplicatively.
      have ha1' : a ≠ 0 := by omega
      have hpa1 : 1 < p ^ a := Nat.one_lt_pow ha1' hp.one_lt
      have hm_pos' : 0 < m := hm_pos
      have hm_lt : m < n := by
        calc m = 1 * m := (one_mul m).symm
          _ < p ^ a * m := Nat.mul_lt_mul_of_lt_of_le hpa1 le_rfl hm_pos'
          _ = n := hfac
      rw [← hfac, hF.map_mul_of_coprime hcop, hG.map_mul_of_coprime hcop,
        h p hp a ha1, ih m hm_lt hm_pos]

/-- Deleting one prime `p` from the bad-prime set preserves infinitude: the bad primes of the
prime-restrictions `F^{(p)}, G^{(p)}` are exactly the bad primes of `F, G` other than `p`. -/
theorem badPrimes_primeRestrict_eq {p : ℕ} (hp : p.Prime) (F G : ℕ → ℂ) :
    badPrimes (IsMultiplicative'.primeRestrict p F) (IsMultiplicative'.primeRestrict p G) =
      badPrimes F G \ {p} := by
  ext q
  simp only [badPrimes, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq, a, ha1, hne⟩
    -- `q` separates the restrictions ⟹ `q ≠ p` (else both sides are `0`) and `q` separates `F,G`.
    have hqp : q ≠ p := by
      rintro rfl
      exact hne (by rw [IsMultiplicative'.primeRestrict_of_dvd ⟨q ^ (a - 1), by
        rw [← pow_succ']; congr 1; omega⟩,
        IsMultiplicative'.primeRestrict_of_dvd ⟨q ^ (a - 1), by
        rw [← pow_succ']; congr 1; omega⟩])
    have hpq : ¬ p ∣ q ^ a := by
      intro h
      have hdvd := hp.dvd_of_dvd_pow h
      rw [Nat.prime_dvd_prime_iff_eq hp hq] at hdvd
      exact hqp hdvd.symm
    refine ⟨⟨hq, a, ha1, ?_⟩, hqp⟩
    rwa [IsMultiplicative'.primeRestrict_of_not_dvd hpq,
      IsMultiplicative'.primeRestrict_of_not_dvd hpq] at hne
  · rintro ⟨⟨hq, a, ha1, hne⟩, hqp⟩
    have hpq : ¬ p ∣ q ^ a := by
      intro h
      have hdvd := hp.dvd_of_dvd_pow h
      rw [Nat.prime_dvd_prime_iff_eq hp hq] at hdvd
      exact hqp hdvd.symm
    refine ⟨hq, a, ha1, ?_⟩
    rwa [IsMultiplicative'.primeRestrict_of_not_dvd hpq,
      IsMultiplicative'.primeRestrict_of_not_dvd hpq]

/-- Non-equivalence is preserved by deleting one prime. -/
theorem not_equiv'_primeRestrict {p : ℕ} (hp : p.Prime) {F G : ℕ → ℂ}
    (h : ¬ Equiv' F G) :
    ¬ Equiv' (IsMultiplicative'.primeRestrict p F) (IsMultiplicative'.primeRestrict p G) := by
  rw [not_equiv'_iff] at h ⊢
  rw [badPrimes_primeRestrict_eq hp]
  exact h.diff (Set.finite_singleton p)

/-- **Molteni's linear-independence lemma, all-nonzero (support) form.**  Strong induction on
`|s|` proving the contrapositive: a family of pairwise non-equivalent multiplicative functions
indexed by a finite set `s`, *all* of whose coefficients are nonzero, cannot satisfy a vanishing
relation `∑_{i ∈ s} cᵢ Fᵢ(n) = 0` for all `n ≥ 1` — unless `s = ∅`. -/
theorem support_eq_empty_of_pairwise_not_equiv'
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℕ → ℂ)
    (hmul : ∀ i ∈ s, IsMultiplicative' (F i))
    (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Equiv' (F i) (F j))
    (c : ι → ℂ) (hc : ∀ i ∈ s, c i ≠ 0)
    (hrel : ∀ n : ℕ, 1 ≤ n → ∑ i ∈ s, c i * F i n = 0) :
    s = ∅ := by
  classical
  induction hcard : s.card using Nat.strong_induction_on generalizing s F c with
  | _ N ih =>
  subst hcard
  rcases Finset.eq_empty_or_nonempty s with hs | ⟨r, hrs⟩
  · exact hs
  exfalso
  -- Pick `r ∈ s`.  Goal: derive that every other `i ∈ s` has `F i ≃ F r`, contradicting `hne`,
  -- OR that `s = {r}`, contradicting the `n = 1` base relation (which gives `c r = 0`).
  -- **Claim**: for every prime `p` and `a ≥ 1`, and every `i ∈ s`, `F i (p^a) = F r (p^a)`.
  have hkey : ∀ p : ℕ, p.Prime → ∀ a : ℕ, 1 ≤ a → ∀ i ∈ s, F i (p ^ a) = F r (p ^ a) := by
    intro p hp a ha1 i his
    -- The prime-restricted relation `∑_{i ∈ s} cᵢ (Fᵢ(p^a) − Fᵣ(p^a)) · Fᵢ^{(p)}(n) = 0 ∀ n`.
    set c' : ι → ℂ := fun i => c i * (F i (p ^ a) - F r (p ^ a)) with hc'_def
    set G : ι → ℕ → ℂ := fun i => IsMultiplicative'.primeRestrict p (F i) with hG_def
    -- `s' = s \ {r}` is the support of `c'` restricted to potentially-nonzero terms.
    set s' : Finset ι := (s.erase r).filter (fun i => c' i ≠ 0) with hs'_def
    have hs'_sub : s' ⊆ s := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    have hmem_s' : ∀ i, i ∈ s' ↔ (i ∈ s ∧ i ≠ r) ∧ c' i ≠ 0 := fun i => by
      simp only [hs'_def, Finset.mem_filter, Finset.mem_erase]; tauto
    -- The relation for the restricted family.
    have hrel' : ∀ n : ℕ, 1 ≤ n → ∑ i ∈ s', c' i * G i n = 0 := by
      intro n hn
      by_cases hpn : p ∣ n
      · -- `p ∣ n`: every `G i n = 0`.
        apply Finset.sum_eq_zero
        intro i _
        simp only [hG_def, IsMultiplicative'.primeRestrict_of_dvd hpn, mul_zero]
      · -- `p ∤ n`: `G i n = F i n`; expand `c'` and use `rel(p^a n) − F r(p^a) · rel(n) = 0`.
        have hpan : Nat.Coprime (p ^ a) n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn |>.pow_left a
        have hpan_pos : 1 ≤ p ^ a * n := Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (pow_pos hp.pos a).ne' (by omega))
        have hrelpan := hrel (p ^ a * n) hpan_pos
        have hreln := hrel n hn
        -- `∑_{i∈s} cᵢ Fᵢ(p^a) Fᵢ(n) = 0`.
        have hexp : ∑ i ∈ s, c i * (F i (p ^ a) * F i n) = 0 := by
          rw [← hrelpan]
          apply Finset.sum_congr rfl
          intro i his'
          rw [(hmul i his').map_mul_of_coprime hpan]
        -- Subtract `F r(p^a) · rel(n)`: `∑_{i∈s} c' i · F i n = 0`.
        have hsub : ∑ i ∈ s, c' i * F i n = 0 := by
          have heq : ∑ i ∈ s, c' i * F i n =
              (∑ i ∈ s, c i * (F i (p ^ a) * F i n)) -
                F r (p ^ a) * ∑ i ∈ s, c i * F i n := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i _; simp only [hc'_def]; ring
          rw [heq, hexp, hreln, mul_zero, sub_zero]
        -- Restrict to `s'`: the dropped terms (in `s \ s'`) have `c' i = 0`, and `G i n = F i n`.
        rw [show (∑ i ∈ s', c' i * G i n) = ∑ i ∈ s', c' i * F i n from by
          apply Finset.sum_congr rfl
          intro i _; simp only [hG_def, IsMultiplicative'.primeRestrict_of_not_dvd hpn]]
        rw [← hsub]
        apply Finset.sum_subset hs'_sub
        intro i hi_s hi_s'
        rw [show c' i = 0 from by
          by_contra hne0
          exact hi_s' ((hmem_s' i).mpr ⟨⟨hi_s, by
            rintro rfl; exact hne0 (by simp only [hc'_def]; ring)⟩, hne0⟩), zero_mul]
    -- Apply the induction hypothesis to `s'` (strictly smaller card).
    have hs'_card : s'.card < s.card :=
      lt_of_le_of_lt
        (Finset.card_le_card (Finset.filter_subset (fun i => c' i ≠ 0) (s.erase r)))
        (Finset.card_erase_lt_of_mem hrs)
    have hs'_empty : s' = ∅ :=
      ih s'.card hs'_card s' G
        (fun i hi => IsMultiplicative'.isMultiplicative'_primeRestrict hp (hmul i (hs'_sub hi)))
        (fun i hi j hj hij =>
          not_equiv'_primeRestrict hp (hne i (hs'_sub hi) j (hs'_sub hj) hij))
        c' (fun i hi => ((hmem_s' i).mp hi).2) hrel' rfl
    -- So for every `i ∈ s`, `i ≠ r`, `c' i = 0`, hence `F i (p^a) = F r (p^a)` (as `c i ≠ 0`).
    by_cases hir : i = r
    · rw [hir]
    · have hi_er : i ∈ s.erase r := Finset.mem_erase.mpr ⟨hir, his⟩
      have hc'i0 : c i * (F i (p ^ a) - F r (p ^ a)) = 0 := by
        by_contra hne0
        have hmem : i ∈ s' := (hmem_s' i).mpr ⟨⟨his, hir⟩, by simpa only [hc'_def] using hne0⟩
        rw [hs'_empty] at hmem
        exact absurd hmem (Finset.notMem_empty i)
      rcases mul_eq_zero.mp hc'i0 with h | h
      · exact absurd h (hc i his)
      · exact sub_eq_zero.mp h
  -- From `hkey`: every `i ∈ s` has `F i = F r` on prime powers, hence (multiplicativity) `F i ≃ F r`.
  -- Case on whether `s` has an element other than `r`.
  by_cases hcard1 : 1 < s.card
  · -- Another element `i ≠ r` exists; `F i ≃ F r` contradicts non-equivalence.
    obtain ⟨i, his, hir⟩ : ∃ i ∈ s, i ≠ r := by
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard1
      rcases eq_or_ne i r with rfl | h
      · exact ⟨j, hj, fun h => hij h.symm⟩
      · exact ⟨i, hi, h⟩
    refine hne i his r hrs hir ?_
    -- `F i` and `F r` agree on all prime powers ⟹ equal on positives ⟹ equivalent (bad set ∅).
    have hagree : ∀ p : ℕ, p.Prime → ∀ a : ℕ, 1 ≤ a → F i (p ^ a) = F r (p ^ a) :=
      fun p hp a ha => hkey p hp a ha i his
    rw [equiv'_iff]
    convert Set.finite_empty
    rw [badPrimes, Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hq, a, ha1, hne_q⟩
    exact hne_q (hagree q hq a ha1)
  · -- `s = {r}`: relation at `n = 1` gives `c r · F r 1 = c r = 0`, contradicting `c r ≠ 0`.
    have hcard_eq : s.card = 1 := le_antisymm (by omega) (Finset.card_pos.mpr ⟨r, hrs⟩)
    have hs_single : s = {r} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hrs, fun x hx => Finset.card_le_one.mp (by omega) x hx r hrs⟩
    have h1 := hrel 1 le_rfl
    rw [hs_single, Finset.sum_singleton, (hmul r hrs).one, mul_one] at h1
    exact absurd h1 (hc r hrs)

/-- **Molteni's linear-independence lemma (`Fintype` form).**  Pairwise non-equivalent
multiplicative functions `F : ι → ℕ → ℂ` (indexed by a `Fintype`) are `ℂ`-linearly independent in
the zero-extended sense: if `∑ᵢ cᵢ Fᵢ(n) = 0` for every `n ≥ 1`, then every `cᵢ = 0`. -/
theorem linearIndependent_of_pairwise_not_equiv'
    {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℕ → ℂ)
    (hmul : ∀ i, IsMultiplicative' (F i))
    (hne : ∀ i j, i ≠ j → ¬ Equiv' (F i) (F j))
    (c : ι → ℂ) (hrel : ∀ n : ℕ, 1 ≤ n → ∑ i, c i * F i n = 0) :
    ∀ i, c i = 0 := by
  classical
  -- The support of `c`.
  set s : Finset ι := Finset.univ.filter (fun i => c i ≠ 0) with hs_def
  -- The relation restricted to the support equals the full relation (dropped terms vanish).
  have hrels : ∀ n : ℕ, 1 ≤ n → ∑ i ∈ s, c i * F i n = 0 := by
    intro n hn
    rw [← hrel n hn]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    rw [show c i = 0 from by
      by_contra h; exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩), zero_mul]
  have hsupp_ne : ∀ i ∈ s, c i ≠ 0 := fun i hi => (Finset.mem_filter.mp hi).2
  have hempty : s = ∅ :=
    support_eq_empty_of_pairwise_not_equiv' s F (fun i _ => hmul i)
      (fun i _ j _ hij => hne i j hij) c hsupp_ne hrels
  intro i
  by_contra hci
  have : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hci⟩
  rw [hempty] at this
  exact absurd this (Finset.notMem_empty i)

end HeckeRing.GL2.Molteni
