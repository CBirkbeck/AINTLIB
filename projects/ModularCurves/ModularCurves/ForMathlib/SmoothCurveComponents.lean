/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# A ring with local domains has comaximal minimal primes (WP-D3a-DOM)

`IsIntegrallyClosed` — and mathlib's `isIntegrallyClosed_ofLocalizationMaximal` — require
`IsDomain`, but the universal base of the Weil-pairing construction is a smooth affine curve
that need not be connected (its connectedness is the irreducibility of the modular curve,
which is out of scope). The fix is to work component by component, and the ring-level form of
"finitely many clopen components, each integral" is a product decomposition over the minimal
primes.

The step here is the one with content: **two minimal primes inside a common maximal ideal
coincide**, as soon as the localization at that maximal ideal is a domain. Everything the
decomposition needs after that is comaximality, which is the contrapositive.

The argument is elementary — no order isomorphism of prime spectra is involved. If `A_m` is a
domain then `⊥` is prime, and its contraction `P₀ := (algebraMap A A_m)⁻¹(⊥)` is a prime of
`A` contained in *every* prime `r ≤ m`: an element killed by some `s ∉ m` lies in `r` because
`r` is prime and `s ∉ r`. Minimality of `r` then forces `r = P₀`, so all minimal primes below
`m` are the same one.
-/

universe u

namespace ModularCurves

variable {A : Type u} [CommRing A]

/-- The contraction of `⊥` along `A ⟶ A_m` sits inside every prime contained in `m`: if
`s * a = 0` with `s ∉ m`, then `s ∉ r` for `r ≤ m`, so primality gives `a ∈ r`. -/
theorem comap_bot_localizationAtPrime_le (m : Ideal A) [m.IsPrime] {r : Ideal A} [r.IsPrime]
    (hrm : r ≤ m) :
    Ideal.comap (algebraMap A (Localization.AtPrime m)) ⊥ ≤ r := by
  intro a ha
  have ha0 : algebraMap A (Localization.AtPrime m) a = 0 := by
    simpa using ha
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl _ a).mp ha0
  have hsr : (s : A) ∉ r := fun h => s.2 (hrm h)
  rcases (Ideal.IsPrime.mem_or_mem ‹r.IsPrime› (hs ▸ r.zero_mem)) with h | h
  · exact absurd h hsr
  · exact h

/-- **(WP-D3a-DOM, the content)** If the localization at a maximal ideal `m` is a domain, then
all minimal primes contained in `m` coincide — each of them is the contraction of `⊥`. -/
theorem eq_comap_bot_of_mem_minimalPrimes (m : Ideal A) [m.IsPrime]
    [IsDomain (Localization.AtPrime m)] {r : Ideal A} (hr : r ∈ minimalPrimes A)
    (hrm : r ≤ m) :
    r = Ideal.comap (algebraMap A (Localization.AtPrime m)) ⊥ := by
  haveI : r.IsPrime := hr.1.1
  haveI : (Ideal.comap (algebraMap A (Localization.AtPrime m)) (⊥ : Ideal
      (Localization.AtPrime m))).IsPrime :=
    Ideal.comap_isPrime _ _
  exact (hr.2 ⟨inferInstance, bot_le⟩ (comap_bot_localizationAtPrime_le m hrm)).antisymm
    (comap_bot_localizationAtPrime_le m hrm)

/-- **(WP-D3a-DOM)** Two minimal primes inside a common prime `m` whose localization is a
domain are equal. -/
theorem eq_of_mem_minimalPrimes_of_le (m : Ideal A) [m.IsPrime]
    [IsDomain (Localization.AtPrime m)] {p q : Ideal A} (hp : p ∈ minimalPrimes A)
    (hq : q ∈ minimalPrimes A) (hpm : p ≤ m) (hqm : q ≤ m) :
    p = q :=
  (eq_comap_bot_of_mem_minimalPrimes m hp hpm).trans
    (eq_comap_bot_of_mem_minimalPrimes m hq hqm).symm

/-- **(WP-D3a-DOM)** …hence distinct minimal primes are **comaximal**, which is the input the
Chinese-remainder decomposition needs. -/
theorem sup_eq_top_of_ne_of_mem_minimalPrimes
    (hloc : ∀ (m : Ideal A) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    {p q : Ideal A} (hp : p ∈ minimalPrimes A) (hq : q ∈ minimalPrimes A) (hne : p ≠ q) :
    p ⊔ q = ⊤ := by
  by_contra hsup
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hsup
  haveI := hm
  haveI := hloc m
  exact hne (eq_of_mem_minimalPrimes_of_le m hp hq (le_sup_left.trans hle)
    (le_sup_right.trans hle))

/-- **(WP-D3a-DOM)** The minimal primes, indexed by the subtype, are pairwise coprime — the
hypothesis of the Chinese remainder theorem and of `Ideal.pi_quotient_surjective`. -/
theorem pairwise_isCoprime_minimalPrimes
    (hloc : ∀ (m : Ideal A) [m.IsMaximal], IsDomain (Localization.AtPrime m)) :
    Pairwise (Function.onFun IsCoprime
      (fun p : {p : Ideal A // p ∈ minimalPrimes A} => (p : Ideal A))) := by
  intro p q hpq
  exact Ideal.isCoprime_iff_sup_eq.mpr
    (sup_eq_top_of_ne_of_mem_minimalPrimes hloc p.2 q.2 (Subtype.coe_ne_coe.mpr hpq))

/-- **(WP-D3a-DOM)** A ring whose localizations at maximal ideals are domains is reduced.
Domains are reduced, and reducedness is a local property at the maximal ideals. -/
theorem isReduced_of_localizationAtPrime_isDomain
    (hloc : ∀ (m : Ideal A) [m.IsMaximal], IsDomain (Localization.AtPrime m)) :
    IsReduced A :=
  isReduced_ofLocalizationMaximal A fun m hm => by
    haveI := hm
    haveI := hloc m
    infer_instance

/-- **(WP-D3a-DOM)** …and its minimal primes therefore intersect in `⊥`: the intersection of
the minimal primes over `⊥` is the radical of `⊥`, which is the nilradical. -/
theorem sInf_minimalPrimes_eq_bot
    (hloc : ∀ (m : Ideal A) [m.IsMaximal], IsDomain (Localization.AtPrime m)) :
    sInf (minimalPrimes A) = ⊥ := by
  haveI := isReduced_of_localizationAtPrime_isDomain hloc
  have h : sInf (Ideal.minimalPrimes (⊥ : Ideal A)) = (⊥ : Ideal A).radical :=
    Ideal.sInf_minimalPrimes
  exact h.trans (nilradical_eq_zero A)

/-- **(WP-D3a-DOM)** The map to the product over the minimal primes is injective. Together
with `Ideal.pi_quotient_surjective` applied to `pairwise_isCoprime_minimalPrimes`, this is the
product decomposition `A ≅ ∏ A ⧸ pᵢ` in the two forms downstream needs: a value can be
prescribed on each component, and a value is determined by its components. -/
theorem injective_pi_quotient_minimalPrimes
    (hloc : ∀ (m : Ideal A) [m.IsMaximal], IsDomain (Localization.AtPrime m)) :
    Function.Injective (fun a : A => fun p : {p : Ideal A // p ∈ minimalPrimes A} =>
      Ideal.Quotient.mk (p : Ideal A) a) := by
  intro a b hab
  have hmem : a - b ∈ sInf (minimalPrimes A) := by
    refine Submodule.mem_sInf.mpr fun p hp => ?_
    exact Ideal.Quotient.eq.mp (congrFun hab ⟨p, hp⟩)
  rw [sInf_minimalPrimes_eq_bot hloc, Ideal.mem_bot, sub_eq_zero] at hmem
  exact hmem

end ModularCurves
