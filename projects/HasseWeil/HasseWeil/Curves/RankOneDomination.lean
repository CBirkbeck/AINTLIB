/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Rank-one valuation-subring domination

A valuation subring `A` of a field `L` that is a **discrete valuation ring** (rank one) has only
two overrings: `A` itself and the whole field `⊤`.  Consequently any larger valuation subring
`B ≥ A` with `B ≠ ⊤` must equal `A`.

This single reusable fact is the *DVR-domination engine* shared by

* the affine valuation-subring domination of Silverman V.1.3
  (`HasseWeil/Hasse/L6Witnesses.lean`), and
* the curve-completeness place classification over the integral closure `B`
  (`HasseWeil/Curves/NormConormIntegralClosure.lean`).

It is kept here in a lightweight `Curves/` file (depending only on the mathlib `ValuationSubring`
and `DiscreteValuationRing` API) so that the place classification need not import the heavy char-`p`
`Hasse/L6Witnesses`.

## Main result

* `rankOne_valuationSubring_le_eq_of_ne_top` — a DVR valuation subring `A ≤ B`, `B ≠ ⊤` forces
  `A = B`.
-/

namespace HasseWeil.Curves

/-- **DVR-domination crux — rank-one overring is self-or-top.**

For a valuation subring `A` of a field `L` that is a **discrete valuation ring**
(rank one — its only overrings are `A` itself and the whole field `⊤`), any larger
valuation subring `B ≥ A` with `B ≠ ⊤` must equal `A`.

**Mathematical content (the geometric crux of V.1.3).** Overrings of a valuation
subring `A` are in order-reversing bijection with the primes of `A`
(`ValuationSubring.primeSpectrumEquiv`: `B ↦ idealOfLE A B`, `ofPrime A (idealOfLE A B h) = B`).
A DVR has exactly two primes, `⊥` and the maximal ideal
(`IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime`: `∃! P ≠ ⊥, P.IsPrime`).
The bottom prime gives the whole field (`ofPrime A ⊥ = ⊤`), the maximal ideal gives
`A` (`ofPrime A m_A = A`). So `A ≤ B`, `B ≠ ⊤` forces `idealOfLE A B = m_A`, whence
`B = ofPrime A m_A = A`. -/
theorem rankOne_valuationSubring_le_eq_of_ne_top {L : Type*} [Field L]
    (A B : ValuationSubring L) [IsDiscreteValuationRing A]
    (hAB : A ≤ B) (hB : B ≠ ⊤) : A = B := by
  -- STRATEGY (assembly of existing mathlib pieces; the residual is just the wiring).
  -- Overrings of `A` ↔ primes of `A` via `B ↦ idealOfLE A B`, with reconstruction
  -- `ofPrime A (idealOfLE A B hAB) = B` (`ofPrime_idealOfLE`). The DVR `A` has a unique
  -- nonzero prime `m_A` (`iff_pid_with_one_nonzero_prime`), so the prime `idealOfLE A B`
  -- is `⊥` or `m_A`:
  --   • `= m_A = idealOfLE A A le_rfl`  ⟹  `B = ofPrime A m_A = A`;
  --   • `= ⊥ = idealOfLE A ⊤ le_top`    ⟹  `B = ofPrime A ⊥ = ⊤`, excluded by `hB`.
  -- (`idealOfLE A A le_rfl = m_A` since the self-inclusion's comap is `id`;
  --  `idealOfLE A ⊤ le_top = ⊥` since the maximal ideal of the field `⊤` is `⊥`.)
  -- The remaining wiring transports `ofPrime A · ·` across an equality of primes; this
  -- is delicate because `ofPrime A : (P : Ideal A) → [P.IsPrime] → ValuationSubring L`
  -- is instance-dependent (naive `congrArg`/`rw` hit a "motive not type correct" wall).
  -- The robust route is `ValuationSubring.primeSpectrumEquiv.injective` on `PrimeSpectrum`
  -- (which bundles the `IsPrime` instance), reducing `B = A` to a `PrimeSpectrum`
  -- equality `⟨idealOfLE A B, _⟩ = ⟨idealOfLE A A, _⟩`.
  classical
  -- The prime of `A` cut out by the overring `B`.
  have hPprime : (A.idealOfLE B hAB).IsPrime := ValuationSubring.prime_idealOfLE A B hAB
  -- Transport: equal primes ⟹ equal overrings, dodging the instance-motive wall by
  -- routing through `primeSpectrumEquiv` (which bundles `IsPrime`) and `ofPrime_idealOfLE`.
  have transport : ∀ (C : ValuationSubring L) (hC : A ≤ C),
      A.idealOfLE B hAB = A.idealOfLE C hC → B = C := by
    intro C hC hEq
    have hPS : (⟨A.idealOfLE B hAB, hPprime⟩ : PrimeSpectrum A)
        = ⟨A.idealOfLE C hC, ValuationSubring.prime_idealOfLE A C hC⟩ :=
      PrimeSpectrum.ext hEq
    have hval := congrArg (fun P ↦ ((ValuationSubring.primeSpectrumEquiv A) P).1) hPS
    simpa only [ValuationSubring.primeSpectrumEquiv_apply, ValuationSubring.ofPrime_idealOfLE]
      using hval
  -- The DVR `A` has Krull dimension ≤ 1, so its prime `idealOfLE A B` is `⊥` or maximal.
  rcases eq_or_ne (A.idealOfLE B hAB) ⊥ with hbot | hne
  · -- Bottom prime: `B = ofPrime A ⊥ = ⊤`, contradicting `hB`.
    exfalso
    apply hB
    refine transport ⊤ le_top ?_
    rw [hbot]
    -- `idealOfLE A ⊤ le_top = ⊥`: the maximal ideal of the field `⊤` is `⊥`, and the
    -- inclusion `A ↪ ⊤` is injective so its `comap ⊥ = ⊥`.
    rw [ValuationSubring.idealOfLE, IsLocalRing.maximalIdeal_eq_bot]
    refine (Ideal.comap_bot_of_injective (ValuationSubring.inclusion A ⊤ le_top) ?_).symm
    intro a b hab
    have hab' := congrArg (Subtype.val (p := fun y ↦ y ∈ (⊤ : ValuationSubring L))) hab
    rw [ValuationSubring.inclusion, Subring.coe_inclusion, Subring.coe_inclusion] at hab'
    exact Subtype.ext hab'
  · -- Nonzero prime in a dimension-≤-1 ring is maximal, hence `= maximalIdeal A`.
    have hmax : (A.idealOfLE B hAB).IsMaximal := hPprime.isMaximal hne
    refine (transport A le_rfl ?_).symm
    rw [IsLocalRing.eq_maximalIdeal hmax]
    -- `idealOfLE A A le_rfl = maximalIdeal A`: the self-inclusion's comap is the identity.
    rw [ValuationSubring.idealOfLE]
    ext x
    have hx : (ValuationSubring.inclusion A A le_rfl) x = x :=
      Subtype.ext (by rw [ValuationSubring.inclusion, Subring.coe_inclusion])
    rw [Ideal.mem_comap, hx]

end HasseWeil.Curves
