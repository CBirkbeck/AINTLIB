/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.GroupWithZero.WithZero

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

/-- **General field-valuation helper (axiom-clean).** Two surjective
`ℤᵐ⁰ = WithZero (Multiplicative ℤ)`-valued valuations on a field that are
`Valuation.IsEquiv` are in fact *equal* (value-precise, not just equivalent).

The order-isomorphism of value groups underlying `IsEquiv` is forced to be the
identity because the only strictly-monotone group automorphism of `ℤ` is the
identity: writing `v e = exp 1` (surjectivity of `v`) and `w x = (w e)^{log(v x)}`
(the unit `x · e^{-log(v x)}` has `v`-value `1`, hence `w`-value `1` by `IsEquiv`),
the integer `c := log(w e)` divides `1` and is positive (`1 < w e` from `1 < v e`),
so `c = 1` and `w x = exp(log(v x)) = v x`.  Used to upgrade a valuation *equivalence*
(from valuation-subring maximality) to the *value identity* of two normalized adic
valuations on `K(C)`. -/
theorem Valuation.isEquiv_iff_eq_of_surjective_withZeroInt
    {F : Type*} [Field F] (v w : Valuation F (WithZero (Multiplicative ℤ)))
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) :
    v = w := by
  obtain ⟨e, he⟩ := hv (WithZero.exp 1)
  have hvpow : ∀ k : ℤ, v (e ^ k) = WithZero.exp k := by
    intro k; rw [map_zpow₀, he, ← WithZero.exp_zsmul, smul_eq_mul, mul_one]
  have hwe0 : w e ≠ 0 :=
    (h.eq_zero).ne.mp (by rw [he]; exact WithZero.exp_ne_zero)
  -- For nonzero `v x`, `w x = (w e)^(log (v x))`.
  have key : ∀ x : F, v x ≠ 0 → w x = (w e) ^ (WithZero.log (v x)) := by
    intro x hx
    set m := WithZero.log (v x) with hm
    have hvu : v (x * e ^ (-m)) = 1 := by
      rw [map_mul, hvpow (-m), ← WithZero.exp_log hx, ← hm, ← WithZero.exp_add,
        add_neg_cancel, WithZero.exp_zero]
    have hwu : w (x * e ^ (-m)) = 1 := (h.eq_one_iff_eq_one).mp hvu
    rw [map_mul, map_zpow₀, zpow_neg, mul_inv_eq_one₀ (zpow_ne_zero _ hwe0)] at hwu
    exact hwu
  -- `1 < w e` from `1 < v e = exp 1`.
  have h1we : (1 : WithZero (Multiplicative ℤ)) < w e := by
    rw [← h.one_lt_iff_one_lt, he, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hc_pos : 0 < WithZero.log (w e) := by
    have := (WithZero.lt_log_iff_exp_lt hwe0 (a := (0 : ℤ))).mpr (by rwa [WithZero.exp_zero])
    simpa using this
  -- `log (w e) = 1` via surjectivity of `w`.
  obtain ⟨x₁, hx₁⟩ := hw (WithZero.exp 1)
  have hvx₁ : v x₁ ≠ 0 :=
    (h.eq_zero).ne.mpr (by rw [hx₁]; exact WithZero.exp_ne_zero)
  have hk := key x₁ hvx₁
  rw [hx₁] at hk
  have hlog : (1 : ℤ) = WithZero.log (v x₁) * WithZero.log (w e) := by
    have h2 : WithZero.log (WithZero.exp (1 : ℤ)) =
        WithZero.log ((w e) ^ (WithZero.log (v x₁))) := by rw [hk]
    rwa [WithZero.log_exp, WithZero.log_zpow, smul_eq_mul] at h2
  have hc1 : WithZero.log (w e) = 1 := by
    have hdvd : WithZero.log (w e) ∣ 1 := ⟨_, by rw [hlog]; ring⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with hh | hh
    · exact hh
    · omega
  apply Valuation.ext
  intro x
  rcases eq_or_ne (v x) 0 with hx0 | hx0
  · rw [hx0, (h.eq_zero).mp hx0]
  · rw [key x hx0, ← WithZero.exp_log hwe0, hc1, ← WithZero.exp_zsmul, smul_eq_mul, mul_one,
      WithZero.exp_log hx0]

/-- **General valuation-subring maximality glue (axiom-clean).** If the valuation
subring of `v` *dominates downward* into the valuation subring of `w` (`O_v ≤ O_w`
in the `LocalSubring` domination order), then `v.IsEquiv w` — because every
valuation subring is maximal for domination (`ValuationSubring.isMax_toLocalSubring`),
so `O_v ≤ O_w` forces `O_v = O_w`, whence the valuations are equivalent
(`Valuation.isEquiv_iff_valuationSubring`). This is the "the reverse maximal-order
inclusion is FREE" step of the valuation identification. -/
theorem Valuation.isEquiv_of_valuationSubring_le
    {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v w : Valuation F Γ₀)
    (hle : v.valuationSubring.toLocalSubring ≤ w.valuationSubring.toLocalSubring) :
    v.IsEquiv w := by
  have heq : v.valuationSubring.toLocalSubring = w.valuationSubring.toLocalSubring :=
    (v.valuationSubring.isMax_toLocalSubring).eq_of_le hle
  rw [Valuation.isEquiv_iff_valuationSubring]
  exact ValuationSubring.toLocalSubring_injective heq

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
