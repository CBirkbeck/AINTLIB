/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
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

## Main results

* `rankOne_valuationSubring_le_eq_of_ne_top` — a DVR valuation subring `A ≤ B`, `B ≠ ⊤` forces
  `A = B` (the DVR-domination engine).
* `valuationSubring_isDVR_of_surjective_withZeroInt` — a surjective `ℤᵐ⁰`-valued valuation on a
  field has a discrete (rank-one) valuation subring.
* `Valuation.isEquiv_iff_eq_of_surjective_withZeroInt` — two surjective `ℤᵐ⁰`-valued valuations
  that are `IsEquiv` are in fact equal.
* `Valuation.isEquiv_of_valuationSubring_le` — downward valuation-subring domination
  `O_v ≤ O_w` implies `v.IsEquiv w`.
-/

namespace HasseWeil.Curves

/-- **General field-valuation helper (axiom-clean).** A surjective
`ℤᵐ⁰ = WithZero (Multiplicative ℤ)`-valued valuation on a field has a *discrete valuation ring* as
its valuation subring (rank one).  Surjectivity onto `ℤᵐ⁰` forces the value group to be all of `⊤`,
hence cyclic and nontrivial, whence `Valuation.valuationSubring_isDiscreteValuationRing` applies.
This is the rank-one input demanded by `rankOne_valuationSubring_le_eq_of_ne_top`. -/
theorem valuationSubring_isDVR_of_surjective_withZeroInt
    {F : Type*} [Field F] (v : Valuation F (WithZero (Multiplicative ℤ)))
    (hv : Function.Surjective v) :
    IsDiscreteValuationRing v.valuationSubring := by
  have hvg : MonoidWithZeroHom.valueGroup (.ofClass v) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [MonoidWithZeroHom.mem_valueGroup_iff_of_comm]
    refine ⟨1, by simp, ?_⟩
    obtain ⟨x, hx⟩ := hv (y : WithZero (Multiplicative ℤ))
    exact ⟨x, by rw [map_one, one_mul]; exact hx.symm⟩
  haveI : IsCyclic (WithZero (Multiplicative ℤ))ˣ :=
    isCyclic_of_surjective WithZero.unitsWithZeroEquiv.symm.toMonoidHom
      WithZero.unitsWithZeroEquiv.symm.surjective
  haveI : Nontrivial (WithZero (Multiplicative ℤ))ˣ :=
    WithZero.unitsWithZeroEquiv.symm.toEquiv.nontrivial
  haveI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass v)) := by
    rw [hvg]
    exact isCyclic_of_surjective Subgroup.topEquiv.symm.toMonoidHom
      Subgroup.topEquiv.symm.surjective
  haveI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass v)) := by
    rw [hvg]; exact Subgroup.topEquiv.symm.toEquiv.nontrivial
  exact Valuation.valuationSubring_isDiscreteValuationRing v

/-- **Power-agreement step for an equivalent valuation pair.** Given two
`ℤᵐ⁰`-valued valuations `v w` that are `Valuation.IsEquiv`, an element `e` whose
`v`-powers realise `exp` (`v (e ^ k) = exp k`), and `w e ≠ 0`, then on every
element `x` with `v x ≠ 0` the `w`-value is the `(log (v x))`-th power of `w e`:
`w x = (w e) ^ log (v x)`.  Proof: the twisted unit `x · e ^ (-log (v x))` has
`v`-value `1`, hence `w`-value `1` by `IsEquiv`, and solving for `w x` gives the
claim.  This is the core that forces the value groups to match up to a scalar. -/
private theorem w_apply_eq_zpow_log_of_v_ne_zero {F : Type*} [Field F]
    (v w : Valuation F (WithZero (Multiplicative ℤ))) (h : v.IsEquiv w)
    {e : F} (hvpow : ∀ k : ℤ, v (e ^ k) = WithZero.exp k) (hwe0 : w e ≠ 0)
    {x : F} (hx : v x ≠ 0) :
    w x = (w e) ^ (WithZero.log (v x)) := by
  set m := WithZero.log (v x) with hm
  have hvu : v (x * e ^ (-m)) = 1 := by
    rw [map_mul, hvpow (-m), ← WithZero.exp_log hx, ← hm, ← WithZero.exp_add,
      add_neg_cancel, WithZero.exp_zero]
  have hwu : w (x * e ^ (-m)) = 1 := (h.eq_one_iff_eq_one).mp hvu
  rw [map_mul, map_zpow₀, zpow_neg, mul_inv_eq_one₀ (zpow_ne_zero _ hwe0)] at hwu
  exact hwu

/-- **The value-group scaling factor is the identity.** For an equivalent pair of
surjective `ℤᵐ⁰`-valued valuations `v w` and an element `e` with `v (e ^ k) = exp k`
and `1 < w e`, the integer `log (w e)` equals `1`.  By surjectivity of `w` pick
`x₁` with `w x₁ = exp 1`; the power-agreement step
(`w_apply_eq_zpow_log_of_v_ne_zero`) gives `1 = log (v x₁) · log (w e)`, so
`log (w e) ∣ 1`, and `1 < w e` forces `log (w e) > 0`, ruling out `-1`. -/
private theorem log_w_uniformizer_eq_one {F : Type*} [Field F]
    (v w : Valuation F (WithZero (Multiplicative ℤ))) (h : v.IsEquiv w)
    (hw : Function.Surjective w) {e : F}
    (hvpow : ∀ k : ℤ, v (e ^ k) = WithZero.exp k) (hwe0 : w e ≠ 0)
    (h1we : (1 : WithZero (Multiplicative ℤ)) < w e) :
    WithZero.log (w e) = 1 := by
  have hc_pos : 0 < WithZero.log (w e) := by
    have := (WithZero.lt_log_iff_exp_lt hwe0 (a := (0 : ℤ))).mpr (by rwa [WithZero.exp_zero])
    simpa using this
  obtain ⟨x₁, hx₁⟩ := hw (WithZero.exp 1)
  have hvx₁ : v x₁ ≠ 0 :=
    (h.eq_zero).ne.mpr (by rw [hx₁]; exact WithZero.exp_ne_zero)
  have hk := w_apply_eq_zpow_log_of_v_ne_zero v w h hvpow hwe0 hvx₁
  rw [hx₁] at hk
  have hlog : (1 : ℤ) = WithZero.log (v x₁) * WithZero.log (w e) := by
    have h2 : WithZero.log (WithZero.exp (1 : ℤ)) =
        WithZero.log ((w e) ^ (WithZero.log (v x₁))) := by rw [hk]
    rwa [WithZero.log_exp, WithZero.log_zpow, smul_eq_mul] at h2
  have hdvd : WithZero.log (w e) ∣ 1 := ⟨_, by rw [hlog]; ring⟩
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with hh | hh
  · exact hh
  · omega

/-- **General field-valuation helper (axiom-clean).** Two surjective
`ℤᵐ⁰ = WithZero (Multiplicative ℤ)`-valued valuations on a field that are
`Valuation.IsEquiv` are in fact *equal* (value-precise, not just equivalent).

The order-isomorphism of value groups underlying `IsEquiv` is forced to be the
identity because the only strictly-monotone group automorphism of `ℤ` is the
identity: writing `v e = exp 1` (surjectivity of `v`) and `w x = (w e)^{log(v x)}`
(the unit `x · e^{-log(v x)}` has `v`-value `1`, hence `w`-value `1` by `IsEquiv`,
`w_apply_eq_zpow_log_of_v_ne_zero`), the integer `c := log(w e)` divides `1` and is
positive (`1 < w e` from `1 < v e`), so `c = 1` (`log_w_uniformizer_eq_one`) and
`w x = exp(log(v x)) = v x`.  Used to upgrade a valuation *equivalence* (from
valuation-subring maximality) to the *value identity* of two normalized adic
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
  -- `1 < w e` from `1 < v e = exp 1`.
  have h1we : (1 : WithZero (Multiplicative ℤ)) < w e := by
    rw [← h.one_lt_iff_one_lt, he, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  -- The value-group scaling factor is the identity.
  have hc1 : WithZero.log (w e) = 1 := log_w_uniformizer_eq_one v w h hw hvpow hwe0 h1we
  apply Valuation.ext
  intro x
  rcases eq_or_ne (v x) 0 with hx0 | hx0
  · rw [hx0, (h.eq_zero).mp hx0]
  · rw [w_apply_eq_zpow_log_of_v_ne_zero v w h hvpow hwe0 hx0, ← WithZero.exp_log hwe0, hc1,
      ← WithZero.exp_zsmul, smul_eq_mul, mul_one, WithZero.exp_log hx0]

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
