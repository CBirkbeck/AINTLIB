/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. BB-FLAT ticket [FF-2].
-/
import ModularCurves.ForMathlib.StandardSmoothStalkDVR

/-!
# Localizations of a standard-smooth curve at maximal ideals are DVRs

The clean packaging of `StandardSmoothStalkDVR`'s stalk analysis, as [FF-2] of the
BB-FLAT fibre-leaf plan (board v10.230-G0): for `A` standard-smooth of relative
dimension `1` over a field `k` and `q` a **maximal** ideal, the local ring
`Localization.AtPrime q` is a discrete valuation ring.

Route: Zariski's lemma (`finite_of_finite_type_of_isJacobsonRing`, Stacks 0CY7) makes
the residue field `A ⧸ q` finite-dimensional, so
`exists_span_nonZeroDivisor_map_localizationAtPrime` (the exported stalk-principality
theorem, applied with `I := q`) produces a nonzerodivisor generator `π` of
`q · A_q = 𝔪(A_q)`; the Krull-intersection criteria of `PrincipalMaximalDVR`
(`IsDomain.of_maximalIdeal_eq_span_nonZeroDivisor`,
`IsDiscreteValuationRing.of_maximalIdeal_eq_span`) conclude.

This is the flatness-ready form of "smooth curves over a field have DVR stalks at
closed points": a finite torsion-free module over `Localization.AtPrime q` is then
flat (`Module.flat_iff_torsion_eq_bot_of_isBezout`), the stalkwise input of the
fibre case of BB-FLAT (`mulByHom_flat` over field bases).
-/

universe u

namespace ModularCurves

open IsLocalRing

/-- **[FF-2] Stalks of a standard-smooth curve over a field at closed points are
discrete valuation rings.** Bundles the `IsDomain` instance (part of the content) with
the DVR structure; downstream consumers `obtain ⟨_, _⟩` and `haveI` both. -/
theorem isDiscreteValuationRing_localizationAtPrime_of_isStandardSmooth
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (q : Ideal A) [q.IsMaximal] :
    ∃ _hd : IsDomain (Localization.AtPrime q),
      IsDiscreteValuationRing (Localization.AtPrime q) := by
  haveI : q.IsPrime := ‹q.IsMaximal›.isPrime
  haveI : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  -- Zariski's lemma: the residue field is a finite extension
  letI := Ideal.Quotient.field q
  haveI : Algebra.FiniteType k (A ⧸ q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k q)
      (Ideal.Quotient.mkₐ_surjective k q)
  haveI hfin : Module.Finite k (A ⧸ q) :=
    finite_of_finite_type_of_isJacobsonRing k (A ⧸ q)
  -- the principal nonzerodivisor generator of the maximal ideal downstairs
  obtain ⟨π, hspan, hnzd⟩ :=
    exists_span_nonZeroDivisor_map_localizationAtPrime k A q q le_rfl hfin
  have hmax : maximalIdeal (Localization.AtPrime q) = Ideal.span {π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact hspan
  -- noetherianity of the stalk
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ ‹IsNoetherianRing A›
  -- Krull-intersection criteria: domain, then DVR
  haveI hdom : IsDomain (Localization.AtPrime q) :=
    IsDomain.of_maximalIdeal_eq_span_nonZeroDivisor _ π hnzd hmax
  exact ⟨hdom, IsDiscreteValuationRing.of_maximalIdeal_eq_span _ π
    (nonZeroDivisors.ne_zero hnzd) hmax⟩

/-- **[FF-alg / BBF-A1 core] A finite* torsion-free algebra over a standard-smooth
curve of relative dimension `1` over a field is flat.** (*No finiteness is even
required — only torsion-freeness of `B` as an `A`-module, packaged here as `B` a domain
with injective structure map.) Every maximal-ideal localization of the domain `A` is a
DVR (`isDiscreteValuationRing_localizationAtPrime_of_isStandardSmooth`), hence a valuation
ring, so `flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal` reduces flatness
to torsion-freeness, which is immediate from `B` a domain and `algebraMap A B` injective.
This is the ring-level heart of the fibre case of BB-FLAT: on each affine chart of the
projective model over a field, the pushforward coordinate ring is a finite torsion-free
module, hence flat. -/
theorem flat_of_isDomain_of_injective_of_isStandardSmooth
    (k A B : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) :
    Module.Flat A B := by
  have hval : ∀ (P : Ideal A), [P.IsMaximal] → ValuationRing (Localization P.primeCompl) := by
    intro P hP
    obtain ⟨hd, hdvr⟩ :=
      isDiscreteValuationRing_localizationAtPrime_of_isStandardSmooth k A P
    haveI := hd
    haveI := hdvr
    infer_instance
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal hval,
    eq_bot_iff]
  intro x hx
  rw [Submodule.mem_torsion_iff] at hx
  obtain ⟨a, ha⟩ := hx
  have ha0 : (a : A) ≠ 0 := nonZeroDivisors.ne_zero a.2
  have hab : algebraMap A B (a : A) * x = 0 := by
    rw [← Algebra.smul_def]; exact ha
  rcases mul_eq_zero.mp hab with h | h
  · exact absurd ((map_eq_zero_iff _ hinj).mp h) ha0
  · rw [Submodule.mem_bot]; exact h

end ModularCurves
