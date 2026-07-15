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

end ModularCurves
