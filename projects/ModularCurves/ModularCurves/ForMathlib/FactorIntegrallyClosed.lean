/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.SmoothCurveComponents
import ModularCurves.ForMathlib.StandardSmoothIntegrallyClosed

/-!
# Each component of a smooth curve is an integrally closed domain (WP-D3a-FACTOR)

This is the join of the two halves that were already in the tree and whose absence as a single
statement was found on 2026-08-04:

* `exists_isLocalization_away_quotient_minimalPrime` (`ForMathlib/SmoothCurveComponents.lean`) — for a
  minimal prime `p`, the factor `A ⧸ p` is a localization of `A` **away from an idempotent**;
* `isIntegrallyClosed_of_isStandardSmoothOfRelativeDimension_one`
  (`ForMathlib/StandardSmoothIntegrallyClosed.lean`) — a **domain** standard smooth of relative
  dimension 1 over a field is integrally closed.

A localization away from an element is standard smooth of relative dimension `0`
(`Algebra.IsStandardSmoothOfRelativeDimension.localization_away`), so the factor is standard smooth of
relative dimension `1` over the base field by transitivity, and it is a domain because `p` is prime.

This is WP-D3d's step 1: `rootOfUnityDescend` (`WeilPairing/UniversalRootBase.lean`) needs
`IsIntegrallyClosed` on each factor.
-/

universe u

namespace ModularCurves

/-- **(WP-D3a-FACTOR)** For `A` standard smooth of relative dimension `1` over a field `k`, whose
localizations at maximal ideals are domains, every minimal-prime quotient `A ⧸ p` is an integrally
closed domain. -/
theorem isIntegrallyClosed_quotient_minimalPrime (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [IsNoetherianRing A] [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (hloc : ∀ (m : Ideal A) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    {p : Ideal A} (hp : p ∈ minimalPrimes A) :
    IsIntegrallyClosed (A ⧸ p) := by
  haveI hpp : p.IsPrime := hp.1.1
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  obtain ⟨e, he⟩ := exists_isLocalization_away_quotient_minimalPrime hloc hp
  haveI := he
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 A (A ⧸ p) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away e
  haveI : Algebra.IsStandardSmoothOfRelativeDimension (0 + 1) k (A ⧸ p) :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans (R := k) (S := A) (T := A ⧸ p) 1 0
  exact isIntegrallyClosed_of_isStandardSmoothOfRelativeDimension_one k (A ⧸ p)

end ModularCurves
