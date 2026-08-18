/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.FactorIntegrallyClosed
import ModularCurves.WeilPairing.UniversalRootBase

/-!
# Roots of unity on a component of a smooth curve (WP-D3d step 3)

`nonempty_weilPairing_of_cover_of_values` (`WeilPairing/FullLevelPairing.lean`) wants `ζ` as an element
of `{ a : Γ(S', ⊤) // a ^ N = 1 }`; the componentwise construction produces it as a root of unity in the
*fraction field* of each factor, namely the field-level Weil pairing value at the component's generic
point. This file is the interface between the two:

`factorRootOfUnityDescend` descends a root of unity from `FractionRing (A ⧸ p)` to `A ⧸ p`, using
`isIntegrallyClosed_quotient_minimalPrime` (`ForMathlib/FactorIntegrallyClosed.lean`) to supply the
`IsIntegrallyClosed` hypothesis that `rootOfUnityDescend` needs.
-/

universe u

namespace ModularCurves

variable (k A : Type u) [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]

/-- **(WP-D3d step 3)** A root of unity in the fraction field of a component descends to the component
itself — the two hypotheses `rootOfUnityDescend` needs (`IsDomain`, `IsIntegrallyClosed`) are supplied
by `p` being a minimal prime and by `isIntegrallyClosed_quotient_minimalPrime`. -/
noncomputable def factorRootOfUnityDescend
    (hloc : ∀ (m : Ideal A) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    {p : Ideal A} (hp : p ∈ minimalPrimes A) {N : ℕ} (hN : N ≠ 0)
    (x : { u : FractionRing (A ⧸ p) // u ^ N = 1 }) : { a : A ⧸ p // a ^ N = 1 } :=
  haveI : p.IsPrime := hp.1.1
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  haveI := isIntegrallyClosed_quotient_minimalPrime k A hloc hp
  rootOfUnityDescend hN x

/-- …and it maps to the given root of unity, so any identity proved at the generic point transports
down. This is what makes the value equations of `nonempty_weilPairing_of_cover_of_values` checkable at
the generic fibre. -/
theorem algebraMap_factorRootOfUnityDescend
    (hloc : ∀ (m : Ideal A) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    {p : Ideal A} (hp : p ∈ minimalPrimes A) {N : ℕ} (hN : N ≠ 0)
    (x : { u : FractionRing (A ⧸ p) // u ^ N = 1 }) :
    haveI : p.IsPrime := hp.1.1
    haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
    algebraMap (A ⧸ p) (FractionRing (A ⧸ p))
        (factorRootOfUnityDescend k A hloc hp hN x).1 = (x : FractionRing (A ⧸ p)) :=
  haveI : p.IsPrime := hp.1.1
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  haveI := isIntegrallyClosed_quotient_minimalPrime k A hloc hp
  algebraMap_rootOfUnityDescend hN x

end ModularCurves
