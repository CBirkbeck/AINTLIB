/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.StandardSmoothMaximalDVR
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# A standard-smooth curve over a field is integrally closed (WP-D3b)

The coordinate ring of a smooth affine curve over a field, when it is a domain, is
integrally closed. This is the input the DS4 root construction needs: a root of unity in the
fraction field of the universal base then lies in the base itself
(`WeilPairing/UniversalRootBase.lean`, `exists_algebraMap_eq_of_pow_eq_one`), so a `μ_N`-value
constructed at the generic point extends over the whole base.

Both halves are already available and this file is only the join:

* `isDiscreteValuationRing_localizationAtPrime_of_isStandardSmooth`
  (`ForMathlib/StandardSmoothMaximalDVR.lean`) — the localization at a **maximal** ideal of a
  standard-smooth curve over a field is a DVR;
* `IsIntegrallyClosed.of_localization_maximal` (mathlib,
  `RingTheory/DedekindDomain/Dvr.lean`) — integral closedness is a local property at the
  maximal ideals.

The general "normal" statements one might reach for instead are **not** available: mathlib has
no normality of schemes (`AlgebraicGeometry/Morphisms/` has no `Normal.lean` or `Regular.lean`)
and no "regular ⟹ integrally closed" (that is Auslander–Buchsbaum). Going through the
one-dimensional DVR criterion sidesteps both.
-/

universe u

namespace ModularCurves

/-- **(WP-D3b)** A standard-smooth curve over a field which is a domain is integrally closed.

Local at the maximal ideals: each localization is a DVR
(`isDiscreteValuationRing_localizationAtPrime_of_isStandardSmooth`), hence a PID, hence
integrally closed. -/
theorem isIntegrallyClosed_of_isStandardSmoothOfRelativeDimension_one
    (k A : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A] :
    IsIntegrallyClosed A := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ hpm => ?_
  haveI : p.IsMaximal := hpm
  obtain ⟨hd, hdvr⟩ :=
    isDiscreteValuationRing_localizationAtPrime_of_isStandardSmooth k A p
  haveI := hd
  haveI := hdvr
  infer_instance

end ModularCurves
