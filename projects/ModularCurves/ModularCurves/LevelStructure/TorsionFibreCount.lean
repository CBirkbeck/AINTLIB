/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.LevelStructure.Basic
import ModularCurves.EllipticCurve.MulByHomUnramified
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Point count of the fibre torsion locus (T-D8-⟹ piece (a))

Over a geometric point `t : Spec k ⟶ S` (`k` algebraically closed, `N` invertible), the preimage
`fst⁻¹(torsionIdeal.support)` in the fibre curve `pullback E.π t` has exactly `N²` points — the
count consumed by the `[YF-⊆]` pigeonhole. Assembled from `natCard_torsion_fibre` (the finite-étale
point count `= N²`) transported along `pullback.range_snd`.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- The support of `torsionIdeal` is the (closed) image of the torsion inclusion `E[N] ↪ E`. -/
theorem torsionIdeal_support (N : ℕ) :
    ((E.torsionIdeal N).support : Set E.E) = Set.range (E.torsionι N).base := by
  haveI := E.torsionι_isClosedImmersion N
  rw [torsionIdeal, Scheme.Hom.support_ker]
  exact (E.torsionι N).isClosedEmbedding.isClosed_range.closure_eq

end EllipticCurve

end ModularCurves
