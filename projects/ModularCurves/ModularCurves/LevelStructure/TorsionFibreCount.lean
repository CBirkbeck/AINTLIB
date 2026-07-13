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

/-- **(T-D8-⟹ piece (a))** Over a geometric point with `N` invertible, the preimage of the
torsion locus in the fibre curve has exactly `N²` points. -/
theorem natCard_fibre_torsion_locus (N : ℕ) [NeZero N] {k : Type u} [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ S) (hN : (N : k) ≠ 0) :
    Nat.card ↥((pullback.fst E.π t).base ⁻¹' ((E.torsionIdeal N).support : Set E.E)) = N ^ 2 := by
  haveI hci : IsClosedImmersion (pullback.snd (E.torsionι N) (pullback.fst E.π t)) :=
    MorphismProperty.pullback_snd _ _ (E.torsionι_isClosedImmersion N)
  have hbp : IsPullback (E.torsionBaseChangeHom N t) ((E.baseChange t).torsionπ N)
      (E.torsionι N ≫ E.π) t := by
    rw [E.torsionι_π N]; exact E.torsion_baseChange_isPullback N t
  have e : pullback (E.torsionι N) (pullback.fst E.π t) ≅ (E.baseChange t).torsion N :=
    (pullbackRightPullbackFstIso E.π t (E.torsionι N)).trans hbp.isoPullback.symm
  have hcard : Nat.card ↥(pullback (E.torsionι N) (pullback.fst E.π t)) = N ^ 2 := by
    rw [Nat.card_congr (Scheme.homeoOfIso e).toEquiv]
    exact E.natCard_torsion_fibre N t hN
  rw [E.torsionIdeal_support N,
    ← AlgebraicGeometry.Scheme.Pullback.range_snd (E.torsionι N) (pullback.fst E.π t),
    Nat.card_range_of_injective
      (pullback.snd (E.torsionι N) (pullback.fst E.π t)).isClosedEmbedding.injective]
  exact hcard

end EllipticCurve

end ModularCurves
