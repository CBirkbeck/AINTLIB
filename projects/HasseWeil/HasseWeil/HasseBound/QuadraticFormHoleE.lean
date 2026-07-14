/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.DegreeQuadraticForm
import HasseWeil.Isogeny.Frobenius.PointCount
import HasseWeil.Isogeny.Dual.Relation
import HasseWeil.HasseBound.Parametric
import HasseWeil.HasseBound.QuadraticForm
import HasseWeil.HasseBound.PointCount
import HasseWeil.HasseBound.Separability
import HasseWeil.HasseBound.OneSubFrobenius
import HasseWeil.Isogeny.Frobenius.OrdAtInfty

/-!
# The Hasse bound from the `negFrobenius` witness, in non-negativity form

`BoundOfWitnesses.lean` derives the Hasse bound from a family of witnesses about
a point-count isogeny `β_pc`. Its discriminant argument needs only the
**non-negativity** of the quadratic form `q·r² − tr·r·s + s²`, not any identity
expressing that form as a degree.

This file specialises that assembly to the concrete point-count isogeny
`isogOneSub_negFrobenius W hq` (built in `OneSubFrobenius.lean`): it takes the
non-negativity of the form as a hypothesis, supplies `h_pc_hom` by `rfl`, and
discharges the fiber witness with `hole_d_of_hom_and_sepDegree`.

## Main results

* `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg` — the real-valued bound
  `|#E(K) − q − 1| ≤ 2√q`.
* `hasse_bound_sq_via_signed_QF_negFrobenius_qf_nonneg` — its squared,
  integer-valued form.

Both are witness-parametric. The unconditional statement, with every hypothesis
here discharged, is `WeilPairing.hasse_bound_unconditional`.
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **The Hasse bound**, non-negativity form: takes `h_qf_nonneg` rather than an
isogeny-family degree equality. -/
theorem hasse_bound_via_signed_QF_negFrobenius_qf_nonneg
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (h_pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable)
    (h_pc_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _
      (isogOneSub_negFrobenius W hq).toAlgebra.toModule)
    (h_sepDeg_eq_pointCount :
      (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine)
    [h_pc_ker_finite : Finite (isogOneSub_negFrobenius W hq).kernel]
    (h_qf_nonneg : ∀ r s : ℤ,
      0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) *
          r * s + s ^ 2) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) :=
  hasse_bound_of_all_qf_nonneg_witnesses W
    (β_pc := isogOneSub_negFrobenius W hq)
    (h_pc_hom := rfl)
    (h_pc_sep := h_pc_sep)
    (h_pc_fin := h_pc_fin)
    (h_pc_fiber_witness := hole_d_of_hom_and_sepDegree W
      (isogOneSub_negFrobenius W hq) rfl h_sepDeg_eq_pointCount)
    (h_qf_nonneg := h_qf_nonneg)

/-- Squared form of `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg`. -/
theorem hasse_bound_sq_via_signed_QF_negFrobenius_qf_nonneg
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (h_pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable)
    (h_pc_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _
      (isogOneSub_negFrobenius W hq).toAlgebra.toModule)
    (h_sepDeg_eq_pointCount :
      (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine)
    [h_pc_ker_finite : Finite (isogOneSub_negFrobenius W hq).kernel]
    (h_qf_nonneg : ∀ r s : ℤ,
      0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) *
          r * s + s ^ 2) :
    ((pointCount W.toAffine : ℤ) - Fintype.card K - 1) ^ 2 ≤
      4 * (Fintype.card K : ℤ) :=
  hasse_bound_sq_of_all_qf_nonneg_witnesses W
    (β_pc := isogOneSub_negFrobenius W hq)
    (h_pc_hom := rfl)
    (h_pc_sep := h_pc_sep)
    (h_pc_fin := h_pc_fin)
    (h_pc_fiber_witness := hole_d_of_hom_and_sepDegree W
      (isogOneSub_negFrobenius W hq) rfl h_sepDeg_eq_pointCount)
    (h_qf_nonneg := h_qf_nonneg)

end HasseWeil
