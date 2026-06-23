import HasseWeil.Hasse.HasseWitnessBundle
import HasseWeil.Hasse.HasseBoundQFNonneg
import HasseWeil.Hasse.PointFix

/-!
# The Hasse bound — canonical entry point

`hasse_bound_of_witnesses` is the canonical sound consumer of the Hasse bound:
given a `HasseWitnesses W hq` bundle (all four deferred fields discharged), it
returns `|#E(F_q) − q − 1| ≤ 2√q` axiom-clean.

This file is the public face of the Hasse-bound infrastructure. The three
deferred witnesses (separability of `1 − π`, fiber-cardinality, QF
non-negativity in `ℤ`) live as fields in `HasseWitnesses` and are owned by
upstream streams; once each lands, callers feed it through this consumer.

Files:

* `Hasse/Witnesses.lean` — the `HasseWitnesses` record (definition only).
* `Hasse/Final.lean` — this file: the bound consumer.
* `Hasse/HoleE.lean` — the underlying `_streamlined_qf_nonneg` chain.
* `Hasse/Unconditional.lean` — sketch / scaffolding (will retire as the
  cluster migrates to the witness record).
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **The Hasse bound from a complete witness bundle.**

`|#E(F_q) − q − 1| ≤ 2√q` for `W/F_q`, given a `HasseWitnesses W hq` bundle
discharging the four deferred inputs (separability, finite-dim,
`sepDegree = pointCount` (V.1.3), QF non-negativity).

Routes through `hasse_bound_via_signed_QF_negFrobenius_qf_nonneg`
(`Hasse/HoleE.lean`), consuming `pc_sepDeg_eq_pointCount` directly without
the previously-circular F_q-rational fiber-witness intermediate.

**R1 reframing note (2026-05-08)**: the former `pc_fiber_witness` field over
`W.toAffine.Point` was circular for `β = 1 − π` (its statement reduced to
V.1.3 after collapsing the F_q-rational fiber). The replacement
`pc_sepDeg_eq_pointCount` IS V.1.3 typed honestly — the bridged form of the
geometric T-II-2-009 + translation bootstrap chain combined with the
kernel-coincidence identity `ker(1 − π) on E(F̄_q) = E(F_q)`. -/
theorem hasse_bound_of_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    {hq : 2 ≤ Fintype.card K} (hw : HasseWitnesses W hq) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) := by
  haveI : Finite (isogOneSub_negFrobenius W hq).kernel := by
    rw [kernel_eq_top_of_hom_eq_id_sub_frobenius W (isogOneSub_negFrobenius W hq) rfl]
    haveI : Fintype (⊤ : AddSubgroup W.toAffine.Point) := Fintype.ofFinite _
    exact Finite.of_fintype _
  exact hasse_bound_via_signed_QF_negFrobenius_qf_nonneg W hq
    hw.pc_sep hw.pc_fin hw.pc_sepDeg_eq_pointCount hw.qf_nonneg

end HasseWeil
