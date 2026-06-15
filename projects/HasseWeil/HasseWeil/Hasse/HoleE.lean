import HasseWeil.DegreeQuadraticForm
import HasseWeil.Frobenius
import HasseWeil.DualIsogeny
import HasseWeil.Hasse.BoundOfWitnesses
import HasseWeil.Hasse.QuadraticForm
import HasseWeil.Hasse.PointFix
import HasseWeil.Hasse.Separability
import HasseWeil.Hasse.OneSubFrobenius
import HasseWeil.AdditionPullback.Frobenius

/-!
# HOLE E closer — degree quadratic form for `isogSmulSub π r s`

This file packages the **HOLE E discharge** assuming the deliverables of the
parallel-running Hasse closure tickets:

* **T-HASSE-CLOSE-A** (AdditionPullback transcendence) — gives real Isogeny
  algebra so the QF composition lands at `mulByInt _ N` Isogeny-equally,
  yielding the AddMonoidHom→degree bridge `h_deg_bridge_family` below.
* **T-HASSE-CLOSE-C** (T-III-6-001 dual existence) — gives a concrete dual
  witness (`IsDualOf`) and the III.6 cascade in witness-parametric form
  (`isogDual_comp_self_of_witness`, `degree_dual_of_witness`, etc.; the
  choice-based `isogDual` cascade was refuted and deleted — see the
  `DualIsogeny.lean` module docstring).

The closer here takes those workers' outputs as **explicit hypotheses** and
produces the QF identity needed by `Hasse/Unconditional.lean:hasse_bound_target`
at the `h_qf_deg` case. When CLOSE-A and CLOSE-C land, instantiating each
hypothesis is a one-liner.

## Hypothesis ↔ ticket mapping

| Hypothesis | Source ticket | Source theorem |
|------------|---------------|-----------------|
| `verschiebung` | CLOSE-C | a witness `V` with `IsDualOf W.toAffine V (frobeniusIsog W)` |
| `h_dual_comp` | CLOSE-C | the `IsDualOf` composition evaluated at points |
| `h_sum_trace` | CLOSE-C | III.8.6 trace formula (witness-parametric chain) |
| `h_deg_bridge_family` | CLOSE-A | real pullback algebra → AddMonoidHom→degree |
| `h_dual_deg_family` | CLOSE-C | `degree_dual_of_witness` applied to `isogSmulSub` pair |
| `h_nonneg_N` | algebraic | structural (β.degree as ℕ ≥ 0) |
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ### Placeholder HOLE-E / signed-QF theorems — REMOVED (2026-05-28 placeholder grind)

hole_e_closer, hasse_bound_via_workers, hole_e_from_signed_QF,
hasse_bound_via_signed_QF, hasse_bound_sq_via_signed_QF, hasse_bound_sq_via_workers,
hole_e_closer_of_isDualOf, hole_e_closer_via_isogDual,
hole_e_closer_via_frobenius_dual_witness — all built on the placeholder
`isogSmulSub` / `oneSubFrobeniusIsog` and used only by the dead Cascade
hasse_bound_F_* exploration. Deleted. The genuine `_negFrobenius` Hasse-bound
assembly below is the live path. -/

/-- **β_qf-parametric form of `hasse_bound_via_signed_QF_negFrobenius`**:
takes the QF isogeny family `β_qf : ℤ → ℤ → Isogeny W.toAffine W.toAffine`
as a parameter instead of hard-coding the placeholder `isogSmulSub`.

This makes the QF identity hypothesis dischargeable when β_qf has genuine
pullback (e.g., via `addPullbackAlgHom_negFrobenius` for r·π − s·id).
The placeholder `isogSmulSub` makes the hard-coded version's QF identity
structurally false (placeholder has degree 1, not q·r² − t·rs + s²).

See `.mathlib-quality/qf-line-322-failure-mode.md` for the analysis. -/
theorem hasse_bound_via_signed_QF_negFrobenius_beta_param
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (h_pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable)
    (h_pc_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _
      (isogOneSub_negFrobenius W hq).toAlgebra.toModule)
    (h_sepDeg_eq_pointCount :
      (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine)
    [Finite (isogOneSub_negFrobenius W hq).kernel]
    (β_qf : ℤ → ℤ → Isogeny W.toAffine W.toAffine)
    (h_qf_deg : ∀ r s : ℤ, ((β_qf r s).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) *
          r * s + s ^ 2) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) :=
  hasse_bound_of_all_witnesses W
    (β_pc := isogOneSub_negFrobenius W hq)
    (h_pc_hom := rfl)
    (h_pc_sep := h_pc_sep)
    (h_pc_fin := h_pc_fin)
    (h_pc_fiber_witness := hole_d_of_hom_and_sepDegree W
      (isogOneSub_negFrobenius W hq) rfl h_sepDeg_eq_pointCount)
    (β_qf := β_qf)
    (h_qf_deg := h_qf_deg)

/-! ### Streamlined wire-up consuming Witness #1 + Witness #2 + fiber witness

The Witness #1 and Witness #3 specialisations (`isogOneSub_negFrobenius_*`)
were extracted to `Hasse/OneSubFrobenius.lean`. -/

/-! ### `qf_nonneg`-parametric `negFrobenius` consumer

The bound's discriminant argument only needs non-negativity of
`q·r² − tr·rs + s²` (see `BoundOfWitnesses.lean`). This consumer takes
exactly that, sidestepping the structurally-false "degree of placeholder
`isogSmulSub` equals the QF expression" hypothesis that the
`_signed`/`_streamlined` chain forces. -/

/-- **Day 4 bound, non-negativity form**: `_signed_QF_negFrobenius` analogue
that takes `h_qf_nonneg` instead of an isogeny-family equality. -/
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

/-- **Streamlined Day 4 bound, non-negativity form**: same as
`hasse_bound_via_signed_QF_negFrobenius_streamlined` but consumes a QF
non-negativity hypothesis directly. -/
theorem hasse_bound_via_signed_QF_negFrobenius_streamlined_qf_nonneg
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (h_pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable)
    (h_pc_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _
      (isogOneSub_negFrobenius W hq).toAlgebra.toModule)
    (h_pc_fiber_witness : ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          (isogOneSub_negFrobenius W hq).toAddMonoidHom P =
            (isogOneSub_negFrobenius W hq).toAddMonoidHom P₀} =
        (isogOneSub_negFrobenius W hq).sepDegree)
    [Finite (isogOneSub_negFrobenius W hq).kernel]
    (h_qf_nonneg : ∀ r s : ℤ,
      0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) *
          r * s + s ^ 2) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) :=
  hasse_bound_via_signed_QF_negFrobenius_qf_nonneg W hq h_pc_sep h_pc_fin
    (isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_witnesses W hq
      h_pc_sep h_pc_fin h_pc_fiber_witness)
    h_qf_nonneg

/-! ### Galois-witness / bijection cascade — REMOVED (2026-05-28 placeholder grind)

The dead witness-parametric theorems hasse_bound_via_galois_witnesses,
hasse_bound_via_isGalois_and_bijection, hasse_bound_via_separable_normal_bijection,
hasse_bound_via_witness1_normal_bijection used the placeholder `isogSmulSub` (via
their h_qf_signed hypothesis) and were unused. Deleted. The genuine _negFrobenius
Hasse-bound assembly above is witness-parametric; the live proven path is
`WeilPairing.hasse_bound_unconditional` (the `hasse_bound_skeleton` milestone and
`HasseWeilSkeleton.lean` were retired 2026-06-11). -/

end HasseWeil
