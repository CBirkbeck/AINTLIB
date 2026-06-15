/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.AdditionPullback.Frobenius
import HasseWeil.DegreeQuadraticForm
import HasseWeil.Hasse.PointFix
import HasseWeil.HasseBound

/-!
# Hasse bound from QF non-negativity in `ℤ`

The bound's discriminant argument (`trace_sq_le_four_mul_deg` in
`HasseWeil/HasseBound.lean`) uses only the non-negativity of the binary
quadratic form `q·r² − t·r·s + s²` for all `r, s : ℤ`. The original consumer
chain in `Hasse/BoundOfWitnesses.lean` carries an isogeny family `β_qf` with
the III.6.3 degree equality; this file ships the slimmer parametric form
that takes the non-negativity directly, sidestepping any cross-binding to a
specific isogeny structure.

Why split. With the placeholder `isogSmulSub` (`Endomorphism.lean:105`):
its `pullback := AlgHom.id` makes `β.degree = 1` for every `r, s`, so any
`h_qf_deg` hypothesis pinning that degree to the QF expression is
structurally false at `(r, s) = (0, 0)` (LHS = 1, RHS = 0). The
non-negativity form is provable: `0 ≤ 0` holds, and for `(r, s) ≠ (0, 0)`
the inequality follows from Silverman III.6.3 applied to a genuine isogeny
family supplied separately.

## Main results

* `traceOfFrobenius_sq_le_of_qf_nonneg` — the discriminant bound `t² ≤ 4q`
  given non-negativity of the QF expression in `ℤ`.
* `hasse_bound_of_qf_nonneg_witnesses` — `|#E(F_q) − q − 1| ≤ 2√q` from
  non-negativity + the point-count witness `pointCount = q + 1 − t`.
* `hasse_bound_of_full_qf_nonneg_witnesses` — same but with the trace
  computed internally as `isogTrace π β_pc`.
* `hasse_bound_of_all_qf_nonneg_witnesses` — single-shot consumer
  consolidating the upstream witness list.
* Squared variants of each.

## Implementation notes

Every declaration here is witness-parametric (the QF non-negativity and
point-count facts arrive as hypotheses); the geometric discharge of those
witnesses for the proven bound lives in the Weil-pairing route
(`WeilPairing/HasseAssembly.lean` → `WeilPairing/HasseBound.lean`).

## References
* [Silverman, *The Arithmetic of Elliptic Curves*], V.1.1.
-/

open WeierstrassCurve Real

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
/-- **Discriminant bound, non-negativity form**. Same as
`traceOfFrobenius_sq_le_of_witness` but takes the QF non-negativity hypothesis
directly, with no isogeny family parameter. -/
theorem traceOfFrobenius_sq_le_of_qf_nonneg (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (t : ℤ) (h_qf_nonneg : ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r ^ 2 - t * r * s + s ^ 2) :
    t ^ 2 ≤ 4 * (Fintype.card K : ℤ) :=
  trace_sq_le_four_mul_deg _ _ Fintype.card_pos h_qf_nonneg

omit [DecidableEq K] in
/-- **Hasse bound, non-negativity form**. Same as `hasse_bound_of_t_witness`
but consumes a non-negativity hypothesis on the QF rather than an isogeny
family + degree-equality witness. -/
theorem hasse_bound_of_qf_nonneg_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (t : ℤ) (h_pc : (pointCount W.toAffine : ℤ) = Fintype.card K + 1 - t)
    (h_qf_nonneg : ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r ^ 2 - t * r * s + s ^ 2) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * sqrt (Fintype.card K : ℝ) := by
  have hpc_real : (↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ) = -(t : ℝ) := by
    exact_mod_cast congrArg ((↑) : ℤ → ℝ)
      (show (pointCount W.toAffine : ℤ) - ↑(Fintype.card K) - 1 = -t by linarith)
  rw [hpc_real, abs_neg]
  exact abs_le_two_sqrt_of_sq_le _ _ (traceOfFrobenius_sq_le_of_qf_nonneg W t h_qf_nonneg)

omit [DecidableEq K] in
/-- Squared form of `hasse_bound_of_qf_nonneg_witnesses`. -/
theorem hasse_bound_sq_of_qf_nonneg_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (t : ℤ) (h_pc : (pointCount W.toAffine : ℤ) = Fintype.card K + 1 - t)
    (h_qf_nonneg : ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r ^ 2 - t * r * s + s ^ 2) :
    ((pointCount W.toAffine : ℤ) - Fintype.card K - 1) ^ 2 ≤
      4 * (Fintype.card K : ℤ) := by
  rw [show (pointCount W.toAffine : ℤ) - ↑(Fintype.card K) - 1 = -t by linarith, neg_sq]
  exact traceOfFrobenius_sq_le_of_qf_nonneg W t h_qf_nonneg

/-- **Fully-chained Hasse bound, non-negativity form**. Replaces the QF
isogeny family + degree-equality witness in `hasse_bound_of_full_witnesses`
by a non-negativity hypothesis on the QF expression with `t` instantiated to
`isogTrace (frobeniusIsog W) β_pc`. -/
theorem hasse_bound_of_full_qf_nonneg_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (β_pc : Isogeny W.toAffine W.toAffine)
    (h_pc_hom : β_pc.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_pc_ker_deg : Nat.card β_pc.kernel = β_pc.degree)
    (h_qf_nonneg : ∀ r s : ℤ,
      0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) β_pc * r * s + s ^ 2) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * sqrt (Fintype.card K : ℝ) :=
  hasse_bound_of_qf_nonneg_witnesses W (isogTrace (frobeniusIsog W) β_pc)
    (pointCount_eq_of_hom_kernel_witness W β_pc h_pc_hom h_pc_ker_deg)
    h_qf_nonneg

/-- **Consolidated Hasse bound, non-negativity form**. Same hypothesis list
as `hasse_bound_of_all_witnesses` except the QF isogeny family is replaced by
an integer non-negativity hypothesis. The bound's discriminant argument
needs only this — the isogeny family was an artefact of how the consumer
chain was originally written. -/
theorem hasse_bound_of_all_qf_nonneg_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (β_pc : Isogeny W.toAffine W.toAffine)
    (h_pc_hom : β_pc.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_pc_sep : β_pc.IsSeparable)
    (h_pc_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ β_pc.toAlgebra.toModule)
    (h_pc_fiber_witness : ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          β_pc.toAddMonoidHom P = β_pc.toAddMonoidHom P₀} =
        β_pc.sepDegree)
    [h_pc_ker_finite : Finite β_pc.kernel]
    (h_qf_nonneg : ∀ r s : ℤ,
      0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) β_pc * r * s + s ^ 2) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * sqrt (Fintype.card K : ℝ) :=
  hasse_bound_of_full_qf_nonneg_witnesses W β_pc h_pc_hom
    (Isogeny.card_kernel_eq_degree_of_separable_witness β_pc h_pc_sep
      h_pc_fin h_pc_fiber_witness)
    h_qf_nonneg

/-- **`qf_nonneg` from the genuine isogeny chain** (Silverman III.6.3 + degree
non-negativity): given a genuine `β r s` family realising `r·π − s·id` at the
`AddMonoidHom` level whose degree matches the QF expression, the QF
non-negativity follows from `Int.natCast_nonneg (β r s).degree`. -/
theorem qf_nonneg_of_genuine_chain (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (β_pc : Isogeny W.toAffine W.toAffine) (β : ℤ → ℤ → Isogeny W.toAffine W.toAffine)
    (h_β_deg : ∀ r s : ℤ, ((β r s).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 - isogTrace (frobeniusIsog W) β_pc * r * s + s ^ 2) :
    ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) β_pc * r * s + s ^ 2 := by
  intro r s
  rw [← h_β_deg r s]
  exact Int.natCast_nonneg _

/-- **Hasse `qf_nonneg` from the Frobenius polarisation chain (Worker D)**: given
families of `addIsog` injectivity witnesses for both the `r·π − s` and `r·V − s`
families, plus the Frobenius-specific dual chain (Verschiebung `V` with `IsDualOf`
halves, the sum-trace identity, and the `addIsog` degree bridge), the `qf_nonneg`
field of `HasseWitnesses` discharges. -/
theorem qf_nonneg_via_frobenius_polarisation
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] (V : Isogeny W.toAffine W.toAffine)
    (one_sub_α : Isogeny W.toAffine W.toAffine)
    (hxy_β : ∀ r s : ℤ, AddNonInversePair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)))
    (hinj_β : ∀ r s : ℤ, Function.Injective (addCoordAlgHomPair (hxy_β r s)))
    (hxy_β_dual : ∀ r s : ℤ,
        AddNonInversePair (V.zsmul r) (mulByInt W.toAffine (-s)))
    (hinj_β_dual : ∀ r s : ℤ,
        Function.Injective (addCoordAlgHomPair (hxy_β_dual r s)))
    (h_dual_comp : ∀ P : W.toAffine.Point,
        V.toAddMonoidHom ((frobeniusIsog W).toAddMonoidHom P) =
          ((frobeniusIsog W).degree : ℤ) • P)
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
        (mulByInt W.toAffine
          (isogTrace (frobeniusIsog W) one_sub_α)).toAddMonoidHom)
    (h_deg_bridge : ∀ r s : ℤ,
        ((addIsog (hxy_β_dual r s) (hinj_β_dual r s)).comp
            (addIsog (hxy_β r s) (hinj_β r s))).toAddMonoidHom =
            (mulByInt W.toAffine
              (((frobeniusIsog W).degree : ℤ) * r ^ 2 -
                isogTrace (frobeniusIsog W) one_sub_α * r * s + s ^ 2)).toAddMonoidHom →
          ((addIsog (hxy_β_dual r s) (hinj_β_dual r s)).comp
              (addIsog (hxy_β r s) (hinj_β r s))).degree =
            ((((frobeniusIsog W).degree : ℤ) * r ^ 2 -
              isogTrace (frobeniusIsog W) one_sub_α * r * s + s ^ 2) ^ 2).toNat)
    (h_dual_deg : ∀ r s : ℤ,
        (addIsog (hxy_β_dual r s) (hinj_β_dual r s)).degree =
          (addIsog (hxy_β r s) (hinj_β r s)).degree)
    (h_nonneg_N : ∀ r s : ℤ,
        0 ≤ ((frobeniusIsog W).degree : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) one_sub_α * r * s + s ^ 2) :
    ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) one_sub_α * r * s + s ^ 2 := by
  have hdeg : ((frobeniusIsog W).degree : ℤ) = (Fintype.card K : ℤ) := by
    rw [frobeniusIsog_degree]
  refine qf_nonneg_of_genuine_chain W one_sub_α
    (fun r s ↦ addIsog (hxy_β r s) (hinj_β r s)) ?_
  intro r s
  have hpol := degree_quadratic_genuine_addIsog (W := W)
    (frobeniusIsog W) V one_sub_α r s
    (hxy_β r s) (hinj_β r s) (hxy_β_dual r s) (hinj_β_dual r s)
    h_dual_comp h_sum_trace (h_deg_bridge r s) (h_dual_deg r s) (h_nonneg_N r s)
  rw [hpol, hdeg]

/-- **Single-`(r, s)` polarisation degree identity** (Silverman III.6.3): for a
dual `V` of Frobenius and the trace identity `h_sum_trace`, the degree of the
genuine `r·π − s·id` isogeny `genuineIsogSmulSub W r s` equals the integer
quadratic-form value `q·r² − t·r·s + s²`. -/
theorem genuineIsogSmulSub_degree_eq_quadratic_form
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (V : Isogeny W.toAffine W.toAffine)
    (hV : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    -- V-side `addIsog` data: supplied as explicit witnesses pending the V-side
    -- genuine-isogeny infrastructure (L9/T9, Phase 1 + Phase 2).
    (hxy_β_dual : AddNonInversePair (V.zsmul r) (mulByInt W.toAffine (-s)))
    (hinj_β_dual : Function.Injective (addCoordAlgHomPair hxy_β_dual))
    (h_deg_bridge :
        ((addIsog hxy_β_dual hinj_β_dual).comp
          (genuineIsogSmulSub W r s hr hs hrK hsK)).toAddMonoidHom =
            (mulByInt W.toAffine
              ((Fintype.card K : ℤ) * r ^ 2 -
                isogTrace (frobeniusIsog W)
                  (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)).toAddMonoidHom →
        ((addIsog hxy_β_dual hinj_β_dual).comp
            (genuineIsogSmulSub W r s hr hs hrK hsK)).degree =
            (((Fintype.card K : ℤ) * r ^ 2 -
              isogTrace (frobeniusIsog W)
                (isogOneSub_negFrobenius W hq) * r * s + s ^ 2) ^ 2).toNat)
    (h_dual_deg :
        (addIsog hxy_β_dual hinj_β_dual).degree =
          (genuineIsogSmulSub W r s hr hs hrK hsK).degree)
    (h_nonneg_N : 0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2) :
    ((genuineIsogSmulSub W r s hr hs hrK hsK).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  have h_dual_comp : ∀ P : W.toAffine.Point,
      V.toAddMonoidHom ((frobeniusIsog W).toAddMonoidHom P) =
        ((frobeniusIsog W).degree : ℤ) • P := by
    intro P
    have h_app := DFunLike.congr_fun (congrArg Isogeny.toAddMonoidHom hV.1) P
    rw [Isogeny.comp_apply] at h_app
    rw [h_app, mulByInt_apply]
  set hxy_β : AddNonInversePair ((frobeniusIsog W).zsmul r)
      (mulByInt W.toAffine (-s)) :=
    AddNonInversePair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK with hxy_β_def
  set hinj_β : Function.Injective (addCoordAlgHomPair hxy_β) :=
    addCoordAlgHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole W r s hr hs hrK hsK
      (by rw [ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK];
          exact_mod_cast (by norm_num : (-2 : ℤ) < 0))
  rw [show genuineIsogSmulSub W r s hr hs hrK hsK = addIsog hxy_β hinj_β from rfl]
  have h_frob_deg : ((frobeniusIsog W).degree : ℤ) = (Fintype.card K : ℤ) := by
    rw [frobeniusIsog_degree]
  refine (degree_quadratic_genuine_addIsog (W := W) (frobeniusIsog W) V
    (isogOneSub_negFrobenius W hq) r s hxy_β hinj_β hxy_β_dual hinj_β_dual
    h_dual_comp h_sum_trace ?_ ?_ ?_).trans ?_
  · intro h_hom_comp
    rw [h_frob_deg] at h_hom_comp
    have hres := h_deg_bridge h_hom_comp
    rw [← h_frob_deg] at hres
    exact hres
  · exact h_dual_deg
  · rw [h_frob_deg]
    exact h_nonneg_N
  · rw [h_frob_deg]

/-- Squared form of `hasse_bound_of_all_qf_nonneg_witnesses`. -/
theorem hasse_bound_sq_of_all_qf_nonneg_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (β_pc : Isogeny W.toAffine W.toAffine)
    (h_pc_hom : β_pc.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_pc_sep : β_pc.IsSeparable)
    (h_pc_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ β_pc.toAlgebra.toModule)
    (h_pc_fiber_witness : ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          β_pc.toAddMonoidHom P = β_pc.toAddMonoidHom P₀} =
        β_pc.sepDegree)
    [h_pc_ker_finite : Finite β_pc.kernel]
    (h_qf_nonneg : ∀ r s : ℤ,
      0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) β_pc * r * s + s ^ 2) :
    ((pointCount W.toAffine : ℤ) - Fintype.card K - 1) ^ 2 ≤
      4 * (Fintype.card K : ℤ) :=
  hasse_bound_sq_of_qf_nonneg_witnesses W (isogTrace (frobeniusIsog W) β_pc)
    (pointCount_eq_of_hom_kernel_witness W β_pc h_pc_hom
      (Isogeny.card_kernel_eq_degree_of_separable_witness β_pc h_pc_sep
        h_pc_fin h_pc_fiber_witness))
    h_qf_nonneg

/-- **QF non-negativity, edge case `r = 0`**: when `r = 0`, the quadratic form
collapses to `s²`, which is non-negative. -/
theorem qf_nonneg_universal_edge_r_zero (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    {hq : 2 ≤ Fintype.card K} (s : ℤ) :
    0 ≤ (Fintype.card K : ℤ) * (0 : ℤ) ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * (0 : ℤ) * s + s ^ 2 := by
  ring_nf
  exact sq_nonneg s

/-- **QF non-negativity, edge case `s = 0`**: when `s = 0`, the quadratic form
collapses to `q·r²`, which is non-negative. -/
theorem qf_nonneg_universal_edge_s_zero (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    {hq : 2 ≤ Fintype.card K} (r : ℤ) :
    0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * (0 : ℤ) + (0 : ℤ) ^ 2 := by
  ring_nf
  exact mul_nonneg (Int.natCast_nonneg _) (sq_nonneg r)

/-- **Universal QF non-negativity via a polarisation witness**: if every inner
pair `(r ≠ 0, s ≠ 0)` admits a genuine isogeny `α` with `(α.degree : ℤ) = Q(r, s)`,
then `Q(r, s) ≥ 0` for all `r, s`. The witness-parametric form of `qf_nonneg`. -/
theorem qf_nonneg_universal_of_polarisation_witness (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] {hq : 2 ≤ Fintype.card K}
    (h_polarisation : ∀ r s : ℤ, r ≠ 0 → s ≠ 0 →
      ∃ α : Isogeny W.toAffine W.toAffine,
        (Fintype.card K : ℤ) * r ^ 2 -
            isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 =
          (α.degree : ℤ)) :
    ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2 := by
  intro r s
  by_cases hr : r = 0
  · subst hr
    exact qf_nonneg_universal_edge_r_zero (hq := hq) W s
  · by_cases hs : s = 0
    · subst hs
      exact qf_nonneg_universal_edge_s_zero (hq := hq) W r
    · obtain ⟨α, hα⟩ := h_polarisation r s hr hs
      rw [hα]
      exact Int.natCast_nonneg _

end HasseWeil
