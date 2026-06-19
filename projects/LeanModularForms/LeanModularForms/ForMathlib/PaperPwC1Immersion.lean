/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Path
import LeanModularForms.ForMathlib.PiecewiseC1Path
import LeanModularForms.ForMathlib.PiecewiseC1PathOn

/-!
# Paper-faithful piecewise C¹ immersions (Hungerbühler–Wasem)

The legacy `PiecewiseC1Path` / `PwC1Immersion` in `PiecewiseC1Path.lean` keep the
partition in the *open* interval `(0, 1)` and only require `C¹` regularity on the
*open* sub-intervals between consecutive breakpoints. That is strictly weaker than
the definition used by Hungerbühler–Wasem (arXiv:1808.00997v2, page 3):

> "A closed piecewise `C¹` immersion `Λ : [a,b] → ℂ` is a closed curve such that
> there is a partition `a = a₀ < a₁ < … < aₙ = b` such that `Λ|_{[aₖ,aₖ₊₁]}` is
> of class `C¹` and such that `Λ̇|_{[aₖ,aₖ₊₁]} ≠ 0` for all `k = 0, …, n−1`."

This file mirrors that definition exactly:

* the partition `Finset ℝ` includes both endpoints `0` and `1`;
* on every closed sub-interval `Icc a b` whose endpoints are consecutive
  partition members, the path is `ContDiffOn ℝ 1`;
* for the immersion variant, the derivative is non-vanishing on each closed
  piece.

Because each piece is `C¹` on a *closed* bounded interval, the derivative is
automatically interval-integrable on each piece, and so on `[0, 1]` by gluing.

## Main definitions

* `Finset.IsConsecutive S a b` — `(a, b)` are consecutive members of `S`
  (both lie in `S`, `a < b`, no element of `S` strictly between them).
* `ClosedPwC1Curve x` — a closed path at `x` that is paper-`C¹`-piecewise.
* `ClosedPwC1Immersion x` — extends with non-vanishing derivative on each piece.

## Main results

* `ClosedPwC1Curve.deriv_intervalIntegrable_piece` — derivative is integrable on
  each closed piece between consecutive partition members.

## References

* K. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997v2, page 3.
-/

open Set Filter Topology MeasureTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pair `(a, b)` are *consecutive* members of `S : Finset ℝ` when both lie
in `S`, `a < b`, and no element of `S` lies strictly between them. -/
def Finset.IsConsecutive (S : Finset ℝ) (a b : ℝ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a < b ∧ ∀ c ∈ S, c ∉ Set.Ioo a b

/-- A **closed piecewise `C¹` curve** in the sense of Hungerbühler–Wasem
(arXiv:1808.00997v2, page 3): a path `[0, 1] → E` returning to its starting point,
together with a partition `0 = a₀ < a₁ < … < aₙ = 1` whose endpoints are included,
such that the path is `C¹` on each *closed* sub-interval `[aₖ, aₖ₊₁]`.

This extends `PiecewiseC1Path x x`. The inherited `partition` field is the
*Ioo-style* (open-interior) partition, while `closedPartition` is the Icc-style
partition with endpoints included. The two are related by
`closedPartition_eq : closedPartition = insert 0 (insert 1 partition)`. -/
@[ext]
structure ClosedPwC1Curve (x : E) extends PiecewiseC1Path x x where
  /-- Closed partition WITH endpoints. Required because the inherited `partition`
  is Ioo-style (interior only). -/
  closedPartition : Finset ℝ
  /-- `0` is a closed-partition point. -/
  zero_mem_closedPartition : (0 : ℝ) ∈ closedPartition
  /-- `1` is a closed-partition point. -/
  one_mem_closedPartition : (1 : ℝ) ∈ closedPartition
  /-- Every closed-partition point lies in `[0, 1]`. -/
  closedPartition_subset : (closedPartition : Set ℝ) ⊆ Icc 0 1
  /-- The closed partition is the Ioo-style `partition` with `0` and `1` adjoined. -/
  closedPartition_eq : closedPartition = insert 0 (insert 1 partition)
  /-- On every closed sub-interval `[a, b]` whose endpoints are consecutive
  closed-partition members, the extended path is `C¹`. -/
  contDiffOn_pieces : ∀ a b, closedPartition.IsConsecutive a b →
    ContDiffOn ℝ 1 toPath.extend (Icc a b)

/-- A **closed piecewise `C¹` immersion** in the sense of Hungerbühler–Wasem
(arXiv:1808.00997v2, page 3): a closed piecewise `C¹` curve whose derivative
is non-vanishing on every closed sub-interval between consecutive partition
points. -/
@[ext]
structure ClosedPwC1Immersion (x : E) extends ClosedPwC1Curve x where
  /-- On every closed sub-interval between consecutive closed-partition members, the
  *within*-derivative of the extended path is non-zero — i.e. `Λ̇|_{[aₖ,aₖ₊₁]} ≠ 0`
  in the paper. We use `derivWithin _ (Icc a b)` rather than the global `deriv`
  because at corner partition points the global `deriv` is `0` by mathlib
  convention (the function is not differentiable there), which would falsely
  contradict non-vanishing. -/
  derivWithin_ne_zero_pieces : ∀ a b, closedPartition.IsConsecutive a b →
    ∀ t ∈ Icc a b, derivWithin toPath.extend (Icc a b) t ≠ 0

namespace ClosedPwC1Curve

variable {x : E}

/-- The underlying extended path is continuous. -/
@[fun_prop]
theorem continuous (γ : ClosedPwC1Curve x) : Continuous γ.toPath.extend :=
  γ.toPath.continuous_extend

/-- Membership in the inherited Ioo-style `partition` is equivalent to lying in
`closedPartition` while not being an endpoint. -/
theorem mem_partition_iff (γ : ClosedPwC1Curve x) {t : ℝ} :
    t ∈ γ.partition ↔ t ∈ γ.closedPartition ∧ t ≠ 0 ∧ t ≠ 1 := by
  refine ⟨fun ht ↦ ?_, fun ⟨h_in, h_ne0, h_ne1⟩ ↦ ?_⟩
  · have h_in_Ioo : t ∈ Ioo (0 : ℝ) 1 := γ.partition_subset ht
    exact ⟨γ.closedPartition_eq ▸ by simp [Finset.mem_insert, ht],
      ne_of_gt h_in_Ioo.1, ne_of_lt h_in_Ioo.2⟩
  · rw [γ.closedPartition_eq, Finset.mem_insert, Finset.mem_insert] at h_in
    exact h_in.resolve_left h_ne0 |>.resolve_left h_ne1

/-! ## Interval integrability of the derivative on each piece

The key payoff of the closed-piece formulation: on each closed sub-interval
between consecutive partition members, the derivative is interval-integrable.
This follows from `ContDiffOn ℝ 1` on the closed piece, which gives a continuous
`derivWithin`, agreeing with `deriv` on the open interior (i.e. almost
everywhere on the piece). -/

/-- On the open interior `Ioo a b`, the within-`Icc a b` derivative agrees with
the global derivative. -/
private lemma derivWithin_eq_deriv_on_Ioo (f : ℝ → E) {a b t : ℝ}
    (ht : t ∈ Ioo a b) :
    derivWithin f (Icc a b) t = deriv f t :=
  derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)

/-- **Piece-wise integrability of the derivative.** On each closed sub-interval
`[a, b]` between consecutive partition members, `deriv γ.toPath.extend` is
interval-integrable. This is `TIGHT-6` for one piece. -/
theorem deriv_intervalIntegrable_piece (γ : ClosedPwC1Curve x) {a b : ℝ}
    (h : γ.closedPartition.IsConsecutive a b) :
    IntervalIntegrable (deriv γ.toPath.extend) volume a b := by
  have hab : a ≤ b := h.2.2.1.le
  have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc a b) := γ.contDiffOn_pieces a b h
  have h_dw_cont : ContinuousOn (derivWithin γ.toPath.extend (Icc a b)) (Icc a b) :=
    hcd.continuousOn_derivWithin (uniqueDiffOn_Icc h.2.2.1) le_rfl
  refine (h_dw_cont.intervalIntegrable_of_Icc hab).congr_ae ?_
  refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioo a b, ?_, fun _ ht ↦ derivWithin_eq_deriv_on_Ioo _ ht⟩
  rw [MeasureTheory.mem_ae_iff, MeasureTheory.Measure.restrict_apply' measurableSet_uIoc]
  refine MeasureTheory.measure_mono_null (t := ({b} : Set ℝ)) ?_ Real.volume_singleton
  intro t ⟨ht_compl, ht_in⟩
  rw [uIoc_of_le hab] at ht_in
  by_contra hne
  exact ht_compl ⟨ht_in.1, lt_of_le_of_ne ht_in.2 hne⟩

end ClosedPwC1Curve

/-! ## Helper: gluing piece-wise predicates over a finite partition -/

/-- Generic "glue piece-wise predicates" induction over a finite partition:
if `P` is reflexive (in the `a = b` sense) and transitive across a shared midpoint
on consecutive pieces, then `P` holds on `[a, b]` once it holds on every consecutive
pair of the partition. The two callers (`IntervalIntegrable` and `LipschitzOnWith`)
fix `P` accordingly. -/
private lemma consecutive_piece_induction {P : ℝ → ℝ → Prop}
    (P_refl : ∀ x, P x x) (P_trans : ∀ {p q r : ℝ}, P p q → P q r → P p r) :
    ∀ s : Finset ℝ, ∀ a b : ℝ, a ∈ s → b ∈ s → a ≤ b →
      (∀ c ∈ s, a ≤ c ∧ c ≤ b) →
      (∀ p q, s.IsConsecutive p q → P p q) → P a b := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro a b ha hb hab hbds hpc
    rcases eq_or_lt_of_le hab with hab_eq | hab_lt
    · subst hab_eq; exact P_refl a
    set t : Finset ℝ := s.filter (a < ·)
    have hb_in_t : b ∈ t := Finset.mem_filter.mpr ⟨hb, hab_lt⟩
    have ha'_in_t : t.min' ⟨b, hb_in_t⟩ ∈ t := t.min'_mem _
    set a' := t.min' ⟨b, hb_in_t⟩
    have ha'_in_s : a' ∈ s := (Finset.mem_filter.mp ha'_in_t).1
    have ha_lt_a' : a < a' := (Finset.mem_filter.mp ha'_in_t).2
    have hcons : s.IsConsecutive a a' :=
      ⟨ha, ha'_in_s, ha_lt_a', fun c hc hc_Ioo ↦
        absurd (t.min'_le c (Finset.mem_filter.mpr ⟨hc, hc_Ioo.1⟩)) (by linarith [hc_Ioo.2])⟩
    set s' : Finset ℝ := s.erase a
    have ha'_in_s' : a' ∈ s' := Finset.mem_erase.mpr ⟨ne_of_gt ha_lt_a', ha'_in_s⟩
    have hb_in_s' : b ∈ s' := Finset.mem_erase.mpr ⟨ne_of_gt hab_lt, hb⟩
    have hbds' : ∀ c ∈ s', a' ≤ c ∧ c ≤ b := fun c hc ↦ by
      have hc_in : c ∈ s := (Finset.mem_erase.mp hc).2
      refine ⟨t.min'_le _ (Finset.mem_filter.mpr ⟨hc_in, ?_⟩), (hbds c hc_in).2⟩
      exact lt_of_le_of_ne (hbds c hc_in).1 (Ne.symm (Finset.mem_erase.mp hc).1)
    have hpc' : ∀ p q, s'.IsConsecutive p q → P p q := fun p q hcons' ↦
      hpc p q ⟨(Finset.mem_erase.mp hcons'.1).2, (Finset.mem_erase.mp hcons'.2.1).2,
        hcons'.2.2.1, fun c hc hc_Ioo ↦ by
          have hp_gt_a : a < p := lt_of_lt_of_le ha_lt_a' (hbds' p hcons'.1).1
          exact hcons'.2.2.2 c (Finset.mem_erase.mpr
            ⟨ne_of_gt (lt_of_lt_of_le hp_gt_a hc_Ioo.1.le), hc⟩) hc_Ioo⟩
    exact P_trans (hpc _ _ hcons)
      (ih s' (Finset.erase_ssubset ha) a' b ha'_in_s' hb_in_s' (hbds' b hb_in_s').1 hbds' hpc')

/-- If `f` is interval-integrable on every consecutive pair of a finite partition
of `[a, b]` containing both endpoints, then `f` is interval-integrable on `[a, b]`. -/
private theorem intervalIntegrable_of_consecutive_pieces
    {α : Type*} [TopologicalSpace α] [ENormedAddMonoid α]
    [TopologicalSpace.PseudoMetrizableSpace α]
    {f : ℝ → α} {μ : MeasureTheory.Measure ℝ} (s : Finset ℝ) (a b : ℝ)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≤ b)
    (hbds : ∀ c ∈ s, a ≤ c ∧ c ≤ b)
    (hpc : ∀ p q, s.IsConsecutive p q → IntervalIntegrable f μ p q) :
    IntervalIntegrable f μ a b :=
  consecutive_piece_induction (P := IntervalIntegrable f μ)
    (fun _ ↦ IntervalIntegrable.refl) (fun h1 h2 ↦ h1.trans h2) s a b ha hb hab hbds hpc

/-! ## Global interval-integrability of the derivative -/

namespace ClosedPwC1Curve

variable {x : E}

/-- **TIGHT-6 (global form).** For a paper-faithful closed piecewise `C¹` curve
`γ`, the derivative `deriv γ.toPath.extend` is interval-integrable on `[0, 1]`. -/
theorem deriv_extend_intervalIntegrable (γ : ClosedPwC1Curve x) :
    IntervalIntegrable (deriv γ.toPath.extend) volume 0 1 :=
  intervalIntegrable_of_consecutive_pieces γ.closedPartition 0 1
    γ.zero_mem_closedPartition γ.one_mem_closedPartition zero_le_one
    (fun _ hc ↦ ⟨(γ.closedPartition_subset hc).1, (γ.closedPartition_subset hc).2⟩)
    (fun _ _ h ↦ γ.deriv_intervalIntegrable_piece h)

/-! ## Bridge to legacy `PiecewiseC1Path`

A paper-faithful curve produces a legacy curve by erasing the global endpoints
`0` and `1` from the partition (the legacy structure keeps the partition in
the open interior `(0, 1)` by convention). -/

/-- For `t` strictly inside `(0, 1)` not in a closed-partition that contains
both endpoints, find the consecutive closed-partition pair containing `t`. -/
private lemma exists_consecutive_pair_aux {closedPartition : Finset ℝ}
    (zero_mem : (0 : ℝ) ∈ closedPartition) (one_mem : (1 : ℝ) ∈ closedPartition)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (htn : t ∉ closedPartition) :
    ∃ a b, closedPartition.IsConsecutive a b ∧ t ∈ Ioo a b := by
  set pred := closedPartition.filter (· < t)
  set succ := closedPartition.filter (t < ·)
  have h0_pred : (0 : ℝ) ∈ pred := Finset.mem_filter.mpr ⟨zero_mem, ht.1⟩
  have h1_succ : (1 : ℝ) ∈ succ := Finset.mem_filter.mpr ⟨one_mem, ht.2⟩
  set a := pred.max' ⟨0, h0_pred⟩
  set b := succ.min' ⟨1, h1_succ⟩
  have ha_mem : a ∈ pred := pred.max'_mem _
  have hb_mem : b ∈ succ := succ.min'_mem _
  have ha_lt : a < t := (Finset.mem_filter.mp ha_mem).2
  have ht_lt_b : t < b := (Finset.mem_filter.mp hb_mem).2
  refine ⟨a, b, ⟨(Finset.mem_filter.mp ha_mem).1, (Finset.mem_filter.mp hb_mem).1,
    ha_lt.trans ht_lt_b, fun c hc hc_Ioo ↦ ?_⟩, ha_lt, ht_lt_b⟩
  rcases lt_trichotomy c t with hct | hct | hct
  · exact absurd (pred.le_max' c (Finset.mem_filter.mpr ⟨hc, hct⟩))
      (by linarith [hc_Ioo.1])
  · exact htn (hct ▸ hc)
  · exact absurd (succ.min'_le c (Finset.mem_filter.mpr ⟨hc, hct⟩))
      (by linarith [hc_Ioo.2])

/-- Method version: find the consecutive closed-partition pair containing `t`. -/
private lemma exists_consecutive_pair_containing (γ : ClosedPwC1Curve x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (htn : t ∉ γ.closedPartition) :
    ∃ a b, γ.closedPartition.IsConsecutive a b ∧ t ∈ Ioo a b :=
  exists_consecutive_pair_aux γ.zero_mem_closedPartition γ.one_mem_closedPartition ht htn


end ClosedPwC1Curve

namespace ClosedPwC1Immersion

variable {x : E}

/-- Helper for the immersion bridge: at an interior closed-partition point `p`, the
predecessor `a := max{c ∈ closedPartition : c < p}` is well-defined and `(a, p)` is
consecutive. -/
private lemma exists_predecessor (γ : ClosedPwC1Immersion x) {p : ℝ}
    (hp_in : p ∈ γ.closedPartition) (hp_pos : 0 < p) :
    ∃ a, γ.closedPartition.IsConsecutive a p := by
  set pred := γ.closedPartition.filter (· < p)
  have h0_pred : (0 : ℝ) ∈ pred :=
    Finset.mem_filter.mpr ⟨γ.zero_mem_closedPartition, hp_pos⟩
  have ha_mem : pred.max' ⟨0, h0_pred⟩ ∈ pred := pred.max'_mem _
  exact ⟨_, (Finset.mem_filter.mp ha_mem).1, hp_in, (Finset.mem_filter.mp ha_mem).2,
    fun c hc hc_Ioo ↦ absurd (pred.le_max' c (Finset.mem_filter.mpr ⟨hc, hc_Ioo.2⟩))
      (by linarith [hc_Ioo.1])⟩

/-- Helper for the immersion bridge: at an interior closed-partition point `p`, the
successor `b := min{c ∈ closedPartition : p < c}` is well-defined and `(p, b)` is
consecutive. -/
private lemma exists_successor (γ : ClosedPwC1Immersion x) {p : ℝ}
    (hp_in : p ∈ γ.closedPartition) (hp_lt_one : p < 1) :
    ∃ b, γ.closedPartition.IsConsecutive p b := by
  set succ := γ.closedPartition.filter (p < ·)
  have h1_succ : (1 : ℝ) ∈ succ :=
    Finset.mem_filter.mpr ⟨γ.one_mem_closedPartition, hp_lt_one⟩
  have hb_mem : succ.min' ⟨1, h1_succ⟩ ∈ succ := succ.min'_mem _
  exact ⟨_, hp_in, (Finset.mem_filter.mp hb_mem).1, (Finset.mem_filter.mp hb_mem).2,
    fun c hc hc_Ioo ↦ absurd (succ.min'_le c (Finset.mem_filter.mpr ⟨hc, hc_Ioo.1⟩))
      (by linarith [hc_Ioo.2])⟩

/-- Shared inner computation for `left_deriv_limit` / `right_deriv_limit` in
`toPwC1Immersion`. Given a piece `Icc a b` with `a < b` and a designated endpoint
`p ∈ {a, b}`, produces the one-sided derivative limit `Tendsto (deriv γ̃) (𝓝[hSide] p)`
where `hSide` is the one-sided neighborhood toward the *interior* of `Icc a b`. -/
private lemma toPwC1Immersion_deriv_limit_aux (γ : ClosedPwC1Immersion x) {a b : ℝ}
    (hcons : γ.closedPartition.IsConsecutive a b) {p : ℝ} (hp : p ∈ Icc a b)
    (S : Set ℝ) (hSeq : 𝓝[S] p = 𝓝[Ioo a b] p) :
    ∃ L : E, L ≠ 0 ∧ Tendsto (deriv γ.toPath.extend) (𝓝[S] p) (𝓝 L) := by
  have hab : a < b := hcons.2.2.1
  have h_dw_cont : ContinuousOn (derivWithin γ.toPath.extend (Icc a b)) (Icc a b) :=
    (γ.contDiffOn_pieces a b hcons).continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  refine ⟨derivWithin γ.toPath.extend (Icc a b) p,
    γ.derivWithin_ne_zero_pieces a b hcons p hp, ?_⟩
  refine (hSeq ▸ (h_dw_cont p hp).mono_left
    (nhdsWithin_mono _ Ioo_subset_Icc_self)).congr' ?_
  rw [hSeq]
  exact Filter.eventuallyEq_of_mem (s := Ioo a b) self_mem_nhdsWithin
    fun _ hu ↦ ClosedPwC1Curve.derivWithin_eq_deriv_on_Ioo _ hu

/-- A `ClosedPwC1Immersion` produces a legacy `PwC1Immersion`. -/
def toPwC1Immersion (γ : ClosedPwC1Immersion x) : PwC1Immersion x x where
  toPiecewiseC1Path := γ.toPiecewiseC1Path
  deriv_ne_zero := by
    intro t ht htn
    have htn_closed : t ∉ γ.closedPartition := fun h_in ↦ htn
      (γ.toClosedPwC1Curve.mem_partition_iff.mpr ⟨h_in, ne_of_gt ht.1, ne_of_lt ht.2⟩)
    obtain ⟨a, b, hcons, ht_Ioo⟩ :=
      γ.toClosedPwC1Curve.exists_consecutive_pair_containing ht htn_closed
    have h_dw_ne :=
      γ.derivWithin_ne_zero_pieces a b hcons t (Ioo_subset_Icc_self ht_Ioo)
    change deriv γ.toPath.extend t ≠ 0
    rwa [ClosedPwC1Curve.derivWithin_eq_deriv_on_Ioo _ ht_Ioo] at h_dw_ne
  left_deriv_limit := by
    intro p hp
    have hp_in : p ∈ γ.closedPartition := (γ.toClosedPwC1Curve.mem_partition_iff.mp hp).1
    obtain ⟨a, hcons⟩ := γ.exists_predecessor hp_in (γ.partition_subset hp).1
    refine γ.toPwC1Immersion_deriv_limit_aux hcons (right_mem_Icc.mpr hcons.2.2.1.le) _ ?_
    rw [← Set.Iio_inter_Ioi (a := p) (b := a),
      nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hcons.2.2.1))]
  right_deriv_limit := by
    intro p hp
    have hp_in : p ∈ γ.closedPartition := (γ.toClosedPwC1Curve.mem_partition_iff.mp hp).1
    obtain ⟨b, hcons⟩ := γ.exists_successor hp_in (γ.partition_subset hp).2
    refine γ.toPwC1Immersion_deriv_limit_aux hcons (left_mem_Icc.mpr hcons.2.2.1.le) _ ?_
    rw [← Set.Ioi_inter_Iio (a := p) (b := b),
      nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hcons.2.2.1))]

end ClosedPwC1Immersion

/-! ## Phase 1 — Lipschitz constant from `ClosedPwC1Curve`

A paper-faithful piecewise-C¹ curve has bounded derivative on each closed
piece (continuity on compact), and by gluing across pieces we obtain a
global Lipschitz constant for `γ.toPath.extend : ℝ → E`. -/

/-- Glue two `LipschitzOnWith` results across a shared midpoint. -/
private lemma lipschitzOnWith_Icc_trans {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a b c : ℝ} {C : NNReal}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hf₁ : LipschitzOnWith C f (Icc a b))
    (hf₂ : LipschitzOnWith C f (Icc b c)) :
    LipschitzOnWith C f (Icc a c) := by
  rw [lipschitzOnWith_iff_norm_sub_le] at hf₁ hf₂ ⊢
  -- Ordered-pair version: prove the bound for x ≤ b ≤ y.
  have split : ∀ {x y : ℝ}, x ∈ Icc a c → y ∈ Icc a c → x ≤ b → b ≤ y →
      ‖f x - f y‖ ≤ C * ‖x - y‖ := by
    intro x y hx hy hxb hby
    have h1 := hf₁ ⟨hx.1, hxb⟩ ⟨hab, le_refl b⟩
    have h2 := hf₂ ⟨le_refl b, hbc⟩ ⟨hby, hy.2⟩
    have h_dist : ‖x - y‖ = ‖x - b‖ + ‖b - y‖ := by
      simp only [Real.norm_eq_abs, abs_of_nonpos (by linarith : x - y ≤ 0),
        abs_of_nonpos (by linarith : x - b ≤ 0), abs_of_nonpos (by linarith : b - y ≤ 0)]
      ring
    calc ‖f x - f y‖
        = ‖(f x - f b) + (f b - f y)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖f x - f b‖ + ‖f b - f y‖ := norm_add_le _ _
      _ ≤ (C : ℝ) * ‖x - b‖ + (C : ℝ) * ‖b - y‖ := by gcongr
      _ = (C : ℝ) * ‖x - y‖ := by rw [← mul_add, ← h_dist]
  intro x hx y hy
  rcases le_total x y with hxy | hxy
  · rcases le_total y b with hyb | hby
    · exact hf₁ ⟨hx.1, hxy.trans hyb⟩ ⟨hx.1.trans hxy, hyb⟩
    · rcases le_total x b with hxb | hbx
      · exact split hx hy hxb hby
      · exact hf₂ ⟨hbx, hx.2⟩ ⟨hbx.trans hxy, hy.2⟩
  · rw [norm_sub_rev (f x) (f y), norm_sub_rev x y]
    rcases le_total x b with hxb | hbx
    · exact hf₁ ⟨hy.1, hxy.trans hxb⟩ ⟨hy.1.trans hxy, hxb⟩
    · rcases le_total y b with hyb | hby
      · exact split hy hx hyb hbx
      · exact hf₂ ⟨hby, hy.2⟩ ⟨hby.trans hxy, hx.2⟩

/-- Inductive gluing: piecewise-`LipschitzOnWith` on consecutive pieces yields
global `LipschitzOnWith` on `Icc a b` containing all pieces. -/
private lemma lipschitzOnWith_of_consecutive_pieces {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} {C : NNReal} (s : Finset ℝ) (a b : ℝ)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≤ b)
    (hbds : ∀ c ∈ s, a ≤ c ∧ c ≤ b)
    (hpc : ∀ p q, s.IsConsecutive p q → LipschitzOnWith C f (Icc p q)) :
    LipschitzOnWith C f (Icc a b) := by
  refine consecutive_piece_induction (P := fun p q ↦ p ≤ q ∧ LipschitzOnWith C f (Icc p q))
    (fun x ↦ ⟨le_refl x, ?_⟩) (fun {p q r} h1 h2 ↦ ⟨h1.1.trans h2.1,
      lipschitzOnWith_Icc_trans h1.1 h2.1 h1.2 h2.2⟩) s a b ha hb hab hbds
    (fun p q hcons ↦ ⟨hcons.2.2.1.le, hpc p q hcons⟩) |>.2
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro y hy z hz
  simp [le_antisymm hy.2 hy.1, le_antisymm hz.2 hz.1]

namespace ClosedPwC1Curve

variable {x : E}

/-- On each closed piece between consecutive partition members, `γ.toPath.extend`
is Lipschitz with the maximum of `‖derivWithin γ.toPath.extend (Icc a b) t‖`
on the piece. -/
theorem lipschitzOnWith_piece (γ : ClosedPwC1Curve x) {a b : ℝ}
    (h : γ.closedPartition.IsConsecutive a b) :
    ∃ K : NNReal, LipschitzOnWith K γ.toPath.extend (Icc a b) := by
  have hab : a ≤ b := h.2.2.1.le
  have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc a b) := γ.contDiffOn_pieces a b h
  have h_dw_cont : ContinuousOn (derivWithin γ.toPath.extend (Icc a b)) (Icc a b) :=
    hcd.continuousOn_derivWithin (uniqueDiffOn_Icc h.2.2.1) le_rfl
  obtain ⟨t₀, _, ht₀_max⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨a, left_mem_Icc.mpr hab⟩ h_dw_cont.norm
  refine ⟨⟨_, norm_nonneg (derivWithin γ.toPath.extend (Icc a b) t₀)⟩, ?_⟩
  exact Convex.lipschitzOnWith_of_nnnorm_derivWithin_le (convex_Icc _ _)
    hcd.differentiableOn_one fun u hu ↦ ht₀_max hu

/-- Existence of a global Lipschitz constant on `Icc 0 1`, by gluing the
piece-wise constants. -/
theorem lipschitzOnWith_Icc01 (γ : ClosedPwC1Curve x) :
    ∃ K : NNReal, LipschitzOnWith K γ.toPath.extend (Icc (0 : ℝ) 1) := by
  classical
  set pairs : Finset (ℝ × ℝ) := (γ.closedPartition.product γ.closedPartition).filter
    (fun p ↦ γ.closedPartition.IsConsecutive p.1 p.2)
  have h_each : ∀ p ∈ pairs, ∃ K : NNReal,
      LipschitzOnWith K γ.toPath.extend (Icc p.1 p.2) := fun p hp ↦
    γ.lipschitzOnWith_piece (Finset.mem_filter.mp hp).2
  choose K hK using h_each
  set Kmax : NNReal := pairs.attach.sup (fun p ↦ K p.1 p.2)
  refine ⟨Kmax, lipschitzOnWith_of_consecutive_pieces γ.closedPartition 0 1
    γ.zero_mem_closedPartition γ.one_mem_closedPartition zero_le_one
    (fun _ hc ↦ ⟨(γ.closedPartition_subset hc).1, (γ.closedPartition_subset hc).2⟩) ?_⟩
  intro p q hcons
  have hpq_in : (p, q) ∈ pairs := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hcons.1, hcons.2.1⟩, hcons⟩
  exact (hK (p, q) hpq_in).weaken <| Finset.le_sup (s := pairs.attach)
    (f := fun p ↦ K p.1 p.2) (Finset.mem_attach pairs ⟨(p, q), hpq_in⟩)

/-- A `ClosedPwC1Curve` extends to a globally Lipschitz function `ℝ → E`.
Outside `[0, 1]`, the extended path is constant. -/
theorem lipschitzWith_extend (γ : ClosedPwC1Curve x) :
    ∃ K : NNReal, LipschitzWith K γ.toPath.extend := by
  obtain ⟨K, hK⟩ := γ.lipschitzOnWith_Icc01
  rw [lipschitzOnWith_iff_norm_sub_le] at hK
  refine ⟨K, ?_⟩
  rw [lipschitzWith_iff_norm_sub_le]
  intro s t
  set s' : ℝ := max 0 (min s 1)
  set t' : ℝ := max 0 (min t 1)
  have clamp_mem : ∀ u : ℝ, max 0 (min u 1) ∈ Icc (0 : ℝ) 1 := fun _ ↦
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hclamp : ∀ u : ℝ, γ.toPath.extend u = γ.toPath.extend (max 0 (min u 1)) := by
    intro u
    rcases le_total u 0 with hu0 | hu0
    · rw [γ.toPath.extend_of_le_zero hu0,
        show max 0 (min u 1) = 0 from by
          simp [min_eq_left (hu0.trans zero_le_one), max_eq_left hu0],
        γ.toPath.extend_zero]
    · rcases le_total u 1 with hu1 | hu1
      · simp [min_eq_left hu1, max_eq_right hu0]
      · rw [γ.toPath.extend_of_one_le hu1,
          show max 0 (min u 1) = 1 from by simp [min_eq_right hu1], γ.toPath.extend_one]
  have h_proj_lip : ‖s' - t'‖ ≤ ‖s - t‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc |s' - t'|
        ≤ max |(0 : ℝ) - 0| |min s 1 - min t 1| := abs_max_sub_max_le_max _ _ _ _
      _ = |min s 1 - min t 1| := by simp
      _ ≤ max |s - t| |(1 : ℝ) - 1| := abs_min_sub_min_le_max _ _ _ _
      _ = |s - t| := by simp
  rw [hclamp s, hclamp t]
  exact (hK (clamp_mem s) (clamp_mem t)).trans
    (mul_le_mul_of_nonneg_left h_proj_lip (NNReal.coe_nonneg _))

end ClosedPwC1Curve

namespace ClosedPwC1Immersion

variable {x : E}

/-- A `ClosedPwC1Immersion` extends to a globally Lipschitz function `ℝ → E`. -/
theorem lipschitzWith_extend (γ : ClosedPwC1Immersion x) :
    ∃ K : NNReal, LipschitzWith K γ.toPath.extend :=
  γ.toClosedPwC1Curve.lipschitzWith_extend

end ClosedPwC1Immersion

end
