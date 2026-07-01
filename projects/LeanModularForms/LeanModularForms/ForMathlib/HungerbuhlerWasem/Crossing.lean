/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.LaurentExtraction
import LeanModularForms.ForMathlib.HungerbuhlerWasem.SectorCancellation
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CrossingCPV
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CrossingHigherOrder
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CPVExistence
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CPVExistenceMulti
import LeanModularForms.ForMathlib.HungerbuhlerWasem.LocalCutoffs
import LeanModularForms.ForMathlib.HungerbuhlerWasem.MultiPoleDCT
import LeanModularForms.ForMathlib.CrossingAnalysis

/-!
# Per-pole CPV composition (T-GL-01)

For each pole `s ∈ S`, the CPV of the polar part `decomp.polarPart s` along
`γ` equals `2πi · w(γ, s) · residue f s` — when γ crosses `s` transversely
(witnessed by a `SingleCrossingData γ s`) and the higher-order Laurent
contributions vanish (which is the conclusion of T-SC-01 under condition (B)).

The proof composes three pieces:

* T-CC-01 (`cpv_simplePole_at_crossing`) for the simple pole `a₀ / (z − s)`
  — this contributes the `2πi · w · residue` term, because `a₀` is exactly
  `decomp.coeff s ⟨0, _⟩ = residue f s`.
* T-SC-01 (`hasCauchyPVOn_singleton_pow_of_conditionB_assembled`, packaged
  per-term) for the higher-order Laurent terms `aₖ / (z − s)^(k+1)`,
  `k ≥ 1` — these contribute zero under condition (B). We take the per-term
  vanishing as a hypothesis here (rather than building it out in this file).
* Three small algebraic helpers (`HasCauchyPV.add`, `HasCauchyPV.zero_fun`,
  `HasCauchyPV.finset_sum`, `HasCauchyPV.congr_pointwise`) that the public
  CPV API in `CauchyPrincipalValue.lean` does not currently provide.

## Main results

* `HungerbuhlerWasem.HasCauchyPV.add` — additivity of CPV.
* `HungerbuhlerWasem.HasCauchyPV.zero_fun` — `HasCauchyPV 0 γ z₀ 0`.
* `HungerbuhlerWasem.HasCauchyPV.finset_sum` — finite-sum form.
* `HungerbuhlerWasem.HasCauchyPV.congr_pointwise` — congruence-rewrite via
  pointwise equality off the singularity.
* `HungerbuhlerWasem.cpv_polarPart_at_pole_under_conditions` — the headline
  theorem.
-/

open Filter Topology Set Complex MeasureTheory
open scoped Real

noncomputable section

namespace HungerbuhlerWasem

variable {x y : ℂ}

/-- Additivity of `HasCauchyPV`: if both `f` and `g` have CPVs along `γ` at `z₀` (with
limits `L₁` and `L₂`) and their cutoff integrands are interval integrable for each
`ε > 0`, then `f + g` has CPV `L₁ + L₂`. -/
theorem HasCauchyPV.add {f g : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ L₁ L₂ : ℂ}
    (hf : HasCauchyPV f γ z₀ L₁) (hg : HasCauchyPV g γ z₀ L₂)
    (hfi : ∀ ε > 0, IntervalIntegrable
      (fun t ↦ cpvIntegrand f γ.toPath.extend z₀ ε t) volume 0 1)
    (hgi : ∀ ε > 0, IntervalIntegrable
      (fun t ↦ cpvIntegrand g γ.toPath.extend z₀ ε t) volume 0 1) :
    HasCauchyPV (fun z ↦ f z + g z) γ z₀ (L₁ + L₂) := by
  simp only [HasCauchyPV] at hf hg ⊢
  have heq : (fun ε ↦ ∫ t in (0 : ℝ)..1,
      cpvIntegrand (fun z ↦ f z + g z) γ.toPath.extend z₀ ε t) =ᶠ[𝓝[>] 0]
      (fun ε ↦ (∫ t in (0 : ℝ)..1, cpvIntegrand f γ.toPath.extend z₀ ε t) +
        (∫ t in (0 : ℝ)..1, cpvIntegrand g γ.toPath.extend z₀ ε t)) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [show (fun t ↦ cpvIntegrand (fun z ↦ f z + g z) γ.toPath.extend z₀ ε t) =
        (fun t ↦ cpvIntegrand f γ.toPath.extend z₀ ε t +
          cpvIntegrand g γ.toPath.extend z₀ ε t) from
      funext fun _ ↦ by simp only [cpvIntegrand]; split_ifs <;> ring]
    exact intervalIntegral.integral_add (hfi ε hε) (hgi ε hε)
  exact (hf.add hg).congr' heq.symm

/-- The Cauchy principal value of the zero function is zero. -/
theorem HasCauchyPV.zero_fun {γ : PiecewiseC1Path x y} {z₀ : ℂ} :
    HasCauchyPV (fun _ ↦ (0 : ℂ)) γ z₀ 0 := by
  simp only [HasCauchyPV]
  refine Tendsto.congr (f₁ := fun _ ↦ (0 : ℂ)) ?_ tendsto_const_nhds
  intro ε
  rw [show (fun t ↦ cpvIntegrand (fun _ : ℂ ↦ (0 : ℂ)) γ.toPath.extend z₀ ε t) =
      fun _ ↦ (0 : ℂ) from
    funext fun _ ↦ by simp only [cpvIntegrand]; split_ifs <;> simp]
  exact intervalIntegral.integral_zero.symm

/-- Congruence rewrite for `HasCauchyPV` via pointwise equality off the singularity:
if `f z = g z` for all `z ≠ z₀`, then `HasCauchyPV f γ z₀ L` implies
`HasCauchyPV g γ z₀ L`. -/
theorem HasCauchyPV.congr_pointwise {f g : ℂ → ℂ} {γ : PiecewiseC1Path x y}
    {z₀ L : ℂ} (h : HasCauchyPV f γ z₀ L) (hfg : ∀ z, z ≠ z₀ → f z = g z) :
    HasCauchyPV g γ z₀ L := by
  simp only [HasCauchyPV] at h ⊢
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [cpvIntegrand]
  split_ifs with hgt
  · rw [hfg _ fun heq ↦ by rw [heq, sub_self, norm_zero] at hgt; linarith]
  · rfl

/-- Finite sum of `HasCauchyPV`: if each `f i` has CPV `L i` along `γ` at `z₀` (with
cutoff integrability), the sum `∑ i ∈ T, f i` has CPV `∑ i ∈ T, L i`. -/
theorem HasCauchyPV.finset_sum {ι : Type*} [DecidableEq ι] (T : Finset ι)
    {γ : PiecewiseC1Path x y} {z₀ : ℂ} {f : ι → ℂ → ℂ} {L : ι → ℂ}
    (hf : ∀ i ∈ T, HasCauchyPV (f i) γ z₀ (L i))
    (hfi : ∀ i ∈ T, ∀ ε > 0, IntervalIntegrable
      (fun t ↦ cpvIntegrand (f i) γ.toPath.extend z₀ ε t) volume 0 1) :
    HasCauchyPV (fun z ↦ ∑ i ∈ T, f i z) γ z₀ (∑ i ∈ T, L i) := by
  induction T using Finset.induction_on with
  | empty => simpa [Finset.sum_empty] using HasCauchyPV.zero_fun (γ := γ) (z₀ := z₀)
  | @insert a T' hia ih =>
    have h_T'_int : ∀ ε > 0, IntervalIntegrable
        (fun t ↦ cpvIntegrand (fun z ↦ ∑ i ∈ T', f i z) γ.toPath.extend z₀ ε t)
        volume 0 1 := fun ε hε ↦ by
      rw [show (fun t ↦ cpvIntegrand (fun z ↦ ∑ i ∈ T', f i z)
          γ.toPath.extend z₀ ε t) =
          (fun t ↦ ∑ i ∈ T', cpvIntegrand (f i) γ.toPath.extend z₀ ε t) from
        funext fun _ ↦ by
          simp only [cpvIntegrand]
          split_ifs
          · rw [Finset.sum_mul]
          · exact Finset.sum_const_zero.symm,
        show (fun t ↦ ∑ i ∈ T', cpvIntegrand (f i) γ.toPath.extend z₀ ε t) =
          ∑ i ∈ T', fun t ↦ cpvIntegrand (f i) γ.toPath.extend z₀ ε t from
          funext fun _ ↦ (Finset.sum_apply _ _ _).symm]
      exact IntervalIntegrable.sum T'
        (fun i hi ↦ hfi i (Finset.mem_insert_of_mem hi) ε hε)
    rw [show (fun z ↦ ∑ i ∈ insert a T', f i z) = (fun z ↦ f a z + ∑ i ∈ T', f i z) from
        funext fun _ ↦ Finset.sum_insert hia, Finset.sum_insert hia]
    exact HasCauchyPV.add (hf a (Finset.mem_insert_self a T'))
      (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hfi i (Finset.mem_insert_of_mem hi)))
      (hfi a (Finset.mem_insert_self a T')) h_T'_int

/-- Pointwise equality of `cpvIntegrandOn S f` with the cutoff integrand of
the polar-part decomposition `analyticRemainder + ∑ polarPart s`. The cutoff
zeroes both sides when `∃ s ∈ S, ‖γ(t) - s‖ ≤ ε`; otherwise `γ(t) ∈ U \ S`
and `decomp.decomp` applies. -/
private theorem cpvIntegrandOn_eq_of_decomp
    {U : Set ℂ} {S : Finset ℂ} {f : ℂ → ℂ}
    (decomp : PolarPartDecomposition f S U)
    {γ : PiecewiseC1Path x x} {t : ℝ} (ht : γ.toPath.extend t ∈ U) {ε : ℝ}
    (hε_pos : 0 < ε) :
    cpvIntegrandOn S f γ.toPath.extend ε t =
      cpvIntegrandOn S
        (fun z ↦ decomp.analyticRemainder z + ∑ s ∈ S, decomp.polarPart s z)
        γ.toPath.extend ε t := by
  classical
  by_cases h : ∃ s ∈ S, ‖γ.toPath.extend t - s‖ ≤ ε
  · rw [cpvIntegrandOn_of_exists_le h, cpvIntegrandOn_of_exists_le h]
  · have h_far : ∀ s ∈ S, ε < ‖γ.toPath.extend t - s‖ :=
      fun s hs ↦ lt_of_not_ge fun h_le ↦ h ⟨s, hs, h_le⟩
    have hγ_notS : γ.toPath.extend t ∉ (↑S : Set ℂ) := fun h_mem ↦ by
      have h_ne_zero := h_far _ (Finset.mem_coe.mp h_mem)
      simp at h_ne_zero; linarith
    rw [cpvIntegrandOn_of_forall_gt h_far, cpvIntegrandOn_of_forall_gt h_far,
      decomp.decomp _ ⟨ht, hγ_notS⟩]

/-- **Hungerbühler–Wasem Theorem 3.3 — compositional crossing form.**

For `f` with a `PolarPartDecomposition` over `S ⊆ U` and a closed γ
null-homologous in `U` (which may cross poles of any order), the multi-point
Cauchy principal value of `∮f` along `γ` equals
`∑ s ∈ S, 2πi · w(γ, s) · residue f s`.

Per-pole CPV witnesses for each polar part — typically obtained from
`cpv_polarPart_at_pole_under_conditions` (T-GL-01) — are supplied as data.
The analytic-remainder CPV and integrability are derived internally from
`analyticRemainder_hasCauchyPVOn_zero` and
`cpvIntegrandOn_diff_intervalIntegrable`. The avoidance form
`residueTheorem_avoidance` is the special case where the per-pole witnesses
come from `hasCauchyPVOn_of_avoids`.

This is the *compositional* form: it consumes a `PolarPartDecomposition` and
per-pole CPV witnesses as data. -/
theorem residueTheorem_crossing_compositional
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U)
    (h_polar_cpv : ∀ s ∈ S, HasCauchyPVOn S (decomp.polarPart s)
      γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s)) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γP t ∈ U := h_null.image_subset
  have h_rem_cpv : HasCauchyPVOn S decomp.analyticRemainder γP 0 :=
    HungerbuhlerWasem.analyticRemainder_hasCauchyPVOn_zero hU_open hU_ne
      hS_in_U γ h_null decomp
  have h_rem_int : ∀ ε > 0, IntervalIntegrable
      (fun t ↦ cpvIntegrandOn S decomp.analyticRemainder
        γP.toPath.extend ε t) volume 0 1 :=
    fun ε _ ↦ HungerbuhlerWasem.cpvIntegrandOn_diff_intervalIntegrable γ S
      decomp.analyticRemainder_diff hγ_in_U ε
  have h_polar_int : ∀ s ∈ S, ∀ ε > 0, IntervalIntegrable
      (fun t ↦ cpvIntegrandOn S (decomp.polarPart s)
        γP.toPath.extend ε t) volume 0 1 :=
    fun s hs ε hε ↦
      HungerbuhlerWasem.cpvIntegrandOn_polarPart_intervalIntegrable γ
        hS_in_U decomp hs h_null hε
  have h_sum_polar :=
    HasCauchyPVOn.finset_sum S h_polar_cpv h_polar_int
  have h_sum_polar_int : ∀ ε > 0, IntervalIntegrable
      (fun t ↦ cpvIntegrandOn S (fun z ↦ ∑ s ∈ S, decomp.polarPart s z)
        γP.toPath.extend ε t) volume 0 1 := by
    intro ε hε
    rw [show (fun t ↦ cpvIntegrandOn S
        (fun z ↦ ∑ s ∈ S, decomp.polarPart s z) γP.toPath.extend ε t) =
        (fun t ↦ ∑ s ∈ S, cpvIntegrandOn S (decomp.polarPart s)
          γP.toPath.extend ε t) from
      funext fun _ ↦ by
        simp only [cpvIntegrandOn]
        split_ifs
        · exact Finset.sum_const_zero.symm
        · rw [Finset.sum_mul],
      show (fun t ↦ ∑ s ∈ S, cpvIntegrandOn S (decomp.polarPart s)
        γP.toPath.extend ε t) = ∑ s ∈ S, fun t ↦ cpvIntegrandOn S (decomp.polarPart s)
          γP.toPath.extend ε t from funext fun _ ↦ (Finset.sum_apply _ _ _).symm]
    exact IntervalIntegrable.sum S (fun s hs ↦ h_polar_int s hs ε hε)
  have h_decomp := HasCauchyPVOn.add h_rem_cpv h_sum_polar h_rem_int h_sum_polar_int
  rw [zero_add] at h_decomp
  simp only [HasCauchyPVOn] at h_decomp ⊢
  refine h_decomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le (zero_le_one' ℝ)] at ht
  exact (cpvIntegrandOn_eq_of_decomp decomp (hγ_in_U t ht) hε).symm

/-- **Per-pole CPV at an uncrossed pole.** When γ avoids the pole `s`, the polar
part `decomp.polarPart s` is regular along γ, and DCT gives that the multi-point
CPV equals the contour integral of the polar part along γ. The contour integral
in turn equals `2πi · w · res f s` by the avoidance computation
(`residueTheorem_avoidance` per-pole step). -/
theorem cpv_polarPart_at_uncrossed_pole
    {U : Set ℂ} (_hU_open : IsOpen U) (_hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U)
    (s : ℂ) (hs : s ∈ S)
    (h_avoid : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s) :
    HasCauchyPVOn S (decomp.polarPart s)
      γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := avoids_delta_bound γP s h_avoid
  have h_deriv_int : IntervalIntegrable (deriv γP.toPath.extend) MeasureTheory.volume 0 1 :=
    HungerbuhlerWasem.deriv_intervalIntegrable_of_lipschitz γP hLip
  have h_cont_inv_each : ∀ k : Fin (decomp.order s), ContinuousOn
      (fun t ↦ decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1))
      (Icc (0 : ℝ) 1) := fun k ↦ ContinuousOn.div continuousOn_const
      ((γP.toPath.continuous_extend.continuousOn.sub continuousOn_const).pow _)
      fun t ht hzero ↦
        h_avoid t ht (sub_eq_zero.mp (pow_eq_zero_iff (Nat.succ_pos _).ne' |>.mp hzero))
  have h_pp_curve_cont : ContinuousOn
      (fun t ↦ decomp.polarPart s (γP.toPath.extend t)) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    have h_sum_cont : ContinuousOn
        (fun t ↦ ∑ k : Fin (decomp.order s),
          decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1))
        (Icc (0 : ℝ) 1) :=
      continuousOn_finsetSum _ fun k _ ↦ h_cont_inv_each k
    refine h_sum_cont.congr fun t ht ↦ ?_
    change decomp.polarPart s (γP.toPath.extend t) =
      ∑ k : Fin (decomp.order s),
        decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1)
    exact decomp.polarPart_eq s hs (γP.toPath.extend t) (h_avoid t ht)
  have h_full : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (decomp.polarPart s) γP)
      MeasureTheory.volume 0 1 :=
    h_deriv_int.continuousOn_mul h_pp_curve_cont
  have h_contourInt :
      γP.contourIntegral (decomp.polarPart s) =
        2 * ↑Real.pi * I * generalizedWindingNumber γP s * residue f s := by
    have h_int_each : ∀ k : Fin (decomp.order s),
        IntervalIntegrable
          (fun t ↦ decomp.coeff s k /
            (γP.toPath.extend t - s) ^ (k.val + 1) *
            deriv γP.toPath.extend t) volume 0 1 :=
      fun k ↦ h_deriv_int.continuousOn_mul ((h_cont_inv_each k).mono
        (by rw [uIcc_of_le (zero_le_one' ℝ)]))
    have h_polarPart_curve : ∀ t ∈ Icc (0 : ℝ) 1,
        decomp.polarPart s (γP.toPath.extend t) =
          ∑ k : Fin (decomp.order s),
            decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1) :=
      fun t ht ↦ decomp.polarPart_eq s hs (γP.toPath.extend t) (h_avoid t ht)
    have h_int_eq : γP.contourIntegral (decomp.polarPart s) =
        γP.contourIntegral (fun z ↦ ∑ k : Fin (decomp.order s),
          decomp.coeff s k / (z - s) ^ (k.val + 1)) := by
      simp only [PiecewiseC1Path.contourIntegral]
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [uIcc_of_le (zero_le_one' ℝ)] at ht
      change decomp.polarPart s (γP.toPath.extend t) * deriv γP.toPath.extend t =
        (∑ k : Fin (decomp.order s),
          decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1)) *
            deriv γP.toPath.extend t
      rw [h_polarPart_curve t ht]
    rw [h_int_eq]
    rw [PiecewiseC1Path.contourIntegral_finset_sum Finset.univ
      (fun k z ↦ decomp.coeff s k / (z - s) ^ (k.val + 1)) γP (fun k _ ↦ h_int_each k)]
    by_cases h_order_pos : 0 < decomp.order s
    · have h_split := Finset.sum_eq_single_of_mem
        (s := (Finset.univ : Finset (Fin (decomp.order s))))
        (a := ⟨0, h_order_pos⟩)
        (f := fun k : Fin (decomp.order s) ↦
          γP.contourIntegral (fun z ↦ decomp.coeff s k / (z - s) ^ (k.val + 1)))
        (Finset.mem_univ _)
        (fun k _ hk_ne ↦ by
          have hk_ge_1 : k.val ≥ 1 := by
            have : k.val ≠ 0 := fun h ↦ hk_ne (Fin.ext h)
            lia
          exact contourIntegral_higherOrder_eq_zero_of_avoids γP h_avoid (by lia)
            _ (h_int_each k))
      rw [h_split]
      simp only [zero_add, pow_one]
      rw [show decomp.coeff s ⟨0, h_order_pos⟩ = residue f s from
        ((decomp.residue_eq s hs).trans (dif_pos h_order_pos)).symm]
      set w := generalizedWindingNumber γP s with hw_def
      have h_winding_int_eq :
          γP.contourIntegral (fun z ↦ (z - s)⁻¹) = 2 * ↑Real.pi * I * w := by
        unfold generalizedWindingNumber at hw_def
        rw [(hasCauchyPV_of_avoids (f := fun z ↦ (z - s)⁻¹) (γ := γP) (z₀ := s)
          ⟨δ, hδ_pos, fun t ht ↦ hδ_bound t ht⟩).cauchyPV_eq] at hw_def
        rw [hw_def, mul_inv_cancel_left₀ (by norm_num [Real.pi_ne_zero, Complex.I_ne_zero])]
      simp only [div_eq_mul_inv, PiecewiseC1Path.contourIntegral_smul, h_winding_int_eq]
      ring
    · rw [show residue f s = 0 by rw [decomp.residue_eq s hs, dif_neg h_order_pos],
        mul_zero]
      exact Finset.sum_eq_zero fun k _ ↦ absurd k.isLt (by lia)
  have h_meas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun t ↦ cpvIntegrandOn S (decomp.polarPart s)
        γP.toPath.extend ε t)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (HungerbuhlerWasem.cpvIntegrandOn_polarPart_intervalIntegrable γ
      hS_in_U decomp hs h_null hε).aestronglyMeasurable_restrict_uIoc
  have h_bound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Set.uIoc (0 : ℝ) 1 →
      ‖cpvIntegrandOn S (decomp.polarPart s) γP.toPath.extend ε x‖ ≤
        ‖PiecewiseC1Path.contourIntegrand (decomp.polarPart s) γP x‖ := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine MeasureTheory.ae_of_all _ fun t _ ↦ ?_
    rw [HungerbuhlerWasem.cpvIntegrandOn_eq_indicator_compl γP S
      (decomp.polarPart s) ε t]
    by_cases ht_in : t ∈ (HungerbuhlerWasem.cpv_badSet γP S ε)ᶜ
    · rw [Set.indicator_of_mem ht_in]
    · rw [Set.indicator_of_notMem ht_in, norm_zero]; exact norm_nonneg _
  have h_pointwise : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      Tendsto (fun ε ↦ cpvIntegrandOn S (decomp.polarPart s)
          γP.toPath.extend ε x) (𝓝[>] 0)
        (𝓝 (PiecewiseC1Path.contourIntegrand (decomp.polarPart s) γP x)) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mp
      (HungerbuhlerWasem.cpvIntegrandOn_tendsto_contourIntegrand_ae γ S
        (decomp.polarPart s))
  unfold HasCauchyPVOn
  rw [show (2 * ↑Real.pi * I *
      generalizedWindingNumber γP s * residue f s : ℂ) =
      γP.contourIntegral (decomp.polarPart s) from h_contourInt.symm]
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t ↦ ‖PiecewiseC1Path.contourIntegrand (decomp.polarPart s) γP t‖)
    h_meas h_bound h_full.norm h_pointwise

/-- **Laurent polynomial uniqueness — vanishing form.**

If a finite Laurent polynomial `Σ k : Fin N, c k / (z - s)^(k+1)` is eventually
equal (in the punctured neighborhood of `s`) to an analytic function at `s`,
then all coefficients `c k` vanish.

We prove this by reverse induction on `N`: peel the highest-order coefficient
(`c_{N-1}`) by evaluating both sides of `(z - s)^N · LHS = (z - s)^N · g` at
`z = s`. The polynomial side at `z = s` equals `c_{N-1}` (only the `k = N-1`
term survives, as it has exponent 0); the analytic side equals `0^N · g(s) = 0`
when `N ≥ 1`. Hence `c_{N-1} = 0`. Induct down. -/
private theorem laurent_polynomial_zero_of_eventuallyEq_analytic :
    ∀ (N : ℕ) (c : Fin N → ℂ) {s : ℂ} {g : ℂ → ℂ}, AnalyticAt ℂ g s →
      (fun z ↦ ∑ k : Fin N, c k / (z - s) ^ (k.val + 1)) =ᶠ[𝓝[≠] s] g →
      ∀ k : Fin N, c k = 0 := by
  classical
  intro N
  induction N with
  | zero =>
    intro c s g _ _ k
    exact absurd k.isLt (by lia)
  | succ N ih =>
    intro c s g hg h_eq
    set P : ℂ → ℂ := fun z ↦ ∑ k : Fin (N + 1), c k * (z - s) ^ (N - k.val) with hP_def
    set Q : ℂ → ℂ := fun z ↦ (z - s) ^ (N + 1) * g z with hQ_def
    have hP_an : AnalyticAt ℂ P s := by
      refine Finset.analyticAt_fun_sum _ fun k _ ↦ ?_
      exact analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).pow _)
    have hQ_an : AnalyticAt ℂ Q s :=
      ((analyticAt_id.sub analyticAt_const).pow (N + 1)).mul hg
    have h_PQ_punc : P =ᶠ[𝓝[≠] s] Q := by
      filter_upwards [h_eq, self_mem_nhdsWithin] with z hz hz_ne
      have hz_sub : (z - s) ≠ 0 := sub_ne_zero.mpr hz_ne
      have h_lhs : P z = (z - s) ^ (N + 1) *
          (∑ k : Fin (N + 1), c k / (z - s) ^ (k.val + 1)) := by
        rw [hP_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [div_eq_mul_inv, show (z - s) ^ (N + 1) =
          (z - s) ^ (N - k.val) * (z - s) ^ (k.val + 1) by
            rw [← pow_add]; congr 1; omega]
        have h_pow_ne : ((z - s) ^ (k.val + 1)) ≠ 0 := pow_ne_zero _ hz_sub
        field_simp
      rw [h_lhs, hz, hQ_def]
    have h_PQ_full : P =ᶠ[𝓝 s] Q :=
      (hP_an.frequently_eq_iff_eventually_eq hQ_an).mp h_PQ_punc.frequently
    have hPs : P s = c ⟨N, Nat.lt_succ_self _⟩ := by
      change (∑ k : Fin (N + 1), c k * (s - s) ^ (N - k.val)) =
        c ⟨N, Nat.lt_succ_self _⟩
      rw [sub_self, Finset.sum_eq_single (⟨N, Nat.lt_succ_self _⟩ : Fin (N + 1))
        (fun k _ hk ↦ by
          rw [zero_pow (Nat.pos_iff_ne_zero.mp <| Nat.sub_pos_of_lt <|
            (Nat.lt_succ_iff.mp k.isLt).lt_of_ne fun h ↦ hk (Fin.ext h)), mul_zero])
        (fun h ↦ absurd (Finset.mem_univ _) h)]
      simp
    have hcN_zero : c ⟨N, Nat.lt_succ_self _⟩ = 0 := by
      rw [← hPs, h_PQ_full.eq_of_nhds]
      change (s - s) ^ (N + 1) * g s = 0
      rw [sub_self, zero_pow (Nat.succ_ne_zero N), zero_mul]
    set c' : Fin N → ℂ := fun k ↦ c k.castSucc
    have h_eq' : (fun z ↦ ∑ k : Fin N, c' k / (z - s) ^ (k.val + 1)) =ᶠ[𝓝[≠] s] g := by
      filter_upwards [h_eq] with z hz
      rw [show ∑ k : Fin N, c' k / (z - s) ^ (k.val + 1) =
          ∑ k : Fin (N + 1), c k / (z - s) ^ (k.val + 1) from ?_]
      · exact hz
      rw [Fin.sum_univ_castSucc, show (Fin.last N : Fin (N+1)) =
          ⟨N, Nat.lt_succ_self _⟩ from rfl, hcN_zero, zero_div]
      simp [c']
    have ih_result : ∀ k : Fin N, c' k = 0 := ih c' hg h_eq'
    intro k
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp k.isLt) with hk | hk
    · rw [show k = (⟨k.val, hk⟩ : Fin N).castSucc from by ext; rfl]
      exact ih_result ⟨k.val, hk⟩
    · rw [show k = ⟨N, Nat.lt_succ_self _⟩ from by ext; exact hk]
      exact hcN_zero

/-- Auxiliary: a Laurent polynomial `Σ k : Fin N, c k / (z - s)^(k+1)` equals
its `(Fin (max N M))` extension (with zeros) at every `z ≠ s`. -/
private lemma laurent_sum_extend {N M : ℕ} (hNM : N ≤ M) (c : Fin N → ℂ)
    (s z : ℂ) (_hz : z ≠ s) :
    (∑ k : Fin N, c k / (z - s) ^ (k.val + 1)) =
      ∑ j : Fin M,
        (if hj : j.val < N then c ⟨j.val, hj⟩ else (0 : ℂ)) /
          (z - s) ^ (j.val + 1) := by
  classical
  have h_emb : Function.Injective
      (fun k : Fin N ↦ (⟨k.val, lt_of_lt_of_le k.isLt hNM⟩ : Fin M)) := by
    intro a b hab; ext; exact Fin.mk.inj_iff.mp hab
  rw [show (∑ j : Fin M, (if hj : j.val < N then c ⟨j.val, hj⟩ else (0 : ℂ)) /
        (z - s) ^ (j.val + 1)) =
      ∑ j ∈ (Finset.univ : Finset (Fin M)).filter (fun j ↦ j.val < N),
        (if hj : j.val < N then c ⟨j.val, hj⟩ else (0 : ℂ)) /
          (z - s) ^ (j.val + 1) from ?_]
  · have h_image : (Finset.univ : Finset (Fin N)).image
        (fun k ↦ (⟨k.val, lt_of_lt_of_le k.isLt hNM⟩ : Fin M)) =
        (Finset.univ : Finset (Fin M)).filter (fun j ↦ j.val < N) := by
      ext j
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rintro ⟨k, hk⟩; rw [← hk]; exact k.isLt
      · intro hj; exact ⟨⟨j.val, hj⟩, by ext; rfl⟩
    rw [← h_image, Finset.sum_image (fun a _ b _ h ↦ h_emb h)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [dif_pos k.isLt]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hj : j.val < N
    · rw [if_pos hj]
    · rw [if_neg hj, dif_neg hj, zero_div]

/-- **Bridge: extended Laurent coefficients of two decompositions of the same `f`
must agree at every index.**

If `Σ k : Fin N₁, c₁ k / (z - s)^(k+1) - Σ k : Fin N₂, c₂ k / (z - s)^(k+1)`
is eventually equal (in `𝓝[≠] s`) to an analytic function at `s`, then for every
index `j`, the extended coefficients agree. -/
private theorem laurent_extended_coeff_eq_of_diff_analytic
    {N₁ N₂ : ℕ} (c₁ : Fin N₁ → ℂ) (c₂ : Fin N₂ → ℂ)
    {s : ℂ} {h : ℂ → ℂ} (hh : AnalyticAt ℂ h s)
    (h_diff : (fun z ↦ (∑ k : Fin N₁, c₁ k / (z - s) ^ (k.val + 1)) -
                        (∑ k : Fin N₂, c₂ k / (z - s) ^ (k.val + 1))) =ᶠ[𝓝[≠] s] h) :
    ∀ j : ℕ,
      (if hj : j < N₁ then c₁ ⟨j, hj⟩ else (0 : ℂ)) =
      (if hj : j < N₂ then c₂ ⟨j, hj⟩ else (0 : ℂ)) := by
  classical
  set M : ℕ := max N₁ N₂
  set d : Fin M → ℂ := fun j ↦
    (if hj : j.val < N₁ then c₁ ⟨j.val, hj⟩ else (0 : ℂ)) -
    (if hj : j.val < N₂ then c₂ ⟨j.val, hj⟩ else (0 : ℂ)) with hd_def
  have h_sum_eq : (fun z ↦ ∑ j : Fin M, d j / (z - s) ^ (j.val + 1)) =ᶠ[𝓝[≠] s] h := by
    filter_upwards [h_diff, self_mem_nhdsWithin] with z hz (hz_ne : z ≠ s)
    have h_d_split : (∑ j : Fin M, d j / (z - s) ^ (j.val + 1)) =
        (∑ j : Fin M,
          (if hj : j.val < N₁ then c₁ ⟨j.val, hj⟩ else (0 : ℂ)) /
            (z - s) ^ (j.val + 1)) -
        (∑ j : Fin M,
          (if hj : j.val < N₂ then c₂ ⟨j.val, hj⟩ else (0 : ℂ)) /
            (z - s) ^ (j.val + 1)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hd_def, sub_div]
    rw [h_d_split,
      ← laurent_sum_extend (le_max_left N₁ N₂) c₁ s z hz_ne,
      ← laurent_sum_extend (le_max_right N₁ N₂) c₂ s z hz_ne]
    exact hz
  have hd_zero : ∀ j : Fin M, d j = 0 :=
    laurent_polynomial_zero_of_eventuallyEq_analytic M d hh h_sum_eq
  intro j
  by_cases hj_M : j < M
  · have hd_j_zero := hd_zero ⟨j, hj_M⟩
    rw [hd_def] at hd_j_zero
    exact sub_eq_zero.mp hd_j_zero
  · rw [dif_neg fun h ↦ hj_M (lt_of_lt_of_le h (le_max_left _ _)),
      dif_neg fun h ↦ hj_M (lt_of_lt_of_le h (le_max_right _ _))]

/-- **Corner-friendly form of `angle_compat_of_condB`** (T-BR-Y10b).
Drops the `h_t₀_off` hypothesis: returns the angle equation in terms of
`angleAtCrossing γ t₀ ht₀` directly, which is `π` at smooth points and
`arg L_+ - arg(-L_-)` at corner points. The caller is responsible for
interpreting the angle in the corner case (via
`h_B_of_angle_compat_corner`). -/
theorem angle_compat_of_condB_anywhere
    {U : Set ℂ} {S : Finset ℂ} {f : ℂ → ℂ} (hU_open : IsOpen U) (hS_in_U : ↑S ⊆ U)
    (γ : ClosedPwC1Immersion x)
    (decomp : PolarPartDecomposition f S U)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    {s : ℂ} (hs : s ∈ S) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at₀ : γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s) :
    ∀ (k : Fin (decomp.order s)), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∃ m : ℤ, ((k.val : ℝ)) * angleAtCrossing γ.toPwC1Immersion t₀ ht₀ =
        (m : ℝ) * (2 * Real.pi) := by
  classical
  intro k hk hk_ne
  have ht_Icc : t₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht₀
  obtain ⟨N, a, g, hg, hf_eq, h_angles⟩ :=
    hCondB.laurent_compatible s hs t₀ ht_Icc h_at₀ ht₀
  set hOther : ℂ → ℂ := fun z ↦
    g z - decomp.analyticRemainder z -
      ∑ s' ∈ S.erase s, decomp.polarPart s' z
  have h_arem_an : AnalyticAt ℂ decomp.analyticRemainder s :=
    decomp.analyticRemainder_diff.analyticAt
      (hU_open.mem_nhds (hS_in_U (Finset.mem_coe.mpr hs)))
  have h_otherPolar_an : AnalyticAt ℂ
      (fun z ↦ ∑ s' ∈ S.erase s, decomp.polarPart s' z) s := by
    refine Finset.analyticAt_fun_sum _ fun s' hs' ↦ ?_
    have hne : s' ≠ s := (Finset.mem_erase.mp hs').1
    have h_sum_an : AnalyticAt ℂ
        (fun z ↦ ∑ k : Fin (decomp.order s'),
          decomp.coeff s' k / (z - s') ^ (k.val + 1)) s :=
      Finset.analyticAt_fun_sum _ fun k _ ↦
        analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
          (pow_ne_zero _ (sub_ne_zero.mpr hne.symm))
    refine h_sum_an.congr ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds
      (show s ∈ ({s'}ᶜ : Set ℂ) from fun h_eq ↦ hne h_eq.symm)] with z hz
    exact (decomp.polarPart_eq s' (Finset.mem_erase.mp hs').2 z hz).symm
  have hOther_an : AnalyticAt ℂ hOther s :=
    (hg.sub h_arem_an).sub h_otherPolar_an
  have h_diff : (fun z ↦ (∑ k : Fin (decomp.order s),
        decomp.coeff s k / (z - s) ^ (k.val + 1)) -
      (∑ k : Fin N, a k / (z - s) ^ (k.val + 1))) =ᶠ[𝓝[≠] s] hOther := by
    filter_upwards [hf_eq, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hU_open.mem_nhds (hS_in_U (Finset.mem_coe.mpr hs))),
      nhdsWithin_le_nhds ((S.erase s).finite_toSet.isClosed.isOpen_compl.mem_nhds
        (show s ∉ (↑(S.erase s) : Set ℂ) from fun h_mem ↦
          (Finset.mem_erase.mp (Finset.mem_coe.mp h_mem)).1 rfl))]
      with z hz hz_ne hz_U hz_not_other
    have hz_not_S : z ∉ (↑S : Set ℂ) := fun h_mem ↦ by
      by_cases h_eq : z = s
      · exact hz_ne h_eq
      · exact hz_not_other (Finset.mem_coe.mpr
          (Finset.mem_erase.mpr ⟨h_eq, Finset.mem_coe.mp h_mem⟩))
    have h_decomp_z : f z = decomp.analyticRemainder z +
        ∑ s' ∈ S, decomp.polarPart s' z := decomp.decomp z ⟨hz_U, hz_not_S⟩
    have h_pp_eq : decomp.polarPart s z =
        ∑ k : Fin (decomp.order s), decomp.coeff s k / (z - s) ^ (k.val + 1) :=
      decomp.polarPart_eq s hs z hz_ne
    change (∑ k : Fin (decomp.order s), decomp.coeff s k / (z - s) ^ (k.val + 1)) -
        (∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) =
      g z - decomp.analyticRemainder z -
        ∑ s' ∈ S.erase s, decomp.polarPart s' z
    have h_combined : decomp.analyticRemainder z +
        (∑ s' ∈ S.erase s, decomp.polarPart s' z) +
        (∑ k : Fin (decomp.order s), decomp.coeff s k / (z - s) ^ (k.val + 1)) =
        g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1) := by
      have h_full : f z = decomp.analyticRemainder z +
          (∑ s' ∈ S.erase s, decomp.polarPart s' z) + decomp.polarPart s z := by
        rw [h_decomp_z, ← Finset.add_sum_erase _ _ hs]; ring
      rw [← h_pp_eq]
      linear_combination -h_full + hz
    linear_combination h_combined
  have h_k_eq :=
    laurent_extended_coeff_eq_of_diff_analytic (decomp.coeff s) a hOther_an h_diff k.val
  rw [dif_pos k.isLt] at h_k_eq
  have h_eq : decomp.coeff s ⟨k.val, k.isLt⟩ = decomp.coeff s k := by congr
  by_cases hk_N : k.val < N
  · rw [dif_pos hk_N] at h_k_eq
    exact h_angles ⟨k.val, hk_N⟩ (by rw [← h_k_eq, h_eq]; exact hk_ne) hk
  · rw [dif_neg hk_N, h_eq] at h_k_eq
    exact absurd h_k_eq hk_ne

/-- **T-BR-Y1 helper.** Angle compatibility for `decomp.coeff` at a smooth crossing,
derived from condition (B). At an off-partition crossing the angle is `π`, so this
specialises `angle_compat_of_condB_anywhere`. -/
theorem angle_compat_of_condB
    {U : Set ℂ} {S : Finset ℂ} {f : ℂ → ℂ} (hU_open : IsOpen U) (hS_in_U : ↑S ⊆ U)
    (γ : ClosedPwC1Immersion x)
    (decomp : PolarPartDecomposition f S U)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    {s : ℂ} (hs : s ∈ S) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at₀ : γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s)
    (h_t₀_off : t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition) :
    ∀ (k : Fin (decomp.order s)), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∃ m : ℤ, ((k.val : ℝ)) * Real.pi = (m : ℝ) * (2 * Real.pi) := fun k hk hk_ne ↦ by
  have := angle_compat_of_condB_anywhere hU_open hS_in_U γ decomp hCondB hs ht₀ h_at₀
    k hk hk_ne
  rwa [angleAtCrossing_smooth γ.toPwC1Immersion t₀ ht₀ h_t₀_off] at this

/-- **Bridge: corner-angle compat to corner `h_B`.** Given the condition (B)
angle equation at a corner — written in terms of `angleAtCrossing`, which at
a corner unfolds to `arg L_+ - arg(-L_-)` for the canonical one-sided derivative
limits — bridge it to the unit-circle power equation
`(L_+/‖L_+‖)^k = ((-L_-)/‖L_-‖)^k`. This packages the angle data for use with
`cpv_polarPart_at_crossed_pole_hasCauchyPV_asymmetric_corner`. -/
theorem corner_angle_compat_to_h_B
    (γ : ClosedPwC1Immersion x)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_part : t₀ ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition)
    {L_minus L_plus : ℂ} (hL_minus_ne : L_minus ≠ 0) (hL_plus_ne : L_plus ≠ 0)
    (hL_left_spec : L_minus = Classical.choose
      (γ.toPwC1Immersion.left_deriv_limit t₀ h_part))
    (hL_right_spec : L_plus = Classical.choose
      (γ.toPwC1Immersion.right_deriv_limit t₀ h_part))
    {k : ℕ} (hk : 2 ≤ k)
    (h_angle_raw : ∃ m : ℤ,
      ((k - 1 : ℕ) : ℝ) * angleAtCrossing γ.toPwC1Immersion t₀ ht₀ =
        (m : ℝ) * (2 * Real.pi)) :
    (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1) =
    ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1) := by
  rw [show angleAtCrossing γ.toPwC1Immersion t₀ ht₀ =
      Complex.arg L_plus - Complex.arg (-L_minus) by
    unfold angleAtCrossing; rw [dif_pos h_part, ← hL_left_spec, ← hL_right_spec]]
    at h_angle_raw
  exact h_B_of_angle_compat_corner hL_minus_ne hL_plus_ne hk h_angle_raw

/-- **Crossing-set existence at a pole with endpoint avoidance.**

For a `ClosedPwC1Immersion γ`, a target pole `s ∈ ℂ`, and the hypothesis that
the basepoint `x ∉ S` with `s ∈ S`, the level-set `{t ∈ [0,1] | γ(t) = s}` is
finite (`crossingSet_finite`) and forms a `Finset ℝ` of crossings strictly in
`Ioo 0 1` (since `γ(0) = γ(1) = x ≠ s`).  Returns an `Exists` bundle with
the standard four predicates `(Ioo, at, complete)` required by the corner-form
multi-crossing CPV API. -/
theorem crossings_finset_of_endpts_off
    (γ : ClosedPwC1Immersion x) {s : ℂ} {S : Finset ℂ} (hs : s ∈ S)
    (hx_notin_S : x ∉ (↑S : Set ℂ)) :
    ∃ crossings : Finset ℝ,
      (∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ t ∈ crossings, γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s →
          t ∈ crossings) := by
  have h0_ne : (γ.toPwC1Immersion : ℝ → ℂ) 0 ≠ s := by
    simp only [show (γ.toPwC1Immersion : ℝ → ℂ) 0 =
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 0 from rfl,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend_zero]
    exact fun h_eq ↦ hx_notin_S (h_eq ▸ hs)
  have h1_ne : (γ.toPwC1Immersion : ℝ → ℂ) 1 ≠ s := by
    simp only [show (γ.toPwC1Immersion : ℝ → ℂ) 1 =
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 1 from rfl,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend_one]
    exact fun h_eq ↦ hx_notin_S (h_eq ▸ hs)
  have hfin : Set.Finite (γ.toPwC1Immersion.crossingSet s) :=
    PwC1Immersion.crossingSet_finite γ.toPwC1Immersion s h0_ne h1_ne
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · intro t ht
    rw [Set.Finite.mem_toFinset] at ht
    refine ⟨lt_of_le_of_ne ht.1.1 fun h_eq ↦ h0_ne ?_,
            lt_of_le_of_ne ht.1.2 fun h_eq ↦ h1_ne ?_⟩
    · rw [← h_eq] at ht; exact ht.2
    · rw [h_eq] at ht; exact ht.2
  · intro t ht
    rw [Set.Finite.mem_toFinset] at ht; exact ht.2
  · intro t ht h_eq
    rw [Set.Finite.mem_toFinset]; exact ⟨ht, h_eq⟩

/-- **Canonical one-sided derivative limits at a `Finset` of crossings.**

For a closed `ClosedPwC1Immersion γ` and a `Finset` of crossings in `Ioo 0 1`,
produce the canonical one-sided derivative limit functions
`L_+ t, L_- t : ℝ → ℂ` plus the four spec predicates needed by the corner-form
CPV API (nonvanishing and right/left `Tendsto` of `deriv γ`):

* at corners (`t ∈ partition`), `L_± t = Classical.choose (right/left_deriv_limit t)`,
* at smooth crossings, `L_± t = deriv γ t`.

Returned as an `Exists` bundle so the caller can `obtain` all six pieces in one
step. -/
theorem canonical_derivLimits_at_crossings_exists
    (γ : ClosedPwC1Immersion x) {crossings : Finset ℝ}
    (h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ L_plus L_minus : ℝ → ℂ,
      (∀ t ∈ crossings,
        L_plus t = if h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition then
          Classical.choose (γ.toPwC1Immersion.right_deriv_limit t h_part)
        else deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t) ∧
      (∀ t ∈ crossings,
        L_minus t = if h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition then
          Classical.choose (γ.toPwC1Immersion.left_deriv_limit t h_part)
        else deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t) ∧
      (∀ t ∈ crossings, L_plus t ≠ 0) ∧
      (∀ t ∈ crossings, L_minus t ≠ 0) ∧
      (∀ t ∈ crossings,
        Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
          (𝓝[>] t) (𝓝 (L_plus t))) ∧
      (∀ t ∈ crossings,
        Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
          (𝓝[<] t) (𝓝 (L_minus t))) := by
  refine ⟨fun t ↦
    if h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition then
      Classical.choose (γ.toPwC1Immersion.right_deriv_limit t h_part)
    else deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t,
    fun t ↦
    if h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition then
      Classical.choose (γ.toPwC1Immersion.left_deriv_limit t h_part)
    else deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t,
    fun _ _ ↦ rfl, fun _ _ ↦ rfl, ?_, ?_, ?_, ?_⟩
  · intro t ht
    by_cases h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
    · simpa [dif_pos h_part] using
        (Classical.choose_spec (γ.toPwC1Immersion.right_deriv_limit t h_part)).1
    · simpa [dif_neg h_part] using
        (deriv_limit_eq_at_off_partition γ (h_Ioo t ht) h_part).1
  · intro t ht
    by_cases h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
    · simpa [dif_pos h_part] using
        (Classical.choose_spec (γ.toPwC1Immersion.left_deriv_limit t h_part)).1
    · simpa [dif_neg h_part] using
        (deriv_limit_eq_at_off_partition γ (h_Ioo t ht) h_part).1
  · intro t ht
    by_cases h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
    · simpa [dif_pos h_part] using
        (Classical.choose_spec (γ.toPwC1Immersion.right_deriv_limit t h_part)).2
    · simpa [dif_neg h_part] using
        (deriv_limit_eq_at_off_partition γ (h_Ioo t ht) h_part).2.1
  · intro t ht
    by_cases h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
    · simpa [dif_pos h_part] using
        (Classical.choose_spec (γ.toPwC1Immersion.left_deriv_limit t h_part)).2
    · simpa [dif_neg h_part] using
        (deriv_limit_eq_at_off_partition γ (h_Ioo t ht) h_part).2.2

/-- **Condition (B) bridged to the corner-form `h_B` predicate at all crossings.**

Given condition (B), a polar-part decomposition, and a `Finset` of crossing
parameters `crossings ⊆ Ioo 0 1` all hitting the same pole `s`, package the
condition-(B) angle equation as the corner-form `h_B` predicate
`(L_+/‖L_+‖)^k = ((-L_-)/‖L_-‖)^k`, where `L_±` are the canonical one-sided
derivative limits (`Classical.choose` of `right_deriv_limit`/`left_deriv_limit`
at corners, `deriv γ t` at smooth crossings).

The dispatching `corner_angle_compat_to_h_B` / `h_B_of_angle_compat_smooth`
discharge is performed internally.  This is the unified discharge consumed by
`cpv_polarPart_at_multiCrossed_pole_under_condB_corner` inside
`residueTheorem_crossing_paper_faithful_clean`. -/
theorem condB_to_h_B_at_crossings_corner
    {U : Set ℂ} {S : Finset ℂ} {f : ℂ → ℂ} (hU_open : IsOpen U) (hS_in_U : ↑S ⊆ U)
    (γ : ClosedPwC1Immersion x)
    (decomp : PolarPartDecomposition f S U)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    {s : ℂ} (hs : s ∈ S)
    {crossings : Finset ℝ}
    (h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : ∀ t ∈ crossings, γ.toPwC1Immersion.toPiecewiseC1Path t = s)
    (L_plus L_minus : ℝ → ℂ)
    (hL_plus_def : ∀ t ∈ crossings,
      L_plus t = if h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition then
        Classical.choose (γ.toPwC1Immersion.right_deriv_limit t h_part)
      else deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
    (hL_minus_def : ∀ t ∈ crossings,
      L_minus t = if h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition then
        Classical.choose (γ.toPwC1Immersion.left_deriv_limit t h_part)
      else deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
    (hL_plus_ne : ∀ t ∈ crossings, L_plus t ≠ 0)
    (hL_minus_ne : ∀ t ∈ crossings, L_minus t ≠ 0) :
    ∀ (k : Fin (decomp.order s)), 1 ≤ k.val →
      decomp.coeff s k ≠ 0 → ∀ t ∈ crossings,
        (L_plus t / (↑‖L_plus t‖ : ℂ)) ^ k.val =
        ((-(L_minus t)) / (↑‖L_minus t‖ : ℂ)) ^ k.val := by
  intro k hk_ge h_coeff_ne t ht
  have ht_Ioo : t ∈ Set.Ioo (0 : ℝ) 1 := h_Ioo t ht
  have h_at_t : γ.toPwC1Immersion.toPiecewiseC1Path t = s := h_at t ht
  have hk_two : 2 ≤ k.val + 1 := by omega
  have h_kval_eq : k.val + 1 - 1 = k.val := by omega
  by_cases h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
  · have hL_plus_eq : L_plus t =
        Classical.choose (γ.toPwC1Immersion.right_deriv_limit t h_part) := by
      rw [hL_plus_def t ht, dif_pos h_part]
    have hL_minus_eq : L_minus t =
        Classical.choose (γ.toPwC1Immersion.left_deriv_limit t h_part) := by
      rw [hL_minus_def t ht, dif_pos h_part]
    have h_angle_pwr : ∃ m : ℤ,
        (((k.val + 1) - 1 : ℕ) : ℝ) *
          angleAtCrossing γ.toPwC1Immersion t ht_Ioo =
        (m : ℝ) * (2 * Real.pi) := by
      rw [show ((k.val + 1) - 1 : ℕ) = k.val from by omega]
      exact angle_compat_of_condB_anywhere hU_open hS_in_U γ
        decomp hCondB hs ht_Ioo h_at_t k hk_ge h_coeff_ne
    have h_result := corner_angle_compat_to_h_B γ ht_Ioo h_part (hL_minus_ne t ht)
      (hL_plus_ne t ht) hL_minus_eq hL_plus_eq hk_two h_angle_pwr
    rw [h_kval_eq] at h_result
    exact h_result
  · have h_L_eq := deriv_limit_eq_at_off_partition γ ht_Ioo h_part
    have hL_plus_unfold : L_plus t =
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t := by
      rw [hL_plus_def t ht, dif_neg h_part]
    have hL_minus_unfold : L_minus t =
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t := by
      rw [hL_minus_def t ht, dif_neg h_part]
    rw [hL_plus_unfold, hL_minus_unfold]
    have h_angle_pwr : ∃ m : ℤ,
        (((k.val + 1) - 1 : ℕ) : ℝ) * Real.pi =
        (m : ℝ) * (2 * Real.pi) := by
      rw [show ((k.val + 1) - 1 : ℕ) = k.val from by omega]
      exact angle_compat_of_condB hU_open hS_in_U γ decomp
        hCondB hs ht_Ioo h_at_t h_part k hk_ge h_coeff_ne
    have h_result := h_B_of_angle_compat_smooth
      (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
      h_L_eq.1 (k.val + 1) hk_two h_angle_pwr
    rw [h_kval_eq] at h_result
    exact h_result

end HungerbuhlerWasem

end
