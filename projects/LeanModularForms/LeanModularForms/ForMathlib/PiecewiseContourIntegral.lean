/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LeanModularForms.ForMathlib.PiecewiseC1Path

/-!
# Contour Integration along Piecewise C¹ Paths

This file defines the contour integral of a complex-valued function along a piecewise C¹
path and proves basic properties including linearity and the fundamental theorem of calculus.

## Main definitions

* `PiecewiseC1Path.contourIntegral f γ` — the contour integral `∫₀¹ f(γ(t)) · γ'(t) dt`

## Main results

* `contourIntegral_add` — `∮_γ (f + g) = ∮_γ f + ∮_γ g` (under integrability)
* `contourIntegral_smul` — `∮_γ (c • f) = c • ∮_γ f`
* `contourIntegral_eq_sub_of_hasDerivAt` — if `F' = f` along the path, then
  `∮_γ f dz = F(y) - F(x)` (FTC telescope)

## Design notes

The contour integral is defined using mathlib's `intervalIntegral` over `[0, 1]`. The path
`γ : PiecewiseC1Path x y` is coerced to `ℝ → ℂ` via `Path.extend`, and the integrand is
`f(γ(t)) * deriv γ.toPath.extend t`.

The FTC telescope works by induction on the number of partition points between sub-interval
endpoints. On each smooth segment, standard FTC applies; adjacent segments telescope because
`F(γ(t_{i+1})) - F(γ(t_i))` cancels with the next segment's `F(γ(t_{i+1}))` term.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set MeasureTheory Filter Topology
open scoped Interval

noncomputable section

variable {x y : ℂ}

namespace PiecewiseC1Path

/-- The contour integral of `f` along a piecewise C¹ path `γ`:
`∮_γ f(z) dz = ∫ t in 0..1, f(γ(t)) · γ'(t) dt`. -/
def contourIntegral (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) : ℂ :=
  ∫ t in (0 : ℝ)..1, f (γ t) * deriv γ.toPath.extend t

/-- The integrand of the contour integral. -/
def contourIntegrand (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (t : ℝ) : ℂ :=
  f (γ t) * deriv γ.toPath.extend t

/-- Addition: `∮_γ (f + g) = ∮_γ f + ∮_γ g` when both integrands are integrable. -/
theorem contourIntegral_add (f g : ℂ → ℂ) (γ : PiecewiseC1Path x y)
    (hf : IntervalIntegrable (contourIntegrand f γ) volume 0 1)
    (hg : IntervalIntegrable (contourIntegrand g γ) volume 0 1) :
    contourIntegral (fun z => f z + g z) γ =
      contourIntegral f γ + contourIntegral g γ := by
  simp only [contourIntegral, add_mul]
  exact intervalIntegral.integral_add hf hg

/-- Scalar multiplication: `∮_γ (c • f) = c • ∮_γ f`. -/
theorem contourIntegral_smul (c : ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) :
    contourIntegral (fun z => c * f z) γ = c * contourIntegral f γ := by
  simp only [contourIntegral, mul_assoc]
  exact intervalIntegral.integral_const_mul c _

/-- The contour integral of the zero function is zero. -/
theorem contourIntegral_zero (γ : PiecewiseC1Path x y) :
    contourIntegral (fun _ => 0) γ = 0 := by
  simp [contourIntegral]

/-- **Finset sum linearity for contour integrals.** When each integrand
`contourIntegrand (f i) γ` is interval-integrable on `[0, 1]`,
`∮_γ (∑ i ∈ ι, f i z) = ∑ i ∈ ι, ∮_γ f i z`. -/
theorem contourIntegral_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℂ → ℂ) (γ : PiecewiseC1Path x y)
    (hf : ∀ i ∈ s, IntervalIntegrable (contourIntegrand (f i) γ) volume 0 1) :
    contourIntegral (fun z => ∑ i ∈ s, f i z) γ =
      ∑ i ∈ s, contourIntegral (f i) γ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [contourIntegral_zero]
  | @insert j t hi ih =>
    have h_t : ∀ i ∈ t, IntervalIntegrable (contourIntegrand (f i) γ) volume 0 1 :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h_t_int : IntervalIntegrable
        (contourIntegrand (fun z => ∑ i ∈ t, f i z) γ) volume 0 1 := by
      refine (IntervalIntegrable.sum t h_t).congr fun u _ => ?_
      simp [contourIntegrand, Finset.sum_mul]
    rw [Finset.sum_insert hi,
        funext (fun z => Finset.sum_insert hi (s := t) (a := j) (f := fun i => f i z)),
        contourIntegral_add (f j) _ γ (hf j (Finset.mem_insert_self _ _)) h_t_int,
        ih h_t]

private lemma ftc_no_partition {F f : ℂ → ℂ} (γ : PiecewiseC1Path x y)
    (a' b' : ℝ) (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc 0 1)
    (hFγ_cont : ContinuousOn (F ∘ γ.toPath.extend) (Icc 0 1))
    (hFγ_deriv : ∀ t ∈ Ioo 0 1, t ∉ γ.partition →
      HasDerivAt (F ∘ γ.toPath.extend) (f (γ t) * deriv γ.toPath.extend t) t)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (hempty : γ.partition.filter (fun t => a' < t ∧ t < b') = ∅) :
    ∫ t in a'..b', f (γ t) * deriv γ.toPath.extend t =
      F (γ b') - F (γ a') := by
  have ha'_bds := hsub (left_mem_Icc.mpr ha'b')
  have hb'_bds := hsub (right_mem_Icc.mpr ha'b')
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha'b' (hFγ_cont.mono hsub)
    (fun t ht => hFγ_deriv t ⟨ha'_bds.1.trans_lt ht.1, ht.2.trans_le hb'_bds.2⟩ fun ht_P =>
      Finset.notMem_empty t (hempty ▸ Finset.mem_filter.mpr ⟨ht_P, ht.1, ht.2⟩))
    (h_int.mono_set <| uIcc_subset_uIcc
      (mem_uIcc_of_le ha'_bds.1 ha'_bds.2)
      (mem_uIcc_of_le hb'_bds.1 hb'_bds.2))

private lemma partition_filter_card_lt_left (P : Finset ℝ) {a' b' c : ℝ}
    (hc_part : c ∈ P) (hac : a' < c) (hcb : c < b') :
    (P.filter (fun t => a' < t ∧ t < c)).card <
      (P.filter (fun t => a' < t ∧ t < b')).card := by
  refine Finset.card_lt_card ⟨fun t ht => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1, ht.2.2.trans hcb⟩
  · have hcmem := hsub (Finset.mem_filter.mpr ⟨hc_part, hac, hcb⟩)
    simp only [Finset.mem_filter] at hcmem
    exact lt_irrefl c hcmem.2.2

private lemma partition_filter_card_lt_right (P : Finset ℝ) {a' b' c : ℝ}
    (hc_part : c ∈ P) (hac : a' < c) (hcb : c < b') :
    (P.filter (fun t => c < t ∧ t < b')).card <
      (P.filter (fun t => a' < t ∧ t < b')).card := by
  refine Finset.card_lt_card ⟨fun t ht => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, hac.trans ht.2.1, ht.2.2⟩
  · have hcmem := hsub (Finset.mem_filter.mpr ⟨hc_part, hac, hcb⟩)
    simp only [Finset.mem_filter] at hcmem
    exact lt_irrefl c hcmem.2.1

private lemma integrability_split {f : ℂ → ℂ} (γ : PiecewiseC1Path x y)
    {a' b' c : ℝ} (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc 0 1)
    (hc_bds : c ∈ Icc 0 1)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    IntervalIntegrable (fun t => f (γ t) * deriv γ.toPath.extend t) volume a' c ∧
    IntervalIntegrable (fun t => f (γ t) * deriv γ.toPath.extend t) volume c b' :=
  let ha := hsub (left_mem_Icc.mpr ha'b')
  let hb := hsub (right_mem_Icc.mpr ha'b')
  let hc := mem_uIcc_of_le hc_bds.1 hc_bds.2
  ⟨h_int.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le ha.1 ha.2) hc),
   h_int.mono_set (uIcc_subset_uIcc hc (mem_uIcc_of_le hb.1 hb.2))⟩

private lemma ftc_induction {F f : ℂ → ℂ} (γ : PiecewiseC1Path x y)
    (n : ℕ) (a' b' : ℝ)
    (hFγ_cont : ContinuousOn (F ∘ γ.toPath.extend) (Icc 0 1))
    (hFγ_deriv : ∀ t ∈ Ioo 0 1, t ∉ γ.partition →
      HasDerivAt (F ∘ γ.toPath.extend) (f (γ t) * deriv γ.toPath.extend t) t)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (hcard : (γ.partition.filter (fun t => a' < t ∧ t < b')).card ≤ n)
    (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc 0 1) :
    ∫ t in a'..b', f (γ t) * deriv γ.toPath.extend t =
      F (γ b') - F (γ a') := by
  induction n generalizing a' b' with
  | zero =>
    exact ftc_no_partition γ a' b' ha'b' hsub hFγ_cont hFγ_deriv h_int
      (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  | succ m ih =>
    by_cases hempty : γ.partition.filter (fun t => a' < t ∧ t < b') = ∅
    · exact ftc_no_partition γ a' b' ha'b' hsub hFγ_cont hFγ_deriv h_int hempty
    · obtain ⟨c, hc_filt⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      simp only [Finset.mem_filter] at hc_filt
      obtain ⟨hcP, hac, hcb⟩ := hc_filt
      have hc_bds : c ∈ Icc 0 1 := hsub ⟨hac.le, hcb.le⟩
      obtain ⟨h_int_ac, h_int_cb⟩ := integrability_split γ ha'b' hsub hc_bds h_int
      have hcard_ac : (γ.partition.filter (fun t => a' < t ∧ t < c)).card ≤ m := by
        have := partition_filter_card_lt_left γ.partition hcP hac hcb; omega
      have hcard_cb : (γ.partition.filter (fun t => c < t ∧ t < b')).card ≤ m := by
        have := partition_filter_card_lt_right γ.partition hcP hac hcb; omega
      have h_ac := ih a' c hcard_ac hac.le
        (fun t ht => hsub ⟨ht.1, ht.2.trans hcb.le⟩)
      have h_cb := ih c b' hcard_cb hcb.le
        (fun t ht => hsub ⟨hac.le.trans ht.1, ht.2⟩)
      rw [← intervalIntegral.integral_add_adjacent_intervals h_int_ac h_int_cb,
          h_ac, h_cb]
      ring

/-- **Fundamental theorem of calculus for piecewise C¹ contour integrals.**

If `F` is a holomorphic primitive of `f` on a set `U` containing the image of `γ`,
then `∮_γ f(z) dz = F(y) - F(x)`.

The proof splits the integral at partition points and applies FTC on each smooth
segment; adjacent segments telescope. -/
theorem contourIntegral_eq_sub_of_hasDerivAt {F f : ℂ → ℂ}
    (γ : PiecewiseC1Path x y) {U : Set ℂ}
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    contourIntegral f γ = F y - F x := by
  unfold contourIntegral
  have hFγ_cont : ContinuousOn (F ∘ γ.toPath.extend) (Icc 0 1) :=
    .comp (fun z hz => (hF z hz).continuousAt.continuousWithinAt)
      γ.toPath.continuous_extend.continuousOn hU
  have hFγ_deriv : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ γ.partition →
      HasDerivAt (F ∘ γ.toPath.extend) (f (γ t) * deriv γ.toPath.extend t) t :=
    fun t ht htp =>
      (hF (γ t) (hU t (Ioo_subset_Icc_self ht))).comp_of_eq t
        (γ.differentiable_off_extend t ht htp).hasDerivAt rfl
  have h := ftc_induction γ _ 0 1 hFγ_cont hFγ_deriv h_int le_rfl zero_le_one subset_rfl
  rwa [γ.apply_one, γ.apply_zero] at h

/-- **FTC for closed piecewise C¹ paths.** If `F' = f` along a closed path, then `∮_γ f = 0`. -/
theorem contourIntegral_eq_zero_of_hasDerivAt_of_closed {F f : ℂ → ℂ}
    (γ : PiecewiseC1Path x y) (hclosed : x = y) {U : Set ℂ}
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    contourIntegral f γ = 0 := by
  rw [contourIntegral_eq_sub_of_hasDerivAt γ hU hF h_int, hclosed, sub_self]

end PiecewiseC1Path

end
