/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import LeanModularForms.ForMathlib.PiecewiseContourIntegral

/-!
# Segment FTC and Log-Derivative

FTC (fundamental theorem of calculus) variants for contour integration on segments,
and log-derivative FTC. These are the building blocks for computing integrals of
`f'/f` along piecewise paths, where the primitive is `log ∘ f`.

## Main results

### Telescoping FTC for log-derivatives

* `ftc_telescope_two` — FTC on two consecutive segments telescopes
* `ftc_telescope_three` — FTC on three consecutive segments telescopes
* `ftc_telescope_closed_split` — for closed curves, the full integral telescopes
  to the log difference at the crossing boundary
* `ftc_telescope_integrability` — transfer integrability via a.e. agreement
* `ftc_telescope_transfer` — transfer both integrability and FTC via a.e. agreement
* `ftc_telescope_piecewise_two` — piecewise FTC with two local comparison functions
* `ftc_telescope_piecewise_three` — piecewise FTC with three local comparison functions

### Log-derivative FTC on segments

* `intervalIntegrable_logDeriv_of_slitPlane` — integrability when `f` stays in slitPlane
* `integral_logDeriv_eq_log_sub` — `∫ f'/f = log f(b) - log f(a)` in slitPlane
* `ftc_log_on_segment` — combined integrability + FTC for a single C^1 function
* `ftc_log_neg_on_segment` — same when `-f` stays in slitPlane
* `integral_logDeriv_eq_neg_log_sub` — bare FTC when `-f` stays in slitPlane
* `ftc_log_pieceFM` — combined integrability + FTC when `f` and `g` agree a.e.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set MeasureTheory Complex
open scoped Interval

namespace SegmentFTC

/-- Transfer integrability from a local function `h` to `g` given that their
log-derivatives agree almost everywhere on the interval. -/
theorem ftc_telescope_integrability {g h : ℝ → ℂ} {a b : ℝ}
    (hint_h : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b)
    (h_ae : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b :=
  hint_h.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
    (h_ae.mono (fun _t ht hm ↦ (ht hm).symm)))

/-- Transfer an FTC result from a local function `h` to `g` given that their
log-derivatives agree a.e. and their values agree at the endpoints.
Produces both integrability and the FTC equality for `g`. -/
theorem ftc_telescope_transfer {g h : ℝ → ℂ} {a b : ℝ}
    (hint_h : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b)
    (h_ftc : ∫ t in a..b, deriv h t / h t = Complex.log (h b) - Complex.log (h a))
    (h_ae : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t)
    (h_ga : g a = h a) (h_gb : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) :=
  ⟨ftc_telescope_integrability hint_h h_ae, by
    rw [intervalIntegral.integral_congr_ae (h_ae.mono (fun _ ↦ id)), h_ftc, h_ga, h_gb]⟩

end SegmentFTC

namespace LogDerivFTC

/-- If `f : ℝ → ℂ` is C^1 on `[a,b]` with `f(t) ∈ slitPlane` for all `t ∈ [a,b]`,
then the log-derivative `t ↦ deriv f t / f t` is interval integrable on `[a,b]`. -/
theorem intervalIntegrable_logDeriv_of_slitPlane {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, f t ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t ↦ deriv f t / f t) volume a b :=
  ((hf_deriv_cont.div hf_cont
      fun t ht ↦ Complex.slitPlane_ne_zero (hf_slit t ht)).mono
    (uIcc_of_le hab ▸ Subset.rfl)).intervalIntegrable

/-- Fundamental theorem of calculus for log-derivative integrals:
If `f : ℝ → ℂ` is differentiable on `(a,b)` with derivative continuous on `[a,b]`,
and `f(t) ∈ slitPlane` for all `t ∈ [a,b]`, then
`∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a)`. -/
theorem integral_logDeriv_eq_log_sub {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, f t ∈ Complex.slitPlane) :
    ∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (ContinuousOn.clog hf_cont hf_slit)
    (fun t ht ↦ (hf_diff t ht).hasDerivAt.clog_real (hf_slit t (Ioo_subset_Icc_self ht)))
    (intervalIntegrable_logDeriv_of_slitPlane hab hf_cont hf_deriv_cont hf_slit)

/-- Combined integrability and FTC for a single C^1 function staying in slitPlane.

Returns both `IntervalIntegrable (f'/f)` and `∫ f'/f = log(f(b)) - log(f(a))`. -/
theorem ftc_log_on_segment {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, f t ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t ↦ deriv f t / f t) volume a b ∧
    ∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a) :=
  ⟨intervalIntegrable_logDeriv_of_slitPlane hab hf_cont hf_deriv_cont hf_slit,
   integral_logDeriv_eq_log_sub hab hf_cont hf_diff hf_deriv_cont hf_slit⟩

/-- Combined integrability and FTC when `-f` stays in slitPlane.

Returns both `IntervalIntegrable (f'/f)` and `∫ f'/f = log(-f(b)) - log(-f(a))`. -/
theorem ftc_log_neg_on_segment {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, -(f t) ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t ↦ deriv f t / f t) volume a b ∧
    ∫ t in a..b, deriv f t / f t =
      Complex.log (-(f b)) - Complex.log (-(f a)) := by
  have hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt (fun t ↦ Complex.log (-(f t)))
      (deriv f x / f x) x := fun x hx ↦ by
    convert (hf_diff x hx).hasDerivAt.neg.clog_real (hf_slit x (Ioo_subset_Icc_self hx)) using 1
    · funext t
      rw [Pi.neg_apply]
    · exact (neg_div_neg_eq (deriv f x) (f x)).symm
  have hint : IntervalIntegrable (fun t ↦ deriv f t / f t) volume a b :=
    (Set.uIcc_of_le hab ▸ hf_deriv_cont.div hf_cont
      fun t ht ↦ neg_ne_zero.mp (Complex.slitPlane_ne_zero (hf_slit t ht))).intervalIntegrable
  exact ⟨hint, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hf_cont.neg.clog hf_slit) hF_deriv hint⟩

/-- Combined integrability and FTC for log-derivative integrals.

Given a "reference" function `h` (C^1 with values in slitPlane) and a function `g`
that agrees with `h` on `(a,b)` up to a null set (with matching endpoint values),
both `∫ g'/g` and `∫ h'/h` are interval integrable and equal
`Complex.log(g b) - Complex.log(g a)`. -/
theorem ftc_log_pieceFM {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b))
    (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_slit : ∀ t ∈ Icc a b, h t ∈ Complex.slitPlane)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  obtain ⟨hint_h, h_ftc⟩ := ftc_log_on_segment hab hh_cont hh_diff hh_deriv_cont hh_slit
  refine SegmentFTC.ftc_telescope_transfer hint_h h_ftc ?_ heq_a heq_b
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton b)] with t ht_ne_b ht_mem
  rw [uIoc_of_le hab] at ht_mem
  obtain ⟨hval, hderiv⟩ := heq t ⟨ht_mem.1,
    lt_of_le_of_ne ht_mem.2 (Set.mem_compl_singleton_iff.mp ht_ne_b)⟩
  rw [hval, hderiv]

end LogDerivFTC
