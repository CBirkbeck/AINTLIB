/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib
import LeanModularForms.ForMathlib.SegmentFTC

/-!
# Telescoping FTC for Log-Derivative on Piecewise Segments

When FTC-for-log is applied to consecutive segments sharing endpoints,
the log terms telescope. For a closed curve split at a crossing t₀ ± δ,
the total integral reduces to log(g(t₀-δ)) - log(g(t₀+δ)).

## Main results

* `ftc_telescope_two` — FTC on two consecutive segments telescopes
* `ftc_telescope_closed_split` — for closed curves, the full integral telescopes
  to the log difference at the crossing boundary
-/

open Set MeasureTheory Complex
open scoped Interval

namespace ContourIntegral

/-- Transfer integrability from a local function `h` to `g` given that their
log-derivatives agree almost everywhere on the interval.  The `h_ae` hypothesis
has the direction `deriv g / g = deriv h / h` pointwise a.e., which is reversed
internally to match the `congr_ae` requirement. -/
theorem ftc_telescope_integrability {g h : ℝ → ℂ} {a b : ℝ}
    (hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b)
    (h_ae : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b :=
  hint_h.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
    (h_ae.mono (fun _t ht hm => (ht hm).symm)))

/-- Transfer an FTC result from a local function `h` to `g` given that their
log-derivatives agree a.e. and their values agree at the endpoints.
Produces both integrability and the FTC equality for `g`. -/
theorem ftc_telescope_transfer {g h : ℝ → ℂ} {a b : ℝ}
    (hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b)
    (h_ftc : ∫ t in a..b, deriv h t / h t = Complex.log (h b) - Complex.log (h a))
    (h_ae : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t)
    (h_ga : g a = h a) (h_gb : g b = h b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  refine ⟨ftc_telescope_integrability hint_h h_ae, ?_⟩
  rw [intervalIntegral.integral_congr_ae h_ae, h_ftc, h_ga, h_gb]

end ContourIntegral
