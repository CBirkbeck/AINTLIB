/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CauchyPrincipalValue
import LeanModularForms.ForMathlib.ClassicalCPV
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ForMathlib.FDBoundaryH
import LeanModularForms.ForMathlib.FDBoundaryPath
import LeanModularForms.ForMathlib.GeneralizedWindingNumber

/-!
# Bridge: `fdBoundaryFun` ↔ `fdBoundary_H`

This file establishes the reparametrization bridge between:
- `fdBoundaryFun H : ℝ → ℂ` parametrized on `[0, 1]` (ForMathlib chain)
- `fdBoundary_H H : ℝ → ℂ` parametrized on `[0, 5]` (old ValenceFormula chain)

The bridge is simply `u = 5*t`: `fdBoundaryFun H t = fdBoundary_H H (5*t)`.

This is used to bridge residue/modular side Tendsto results between the two
chains until the residue side is fully ported to the ForMathlib chain.

## Main results

* `hasCauchyPVOn_of_cauchyPVOn'_tendsto` — bridge the multi-point old-chain CPV
  Tendsto into a `HasCauchyPVOn` predicate on the new-chain path
* `generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber` — extract
  the old-chain winding-number value from the new chain's winding-number proof
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

/-- The ForMathlib `fdBoundaryFun` is the old-chain `fdBoundary_H` after
reparametrization `t ↦ 5t`. -/
private lemma fdBoundaryFun_eq_fdBoundary_H_scaled (H : ℝ) (t : ℝ) :
    fdBoundaryFun H t = fdBoundary_H H (5 * t) := by
  unfold fdBoundaryFun fdBoundary_H
  split_ifs <;> (try exfalso; linarith) <;> push_cast <;> ring

/-- `∫ 0..5 of F = ∫ 0..1 of (5 * F(5*t))`. Complex-multiplication form of the
linear change-of-variable identity `t ↦ 5t`, packaged as a rewrite. -/
private lemma integral_zero_to_five_eq_integral_const_mul (F : ℝ → ℂ) :
    ∫ u in (0 : ℝ)..5, F u = ∫ t in (0 : ℝ)..1, (5 : ℂ) * F (5 * t) := by
  have h5 := (intervalIntegral.smul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (f := F) 5).symm
  simp only [mul_zero, mul_one] at h5
  rw [h5, Complex.real_smul]
  push_cast
  exact (intervalIntegral.integral_const_mul (5 : ℂ) _).symm

/-- Complex-valued chain-rule identity:
`deriv (fdBoundaryFun H) t = 5 * deriv (fdBoundary_H H) (5*t)`.
Works everywhere thanks to `deriv_comp_mul_left` (which handles both the
differentiable and the non-differentiable case uniformly). -/
private lemma deriv_fdBoundaryFun_eq (H : ℝ) (t : ℝ) :
    deriv (fdBoundaryFun H) t = (5 : ℂ) * deriv (fdBoundary_H H) (5 * t) := by
  have h : deriv (fdBoundaryFun H) t = (5 : ℝ) • deriv (fdBoundary_H H) (5 * t) :=
    (funext (fdBoundaryFun_eq_fdBoundary_H_scaled H) : fdBoundaryFun H = _)
      ▸ deriv_comp_mul_left (5 : ℝ) (fdBoundary_H H) t
  rw [show (5 : ℝ) • deriv (fdBoundary_H H) (5 * t) =
    (5 : ℂ) * deriv (fdBoundary_H H) (5 * t) by rw [Complex.real_smul]; norm_num] at h
  exact h

/-- Integral of the single-point old-chain CPV integrand on `[0, 5]` equals the
integral of the new-chain `cpvIntegrand` on `[0, 1]`. -/
private lemma integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun
    (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ) (H : ℝ) :
    ∫ u in (0 : ℝ)..5,
      (if ‖fdBoundary_H H u - z₀‖ > ε then
        f (fdBoundary_H H u) * deriv (fdBoundary_H H) u else 0) =
    ∫ t in (0 : ℝ)..1, cpvIntegrand f (fdBoundaryFun H) z₀ ε t := by
  rw [integral_zero_to_five_eq_integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [cpvIntegrand, fdBoundaryFun_eq_fdBoundary_H_scaled, deriv_fdBoundaryFun_eq]
  split_ifs <;> ring


private lemma mem_Ioo_zero_one_of_uIoc {t : ℝ} (ht_ne_1 : t ∈ ({1} : Set ℝ)ᶜ)
    (ht_mem : t ∈ Ioc (0 : ℝ) 1) : t ∈ Ioo (0 : ℝ) 1 :=
  ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 fun h => ht_ne_1 (mem_singleton_iff.mpr h)⟩

/-- Helper: a path agreeing with `fdBoundaryFun H` on `Icc 0 1` is eventually
equal to `fdBoundaryFun H` in a punctured neighborhood of any interior point. -/
private lemma extend_eventuallyEq_fdBoundaryFun {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    γ.toPath.extend =ᶠ[𝓝 t] fdBoundaryFun H := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact hγ s (Ioo_subset_Icc_self hs)

/-- Replace `γ.toPath.extend` with `fdBoundaryFun H` inside `cpvIntegrandOn`. -/
private lemma integral_cpvIntegrandOn_extend_eq {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) :
    (∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t) =
      ∫ t in (0 : ℝ)..1, cpvIntegrandOn S f (fdBoundaryFun H) ε t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton 1)] with t ht_ne_1 ht_mem
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht_mem
  have ht_open : t ∈ Ioo (0 : ℝ) 1 := mem_Ioo_zero_one_of_uIoc ht_ne_1 ht_mem
  simp only [cpvIntegrandOn, hγ t (Ioo_subset_Icc_self ht_open)]
  rw [(extend_eventuallyEq_fdBoundaryFun γ hγ ht_open).symm.deriv_eq]

/-- Replace `γ.toPath.extend` with `fdBoundaryFun H` inside `cpvIntegrand`.
Derived from the multi-point version via `cpvIntegrand_eq_cpvIntegrandOn_singleton`. -/
private lemma integral_cpvIntegrand_extend_eq {H : ℝ} {z₀ : ℂ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t) (ε : ℝ) :
    (∫ t in (0 : ℝ)..1, cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t) =
      ∫ t in (0 : ℝ)..1, cpvIntegrand (fun z => (z - z₀)⁻¹) (fdBoundaryFun H) z₀ ε t := by
  simp_rw [cpvIntegrand_eq_cpvIntegrandOn_singleton]
  exact integral_cpvIntegrandOn_extend_eq γ hγ {z₀} _ ε

/-- Multi-point integral equivalence: the integral over `[0, 5]` of the
old-chain CPV integrand equals the integral over `[0, 1]` of the new-chain
`cpvIntegrandOn` integrand. -/
private lemma integral_cpvIntegrandOn_fdBoundary_H_eq_fdBoundaryFun
    (S : Finset ℂ) (f : ℂ → ℂ) (ε : ℝ) (H : ℝ) :
    ∫ u in (0 : ℝ)..5,
      (if ∃ s ∈ S, ‖fdBoundary_H H u - s‖ ≤ ε then 0
        else f (fdBoundary_H H u) * deriv (fdBoundary_H H) u) =
    ∫ t in (0 : ℝ)..1, cpvIntegrandOn S f (fdBoundaryFun H) ε t := by
  rw [integral_zero_to_five_eq_integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [cpvIntegrandOn, fdBoundaryFun_eq_fdBoundary_H_scaled, deriv_fdBoundaryFun_eq]
  split_ifs <;> ring

/-- Multi-point version: convert a Tendsto statement about the old-chain
multi-point CPV integrand on `[0, 5]` into a ForMathlib `HasCauchyPVOn`
statement on a `PiecewiseC1Path` agreeing with `fdBoundaryFun H`. -/
theorem hasCauchyPVOn_of_cauchyPVOn'_tendsto
    {H : ℝ} {S : Finset ℂ} {f : ℂ → ℂ} {L : ℂ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    (h_old : Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..5,
        if ∃ s ∈ S, ‖fdBoundary_H H t - s‖ ≤ ε then 0
          else f (fdBoundary_H H t) * deriv (fdBoundary_H H) t)
      (𝓝[>] 0) (𝓝 L)) :
    HasCauchyPVOn S f γ L :=
  h_old.congr fun ε => by
    rw [integral_cpvIntegrandOn_fdBoundary_H_eq_fdBoundaryFun S f ε H,
      ← integral_cpvIntegrandOn_extend_eq γ hγ S f ε]

/-- **Reverse bridge**: from a new-chain `HasGeneralizedWindingNumber` (with a
known value `w`), derive the old chain's `generalizedWindingNumber' = w`.

This is the per-point converter: if the new chain proves a winding number value,
the old chain's parametrization gives the same value. -/
theorem generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber
    {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z₀ w : ℂ} (h : HasGeneralizedWindingNumber γ z₀ w) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 z₀ = w := by
  have h_pv_val : cauchyPrincipalValue' (·⁻¹) (fun t => fdBoundary_H H t - z₀) 0 5 0 =
      2 * ↑Real.pi * I * w :=
    ((h.congr fun ε => by
        rw [integral_cpvIntegrand_extend_eq γ hγ ε,
          ← integral_cpvIntegrand_fdBoundary_H_eq_fdBoundaryFun
            (fun z => (z - z₀)⁻¹) z₀ ε H]).congr' (.of_forall fun _ =>
      intervalIntegral.integral_congr fun _ _ => by simp [deriv_sub_const])).limUnder_eq
  simp only [generalizedWindingNumber', h_pv_val]
  field_simp [Complex.two_pi_I_ne_zero]

end
