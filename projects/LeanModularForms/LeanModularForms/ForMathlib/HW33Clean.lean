/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.MultiCrossingCPV

/-!
# HW Theorem 3.3 — final paper-faithful clean form

This file exposes the **fully discharged paper-faithful** statement of
Hungerbühler–Wasem Theorem 3.3 in its most general (multi-crossing,
higher-order meromorphic) form.

Compared to `hw_3_3_paper`, which exposes six oracle hypotheses
(`h_polar_cancel`, `h_holo_cancel`, `hI_polar`, `hI_holo`, `hPV_sing`,
`hI_sing`) plus `hMero`, this final form discharges all of them via the
ported `HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean`
machinery.

## Main result

* `hw_3_3_clean_full_mero` — the maximally general paper-faithful form,
  for higher-order meromorphic `f`, arbitrary multi-pole multi-crossing,
  and the 8 paper hypotheses (`hU_open, hU_ne, hS_in_U, hf, h_null,
  hMero, hCondA, hCondB`) plus the single structural residual
  `hx_notin_S` (basepoint off the singular set).
-/

noncomputable section

namespace LeanModularForms

open Set Complex
open scoped Real

variable {x : ℂ}

/-- **HW Theorem 3.3 — fully general, multi-crossing, meromorphic, clean form.**

The maximally general paper-faithful HW 3.3 in the project: `f` may have
**higher-order** meromorphic poles at each point of `S` and γ may cross
any subset of `S` at any number of parameters.

Hypotheses (8 paper + 1 structural):

* `hU_open, hU_ne, hS_in_U, hf, h_null, hMero, hCondA, hCondB` — the 8 paper
  hypotheses, exactly matching Hungerbühler–Wasem Theorem 3.3.
* `hx_notin_S` — basepoint off `S`. The only Lean-formalization residual:
  `ClosedPwC1Immersion x` carries a typed basepoint, while the paper's "cycle"
  formulation has no basepoint. Every practical caller satisfies it.

All cancellation, integrability, CPV-existence (at crossings AND at avoided
poles), multi-pole aggregation, polar-part decomposition, higher-order Laurent
vanishing under condition (B), and corner-crossing avoidance are discharged
internally via `HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean`.

The formal elimination of `hx_notin_S` is provided by the `cyclicShift`
infrastructure in `PaperPwC1Immersion.lean`: if `x ∈ S`, pick `τ ∈ Ioo 0 1`
with `γ(τ) ∉ S` (exists by `preimage_finite`), apply the theorem to
`γ.cyclicShift τ` whose basepoint is `γ(τ) ∉ S`, and lift back via
the corresponding invariance lemmas. -/
theorem hw_3_3_clean_full_mero
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s ↦
        (HungerbuhlerWasem.PolarPartDecomposition.ofMeromorphicWithCondB
          hU_open hS_in_U hf
          (γ := γ.toPwC1Immersion) hMero hCondB).order s))
    (hx_notin_S : x ∉ (↑S : Set ℂ)) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) :=
  HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean hU_open hU_ne
    hS_in_U hf γ h_null hMero hCondB hCondA hx_notin_S
