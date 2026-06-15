/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ClassicalCPV

/-!
# `limUnder` of an eventually-constant filter

A single utility lemma used by the residue-theory chain: if `f` is eventually
equal to a constant `c` along a non-trivial filter, then `limUnder l f = c`.

The bulk of this file used to host the winding-number integrality chain
(`exp_integral_eq_endpoint_ratio*`, the `gFunc_constant_*` G-function technique,
the `exists_*_avoiding_finset` shape lemmas, and the
`logDeriv_continuous*`/`stronglyMeasurable*`/`integral_hasDerivAt_*` infrastructure).
None of that material is reachable from the protected theorems
`LeanModularForms.hw_3_3_clean_full_mero` or `valence_formula_textbook`, so it has
been removed.
-/

open Filter Topology

noncomputable section

/-- If `f` is eventually equal to a constant `c`, then `limUnder l f = c`. -/
theorem limUnder_eventually_eq_const {α : Type*} [TopologicalSpace α] {f : α → ℂ}
    {l : Filter α} {c : ℂ} [l.NeBot] (hf : ∀ᶠ x in l, f x = c) : limUnder l f = c :=
  (tendsto_const_nhds.congr' (hf.mono fun _ h => h.symm)).limUnder_eq

end
