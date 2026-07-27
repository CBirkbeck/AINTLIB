/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.Labels.HeckeFieldArithmetic
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.HeckeFinite
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.HeckeCommute
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.PeriodInvariant
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.PeriodInjective
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.EichlerInjective
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.PeriodHecke

/-!
# Installing the live `heckeAlgℤ_finite` instance via the period route (`k ≥ 2`)

The integral Hecke algebra `HeckeRing.GL2.heckeAlgℤ N k` is module-finite over `ℤ`.  This file
installs that fact as the live `Module.Finite ℤ (heckeAlgℤ N k)` **instance**, rerouting the proof
so that the deep input depends on the *weight*:

* **`k ≥ 2`** — through the integral modular-symbol **period map**
  (`HeckeRing.GL2.ModularSymbols.heckeAlgℤ_finite_of_period`): the period map `periodMap' N k hk`
  is injective (Eichler–Shimura, `periodMap'_injective`) and intertwines the Hecke operators
  (`periodMap'_heckeEnd`) and diamond operators (`periodMap'_diamond`) with their integral
  modular-symbol counterparts, while the symbol-side generators pairwise commute (`hComm_genM`).
  The single residual analytic input on this route is the model-change identity
  `exists_pairedBoundary_fundDomain_petersson_eq` (inside `periodMap'_injective`), **not**
  `exists_HeckeStableLattice`.

* **`k < 2`** — from the lattice route `heckeAlgℤ_finite_of_lattice` (`HeckeFieldArithmetic.lean`):
  `k = 1` is the genuine Deligne–Serre input and `k ≤ 0` is trivial.  This still rests on the
  isolated `exists_HeckeStableLattice` sorry, but that sorry is now invoked **only** for `k < 2`.

The `theorem` statement `Module.Finite ℤ (heckeAlgℤ N k)` (for all `k`) is unchanged from the
former upstream instance; only the *proof* is rerouted by a case split on the weight.

The `[T004b]` eigenvalue-ring finiteness lemma `newformEigenHom_range_finite` is also placed here
(downstream of the live instance it consumes).
-/

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **(T002, `k ≥ 2`)** The integral Hecke algebra `heckeAlgℤ N k` is module-finite over `ℤ` for
weight `k ≥ 2`, via the integral modular-symbol period map with injectivity supplied by the
**Eichler-integral route** `periodMap'_injective_eichler`.  This is **axiom-clean**
(`{propext, Classical.choice, Quot.sound}`; depends on neither the Stokes-route
`interior_edges_cancel_sum` nor `exists_HeckeStableLattice`).  It is the `k ≥ 2` half of the live
instance `heckeAlgℤ_finite`; its `k < 2` sibling is `heckeAlgℤ_finite_of_lattice`.  Naming it here
(rather than inlining the period-route invocation) lets the `k ≥ 2` axiom-clean
arithmetic corollaries
downstream (e.g. `Newform.coeffField_numberField_of_two_le`) reuse it without re-pulling the `k < 2`
lattice input through the weight-case-split of the instance. -/
theorem heckeAlgℤ_finite_of_two_le (hk : 2 ≤ k) : Module.Finite ℤ (heckeAlgℤ N k) :=
  ModularSymbols.heckeAlgℤ_finite_of_period (ModularSymbols.hComm_genM N k)
    (ModularSymbols.periodMap' N k hk) (ModularSymbols.periodMap'_injective_eichler hk)
    (ModularSymbols.periodMap'_heckeEnd hk) (ModularSymbols.periodMap'_diamond hk)

/-- **(T002 / FIH — live instance)** The integral Hecke algebra `heckeAlgℤ N k` is a finite
`ℤ`-module, for every weight `k`.

The proof splits on the weight:
* `2 ≤ k`: `heckeAlgℤ_finite_of_two_le` (the integral Eichler–Shimura period route, axiom-clean —
  **not** the Stokes-route `interior_edges_cancel_sum` nor `exists_HeckeStableLattice`);
* `k < 2`: via the full-rank Hecke-stable lattice route `heckeAlgℤ_finite_of_lattice`
  (`k = 1` = Deligne–Serre, `k ≤ 0` trivial), the only branch still resting on
  `exists_HeckeStableLattice`. -/
instance heckeAlgℤ_finite (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Finite ℤ (heckeAlgℤ N k) := by
  rcases le_or_gt 2 k with hk | hk
  · exact heckeAlgℤ_finite_of_two_le hk
  · exact heckeAlgℤ_finite_of_lattice N k

/-- **[T004b]** The eigenvalue ring `O_f := (newformEigenHom f).range ⊆ ℂ` is module-finite over
`ℤ` — the surjective image of the finite `ℤ`-module `heckeAlgℤ N k`. -/
theorem newformEigenHom_range_finite (f : Newform N k) :
    Module.Finite ℤ ↥(newformEigenHom f).range :=
  Module.Finite.of_surjective
    (RingHom.rangeRestrict (newformEigenHom f)).toIntAlgHom.toLinearMap
    (RingHom.rangeRestrict_surjective _)

end HeckeRing.GL2
