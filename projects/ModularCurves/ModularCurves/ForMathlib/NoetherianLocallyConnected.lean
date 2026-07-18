/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Noetherian spaces are locally connected

Connected components of a noetherian topological space are open: the complement of the
component of `x` is the union of the finitely many irreducible components not contained in
it, and irreducible components are closed. Consequently a noetherian space is locally
connected (connected components of open subsets are open, since opens of noetherian spaces
are noetherian).

Both facts appear to be missing from mathlib (2026-07-07); upstream candidates. Supply for
the componentwise canonicity glue (T-W7.7·C4glue): a locally noetherian scheme is locally
connected, so its connected components are clopen.

AINTLIB ModularCurves (T-W7.7 rigidity infrastructure); upstream candidate.
-/

open TopologicalSpace Set

variable {α : Type*} [TopologicalSpace α]

/-- In a noetherian space, connected components are open: the complement of the component of
`x` is the finite closed union of the irreducible components not contained in it. -/
theorem TopologicalSpace.NoetherianSpace.isOpen_connectedComponent [NoetherianSpace α]
    (x : α) : IsOpen (connectedComponent x) := by
  have hfin : (irreducibleComponents α).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcompl : connectedComponent x
      = (⋃ C ∈ {C ∈ irreducibleComponents α | ¬ C ⊆ connectedComponent x}, C)ᶜ := by
    apply Set.eq_of_subset_of_subset
    · intro y hy
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
      rintro C ⟨hCmem, hCnot⟩ hyC
      refine hCnot ?_
      have hsub : C ⊆ connectedComponent y :=
        hCmem.1.2.isPreconnected.subset_connectedComponent hyC
      exact hsub.trans (connectedComponent_eq hy).ge
    · intro y hy
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hy
      by_contra hyx
      refine hy (irreducibleComponent y)
        ⟨irreducibleComponent_mem_irreducibleComponents y, fun hsub => hyx ?_⟩
        mem_irreducibleComponent
      exact hsub mem_irreducibleComponent
  rw [hcompl, isOpen_compl_iff]
  exact (hfin.subset (fun C hC => hC.1)).isClosed_biUnion
    (fun C hC => isClosed_of_mem_irreducibleComponents C hC.1)

/-- A noetherian space is locally connected. -/
instance (priority := 100) TopologicalSpace.NoetherianSpace.toLocallyConnectedSpace
    [NoetherianSpace α] : LocallyConnectedSpace α := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro F hF x hx
  haveI : NoetherianSpace ↥F := NoetherianSpace.of_subset (subset_univ F)
  rw [connectedComponentIn_eq_image hx]
  exact hF.isOpenMap_subtype_val _ (NoetherianSpace.isOpen_connectedComponent _)
