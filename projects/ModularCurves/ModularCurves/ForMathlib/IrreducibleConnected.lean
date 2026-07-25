/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.LocallyFinite

/-!
# Connected + locally-irreducible ⟹ irreducible

**[T-G4a-SUB3]** If the irreducible components of a space are pairwise disjoint and
locally finite — the situation for a scheme all of whose local rings are domains — then
each component is clopen, so a nonempty connected such space is irreducible.

This is the purely topological half of "a connected smooth curve is irreducible"
(`decomposition-km10.md` §L1); the other half is that smoothness forces the components
to be disjoint (tickets T-G4a-SUB1/SUB2).
-/

open Set

variable {X : Type*} [TopologicalSpace X]

/-- If the irreducible components are locally finite and pairwise disjoint, then every
irreducible component is open (its complement is the union of the others, a locally
finite union of closed sets). -/
theorem isOpen_of_mem_irreducibleComponents_of_disjoint
    (hlf : LocallyFinite ((↑) : irreducibleComponents X → Set X))
    (hdisj : ∀ Z ∈ irreducibleComponents X, ∀ W ∈ irreducibleComponents X, Z ≠ W →
      Disjoint Z W)
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsOpen Z := by
  have hcover : ∀ x : X, ∃ W ∈ irreducibleComponents X, x ∈ W :=
    fun x => ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
      mem_irreducibleComponent⟩
  have hcompl : Zᶜ = ⋃ W : {W : Set X // W ∈ irreducibleComponents X ∧ (W : Set X) ≠ Z},
      (W : Set X) := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      obtain ⟨W, hW, hxW⟩ := hcover x
      have hWZ : W ≠ Z := by
        rintro rfl
        exact hx hxW
      exact Set.mem_iUnion.mpr ⟨⟨W, hW, hWZ⟩, hxW⟩
    · rintro x hx hxZ
      obtain ⟨⟨W, hW, hWZ⟩, hxW⟩ := Set.mem_iUnion.mp hx
      exact (hdisj W hW Z hZ hWZ).le_bot ⟨hxW, hxZ⟩
  rw [← isClosed_compl_iff, hcompl]
  have hginj : Function.Injective
      (fun W : {W : Set X // W ∈ irreducibleComponents X ∧ (W : Set X) ≠ Z} =>
        (⟨W.1, W.2.1⟩ : irreducibleComponents X)) := by
    rintro ⟨W, hW, hWZ⟩ ⟨V, hV, hVZ⟩ h
    have hWV : W = V := congrArg Subtype.val h
    subst hWV
    rfl
  refine LocallyFinite.isClosed_iUnion (hlf.comp_injective hginj) ?_
  rintro ⟨W, hW, -⟩
  exact isClosed_of_mem_irreducibleComponents W hW

/-- **[T-G4a-SUB3]** A nonempty connected space whose irreducible components are locally
finite and pairwise disjoint is irreducible. -/
theorem irreducibleSpace_of_connected_of_disjoint_irreducibleComponents
    [Nonempty X] [ConnectedSpace X]
    (hlf : LocallyFinite ((↑) : irreducibleComponents X → Set X))
    (hdisj : ∀ Z ∈ irreducibleComponents X, ∀ W ∈ irreducibleComponents X, Z ≠ W →
      Disjoint Z W) :
    IrreducibleSpace X := by
  obtain ⟨x⟩ := ‹Nonempty X›
  set Z := irreducibleComponent x with hZdef
  have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hopen : IsOpen Z :=
    isOpen_of_mem_irreducibleComponents_of_disjoint hlf hdisj hZ
  have hclosed : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hne : Z.Nonempty := ⟨x, mem_irreducibleComponent⟩
  have huniv : Z = Set.univ :=
    (isClopen_iff.mp ⟨hclosed, hopen⟩).resolve_left hne.ne_empty
  have hirr : IsIrreducible (Set.univ : Set X) := huniv ▸ isIrreducible_irreducibleComponent
  exact { toPreirreducibleSpace := ⟨hirr.2⟩, toNonempty := ⟨x⟩ }
