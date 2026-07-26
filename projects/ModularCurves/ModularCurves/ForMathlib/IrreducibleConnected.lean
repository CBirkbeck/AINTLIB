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

/-- The union of an **open** irreducible set with any irreducible set meeting it is
irreducible. (Openness is essential: two intersecting irreducible *closed* sets can have a
reducible union.) -/
theorem IsIrreducible.union_of_isOpen_of_inter_nonempty {U Z : Set X}
    (hU : IsIrreducible U) (hUo : IsOpen U) (hZ : IsIrreducible Z)
    (hne : (U ∩ Z).Nonempty) : IsIrreducible (U ∪ Z) := by
  refine ⟨hU.1.mono Set.subset_union_left, fun a b ha hb hUa hUb => ?_⟩
  -- `Z` meets `U`, so any open meeting `Z` meets `Z ∩ U`
  have key : ∀ c : Set X, IsOpen c → ((U ∪ Z) ∩ c).Nonempty → (U ∩ c).Nonempty := by
    intro c hc hcne
    obtain ⟨w, hw, hwc⟩ := hcne
    rcases hw with hwU | hwZ
    · exact ⟨w, hwU, hwc⟩
    · obtain ⟨z, hz, hzU, hzc⟩ := hZ.2 U c hUo hc
        (by obtain ⟨v, hvU, hvZ⟩ := hne; exact ⟨v, hvZ, hvU⟩) ⟨w, hwZ, hwc⟩
      exact ⟨z, hzU, hzc⟩
  obtain ⟨z, hz, hzab⟩ := hU.2 a b ha hb (key a ha hUa) (key b hb hUb)
  exact ⟨z, Or.inl hz, hzab⟩

/-- **(T-G4a, the local-to-global step)** A nonempty connected space in which **every point
has an irreducible open neighbourhood** is irreducible.

The irreducible component through a point then *contains* every such neighbourhood (by
maximality, using `IsIrreducible.union_of_isOpen_of_inter_nonempty`), so components are
open; being also closed and nonempty, connectedness forces a single one. -/
theorem irreducibleSpace_of_connected_of_locallyIrreducible [Nonempty X] [ConnectedSpace X]
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsIrreducible U) : IrreducibleSpace X := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hopen : IsOpen (irreducibleComponent x) := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨U, hUo, hyU, hUirr⟩ := h y
    have hunion : IsIrreducible (U ∪ irreducibleComponent x) :=
      hUirr.union_of_isOpen_of_inter_nonempty hUo isIrreducible_irreducibleComponent
        ⟨y, hyU, hy⟩
    have heq : U ∪ irreducibleComponent x = irreducibleComponent x :=
      eq_irreducibleComponent hunion.2 Set.subset_union_right
    exact ⟨U, heq ▸ Set.subset_union_left, hUo, hyU⟩
  have hclopen : IsClopen (irreducibleComponent x) := ⟨isClosed_irreducibleComponent, hopen⟩
  have huniv : irreducibleComponent x = Set.univ :=
    hclopen.eq_univ ⟨x, mem_irreducibleComponent⟩
  exact { isPreirreducible_univ := huniv ▸ isIrreducible_irreducibleComponent.2
          toNonempty := ⟨x⟩ }

