/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.LocalAtTarget

/-!
# Connected total space of an open–closed map with connected fibres

If `f : X → Y` is an open and closed map whose every fibre `f ⁻¹' {y}` is connected, and the
base `Y` is connected, then the total space `X` is connected.

This is the topological heart of the "rigidity along the second factor" step (GIT Cor 6.3):
a nontrivial clopen partition `s`, `sᶜ` of `X` has clopen images under `f` (open + closed
map), each of which is all of `Y` if nonempty (`Y` connected); intersecting the partition
with a single connected fibre then splits that fibre, a contradiction.

`Mathlib.Topology.Connected.CardComponents` proves the sharper *cardinality* bound
`#(ConnectedComponents X) ≤ #(f ⁻¹' {y})` for open–closed maps; the statement here is the
qualitative consequence in the case where the fibres are themselves connected (so the bound
would be vacuous). No continuity of `f` is needed.

AINTLIB ModularCurves (T-W7.7 rigidity infrastructure); upstream candidate.
-/

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- **Connected total space of an open–closed map with connected fibres.** If `f : X → Y` is
open and closed, every fibre `f ⁻¹' {y}` is connected, and `Y` is connected, then `X` is
connected. -/
theorem connectedSpace_of_isOpenMap_of_isClosedMap_of_isConnected_preimage
    (hf₁ : IsOpenMap f) (hf₂ : IsClosedMap f) [ConnectedSpace Y]
    (hfib : ∀ y, IsConnected (f ⁻¹' {y})) : ConnectedSpace X := by
  have hne : Nonempty X := ⟨(hfib (Classical.arbitrary Y)).nonempty.choose⟩
  have hpre : PreconnectedSpace X := by
    rw [preconnectedSpace_iff_clopen]
    intro s hs
    rw [or_iff_not_imp_left]
    intro hs0
    by_contra hsu
    have hsne : s.Nonempty := nonempty_iff_ne_empty.mpr hs0
    have hscne : sᶜ.Nonempty := nonempty_compl.mpr hsu
    have hclc : IsClopen sᶜ := hs.compl
    have hfs : f '' s = univ := IsClopen.eq_univ ⟨hf₂ _ hs.1, hf₁ _ hs.2⟩ (hsne.image f)
    have hfsc : f '' sᶜ = univ := IsClopen.eq_univ ⟨hf₂ _ hclc.1, hf₁ _ hclc.2⟩ (hscne.image f)
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    have h1 : (f ⁻¹' {y} ∩ s).Nonempty := by
      obtain ⟨x, hxs, hxy⟩ := hfs ▸ mem_univ y
      exact ⟨x, hxy, hxs⟩
    have h2 : (f ⁻¹' {y} ∩ sᶜ).Nonempty := by
      obtain ⟨x, hxs, hxy⟩ := hfsc ▸ mem_univ y
      exact ⟨x, hxy, hxs⟩
    have hsub : f ⁻¹' {y} ⊆ s ∪ sᶜ := by rw [union_compl_self]; exact subset_univ _
    have hsplit := (hfib y).2 s sᶜ hs.2 hclc.2 hsub h1 h2
    rw [inter_compl_self, inter_empty] at hsplit
    exact hsplit.ne_empty rfl
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

/-- Connectedness transfers up a subtype inclusion. -/
lemma isConnected_preimage_val {Z : Type*} [TopologicalSpace Z] {u A : Set Z} (hAu : A ⊆ u)
    (hA : IsConnected A) : IsConnected (Subtype.val ⁻¹' A : Set u) := by
  haveI : ConnectedSpace ↑A := isConnected_iff_connectedSpace.mp hA
  rw [show (Subtype.val ⁻¹' A : Set u) = Set.range (Set.inclusion hAu) from
    (Set.range_inclusion hAu).symm, ← Set.image_univ]
  exact isConnected_univ.image _ (continuous_inclusion hAu).continuousOn

/-- **Components of the total space of an open–closed map with connected fibres are the
fibres of the components**: `connectedComponent x = f ⁻¹' (connectedComponent (f x))`.
The `⊇` direction restricts `f` over a component and applies
`connectedSpace_of_isOpenMap_of_isClosedMap_of_isConnected_preimage`. Supply for the
componentwise canonicity glue (AINTLIB T-W7.7·C4glue); upstream candidate. -/
theorem connectedComponent_eq_preimage_connectedComponent
    (hcont : Continuous f) (hopen : IsOpenMap f) (hclosed : IsClosedMap f)
    (hfib : ∀ y, IsConnected (f ⁻¹' {y})) (x : X) :
    connectedComponent x = f ⁻¹' (connectedComponent (f x)) := by
  apply Set.eq_of_subset_of_subset
  · intro z hz
    have himg : f '' connectedComponent x ⊆ connectedComponent (f x) :=
      (isPreconnected_connectedComponent.image f
        hcont.continuousOn).subset_connectedComponent
        ⟨x, mem_connectedComponent, rfl⟩
    exact himg ⟨z, hz, rfl⟩
  · have hpre : IsConnected (f ⁻¹' connectedComponent (f x)) := by
      rw [isConnected_iff_connectedSpace]
      have hopen' : IsOpenMap ((connectedComponent (f x)).restrictPreimage f) :=
        hopen.restrictPreimage _
      have hclosed' : IsClosedMap ((connectedComponent (f x)).restrictPreimage f) :=
        hclosed.restrictPreimage _
      haveI : ConnectedSpace (connectedComponent (f x)) :=
        isConnected_iff_connectedSpace.mp isConnected_connectedComponent
      have hfib' : ∀ y : connectedComponent (f x),
          IsConnected ((connectedComponent (f x)).restrictPreimage f ⁻¹' {y}) := by
        intro y
        have hker : ((connectedComponent (f x)).restrictPreimage f ⁻¹' {y})
            = (Subtype.val ⁻¹' (f ⁻¹' {y.1}) :
                Set (f ⁻¹' connectedComponent (f x))) := by
          ext z
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.restrictPreimage,
            Subtype.ext_iff]
          rfl
        rw [hker]
        exact isConnected_preimage_val
          (fun w hw => by simp only [Set.mem_preimage] at hw ⊢; rw [hw]; exact y.2)
          (hfib y.1)
      exact connectedSpace_of_isOpenMap_of_isClosedMap_of_isConnected_preimage
        hopen' hclosed' hfib'
    exact hpre.isPreconnected.subset_connectedComponent
      (by simp only [Set.mem_preimage]; exact mem_connectedComponent)
