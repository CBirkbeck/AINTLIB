/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Topology.Connected.Clopen

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
