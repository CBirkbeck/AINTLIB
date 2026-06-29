/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.GroupTheory.Commensurable
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# The commensurability class of a subgroup as a directed index

Fix a subgroup `Γ₀ ≤ GL₂(ℝ)` and a predicate `P` on subgroups that is closed under intersection and
conjugation (`Subgroup.IsConjInfClosed`). This file packages the subgroups commensurable with `Γ₀`
that satisfy `P` as a **directed index type** `ModularForm.CommIndex Γ₀ P`, ordered by *reverse*
inclusion (`i ≤ j ↔ j.carrier ≤ i.carrier`).

The predicate `P` selects a conjugation-stable sub-family of the commensurability class. The two
instances of interest are `P = fun _ => True` (the whole class — used for the `ℝ`-vector-space direct
limit) and `P = fun Γ => Γ.HasDetOne` (the determinant-one subgroups — used for the `ℂ`-vector-space
direct limit); see `CommensurableLimit/DirectLimit.lean`.

## Main definitions

* `Subgroup.IsConjInfClosed P` — `P` is closed under `⊓` and under conjugation.
* `ModularForm.CommIndex Γ₀ P` — a subgroup commensurable with `Γ₀` and satisfying `P`.

## Main results

* `Subgroup.HasDetOne.of_le` — `HasDetOne` is antitone: it passes to subgroups.
* `Subgroup.commensurable_inf` — the meet of two subgroups commensurable with `Γ₀` is commensurable
  with `Γ₀`.
* `Preorder`, `DecidableEq` and `IsDirected` (reverse inclusion) instances on `CommIndex Γ₀ P`,
  making it a directed index for a direct limit.
-/

open scoped MatrixGroups Pointwise

namespace Subgroup

/-- `HasDetOne` is antitone: a subgroup of a determinant-one subgroup is itself determinant-one.
(Mathlib only provides the `⊓` special cases; this is the general monotonicity.) -/
theorem HasDetOne.of_le {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    {Γ' Γ : Subgroup (GL n R)} (h : Γ' ≤ Γ) [Γ.HasDetOne] : Γ'.HasDetOne :=
  ⟨fun hg ↦ HasDetOne.det_eq (h hg)⟩

/-- The meet of two subgroups commensurable with a fixed `Γ₀` is again commensurable with `Γ₀`. -/
theorem commensurable_inf {G : Type*} [Group G] {Γ₁ Γ₂ Γ₀ : Subgroup G}
    (h₁ : Commensurable Γ₁ Γ₀) (h₂ : Commensurable Γ₂ Γ₀) :
    Commensurable (Γ₁ ⊓ Γ₂) Γ₀ := by
  refine ⟨relIndex_inf_ne_zero h₁.1 h₂.1, relIndex_ne_zero_trans (K := Γ₁) h₁.2 ?_⟩
  rw [relIndex_eq_one.mpr inf_le_left]
  exact one_ne_zero

/-- A predicate on subgroups of `GL₂(ℝ)` closed under intersection and conjugation — the data
carving a directed, conjugation-stable sub-family from a commensurability class. -/
class IsConjInfClosed (P : Subgroup (GL (Fin 2) ℝ) → Prop) : Prop where
  /-- `P` is closed under intersection. -/
  inf_mem : ∀ {Γ Γ' : Subgroup (GL (Fin 2) ℝ)}, P Γ → P Γ' → P (Γ ⊓ Γ')
  /-- `P` is closed under conjugation. -/
  conj_mem : ∀ (g : GL (Fin 2) ℝ) {Γ : Subgroup (GL (Fin 2) ℝ)}, P Γ → P (ConjAct.toConjAct g • Γ)

instance : IsConjInfClosed (fun _ ↦ True) where
  inf_mem := by intros; trivial
  conj_mem := by intros; trivial

end Subgroup

namespace ModularForm

open Subgroup

/-- Determinant-one passes to conjugates: if `Γ` has determinant one, so does any conjugate
`g • Γ` (the determinant is conjugation-invariant). -/
instance HasDetOne.conj {g : GL (Fin 2) ℝ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] :
    (ConjAct.toConjAct g • Γ).HasDetOne := by
  refine ⟨fun {x} hx ↦ ?_⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  simpa [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, map_mul, mul_comm, mul_left_comm]
    using HasDetOne.det_eq hx

/-- The determinant-one predicate, as a named conjugation- and `⊓`-closed family of subgroups of
`GL₂(ℝ)`: the predicate selecting the index of the `ℂ`-vector-space direct limit. -/
abbrev DetOnePred : Subgroup (GL (Fin 2) ℝ) → Prop := fun Γ ↦ Γ.HasDetOne

instance : IsConjInfClosed DetOnePred where
  inf_mem := by intro Γ Γ' h _; haveI := h; infer_instance
  conj_mem := by intro g Γ h; haveI := h; infer_instance

/-- Index type for the commensurability-class direct limit: a subgroup of `GL₂(ℝ)` that is
commensurable with `Γ₀` and satisfies the (conjugation- and `⊓`-closed) predicate `P`, bundled with
those facts.

Ordered by **reverse inclusion** (`i ≤ j ↔ j.carrier ≤ i.carrier`), so that the restriction maps of
the modular-form direct limit run in the direction of increasing `≤`. -/
structure CommIndex (Γ₀ : Subgroup (GL (Fin 2) ℝ)) (P : Subgroup (GL (Fin 2) ℝ) → Prop) where
  /-- the underlying subgroup -/
  carrier : Subgroup (GL (Fin 2) ℝ)
  /-- it is commensurable with the fixed base `Γ₀` -/
  commensurable : Commensurable carrier Γ₀
  /-- it satisfies the selecting predicate `P` -/
  prop : P carrier

namespace CommIndex

variable {Γ₀ : Subgroup (GL (Fin 2) ℝ)} {P : Subgroup (GL (Fin 2) ℝ) → Prop}

/-- Reverse-inclusion preorder: `i ≤ j` means `j.carrier ≤ i.carrier`. -/
instance : Preorder (CommIndex Γ₀ P) where
  le i j := j.carrier ≤ i.carrier
  le_refl i := le_refl i.carrier
  le_trans _ _ _ hij hjk := le_trans hjk hij

@[simp] lemma le_def {i j : CommIndex Γ₀ P} : i ≤ j ↔ j.carrier ≤ i.carrier := Iff.rfl

/-- `Module.DirectLimit` needs decidable equality on the index; subgroup equality is not decidable,
so we use the classical instance. -/
noncomputable instance : DecidableEq (CommIndex Γ₀ P) := Classical.decEq _

/-- The commensurability class is directed under reverse inclusion: two indices have their meet as a
common upper bound (it is commensurable with `Γ₀` and satisfies `P`). -/
instance [IsConjInfClosed P] : IsDirected (CommIndex Γ₀ P) (· ≤ ·) where
  directed i j :=
    ⟨⟨i.carrier ⊓ j.carrier, commensurable_inf i.commensurable j.commensurable,
        IsConjInfClosed.inf_mem i.prop j.prop⟩,
      le_def.mpr inf_le_left, le_def.mpr inf_le_right⟩

/-- The base `Γ₀` is itself an index whenever it satisfies `P`. -/
def base (hΓ₀ : P Γ₀) : CommIndex Γ₀ P := ⟨Γ₀, .refl Γ₀, hΓ₀⟩

/-- The carrier of a determinant-one index is itself determinant-one — the `prop` field exposed as
an instance, so that the `ℂ`-module structure on `ModularForm i.carrier k` resolves. -/
instance (i : CommIndex Γ₀ DetOnePred) : i.carrier.HasDetOne := i.prop

/-- The determinant-one index over a determinant-one base is nonempty (the base itself is an index),
as required by the directedness-gated direct-limit lemmas. -/
instance [Γ₀.HasDetOne] : Nonempty (CommIndex Γ₀ DetOnePred) := ⟨base inferInstance⟩

end CommIndex

end ModularForm
