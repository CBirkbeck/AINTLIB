/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex, AINTLIB ModularCurves project

Adapted from Clawristotle's `CoherentCohomologyFinite.SegreExponentMatrix`.
-/
import ModularCurves.ForMathlib.SegreCoordinateAlgebra
import Mathlib.Data.Finsupp.Multiset

/-!
# Exponent matrices for Segre monomials

Exponent vectors of equal total degree are the row and column sums of a finitely
supported exponent matrix.
-/

noncomputable section

namespace MvPolynomial

private lemma exists_pairingMultiset
    {α β : Type*} (s : Multiset α) (t : Multiset β)
    (hcard : s.card = t.card) :
    ∃ u : Multiset (α × β), u.map Prod.fst = s ∧ u.map Prod.snd = t := by
  induction s using Multiset.induction_on generalizing t with
  | empty =>
      have ht : t = 0 := by
        rw [← Multiset.card_eq_zero]
        simpa using hcard.symm
      subst ht
      exact ⟨0, by simp⟩
  | cons a s ih =>
      have ht : t ≠ 0 := by
        intro ht
        subst ht
        simp at hcard
      obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero ht
      obtain ⟨t', rfl⟩ := Multiset.exists_cons_of_mem hb
      have hcard' : s.card = t'.card := by
        simpa using hcard
      obtain ⟨u, hu₁, hu₂⟩ := ih t' hcard'
      refine ⟨(a, b) ::ₘ u, ?_, ?_⟩
      · simp [hu₁]
      · simp [hu₂]

/-- Sum an exponent matrix along its second coordinate. -/
def segreRowSum
    {α β : Type*} [DecidableEq α] (e : α × β →₀ ℕ) : α →₀ ℕ :=
  e.mapDomain Prod.fst

/-- Sum an exponent matrix along its first coordinate. -/
def segreColumnSum
    {α β : Type*} [DecidableEq β] (e : α × β →₀ ℕ) : β →₀ ℕ :=
  e.mapDomain Prod.snd

/-- Equal-degree exponent vectors are the margins of an exponent matrix. -/
lemma exists_exponentMatrix
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a : α →₀ ℕ) (b : β →₀ ℕ) (hdegree : a.degree = b.degree) :
    ∃ e : α × β →₀ ℕ, segreRowSum e = a ∧ segreColumnSum e = b := by
  classical
  have hcard :
      (Finsupp.toMultiset a).card = (Finsupp.toMultiset b).card := by
    rw [Finsupp.card_toMultiset, Finsupp.card_toMultiset]
    calc
      a.sum (fun _ => id) = a.degree := by
        rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply]
        simp [Function.id_def]
      _ = b.degree := hdegree
      _ = b.sum (fun _ => id) := by
        rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply]
        simp [Function.id_def]
  obtain ⟨u, hu₁, hu₂⟩ :=
    exists_pairingMultiset (Finsupp.toMultiset a) (Finsupp.toMultiset b) hcard
  let e : α × β →₀ ℕ := Multiset.toFinsupp u
  refine ⟨e, ?_, ?_⟩
  · apply Multiset.toFinsupp.symm.injective
    change Finsupp.toMultiset (segreRowSum e) = Finsupp.toMultiset a
    rw [segreRowSum, ← Finsupp.toMultiset_map,
      Multiset.toFinsupp_toMultiset, hu₁]
  · apply Multiset.toFinsupp.symm.injective
    change Finsupp.toMultiset (segreColumnSum e) = Finsupp.toMultiset b
    rw [segreColumnSum, ← Finsupp.toMultiset_map,
      Multiset.toFinsupp_toMultiset, hu₂]

end MvPolynomial
