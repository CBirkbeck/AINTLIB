/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.NumberTheory.ModularForms.QExpansion

@[expose] public section

/-!
# Helper lemmas for `UpperHalfPlane.atImInfty`

A few utility lemmas about the filter `atImInfty` on the upper half-plane: unfolding
`Eventually` predicates, the imaginary-part tendsto, and a non-vanishing criterion from
a non-zero limit. Candidates for upstreaming to
`Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty`.
-/

open UpperHalfPlane Filter Topology ModularForm

/-- `FunLike` on raw `ℍ → ℂ`, used by the `qExpansion`-extensionality lemma when one of
the arguments is an explicit function instead of a bundled modular form. -/
instance : FunLike (ℍ → ℂ) ℍ ℂ where
  coe := fun ⦃a₁⦄ ↦ a₁
  coe_injective := fun ⦃_ _⦄ a ↦ a

/-- Two `FunLike` objects with identical underlying functions have the same period-1
q-expansion. -/
lemma qExpansion_ext2 {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ]
    (f : α) (g : β) (h : ⇑f = ⇑g) : qExpansion 1 f = qExpansion 1 g := by
  have hcf : cuspFunction 1 f = cuspFunction 1 g := congrArg (cuspFunction 1) h
  ext m
  simp [qExpansion_coeff, hcf]
