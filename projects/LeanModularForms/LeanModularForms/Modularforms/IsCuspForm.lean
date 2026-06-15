/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import LeanModularForms.Modularforms.AtImInfty
public import LeanModularForms.Modularforms.ForMathlib_Cusps

@[expose] public section

/-!
# Cusp forms as a submodule of modular forms (project bridge)

`Mathlib.NumberTheory.ModularForms.CuspFormSubmodule` provides the canonical
`ModularForm.IsCuspForm`, `ModularForm.cuspFormSubmodule`, and the inclusion
`CuspForm.toModularFormₗ`. This file is a thin compatibility layer that exposes
the SL-side names the project historically used, so existing call sites keep
working.
-/

open ModularForm UpperHalfPlane MatrixGroups CongruenceSubgroup

noncomputable section

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- The project's `IsCuspForm` predicate, expressed via mathlib's
`ModularForm.IsCuspForm` on the coerced GL-side subgroup. -/
def IsCuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k) : Prop :=
  ModularForm.IsCuspForm f

/-- Reconstruct a `CuspForm` from a modular form known to be a cusp form. -/
def IsCuspForm_to_CuspForm (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) : CuspForm Γ k :=
  hf.choose

/-- The `SlashInvariantForm` part of `IsCuspForm_to_CuspForm` agrees with the
underlying modular form. -/
lemma CuspForm_to_ModularForm_coe (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ModularForm Γ k)
    (hf : IsCuspForm Γ k f) :
    (IsCuspForm_to_CuspForm Γ k f hf).toSlashInvariantForm = f.toSlashInvariantForm := by
  have hg : (IsCuspForm_to_CuspForm Γ k f hf).toModularFormₗ = f := hf.choose_spec
  exact congr_arg ModularForm.toSlashInvariantForm hg
