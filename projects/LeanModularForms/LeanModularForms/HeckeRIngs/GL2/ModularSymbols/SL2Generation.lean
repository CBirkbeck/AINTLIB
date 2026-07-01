/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.GroupTheory.Schreier
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# `SL(2, ℤ)` is finitely generated

This file records that the modular group `SL(2, ℤ) = Matrix.SpecialLinearGroup (Fin 2) ℤ` is
finitely generated as a group, and notes the downstream consequence that each congruence subgroup
`Γ₁(N)` is finitely generated.

## Main results

* `Matrix.SpecialLinearGroup.instGroupFG` : `Group.FG SL(2, ℤ)`.

The proof is immediate from the classical generation lemma
`SpecialLinearGroup.SL2Z_generators : Subgroup.closure {S, T} = ⊤` (in
`Mathlib.LinearAlgebra.Matrix.FixedDetMatrices`), since the generating set `{S, T}` is finite.

## Downstream

Combined with the mathlib Schreier instance
`Subgroup.fg_of_index_ne_zero [Group.FG G] [H.FiniteIndex] : Group.FG H` and the finite-index
instance `CongruenceSubgroup.instFiniteIndexGamma1 [NeZero N]`, typeclass inference resolves
`Group.FG (CongruenceSubgroup.Gamma1 N)` for any `[NeZero N]` automatically (no helper instance is
required). This is needed for a downstream leaf that generates `Div⁰(ℙ¹ℚ)` over `ℤ[Γ₁N]`.
-/

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

/-- `SL(2, ℤ)` is finitely generated, by `S = ![![0, -1], ![1, 0]]` and `T = ![![1, 1], ![0, 1]]`.
This is immediate from `SpecialLinearGroup.SL2Z_generators` (the classical fact that `S` and `T`
generate `SL(2, ℤ)`) together with the finiteness of the two-element generating set. -/
instance instGroupFG : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
    SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

end Matrix.SpecialLinearGroup
