/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Mating equivalences across adjunctions

This file identifies inverse autoequivalences across a right adjoint when
the original autoequivalences commute across the corresponding left adjoint.

The construction is adapted from Clawristotle's Apache-licensed
`EquivalencePullbackPushforwardMate.lean`.
-/

namespace CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- If autoequivalences commute with a left adjoint, then their inverse
autoequivalences commute with the corresponding right adjoint. -/
noncomputable def inverseEquivalenceCommutesWithRightAdjoint
    (EC : C ≌ C) (ED : D ≌ D)
    (L : C ⥤ D) (U : D ⥤ C)
    (adj : L ⊣ U)
    (h : EC.functor ⋙ L ≅ L ⋙ ED.functor) :
    U ⋙ EC.inverse ≅ ED.inverse ⋙ U :=
  ((EC.toAdjunction.comp adj).ofNatIsoLeft h).rightAdjointUniq
    (adj.comp ED.toAdjunction)

end

end CategoryTheory
