/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Stalk

/-!
ForMathlib (OURS, not vendored): upstream candidate.

# The function field pullback of a dominant morphism

For a dominant morphism `f : X ⟶ Y` of irreducible schemes, the generic point of `X` maps to the
generic point of `Y` (`genericPoint_eq_of_isDominant`, the dense-range generalisation of mathlib's
`genericPoint_eq_of_isOpenImmersion`), so `f`'s stalk map at the generic point is the induced
pullback on function fields `Scheme.Hom.functionFieldMap : Y.functionField ⟶ X.functionField`.

This is the scheme-morphism → function-field functoriality that mathlib currently lacks (it only
packages `germToFunctionField`), and the substrate for the finrank ↔ function-field-degree bridge
(`[N]`'s scheme fibre rank = its function-field extension degree).
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- **(dense-range generic point)** A dominant morphism of irreducible schemes carries the generic
point to the generic point. Generalises `genericPoint_eq_of_isOpenImmersion` from open immersions to
arbitrary dominant morphisms — the image of the generic point is a generic point of `closure (range f)
= univ`, hence *the* generic point of the irreducible target. -/
theorem genericPoint_eq_of_isDominant (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    f.base (genericPoint X) = genericPoint Y := by
  refine ((genericPoint_spec Y).eq ?_).symm
  have h := (genericPoint_spec X).image f.continuous
  rwa [Set.image_univ, f.denseRange.closure_eq] at h

/-- **(function field pullback of a dominant morphism)** The map on function fields induced by a
dominant morphism `f : X ⟶ Y` of irreducible schemes: the stalk map of `f` at the generic point of
`X` (whose image is the generic point of `Y` by `genericPoint_eq_of_isDominant`). For an open
immersion this is an isomorphism; in general it is the field extension `K(Y) ↪ K(X)` pulled back
along `f`. -/
noncomputable def Scheme.Hom.functionFieldMap (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    Y.functionField ⟶ X.functionField :=
  eqToHom (show Y.functionField = Y.presheaf.stalk (f.base (genericPoint X)) from
      congrArg (Y.presheaf.stalk) (genericPoint_eq_of_isDominant f).symm) ≫
    f.stalkMap (genericPoint X)

end AlgebraicGeometry
