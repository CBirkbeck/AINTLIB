/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flatness is stable under retracts of schemes over a base

**[KM-W0 / F3-flat] ForMathlib brick (candidate mathlib PR).** If `X` is a retract of
`Y` over `S` (morphisms `i : X ⟶ Y`, `r : Y ⟶ X` over `S` with `i ≫ r = 𝟙 X`) and
`Y ⟶ S` is flat, then `X ⟶ S` is flat.

Route: the stalkwise criterion (`AlgebraicGeometry.Flat.of_stalkMap` /
`Flat.stalkMap`) plus `Module.Flat.of_retract` — at each `x : X` the stalk
`𝒪_{X,x}` is a module retract of `𝒪_{Y, i x}` over `𝒪_{S, s}` via the stalk maps of
`i` and `r`, whose composite is the identity by `i ≫ r = 𝟙`.

KM (print p. 27, the use site): *"the sheaf of `S`-algebras defining `G[N₁]` is an
`S`-direct factor of that defining `G`, so flat over `S`."*
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

/-- **Flatness descends along retracts over a base.** If `i : X ⟶ Y` and `r : Y ⟶ X`
are morphisms over `S` with `i ≫ r = 𝟙 X`, and `g : Y ⟶ S` is flat, then
`f : X ⟶ S` is flat. -/
theorem Flat.of_retract_over {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (i : X ⟶ Y) (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X)
    (hi : i ≫ g = f) (hr : r ≫ f = g) [Flat g] : Flat f := by
  sorry

end ModularCurves
