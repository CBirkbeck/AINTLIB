/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Monoidal functors preserve powers of morphisms into a group object

`Functor.map_zpow'`: for a monoidal functor `F` and a group object `G`, the functor
action on hom-into-`G` preserves integer powers — `F.map (f ^ n) = (F.map f) ^ n`.
This is the `zpow` companion of mathlib's `Functor.map_inv'`. Upstream candidate.
-/

open CategoryTheory MonObj

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] {X G : C} [GrpObj G]

open scoped _root_.CategoryTheory.Obj in
/-- A monoidal functor's action on morphisms into a group object preserves integer
powers. -/
@[to_additive]
lemma map_zpow' (f : X ⟶ G) (n : ℤ) : F.map (f ^ n) = (F.map f) ^ n :=
  map_zpow (Functor.homMonoidHom F) f n

end CategoryTheory.Functor
