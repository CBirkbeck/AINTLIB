/-
================================================================================
PR DRAFT #1 — `Functor.map_zpow'`  (staged locally; DO NOT open externally)
================================================================================
Owner action: submitting to mathlib is an owner decision. This file is the
mathlib-ready extract; strip this metadata block before submission.

* TARGET FILE : Mathlib/CategoryTheory/Monoidal/Cartesian/Grp.lean
* PLACEMENT   : immediately after `Functor.map_inv'` (currently ~line 191).
                `map_zpow'` is the exact `zpow` sibling of the existing `map_inv'`.
* CLASS       : fills-cited-gap (natural API companion of `map_inv'`).
* SHORTENS    : Grp.lean already uses `map_zpow (Functor.homMonoidHom F) …` inline
                at ~line 166; that inline use can be replaced by `F.map_zpow'`.
* IMPORTS     : none new (the target file already imports everything used).
* NOTES       : keep `@[to_additive]` (gives `Functor.map_zsmul'` for free); the
                `open scoped CategoryTheory.Obj in` is needed for `GrpObj`.
* SOURCE      : ForMathlib/FunctorMapZpow.lean (verified compiling in-project).
================================================================================
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Monoidal functors preserve powers of morphisms into a group object

`Functor.map_zpow'`: for a monoidal functor `F` and a group object `G`, the functor
action on hom-into-`G` preserves integer powers — `F.map (f ^ n) = (F.map f) ^ n`.
This is the `zpow` companion of `Functor.map_inv'`.
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
