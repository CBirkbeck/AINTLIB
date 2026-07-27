/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The projection intertwines the pullback monoid multiplication

For a monoid object `Over.mk f` in `Over S` and `g : T ⟶ S`, the base-changed monoid
structure on `Over.mk (pullback.snd f g)` (mathlib's `Over.monObjMkPullbackSnd`, the image
under the monoidal functor `Over.pullback g`) multiplies compatibly with the first
projection: `μ_{pullback}.left ≫ pullback.fst = ⟨fst ≫ fst, snd ≫ fst⟩ ≫ μ.left`.

This is the morphism-level naturality that makes point-pullback along base change an
additive map (AINTLIB T-H2b). Mathlib's `isMonHom_pullbackFst_id_right` is the
`g = 𝟙`-specialisation packaged `Over`-categorically; the general `g` statement cannot be
an `Over`-morphism statement (the two objects live over different bases), so it is stated
raw. Entirely term-mode: the defeq seam `((Over.pullback g).obj A).left ≡ pullback A.hom g`
is semireducible, and `rw`/`simp` matchers (`kabstract`) re-check compositions at
`instances` transparency where the mixed spellings are not type-correct.

AINTLIB ModularCurves (T-H2b); upstream candidate.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits MonObj

universe v u

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable {X S T : C} (f : X ⟶ S) (g : T ⟶ S)

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory CategoryTheory.Over.monObjMkPullbackSnd

/-- The first projection intertwines the pullback monoid multiplication with the original
one, over the base-change square. -/
lemma monObjMkPullbackSnd_mul_left_fst [MonObj (Over.mk f)] :
    (μ[Over.mk (pullback.snd f g)]).left ≫ pullback.fst f g
      = pullback.lift
          (pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.fst f g)
          (pullback.snd (pullback.snd f g) (pullback.snd f g) ≫ pullback.fst f g)
          (by
            simp only [Over.mk_hom, Category.assoc]
            rw [pullback.condition (f := f) (g := g), ← Category.assoc,
              pullback.condition (f := pullback.snd f g) (g := pullback.snd f g),
              Category.assoc])
        ≫ (μ[Over.mk f]).left := by
  have hmap : ∀ (h : Over.mk f ⊗ Over.mk f ⟶ Over.mk f),
      ((Over.pullback g).map h).left ≫ pullback.fst f g
        = pullback.fst (Over.mk f ⊗ Over.mk f).hom g ≫ h.left := fun h => by
    simp only [Over.pullback]
    exact pullback.lift_fst _ _ _
  have hmapfst := hmap (fst (Over.mk f) (Over.mk f))
  have hmapsnd := hmap (snd (Over.mk f) (Over.mk f))
  have h1 := congrArg CommaMorphism.left
    (Functor.Monoidal.μ_fst (F := Over.pullback g) (Over.mk f) (Over.mk f))
  have h2 := congrArg CommaMorphism.left
    (Functor.Monoidal.μ_snd (F := Over.pullback g) (Over.mk f) (Over.mk f))
  have hcomp : (Functor.LaxMonoidal.μ (Over.pullback g) (Over.mk f) (Over.mk f)).left
        ≫ pullback.fst (Over.mk f ⊗ Over.mk f).hom g
      = pullback.lift
          (pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.fst f g)
          (pullback.snd (pullback.snd f g) (pullback.snd f g) ≫ pullback.fst f g)
          (by
            simp only [Over.mk_hom, Category.assoc]
            rw [pullback.condition (f := f) (g := g), ← Category.assoc,
              pullback.condition (f := pullback.snd f g) (g := pullback.snd f g),
              Category.assoc]) := by
    apply Over.tensorObj_ext
    · exact (Category.assoc _ _ _).trans <|
        (congrArg ((Functor.LaxMonoidal.μ (Over.pullback g) (Over.mk f) (Over.mk f)).left ≫ ·)
          hmapfst.symm).trans <|
        (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ pullback.fst f g) (Over.comp_left _ _ _ _ _).symm).trans <|
        (congrArg (· ≫ pullback.fst f g) h1).trans <|
        (pullback.lift_fst _ _ _).symm
    · exact (Category.assoc _ _ _).trans <|
        (congrArg ((Functor.LaxMonoidal.μ (Over.pullback g) (Over.mk f) (Over.mk f)).left ≫ ·)
          hmapsnd.symm).trans <|
        (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ pullback.fst f g) (Over.comp_left _ _ _ _ _).symm).trans <|
        (congrArg (· ≫ pullback.fst f g) h2).trans <|
        (pullback.lift_snd _ _ _).symm
  rw [Over.monObjMkPullbackSnd_mul]
  exact (congrArg (· ≫ pullback.fst f g) (Over.comp_left _ _ _ _ _)).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((Functor.LaxMonoidal.μ (Over.pullback g) (Over.mk f) (Over.mk f)).left ≫ ·)
      (hmap _)).trans <|
    (Category.assoc _ _ _).symm.trans <|
    congrArg (· ≫ (μ[Over.mk f]).left) hcomp

attribute [local instance] CategoryTheory.Over.grpObjMkPullbackSnd

/-- The group-object form of `monObjMkPullbackSnd_mul_left_fst` (the two structures share
their underlying multiplication definitionally). -/
lemma grpObjMkPullbackSnd_mul_left_fst [GrpObj (Over.mk f)] :
    (μ[Over.mk (pullback.snd f g)]).left ≫ pullback.fst f g
      = pullback.lift
          (pullback.fst (pullback.snd f g) (pullback.snd f g) ≫ pullback.fst f g)
          (pullback.snd (pullback.snd f g) (pullback.snd f g) ≫ pullback.fst f g)
          (by
            simp only [Over.mk_hom, Category.assoc]
            rw [pullback.condition (f := f) (g := g), ← Category.assoc,
              pullback.condition (f := pullback.snd f g) (g := pullback.snd f g),
              Category.assoc])
        ≫ (μ[Over.mk f]).left :=
  monObjMkPullbackSnd_mul_left_fst f g

end CategoryTheory.Over
