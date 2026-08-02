/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.QuotientProblem

/-!
# Morphisms into a `pullbackAlong` (WP-D2c-3a)

An `Ell/R`-morphism into `X.pullbackAlong g` is the same thing as an `Ell/R`-morphism into
`X` together with a lift of its base map through `g`:

  `(T ⟶ X.pullbackAlong g) ≃ Σ (u : T ⟶ X), { b : T.base ⟶ B // b ≫ g = u.baseHom }`.

This is the general shape behind "the full-level space over `Y₁(N)` represents `Γ(N)`": with
`g` the structure map of a relative level locus, the right-hand side is *a level structure of
the coarser type, plus a refinement of it*.

**Why the projection is injective here, when `EllHom` is *not* determined by its `baseHom`.**
An `EllHom` is determined by its `top` and `baseHom` (the remaining fields are `Prop`s), and
`baseHom` alone genuinely does not suffice — inversion `[-1]` gives a second `EllHom X X`
over `𝟙`. But in this equivalence the datum being matched includes `u`, and `w.top` is
recovered from `u.top` together with `w.baseHom` by `pullback.hom_ext`, since
`w.top ≫ pullback.fst = u.top`. Changing `top` changes `u`, so the counterexample does not
apply.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

-- `(X.pullbackAlong g).curve.E` and `pullback X.curve.π g` are definitionally equal but not
-- syntactically; `rw` needs to see through that, as in `Moduli/LevelLocusNatural.lean:27`.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace ModularCurves

namespace EllObj

variable {R : CommRingCat.{u}}

@[simp] theorem comp_baseHom {X Y Z : EllObj R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).baseHom = f.baseHom ≫ g.baseHom := rfl

@[simp] theorem comp_top {X Y Z : EllObj R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).top = f.top ≫ g.top := rfl

/-- An `EllHom` is determined by its `baseHom` **and** its `top`; the other fields are
propositions. -/
theorem hom_ext {X Y : EllObj R} {f g : X ⟶ Y} (hb : f.baseHom = g.baseHom)
    (ht : f.top = g.top) : f = g := by
  cases f; cases g; cases hb; cases ht; rfl

/-- **(WP-D2c-3a, injectivity)** A morphism into a `pullbackAlong` is determined by its base
map together with its composite to `X`. -/
theorem hom_pullbackAlong_ext {T X : EllObj R} {B : Scheme.{u}} {g : B ⟶ X.base}
    {w w' : T ⟶ X.pullbackAlong g}
    (hb : w.baseHom = w'.baseHom)
    (hu : w ≫ X.pullbackAlongπ g = w' ≫ X.pullbackAlongπ g) : w = w' := by
  refine hom_ext hb ?_
  refine pullback.hom_ext ?_ ?_
  · have h := congrArg EllHom.top hu
    exact h
  · show w.top ≫ pullback.snd X.curve.π g = w'.top ≫ pullback.snd X.curve.π g
    have hw : w.top ≫ pullback.snd X.curve.π g = T.curve.π ≫ w.baseHom :=
      w.isPullback.w
    have hw' : w'.top ≫ pullback.snd X.curve.π g = T.curve.π ≫ w'.baseHom :=
      w'.isPullback.w
    rw [hw, hw', hb]

/-- **(WP-D2c-3a, the backward map)** From a morphism `u : T ⟶ X` and a lift `b` of its base
map through `g`, a morphism `T ⟶ X.pullbackAlong g`. Built explicitly rather than by
transporting `toPullbackAlong`, so that no `eqToHom` appears and the `baseHom`/`top`
components are definitionally what one expects. -/
noncomputable def ofPullbackAlongData {T X : EllObj R} {B : Scheme.{u}} (g : B ⟶ X.base)
    (u : T ⟶ X) (b : T.base ⟶ B) (hb : b ≫ g = u.baseHom) :
    T ⟶ X.pullbackAlong g where
  baseHom := b
  base_w := by
    show b ≫ g ≫ X.structMap = T.structMap
    rw [← Category.assoc, hb, u.base_w]
  top := pullback.lift u.top (T.curve.π ≫ b) (by
    rw [Category.assoc, hb]
    exact u.isPullback.w)
  isPullback := by
    have h2 : IsPullback u.top T.curve.π X.curve.π (b ≫ g) := by
      rw [hb]; exact u.isPullback
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback X.curve.π g)
    exact (pullback.lift_fst (f := X.curve.π) (g := g) u.top (T.curve.π ≫ b)
      (by rw [Category.assoc, hb]; exact u.isPullback.w)).symm ▸ h2
  zero_w := by
    refine pullback.hom_ext ?_ ?_
    · have hl : (T.curve.zero ≫ pullback.lift u.top (T.curve.π ≫ b)
          (by rw [Category.assoc, hb]; exact u.isPullback.w)) ≫
            pullback.fst X.curve.π g = T.curve.zero ≫ u.top :=
        (Category.assoc _ _ _).trans
          (congrArg (fun m => T.curve.zero ≫ m) (pullback.lift_fst _ _ _))
      refine hl.trans ?_
      show T.curve.zero ≫ u.top = (b ≫ pullback.lift (g ≫ X.curve.zero) (𝟙 B) _) ≫
        pullback.fst X.curve.π g
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hb]
      exact u.zero_w
    · have hl : (T.curve.zero ≫ pullback.lift u.top (T.curve.π ≫ b)
          (by rw [Category.assoc, hb]; exact u.isPullback.w)) ≫
            pullback.snd X.curve.π g = T.curve.zero ≫ T.curve.π ≫ b :=
        (Category.assoc _ _ _).trans
          (congrArg (fun m => T.curve.zero ≫ m) (pullback.lift_snd _ _ _))
      refine hl.trans ?_
      show T.curve.zero ≫ T.curve.π ≫ b = (b ≫ pullback.lift (g ≫ X.curve.zero) (𝟙 B) _) ≫
        pullback.snd X.curve.π g
      rw [Category.assoc, pullback.lift_snd, Category.comp_id, ← Category.assoc,
        T.curve.zero_π, Category.id_comp]

@[simp] theorem ofPullbackAlongData_baseHom {T X : EllObj R} {B : Scheme.{u}}
    (g : B ⟶ X.base) (u : T ⟶ X) (b : T.base ⟶ B) (hb : b ≫ g = u.baseHom) :
    (ofPullbackAlongData g u b hb).baseHom = b := rfl

@[simp] theorem ofPullbackAlongData_comp_pullbackAlongπ {T X : EllObj R} {B : Scheme.{u}}
    (g : B ⟶ X.base) (u : T ⟶ X) (b : T.base ⟶ B) (hb : b ≫ g = u.baseHom) :
    ofPullbackAlongData g u b hb ≫ X.pullbackAlongπ g = u := by
  refine hom_ext ?_ ?_
  · show b ≫ g = u.baseHom
    exact hb
  · show pullback.lift u.top (T.curve.π ≫ b) _ ≫ pullback.fst X.curve.π g = u.top
    exact pullback.lift_fst _ _ _

end EllObj

end ModularCurves
