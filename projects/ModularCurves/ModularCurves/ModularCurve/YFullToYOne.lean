/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.RepresentableByMap
import ModularCurves.Moduli.GammaFullToGammaOne
import ModularCurves.ModularCurve.YOneTatePoint

/-!
# The morphism `Y(N) ⟶ Y₁(N)` (WP-D1c, construction)

`Y₁(N)` is smooth and affine over the base — `gammaOneNaive_representable`, axiom-verified —
while the corresponding statement for `Y(N)` is the open
`YFull.exists_representing_smooth_affine`. The plan (WP-D2) is to transport smoothness along
a finite étale `Y(N) ⟶ Y₁(N)`.

This file constructs the morphism. It is Yoneda applied to the level-forgetting natural
transformation `gammaFullToGammaOne` (WP-D1b), through the general
`Functor.RepresentableBy.map`. Its characterising property `yFullToYOne_homEquiv` says
exactly what one wants: an `Ell/R`-morphism into `Y(N)` classifies a full level-`N`
structure, and composing with `yFullToYOne` classifies its first member.

What remains for WP-D1c is that this morphism is **finite étale**; the fibre over a
`Γ₁(N)`-structure `P` is the set of `Q` completing `P` to a basis of `E[N]`, a clopen
subscheme of `E[N]`, so `fullLevelLocus`'s finiteness and étaleness machinery
(`Moduli/Bootstrap.lean`'s `naiveLevelThree_relativelyRepresentable_finiteEtale` is the
model) should apply one level down.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace ModularCurves

variable (R : CommRingCat.{u})

/-- **(WP-D1c, construction)** The level-forgetting morphism `Y(N) ⟶ Y₁(N)`, for any pair
of objects representing the two problems. Taking the representations as arguments rather
than choosing them keeps the definition free of hidden `Classical.choice` and makes it apply
to whichever representing objects a caller has in hand. -/
noncomputable def yFullToYOne (N : ℕ) [NeZero N] (hinv : IsUnit (N : R))
    {X Y : EllObj R} (rFull : (gammaFullNaiveProblem R N).RepresentableBy X)
    (rOne : (gammaOneNaiveProblem R N).RepresentableBy Y) : X ⟶ Y :=
  rFull.map rOne (gammaFullToGammaOne N hinv)

/-- **(WP-D1c, the characterising property)** Composing with `yFullToYOne` forgets the
second member of the level structure: if `f : T ⟶ Y(N)` classifies `(P, Q)`, then
`f ≫ yFullToYOne` classifies `P`. -/
theorem yFullToYOne_homEquiv (N : ℕ) [NeZero N] (hinv : IsUnit (N : R))
    {X Y : EllObj R} (rFull : (gammaFullNaiveProblem R N).RepresentableBy X)
    (rOne : (gammaOneNaiveProblem R N).RepresentableBy Y)
    {T : EllObj R} (f : T ⟶ X) :
    (rOne.homEquiv (f ≫ yFullToYOne R N hinv rFull rOne)).1 = (rFull.homEquiv f).1.1 :=
  congrArg Subtype.val
    (Functor.RepresentableBy.homEquiv_comp_map rFull rOne (gammaFullToGammaOne N hinv) f)

/-- **(WP-D1c)** The morphism exists for the Tate-point model `Y₁(N)`, which is the one
whose smoothness is known (`gammaOneNaive_representable`). -/
theorem nonempty_yFullToYOne (N : ℕ) [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R))
    {X : EllObj R} (rFull : (gammaFullNaiveProblem R N).RepresentableBy X) :
    Nonempty (X ⟶ yOneEllObj R N) :=
  (yOne_representableBy R N hN hinv).map (yFullToYOne R N hinv rFull)

/-! ### The universal level structures (WP-D2a)

A representing object carries a tautological level structure — the image of its identity
under the representing equivalence — and every classified structure is its pullback. This is
the input to WP-D2b, where `Y(N)` is identified with the relative locus of the universal
curve over `Y₁(N)`. -/

/-- **(WP-D2a)** The universal naive `Γ₁(N)`-structure on a representing object. -/
noncomputable def universalGammaOne (N : ℕ) [NeZero N] {Y : EllObj R}
    (rOne : (gammaOneNaiveProblem R N).RepresentableBy Y) :
    { P : Y.curve.Section // Y.curve.IsNaiveGammaOne N P } :=
  rOne.homEquiv (𝟙 Y)

/-- **(WP-D2a)** Every classified naive `Γ₁(N)`-structure is the pullback of the universal
one along its classifying morphism. -/
theorem homEquiv_eq_map_universalGammaOne (N : ℕ) [NeZero N] {Y : EllObj R}
    (rOne : (gammaOneNaiveProblem R N).RepresentableBy Y) {T : EllObj R} (f : T ⟶ Y) :
    rOne.homEquiv f =
      (gammaOneNaiveProblem R N).map f.op (universalGammaOne R N rOne) := by
  rw [universalGammaOne, ← rOne.homEquiv_comp f (𝟙 Y), Category.comp_id]

/-- **(WP-D2a)** The universal naive full level-`N` structure on a representing object. -/
noncomputable def universalFullLevel (N : ℕ) [NeZero N] {X : EllObj R}
    (rFull : (gammaFullNaiveProblem R N).RepresentableBy X) :
    { PQ : X.curve.Section × X.curve.Section //
      X.curve.IsNaiveFullLevel N PQ.1 PQ.2 } :=
  rFull.homEquiv (𝟙 X)

/-- **(WP-D2a)** Every classified naive full level-`N` structure is the pullback of the
universal one. -/
theorem homEquiv_eq_map_universalFullLevel (N : ℕ) [NeZero N] {X : EllObj R}
    (rFull : (gammaFullNaiveProblem R N).RepresentableBy X) {T : EllObj R} (f : T ⟶ X) :
    rFull.homEquiv f =
      (gammaFullNaiveProblem R N).map f.op (universalFullLevel R N rFull) := by
  rw [universalFullLevel, ← rFull.homEquiv_comp f (𝟙 X), Category.comp_id]

/-- **(WP-D2a → D2b)** The universal full level structure's first member is the pullback of
the universal `Γ₁(N)`-structure along `yFullToYOne`. This is the compatibility that lets
`Y(N)` be recognised, over `Y₁(N)`, as the space of completions of the universal `P`. -/
theorem universalFullLevel_fst_eq (N : ℕ) [NeZero N] (hinv : IsUnit (N : R))
    {X Y : EllObj R} (rFull : (gammaFullNaiveProblem R N).RepresentableBy X)
    (rOne : (gammaOneNaiveProblem R N).RepresentableBy Y) :
    ((gammaOneNaiveProblem R N).map (yFullToYOne R N hinv rFull rOne).op
        (universalGammaOne R N rOne)).1 = (universalFullLevel R N rFull).1.1 := by
  rw [← homEquiv_eq_map_universalGammaOne R N rOne (yFullToYOne R N hinv rFull rOne)]
  have h := yFullToYOne_homEquiv R N hinv rFull rOne (𝟙 X)
  rw [Category.id_comp] at h
  exact h

end ModularCurves
