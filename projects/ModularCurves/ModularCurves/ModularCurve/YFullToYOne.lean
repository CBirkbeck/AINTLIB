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

end ModularCurves
