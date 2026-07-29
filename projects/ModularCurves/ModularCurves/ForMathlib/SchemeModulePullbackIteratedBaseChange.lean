/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Iterated pullback of scheme modules

This file identifies direct pullback of a scheme module with iterated pullback
through the canonical associator for successive base changes.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Direct pullback of a scheme module along a composite base change agrees
with successive pullback along the two base changes, after transport through
the canonical associator of the two pullback schemes. -/
noncomputable def pullbackIteratedBaseChangeIso
    {X S T U : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (u : U ⟶ T)
    (M : X.Modules) :
    (pullback (Limits.pullback.fst f (u ≫ t))).obj M ≅
      (pullback (pullbackLeftPullbackSndIso f t u).inv).obj
        ((pullback (Limits.pullback.fst (Limits.pullback.snd f t) u)).obj
          ((pullback (Limits.pullback.fst f t)).obj M)) :=
  (pullbackCongr (pullbackLeftPullbackSndIso_inv_fst f t u)).symm.app M ≪≫
    (pullbackComp (pullbackLeftPullbackSndIso f t u).inv
      (Limits.pullback.fst (Limits.pullback.snd f t) u ≫
        Limits.pullback.fst f t)).symm.app M ≪≫
    (pullback (pullbackLeftPullbackSndIso f t u).inv).mapIso
      ((pullbackComp (Limits.pullback.fst (Limits.pullback.snd f t) u)
        (Limits.pullback.fst f t)).symm.app M)

end AlgebraicGeometry.Scheme.Modules
