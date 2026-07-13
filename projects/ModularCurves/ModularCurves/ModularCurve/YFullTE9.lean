/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ModularCurve.YFullRoute

/-!
# The Y(N) representability master theorem T-E9 (relocated)

`ModularCurves.LevelModuli.gammaFullNaive_representable` (T-E9) is discharged from the YFULL
route assembly `YFull.gammaFullNaive_representable_assembly`. Per the v10.111/v10.117 relocation
doctrine the master lives **downstream** of `ModularCurve/YFullRoute.lean` (which supplies the
assembly) — the byte-identical statement previously held in `Moduli/NaiveProblems.lean` is closed
here by the single `exact`, and its remaining content is exactly the route's two boarded gates:
`gammaFullNaive_rigid` ([YF-NOETH] / CHARTER-P3B3 rigidity linchpin) and
`exists_representing_smooth_affine` ([YF-GEOM] / CHARTER-FP4 engine construction).
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

namespace LevelModuli

variable (R : CommRingCat.{u})

/-- **(T-E9 = Loeffler Prop 3.8.2–3.8.3; KM 3.1/4.7/5.1)** For `N ≥ 3` and `N` invertible in
`R`, the naive full-level problem `[Γ(N)]` is rigid and representable; the representing scheme
`Y(N)` is smooth and affine over `Spec R`. Discharged via the YFULL route assembly. -/
theorem gammaFullNaive_representable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    ((gammaFullNaiveProblem R N).Rigid ∧ (gammaFullNaiveProblem R N).Representable) ∧
      ∀ X : EllObj R, Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) :=
  YFull.gammaFullNaive_representable_assembly R N hN hinv

end LevelModuli

end ModularCurves
