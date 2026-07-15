/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionChartRing

/-!
# The two laws are projectively proportional on a chart-product (T-W7.0c-c5β, β4(a))

The six certified minors of `AdditionLaw.lean` — the first thing proved in this ticket — are
consumed here, instantiated at the tautological points of the `(i,j)` chart-product:

  `lawOneTriple m * lawTwoTriple n = lawOneTriple n * lawTwoTriple m`   for all `m n : Fin 3`.

That is: the two Bosma–Lenstra laws, as projective triples over `biChartRing W i j`, have
vanishing `2 × 2` minors, i.e. they are proportional wherever both are regular. This is the
ring-level content of `addOn_agree` (T-W7.0c(c3)) — the statement that the glued morphism is
well defined on the overlap of the two laws' regularity opens.

No certificate is re-proved here: the identities are `addX_mul_dblAddY`, `addX_mul_dblAddZ`,
`addY_mul_dblAddZ` (dba3aa8c) applied to the tautological points, whose curve equations are
`equation_biChartPointFst` / `_Snd` (4eebfdee).
-/

open MvPolynomial

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i j : Fin 3)

lemma lawOneTriple_zero : lawOneTriple W i j 0 =
    (W.map (algebraMap R (biChartRing W i j))).toProjective.addX
      (biChartPointFst W i j) (biChartPointSnd W i j) := rfl

lemma lawOneTriple_one : lawOneTriple W i j 1 =
    (W.map (algebraMap R (biChartRing W i j))).toProjective.addY
      (biChartPointFst W i j) (biChartPointSnd W i j) := rfl

lemma lawOneTriple_two : lawOneTriple W i j 2 =
    (W.map (algebraMap R (biChartRing W i j))).toProjective.addZ
      (biChartPointFst W i j) (biChartPointSnd W i j) := rfl

lemma lawTwoTriple_zero : lawTwoTriple W i j 0 =
    (W.map (algebraMap R (biChartRing W i j))).toProjective.dblAddX
      (biChartPointFst W i j) (biChartPointSnd W i j) := rfl

lemma lawTwoTriple_one : lawTwoTriple W i j 1 =
    (W.map (algebraMap R (biChartRing W i j))).toProjective.dblAddY
      (biChartPointFst W i j) (biChartPointSnd W i j) := rfl

lemma lawTwoTriple_two : lawTwoTriple W i j 2 =
    (W.map (algebraMap R (biChartRing W i j))).toProjective.dblAddZ
      (biChartPointFst W i j) (biChartPointSnd W i j) := rfl

/-- **(β4(a), the minors consumed)** The two Bosma–Lenstra laws are projectively proportional on
every chart-product: all `2 × 2` minors of the pair of triples vanish. This is the ring-level
content of `addOn_agree` — the two laws glue. -/
theorem lawOneTriple_mul_lawTwoTriple (m n : Fin 3) :
    lawOneTriple W i j m * lawTwoTriple W i j n =
      lawOneTriple W i j n * lawTwoTriple W i j m := by
  have hP := equation_biChartPointFst W i j
  have hQ := equation_biChartPointSnd W i j
  fin_cases m <;> fin_cases n
  · rfl
  · exact addX_mul_dblAddY hP hQ
  · exact addX_mul_dblAddZ hP hQ
  · exact (addX_mul_dblAddY hP hQ).symm
  · rfl
  · exact addY_mul_dblAddZ hP hQ
  · exact (addX_mul_dblAddZ hP hQ).symm
  · exact (addY_mul_dblAddZ hP hQ).symm
  · rfl

end WeierstrassCurve.Projective
