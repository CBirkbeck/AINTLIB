/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.UniversalLevelThree

/-!
# The `{±1}`-symmetry of Legendre data ([T-E14-ACT'] datum layer)

**(STREAM-OMEGA 2026-07-17, G0's :206 asks (2a).)** The Legendre-datum condition is
symmetric under the `{±1}`-action on the `ω`-basis: `IsLegendreDatum.neg` — a datum for
`(L, b)` is a datum for `(L, (-1) • b)`. Mechanism: the scaling variable change
`C = ⟨-1, 0, 0, 0⟩` fixes every Legendre curve (`a₁ = a₃ = 0`, and `a₂, a₄, a₆` scale
by even powers of `u`), fixes both markings (their `y`-coordinates vanish and
`r = s = t = 0`), and flips the adaptation unit by `C.u = -1`
(`basisUnitAt_ofVC` + `basisUnitAt_smul`), matching the basis flip.

This is one of the two fibre-pinning lemmas of the `±ω` scale-torsor over the level-2
locus (G0's `legendreDelta_relRep_finiteEtale_of_scaleTorsor` funnel for
`Bootstrap.lean:206`); the other (uniqueness-up-to-`±`) is tracked separately.
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([T-E14-ACT'] the `{±1}`-flip of a Legendre datum)** A Legendre datum for
`(L, b)` is one for `(L, (-1) • b)`: twist each witness chart by the scaling variable
change `⟨-1, 0, 0, 0⟩`. -/
theorem IsLegendreDatum.neg {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) :
    IsLegendreDatum X L ((-1 : Γ(X.base, ⊤)ˣ) • b) := by
  intro s
  obtain ⟨V, hsV, Pr, lam, hAd, hW, hMP, hMQ⟩ := hD s
  set C : WeierstrassCurve.VariableChange Γ(X.base, V.1) := ⟨-1, 0, 0, 0⟩ with hC
  have hWfix : C • Pr.W = legendreCurve lam := by
    rw [hW]
    ext <;>
      simp [hC, legendreCurve, WeierstrassCurve.variableChange_def, Units.val_neg,
        Units.val_one] <;>
      ring
  refine ⟨V, hsV, Pr.ofVC C, lam, ?_, ?_, ?_, ?_⟩
  · -- adaptation to the flipped basis
    show (((Pr.ofVC C).basisUnitAt _)).1 = 1
    rw [basisUnitAt_smul, basisUnitAt_ofVC, hAd]
    refine Units.ext ?_
    simp [hC, Scheme.resUnit_val]
  · -- the twisted chart curve is the same Legendre curve
    show C • Pr.W = legendreCurve lam
    exact hWfix
  · -- the `P`-marking at `(0, 0)` survives
    refine LocalPresentation.MarksAt.ofVC Pr C ?_ ?_
    · rw [hWfix]
      exact legendreCurve_equation_zero lam
    · convert hMP using 2 <;> simp [hC]
  · -- the `Q`-marking at `(1, 0)` survives
    refine LocalPresentation.MarksAt.ofVC Pr C ?_ ?_
    · rw [hWfix]
      exact legendreCurve_equation_one lam
    · convert hMQ using 2 <;> simp [hC]

end ModularCurves
