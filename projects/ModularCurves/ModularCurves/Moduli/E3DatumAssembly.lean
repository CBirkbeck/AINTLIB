/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.UniversalLevelThree
import ModularCurves.Moduli.SectionMarking
import ModularCurves.Moduli.LevelMarking

/-!
# The `ℰ₃`-datum assembly layers ([hArb-3])

**(STREAM-OMEGA 2026-07-17.)** The mechanical layers between the marking pipeline
([hArb-1/2], every level section has honest chart coordinates) and `IsE3Datum`:
translation of a marked chart to the origin (`marksAt_origin_ofVC`). The remaining
inputs of `isE3Datum_of_flexCharts` are the two torsion→coordinate bridges
(`3•σP = 0 ⟹` flex-normalizability; `3•σQ = 0 ⟹` the cubic), KM-coordinated per
board v10.307.
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory

namespace LocalPresentation


open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([hArb-3a] translation to the origin)** A chart marking `σ` at `(p₀, q₀)` twists
by the pure translation `⟨1, p₀, 0, q₀⟩` to a chart marking `σ` at the origin. -/
theorem marksAt_origin_ofVC {S : Scheme.{u}} {G : EllipticCurveGeom S}
    {V : S.affineOpens} (Pr : LocalPresentation G V)
    {σ : S ⟶ G.E} {hσ : σ ≫ G.π = 𝟙 S} {p₀ q₀ : Γ(S, V.1)}
    (hM : Pr.MarksAt hσ p₀ q₀) :
    (Pr.ofVC ⟨1, p₀, 0, q₀⟩).MarksAt hσ 0 0 := by
  obtain ⟨hEq, -⟩ := id hM
  set C : VariableChange Γ(S, V.1) := ⟨1, p₀, 0, q₀⟩ with hC
  have hEq' : (C • Pr.W).toAffine.Equation 0 0 := by
    have h := C.equation_smul Pr.W hEq
    rw [show C.vcX p₀ = 0 from by
        simp [hC, WeierstrassCurve.VariableChange.vcX],
      show C.vcY p₀ q₀ = 0 from by
        simp [hC, WeierstrassCurve.VariableChange.vcY]] at h
    exact h
  refine LocalPresentation.MarksAt.ofVC Pr C hEq' ?_
  convert hM using 2 <;> simp [hC]


end LocalPresentation

end ModularCurves
