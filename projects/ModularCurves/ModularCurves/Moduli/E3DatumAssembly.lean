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

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([hArb-3b] the B-locus hypothesis is redundant ★★)** On a flex-normal-form chart
with a marked `3`-torsion point `(p, q)`, the `isE3Form_of_threeTorsion` B-quantity is
AUTOMATICALLY a unit: its norm over the chart quotient is `27·a₃⁸·(a₁³−27a₃)² = 27a₃²Δ²`,
witnessed by the integral adjugate certificate
(`docs/certificates/hB-redundancy-certificate.py`). No fibrewise argument, no sheet
fallback, valid over any (non-reduced) base ring. -/
theorem isUnit_e3B {A : Type u} [CommRing A] {W : WeierstrassCurve A} {p q : A}
    (hcurve : q ^ 2 + W.a₁ * p * q + W.a₃ * q = p ^ 3)
    (hcubic : 3 * p ^ 3 + W.a₁ ^ 2 * p ^ 2 + 3 * W.a₁ * W.a₃ * p + 3 * W.a₃ ^ 2 = 0)
    (ha₃ : IsUnit W.a₃) (h3 : IsUnit (3 : A))
    (hfac : IsUnit (W.a₁ ^ 3 - 27 * W.a₃)) :
    IsUnit (W.a₁ ^ 3 * p + W.a₁ ^ 2 * W.a₃ + W.a₁ ^ 2 * q + 6 * W.a₁ * p ^ 2
      + 3 * W.a₃ * p + 6 * p * q) := by
  set a1 := W.a₁
  set a3 := W.a₃
  refine isUnit_of_mul_isUnit_left (y := a3 ^ 4 * (a1 ^ 3 - 27 * a3) *
    (-(a1 ^ 7 * q) - 3 * a1 ^ 5 * a3 * p + 6 * a1 ^ 5 * p * q + 45 * a1 ^ 4 * a3 * q
      - 9 * a1 ^ 3 * a3 * p ^ 2 + 27 * a1 ^ 3 * p ^ 2 * q - 27 * a1 ^ 2 * a3 * p * q
      - 135 * a1 * a3 ^ 3 - 270 * a1 * a3 ^ 2 * q - 81 * a3 ^ 2 * p ^ 2
      - 162 * a3 * p ^ 2 * q)) ?_
  rw [show (a1 ^ 3 * p + a1 ^ 2 * a3 + a1 ^ 2 * q + 6 * a1 * p ^ 2 + 3 * a3 * p
        + 6 * p * q) * (a3 ^ 4 * (a1 ^ 3 - 27 * a3) *
      (-(a1 ^ 7 * q) - 3 * a1 ^ 5 * a3 * p + 6 * a1 ^ 5 * p * q + 45 * a1 ^ 4 * a3 * q
        - 9 * a1 ^ 3 * a3 * p ^ 2 + 27 * a1 ^ 3 * p ^ 2 * q - 27 * a1 ^ 2 * a3 * p * q
        - 135 * a1 * a3 ^ 3 - 270 * a1 * a3 ^ 2 * q - 81 * a3 ^ 2 * p ^ 2
        - 162 * a3 * p ^ 2 * q))
      = 27 * a3 ^ 8 * (a1 ^ 3 - 27 * a3) ^ 2 from by
    linear_combination (norm := ring)
      (-(a1 ^ 12 * a3 ^ 4) + 72 * a1 ^ 9 * a3 ^ 5 + 63 * a1 ^ 8 * a3 ^ 4 * p ^ 2
        + 243 * a1 ^ 7 * a3 ^ 5 * p - 1485 * a1 ^ 6 * a3 ^ 6 + 162 * a1 ^ 6 * a3 ^ 4 * p ^ 3
        - 2025 * a1 ^ 5 * a3 ^ 5 * p ^ 2 - 8181 * a1 ^ 4 * a3 ^ 6 * p
        + 7290 * a1 ^ 3 * a3 ^ 7 - 5346 * a1 ^ 3 * a3 ^ 5 * p ^ 3
        + 8748 * a1 ^ 2 * a3 ^ 6 * p ^ 2 + 43740 * a1 * a3 ^ 7 * p
        + 26244 * a3 ^ 6 * p ^ 3) * hcurve +
      (-(a1 ^ 10 * a3 ^ 4 * p) + 3 * a1 ^ 8 * a3 ^ 4 * p ^ 2 + 36 * a1 ^ 7 * a3 ^ 5 * p
        - 54 * a1 ^ 6 * a3 ^ 6 - 45 * a1 ^ 6 * a3 ^ 5 * q + 54 * a1 ^ 6 * a3 ^ 4 * p ^ 3
        - 81 * a1 ^ 5 * a3 ^ 5 * p ^ 2 - 621 * a1 ^ 4 * a3 ^ 6 * p
        + 1701 * a1 ^ 3 * a3 ^ 7 + 1215 * a1 ^ 3 * a3 ^ 6 * q
        - 1782 * a1 ^ 3 * a3 ^ 5 * p ^ 3 + 10206 * a1 * a3 ^ 7 * p - 6561 * a3 ^ 8
        + 8748 * a3 ^ 6 * p ^ 3) * hcubic]
  exact ((show IsUnit (27 : A) from by
      rw [show (27 : A) = 3 ^ 3 by norm_num]
      exact h3.pow 3).mul (ha₃.pow 8)).mul (hfac.pow 2)


end ModularCurves
