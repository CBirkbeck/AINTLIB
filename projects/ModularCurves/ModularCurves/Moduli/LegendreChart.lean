/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.UniversalLevelThree

/-!
# The Legendre chart: normalising a marked char-≠2 presentation (T-G3a-SUB2)

**(STREAM-OMEGA 2026-07-25; the `N = 2` mirror of `isE3Chart`.)** The scheme-level
counterpart of `ModularCurves.exists_legendre_variableChange_of_two_torsion`: given a
local presentation `P₀` in char-≠2 normal form (`a₁ = a₃ = 0`) marking two sections at
`(p, 0)` and `(p', 0)`, together with

* Vieta data `e₃` expressing the cubic as `(x−p)(x−p')(x−e₃)`, and
* a unit square root `u` of `p' − p`,

the twisted chart `P₀.ofVC ⟨u, p, 0, 0⟩` is a **Legendre** chart: its curve is
`legendreCurve λ` for `λ = u⁻²(e₃ − p)`, it marks the first section at `(0, 0)` and the
second at `(1, 0)`. Together with `LocalPresentation.IsAdapted.ofVC` this discharges all
four conjuncts of `IsLegendreDatum` at a point.

The field/algebraically-closed hypotheses are **not** needed here — they enter only when
producing `e₃` (`exists_third_root_vieta`) and `u` (`IsAlgClosed.exists_pow_nat_eq`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits WeierstrassCurve

namespace ModularCurves

open LocalPresentation

variable {S : Scheme.{u}} {G : EllipticCurveGeom S} {V : S.affineOpens}

set_option backward.isDefEq.respectTransparency false in
/-- **(T-G3a-SUB2, the Legendre chart ★)** A char-≠2 chart marking two sections at
`(p, 0)`, `(p', 0)`, with Vieta data and a square root `u² = p' − p`, becomes a Legendre
chart after the variable change `⟨u, p, 0, 0⟩`: the curve is `legendreCurve (u⁻²(e₃−p))`
and the two marks move to `(0, 0)` and `(1, 0)`.

This is the `N = 2` mirror of `isE3Chart`; the algebraic heart is
`scale_translate_smul_eq_legendreCurve` and the marking transport is
`LocalPresentation.MarksAt.ofVC`. -/
theorem isLegendreChart (P₀ : LocalPresentation G V)
    (ha₁ : P₀.W.a₁ = 0) (ha₃ : P₀.W.a₃ = 0)
    {σP σQ : S ⟶ G.E} {hσP : σP ≫ G.π = 𝟙 S} {hσQ : σQ ≫ G.π = 𝟙 S}
    {p p' e₃ : Γ(S, V.1)} (hMP : P₀.MarksAt hσP p 0) (hMQ : P₀.MarksAt hσQ p' 0)
    (ha₂ : P₀.W.a₂ = -(p + p' + e₃))
    (ha₄ : P₀.W.a₄ = p * p' + p * e₃ + p' * e₃)
    (ha₆ : P₀.W.a₆ = -(p * p' * e₃))
    (u : Γ(S, V.1)ˣ) (hu : ((u : Γ(S, V.1))) ^ 2 = p' - p) :
    (P₀.ofVC ⟨u, p, 0, 0⟩).W =
        legendreCurve (((u⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1)) ^ 2 * (e₃ - p)) ∧
      (P₀.ofVC ⟨u, p, 0, 0⟩).MarksAt hσP 0 0 ∧
      (P₀.ofVC ⟨u, p, 0, 0⟩).MarksAt hσQ 1 0 := by
  set C : VariableChange Γ(S, V.1) := ⟨u, p, 0, 0⟩ with hC
  set lam : Γ(S, V.1) := ((u⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1)) ^ 2 * (e₃ - p) with hlam
  have hW : (P₀.ofVC C).W = legendreCurve lam :=
    scale_translate_smul_eq_legendreCurve ha₁ ha₃ u ha₂ ha₄ ha₆ hu
  refine ⟨hW, ?_, ?_⟩
  · have hEq : (C • P₀.W).toAffine.Equation 0 0 := by
      rw [show C • P₀.W = legendreCurve lam from hW]
      exact legendreCurve_equation_zero lam
    refine LocalPresentation.MarksAt.ofVC P₀ C hEq ?_
    rw [hC]
    simpa using hMP
  · have hEq : (C • P₀.W).toAffine.Equation 1 0 := by
      rw [show C • P₀.W = legendreCurve lam from hW]
      exact legendreCurve_equation_one lam
    refine LocalPresentation.MarksAt.ofVC P₀ C hEq ?_
    rw [hC]
    have hp' : (u : Γ(S, V.1)) ^ 2 + p = p' := by rw [hu]; ring
    simpa [hp'] using hMQ

end ModularCurves
