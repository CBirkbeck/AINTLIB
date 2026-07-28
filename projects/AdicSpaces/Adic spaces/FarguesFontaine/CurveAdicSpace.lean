/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.CurveQuotientLeg
import «Adic spaces».AdicSpaceV

/-!
# The adic Fargues–Fontaine curve is an adic space — the reduction

Wedhorn Definition 8.22 asks for an open cover of `X` by opens `𝒱`-isomorphic to
adic spectra of sheafy affinoid pairs.  P5-5 supplies the quotient leg
`𝒴|_V ≅ X|_{π V}` for every wandering `V`, so a chart on `𝒴` transports to a
chart on `X`, and the capstone reduces to a statement about `𝒴` alone:

    every point of `𝒴` has a WANDERING neighbourhood `𝒱`-isomorphic to an affinoid.

`curveAdicSpacePresentation` already proves the corresponding *topological*
statement; what remains for `isAdicSpace_xVObj` is to upgrade the chart
homeomorphism supplied by `exists_window_subdatum_nbhd` to a `𝒱`-isomorphism.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology
  Filter CategoryTheory Opposite Pointwise

open scoped AlgebraicGeometry

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- The wandering condition on an open of `𝒴`. -/
def IsWandering (V : Opens ↥(yTop p F ϖ)) : Prop :=
  ∀ k : ℤ, k ≠ 0 →
    Disjoint (((Opens.map (yFrobTop p F ϖ k)).obj V
        : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))
      ((V : Opens ↥(yTop p F ϖ)) : Set ↥(yTop p F ϖ))

/-- **The chart criterion for the adic Fargues–Fontaine curve**: if every point
of `𝒴` has a *wandering* open neighbourhood that is `𝒱`-isomorphic to the adic
spectrum of a sheafy affinoid pair, then the curve is an adic space in the sense
of Wedhorn Definition 8.22.

The quotient leg `𝒴|_V ≅ X|_{π V}` (P5-5) does all the work: it transports a
chart on `𝒴` to a chart on `X`. -/
theorem isAdicSpace_xVObj_of_yCharts
    (h : ∀ y : ↥(yTop p F ϖ), ∃ (V : Opens ↥(yTop p F ϖ)), y ∈ V ∧
      IsWandering p F ϖ V ∧ ∃ C : ValuationSpectrum.AffinoidVChart,
        Nonempty ((yVObj p F ϖ).restrictOpen V ≅ C.toVObj)) :
    ValuationSpectrum.IsAdicSpace (xVObj p F ϖ) := by
  intro x
  obtain ⟨V, hyV, hdis, C, ⟨e⟩⟩ := h (fiberPoint p F ϖ x)
  refine ⟨xImage p F ϖ V, ⟨fiberPoint p F ϖ x, hyV,
    yTopToCurve_fiberPoint p F ϖ x⟩, C, ⟨?_⟩⟩
  exact (quotientLegVObjIso p F ϖ V hdis).symm ≪≫ e

end FarguesFontaine

end
