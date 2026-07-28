/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.CurveQuotientLeg
import «Adic spaces».AdicSpaceV
import «Adic spaces».FarguesFontaine.CurveYSlice
import «Adic spaces».FarguesFontaine.CurveVChart

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


/-! ### The window-chart form of the capstone

Specialising `isAdicSpace_xVObj_of_yCharts` to the charts `windowSubOpen` that
`CurveYSlice.lean` produces.  `CurveAdicPresentation.lean` and `CurveYSlice.lean`
declare the window-chart ring facts as `local instance`s, so they are re-declared
here. -/

noncomputable local instance instTateWindow' (n : ℤ) :
    IsTateRing (windowChartRing p F ϖ n) :=
  isTateRing_bigWindowChart p F (windowUnif p F ϖ n)

noncomputable local instance instStronglyNoetherianWindow' (n : ℤ) :
    IsStronglyNoetherian (windowChartRing p F ϖ n) :=
  isStronglyNoetherian_canonical_window p F ϖ n

noncomputable local instance instNoetherianWindow' (n : ℤ) :
    IsNoetherianRing (windowChartRing p F ϖ n) :=
  IsStronglyNoetherian.isNoetherianRing _

noncomputable local instance instTateSub' (n : ℤ)
    (D' : RationalLocData (windowChartRing p F ϖ n)) :
    IsTateRing (presheafValue D') := presheafValue_isTateRing_concrete D'

noncomputable local instance instSNSub' (n : ℤ)
    (D' : RationalLocData (windowChartRing p F ϖ n)) :
    IsStronglyNoetherian (presheafValue D') :=
  presheafValue_isStronglyNoetherian_faithful D'

/-- The window chart's `𝒱`-object is exactly the P5-2 `spaVObjTate` package. -/
theorem windowSubVChart_toVPreObj (n : ℤ)
    (D' : RationalLocData (windowChartRing p F ϖ n)) :
    (windowSubVChart p F ϖ n D').toVObj.toVPreObj
      = (ValuationSpectrum.spaVObjTate
          (A := presheafValue D')).toVPreObj := rfl

/-- **The adic Fargues–Fontaine curve is an adic space, given the two chart
facts about `𝒴`**: that the window sub-opens are a neighbourhood basis, and that
each of them is `𝒱`-isomorphic to its window sub-affinoid.

Everything else — the quotient leg `𝒴|_V ≅ X|_{π V}` (P5-5), the wandering
neighbourhoods, the chart package, and Wedhorn's Definition 8.22 itself — is
already proven. -/
theorem isAdicSpace_xVObj_of_windowCharts
    (hbasis : ∀ (y : ↥(yTop p F ϖ)) (O : Opens ↥(yTop p F ϖ)), y ∈ O →
      ∃ (n : ℤ) (D' : RationalLocData (windowChartRing p F ϖ n))
        (u' : (presheafValue D')ˣ) (hu' : IsTopologicallyNilpotent
          ((u' : (presheafValue D')ˣ) : presheafValue D'))
        (u : (windowChartRing p F ϖ n)ˣ) (hu : IsTopologicallyNilpotent
          ((u : (windowChartRing p F ϖ n)ˣ) : windowChartRing p F ϖ n)),
        y ∈ windowSubOpen p F ϖ n D' u' hu' u hu ∧
          windowSubOpen p F ϖ n D' u' hu' u hu ≤ O)
    (hviso : ∀ (n : ℤ) (D' : RationalLocData (windowChartRing p F ϖ n))
        (u' : (presheafValue D')ˣ) (hu' : IsTopologicallyNilpotent
          ((u' : (presheafValue D')ˣ) : presheafValue D'))
        (u : (windowChartRing p F ϖ n)ˣ) (hu : IsTopologicallyNilpotent
          ((u : (windowChartRing p F ϖ n)ˣ) : windowChartRing p F ϖ n)),
      Nonempty ((ValuationSpectrum.spaVObjTate (A := presheafValue D')).toVPreObj
        ≅ (yVPreObj p F ϖ).restrictOpen
            (windowSubOpen p F ϖ n D' u' hu' u hu))) :
    ValuationSpectrum.IsAdicSpace (xVObj p F ϖ) := by
  refine isAdicSpace_xVObj_of_yCharts p F ϖ (fun y => ?_)
  obtain ⟨W₀, hyW₀, hdis₀⟩ := exists_disjoint_translates p F ϖ y
  obtain ⟨n, D', u', hu', u, hu, hyV, hVW₀⟩ := hbasis y W₀ hyW₀
  refine ⟨windowSubOpen p F ϖ n D' u' hu' u hu, hyV,
    disjoint_translates_mono p F ϖ hVW₀ hdis₀,
    windowSubVChart p F ϖ n D', ?_⟩
  obtain ⟨e⟩ := hviso n D' u' hu' u hu
  exact ⟨ValuationSpectrum.VObj.isoOfVPreIso e.symm⟩

end FarguesFontaine

end
