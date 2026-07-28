/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.CurveAdicSpace
import «Adic spaces».FarguesFontaine.CurveChartVIso

/-!
# The adic Fargues–Fontaine curve is an adic space

The capstone of Campaign 9.  `isAdicSpace_xVObj` states Wedhorn Definition 8.22
for `X = 𝒴/φ^ℤ`: every point has an open neighbourhood isomorphic **in Wedhorn's
category `𝒱`** to the adic spectrum of a sheafy affinoid pair — an isomorphism
that carries the structure sheaf, the stalk local rings and the stalk
valuations, not merely the topology.

The two ingredients are the quotient leg `𝒴|_V ≅ X|_{π V}` for wandering `V`
(`CurveQuotientLeg.lean`) and the chart isomorphism
`Spa(𝒪_{B_n}(D')) ≅ 𝒴|_{windowSubOpen}` (`CurveChartVIso.lean`), together with
the fact that the window sub-opens are a neighbourhood basis of `𝒴`
(`CurveYSlice.lean`).
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

/-- **★ THE ADIC FARGUES–FONTAINE CURVE IS AN ADIC SPACE ★**
(Wedhorn Definition 8.22): every point of `X = 𝒴/φ^ℤ` has an open neighbourhood
which is isomorphic **in Wedhorn's category `𝒱`** — carrying the structure
sheaf, the stalk local rings and the stalk valuations, not merely the topology —
to the adic spectrum of a sheafy affinoid pair. -/
theorem isAdicSpace_xVObj : ValuationSpectrum.IsAdicSpace (xVObj p F ϖ) :=
  isAdicSpace_xVObj_of_windowVIso p F ϖ (one_lt_p p)
    (fun n D' u' hu' u hu =>
      nonempty_windowSubVPreIso p F ϖ n D' u' hu' u hu (one_lt_p p))

/-- **`𝒴` is an adic space** — the companion statement. -/
theorem isAdicSpace_yVObj : ValuationSpectrum.IsAdicSpace (yVObj p F ϖ) :=
  isAdicSpace_yVObj_of_windowVIso p F ϖ (one_lt_p p)
    (fun n D' u' hu' u hu =>
      nonempty_windowSubVPreIso p F ϖ n D' u' hu' u hu (one_lt_p p))

end FarguesFontaine

end
