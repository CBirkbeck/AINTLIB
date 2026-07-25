/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.PolynomialStandardSmooth
import ModularCurves.Moduli.UniversalLegendre

/-!
# The Legendre moduli scheme is smooth of relative dimension one

`Spec R[λ][(λ(λ−1))⁻¹] ⟶ Spec R` is smooth of relative dimension one: the
λ-line chart of the `Y(ρ̄)` smoothness leaf (T-YR-6 (b1)+(b2a) applied to the
`T-E14` universal Legendre object).
-/

noncomputable section

namespace ModularCurves

open AlgebraicGeometry Algebra

universe u

variable (R : CommRingCat.{u})

instance legendreModuliRing_isStandardSmoothOfRelativeDimension :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (LegendreModuliRing R) :=
  Algebra.IsStandardSmoothOfRelativeDimension.localizationAway_mvPolynomialFinOne
    R (legendrePoly R)

/-- **[T-YR-6 (b1) scheme level]** The universal Legendre object's structure
map is smooth of relative dimension one. -/
theorem universalLegendreObj_structMap_smooth (hR : IsUnit (2 : R)) :
    SmoothOfRelativeDimension 1 (universalLegendreObj R hR).structMap :=
  smoothOfRelativeDimension_spec_map_algebraMap 1

end ModularCurves

end
