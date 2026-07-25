/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ModularCurve.RhoSections
import ModularCurves.Moduli.LegendreSmooth

/-!
# The Legendre-anchored ρ-cover is smooth of relative dimension one

**[T-YR-6 carrier]** The free `GL₂`-quotient of the symplectically framed
moduli at the universal Legendre anchor is finite étale over the λ-line, hence
smooth of relative dimension one over `Spec ℚ`. This is the smooth carrier for
the `Y(ρ̄)` smoothness leaf: `Y(ρ̄)` itself receives a finite étale surjective
cover from this scheme (the Legendre-datum forget map), so its smoothness
follows once smoothness descends along finite étale covers (T-YR-6 (c1)).
-/

noncomputable section

namespace ModularCurves

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {N : ℕ} [NeZero N]

open scoped FintypeCatDiscrete in
/-- **[T-YR-6 carrier]** The Legendre-anchored ρ-quotient is smooth of relative
dimension one over `Spec ℚ`: finite étale over the λ-line, which is smooth of
relative dimension one. -/
theorem rhoLegendre_carrier_smooth (D : GaloisRepData N) [Fact (1 < N)]
    (hR : IsUnit (2 : (CommRingCat.of ℚ)))
    (d : ModuliProblem.EquivariantRelRepData (sympFramedAut D)
      (universalLegendreObj (CommRingCat.of ℚ) hR))
    [IsAffineHom d.f] :
    SmoothOfRelativeDimension 1
      (d.σZ.relQuotientStruct d.f d.over_base ≫
        (universalLegendreObj (CommRingCat.of ℚ) hR).structMap) := by
  have hfe := d.σZ.relQuotientStruct_finite_etale_of_free d.f d.over_base
    (d.free_on_points (sympFramedAut_freeAction D)) d.finite d.etale
  haveI hFin : IsFinite (d.σZ.relQuotientStruct d.f d.over_base) := hfe.1
  haveI hEt : Etale (d.σZ.relQuotientStruct d.f d.over_base) := hfe.2
  haveI h0 : SmoothOfRelativeDimension 0
      (d.σZ.relQuotientStruct d.f d.over_base) := inferInstance
  haveI h1 : SmoothOfRelativeDimension 1
      ((universalLegendreObj (CommRingCat.of ℚ) hR).structMap) :=
    universalLegendreObj_structMap_smooth (CommRingCat.of ℚ) hR
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1)
    (d.σZ.relQuotientStruct d.f d.over_base ≫
      (universalLegendreObj (CommRingCat.of ℚ) hR).structMap))

end ModularCurves

end
