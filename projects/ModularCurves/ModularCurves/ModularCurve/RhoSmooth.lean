/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ModularCurve.RhoSections
import ModularCurves.Moduli.LegendreSmooth
import ModularCurves.Moduli.BaseChangeIso

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


open scoped FintypeCatDiscrete in
/-- **[T-YR-6-APP (i)]** The ρ-level problem over `ℚ` is represented by an object with
**affine** base: the engine's `D(3)` leg produces one over `ℚ[1/3]`, and `3` is a unit
in `ℚ`, so the base-change isomorphism transports it back. -/
theorem rhoProblem_exists_representableBy_isAffine (D : GaloisRepData N) [Fact (1 < N)]
    (hN : 3 ≤ (N : ℤ)) :
    ∃ Y : EllObj (CommRingCat.of ℚ), IsAffine Y.base ∧
      Nonempty ((rhoProblem D).RepresentableBy Y) := by
  haveI : IsIso (ModuliProblem.awayHomWire (CommRingCat.of ℚ) (3 : CommRingCat.of ℚ)) :=
    isIso_awayHomWire_of_isUnit _ _ (by
      refine isUnit_iff_ne_zero.mpr ?_
      norm_num)
  exact ModuliProblem.exists_representableBy_isAffine_of_isIso _
    (ModuliProblem.exists_representableBy_isAffine_baseChange_three
      (CommRingCat.of ℚ) (rhoProblem D) (rhoProblem_affineOverEll D) (rho_rigidNoeth D hN))

/-- **[T-YR-6-APP (i)]** Every representing object of the ρ-level problem has affine base. -/
theorem rhoProblem_isAffine_base (D : GaloisRepData N) [Fact (1 < N)] (hN : 3 ≤ (N : ℤ))
    {X : EllObj (CommRingCat.of ℚ)} (r : (rhoProblem D).RepresentableBy X) :
    IsAffine X.base :=
  ModuliProblem.isAffine_base_of_representableBy
    (rhoProblem_exists_representableBy_isAffine D hN) r

end ModularCurves

end
