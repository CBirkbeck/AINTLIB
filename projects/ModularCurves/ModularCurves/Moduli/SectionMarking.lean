/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.SectionCoordinates
import ModularCurves.Moduli.LegendreDelta

/-!
# Marking existence for chart-avoiding sections ([hArb-1])

**(STREAM-OMEGA 2026-07-17.)** A section of a geometric elliptic curve whose chart
image avoids the point at infinity everywhere over an affine piece is MARKED there:
`LocalPresentation.marksAt_of_forall_basicOpen` produces honest affine coordinates
`(p, q)` with `Pr.MarksAt hσ p q`, by factoring the chart composite through the
`Z`-chart (`IsOpenImmersion.lift`) and reading the coordinates off
`eq_affineSection_of_zChart_factor` ([hArb-1] core, `SectionCoordinates.lean`).

The remaining input — the pointwise `Z`-chart membership — is supplied by the level
structure (fibrewise nonvanishing of the marked sections; [hArb-2]).
-/

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory Limits HomogeneousIdeal HomogeneousLocalization

namespace LocalPresentation

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([hArb-1] marking existence)** If the chart image of a section lies in the
`Z`-chart at every point of `Spec Γ(V)`, the presentation marks the section at honest
affine coordinates. -/
theorem marksAt_of_forall_basicOpen {S : Scheme.{u}}
    {G : EllipticCurveGeom S} {V : S.affineOpens} (Pr : LocalPresentation G V)
    {σ : S ⟶ G.E} (hσ : σ ≫ G.π = 𝟙 S)
    (hz : ∀ x, ((V.2.isoSpec.inv ≫ sectionLift G hσ V) ≫ Pr.e.hom).base x ∈
      Proj.basicOpen (quotientGrading (projIdeal Pr.W))
        ((quotientGradingHom (projIdeal Pr.W)) (MvPolynomial.X 2))) :
    ∃ p q : Γ(S, V.1), Pr.MarksAt hσ p q := by
  have hπ : ((V.2.isoSpec.inv ≫ sectionLift G hσ V) ≫ Pr.e.hom) ≫ projModelπ Pr.W
      = 𝟙 _ := by
    rw [Category.assoc, Pr.compat_π]
    rw [show (V.2.isoSpec.inv ≫ sectionLift G hσ V) ≫ pullback.snd G.π V.1.ι ≫
          V.2.isoSpec.hom
        = V.2.isoSpec.inv ≫ (sectionLift G hσ V ≫ pullback.snd G.π V.1.ι) ≫
          V.2.isoSpec.hom from by
      simp only [Category.assoc]]
    rw [show sectionLift G hσ V ≫ pullback.snd G.π V.1.ι = 𝟙 _ from
      pullback.lift_snd _ _ _]
    rw [Category.id_comp, Iso.inv_hom_id]
  have hrange : Set.range ((V.2.isoSpec.inv ≫ sectionLift G hσ V) ≫ Pr.e.hom).base ⊆
      Set.range (Proj.awayι (quotientGrading (projIdeal Pr.W))
        ((quotientGradingHom (projIdeal Pr.W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one Pr.W 2) one_pos).base := by
    rw [show Set.range (Proj.awayι (quotientGrading (projIdeal Pr.W))
        ((quotientGradingHom (projIdeal Pr.W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one Pr.W 2) one_pos).base
        = (Proj.basicOpen (quotientGrading (projIdeal Pr.W))
            ((quotientGradingHom (projIdeal Pr.W)) (MvPolynomial.X 2)) :
          Set (Proj (quotientGrading (projIdeal Pr.W)))) from by
      rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]]
    rintro _ ⟨x, rfl⟩
    exact hz x
  obtain ⟨p, q, heq, hτ⟩ := eq_affineSection_of_zChart_factor Pr.W _ hπ
    (IsOpenImmersion.lift _ _ hrange) (IsOpenImmersion.lift_fac _ _ hrange)
  exact ⟨p, q, heq, hτ⟩

end LocalPresentation

end ModularCurves
