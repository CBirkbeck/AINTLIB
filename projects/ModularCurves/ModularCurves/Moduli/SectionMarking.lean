/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.SectionCoordinates
import ModularCurves.EllipticCurve.ModelVariableChange
import ModularCurves.LevelStructure.Factorization
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

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([hArb-2a] marking existence from zero-avoidance)** A section avoiding the zero
section topologically over `V` is marked at honest coordinates: off the zero section is
in the `Z`-chart (`mem_range_zero_of_not_mem_zChart`), so `marksAt_of_forall_basicOpen`
applies. The zero-avoidance hypothesis is stated on the curve `G` itself, where the
level structure supplies it fibrewise. -/
theorem marksAt_of_forall_not_mem_range_zero {S : Scheme.{u}}
    {G : EllipticCurveGeom S} {V : S.affineOpens} (Pr : LocalPresentation G V)
    {σ : S ⟶ G.E} (hσ : σ ≫ G.π = 𝟙 S)
    (hne : ∀ w, w ∈ V.1 → σ.base w ∉ Set.range G.zero.base) :
    ∃ p q : Γ(S, V.1), Pr.MarksAt hσ p q := by
  refine Pr.marksAt_of_forall_basicOpen hσ (fun x => ?_)
  by_contra hmem
  -- off the chart lands on the model zero section
  have hz := mem_range_zero_of_not_mem_zChart (W := Pr.W) hmem
  obtain ⟨y, hy⟩ := hz
  -- transport the zero-image membership back through the chart iso
  have hzc : projModelZero Pr.W =
      (V.2.isoSpec.inv ≫ pullback.lift (V.1.ι ≫ G.zero) (𝟙 _)
        (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])) ≫
        Pr.e.hom := Pr.compat_zero.symm
  rw [hzc] at hy
  -- peel the (iso) chart map
  have hy' : ((V.2.isoSpec.inv ≫ sectionLift G hσ V)).base x =
      ((V.2.isoSpec.inv ≫ pullback.lift (V.1.ι ≫ G.zero) (𝟙 _)
        (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp]))).base y := by
    have hinj : Function.Injective (Pr.e.hom.base) :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso Pr.e)).injective
    apply hinj
    have h1 : (((V.2.isoSpec.inv ≫ sectionLift G hσ V) ≫ Pr.e.hom)).base x =
        Pr.e.hom.base (((V.2.isoSpec.inv ≫ sectionLift G hσ V)).base x) := rfl
    have h2 : (((V.2.isoSpec.inv ≫ pullback.lift (V.1.ι ≫ G.zero) (𝟙 _)
          (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])) ≫
        Pr.e.hom)).base y =
        Pr.e.hom.base (((V.2.isoSpec.inv ≫ pullback.lift (V.1.ι ≫ G.zero) (𝟙 _)
          (by rw [Category.assoc, G.zero_π, Category.comp_id,
            Category.id_comp]))).base y) := rfl
    rw [← h1, ← h2]
    exact hy.symm
  -- push to `E` along the first pullback leg
  have hfst := congrArg (pullback.fst G.π V.1.ι).base hy'
  have hsl : sectionLift G hσ V ≫ pullback.fst G.π V.1.ι = V.1.ι ≫ σ :=
    pullback.lift_fst _ _ _
  have hzl : pullback.lift (V.1.ι ≫ G.zero) (𝟙 _)
      (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp]) ≫
        pullback.fst G.π V.1.ι = V.1.ι ≫ G.zero :=
    pullback.lift_fst _ _ _
  have hEpoint : (V.1.ι ≫ σ).base (V.2.isoSpec.inv.base x) =
      (V.1.ι ≫ G.zero).base (V.2.isoSpec.inv.base y) := by
    have h1 : (V.1.ι ≫ σ).base (V.2.isoSpec.inv.base x) =
        ((V.2.isoSpec.inv ≫ sectionLift G hσ V) ≫ pullback.fst G.π V.1.ι).base x := by
      rw [Category.assoc, hsl]
      rfl
    have h2 : (V.1.ι ≫ G.zero).base (V.2.isoSpec.inv.base y) =
        ((V.2.isoSpec.inv ≫ pullback.lift (V.1.ι ≫ G.zero) (𝟙 _)
          (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])) ≫
          pullback.fst G.π V.1.ι).base y := by
      rw [Category.assoc, hzl]
      rfl
    rw [h1, h2]
    exact hfst
  -- contradict zero-avoidance at the underlying point of `V`
  refine hne (V.1.ι.base (V.2.isoSpec.inv.base x)) ?_ ?_
  · exact (V.2.isoSpec.inv.base x).2
  · exact ⟨V.1.ι.base (V.2.isoSpec.inv.base y), by
      have := hEpoint
      rw [show (V.1.ι ≫ σ).base (V.2.isoSpec.inv.base x) =
        σ.base (V.1.ι.base (V.2.isoSpec.inv.base x)) from rfl,
        show (V.1.ι ≫ G.zero).base (V.2.isoSpec.inv.base y) =
        G.zero.base (V.1.ι.base (V.2.isoSpec.inv.base y)) from rfl] at this
      exact this.symm⟩


/-- **([hArb-2b] fibrewise distinctness ⟹ disjoint ranges)** Two sections of a
separated morphism whose pulls differ at every algebraically closed geometric point
have disjoint topological images: their graph ideals are comaximal
(`sup_ker_eq_top_of_pull_ne`), so the supports — the closed ranges — do not meet. -/
theorem forall_not_mem_range_of_pull_ne {S : Scheme.{u}} {C : Scheme.{u}} {π : C ⟶ S}
    [IsSeparated π] (Q₁ Q₂ : S ⟶ C) (hQ₁ : Q₁ ≫ π = 𝟙 S) (hQ₂ : Q₂ ≫ π = 𝟙 S)
    (hne : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ Q₁ ≠ t ≫ Q₂)
    (w : S) : Q₁.base w ∉ Set.range Q₂.base := by
  intro hw
  haveI hci₁ : IsClosedImmersion Q₁ := by
    have hcomp : IsClosedImmersion (Q₁ ≫ π) := by rw [hQ₁]; infer_instance
    exact IsClosedImmersion.of_comp Q₁ π
  haveI hci₂ : IsClosedImmersion Q₂ := by
    have hcomp : IsClosedImmersion (Q₂ ≫ π) := by rw [hQ₂]; infer_instance
    exact IsClosedImmersion.of_comp Q₂ π
  have hsup := RelEffCartierDiv.sup_ker_eq_top_of_pull_ne Q₁ Q₂ hQ₁ hQ₂ hne
  have hc : Q₁.base w ∈ (Scheme.Hom.ker Q₁ ⊔ Scheme.Hom.ker Q₂).support := by
    rw [Scheme.IdealSheafData.support_sup]
    refine ⟨?_, ?_⟩
    · rw [Scheme.Hom.support_ker]
      exact subset_closure ⟨w, rfl⟩
    · rw [Scheme.Hom.support_ker]
      exact subset_closure hw
  rw [hsup, Scheme.IdealSheafData.support_top] at hc
  exact hc

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([hArb-2] marking existence from fibrewise nonvanishing)** A section of a
geometric elliptic curve whose pull differs from zero at every algebraically closed
geometric point of the base is marked at honest coordinates on every affine piece —
the interface the level structure feeds directly. -/
theorem marksAt_of_forall_pull_ne_zero {S : Scheme.{u}}
    {G : EllipticCurveGeom S} {V : S.affineOpens} (Pr : LocalPresentation G V)
    {σ : S ⟶ G.E} (hσ : σ ≫ G.π = 𝟙 S)
    (hne : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ σ ≠ t ≫ G.zero) :
    ∃ p q : Γ(S, V.1), Pr.MarksAt hσ p q := by
  haveI : IsProper G.π := G.proper
  exact Pr.marksAt_of_forall_not_mem_range_zero hσ
    (fun w _ => forall_not_mem_range_of_pull_ne σ G.zero hσ G.zero_π hne w)


end LocalPresentation

end ModularCurves
