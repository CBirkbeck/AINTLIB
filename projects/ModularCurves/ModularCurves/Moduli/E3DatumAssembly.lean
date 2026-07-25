/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.UniversalLevelThree
import ModularCurves.Moduli.SectionMarking
import ModularCurves.Moduli.LevelMarking
import ModularCurves.ForMathlib.IsUnitOfResidue

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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

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


section ChartRecord

variable {S : Scheme.{u}} {E : EllipticCurve S} {V : S.affineOpens}
  (Pr : LocalPresentation E.toEllipticCurveGeom V)

/-- The classifying morphism of the affine piece. -/
noncomputable abbrev chartρ (V : S.affineOpens) : Spec Γ(S, V.1) ⟶ S :=
  V.2.isoSpec.inv ≫ V.1.ι

/-- **([hArb-3c-α] the pullback comparison)** Base change along `chartρ` agrees with
the chart pullback. -/
noncomputable def chartPullbackIso :
    (pullback E.π (chartρ V) : Scheme.{u}) ≅ pullback E.toEllipticCurveGeom.π V.1.ι where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ V.2.isoSpec.inv)
    (by rw [pullback.condition]; simp [chartρ])
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ V.2.isoSpec.hom)
    (by rw [pullback.condition, chartρ]
        simp only [Category.assoc, Iso.hom_inv_id_assoc])
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, Category.assoc]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- **([hArb-3c-α] the record comparison)** The base-changed record over `Spec Γ(V)`
is pointed-isomorphic (as an `Over`-object) to the chart model. -/
noncomputable def chartRecordIso :
    letI := Pr.elliptic
    (E.baseChange (chartρ V)).asOver ≅ (modelEllipticCurve Pr.W).asOver :=
  letI := Pr.elliptic
  Over.isoMk ((chartPullbackIso (E := E) (V := V)) ≪≫ Pr.e)
    (by
      show ((chartPullbackIso (E := E) (V := V)).hom ≫ Pr.e.hom) ≫ projModelπ Pr.W =
        pullback.snd E.π (chartρ V)
      rw [Category.assoc, Pr.compat_π]
      rw [show (chartPullbackIso (E := E) (V := V)).hom ≫
          pullback.snd E.toEllipticCurveGeom.π V.1.ι ≫ V.2.isoSpec.hom =
        ((chartPullbackIso (E := E) (V := V)).hom ≫
          pullback.snd E.toEllipticCurveGeom.π V.1.ι) ≫ V.2.isoSpec.hom from
        (Category.assoc _ _ _).symm]
      rw [show (chartPullbackIso (E := E) (V := V)).hom ≫
          pullback.snd E.toEllipticCurveGeom.π V.1.ι =
        pullback.snd E.π (chartρ V) ≫ V.2.isoSpec.inv from pullback.lift_snd _ _ _]
      simp [Category.assoc])

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([hArb-3c-β] pointedness)** The record comparison carries the base-changed zero
section to the model zero section. -/
theorem chartRecordIso_unit :
    letI := Pr.elliptic
    (η[(E.baseChange (chartρ V)).asOver] :
        𝟙_ (Over (Spec Γ(S, V.1))) ⟶ (E.baseChange (chartρ V)).asOver) ≫
      (chartRecordIso Pr).hom =
    η[(modelEllipticCurve Pr.W).asOver] := by
  letI := Pr.elliptic
  ext1
  rw [Over.comp_left, (E.baseChange (chartρ V)).one_eq_zero,
    (modelEllipticCurve Pr.W).one_eq_zero]
  rw [Category.assoc]
  congr 1
  -- `zero ≫ (pullback comparison ≫ e) = projModelZero`
  show (E.baseChange (chartρ V)).zero ≫
      ((chartPullbackIso (E := E) (V := V)).hom ≫ Pr.e.hom) = projModelZero Pr.W
  rw [← Pr.compat_zero, ← Category.assoc]
  congr 1
  refine pullback.hom_ext ?_ ?_
  · show ((E.baseChange (chartρ V)).zero ≫ (chartPullbackIso (E := E) (V := V)).hom) ≫
      pullback.fst E.toEllipticCurveGeom.π V.1.ι = _
    rw [Category.assoc,
      show (chartPullbackIso (E := E) (V := V)).hom ≫
          pullback.fst E.toEllipticCurveGeom.π V.1.ι = pullback.fst E.π (chartρ V) from
        pullback.lift_fst _ _ _]
    rw [show (E.baseChange (chartρ V)).zero ≫ pullback.fst E.π (chartρ V) =
      chartρ V ≫ E.zero from pullback.lift_fst _ _ _]
    rw [show (V.2.isoSpec.inv ≫ pullback.lift (V.1.ι ≫ E.toEllipticCurveGeom.zero)
        (𝟙 _) _) ≫ pullback.fst E.toEllipticCurveGeom.π V.1.ι =
      V.2.isoSpec.inv ≫ V.1.ι ≫ E.toEllipticCurveGeom.zero from by
        rw [Category.assoc, pullback.lift_fst]]
    rw [chartρ, Category.assoc]
  · show ((E.baseChange (chartρ V)).zero ≫ (chartPullbackIso (E := E) (V := V)).hom) ≫
      pullback.snd E.toEllipticCurveGeom.π V.1.ι = _
    rw [Category.assoc,
      show (chartPullbackIso (E := E) (V := V)).hom ≫
          pullback.snd E.toEllipticCurveGeom.π V.1.ι =
        pullback.snd E.π (chartρ V) ≫ V.2.isoSpec.inv from pullback.lift_snd _ _ _]
    rw [show (E.baseChange (chartρ V)).zero ≫ pullback.snd E.π (chartρ V) ≫
        V.2.isoSpec.inv = ((E.baseChange (chartρ V)).zero ≫
          pullback.snd E.π (chartρ V)) ≫ V.2.isoSpec.inv from
      (Category.assoc _ _ _).symm]
    rw [show (E.baseChange (chartρ V)).zero ≫ pullback.snd E.π (chartρ V) = 𝟙 _ from
      pullback.lift_snd _ _ _]
    rw [show (V.2.isoSpec.inv ≫ pullback.lift (V.1.ι ≫ E.toEllipticCurveGeom.zero)
        (𝟙 _) _) ≫ pullback.snd E.toEllipticCurveGeom.π V.1.ι =
      V.2.isoSpec.inv ≫ 𝟙 _ from by rw [Category.assoc, pullback.lift_snd]]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- **([hArb-3c-γ] the chart points equivalence)** Abstract points of `E` over a
`Spec Γ(V)`-point correspond additively to model points of the chart — the
base-change equivalence composed with the record-comparison transport
(`pointAddEquiv` + `isMonHom_of_pointedIso_records`). -/
noncomputable def chartPointsEquiv {T : Scheme.{u}} (tV : T ⟶ Spec Γ(S, V.1)) :
    letI := Pr.elliptic
    E.Point (tV ≫ chartρ V) ≃+ (modelEllipticCurve Pr.W).Point tV :=
  letI := Pr.elliptic
  (EllipticCurve.Point.baseChangeEquiv (E := E) (chartρ V) tV).symm.trans
    (EllipticCurve.pointAddEquiv (chartRecordIso Pr)
      (isMonHom_of_pointedIso_records _ _ (chartRecordIso Pr)
        (chartRecordIso_unit Pr)) tV)


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([hArb-3c-δ] the marked value)** Under the chart points equivalence, the pull of a
marked section evaluates to the (pulled) affine-point section of its chart
coordinates. -/
theorem chartPointsEquiv_pull_marked {T : Scheme.{u}} (tV : T ⟶ Spec Γ(S, V.1))
    {σ : S ⟶ E.toEllipticCurveGeom.E} {hσ : σ ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    {p q : Γ(S, V.1)} (heq : Pr.W.toAffine.Equation p q)
    (hMeq : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσ V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W p q heq) :
    letI := Pr.elliptic
    ((chartPointsEquiv Pr tV
        (EllipticCurve.Point.pull E (tV ≫ chartρ V) ⟨σ, hσ⟩))).1
      = tV ≫ projModelAffineSection Pr.W p q heq := by
  letI := Pr.elliptic
  show (pullback.lift ((tV ≫ chartρ V) ≫ σ) tV
      (by rw [Category.assoc, hσ, Category.comp_id]) ≫
    ((chartPullbackIso (E := E) (V := V)).hom ≫ Pr.e.hom)) = _
  rw [← hMeq]
  rw [show tV ≫ (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσ V) ≫ Pr.e.hom
      = (tV ≫ V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσ V) ≫ Pr.e.hom from
    by simp only [Category.assoc]]
  rw [← Category.assoc]
  congr 1
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc,
      show (chartPullbackIso (E := E) (V := V)).hom ≫
          pullback.fst E.toEllipticCurveGeom.π V.1.ι = pullback.fst E.π (chartρ V) from
        pullback.lift_fst _ _ _,
      pullback.lift_fst]
    simp only [Category.assoc]
    rw [show sectionLift E.toEllipticCurveGeom hσ V ≫
          pullback.fst E.toEllipticCurveGeom.π V.1.ι = V.1.ι ≫ σ from
        pullback.lift_fst _ _ _]
  · rw [Category.assoc,
      show (chartPullbackIso (E := E) (V := V)).hom ≫
          pullback.snd E.toEllipticCurveGeom.π V.1.ι =
        pullback.snd E.π (chartρ V) ≫ V.2.isoSpec.inv from pullback.lift_snd _ _ _,
      ← Category.assoc, pullback.lift_snd]
    simp only [Category.assoc]
    rw [show sectionLift E.toEllipticCurveGeom hσ V ≫
          pullback.snd E.toEllipticCurveGeom.π V.1.ι = 𝟙 _ from
        pullback.lift_snd _ _ _]
    simp


open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([hArb-3c-ε] the `a₃`-certificate ★★)** On a chart marking a fibrewise-nonzero
`3`-torsion section at the origin, `a₃` is a unit: at every residue point the marked
model point is `some(0,0)`, nonzero and `3`-torsion, hence not `2`-torsion — but
`a₃ = 0` would make `(0,0)` its own negation (`negY 0 0 = -a₃`). -/
theorem isUnit_a₃_of_marked_origin {S : Scheme.{u}} {E : EllipticCurve S}
    {V : S.affineOpens} (Pr : LocalPresentation E.toEllipticCurveGeom V)
    {σ : S ⟶ E.toEllipticCurveGeom.E} {hσ : σ ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    (heq : Pr.W.toAffine.Equation 0 0)
    (hMeq : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσ V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W 0 0 heq)
    (hkill : (3 : ℤ) • (⟨σ, hσ⟩ : E.Section) = 0)
    (hne : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ σ ≠ t ≫ E.zero) :
    IsUnit Pr.W.a₃ := by
  letI := Pr.elliptic
  refine isUnit_of_forall_algebraMap_residueField_ne_zero (fun 𝔭 => ?_)
  intro ha₃
  set K : Type u := 𝔭.asIdeal.ResidueField with hK
  set Kb : Type u := AlgebraicClosure K with hKb
  letI : DecidableEq Kb := Classical.decEq Kb
  letI : Algebra ↑Γ(S, V.1) Kb :=
    ((algebraMap K Kb).comp (algebraMap ↑Γ(S, V.1) K)).toAlgebra
  have halgKb : ∀ z : ↑Γ(S, V.1), algebraMap ↑Γ(S, V.1) Kb z =
      algebraMap K Kb (algebraMap ↑Γ(S, V.1) K z) := fun _ => rfl
  set tVb : Spec (CommRingCat.of Kb) ⟶ Spec Γ(S, V.1) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, V.1) Kb)) with htVb
  -- the transported marked point
  set x := chartPointsEquiv Pr tVb
    (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σ, hσ⟩) with hx
  have hkillE : (3 : ℤ) • EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σ, hσ⟩ = 0 := by
    rw [← EllipticCurve.Point.pull_zsmul, hkill, EllipticCurve.Point.pull_zero]
  have hkill3 : (3 : ℤ) • x = 0 := by
    rw [hx, ← map_zsmul, hkillE, map_zero]
  have hx0 : x ≠ 0 := by
    intro hc
    have h0 : EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σ, hσ⟩ = 0 := by
      have := (chartPointsEquiv Pr tVb).map_eq_zero_iff.mp (hx ▸ hc)
      exact this
    refine hne Kb (tVb ≫ chartρ V) ?_
    have hval := congrArg Subtype.val h0
    rw [E.point_zero_val] at hval
    exact hval
  -- its model value is `some (0, 0)`
  haveI : ((Pr.W.baseChange Kb)).IsElliptic :=
    inferInstanceAs ((Pr.W.map (algebraMap ↑Γ(S, V.1) Kb)).IsElliptic)
  have hns : (Pr.W.baseChange Kb).toAffine.Nonsingular
      (algebraMap ↑Γ(S, V.1) Kb 0) (algebraMap ↑Γ(S, V.1) Kb 0) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heq)
  have hxpkg : x = ⟨(affineSectionSpecPoint Pr.W Kb 0 0 heq).1,
      (affineSectionSpecPoint Pr.W Kb 0 0 heq).2⟩ := by
    refine Subtype.ext ?_
    rw [hx, chartPointsEquiv_pull_marked Pr tVb heq hMeq]
    rfl
  set y := modelPointAddEquiv Pr.W (K' := Kb) x with hy
  have hyval : y = WeierstrassCurve.Affine.Point.some _ _ hns := by
    rw [hy, hxpkg]
    show projModelPointsEquiv Pr.W Kb (affineSectionSpecPoint Pr.W Kb 0 0 heq) = _
    exact projModelPointsEquiv_affineSectionSpecPoint Pr.W 0 0 heq hns
  have hy3 : (3 : ℤ) • y = 0 := by
    rw [hy, ← map_zsmul, hkill3, map_zero]
  have hy0 : y ≠ 0 := by
    rw [hy]
    exact fun hc => hx0 ((modelPointAddEquiv Pr.W (K' := Kb)).map_eq_zero_iff.mp hc)
  -- `a₃ = 0` makes the marked point `2`-torsion
  have ha₃Kb : algebraMap ↑Γ(S, V.1) Kb Pr.W.a₃ = 0 := by
    rw [halgKb, ha₃, map_zero]
  have hy2 : (2 : ℤ) • y = 0 := by
    rw [hyval, two_zsmul]
    refine WeierstrassCurve.Affine.Point.add_of_Y_eq rfl ?_
    show algebraMap ↑Γ(S, V.1) Kb 0 = (Pr.W.baseChange Kb).toAffine.negY
      (algebraMap ↑Γ(S, V.1) Kb 0) (algebraMap ↑Γ(S, V.1) Kb 0)
    rw [WeierstrassCurve.Affine.negY]
    rw [show ((Pr.W.baseChange Kb)).toAffine.a₁ =
      algebraMap ↑Γ(S, V.1) Kb Pr.W.a₁ from rfl,
      show ((Pr.W.baseChange Kb)).toAffine.a₃ =
      algebraMap ↑Γ(S, V.1) Kb Pr.W.a₃ from rfl]
    rw [ha₃Kb, map_zero]
    ring
  -- `3`-torsion ∧ `2`-torsion ⟹ zero
  have : y = 0 := by
    have h1 : ((3 : ℤ) - 2) • y = 0 := by
      rw [sub_smul, hy3, hy2, sub_zero]
    rwa [show ((3 : ℤ) - 2) = 1 by norm_num, one_smul] at h1
  exact hy0 this


open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([hArb-3a′] the general marking transport)** Twisting a chart moves a marking by
the coordinate change: `(p, q) ↦ (vcX p, vcY p q)`. -/
theorem marksAt_ofVC_vc {S : Scheme.{u}} {G : EllipticCurveGeom S}
    {V : S.affineOpens} (Pr : LocalPresentation G V)
    {σ : S ⟶ G.E} {hσ : σ ≫ G.π = 𝟙 S} {p q : Γ(S, V.1)}
    (hM : Pr.MarksAt hσ p q) (C : VariableChange Γ(S, V.1)) :
    (Pr.ofVC C).MarksAt hσ (C.vcX p) (C.vcY p q) := by
  obtain ⟨heq, -⟩ := id hM
  refine LocalPresentation.MarksAt.ofVC Pr C (C.equation_smul Pr.W heq) ?_
  convert hM using 2
  · show ((C.u : Γ(S, V.1))) ^ 2 * C.vcX p + C.r = p
    rw [WeierstrassCurve.VariableChange.vcX,
      show ((C.u : Γ(S, V.1))) ^ 2 * (((C.u⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1)) ^ 2 *
          (p - C.r)) + C.r
        = (((C.u * C.u⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1))) ^ 2 * (p - C.r) + C.r from by
      push_cast
      ring]
    simp
  · show ((C.u : Γ(S, V.1))) ^ 3 * C.vcY p q +
      C.s * ((C.u : Γ(S, V.1))) ^ 2 * C.vcX p + C.t = q
    rw [WeierstrassCurve.VariableChange.vcX, WeierstrassCurve.VariableChange.vcY,
      show ((C.u : Γ(S, V.1))) ^ 3 * (((C.u⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1)) ^ 3 *
          (q - C.s * (p - C.r) - C.t)) +
        C.s * ((C.u : Γ(S, V.1))) ^ 2 * (((C.u⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1)) ^ 2 *
          (p - C.r)) + C.t
        = (((C.u * C.u⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1))) ^ 3 * (q - C.s * (p - C.r) - C.t)
          + C.s * (((C.u * C.u⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1))) ^ 2 * (p - C.r) + C.t from by
      push_cast
      ring]
    simp
    ring


end ChartRecord


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


open LocalPresentation WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- **([hArb] THE CONDITIONAL ASSEMBLY ★★★)** Modulo the two torsion→coordinate
bridges (`BRIDGE-P`: the `a₂`-obstruction of an origin-marked chart vanishes;
`BRIDGE-Q`: the flex-chart cubic at the second marked point — the KM-split content,
board v10.310), EVERY naive full level-`3` structure is an `ℰ₃`-datum: the marking
pipeline produces chart coordinates, translation and the `a₄`-shear normalize the
chart (the `a₃`-unit certificate powers the shear), `BRIDGE-P` kills `a₂`, and all
remaining `isE3Chart` inputs are proven (`isUnit_e3B` for the B-locus). -/
theorem isE3Datum_of_bridges {R : CommRingCat.{u}} (X : EllObj R)
    (hR : IsUnit (3 : R)) (L : X.curve.FullLevelPt 3)
    (bridgeP : ∀ (V : X.base.affineOpens)
      (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
      (_ : Pr.MarksAt L.1.1.2 0 0),
      Pr.W.a₂ * Pr.W.a₃ ^ 2 - Pr.W.a₄ * Pr.W.a₁ * Pr.W.a₃ - Pr.W.a₄ ^ 2 = 0)
    (bridgeQ : ∀ (V : X.base.affineOpens)
      (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
      (_ : Pr.W.a₂ = 0) (_ : Pr.W.a₄ = 0) (_ : Pr.W.a₆ = 0)
      (_ : Pr.MarksAt L.1.1.2 0 0) (p q : Γ(X.base, V.1))
      (_ : Pr.MarksAt L.1.2.2 p q),
      3 * p ^ 3 + Pr.W.a₁ ^ 2 * p ^ 2 + 3 * Pr.W.a₁ * Pr.W.a₃ * p
        + 3 * Pr.W.a₃ ^ 2 = 0) :
    IsE3Datum X L := by
  refine isE3Datum_of_flexCharts X L (fun s => ?_)
  classical
  -- the atlas chart at `s`
  obtain ⟨i, hsi⟩ := X.curve.toEllipticCurveGeom.atlas.covers s
  -- fibrewise nonvanishing of the two marked sections
  have hN : NIsInvertible X.base 3 := by
    have h0 : NIsInvertible (Spec R) 3 := by
      rw [NIsInvertible, Nat.cast_ofNat]
      have := hR.map (Scheme.ΓSpecIso R).inv.hom
      rwa [map_ofNat] at this
    exact h0.of_hom X.structMap
  have hneP := X.curve.pull_ne_zero_left_of_isNaiveFullLevel 3 (by norm_num) hN L.2
  have hneQ := X.curve.pull_ne_zero_right_of_isNaiveFullLevel 3 (by norm_num) hN L.2
  -- markings on the atlas chart
  obtain ⟨p₀, q₀, hMP₀⟩ :=
    (X.curve.toEllipticCurveGeom.atlas.presentation i).marksAt_of_forall_pull_ne_zero
      L.1.1.2 hneP
  obtain ⟨p₁, q₁, hMQ₀⟩ :=
    (X.curve.toEllipticCurveGeom.atlas.presentation i).marksAt_of_forall_pull_ne_zero
      L.1.2.2 hneQ
  -- translate `P` to the origin
  set C₁ : VariableChange ↑Γ(X.base, (X.curve.toEllipticCurveGeom.atlas.U i).1) :=
    ⟨1, p₀, 0, q₀⟩ with hC₁
  set Pr₁ := (X.curve.toEllipticCurveGeom.atlas.presentation i).ofVC C₁ with hPr₁
  have hMP₁ : Pr₁.MarksAt L.1.1.2 0 0 :=
    marksAt_origin_ofVC (X.curve.toEllipticCurveGeom.atlas.presentation i) hMP₀
  have hMQ₁ := marksAt_ofVC_vc (X.curve.toEllipticCurveGeom.atlas.presentation i)
    hMQ₀ C₁
  -- the section-level killing of `P`
  have hkillP : (3 : ℤ) • (⟨(L.1.1 : _ ⟶ _), L.1.1.2⟩ : X.curve.Section) = 0 := by
    have h := L.2.1.1
    exact_mod_cast h
  -- the `a₃`-unit on the origin-marked chart
  obtain ⟨heq₁, hMeq₁⟩ := id hMP₁
  have ha₃ : IsUnit Pr₁.W.a₃ :=
    isUnit_a₃_of_marked_origin Pr₁ heq₁ hMeq₁ hkillP hneP
  -- the `a₄`-killing shear
  set sSh : ↑Γ(X.base, (X.curve.toEllipticCurveGeom.atlas.U i).1) :=
    Pr₁.W.a₄ * ((ha₃.unit⁻¹ : _ˣ) : _) with hsSh
  set C₂ : VariableChange ↑Γ(X.base, (X.curve.toEllipticCurveGeom.atlas.U i).1) :=
    ⟨1, 0, sSh, 0⟩ with hC₂
  set Pr₂ := Pr₁.ofVC C₂ with hPr₂
  have hMP₂ : Pr₂.MarksAt L.1.1.2 0 0 := by
    have h := marksAt_ofVC_vc Pr₁ hMP₁ C₂
    have hx : C₂.vcX 0 = 0 := by
      simp [WeierstrassCurve.VariableChange.vcX, hC₂]
    have hy : C₂.vcY 0 0 = 0 := by
      simp [WeierstrassCurve.VariableChange.vcY, hC₂]
    rwa [hx, hy] at h
  have hMQ₂ := marksAt_ofVC_vc Pr₁ hMQ₁ C₂
  -- the chart coefficients
  have ha₃₂ : Pr₂.W.a₃ = Pr₁.W.a₃ := by
    show (C₂ • Pr₁.W).a₃ = Pr₁.W.a₃
    rw [WeierstrassCurve.variableChange_a₃]
    simp [hC₂]
  have ha₄₂ : Pr₂.W.a₄ = 0 := by
    show (C₂ • Pr₁.W).a₄ = 0
    rw [WeierstrassCurve.variableChange_a₄]
    simp only [hC₂, hsSh]
    rw [show ((⟨1, 0, sSh, 0⟩ : VariableChange _).u⁻¹ : _) = (1 : _ˣ) from by
      simp [hC₂]]
    push_cast
    rw [show Pr₁.W.a₄ - Pr₁.W.a₄ * ((ha₃.unit⁻¹ : _ˣ) : _) * Pr₁.W.a₃
        = Pr₁.W.a₄ * (1 - ((ha₃.unit⁻¹ : _ˣ) : _) * Pr₁.W.a₃) from by ring]
    rw [show ((ha₃.unit⁻¹ : _ˣ) : _) * Pr₁.W.a₃
        = ((ha₃.unit⁻¹ * ha₃.unit : _ˣ) : _) from by
      rw [Units.val_mul, IsUnit.unit_spec]]
    simp
  have ha₆₂ : Pr₂.W.a₆ = 0 := by
    obtain ⟨heq₂, -⟩ := id hMP₂
    exact (WeierstrassCurve.Affine.equation_zero).mp heq₂
  have ha₃u : IsUnit Pr₂.W.a₃ := by rw [ha₃₂]; exact ha₃
  have ha₂₂ : Pr₂.W.a₂ = 0 := by
    have hbr := bridgeP _ Pr₂ hMP₂
    rw [ha₄₂] at hbr
    have h2 : Pr₂.W.a₂ * Pr₂.W.a₃ ^ 2 = 0 := by linear_combination hbr
    exact ((ha₃u.pow 2).mul_left_eq_zero).mp h2
  -- the cubic (BRIDGE-Q)
  have hcubic := bridgeQ _ Pr₂ ha₂₂ ha₄₂ ha₆₂ hMP₂ _ _ hMQ₂
  -- `3` is a unit on the chart
  have h3V : IsUnit (3 : ↑Γ(X.base, (X.curve.toEllipticCurveGeom.atlas.U i).1)) := by
    have h1 := hR.map X.baseRingHom
    rw [map_ofNat] at h1
    have h2 := h1.map (Scheme.resLE
      (le_top : (X.curve.toEllipticCurveGeom.atlas.U i).1 ≤ ⊤))
    rwa [map_ofNat] at h2
  -- the B-locus unit (`isUnit_e3B`)
  obtain ⟨heqQ₂, -⟩ := id hMQ₂
  have hcurveQ : (C₂.vcY (C₁.vcX p₁) (C₁.vcY p₁ q₁)) ^ 2
      + Pr₂.W.a₁ * (C₂.vcX (C₁.vcX p₁)) * (C₂.vcY (C₁.vcX p₁) (C₁.vcY p₁ q₁))
      + Pr₂.W.a₃ * (C₂.vcY (C₁.vcX p₁) (C₁.vcY p₁ q₁))
      = (C₂.vcX (C₁.vcX p₁)) ^ 3 := by
    have h := (WeierstrassCurve.Affine.equation_iff _ _).mp heqQ₂
    rw [ha₂₂, ha₄₂, ha₆₂] at h
    linear_combination h
  have hfac : IsUnit (Pr₂.W.a₁ ^ 3 - 27 * Pr₂.W.a₃) := by
    have hΔ : Pr₂.W.Δ = Pr₂.W.a₃ ^ 3 * (Pr₂.W.a₁ ^ 3 - 27 * Pr₂.W.a₃) := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈, ha₂₂, ha₄₂, ha₆₂]
      ring
    have hu := (WeierstrassCurve.isElliptic_iff Pr₂.W).mp Pr₂.elliptic
    rw [hΔ] at hu
    exact isUnit_of_mul_isUnit_right hu
  have hB := isUnit_e3B (W := Pr₂.W) hcurveQ hcubic ha₃u h3V hfac
  exact ⟨_, hsi, Pr₂, _, _, ha₂₂, ha₄₂, ha₆₂, hMP₂, hMQ₂, hcubic, ha₃u, h3V, hB⟩

open WeierstrassCurve Polynomial in
/-- **([O2c] BRIDGE-P from `Ψ₃`)** On an `a₆ = 0` chart (P marked at the origin), the
`Ψ₃`-vanishing at `x = 0` IS the BRIDGE-P obstruction: `Ψ₃(0) = b₈ = a₂a₃² − a₁a₃a₄ − a₄²`. -/
theorem bridgeP_of_psi3_eval {A : Type u} [CommRing A] {W : WeierstrassCurve A}
    (ha₆ : W.a₆ = 0) (hψ : W.Ψ₃.eval 0 = 0) :
    W.a₂ * W.a₃ ^ 2 - W.a₄ * W.a₁ * W.a₃ - W.a₄ ^ 2 = 0 := by
  have h := hψ
  simp only [WeierstrassCurve.Ψ₃, eval_add, eval_mul, eval_pow, eval_ofNat, eval_C,
    eval_X, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, ha₆] at h
  linear_combination h

open WeierstrassCurve Polynomial in
/-- **([O2c] BRIDGE-Q from `Ψ₃`)** On a flex chart, `Ψ₃ = x · (the cubic)`, so
`Ψ₃`-vanishing at a UNIT abscissa gives the cubic. -/
theorem bridgeQ_of_psi3_eval {A : Type u} [CommRing A] {W : WeierstrassCurve A}
    (ha₂ : W.a₂ = 0) (ha₄ : W.a₄ = 0) (ha₆ : W.a₆ = 0) {p : A} (hp : IsUnit p)
    (hψ : W.Ψ₃.eval p = 0) :
    3 * p ^ 3 + W.a₁ ^ 2 * p ^ 2 + 3 * W.a₁ * W.a₃ * p + 3 * W.a₃ ^ 2 = 0 := by
  have hfac : W.Ψ₃.eval p = p * (3 * p ^ 3 + W.a₁ ^ 2 * p ^ 2
      + 3 * W.a₁ * W.a₃ * p + 3 * W.a₃ ^ 2) := by
    simp only [WeierstrassCurve.Ψ₃, eval_add, eval_mul, eval_pow, eval_ofNat, eval_C,
      eval_X, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, ha₂, ha₄, ha₆]
    ring
  rw [hfac] at hψ
  exact hp.mul_right_eq_zero.mp hψ


open WeierstrassCurve LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- **([O2b] the abscissa-unit certificate ★★)** On a chart marking `P` at the origin
and `Q` at `(p, q)`, if the pulled points satisfy `Q̄ ≠ ±P̄` at every geometric point,
then `p = x(Q)` is a unit: a vanishing fibre abscissa forces `q̄(q̄ + a₃̄) = 0` (the
`a₆ = 0` curve at `x = 0`), i.e. `Q̄ ∈ {P̄, −P̄}`. -/
theorem isUnit_x_of_marked_pair {S : Scheme.{u}} {E : EllipticCurve S}
    {V : S.affineOpens} (Pr : LocalPresentation E.toEllipticCurveGeom V)
    {σP : S ⟶ E.toEllipticCurveGeom.E} {hσP : σP ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    {σQ : S ⟶ E.toEllipticCurveGeom.E} {hσQ : σQ ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    (heqP : Pr.W.toAffine.Equation 0 0)
    (hMeqP : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσP V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W 0 0 heqP)
    {p q : Γ(S, V.1)} (heqQ : Pr.W.toAffine.Equation p q)
    (hMeqQ : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσQ V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W p q heqQ)
    (hpm : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      EllipticCurve.Point.pull E t ⟨σQ, hσQ⟩ ≠ EllipticCurve.Point.pull E t ⟨σP, hσP⟩ ∧
      EllipticCurve.Point.pull E t ⟨σQ, hσQ⟩ ≠ -EllipticCurve.Point.pull E t ⟨σP, hσP⟩) :
    IsUnit p := by
  letI := Pr.elliptic
  refine isUnit_of_forall_algebraMap_residueField_ne_zero (fun 𝔭 => ?_)
  intro hp0
  set K : Type u := 𝔭.asIdeal.ResidueField with hK
  set Kb : Type u := AlgebraicClosure K with hKb
  letI : DecidableEq Kb := Classical.decEq Kb
  letI : Algebra ↑Γ(S, V.1) Kb :=
    ((algebraMap K Kb).comp (algebraMap ↑Γ(S, V.1) K)).toAlgebra
  have halgKb : ∀ z : ↑Γ(S, V.1), algebraMap ↑Γ(S, V.1) Kb z =
      algebraMap K Kb (algebraMap ↑Γ(S, V.1) K z) := fun _ => rfl
  set tVb : Spec (CommRingCat.of Kb) ⟶ Spec Γ(S, V.1) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, V.1) Kb)) with htVb
  haveI : ((Pr.W.baseChange Kb)).IsElliptic :=
    inferInstanceAs ((Pr.W.map (algebraMap ↑Γ(S, V.1) Kb)).IsElliptic)
  have hnsP : (Pr.W.baseChange Kb).toAffine.Nonsingular
      (algebraMap ↑Γ(S, V.1) Kb 0) (algebraMap ↑Γ(S, V.1) Kb 0) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heqP)
  have hnsQ : (Pr.W.baseChange Kb).toAffine.Nonsingular
      (algebraMap ↑Γ(S, V.1) Kb p) (algebraMap ↑Γ(S, V.1) Kb q) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heqQ)
  have hvalP : modelPointAddEquiv Pr.W (K' := Kb)
      (chartPointsEquiv Pr tVb
        (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σP, hσP⟩))
      = WeierstrassCurve.Affine.Point.some _ _ hnsP := by
    have hxpkg : chartPointsEquiv Pr tVb
        (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σP, hσP⟩)
        = ⟨(affineSectionSpecPoint Pr.W Kb 0 0 heqP).1,
          (affineSectionSpecPoint Pr.W Kb 0 0 heqP).2⟩ := by
      refine Subtype.ext ?_
      rw [chartPointsEquiv_pull_marked Pr tVb heqP hMeqP]
      rfl
    rw [hxpkg]
    show projModelPointsEquiv Pr.W Kb (affineSectionSpecPoint Pr.W Kb 0 0 heqP) = _
    exact projModelPointsEquiv_affineSectionSpecPoint Pr.W 0 0 heqP hnsP
  have hvalQ : modelPointAddEquiv Pr.W (K' := Kb)
      (chartPointsEquiv Pr tVb
        (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σQ, hσQ⟩))
      = WeierstrassCurve.Affine.Point.some _ _ hnsQ := by
    have hxpkg : chartPointsEquiv Pr tVb
        (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σQ, hσQ⟩)
        = ⟨(affineSectionSpecPoint Pr.W Kb p q heqQ).1,
          (affineSectionSpecPoint Pr.W Kb p q heqQ).2⟩ := by
      refine Subtype.ext ?_
      rw [chartPointsEquiv_pull_marked Pr tVb heqQ hMeqQ]
      rfl
    rw [hxpkg]
    show projModelPointsEquiv Pr.W Kb (affineSectionSpecPoint Pr.W Kb p q heqQ) = _
    exact projModelPointsEquiv_affineSectionSpecPoint Pr.W p q heqQ hnsQ
  -- the vanishing abscissa and the `y`-quadratic
  have hpb : algebraMap ↑Γ(S, V.1) Kb p = 0 := by
    rw [halgKb, hp0, map_zero]
  have ha₆ : Pr.W.a₆ = 0 := WeierstrassCurve.Affine.equation_zero.mp heqP
  have hcurve := (WeierstrassCurve.Affine.equation_iff _ _).mp
    (WeierstrassCurve.Affine.Equation.map (algebraMap ↑Γ(S, V.1) Kb) heqQ)
  have hfactor : (algebraMap ↑Γ(S, V.1) Kb q) *
      (algebraMap ↑Γ(S, V.1) Kb q + algebraMap ↑Γ(S, V.1) Kb Pr.W.a₃) = 0 := by
    have h := hcurve
    rw [show (Pr.W.toAffine.map (algebraMap ↑Γ(S, V.1) Kb)).a₁
        = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₁ from rfl,
      show (Pr.W.toAffine.map (algebraMap ↑Γ(S, V.1) Kb)).a₂
        = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₂ from rfl,
      show (Pr.W.toAffine.map (algebraMap ↑Γ(S, V.1) Kb)).a₃
        = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₃ from rfl,
      show (Pr.W.toAffine.map (algebraMap ↑Γ(S, V.1) Kb)).a₄
        = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₄ from rfl,
      show (Pr.W.toAffine.map (algebraMap ↑Γ(S, V.1) Kb)).a₆
        = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₆ from rfl,
      ha₆, map_zero, hpb] at h
    linear_combination h
  obtain ⟨hne1, hne2⟩ := hpm Kb (tVb ≫ chartρ V)
  rcases mul_eq_zero.mp hfactor with hq0 | hqneg
  · -- `Q̄ = P̄`
    refine hne1 ?_
    refine (chartPointsEquiv Pr tVb).injective ?_
    apply (modelPointAddEquiv Pr.W (K' := Kb)).injective
    rw [hvalQ, hvalP]
    congr 1
    · exact hpb.trans (map_zero _).symm
    · exact hq0.trans (map_zero _).symm
  · -- `Q̄ = −P̄`
    have hqval : algebraMap ↑Γ(S, V.1) Kb q =
        -(algebraMap ↑Γ(S, V.1) Kb Pr.W.a₃) := by
      linear_combination hqneg
    refine hne2 ?_
    refine (chartPointsEquiv Pr tVb).injective ?_
    apply (modelPointAddEquiv Pr.W (K' := Kb)).injective
    rw [hvalQ, map_neg, map_neg, hvalP, WeierstrassCurve.Affine.Point.neg_some]
    congr 1
    · exact hpb.trans (map_zero _).symm
    · rw [hqval]
      show -(algebraMap ↑Γ(S, V.1) Kb Pr.W.a₃)
        = (Pr.W.baseChange Kb).toAffine.negY
          (algebraMap ↑Γ(S, V.1) Kb 0) (algebraMap ↑Γ(S, V.1) Kb 0)
      rw [WeierstrassCurve.Affine.negY]
      rw [show ((Pr.W.baseChange Kb)).toAffine.a₁
          = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₁ from rfl,
        show ((Pr.W.baseChange Kb)).toAffine.a₃
          = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₃ from rfl]
      rw [map_zero]
      ring



/-! ## The abscissa-difference unit certificate (LEAF-U's engine) -/

open WeierstrassCurve LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- **The general marked-pair abscissa-difference certificate.** On a chart marking `P`
at `(pP, qP)` and `Q` at `(pQ, qQ)`, if the pulled points satisfy `Q̄ ≠ ±P̄` at every
geometric point, then the abscissa difference `x(Q) − x(P) = pQ − pP` is a unit: a
vanishing fibre abscissa difference forces equal `X`-coordinates, so the two model points
are `±` (`Y_eq_of_X_eq`), contradicting the `±`-independence. This is the general-marking
analogue of `isUnit_x_of_marked_pair` (which pins `P` at the origin). -/
theorem isUnit_x_diff_of_marked_pair {S : Scheme.{u}} {E : EllipticCurve S}
    {V : S.affineOpens} (Pr : LocalPresentation E.toEllipticCurveGeom V)
    {σP : S ⟶ E.toEllipticCurveGeom.E} {hσP : σP ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    {σQ : S ⟶ E.toEllipticCurveGeom.E} {hσQ : σQ ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    {pP qP : Γ(S, V.1)} (heqP : Pr.W.toAffine.Equation pP qP)
    (hMeqP : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσP V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W pP qP heqP)
    {pQ qQ : Γ(S, V.1)} (heqQ : Pr.W.toAffine.Equation pQ qQ)
    (hMeqQ : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσQ V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W pQ qQ heqQ)
    (hpm : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      EllipticCurve.Point.pull E t ⟨σQ, hσQ⟩ ≠ EllipticCurve.Point.pull E t ⟨σP, hσP⟩ ∧
      EllipticCurve.Point.pull E t ⟨σQ, hσQ⟩ ≠ -EllipticCurve.Point.pull E t ⟨σP, hσP⟩) :
    IsUnit (pQ - pP) := by
  letI := Pr.elliptic
  refine isUnit_of_forall_algebraMap_residueField_ne_zero (fun 𝔭 => ?_)
  intro hp0
  set K : Type u := 𝔭.asIdeal.ResidueField with hK
  set Kb : Type u := AlgebraicClosure K with hKb
  letI : DecidableEq Kb := Classical.decEq Kb
  letI : Algebra ↑Γ(S, V.1) Kb :=
    ((algebraMap K Kb).comp (algebraMap ↑Γ(S, V.1) K)).toAlgebra
  have halgKb : ∀ z : ↑Γ(S, V.1), algebraMap ↑Γ(S, V.1) Kb z =
      algebraMap K Kb (algebraMap ↑Γ(S, V.1) K z) := fun _ => rfl
  set tVb : Spec (CommRingCat.of Kb) ⟶ Spec Γ(S, V.1) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, V.1) Kb)) with htVb
  haveI : ((Pr.W.baseChange Kb)).IsElliptic :=
    inferInstanceAs ((Pr.W.map (algebraMap ↑Γ(S, V.1) Kb)).IsElliptic)
  have hnsP : (Pr.W.baseChange Kb).toAffine.Nonsingular
      (algebraMap ↑Γ(S, V.1) Kb pP) (algebraMap ↑Γ(S, V.1) Kb qP) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heqP)
  have hnsQ : (Pr.W.baseChange Kb).toAffine.Nonsingular
      (algebraMap ↑Γ(S, V.1) Kb pQ) (algebraMap ↑Γ(S, V.1) Kb qQ) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heqQ)
  have hvalP : modelPointAddEquiv Pr.W (K' := Kb)
      (chartPointsEquiv Pr tVb
        (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σP, hσP⟩))
      = WeierstrassCurve.Affine.Point.some _ _ hnsP := by
    have hxpkg : chartPointsEquiv Pr tVb
        (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σP, hσP⟩)
        = ⟨(affineSectionSpecPoint Pr.W Kb pP qP heqP).1,
          (affineSectionSpecPoint Pr.W Kb pP qP heqP).2⟩ := by
      refine Subtype.ext ?_
      rw [chartPointsEquiv_pull_marked Pr tVb heqP hMeqP]
      rfl
    rw [hxpkg]
    show projModelPointsEquiv Pr.W Kb (affineSectionSpecPoint Pr.W Kb pP qP heqP) = _
    exact projModelPointsEquiv_affineSectionSpecPoint Pr.W pP qP heqP hnsP
  have hvalQ : modelPointAddEquiv Pr.W (K' := Kb)
      (chartPointsEquiv Pr tVb
        (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σQ, hσQ⟩))
      = WeierstrassCurve.Affine.Point.some _ _ hnsQ := by
    have hxpkg : chartPointsEquiv Pr tVb
        (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σQ, hσQ⟩)
        = ⟨(affineSectionSpecPoint Pr.W Kb pQ qQ heqQ).1,
          (affineSectionSpecPoint Pr.W Kb pQ qQ heqQ).2⟩ := by
      refine Subtype.ext ?_
      rw [chartPointsEquiv_pull_marked Pr tVb heqQ hMeqQ]
      rfl
    rw [hxpkg]
    show projModelPointsEquiv Pr.W Kb (affineSectionSpecPoint Pr.W Kb pQ qQ heqQ) = _
    exact projModelPointsEquiv_affineSectionSpecPoint Pr.W pQ qQ heqQ hnsQ
  -- equal abscissae at the residue field (from the vanishing difference)
  have hxeq : algebraMap ↑Γ(S, V.1) Kb pP = algebraMap ↑Γ(S, V.1) Kb pQ := by
    have h0 : algebraMap ↑Γ(S, V.1) Kb (pQ - pP) = 0 := by
      rw [halgKb, hp0, map_zero]
    rw [map_sub, sub_eq_zero] at h0
    exact h0.symm
  obtain ⟨hne1, hne2⟩ := hpm Kb (tVb ≫ chartρ V)
  -- the `Y`-dichotomy from `Y_eq_of_X_eq`
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq
      (WeierstrassCurve.Affine.Equation.map (algebraMap ↑Γ(S, V.1) Kb) heqP)
      (WeierstrassCurve.Affine.Equation.map (algebraMap ↑Γ(S, V.1) Kb) heqQ)
      hxeq with hYeq | hYneg
  · -- `Q̄ = P̄`
    refine hne1 ?_
    refine (chartPointsEquiv Pr tVb).injective ?_
    apply (modelPointAddEquiv Pr.W (K' := Kb)).injective
    rw [hvalQ, hvalP]
    congr 1
    · exact hxeq.symm
    · exact hYeq.symm
  · -- `Q̄ = −P̄`
    refine hne2 ?_
    refine (chartPointsEquiv Pr tVb).injective ?_
    apply (modelPointAddEquiv Pr.W (K' := Kb)).injective
    rw [hvalQ, map_neg, map_neg, hvalP, WeierstrassCurve.Affine.Point.neg_some]
    congr 1
    · exact hxeq.symm
    · rw [hxeq, hYneg]
      exact (WeierstrassCurve.Affine.negY_negY _ _).symm

end ModularCurves
