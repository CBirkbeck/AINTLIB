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


end ModularCurves
