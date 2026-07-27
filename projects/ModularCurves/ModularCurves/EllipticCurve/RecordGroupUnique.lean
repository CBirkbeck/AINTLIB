/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.GroupLaw
import ModularCurves.EllipticCurve.ModelGroupUniq
import ModularCurves.EllipticCurve.WeierstrassAtlasBundle
import ModularCurves.ForMathlib.OverPullbackMul

/-!
# Uniqueness of the pointed group structure on a locally Weierstrass record (K3)

The records-level canonicity primitive: on a geometric elliptic curve record
(`EllipticCurveGeom`, whose defining `localModel` field says the curve is Zariski-locally
on the base a projective Weierstrass model), any two group-object structures with the zero
section as unit have the same multiplication — over an **arbitrary** base scheme.

The proof is chart-local: equality of morphisms into a scheme is Zariski-local on the
source (`Scheme.hom_ext_of_forall`), each chart base-changes the two structures to the
model over the affine chart ring (`Over.grpObjMkPullbackSnd`), the pointed chart
isomorphism transports them onto `modelOver W` (`GrpObj.ofIso`), and the model-level
uniqueness `modelGrpObj_unique` ([U-MODEL], `ModelGroupUniq.lean`) collapses both to the
T-G4 multiplication `mulOver W`.

Downstream (K4): the pointed-isomorphism corollary `isMonHom_of_pointedIso_records`
supplies the `h64`/`hμ` arguments of `transportSection_add_of_finitePresentation` and the
`IsoTransport` lemmas, replacing the sorried route (a) primitive
(`isMonHom_of_one_comp_eq'_of_finitePresentation`) on the MASTER trail.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj WeierstrassCurve

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

variable {S : Scheme.{u}} {G : EllipticCurveGeom S} (A : WeierstrassAtlasData G)

/-! ## Chart geometry -/

section ChartGeometry

/-- The chart base morphism `Spec Γ(S, U i) ⟶ S`. -/
noncomputable def chartToBase (i : A.ι) : Spec Γ(S, (A.U i).1) ⟶ S :=
  (A.U i).2.isoSpec.inv ≫ (A.U i).1.ι

/-- The base change of the record total space along the chart base agrees with the base
change along the open inclusion. -/
noncomputable def chartLegIso (i : A.ι) :
    pullback G.π (chartToBase A i) ≅ pullback G.π (A.U i).1.ι where
  hom := pullback.map _ _ _ _ (𝟙 _) (A.U i).2.isoSpec.inv (𝟙 S)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id]; rfl)
  inv := pullback.map _ _ _ _ (𝟙 _) (A.U i).2.isoSpec.hom (𝟙 S)
    (by rw [Category.comp_id, Category.id_comp])
    (by
      rw [Category.comp_id]
      show (A.U i).1.ι = (A.U i).2.isoSpec.hom ≫ (A.U i).2.isoSpec.inv ≫ (A.U i).1.ι
      rw [Iso.hom_inv_id_assoc])
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst]
      simp only [Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst]
      simp only [Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]

/-- The chart total isomorphism: the chart base change of the record is the projective
model of the chart Weierstrass curve. -/
noncomputable def chartTotalIso (i : A.ι) :
    pullback G.π (chartToBase A i) ≅ projModel (A.W i) :=
  chartLegIso A i ≪≫ A.e i

/-- Component laws of the leg isomorphism. -/
theorem chartLegIso_hom_fst (i : A.ι) :
    (chartLegIso A i).hom ≫ pullback.fst G.π (A.U i).1.ι =
      pullback.fst G.π (chartToBase A i) ≫ 𝟙 G.E :=
  pullback.lift_fst _ _ _

theorem chartLegIso_hom_snd (i : A.ι) :
    (chartLegIso A i).hom ≫ pullback.snd G.π (A.U i).1.ι =
      pullback.snd G.π (chartToBase A i) ≫ (A.U i).2.isoSpec.inv :=
  pullback.lift_snd _ _ _

/-- The chart total isomorphism respects the structure morphisms. -/
theorem chartTotalIso_π (i : A.ι) :
    haveI := A.elliptic i
    (chartTotalIso A i).hom ≫ projModelπ (A.W i) =
      pullback.snd G.π (chartToBase A i) := by
  show ((chartLegIso A i).hom ≫ (A.e i).hom) ≫ projModelπ (A.W i) = _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((chartLegIso A i).hom ≫ ·) (A.compat_π i)).trans ?_
  refine ((Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (· ≫ (A.U i).2.isoSpec.hom) (chartLegIso_hom_snd A i)).trans ?_
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The lifted zero section of the chart base change. -/
noncomputable def chartZero (i : A.ι) :
    Spec Γ(S, (A.U i).1) ⟶ pullback G.π (chartToBase A i) :=
  pullback.lift (chartToBase A i ≫ G.zero) (𝟙 _)
    (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])

theorem chartZero_fst (i : A.ι) :
    chartZero A i ≫ pullback.fst G.π (chartToBase A i) = chartToBase A i ≫ G.zero :=
  pullback.lift_fst _ _ _

theorem chartZero_snd (i : A.ι) :
    chartZero A i ≫ pullback.snd G.π (chartToBase A i) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The chart total isomorphism respects the zero sections. -/
theorem chartZero_totalIso (i : A.ι) :
    haveI := A.elliptic i
    chartZero A i ≫ (chartTotalIso A i).hom = projModelZero (A.W i) := by
  have hfac : chartZero A i ≫ (chartLegIso A i).hom =
      (A.U i).2.isoSpec.inv ≫ pullback.lift ((A.U i).1.ι ≫ G.zero) (𝟙 _)
        (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp]) := by
    refine pullback.hom_ext ?_ ?_
    · have hA : (chartZero A i ≫ (chartLegIso A i).hom) ≫
          pullback.fst G.π (A.U i).1.ι =
          (A.U i).2.isoSpec.inv ≫ ((A.U i).1.ι ≫ G.zero) := by
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (chartZero A i ≫ ·) (chartLegIso_hom_fst A i)).trans ?_
        refine (congrArg (chartZero A i ≫ ·) (Category.comp_id _)).trans ?_
        refine (chartZero_fst A i).trans ?_
        show ((A.U i).2.isoSpec.inv ≫ (A.U i).1.ι) ≫ G.zero = _
        exact Category.assoc _ _ _
      have hB : ((A.U i).2.isoSpec.inv ≫ pullback.lift ((A.U i).1.ι ≫ G.zero) (𝟙 _)
            (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])) ≫
          pullback.fst G.π (A.U i).1.ι =
          (A.U i).2.isoSpec.inv ≫ ((A.U i).1.ι ≫ G.zero) := by
        refine (Category.assoc _ _ _).trans ?_
        exact congrArg ((A.U i).2.isoSpec.inv ≫ ·) (pullback.lift_fst _ _ _)
      exact hA.trans hB.symm
    · have hA : (chartZero A i ≫ (chartLegIso A i).hom) ≫
          pullback.snd G.π (A.U i).1.ι = (A.U i).2.isoSpec.inv := by
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (chartZero A i ≫ ·) (chartLegIso_hom_snd A i)).trans ?_
        refine ((Category.assoc _ _ _).symm).trans ?_
        refine (congrArg (· ≫ (A.U i).2.isoSpec.inv) (chartZero_snd A i)).trans ?_
        exact Category.id_comp _
      have hB : ((A.U i).2.isoSpec.inv ≫ pullback.lift ((A.U i).1.ι ≫ G.zero) (𝟙 _)
            (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])) ≫
          pullback.snd G.π (A.U i).1.ι = (A.U i).2.isoSpec.inv := by
        refine (Category.assoc _ _ _).trans ?_
        refine (congrArg ((A.U i).2.isoSpec.inv ≫ ·) (pullback.lift_snd _ _ _)).trans ?_
        exact Category.comp_id _
      exact hA.trans hB.symm
  show chartZero A i ≫ ((chartLegIso A i).hom ≫ (A.e i).hom) = _
  refine ((Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (· ≫ (A.e i).hom) hfac).trans ?_
  exact A.compat_zero i

end ChartGeometry

/-! ## Chart transport of the group structures -/

section ChartTransport

/-- The chart base change of the record, as an object of `Over (Spec Γ(U i))`. -/
noncomputable abbrev chartOver (i : A.ι) : Over (Spec Γ(S, (A.U i).1)) :=
  Over.mk (pullback.snd G.π (chartToBase A i))

/-- The pointed chart isomorphism in the over category. -/
noncomputable def chartOverIso (i : A.ι) :
    haveI := A.elliptic i
    chartOver A i ≅ modelOver (A.W i) :=
  haveI := A.elliptic i
  Over.isoMk (chartTotalIso A i) (chartTotalIso_π A i)

/-- The base-changed group structure on the chart. -/
noncomputable abbrev bcGrp (Gj : GrpObj (Over.mk G.π)) (i : A.ι) :
    GrpObj (chartOver A i) :=
  letI := Gj
  Over.grpObjMkPullbackSnd

/-- The unit of the base-changed structure is the lifted zero section. -/
theorem bcGrp_one_left (Gj : GrpObj (Over.mk G.π))
    (hj : (letI := Gj; (η[Over.mk G.π] : 𝟙_ (Over S) ⟶ Over.mk G.π).left) =
      (𝟙_ (Over S)).hom ≫ G.zero) (i : A.ι) :
    (letI := bcGrp A Gj i;
      (η[chartOver A i] : 𝟙_ (Over (Spec Γ(S, (A.U i).1))) ⟶ chartOver A i).left) =
    (𝟙_ (Over (Spec Γ(S, (A.U i).1)))).hom ≫ chartZero A i := by
  letI := Gj
  apply pullback.hom_ext
  all_goals dsimp [Over.grpObjMkPullbackSnd_one]
  all_goals simp only [Over.grpObjMkPullbackSnd_one, Over.pullback, Over.comp_left,
    Over.homMk_left, Category.id_comp, hj]
  all_goals
    have hε2 : (Functor.LaxMonoidal.ε (Over.pullback (chartToBase A i))).left ≫
        pullback.snd (𝟙 S) (chartToBase A i) = 𝟙 _ := Over.w _
  · have hε1 : (Functor.LaxMonoidal.ε (Over.pullback (chartToBase A i))).left ≫
        pullback.fst (𝟙 S) (chartToBase A i) = chartToBase A i := by
      have hc : pullback.fst (𝟙 S) (chartToBase A i) =
          pullback.snd (𝟙 S) (chartToBase A i) ≫ chartToBase A i := by
        simpa using pullback.condition (f := 𝟙 S) (g := chartToBase A i)
      calc (Functor.LaxMonoidal.ε (Over.pullback (chartToBase A i))).left ≫
          pullback.fst (𝟙 S) (chartToBase A i)
          = (Functor.LaxMonoidal.ε (Over.pullback (chartToBase A i))).left ≫
            pullback.snd (𝟙 S) (chartToBase A i) ≫ chartToBase A i := congrArg
              (fun q => (Functor.LaxMonoidal.ε (Over.pullback (chartToBase A i))).left ≫ q)
              hc
        _ = ((Functor.LaxMonoidal.ε (Over.pullback (chartToBase A i))).left ≫
            pullback.snd (𝟙 S) (chartToBase A i)) ≫ chartToBase A i :=
            (Category.assoc _ _ _).symm
        _ = 𝟙 _ ≫ chartToBase A i := congrArg (· ≫ chartToBase A i) hε2
        _ = chartToBase A i := Category.id_comp _
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg
      (fun q => (Functor.LaxMonoidal.ε (Over.pullback (chartToBase A i))).left ≫ q)
      (pullback.lift_fst _ _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (· ≫ G.zero) hε1) ?_
    exact (chartZero_fst A i).symm
  · refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg
      (fun q => (Functor.LaxMonoidal.ε (Over.pullback (chartToBase A i))).left ≫ q)
      (pullback.lift_snd _ _ _)) ?_
    exact hε2.trans (chartZero_snd A i).symm

/-- The chart-transported group structure on the projective model. -/
noncomputable abbrev chartGrp (Gj : GrpObj (Over.mk G.π)) (i : A.ι) :
    haveI := A.elliptic i
    GrpObj (modelOver (A.W i)) :=
  haveI := A.elliptic i
  letI := bcGrp A Gj i
  GrpObj.ofIso (chartOverIso A i)

/-- The transported structure is pointed by the model zero section. -/
theorem chartGrp_one (Gj : GrpObj (Over.mk G.π))
    (hj : (letI := Gj; (η[Over.mk G.π] : 𝟙_ (Over S) ⟶ Over.mk G.π).left) =
      (𝟙_ (Over S)).hom ≫ G.zero) (i : A.ι) :
    haveI := A.elliptic i
    (letI := chartGrp A Gj i;
      (η[modelOver (A.W i)] : 𝟙_ (Over (Spec (CommRingCat.of Γ(S, (A.U i).1)))) ⟶
        modelOver (A.W i))) = oneOver (A.W i) := by
  haveI := A.elliptic i
  letI := bcGrp A Gj i
  apply Over.OverMorphism.ext
  show ((η[chartOver A i] : 𝟙_ _ ⟶ chartOver A i) ≫ (chartOverIso A i).hom).left =
    (oneOver (A.W i)).left
  show (η[chartOver A i] : 𝟙_ _ ⟶ chartOver A i).left ≫ (chartTotalIso A i).hom =
    (oneOver (A.W i)).left
  rw [bcGrp_one_left A Gj hj i, oneOver_left]
  show (𝟙 _ ≫ chartZero A i) ≫ (chartTotalIso A i).hom = _
  rw [Category.id_comp, chartZero_totalIso A i]
  show projModelZero (A.W i) = 𝟙 _ ≫ projModelZero (A.W i)
  rw [Category.id_comp]

/-- **(K3 chart step)** The two base-changed multiplications agree on every chart: both
transport to pointed group structures on the projective model, where [U-MODEL]
(`modelGrpObj_unique`) pins each to the T-G4 multiplication. -/
theorem chart_mul_eq (G₁ G₂ : GrpObj (Over.mk G.π))
    (h₁ : (letI := G₁; (η[Over.mk G.π] : 𝟙_ (Over S) ⟶ Over.mk G.π).left) =
      (𝟙_ (Over S)).hom ≫ G.zero)
    (h₂ : (letI := G₂; (η[Over.mk G.π] : 𝟙_ (Over S) ⟶ Over.mk G.π).left) =
      (𝟙_ (Over S)).hom ≫ G.zero) (i : A.ι) :
    (letI := bcGrp A G₁ i;
      (μ[chartOver A i] : chartOver A i ⊗ chartOver A i ⟶ chartOver A i)) =
    (letI := bcGrp A G₂ i;
      (μ[chartOver A i] : chartOver A i ⊗ chartOver A i ⟶ chartOver A i)) := by
  haveI := A.elliptic i
  have key : ∀ (Gj : GrpObj (Over.mk G.π)),
      (letI := Gj; (η[Over.mk G.π] : 𝟙_ (Over S) ⟶ Over.mk G.π).left) =
        (𝟙_ (Over S)).hom ≫ G.zero →
      (letI := bcGrp A Gj i;
        (μ[chartOver A i] : chartOver A i ⊗ chartOver A i ⟶ chartOver A i)) =
      ((chartOverIso A i).hom ⊗ₘ (chartOverIso A i).hom) ≫ mulOver (A.W i) ≫
        (chartOverIso A i).inv := by
    intro Gj hj
    letI := bcGrp A Gj i
    have hmodel : (letI := chartGrp A Gj i;
        (μ[modelOver (A.W i)] : modelOver (A.W i) ⊗ modelOver (A.W i) ⟶
          modelOver (A.W i))) = mulOver (A.W i) :=
      modelGrpObj_unique (A.W i) (chartGrp A Gj i) (chartGrp_one A Gj hj i)
    have hofiso : (letI := chartGrp A Gj i;
        (μ[modelOver (A.W i)] : modelOver (A.W i) ⊗ modelOver (A.W i) ⟶
          modelOver (A.W i))) =
        ((chartOverIso A i).inv ⊗ₘ (chartOverIso A i).inv) ≫
          (μ[chartOver A i] : chartOver A i ⊗ chartOver A i ⟶ chartOver A i) ≫
          (chartOverIso A i).hom := rfl
    have h := hofiso.symm.trans hmodel
    have h2 := congrArg (fun m => ((chartOverIso A i).hom ⊗ₘ (chartOverIso A i).hom) ≫
      m ≫ (chartOverIso A i).inv) h
    simp only [← Category.assoc] at h2
    rw [tensorHom_comp_tensorHom, Iso.hom_inv_id, id_tensorHom_id, Category.id_comp,
      Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h2
    exact h2
  exact (key G₁ h₁).trans (key G₂ h₂).symm

end ChartTransport

/-! ## The chart restriction of the square -/

section ChartSquare

/-- The chart square comparison: the base-changed square maps to the record square. -/
noncomputable def chartSqCmp (i : A.ι) :
    pullback (pullback.snd G.π (chartToBase A i)) (pullback.snd G.π (chartToBase A i)) ⟶
    pullback G.π G.π :=
  pullback.lift
    (pullback.fst (pullback.snd G.π (chartToBase A i))
      (pullback.snd G.π (chartToBase A i)) ≫ pullback.fst G.π (chartToBase A i))
    (pullback.snd (pullback.snd G.π (chartToBase A i))
      (pullback.snd G.π (chartToBase A i)) ≫ pullback.fst G.π (chartToBase A i))
    (by
      simp only [Category.assoc]
      rw [pullback.condition (f := G.π) (g := chartToBase A i), ← Category.assoc,
        pullback.condition (f := pullback.snd G.π (chartToBase A i))
          (g := pullback.snd G.π (chartToBase A i)), Category.assoc])

/-- Chart evaluation of a base-changed multiplication: through the comparison, the
record multiplication restricts to the base-changed one. -/
theorem chartSqCmp_mul (Gj : GrpObj (Over.mk G.π)) (i : A.ι) :
    chartSqCmp A i ≫ (letI := Gj;
      (μ[Over.mk G.π] : Over.mk G.π ⊗ Over.mk G.π ⟶ Over.mk G.π)).left =
    (letI := bcGrp A Gj i;
      (μ[chartOver A i] : chartOver A i ⊗ chartOver A i ⟶ chartOver A i)).left ≫
      pullback.fst G.π (chartToBase A i) := by
  letI := Gj
  have h := Over.grpObjMkPullbackSnd_mul_left_fst G.π (chartToBase A i)
  exact h.symm

/-- The chart open of the record square: pairs lying over the chart. -/
noncomputable def chartOpen (i : A.ι) : (pullback G.π G.π).Opens :=
  (pullback.fst G.π G.π ≫ G.π) ⁻¹ᵁ (A.U i).1

/-- The chart section of the square open into the chart base. -/
noncomputable def chartOpenToBase (i : A.ι) :
    ((chartOpen A i : (pullback G.π G.π).Opens) : Scheme) ⟶ Spec Γ(S, (A.U i).1) :=
  ((pullback.fst G.π G.π ≫ G.π) ∣_ (A.U i).1) ≫ (A.U i).2.isoSpec.hom

theorem chartOpenToBase_w (i : A.ι) :
    chartOpenToBase A i ≫ chartToBase A i =
    (chartOpen A i).ι ≫ pullback.fst G.π G.π ≫ G.π := by
  show (((pullback.fst G.π G.π ≫ G.π) ∣_ (A.U i).1) ≫ (A.U i).2.isoSpec.hom) ≫
    ((A.U i).2.isoSpec.inv ≫ (A.U i).1.ι) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]
  rfl

/-- The chart restriction of the record square into the base-changed square. -/
noncomputable def chartRestrict (i : A.ι) :
    ((chartOpen A i : (pullback G.π G.π).Opens) : Scheme) ⟶
    pullback (pullback.snd G.π (chartToBase A i)) (pullback.snd G.π (chartToBase A i)) :=
  pullback.lift
    (pullback.lift ((chartOpen A i).ι ≫ pullback.fst G.π G.π) (chartOpenToBase A i)
      (by rw [chartOpenToBase_w, Category.assoc]))
    (pullback.lift ((chartOpen A i).ι ≫ pullback.snd G.π G.π) (chartOpenToBase A i)
      (by rw [chartOpenToBase_w, Category.assoc, ← pullback.condition]))
    (by rw [pullback.lift_snd, pullback.lift_snd])

/-- The chart restriction factors the open inclusion through the comparison. -/
theorem chartRestrict_cmp (i : A.ι) :
    chartRestrict A i ≫ chartSqCmp A i = (chartOpen A i).ι := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc]
    show chartRestrict A i ≫ chartSqCmp A i ≫ pullback.fst G.π G.π = _
    rw [chartSqCmp, pullback.lift_fst, ← Category.assoc, chartRestrict,
      pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc]
    show chartRestrict A i ≫ chartSqCmp A i ≫ pullback.snd G.π G.π = _
    rw [chartSqCmp, pullback.lift_snd, ← Category.assoc, chartRestrict,
      pullback.lift_snd, pullback.lift_fst]

/-- The per-chart agreement of the two multiplications, restricted to the chart open. -/
theorem chartOpen_mul_eq (G₁ G₂ : GrpObj (Over.mk G.π))
    (h₁ : (letI := G₁; (η[Over.mk G.π] : 𝟙_ (Over S) ⟶ Over.mk G.π).left) =
      (𝟙_ (Over S)).hom ≫ G.zero)
    (h₂ : (letI := G₂; (η[Over.mk G.π] : 𝟙_ (Over S) ⟶ Over.mk G.π).left) =
      (𝟙_ (Over S)).hom ≫ G.zero) (i : A.ι) :
    (chartOpen A i).ι ≫ (letI := G₁;
      (μ[Over.mk G.π] : Over.mk G.π ⊗ Over.mk G.π ⟶ Over.mk G.π)).left =
    (chartOpen A i).ι ≫ (letI := G₂;
      (μ[Over.mk G.π] : Over.mk G.π ⊗ Over.mk G.π ⟶ Over.mk G.π)).left := by
  have hchain : ∀ (Gj : GrpObj (Over.mk G.π)),
      (chartOpen A i).ι ≫ (letI := Gj;
        (μ[Over.mk G.π] : Over.mk G.π ⊗ Over.mk G.π ⟶ Over.mk G.π)).left =
      chartRestrict A i ≫ ((letI := bcGrp A Gj i;
        (μ[chartOver A i] : chartOver A i ⊗ chartOver A i ⟶ chartOver A i)).left ≫
        pullback.fst G.π (chartToBase A i)) := by
    intro Gj
    have h1 := chartSqCmp_mul A Gj i
    have h2 := congrArg (chartRestrict A i ≫ ·) h1
    have h3 := congrArg (· ≫ (letI := Gj;
      (μ[Over.mk G.π] : Over.mk G.π ⊗ Over.mk G.π ⟶ Over.mk G.π)).left)
      (chartRestrict_cmp A i).symm
    exact h3.trans ((Category.assoc _ _ _).trans h2)
  have hmul := chart_mul_eq A G₁ G₂ h₁ h₂ i
  have hml := congrArg (fun m => chartRestrict A i ≫
    (Over.Hom.left m ≫ pullback.fst G.π (chartToBase A i))) hmul
  exact (hchain G₁).trans (hml.trans (hchain G₂).symm)

end ChartSquare

/-! ## The glue: uniqueness over the arbitrary base -/

section Unique

/-- **(K3, the records-level [U-MODEL])** Any two group-object structures on a geometric
elliptic curve record with the zero section as unit have the same multiplication — over an
arbitrary base scheme. Chart-locally both transport to the projective model, where
`modelGrpObj_unique` pins each to the T-G4 multiplication; equality of scheme morphisms is
Zariski-local on the source. -/
theorem grpObj_mul_unique {S : Scheme.{u}} (G : EllipticCurveGeom S)
    (G₁ G₂ : GrpObj (Over.mk G.π))
    (h₁ : (letI := G₁; (η[Over.mk G.π] : 𝟙_ (Over S) ⟶ Over.mk G.π).left) =
      (𝟙_ (Over S)).hom ≫ G.zero)
    (h₂ : (letI := G₂; (η[Over.mk G.π] : 𝟙_ (Over S) ⟶ Over.mk G.π).left) =
      (𝟙_ (Over S)).hom ≫ G.zero) :
    (letI := G₁; (μ[Over.mk G.π] : Over.mk G.π ⊗ Over.mk G.π ⟶ Over.mk G.π)) =
    (letI := G₂; (μ[Over.mk G.π] : Over.mk G.π ⊗ Over.mk G.π ⟶ Over.mk G.π)) := by
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ (fun x => ?_)
  obtain ⟨i, hi⟩ := (G.atlas).covers ((pullback.fst G.π G.π ≫ G.π).base x)
  exact ⟨chartOpen G.atlas i, hi, chartOpen_mul_eq G.atlas G₁ G₂ h₁ h₂ i⟩

end Unique

/-! ## The pointed-isomorphism corollary (the K4 supply) -/

section PointedIso

/-- **(K4 supply — the records-level canonicity primitive)** A pointed isomorphism of
working records is a homomorphism of their group structures: the transported structure
`GrpObj.ofIso` shares the unit with the target's, so the records-level [U-MODEL]
(`grpObj_mul_unique`) identifies the multiplications, and conjugating back gives the
`IsMonHom` equation. This replaces the sorried route (a) primitive
(`isMonHom_of_one_comp_eq'_of_finitePresentation`) at its MASTER-trail consumption sites. -/
theorem isMonHom_of_pointedIso_records {S : Scheme.{u}}
    (E E' : EllipticCurve S) (e : E.asOver ≅ E'.asOver)
    (hη : (η[E.asOver] : 𝟙_ (Over S) ⟶ E.asOver) ≫ e.hom = η[E'.asOver]) :
    (μ[E.asOver] : E.asOver ⊗ E.asOver ⟶ E.asOver) ≫ e.hom =
      MonoidalCategory.tensorHom e.hom e.hom ≫
        (μ[E'.asOver] : E'.asOver ⊗ E'.asOver ⟶ E'.asOver) := by
  letI Gt : GrpObj E'.asOver := GrpObj.ofIso e
  have ht : (letI := Gt;
      (η[E'.asOver] : 𝟙_ (Over S) ⟶ E'.asOver).left) =
      (𝟙_ (Over S)).hom ≫ E'.zero := by
    have h0 : (letI := Gt; (η[E'.asOver] : 𝟙_ (Over S) ⟶ E'.asOver)) =
        (η[E.asOver] : 𝟙_ (Over S) ⟶ E.asOver) ≫ e.hom := rfl
    rw [h0, hη]
    exact E'.one_eq_zero
  have h' : (letI := E'.grp;
      (η[E'.asOver] : 𝟙_ (Over S) ⟶ E'.asOver).left) =
      (𝟙_ (Over S)).hom ≫ E'.zero := E'.one_eq_zero
  have huniq := grpObj_mul_unique E'.toEllipticCurveGeom Gt E'.grp ht h'
  have hofiso : (letI := Gt;
      (μ[E'.asOver] : E'.asOver ⊗ E'.asOver ⟶ E'.asOver)) =
      (e.inv ⊗ₘ e.inv) ≫ (μ[E.asOver] : E.asOver ⊗ E.asOver ⟶ E.asOver) ≫ e.hom := rfl
  have hcon := hofiso.symm.trans huniq
  have h2 := congrArg (fun m => (e.hom ⊗ₘ e.hom) ≫ m) hcon
  rw [← Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id, id_tensorHom_id,
    Category.id_comp] at h2
  exact h2

end PointedIso



end ModularCurves
