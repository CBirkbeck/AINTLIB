import ModularCurves.GroupScheme.PatchHopf
import ModularCurves.ForMathlib.Coaction
import ModularCurves.ForMathlib.BaseChangeAlongCompat

/-!
# The chart co-action is a co-action

`[HG-C1d]`: the chart co-action `chartCoaction : B →ₐ[R] B ⊗[R] A` (`StableCharts.lean`) satisfies
the two `IsCoaction` axioms (`ForMathlib/Coaction.lean`) with respect to the chart Hopf-algebra
bialgebra structure `instBialgebraOpens` (`PatchHopf.lean`). The two axioms are the `Γ`-duals of the
two group-action laws `translationAction_unit` / `translationAction_assoc`
(`SubgroupGroupObject.lean`), mirroring the Hopf coassoc/counit development in `PatchHopf.lean`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 5

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} {E : EllipticCurve S}

namespace FiniteLocallyFreeSubgroup

namespace AffineChartPatch

variable {G : FiniteLocallyFreeSubgroup E} (P : G.AffineChartPatch)

/-! ### The counit law, geometric core -/

/-- The chart, as a scheme over `S` (via `U ↪ E → S`). -/
noncomputable def chartOver : Over S := Over.mk (P.U.ι ≫ E.π)

/-- The chart inclusion `U ↪ E`, as a morphism over `S`. -/
noncomputable def chartIncl : P.chartOver ⟶ E.asOver := Over.homMk P.U.ι rfl

@[simp] theorem chartIncl_left : P.chartIncl.left = P.U.ι := rfl

/-- **The unit-insertion** `x ↦ (e, x) : U ⟶ G ×_S E`, as a morphism over `S`. -/
noncomputable def unitInsertOver : P.chartOver ⟶ (Over.mk G.π) ⊗ E.asOver :=
  lift (toUnit P.chartOver ≫ G.unitOver) P.chartIncl

/-- The unit-insertion, followed by the projection, is the inclusion. -/
theorem unitInsertOver_actionProj :
    P.unitInsertOver ≫ G.actionProj = P.chartIncl := by
  rw [unitInsertOver, actionProj, lift_snd]

/-- **The unit-insertion, followed by the action, is the inclusion** — acting by the unit
does nothing. The `Γ`-dual of the counit axiom. Proved by precomposing `translationAction_unit`. -/
theorem unitInsertOver_translationAction :
    P.unitInsertOver ≫ G.translationAction = P.chartIncl := by
  have h : P.unitInsertOver = lift (toUnit P.chartOver) P.chartIncl ≫ (G.unitOver ⊗ₘ 𝟙 E.asOver) := by
    rw [unitInsertOver, lift_map, Category.comp_id]
  rw [h, Category.assoc, G.translationAction_unit, leftUnitor_hom, lift_snd]

/-- Underlying-scheme form: `unitInsert ≫ pr = U.ι`. -/
theorem unitInsertOver_left_actionProj :
    P.unitInsertOver.left ≫ G.actionProj.left = P.U.ι := by
  rw [← Over.comp_left, P.unitInsertOver_actionProj, chartIncl_left]

/-- Underlying-scheme form: `unitInsert ≫ act = U.ι`. -/
theorem unitInsertOver_left_translationAction :
    P.unitInsertOver.left ≫ G.translationAction.left = P.U.ι := by
  rw [← Over.comp_left, P.unitInsertOver_translationAction, chartIncl_left]

/-- The unit-insertion factors through the restricted-action domain `pr⁻¹U`, as a section
`U ⟶ pr⁻¹U` (via the pullback presentation of the domain). -/
noncomputable def unitInsert :
    P.U.toScheme ⟶ (G.actionProj.left ⁻¹ᵁ P.U).toScheme :=
  pullback.lift P.unitInsertOver.left (𝟙 _)
    (P.unitInsertOver_left_actionProj.trans (Category.id_comp _).symm)
    ≫ (G.restrictedDomainIso P.U).inv

@[reassoc]
theorem unitInsert_comp_ι :
    P.unitInsert ≫ (G.actionProj.left ⁻¹ᵁ P.U).ι = P.unitInsertOver.left := by
  rw [unitInsert, Category.assoc,
    show (G.restrictedDomainIso P.U).inv ≫ (G.actionProj.left ⁻¹ᵁ P.U).ι
        = pullback.fst G.actionProj.left P.U.ι from
      pullbackRestrictIsoRestrict_hom_ι _ _,
    pullback.lift_fst]

/-- The restricted action, composed into the chart inclusion, is `pr⁻¹U ↪ G ×_S E` followed
by the action (`resLE_comp_ι`). -/
theorem restrictedAction_comp_ι :
    G.restrictedAction P.hstable ≫ P.U.ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ G.translationAction.left :=
  Scheme.Hom.resLE_comp_ι _ _

/-- **The counit law, scheme side**: inserting the unit and acting is the identity on the
chart, `unitInsert ≫ restrictedAction = 𝟙`. Dualises `translationAction_unit`. -/
theorem unitInsert_comp_restrictedAction :
    P.unitInsert ≫ G.restrictedAction P.hstable = 𝟙 P.U.toScheme := by
  refine (cancel_mono P.U.ι).mp ?_
  rw [Category.id_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (P.unitInsert ≫ ·) P.restrictedAction_comp_ι).trans
      ((P.unitInsert_comp_ι_assoc _).trans P.unitInsertOver_left_translationAction))

/-! ### The Künneth inclusion-leg duals for the chart co-action `Spec`-iso -/

/-- The chart Künneth carries the second projection to the chart projection (extracted from
`chartSpecIso_hom_base`'s internal computation). -/
theorem chartKunnethSchemeIso_hom_snd :
    P.chartKunnethSchemeIso.hom ≫ pullback.snd P.groupToBase P.chartToBase
      = pullback.snd G.π (P.U.ι ≫ E.π) := by
  rw [chartKunnethSchemeIso, Iso.trans_hom, Category.assoc]
  rw [show P.pullbackToPatchLevel.hom ≫ pullback.snd P.groupToBase P.chartToBase
      = pullback.snd (pullback.snd G.π P.V.ι) P.chartToBase from by
    rw [pullbackToPatchLevel]
    refine (pullback.lift_snd _ _ _).trans ?_
    exact Category.comp_id _]
  rw [pullbackToVLevel, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Category.assoc]
  rw [pullbackLeftPullbackSndIso_inv_snd_snd]
  rw [show (pullback.congrHom rfl P.chartToBase_comp_ι).inv
        ≫ pullback.snd G.π (P.chartToBase ≫ P.V.ι)
      = pullback.snd G.π (P.U.ι ≫ E.π) from by
    rw [pullback.congrHom_inv]
    refine (pullback.lift_snd _ _ _).trans ?_
    exact Category.comp_id _]

/-- **The chart (right) inclusion-leg dual**: the co-action `Spec`-iso carries `Spec` of the
right inclusion `B ↪ A ⊗ B` to the chart projection. -/
theorem chartSpecIso_hom_includeRight :
    P.chartSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := P.baseRing) (A := P.groupRing)
          (B := P.chartRing)).toRingHom)
      = pullback.snd G.π (P.U.ι ≫ E.π) ≫ P.U.toSpecΓ := by
  have hksnd : P.kunnethToSpec.hom ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap P.baseRing P.groupRing)))
        (Spec.map (CommRingCat.ofHom (algebraMap P.baseRing P.chartRing)))
      = pullback.snd P.groupToBase P.chartToBase ≫ P.U.toSpecΓ := by
    rw [kunnethToSpec]; exact pullback.lift_snd _ _ _
  rw [chartSpecIso, Iso.trans_hom, Category.assoc, kunnethSpecIso, Iso.trans_hom,
    Category.assoc,
    show Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := P.baseRing) (A := P.groupRing) (B := P.chartRing)).toRingHom)
        = Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight (R := P.baseRing) (A := P.groupRing)
            (B := P.chartRing)))) from rfl,
    pullbackSpecIso_hom_snd, hksnd, reassoc_of% P.chartKunnethSchemeIso_hom_snd]

/-- **The group (left) inclusion-leg dual**: the co-action `Spec`-iso carries `Spec` of the
left inclusion `A ↪ A ⊗ B` to the group projection of the patch-level product. -/
theorem chartSpecIso_hom_includeLeft :
    P.chartSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing) (A := P.groupRing)
          (B := P.chartRing)))
      = P.chartKunnethSchemeIso.hom
        ≫ pullback.fst P.groupToBase P.chartToBase ≫ P.groupOpen.toSpecΓ := by
  have hkfst : P.kunnethToSpec.hom ≫ pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap P.baseRing P.groupRing)))
        (Spec.map (CommRingCat.ofHom (algebraMap P.baseRing P.chartRing)))
      = pullback.fst P.groupToBase P.chartToBase ≫ P.groupOpen.toSpecΓ := by
    rw [kunnethToSpec]; exact pullback.lift_fst _ _ _
  rw [chartSpecIso, Iso.trans_hom, Category.assoc, kunnethSpecIso, Iso.trans_hom,
    Category.assoc, pullbackSpecIso_hom_fst, hkfst]

/-- The unit-insertion as a section of the chart co-action `Spec`-morphism. -/
noncomputable def unitAct : P.U.toScheme ⟶ (Spec (.of (P.groupRing ⊗[P.baseRing] P.chartRing)) : Scheme) :=
  P.unitInsert ≫ (G.chartPullbackIso P.U).hom ≫ P.chartSpecIso.hom

/-- **The counit law, `Spec` side**: the unit-insertion is a section of the co-action. -/
theorem unitAct_comp_chartCoactionSpec :
    P.unitAct ≫ P.chartCoactionSpec = 𝟙 P.U.toScheme := by
  rw [unitAct, chartCoactionSpec, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id_assoc, unitInsert_comp_restrictedAction]

/-- The chart component of the unit-insertion is the identity. -/
theorem unitInsert_chartPullback_snd :
    P.unitInsert ≫ (G.chartPullbackIso P.U).hom ≫ pullback.snd G.π (P.U.ι ≫ E.π)
      = 𝟙 P.U.toScheme := by
  rw [unitInsert, chartPullbackIso, Iso.trans_hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc]
  erw [pullbackLeftPullbackSndIso_hom_snd]
  exact pullback.lift_snd _ _ _

/-- The chart Künneth carries the first projection (into the group patch), followed by the
group-patch inclusion, to the group projection of the `S`-level product. -/
theorem chartKunnethSchemeIso_hom_fst_ι :
    P.chartKunnethSchemeIso.hom ≫ pullback.fst P.groupToBase P.chartToBase ≫ P.groupOpen.ι
      = pullback.fst G.π (P.U.ι ≫ E.π) := by
  rw [chartKunnethSchemeIso, Iso.trans_hom, Category.assoc]
  rw [show P.pullbackToPatchLevel.hom ≫ pullback.fst P.groupToBase P.chartToBase ≫ P.groupOpen.ι
      = pullback.fst (pullback.snd G.π P.V.ι) P.chartToBase ≫ pullback.fst G.π P.V.ι from by
    rw [pullbackToPatchLevel, ← Category.assoc, asIso_hom, pullback.lift_fst,
      Category.assoc, pullbackRestrictIsoRestrict_hom_ι]]
  rw [pullbackToVLevel, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst]
  rw [show (pullback.congrHom rfl P.chartToBase_comp_ι).inv
        ≫ pullback.fst G.π (P.chartToBase ≫ P.V.ι)
      = pullback.fst G.π (P.U.ι ≫ E.π) from by
    rw [pullback.congrHom_inv]; exact pullback.lift_fst _ _ _]

/-- The unit-insertion's group component, before the Künneth re-expression. -/
theorem unitInsert_chartPullback_fst :
    P.unitInsert ≫ (G.chartPullbackIso P.U).hom ≫ pullback.fst G.π (P.U.ι ≫ E.π)
      = (P.U.ι ≫ E.π) ≫ G.unitHom := by
  have hfst : P.unitInsertOver.left ≫ pullback.fst G.π E.π = (P.U.ι ≫ E.π) ≫ G.unitHom := by
    have h : P.unitInsertOver ≫ fst (Over.mk G.π) E.asOver = toUnit P.chartOver ≫ G.unitOver :=
      lift_fst _ _
    have h2 := congrArg CommaMorphism.left h
    simp only [Over.comp_left, Over.fst_left, Over.toUnit_left, unitOver, Over.homMk_left,
      chartOver, Over.mk_hom] at h2
    exact h2
  rw [unitInsert, chartPullbackIso, Iso.trans_hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc]
  erw [pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst_assoc]
  exact hfst

/-- The group component of the unit-insertion is the unit section over the chart. -/
theorem unitInsert_chartKunneth_fst :
    P.unitInsert ≫ (G.chartPullbackIso P.U).hom ≫ P.chartKunnethSchemeIso.hom
        ≫ pullback.fst P.groupToBase P.chartToBase
      = P.chartToBase ≫ P.unitSection := by
  refine (cancel_mono P.groupOpen.ι).mp ?_
  have hL : (P.unitInsert ≫ (G.chartPullbackIso P.U).hom ≫ P.chartKunnethSchemeIso.hom
        ≫ pullback.fst P.groupToBase P.chartToBase) ≫ P.groupOpen.ι
      = (P.U.ι ≫ E.π) ≫ G.unitHom := by
    rw [Category.assoc, Category.assoc, Category.assoc]
    erw [P.chartKunnethSchemeIso_hom_fst_ι]
    exact P.unitInsert_chartPullback_fst
  have hR : (P.chartToBase ≫ P.unitSection) ≫ P.groupOpen.ι = (P.U.ι ≫ E.π) ≫ G.unitHom := by
    rw [Category.assoc, P.unitSection_comp_ι, ← Category.assoc, P.chartToBase_comp_ι]
  rw [hL, hR]

/-- The chart component of the section: `unitAct` composed with the right inclusion's `Spec`
is the chart's affine identification. -/
theorem unitAct_includeRight :
    P.unitAct ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing) (B := P.chartRing)).toRingHom)
      = P.U.toSpecΓ := by
  rw [unitAct, Category.assoc, Category.assoc, chartSpecIso_hom_includeRight,
    reassoc_of% P.unitInsert_chartPullback_snd]

/-- The group component of the section: `unitAct` composed with the left inclusion's `Spec`
is the unit section over the chart. -/
theorem unitAct_includeLeft :
    P.unitAct ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRing) (A := P.groupRing) (B := P.chartRing)))
      = P.chartToBase ≫ P.unitSection ≫ P.groupOpen.toSpecΓ := by
  rw [unitAct, Category.assoc, Category.assoc, chartSpecIso_hom_includeLeft,
    reassoc_of% P.unitInsert_chartKunneth_fst]

/-! ### The counit law, algebra side -/

/-- The `Γ`-dual of the unit-insertion section: a `CommRingCat` map `A ⊗ B ⟶ B`. -/
noncomputable def chartCounitLiftΓ :
    CommRingCat.of (P.groupRing ⊗[P.baseRing] P.chartRing) ⟶ P.chartRing :=
  (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.chartRing))).inv
    ≫ P.unitAct.appTop ≫ P.U.topIso.hom

/-- **The counit law, transported form**: the co-action followed by the dual of the
unit-insertion is the identity. -/
theorem coactionRing_comp_chartCounitLiftΓ :
    P.coactionRing ≫ P.chartCounitLiftΓ = 𝟙 P.chartRing := by
  have hc : P.chartCoactionSpec.appTop ≫ P.unitAct.appTop ≫ P.U.topIso.hom = P.U.topIso.hom := by
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, unitAct_comp_chartCoactionSpec,
      AlgebraicGeometry.Scheme.Hom.id_appTop, Category.id_comp]
  rw [coactionRing_eq_appTop, chartCounitLiftΓ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [hc]
  rw [Iso.inv_hom_id]

/-- The right inclusion, composed with the dual of the section, is the identity. -/
theorem includeRight_comp_chartCounitLiftΓ :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing) (B := P.chartRing)).toRingHom
      ≫ P.chartCounitLiftΓ = 𝟙 P.chartRing := by
  have hR : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing) (B := P.chartRing)).toRingHom)).appTop
        ≫ P.unitAct.appTop ≫ P.U.topIso.hom
      = (Scheme.ΓSpecIso P.chartRing).hom := by
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, unitAct_includeRight,
      Scheme.Opens.toSpecΓ_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [chartCounitLiftΓ, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]
  simp only [Category.assoc]
  erw [hR]
  exact Iso.inv_hom_id _

/-- The left inclusion, composed with the dual of the section, is the counit followed by the
base-patch algebra structure. -/
theorem includeLeft_comp_chartCounitLiftΓ :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRing) (A := P.groupRing) (B := P.chartRing))
      ≫ P.chartCounitLiftΓ
      = P.groupPatchCounit ≫ E.π.appLE P.V P.U P.hover := by
  have hL : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRing) (A := P.groupRing) (B := P.chartRing)))).appTop
        ≫ P.unitAct.appTop ≫ P.U.topIso.hom
      = (Scheme.ΓSpecIso P.groupRing).hom ≫ P.groupPatchCounit ≫ E.π.appLE P.V P.U P.hover := by
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, unitAct_includeLeft,
      Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
      unitSection_appTop,
      show P.chartToBase.appTop
          = P.V.topIso.hom ≫ E.π.appLE P.V P.U P.hover ≫ P.U.topIso.inv from
        Scheme.Hom.resLE_app_top (f := E.π) (U := P.V) (V := P.U) P.hover]
    simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
  rw [chartCounitLiftΓ, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]
  simp only [Category.assoc]
  erw [hL]
  exact Iso.inv_hom_id_assoc _ _

/-- The algebraic counit collapse `A ⊗ B →ₐ[R] B`, `a ⊗ b ↦ ε(a) • b`. -/
noncomputable def chartCounitCollapse :
    (P.groupRing ⊗[P.baseRing] P.chartRing) →ₐ[P.baseRing] P.chartRing :=
  Algebra.TensorProduct.lift ((Algebra.ofId P.baseRing P.chartRing).comp (counitAlg G P))
    (AlgHom.id P.baseRing P.chartRing) (fun _ _ => Commute.all _ _)

/-- **The counit collapse is the `Γ`-dual of the unit-insertion section.** -/
theorem ofHom_chartCounitCollapse :
    CommRingCat.ofHom P.chartCounitCollapse.toRingHom = P.chartCounitLiftΓ := by
  refine tensor_hom_ext ?_ ?_
  · rw [P.includeLeft_comp_chartCounitLiftΓ]
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show chartCounitCollapse P (a ⊗ₜ[P.baseRing] (1 : P.chartRing)) = _
    rw [chartCounitCollapse, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one,
      AlgHom.comp_apply, Algebra.ofId_apply]
    rfl
  · rw [P.includeRight_comp_chartCounitLiftΓ]
    refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    show chartCounitCollapse P ((1 : P.groupRing) ⊗ₜ[P.baseRing] b) = _
    rw [chartCounitCollapse, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    rfl

/-- **The counit law, `AlgHom` form**: `κ ∘ ρ' = id` (the group factor collapses via `ε`). -/
theorem chartCounitCollapse_comp_coactionAlgLeft :
    P.chartCounitCollapse.comp P.coactionAlgLeft = AlgHom.id P.baseRing P.chartRing := by
  refine AlgHom.ext fun b => ?_
  rw [AlgHom.comp_apply, AlgHom.id_apply]
  have h := congrArg (fun m : P.chartRing ⟶ P.chartRing => m.hom b)
    (P.ofHom_chartCounitCollapse ▸ P.coactionRing_comp_chartCounitLiftΓ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply, CommRingCat.hom_ofHom] at h
  exact h

/-! ### The coassoc law, geometric core -/

/-- The restricted action on the clean product `G|_V ×_V U ⟶ U` (`(g, x) ↦ x + g`). -/
noncomputable def chartAct : pullback P.groupToBase P.chartToBase ⟶ P.U.toScheme :=
  P.chartKunnethSchemeIso.inv ≫ (G.chartPullbackIso P.U).inv ≫ G.restrictedAction P.hstable

/-- The clean product mapped into `G ×_S E` — the point `(g, x)`. -/
noncomputable def chartActToGE :
    pullback P.groupToBase P.chartToBase ⟶ (Over.mk G.π ⊗ E.asOver).left :=
  P.chartKunnethSchemeIso.inv ≫ (G.chartPullbackIso P.U).inv ≫ (G.actionProj.left ⁻¹ᵁ P.U).ι

@[reassoc]
theorem chartAct_comp_ι : P.chartAct ≫ P.U.ι = P.chartActToGE ≫ G.translationAction.left := by
  rw [chartAct, chartActToGE, Category.assoc, Category.assoc, Category.assoc, Category.assoc]
  exact congrArg (P.chartKunnethSchemeIso.inv ≫ (G.chartPullbackIso P.U).inv ≫ ·)
    P.restrictedAction_comp_ι

/-- The clean product inclusion into `G ×_S E`, in pullback-pasting form. -/
theorem chartActToGE_eq :
    P.chartActToGE = P.chartKunnethSchemeIso.inv
      ≫ (pullbackLeftPullbackSndIso G.π E.π P.U.ι).inv
      ≫ pullback.fst G.actionProj.left P.U.ι := by
  rw [chartActToGE, chartPullbackIso, Iso.trans_inv, Category.assoc]
  congr 2
  exact pullbackRestrictIsoRestrict_hom_ι _ _

/-- The group coordinate of the action point: `(g,x) ↦ g`. -/
theorem chartActToGE_fst :
    P.chartActToGE ≫ pullback.fst G.π E.π
      = pullback.fst P.groupToBase P.chartToBase ≫ P.groupOpen.ι := by
  rw [chartActToGE_eq, Category.assoc, Category.assoc]
  erw [pullbackLeftPullbackSndIso_inv_fst]
  rw [← P.chartKunnethSchemeIso_hom_fst_ι, Iso.inv_hom_id_assoc]

/-- The chart coordinate of the action point: `(g,x) ↦ x`. -/
theorem chartActToGE_snd :
    P.chartActToGE ≫ G.actionProj.left
      = pullback.snd P.groupToBase P.chartToBase ≫ P.U.ι := by
  rw [chartActToGE_eq]
  show P.chartKunnethSchemeIso.inv ≫ (pullbackLeftPullbackSndIso G.π E.π P.U.ι).inv
        ≫ pullback.fst (pullback.snd G.π E.π) P.U.ι ≫ pullback.snd G.π E.π
      = pullback.snd P.groupToBase P.chartToBase ≫ P.U.ι
  rw [pullbackLeftPullbackSndIso_inv_fst_snd, ← P.chartKunnethSchemeIso_hom_snd,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- The group coordinate of the action product `G ×_S E`, as an `E`-point (`g ↦ ι g`). -/
noncomputable def actGPt (G : FiniteLocallyFreeSubgroup E) :
    E.Point ((Over.mk G.π ⊗ E.asOver).hom) :=
  (E.pointEquivOverHom _).symm (fst (Over.mk G.π) E.asOver ≫ G.ιOver)

/-- The curve coordinate of the action product `G ×_S E`, as an `E`-point (`x ↦ x`). -/
noncomputable def actXPt (G : FiniteLocallyFreeSubgroup E) :
    E.Point ((Over.mk G.π ⊗ E.asOver).hom) :=
  (E.pointEquivOverHom _).symm (snd (Over.mk G.π) E.asOver)

@[simp] theorem actGPt_val (G : FiniteLocallyFreeSubgroup E) :
    (actGPt G).1 = (fst (Over.mk G.π) E.asOver).left ≫ G.ι := rfl
@[simp] theorem actXPt_val (G : FiniteLocallyFreeSubgroup E) :
    (actXPt G).1 = (snd (Over.mk G.π) E.asOver).left := rfl

/-- **The action as an `E`-point sum** (the analog of `mulHom_ι`): the underlying map of the
translation action `G ×_S E ⟶ E` is the coercion of the sum of the two universal points
`g ↦ ι(g)` and `x ↦ x`. -/
theorem translationAction_left_eq_add (G : FiniteLocallyFreeSubgroup E) :
    G.translationAction.left = ((actGPt G + actXPt G : E.Point _)).1 := by
  letI : CommGroup ((Over.mk G.π ⊗ E.asOver) ⟶ E.asOver) := CategoryTheory.Hom.commGroup
  have h : (E.pointEquivOverHom ((Over.mk G.π ⊗ E.asOver).hom)) (actGPt G + actXPt G)
      = G.translationAction := by
    rw [E.pointEquivOverHom_add, actGPt, actXPt, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact G.translationAction_eq_mul.symm
  exact (congrArg CommaMorphism.left h).symm

/-- `groupToBase` (morphismRestrict, used by `chartAct`/`chartSpecIso`) equals `groupToBaseRes`
(resLE, used by `groupSquare`/`squareMulRes`). -/
theorem groupToBase_eq_res : P.groupToBase = P.groupToBaseRes :=
  (Scheme.Hom.resLE_eq_morphismRestrict G.π).symm

/-- The bridge iso between the two spellings of the clean product `G|_V ×_V U`. -/
noncomputable def chartD2congr :
    pullback P.groupToBase P.chartToBase ≅ pullback P.groupToBaseRes P.chartToBase :=
  pullback.congrHom P.groupToBase_eq_res rfl

/-- The clean product action in the `resLE` spelling (matching `squareToBase`). -/
noncomputable def chartActRes : pullback P.groupToBaseRes P.chartToBase ⟶ P.U.toScheme :=
  P.chartD2congr.inv ≫ P.chartAct

/-- The clean-product inclusion into `G ×_S E`, `resLE` spelling. -/
noncomputable def chartActToGERes :
    pullback P.groupToBaseRes P.chartToBase ⟶ (Over.mk G.π ⊗ E.asOver).left :=
  P.chartD2congr.inv ≫ P.chartActToGE

@[reassoc]
theorem chartD2congr_inv_fst :
    P.chartD2congr.inv ≫ pullback.fst P.groupToBase P.chartToBase
      = pullback.fst P.groupToBaseRes P.chartToBase := by
  rw [chartD2congr, pullback.congrHom_inv, pullback.lift_fst, Category.comp_id]

@[reassoc]
theorem chartD2congr_inv_snd :
    P.chartD2congr.inv ≫ pullback.snd P.groupToBase P.chartToBase
      = pullback.snd P.groupToBaseRes P.chartToBase := by
  rw [chartD2congr, pullback.congrHom_inv, pullback.lift_snd, Category.comp_id]

@[reassoc]
theorem chartActRes_comp_ι :
    P.chartActRes ≫ P.U.ι = P.chartActToGERes ≫ G.translationAction.left := by
  rw [chartActRes, chartActToGERes]
  simp only [Category.assoc]
  exact congrArg (P.chartD2congr.inv ≫ ·) P.chartAct_comp_ι

theorem chartActToGERes_fst :
    P.chartActToGERes ≫ pullback.fst G.π E.π
      = pullback.fst P.groupToBaseRes P.chartToBase ≫ P.groupOpen.ι := by
  rw [chartActToGERes, Category.assoc, P.chartActToGE_fst, P.chartD2congr_inv_fst_assoc]

theorem chartActToGERes_snd :
    P.chartActToGERes ≫ G.actionProj.left
      = pullback.snd P.groupToBaseRes P.chartToBase ≫ P.U.ι := by
  rw [chartActToGERes, Category.assoc, P.chartActToGE_snd]
  show P.chartD2congr.inv ≫ pullback.snd P.groupToBase P.chartToBase ≫ P.U.ι
      = pullback.snd P.groupToBaseRes P.chartToBase ≫ P.U.ι
  rw [P.chartD2congr_inv_snd_assoc]

/-- The action preserves the base point: `(g, x) ↦ x + g` lies over the same `V`-point as `x`. -/
theorem chartAct_comp_chartToBase :
    P.chartAct ≫ P.chartToBase
      = pullback.snd P.groupToBase P.chartToBase ≫ P.chartToBase := by
  rw [chartAct]
  simp only [Category.assoc]
  rw [P.restrictedAction_comp_chartToBase, P.chartPullbackIso_inv_comp_prOpenToBase,
    ← Category.assoc, ← P.chartKunnethSchemeIso_hom_snd, Iso.inv_hom_id_assoc]

/-- The structure map of the clean product `G|_V ×_V U` to the base patch (`resLE` spelling). -/
noncomputable abbrev chartD2ToBase :
    pullback P.groupToBaseRes P.chartToBase ⟶ P.V.toScheme :=
  pullback.fst P.groupToBaseRes P.chartToBase ≫ P.groupToBaseRes

@[reassoc]
theorem chartActRes_comp_chartToBase :
    P.chartActRes ≫ P.chartToBase = P.chartD2ToBase := by
  rw [chartActRes, Category.assoc, P.chartAct_comp_chartToBase, P.chartD2congr_inv_snd_assoc,
    chartD2ToBase, ← pullback.condition]

/-- The right-associated chart cube `G|_V ×_V (G|_V ×_V U)`. -/
noncomputable abbrev chartCube : Scheme.{u} :=
  pullback P.groupToBaseRes P.chartD2ToBase

/-- The left-associated chart cube `(G|_V ×_V G|_V) ×_V U`. -/
noncomputable abbrev chartCubeL : Scheme.{u} :=
  pullback P.squareToBase P.chartToBase

/-- Inner action `chartCube → G|_V ×_V U`: `(g₁,(g₂,x)) ↦ (g₁, x + g₂)`. -/
noncomputable def chartInnerAct : P.chartCube ⟶ pullback P.groupToBaseRes P.chartToBase :=
  pullback.lift (pullback.fst P.groupToBaseRes P.chartD2ToBase)
    (pullback.snd P.groupToBaseRes P.chartD2ToBase ≫ P.chartActRes)
    (by rw [Category.assoc, P.chartActRes_comp_chartToBase]; exact pullback.condition)

@[reassoc]
theorem chartInnerAct_fst :
    P.chartInnerAct ≫ pullback.fst P.groupToBaseRes P.chartToBase
      = pullback.fst P.groupToBaseRes P.chartD2ToBase := by
  rw [chartInnerAct, pullback.lift_fst]

@[reassoc]
theorem chartInnerAct_snd :
    P.chartInnerAct ≫ pullback.snd P.groupToBaseRes P.chartToBase
      = pullback.snd P.groupToBaseRes P.chartD2ToBase ≫ P.chartActRes := by
  rw [chartInnerAct, pullback.lift_snd]

/-- Outer multiplication `chartCubeL → G|_V ×_V U`: `((g₁,g₂),x) ↦ (g₁·g₂, x)`. -/
noncomputable def chartOuterMul : P.chartCubeL ⟶ pullback P.groupToBaseRes P.chartToBase :=
  pullback.lift (pullback.fst P.squareToBase P.chartToBase ≫ P.squareMulRes)
    (pullback.snd P.squareToBase P.chartToBase)
    (by rw [Category.assoc, P.squareMulRes_comp_groupToBaseRes]; exact pullback.condition)

@[reassoc]
theorem chartOuterMul_fst :
    P.chartOuterMul ≫ pullback.fst P.groupToBaseRes P.chartToBase
      = pullback.fst P.squareToBase P.chartToBase ≫ P.squareMulRes := by
  rw [chartOuterMul, pullback.lift_fst]

@[reassoc]
theorem chartOuterMul_snd :
    P.chartOuterMul ≫ pullback.snd P.groupToBaseRes P.chartToBase
      = pullback.snd P.squareToBase P.chartToBase := by
  rw [chartOuterMul, pullback.lift_snd]

/-- The associator `chartCube → chartCubeL`: `(g₁,(g₂,x)) ↦ ((g₁,g₂),x)`. -/
noncomputable def chartAssoc : P.chartCube ⟶ P.chartCubeL := by
  refine pullback.lift
    (pullback.lift (pullback.fst P.groupToBaseRes P.chartD2ToBase)
      (pullback.snd P.groupToBaseRes P.chartD2ToBase
        ≫ pullback.fst P.groupToBaseRes P.chartToBase) ?_)
    (pullback.snd P.groupToBaseRes P.chartD2ToBase
      ≫ pullback.snd P.groupToBaseRes P.chartToBase) ?_
  · show pullback.fst P.groupToBaseRes P.chartD2ToBase ≫ P.groupToBaseRes
      = (pullback.snd P.groupToBaseRes P.chartD2ToBase
          ≫ pullback.fst P.groupToBaseRes P.chartToBase) ≫ P.groupToBaseRes
    rw [pullback.condition, Category.assoc]
  · show pullback.lift (pullback.fst P.groupToBaseRes P.chartD2ToBase)
          (pullback.snd P.groupToBaseRes P.chartD2ToBase
            ≫ pullback.fst P.groupToBaseRes P.chartToBase) _
        ≫ (pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes)
      = (pullback.snd P.groupToBaseRes P.chartD2ToBase
          ≫ pullback.snd P.groupToBaseRes P.chartToBase) ≫ P.chartToBase
    rw [← Category.assoc, pullback.lift_fst, pullback.condition, Category.assoc]
    congr 1
    rw [← pullback.condition]

@[reassoc]
theorem chartAssoc_fst_fst :
    P.chartAssoc ≫ pullback.fst P.squareToBase P.chartToBase
        ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes
      = pullback.fst P.groupToBaseRes P.chartD2ToBase := by
  rw [chartAssoc, pullback.lift_fst_assoc, pullback.lift_fst]

@[reassoc]
theorem chartAssoc_fst_snd :
    P.chartAssoc ≫ pullback.fst P.squareToBase P.chartToBase
        ≫ pullback.snd P.groupToBaseRes P.groupToBaseRes
      = pullback.snd P.groupToBaseRes P.chartD2ToBase
        ≫ pullback.fst P.groupToBaseRes P.chartToBase := by
  rw [chartAssoc, pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc]
theorem chartAssoc_snd :
    P.chartAssoc ≫ pullback.snd P.squareToBase P.chartToBase
      = pullback.snd P.groupToBaseRes P.chartD2ToBase
        ≫ pullback.snd P.groupToBaseRes P.chartToBase := by
  rw [chartAssoc, pullback.lift_snd]

/-- The base map to `S` of the clean product's two coordinate points. -/
noncomputable abbrev d2Base : pullback P.groupToBaseRes P.chartToBase ⟶ S :=
  pullback.fst P.groupToBaseRes P.chartToBase ≫ P.groupOpen.ι ≫ G.π

/-- The group coordinate of the clean product `G|_V ×_V U`, as an `E`-point (`g ↦ ι g`). -/
noncomputable def d2gPt : E.Point P.d2Base :=
  ⟨pullback.fst P.groupToBaseRes P.chartToBase ≫ P.groupOpen.ι ≫ G.ι, by
    simp only [d2Base, Category.assoc, G.ι_π]⟩

/-- The curve coordinate of the clean product `G|_V ×_V U`, as an `E`-point (`x ↦ x`). -/
noncomputable def d2xPt : E.Point P.d2Base :=
  ⟨pullback.snd P.groupToBaseRes P.chartToBase ≫ P.U.ι, by
    rw [Category.assoc, ← P.chartToBase_comp_ι, ← Category.assoc, ← pullback.condition,
      Category.assoc, show P.groupToBaseRes ≫ P.V.ι = P.groupOpen.ι ≫ G.π from
        Scheme.Hom.resLE_comp_ι _ _]⟩

theorem chartActToGERes_actGPt :
    P.chartActToGERes ≫ (actGPt G).1
      = pullback.fst P.groupToBaseRes P.chartToBase ≫ P.groupOpen.ι ≫ G.ι := by
  rw [actGPt_val, ← Category.assoc,
    show P.chartActToGERes ≫ (fst (Over.mk G.π) E.asOver).left
        = pullback.fst P.groupToBaseRes P.chartToBase ≫ P.groupOpen.ι from P.chartActToGERes_fst]
  exact Category.assoc _ _ _

/-- **The action as a coordinate point sum** on the clean product: `(g, x) ↦ x + g`, i.e. the
sum of the group point (via `ι`) and the curve point. The analog of the group's
`squareMulRes ≫ ι ≫ G.ι = (sqFst + sqSnd)`. -/
theorem chartActRes_comp_ι_eq_add :
    P.chartActRes ≫ P.U.ι = (P.d2gPt + P.d2xPt : E.Point P.d2Base).1 := by
  have hbase : P.chartActToGERes ≫ (Over.mk G.π ⊗ E.asOver).hom = P.d2Base := by
    rw [← G.actionProj_left_π, reassoc_of% P.chartActToGERes_snd]
    exact P.d2xPt.2
  have hp : P.chartActToGERes ≫ (actGPt G).1 = P.d2gPt.1 := P.chartActToGERes_actGPt
  have hq : P.chartActToGERes ≫ (actXPt G).1 = P.d2xPt.1 := by
    rw [actXPt_val]; exact P.chartActToGERes_snd
  have key : (hbase ▸ EllipticCurve.Point.restrict E P.chartActToGERes (actGPt G + actXPt G) :
      E.Point P.d2Base) = P.d2gPt + P.d2xPt :=
    point_restrictT_add_eq hbase (actGPt G) (actXPt G) P.d2gPt P.d2xPt hp hq
  rw [chartActRes_comp_ι, translationAction_left_eq_add]
  show (EllipticCurve.Point.restrict E P.chartActToGERes (actGPt G + actXPt G)).1
      = (P.d2gPt + P.d2xPt).1
  rw [← key]
  exact (point_base_congr hbase _).symm

/-- Act twice: `(g₁,(g₂,x)) ↦ (x + g₂) + g₁`. Dual of `(id ⊗ ρ) ∘ ρ`. -/
noncomputable def mTwice : P.chartCube ⟶ P.U.toScheme := P.chartInnerAct ≫ P.chartActRes

/-- Multiply then act: `((g₁,g₂),x) ↦ x + (g₁·g₂)`. Dual of `(Δ ⊗ id) ∘ ρ`. -/
noncomputable def mProd : P.chartCubeL ⟶ P.U.toScheme := P.chartOuterMul ≫ P.chartActRes

/-- The common base of the three coordinate points of the chart cube: the projection to `S`. -/
noncomputable abbrev chartCubeBase : P.chartCube ⟶ S :=
  pullback.fst P.groupToBaseRes P.chartD2ToBase ≫ P.groupOpen.ι ≫ G.π

/-- First coordinate point `g₁` of the chart cube. -/
noncomputable def chartCubePt₁ : E.Point P.chartCubeBase :=
  ⟨pullback.fst P.groupToBaseRes P.chartD2ToBase ≫ P.groupOpen.ι ≫ G.ι, by
    simp only [chartCubeBase, Category.assoc, G.ι_π]⟩

/-- Second coordinate point `g₂` of the chart cube. -/
noncomputable def chartCubePt₂ : E.Point P.chartCubeBase :=
  ⟨pullback.snd P.groupToBaseRes P.chartD2ToBase ≫ pullback.fst P.groupToBaseRes P.chartToBase
      ≫ P.groupOpen.ι ≫ G.ι, by
    have hb : P.groupOpen.ι ≫ G.π = P.groupToBaseRes ≫ P.V.ι :=
      (Scheme.Hom.resLE_comp_ι _ _).symm
    have hc₂ : pullback.snd P.groupToBaseRes P.chartD2ToBase
          ≫ pullback.fst P.groupToBaseRes P.chartToBase ≫ P.groupToBaseRes
        = pullback.fst P.groupToBaseRes P.chartD2ToBase ≫ P.groupToBaseRes :=
      pullback.condition.symm
    simp only [chartCubeBase, Category.assoc, G.ι_π, hb]
    rw [reassoc_of% hc₂]⟩

/-- Third coordinate point `x` of the chart cube (the curve factor). -/
noncomputable def chartCubePt₃ : E.Point P.chartCubeBase :=
  ⟨pullback.snd P.groupToBaseRes P.chartD2ToBase ≫ pullback.snd P.groupToBaseRes P.chartToBase
      ≫ P.U.ι, by
    have hb : P.groupOpen.ι ≫ G.π = P.groupToBaseRes ≫ P.V.ι :=
      (Scheme.Hom.resLE_comp_ι _ _).symm
    have hc₃ : pullback.snd P.groupToBaseRes P.chartD2ToBase
          ≫ pullback.snd P.groupToBaseRes P.chartToBase ≫ P.chartToBase
        = pullback.fst P.groupToBaseRes P.chartD2ToBase ≫ P.groupToBaseRes := by
      rw [← pullback.condition (f := P.groupToBaseRes) (g := P.chartToBase)]
      exact pullback.condition.symm
    simp only [chartCubeBase, Category.assoc, hb, ← P.chartToBase_comp_ι]
    rw [reassoc_of% hc₃]⟩

@[simp] theorem d2gPt_val : P.d2gPt.1
    = pullback.fst P.groupToBaseRes P.chartToBase ≫ P.groupOpen.ι ≫ G.ι := rfl
@[simp] theorem d2xPt_val : P.d2xPt.1
    = pullback.snd P.groupToBaseRes P.chartToBase ≫ P.U.ι := rfl
@[simp] theorem chartCubePt₁_val : P.chartCubePt₁.1
    = pullback.fst P.groupToBaseRes P.chartD2ToBase ≫ P.groupOpen.ι ≫ G.ι := rfl
@[simp] theorem chartCubePt₂_val : P.chartCubePt₂.1
    = pullback.snd P.groupToBaseRes P.chartD2ToBase ≫ pullback.fst P.groupToBaseRes P.chartToBase
      ≫ P.groupOpen.ι ≫ G.ι := rfl
@[simp] theorem chartCubePt₃_val : P.chartCubePt₃.1
    = pullback.snd P.groupToBaseRes P.chartD2ToBase ≫ pullback.snd P.groupToBaseRes P.chartToBase
      ≫ P.U.ι := rfl

/-- **The chart-level associativity of the action** (the analog of `assocScheme_leftMulSchemeL`):
acting by `g₁` after acting by `g₂` equals acting by the product `g₁·g₂`. Cancelling `U.ι`,
both sides are the coercion of a triple sum of the cube's three coordinate points, and the
identity is `add_assoc` in `E.Point chartCubeBase`. -/
theorem chartAssoc_mProd : P.chartAssoc ≫ P.mProd = P.mTwice := by
  rw [← cancel_mono P.U.ι]
  have hb : P.groupOpen.ι ≫ G.π = P.groupToBaseRes ≫ P.V.ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  have hU : (G.sqFstPoint + G.sqSndPoint : E.Point _).1 = G.mulHom ≫ G.ι := G.mulHom_ι.symm
  -- `groupSquareToSquare` carries the two square-projections to the two `G|_V` legs (into `E`).
  have hfstι : P.groupSquareToSquare ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
      = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι := by
    rw [← Category.assoc, P.groupSquareToSquare_fst]; exact Category.assoc _ _ _
  have hsndι : P.groupSquareToSquare ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
      = pullback.snd P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι := by
    rw [← Category.assoc, P.groupSquareToSquare_snd]; exact Category.assoc _ _ _
  -- the base identities of the various restricted points.
  have hInner : P.chartInnerAct ≫ P.d2Base = P.chartCubeBase := by
    rw [d2Base, ← Category.assoc, P.chartInnerAct_fst]
  have hsndbase : pullback.snd P.groupToBaseRes P.chartD2ToBase ≫ P.d2Base = P.chartCubeBase := by
    have hc₂ : pullback.snd P.groupToBaseRes P.chartD2ToBase
          ≫ pullback.fst P.groupToBaseRes P.chartToBase ≫ P.groupToBaseRes
        = pullback.fst P.groupToBaseRes P.chartD2ToBase ≫ P.groupToBaseRes :=
      pullback.condition.symm
    rw [d2Base, chartCubeBase, hb, ← reassoc_of% hc₂]
  have hgsts : P.groupSquareToSquare ≫ (Over.mk G.π ⊗ Over.mk G.π).hom
      = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes ≫ P.V.ι := by
    rw [← G.mulHom_π, ← Category.assoc]; exact P.squareMul_π
  have hmulbase : (P.chartAssoc ≫ pullback.fst P.squareToBase P.chartToBase
        ≫ P.groupSquareToSquare) ≫ (Over.mk G.π ⊗ Over.mk G.π).hom = P.chartCubeBase := by
    simp only [Category.assoc, hgsts, P.chartAssoc_fst_fst_assoc, chartCubeBase, hb]
  -- the inner action `act(g₂, x) = g₂ + x` splits into the coordinate points `g₂` and `x`.
  have Einner : (hsndbase ▸ EllipticCurve.Point.restrict E
        (pullback.snd P.groupToBaseRes P.chartD2ToBase) (P.d2gPt + P.d2xPt) :
        E.Point P.chartCubeBase) = P.chartCubePt₂ + P.chartCubePt₃ :=
    point_restrictT_add_eq hsndbase P.d2gPt P.d2xPt P.chartCubePt₂ P.chartCubePt₃ rfl rfl
  -- the multiplication `g₁·g₂` splits into the coordinate points `g₁` and `g₂`.
  have EmulL : (hmulbase ▸ EllipticCurve.Point.restrict E
        (P.chartAssoc ≫ pullback.fst P.squareToBase P.chartToBase ≫ P.groupSquareToSquare)
        (G.sqFstPoint + G.sqSndPoint) : E.Point P.chartCubeBase)
      = P.chartCubePt₁ + P.chartCubePt₂ :=
    point_restrictT_add_eq hmulbase G.sqFstPoint G.sqSndPoint P.chartCubePt₁ P.chartCubePt₂
      (by
        show (P.chartAssoc ≫ pullback.fst P.squareToBase P.chartToBase ≫ P.groupSquareToSquare)
            ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι = _
        simp only [Category.assoc, hfstι, P.chartAssoc_fst_fst_assoc, chartCubePt₁_val])
      (by
        show (P.chartAssoc ≫ pullback.fst P.squareToBase P.chartToBase ≫ P.groupSquareToSquare)
            ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι = _
        simp only [Category.assoc, hsndι, P.chartAssoc_fst_snd_assoc, chartCubePt₂_val])
  -- LHS full split: `((g₁ + g₂) + x)`.
  have hLbase : (P.chartAssoc ≫ P.chartOuterMul) ≫ P.d2Base = P.chartCubeBase := by
    simp only [d2Base, Category.assoc, P.chartOuterMul_fst_assoc,
      P.squareMulRes_comp_groupToBaseRes_assoc, P.chartAssoc_fst_fst_assoc, chartCubeBase, hb]
  have ELHS : (hLbase ▸ EllipticCurve.Point.restrict E (P.chartAssoc ≫ P.chartOuterMul)
        (P.d2gPt + P.d2xPt) : E.Point P.chartCubeBase)
      = (P.chartCubePt₁ + P.chartCubePt₂) + P.chartCubePt₃ :=
    point_restrictT_add_eq hLbase P.d2gPt P.d2xPt (P.chartCubePt₁ + P.chartCubePt₂) P.chartCubePt₃
      (by
        have hL : ((P.chartCubePt₁ + P.chartCubePt₂ : E.Point P.chartCubeBase)).1
            = (P.chartAssoc ≫ pullback.fst P.squareToBase P.chartToBase ≫ P.groupSquareToSquare)
              ≫ (G.sqFstPoint + G.sqSndPoint : E.Point _).1 := by
          rw [← EmulL]; exact point_base_congr hmulbase _
        rw [hL]
        simp only [d2gPt_val, Category.assoc, P.chartOuterMul_fst_assoc,
          P.squareMulRes_comp_ι_assoc, squareMul, G.mulHom_ι])
      (by
        simp only [d2xPt_val, Category.assoc, P.chartOuterMul_snd_assoc, P.chartAssoc_snd_assoc,
          chartCubePt₃_val])
  -- RHS full split: `(g₁ + (g₂ + x))`.
  have EmTwice : (hInner ▸ EllipticCurve.Point.restrict E P.chartInnerAct (P.d2gPt + P.d2xPt) :
        E.Point P.chartCubeBase) = P.chartCubePt₁ + (P.chartCubePt₂ + P.chartCubePt₃) :=
    point_restrictT_add_eq hInner P.d2gPt P.d2xPt P.chartCubePt₁ (P.chartCubePt₂ + P.chartCubePt₃)
      (by simp only [d2gPt_val, P.chartInnerAct_fst_assoc, chartCubePt₁_val])
      (by
        have hR : ((P.chartCubePt₂ + P.chartCubePt₃ : E.Point P.chartCubeBase)).1
            = pullback.snd P.groupToBaseRes P.chartD2ToBase
              ≫ (P.d2gPt + P.d2xPt : E.Point _).1 := by
          rw [← Einner]; exact point_base_congr hsndbase _
        rw [hR]
        simp only [d2xPt_val, P.chartInnerAct_snd_assoc, P.chartActRes_comp_ι_eq_add])
  have hLHS : (P.chartAssoc ≫ P.mProd) ≫ P.U.ι
      = ((P.chartCubePt₁ + P.chartCubePt₂) + P.chartCubePt₃).1 := by
    rw [← ELHS, point_base_congr]
    simp only [mProd, EllipticCurve.Point.restrict, Category.assoc, P.chartActRes_comp_ι_eq_add]
  have hRHS : P.mTwice ≫ P.U.ι = (P.chartCubePt₁ + (P.chartCubePt₂ + P.chartCubePt₃)).1 := by
    rw [← EmTwice, point_base_congr]
    simp only [mTwice, EllipticCurve.Point.restrict, Category.assoc, P.chartActRes_comp_ι_eq_add]
  rw [hLHS, hRHS, add_assoc]

/-! ### The coassoc law, algebra side: dualising `chartAssoc_mProd` -/

/-- **Ext principle for maps into `Spec (A ⊗ B)`**: two scheme maps into `Spec (A ⊗[R] B)`
agreeing after the two `Spec`-inclusions agree. -/
theorem spec_tensor_hom_ext {R₁ A₁ B₁ : Type u} [CommRing R₁] [CommRing A₁] [CommRing B₁]
    [Algebra R₁ A₁] [Algebra R₁ B₁] {Z : Scheme.{u}}
    {φ ψ : Z ⟶ (Spec (.of (A₁ ⊗[R₁] B₁)) : Scheme)}
    (hL : φ ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R₁) (A := A₁) (B := B₁)))
      = ψ ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R₁) (A := A₁) (B := B₁))))
    (hR : φ ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R₁) (A := A₁) (B := B₁)).toRingHom)
      = ψ ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R₁) (A := A₁) (B := B₁)).toRingHom)) :
    φ = ψ := by
  rw [← cancel_mono (pullbackSpecIso R₁ A₁ B₁).inv]
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, pullbackSpecIso_inv_fst]; exact hL
  · rw [Category.assoc, Category.assoc, pullbackSpecIso_inv_snd]; exact hR

/-- `chartCoactionSpec` re-expressed via the clean-product action `chartAct`. -/
theorem chartCoactionSpec_eq :
    P.chartCoactionSpec = P.kunnethSpecIso.inv ≫ P.chartAct := by
  rw [chartCoactionSpec, chartAct, chartSpecIso, Iso.trans_inv, Category.assoc]

/-- **(K0)** `Spec` of the coaction ring map is the action `Spec`-morphism, followed by the
chart's affine identification. -/
theorem specMap_coactionRing :
    Spec.map P.coactionRing = P.chartCoactionSpec ≫ P.U.toSpecΓ := by
  rw [Scheme.Opens.toSpecΓ, ← Category.assoc, Scheme.toSpecΓ_naturality,
    ← SpecMap_ΓSpecIso_hom, coactionRing_eq_appTop]
  simp only [Spec.map_comp, Category.assoc]

/-- The Künneth `Spec`-iso carries `Spec` of the left inclusion `A ↪ A ⊗ B` to the group leg. -/
theorem kunnethSpecIso_hom_includeLeft :
    P.kunnethSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing) (A := P.groupRing)
          (B := P.chartRing)))
      = pullback.fst P.groupToBase P.chartToBase ≫ P.groupOpen.toSpecΓ := by
  have h := P.chartSpecIso_hom_includeLeft
  rw [chartSpecIso, Iso.trans_hom, Category.assoc] at h
  exact (cancel_epi P.chartKunnethSchemeIso.hom).mp h

/-- The Künneth `Spec`-iso carries `Spec` of the right inclusion `B ↪ A ⊗ B` to the chart leg. -/
theorem kunnethSpecIso_hom_includeRight :
    P.kunnethSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := P.baseRing) (A := P.groupRing)
          (B := P.chartRing)).toRingHom)
      = pullback.snd P.groupToBase P.chartToBase ≫ P.U.toSpecΓ := by
  have h := P.chartSpecIso_hom_includeRight
  rw [chartSpecIso, Iso.trans_hom, ← P.chartKunnethSchemeIso_hom_snd] at h
  simp only [Category.assoc] at h
  exact (cancel_epi P.chartKunnethSchemeIso.hom).mp h

/-- The Künneth `Spec`-iso carries `Spec` of the base algebra map to the chart structure leg. -/
theorem kunnethSpecIso_hom_base :
    P.kunnethSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap P.baseRing (P.groupRing ⊗[P.baseRing] P.chartRing)))
      = pullback.snd P.groupToBase P.chartToBase ≫ P.chartToBase ≫ P.V.toSpecΓ := by
  have h := P.chartSpecIso_hom_base
  rw [chartSpecIso, Iso.trans_hom, ← P.chartKunnethSchemeIso_hom_snd] at h
  simp only [Category.assoc] at h
  exact (cancel_epi P.chartKunnethSchemeIso.hom).mp h

/-- **(K)** the key action-dual: the Künneth `Spec`-iso conjugates `Spec (coactionRing)` into
the clean-product action `chartAct`. -/
theorem kunnethSpecIso_hom_specMap_coactionRing :
    P.kunnethSpecIso.hom ≫ Spec.map P.coactionRing = P.chartAct ≫ P.U.toSpecΓ := by
  rw [specMap_coactionRing, chartCoactionSpec_eq, ← Category.assoc, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- The group-square affine identification `G|_V ×_V G|_V ≅ Spec (A ⊗ A)`. -/
noncomputable abbrev squareSpecIso :
    P.groupSquare ≅ Spec (.of (P.groupRing ⊗[P.baseRing] P.groupRing)) :=
  patchKunneth G.π G.π P.hV P.isAffineOpen_groupOpen P.isAffineOpen_groupOpen
    (e₁ := le_rfl) (e₂ := le_rfl) rfl rfl

/-- **The right-associated triple identification** `chartCube ≅ Spec (A ⊗ (A ⊗ B))`. -/
noncomputable def cubeSpecIso :
    P.chartCube ≅ Spec (.of (P.groupRing ⊗[P.baseRing]
        (P.groupRing ⊗[P.baseRing] P.chartRing))) := by
  haveI := P.isIso_toSpecΓ_V
  haveI := P.isIso_toSpecΓ_groupOpen
  refine asIso (pullback.map P.groupToBaseRes P.chartD2ToBase
      (Spec.map (CommRingCat.ofHom (algebraMap P.baseRing P.groupRing)))
      (Spec.map (CommRingCat.ofHom (algebraMap P.baseRing
        (P.groupRing ⊗[P.baseRing] P.chartRing))))
      P.groupOpen.toSpecΓ (P.chartD2congr.inv ≫ P.kunnethSpecIso.hom) P.V.toSpecΓ ?_ ?_)
    ≪≫ pullbackSpecIso P.baseRing P.groupRing (P.groupRing ⊗[P.baseRing] P.chartRing)
  · exact (Scheme.Opens.toSpecΓ_SpecMap_appLE G.π P.V P.groupOpen le_rfl).symm
  · conv_rhs => rw [Category.assoc, kunnethSpecIso_hom_base]
    rw [P.chartD2congr_inv_snd_assoc]
    show (pullback.fst P.groupToBaseRes P.chartToBase ≫ P.groupToBaseRes) ≫ P.V.toSpecΓ
        = pullback.snd P.groupToBaseRes P.chartToBase ≫ P.chartToBase ≫ P.V.toSpecΓ
    rw [Category.assoc, pullback.condition_assoc]

/-- **The left-associated triple identification** `chartCubeL ≅ Spec ((A ⊗ A) ⊗ B)`. -/
noncomputable def cubeLSpecIso :
    P.chartCubeL ≅ Spec (.of ((P.groupRing ⊗[P.baseRing] P.groupRing)
        ⊗[P.baseRing] P.chartRing)) := by
  haveI := P.isIso_toSpecΓ_V
  haveI := P.isIso_toSpecΓ_U
  refine asIso (pullback.map P.squareToBase P.chartToBase
      (Spec.map (CommRingCat.ofHom (algebraMap P.baseRing
        (P.groupRing ⊗[P.baseRing] P.groupRing))))
      (Spec.map (CommRingCat.ofHom (algebraMap P.baseRing P.chartRing)))
      P.squareSpecIso.hom P.U.toSpecΓ P.V.toSpecΓ ?_ ?_)
    ≪≫ pullbackSpecIso P.baseRing (P.groupRing ⊗[P.baseRing] P.groupRing) P.chartRing
  · rw [squareToBase, Category.assoc]
    exact (patchKunneth_hom_base G.π G.π P.hV P.isAffineOpen_groupOpen
      P.isAffineOpen_groupOpen (e₁ := le_rfl) (e₂ := le_rfl) rfl rfl).symm
  · exact (Scheme.Opens.toSpecΓ_SpecMap_appLE E.π P.V P.U P.hover).symm

/-- The right-triple identification carries the outer left inclusion `A ↪ A ⊗ (A ⊗ B)` to the
first cube projection. -/
theorem cubeSpecIso_hom_includeLeft :
    P.cubeSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing) (A := P.groupRing)
          (B := P.groupRing ⊗[P.baseRing] P.chartRing)))
      = pullback.fst P.groupToBaseRes P.chartD2ToBase ≫ P.groupOpen.toSpecΓ := by
  rw [cubeSpecIso, Iso.trans_hom, asIso_hom, Category.assoc, pullbackSpecIso_hom_fst]
  exact pullback.lift_fst _ _ _

/-- The right-triple identification carries the outer right inclusion `(A ⊗ B) ↪ A ⊗ (A ⊗ B)`
to the second cube projection, followed by the pair identification. -/
theorem cubeSpecIso_hom_includeRight :
    P.cubeSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := P.baseRing) (A := P.groupRing)
          (B := P.groupRing ⊗[P.baseRing] P.chartRing)).toRingHom)
      = pullback.snd P.groupToBaseRes P.chartD2ToBase
        ≫ P.chartD2congr.inv ≫ P.kunnethSpecIso.hom := by
  rw [cubeSpecIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [show Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing)
        (B := P.groupRing ⊗[P.baseRing] P.chartRing)).toRingHom)
      = Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := P.baseRing) (A := P.groupRing)
          (B := P.groupRing ⊗[P.baseRing] P.chartRing)))) from rfl,
    pullbackSpecIso_hom_snd]
  exact pullback.lift_snd _ _ _

/-- The left-triple identification carries the outer left inclusion `(A ⊗ A) ↪ (A ⊗ A) ⊗ B`
to the first cube projection, followed by the square identification. -/
@[reassoc]
theorem cubeLSpecIso_hom_includeLeft :
    P.cubeLSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing)
          (A := P.groupRing ⊗[P.baseRing] P.groupRing) (B := P.chartRing)))
      = pullback.fst P.squareToBase P.chartToBase ≫ P.squareSpecIso.hom := by
  rw [cubeLSpecIso, Iso.trans_hom, asIso_hom, Category.assoc, pullbackSpecIso_hom_fst]
  exact pullback.lift_fst _ _ _

/-- The left-triple identification carries the outer right inclusion `B ↪ (A ⊗ A) ⊗ B` to the
chart projection. -/
theorem cubeLSpecIso_hom_includeRight :
    P.cubeLSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := P.baseRing)
          (A := P.groupRing ⊗[P.baseRing] P.groupRing) (B := P.chartRing)).toRingHom)
      = pullback.snd P.squareToBase P.chartToBase ≫ P.U.toSpecΓ := by
  rw [cubeLSpecIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [show Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing ⊗[P.baseRing] P.groupRing)
        (B := P.chartRing)).toRingHom)
      = Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := P.baseRing)
          (A := P.groupRing ⊗[P.baseRing] P.groupRing) (B := P.chartRing)))) from rfl,
    pullbackSpecIso_hom_snd]
  exact pullback.lift_snd _ _ _

/-- **The group-multiplication dual**: the square identification conjugates `Spec (Δ)` (the
comultiplication) into the corestricted multiplication `squareMulRes`. -/
theorem squareSpecIso_hom_comul :
    P.squareSpecIso.hom ≫ Spec.map P.groupPatchComul
      = P.squareMulRes ≫ P.groupOpen.toSpecΓ := by
  rw [groupPatchComul_eq, Spec.map_comp, patchKunnethΓ, Spec.map_comp, SpecMap_ΓSpecIso_hom,
    Scheme.Opens.toSpecΓ, squareMul_appLE_eq, Spec.map_comp]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc, Iso.hom_inv_id_assoc,
    ← Scheme.toSpecΓ_naturality_assoc]

/-- Tensor identity: `A ↪ A ⊗ B` post-composed with `id ⊗ ρ_L` is `A ↪ A ⊗ (A ⊗ B)`. -/
theorem ofHom_includeLeft_map_id_coaction :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing)
        (A := P.groupRing) (B := P.chartRing))
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.groupRing)
          P.coactionAlgLeft).toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing)
        (A := P.groupRing) (B := P.groupRing ⊗[P.baseRing] P.chartRing)) := by
  rw [← CommRingCat.ofHom_comp]
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  show (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.groupRing) P.coactionAlgLeft)
      (a ⊗ₜ[P.baseRing] (1 : P.chartRing))
      = a ⊗ₜ[P.baseRing] (1 : P.groupRing ⊗[P.baseRing] P.chartRing)
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

/-- Tensor identity: `B ↪ A ⊗ B` post-composed with `id ⊗ ρ_L` is `ρ_L` then `A ⊗ B ↪ A ⊗ (A ⊗ B)`. -/
theorem ofHom_includeRight_map_id_coaction :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := P.baseRing)
        (A := P.groupRing) (B := P.chartRing)).toRingHom
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.groupRing)
          P.coactionAlgLeft).toRingHom
      = P.coactionRing ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := P.baseRing) (A := P.groupRing)
        (B := P.groupRing ⊗[P.baseRing] P.chartRing)).toRingHom := by
  rw [← CommRingCat.ofHom_comp]
  refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
  show (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.groupRing) P.coactionAlgLeft)
      ((1 : P.groupRing) ⊗ₜ[P.baseRing] b)
      = (1 : P.groupRing) ⊗ₜ[P.baseRing] P.coactionAlgLeft b
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- **(ML)** `Spec` of `(id ⊗ ρ_L) ∘ ·` conjugates through the triples into the inner action. -/
theorem cubeSpecIso_hom_mapIdCoaction :
    P.cubeSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.groupRing)
          P.coactionAlgLeft).toRingHom)
      = P.chartInnerAct ≫ P.chartD2congr.inv ≫ P.kunnethSpecIso.hom := by
  refine spec_tensor_hom_ext ?_ ?_
  · simp only [Category.assoc]
    rw [← Spec.map_comp, ofHom_includeLeft_map_id_coaction, cubeSpecIso_hom_includeLeft,
      kunnethSpecIso_hom_includeLeft, P.chartD2congr_inv_fst_assoc, P.chartInnerAct_fst_assoc]
  · simp only [Category.assoc]
    rw [← Spec.map_comp, ofHom_includeRight_map_id_coaction, Spec.map_comp, ← Category.assoc,
      cubeSpecIso_hom_includeRight, kunnethSpecIso_hom_includeRight,
      P.chartD2congr_inv_snd_assoc, P.chartInnerAct_snd_assoc]
    simp only [Category.assoc]
    rw [kunnethSpecIso_hom_specMap_coactionRing, chartActRes]
    simp only [Category.assoc]

/-- Tensor identity: `A ↪ A ⊗ B` post-composed with `Δ ⊗ id` is `Δ` then `A⊗A ↪ (A⊗A) ⊗ B`. -/
theorem ofHom_includeLeft_map_comul_id :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing)
        (A := P.groupRing) (B := P.chartRing))
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.map (comulAlg G P)
          (AlgHom.id P.baseRing P.chartRing)).toRingHom
      = P.groupPatchComul ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := P.baseRing) (A := P.groupRing ⊗[P.baseRing] P.groupRing) (B := P.chartRing)) := by
  rw [← CommRingCat.ofHom_comp]
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  show (Algebra.TensorProduct.map (comulAlg G P) (AlgHom.id P.baseRing P.chartRing))
      (a ⊗ₜ[P.baseRing] (1 : P.chartRing))
      = (comulAlg G P a) ⊗ₜ[P.baseRing] (1 : P.chartRing)
  rw [Algebra.TensorProduct.map_tmul, map_one]

/-- Tensor identity: `B ↪ A ⊗ B` post-composed with `Δ ⊗ id` is `B ↪ (A⊗A) ⊗ B`. -/
theorem ofHom_includeRight_map_comul_id :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := P.baseRing)
        (A := P.groupRing) (B := P.chartRing)).toRingHom
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.map (comulAlg G P)
          (AlgHom.id P.baseRing P.chartRing)).toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := P.baseRing)
        (A := P.groupRing ⊗[P.baseRing] P.groupRing) (B := P.chartRing)).toRingHom := by
  rw [← CommRingCat.ofHom_comp]
  refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
  show (Algebra.TensorProduct.map (comulAlg G P) (AlgHom.id P.baseRing P.chartRing))
      ((1 : P.groupRing) ⊗ₜ[P.baseRing] b)
      = (1 : P.groupRing ⊗[P.baseRing] P.groupRing) ⊗ₜ[P.baseRing] b
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

/-- **(MO)** `Spec` of `(Δ ⊗ id) ∘ ·` conjugates through the triples into the outer
multiplication. -/
@[reassoc]
theorem cubeLSpecIso_hom_mapComulId :
    P.cubeLSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (comulAlg G P) (AlgHom.id P.baseRing P.chartRing)).toRingHom)
      = P.chartOuterMul ≫ P.chartD2congr.inv ≫ P.kunnethSpecIso.hom := by
  refine spec_tensor_hom_ext ?_ ?_
  · simp only [Category.assoc]
    rw [← Spec.map_comp, ofHom_includeLeft_map_comul_id, Spec.map_comp, ← Category.assoc,
      cubeLSpecIso_hom_includeLeft, kunnethSpecIso_hom_includeLeft,
      P.chartD2congr_inv_fst_assoc, P.chartOuterMul_fst_assoc]
    simp only [Category.assoc]
    rw [squareSpecIso_hom_comul]
  · simp only [Category.assoc]
    rw [← Spec.map_comp, ofHom_includeRight_map_comul_id, cubeLSpecIso_hom_includeRight,
      kunnethSpecIso_hom_includeRight, P.chartD2congr_inv_snd_assoc, P.chartOuterMul_snd_assoc]

/-- The square identification carries `Spec` of the left inclusion `A ↪ A ⊗ A` to the first
group leg. -/
@[reassoc]
theorem squareSpecIso_hom_includeLeft :
    P.squareSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing) (A := P.groupRing)
          (B := P.groupRing)))
      = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.toSpecΓ :=
  patchKunneth_hom_comp_includeLeft G.π G.π P.hV P.isAffineOpen_groupOpen
    P.isAffineOpen_groupOpen (e₁ := le_rfl) (e₂ := le_rfl) rfl rfl

/-- The square identification carries `Spec` of the right inclusion `A ↪ A ⊗ A` to the second
group leg. -/
@[reassoc]
theorem squareSpecIso_hom_includeRight :
    P.squareSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := P.baseRing) (A := P.groupRing)
          (B := P.groupRing)).toRingHom)
      = pullback.snd P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.toSpecΓ :=
  patchKunneth_hom_comp_includeRight G.π G.π P.hV P.isAffineOpen_groupOpen
    P.isAffineOpen_groupOpen (e₁ := le_rfl) (e₂ := le_rfl) rfl rfl

/-- Tensor identity (g₁): `A ↪ (A⊗A) ↪ (A⊗A)⊗B` then `assoc` is `A ↪ A⊗(A⊗B)`. -/
theorem ofHom_assoc_includeLeft_includeLeft :
    (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing)
        (A := P.groupRing) (B := P.groupRing))
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing)
        (A := P.groupRing ⊗[P.baseRing] P.groupRing) (B := P.chartRing)))
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
          P.groupRing P.groupRing P.chartRing).toAlgHom.toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing)
        (A := P.groupRing) (B := P.groupRing ⊗[P.baseRing] P.chartRing)) := by
  simp only [← CommRingCat.ofHom_comp]
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  show (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
        P.groupRing P.groupRing P.chartRing)
      ((a ⊗ₜ[P.baseRing] (1 : P.groupRing)) ⊗ₜ[P.baseRing] (1 : P.chartRing))
      = a ⊗ₜ[P.baseRing] (1 : P.groupRing ⊗[P.baseRing] P.chartRing)
  rw [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.one_def]

/-- Tensor identity (g₂): `A ↪ (A⊗A)` (right) `↪ (A⊗A)⊗B` then `assoc` is `A ↪ A⊗B ↪ A⊗(A⊗B)`. -/
theorem ofHom_assoc_includeLeft_includeRight :
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := P.baseRing)
        (A := P.groupRing) (B := P.groupRing)).toRingHom
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing)
        (A := P.groupRing ⊗[P.baseRing] P.groupRing) (B := P.chartRing)))
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
          P.groupRing P.groupRing P.chartRing).toAlgHom.toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing)
        (A := P.groupRing) (B := P.chartRing))
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := P.baseRing)
        (A := P.groupRing) (B := P.groupRing ⊗[P.baseRing] P.chartRing)).toRingHom := by
  simp only [← CommRingCat.ofHom_comp]
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  show (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
        P.groupRing P.groupRing P.chartRing)
      (((1 : P.groupRing) ⊗ₜ[P.baseRing] a) ⊗ₜ[P.baseRing] (1 : P.chartRing))
      = (1 : P.groupRing) ⊗ₜ[P.baseRing] (a ⊗ₜ[P.baseRing] (1 : P.chartRing))
  rw [Algebra.TensorProduct.assoc_tmul]

/-- Tensor identity (x): `B ↪ (A⊗A)⊗B` then `assoc` is `B ↪ A⊗B ↪ A⊗(A⊗B)`. -/
theorem ofHom_assoc_includeRight :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := P.baseRing)
        (A := P.groupRing ⊗[P.baseRing] P.groupRing) (B := P.chartRing)).toRingHom
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
          P.groupRing P.groupRing P.chartRing).toAlgHom.toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := P.baseRing)
        (A := P.groupRing) (B := P.chartRing)).toRingHom
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := P.baseRing)
        (A := P.groupRing) (B := P.groupRing ⊗[P.baseRing] P.chartRing)).toRingHom := by
  simp only [← CommRingCat.ofHom_comp]
  refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
  show (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
        P.groupRing P.groupRing P.chartRing)
      ((1 : P.groupRing ⊗[P.baseRing] P.groupRing) ⊗ₜ[P.baseRing] b)
      = (1 : P.groupRing) ⊗ₜ[P.baseRing] ((1 : P.groupRing) ⊗ₜ[P.baseRing] b)
  rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.assoc_tmul]

/-- **(MA)** `Spec` of the tensor associator conjugates through the triples into the geometric
associator `chartAssoc`. -/
@[reassoc]
theorem cubeSpecIso_hom_assoc :
    P.cubeSpecIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
          P.groupRing P.groupRing P.chartRing).toAlgHom.toRingHom)
      = P.chartAssoc ≫ P.cubeLSpecIso.hom := by
  refine spec_tensor_hom_ext ?_ ?_
  · refine spec_tensor_hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [P.cubeLSpecIso_hom_includeLeft_assoc, squareSpecIso_hom_includeLeft,
        P.chartAssoc_fst_fst_assoc, ← Spec.map_comp, ← Spec.map_comp,
        ofHom_assoc_includeLeft_includeLeft, cubeSpecIso_hom_includeLeft]
    · simp only [Category.assoc]
      rw [P.cubeLSpecIso_hom_includeLeft_assoc, squareSpecIso_hom_includeRight,
        P.chartAssoc_fst_snd_assoc, ← Spec.map_comp, ← Spec.map_comp,
        ofHom_assoc_includeLeft_includeRight, Spec.map_comp, ← Category.assoc,
        cubeSpecIso_hom_includeRight]
      simp only [Category.assoc]
      rw [kunnethSpecIso_hom_includeLeft, P.chartD2congr_inv_fst_assoc]
  · simp only [Category.assoc]
    rw [cubeLSpecIso_hom_includeRight, P.chartAssoc_snd_assoc, ← Spec.map_comp,
      ofHom_assoc_includeRight, Spec.map_comp, ← Category.assoc,
      cubeSpecIso_hom_includeRight]
    simp only [Category.assoc]
    rw [kunnethSpecIso_hom_includeRight, P.chartD2congr_inv_snd_assoc]

/-- **(C1) coassoc, `CommRingCat` form** for the group-first co-action ring map: the left
convention `(id ⊗ ρ_L) ∘ ρ_L = assoc ∘ (Δ ⊗ id) ∘ ρ_L`. Assembled from `(ML)`, `(MA)`, `(MO)`,
`(K)` and the geometric `chartAssoc_mProd`, descended through `Spec`. -/
theorem coactionRing_coassoc :
    P.coactionRing ≫ CommRingCat.ofHom (Algebra.TensorProduct.map
        (AlgHom.id P.baseRing P.groupRing) P.coactionAlgLeft).toRingHom
      = P.coactionRing ≫ CommRingCat.ofHom (Algebra.TensorProduct.map (comulAlg G P)
          (AlgHom.id P.baseRing P.chartRing)).toRingHom
        ≫ CommRingCat.ofHom (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
          P.groupRing P.groupRing P.chartRing).toAlgHom.toRingHom := by
  refine Spec.map_injective ?_
  rw [← cancel_epi P.cubeSpecIso.hom]
  calc P.cubeSpecIso.hom ≫ Spec.map (P.coactionRing ≫ CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.groupRing)
            P.coactionAlgLeft).toRingHom)
      = P.mTwice ≫ P.U.toSpecΓ := by
        rw [Spec.map_comp, ← Category.assoc, cubeSpecIso_hom_mapIdCoaction, Category.assoc,
          Category.assoc, kunnethSpecIso_hom_specMap_coactionRing, mTwice, chartActRes]
        simp only [Category.assoc]
    _ = (P.chartAssoc ≫ P.mProd) ≫ P.U.toSpecΓ := by rw [chartAssoc_mProd]
    _ = P.cubeSpecIso.hom ≫ Spec.map (P.coactionRing ≫ CommRingCat.ofHom
          (Algebra.TensorProduct.map (comulAlg G P) (AlgHom.id P.baseRing P.chartRing)).toRingHom
          ≫ CommRingCat.ofHom (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
            P.groupRing P.groupRing P.chartRing).toAlgHom.toRingHom) := by
        rw [Spec.map_comp, Spec.map_comp]
        simp only [Category.assoc]
        rw [cubeSpecIso_hom_assoc_assoc, cubeLSpecIso_hom_mapComulId_assoc,
          kunnethSpecIso_hom_specMap_coactionRing, mProd, chartActRes]
        simp only [Category.assoc]

/-- **Stage 1: the left-convention coassoc** for `coactionAlgLeft`, `AlgHom` form. -/
theorem coactionAlgLeft_coassoc :
    (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.groupRing) P.coactionAlgLeft).comp
        P.coactionAlgLeft
      = (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing
          P.groupRing P.groupRing P.chartRing).toAlgHom.comp
        ((Algebra.TensorProduct.map (comulAlg G P) (AlgHom.id P.baseRing P.chartRing)).comp
          P.coactionAlgLeft) := by
  refine AlgHom.ext fun b => ?_
  have h := congrArg (fun m : P.chartRing ⟶ CommRingCat.of (P.groupRing ⊗[P.baseRing]
    (P.groupRing ⊗[P.baseRing] P.chartRing)) => m.hom b) P.coactionRing_coassoc
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  exact h

/-! ### Cocommutativity of the comultiplication (the group is abelian) -/

/-- The common base of the two coordinate points of the group square. -/
noncomputable abbrev sqMulBase : P.groupSquare ⟶ S :=
  pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes ≫ P.V.ι

/-- Swap the two factors of the group square `G|_V ×_V G|_V`. -/
noncomputable def squareSwap : P.groupSquare ⟶ P.groupSquare :=
  pullback.lift (pullback.snd P.groupToBaseRes P.groupToBaseRes)
    (pullback.fst P.groupToBaseRes P.groupToBaseRes) pullback.condition.symm

@[reassoc] theorem squareSwap_fst :
    P.squareSwap ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes
      = pullback.snd P.groupToBaseRes P.groupToBaseRes := pullback.lift_fst _ _ _

@[reassoc] theorem squareSwap_snd :
    P.squareSwap ≫ pullback.snd P.groupToBaseRes P.groupToBaseRes
      = pullback.fst P.groupToBaseRes P.groupToBaseRes := pullback.lift_snd _ _ _

/-- First coordinate point `g₁` of the group square. -/
noncomputable def sqMulPt₁ : E.Point P.sqMulBase :=
  ⟨pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι, by
    show (pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι) ≫ E.π
        = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes ≫ P.V.ι
    rw [Category.assoc, Category.assoc, G.ι_π,
      show P.groupOpen.ι ≫ G.π = P.groupToBaseRes ≫ P.V.ι from (Scheme.Hom.resLE_comp_ι _ _).symm]⟩

/-- Second coordinate point `g₂` of the group square. -/
noncomputable def sqMulPt₂ : E.Point P.sqMulBase :=
  ⟨pullback.snd P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι, by
    show (pullback.snd P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι) ≫ E.π
        = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes ≫ P.V.ι
    rw [Category.assoc, Category.assoc, G.ι_π,
      show P.groupOpen.ι ≫ G.π = P.groupToBaseRes ≫ P.V.ι from (Scheme.Hom.resLE_comp_ι _ _).symm,
      ← Category.assoc, ← pullback.condition, Category.assoc]⟩

@[simp] theorem sqMulPt₁_val : P.sqMulPt₁.1
    = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι := rfl
@[simp] theorem sqMulPt₂_val : P.sqMulPt₂.1
    = pullback.snd P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι := rfl

/-- **Commutativity of the group multiplication** on the square: swapping the two factors before
multiplying gives the same result (the subgroup of the elliptic curve is abelian). Proved by
`ι`-cancellation, both sides a coordinate point sum, finishing with `add_comm`. -/
theorem squareSwap_comp_squareMulRes : P.squareSwap ≫ P.squareMulRes = P.squareMulRes := by
  rw [← cancel_mono (P.groupOpen.ι ≫ G.ι)]
  have hgsts : P.groupSquareToSquare ≫ (Over.mk G.π ⊗ Over.mk G.π).hom = P.sqMulBase := by
    rw [← G.mulHom_π, ← Category.assoc]; exact P.squareMul_π
  have hfstι : P.groupSquareToSquare ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
      = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι := by
    rw [← Category.assoc, P.groupSquareToSquare_fst]; exact Category.assoc _ _ _
  have hsndι : P.groupSquareToSquare ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι
      = pullback.snd P.groupToBaseRes P.groupToBaseRes ≫ P.groupOpen.ι ≫ G.ι := by
    rw [← Category.assoc, P.groupSquareToSquare_snd]; exact Category.assoc _ _ _
  have hbaseP : (P.squareSwap ≫ P.groupSquareToSquare) ≫ (Over.mk G.π ⊗ Over.mk G.π).hom
      = P.sqMulBase := by
    rw [Category.assoc, hgsts]
    show (P.squareSwap ≫ pullback.fst P.groupToBaseRes P.groupToBaseRes) ≫ P.groupToBaseRes ≫ P.V.ι
        = pullback.fst P.groupToBaseRes P.groupToBaseRes ≫ P.groupToBaseRes ≫ P.V.ι
    rw [squareSwap_fst, ← Category.assoc, ← pullback.condition, Category.assoc]
  have EId : (hgsts ▸ EllipticCurve.Point.restrict E P.groupSquareToSquare
        (G.sqFstPoint + G.sqSndPoint) : E.Point P.sqMulBase) = P.sqMulPt₁ + P.sqMulPt₂ :=
    point_restrictT_add_eq hgsts G.sqFstPoint G.sqSndPoint P.sqMulPt₁ P.sqMulPt₂
      (by rw [sqMulPt₁_val]; exact hfstι) (by rw [sqMulPt₂_val]; exact hsndι)
  have ESwap : (hbaseP ▸ EllipticCurve.Point.restrict E
        (P.squareSwap ≫ P.groupSquareToSquare) (G.sqFstPoint + G.sqSndPoint) : E.Point P.sqMulBase)
      = P.sqMulPt₂ + P.sqMulPt₁ :=
    point_restrictT_add_eq hbaseP G.sqFstPoint G.sqSndPoint P.sqMulPt₂ P.sqMulPt₁
      (by
        show (P.squareSwap ≫ P.groupSquareToSquare)
            ≫ (fst (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι = P.sqMulPt₂.1
        rw [sqMulPt₂_val, Category.assoc, hfstι, ← Category.assoc, squareSwap_fst])
      (by
        show (P.squareSwap ≫ P.groupSquareToSquare)
            ≫ (snd (Over.mk G.π) (Over.mk G.π)).left ≫ G.ι = P.sqMulPt₁.1
        rw [sqMulPt₁_val, Category.assoc, hsndι, ← Category.assoc, squareSwap_snd])
  have hRHSm : P.squareMulRes ≫ P.groupOpen.ι ≫ G.ι = (P.sqMulPt₁ + P.sqMulPt₂).1 := by
    rw [← EId, point_base_congr]
    simp only [EllipticCurve.Point.restrict, Category.assoc, P.squareMulRes_comp_ι_assoc,
      squareMul, G.mulHom_ι]
  have hLHSm : (P.squareSwap ≫ P.squareMulRes) ≫ P.groupOpen.ι ≫ G.ι
      = (P.sqMulPt₂ + P.sqMulPt₁).1 := by
    rw [← ESwap, point_base_congr]
    simp only [EllipticCurve.Point.restrict, Category.assoc, P.squareMulRes_comp_ι_assoc,
      squareMul, G.mulHom_ι]
  rw [hLHSm, hRHSm, add_comm]

/-- Tensor identity: `A ↪ A ⊗ A` (left) then `comm` is `A ↪ A ⊗ A` (right). -/
theorem ofHom_includeLeft_comm :
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing)
        (A := P.groupRing) (B := P.groupRing))
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.comm P.baseRing P.groupRing
          P.groupRing).toAlgHom.toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := P.baseRing)
        (A := P.groupRing) (B := P.groupRing)).toRingHom := by
  rw [← CommRingCat.ofHom_comp]
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  show (Algebra.TensorProduct.comm P.baseRing P.groupRing P.groupRing)
      (a ⊗ₜ[P.baseRing] (1 : P.groupRing)) = (1 : P.groupRing) ⊗ₜ[P.baseRing] a
  rw [Algebra.TensorProduct.comm_tmul]

/-- Tensor identity: `A ↪ A ⊗ A` (right) then `comm` is `A ↪ A ⊗ A` (left). -/
theorem ofHom_includeRight_comm :
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := P.baseRing)
        (A := P.groupRing) (B := P.groupRing)).toRingHom
      ≫ CommRingCat.ofHom (Algebra.TensorProduct.comm P.baseRing P.groupRing
          P.groupRing).toAlgHom.toRingHom
      = CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := P.baseRing)
        (A := P.groupRing) (B := P.groupRing)) := by
  rw [← CommRingCat.ofHom_comp]
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  show (Algebra.TensorProduct.comm P.baseRing P.groupRing P.groupRing)
      ((1 : P.groupRing) ⊗ₜ[P.baseRing] a) = a ⊗ₜ[P.baseRing] (1 : P.groupRing)
  rw [Algebra.TensorProduct.comm_tmul]

/-- **The comm dual**: the square identification conjugates `Spec (comm)` into the square swap. -/
theorem squareSpecIso_hom_comm :
    P.squareSpecIso.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.comm P.baseRing
        P.groupRing P.groupRing).toAlgHom.toRingHom)
      = P.squareSwap ≫ P.squareSpecIso.hom := by
  refine spec_tensor_hom_ext ?_ ?_
  · simp only [Category.assoc]
    rw [← Spec.map_comp, ofHom_includeLeft_comm, squareSpecIso_hom_includeRight,
      squareSpecIso_hom_includeLeft, ← Category.assoc, squareSwap_fst]
  · simp only [Category.assoc]
    rw [← Spec.map_comp, ofHom_includeRight_comm, squareSpecIso_hom_includeLeft,
      squareSpecIso_hom_includeRight, ← Category.assoc, squareSwap_snd]

/-- **Cocommutativity, `CommRingCat` form**: `comm ∘ Δ = Δ`, dual to the group-multiplication
commutativity. -/
theorem groupPatchComul_comm :
    P.groupPatchComul ≫ CommRingCat.ofHom (Algebra.TensorProduct.comm P.baseRing
        P.groupRing P.groupRing).toAlgHom.toRingHom = P.groupPatchComul := by
  refine Spec.map_injective ?_
  rw [Spec.map_comp, ← cancel_epi P.squareSpecIso.hom, ← Category.assoc,
    squareSpecIso_hom_comm, Category.assoc, squareSpecIso_hom_comul, ← Category.assoc,
    squareSwap_comp_squareMulRes]

/-- **Cocommutativity, `AlgHom` form**: `comm ∘ Δ = Δ`. -/
theorem comulAlg_comm :
    (Algebra.TensorProduct.comm P.baseRing P.groupRing P.groupRing).toAlgHom.comp (comulAlg G P)
      = comulAlg G P := by
  refine AlgHom.ext fun a => ?_
  have h := congrArg (fun m : P.groupRing ⟶ CommRingCat.of (P.groupRing ⊗[P.baseRing] P.groupRing)
    => m.hom a) P.groupPatchComul_comm
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  exact h

/-! ### Stage 2: converting the left convention to the comodule (right) convention -/

/-- The reversing coherence `Θ ∘ assoc` on a pure tensor `s ⊗ b`, `s ∈ A ⊗ A`: it sends
`s ⊗ b ↦ b ⊗ comm(s)`. -/
theorem theta_assoc_tmul (s : P.groupRing ⊗[P.baseRing] P.groupRing) (b : P.chartRing) :
    (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing P.chartRing P.groupRing
        P.groupRing)
        ((Algebra.TensorProduct.map (Algebra.TensorProduct.comm P.baseRing P.groupRing
            P.chartRing).toAlgHom (AlgHom.id P.baseRing P.groupRing))
          ((Algebra.TensorProduct.comm P.baseRing P.groupRing
              (P.groupRing ⊗[P.baseRing] P.chartRing))
            ((Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing P.groupRing P.groupRing
                P.chartRing) (s ⊗ₜ[P.baseRing] b))))
      = b ⊗ₜ[P.baseRing] (Algebra.TensorProduct.comm P.baseRing P.groupRing P.groupRing) s := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [TensorProduct.add_tmul, map_add, hx, hy, TensorProduct.tmul_add]
  | tmul a a' =>
    simp only [Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgHom.id_apply]

/-- **The front coherence**: the pure reshuffle `Θ` composed with `assoc ∘ (Δ ⊗ id)` equals
`(id ⊗ Δ) ∘ comm`. This is where cocommutativity (`comulAlg_comm`) enters. -/
theorem hFront_coherence :
    (Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing P.chartRing P.groupRing
        P.groupRing).toAlgHom.comp
        ((Algebra.TensorProduct.map (Algebra.TensorProduct.comm P.baseRing P.groupRing
            P.chartRing).toAlgHom (AlgHom.id P.baseRing P.groupRing)).comp
          ((Algebra.TensorProduct.comm P.baseRing P.groupRing
              (P.groupRing ⊗[P.baseRing] P.chartRing)).toAlgHom.comp
            ((Algebra.TensorProduct.assoc P.baseRing P.baseRing P.baseRing P.groupRing P.groupRing
                P.chartRing).toAlgHom.comp
              (Algebra.TensorProduct.map (comulAlg G P) (AlgHom.id P.baseRing P.chartRing)))))
      = (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.chartRing) (comulAlg G P)).comp
          (Algebra.TensorProduct.comm P.baseRing P.groupRing P.chartRing).toAlgHom := by
  refine AlgHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
    rw [theta_assoc_tmul]
    have hcc := AlgHom.congr_fun P.comulAlg_comm a
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hcc
    rw [hcc]

theorem chartCoaction_isCoaction : IsCoaction P.chartCoaction where
  counit := by
    rw [show Bialgebra.counitAlgHom P.baseRing P.groupRing = counitAlg G P from
      counitAlgHom_eq_opens G P]
    have hcollapse : ((Algebra.TensorProduct.rid P.baseRing P.baseRing P.chartRing).toAlgHom.comp
            (Algebra.TensorProduct.map (AlgHom.id P.baseRing P.chartRing) (counitAlg G P))).comp
            (Algebra.TensorProduct.comm P.baseRing P.groupRing P.chartRing).toAlgHom
        = P.chartCounitCollapse := by
      refine AlgHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul a b =>
        simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.comm_tmul,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul,
          chartCounitCollapse, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
          Algebra.smul_def, _root_.mul_comm]
    rw [show P.chartCoaction = (Algebra.TensorProduct.comm P.baseRing P.groupRing
        P.chartRing).toAlgHom.comp P.coactionAlgLeft from rfl,
      ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hcollapse,
      chartCounitCollapse_comp_coactionAlgLeft]
  coassoc := by
    -- The Γ-dual of `translationAction_assoc`: assembled from `coactionAlgLeft_coassoc`
    -- (Stage 1, dualising `chartAssoc_mProd`) converted to the right (comodule) convention via
    -- the braiding naturality `comm_comp_map`, the front coherence `hFront_coherence`, and
    -- cocommutativity `comulAlg_comm`.
    rw [show Bialgebra.comulAlgHom P.baseRing P.groupRing = comulAlg G P from
        comulAlgHom_eq_opens G P,
      show P.chartCoaction = (Algebra.TensorProduct.comm P.baseRing P.groupRing
        P.chartRing).toAlgHom.comp P.coactionAlgLeft from rfl]
    refine AlgHom.ext fun b => ?_
    have hkey := AlgHom.congr_fun P.coactionAlgLeft_coassoc b
    have hfront := AlgHom.congr_fun P.hFront_coherence (P.coactionAlgLeft b)
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hkey hfront ⊢
    rw [show (Algebra.TensorProduct.map ((Algebra.TensorProduct.comm P.baseRing P.groupRing
          P.chartRing).toAlgHom.comp P.coactionAlgLeft) (AlgHom.id P.baseRing P.groupRing))
        = (Algebra.TensorProduct.map (Algebra.TensorProduct.comm P.baseRing P.groupRing
            P.chartRing).toAlgHom (AlgHom.id P.baseRing P.groupRing)).comp
          (Algebra.TensorProduct.map P.coactionAlgLeft (AlgHom.id P.baseRing P.groupRing)) from by
        rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp]]
    simp only [AlgHom.comp_apply]
    rw [← Algebra.TensorProduct.comm_comp_map_apply, hkey]
    exact hfront

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
