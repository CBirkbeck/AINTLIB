import ModularCurves.GroupScheme.PatchHopf
import ModularCurves.ForMathlib.Coaction

/-!
# The chart co-action is a co-action

`[HG-C1d]`: the chart co-action `chartCoaction : B →ₐ[R] B ⊗[R] A` (`StableCharts.lean`) satisfies
the two `IsCoaction` axioms (`ForMathlib/Coaction.lean`) with respect to the chart Hopf-algebra
bialgebra structure `instBialgebraOpens` (`PatchHopf.lean`). The two axioms are the `Γ`-duals of the
two group-action laws `translationAction_unit` / `translationAction_assoc`
(`SubgroupGroupObject.lean`), mirroring the Hopf coassoc/counit development in `PatchHopf.lean`.
-/

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
    -- REMAINING (WIP): the Γ-dual of `translationAction_assoc`, mirroring PatchHopf's
    -- `comulTop_coassoc`. Plan (analogous to the completed `counit` field above):
    --  1. Build the triple identification `Spec(A ⊗ (A ⊗ B)) ≅ G|_V ×_V (G|_V ×_V U)` by
    --     layering `pullbackSpecIso P.baseRing P.groupRing (A⊗B)` on `chartSpecIso`, with
    --     its three inclusion-leg duals (reuse `chartSpecIso_hom_includeLeft/Right`).
    --  2. Build the two triple-action scheme maps `m_twice = α∘(id_G ×_V α)` and
    --     `m_prod = α∘(μ ×_V id_U)∘assoc` on the triple, where α = `chartCoactionSpec`,
    --     μ = `squareMul` (from PatchHopf).
    --  3. Prove `m_twice = m_prod` by `cancel_mono P.U.ι` + the E.Point route (cube points
    --     `cubePt₁/₂/₃`, `point_restrictT_add_eq`), finishing with `add_assoc` — mirroring
    --     `assocScheme_leftMulSchemeL`.
    --  4. Γ-dualise (through the triple legs + `ΓSpecIso_inv_naturality`) to the AlgHom
    --     coassoc for `coactionAlgLeft`, then convert to `chartCoaction` via `comm`/`assoc`
    --     coherence (pure tensor algebra), and rewrite `comulAlgHom` via `comulAlgHom_eq_opens`.
    sorry

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
