/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.KernelDivisibilityChart
import ModularCurves.EllipticCurve.ModelRecord
import ModularCurves.EllipticCurve.MulByHomFlat
import ModularCurves.EllipticCurve.RecordGroupUnique
import ModularCurves.LevelStructure.IsoTransport
import ModularCurves.ForMathlib.BaseChangeAlongCompat
import ModularCurves.LevelStructure.Factorization

/-!
# Kernel divisibility: from the chart to arbitrary records (BB-FLAT N5)

The glue phase: `KernelNDivisible` for arbitrary records and tests, from
the chart-local calculus (`KernelDivisibilityChart.lean`). This file instantiates the
chart theorems at the projective model's Y-chart, transports them along the
`Point.baseChangeEquiv`/`pointAddEquiv` chain (the BB-QF pattern, hμ from K3), and glues
over a basic-open cover of the test.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 5

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj WeierstrassCurve TensorProduct

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

namespace EllipticCurve

section ModelInstance

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) [W.IsElliptic]

/-- The Y-chart of the projective model: the affine open containing the zero section. -/
noncomputable def modelYChart : (projModel W).Opens :=
  Proj.basicOpen (projIdeal W).quotientGrading
    ((projIdeal W).quotientGradingHom (MvPolynomial.X 1))

omit [W.IsElliptic] in
theorem modelYChart_isAffineOpen : IsAffineOpen (modelYChart W) :=
  Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 1) one_pos

theorem modelYChart_zero_mem (x : ↑(Spec (CommRingCat.of B))) :
    ((modelEllipticCurve W).zero).base x ∈ modelYChart W := by
  have h := projModelZero_preimage_yChart W
  have h2 : x ∈ projModelZero W ⁻¹ᵁ (modelYChart W) := by
    rw [show projModelZero W ⁻¹ᵁ (modelYChart W) = ⊤ from h]
    trivial
  exact h2


set_option backward.isDefEq.respectTransparency false in
/-- **(MODEL-DIV)** Kernel divisibility for the projective model record. -/
theorem modelKernel_div {R S' : CommRingCat.{u}} {φ : R ⟶ S'}
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec (CommRingCat.of B)} (N : ℕ) (hN : IsUnit ((N : ℕ) : ↑R))
    (P : (modelEllipticCurve W).Point t)
    (hP : Point.restrict (modelEllipticCurve W) (Spec.map φ) P = 0) :
    ∃ δ : (modelEllipticCurve W).Point t,
      Point.restrict (modelEllipticCurve W) (Spec.map φ) δ = 0 ∧ (N : ℤ) • δ = P := by
  have hU := modelYChart_isAffineOpen W
  have heU : ∀ x : ↑(Spec (CommRingCat.of B)),
      ((modelEllipticCurve W).zero).base x ∈ modelYChart W := modelYChart_zero_mem W
  have htaut : ∀ x : ↑(Spec Γ((modelEllipticCurve W).E, modelYChart W)),
      (hU.fromSpec).base x ∈ modelYChart W := by
    intro x
    have hr := IsAffineOpen.range_fromSpec hU
    have h2 : (hU.fromSpec).base x ∈ Set.range (hU.fromSpec).base := Set.mem_range_self x
    rwa [hr] at h2
  have hz : ∀ x : ↑(Spec Γ((modelEllipticCurve W).E, modelYChart W)),
      ((0 : (modelEllipticCurve W).Point
        (hU.fromSpec ≫ (modelEllipticCurve W).π))).1.base x ∈ modelYChart W := by
    intro x
    rw [(modelEllipticCurve W).point_zero_val]
    rw [Scheme.Hom.comp_apply]
    exact heU _
  exact exists_kernel_div hU heU htaut hz hφ hφ2 N hN P hP

set_option backward.isDefEq.respectTransparency false in
/-- **(MODEL-INJ)** Kernel `N`-injectivity for the projective model record. -/
theorem modelKernel_inj {R S' : CommRingCat.{u}} {φ : R ⟶ S'}
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec (CommRingCat.of B)} (N : ℕ) (hN : IsUnit ((N : ℕ) : ↑R))
    (P : (modelEllipticCurve W).Point t)
    (hP : Point.restrict (modelEllipticCurve W) (Spec.map φ) P = 0)
    (h0 : (N • P : (modelEllipticCurve W).Point t) = 0) : P = 0 := by
  have hU := modelYChart_isAffineOpen W
  have heU : ∀ x : ↑(Spec (CommRingCat.of B)),
      ((modelEllipticCurve W).zero).base x ∈ modelYChart W := modelYChart_zero_mem W
  have htaut : ∀ x : ↑(Spec Γ((modelEllipticCurve W).E, modelYChart W)),
      (hU.fromSpec).base x ∈ modelYChart W := by
    intro x
    have hr := IsAffineOpen.range_fromSpec hU
    have h2 : (hU.fromSpec).base x ∈ Set.range (hU.fromSpec).base := Set.mem_range_self x
    rwa [hr] at h2
  have hz : ∀ x : ↑(Spec Γ((modelEllipticCurve W).E, modelYChart W)),
      ((0 : (modelEllipticCurve W).Point
        (hU.fromSpec ≫ (modelEllipticCurve W).π))).1.base x ∈ modelYChart W := by
    intro x
    rw [(modelEllipticCurve W).point_zero_val]
    rw [Scheme.Hom.comp_apply]
    exact heU _
  exact kernel_eq_zero_of_nsmul_eq_zero hU heU htaut hz hφ hφ2 N hN P hP h0

end ModelInstance

section PieceTransport

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(PIECE-DIV)** Kernel divisibility over a test factoring through an atlas chart:
transport along the base-change/pointed-iso chain (hμ from K3) to the model record and
apply MODEL-DIV. -/
theorem kernel_div_of_chartFactor (A : WeierstrassAtlasData E.toEllipticCurveGeom)
    (i : A.ι) {R S' : CommRingCat.{u}} {φ : R ⟶ S'}
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    (tB : Spec R ⟶ Spec Γ(S, (A.U i).1))
    (N : ℕ) (hN : IsUnit ((N : ℕ) : ↑R))
    (P : E.Point (tB ≫ chartToBase A i))
    (hP : Point.restrict E (Spec.map φ) P = 0) :
    ∃ δ : E.Point (tB ≫ chartToBase A i),
      Point.restrict E (Spec.map φ) δ = 0 ∧ (N : ℤ) • δ = P := by
  classical
  haveI := A.elliptic i
  -- the transport chain
  have hη : (η[(E.baseChange (chartToBase A i)).asOver] :
      𝟙_ (Over (Spec Γ(S, (A.U i).1))) ⟶ (E.baseChange (chartToBase A i)).asOver) ≫
      (chartOverIso A i).hom = η[(modelEllipticCurve (A.W i)).asOver] :=
    chartGrp_one A E.grp E.one_eq_zero i
  have hμ := isMonHom_of_pointedIso_records (E.baseChange (chartToBase A i))
    (modelEllipticCurve (A.W i)) (chartOverIso A i) hη
  set eqc : E.Point (tB ≫ chartToBase A i) ≃+
      (modelEllipticCurve (A.W i)).Point tB :=
    (Point.baseChangeEquiv E (chartToBase A i) tB).symm.trans
      (pointAddEquiv (chartOverIso A i) hμ tB) with heqc
  have heqc_coe : ∀ Q : E.Point (tB ≫ chartToBase A i),
      (eqc Q).1 = pullback.lift Q.1 tB Q.2 ≫ (chartTotalIso A i).hom := fun Q => rfl
  have heqc_symm_coe : ∀ Qm : (modelEllipticCurve (A.W i)).Point tB,
      (eqc.symm Qm).1 = (Qm.1 ≫ (chartTotalIso A i).inv) ≫
        pullback.fst E.π (chartToBase A i) := fun Qm => rfl
  -- transported kernel membership
  have hPm : Point.restrict (modelEllipticCurve (A.W i)) (Spec.map φ) (eqc P) = 0 := by
    refine Subtype.ext ?_
    show Spec.map φ ≫ (eqc P).1 = _
    rw [(modelEllipticCurve (A.W i)).point_zero_val]
    rw [heqc_coe]
    have hPval : Spec.map φ ≫ P.1 =
        (Spec.map φ ≫ (tB ≫ chartToBase A i)) ≫ E.zero := by
      have h1 := congrArg Subtype.val hP
      rw [show ((0 : E.Point (Spec.map φ ≫ (tB ≫ chartToBase A i))) :
        Spec S' ⟶ E.E) = (Spec.map φ ≫ (tB ≫ chartToBase A i)) ≫ E.zero from
        E.point_zero_val _] at h1
      exact h1
    -- the restricted lift is the chart zero lift
    have hliftres : Spec.map φ ≫ pullback.lift P.1 tB P.2 =
        (Spec.map φ ≫ tB) ≫ chartZero A i := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc]
        rw [show chartZero A i ≫ pullback.fst E.toEllipticCurveGeom.π (chartToBase A i) =
          chartToBase A i ≫ E.toEllipticCurveGeom.zero from chartZero_fst A i]
        rw [hPval]
        simp only [Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc]
        rw [show chartZero A i ≫ pullback.snd E.toEllipticCurveGeom.π (chartToBase A i) =
          𝟙 _ from chartZero_snd A i]
        rw [Category.comp_id]
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ (chartTotalIso A i).hom) hliftres).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Spec.map φ ≫ tB) ≫ ·) (chartZero_totalIso A i)).trans ?_
    rfl
  -- solve at the model
  obtain ⟨δm, hδmK, hδmN⟩ := modelKernel_div (A.W i) hφ hφ2 N hN (eqc P) hPm
  refine ⟨eqc.symm δm, ?_, ?_⟩
  · -- kernel membership pulls back
    refine Subtype.ext ?_
    show Spec.map φ ≫ (eqc.symm δm).1 = _
    rw [E.point_zero_val]
    rw [heqc_symm_coe]
    have hδmval : Spec.map φ ≫ δm.1 = (Spec.map φ ≫ tB) ≫ projModelZero (A.W i) := by
      have h1 := congrArg Subtype.val hδmK
      rw [show ((0 : (modelEllipticCurve (A.W i)).Point (Spec.map φ ≫ tB)) :
        Spec S' ⟶ (modelEllipticCurve (A.W i)).E) =
        (Spec.map φ ≫ tB) ≫ projModelZero (A.W i) from
        (modelEllipticCurve (A.W i)).point_zero_val _] at h1
      exact h1
    have hzeroinv : projModelZero (A.W i) ≫ (chartTotalIso A i).inv = chartZero A i := by
      rw [← chartZero_totalIso A i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ pullback.fst E.π (chartToBase A i))
      ((Category.assoc _ _ _).symm)).trans ?_
    refine (congrArg (fun m => (m ≫ (chartTotalIso A i).inv) ≫
      pullback.fst E.π (chartToBase A i)) hδmval).trans ?_
    refine (congrArg (· ≫ pullback.fst E.π (chartToBase A i))
      (Category.assoc _ _ _)).trans ?_
    refine (congrArg (· ≫ pullback.fst E.π (chartToBase A i))
      (congrArg ((Spec.map φ ≫ tB) ≫ ·) hzeroinv)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Spec.map φ ≫ tB) ≫ ·) (chartZero_fst A i)).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    exact Category.assoc _ _ _
  · -- the scalar identity pulls back
    have h1 : eqc ((N : ℤ) • eqc.symm δm) = eqc P := by
      rw [map_zsmul, AddEquiv.apply_symm_apply, hδmN]
    exact eqc.injective h1

/-- **(PIECE-INJ)** Kernel `N`-injectivity over a chart-factoring test. -/
theorem kernel_inj_of_chartFactor (A : WeierstrassAtlasData E.toEllipticCurveGeom)
    (i : A.ι) {R S' : CommRingCat.{u}} {φ : R ⟶ S'}
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    (tB : Spec R ⟶ Spec Γ(S, (A.U i).1))
    (N : ℕ) (hN : IsUnit ((N : ℕ) : ↑R))
    (P : E.Point (tB ≫ chartToBase A i))
    (hP : Point.restrict E (Spec.map φ) P = 0)
    (h0 : (N • P : E.Point (tB ≫ chartToBase A i)) = 0) : P = 0 := by
  classical
  haveI := A.elliptic i
  have hη : (η[(E.baseChange (chartToBase A i)).asOver] :
      𝟙_ (Over (Spec Γ(S, (A.U i).1))) ⟶ (E.baseChange (chartToBase A i)).asOver) ≫
      (chartOverIso A i).hom = η[(modelEllipticCurve (A.W i)).asOver] :=
    chartGrp_one A E.grp E.one_eq_zero i
  have hμ := isMonHom_of_pointedIso_records (E.baseChange (chartToBase A i))
    (modelEllipticCurve (A.W i)) (chartOverIso A i) hη
  set eqc : E.Point (tB ≫ chartToBase A i) ≃+
      (modelEllipticCurve (A.W i)).Point tB :=
    (Point.baseChangeEquiv E (chartToBase A i) tB).symm.trans
      (pointAddEquiv (chartOverIso A i) hμ tB) with heqc
  have heqc_coe : ∀ Q : E.Point (tB ≫ chartToBase A i),
      (eqc Q).1 = pullback.lift Q.1 tB Q.2 ≫ (chartTotalIso A i).hom := fun Q => rfl
  have hPm : Point.restrict (modelEllipticCurve (A.W i)) (Spec.map φ) (eqc P) = 0 := by
    refine Subtype.ext ?_
    show Spec.map φ ≫ (eqc P).1 = _
    rw [(modelEllipticCurve (A.W i)).point_zero_val]
    rw [heqc_coe]
    have hPval : Spec.map φ ≫ P.1 =
        (Spec.map φ ≫ (tB ≫ chartToBase A i)) ≫ E.zero := by
      have h1 := congrArg Subtype.val hP
      rw [show ((0 : E.Point (Spec.map φ ≫ (tB ≫ chartToBase A i))) :
        Spec S' ⟶ E.E) = (Spec.map φ ≫ (tB ≫ chartToBase A i)) ≫ E.zero from
        E.point_zero_val _] at h1
      exact h1
    have hliftres : Spec.map φ ≫ pullback.lift P.1 tB P.2 =
        (Spec.map φ ≫ tB) ≫ chartZero A i := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc]
        rw [show chartZero A i ≫ pullback.fst E.toEllipticCurveGeom.π (chartToBase A i) =
          chartToBase A i ≫ E.toEllipticCurveGeom.zero from chartZero_fst A i]
        rw [hPval]
        simp only [Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc]
        rw [show chartZero A i ≫ pullback.snd E.toEllipticCurveGeom.π (chartToBase A i) =
          𝟙 _ from chartZero_snd A i]
        rw [Category.comp_id]
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ (chartTotalIso A i).hom) hliftres).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Spec.map φ ≫ tB) ≫ ·) (chartZero_totalIso A i)).trans ?_
    rfl
  have h0m : (N • eqc P : (modelEllipticCurve (A.W i)).Point tB) = 0 := by
    have h1 := congrArg eqc h0
    rw [show (N • P : E.Point (tB ≫ chartToBase A i)) = ((N : ℤ) • P : E.Point _) from
      (natCast_zsmul P N).symm, map_zsmul, map_zero] at h1
    rw [show (N • eqc P : (modelEllipticCurve (A.W i)).Point tB) =
      ((N : ℤ) • eqc P : (modelEllipticCurve (A.W i)).Point tB) from
      (natCast_zsmul (eqc P) N).symm]
    exact h1
  have hzero := modelKernel_inj (A.W i) hφ hφ2 N hN (eqc P) hPm h0m
  have h2 := congrArg eqc.symm hzero
  rwa [AddEquiv.symm_apply_apply, map_zero] at h2

/-- **(PIECE-UNIQ, value form)** Two kernel-valued solutions of the same `[N]`-equation
over a chart-factoring test have equal underlying morphisms — the cast-free interface for
the gluing. -/
theorem kernel_val_unique_of_chartFactor (A : WeierstrassAtlasData E.toEllipticCurveGeom)
    (i : A.ι) {R S' : CommRingCat.{u}} {φ : R ⟶ S'}
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    (tB : Spec R ⟶ Spec Γ(S, (A.U i).1))
    (N : ℕ) (hN : IsUnit ((N : ℕ) : ↑R))
    (v₁ v₂ : Spec R ⟶ E.E)
    (hπ₁ : v₁ ≫ E.π = tB ≫ chartToBase A i) (hπ₂ : v₂ ≫ E.π = tB ≫ chartToBase A i)
    (hK₁ : Spec.map φ ≫ v₁ = (Spec.map φ ≫ (tB ≫ chartToBase A i)) ≫ E.zero)
    (hK₂ : Spec.map φ ≫ v₂ = (Spec.map φ ≫ (tB ≫ chartToBase A i)) ≫ E.zero)
    (hNv : v₁ ≫ E.mulByHom (N : ℤ) = v₂ ≫ E.mulByHom (N : ℤ)) : v₁ = v₂ := by
  set P₁ : E.Point (tB ≫ chartToBase A i) := ⟨v₁, hπ₁⟩ with hP₁
  set P₂ : E.Point (tB ≫ chartToBase A i) := ⟨v₂, hπ₂⟩ with hP₂
  have hK₁' : Point.restrict E (Spec.map φ) P₁ = 0 := by
    refine Subtype.ext ?_
    show Spec.map φ ≫ v₁ = _
    rw [E.point_zero_val]
    exact hK₁
  have hK₂' : Point.restrict E (Spec.map φ) P₂ = 0 := by
    refine Subtype.ext ?_
    show Spec.map φ ≫ v₂ = _
    rw [E.point_zero_val]
    exact hK₂
  have hsmul : ((N : ℤ) • P₁ : E.Point _) = (N : ℤ) • P₂ := by
    refine Subtype.ext ?_
    rw [E.point_smul_eq_comp_mulBy, E.point_smul_eq_comp_mulBy]
    exact hNv
  have hdK : Point.restrict E (Spec.map φ) (P₁ - P₂) = 0 := by
    rw [E.restrict_sub, hK₁', hK₂', sub_zero]
  have hd0 : (N • (P₁ - P₂) : E.Point _) = 0 := by
    have h1 : ((N : ℤ) • (P₁ - P₂) : E.Point _) = 0 := by
      rw [smul_sub, hsmul, sub_self]
    rwa [natCast_zsmul] at h1
  have hd := kernel_inj_of_chartFactor E A i hφ hφ2 tB N hN (P₁ - P₂) hdK hd0
  have h2 : P₁ = P₂ := by
    have h3 := congrArg (· + P₂) hd
    simpa [sub_add_cancel] using h3
  exact congrArg Subtype.val h2

end PieceTransport

section Overlap

variable {A' : CommRingCat.{u}} (a b : ↑A')

/-- The overlap ring of two basic localizations — kept as a separate `def` because inlining
the tensor-of-localizations churns instance paths. -/
private def OverlapRing : Type u :=
  Localization.Away a ⊗[↑A'] Localization.Away b

private noncomputable instance : CommRing (OverlapRing a b) :=
  inferInstanceAs (CommRing (Localization.Away a ⊗[↑A'] Localization.Away b))

private noncomputable instance : Algebra ↑A' (OverlapRing a b) :=
  inferInstanceAs (Algebra ↑A' (Localization.Away a ⊗[↑A'] Localization.Away b))

/-- The left inclusion of the overlap. -/
private noncomputable def overlapInL : Localization.Away a →+* OverlapRing a b :=
  Algebra.TensorProduct.includeLeftRingHom

/-- The right inclusion of the overlap. -/
private noncomputable def overlapInR : Localization.Away b →+* OverlapRing a b :=
  (Algebra.TensorProduct.includeRight (R := ↑A') (A := Localization.Away a)
    (B := Localization.Away b)).toRingHom

private theorem overlapInL_alg :
    (overlapInL a b).comp (algebraMap ↑A' (Localization.Away a)) =
      algebraMap ↑A' (OverlapRing a b) :=
  RingHom.ext fun _ => rfl

private theorem overlapInR_alg :
    (overlapInR a b).comp (algebraMap ↑A' (Localization.Away b)) =
      algebraMap ↑A' (OverlapRing a b) :=
  RingHom.ext fun x => (Algebra.TensorProduct.algebraMap_apply' x).symm

/-- The pullback-of-Spec identification, restated at the overlap spelling. -/
private theorem overlap_inv_fst :
    (pullbackSpecIso ↑A' (Localization.Away a) (Localization.Away b)).inv ≫
      pullback.fst _ _ = Spec.map (CommRingCat.ofHom (overlapInL a b)) := by
  have h := pullbackSpecIso_inv_fst ↑A' (Localization.Away a) (Localization.Away b)
  exact h

private theorem overlap_inv_snd :
    (pullbackSpecIso ↑A' (Localization.Away a) (Localization.Away b)).inv ≫
      pullback.snd _ _ = Spec.map (CommRingCat.ofHom (overlapInR a b)) := by
  have h := pullbackSpecIso_inv_snd ↑A' (Localization.Away a) (Localization.Away b)
  exact h

end Overlap

section Glue

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- Transport of points along an equality of base morphisms. -/
-- `Point.castBase` / `Point.castBase_coe` live in `LevelStructure/Factorization.lean`
-- (imported above); both consumers of them sit downstream of that file, not of this one.

@[simp] theorem Point.castBase_symm_coe {T : Scheme.{u}} {g g' : T ⟶ S} (h : g = g')
    (P : E.Point g') : ((Point.castBase E h).symm P).1 = P.1 := by subst h; rfl

/-- Transport of "`N` is a unit" along a ring homomorphism. -/
private theorem isUnit_natCast_of_ringHom {A B : Type*} [Semiring A] [Semiring B] {N : ℕ}
    (h : IsUnit ((N : ℕ) : A)) (f : A →+* B) : IsUnit ((N : ℕ) : B) := by
  have h2 := h.map f
  rwa [map_natCast] at h2

/-- The reduction of a square-zero ideal along a ring homomorphism is again square-zero:
the kernel of the quotient by `I.map f` squares to `⊥`. -/
private theorem ker_mk_map_sq_eq_bot {A B : Type*} [CommRing A] [CommRing B] {I : Ideal A}
    (hI : I ^ 2 = ⊥) (f : A →+* B) :
    RingHom.ker (Ideal.Quotient.mk (I.map f)) ^ 2 = ⊥ := by
  rw [Ideal.mk_ker, ← Ideal.map_pow, hI, Ideal.map_bot]

/-- **(N5, the KernelNDivisible discharge)** The square-zero point kernels of a working
record are `N`-divisible when `N` is invertible on the base. -/
theorem kernelNDivisible_of_nIsInvertible (N : ℕ) (h : NIsInvertible S N) :
    E.KernelNDivisible N := by
  classical
  intro A' I hI b' ε hε
  set φ : A' ⟶ CommRingCat.of (↑A' ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I) with hφdef
  have hφ : Function.Surjective φ.hom := Ideal.Quotient.mk_surjective
  have hφ2 : RingHom.ker φ.hom ^ 2 = ⊥ := by
    show RingHom.ker (Ideal.Quotient.mk I) ^ 2 = ⊥
    rw [Ideal.mk_ker]
    exact hI
  -- `N` is a unit on the test
  have hNA' : IsUnit ((N : ℕ) : ↑A') :=
    isUnit_natCast_of_ringHom (h : IsUnit ((N : ℕ) : ↑Γ(S, ⊤)))
      (b'.appTop ≫ (Scheme.ΓSpecIso A').hom).hom
  -- the atlas and the basic-open cover adapted to it
  set A : WeierstrassAtlasData E.toEllipticCurveGeom := E.toEllipticCurveGeom.atlas with hA
  have hcover : ∀ p : ↑(Spec A'), ∃ (a : ↑A') (i : A.ι),
      p ∈ PrimeSpectrum.basicOpen a ∧
      ∀ q : ↑(Spec A'), q ∈ PrimeSpectrum.basicOpen a → b'.base q ∈ (A.U i).1 := by
    intro p
    obtain ⟨i, hi⟩ := A.covers (b'.base p)
    have hopen : IsOpen (b'.base ⁻¹' ((A.U i).1 : Set S)) :=
      (A.U i).1.2.preimage b'.continuous
    have hmem : p ∈ b'.base ⁻¹' ((A.U i).1 : Set S) := hi
    obtain ⟨V, ⟨a, rfl⟩, haV, hVsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem hopen
    exact ⟨a, i, haV, fun q hq => hVsub hq⟩
  choose aa ii hmemA hsubA using hcover
  -- the per-piece localized tests and their chart factorisations
  have hfac : ∀ p : ↑(Spec A'), ∃ tB : Spec (CommRingCat.of
        (Localization.Away (aa p))) ⟶ Spec Γ(S, (A.U (ii p)).1),
      tB ≫ chartToBase A (ii p) =
        Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p)))) ≫ b' := by
    intro p
    have hrange : Set.range ((Spec.map (CommRingCat.ofHom
        (algebraMap ↑A' (Localization.Away (aa p)))) ≫ b')).base ⊆
        Set.range (A.U (ii p)).1.ι.base := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      rw [Scheme.Hom.comp_apply]
      refine hsubA p _ ?_
      have h2 := PrimeSpectrum.localization_away_comap_range
        (Localization.Away (aa p)) (aa p)
      have h3 : (Spec.map (CommRingCat.ofHom
          (algebraMap ↑A' (Localization.Away (aa p))))).base x ∈
          Set.range (PrimeSpectrum.comap (algebraMap ↑A' (Localization.Away (aa p)))) :=
        Set.mem_range_self x
      rwa [h2] at h3
    refine ⟨IsOpenImmersion.lift (A.U (ii p)).1.ι _ hrange ≫ (A.U (ii p)).2.isoSpec.hom, ?_⟩
    rw [chartToBase, Category.assoc, Iso.hom_inv_id_assoc]
    exact IsOpenImmersion.lift_fac _ _ hrange
  choose tB htB using hfac
  -- the per-piece square-zero data
  have hφpsurj : ∀ p : ↑(Spec A'), Function.Surjective (CommRingCat.ofHom
      (Ideal.Quotient.mk (I.map (algebraMap ↑A' (Localization.Away (aa p)))))).hom :=
    fun p => Ideal.Quotient.mk_surjective
  have hφp2 : ∀ p : ↑(Spec A'), RingHom.ker (CommRingCat.ofHom
      (Ideal.Quotient.mk (I.map (algebraMap ↑A' (Localization.Away (aa p)))))).hom ^ 2 =
      ⊥ :=
    fun p => ker_mk_map_sq_eq_bot hI (algebraMap ↑A' (Localization.Away (aa p)))
  -- `N` is a unit on each piece
  have hNp : ∀ p : ↑(Spec A'), IsUnit ((N : ℕ) :
      Localization.Away (aa p)) :=
    fun p => isUnit_natCast_of_ringHom hNA' (algebraMap ↑A' (Localization.Away (aa p)))
  -- the per-piece kernel points
  have hεp : ∀ p : ↑(Spec A'),
      Point.restrict E (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I.map (algebraMap ↑A' (Localization.Away (aa p)))))))
        ((Point.castBase E (htB p).symm) (Point.restrict E
          (Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p))))) ε)) =
      0 := by
    intro p
    refine Subtype.ext ?_
    show Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (I.map (algebraMap ↑A' (Localization.Away (aa p)))))) ≫
      ((Point.castBase E (htB p).symm) (Point.restrict E
        (Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p))))) ε)).1 =
      _
    rw [E.point_zero_val, Point.castBase_coe]
    show Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (I.map (algebraMap ↑A' (Localization.Away (aa p)))))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p)))) ≫ ε.1) = _
    -- the quotientMap square
    have hle : I ≤ (I.map (algebraMap ↑A' (Localization.Away (aa p)))).comap
        (algebraMap ↑A' (Localization.Away (aa p))) := Ideal.le_comap_map
    have hsq : CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p))) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk
          (I.map (algebraMap ↑A' (Localization.Away (aa p))))) =
        φ ≫ CommRingCat.ofHom (Ideal.quotientMap _
          (algebraMap ↑A' (Localization.Away (aa p))) hle) := by
      refine CommRingCat.hom_ext ?_
      exact (Ideal.quotientMap_comp_mk hle).symm
    have hspec : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (I.map (algebraMap ↑A' (Localization.Away (aa p)))))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p)))) =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap _
          (algebraMap ↑A' (Localization.Away (aa p))) hle)) ≫ Spec.map φ := by
      rw [← Spec.map_comp, ← Spec.map_comp, hsq]
    have hεval : Spec.map φ ≫ ε.1 = (Spec.map φ ≫ b') ≫ E.zero := by
      have h1 := congrArg Subtype.val hε
      rw [show ((0 : E.Point (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b')) :
        Spec (CommRingCat.of (↑A' ⧸ I)) ⟶ E.E) =
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b') ≫ E.zero from
        E.point_zero_val _] at h1
      exact h1
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ ε.1) hspec).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (Spec.map (CommRingCat.ofHom (Ideal.quotientMap _
      (algebraMap ↑A' (Localization.Away (aa p))) hle)) ≫ ·) hεval).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ E.zero) ((Category.assoc _ _ _).symm)).trans ?_
    refine (congrArg (fun m => (m ≫ b') ≫ E.zero) hspec.symm).trans ?_
    refine (congrArg (· ≫ E.zero) (Category.assoc _ _ _)).trans ?_
    refine (congrArg (fun m => (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (I.map (algebraMap ↑A' (Localization.Away (aa p)))))) ≫ m) ≫ E.zero)
      (htB p).symm).trans ?_
    rfl
  -- the per-piece solutions
  have hsol : ∀ p : ↑(Spec A'), ∃ δp : E.Point (tB p ≫ chartToBase A (ii p)),
      Point.restrict E (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I.map (algebraMap ↑A' (Localization.Away (aa p))))))) δp = 0 ∧
      (N : ℤ) • δp = (Point.castBase E (htB p).symm) (Point.restrict E
        (Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p))))) ε) :=
    fun p => kernel_div_of_chartFactor E A (ii p) (hφpsurj p) (hφp2 p) (tB p) N (hNp p)
      _ (hεp p)
  choose δp hδpK hδpN using hsol
  -- value forms of the piece data
  have hvπ : ∀ p : ↑(Spec A'), (δp p).1 ≫ E.π = tB p ≫ chartToBase A (ii p) :=
    fun p => (δp p).2
  have hvK : ∀ p : ↑(Spec A'),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (I.map (algebraMap ↑A' (Localization.Away (aa p)))))) ≫ (δp p).1 =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (I.map (algebraMap ↑A' (Localization.Away (aa p)))))) ≫
        (tB p ≫ chartToBase A (ii p))) ≫ E.zero := by
    intro p
    have h1 := congrArg Subtype.val (hδpK p)
    rw [show ((0 : E.Point (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (I.map (algebraMap ↑A' (Localization.Away (aa p)))))) ≫
      (tB p ≫ chartToBase A (ii p)))) :
      Spec (CommRingCat.of ((Localization.Away (aa p)) ⧸
        (I.map (algebraMap ↑A' (Localization.Away (aa p)))))) ⟶ E.E) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (I.map (algebraMap ↑A' (Localization.Away (aa p)))))) ≫
        (tB p ≫ chartToBase A (ii p))) ≫ E.zero from E.point_zero_val _] at h1
    exact h1
  have hvN : ∀ p : ↑(Spec A'), (δp p).1 ≫ E.mulByHom (N : ℤ) =
      Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p)))) ≫ ε.1 := by
    intro p
    have h1 := congrArg Subtype.val (hδpN p)
    rw [E.point_smul_eq_comp_mulBy] at h1
    rw [h1, Point.castBase_coe]
    rfl
  -- the overlap agreement
  have hcompat : ∀ p q : ↑(Spec A'),
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap ↑A'
          (Localization.Away (aa p)))))
        (Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa q))))) ≫
        (δp p).1 =
      pullback.snd _ _ ≫ (δp q).1 := by
    intro p q
    rw [← cancel_epi (pullbackSpecIso ↑A' (Localization.Away (aa p))
      (Localization.Away (aa q))).inv]
    rw [← Category.assoc, ← Category.assoc, overlap_inv_fst, overlap_inv_snd]
    -- the algebra triangles at the overlap spelling
    have htriL : Spec.map (CommRingCat.ofHom (overlapInL (aa p) (aa q))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p)))) =
        Spec.map (CommRingCat.ofHom (algebraMap ↑A' (OverlapRing (aa p) (aa q)))) := by
      rw [← Spec.map_comp]
      refine congrArg Spec.map ?_
      refine CommRingCat.hom_ext ?_
      exact overlapInL_alg (aa p) (aa q)
    have htriR : Spec.map (CommRingCat.ofHom (overlapInR (aa p) (aa q))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa q)))) =
        Spec.map (CommRingCat.ofHom (algebraMap ↑A' (OverlapRing (aa p) (aa q)))) := by
      rw [← Spec.map_comp]
      refine congrArg Spec.map ?_
      refine CommRingCat.hom_ext ?_
      exact overlapInR_alg (aa p) (aa q)
    -- the overlap chart factorisation (through the p-chart)
    have hrangeT : Set.range ((Spec.map (CommRingCat.ofHom (algebraMap ↑A'
        (OverlapRing (aa p) (aa q)))) ≫ b')).base ⊆
        Set.range (A.U (ii p)).1.ι.base := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      refine hsubA p _ ?_
      have hunit : IsUnit (algebraMap ↑A' (OverlapRing (aa p) (aa q)) (aa p)) := by
        have h1 : IsUnit (algebraMap ↑A' (Localization.Away (aa p)) (aa p)) :=
          IsLocalization.Away.algebraMap_isUnit (aa p)
        have h2 := h1.map (overlapInL (aa p) (aa q))
        rwa [show (overlapInL (aa p) (aa q)) (algebraMap ↑A'
          (Localization.Away (aa p)) (aa p)) =
          algebraMap ↑A' (OverlapRing (aa p) (aa q)) (aa p) from
          congrArg (fun (m : ↑A' →+* OverlapRing (aa p) (aa q)) => m (aa p))
            (overlapInL_alg (aa p) (aa q))] at h2
      intro hy
      exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy hunit)
    set tT : Spec (CommRingCat.of (OverlapRing (aa p) (aa q))) ⟶
        Spec Γ(S, (A.U (ii p)).1) :=
      IsOpenImmersion.lift (A.U (ii p)).1.ι _ hrangeT ≫ (A.U (ii p)).2.isoSpec.hom
      with htT_def
    have htT : tT ≫ chartToBase A (ii p) =
        Spec.map (CommRingCat.ofHom (algebraMap ↑A' (OverlapRing (aa p) (aa q)))) ≫ b' := by
      rw [htT_def, chartToBase, Category.assoc, Iso.hom_inv_id_assoc]
      exact IsOpenImmersion.lift_fac _ _ hrangeT
    -- square-zero data over the overlap
    have hφT2 : RingHom.ker (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap ↑A'
        (OverlapRing (aa p) (aa q)))))).hom ^ 2 = ⊥ :=
      ker_mk_map_sq_eq_bot hI (algebraMap ↑A' (OverlapRing (aa p) (aa q)))
    have hNT : IsUnit ((N : ℕ) : OverlapRing (aa p) (aa q)) :=
      isUnit_natCast_of_ringHom hNA' (algebraMap ↑A' (OverlapRing (aa p) (aa q)))
    -- the kernel squares
    have hmapL : I.map (algebraMap ↑A' (OverlapRing (aa p) (aa q))) =
        (I.map (algebraMap ↑A' (Localization.Away (aa p)))).map
          (overlapInL (aa p) (aa q)) := by
      rw [Ideal.map_map, overlapInL_alg]
    have hleL : I.map (algebraMap ↑A' (Localization.Away (aa p))) ≤
        (I.map (algebraMap ↑A' (OverlapRing (aa p) (aa q)))).comap
          (overlapInL (aa p) (aa q)) := by
      rw [hmapL]
      exact Ideal.le_comap_map
    have hsqL : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap ↑A'
        (OverlapRing (aa p) (aa q)))))) ≫
        Spec.map (CommRingCat.ofHom (overlapInL (aa p) (aa q))) =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (overlapInL (aa p) (aa q))
          hleL)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap ↑A'
          (Localization.Away (aa p)))))) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      refine congrArg Spec.map (CommRingCat.hom_ext ?_)
      exact (Ideal.quotientMap_comp_mk hleL).symm
    have hmapR : I.map (algebraMap ↑A' (OverlapRing (aa p) (aa q))) =
        (I.map (algebraMap ↑A' (Localization.Away (aa q)))).map
          (overlapInR (aa p) (aa q)) := by
      rw [Ideal.map_map, overlapInR_alg]
    have hleR : I.map (algebraMap ↑A' (Localization.Away (aa q))) ≤
        (I.map (algebraMap ↑A' (OverlapRing (aa p) (aa q)))).comap
          (overlapInR (aa p) (aa q)) := by
      rw [hmapR]
      exact Ideal.le_comap_map
    have hsqR : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap ↑A'
        (OverlapRing (aa p) (aa q)))))) ≫
        Spec.map (CommRingCat.ofHom (overlapInR (aa p) (aa q))) =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (overlapInR (aa p) (aa q))
          hleR)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap ↑A'
          (Localization.Away (aa q)))))) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      refine congrArg Spec.map (CommRingCat.hom_ext ?_)
      exact (Ideal.quotientMap_comp_mk hleR).symm
    -- the composed base facts
    have hbaseL : Spec.map (CommRingCat.ofHom (overlapInL (aa p) (aa q))) ≫
        (tB p ≫ chartToBase A (ii p)) = tT ≫ chartToBase A (ii p) := by
      rw [htB p, htT, ← Category.assoc, htriL]
    have hbaseR : Spec.map (CommRingCat.ofHom (overlapInR (aa p) (aa q))) ≫
        (tB q ≫ chartToBase A (ii q)) = tT ≫ chartToBase A (ii p) := by
      rw [htB q, htT, ← Category.assoc, htriR]
    -- apply the value uniqueness at the overlap
    refine kernel_val_unique_of_chartFactor E A (ii p) Ideal.Quotient.mk_surjective hφT2
      tT N hNT _ _ ?_ ?_ ?_ ?_ ?_
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (Spec.map (CommRingCat.ofHom (overlapInL (aa p) (aa q))) ≫ ·)
        (hvπ p)).trans ?_
      exact hbaseL
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (Spec.map (CommRingCat.ofHom (overlapInR (aa p) (aa q))) ≫ ·)
        (hvπ q)).trans ?_
      exact hbaseR
    · refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ (δp p).1) hsqL).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (Spec.map (CommRingCat.ofHom (Ideal.quotientMap _
        (overlapInL (aa p) (aa q)) hleL)) ≫ ·) (hvK p)).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ E.zero) ((Category.assoc _ _ _).symm)).trans ?_
      refine (congrArg (fun m => (m ≫ (tB p ≫ chartToBase A (ii p))) ≫ E.zero)
        hsqL.symm).trans ?_
      refine (congrArg (· ≫ E.zero) (Category.assoc _ _ _)).trans ?_
      refine (congrArg (fun m => (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (I.map (algebraMap ↑A' (OverlapRing (aa p) (aa q)))))) ≫ m) ≫ E.zero)
        hbaseL).trans ?_
      rfl
    · refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ (δp q).1) hsqR).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (Spec.map (CommRingCat.ofHom (Ideal.quotientMap _
        (overlapInR (aa p) (aa q)) hleR)) ≫ ·) (hvK q)).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ E.zero) ((Category.assoc _ _ _).symm)).trans ?_
      refine (congrArg (fun m => (m ≫ (tB q ≫ chartToBase A (ii q))) ≫ E.zero)
        hsqR.symm).trans ?_
      refine (congrArg (· ≫ E.zero) (Category.assoc _ _ _)).trans ?_
      refine (congrArg (fun m => (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (I.map (algebraMap ↑A' (OverlapRing (aa p) (aa q)))))) ≫ m) ≫ E.zero)
        hbaseR).trans ?_
      rfl
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (Spec.map (CommRingCat.ofHom (overlapInL (aa p) (aa q))) ≫ ·)
        (hvN p)).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ ε.1) htriL).trans ?_
      refine (congrArg (· ≫ ε.1) htriR.symm).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (Spec.map (CommRingCat.ofHom (overlapInR (aa p) (aa q))) ≫ ·)
        (hvN q).symm).trans ?_
      exact (Category.assoc _ _ _).symm
  -- the open cover by the pieces and the glued value
  set 𝒰 : (Spec A').OpenCover :=
    Scheme.Cover.mkOfCovers (↑(Spec A'))
      (fun p => Spec (CommRingCat.of (Localization.Away (aa p))))
      (fun p => Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p)))))
      (fun x => by
        have h2 := PrimeSpectrum.localization_away_comap_range
          (Localization.Away (aa x)) (aa x)
        have h3 : x ∈ Set.range (PrimeSpectrum.comap
            (algebraMap ↑A' (Localization.Away (aa x)))) := by
          rw [h2]; exact hmemA x
        obtain ⟨y, hy⟩ := h3
        exact ⟨x, y, hy⟩) with h𝒰
  set w : Spec A' ⟶ E.E := 𝒰.glueMorphisms (fun p => (δp p).1) hcompat with hw
  have hι : ∀ p : ↑(Spec A'),
      Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p)))) ≫ w =
      (δp p).1 := fun p => Scheme.Cover.ι_glueMorphisms 𝒰 (fun p => (δp p).1) hcompat p
  have hover : w ≫ E.π = b' := by
    refine Scheme.Cover.hom_ext 𝒰 _ _ (fun p => ?_)
    show Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p)))) ≫
      (w ≫ E.π) = _ ≫ b'
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ E.π) (hι p)).trans ?_
    exact (hvπ p).trans (htB p)
  refine ⟨⟨w, hover⟩, ?_, ?_⟩
  · -- the kernel membership of the glued point
    refine Subtype.ext ?_
    show Spec.map φ ≫ w = _
    rw [E.point_zero_val]
    refine Scheme.Cover.hom_ext (𝒰.pullback₁ (Spec.map φ)) _ _ (fun p => ?_)
    show pullback.fst (Spec.map φ) (𝒰.f p) ≫ (Spec.map φ ≫ w) =
      pullback.fst (Spec.map φ) (𝒰.f p) ≫ ((Spec.map φ ≫ b') ≫ E.zero)
    -- both sides through the pullback condition
    have hcond : pullback.fst (Spec.map φ) (𝒰.f p) ≫ Spec.map φ =
        pullback.snd (Spec.map φ) (𝒰.f p) ≫ 𝒰.f p := pullback.condition
    -- LHS
    have hLHS : pullback.fst (Spec.map φ) (𝒰.f p) ≫ (Spec.map φ ≫ w) =
        pullback.snd (Spec.map φ) (𝒰.f p) ≫ (δp p).1 := by
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ w) hcond).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      exact congrArg (pullback.snd (Spec.map φ) (𝒰.f p) ≫ ·) (hι p)
    rw [hLHS]
    -- RHS
    have hRHS : pullback.fst (Spec.map φ) (𝒰.f p) ≫
        ((Spec.map φ ≫ b') ≫ E.zero) =
        (pullback.snd (Spec.map φ) (𝒰.f p) ≫ (tB p ≫ chartToBase A (ii p))) ≫ E.zero := by
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (· ≫ E.zero) ((Category.assoc _ _ _).symm)).trans ?_
      refine (congrArg (fun m => (m ≫ b') ≫ E.zero) hcond).trans ?_
      refine (congrArg (· ≫ E.zero) (Category.assoc _ _ _)).trans ?_
      refine congrArg (· ≫ E.zero) ?_
      refine congrArg (pullback.snd (Spec.map φ) (𝒰.f p) ≫ ·) (htB p).symm
    rw [hRHS]
    -- factor the reduced piece through the quotient of the localization
    show pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap ↑A' (↑A' ⧸ I))))
        (Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p))))) ≫
        (δp p).1 =
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap ↑A' (↑A' ⧸ I))))
        (Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p))))) ≫
        (tB p ≫ chartToBase A (ii p))) ≫ E.zero
    rw [← cancel_epi (pullbackSpecIso ↑A' (↑A' ⧸ I) (Localization.Away (aa p))).inv]
    have hks := pullbackSpecIso_inv_snd ↑A' (↑A' ⧸ I) (Localization.Away (aa p))
    have hkill : ∀ a ∈ I.map (algebraMap ↑A' (Localization.Away (aa p))),
        (Algebra.TensorProduct.includeRight (R := ↑A') (A := ↑A' ⧸ I)
          (B := Localization.Away (aa p))).toRingHom a = 0 := by
      have hle : I.map (algebraMap ↑A' (Localization.Away (aa p))) ≤
          RingHom.ker (Algebra.TensorProduct.includeRight (R := ↑A') (A := ↑A' ⧸ I)
            (B := Localization.Away (aa p))).toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro i hi
        show (1 : ↑A' ⧸ I) ⊗ₜ[↑A'] (algebraMap ↑A' (Localization.Away (aa p)) i) = 0
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.smul_def, _root_.mul_one,
          Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hi,
          TensorProduct.zero_tmul]
      exact fun a ha => hle ha
    set ψ' : (Localization.Away (aa p)) ⧸ (I.map (algebraMap ↑A'
        (Localization.Away (aa p)))) →+* ((↑A' ⧸ I) ⊗[↑A'] Localization.Away (aa p)) :=
      Ideal.Quotient.lift _ _ hkill with hψ'
    have hfact : Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight
        (R := ↑A') (A := ↑A' ⧸ I) (B := Localization.Away (aa p))).toRingHom)) =
        Spec.map (CommRingCat.ofHom ψ') ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I.map (algebraMap ↑A' (Localization.Away (aa p)))))) := by
      rw [← Spec.map_comp]
      refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
      show _ = ψ' (Ideal.Quotient.mk _ a)
      exact (Ideal.Quotient.lift_mk _ _ _).symm
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ (δp p).1) hks).trans ?_
    refine (congrArg (· ≫ (δp p).1) hfact).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (Spec.map (CommRingCat.ofHom ψ') ≫ ·) (hvK p)).trans ?_
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ E.zero) ((Category.assoc _ _ _).symm)).trans ?_
    refine (congrArg (fun m => (m ≫ (tB p ≫ chartToBase A (ii p))) ≫ E.zero)
      hfact.symm).trans ?_
    refine (congrArg (fun m => (m ≫ (tB p ≫ chartToBase A (ii p))) ≫ E.zero)
      hks.symm).trans ?_
    refine (congrArg (· ≫ E.zero) (Category.assoc _ _ _)).trans ?_
    exact Category.assoc _ _ _
  · -- the scalar identity of the glued point
    refine Subtype.ext ?_
    show ((N : ℤ) • (⟨w, hover⟩ : E.Point b') : E.Point b').1 = ε.1
    rw [E.point_smul_eq_comp_mulBy]
    refine Scheme.Cover.hom_ext 𝒰 _ _ (fun p => ?_)
    show Spec.map (CommRingCat.ofHom (algebraMap ↑A' (Localization.Away (aa p)))) ≫
      (w ≫ E.mulByHom (N : ℤ)) = _ ≫ ε.1
    refine ((Category.assoc _ _ _).symm).trans ?_
    refine (congrArg (· ≫ E.mulByHom (N : ℤ)) (hι p)).trans ?_
    exact hvN p

end Glue





end EllipticCurve

end ModularCurves
