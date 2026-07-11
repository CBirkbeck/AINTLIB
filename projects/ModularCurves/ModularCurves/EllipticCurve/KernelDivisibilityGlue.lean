/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.KernelDivisibilityChart

/-!
# Kernel divisibility: from the chart to arbitrary records (BB-FLAT N5)

The glue phase of board v10.150: `KernelNDivisible` for arbitrary records and tests, from
the chart-local calculus (`KernelDivisibilityChart.lean`). This file instantiates the
chart theorems at the projective model's Y-chart, transports them along the
`Point.baseChangeEquiv`/`pointAddEquiv` chain (the BB-QF pattern, hμ from K3), and glues
over a basic-open cover of the test.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj WeierstrassCurve

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

theorem modelYChart_isAffineOpen : IsAffineOpen (modelYChart W) :=
  Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 1) one_pos

theorem modelYChart_zero_mem (x : ↑(Spec (CommRingCat.of B))) :
    ((modelEllipticCurve W).zero).base x ∈ modelYChart W := by
  have h := projModelZero_preimage_yChart W
  have h2 : x ∈ projModelZero W ⁻¹ᵁ (modelYChart W) := by
    rw [show projModelZero W ⁻¹ᵁ (modelYChart W) = ⊤ from h]
    trivial
  exact h2


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

end PieceTransport



end EllipticCurve

end ModularCurves
