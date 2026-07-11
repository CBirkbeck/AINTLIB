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

end EllipticCurve

end ModularCurves
