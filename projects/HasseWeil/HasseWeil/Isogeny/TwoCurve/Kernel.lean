/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Isogeny.TwoCurve.Covariance
import HasseWeil.Isogeny.TwoCurve.FixedField
import HasseWeil.Isogeny.TwoCurve.NormConorm
import HasseWeil.Foundation.EC.KernelCount
import HasseWeil.Foundation.Curves.Fiber.LocalizedDictionary
import Mathlib.FieldTheory.Fixed

/-!
# Kernels of separable two-curve isogenies

This file proves that the cardinality of the kernel of a separable two-curve isogeny equals its
degree. It also establishes finiteness of the fibres of the stored point map.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6(b), III.4.10(a,c).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- Pullback evaluation implies invariance under translation by a point in the kernel. -/
theorem hcov_of_pullbackEvaluation_twoCurve [IsAlgClosed F]
    (β : Isogeny W₁ W₂) {bad : Set (W_smooth W₁).SmoothPoint}
    (hbad : bad.Finite) (hw : WeilPairing.PullbackEvaluation_twoCurve W₁ W₂ β bad) :
    ∀ k : β.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (β.pullback z) = β.pullback z :=
  fun k z =>
    Isogeny.translate_pullback_invariance_of_xy_twoCurve β k.val
      (WeilPairing.xy_family_of_pullbackEvaluation_twoCurve W₁ W₂ β hbad hw k).1
      (WeilPairing.xy_family_of_pullbackEvaluation_twoCurve W₁ W₂ β hbad hw k).2 z

/-- The action of the kernel by translation on the function-field extension. -/
noncomputable def kernelTranslateForwardAut_twoCurve
    (β : Isogeny W₁ W₂)
    (hcov : ∀ k : β.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (β.pullback z) = β.pullback z) :
    β.kernel → (@AlgEquiv W₂.FunctionField W₁.FunctionField W₁.FunctionField _ _ _
      β.toAlgebra β.toAlgebra) :=
  fun k =>
    letI := β.toAlgebra
    AlgEquiv.ofRingEquiv (f := (translateAlgEquivOfPoint W₁ k.val).toRingEquiv)
      (hcov k)

/-- The action of the kernel by translation on the function-field extension is faithful. -/
theorem kernelTranslateForwardAut_twoCurve_injective
    (β : Isogeny W₁ W₂)
    (hcov : ∀ k : β.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (β.pullback z) = β.pullback z) :
    Function.Injective (kernelTranslateForwardAut_twoCurve β hcov) := by
  intro k₁ k₂ h
  apply Subtype.ext
  apply translateAlgEquivOfPoint_injective W₁
  exact AlgEquiv.ext fun z => DFunLike.congr_fun h z

private theorem card_kernel_le_degree_of_hcov_twoCurve (β : Isogeny W₁ W₂)
    (hcov : ∀ k : β.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (β.pullback z) = β.pullback z) :
    Nat.card β.kernel ≤ β.degree := by
  letI βAlg : Algebra W₂.FunctionField W₁.FunctionField := β.toAlgebra
  haveI hfd : @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _ β.toAlgebra.toModule :=
    Isogeny.finiteDimensional_toAlgebra_twoCurve β
  haveI hAutFin : Finite (@AlgEquiv W₂.FunctionField W₁.FunctionField W₁.FunctionField _ _ _
      β.toAlgebra β.toAlgebra) := Finite.of_fintype _
  calc
    Nat.card β.kernel ≤
        Nat.card (@AlgEquiv W₂.FunctionField W₁.FunctionField W₁.FunctionField _ _ _
          β.toAlgebra β.toAlgebra) :=
      Nat.card_le_card_of_injective _
        (kernelTranslateForwardAut_twoCurve_injective β hcov)
    _ ≤ β.degree := by
      have h := @AlgEquiv.card_le W₂.FunctionField W₁.FunctionField _ _ β.toAlgebra hfd
      rwa [← Nat.card_eq_fintype_card] at h

private theorem finite_point_kernel_twoCurve {β : Isogeny W₁ W₂}
    {bad : Set (W_smooth W₁).SmoothPoint}
    (hw : WeilPairing.PullbackEvaluation_twoCurve W₁ W₂ β bad) (hbad : bad.Finite) :
    {R : W₁.Point | β.toAddMonoidHom R = 0}.Finite := by
  refine (Set.Finite.insert (0 : W₁.Point)
    (hbad.image fun P : (W_smooth W₁).SmoothPoint => P.toAffinePoint)).subset ?_
  rintro (_ | ⟨x, y, hns⟩) hR
  · exact Set.mem_insert_iff.mpr (Or.inl WeierstrassCurve.Affine.Point.zero_def.symm)
  · refine Set.mem_insert_iff.mpr (Or.inr ⟨⟨x, y, hns⟩, ?_, rfl⟩)
    by_contra hnotbad
    obtain ⟨x', y', h', heq, -, -⟩ := hw ⟨x, y, hns⟩ hnotbad
    rw [Set.mem_setOf_eq] at hR
    have hcontra := WeierstrassCurve.Affine.Point.zero_def.symm.trans (hR.symm.trans heq)
    simp only [reduceCtorEq] at hcontra

/-- Every fibre of the stored point map is finite. -/
theorem finite_fiber_twoCurve {β : Isogeny W₁ W₂}
    {bad : Set (W_smooth W₁).SmoothPoint}
    (hw : WeilPairing.PullbackEvaluation_twoCurve W₁ W₂ β bad)
    (hbad : bad.Finite) (Q : W₂.Point) :
    {P : (W_smooth W₁).SmoothPoint | β.toAddMonoidHom P.toAffinePoint = Q}.Finite := by
  haveI : Finite β.kernel :=
    Set.finite_coe_iff.mpr (finite_point_kernel_twoCurve hw hbad)
  have hfiber : {R : W₁.Point | β.toAddMonoidHom R = Q}.Finite :=
    Set.finite_coe_iff.mp (Isogeny.fiber_finite_of_kernel_finite β inferInstance)
  exact Set.Finite.preimage (smoothPoint_toAffinePoint_injective W₁).injOn hfiber

private theorem badTarget_finite_twoCurve (β : Isogeny W₁ W₂)
    {bad : Set (W_smooth W₁).SmoothPoint} (hbad : bad.Finite) :
    {Q' : (W_smooth W₂).SmoothPoint | ∃ p ∈ bad,
      WeilPairing.EvaluatesTo W₁ p (β.pullback (x_gen W₂)) Q'.x ∧
      WeilPairing.EvaluatesTo W₁ p (β.pullback (y_gen W₂)) Q'.y}.Finite := by
  have hsub : {Q' : (W_smooth W₂).SmoothPoint | ∃ p ∈ bad,
      WeilPairing.EvaluatesTo W₁ p (β.pullback (x_gen W₂)) Q'.x ∧
      WeilPairing.EvaluatesTo W₁ p (β.pullback (y_gen W₂)) Q'.y} ⊆
      ⋃ p ∈ bad, {Q' : (W_smooth W₂).SmoothPoint |
        WeilPairing.EvaluatesTo W₁ p (β.pullback (x_gen W₂)) Q'.x ∧
        WeilPairing.EvaluatesTo W₁ p (β.pullback (y_gen W₂)) Q'.y} := by
    rintro Q' ⟨p, hp, h1, h2⟩
    exact Set.mem_biUnion hp ⟨h1, h2⟩
  refine Set.Finite.subset (Set.Finite.biUnion hbad fun p _ => ?_) hsub
  refine Set.Subsingleton.finite ?_
  rintro Q₁ ⟨hx₁, hy₁⟩ Q₂ ⟨hx₂, hy₂⟩
  exact Curves.SmoothPlaneCurve.SmoothPoint.ext (hx₁.unique hx₂) (hy₁.unique hy₂)

private theorem mapAddMonoidHom_toAffinePoint_of_evaluatesTo_twoCurve (β : Isogeny W₁ W₂)
    {bad : Set (W_smooth W₁).SmoothPoint}
    (hw : WeilPairing.PullbackEvaluation_twoCurve W₁ W₂ β bad)
    (Q : (W_smooth W₂).SmoothPoint) (pt : (W_smooth W₁).SmoothPoint) (hpt : pt ∉ bad)
    (hex : WeilPairing.EvaluatesTo W₁ pt (β.pullback (x_gen W₂)) Q.x)
    (hey : WeilPairing.EvaluatesTo W₁ pt (β.pullback (y_gen W₂)) Q.y) :
    β.toAddMonoidHom pt.toAffinePoint = Q.toAffinePoint := by
  obtain ⟨x', y', h', heq, hx, hy⟩ := hw pt hpt
  rw [heq, Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def]
  exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr
    ⟨hx.unique hex, hy.unique hey⟩

private theorem degree_le_card_kernel_of_good_fiber_twoCurve (β : Isogeny W₁ W₂)
    (hker_fin : Finite β.kernel) (Q : (W_smooth W₂).SmoothPoint)
    (S : Finset (W_smooth W₁).SmoothPoint) (hScard : S.card = β.degree)
    (hfibmem : ∀ pt ∈ S, β.toAddMonoidHom pt.toAffinePoint = Q.toAffinePoint) :
    β.degree ≤ Nat.card β.kernel := by
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos, hScard]
    exact Isogeny.degree_pos_twoCurve β
  obtain ⟨pt₀, hpt₀⟩ := hSne
  haveI hfib_fin : Finite {R : W₁.Point // β.toAddMonoidHom R = Q.toAffinePoint} :=
    Isogeny.fiber_finite_of_kernel_finite β hker_fin
  have hinj : Function.Injective (fun p : {x // x ∈ S} =>
      (⟨p.1.toAffinePoint, hfibmem p.1 p.2⟩ :
        {R : W₁.Point // β.toAddMonoidHom R = Q.toAffinePoint})) := by
    intro p₁ p₂ h
    exact Subtype.ext (smoothPoint_toAffinePoint_injective W₁ (congrArg Subtype.val h))
  calc
    β.degree = S.card := hScard.symm
    _ = Nat.card {x // x ∈ S} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Nat.card {R : W₁.Point // β.toAddMonoidHom R = Q.toAffinePoint} :=
      Nat.card_le_card_of_injective _ hinj
    _ = Nat.card β.kernel :=
      Isogeny.fiber_card_eq_kernel_card β (hfibmem pt₀ hpt₀)

private theorem degree_le_card_kernel_of_separable_twoCurve [IsAlgClosed F]
    [IsIntegrallyClosed W₂.toAffine.CoordinateRing]
    (β : Isogeny W₁ W₂) (hsep : β.IsSeparable)
    {bad : Set (W_smooth W₁).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation_twoCurve W₁ W₂ β bad)
    (hker_fin : Finite β.kernel) : β.degree ≤ Nat.card β.kernel := by
  classical
  haveI hIC : IsIntegrallyClosed (W_smooth W₂).CoordinateRing :=
    ‹IsIntegrallyClosed W₂.toAffine.CoordinateRing›
  haveI hfd : @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _ β.toAlgebra.toModule :=
    Isogeny.finiteDimensional_toAlgebra_twoCurve β
  haveI hsepAlg : @Algebra.IsSeparable (W_smooth W₂).FunctionField
      (W_smooth W₁).FunctionField _ _ β.toAlgebra := hsep
  haveI twFKL : @IsScalarTower F W₂.FunctionField W₁.FunctionField _ β.toAlgebra.toSMul _ :=
    @IsScalarTower.of_algebraMap_eq F W₂.FunctionField W₁.FunctionField _ _ _ _ β.toAlgebra _
      fun c => (β.pullback.commutes c).symm
  obtain ⟨f₀, hf₀, hdx, hdy⟩ := @Curves.LocalizedDictionary.exists_denominator F _
    (W_smooth W₂) (W_smooth W₁) β.toAlgebra
  set Af := Localization.Away f₀
  letI algAfK : Algebra Af (W_smooth W₂).FunctionField :=
    Curves.GoodAffineLocus.awayAlgebra (W_smooth W₂) f₀ hf₀
  haveI twAfK : letI := algAfK
      IsScalarTower (W_smooth W₂).CoordinateRing Af (W_smooth W₂).FunctionField :=
    Curves.GoodAffineLocus.awayAlgebra_isScalarTower (W_smooth W₂) f₀ hf₀
  letI algAfL : Algebra Af W₁.FunctionField :=
    ((β.pullback.toRingHom).comp (algebraMap Af (W_smooth W₂).FunctionField)).toAlgebra
  haveI twAfKL : @IsScalarTower Af W₂.FunctionField W₁.FunctionField algAfK.toSMul
      β.toAlgebra.toSMul algAfL.toSMul :=
    @IsScalarTower.of_algebraMap_eq Af W₂.FunctionField W₁.FunctionField _ _ _ algAfK
      β.toAlgebra algAfL fun _ => rfl
  obtain ⟨Q, hQbadT, S, hScard, hSpts⟩ :=
    @Curves.LocalizedDictionary.exists_good_fiber_points F _ (W_smooth W₂) f₀ Af _ _ _
      (W_smooth W₁) β.toAlgebra hfd algAfK twAfK algAfL twAfKL twFKL ‹_› ‹_› hsepAlg
      _ hIC hf₀ hdx hdy _ (badTarget_finite_twoCurve β hbad)
  refine degree_le_card_kernel_of_good_fiber_twoCurve β hker_fin Q S hScard ?_
  intro pt hpt
  exact mapAddMonoidHom_toAffinePoint_of_evaluatesTo_twoCurve β hw Q pt
    (fun hmem => hQbadT ⟨pt, hmem, (hSpts pt hpt).1, (hSpts pt hpt).2⟩)
    (hSpts pt hpt).1 (hSpts pt hpt).2

/-- The cardinality of the kernel of a separable two-curve isogeny equals its degree. -/
theorem card_kernel_eq_degree_twoCurve [IsAlgClosed F]
    [IsIntegrallyClosed W₂.toAffine.CoordinateRing]
    (β : Isogeny W₁ W₂) (hsep : β.IsSeparable)
    {bad : Set (W_smooth W₁).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation_twoCurve W₁ W₂ β bad) :
    Nat.card β.kernel = β.degree := by
  have hcov : ∀ k : β.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (β.pullback z) = β.pullback z :=
    hcov_of_pullbackEvaluation_twoCurve β hbad hw
  have hker_fin : Finite β.kernel := Isogeny.finite_kernel_of_hcov_twoCurve β hcov
  exact le_antisymm (card_kernel_le_degree_of_hcov_twoCurve β hcov)
    (degree_le_card_kernel_of_separable_twoCurve β hsep hbad hw hker_fin)

end HasseWeil
