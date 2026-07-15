/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.Curves.Fiber.LocalizedDictionary
import HasseWeil.Foundation.EC.KernelCount
import HasseWeil.Foundation.EC.SeparableKernelTorsor
import HasseWeil.Isogeny.Dual.GaloisUnconditional
import HasseWeil.Isogeny.SeparableWitnessReductions
import Mathlib.FieldTheory.Fixed

/-!
# Kernels of general separable isogenies

This file proves that the cardinality of the kernel of a separable isogeny equals its degree from
a cofinite pullback-evaluation witness. It also derives normality, translation descent, and dual
isogeny data from the same witness.

## Main results

* `card_kernel_eq_degree_of_separable`: the kernel cardinality equals the degree.
* `finite_kernel_of_separable`: the kernel is finite.
* `normal_of_separable_general`: the induced function-field extension is normal.
* `hdesc_of_separable_general`: function-field automorphisms arise from kernel translations.
* `exists_dual_of_pullbackEvaluation_general`: a reverse isogeny exists.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6(b), III.4.10(c).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

private theorem kernel_card_le_degree_of_hcov
    (β : Isogeny W.toAffine W.toAffine)
    (hcov : ∀ k : β.kernel, ∀ z : KE,
      translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z) :
    Nat.card β.kernel ≤ β.degree := by
  let βAlg : Algebra KE KE := β.toAlgebra
  have hfd : @FiniteDimensional KE KE _ _ β.toAlgebra.toModule :=
    isogeny_finiteDimensional W β
  have hAutFin : Finite (@AlgEquiv KE KE KE _ _ _ β.toAlgebra β.toAlgebra) :=
    Finite.of_fintype _
  calc
    Nat.card β.kernel ≤ Nat.card (@AlgEquiv KE KE KE _ _ _ β.toAlgebra β.toAlgebra) :=
      Nat.card_le_card_of_injective _ (kernelTranslateForwardAut_injective W β hcov)
    _ ≤ β.degree := by
      have h := @AlgEquiv.card_le KE KE _ _ β.toAlgebra hfd
      rwa [← Nat.card_eq_fintype_card] at h

private theorem badTarget_finite (β : Isogeny W.toAffine W.toAffine)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite) :
    {Q' : (W_smooth W).SmoothPoint | ∃ p ∈ bad,
      WeilPairing.EvaluatesTo W p (β.pullback (x_gen W)) Q'.x ∧
      WeilPairing.EvaluatesTo W p (β.pullback (y_gen W)) Q'.y}.Finite := by
  have hsub : {Q' : (W_smooth W).SmoothPoint | ∃ p ∈ bad,
      WeilPairing.EvaluatesTo W p (β.pullback (x_gen W)) Q'.x ∧
      WeilPairing.EvaluatesTo W p (β.pullback (y_gen W)) Q'.y} ⊆
      ⋃ p ∈ bad, {Q' : (W_smooth W).SmoothPoint |
        WeilPairing.EvaluatesTo W p (β.pullback (x_gen W)) Q'.x ∧
        WeilPairing.EvaluatesTo W p (β.pullback (y_gen W)) Q'.y} := by
    rintro Q' ⟨p, hp, h1, h2⟩
    exact Set.mem_biUnion hp ⟨h1, h2⟩
  refine Set.Finite.subset (Set.Finite.biUnion hbad fun p _ => ?_) hsub
  refine Set.Subsingleton.finite ?_
  rintro Q₁ ⟨hx₁, hy₁⟩ Q₂ ⟨hx₂, hy₂⟩
  exact Curves.SmoothPlaneCurve.SmoothPoint.ext (hx₁.unique hx₂) (hy₁.unique hy₂)

private theorem mapAddMonoidHom_toAffinePoint_of_evaluatesTo
    (β : Isogeny W.toAffine W.toAffine)
    {bad : Set (W_smooth W).SmoothPoint}
    (hw : WeilPairing.PullbackEvaluation W β bad)
    (Q pt : (W_smooth W).SmoothPoint) (hpt : pt ∉ bad)
    (hex : WeilPairing.EvaluatesTo W pt (β.pullback (x_gen W)) Q.x)
    (hey : WeilPairing.EvaluatesTo W pt (β.pullback (y_gen W)) Q.y) :
    β.toAddMonoidHom pt.toAffinePoint = Q.toAffinePoint := by
  obtain ⟨x', y', h', heq, hx, hy⟩ := hw pt hpt
  rw [heq, Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def]
  exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr
    ⟨hx.unique hex, hy.unique hey⟩

private theorem hcov_of_pullbackEvaluation_aux [IsAlgClosed F]
    (β : Isogeny W.toAffine W.toAffine)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    ∀ k : β.kernel, ∀ z : KE,
      translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z :=
  fun k z => WeilPairing.hcov_of_mapTranslateGenericPoint_canonical W β
    (WeilPairing.mapTranslateGenericPoint_of_pullbackEvaluation W β hbad hw) k z

private theorem degree_le_card_kernel_of_good_fiber_aux
    (β : Isogeny W.toAffine W.toAffine) (hker_fin : Finite β.kernel)
    (Q : (W_smooth W).SmoothPoint) (S : Finset (W_smooth W).SmoothPoint)
    (hScard : S.card = β.degree)
    (hfibmem : ∀ pt ∈ S, β.toAddMonoidHom pt.toAffinePoint = Q.toAffinePoint) :
    β.degree ≤ Nat.card β.kernel := by
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos, hScard]
    exact isogeny_degree_pos W β
  obtain ⟨pt₀, hpt₀⟩ := hSne
  haveI hfib_fin : Finite {R : W.toAffine.Point //
      β.toAddMonoidHom R = Q.toAffinePoint} :=
    Isogeny.fiber_finite_of_kernel_finite β hker_fin
  have hinj : Function.Injective (fun p : {x // x ∈ S} =>
      (⟨p.1.toAffinePoint, hfibmem p.1 p.2⟩ :
        {R : W.toAffine.Point // β.toAddMonoidHom R = Q.toAffinePoint})) := by
    intro p₁ p₂ h
    exact Subtype.ext (smoothPoint_toAffinePoint_injective W (congrArg Subtype.val h))
  calc
    β.degree = S.card := hScard.symm
    _ = Nat.card {x // x ∈ S} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Nat.card {R : W.toAffine.Point // β.toAddMonoidHom R = Q.toAffinePoint} :=
      Nat.card_le_card_of_injective _ hinj
    _ = Nat.card β.kernel :=
      Isogeny.fiber_card_eq_kernel_card β (hfibmem pt₀ hpt₀)

private theorem degree_le_card_kernel_of_separable_aux [IsAlgClosed F]
    [IsIntegrallyClosed W.toAffine.CoordinateRing]
    (β : Isogeny W.toAffine W.toAffine) (hsep : β.IsSeparable)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad)
    (hker_fin : Finite β.kernel) : β.degree ≤ Nat.card β.kernel := by
  classical
  have hEll : (W_smooth W).toAffine.IsElliptic := ‹W.toAffine.IsElliptic›
  have hIC : IsIntegrallyClosed (W_smooth W).CoordinateRing :=
    ‹IsIntegrallyClosed W.toAffine.CoordinateRing›
  let βAlg : Algebra KE KE := β.toAlgebra
  have hfd : @FiniteDimensional KE KE _ _ β.toAlgebra.toModule :=
    isogeny_finiteDimensional W β
  have hsepAlg : @Algebra.IsSeparable (W_smooth W).FunctionField
      (W_smooth W).FunctionField _ _ β.toAlgebra := hsep
  have twFKL : @IsScalarTower F KE KE _ β.toAlgebra.toSMul _ :=
    @IsScalarTower.of_algebraMap_eq F KE KE _ _ _ _ β.toAlgebra _
      fun c => (β.pullback.commutes c).symm
  obtain ⟨f₀, hf₀, hdx, hdy⟩ := @Curves.LocalizedDictionary.exists_denominator F _
    (W_smooth W) (W_smooth W) β.toAlgebra
  set Af := Localization.Away f₀
  let algAfK : Algebra Af (W_smooth W).FunctionField :=
    Curves.GoodAffineLocus.awayAlgebra (W_smooth W) f₀ hf₀
  have twAfK : letI := algAfK
      IsScalarTower (W_smooth W).CoordinateRing Af (W_smooth W).FunctionField :=
    Curves.GoodAffineLocus.awayAlgebra_isScalarTower (W_smooth W) f₀ hf₀
  let algAfL : Algebra Af KE :=
    ((β.pullback.toRingHom).comp (algebraMap Af (W_smooth W).FunctionField)).toAlgebra
  have twAfKL : @IsScalarTower Af KE KE algAfK.toSMul β.toAlgebra.toSMul algAfL.toSMul :=
    @IsScalarTower.of_algebraMap_eq Af KE KE _ _ _ algAfK β.toAlgebra algAfL fun _ => rfl
  obtain ⟨Q, hQbadT, S, hScard, hSpts⟩ :=
    @Curves.LocalizedDictionary.exists_good_fiber_points F _ (W_smooth W) f₀ Af _ _ _
      (W_smooth W) β.toAlgebra hfd algAfK twAfK algAfL twAfKL twFKL hEll hEll hsepAlg
      _ hIC hf₀ hdx hdy _ (badTarget_finite W β hbad)
  refine degree_le_card_kernel_of_good_fiber_aux W β hker_fin Q S hScard ?_
  intro pt hpt
  exact mapAddMonoidHom_toAffinePoint_of_evaluatesTo W β hw Q pt
    (fun hmem => hQbadT ⟨pt, hmem, (hSpts pt hpt).1, (hSpts pt hpt).2⟩)
    (hSpts pt hpt).1 (hSpts pt hpt).2

/-- The cardinality of the kernel of a separable isogeny equals its degree. -/
theorem card_kernel_eq_degree_of_separable [IsAlgClosed F]
    [IsIntegrallyClosed W.toAffine.CoordinateRing]
    (β : Isogeny W.toAffine W.toAffine) (hsep : β.IsSeparable)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    Nat.card β.kernel = β.degree := by
  have hcov : ∀ k : β.kernel, ∀ z : KE,
      translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z :=
    hcov_of_pullbackEvaluation_aux W β hbad hw
  have hker_fin : Finite β.kernel := finite_kernel_of_hcov W β hcov
  exact le_antisymm (kernel_card_le_degree_of_hcov W β hcov)
    (degree_le_card_kernel_of_separable_aux W β hsep hbad hw hker_fin)

/-- The kernel is finite when the pullback evaluation is coherent away from a finite set. -/
theorem finite_kernel_of_separable [IsAlgClosed F]
    (β : Isogeny W.toAffine W.toAffine)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    Finite β.kernel :=
  finite_kernel_of_hcov W β (hcov_of_pullbackEvaluation_aux W β hbad hw)

section Cascade

variable [IsAlgClosed F] [IsIntegrallyClosed W.toAffine.CoordinateRing]

omit [IsIntegrallyClosed W.toAffine.CoordinateRing] in
/-- Kernel translations fix the pullbacks of the coordinate generators. -/
theorem xy_family_of_pullbackEvaluation (β : Isogeny W.toAffine W.toAffine)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)) :=
  WeilPairing.xy_family_of_pullbackEvaluation W β hbad hw

/-- The function-field extension induced by a separable isogeny is normal. -/
theorem normal_of_separable_general (β : Isogeny W.toAffine W.toAffine)
    (hsep : β.IsSeparable)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    letI := β.toAlgebra
    Normal W.toAffine.FunctionField W.toAffine.FunctionField :=
  normal_of_xy_family_card W β (xy_family_of_pullbackEvaluation W β hbad hw)
    (card_kernel_eq_degree_of_separable W β hsep hbad hw)

/-- Every automorphism of the induced function-field extension is a kernel translation. -/
theorem hdesc_of_separable_general (β : Isogeny W.toAffine W.toAffine)
    (hsep : β.IsSeparable)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ β.kernel ∧
        liftPointToKE W k = genericPointAct W β σ - genericPoint W :=
  hdesc_of_xy_family_card W β (xy_family_of_pullbackEvaluation W β hbad hw)
    (card_kernel_eq_degree_of_separable W β hsep hbad hw)

/-- Galois data for a separable isogeny with coherent pullback evaluation. -/
noncomputable def dualGaloisData_of_pullbackEvaluation_general
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (hsep : β.IsSeparable)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    EC.Isogeny.DualGaloisData φ :=
  dualGaloisData_of_pullbackEvaluation W φ β h_pb hsep
    (isogeny_degree_pos W β).ne' hbad hw
    (normal_of_separable_general W β hsep hbad hw)
    (hdesc_of_separable_general W β hsep hbad hw)
    (hν_mulByInt W (β.degree : ℤ)
      (by exact_mod_cast (isogeny_degree_pos W β).ne'))

/-- A separable isogeny with coherent pullback evaluation admits a reverse isogeny. -/
theorem exists_dual_of_pullbackEvaluation_general
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (hsep : β.IsSeparable)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    Nonempty (EC.Isogeny W.toAffine W.toAffine) :=
  φ.exists_dual_of_witness
    (φ.hasDualWitness_of_galoisData
      (dualGaloisData_of_pullbackEvaluation_general W φ β h_pb hsep hbad hw))

end Cascade

end HasseWeil
