module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.Augmentation

/-!
# Unit quotients: augmentation trace comparison

This file restricts the cyclotomic permutation action to the augmentation
hyperplane and compares its trace with the trace on the full logarithmic
permutation representation.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

open Finset

set_option linter.unusedSectionVars false

attribute [local instance] Fintype.ofFinite
attribute [local instance] NumberField.Units.instZLattice_unitLattice

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The full logarithmic augmentation hyperplane is stable under the
cyclotomic permutation action on infinite places. -/
theorem cyclotomicFullLogAugmentationSubmodule_map
    (a : CyclotomicUnitDelta p)
    {f : CyclotomicFullLogSpace K}
    (hf : f ∈ cyclotomicFullLogAugmentationSubmodule K) :
    cyclotomicFullLogSpaceDeltaAction (p := p) K a f ∈
      cyclotomicFullLogAugmentationSubmodule K := by
  rw [cyclotomicFullLogAugmentationSubmodule, LinearMap.mem_ker] at hf ⊢
  rw [cyclotomicFullLogAugmentationMap]
  change ∑ w : InfinitePlace K,
      cyclotomicFullLogSpaceDeltaAction (p := p) K a f w = 0
  rw [cyclotomicFullLogSpaceDeltaAction]
  change ∑ w : InfinitePlace K,
      f ((cyclotomicSigmaOfUnit (p := p) K a)⁻¹ • w) = 0
  rw [show (∑ w : InfinitePlace K,
      f ((cyclotomicSigmaOfUnit (p := p) K a)⁻¹ • w)) =
      ∑ w : InfinitePlace K, f w by
    simpa [MulAction.toPerm] using
      (Equiv.sum_comp
        (MulAction.toPerm ((cyclotomicSigmaOfUnit (p := p) K a)⁻¹)) f)]
  exact hf

/-- The cyclotomic permutation action on the full logarithmic space restricts
to the augmentation hyperplane. -/
noncomputable def cyclotomicFullLogAugmentationLinearEquiv
    (a : CyclotomicUnitDelta p) :
    cyclotomicFullLogAugmentationSubmodule K ≃ₗ[ℝ]
      cyclotomicFullLogAugmentationSubmodule K where
  toFun f := ⟨cyclotomicFullLogSpaceDeltaAction (p := p) K a f.1,
    cyclotomicFullLogAugmentationSubmodule_map (p := p) (K := K) a f.2⟩
  invFun f := ⟨(cyclotomicFullLogSpaceDeltaAction (p := p) K a).symm f.1, by
    have hs :
        (cyclotomicFullLogSpaceDeltaAction (p := p) K a).symm f.1 =
          cyclotomicFullLogSpaceDeltaAction (p := p) K a⁻¹ f.1 := by
      ext w
      simp
    rw [hs]
    exact cyclotomicFullLogAugmentationSubmodule_map (p := p) (K := K) a⁻¹ f.2⟩
  left_inv f := by
    apply Subtype.ext
    ext w
    change f.1 ((cyclotomicSigmaOfUnit (p := p) K a)⁻¹ •
        (cyclotomicSigmaOfUnit (p := p) K a • w)) = f.1 w
    rw [← mul_smul, inv_mul_cancel, one_smul]
  right_inv f := by
    apply Subtype.ext
    ext w
    change f.1 (cyclotomicSigmaOfUnit (p := p) K a •
        ((cyclotomicSigmaOfUnit (p := p) K a)⁻¹ • w)) = f.1 w
    rw [← mul_smul, mul_inv_cancel, one_smul]
  map_add' f g := by
    ext w
    rfl
  map_smul' c f := by
    ext w
    rfl

/-- The cyclotomic action on the full logarithmic augmentation hyperplane as
an `ℝ`-linear representation of `Delta`. -/
noncomputable def cyclotomicFullLogAugmentationDeltaAction :
    CyclotomicUnitDelta p →*
      (cyclotomicFullLogAugmentationSubmodule K ≃ₗ[ℝ]
        cyclotomicFullLogAugmentationSubmodule K) where
  toFun := cyclotomicFullLogAugmentationLinearEquiv (p := p) K
  map_one' := by
    ext f w
    simp [cyclotomicFullLogAugmentationLinearEquiv]
  map_mul' a b := by
    ext f w
    simp [cyclotomicFullLogAugmentationLinearEquiv]

/-- The average value of a vector in the full logarithmic permutation space. -/
noncomputable def cyclotomicFullLogAverage (f : CyclotomicFullLogSpace K) : ℝ :=
  (Fintype.card (InfinitePlace K) : ℝ)⁻¹ * ∑ w : InfinitePlace K, f w

/-- The full logarithmic permutation space splits as augmentation hyperplane
plus constants. -/
noncomputable def cyclotomicFullLogAugmentationProdEquiv :
    (cyclotomicFullLogAugmentationSubmodule K × ℝ) ≃ₗ[ℝ] CyclotomicFullLogSpace K where
  toFun x w := x.1.1 w + x.2
  invFun f :=
    let c := cyclotomicFullLogAverage K f
    (⟨fun w => f w - c, by
        rw [cyclotomicFullLogAugmentationSubmodule, LinearMap.mem_ker]
        change ∑ w : InfinitePlace K, (f w - c) = 0
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        dsimp [c, cyclotomicFullLogAverage]
        have hcard : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
          exact_mod_cast Fintype.card_ne_zero
        field_simp [hcard]
        ring⟩, c)
  left_inv x := by
    have hsum : ∑ w : InfinitePlace K, x.1.1 w = 0 := by
      have hx : x.1.1 ∈ LinearMap.ker (cyclotomicFullLogAugmentationMap K) := x.1.2
      rwa [LinearMap.mem_ker] at hx
    have havg :
        cyclotomicFullLogAverage K (fun w : InfinitePlace K => x.1.1 w + x.2) = x.2 := by
      have hcard : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simp [cyclotomicFullLogAverage, Finset.sum_add_distrib, hsum, Finset.sum_const,
        nsmul_eq_mul]
    ext w
    · change x.1.1 w + x.2 - cyclotomicFullLogAverage K
          (fun w : InfinitePlace K => x.1.1 w + x.2) = x.1.1 w
      rw [havg]
      abel
    · exact havg
  right_inv f := by
    ext w
    simp [cyclotomicFullLogAverage]
  map_add' x y := by
    ext w
    simp [add_assoc, add_left_comm, add_comm]
  map_smul' c x := by
    ext w
    simp [mul_add]

@[simp]
theorem cyclotomicFullLogAugmentationProdEquiv_apply
    (x : cyclotomicFullLogAugmentationSubmodule K × ℝ) (w : InfinitePlace K) :
    cyclotomicFullLogAugmentationProdEquiv K x w = x.1.1 w + x.2 :=
  rfl

theorem cyclotomicFullLogAverage_deltaAction
    (a : CyclotomicUnitDelta p) (f : CyclotomicFullLogSpace K) :
    cyclotomicFullLogAverage K
        (cyclotomicFullLogSpaceDeltaAction (p := p) K a f) =
      cyclotomicFullLogAverage K f := by
  dsimp [cyclotomicFullLogAverage]
  congr 1
  change ∑ w : InfinitePlace K,
      f ((cyclotomicSigmaOfUnit (p := p) K a)⁻¹ • w) =
    ∑ w : InfinitePlace K, f w
  simpa [MulAction.toPerm] using
    (Equiv.sum_comp
      (MulAction.toPerm ((cyclotomicSigmaOfUnit (p := p) K a)⁻¹)) f)

theorem cyclotomicFullLogAugmentationProdEquiv_symm_apply_deltaAction
    (a : CyclotomicUnitDelta p)
    (x : cyclotomicFullLogAugmentationSubmodule K × ℝ) :
    (cyclotomicFullLogAugmentationProdEquiv K).symm
        (cyclotomicFullLogSpaceDeltaAction (p := p) K a
          (cyclotomicFullLogAugmentationProdEquiv K x)) =
      (cyclotomicFullLogAugmentationLinearEquiv (p := p) K a x.1, x.2) := by
  ext w
  · change
      cyclotomicFullLogSpaceDeltaAction (p := p) K a
          (cyclotomicFullLogAugmentationProdEquiv K x) w -
        cyclotomicFullLogAverage K
          (cyclotomicFullLogSpaceDeltaAction (p := p) K a
            (cyclotomicFullLogAugmentationProdEquiv K x)) =
      (cyclotomicFullLogAugmentationLinearEquiv (p := p) K a x.1).1 w
    rw [cyclotomicFullLogAverage_deltaAction]
    have hconst :
        cyclotomicFullLogAverage K (cyclotomicFullLogAugmentationProdEquiv K x) = x.2 := by
      have hx : ∑ w : InfinitePlace K, x.1.1 w = 0 := by
        have hxmem : x.1.1 ∈ LinearMap.ker (cyclotomicFullLogAugmentationMap K) := x.1.2
        rwa [LinearMap.mem_ker] at hxmem
      have hcard : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simp [cyclotomicFullLogAverage, Finset.sum_add_distrib, hx, Finset.sum_const,
        nsmul_eq_mul, hcard]
    rw [hconst]
    rw [cyclotomicFullLogSpaceDeltaAction_apply]
    rw [cyclotomicFullLogAugmentationProdEquiv_apply]
    abel
  · change cyclotomicFullLogAverage K
        (cyclotomicFullLogSpaceDeltaAction (p := p) K a
          (cyclotomicFullLogAugmentationProdEquiv K x)) = x.2
    rw [cyclotomicFullLogAverage_deltaAction]
    have hx : ∑ w : InfinitePlace K, x.1.1 w = 0 := by
      have hxmem : x.1.1 ∈ LinearMap.ker (cyclotomicFullLogAugmentationMap K) := x.1.2
      rwa [LinearMap.mem_ker] at hxmem
    have hcard : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [cyclotomicFullLogAverage, Finset.sum_add_distrib, hx, Finset.sum_const,
      nsmul_eq_mul, hcard]

theorem cyclotomicFullLogSpaceDeltaAction_trace_eq_augmentation_trace_add_one
    (a : CyclotomicUnitDelta p) :
    LinearMap.trace ℝ (CyclotomicFullLogSpace K)
        ((cyclotomicFullLogSpaceDeltaAction (p := p) K a).toLinearMap) =
      LinearMap.trace ℝ (cyclotomicFullLogAugmentationSubmodule K)
        ((cyclotomicFullLogAugmentationLinearEquiv (p := p) K a).toLinearMap) + 1 := by
  let e := cyclotomicFullLogAugmentationProdEquiv K
  have hconj :
      e.symm.toLinearMap.comp
          (((cyclotomicFullLogSpaceDeltaAction (p := p) K a).toLinearMap).comp e.toLinearMap) =
        LinearMap.prodMap
          ((cyclotomicFullLogAugmentationLinearEquiv (p := p) K a).toLinearMap)
          (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
    ext x <;> simp [LinearMap.comp_apply, e,
      cyclotomicFullLogAugmentationProdEquiv_symm_apply_deltaAction]
  calc
    LinearMap.trace ℝ (CyclotomicFullLogSpace K)
        ((cyclotomicFullLogSpaceDeltaAction (p := p) K a).toLinearMap)
        = LinearMap.trace ℝ (cyclotomicFullLogAugmentationSubmodule K × ℝ)
            (LinearMap.prodMap
              ((cyclotomicFullLogAugmentationLinearEquiv (p := p) K a).toLinearMap)
              (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) := by
          rw [← hconj]
          exact (LinearMap.trace_conj'
            ((cyclotomicFullLogSpaceDeltaAction (p := p) K a).toLinearMap) e.symm).symm
    _ = LinearMap.trace ℝ (cyclotomicFullLogAugmentationSubmodule K)
          ((cyclotomicFullLogAugmentationLinearEquiv (p := p) K a).toLinearMap) + 1 := by
          rw [LinearMap.trace_prodMap', LinearMap.trace_id]
          simp


end BernoulliRegular

end
