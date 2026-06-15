module

public import BernoulliRegular.UnitQuotient.FreeCharacterProfile

/-!
# Unit quotients: augmentation comparison

This file defines the full logarithmic augmentation hyperplane, identifies it
with the deleted-coordinate logarithmic space, and records the equivariant
restricted embedding of the torsion-free unit quotient.
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

/-- The summation map on the full logarithmic space.  The logarithmic image of
global units lies in its kernel by the product formula. -/
def cyclotomicFullLogAugmentationMap :
    CyclotomicFullLogSpace K →ₗ[ℝ] ℝ where
  toFun f := ∑ w : InfinitePlace K, f w
  map_add' f g := by
    simp [sum_add_distrib]
  map_smul' c f := by
    change ∑ w : InfinitePlace K, c * f w =
      c * ∑ w : InfinitePlace K, f w
    rw [Finset.mul_sum]

/-- The full logarithmic augmentation hyperplane. -/
def cyclotomicFullLogAugmentationSubmodule :
    Submodule ℝ (CyclotomicFullLogSpace K) :=
  LinearMap.ker (cyclotomicFullLogAugmentationMap K)

theorem cyclotomicFullLogEmbedding_mem_augmentation
    (u : CyclotomicUnitGroup K) :
    cyclotomicFullLogEmbedding K (Additive.ofMul u) ∈
      cyclotomicFullLogAugmentationSubmodule K := by
  rw [cyclotomicFullLogAugmentationSubmodule, LinearMap.mem_ker]
  exact NumberField.Units.sum_mult_mul_log u

theorem cyclotomicFullLogEmbeddingFreePart_mem_augmentation
    (x : CyclotomicUnitFreePart K) :
    cyclotomicFullLogEmbeddingFreePart K x ∈
      cyclotomicFullLogAugmentationSubmodule K := by
  induction x using Additive.rec with
  | ofMul q =>
      refine QuotientGroup.induction_on q ?_
      intro u
      change cyclotomicFullLogEmbeddingFreePart K
          (Additive.ofMul (cyclotomicUnitFreeClass K u)) ∈
        cyclotomicFullLogAugmentationSubmodule K
      rw [cyclotomicFullLogEmbeddingFreePart_apply]
      exact cyclotomicFullLogEmbedding_mem_augmentation (K := K) u

/-- The full logarithmic embedding, with codomain restricted to the
augmentation hyperplane. -/
def cyclotomicFullLogEmbeddingFreePartAugmentation :
    CyclotomicUnitFreePart K →+
      cyclotomicFullLogAugmentationSubmodule K :=
  (cyclotomicFullLogEmbeddingFreePart K).codRestrict
    (cyclotomicFullLogAugmentationSubmodule K)
    (cyclotomicFullLogEmbeddingFreePart_mem_augmentation (K := K))

@[simp]
theorem cyclotomicFullLogEmbeddingFreePartAugmentation_apply
    (x : CyclotomicUnitFreePart K) :
    (cyclotomicFullLogEmbeddingFreePartAugmentation K x :
        CyclotomicFullLogSpace K) =
      cyclotomicFullLogEmbeddingFreePart K x :=
  rfl

/-- Delete the distinguished coordinate from the full augmentation hyperplane.
The missing coordinate is recovered from the relation that the sum is zero. -/
noncomputable def cyclotomicFullLogAugmentationEquivDeleted :
    cyclotomicFullLogAugmentationSubmodule K ≃ₗ[ℝ]
      NumberField.Units.dirichletUnitTheorem.logSpace K := by
  classical
  refine
    { toFun := fun f w => f.1 w.1
      map_add' := by
        intro f g
        ext w
        rfl
      map_smul' := by
        intro c f
        ext w
        rfl
      invFun := fun g =>
        ⟨fun w =>
          if h : w = NumberField.Units.dirichletUnitTheorem.w₀ then
            -∑ v : {v : InfinitePlace K //
                v ≠ NumberField.Units.dirichletUnitTheorem.w₀}, g v
          else
            g ⟨w, h⟩,
          by
            rw [cyclotomicFullLogAugmentationSubmodule, LinearMap.mem_ker]
            change ∑ w : InfinitePlace K,
                (if h : w = NumberField.Units.dirichletUnitTheorem.w₀ then
                  -∑ v : {v : InfinitePlace K //
                      v ≠ NumberField.Units.dirichletUnitTheorem.w₀}, g v
                else
                  g ⟨w, h⟩) = 0
            rw [Fintype.sum_eq_add_sum_subtype_ne _
              NumberField.Units.dirichletUnitTheorem.w₀]
            rw [show
                (∑ x : {v : InfinitePlace K //
                    v ≠ NumberField.Units.dirichletUnitTheorem.w₀},
                  (if h : (x : InfinitePlace K) =
                      NumberField.Units.dirichletUnitTheorem.w₀ then
                    -∑ v : {v : InfinitePlace K //
                        v ≠ NumberField.Units.dirichletUnitTheorem.w₀}, g v
                  else
                    g ⟨x, h⟩)) = ∑ x, g x by
              apply Finset.sum_congr rfl
              intro x _hx
              rw [dif_neg x.2]]
            simp
        ⟩
      left_inv := by
        intro f
        ext w
        by_cases hw : w = NumberField.Units.dirichletUnitTheorem.w₀
        · subst hw
          have hsum : ∑ v : InfinitePlace K, f.1 v = 0 := by
            have hf : f.1 ∈ LinearMap.ker (cyclotomicFullLogAugmentationMap K) := f.2
            rw [LinearMap.mem_ker] at hf
            exact hf
          rw [Fintype.sum_eq_add_sum_subtype_ne _
            NumberField.Units.dirichletUnitTheorem.w₀] at hsum
          change (if h : NumberField.Units.dirichletUnitTheorem.w₀ =
              NumberField.Units.dirichletUnitTheorem.w₀ then
            -∑ v : {v : InfinitePlace K //
                v ≠ NumberField.Units.dirichletUnitTheorem.w₀}, f.1 v
          else
            f.1 NumberField.Units.dirichletUnitTheorem.w₀) =
            f.1 NumberField.Units.dirichletUnitTheorem.w₀
          rw [dif_pos rfl]
          linarith
        · change (if h : w = NumberField.Units.dirichletUnitTheorem.w₀ then
            -∑ v : {v : InfinitePlace K //
                v ≠ NumberField.Units.dirichletUnitTheorem.w₀}, f.1 v
          else
            f.1 w) = f.1 w
          rw [dif_neg hw]
      right_inv := by
        intro g
        ext w
        change (if h : (w : InfinitePlace K) =
            NumberField.Units.dirichletUnitTheorem.w₀ then
          -∑ v : {v : InfinitePlace K //
              v ≠ NumberField.Units.dirichletUnitTheorem.w₀}, g v
        else
          g ⟨w, h⟩) = g w
        rw [dif_neg w.2] }

@[simp]
theorem cyclotomicFullLogAugmentationEquivDeleted_apply
    (f : cyclotomicFullLogAugmentationSubmodule K)
    (w : {w : InfinitePlace K //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    cyclotomicFullLogAugmentationEquivDeleted K f w = f.1 w.1 :=
  rfl

theorem cyclotomicFullLogAugmentationEquivDeleted_apply_embedding
    (x : CyclotomicUnitFreePart K) :
    cyclotomicFullLogAugmentationEquivDeleted K
        (cyclotomicFullLogEmbeddingFreePartAugmentation K x) =
      NumberField.Units.logEmbeddingQuot K x := by
  induction x using Additive.rec with
  | ofMul q =>
      refine QuotientGroup.induction_on q ?_
      intro u
      ext w
      rw [cyclotomicFullLogAugmentationEquivDeleted_apply]
      rw [NumberField.Units.logEmbeddingQuot_apply]
      rfl

theorem unitLattice_eq_range_logEmbeddingQuot :
    (NumberField.Units.unitLattice K :
        Set (NumberField.Units.dirichletUnitTheorem.logSpace K)) =
      Set.range (NumberField.Units.logEmbeddingQuot K) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨u, _hu, rfl⟩
    refine ⟨Additive.ofMul (QuotientGroup.mk u.toMul), ?_⟩
    exact NumberField.Units.logEmbeddingQuot_apply K u.toMul
  · rintro ⟨x, rfl⟩
    induction x using Additive.rec with
    | ofMul q =>
        refine QuotientGroup.induction_on q ?_
        intro u
        rw [NumberField.Units.logEmbeddingQuot_apply]
        exact Submodule.mem_map_of_mem trivial

/-- The full logarithmic image of the torsion-free unit quotient spans the
augmentation hyperplane. -/
theorem cyclotomicFullLogEmbeddingFreePartAugmentation_span_eq_top :
    Submodule.span ℝ
        (Set.range (cyclotomicFullLogEmbeddingFreePartAugmentation K)) =
      ⊤ := by
  let e := cyclotomicFullLogAugmentationEquivDeleted K
  rw [← Submodule.map_eq_top_iff (e := e)]
  rw [Submodule.map_span]
  let imageSet : Set (NumberField.Units.dirichletUnitTheorem.logSpace K) :=
    (cyclotomicFullLogAugmentationEquivDeleted K ''
      Set.range (cyclotomicFullLogEmbeddingFreePartAugmentation K))
  have himage :
      imageSet =
        (NumberField.Units.unitLattice K :
          Set (NumberField.Units.dirichletUnitTheorem.logSpace K)) := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      rw [cyclotomicFullLogAugmentationEquivDeleted_apply_embedding]
      rw [unitLattice_eq_range_logEmbeddingQuot]
      exact ⟨z, rfl⟩
    · intro hy
      rw [unitLattice_eq_range_logEmbeddingQuot] at hy
      rcases hy with ⟨z, rfl⟩
      refine ⟨cyclotomicFullLogEmbeddingFreePartAugmentation K z, ⟨z, rfl⟩, ?_⟩
      rw [cyclotomicFullLogAugmentationEquivDeleted_apply_embedding]
  change Submodule.span ℝ imageSet = ⊤
  rw [himage]
  exact NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top K

/-- Ambient-space version of
`cyclotomicFullLogEmbeddingFreePartAugmentation_span_eq_top`. -/
theorem cyclotomicFullLogEmbeddingFreePart_span_eq_augmentation :
    Submodule.span ℝ (Set.range (cyclotomicFullLogEmbeddingFreePart K)) =
      cyclotomicFullLogAugmentationSubmodule K := by
  let S := cyclotomicFullLogAugmentationSubmodule K
  have htop := cyclotomicFullLogEmbeddingFreePartAugmentation_span_eq_top (K := K)
  have hmap := congrArg (fun T : Submodule ℝ S => T.map S.subtype) htop
  change Submodule.map S.subtype
      (Submodule.span ℝ
        (Set.range (cyclotomicFullLogEmbeddingFreePartAugmentation K))) =
    Submodule.map S.subtype (⊤ : Submodule ℝ S) at hmap
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hmap
  have hset :
      ((fun a : S => (a : CyclotomicFullLogSpace K)) ''
          Set.range (cyclotomicFullLogEmbeddingFreePartAugmentation K)) =
        Set.range (cyclotomicFullLogEmbeddingFreePart K) := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨cyclotomicFullLogEmbeddingFreePartAugmentation K z, ⟨z, rfl⟩, rfl⟩
  change Submodule.span ℝ
      ((fun a : S => (a : CyclotomicFullLogSpace K)) ''
        Set.range (cyclotomicFullLogEmbeddingFreePartAugmentation K)) =
    S at hmap
  rw [hset] at hmap
  exact hmap

/-- Equivariance of the logarithmic embedding after restricting its codomain
to the augmentation hyperplane. -/
theorem cyclotomicFullLogEmbeddingFreePartAugmentation_equivariant
    (a : CyclotomicUnitDelta p) (x : CyclotomicUnitFreePart K) :
    cyclotomicFullLogEmbeddingFreePartAugmentation K
        (cyclotomicUnitFreePartDeltaAction (p := p) K a x) =
      ⟨cyclotomicFullLogSpaceDeltaAction (p := p) K a
          (cyclotomicFullLogEmbeddingFreePart K x),
        by
          rw [← cyclotomicFullLogEmbeddingFreePart_equivariant
            (p := p) (K := K) a x]
          exact cyclotomicFullLogEmbeddingFreePart_mem_augmentation (K := K)
            (cyclotomicUnitFreePartDeltaAction (p := p) K a x)⟩ := by
  ext w
  exact congrFun
    (cyclotomicFullLogEmbeddingFreePart_equivariant (p := p) (K := K) a x) w

end BernoulliRegular

end
