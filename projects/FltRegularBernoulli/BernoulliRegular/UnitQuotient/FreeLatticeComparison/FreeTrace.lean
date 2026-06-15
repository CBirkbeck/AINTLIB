module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace

/-!
# Unit quotients: free unit trace comparison

This file transports the augmentation trace computation to the Dirichlet free
unit lattice and records that the free-unit action factors through Delta
modulo ±1.
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

/-- The deleted-coordinate logarithmic space carries the transported
`Delta` action obtained by conjugating the augmentation-hyperplane action via
the deleted-coordinate equivalence. -/
noncomputable def cyclotomicDeletedLogLinearEquiv
    (a : CyclotomicUnitDelta p) :
    NumberField.Units.dirichletUnitTheorem.logSpace K ≃ₗ[ℝ]
      NumberField.Units.dirichletUnitTheorem.logSpace K :=
  (cyclotomicFullLogAugmentationEquivDeleted K).symm.trans
    ((cyclotomicFullLogAugmentationLinearEquiv (p := p) K a).trans
      (cyclotomicFullLogAugmentationEquivDeleted K))

@[simp]
theorem cyclotomicDeletedLogLinearEquiv_apply_logEmbeddingQuot
    (a : CyclotomicUnitDelta p) (x : CyclotomicUnitFreePart K) :
    cyclotomicDeletedLogLinearEquiv (p := p) K a
        (NumberField.Units.logEmbeddingQuot K x) =
      NumberField.Units.logEmbeddingQuot K
        (cyclotomicUnitFreePartDeltaAction (p := p) K a x) := by
  have hs :
      (cyclotomicFullLogAugmentationEquivDeleted K).symm
          (NumberField.Units.logEmbeddingQuot K x) =
        cyclotomicFullLogEmbeddingFreePartAugmentation K x := by
    apply (cyclotomicFullLogAugmentationEquivDeleted K).injective
    simp [cyclotomicFullLogAugmentationEquivDeleted_apply_embedding]
  calc
    cyclotomicDeletedLogLinearEquiv (p := p) K a
        (NumberField.Units.logEmbeddingQuot K x)
      = cyclotomicFullLogAugmentationEquivDeleted K
          ((cyclotomicFullLogAugmentationLinearEquiv (p := p) K a)
            (cyclotomicFullLogEmbeddingFreePartAugmentation K x)) := by
              simp [cyclotomicDeletedLogLinearEquiv, hs]
    _ = NumberField.Units.logEmbeddingQuot K
          (cyclotomicUnitFreePartDeltaAction (p := p) K a x) := by
            rw [show (cyclotomicFullLogAugmentationLinearEquiv (p := p) K a)
                  (cyclotomicFullLogEmbeddingFreePartAugmentation K x)
                = cyclotomicFullLogEmbeddingFreePartAugmentation K
                    (cyclotomicUnitFreePartDeltaAction (p := p) K a x) from
              (cyclotomicFullLogEmbeddingFreePartAugmentation_equivariant
                (p := p) (K := K) a x).symm]
            exact cyclotomicFullLogAugmentationEquivDeleted_apply_embedding (K := K)
              (cyclotomicUnitFreePartDeltaAction (p := p) K a x)

theorem cyclotomicDeletedLogLinearEquiv_map_unitLattice
    (a : CyclotomicUnitDelta p)
    {y : NumberField.Units.dirichletUnitTheorem.logSpace K}
    (hy : y ∈ NumberField.Units.unitLattice K) :
    cyclotomicDeletedLogLinearEquiv (p := p) K a y ∈
      NumberField.Units.unitLattice K := by
  change y ∈ (NumberField.Units.unitLattice K :
    Set (NumberField.Units.dirichletUnitTheorem.logSpace K)) at hy
  rw [unitLattice_eq_range_logEmbeddingQuot (K := K)] at hy
  rcases hy with ⟨x, rfl⟩
  change cyclotomicDeletedLogLinearEquiv (p := p) K a
      (NumberField.Units.logEmbeddingQuot K x) ∈
    (NumberField.Units.unitLattice K :
      Set (NumberField.Units.dirichletUnitTheorem.logSpace K))
  rw [cyclotomicDeletedLogLinearEquiv_apply_logEmbeddingQuot]
  rw [unitLattice_eq_range_logEmbeddingQuot]
  exact ⟨cyclotomicUnitFreePartDeltaAction (p := p) K a x, rfl⟩

/-- The actual free-part action, transported to the integral Dirichlet unit
lattice via `logEmbeddingEquiv`. -/
noncomputable def cyclotomicUnitLatticeLinearEquiv
    (a : CyclotomicUnitDelta p) :
    NumberField.Units.unitLattice K ≃ₗ[ℤ] NumberField.Units.unitLattice K :=
  (NumberField.Units.logEmbeddingEquiv K).symm.trans
    ((cyclotomicUnitFreePartLinearEquiv (p := p) K a).trans
      (NumberField.Units.logEmbeddingEquiv K))

@[simp]
theorem cyclotomicUnitLatticeLinearEquiv_apply_logEmbeddingEquiv
    (a : CyclotomicUnitDelta p) (x : CyclotomicUnitFreePart K) :
    cyclotomicUnitLatticeLinearEquiv (p := p) K a
        (NumberField.Units.logEmbeddingEquiv K x) =
      NumberField.Units.logEmbeddingEquiv K
        ((cyclotomicUnitFreePartLinearEquiv (p := p) K a) x) := by
  simp [cyclotomicUnitLatticeLinearEquiv]

@[simp]
theorem cyclotomicDeletedLogLinearEquiv_apply_unitLattice
    (a : CyclotomicUnitDelta p) (y : NumberField.Units.unitLattice K) :
    cyclotomicDeletedLogLinearEquiv (p := p) K a
        (y : NumberField.Units.dirichletUnitTheorem.logSpace K) =
      (cyclotomicUnitLatticeLinearEquiv (p := p) K a y :
        NumberField.Units.dirichletUnitTheorem.logSpace K) := by
  rcases (NumberField.Units.logEmbeddingEquiv K).surjective y with ⟨x, rfl⟩
  calc
    cyclotomicDeletedLogLinearEquiv (p := p) K a
        ((NumberField.Units.logEmbeddingEquiv K x : NumberField.Units.unitLattice K) :
          NumberField.Units.dirichletUnitTheorem.logSpace K)
      = NumberField.Units.logEmbeddingQuot K
          (cyclotomicUnitFreePartDeltaAction (p := p) K a x) :=
        cyclotomicDeletedLogLinearEquiv_apply_logEmbeddingQuot
          (p := p) (K := K) a x
    _ = (cyclotomicUnitLatticeLinearEquiv (p := p) K a
          (NumberField.Units.logEmbeddingEquiv K x) :
            NumberField.Units.dirichletUnitTheorem.logSpace K) := by
          rw [cyclotomicUnitLatticeLinearEquiv_apply_logEmbeddingEquiv]
          rfl

@[simp]
theorem cyclotomicUnitLatticeLinearEquiv_toMatrix_apply
    (a : CyclotomicUnitDelta p)
    (i j : Fin (NumberField.Units.rank K)) :
    LinearMap.toMatrixAlgEquiv (NumberField.Units.basisUnitLattice K)
        ((cyclotomicUnitLatticeLinearEquiv (p := p) K a).toLinearMap) i j =
      LinearMap.toMatrixAlgEquiv (cyclotomicUnitFreeBasis K)
        ((cyclotomicUnitFreePartLinearEquiv (p := p) K a).toLinearMap) i j := by
  rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrixAlgEquiv_apply]
  change (NumberField.Units.basisUnitLattice K).repr
      (cyclotomicUnitLatticeLinearEquiv (p := p) K a
        ((NumberField.Units.basisUnitLattice K) j)) i =
    (cyclotomicUnitFreeBasis K).repr
      ((cyclotomicUnitFreePartLinearEquiv (p := p) K a)
        ((cyclotomicUnitFreeBasis K) j)) i
  simp [NumberField.Units.basisUnitLattice, cyclotomicUnitFreeBasis,
    cyclotomicUnitLatticeLinearEquiv_apply_logEmbeddingEquiv]

@[simp]
theorem cyclotomicDeletedLogLinearEquiv_toUnitLatticeMatrix_apply
  [IsZLattice ℝ (NumberField.Units.unitLattice K)]
    (a : CyclotomicUnitDelta p)
    (i j : Fin (NumberField.Units.rank K)) :
    LinearMap.toMatrixAlgEquiv
        ((NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
          (NumberField.Units.unitLattice K))
        ((cyclotomicDeletedLogLinearEquiv (p := p) K a).toLinearMap) i j =
      ((LinearMap.toMatrixAlgEquiv (NumberField.Units.basisUnitLattice K)
          ((cyclotomicUnitLatticeLinearEquiv (p := p) K a).toLinearMap) i j : ℤ) : ℝ) := by
  rw [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrixAlgEquiv_apply]
  change (((NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
      (NumberField.Units.unitLattice K)).repr
      (cyclotomicDeletedLogLinearEquiv (p := p) K a
        (((NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
            (NumberField.Units.unitLattice K)) j)) i) =
    (((NumberField.Units.basisUnitLattice K).repr
      (cyclotomicUnitLatticeLinearEquiv (p := p) K a
        ((NumberField.Units.basisUnitLattice K) j)) i : ℤ) : ℝ)
  rw [show ((NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
      (NumberField.Units.unitLattice K)) j = (NumberField.Units.basisUnitLattice K) j by
        simp]
  rw [cyclotomicDeletedLogLinearEquiv_apply_unitLattice]
  simp

@[simp]
theorem cyclotomicDeletedLogLinearEquiv_toMatrix_apply
  [IsZLattice ℝ (NumberField.Units.unitLattice K)]
    (a : CyclotomicUnitDelta p)
    (i j : Fin (NumberField.Units.rank K)) :
    LinearMap.toMatrixAlgEquiv
        ((NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
          (NumberField.Units.unitLattice K))
        ((cyclotomicDeletedLogLinearEquiv (p := p) K a).toLinearMap) i j =
      ((LinearMap.toMatrixAlgEquiv (cyclotomicUnitFreeBasis K)
          ((cyclotomicUnitFreePartLinearEquiv (p := p) K a).toLinearMap) i j : ℤ) : ℝ) := by
  rw [cyclotomicDeletedLogLinearEquiv_toUnitLatticeMatrix_apply,
    cyclotomicUnitLatticeLinearEquiv_toMatrix_apply]

theorem cyclotomicDeletedLogLinearEquiv_trace
  [IsZLattice ℝ (NumberField.Units.unitLattice K)]
    (a : CyclotomicUnitDelta p) :
    LinearMap.trace ℝ (NumberField.Units.dirichletUnitTheorem.logSpace K)
        ((cyclotomicDeletedLogLinearEquiv (p := p) K a).toLinearMap) =
      ((LinearMap.trace ℤ (CyclotomicUnitFreePart K)
          ((cyclotomicUnitFreePartLinearEquiv (p := p) K a).toLinearMap) : ℤ) : ℝ) := by
  rw [LinearMap.trace_eq_matrix_trace
      (b := (NumberField.Units.basisUnitLattice K).ofZLatticeBasis ℝ
        (NumberField.Units.unitLattice K)),
    LinearMap.trace_eq_matrix_trace (b := cyclotomicUnitFreeBasis K)]
  simp only [Matrix.trace, Matrix.diag]
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact cyclotomicDeletedLogLinearEquiv_toMatrix_apply (p := p) (K := K) a i i

theorem cyclotomicFullLogAugmentationLinearEquiv_trace
  [IsZLattice ℝ (NumberField.Units.unitLattice K)]
    (a : CyclotomicUnitDelta p) :
    LinearMap.trace ℝ (cyclotomicFullLogAugmentationSubmodule K)
        ((cyclotomicFullLogAugmentationLinearEquiv (p := p) K a).toLinearMap) =
      ((LinearMap.trace ℤ (CyclotomicUnitFreePart K)
          ((cyclotomicUnitFreePartLinearEquiv (p := p) K a).toLinearMap) : ℤ) : ℝ) := by
  calc
    LinearMap.trace ℝ (cyclotomicFullLogAugmentationSubmodule K)
        ((cyclotomicFullLogAugmentationLinearEquiv (p := p) K a).toLinearMap)
      = LinearMap.trace ℝ (NumberField.Units.dirichletUnitTheorem.logSpace K)
          ((cyclotomicDeletedLogLinearEquiv (p := p) K a).toLinearMap) := by
            symm
            rw [show (cyclotomicDeletedLogLinearEquiv (p := p) K a).toLinearMap =
                (cyclotomicFullLogAugmentationEquivDeleted K).conj
                  ((cyclotomicFullLogAugmentationLinearEquiv (p := p) K a).toLinearMap) from
              rfl]
            exact LinearMap.trace_conj'
              ((cyclotomicFullLogAugmentationLinearEquiv (p := p) K a).toLinearMap)
              (cyclotomicFullLogAugmentationEquivDeleted K)
    _ = ((LinearMap.trace ℤ (CyclotomicUnitFreePart K)
          ((cyclotomicUnitFreePartLinearEquiv (p := p) K a).toLinearMap) : ℤ) : ℝ) :=
        cyclotomicDeletedLogLinearEquiv_trace (p := p) (K := K) a

theorem cyclotomicUnitFreePartLinearEquiv_trace_formula
  [IsZLattice ℝ (NumberField.Units.unitLattice K)]
    (hp_gt_two : 2 < p) (a : CyclotomicUnitDelta p) :
    LinearMap.trace ℤ (CyclotomicUnitFreePart K)
        ((cyclotomicUnitFreePartLinearEquiv (p := p) K a).toLinearMap) =
      if cyclotomicEvenDeltaQuotient p a = 1 then
        (NumberField.Units.rank K : ℤ) else -1 := by
  apply Int.cast_injective (α := ℝ)
  by_cases hq : cyclotomicEvenDeltaQuotient p a = 1
  · rw [if_pos hq, Int.cast_natCast]
    rw [← cyclotomicFullLogAugmentationLinearEquiv_trace (p := p) (K := K) a,
      cyclotomicFullLogAugmentationLinearEquiv_trace_formula
        (p := p) (K := K) hp_gt_two a, if_pos hq]
  · rw [if_neg hq, Int.cast_neg, Int.cast_one]
    rw [← cyclotomicFullLogAugmentationLinearEquiv_trace (p := p) (K := K) a,
      cyclotomicFullLogAugmentationLinearEquiv_trace_formula
        (p := p) (K := K) hp_gt_two a, if_neg hq]

/-- The action of `-1 ∈ Delta` on the ring of integers is complex
conjugation. -/
theorem cyclotomicRingOfIntegersEquiv_neg_one_apply
    (hp_gt_two : 2 < p) (x : 𝓞 K) :
    cyclotomicRingOfIntegersEquiv (p := p) K (-1) x =
      cyclotomicRingOfIntegersComplexConj (p := p) K hp_gt_two x := by
  apply RingOfIntegers.ext
  change cyclotomicSigmaOfUnit (p := p) K (-1) (x : K) =
    cyclotomicComplexConjGal (p := p) K hp_gt_two (x : K)
  rw [cyclotomicSigmaOfUnit_neg_one_eq_complexConjGal (p := p) (K := K) hp_gt_two]

/-- The action of `-1 ∈ Delta` on units is complex conjugation. -/
theorem cyclotomicUnitEquiv_neg_one_apply
    (hp_gt_two : 2 < p) (u : CyclotomicUnitGroup K) :
    cyclotomicUnitEquiv (p := p) K (-1) u =
      cyclotomicUnitsComplexConj (p := p) K hp_gt_two u := by
  apply Units.ext
  change cyclotomicRingOfIntegersEquiv (p := p) K (-1) (u : 𝓞 K) =
    cyclotomicRingOfIntegersComplexConj (p := p) K hp_gt_two (u : 𝓞 K)
  exact cyclotomicRingOfIntegersEquiv_neg_one_apply
    (p := p) (K := K) hp_gt_two (u : 𝓞 K)

/-- In a cyclotomic CM field, a unit and its complex conjugate have the same
class modulo roots of unity. -/
theorem cyclotomicUnitFreeClass_unitsComplexConj_eq
    (hp_gt_two : 2 < p) (u : CyclotomicUnitGroup K) :
    cyclotomicUnitFreeClass K
        (cyclotomicUnitsComplexConj (p := p) K hp_gt_two u) =
      cyclotomicUnitFreeClass K u := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  have htorsion :
      u * (cyclotomicUnitsComplexConj (p := p) K hp_gt_two u)⁻¹ ∈
        CyclotomicUnitTorsion K :=
    (NumberField.IsCMField.unitsMulComplexConjInv K u).property
  have hfree :
      cyclotomicUnitFreeClass K
          (u * (cyclotomicUnitsComplexConj (p := p) K hp_gt_two u)⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, cyclotomicUnitFreeClass_ker]
    exact htorsion
  rw [map_mul, map_inv] at hfree
  exact (mul_inv_eq_one.mp hfree).symm

/-- Additive form of `cyclotomicUnitFreeClass_unitsComplexConj_eq`. -/
theorem cyclotomicUnitFreePart_unitsComplexConj_eq
    (hp_gt_two : 2 < p) (u : CyclotomicUnitGroup K) :
    Additive.ofMul
        (cyclotomicUnitFreeClass K
          (cyclotomicUnitsComplexConj (p := p) K hp_gt_two u)) =
      Additive.ofMul (cyclotomicUnitFreeClass K u) := by
  rw [cyclotomicUnitFreeClass_unitsComplexConj_eq (p := p) (K := K) hp_gt_two u]

/-- Complex conjugation also acts trivially after reducing the free quotient
modulo `p`. -/
theorem cyclotomicUnitFreePartModPClass_unitsComplexConj_eq
    (hp_gt_two : 2 < p) (u : CyclotomicUnitGroup K) :
    cyclotomicUnitFreePartModPClass (p := p) K
        (Additive.ofMul
          (cyclotomicUnitFreeClass K
            (cyclotomicUnitsComplexConj (p := p) K hp_gt_two u))) =
      cyclotomicUnitFreePartModPClass (p := p) K
        (Additive.ofMul (cyclotomicUnitFreeClass K u)) := by
  rw [cyclotomicUnitFreePart_unitsComplexConj_eq (p := p) (K := K) hp_gt_two u]

/-- The element `-1 ∈ Delta` acts trivially on every unit class in the
torsion-free quotient. -/
theorem cyclotomicUnitFreePartLinearEquiv_neg_one_apply_class
    (hp_gt_two : 2 < p) (u : CyclotomicUnitGroup K) :
    cyclotomicUnitFreePartLinearEquiv (p := p) K (-1)
        (Additive.ofMul (cyclotomicUnitFreeClass K u)) =
      Additive.ofMul (cyclotomicUnitFreeClass K u) := by
  rw [cyclotomicUnitFreePartLinearEquiv_apply_class,
    cyclotomicUnitEquiv_neg_one_apply (p := p) (K := K) hp_gt_two,
    cyclotomicUnitFreePart_unitsComplexConj_eq (p := p) (K := K) hp_gt_two]

/-- The element `-1 ∈ Delta` acts trivially on the whole torsion-free unit
quotient. -/
theorem cyclotomicUnitFreePartLinearEquiv_neg_one_apply
    (hp_gt_two : 2 < p) (x : CyclotomicUnitFreePart K) :
    cyclotomicUnitFreePartLinearEquiv (p := p) K (-1) x = x := by
  induction x using Additive.rec with
  | ofMul q =>
      refine QuotientGroup.induction_on q ?_
      intro u
      exact cyclotomicUnitFreePartLinearEquiv_neg_one_apply_class
        (p := p) (K := K) hp_gt_two u

/-- The actual `Delta` action sends `-1` to the identity on the torsion-free
unit quotient. -/
theorem cyclotomicUnitFreePartDeltaAction_neg_one_apply
    (hp_gt_two : 2 < p) (x : CyclotomicUnitFreePart K) :
    cyclotomicUnitFreePartDeltaAction (p := p) K (-1) x = x :=
  cyclotomicUnitFreePartLinearEquiv_neg_one_apply
    (p := p) (K := K) hp_gt_two x

/-- The actual action on the torsion-free unit quotient factors through
`Delta / {±1}`. -/
noncomputable def cyclotomicUnitFreePartEvenDeltaAction
    (hp_gt_two : 2 < p) :
    CyclotomicEvenDelta p →*
      (CyclotomicUnitFreePart K ≃ₗ[ℤ] CyclotomicUnitFreePart K) :=
  QuotientGroup.lift
    (CyclotomicEvenDeltaSubgroup p)
    (cyclotomicUnitFreePartDeltaAction (p := p) K)
    (by
      apply Subgroup.zpowers_le_of_mem
      rw [MonoidHom.mem_ker]
      ext x
      exact cyclotomicUnitFreePartDeltaAction_neg_one_apply
        (p := p) (K := K) hp_gt_two x)

@[simp]
theorem cyclotomicUnitFreePartEvenDeltaAction_apply_quotient
    (hp_gt_two : 2 < p) (a : CyclotomicUnitDelta p) :
    cyclotomicUnitFreePartEvenDeltaAction (p := p) K hp_gt_two
        (cyclotomicEvenDeltaQuotient p a) =
      cyclotomicUnitFreePartDeltaAction (p := p) K a :=
  rfl


end BernoulliRegular

end
