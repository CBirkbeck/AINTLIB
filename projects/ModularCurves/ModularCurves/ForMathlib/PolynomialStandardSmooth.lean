/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Polynomial algebras are standard smooth of their rank

The free presentation of `MvPolynomial ι R` (generators `ι`, no relations) is a
submersive presentation of dimension `Nat.card ι`; hence `MvPolynomial ι R` is
standard smooth of relative dimension `Nat.card ι` over `R`, and `Polynomial R`
is standard smooth of relative dimension `1`.

These are the missing base instances for the λ-line chart computation of the
`Y(ρ̄)` smoothness leaf (T-YR-6 (b1)); `IsStandardSmoothOfRelativeDimension`'s
`.trans` and `.localization_away` then give relative dimension 1 for localized
polynomial algebras.
-/

namespace Algebra

open MvPolynomial

variable (R : Type*) [CommRing R] (ι : Type) [Finite ι]

/-- The free submersive presentation of the polynomial algebra: `ι` generators,
no relations, trivially invertible (empty) Jacobian. -/
noncomputable def SubmersivePresentation.mvPolynomialFree :
    SubmersivePresentation R (MvPolynomial ι R) ι PEmpty.{1} where
  toGenerators := Generators.mvPolynomial R ι
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    rw [Set.range_eq_empty, Ideal.span_empty, Generators.ker_mvPolynomial]
  map := PEmpty.elim
  map_inj := fun a => a.elim
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.jacobian,
      LinearMap.det_eq_one_of_subsingleton, map_one]
    exact isUnit_one

@[simp]
lemma SubmersivePresentation.mvPolynomialFree_dimension :
    (SubmersivePresentation.mvPolynomialFree R ι).dimension = Nat.card ι := by
  simp [Presentation.dimension]

/-- The polynomial algebra on a finite type is standard smooth of relative
dimension its cardinality. -/
theorem IsStandardSmoothOfRelativeDimension.mvPolynomial :
    IsStandardSmoothOfRelativeDimension (Nat.card ι) R (MvPolynomial ι R) :=
  (SubmersivePresentation.mvPolynomialFree R ι).isStandardSmoothOfRelativeDimension
    (SubmersivePresentation.mvPolynomialFree_dimension R ι)

/-- The univariate polynomial algebra is standard smooth of relative
dimension one. -/
theorem IsStandardSmoothOfRelativeDimension.polynomial :
    IsStandardSmoothOfRelativeDimension 1 R (Polynomial R) := by
  haveI h : IsStandardSmoothOfRelativeDimension 1 R
      (MvPolynomial PUnit.{1} R) := by
    have h0 := IsStandardSmoothOfRelativeDimension.mvPolynomial R PUnit.{1}
    rwa [Nat.card_unique] at h0
  exact IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
    (e := (MvPolynomial.pUnitAlgEquiv R :
      MvPolynomial PUnit.{1} R ≃ₐ[R] Polynomial R))

end Algebra
