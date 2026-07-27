/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.FiniteProperClosure
import ModularCurves.ForMathlib.FiniteProjectiveFactorization

/-!
# Projectivity of finite proper closures

The scheme-theoretic closure inside a nonempty finite product of projectively factored schemes
still has a projective factorization over the affine base.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FiniteProperClosure

variable {R : Type u} [CommRing R] {T : Scheme.{u}}
variable {ι : Type u} [Finite ι] [Nonempty ι]
variable {Z : ι → Scheme.{u}} (p : ∀ i, Z i ⟶ Spec (.of R))
variable (q : T ⟶ Spec (.of R)) (f : ∀ i, T ⟶ Z i)
variable (hf : ∀ i, f i ≫ p i = q)

/-- A scheme-theoretic closure in a nonempty finite projective product is projective. -/
lemma π_isProjectiveFactorization
    (hp : ∀ i, AlgebraicGeometry.IsProjectiveFactorization (p i)) :
    AlgebraicGeometry.IsProjectiveFactorization (π p q f hf) :=
  (FiniteProperProduct.π_isProjectiveFactorization p hp).comp_isClosedImmersion
    (inclusion p q f hf) (by infer_instance)

end AlgebraicGeometry.Scheme.FiniteProperClosure
