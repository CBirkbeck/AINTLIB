/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.GroupLawConstruction

/-!
# Base-change naturality of negation on the projective Weierstrass model

`negModelHom W : projModel W ⟶ projModel W` (`GroupLawConstruction`) is the negation
endomorphism, `Proj.map` of the graded substitution `X ↦ X, Y ↦ −Y−a₁X−a₃Z, Z ↦ Z`. This file
proves it commutes with the base-change morphism `projModelBaseChange f W`, mirroring
`projModelZero_baseChange` (`WeierstrassModel.lean`).

Both `negModelHom` and `projModelBaseChange` are `Proj.map` of graded homomorphisms, so the
naturality square reduces (via `Proj.map_comp` both ways) to the graded homomorphisms
commuting — which is the polynomial fact that base change commutes with the (universally
formulaic) negation substitution: `negVec (W.map f) = MvPolynomial.map f ∘ negVec W`.

## Main results

* `negModelHom_baseChange`: `negModelHom (W.map f) ≫ projModelBaseChange f W =
  projModelBaseChange f W ≫ negModelHom W`. Consumed by the `invOver` group-axiom transport
  (c5β's T-G4).
-/

open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousIdeal

universe u

namespace ModularCurves

attribute [local instance] MvPolynomial.gradedAlgebra

-- `Proj_map_congr` (equality of `Proj.map`s from equal graded homs) is the shared public
-- helper from `GroupLawConstruction` (imported above); the former local copy was deduplicated.

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']

/-- The negation substitution vector base-changes coefficientwise: negating over `W.map f`
is negating over `W` followed by coefficient base change (the `a₁`, `a₃` coefficients map). -/
lemma negVec_map (f : R →+* R') (W : WeierstrassCurve R) (i : Fin 3) :
    negVec (W.map f) i = MvPolynomial.map f (negVec W i) := by
  fin_cases i <;>
    simp [negVec, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, sub_eq_add_neg]

/-- The negation substitution commutes with coefficient base change on all of `R[X,Y,Z]`. -/
lemma aeval_negVec_map (f : R →+* R') (W : WeierstrassCurve R) (p : MvPolynomial (Fin 3) R) :
    aeval (negVec (W.map f)) (MvPolynomial.map f p)
      = MvPolynomial.map f (aeval (negVec W) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.map_X, map_mul, aeval_X, map_mul, hp, map_mul, aeval_X, negVec_map]

/-- The graded negation endomorphism commutes with the graded base-change homomorphism. -/
lemma negGradedQuot_comp_baseChangeGradedHom (f : R →+* R') (W : WeierstrassCurve R) :
    (negGradedQuot (W.map f)).comp (baseChangeGradedHom f W)
      = (baseChangeGradedHom f W).comp (negGradedQuot W) := by
  refine GradedRingHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hbc : ∀ p : MvPolynomial (Fin 3) R,
      baseChangeGradedHom f W (Ideal.Quotient.mk (projIdeal W).toIdeal p)
        = Ideal.Quotient.mk (projIdeal (W.map f)).toIdeal (MvPolynomial.map f p) :=
    fun p ↦ quotientGradingMap_mk (mvMapGraded f) (projIdeal W) (projIdeal (W.map f))
      (projIdeal_le_comap f W) p
  have hneg : ∀ p : MvPolynomial (Fin 3) R,
      negGradedQuot W (Ideal.Quotient.mk (projIdeal W).toIdeal p)
        = Ideal.Quotient.mk (projIdeal W).toIdeal (aeval (negVec W) p) :=
    fun p ↦ quotientGradingMap_mk (negGradedPoly W) (projIdeal W) (projIdeal W)
      (negGradedPoly_comap W) p
  have hneg' : ∀ p : MvPolynomial (Fin 3) R',
      negGradedQuot (W.map f) (Ideal.Quotient.mk (projIdeal (W.map f)).toIdeal p)
        = Ideal.Quotient.mk (projIdeal (W.map f)).toIdeal (aeval (negVec (W.map f)) p) :=
    fun p ↦ quotientGradingMap_mk (negGradedPoly (W.map f)) (projIdeal (W.map f))
      (projIdeal (W.map f)) (negGradedPoly_comap (W.map f)) p
  show negGradedQuot (W.map f) (baseChangeGradedHom f W (Ideal.Quotient.mk _ a))
    = baseChangeGradedHom f W (negGradedQuot W (Ideal.Quotient.mk _ a))
  rw [hbc, hneg', hneg, hbc]
  exact congrArg (Ideal.Quotient.mk _) (aeval_negVec_map f W a)

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-W7.0b-BC)** Negation on the projective Weierstrass model commutes with base change:
`negModelHom` is natural in the base ring. Mirrors `projModelZero_baseChange`; consumed by the
`invOver` Over-level group-axiom transport (c5β's T-G4). -/
theorem negModelHom_baseChange (f : R →+* R') (W : WeierstrassCurve R) :
    negModelHom (W.map f) ≫ projModelBaseChange f W
      = projModelBaseChange f W ≫ negModelHom W := by
  simp only [negModelHom]
  rw [show projModelBaseChange f W
      = Proj.map (baseChangeGradedHom f W) (baseChangeGradedHom_irrelevant_le f W) from rfl,
    ← Proj.map_comp, ← Proj.map_comp]
  exact Proj_map_congr (negGradedQuot_comp_baseChangeGradedHom f W) _ _

end ModularCurves
