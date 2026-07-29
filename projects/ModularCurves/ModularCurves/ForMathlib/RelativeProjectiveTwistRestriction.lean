/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.RelativeProjectiveFactorizationAffineMap
import ModularCurves.ForMathlib.RelativeProjectiveTwist

/-!
# Restricting twists from a relative projective factorization

Restriction of a chosen relative projective twist is pullback along the restricted source
inclusion followed by the chosen projective map.
-/

open CategoryTheory

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.IsRelativeProjectiveFactorization

variable {R : Type u} [CommRing R] {X S : Scheme.{u}}
variable {s : S ⟶ Spec (.of R)} {f : X ⟶ S}

/-- Restricting the chosen twist to the inverse image of a base open is the same as pulling the
absolute projective twist back along the composite restricted projective map. -/
noncomputable def chosenTwistRestrictCompositeIso
    (h : IsRelativeProjectiveFactorization s f) (U : S.Opens) (d : ℤ) :
    (h.chosenTwist d).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback
        ((f ⁻¹ᵁ U).ι ≫ h.chosenProjectiveMap)).obj
          (MvPolynomial.coordinateHyperplaneTwist
            (R := R) (0 : Fin (h.chosenDimension + 1)) d) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app
      (h.chosenTwist d) ≪≫
    (Scheme.Modules.pullbackComp
      (f ⁻¹ᵁ U).ι h.chosenProjectiveMap).app
        (MvPolynomial.coordinateHyperplaneTwist
          (R := R) (0 : Fin (h.chosenDimension + 1)) d)

end AlgebraicGeometry.IsRelativeProjectiveFactorization
