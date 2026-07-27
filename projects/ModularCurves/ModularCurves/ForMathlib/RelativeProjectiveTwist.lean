/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.RelativeProjectiveFactorizationChoice
import ModularCurves.EllipticCurve.ProjectiveSpaceTwist
import ModularCurves.Picard.InvertibleSheafLocallyFree

/-!
# Twists from a relative projective factorization

The chosen projective map of a relative projective factorization pulls the concrete integer
twists on polynomial projective space back to invertible modules on the source.
-/

open CategoryTheory

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.IsRelativeProjectiveFactorization

variable {R : Type u} [CommRing R] {X S : Scheme.{u}}
variable {s : S ⟶ Spec (.of R)} {f : X ⟶ S}

/-- The integer projective twist pulled back along the chosen projective map. -/
noncomputable def chosenTwist
    (h : IsRelativeProjectiveFactorization s f) (d : ℤ) : X.Modules :=
  (Scheme.Modules.pullback h.chosenProjectiveMap).obj
    (MvPolynomial.coordinateHyperplaneTwist
      (R := R) (0 : Fin (h.chosenDimension + 1)) d)

/-- Every chosen relative projective twist is invertible. -/
lemma chosenTwist_isInvertible
    (h : IsRelativeProjectiveFactorization s f) (d : ℤ) :
    Scheme.Modules.IsInvertible (h.chosenTwist d) :=
  (MvPolynomial.coordinateHyperplaneTwist_isInvertible
    (R := R) (0 : Fin (h.chosenDimension + 1)) d).pullback
      h.chosenProjectiveMap

/-- Every chosen relative projective twist is quasicoherent. -/
lemma chosenTwist_isQuasicoherent
    (h : IsRelativeProjectiveFactorization s f) (d : ℤ) :
    (h.chosenTwist d).IsQuasicoherent :=
  (h.chosenTwist_isInvertible d).isQuasicoherent

/-- Every chosen relative projective twist is finitely presented. -/
lemma chosenTwist_isFinitePresentation
    (h : IsRelativeProjectiveFactorization s f) (d : ℤ) :
    (h.chosenTwist d).IsFinitePresentation :=
  (h.chosenTwist_isInvertible d).isFinitePresentation

end AlgebraicGeometry.IsRelativeProjectiveFactorization
