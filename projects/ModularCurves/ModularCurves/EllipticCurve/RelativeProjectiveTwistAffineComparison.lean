/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpacePoleSheafBaseChange
import ModularCurves.ForMathlib.RelativeProjectiveTwistRestriction

/-!
# Relative projective twists over affine base opens

Restriction of a chosen nonnegative relative projective twist over an affine
base open is the pullback of the corresponding absolute projective twist.
-/

open CategoryTheory Limits

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.IsRelativeProjectiveFactorization

variable {k : Type u} [CommRing k] {X S : Scheme.{u}}
variable {s : S ⟶ Spec (.of k)} {f : X ⟶ S}

/-- Over an affine base open, the chosen relative `O(n)` is the pullback of
the absolute coordinate-hyperplane `O(n)` along the chosen affine projective
embedding. -/
noncomputable def chosenTwistRestrictOfNatAffineIso
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    (h.chosenTwist (.ofNat n)).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback
        (h.chosenAffineProjectiveEmbedding U hU)).obj
          (MvPolynomial.coordinateHyperplanePoleSheafPower
            (R := Γ(S, U))
            (0 : Fin (h.chosenDimension + 1)) n) := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  let g := h.chosenAffineProjectiveEmbedding U hU
  let c := MvPolynomial.coefficientMap
    (algebraMap k Γ(S, U)) h.chosenDimension
  let P := MvPolynomial.coordinateHyperplanePoleSheafPower
    (R := k) (0 : Fin (h.chosenDimension + 1)) n
  exact h.chosenTwistRestrictCompositeIso U (.ofNat n) ≪≫
    ((Scheme.Modules.pullbackCongr
      (h.chosenAffineProjectiveEmbedding_coefficientMap U hU)).app P).symm ≪≫
    ((Scheme.Modules.pullbackComp g c).app P).symm ≪≫
    (Scheme.Modules.pullback g).mapIso
      (MvPolynomial.coordinateHyperplanePoleSheafPowerBaseChangeIso
        (algebraMap k Γ(S, U)) h.chosenDimension
        (0 : Fin (h.chosenDimension + 1)) n)

end AlgebraicGeometry.IsRelativeProjectiveFactorization
