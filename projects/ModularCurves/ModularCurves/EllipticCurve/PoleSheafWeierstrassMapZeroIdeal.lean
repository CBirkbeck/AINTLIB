/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.PoleSheafWeierstrassChartIdeal
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapOverlap

/-!
# The zero ideal under the pole-sheaf Weierstrass comparison

The normalized `Y`-chart calculation is transported through the
coprime-coordinate constructor and restriction to an affine source.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open WeierstrassCurve.Projective HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ModularCurves

universe u

variable {R : Type u} [CommRing R]

/-- If the `Y`-coordinate is a unit, the coprime-coordinate constructor pulls
the model zero ideal back to the normalized principal ideal. -/
theorem projModelFromOfGlobalSectionsOfIsCoprime_comap_zeroIdeal_chartY
    {X : Scheme.{u}} [IsAffine X] (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens)))
    (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P)
    (i j : Fin 3) (hij : IsCoprime (P i) (P j))
    (hi : IsUnit (P 1))
    (r x : Γ(X, (⊤ : X.Opens)))
    (hP0 : P 0 = x * r) (hP2 : P 2 = r ^ 3)
    (hx : IsUnit x) :
    ((projModelZero W).ker.comap
      (projModelFromOfGlobalSectionsOfIsCoprime
        W f P hP i j hij)).ideal
          ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {r} := by
  letI : Algebra R Γ(X, (⊤ : X.Opens)) := f.toAlgebra
  rw [projModelFromOfGlobalSectionsOfIsCoprime_eq_of_isUnit
    W f P hP i j 1 hij hi]
  exact projModelFromOfGlobalSections_comap_zeroIdeal_chartY
    W P hP hi r x hP0 hP2 hx

/-- The normalized inverse-image ideal computation is stable under pullback
to an affine source. -/
theorem
    projModelFromOfGlobalSectionsOfIsCoprime_comp_comap_zeroIdeal_chartY
    {X Y : Scheme.{u}} [IsAffine Y]
    (g : Y ⟶ X) (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens)))
    (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P)
    (i j : Fin 3) (hij : IsCoprime (P i) (P j))
    (hi : IsUnit ((g.appTop.hom ∘ P) 1))
    (r x : Γ(Y, (⊤ : Y.Opens)))
    (hP0 : (g.appTop.hom ∘ P) 0 = x * r)
    (hP2 : (g.appTop.hom ∘ P) 2 = r ^ 3)
    (hx : IsUnit x) :
    ((projModelZero W).ker.comap
      (g ≫ projModelFromOfGlobalSectionsOfIsCoprime
        W f P hP i j hij)).ideal
          ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {r} := by
  let P' : Fin 3 → Γ(Y, (⊤ : Y.Opens)) := g.appTop.hom ∘ P
  let hP' :
      (W.map (g.appTop.hom.comp f)).toProjective.Equation P' := by
    simpa only [WeierstrassCurve.map_map] using hP.map g.appTop.hom
  rw [projModelFromOfGlobalSectionsOfIsCoprime_naturality
    g W f P hP i j hij]
  exact (by
    letI : Algebra R Γ(Y, (⊤ : Y.Opens)) :=
      (g.appTop.hom.comp f).toAlgebra
    rw [projModelFromOfGlobalSectionsOfIsCoprime_eq_of_isUnit
      W (g.appTop.hom.comp f) P' hP' i j 1
        (hij.map g.appTop.hom) hi]
    exact projModelFromOfGlobalSections_comap_zeroIdeal_chartY
      W P' hP' hi r x hP0 hP2 hx)

end ModularCurves
