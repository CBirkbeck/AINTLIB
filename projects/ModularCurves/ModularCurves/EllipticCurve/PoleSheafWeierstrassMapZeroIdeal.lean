/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.PoleSheafWeierstrassChartIdeal
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapGlue
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

/-- On the basic open where both normalized coefficients are units, the
coprime-coordinate comparison pulls the model zero ideal back to the
restricted normalized parameter. -/
theorem
    projModelFromOfGlobalSectionsOfIsCoprime_comap_zeroIdeal_affineBasicOpen_mul
    {X : Scheme.{u}} [IsAffine X] (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens)))
    (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P)
    (i j : Fin 3) (hij : IsCoprime (P i) (P j))
    (a b r : Γ(X, (⊤ : X.Opens)))
    (hP0 : P 0 = a * r) (hP1 : P 1 = b) (hP2 : P 2 = r ^ 3) :
    let T : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
    let B := X.affineBasicOpen (U := T) (a * b)
    ((projModelZero W).ker.comap
      (projModelFromOfGlobalSectionsOfIsCoprime
        W f P hP i j hij)).ideal B =
      Ideal.span {
        X.presheaf.map
          (homOfLE (X.affineBasicOpen_le (V := T) (a * b))).op r} := by
  dsimp only
  let T : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let B := X.affineBasicOpen (U := T) (a * b)
  let F := projModelFromOfGlobalSectionsOfIsCoprime
    W f P hP i j hij
  let g : B.1.toScheme ⟶ X := B.1.ι
  let res : Γ(X, (⊤ : X.Opens)) →+* Γ(X, B.1) :=
    (X.presheaf.map
      (homOfLE (X.affineBasicOpen_le (V := T) (a * b))).op).hom
  have hab : IsUnit (res (a * b)) := by
    exact AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen
      X.toRingedSpace (a * b)
  have hab' : IsUnit (res a * res b) := by
    simpa only [map_mul] using hab
  have ha : IsUnit (res a) := (IsUnit.mul_iff.mp hab').1
  have hb : IsUnit (res b) := (IsUnit.mul_iff.mp hab').2
  have happ (q : Γ(X, (⊤ : X.Opens))) :
      g.appTop.hom q = B.1.topIso.inv.hom (res q) := by
    rw [opens_ι_appTop]
    rfl
  have hga : IsUnit (g.appTop.hom a) := by
    rw [happ]
    exact ha.map B.1.topIso.inv.hom
  have hgb : IsUnit ((g.appTop.hom ∘ P) 1) := by
    rw [Function.comp_apply, hP1, happ]
    exact hb.map B.1.topIso.inv.hom
  have htop :
      ((projModelZero W).ker.comap (g ≫ F)).ideal
          ⟨⊤, isAffineOpen_top B.1.toScheme⟩ =
        Ideal.span {g.appTop.hom r} := by
    apply
      projModelFromOfGlobalSectionsOfIsCoprime_comp_comap_zeroIdeal_chartY
        g W f P hP i j hij hgb (g.appTop.hom r) (g.appTop.hom a)
    · rw [Function.comp_apply, hP0, map_mul]
    · rw [Function.comp_apply, hP2, map_pow]
    · exact hga
  let J : X.IdealSheafData := (projModelZero W).ker.comap F
  have hmapped :
      (J.ideal B).map B.1.topIso.inv.hom =
        (Ideal.span {res r}).map B.1.topIso.inv.hom := by
    rw [← J.ideal_comap_affineOpen_top B]
    rw [Ideal.map_span, Set.image_singleton]
    rw [← happ]
    change (((projModelZero W).ker.comap F).comap g).ideal
        ⟨⊤, isAffineOpen_top B.1.toScheme⟩ =
      Ideal.span {g.appTop.hom r}
    rw [← Scheme.IdealSheafData.comap_comp]
    exact htop
  have hback := congrArg (Ideal.map B.1.topIso.hom.hom) hmapped
  have hleft :
      ((J.ideal B).map B.1.topIso.inv.hom).map
          B.1.topIso.hom.hom = J.ideal B := by
    exact Ideal.map_of_equiv
      B.1.topIso.commRingCatIsoToRingEquiv.symm
  have hright :
      ((Ideal.span {res r}).map B.1.topIso.inv.hom).map
          B.1.topIso.hom.hom = Ideal.span {res r} := by
    exact Ideal.map_of_equiv
      B.1.topIso.commRingCatIsoToRingEquiv.symm
  rw [hleft, hright] at hback
  exact hback

end ModularCurves
