/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.PoleSheafWeierstrassChartIdeal
import ModularCurves.EllipticCurve.PoleSheafAwaySections
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

/-- A global morphism whose affine-chart restriction is a normalized
coprime-coordinate comparison pulls the model zero ideal back to the
restricted Cartier generator on the corresponding basic open. -/
theorem projModelMap_comap_zeroIdeal_affineBasicOpen_mul_of_restrict
    {C : Scheme.{u}} (U : C.affineOpens)
    (a b r : Γ(C, U.1))
    (W : WeierstrassCurve R)
    (f : R →+* Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)))
    (P : Fin 3 → Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)))
    (hP : (W.map f).toProjective.Equation P)
    (hcop : IsCoprime (P 1) (P 2))
    (hP0 : P 0 = U.1.topIso.inv.hom (a * r))
    (hP1 : P 1 = U.1.topIso.inv.hom b)
    (hP2 : P 2 = U.1.topIso.inv.hom (r ^ 3))
    (F : C ⟶ projModel W)
    (hFU : U.1.ι ≫ F =
      projModelFromOfGlobalSectionsOfIsCoprime
        W f P hP 1 2 hcop) :
    ((projModelZero W).ker.comap F).ideal
        (C.affineBasicOpen (U := U) (a * b)) =
      Ideal.span {
        C.presheaf.map
          (homOfLE (C.affineBasicOpen_le (a * b))).op r} := by
  let B := C.affineBasicOpen (U := U) (a * b)
  let hBU : B.1 ≤ U.1 := C.affineBasicOpen_le (a * b)
  let g : B.1.toScheme ⟶ U.1.toScheme := C.homOfLE hBU
  let res : Γ(C, U.1) →+* Γ(C, B.1) :=
    (C.presheaf.map (homOfLE hBU).op).hom
  have hab : IsUnit (res (a * b)) :=
    AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen
      C.toRingedSpace (a * b)
  have hab' : IsUnit (res a * res b) := by
    simpa only [map_mul] using hab
  have ha : IsUnit (res a) := (IsUnit.mul_iff.mp hab').1
  have hb : IsUnit (res b) := (IsUnit.mul_iff.mp hab').2
  have happ (q : Γ(C, U.1)) :
      g.appTop.hom (U.1.topIso.inv.hom q) =
        B.1.topIso.inv.hom (res q) := by
    exact ConcreteCategory.congr_hom
      (Scheme.Modules.topIso_inv_naturality hBU) q
  have hga : IsUnit (g.appTop.hom (U.1.topIso.inv.hom a)) := by
    rw [happ]
    exact ha.map B.1.topIso.inv.hom
  have hgb : IsUnit ((g.appTop.hom ∘ P) 1) := by
    rw [Function.comp_apply, hP1, happ]
    exact hb.map B.1.topIso.inv.hom
  have htop :
      ((projModelZero W).ker.comap
        (g ≫ projModelFromOfGlobalSectionsOfIsCoprime
          W f P hP 1 2 hcop)).ideal
          ⟨⊤, isAffineOpen_top B.1.toScheme⟩ =
        Ideal.span {g.appTop.hom (U.1.topIso.inv.hom r)} := by
    apply
      projModelFromOfGlobalSectionsOfIsCoprime_comp_comap_zeroIdeal_chartY
        g W f P hP 1 2 hcop hgb
        (g.appTop.hom (U.1.topIso.inv.hom r))
        (g.appTop.hom (U.1.topIso.inv.hom a))
    · simp only [Function.comp_apply, hP0, map_mul]
    · simp only [Function.comp_apply, hP2, map_pow]
    · exact hga
  have hgf :
      g ≫ projModelFromOfGlobalSectionsOfIsCoprime
          W f P hP 1 2 hcop =
        B.1.ι ≫ F := by
    rw [← hFU]
    rw [← Category.assoc, Scheme.homOfLE_ι]
  let J : C.IdealSheafData := (projModelZero W).ker.comap F
  have hmapped :
      (J.ideal B).map B.1.topIso.inv.hom =
        (Ideal.span {res r}).map B.1.topIso.inv.hom := by
    rw [← J.ideal_comap_affineOpen_top B]
    rw [Ideal.map_span, Set.image_singleton]
    rw [← happ]
    change (((projModelZero W).ker.comap F).comap B.1.ι).ideal
        ⟨⊤, isAffineOpen_top B.1.toScheme⟩ =
      Ideal.span {g.appTop.hom (U.1.topIso.inv.hom r)}
    rw [← Scheme.IdealSheafData.comap_comp]
    rw [← hgf]
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

/-- The model zero ideal pulls back to the unit ideal on every affine source
open mapping into the standard `Z`-chart. -/
theorem projModelMap_comap_zeroIdeal_eq_top_of_le_preimage_zChart
    {C : Scheme.{u}} (W : WeierstrassCurve R)
    (F : C ⟶ projModel W) (V : C.affineOpens)
    (hV : V.1 ≤ F ⁻¹ᵁ (projModelZChart W).1) :
    ((projModelZero W).ker.comap F).ideal V = ⊤ := by
  have hI :
      (projModelZero W).ker.ideal (projModelZChart W) =
        Ideal.span {1} :=
    projModelZero_ker_ideal_chartZ W
  rw [ideal_comap_affineOpens_span
    (projModelZero W).ker F V (projModelZChart W) hV 1 hI]
  rw [Ideal.span_singleton_eq_top]
  simp only [affinePullbackSection, affineOpenTopSection,
    affineOpenAmbientSection, map_one]
  exact isUnit_one

/-- The ideal of a marked section is the unit ideal on every affine open
contained in the complement of that section. -/
theorem section_ker_ideal_eq_top_of_le_sectionAway
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (V : C.affineOpens) (hV : V.1 ≤ sectionAway z hz) :
    z.ker.ideal V = ⊤ := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  let I : V.1.toScheme.IdealSheafData := z.ker.comap V.1.ι
  have hsupp : I.support = ⊥ := by
    change (z.ker.comap V.1.ι).support = ⊥
    rw [Scheme.IdealSheafData.support_comap]
    ext x
    change (x.1 : C) ∈ z.ker.support ↔ False
    have hzmem := congrArg
      (fun Z : Set C => (x.1 : C) ∈ Z) z.support_ker
    have hclosure := congrArg
      (fun Z : Set C => (x.1 : C) ∈ Z)
      z.isClosedEmbedding.isClosed_range.closure_eq
    constructor
    · intro hx
      have hxrange : (x.1 : C) ∈ Set.range z :=
        hclosure.mp (hzmem.mp hx)
      have hxV : (x.1 : C) ∈ sectionAway z hz := hV x.2
      exact (hxV hxrange).elim
    · intro hx
      exact hx.elim
  have hI : I = ⊤ := I.support_eq_bot_iff.mp hsupp
  have hmapped :
      (z.ker.ideal V).map V.1.topIso.inv.hom =
        (⊤ : Ideal Γ(V.1.toScheme, (⊤ : V.1.toScheme.Opens))) := by
    rw [← z.ker.ideal_comap_affineOpen_top V]
    change I.ideal ⟨⊤, isAffineOpen_top _⟩ = ⊤
    rw [hI]
    rfl
  have hback := congrArg (Ideal.map V.1.topIso.hom.hom) hmapped
  have hleft :
      ((z.ker.ideal V).map V.1.topIso.inv.hom).map
          V.1.topIso.hom.hom = z.ker.ideal V := by
    exact Ideal.map_of_equiv
      V.1.topIso.commRingCatIsoToRingEquiv.symm
  have hright :
      (⊤ : Ideal Γ(V.1.toScheme, (⊤ : V.1.toScheme.Opens))).map
          V.1.topIso.hom.hom = ⊤ := by
    exact Ideal.map_top V.1.topIso.hom.hom
  rw [hleft, hright] at hback
  exact hback

end ModularCurves
