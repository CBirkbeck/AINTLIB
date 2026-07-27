import ModularCurves.EllipticCurve.PoleSheafAwayChartHom
import ModularCurves.EllipticCurve.WeierstrassModelCoordinateTransition

/-!
# Factoring the section-away comparison through the projective chart

The unit-coordinate projective comparison factors through the corresponding
affine chart.  For the canonical pole coordinates on the complement of the
marked section, the middle morphism of affine schemes is an isomorphism.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open WeierstrassCurve.Projective

universe u

namespace ModularCurves

noncomputable section

/-- The affine-chart homomorphism attached to a homogeneous triple over an
explicit base ring homomorphism. -/
noncomputable def chartAwayHomOfTripleOfRingHom
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens)))
    (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P)
    (i : Fin 3) (hi : IsUnit (P i)) :
    chartAway W i →+* Γ(X, (⊤ : X.Opens)) := by
  letI : Algebra R Γ(X, (⊤ : X.Opens)) := f.toAlgebra
  have hP' :
      (W.map (algebraMap R Γ(X, (⊤ : X.Opens)))).toProjective.Equation P := by
    rw [RingHom.algebraMap_toAlgebra]
    exact hP
  exact (chartAwayHomOfTriple W i P
    (↑hi.unit⁻¹) hi.mul_val_inv hP').toRingHom

/-- The unit-coordinate projective morphism factors through the affine chart
for an explicitly supplied base ring homomorphism. -/
theorem projModelFromOfGlobalSections_eq_chart_of_ringHom
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens)))
    (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P)
    (i : Fin 3) (hi : IsUnit (P i)) :
    projModelFromOfGlobalSections W f P hP i hi =
      X.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          (chartAwayHomOfTripleOfRingHom W f P hP i hi)) ≫
        chartι W i := by
  letI : Algebra R Γ(X, (⊤ : X.Opens)) := f.toAlgebra
  have hP' :
      (W.map (algebraMap R Γ(X, (⊤ : X.Opens)))).toProjective.Equation P := by
    rw [RingHom.algebraMap_toAlgebra]
    exact hP
  simpa only [chartAwayHomOfTripleOfRingHom,
    RingHom.algebraMap_toAlgebra] using
    projModelFromOfGlobalSections_eq_chart W P hP' i hi

/-- For the canonical pole coordinates on the exact section complement, the
affine-scheme morphism induced by the projective `Z`-chart homomorphism is an
isomorphism.  This does not assert that the complement's affinization map is
an isomorphism. -/
theorem sectionAway_chartSpecMap_isIso
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hHOne : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (bOne : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz 1)))
    (hbOne : bOne 0 = sectionPoleSheafPowerOneSection π z hz)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens))) :
    let V := sectionAway z hz
    let A : Γ(S, (⊤ : S.Opens)) →+* Γ(C, V) :=
      (C.presheaf.map
        (homOfLE (le_top : V ≤ (⊤ : C.Opens))).op).hom.comp
          π.appTop.hom
    let X := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz 2) V
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz 2) V
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V (preimage_sectionAway z hz) 2)) x
    let Y := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz 3) V
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz 3) V
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V (preimage_sectionAway z hz) 3)) y
    let τ : Γ(C, V) →+*
        Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
      V.topIso.inv.hom
    let f := τ.comp A
    ∀ hxy : (W.map A).toAffine.Equation X Y,
      let hxy' := affineEquation_map_comp W A τ X Y hxy
      letI : Algebra Γ(S, (⊤ : S.Opens))
          Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
        f.toAlgebra
      let hxy'' : (W.map (algebraMap Γ(S, (⊤ : S.Opens))
          Γ(V.toScheme, (⊤ : V.toScheme.Opens)))).toAffine.Equation
          (τ X) (τ Y) := by
        rw [RingHom.algebraMap_toAlgebra]
        exact hxy'
      let P : Fin 3 → Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
        ![τ X, τ Y, 1]
      let hP : (W.map (algebraMap Γ(S, (⊤ : S.Opens))
          Γ(V.toScheme, (⊤ : V.toScheme.Opens)))).toProjective.Equation P := by
        rw [WeierstrassCurve.Projective.equation_some]
        exact hxy''
      IsIso (Spec.map (CommRingCat.ofHom
        (chartAwayHomOfTriple W 2 P 1 (by simp [P]) hP).toRingHom)) := by
  dsimp only
  intro hxy
  letI : Algebra Γ(S, (⊤ : S.Opens))
      Γ((sectionAway z hz).toScheme,
        (⊤ : (sectionAway z hz).toScheme.Opens)) :=
    ((sectionAway z hz).topIso.inv.hom.comp
      ((C.presheaf.map
        (homOfLE (le_top :
          sectionAway z hz ≤ (⊤ : C.Opens))).op).hom.comp
            π.appTop.hom)).toAlgebra
  let g :=
    (chartAwayHomOfTriple W 2
      ![(sectionAway z hz).topIso.inv.hom
          (overTrivializationCoefficient
            (sectionPoleSheafPower π z hz 2) (sectionAway z hz)
            (Scheme.Modules.overTrivializationOfRestrictIso
              (sectionPoleSheafPower π z hz 2) (sectionAway z hz)
              (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
                z hz (sectionAway z hz) (preimage_sectionAway z hz) 2)) x),
        (sectionAway z hz).topIso.inv.hom
          (overTrivializationCoefficient
            (sectionPoleSheafPower π z hz 3) (sectionAway z hz)
            (Scheme.Modules.overTrivializationOfRestrictIso
              (sectionPoleSheafPower π z hz 3) (sectionAway z hz)
              (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
                z hz (sectionAway z hz) (preimage_sectionAway z hz) 3)) y),
        1]
      1 (by simp)
      (by
        rw [WeierstrassCurve.Projective.equation_some]
        rw [RingHom.algebraMap_toAlgebra]
        exact affineEquation_map_comp W
          ((C.presheaf.map
            (homOfLE (le_top :
              sectionAway z hz ≤ (⊤ : C.Opens))).op).hom.comp
                π.appTop.hom)
          (sectionAway z hz).topIso.inv.hom _ _ hxy)).toRingHom
  have hg : Function.Bijective g := by
    exact sectionAway_chartAwayHomOfTriple_z_bijective
      hsm z hz U hU r hspan hnzd hHOne bOne hbOne x hx y hy W hxy
  let e := RingEquiv.ofBijective g hg
  letI : IsIso (CommRingCat.ofHom g) :=
    (RingEquiv.toCommRingCatIso e).isIso_hom
  infer_instance

end

end ModularCurves
