/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafCartierTrivialization
import ModularCurves.EllipticCurve.PoleSheafWeierstrassRelation
import ModularCurves.EllipticCurve.WeierstrassModelCoordinates

/-!
# The Weierstrass equation in a Cartier chart

The global pole-sheaf relation is expressed in the local frames induced by a
Cartier generator of the marked section. This produces the homogeneous
Weierstrass equation used to construct the local map to the projective cubic.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

noncomputable section

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A base scalar in a local module frame is the restriction of its image
under the structure morphism. -/
theorem localTrivializationCoefficient_baseSections_smul
    {C S : Scheme.{u}} (π : C ⟶ S) (M : C.Modules)
    (U : C.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (a : Γ(S, (⊤ : S.Opens)))
    (x : Scheme.Modules.baseSections π M) :
    localTrivializationCoefficient M U e
        ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom (a • x)) =
      C.presheaf.map (homOfLE le_top).op (π.appTop.hom a) *
        localTrivializationCoefficient M U e
          ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom x) := by
  rw [map_smul]
  exact localTrivializationCoefficient_smul M U e (π.appTop.hom a)
    ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom x)

/-- The basic open of the Cartier-chart coefficient of a normalized successor
pole section contains the entire marked section. -/
theorem sectionPoleSheafPower_succ_preimage_basicOpen_coefficient_eq_top
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1)))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd n x = 1) :
    let hr : r ∈ z.ker.ideal U :=
      hspan ▸ Ideal.subset_span (Set.mem_singleton r)
    let X := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz (n + 1)) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd (n + 1)) x
    z ⁻¹ᵁ C.basicOpen X = ⊤ := by
  dsimp only
  have hr : r ∈ z.ker.ideal U := by
    rw [hspan]
    exact Ideal.subset_span (Set.mem_singleton r)
  let X := localTrivializationCoefficient
    (sectionPoleSheafPower π z hz (n + 1)) U
    (sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd (n + 1)) x
  have hcoordinate :=
    sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator_hom_baseSectionsMap
      hsm z hz U hU r hspan hnzd n x
  have hcoordinate' :
      sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
          hsm z hz U hU r hspan hnzd n x =
        S.presheaf.map (eqToHom hU.symm).op (z.app U.1 X) := by
    rw [sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator_apply]
    simpa only [X, sectionPoleSheafPowerTrivializationOfCartierGenerator,
      sectionPoleSheafTrivializationOfCartierGenerator] using hcoordinate
  have hrestrict :
      S.presheaf.map (eqToHom hU.symm).op (z.app U.1 X) = 1 := by
    rw [← hcoordinate']
    exact hx
  rw [Scheme.preimage_basicOpen]
  rw [← Scheme.basicOpen_res_eq (X := S) (f := z.app U.1 X) (eqToHom hU.symm).op]
  rw [hrestrict, Scheme.basicOpen_one]

/-- The Cartier-chart coefficient of a normalized successor pole section is
coprime to the generator of the marked section. -/
theorem sectionPoleSheafPower_succ_isCoprime_coefficient_generator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1)))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd n x = 1) :
    let hr : r ∈ z.ker.ideal U :=
      hspan ▸ Ideal.subset_span (Set.mem_singleton r)
    let X := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz (n + 1)) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd (n + 1)) x
    IsCoprime X r := by
  dsimp only
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  have hr : r ∈ z.ker.ideal U := by
    rw [hspan]
    exact Ideal.subset_span (Set.mem_singleton r)
  let X := localTrivializationCoefficient
    (sectionPoleSheafPower π z hz (n + 1)) U
    (sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd (n + 1)) x
  have hcoordinate :=
    sectionPoleSheafSuccCoker_baseSectionsIsoOfCartierGenerator_hom_baseSectionsMap
      hsm z hz U hU r hspan hnzd n x
  have hcoordinate' :
      sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
          hsm z hz U hU r hspan hnzd n x =
        S.presheaf.map (eqToHom hU.symm).op (z.app U.1 X) := by
    rw [sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator_apply]
    simpa only [X, sectionPoleSheafPowerTrivializationOfCartierGenerator,
      sectionPoleSheafTrivializationOfCartierGenerator] using hcoordinate
  have hrestrict :
      S.presheaf.map (eqToHom hU.symm).op (z.app U.1 X) = 1 := by
    rw [← hcoordinate']
    exact hx
  have hX : z.app U.1 X = 1 := by
    apply (ConcreteCategory.bijective_of_isIso
      (S.presheaf.map (eqToHom hU.symm).op)).1
    simpa using hrestrict
  have hker : X - 1 ∈ z.ker.ideal U := by
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker, map_sub, hX, map_one, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ hker)
  refine ⟨1, -c, ?_⟩
  rw [one_mul, neg_mul, hc]
  ring

/-- A normalized successor coefficient remains coprime to every power of the
Cartier generator. -/
theorem sectionPoleSheafPower_succ_isCoprime_coefficient_generator_pow
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n m : ℕ)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1)))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd n x = 1) :
    let hr : r ∈ z.ker.ideal U :=
      hspan ▸ Ideal.subset_span (Set.mem_singleton r)
    let X := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz (n + 1)) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd (n + 1)) x
    IsCoprime X (r ^ m) := by
  exact (sectionPoleSheafPower_succ_isCoprime_coefficient_generator
    hsm z hz U hU r hspan hnzd n x hx).pow_right

private theorem localTrivializationCoefficient_baseSections_add
    {C S : Scheme.{u}} (π : C ⟶ S) (M : C.Modules)
    (U : C.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (x y : Scheme.Modules.baseSections π M) :
    localTrivializationCoefficient M U e
        ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom (x + y)) =
      localTrivializationCoefficient M U e
          ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom x) +
        localTrivializationCoefficient M U e
          ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom y) := by
  rw [map_add]
  exact localTrivializationCoefficient_add M U e _ _

private theorem localTrivializationCoefficient_baseSectionsIso_hom
    {C S : Scheme.{u}} (π : C ⟶ S) (M : C.Modules)
    (U : C.affineOpens)
    (e : M.restrict U.1.ι ≅ Scheme.Modules.unitObj U.1.toScheme)
    (x : Scheme.Modules.baseSections π M) :
    localTrivializationCoefficient M U e
        ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π M).hom x) =
      localTrivializationCoefficient M U e x := by
  rfl

/-- On a Cartier-generator chart, the global pole relation is the homogeneous
generalized Weierstrass equation in the local coefficients of `x` and `y`. -/
theorem sectionPoleSheafPower_six_local_homogeneous_weierstrass_relation_of_CartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hH1 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (hH2 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 2).sheaf 1))
    (hH3 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 3).sheaf 1))
    (hH4 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 4).sheaf 1))
    (hH5 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 5).sheaf 1))
    (b1 : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 1)))
    (hb1 : b1 0 = sectionPoleSheafPowerOneSection π z hz)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1) :
    ∃ a₁ a₂ a₃ a₄ a₆ : Γ(S, (⊤ : S.Opens)),
      let hr : r ∈ z.ker.ideal U :=
        hspan ▸ Ideal.subset_span (Set.mem_singleton r)
      let X := localTrivializationCoefficient
        (sectionPoleSheafPower π z hz 2) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd 2) x
      let Y := localTrivializationCoefficient
        (sectionPoleSheafPower π z hz 3) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd 3) y
      let A : Γ(S, (⊤ : S.Opens)) → Γ(C, U.1) := fun a ↦
        C.presheaf.map (homOfLE le_top).op (π.appTop.hom a)
      Y ^ 2 + A a₁ * X * Y * r + A a₃ * Y * r ^ 3 =
        X ^ 3 + A a₂ * X ^ 2 * r ^ 2 + A a₄ * X * r ^ 4 + A a₆ * r ^ 6 := by
  obtain ⟨a₁, a₂, a₃, a₄, a₆, hrel⟩ :=
    sectionPoleSheafPower_exists_monomial_weierstrass_relation_of_CartierGenerator
      hsm z hz U hU r hspan hnzd hH1 hH2 hH3 hH4 hH5 b1 hb1 x hx y hy
  refine ⟨a₁, a₂, a₃, a₄, a₆, ?_⟩
  dsimp only
  have hr : r ∈ z.ker.ideal U := by
    rw [hspan]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hsucc1 (q : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 1)) :
      localTrivializationCoefficient (sectionPoleSheafPower π z hz 2) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd 2)
          (Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 1) q) =
        localTrivializationCoefficient (sectionPoleSheafPower π z hz 1) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 1) q * r := by
    simpa using
      localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsSucc
        z hz U r hr hspan hnzd 1 q
  have hsucc2 (q : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2)) :
      localTrivializationCoefficient (sectionPoleSheafPower π z hz 3) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd 3)
          (Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 2) q) =
        localTrivializationCoefficient (sectionPoleSheafPower π z hz 2) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 2) q * r := by
    simpa using
      localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsSucc
        z hz U r hr hspan hnzd 2 q
  have hsucc3 (q : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3)) :
      localTrivializationCoefficient (sectionPoleSheafPower π z hz 4) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd 4)
          (Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 3) q) =
        localTrivializationCoefficient (sectionPoleSheafPower π z hz 3) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 3) q * r := by
    simpa using
      localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsSucc
        z hz U r hr hspan hnzd 3 q
  have hsucc4 (q : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 4)) :
      localTrivializationCoefficient (sectionPoleSheafPower π z hz 5) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd 5)
          (Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 4) q) =
        localTrivializationCoefficient (sectionPoleSheafPower π z hz 4) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 4) q * r := by
    simpa using
      localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsSucc
        z hz U r hr hspan hnzd 4 q
  have hsucc5 (q : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 5)) :
      localTrivializationCoefficient (sectionPoleSheafPower π z hz 6) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd 6)
          (Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5) q) =
        localTrivializationCoefficient (sectionPoleSheafPower π z hz 5) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 5) q * r := by
    simpa using
      localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsSucc
        z hz U r hr hspan hnzd 5 q
  have hcoeff := congrArg
    (fun q : Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz 6) ↦
      localTrivializationCoefficient
        (sectionPoleSheafPower π z hz 6) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd 6)
        ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π
          (sectionPoleSheafPower π z hz 6)).hom q)) hrel
  simp only [localTrivializationCoefficient_baseSections_add,
    localTrivializationCoefficient_baseSections_smul] at hcoeff
  simp only [localTrivializationCoefficient_baseSectionsIso_hom] at hcoeff
  let ePole := sectionPoleSheafTrivializationOfCartierGenerator
    z hz U r hr hspan hnzd
  have hyy :=
    localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsMul_tmul
      z hz U ePole 3 3 y y
  have hyy' :
      localTrivializationCoefficient (sectionPoleSheafPower π z hz 6) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd 6)
          (sectionPoleSheafPower_baseSectionsMul z hz 3 3 (y ⊗ₜ y)) =
        localTrivializationCoefficient (sectionPoleSheafPower π z hz 3) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 3) y *
          localTrivializationCoefficient (sectionPoleSheafPower π z hz 3) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 3) y := by
    simpa only [ePole,
      sectionPoleSheafPowerTrivializationOfCartierGenerator] using hyy
  have hxy :=
    localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsMul_tmul
      z hz U ePole 2 3 x y
  have hxy' :
      localTrivializationCoefficient (sectionPoleSheafPower π z hz 5) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd 5)
          (sectionPoleSheafPower_baseSectionsMul z hz 2 3 (x ⊗ₜ y)) =
        localTrivializationCoefficient (sectionPoleSheafPower π z hz 2) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 2) x *
          localTrivializationCoefficient (sectionPoleSheafPower π z hz 3) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 3) y := by
    simpa only [ePole,
      sectionPoleSheafPowerTrivializationOfCartierGenerator] using hxy
  have hxx :=
    localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsMul_tmul
      z hz U ePole 2 2 x x
  have hxx' :
      localTrivializationCoefficient (sectionPoleSheafPower π z hz 4) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd 4)
          (sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x)) =
        localTrivializationCoefficient (sectionPoleSheafPower π z hz 2) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 2) x *
          localTrivializationCoefficient (sectionPoleSheafPower π z hz 2) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 2) x := by
    simpa only [ePole,
      sectionPoleSheafPowerTrivializationOfCartierGenerator] using hxx
  have hxxx :=
    localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsMul_tmul
      z hz U ePole 2 4 x
        (sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x))
  have hxxx' :
      localTrivializationCoefficient (sectionPoleSheafPower π z hz 6) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r hr hspan hnzd 6)
          (sectionPoleSheafPower_baseSectionsMul z hz 2 4
            (x ⊗ₜ sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x))) =
        localTrivializationCoefficient (sectionPoleSheafPower π z hz 2) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 2) x *
          localTrivializationCoefficient (sectionPoleSheafPower π z hz 4) U
            (sectionPoleSheafPowerTrivializationOfCartierGenerator
              z hz U r hr hspan hnzd 4)
            (sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x)) := by
    simpa only [ePole,
      sectionPoleSheafPowerTrivializationOfCartierGenerator] using hxxx
  have hone :=
    localTrivializationCoefficient_sectionPoleSheafPowerOneSection
      z hz U r hr hspan hnzd
  rw [hyy'] at hcoeff
  simp only [hsucc5, hsucc4, hsucc3, hsucc2, hsucc1] at hcoeff
  simp only [hxy', hxx', hxxx', hone] at hcoeff
  ring_nf at hcoeff ⊢
  exact hcoeff

/-- The Cartier-frame pole relation gives homogeneous coordinates on the
corresponding projective Weierstrass cubic. -/
theorem sectionPoleSheafPower_six_local_homogeneous_weierstrass_equation_of_CartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hH1 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (hH2 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 2).sheaf 1))
    (hH3 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 3).sheaf 1))
    (hH4 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 4).sheaf 1))
    (hH5 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 5).sheaf 1))
    (b1 : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 1)))
    (hb1 : b1 0 = sectionPoleSheafPowerOneSection π z hz)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1) :
    ∃ a₁ a₂ a₃ a₄ a₆ : Γ(S, (⊤ : S.Opens)),
      let hr : r ∈ z.ker.ideal U :=
        hspan ▸ Ideal.subset_span (Set.mem_singleton r)
      let X := localTrivializationCoefficient
        (sectionPoleSheafPower π z hz 2) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd 2) x
      let Y := localTrivializationCoefficient
        (sectionPoleSheafPower π z hz 3) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd 3) y
      let A : Γ(S, (⊤ : S.Opens)) →+* Γ(C, U.1) :=
        (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
      let W : WeierstrassCurve Γ(S, (⊤ : S.Opens)) := ⟨a₁, a₂, a₃, a₄, a₆⟩
      (W.map A).toProjective.Equation ![X * r, Y, r ^ 3] := by
  obtain ⟨a₁, a₂, a₃, a₄, a₆, hrel⟩ :=
    sectionPoleSheafPower_six_local_homogeneous_weierstrass_relation_of_CartierGenerator
      hsm z hz U hU r hspan hnzd hH1 hH2 hH3 hH4 hH5 b1 hb1 x hx y hy
  refine ⟨a₁, a₂, a₃, a₄, a₆, ?_⟩
  dsimp only
  apply WeierstrassCurve.Projective.equation_X_mul_r_Y_r_pow_three
  simpa only [WeierstrassCurve.map, RingHom.comp_apply] using hrel

/-- The homogeneous Cartier coordinates define a morphism from the
section-containing `Y`-basic open to the projective Weierstrass model. -/
theorem sectionPoleSheafPower_six_exists_projModelMap_on_Y_basicOpen_of_CartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hH1 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (hH2 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 2).sheaf 1))
    (hH3 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 3).sheaf 1))
    (hH4 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 4).sheaf 1))
    (hH5 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 5).sheaf 1))
    (b1 : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 1)))
    (hb1 : b1 0 = sectionPoleSheafPowerOneSection π z hz)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1) :
    ∃ a₁ a₂ a₃ a₄ a₆ : Γ(S, (⊤ : S.Opens)),
      let hr : r ∈ z.ker.ideal U :=
        hspan ▸ Ideal.subset_span (Set.mem_singleton r)
      let X := localTrivializationCoefficient
        (sectionPoleSheafPower π z hz 2) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd 2) x
      let Y := localTrivializationCoefficient
        (sectionPoleSheafPower π z hz 3) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd 3) y
      let A : Γ(S, (⊤ : S.Opens)) →+* Γ(C, U.1) :=
        (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
      let W : WeierstrassCurve Γ(S, (⊤ : S.Opens)) := ⟨a₁, a₂, a₃, a₄, a₆⟩
      let τ : Γ(C, U.1) →+*
          Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
        U.1.topIso.inv.hom
      let f := τ.comp A
      let P : Fin 3 → Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
        τ ∘ ![X * r, Y, r ^ 3]
      ∃ hP : (W.map f).toProjective.Equation P,
        z ⁻¹ᵁ C.basicOpen Y = ⊤ ∧
        U.1.ι ''ᵁ U.1.toScheme.basicOpen (P 1) = C.basicOpen Y ∧
        projModelFromBasicOpen U.1.toScheme W f P hP 1 ⁻¹ᵁ
            Proj.basicOpen (quotientGrading (projIdeal W))
              ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)) = ⊤ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₆, hPU⟩ :=
    sectionPoleSheafPower_six_local_homogeneous_weierstrass_equation_of_CartierGenerator
      hsm z hz U hU r hspan hnzd hH1 hH2 hH3 hH4 hH5 b1 hb1 x hx y hy
  refine ⟨a₁, a₂, a₃, a₄, a₆, ?_⟩
  dsimp only
  let A : Γ(S, (⊤ : S.Opens)) →+* Γ(C, U.1) :=
    (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
  let W : WeierstrassCurve Γ(S, (⊤ : S.Opens)) := ⟨a₁, a₂, a₃, a₄, a₆⟩
  let τ : Γ(C, U.1) →+* Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
    U.1.topIso.inv.hom
  let f := τ.comp A
  let P : Fin 3 → Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
    τ ∘ ![
      localTrivializationCoefficient
          (sectionPoleSheafPower π z hz 2) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r
              (hspan ▸ Ideal.subset_span (Set.mem_singleton r))
              hspan hnzd 2) x * r,
      localTrivializationCoefficient
        (sectionPoleSheafPower π z hz 3) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r
            (hspan ▸ Ideal.subset_span (Set.mem_singleton r))
            hspan hnzd 3) y,
      r ^ 3]
  have hP : (W.map f).toProjective.Equation P := by
    simpa only [W, f, P, WeierstrassCurve.map_map] using hPU.map τ
  refine ⟨hP, ?_, ?_, ?_⟩
  · exact sectionPoleSheafPower_succ_preimage_basicOpen_coefficient_eq_top
      hsm z hz U hU r hspan hnzd 2 y hy
  · simpa only [P, Function.comp_apply,
      WeierstrassCurve.Projective.fin3_def_ext] using
      U.1.ι_image_basicOpen_topIso_inv
        (localTrivializationCoefficient
          (sectionPoleSheafPower π z hz 3) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r
              (hspan ▸ Ideal.subset_span (Set.mem_singleton r))
              hspan hnzd 3) y)
  · exact projModelFromBasicOpen_preimage_basicOpen
      U.1.toScheme W f P hP 1

/-- The homogeneous Cartier coordinates define one morphism from the entire
Cartier chart to the projective Weierstrass model. -/
theorem sectionPoleSheafPower_six_exists_projModelMap_on_CartierChart_of_CartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hH1 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (hH2 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 2).sheaf 1))
    (hH3 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 3).sheaf 1))
    (hH4 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 4).sheaf 1))
    (hH5 : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 5).sheaf 1))
    (b1 : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 1)))
    (hb1 : b1 0 = sectionPoleSheafPowerOneSection π z hz)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1) :
    ∃ a₁ a₂ a₃ a₄ a₆ : Γ(S, (⊤ : S.Opens)),
      let hr : r ∈ z.ker.ideal U :=
        hspan ▸ Ideal.subset_span (Set.mem_singleton r)
      let X := localTrivializationCoefficient
        (sectionPoleSheafPower π z hz 2) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd 2) x
      let Y := localTrivializationCoefficient
        (sectionPoleSheafPower π z hz 3) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r hr hspan hnzd 3) y
      let A : Γ(S, (⊤ : S.Opens)) →+* Γ(C, U.1) :=
        (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
      let W : WeierstrassCurve Γ(S, (⊤ : S.Opens)) := ⟨a₁, a₂, a₃, a₄, a₆⟩
      let τ : Γ(C, U.1) →+*
          Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
        U.1.topIso.inv.hom
      let f := τ.comp A
      let P : Fin 3 → Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
        τ ∘ ![X * r, Y, r ^ 3]
      ∃ hP : (W.map f).toProjective.Equation P,
        ∃ hcop : IsCoprime (P 1) (P 2),
          projModelFromOfGlobalSectionsOfIsCoprime W f P hP 1 2 hcop ≫
              projModelπ W =
            U.1.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) ∧
          projModelFromOfGlobalSectionsOfIsCoprime W f P hP 1 2 hcop ⁻¹ᵁ
              Proj.basicOpen (quotientGrading (projIdeal W))
                ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 1)) =
            U.1.toScheme.basicOpen (P 1) ∧
          projModelFromOfGlobalSectionsOfIsCoprime W f P hP 1 2 hcop ⁻¹ᵁ
              Proj.basicOpen (quotientGrading (projIdeal W))
                ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) =
            U.1.toScheme.basicOpen (P 2) := by
  obtain ⟨a₁, a₂, a₃, a₄, a₆, hPU⟩ :=
    sectionPoleSheafPower_six_local_homogeneous_weierstrass_equation_of_CartierGenerator
      hsm z hz U hU r hspan hnzd hH1 hH2 hH3 hH4 hH5 b1 hb1 x hx y hy
  refine ⟨a₁, a₂, a₃, a₄, a₆, ?_⟩
  dsimp only
  let A : Γ(S, (⊤ : S.Opens)) →+* Γ(C, U.1) :=
    (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
  let W : WeierstrassCurve Γ(S, (⊤ : S.Opens)) := ⟨a₁, a₂, a₃, a₄, a₆⟩
  let τ : Γ(C, U.1) →+* Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
    U.1.topIso.inv.hom
  let f := τ.comp A
  let P : Fin 3 → Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
    τ ∘ ![
      localTrivializationCoefficient
          (sectionPoleSheafPower π z hz 2) U
          (sectionPoleSheafPowerTrivializationOfCartierGenerator
            z hz U r
              (hspan ▸ Ideal.subset_span (Set.mem_singleton r))
              hspan hnzd 2) x * r,
      localTrivializationCoefficient
        (sectionPoleSheafPower π z hz 3) U
        (sectionPoleSheafPowerTrivializationOfCartierGenerator
          z hz U r
            (hspan ▸ Ideal.subset_span (Set.mem_singleton r))
            hspan hnzd 3) y,
      r ^ 3]
  have hP : (W.map f).toProjective.Equation P := by
    simpa only [W, f, P, WeierstrassCurve.map_map] using hPU.map τ
  have hcopU :=
    sectionPoleSheafPower_succ_isCoprime_coefficient_generator_pow
      hsm z hz U hU r hspan hnzd 2 3 y hy
  have hcop : IsCoprime (P 1) (P 2) := by
    simpa only [P, Function.comp_apply,
      WeierstrassCurve.Projective.fin3_def_ext] using hcopU.map τ
  refine ⟨hP, hcop, ?_, ?_, ?_⟩
  · exact projModelFromOfGlobalSectionsOfIsCoprime_projModelπ
      W f P hP 1 2 hcop
  · exact projModelFromOfGlobalSectionsOfIsCoprime_preimage_basicOpen
      W f P hP 1 2 hcop 1
  · exact projModelFromOfGlobalSectionsOfIsCoprime_preimage_basicOpen
      W f P hP 1 2 hcop 2

end

end ModularCurves
