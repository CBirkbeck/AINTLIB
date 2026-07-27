/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafMonomialBasisAway

/-!
# Compatibility of finite pole stages with the section complement

The finite-stage linear equivalence from abstract pole sections to model
Weierstrass monomials agrees with evaluation on every open disjoint from the
marked section.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace ModularCurves

noncomputable section

private noncomputable def modelPoleFiltrationEval
    {R T : Type*} [CommRing R] [CommRing T]
    (W : WeierstrassCurve R) (n : ℕ)
    (A : R →+* T) (φ : W.toAffine.CoordinateRing →+* T)
    (hφ : φ.comp (algebraMap R W.toAffine.CoordinateRing) = A) :
    poleOrderFiltration W n →ₛₗ[A] T where
  toFun q := φ q.1
  map_add' p q := map_add φ p.1 q.1
  map_smul' a q := by
    simpa only [Submodule.coe_smul, Algebra.smul_def, map_mul,
      smul_eq_mul, RingHom.comp_apply, Algebra.algebraMap_self_apply] using
      congrArg (fun t : T => t * φ q.1) (DFunLike.congr_fun hφ a)

private noncomputable def sectionPoleSheafPowerAwayCoefficient
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥) (n : ℕ) :
    let A : Γ(S, (⊤ : S.Opens)) →+* Γ(C, V) :=
      (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
    Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz n) →ₛₗ[A] Γ(C, V) := by
  let A : Γ(S, (⊤ : S.Opens)) →+* Γ(C, V) :=
    (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
  let e :=
    Scheme.Modules.overTrivializationOfRestrictIso
      (sectionPoleSheafPower π z hz n) V
      (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
        z hz V hV n)
  exact
    { toFun := fun q =>
        overTrivializationCoefficient
          (sectionPoleSheafPower π z hz n) V e
          ((Scheme.Modules.baseSectionsIsoRestrictScalarsTop π
            (sectionPoleSheafPower π z hz n)).hom q)
      map_add' := fun p q => by
        rw [map_add]
        exact overTrivializationCoefficient_add
          (sectionPoleSheafPower π z hz n) V e _ _
      map_smul' := fun a q => by
        simpa only [A, e, smul_eq_mul, RingHom.comp_apply] using
          overTrivializationCoefficient_baseSections_smul
            π (sectionPoleSheafPower π z hz n) V e a q }

/-- Evaluating the model image of a finite-stage pole section agrees with its
canonical regular-function coefficient away from the marked section. -/
theorem sectionPoleSheafPower_poleOrderFiltrationLinearEquiv_away
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
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (φ : W.toAffine.CoordinateRing →+* Γ(C, V))
    (hφ : φ.comp
      (algebraMap Γ(S, (⊤ : S.Opens)) W.toAffine.CoordinateRing) =
        (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom)
    (hφx : φ (coordX W) =
      overTrivializationCoefficient
        (sectionPoleSheafPower π z hz 2) V
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz 2) V
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz V hV 2)) x)
    (hφy : φ (coordY W) =
      overTrivializationCoefficient
        (sectionPoleSheafPower π z hz 3) V
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz 3) V
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz V hV 3)) y)
    (n : ℕ)
    (q : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1))) :
    φ ((sectionPoleSheafPower_poleOrderFiltrationLinearEquiv
        hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy W n q :
      poleOrderFiltration W (n + 1)) :
        W.toAffine.CoordinateRing) =
      overTrivializationCoefficient
        (sectionPoleSheafPower π z hz (n + 1)) V
        (Scheme.Modules.overTrivializationOfRestrictIso
          (sectionPoleSheafPower π z hz (n + 1)) V
          (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
            z hz V hV (n + 1))) q := by
  let A : Γ(S, (⊤ : S.Opens)) →+* Γ(C, V) :=
    (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
  let b := sectionPoleSheafPower_monomialBasis
    hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy n
  let e := sectionPoleSheafPower_poleOrderFiltrationLinearEquiv
    hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy W n
  let lhs := sectionPoleSheafPowerAwayCoefficient z hz V hV (n + 1)
  let eval := modelPoleFiltrationEval W (n + 1) A φ hφ
  let rhs : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1)) →ₛₗ[A] Γ(C, V) :=
    eval.comp e.toLinearMap
  have hmaps : lhs = rhs := by
    apply b.ext
    intro i
    simp only [lhs, rhs, eval, e, LinearMap.comp_apply]
    dsimp only [sectionPoleSheafPowerAwayCoefficient,
      modelPoleFiltrationEval]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    change
      overTrivializationCoefficient
          (sectionPoleSheafPower π z hz (n + 1)) V _
          (b i) =
        φ (((sectionPoleSheafPower_poleOrderFiltrationLinearEquiv
          hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy W n)
            (b i) : poleOrderFiltration W (n + 1)) :
              W.toAffine.CoordinateRing)
    rw [sectionPoleSheafPower_poleOrderFiltrationLinearEquiv_apply_basis]
    dsimp only [b]
    refine (overTrivializationCoefficient_sectionPoleSheafPower_monomialBasis
      hsm z hz U hU r hspan hnzd hHOne bOne hbOne x hx y hy V hV n i).trans ?_
    rw [poleOrderMonomialSequence_eq_poleMonomialSequence,
      map_poleMonomialSequence, hφx, hφy]
  exact (DFunLike.congr_fun hmaps q).symm

end

end ModularCurves
