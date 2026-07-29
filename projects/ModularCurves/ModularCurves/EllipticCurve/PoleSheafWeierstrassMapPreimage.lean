/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafAwaySections
import ModularCurves.EllipticCurve.PoleSheafModel
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapGlue

/-!
# The affine-chart preimage of the pole-sheaf comparison

The projective `Z`-chart pulls back under the pole-sheaf comparison to the
complement of the marked section. This identifies the source open on which
the comparison can be studied as a morphism of affine schemes.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace ModularCurves

open HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A positive power of a Cartier generator cuts out the pullback of the
complement of the marked section on its affine chart. -/
theorem basicOpen_topIso_inv_pow_generator_eq_preimage_sectionAway
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1))
    (hspan : z.ker.ideal U = Ideal.span {r})
    (n : ℕ) (hn : 0 < n) :
    U.1.toScheme.basicOpen (U.1.topIso.inv (r ^ n)) =
      U.1.ι ⁻¹ᵁ sectionAway z hz := by
  apply U.1.ι.image_injective
  change U.1.ι ''ᵁ U.1.toScheme.basicOpen (U.1.topIso.inv (r ^ n)) =
    U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ sectionAway z hz)
  rw [U.1.ι_image_basicOpen_topIso_inv,
    Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι,
    C.basicOpen_pow r hn,
    affine_inf_sectionAway_eq_basicOpen z hz U r hspan]

/-- On a Cartier chart, the coprime-coordinate comparison pulls the
projective `Z`-chart back to the complement of the marked section. -/
theorem
    projModelFromOfGlobalSectionsOfIsCoprime_preimage_zChart_eq_sectionAway
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1))
    (hspan : z.ker.ideal U = Ideal.span {r})
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (f : R →+* Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)))
    (P : Fin 3 → Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)))
    (hP : (W.map f).toProjective.Equation P)
    (hcop : IsCoprime (P 1) (P 2))
    (hP2 : P 2 = U.1.topIso.inv (r ^ 3)) :
    projModelFromOfGlobalSectionsOfIsCoprime W f P hP 1 2 hcop ⁻¹ᵁ
        (projModelZChart W : (projModel W).Opens) =
      U.1.ι ⁻¹ᵁ sectionAway z hz := by
  change
    projModelFromOfGlobalSectionsOfIsCoprime W f P hP 1 2 hcop ⁻¹ᵁ
        Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) =
      U.1.ι ⁻¹ᵁ sectionAway z hz
  rw [projModelFromOfGlobalSectionsOfIsCoprime_preimage_basicOpen,
    hP2]
  exact
    basicOpen_topIso_inv_pow_generator_eq_preimage_sectionAway
      z hz U r hspan 3 (by omega)

private theorem preimage_eq_of_two_open_restrict
    {X Y : Scheme.{u}} (U V : X.Opens) (D : Y.Opens)
    (hUV : U ⊔ V = ⊤) (F : X ⟶ Y)
    (fU : U.toScheme ⟶ Y) (fV : V.toScheme ⟶ Y)
    (hFU : U.ι ≫ F = fU) (hFV : V.ι ≫ F = fV)
    (hpreU : fU ⁻¹ᵁ D = U.ι ⁻¹ᵁ V)
    (hpreV : fV ⁻¹ᵁ D = ⊤) :
    F ⁻¹ᵁ D = V := by
  let E := F ⁻¹ᵁ D
  have hEU : U.ι ⁻¹ᵁ E = U.ι ⁻¹ᵁ V := by
    rw [show U.ι ⁻¹ᵁ E = (U.ι ≫ F) ⁻¹ᵁ D by
      rw [Scheme.Hom.comp_preimage]]
    rw [hFU, hpreU]
  have hEV : V.ι ⁻¹ᵁ E = ⊤ := by
    rw [show V.ι ⁻¹ᵁ E = (V.ι ≫ F) ⁻¹ᵁ D by
      rw [Scheme.Hom.comp_preimage]]
    rw [hFV, hpreV]
  have hUE : U ⊓ E = U ⊓ V := by
    have h := congrArg (U.ι ''ᵁ ·) hEU
    simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι] using h
  have hVE : V ⊓ E = V := by
    have h := congrArg (V.ι ''ᵁ ·) hEV
    simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, Scheme.Opens.ι_image_top] using h
  calc
    E = ⊤ ⊓ E := (top_inf_eq E).symm
    _ = (U ⊔ V) ⊓ E := congrArg (· ⊓ E) hUV.symm
    _ = U ⊓ E ⊔ V ⊓ E := inf_sup_right U V E
    _ = U ⊓ V ⊔ V := by rw [hUE, hVE]
    _ = V := sup_eq_right.mpr inf_le_right

/-- A global comparison with the literal Cartier and away restrictions pulls
the projective `Z`-chart back to the complement of the marked section. -/
theorem projModelMap_preimage_zChart_eq_sectionAway_of_restrict
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1))
    (hspan : z.ker.ideal U = Ideal.span {r})
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (fU : R →+* Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)))
    (PU : Fin 3 → Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)))
    (hPU : (W.map fU).toProjective.Equation PU)
    (hcop : IsCoprime (PU 1) (PU 2))
    (hPU2 : PU 2 = U.1.topIso.inv (r ^ 3))
    (fV : R →+*
      Γ((sectionAway z hz).toScheme,
        (⊤ : (sectionAway z hz).toScheme.Opens)))
    (PV : Fin 3 →
      Γ((sectionAway z hz).toScheme,
        (⊤ : (sectionAway z hz).toScheme.Opens)))
    (hPV : (W.map fV).toProjective.Equation PV)
    (hZ : IsUnit (PV 2))
    (F : C ⟶ projModel W)
    (hFU : U.1.ι ≫ F =
      projModelFromOfGlobalSectionsOfIsCoprime
        W fU PU hPU 1 2 hcop)
    (hFV : (sectionAway z hz).ι ≫ F =
      projModelFromOfGlobalSections W fV PV hPV 2 hZ) :
    F ⁻¹ᵁ (projModelZChart W : (projModel W).Opens) =
      sectionAway z hz := by
  apply preimage_eq_of_two_open_restrict
    U.1 (sectionAway z hz)
    (projModelZChart W : (projModel W).Opens)
    (sup_sectionAway_eq_top_of_preimage_eq_top z hz U.1 hU)
    F
    (projModelFromOfGlobalSectionsOfIsCoprime
      W fU PU hPU 1 2 hcop)
    (projModelFromOfGlobalSections W fV PV hPV 2 hZ)
    hFU hFV
  · exact
      projModelFromOfGlobalSectionsOfIsCoprime_preimage_zChart_eq_sectionAway
        z hz U r hspan W fU PU hPU hcop hPU2
  · change
      projModelFromOfGlobalSections W fV PV hPV 2 hZ ⁻¹ᵁ
          Proj.basicOpen (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) =
        ⊤
    rw [projModelFromOfGlobalSections_preimage_basicOpen]
    exact Scheme.basicOpen_of_isUnit _ hZ

end ModularCurves
