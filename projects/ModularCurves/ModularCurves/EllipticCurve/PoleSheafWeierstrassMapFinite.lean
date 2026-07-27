import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import ModularCurves.EllipticCurve.PoleSheafAwayChartFactor
import ModularCurves.EllipticCurve.PoleSheafAwayModel
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapProper

/-!
# Finiteness of the punctured pole-sheaf comparison

The exact restriction of a pole-sheaf comparison to the marked-section
complement and the standard affine Weierstrass chart is finite.
-/

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits
open HomogeneousIdeal
open WeierstrassCurve.Projective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

noncomputable section

/-- The restriction of a proper fibrewise-elliptic comparison to the exact
marked-section complement and standard Weierstrass chart is finite. -/
theorem projModelMap_sectionAway_isFinite
    {C S : Scheme.{u}} {π : C ⟶ S} [IsAffine S] [IsProper π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (F : C ⟶ projModel W)
    (hF : F ≫ projModelπ W = π ≫ S.toSpecΓ)
    (hpre : F ⁻¹ᵁ (projModelZChart W : (projModel W).Opens) =
      sectionAway z hz) :
    IsFinite
      (F.resLE (projModelZChart W : (projModel W).Opens)
        (sectionAway z hz) (le_of_eq hpre.symm)) := by
  let G :=
    F.resLE (projModelZChart W : (projModel W).Opens)
      (sectionAway z hz) (le_of_eq hpre.symm)
  let q : (projModelZChart W).1.toScheme ⟶ S :=
    (projModelZChart W).1.ι ≫ projModelπ W ≫ inv S.toSpecΓ
  haveI : IsIso S.toSpecΓ := IsAffine.affine
  haveI hFproper : IsProper F :=
    projModelMap_isProper_of_isAffine W F hF
  haveI hGproper : IsProper G := by
    dsimp only [G]
    exact resLE_isProper_of_preimage_eq F
      (projModelZChart W : (projModel W).Opens) (sectionAway z hz) hpre
  have hqAffine : IsAffineHom q := by
    exact @isAffineHom_of_isAffine _ _ q (projModelZChart W).2 inferInstance
  haveI hqSeparated : IsSeparated q :=
    @AlgebraicGeometry.IsSeparated.of_isAffineHom _ _ q hqAffine
  have hGq : G ≫ q = (sectionAway z hz).ι ≫ π := by
    dsimp only [G, q]
    simp only [← Category.assoc]
    rw [F.resLE_comp_ι]
    rw [Category.assoc (sectionAway z hz).ι F (projModelπ W), hF]
    simp
  haveI hGquasiFinite : LocallyQuasiFinite G :=
    locallyQuasiFinite_of_isProper_of_comp_fiber_isAffine G q fun s => by
      rw [hGq]
      exact h.sectionAway_comp_fiber_isAffine s
  change IsFinite G
  exact IsFinite.of_isProper_of_locallyQuasiFinite G

/-- An exact punctured comparison is an isomorphism once its affine chart
homomorphism is an isomorphism. -/
theorem projModelMap_sectionAway_isIso_of_restrict
    {C S : Scheme.{u}} {π : C ⟶ S} [IsAffine S] [IsProper π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (F : C ⟶ projModel W)
    (hF : F ≫ projModelπ W = π ≫ S.toSpecΓ)
    (hpre : F ⁻¹ᵁ (projModelZChart W : (projModel W).Opens) =
      sectionAway z hz)
    (fV : Γ(S, (⊤ : S.Opens)) →+*
      Γ((sectionAway z hz).toScheme,
        (⊤ : (sectionAway z hz).toScheme.Opens)))
    (PV : Fin 3 →
      Γ((sectionAway z hz).toScheme,
        (⊤ : (sectionAway z hz).toScheme.Opens)))
    (hPV : (W.map fV).toProjective.Equation PV)
    (hZ : IsUnit (PV 2))
    (hFV : (sectionAway z hz).ι ≫ F =
      projModelFromOfGlobalSections W fV PV hPV 2 hZ)
    (hchart : IsIso (Spec.map (CommRingCat.ofHom
      (chartAwayHomOfTripleOfRingHom W fV PV hPV 2 hZ)))) :
    IsIso
      (F.resLE (projModelZChart W : (projModel W).Opens)
        (sectionAway z hz) (le_of_eq hpre.symm)) := by
  let G :=
    F.resLE (projModelZChart W : (projModel W).Opens)
      (sectionAway z hz) (le_of_eq hpre.symm)
  haveI hGfinite : IsFinite G :=
    projModelMap_sectionAway_isFinite z hz h W F hF hpre
  haveI hVaffine : IsAffine (sectionAway z hz).toScheme :=
    @isAffine_of_isAffineHom _ _
      G hGfinite.toIsAffineHom (projModelZChart W).2
  haveI hToSpec : IsIso (sectionAway z hz).toScheme.toSpecΓ :=
    IsAffine.affine
  haveI hChartSpec : IsIso (Spec.map (CommRingCat.ofHom
      (chartAwayHomOfTripleOfRingHom W fV PV hPV 2 hZ))) :=
    hchart
  let eZ :=
    Proj.basicOpenIsoSpec (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI hEZ : IsIso eZ.inv := by
    dsimp only [eZ]
    infer_instance
  have heZ :
      eZ.inv ≫ (projModelZChart W).1.ι = chartι W 2 := by
    rfl
  have hLocalFactor :
      projModelFromOfGlobalSections W fV PV hPV 2 hZ =
        (sectionAway z hz).toScheme.toSpecΓ ≫
          Spec.map (CommRingCat.ofHom
            (chartAwayHomOfTripleOfRingHom W fV PV hPV 2 hZ)) ≫
          chartι W 2 :=
    projModelFromOfGlobalSections_eq_chart_of_ringHom
      W fV PV hPV 2 hZ
  have hG :
      G =
        (sectionAway z hz).toScheme.toSpecΓ ≫
          Spec.map (CommRingCat.ofHom
            (chartAwayHomOfTripleOfRingHom W fV PV hPV 2 hZ)) ≫
          eZ.inv := by
    rw [← cancel_mono (projModelZChart W).1.ι]
    calc
      G ≫ (projModelZChart W).1.ι =
          (sectionAway z hz).ι ≫ F := by
        dsimp only [G]
        exact F.resLE_comp_ι (le_of_eq hpre.symm)
      _ = projModelFromOfGlobalSections W fV PV hPV 2 hZ := hFV
      _ = (sectionAway z hz).toScheme.toSpecΓ ≫
          Spec.map (CommRingCat.ofHom
            (chartAwayHomOfTripleOfRingHom W fV PV hPV 2 hZ)) ≫
          chartι W 2 := hLocalFactor
      _ = ((sectionAway z hz).toScheme.toSpecΓ ≫
          Spec.map (CommRingCat.ofHom
            (chartAwayHomOfTripleOfRingHom W fV PV hPV 2 hZ)) ≫
          eZ.inv) ≫ (projModelZChart W).1.ι := by
        simp only [Category.assoc, heZ]
  haveI hChartFactor : IsIso
      (Spec.map (CommRingCat.ofHom
          (chartAwayHomOfTripleOfRingHom W fV PV hPV 2 hZ)) ≫
        eZ.inv) := by
    exact IsIso.comp_isIso' hChartSpec hEZ
  haveI hFactor : IsIso
      ((sectionAway z hz).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          (chartAwayHomOfTripleOfRingHom W fV PV hPV 2 hZ)) ≫
        eZ.inv) := by
    exact IsIso.comp_isIso' hToSpec hChartFactor
  change IsIso G
  rw [hG]
  exact hFactor

end

end ModularCurves
