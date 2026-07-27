import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import ModularCurves.EllipticCurve.PoleSheafAwayModel
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapProper

/-!
# Finiteness of the punctured pole-sheaf comparison

The exact restriction of a pole-sheaf comparison to the marked-section
complement and the standard affine Weierstrass chart is finite.
-/

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

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

end

end ModularCurves
