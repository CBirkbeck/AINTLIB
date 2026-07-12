import ModularCurves.EllipticCurve.PoleSheafCechHOne
import ModularCurves.ForMathlib.SchemeModuleBaseCechHomology

/-!
# Base-linear Cech comparison for pole sheaves

Retain the affine-base module structure on the Cech model computing degree-one
cohomology of the pole line bundles on a smooth proper pointed relative curve.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace ModularCurves

/-- On an affine open cover, forgetting the base-module structure on degree-one
Cech homology of `O(n[0])` recovers its genuine sheaf cohomology. -/
noncomputable def sectionPoleSheafPower_baseCechHomologyOneIso
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π]
    (hsm : SmoothOfRelativeDimension 1 π) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (n : ℕ) {ι : Type u} (U : ι → E.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    (Scheme.Modules.baseModuleForget S).obj
        ((Scheme.Modules.baseCechComplex π
          (sectionPoleSheafPower π z hz n) U).homology 1) ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H
        (sectionPoleSheafPower π z hz n).sheaf 1) := by
  letI : (sectionPoleSheafPower π z hz n).IsQuasicoherent :=
    sectionPoleSheafPower_isQuasicoherent hsm z hz n
  exact Scheme.Modules.baseCechHomologyOneIso_of_affine_openCover
    π (sectionPoleSheafPower π z hz n) U hU hUaff

/-- A smooth proper pointed curve over an affine base admits a finite affine
cover whose base-linear Cech homology computes `H¹(O(n[0]))` after forgetting
the base-module structure. -/
theorem exists_sectionPoleSheafPower_finiteAffineBaseCechComparison
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (n : ℕ) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → E.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        Nonempty ((Scheme.Modules.baseModuleForget S).obj
            ((Scheme.Modules.baseCechComplex π
              (sectionPoleSheafPower π z hz n) U).homology 1) ≅
          AddCommGrpCat.of (CategoryTheory.Sheaf.H
            (sectionPoleSheafPower π z hz n).sheaf 1)) := by
  obtain ⟨ι, hι, U, hU, hUaff, _⟩ :=
    π.exists_finite_affine_openCover_of_isProper
  exact ⟨ι, hι, U, hU, hUaff,
    ⟨sectionPoleSheafPower_baseCechHomologyOneIso
      hsm z hz n U hU hUaff⟩⟩

end ModularCurves
