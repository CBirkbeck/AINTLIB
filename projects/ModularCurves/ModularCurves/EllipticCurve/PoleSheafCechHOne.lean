import ModularCurves.EllipticCurve.PoleSheafQuasicoherent
import ModularCurves.ForMathlib.AcyclicAffineCechComparison

/-!
# Cech comparison for pole sheaves

Apply the affine-cover Cech comparison to the pole line bundles of a smooth
proper pointed relative curve.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace ModularCurves

/-- On an affine open cover, the native Cech complex of `O(n[0])` computes its
genuine degree-one sheaf cohomology. -/
noncomputable def sectionPoleSheafPower_cechHomologyOneIso
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π]
    (hsm : SmoothOfRelativeDimension 1 π) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (n : ℕ) {ι : Type u} (U : ι → E.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    ((CategoryTheory.cechComplexFunctor U).obj
      (sectionPoleSheafPower π z hz n).sheaf.obj).homology 1 ≅
        AddCommGrpCat.of (CategoryTheory.Sheaf.H
          (sectionPoleSheafPower π z hz n).sheaf 1) := by
  letI : (sectionPoleSheafPower π z hz n).IsQuasicoherent :=
    sectionPoleSheafPower_isQuasicoherent hsm z hz n
  exact Scheme.Modules.cechHomologyOneIso_of_affine_openCover
    (sectionPoleSheafPower π z hz n) U hU hUaff

/-- A smooth proper pointed curve over an affine base admits a finite affine
cover whose native Cech complex computes `H¹(O(n[0]))`. -/
theorem exists_sectionPoleSheafPower_finiteAffineCechComparison
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (n : ℕ) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → E.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        Nonempty (((CategoryTheory.cechComplexFunctor U).obj
          (sectionPoleSheafPower π z hz n).sheaf.obj).homology 1 ≅
            AddCommGrpCat.of (CategoryTheory.Sheaf.H
              (sectionPoleSheafPower π z hz n).sheaf 1)) := by
  obtain ⟨ι, hι, U, hU, hUaff, _⟩ :=
    π.exists_finite_affine_openCover_of_isProper
  exact ⟨ι, hι, U, hU, hUaff,
    ⟨sectionPoleSheafPower_cechHomologyOneIso hsm z hz n U hU hUaff⟩⟩

end ModularCurves
