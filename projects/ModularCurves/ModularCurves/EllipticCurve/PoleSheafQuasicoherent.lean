import ModularCurves.EllipticCurve.PoleSheaf
import ModularCurves.Picard.InvertibleSheafLocallyFree

/-!
# Quasicoherence of pole sheaves

The pole line bundle of the zero section and all of its nonnegative tensor powers are
quasicoherent. This is the sheaf-theoretic input required by affine vanishing and by
cohomology-and-base-change arguments.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

/-- The simple-pole sheaf of a section of a smooth separated relative curve is
quasicoherent. -/
theorem sectionPoleSheaf_isQuasicoherent
    {C S : Scheme.{u}} {π : C ⟶ S} (hsm : SmoothOfRelativeDimension 1 π)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) :
    (sectionPoleSheaf π z hz).IsQuasicoherent :=
  (sectionPoleSheaf_isInvertible hsm z hz).isQuasicoherent

/-- Every nonnegative tensor power of the pole sheaf is quasicoherent. -/
theorem sectionPoleSheafPower_isQuasicoherent
    {C S : Scheme.{u}} {π : C ⟶ S} (hsm : SmoothOfRelativeDimension 1 π)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    (sectionPoleSheafPower π z hz n).IsQuasicoherent :=
  (sectionPoleSheafPower_isInvertible hsm z hz n).isQuasicoherent

/-- The simple-pole sheaf of a section of a smooth separated relative curve is finitely
presented. -/
theorem sectionPoleSheaf_isFinitePresentation
    {C S : Scheme.{u}} {π : C ⟶ S} (hsm : SmoothOfRelativeDimension 1 π)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) :
    (sectionPoleSheaf π z hz).IsFinitePresentation :=
  (sectionPoleSheaf_isInvertible hsm z hz).isFinitePresentation

/-- Every nonnegative tensor power of the pole sheaf is finitely presented. -/
theorem sectionPoleSheafPower_isFinitePresentation
    {C S : Scheme.{u}} {π : C ⟶ S} (hsm : SmoothOfRelativeDimension 1 π)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    (sectionPoleSheafPower π z hz n).IsFinitePresentation :=
  (sectionPoleSheafPower_isInvertible hsm z hz n).isFinitePresentation

/-- The quotient between two consecutive pole sheaves. -/
noncomputable def sectionPoleSheafSuccCoker
    {C S : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) : C.Modules :=
  cokernel (sectionPoleSheafSuccHom π z hz n)

/-- A successive pole-filtration quotient is a finitely presented scheme module. -/
theorem sectionPoleSheafSuccCoker_isFinitePresentation
    {C S : Scheme.{u}} {π : C ⟶ S} (hsm : SmoothOfRelativeDimension 1 π)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    (sectionPoleSheafSuccCoker π z hz n).IsFinitePresentation :=
  (sectionPoleSheafPower_isInvertible hsm z hz n).cokernel_isFinitePresentation
    (sectionPoleSheafPower_isInvertible hsm z hz (n + 1))
    (sectionPoleSheafSuccHom π z hz n)

end ModularCurves
