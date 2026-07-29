import Mathlib.AlgebraicGeometry.Morphisms.Proper
import ModularCurves.EllipticCurve.PoleSheaf
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCech
import ModularCurves.Picard.InvertibleSheafBaseCechFlat

/-!
# Flat base-linear Cech models for pole sheaves

The pole line bundles on a smooth proper pointed curve have finite affine
trivializing covers whose base-linear Cech complexes are termwise flat.
-/

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace ModularCurves

/-- Over an affine base, every pole line bundle on a smooth proper pointed
curve has a finite affine trivializing cover whose base-linear Cech complex
is termwise flat. -/
theorem exists_sectionPoleSheafPower_finiteAffineBaseCech_flat
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π) (z : S ⟶ E)
    (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → E.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        (∀ i, Nonempty
          ((sectionPoleSheafPower π z hz n).restrict (U i).ι ≅
            Scheme.Modules.unitObj (U i).toScheme)) ∧
          ∀ q, Module.Flat Γ(S, (⊤ : S.Opens))
            ((Scheme.Modules.baseCechComplex π
              (sectionPoleSheafPower π z hz n) U).X q) := by
  letI : SmoothOfRelativeDimension 1 π := hsm
  letI : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  letI : CompactSpace E := (quasiCompact_iff_compactSpace π).mp inferInstance
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  exact (sectionPoleSheafPower_isInvertible hsm z hz n).exists_finiteAffineBaseCech_flat π

/-- Over an affine base, a pole line bundle admits a finite linearly ordered
affine trivializing cover whose ordered base-linear Cech complex is termwise
flat. -/
theorem exists_sectionPoleSheafPower_finiteAffineOrderedBaseCech_flat
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π) (z : S ⟶ E)
    (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : LinearOrder ι)
      (U : ι → E.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        (∀ i, Nonempty
          ((sectionPoleSheafPower π z hz n).restrict (U i).ι ≅
            Scheme.Modules.unitObj (U i).toScheme)) ∧
          ∀ q, Module.Flat Γ(S, (⊤ : S.Opens))
            ((Scheme.Modules.orderedBaseCechComplex π
              (sectionPoleSheafPower π z hz n) U).X q) := by
  letI : SmoothOfRelativeDimension 1 π := hsm
  letI : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  obtain ⟨ι, hι, U, hU, hUaff, htriv, _⟩ :=
    exists_sectionPoleSheafPower_finiteAffineBaseCech_flat hsm z hz n
  letI : Finite ι := hι
  letI : Fintype ι := Fintype.ofFinite ι
  letI : LinearOrder ι :=
    LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  refine ⟨ι, inferInstance, inferInstance, U, hU, hUaff, htriv, ?_⟩
  intro q
  exact Scheme.Modules.orderedBaseCechObject_flat_of_trivializingCover
    π (sectionPoleSheafPower π z hz n) U hUaff htriv q

end ModularCurves
