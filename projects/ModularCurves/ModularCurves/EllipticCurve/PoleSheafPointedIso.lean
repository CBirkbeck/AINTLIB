import ModularCurves.EllipticCurve.PoleSheaf
import ModularCurves.LevelStructure.IsoTransport

/-!
# Pole sheaves under pointed isomorphisms

This file transports the ideal sheaf of a section, its dual pole sheaf, and every tensor
power of that pole sheaf along an isomorphism carrying one marked section to another.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory SheafOfModules
  TopologicalSpace

universe u

namespace ModularCurves

/-- A pointed isomorphism identifies the pullback of the target section's ideal module
with the source section's ideal module. -/
noncomputable def sectionIdealModulePointedIso
    {C C' S : Scheme.{u}} {π : C ⟶ S} {π' : C' ⟶ S}
    [IsSeparated π] [IsSeparated π']
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (z' : S ⟶ C') (hz' : z' ≫ π' = 𝟙 S)
    (e : C ≅ C') (hez : z ≫ e.hom = z') :
    (Scheme.Modules.pullback e.hom).obj (sectionIdealModule π' z' hz') ≅
      sectionIdealModule π z hz := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  letI : IsClosedImmersion z' := isClosedImmersion_section z' hz'
  letI : QuasiCompact z' := inferInstance
  have hker : z.ker = z'.ker.comap e.hom := by
    calc
      z.ker = (z.ker.comap e.inv).comap e.hom := by
        rw [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id,
          Scheme.IdealSheafData.comap_id]
      _ = (z ≫ e.hom).ker.comap e.hom := by
        rw [Scheme.Hom.ker_comp_iso]
      _ = z'.ker.comap e.hom := by rw [hez]
  exact ((Scheme.Modules.restrictFunctorIsoPullback e.hom).app
      (sectionIdealModule π' z' hz')).symm ≪≫
    restrictIdealModuleIso z' e.hom z hker

/-- A pointed isomorphism identifies the pullback of the target pole sheaf with the
source pole sheaf. -/
noncomputable def sectionPoleSheafPointedIso
    {C C' S : Scheme.{u}} {π : C ⟶ S} {π' : C' ⟶ S}
    [IsSeparated π] [IsSeparated π']
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (z' : S ⟶ C') (hz' : z' ≫ π' = 𝟙 S)
    (hsm' : SmoothOfRelativeDimension 1 π')
    (e : C ≅ C') (hez : z ≫ e.hom = z') :
    (Scheme.Modules.pullback e.hom).obj (sectionPoleSheaf π' z' hz') ≅
      sectionPoleSheaf π z hz := by
  exact Scheme.Modules.dualPullbackIsoOfIsInvertible e.hom
      (sectionIdealModule π' z' hz')
      (sectionIdealModule_isInvertible hsm' z' hz') ≪≫
    (Scheme.Modules.dualIsoObj
      (sectionIdealModulePointedIso z hz z' hz' e hez)).symm

/-- A pointed isomorphism identifies the pullback of every tensor power of the target
pole sheaf with the corresponding tensor power of the source pole sheaf. -/
noncomputable def sectionPoleSheafPowerPointedIso
    {C C' S : Scheme.{u}} {π : C ⟶ S} {π' : C' ⟶ S}
    [IsSeparated π] [IsSeparated π']
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (z' : S ⟶ C') (hz' : z' ≫ π' = 𝟙 S)
    (hsm' : SmoothOfRelativeDimension 1 π')
    (e : C ≅ C') (hez : z ≫ e.hom = z') :
    ∀ n : ℕ,
      (Scheme.Modules.pullback e.hom).obj (sectionPoleSheafPower π' z' hz' n) ≅
        sectionPoleSheafPower π z hz n
  | 0 => by
      letI : MonoidalCategory C'.Modules := Scheme.Modules.monoidalCategory C'
      letI : MonoidalCategory C.Modules := Scheme.Modules.monoidalCategory C
      letI : (Scheme.Modules.pullback e.hom).Monoidal :=
        Scheme.Modules.pullbackMonoidal e.hom
      exact (Functor.Monoidal.εIso (Scheme.Modules.pullback e.hom)).symm
  | n + 1 => by
      letI : MonoidalCategory C'.Modules := Scheme.Modules.monoidalCategory C'
      letI : MonoidalCategory C.Modules := Scheme.Modules.monoidalCategory C
      letI : (Scheme.Modules.pullback e.hom).Monoidal :=
        Scheme.Modules.pullbackMonoidal e.hom
      exact (Functor.Monoidal.μIso (Scheme.Modules.pullback e.hom)
          (sectionPoleSheafPower π' z' hz' n) (sectionPoleSheaf π' z' hz')).symm ≪≫
        (sectionPoleSheafPowerPointedIso z hz z' hz' hsm' e hez n ⊗ᵢ
          sectionPoleSheafPointedIso z hz z' hz' hsm' e hez)

end ModularCurves
