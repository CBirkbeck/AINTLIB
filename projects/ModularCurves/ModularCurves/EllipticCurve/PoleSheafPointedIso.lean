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

/-- Compatible isomorphisms of the total and base schemes identify the pullback
of the target section's ideal module with the source section's ideal module. -/
noncomputable def sectionIdealModulePointedIsoOfBaseIso
    {C C' S S' : Scheme.{u}} {π : C ⟶ S} {π' : C' ⟶ S'}
    [IsSeparated π] [IsSeparated π']
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (z' : S' ⟶ C') (hz' : z' ≫ π' = 𝟙 S')
    (eC : C ≅ C') (eS : S ≅ S')
    (hez : eS.hom ≫ z' = z ≫ eC.hom) :
    (Scheme.Modules.pullback eC.hom).obj (sectionIdealModule π' z' hz') ≅
      sectionIdealModule π z hz := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  letI : IsClosedImmersion z' := isClosedImmersion_section z' hz'
  letI : QuasiCompact z' := inferInstance
  have hker : z.ker = z'.ker.comap eC.hom := by
    calc
      z.ker = (z.ker.comap eC.inv).comap eC.hom := by
        rw [← Scheme.IdealSheafData.comap_comp, eC.hom_inv_id,
          Scheme.IdealSheafData.comap_id]
      _ = (z ≫ eC.hom).ker.comap eC.hom := by
        rw [Scheme.Hom.ker_comp_iso]
      _ = (eS.hom ≫ z').ker.comap eC.hom := by rw [hez]
      _ = z'.ker.comap eC.hom := by rw [Scheme.Hom.ker_iso_comp]
  exact ((Scheme.Modules.restrictFunctorIsoPullback eC.hom).app
      (sectionIdealModule π' z' hz')).symm ≪≫
    restrictIdealModuleIso z' eC.hom z hker

/-- A pointed isomorphism identifies the pullback of the target section's ideal module
with the source section's ideal module. -/
noncomputable def sectionIdealModulePointedIso
    {C C' S : Scheme.{u}} {π : C ⟶ S} {π' : C' ⟶ S}
    [IsSeparated π] [IsSeparated π']
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (z' : S ⟶ C') (hz' : z' ≫ π' = 𝟙 S)
    (e : C ≅ C') (hez : z ≫ e.hom = z') :
    (Scheme.Modules.pullback e.hom).obj (sectionIdealModule π' z' hz') ≅
      sectionIdealModule π z hz :=
  sectionIdealModulePointedIsoOfBaseIso
    z hz z' hz' e (Iso.refl S) (by simpa using hez.symm)

/-- Compatible isomorphisms of the total and base schemes identify the pullback
of the target pole sheaf with the source pole sheaf. -/
noncomputable def sectionPoleSheafPointedIsoOfBaseIso
    {C C' S S' : Scheme.{u}} {π : C ⟶ S} {π' : C' ⟶ S'}
    [IsSeparated π] [IsSeparated π']
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (z' : S' ⟶ C') (hz' : z' ≫ π' = 𝟙 S')
    (hsm' : SmoothOfRelativeDimension 1 π')
    (eC : C ≅ C') (eS : S ≅ S')
    (hez : eS.hom ≫ z' = z ≫ eC.hom) :
    (Scheme.Modules.pullback eC.hom).obj (sectionPoleSheaf π' z' hz') ≅
      sectionPoleSheaf π z hz := by
  exact Scheme.Modules.dualPullbackIsoOfIsInvertible eC.hom
      (sectionIdealModule π' z' hz')
      (sectionIdealModule_isInvertible hsm' z' hz') ≪≫
    (Scheme.Modules.dualIsoObj
      (sectionIdealModulePointedIsoOfBaseIso
        z hz z' hz' eC eS hez)).symm

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
      sectionPoleSheaf π z hz :=
  sectionPoleSheafPointedIsoOfBaseIso
    z hz z' hz' hsm' e (Iso.refl S) (by simpa using hez.symm)

/-- Compatible isomorphisms of the total and base schemes identify the pullback
of every tensor power of the target pole sheaf with the corresponding source
pole-sheaf power. -/
noncomputable def sectionPoleSheafPowerPointedIsoOfBaseIso
    {C C' S S' : Scheme.{u}} {π : C ⟶ S} {π' : C' ⟶ S'}
    [IsSeparated π] [IsSeparated π']
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (z' : S' ⟶ C') (hz' : z' ≫ π' = 𝟙 S')
    (hsm' : SmoothOfRelativeDimension 1 π')
    (eC : C ≅ C') (eS : S ≅ S')
    (hez : eS.hom ≫ z' = z ≫ eC.hom) :
    ∀ n : ℕ,
      (Scheme.Modules.pullback eC.hom).obj
          (sectionPoleSheafPower π' z' hz' n) ≅
        sectionPoleSheafPower π z hz n
  | 0 => by
      letI : MonoidalCategory C'.Modules := Scheme.Modules.monoidalCategory C'
      letI : MonoidalCategory C.Modules := Scheme.Modules.monoidalCategory C
      letI : (Scheme.Modules.pullback eC.hom).Monoidal :=
        Scheme.Modules.pullbackMonoidal eC.hom
      exact (Functor.Monoidal.εIso (Scheme.Modules.pullback eC.hom)).symm
  | n + 1 => by
      letI : MonoidalCategory C'.Modules := Scheme.Modules.monoidalCategory C'
      letI : MonoidalCategory C.Modules := Scheme.Modules.monoidalCategory C
      letI : (Scheme.Modules.pullback eC.hom).Monoidal :=
        Scheme.Modules.pullbackMonoidal eC.hom
      exact (Functor.Monoidal.μIso (Scheme.Modules.pullback eC.hom)
          (sectionPoleSheafPower π' z' hz' n)
          (sectionPoleSheaf π' z' hz')).symm ≪≫
        (sectionPoleSheafPowerPointedIsoOfBaseIso
            z hz z' hz' hsm' eC eS hez n ⊗ᵢ
          sectionPoleSheafPointedIsoOfBaseIso
            z hz z' hz' hsm' eC eS hez)

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
  | n =>
      sectionPoleSheafPowerPointedIsoOfBaseIso
        z hz z' hz' hsm' e (Iso.refl S) (by simpa using hez.symm) n

end ModularCurves
