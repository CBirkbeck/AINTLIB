import ModularCurves.EllipticCurve.PoleSheaf
import ModularCurves.Picard.InvertibleSheafLocallyFree
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Quasicoherence of pole sheaves

The pole line bundle of the zero section and all of its nonnegative tensor powers are
quasicoherent. This is the sheaf-theoretic input required by affine vanishing and by
cohomology-and-base-change arguments.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace SheafOfModules

/-- For a closed immersion, the structure-sheaf map to the pushed-forward structure
sheaf is an epimorphism of sheaves of modules. -/
theorem unitToPushforwardObjUnit_epi_of_isClosedImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    Epi (unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  let F := toSheaf Y.ringCatSheaf
  let q := unitToPushforwardObjUnit f.toRingCatSheafHom
  have hq : Epi (F.map q) := by
    letI : CategoryTheory.Sheaf.IsLocallySurjective (F.map q) := by
      change CategoryTheory.Presheaf.IsLocallySurjective
        (Opens.grothendieckTopology Y) (F.map q).hom
      constructor
      intro U t
      change ∀ y ∈ U, ∃ (V : TopologicalSpace.Opens Y) (i : V ⟶ U),
        CategoryTheory.Presheaf.imageSieve (F.map q).hom t i ∧ y ∈ V
      intro y hy
      obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
      let i : V ⟶ U := homOfLE hVU
      obtain ⟨s, hs⟩ := f.app_surjective V hV
        (((Scheme.Modules.pushforward f).obj (Scheme.Modules.unitObj X)).val.map
          i.op t)
      refine ⟨V, i, ⟨s, ?_⟩, hyV⟩
      change
        (unitToPushforwardObjUnit f.toRingCatSheafHom).val.app (op V) s =
          (((Scheme.Modules.pushforward f).obj (Scheme.Modules.unitObj X)).val.map
            i.op t)
      exact
        (unitToPushforwardObjUnit_val_app_apply f.toRingCatSheafHom s).trans hs
    infer_instance
  letI := hq
  constructor
  intro Z g h hgh
  apply F.map_injective
  apply (cancel_epi (F.map q)).mp
  rw [← F.map_comp, ← F.map_comp, hgh]

end SheafOfModules

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

/-- The quotient of the structure sheaf by the ideal module of a closed immersion is
canonically the pushed-forward structure sheaf of its source. -/
noncomputable def idealModuleCokerIsoPushforwardUnit
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    cokernel (idealModuleToUnit f) ≅
      (Scheme.Modules.pushforward f).obj (Scheme.Modules.unitObj X) := by
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  letI : Epi q :=
    SheafOfModules.unitToPushforwardObjUnit_epi_of_isClosedImmersion f
  change cokernel (kernel.ι q) ≅ _
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (kernel.ι q))
    (Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι q) (kernel.condition q)) (kernelIsKernel q))

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
