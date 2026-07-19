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

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction to an open subscheme commutes with cokernels. -/
noncomputable def restrictCokernelIso
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) :
    cokernel ((restrictFunctor U.ι).map f) ≅
      (restrictFunctor U.ι).obj (cokernel f) := by
  let F := restrictFunctor U.ι
  letI : F.IsLeftAdjoint := (restrictAdjunction U.ι).isLeftAdjoint
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  exact (PreservesCokernel.iso F f).symm

end AlgebraicGeometry.Scheme.Modules

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

local instance (X : Scheme.{u}) :
    ∀ V, IsMulCommutative (X.ringCatSheaf.obj.obj V) :=
  fun V ↦ by
    change IsMulCommutative (X.presheaf.obj V)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

private theorem eq_comp_iso_inv_of_comp_eq
    {D : Type*} [Category* D] {A B T : D}
    (a : A ⟶ B) (e : B ≅ T) (b : A ⟶ T) (h : a ≫ e.hom = b) :
    a = b ≫ e.inv := by
  rw [Iso.eq_comp_inv]
  exact h

private theorem isoSquareOfScalarCoordinates
    {D : Type*} [Category* D] {A B I O T : D}
    (f : A ⟶ B) (g : I ⟶ O) (eA : A ≅ T) (eB : B ≅ T)
    (eI : T ≅ I) (eO : O ≅ T) (d : T ⟶ T)
    (hf : f ≫ eB.hom = eA.hom ≫ d)
    (hg : eI.hom ≫ g = d ≫ eO.inv) :
    f ≫ (eB ≪≫ eO.symm).hom = (eA ≪≫ eI).hom ≫ g := by
  have h₁ :
      f ≫ (eB.hom ≫ eO.inv) = (f ≫ eB.hom) ≫ eO.inv :=
    (Category.assoc _ _ _).symm
  have h₂ :
      (f ≫ eB.hom) ≫ eO.inv = (eA.hom ≫ d) ≫ eO.inv :=
    congrArg (fun k ↦ k ≫ eO.inv) hf
  have h₃ :
      (eA.hom ≫ d) ≫ eO.inv = eA.hom ≫ (d ≫ eO.inv) :=
    Category.assoc _ _ _
  have h₄ :
      eA.hom ≫ (d ≫ eO.inv) = eA.hom ≫ (eI.hom ≫ g) :=
    congrArg (fun k ↦ eA.hom ≫ k) hg.symm
  have h₅ : eA.hom ≫ (eI.hom ≫ g) = (eA.hom ≫ eI.hom) ≫ g :=
    (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- On a Cartier-generator chart, a consecutive pole quotient agrees with the
restriction of the section-ideal quotient. -/
noncomputable def sectionPoleSheafSuccCoker_restrictIsoIdealCoker
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ) :
    letI : IsClosedImmersion z := isClosedImmersion_section z hz
    letI : QuasiCompact z := inferInstance
    (Scheme.Modules.restrictFunctor U.1.ι).obj
        (sectionPoleSheafSuccCoker π z hz n) ≅
      (Scheme.Modules.restrictFunctor U.1.ι).obj
        (cokernel (idealModuleToUnit z)) := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  let F := Scheme.Modules.restrictFunctor U.1.ι
  let eGen := localIdealGeneratorIso z U r hr hspan hnzd
  let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
    (sectionIdealModule π z hz) U.1 eGen.symm
  let ePoleOver := SheafOfModules.dualOverIsoOfIso
    C.ringCatSheaf (sectionIdealModule π z hz) U.1 eIdeal
  let ePole := restrictTrivializationOfOverIso
    (sectionPoleSheaf π z hz) U.1 ePoleOver
  let eP := sectionPoleSheafPowerTrivialization z hz U.1 ePole n
  let ePsucc := sectionPoleSheafPowerTrivialization z hz U.1 ePole (n + 1)
  let eUnit := Scheme.Modules.restrictUnitIso U.1.ι
  let d := unitEndomorphismOfTopSection
    (Scheme.Modules.openTopSection U.1 r)
  let p := eP ≪≫ eGen
  let q := ePsucc ≪≫ eUnit.symm
  have hsucc :
      F.map (sectionPoleSheafSuccHom π z hz n) ≫ ePsucc.hom =
        eP.hom ≫ d := by
    simpa only [F, ePsucc, eP, ePole, ePoleOver, eIdeal, eGen, d] using
      sectionPoleSheafSuccHom_restrict_comp_generatorTrivialization
        z hz U r hr hspan hnzd n
  have hideal :
      eGen.hom ≫ restrictIdealModuleToUnit z U.1.ι = d := by
    change localIdealGeneratorHom z U r hr ≫
        restrictIdealModuleToUnit z U.1.ι = d
    simpa only [d, Scheme.Modules.openTopSection, affineOpenTopSection] using
      localIdealGeneratorHom_comp_restrictIdealModuleToUnit z U r hr
  have hideal' :
      eGen.hom ≫ F.map (idealModuleToUnit z) = d ≫ eUnit.inv := by
    apply eq_comp_iso_inv_of_comp_eq
      (eGen.hom ≫ F.map (idealModuleToUnit z)) eUnit d
    change eGen.hom ≫ (F.map (idealModuleToUnit z) ≫ eUnit.hom) = d
    exact hideal
  have hsquare :
      F.map (sectionPoleSheafSuccHom π z hz n) ≫ q.hom =
        p.hom ≫ F.map (idealModuleToUnit z) := by
    exact isoSquareOfScalarCoordinates
      (F.map (sectionPoleSheafSuccHom π z hz n))
      (F.map (idealModuleToUnit z)) eP ePsucc eGen eUnit d hsucc hideal'
  exact
    (Scheme.Modules.restrictCokernelIso
      (sectionPoleSheafSuccHom π z hz n) U.1).symm ≪≫
      cokernel.mapIso (f := F.map (sectionPoleSheafSuccHom π z hz n))
        (F.map (idealModuleToUnit z)) p q hsquare ≪≫
      Scheme.Modules.restrictCokernelIso (idealModuleToUnit z) U.1

/-- On a Cartier-generator chart, a consecutive pole quotient is supported on
the zero section. -/
noncomputable def sectionPoleSheafSuccCoker_restrictIsoPushforwardUnit
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ) :
    letI : IsClosedImmersion z := isClosedImmersion_section z hz
    letI : QuasiCompact z := inferInstance
    (Scheme.Modules.restrictFunctor U.1.ι).obj
        (sectionPoleSheafSuccCoker π z hz n) ≅
      (Scheme.Modules.restrictFunctor U.1.ι).obj
        ((Scheme.Modules.pushforward z).obj (Scheme.Modules.unitObj S)) := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  exact sectionPoleSheafSuccCoker_restrictIsoIdealCoker
      z hz U r hr hspan hnzd n ≪≫
    (Scheme.Modules.restrictFunctor U.1.ι).mapIso
      (idealModuleCokerIsoPushforwardUnit z)

end ModularCurves
