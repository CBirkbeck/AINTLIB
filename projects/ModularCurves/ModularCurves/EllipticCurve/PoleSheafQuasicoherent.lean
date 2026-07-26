import ModularCurves.EllipticCurve.PoleSheaf
import ModularCurves.Picard.InvertibleSheafLocallyFree
import ModularCurves.ForMathlib.SheafDisjointUnion
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.AddCommGrpCat
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

open ZeroObject

/-- If a scheme module restricts to zero on an open subscheme, then its sections
on the corresponding ambient open form a subsingleton. -/
theorem subsingleton_sections_of_isZero_restrict
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (hzero : IsZero ((restrictFunctor U.ι).obj M)) :
    Subsingleton Γ(M, U) := by
  let F := SheafOfModules.toSheaf U.toScheme.ringCatSheaf
  have hzeroSheaf : IsZero (F.obj (M.restrict U.ι)) :=
    F.map_isZero hzero
  let E := TopCat.Sheaf.forget AddCommGrpCat U.toScheme.toTopCat ⋙
    (CategoryTheory.evaluation U.toScheme.Opensᵒᵖ AddCommGrpCat).obj (.op ⊤)
  letI : E.PreservesZeroMorphisms := by
    constructor
    intro A B
    rfl
  have htop : Subsingleton ↑Γ(M.restrict U.ι, ⊤) :=
    AddCommGrpCat.subsingleton_of_isZero (E.map_isZero hzeroSheaf)
  rw [← Scheme.Opens.opensRange_ι (U := U),
    ← Scheme.Hom.image_top_eq_opensRange]
  change Subsingleton ↑Γ(M.restrict U.ι, ⊤)
  exact htop

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

/-- Restricting a pushforward to an open with empty source preimage gives the zero
module. -/
theorem restrictPushforward_isZero_of_preimage_opensRange_eq_bot
    {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : W ⟶ Y) [IsOpenImmersion g]
    (M : X.Modules) (h : f ⁻¹ᵁ g.opensRange = ⊥) :
    IsZero ((restrictFunctor g).obj ((pushforward f).obj M)) := by
  let q : (restrictFunctor g).obj ((pushforward f).obj M) ⟶ 0 := 0
  haveI : IsIso q := by
    rw [Hom.isIso_iff_isIso_app]
    intro U
    have hpre : f ⁻¹ᵁ (g ''ᵁ U) = ⊥ := by
      apply le_antisymm
      · calc
          f ⁻¹ᵁ (g ''ᵁ U) ≤ f ⁻¹ᵁ g.opensRange :=
            Scheme.Hom.preimage_mono f (g.image_le_opensRange U)
          _ = ⊥ := h
      · exact bot_le
    haveI : Subsingleton Γ(M, f ⁻¹ᵁ (g ''ᵁ U)) := by
      rw [hpre]
      exact TopCat.Sheaf.subsingleton_toType_obj_bot
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    haveI hsource : Subsingleton ↑Γ((restrictFunctor g).obj
        ((pushforward f).obj M), U) := by
      change Subsingleton Γ(M, f ⁻¹ᵁ (g ''ᵁ U))
      infer_instance
    haveI htarget : Subsingleton ↑Γ((0 : W.Modules), U) := by
      let F := SheafOfModules.toSheaf W.ringCatSheaf
      have hz : IsZero (F.obj (0 : W.Modules)) :=
        F.map_isZero (isZero_zero W.Modules)
      let E := TopCat.Sheaf.forget AddCommGrpCat W ⋙
        (CategoryTheory.evaluation (W.Opens)ᵒᵖ AddCommGrpCat).obj (.op U)
      letI : E.PreservesZeroMorphisms := by
        constructor
        intro A B
        rfl
      exact AddCommGrpCat.subsingleton_of_isZero (E.map_isZero hz)
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro y
      exact ⟨0, Subsingleton.elim _ y⟩
  exact (isZero_zero _).of_iso (asIso q)

/-- A scheme module with zero stalk at every point is zero. -/
theorem isZero_of_forall_stalk_isZero
    {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, IsZero
      ((toPresheaf.{u} X ⋙ TopCat.Presheaf.stalkFunctor.{u, u + 1}
        AddCommGrpCat.{u} x).obj M)) :
    IsZero M := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hs : IsZero (F.obj M) := by
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (F.obj M)).2
    intro x
    exact h x
  let q : M ⟶ 0 := 0
  letI hreflect : F.ReflectsIsomorphisms :=
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
  have htarget : IsZero (F.obj (0 : X.Modules)) :=
    F.map_isZero (isZero_zero X.Modules)
  haveI hmap : IsIso (F.map q) :=
    isIso_of_source_target_iso_zero (F.map q) hs.isoZero htarget.isoZero
  haveI : IsIso q :=
    @Functor.ReflectsIsomorphisms.reflects _ _ _ _ F hreflect _ _ q hmap
  exact (isZero_zero _).of_iso (asIso q)

/-- A scheme module restricts to zero when all ambient stalks over the open are
zero. -/
theorem restrict_isZero_of_forall_stalk_isZero
    {X : Scheme.{u}} (M : X.Modules) (W : X.Opens)
    (h : ∀ x : X, x ∈ W → IsZero
      ((toPresheaf.{u} X ⋙ TopCat.Presheaf.stalkFunctor.{u, u + 1}
        AddCommGrpCat.{u} x).obj M)) :
    IsZero ((restrictFunctor W.ι).obj M) := by
  apply isZero_of_forall_stalk_isZero
  intro x
  exact (h x.1 x.2).of_iso ((restrictStalkNatIso W.ι x).app M)

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

/-- The ideal-quotient isomorphism carries the cokernel projection to the
canonical map from the structure sheaf to the section's pushforward. -/
theorem idealModuleCokerIsoPushforwardUnit_π_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    cokernel.π (idealModuleToUnit f) ≫
        (idealModuleCokerIsoPushforwardUnit f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  letI : Epi q :=
    SheafOfModules.unitToPushforwardObjUnit_epi_of_isClosedImmersion f
  let hq := Abelian.epiIsCokernelOfKernel
    (KernelFork.ofι (kernel.ι q) (kernel.condition q)) (kernelIsKernel q)
  change cokernel.π (kernel.ι q) ≫
      (IsColimit.coconePointUniqueUpToIso
        (cokernelIsCokernel (kernel.ι q)) hq).hom = q
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (kernel.ι q)) hq WalkingParallelPair.one

/-- The ideal module of a closed immersion is the structure sheaf away from
the closed subscheme. -/
theorem restrictIdealModuleToUnit_isIso_of_preimage_eq_bot
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (U : Y.Opens) (hU : f ⁻¹ᵁ U = ⊥) :
    IsIso (restrictIdealModuleToUnit f U.ι) := by
  have htarget : IsZero
      ((Scheme.Modules.restrictFunctor U.ι).obj
        ((Scheme.Modules.pushforward f).obj (Scheme.Modules.unitObj X))) := by
    apply Scheme.Modules.restrictPushforward_isZero_of_preimage_opensRange_eq_bot
    simpa only [Scheme.Opens.opensRange_ι] using hU
  have hrestrictedCokernel : IsZero
      ((Scheme.Modules.restrictFunctor U.ι).obj
        (cokernel (idealModuleToUnit f))) :=
    htarget.of_iso ((Scheme.Modules.restrictFunctor U.ι).mapIso
      (idealModuleCokerIsoPushforwardUnit f))
  have hcokernel : IsZero
      (cokernel ((Scheme.Modules.restrictFunctor U.ι).map
        (idealModuleToUnit f))) :=
    hrestrictedCokernel.of_iso
      (Scheme.Modules.restrictCokernelIso (idealModuleToUnit f) U)
  have hleft : Epi ((Scheme.Modules.restrictFunctor U.ι).map
      (idealModuleToUnit f)) :=
    Preadditive.epi_of_isZero_cokernel _ hcokernel
  have hright : Epi (Scheme.Modules.restrictUnitIso U.ι).hom := by
    letI : IsIso (Scheme.Modules.restrictUnitIso U.ι).hom :=
      Iso.isIso_hom (Scheme.Modules.restrictUnitIso U.ι)
    exact IsIso.epi_of_iso _
  haveI : Epi (restrictIdealModuleToUnit f U.ι) := by
    change Epi ((Scheme.Modules.restrictFunctor U.ι).map
      (idealModuleToUnit f) ≫ (Scheme.Modules.restrictUnitIso U.ι).hom)
    exact epi_comp' hleft hright
  haveI : Mono (restrictIdealModuleToUnit f U.ι) :=
    restrictIdealModuleToUnit_mono f U.ι
  exact isIso_of_mono_of_epi _

/-- The pole sheaf of a section is canonically trivial on every open disjoint
from the section. -/
noncomputable def sectionPoleSheafTrivializationOfSectionPreimageEqBot
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (hU : z ⁻¹ᵁ U = ⊥) :
    (sectionPoleSheaf π z hz).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  let hIso : IsIso (restrictIdealModuleToUnit z U.ι) :=
    restrictIdealModuleToUnit_isIso_of_preimage_eq_bot z U hU
  let e := @asIso _ _ _ _ (restrictIdealModuleToUnit z U.ι) hIso
  exact Scheme.Modules.dualRestrictIsoOfRestrictIso
    (sectionIdealModule π z hz) U e

/-- Every nonnegative pole-sheaf power is canonically trivial on an open
disjoint from the section. -/
noncomputable def sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (hU : z ⁻¹ᵁ U = ⊥) (n : ℕ) :
    (sectionPoleSheafPower π z hz n).restrict U.ι ≅
      Scheme.Modules.unitObj U.toScheme :=
  sectionPoleSheafPowerTrivialization z hz U
    (sectionPoleSheafTrivializationOfSectionPreimageEqBot z hz U hU) n

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

/-- A successive pole-filtration quotient is quasicoherent. -/
theorem sectionPoleSheafSuccCoker_isQuasicoherent
    {C S : Scheme.{u}} {π : C ⟶ S} (hsm : SmoothOfRelativeDimension 1 π)
    [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    SheafOfModules.IsQuasicoherent.{u}
      (sectionPoleSheafSuccCoker π z hz n) := by
  letI : (sectionPoleSheafSuccCoker π z hz n).IsFinitePresentation :=
    sectionPoleSheafSuccCoker_isFinitePresentation hsm z hz n
  exact (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (sectionPoleSheafSuccCoker π z hz n)).choose.isQuasicoherent

local instance (X : Scheme.{u}) :
    ∀ V, IsMulCommutative (X.ringCatSheaf.obj.obj V) :=
  fun V ↦ by
    change IsMulCommutative (X.presheaf.obj V)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- The over-site trivialization induced by an invertible restricted map to the
structure module has hom equal to the original map on the over-site. -/
theorem overTrivializationOfRestrictMapIso_hom
    {X : Scheme.{u}} {M : X.Modules}
    (i : M ⟶ Scheme.Modules.unitObj X) (U : X.Opens)
    (hIso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map i ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom)) :
    let e := @asIso _ _ _ _
      ((Scheme.Modules.restrictFunctor U.ι).map i ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom) hIso
    (Scheme.Modules.overTrivializationOfRestrictIso M U e).hom = i.over U := by
  let H := (Scheme.Modules.restrictFunctor U.ι).map i ≫
    (Scheme.Modules.restrictUnitIso U.ι).hom
  let e := @asIso _ _ _ _ H hIso
  let eOver := Scheme.Modules.overTrivializationOfRestrictIso M U e
  let G := (Scheme.Modules.overEquiv U).functor
  let F := Scheme.Modules.overFunctorEquiv U
  let E := U.sheafOfModulesEquivOverUnit X.ringCatSheaf
  let C := E.hom
  let FI := F.app M
  let FO := F.app (Scheme.Modules.unitObj X)
  let q := (Scheme.Modules.restrictFunctor U.ι).map i
  let eO := (Scheme.Modules.restrictUnitIso U.ι).hom
  let B := G.map (i.over U)
  have hC : FO.hom ≫ eO = C := by
    dsimp only [FO, F, eO, C]
    rw [Scheme.Modules.overFunctorEquiv_unitP]
    exact (Scheme.Modules.restrictUnitIso U.ι).inv_hom_id
  have hnat := F.hom.naturality i
  change B ≫ FO.hom = FI.hom ≫ q at hnat
  have hnatComp := congrArg (fun p ↦ p ≫ eO) hnat
  have hleft : B ≫ (FO.hom ≫ eO) = (B ≫ FO.hom) ≫ eO :=
    (Category.assoc _ _ _).symm
  have hright : (FI.hom ≫ q) ≫ eO = FI.hom ≫ (q ≫ eO) :=
    Category.assoc _ _ _
  have hbase : B ≫ (FO.hom ≫ eO) = FI.hom ≫ (q ≫ eO) :=
    hleft.trans (hnatComp.trans hright)
  have hBC : B ≫ C = FI.hom ≫ (q ≫ eO) :=
    (congrArg (fun p ↦ B ≫ p) hC.symm).trans hbase
  have hinner : FI.hom ≫ (q ≫ eO) = B ≫ C := hBC.symm
  apply G.map_injective
  change G.map eOver.hom = B
  simp only [eOver, Scheme.Modules.overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom]
  change FI.hom ≫ H ≫ E.inv = B
  change FI.hom ≫ (q ≫ eO) ≫ E.inv = B
  have houter := congrArg (fun p ↦ p ≫ E.inv) hinner
  have hassoc : (B ≫ C) ≫ E.inv = B ≫ (C ≫ E.inv) :=
    Category.assoc _ _ _
  have hcancel : B ≫ (C ≫ E.inv) = B ≫ 𝟙 _ :=
    congrArg (fun p ↦ B ≫ p) E.hom_inv_id
  exact houter.trans (hassoc.trans (hcancel.trans (Category.comp_id _)))

/-- Away from the section, the ideal inclusion is the hom of its canonical
over-site trivialization. -/
theorem sectionIdealToUnit_over_eq_trivializationOfSectionPreimageEqBot
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (hU : z ⁻¹ᵁ U = ⊥) :
    letI : IsClosedImmersion z := isClosedImmersion_section z hz
    let hIso : IsIso (restrictIdealModuleToUnit z U.ι) :=
      restrictIdealModuleToUnit_isIso_of_preimage_eq_bot z U hU
    let eRestrict := @asIso _ _ _ _ (restrictIdealModuleToUnit z U.ι) hIso
    let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
      (sectionIdealModule π z hz) U eRestrict
    eIdeal.hom = (sectionIdealToUnit π z hz).over U := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  let hIso : IsIso (restrictIdealModuleToUnit z U.ι) :=
    restrictIdealModuleToUnit_isIso_of_preimage_eq_bot z U hU
  dsimp only
  exact overTrivializationOfRestrictMapIso_hom
    (sectionIdealToUnit π z hz) U hIso

/-- In the canonical frame away from the section, the inclusion into the
simple-pole sheaf has scalar coordinate one. -/
theorem sectionPoleUnitHom_over_comp_trivializationOfSectionPreimageEqBot
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (hU : z ⁻¹ᵁ U = ⊥) :
    letI : IsClosedImmersion z := isClosedImmersion_section z hz
    let hIso : IsIso (restrictIdealModuleToUnit z U.ι) :=
      restrictIdealModuleToUnit_isIso_of_preimage_eq_bot z U hU
    let eRestrict := @asIso _ _ _ _ (restrictIdealModuleToUnit z U.ι) hIso
    let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
      (sectionIdealModule π z hz) U eRestrict
    ((sectionPoleUnitHom π z hz).over U) ≫
        (SheafOfModules.dualOverIsoOfIso C.ringCatSheaf
          (sectionIdealModule π z hz) U eIdeal).hom =
      SheafOfModules.overUnitScalarEnd C.ringCatSheaf U 1 := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  let hIso : IsIso (restrictIdealModuleToUnit z U.ι) :=
    restrictIdealModuleToUnit_isIso_of_preimage_eq_bot z U hU
  let eRestrict := @asIso _ _ _ _ (restrictIdealModuleToUnit z U.ι) hIso
  let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
    (sectionIdealModule π z hz) U eRestrict
  apply dualMap_over_comp_dualOverIsoOfIso_hom_eq_scalar
    (sectionIdealToUnit π z hz) U eIdeal 1
  have he : eIdeal.hom = (sectionIdealToUnit π z hz).over U :=
    sectionIdealToUnit_over_eq_trivializationOfSectionPreimageEqBot
      z hz U hU
  have hcomp : eIdeal.inv ≫ (sectionIdealToUnit π z hz).over U =
      eIdeal.inv ≫ eIdeal.hom :=
    congrArg (fun p ↦ eIdeal.inv ≫ p) he.symm
  have hid : eIdeal.inv ≫ eIdeal.hom = 𝟙 _ := eIdeal.inv_hom_id
  have hone : (𝟙 _) = SheafOfModules.overUnitScalarEnd
      C.ringCatSheaf U 1 :=
    (SheafOfModules.overUnitScalarEndRingHom C.ringCatSheaf U).map_one.symm
  exact hcomp.trans (hid.trans hone)

/-- Away from the section, every consecutive pole-filtration map is the
identity under the canonical power trivializations. -/
theorem sectionPoleSheafSuccHom_restrict_comp_trivializationOfSectionPreimageEqBot
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (hU : z ⁻¹ᵁ U = ⊥) (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map
          (sectionPoleSheafSuccHom π z hz n) ≫
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz U hU (n + 1)).hom =
      (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
        z hz U hU n).hom := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  let hIso : IsIso (restrictIdealModuleToUnit z U.ι) :=
    restrictIdealModuleToUnit_isIso_of_preimage_eq_bot z U hU
  let eRestrict := @asIso _ _ _ _ (restrictIdealModuleToUnit z U.ι) hIso
  let eIdeal := Scheme.Modules.overTrivializationOfRestrictIso
    (sectionIdealModule π z hz) U eRestrict
  let ePoleOver := SheafOfModules.dualOverIsoOfIso C.ringCatSheaf
    (sectionIdealModule π z hz) U eIdeal
  have h := sectionPoleSheafSuccHom_restrict_comp_powerTrivialization
    z hz U ePoleOver 1
      (sectionPoleUnitHom_over_comp_trivializationOfSectionPreimageEqBot
        z hz U hU) n
  have hePole :
      restrictTrivializationOfOverIso (sectionPoleSheaf π z hz) U ePoleOver =
        sectionPoleSheafTrivializationOfSectionPreimageEqBot z hz U hU := by
    apply Iso.ext
    rfl
  rw [hePole] at h
  simpa only [sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot,
    Scheme.Modules.openTopSection, map_one, unitEndomorphismOfTopSection_one,
    Category.comp_id] using h

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

private noncomputable def
    sectionPoleSheafSuccCoker_restrictIsoIdealCokerData
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ) :
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
    let ePsucc := sectionPoleSheafPowerTrivialization
      z hz U.1 ePole (n + 1)
    let eUnit := Scheme.Modules.restrictUnitIso U.1.ι
    let q := ePsucc ≪≫ eUnit.symm
    { e : F.obj (sectionPoleSheafSuccCoker π z hz n) ≅
          F.obj (cokernel (idealModuleToUnit z)) //
      F.map (cokernel.π (sectionPoleSheafSuccHom π z hz n)) ≫ e.hom =
        q.hom ≫ F.map (cokernel.π (idealModuleToUnit z)) } := by
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
  let ePoleCoker := Scheme.Modules.restrictCokernelIso
    (sectionPoleSheafSuccHom π z hz n) U.1
  let eMap := cokernel.mapIso
    (f := F.map (sectionPoleSheafSuccHom π z hz n))
    (F.map (idealModuleToUnit z)) p q hsquare
  let eIdealCoker := Scheme.Modules.restrictCokernelIso
    (idealModuleToUnit z) U.1
  let e := ePoleCoker.symm ≪≫ eMap ≪≫ eIdealCoker
  have hfirst :
      F.map (cokernel.π (sectionPoleSheafSuccHom π z hz n)) ≫
          ePoleCoker.symm.hom =
        cokernel.π (F.map (sectionPoleSheafSuccHom π z hz n)) := by
    simpa only [ePoleCoker, Scheme.Modules.restrictCokernelIso,
      Iso.symm_hom, Iso.symm_inv] using
        PreservesCokernel.π_iso_hom F
          (sectionPoleSheafSuccHom π z hz n)
  have hmiddle :
      cokernel.π (F.map (sectionPoleSheafSuccHom π z hz n)) ≫
          eMap.hom =
        q.hom ≫ cokernel.π (F.map (idealModuleToUnit z)) := by
    change cokernel.π (F.map (sectionPoleSheafSuccHom π z hz n)) ≫
        cokernel.map (F.map (sectionPoleSheafSuccHom π z hz n))
          (F.map (idealModuleToUnit z)) p.hom q.hom hsquare =
      q.hom ≫ cokernel.π (F.map (idealModuleToUnit z))
    exact cokernel.π_desc _ _ _
  have hlast :
      cokernel.π (F.map (idealModuleToUnit z)) ≫ eIdealCoker.hom =
        F.map (cokernel.π (idealModuleToUnit z)) := by
    have h := PreservesCokernel.π_iso_hom F (idealModuleToUnit z)
    have hcomp := congrArg
      (fun k ↦ k ≫ (PreservesCokernel.iso F (idealModuleToUnit z)).inv) h
    simpa only [eIdealCoker, Scheme.Modules.restrictCokernelIso,
      Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
        hcomp.symm
  refine ⟨e, ?_⟩
  have hmiddleWhisker := congrArg (fun k ↦ k ≫ eIdealCoker.hom) hmiddle
  have hlastWhisker := congrArg (fun k ↦ q.hom ≫ k) hlast
  calc
    F.map (cokernel.π (sectionPoleSheafSuccHom π z hz n)) ≫ e.hom =
        (F.map (cokernel.π (sectionPoleSheafSuccHom π z hz n)) ≫
            ePoleCoker.symm.hom) ≫ eMap.hom ≫ eIdealCoker.hom := by
      simp only [e, Iso.trans_hom, Category.assoc]
    _ = cokernel.π (F.map (sectionPoleSheafSuccHom π z hz n)) ≫
          eMap.hom ≫ eIdealCoker.hom := by rw [hfirst]
    _ = (q.hom ≫ cokernel.π (F.map (idealModuleToUnit z))) ≫
          eIdealCoker.hom := hmiddleWhisker
    _ = q.hom ≫
          (cokernel.π (F.map (idealModuleToUnit z)) ≫
            eIdealCoker.hom) := Category.assoc _ _ _
    _ = q.hom ≫ F.map (cokernel.π (idealModuleToUnit z)) := hlastWhisker

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
        (cokernel (idealModuleToUnit z)) :=
  (sectionPoleSheafSuccCoker_restrictIsoIdealCokerData
    z hz U r hr hspan hnzd n).1

/-- The local pole-quotient isomorphism respects the canonical cokernel
projections. -/
theorem sectionPoleSheafSuccCoker_restrictIsoIdealCoker_π_hom
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ) :
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
    let ePsucc := sectionPoleSheafPowerTrivialization
      z hz U.1 ePole (n + 1)
    let eUnit := Scheme.Modules.restrictUnitIso U.1.ι
    F.map (cokernel.π (sectionPoleSheafSuccHom π z hz n)) ≫
        (sectionPoleSheafSuccCoker_restrictIsoIdealCoker
          z hz U r hr hspan hnzd n).hom =
      (ePsucc ≪≫ eUnit.symm).hom ≫
        F.map (cokernel.π (idealModuleToUnit z)) :=
  (sectionPoleSheafSuccCoker_restrictIsoIdealCokerData
    z hz U r hr hspan hnzd n).2

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

/-- The local identification of a consecutive pole quotient with the pushed-forward
structure sheaf respects the canonical quotient projection. -/
theorem sectionPoleSheafSuccCoker_restrictIsoPushforwardUnit_π_hom
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ) :
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
    let ePsucc := sectionPoleSheafPowerTrivialization
      z hz U.1 ePole (n + 1)
    let eUnit := Scheme.Modules.restrictUnitIso U.1.ι
    F.map (cokernel.π (sectionPoleSheafSuccHom π z hz n)) ≫
        (sectionPoleSheafSuccCoker_restrictIsoPushforwardUnit
          z hz U r hr hspan hnzd n).hom =
      (ePsucc ≪≫ eUnit.symm).hom ≫
        F.map (SheafOfModules.unitToPushforwardObjUnit
          z.toRingCatSheafHom) := by
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
  let ePsucc := sectionPoleSheafPowerTrivialization
    z hz U.1 ePole (n + 1)
  let eUnit := Scheme.Modules.restrictUnitIso U.1.ι
  let q := ePsucc ≪≫ eUnit.symm
  let eLocal := sectionPoleSheafSuccCoker_restrictIsoIdealCoker
    z hz U r hr hspan hnzd n
  let eCoker := idealModuleCokerIsoPushforwardUnit z
  have hpole :
      F.map (cokernel.π (sectionPoleSheafSuccHom π z hz n)) ≫
          eLocal.hom =
        q.hom ≫ F.map (cokernel.π (idealModuleToUnit z)) := by
    exact sectionPoleSheafSuccCoker_restrictIsoIdealCoker_π_hom
      z hz U r hr hspan hnzd n
  have hcoker := idealModuleCokerIsoPushforwardUnit_π_hom z
  have hmap :
      F.map (cokernel.π (idealModuleToUnit z)) ≫ F.map eCoker.hom =
        F.map (SheafOfModules.unitToPushforwardObjUnit
          z.toRingCatSheafHom) := by
    rw [← F.map_comp]
    exact congrArg F.map hcoker
  have hpoleWhisker := congrArg (fun k ↦ k ≫ F.map eCoker.hom) hpole
  have hmapWhisker := congrArg (fun k ↦ q.hom ≫ k) hmap
  change F.map (cokernel.π (sectionPoleSheafSuccHom π z hz n)) ≫
      (eLocal.hom ≫ F.map eCoker.hom) =
    q.hom ≫ F.map (SheafOfModules.unitToPushforwardObjUnit
      z.toRingCatSheafHom)
  have hassocSource :
      F.map (cokernel.π (sectionPoleSheafSuccHom π z hz n)) ≫
          (eLocal.hom ≫ F.map eCoker.hom) =
        (F.map (cokernel.π (sectionPoleSheafSuccHom π z hz n)) ≫
          eLocal.hom) ≫ F.map eCoker.hom :=
    (Category.assoc _ _ _).symm
  have hassocTarget :
      (q.hom ≫ F.map (cokernel.π (idealModuleToUnit z))) ≫
          F.map eCoker.hom =
        q.hom ≫ (F.map (cokernel.π (idealModuleToUnit z)) ≫
          F.map eCoker.hom) :=
    Category.assoc _ _ _
  exact hassocSource.trans
    (hpoleWhisker.trans (hassocTarget.trans hmapWhisker))

/-- A consecutive pole quotient vanishes on a Cartier-generator chart disjoint
from the section. -/
theorem sectionPoleSheafSuccCoker_restrict_isZero_of_preimage_eq_bot
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (n : ℕ)
    (hU : z ⁻¹ᵁ U.1 = ⊥) :
    IsZero ((Scheme.Modules.restrictFunctor U.1.ι).obj
      (sectionPoleSheafSuccCoker π z hz n)) := by
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  have htarget : IsZero
      ((Scheme.Modules.restrictFunctor U.1.ι).obj
        ((Scheme.Modules.pushforward z).obj (Scheme.Modules.unitObj S))) := by
    apply Scheme.Modules.restrictPushforward_isZero_of_preimage_opensRange_eq_bot
    simpa only [Scheme.Opens.opensRange_ι] using hU
  exact htarget.of_iso
    (sectionPoleSheafSuccCoker_restrictIsoPushforwardUnit
      z hz U r hr hspan hnzd n)

/-- A consecutive pole quotient restricts to zero on every open whose preimage
under the section is empty. -/
theorem sectionPoleSheafSuccCoker_restrict_isZero_of_section_preimage_eq_bot
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (W : C.Opens)
    (hW : z ⁻¹ᵁ W = ⊥) (n : ℕ) :
    IsZero ((Scheme.Modules.restrictFunctor W.ι).obj
      (sectionPoleSheafSuccCoker π z hz n)) := by
  apply Scheme.Modules.restrict_isZero_of_forall_stalk_isZero
  intro x hxW
  obtain ⟨V, hxV, r, hspan, hnzd⟩ :=
    (RelEffCartierDiv.sectionDivisor_isOfficial hsm z hz).locallyPrincipal x
  change z.ker.ideal V = Ideal.span {r} at hspan
  obtain ⟨a, hxU, hUW⟩ :=
    exists_chartBasicOpenImage_le_of_mem V W x hxV hxW
  let U := chartBasicOpenImage V a
  let rU := C.presheaf.map (homOfLE (chartBasicOpenImage_le V a)).op r
  have hdata := ideal_chartBasicOpenImage_span_nzd z.ker V r hspan hnzd a
  have hrU : rU ∈ z.ker.ideal U := by
    rw [hdata.1]
    exact Ideal.mem_span_singleton_self rU
  have hpreU : z ⁻¹ᵁ U.1 = ⊥ := by
    apply le_antisymm
    · calc
        z ⁻¹ᵁ U.1 ≤ z ⁻¹ᵁ W := Scheme.Hom.preimage_mono z hUW
        _ = ⊥ := hW
    · exact bot_le
  have hlocal : IsZero ((Scheme.Modules.restrictFunctor U.1.ι).obj
      (sectionPoleSheafSuccCoker π z hz n)) :=
    sectionPoleSheafSuccCoker_restrict_isZero_of_preimage_eq_bot
      z hz U rU hrU hdata.1 hdata.2 n hpreU
  let xU : U.1.toScheme := ⟨x, hxU⟩
  let F := SheafOfModules.toSheaf U.1.toScheme.ringCatSheaf
  have hlocalSheaf : IsZero (F.obj
      ((Scheme.Modules.restrictFunctor U.1.ι).obj
        (sectionPoleSheafSuccCoker π z hz n))) :=
    F.map_isZero hlocal
  have hlocalStalk :=
    (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).1 hlocalSheaf xU
  exact hlocalStalk.of_iso
    ((Scheme.Modules.restrictStalkNatIso U.1.ι xU).app
      (sectionPoleSheafSuccCoker π z hz n)).symm

end ModularCurves
