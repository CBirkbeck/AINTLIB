/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI contributors
-/
import «Adic spaces».StructureSheaf
import «Adic spaces».AdicMorphismsCore

/-!
# Restriction of `𝒱`-objects to open subsets (Campaign 9, P5-1)

The restriction of a valued (pre)sheafed space to an open subset:
`VPreObj.restrictOpen` restricts the presheafed space along the open
inclusion and transports the stalk package (locality, valuation, support)
along mathlib's `restrictStalkIso`; `VObj.restrictOpen` adds the restricted
sheaf-of-topological-rings condition (image covers are covers, so the
ambient `Hom_cont(T, −)`-gluing applies).

This is the `X|_U` operation of Wedhorn Definition 8.22.
-/


open CategoryTheory TopologicalSpace Opposite

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace ValuationSpectrum

/-! ### P5-1: restriction of a `𝒱^pre`-object to an open subset -/

variable (X : VPreObj.{u}) (U : Opens ↥(X.toTopCat))

/-- The inclusion of an open subset, as a morphism of `TopCat`. -/
def opensIncl : TopCat.of ↥U ⟶ X.toTopCat :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem opensIncl_isOpenEmbedding :
    Topology.IsOpenEmbedding (opensIncl X U) :=
  U.2.isOpenEmbedding_subtypeVal

/-- The ambient point of a subset point (spelled as the inclusion image, so
the stalk types line up definitionally). -/
def restrictPoint (x : ↥U) : ↥(X.toTopCat) :=
  show ↥(X.toTopCat) from (ConcreteCategory.hom (opensIncl X U)) x

/-- The restricted presheafed space of complete topological rings. -/
def restrictSpace : TopRingPresheafedSpace :=
  X.toPresheafedSpace.restrict (opensIncl_isOpenEmbedding X U)

/-- The ambient space with its ring presheaf, as a `CommRingCat`-valued
presheafed space (the stalk-comparison vehicle). -/
def restrictRingAmbient : AlgebraicGeometry.PresheafedSpace CommRingCat where
  carrier := X.toTopCat
  presheaf := X.toPresheafedSpace.ringPresheaf

/-- **The restricted ring stalks are the ambient ring stalks** (mathlib's
`restrictStalkIso` at the ring-presheaf level). -/
noncomputable def restrictRingStalkIso (x : ↥U) :
    (restrictSpace X U).ringStalk x
      ≅ X.toPresheafedSpace.ringStalk (restrictPoint X U x) :=
  AlgebraicGeometry.PresheafedSpace.restrictStalkIso
    (restrictRingAmbient X) (opensIncl_isOpenEmbedding X U) x

/-- The stalk comparison as a ring equivalence. -/
noncomputable def restrictRingStalkEquiv (x : ↥U) :
    ToType ((restrictSpace X U).ringStalk x)
      ≃+* ToType (X.toPresheafedSpace.ringStalk (restrictPoint X U x)) :=
  (restrictRingStalkIso X U x).commRingCatIsoToRingEquiv

/-- Maximal ideals transport through a ring equivalence of local rings
(instance-explicit form). -/
theorem maximalIdeal_comap_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (instR : IsLocalRing R) (instS : IsLocalRing S) (e : R ≃+* S) :
    @IsLocalRing.maximalIdeal R _ instR
      = (@IsLocalRing.maximalIdeal S _ instS).comap (e : R →+* S) := by
  refine Ideal.ext fun r => ?_
  rw [@IsLocalRing.mem_maximalIdeal _ _ instR, Ideal.mem_comap,
    @IsLocalRing.mem_maximalIdeal _ _ instS, mem_nonunits_iff,
    mem_nonunits_iff, not_iff_not]
  exact ⟨fun h => h.map (e : R →+* S), fun h => by
    have := h.map (e.symm : S →+* R)
    rwa [show (e.symm : S →+* R) ((e : R →+* S) r) = r from
      e.symm_apply_apply r] at this⟩

/-- The stalks of the restriction are local. -/
theorem isLocalRing_restrictStalk (x : ↥U) :
    IsLocalRing (ToType ((restrictSpace X U).ringStalk x)) := by
  haveI : IsLocalRing (ToType (X.toPresheafedSpace.ringStalk
      (restrictPoint X U x))) := X.isLocalRing_stalk (restrictPoint X U x)
  exact (restrictRingStalkEquiv X U x).symm.isLocalRing

/-- **The restriction of a `𝒱^pre`-object to an open subset**: the restricted
presheafed space, with the stalk package transported along the restriction
stalk isomorphisms. -/
noncomputable def VPreObj.restrictOpen : VPreObj where
  toPresheafedSpace := restrictSpace X U
  isLocalRing_stalk := fun x => isLocalRing_restrictStalk X U x
  val := fun x => comap ((restrictRingStalkEquiv X U x : _ →+* _))
    (X.val (restrictPoint X U x))
  val_supp := fun x => by
    haveI hAmb : IsLocalRing (ToType (X.toPresheafedSpace.ringStalk
        (restrictPoint X U x))) := X.isLocalRing_stalk (restrictPoint X U x)
    rw [supp_comap]
    rw [show (X.val (restrictPoint X U x)).supp
        = @IsLocalRing.maximalIdeal _ _ hAmb from X.val_supp _]
    exact (maximalIdeal_comap_of_ringEquiv (isLocalRing_restrictStalk X U x)
      hAmb (restrictRingStalkEquiv X U x)).symm

/-! ### The open-image functor bookkeeping -/

/-- The open-image functor of the inclusion. -/
def restrictOpenFunctor : Opens ↥U ⥤ Opens ↥(X.toTopCat) :=
  (opensIncl_isOpenEmbedding X U).isOpenMap.functor

theorem restrictOpenFunctor_iSup {ι : Type*} (W : ι → Opens ↥U) :
    (restrictOpenFunctor X U).obj (iSup W)
      = ⨆ i, (restrictOpenFunctor X U).obj (W i) := by
  refine Opens.ext ?_
  show (opensIncl X U) '' ((iSup W : Opens ↥U) : Set ↥U) = _
  rw [Opens.coe_iSup, Set.image_iUnion, Opens.coe_iSup]
  rfl

theorem restrictOpenFunctor_inf (W₁ W₂ : Opens ↥U) :
    (restrictOpenFunctor X U).obj (W₁ ⊓ W₂)
      = (restrictOpenFunctor X U).obj W₁ ⊓ (restrictOpenFunctor X U).obj W₂ := by
  refine Opens.ext ?_
  show (opensIncl X U) '' ((W₁ ⊓ W₂ : Opens ↥U) : Set ↥U) = _
  rw [Opens.coe_inf, Set.image_inter
    (show Function.Injective (⇑(ConcreteCategory.hom (opensIncl X U)))
      from Subtype.val_injective)]
  rfl

/-! ### Restriction of the sheaf condition -/

/-- **The sheaf-of-topological-rings condition restricts along an open
inclusion**: image covers are covers, so the ambient gluing applies. -/
theorem isSheafOfTopologicalRings_restrict
    (h : TopCat.Presheaf.IsSheafOfTopologicalRings
      X.toPresheafedSpace.presheaf) :
    TopCat.Presheaf.IsSheafOfTopologicalRings
      (restrictSpace X U).presheaf := by
  intro T _tc _tt _tr ι W f hcompat
  have key2 : ∀ i j (Z : Opens ↥(X.toTopCat))
      (_ : Z = (restrictOpenFunctor X U).obj (W i ⊓ W j))
      (h1 : Z ≤ (restrictOpenFunctor X U).obj (W i))
      (h2 : Z ≤ (restrictOpenFunctor X U).obj (W j)),
      (X.toPresheafedSpace.presheaf.map (homOfLE h1).op).1.comp (f i).1
        = (X.toPresheafedSpace.presheaf.map (homOfLE h2).op).1.comp (f j).1 := by
    intro i j Z hZ h1 h2
    subst hZ
    exact hcompat i j
  obtain ⟨g, hg, huniq⟩ := h T _tc _tt _tr
    (fun i => (restrictOpenFunctor X U).obj (W i)) f
    (fun i j => key2 i j _ (restrictOpenFunctor_inf X U (W i) (W j)).symm
      inf_le_left inf_le_right)
  have keyS : ∀ (Z : Opens ↥(X.toTopCat))
      (_ : Z = ⨆ i, (restrictOpenFunctor X U).obj (W i))
      (hle : ∀ i, (restrictOpenFunctor X U).obj (W i) ≤ Z),
      ∃! g : {g : T →+* ((X.toPresheafedSpace.presheaf.obj (op Z)) : Type u) //
          Continuous g},
        ∀ i, (X.toPresheafedSpace.presheaf.map (homOfLE (hle i)).op).1.comp g.1
          = (f i).1 := by
    intro Z hZ hle
    subst hZ
    exact ⟨g, hg, huniq⟩
  exact keyS ((restrictOpenFunctor X U).obj (iSup W))
    (restrictOpenFunctor_iSup X U W)
    (fun i => le_of_le_of_eq
      (le_iSup (fun k => (restrictOpenFunctor X U).obj (W k)) i)
      (restrictOpenFunctor_iSup X U W).symm)

/-- **The restriction of a `𝒱`-object to an open subset** is again a
`𝒱`-object. -/
noncomputable def VObj.restrictOpen (X : VObj.{u}) (U : Opens ↥(X.toTopCat)) :
    VObj where
  toVPreObj := X.toVPreObj.restrictOpen U
  isSheafTopRings := isSheafOfTopologicalRings_restrict X.toVPreObj U
    X.isSheafTopRings

/-! ### Transport of a `𝒱^pre`-structure along an isomorphism of presheafed
spaces (Campaign 9, P5-K8) -/

/-- The ring stalk map of an isomorphism of presheafed spaces is an
isomorphism. -/
instance isIso_ringStalkMap {X Y : TopRingPresheafedSpace.{u}} (α : X ⟶ Y)
    [IsIso α] (x : X) : IsIso (ringStalkMap α x) := by
  haveI : IsIso (CompleteTopCommRingCat.forgetToCommRingCat.mapPresheaf.map α) :=
    Functor.map_isIso _ α
  exact (show IsIso ((CompleteTopCommRingCat.forgetToCommRingCat.mapPresheaf.map
    α).stalkMap x) from AlgebraicGeometry.PresheafedSpace.stalkMap.isIso
      (CompleteTopCommRingCat.forgetToCommRingCat.mapPresheaf.map α) x)

/-- The stalk comparison of an isomorphism, as a ring equivalence. -/
noncomputable def isoStalkRingEquiv {X Y : TopRingPresheafedSpace.{u}}
    (e : X ≅ Y) (x : X) :
    ToType (Y.ringStalk (ConcreteCategory.hom e.hom.base x))
      ≃+* ToType (X.ringStalk x) :=
  (asIso (ringStalkMap e.hom x)).commRingCatIsoToRingEquiv

/-- **Transport of a `𝒱^pre`-structure along an isomorphism** (P5-K8): a
presheafed space isomorphic to a `𝒱^pre`-object is one, with the stalk
package pulled back along the stalk comparisons. -/
noncomputable def VPreObj.ofIso {X : TopRingPresheafedSpace.{u}} {Y : VPreObj.{u}}
    (e : X ≅ Y.toPresheafedSpace) : VPreObj.{u} where
  toPresheafedSpace := X
  isLocalRing_stalk := fun x => by
    haveI : IsLocalRing (ToType (Y.toPresheafedSpace.ringStalk
        (ConcreteCategory.hom e.hom.base x))) := Y.isLocalRing_stalk _
    exact (isoStalkRingEquiv e x).isLocalRing
  val := fun x => comap ((isoStalkRingEquiv e x).symm : _ →+* _)
    (Y.val (ConcreteCategory.hom e.hom.base x))
  val_supp := fun x => by
    haveI hY : IsLocalRing (ToType (Y.toPresheafedSpace.ringStalk
        (ConcreteCategory.hom e.hom.base x))) := Y.isLocalRing_stalk _
    haveI hX : IsLocalRing (ToType (X.ringStalk x)) := by
      exact (isoStalkRingEquiv e x).isLocalRing
    rw [supp_comap]
    rw [show (Y.val (ConcreteCategory.hom e.hom.base x)).supp
        = @IsLocalRing.maximalIdeal _ _ hY from Y.val_supp _]
    exact (maximalIdeal_comap_of_ringEquiv hX hY (isoStalkRingEquiv e x).symm).symm

/-- The isomorphism is a morphism of `𝒱^pre` onto the transported
structure. -/
noncomputable def VPreHom.ofIso {X : TopRingPresheafedSpace.{u}} {Y : VPreObj.{u}}
    (e : X ≅ Y.toPresheafedSpace) :
    VPreHom (VPreObj.ofIso e) Y where
  toHom := e.hom
  isLocalHom_stalkMap := fun x => by
    haveI hY : IsLocalRing (ToType (Y.toPresheafedSpace.ringStalk
        (ConcreteCategory.hom e.hom.base x))) := Y.isLocalRing_stalk _
    haveI hX : IsLocalRing (ToType (X.ringStalk x)) :=
      (isoStalkRingEquiv e x).isLocalRing
    exact @IsLocalHom.of_surjective _ _ _ _ hX.toNontrivial hY
      ((ringStalkMap e.hom x).hom') (isoStalkRingEquiv e x).surjective
  val_compat := fun x => by
    show Y.val (ConcreteCategory.hom e.hom.base x)
      = comap (ringStalkMap e.hom x).hom'
        (comap ((isoStalkRingEquiv e x).symm.toRingHom)
          (Y.val (ConcreteCategory.hom e.hom.base x)))
    have h2 := congr_fun (comap_comp ((ringStalkMap e.hom x).hom')
      ((isoStalkRingEquiv e x).symm.toRingHom))
      (Y.val (ConcreteCategory.hom e.hom.base x))
    have hcomp : ((isoStalkRingEquiv e x).symm.toRingHom).comp
        (ringStalkMap e.hom x).hom' = RingHom.id _ :=
      RingHom.ext fun z => (isoStalkRingEquiv e x).symm_apply_apply z
    refine Eq.trans ?_ h2.symm
    show Y.val (ConcreteCategory.hom e.hom.base x)
      = comap (((isoStalkRingEquiv e x).symm.toRingHom).comp
          (ringStalkMap e.hom x).hom')
        (Y.val (ConcreteCategory.hom e.hom.base x))
    rw [hcomp]
    exact (congr_fun comap_id _).symm

end ValuationSpectrum

end
