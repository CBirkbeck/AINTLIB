/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI contributors
-/
import Mathlib.Geometry.RingedSpace.OpenImmersion

import «Adic spaces».AdicMorphismsCore
import «Adic spaces».StructureSheaf

/-!
# Restriction and corestriction in Wedhorn's category `𝒱`

The `X|_U` operation of Wedhorn Definition 8.22 and the morphism-level toolkit
built on it: restricting a valued (pre)sheafed space to an open subset,
corestricting a morphism onto an open containing its range, and the transport
lemmas that turn a presheafed-space isomorphism into a `𝒱`-isomorphism.

## Main definitions

* `VPreObj.restrictOpen`, `VObj.restrictOpen`: restrict along the open inclusion,
  transporting the stalk package (locality, valuation, support) along mathlib's
  `restrictStalkIso`, and — for `VObj` — the sheaf-of-topological-rings condition.
* `VPreObj.ofIso`, `VPreHom.ofIso`: transport of a `𝒱^pre`-structure along an
  isomorphism of presheafed spaces.
* `liftToRestrict`, `VPreHom.corestrict`: corestriction of a morphism whose range
  lands in an open, at the presheafed-space and `𝒱^pre` levels.
* `VPreHom.inv`, `VPreHom.asIso`: the inverse of an invertible `𝒱^pre`-morphism.

## Main results

* `VPreHom.isIso_of_isIso_toHom`: the forgetful functor to presheafed spaces
  reflects isomorphisms, so a `𝒱^pre`-morphism is invertible as soon as its
  underlying morphism is.
* `restrictRestrictIso`, `VPreObj.restrictRestrictIso`, `restrictIsoOfIso`,
  `VPreHom.restrictIso`: restriction is transitive and transports along
  isomorphisms, at both levels.
* `VPreObj.isoRestrictOfOpenImmersion`: **the chart step** — an open immersion
  between `𝒱^pre`-objects that respects the stalk valuations exhibits its source
  as the restriction of its target to its range. Locality of the stalk maps and
  invertibility both come for free.
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

/-- The inclusion of an open subset is an open embedding — the input mathlib's
`PresheafedSpace.restrict` needs. -/
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

/-- The stalks of the restriction are local. -/
theorem isLocalRing_restrictStalk (x : ↥U) :
    IsLocalRing (ToType ((restrictSpace X U).ringStalk x)) := by
  have : IsLocalRing (ToType (X.toPresheafedSpace.ringStalk
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
    have hAmb : IsLocalRing (ToType (X.toPresheafedSpace.ringStalk
        (restrictPoint X U x))) := X.isLocalRing_stalk (restrictPoint X U x)
    rw [supp_comap]
    rw [show (X.val (restrictPoint X U x)).supp
        = @IsLocalRing.maximalIdeal _ _ hAmb from X.val_supp _]
    exact @IsLocalRing.maximalIdeal_comap _ _ _ (isLocalRing_restrictStalk X U x)
      _ hAmb ((restrictRingStalkEquiv X U x : _ →+* _))
      ⟨fun a ha => (isLocalHom_equiv (restrictRingStalkEquiv X U x)).map_nonunit a ha⟩

/-! ### The open-image functor bookkeeping -/

/-- The open-image functor of the inclusion. -/
def restrictOpenFunctor : Opens ↥U ⥤ Opens ↥(X.toTopCat) :=
  (opensIncl_isOpenEmbedding X U).isOpenMap.functor

/-- The open-image functor preserves suprema. Needed so that a cover of an open of
`U` maps to a cover of the corresponding open of `X`. -/
theorem restrictOpenFunctor_iSup {ι : Type*} (W : ι → Opens ↥U) :
    (restrictOpenFunctor X U).obj (iSup W)
      = ⨆ i, (restrictOpenFunctor X U).obj (W i) := by
  refine Opens.ext ?_
  show (opensIncl X U) '' ((iSup W : Opens ↥U) : Set ↥U) = _
  rw [Opens.coe_iSup, Set.image_iUnion, Opens.coe_iSup]
  rfl

/-- The open-image functor preserves binary intersections — the overlap half of the
sheaf condition transported through the restriction. -/
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
  have : IsIso (CompleteTopCommRingCat.forgetToCommRingCat.mapPresheaf.map α) :=
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
    have : IsLocalRing (ToType (Y.toPresheafedSpace.ringStalk
        (ConcreteCategory.hom e.hom.base x))) := Y.isLocalRing_stalk _
    exact (isoStalkRingEquiv e x).isLocalRing
  val := fun x => comap ((isoStalkRingEquiv e x).symm : _ →+* _)
    (Y.val (ConcreteCategory.hom e.hom.base x))
  val_supp := fun x => by
    have hY : IsLocalRing (ToType (Y.toPresheafedSpace.ringStalk
        (ConcreteCategory.hom e.hom.base x))) := Y.isLocalRing_stalk _
    have hX : IsLocalRing (ToType (X.ringStalk x)) := by
      exact (isoStalkRingEquiv e x).isLocalRing
    rw [supp_comap]
    rw [show (Y.val (ConcreteCategory.hom e.hom.base x)).supp
        = @IsLocalRing.maximalIdeal _ _ hY from Y.val_supp _]
    exact @IsLocalRing.maximalIdeal_comap _ _ _ hX
      _ hY (((isoStalkRingEquiv e x).symm : _ →+* _))
      ⟨fun a ha => (isLocalHom_equiv (isoStalkRingEquiv e x).symm).map_nonunit a ha⟩

/-- The isomorphism is a morphism of `𝒱^pre` onto the transported
structure. -/
noncomputable def VPreHom.ofIso {X : TopRingPresheafedSpace.{u}} {Y : VPreObj.{u}}
    (e : X ≅ Y.toPresheafedSpace) :
    VPreHom (VPreObj.ofIso e) Y where
  toHom := e.hom
  isLocalHom_stalkMap := fun x => by
    have hY : IsLocalRing (ToType (Y.toPresheafedSpace.ringStalk
        (ConcreteCategory.hom e.hom.base x))) := Y.isLocalRing_stalk _
    have hX : IsLocalRing (ToType (X.ringStalk x)) :=
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

/-! ### Corestriction of a morphism to an open containing its range -/

section Corestrict

variable {Z X : TopRingPresheafedSpace.{u}} (f : Z ⟶ X)
  (U : Opens ↥(X.carrier))
  (hrange : ∀ z : ↥(Z.carrier), (ConcreteCategory.hom f.base) z ∈ U)

/-- The corestriction of the base map to an open containing its range. -/
def corestrictBase : Z.carrier ⟶ TopCat.of ↥U :=
  TopCat.ofHom ⟨fun z => ⟨(ConcreteCategory.hom f.base) z, hrange z⟩,
    Continuous.subtype_mk (ConcreteCategory.hom f.base).continuous _⟩

/-- The image of an open of `U` in the ambient space. -/
def imgOfOpen (V : Opens ↥U) : Opens ↥(X.carrier) where
  carrier := Subtype.val '' (V : Set ↥U)
  is_open' := (U.2.isOpenEmbedding_subtypeVal).isOpenMap _ V.2

/-- The preimage of an open of `U` agrees with the preimage of its image. -/
theorem corestrict_preimage_eq (V : Opens ↥U) :
    (Opens.map (corestrictBase f U hrange)).obj V
      = (Opens.map f.base).obj (imgOfOpen U V) := by
  refine Opens.ext (Set.ext fun z => ?_)
  constructor
  · intro hz
    exact ⟨⟨_, hrange z⟩, hz, rfl⟩
  · rintro ⟨y, hy, hyeq⟩
    have hy' : y = ⟨(ConcreteCategory.hom f.base) z, hrange z⟩ := Subtype.ext hyeq
    show (⟨(ConcreteCategory.hom f.base) z, hrange z⟩ : ↥U) ∈ V
    exact hy' ▸ hy

/-- The open inclusion of `U` as a `TopCat`-morphism. -/
def openIncl : TopCat.of ↥U ⟶ X.carrier :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The open inclusion is an open embedding. Stated at the `.carrier` spelling (not
`.toTopCat`), which is what mathlib's `IsOpenImmersion.ofRestrict` instance needs:
typeclass unification is reducible-only and `toTopCat` is a plain `def`. -/
theorem openIncl_isOpenEmbedding :
    Topology.IsOpenEmbedding (openIncl (X := X) U) :=
  U.2.isOpenEmbedding_subtypeVal

/-- The image functor of the open inclusion. -/
def imgFunctor : Opens ↥U ⥤ Opens ↥(X.carrier) :=
  (openIncl_isOpenEmbedding U).isOpenMap.functor

/-- The image functor computes the set-image open, definitionally. -/
theorem imgFunctor_obj (V : Opens ↥U) : (imgFunctor U).obj V = imgOfOpen U V := rfl

/-- The corestricted preimage functor factors through the image functor. -/
theorem corestrict_functor_eq :
    (imgFunctor U) ⋙ (Opens.map f.base)
      = Opens.map (corestrictBase f U hrange) := by
  refine CategoryTheory.Functor.ext
    (fun V => (corestrict_preimage_eq f U hrange V).symm) ?_
  intro V V' i
  exact Subsingleton.elim _ _

/-- **The corestriction of a morphism to an open containing its range.** -/
def corestrictHom : Z ⟶ X.restrict (openIncl_isOpenEmbedding U) where
  base := corestrictBase f U hrange
  c := Functor.whiskerLeft (imgFunctor U).op f.c ≫
    eqToHom (congrArg (fun G : Opens ↥U ⥤ Opens ↥(Z.carrier) => G.op ⋙ Z.presheaf)
      (corestrict_functor_eq f U hrange))

/-- The restriction stalk comparison at the raw presheafed-space level. -/
noncomputable def restrictRingStalkIsoRaw (x : ↥U) :
    TopRingPresheafedSpace.ringStalk (X.restrict (openIncl_isOpenEmbedding U)) x
      ≅ TopRingPresheafedSpace.ringStalk X
        (ConcreteCategory.hom (openIncl U) x) :=
  AlgebraicGeometry.PresheafedSpace.restrictStalkIso
    (CompleteTopCommRingCat.forgetToCommRingCat.mapPresheaf.obj X)
    (openIncl_isOpenEmbedding U) x

/-- The range of the open inclusion is `U`. -/
theorem range_openIncl :
    Set.range (ConcreteCategory.hom (openIncl (X := X) U))
      = (U : Set ↥(X.carrier)) :=
  Subtype.range_val

/-- **The corestriction of a morphism into an open containing its range**,
via mathlib's `IsOpenImmersion.lift` at the restriction inclusion. -/
noncomputable def liftToRestrict
    (hr : Set.range (ConcreteCategory.hom f.base) ⊆ (U : Set ↥(X.carrier))) :
    Z ⟶ X.restrict (openIncl_isOpenEmbedding U) :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift
    (X.ofRestrict (openIncl_isOpenEmbedding U)) f
    (by
      have h : Set.range (ConcreteCategory.hom
          (X.ofRestrict (openIncl_isOpenEmbedding U)).base)
          = (U : Set ↥(X.carrier)) := range_openIncl U
      rw [h]
      exact hr)

/-- The lift factors the original morphism. -/
theorem liftToRestrict_fac
    (hr : Set.range (ConcreteCategory.hom f.base) ⊆ (U : Set ↥(X.carrier))) :
    liftToRestrict f U hr ≫ X.ofRestrict (openIncl_isOpenEmbedding U) = f :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac _ _ _

/-- The base of the lift, as a point of `U`. -/
theorem liftToRestrict_base
    (hr : Set.range (ConcreteCategory.hom f.base) ⊆ (U : Set ↥(X.carrier)))
    (z : ↥(Z.carrier)) :
    ConcreteCategory.hom (openIncl U)
        (ConcreteCategory.hom (liftToRestrict f U hr).base z)
      = ConcreteCategory.hom f.base z := by
  have h := congrArg (fun g : Z ⟶ X => ConcreteCategory.hom g.base z)
    (liftToRestrict_fac f U hr)
  exact h

/-- **The lift's stalk map factors the original one through the restriction
stalk comparison.** The `eqToHom` is forced: the two source stalks sit at
propositionally-equal points of `X`. -/
theorem ringStalkMap_liftToRestrict
    (hr : Set.range (ConcreteCategory.hom f.base) ⊆ (U : Set ↥(X.carrier)))
    (z : ↥(Z.carrier)) :
    ringStalkMap f z
      = eqToHom (congrArg (TopRingPresheafedSpace.ringPresheaf X).stalk
          (congrArg (fun g : Z ⟶ X => ConcreteCategory.hom g.base z)
            (liftToRestrict_fac f U hr).symm)) ≫
        ringStalkMap (liftToRestrict f U hr ≫
          X.ofRestrict (openIncl_isOpenEmbedding U)) z := by
  exact AlgebraicGeometry.PresheafedSpace.stalkMap.congr_hom
    (CompleteTopCommRingCat.forgetToCommRingCat.mapPresheaf.map f)
    (CompleteTopCommRingCat.forgetToCommRingCat.mapPresheaf.map
      (liftToRestrict f U hr ≫ X.ofRestrict (openIncl_isOpenEmbedding U)))
    (congrArg CompleteTopCommRingCat.forgetToCommRingCat.mapPresheaf.map
      (liftToRestrict_fac f U hr).symm) z

/-- The stalk map of the restriction inclusion is the inverse of the
restriction stalk comparison (mathlib, in our `ringStalkMap` spelling). -/
theorem ringStalkMap_ofRestrict {X : TopRingPresheafedSpace.{u}}
    (U : Opens ↥(X.carrier)) (y : ↥U) :
    ringStalkMap (X.ofRestrict (openIncl_isOpenEmbedding U)) y
      = (restrictRingStalkIsoRaw U y).inv :=
  (AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict
    (CompleteTopCommRingCat.forgetToCommRingCat.mapPresheaf.obj X)
    (openIncl_isOpenEmbedding U) y).symm


section RestrictHom

variable {X : VPreObj.{u}} (U : Opens ↥(X.toTopCat))

/-- **The valuation route to locality**: a ring hom whose source valuation is
the pullback of the target's is a local homomorphism, when both supports are
the maximal ideals. -/
theorem isLocalHom_of_val_comap {R S : Type*} [CommRing R] [CommRing S]
    (instR : IsLocalRing R) (instS : IsLocalRing S) (φ : R →+* S)
    (vR : Spv R) (vS : Spv S) (hval : vR = comap φ vS)
    (hR : vR.supp = @IsLocalRing.maximalIdeal _ _ instR)
    (hS : vS.supp = @IsLocalRing.maximalIdeal _ _ instS) :
    IsLocalHom φ := by
  refine ⟨fun a ha => ?_⟩
  have h1 : φ a ∉ vS.supp := by
    rw [hS]
    exact fun hmem => (mem_nonunits_iff.mp
      ((@IsLocalRing.mem_maximalIdeal _ _ instS _).mp hmem)) ha
  have hchain : vR.supp = (vS.supp).comap φ := by
    rw [hval]; exact supp_comap _ _
  have h2 : a ∉ vR.supp := fun h => h1 (Ideal.mem_comap.mp (hchain ▸ h))
  by_contra hnu
  refine h2 ?_
  rw [hR]
  exact (@IsLocalRing.mem_maximalIdeal _ _ instR _).mpr (mem_nonunits_iff.mpr hnu)

/-- The restriction comparison and the inclusion's stalk map are mutually
inverse, elementwise. -/
theorem restrictRingStalkEquiv_ringStalkMap_ofRestrict (y : ↥U)
    (t : ToType (X.toPresheafedSpace.ringStalk (restrictPoint X U y))) :
    (restrictRingStalkEquiv X U y)
        ((ringStalkMap (X.toPresheafedSpace.ofRestrict
          (opensIncl_isOpenEmbedding X U)) y).hom' t) = t := by
  have h1 : (ringStalkMap (X.toPresheafedSpace.ofRestrict
      (opensIncl_isOpenEmbedding X U)) y) = (restrictRingStalkIso X U y).inv :=
    (AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict
      (restrictRingAmbient X) (opensIncl_isOpenEmbedding X U) y).symm
  rw [h1]
  exact congrFun (congrArg (fun m : _ ⟶ _ => (CommRingCat.Hom.hom m).toFun)
    ((restrictRingStalkIso X U y).inv_hom_id)) t

/-- **The restriction inclusion is a `𝒱^pre`-morphism.** Its stalk maps are
the restriction comparisons, so both fields hold by construction. -/
noncomputable def VPreHom.ofRestrictOpen : VPreHom (X.restrictOpen U) X where
  toHom := X.toPresheafedSpace.ofRestrict (opensIncl_isOpenEmbedding X U)
  isLocalHom_stalkMap := fun y => by
    have hX : IsLocalRing (ToType (X.toPresheafedSpace.ringStalk
        (restrictPoint X U y))) := X.isLocalRing_stalk _
    have hR : IsLocalRing (ToType ((restrictSpace X U).ringStalk y)) :=
      isLocalRing_restrictStalk X U y
    refine @IsLocalHom.of_surjective _ _ _ _ hR.toNontrivial hX _ ?_
    intro c
    refine ⟨restrictRingStalkEquiv X U y c, ?_⟩
    have h := restrictRingStalkEquiv_ringStalkMap_ofRestrict U y
    have hinj : Function.Injective (restrictRingStalkEquiv X U y) :=
      (restrictRingStalkEquiv X U y).injective
    exact hinj (h (restrictRingStalkEquiv X U y c))
  val_compat := fun y => by
    refine (ValuationSpectrum.ext (funext₂ fun a b => propext ?_)).symm
    show ((X.restrictOpen U).val y).vle
        ((ringStalkMap (X.toPresheafedSpace.ofRestrict
          (opensIncl_isOpenEmbedding X U)) y).hom' a)
        ((ringStalkMap (X.toPresheafedSpace.ofRestrict
          (opensIncl_isOpenEmbedding X U)) y).hom' b)
      ↔ (X.val (restrictPoint X U y)).vle a b
    show (X.val (restrictPoint X U y)).vle
        ((restrictRingStalkEquiv X U y)
          ((ringStalkMap (X.toPresheafedSpace.ofRestrict
            (opensIncl_isOpenEmbedding X U)) y).hom' a))
        ((restrictRingStalkEquiv X U y)
          ((ringStalkMap (X.toPresheafedSpace.ofRestrict
            (opensIncl_isOpenEmbedding X U)) y).hom' b))
      ↔ (X.val (restrictPoint X U y)).vle a b
    rw [restrictRingStalkEquiv_ringStalkMap_ofRestrict U y a,
      restrictRingStalkEquiv_ringStalkMap_ofRestrict U y b]

end RestrictHom

end Corestrict

/-! ### Corestriction of `𝒱^pre`-morphisms

A morphism of `𝒱^pre` whose range lands in an open `U` of the target
corestricts to a morphism into `X|_U`.  Both structure fields come from a
single valuation identity: the stalk maps factor through the (isomorphic)
inclusion stalk maps, and locality is then read off the valuation. -/

section CorestrictV

/-! ### Restriction transitivity (P5-RT) -/

/-- The range of the double inclusion `↥W → ↥U → α` of an open `W` of an open
`U`, as the range of the inclusion of the image `Subtype.val '' W`. -/
theorem range_val_val {α : Type u} (U : Set α) (W : Set ↥U) :
    Set.range (fun w : ↥W => ((w : ↥U) : α))
      = Set.range (Subtype.val : ↥(Subtype.val '' W : Set α) → α) := by
  rw [Subtype.range_coe, show (fun w : ↥W => ((w : ↥U) : α))
        = (Subtype.val : ↥U → α) ∘ (Subtype.val : ↥W → ↥U) from rfl,
    Set.range_comp, Subtype.range_coe]

/-- The composite inclusion of a double restriction has the same range as the
inclusion of the image open. -/
theorem range_openIncl_comp {X : TopRingPresheafedSpace.{u}}
    (U : Opens ↥(X.carrier)) (W : Opens ↥U) :
    Set.range (ConcreteCategory.hom
        ((X.restrict (openIncl_isOpenEmbedding U)).ofRestrict
            (openIncl_isOpenEmbedding W) ≫
          X.ofRestrict (openIncl_isOpenEmbedding U)).base)
      = Set.range (ConcreteCategory.hom
          (X.ofRestrict (openIncl_isOpenEmbedding (imgOfOpen U W))).base) :=
  range_val_val (α := ↥(X.carrier)) (U : Set ↥(X.carrier)) (W : Set ↥U)

/-- The range of `g` restricted to a subset, as the range of the inclusion of
the image. -/
theorem range_comp_val {α β : Type u} (g : α → β) (U : Set α) :
    Set.range (fun w : ↥U => g (w : α))
      = Set.range (Subtype.val : ↥(g '' U) → β) := by
  rw [Subtype.range_coe, show (fun w : ↥U => g (w : α))
      = g ∘ (Subtype.val : ↥U → α) from rfl, Set.range_comp, Subtype.range_coe]

/-- The image of an open under an isomorphism of presheafed spaces. -/
def imgOfIso {X Y : TopRingPresheafedSpace.{u}} (e : X ≅ Y)
    (U : Opens ↥(X.carrier)) : Opens ↥(Y.carrier) where
  carrier := (ConcreteCategory.hom e.hom.base) '' (U : Set ↥(X.carrier))
  is_open' :=
    have := AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso e
    (AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open
      (f := e.hom)).isOpenMap _ U.2

/-- **Restriction transports along an isomorphism.** -/
noncomputable def restrictIsoOfIso {X Y : TopRingPresheafedSpace.{u}} (e : X ≅ Y)
    (U : Opens ↥(X.carrier)) :
    X.restrict (openIncl_isOpenEmbedding U)
      ≅ Y.restrict (openIncl_isOpenEmbedding (imgOfIso e U)) :=
  have := AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso e
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    (X.ofRestrict (openIncl_isOpenEmbedding U) ≫ e.hom)
    (Y.ofRestrict (openIncl_isOpenEmbedding (imgOfIso e U)))
    (range_comp_val (α := ↥(X.carrier)) (β := ↥(Y.carrier))
      (ConcreteCategory.hom e.hom.base) (U : Set ↥(X.carrier)))

/-- **Restriction transitivity** (P5-RT): restricting twice is restricting to
the image open. -/
noncomputable def restrictRestrictIso {X : TopRingPresheafedSpace.{u}}
    (U : Opens ↥(X.carrier)) (W : Opens ↥U) :
    (X.restrict (openIncl_isOpenEmbedding U)).restrict
        (openIncl_isOpenEmbedding W)
      ≅ X.restrict (openIncl_isOpenEmbedding (imgOfOpen U W)) :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    ((X.restrict (openIncl_isOpenEmbedding U)).ofRestrict
        (openIncl_isOpenEmbedding W) ≫
      X.ofRestrict (openIncl_isOpenEmbedding U))
    (X.ofRestrict (openIncl_isOpenEmbedding (imgOfOpen U W)))
    (range_openIncl_comp U W)


/-- **`𝒱` is a full subcategory of `𝒱^pre`**: an isomorphism of the underlying
`𝒱^pre`-objects is an isomorphism of `𝒱`-objects. -/
def VObj.isoOfVPreIso {X Y : VObj.{u}} (e : X.toVPreObj ≅ Y.toVPreObj) :
    X ≅ Y where
  hom := e.hom
  inv := e.inv
  hom_inv_id := VPreHom.ext
    (congrArg (fun f : VPreHom X.toVPreObj X.toVPreObj => f.toHom) e.hom_inv_id)
  inv_hom_id := VPreHom.ext
    (congrArg (fun f : VPreHom Y.toVPreObj Y.toVPreObj => f.toHom) e.inv_hom_id)


/-- Composition of `𝒱^pre`-morphisms. This is exactly the composition of the
`Category VPreObj` instance, named because the `⟶` spelling does not always
elaborate when the expected type is written as `VPreHom _ _`. -/
noncomputable abbrev VPreHom.comp {X Y Z : VPreObj.{u}} (f : VPreHom X Y)
    (g : VPreHom Y Z) : VPreHom X Z :=
  show X ⟶ Z from (f : X ⟶ Y) ≫ (g : Y ⟶ Z)

/-- A `𝒱^pre`-morphism whose underlying morphism of presheafed spaces is
invertible is an isomorphism of `𝒱^pre`. -/
noncomputable def VPreHom.isoOfIsIso {X Y : VPreObj.{u}} (f : VPreHom X Y)
    [IsIso f.toHom] (ginv : VPreHom Y X)
    (hg : ginv.toHom = CategoryTheory.inv f.toHom) : X ≅ Y where
  hom := f
  inv := ginv
  hom_inv_id := VPreHom.ext (by rw [show (f.comp ginv).toHom
    = f.toHom ≫ ginv.toHom from rfl, hg, IsIso.hom_inv_id]; rfl)
  inv_hom_id := VPreHom.ext (by rw [show (ginv.comp f).toHom
    = ginv.toHom ≫ f.toHom from rfl, hg, IsIso.inv_hom_id]; rfl)

/-! ### `𝒱^pre` reflects isomorphisms (P5-6c) -/

section Reflects

variable {X Y : VPreObj.{u}} (f : VPreHom X Y) [IsIso f.toHom]

/-- An endomorphism of a `𝒱^pre`-object that is the identity satisfies the
valuation-compatibility condition. -/
theorem val_compat_of_eq_id (Z : VPreObj.{u})
    (g : Z.toPresheafedSpace ⟶ Z.toPresheafedSpace)
    (hg : g = 𝟙 Z.toPresheafedSpace) (z : Z.toPresheafedSpace) :
    Z.val (ConcreteCategory.hom g.base z)
      = comap (ringStalkMap g z).hom' (Z.val z) := by
  subst hg
  simp only [ringStalkMap_id]
  exact (congr_fun ValuationSpectrum.comap_id (Z.val z)).symm

/-- The ring stalk map of an endomorphism equal to the identity is surjective. -/
theorem surjective_ringStalkMap_of_eq_id (Z : VPreObj.{u})
    (g : Z.toPresheafedSpace ⟶ Z.toPresheafedSpace)
    (hg : g = 𝟙 Z.toPresheafedSpace) (z : Z.toPresheafedSpace) :
    Function.Surjective (ringStalkMap g z).hom' := by
  subst hg
  rw [ringStalkMap_id]
  exact Function.surjective_id

omit [IsIso f.toHom] in
/-- **Valuation compatibility of a two-sided inverse.** -/
theorem val_compat_of_inverse (g : Y.toPresheafedSpace ⟶ X.toPresheafedSpace)
    (hgf : g ≫ f.toHom = 𝟙 Y.toPresheafedSpace)
    (hfg : f.toHom ≫ g = 𝟙 X.toPresheafedSpace) (y : Y.toPresheafedSpace) :
    X.val (ConcreteCategory.hom g.base y)
      = comap (ringStalkMap g y).hom' (Y.val y) := by
  have hsurj : Function.Surjective
      (ringStalkMap f.toHom (ConcreteCategory.hom g.base y)).hom' := by
    have h := surjective_ringStalkMap_of_eq_id X (f.toHom ≫ g) hfg
      (ConcreteCategory.hom g.base y)
    rw [ringStalkMap_comp] at h
    have h2 : Function.Surjective
        ((ringStalkMap f.toHom (ConcreteCategory.hom g.base y)).hom' ∘
          (ringStalkMap g (ConcreteCategory.hom f.toHom.base
            (ConcreteCategory.hom g.base y))).hom') := h
    exact h2.of_comp
  refine comap_injective hsurj ?_
  have e1 : comap (ringStalkMap f.toHom (ConcreteCategory.hom g.base y)).hom'
        (X.val (ConcreteCategory.hom g.base y))
      = Y.val (ConcreteCategory.hom f.toHom.base (ConcreteCategory.hom g.base y)) :=
    (f.val_compat _).symm
  have e2 : comap ((ringStalkMap g y).hom'.comp
        (ringStalkMap f.toHom (ConcreteCategory.hom g.base y)).hom') (Y.val y)
      = comap (ringStalkMap f.toHom (ConcreteCategory.hom g.base y)).hom'
          (comap (ringStalkMap g y).hom' (Y.val y)) :=
    congr_fun (comap_comp _ _) (Y.val y)
  have e3 : (ringStalkMap (g ≫ f.toHom) y).hom'
      = (ringStalkMap g y).hom'.comp
          (ringStalkMap f.toHom (ConcreteCategory.hom g.base y)).hom' := by
    rw [ringStalkMap_comp]
    rfl
  have e4 : Y.val (ConcreteCategory.hom (g ≫ f.toHom).base y)
      = comap (ringStalkMap (g ≫ f.toHom) y).hom' (Y.val y) :=
    val_compat_of_eq_id Y (g ≫ f.toHom) hgf y
  exact e1.trans (e4.trans ((congrArg (fun ρ => comap ρ (Y.val y)) e3).trans e2))

/-- **The inverse of an invertible `𝒱^pre`-morphism is a `𝒱^pre`-morphism.** -/
noncomputable def VPreHom.inv : VPreHom Y X where
  toHom := CategoryTheory.inv f.toHom
  isLocalHom_stalkMap := fun y =>
    isLocalHom_of_val_comap (X.isLocalRing_stalk _) (Y.isLocalRing_stalk y) _ _ _
      (val_compat_of_inverse f (CategoryTheory.inv f.toHom)
        (IsIso.inv_hom_id f.toHom) (IsIso.hom_inv_id f.toHom) y)
      (X.val_supp _) (Y.val_supp y)
  val_compat := fun y =>
    val_compat_of_inverse f (CategoryTheory.inv f.toHom)
      (IsIso.inv_hom_id f.toHom) (IsIso.hom_inv_id f.toHom) y

/-- A `𝒱^pre`-morphism whose underlying morphism is invertible is an isomorphism. -/
noncomputable def VPreHom.asIso : X ≅ Y :=
  VPreHom.isoOfIsIso f (VPreHom.inv f) rfl

/-- **The forgetful functor `𝒱^pre ⥤ PresheafedSpace` reflects isomorphisms.** -/
theorem VPreHom.isIso_of_isIso_toHom : IsIso (show X ⟶ Y from f) :=
  (VPreHom.asIso f).isIso_hom

end Reflects




/-- The inclusion's stalk map is surjective — it is the inverse of the
restriction stalk comparison. -/
theorem ringStalkMap_ofRestrict_surjective {X : VPreObj.{u}}
    (U : Opens ↥(X.toTopCat)) (y : ↥U) :
    Function.Surjective
      (ringStalkMap (X.toPresheafedSpace.ofRestrict
        (opensIncl_isOpenEmbedding X U)) y).hom' := by
  intro c
  refine ⟨restrictRingStalkEquiv X U y c, ?_⟩
  exact (restrictRingStalkEquiv X U y).injective
    (restrictRingStalkEquiv_ringStalkMap_ofRestrict U y _)

variable {Z X : VPreObj.{u}} (g : VPreHom Z X)
  (U : Opens ↥(X.toPresheafedSpace.carrier))
  (hr : Set.range (ConcreteCategory.hom g.toHom.base)
    ⊆ (U : Set ↥(X.toPresheafedSpace.carrier)))

/-- **The corestricted valuation compatibility.** Rewrite `g.toHom` as
`lift ≫ ofRestrict` (so no `eqToHom` ever appears), split the stalk map, and
cancel the inclusion's stalk map, which is surjective. -/
theorem val_compat_liftToRestrict (z : ↥(Z.toTopCat)) :
    (X.restrictOpen U).val
        (ConcreteCategory.hom (liftToRestrict g.toHom U hr).base z)
      = comap (ringStalkMap (liftToRestrict g.toHom U hr) z).hom' (Z.val z) := by
  set y := ConcreteCategory.hom (liftToRestrict g.toHom U hr).base z with hy
  have hincl := (VPreHom.ofRestrictOpen (X := X) U).val_compat y
  have hg := g.val_compat z
  rw [← liftToRestrict_fac g.toHom U hr] at hg
  rw [ringStalkMap_comp (liftToRestrict g.toHom U hr)
    (X.toPresheafedSpace.ofRestrict (openIncl_isOpenEmbedding U)) z] at hg
  refine comap_injective (ringStalkMap_ofRestrict_surjective U y) ?_
  exact hincl.symm.trans hg

/-- **The corestriction of a `𝒱^pre`-morphism into an open containing its
range** — Wedhorn's `𝒱`-morphisms restrict to opens of the target. -/
noncomputable def VPreHom.corestrict : VPreHom Z (X.restrictOpen U) where
  toHom := liftToRestrict g.toHom U hr
  isLocalHom_stalkMap := fun z =>
    isLocalHom_of_val_comap
      ((X.restrictOpen U).isLocalRing_stalk _) (Z.isLocalRing_stalk z) _ _ _
      (val_compat_liftToRestrict g U hr z)
      ((X.restrictOpen U).val_supp _) (Z.val_supp z)
  val_compat := fun z => val_compat_liftToRestrict g U hr z

/-! ### Restriction of a `𝒱^pre`-isomorphism to an open

Being an adic space is a local property, which needs: an isomorphism of
`𝒱^pre`-objects restricts to an isomorphism between the restrictions to an open
and its image. -/

section RestrictIso

variable {X Y : VPreObj.{u}} (f : VPreHom X Y) [IsIso f.toHom]
  (U : Opens ↥(X.toPresheafedSpace.carrier))

/-- The image of an open under an invertible `𝒱^pre`-morphism. -/
def imgOpenOfHom : Opens ↥(Y.toPresheafedSpace.carrier) :=
  imgOfIso (asIso f.toHom) U

/-- The restricted morphism lands in the image open. -/
theorem range_restrict_comp :
    Set.range (ConcreteCategory.hom
        (((VPreHom.ofRestrictOpen (X := X) U).comp f).toHom).base)
      = ((imgOpenOfHom f U : Opens ↥(Y.toPresheafedSpace.carrier))
          : Set ↥(Y.toPresheafedSpace.carrier)) :=
  (range_comp_val (α := ↥(X.toPresheafedSpace.carrier))
    (β := ↥(Y.toPresheafedSpace.carrier))
    (ConcreteCategory.hom f.toHom.base)
    (U : Set ↥(X.toPresheafedSpace.carrier))).trans Subtype.range_coe

/-- **The restriction of an invertible `𝒱^pre`-morphism to an open**. -/
noncomputable def VPreHom.restrictHom :
    VPreHom (X.restrictOpen U) (Y.restrictOpen (imgOpenOfHom f U)) :=
  VPreHom.corestrict ((VPreHom.ofRestrictOpen (X := X) U).comp f)
    (imgOpenOfHom f U) (le_of_eq (range_restrict_comp f U))

/-- The presheafed-space isomorphism induced on the restrictions. -/
noncomputable def restrictHomIso :
    (X.restrictOpen U).toPresheafedSpace
      ≅ Y.toPresheafedSpace.restrict
          (openIncl_isOpenEmbedding (X := Y.toPresheafedSpace)
            (imgOpenOfHom f U)) :=
  have _hoi : AlgebraicGeometry.PresheafedSpace.IsOpenImmersion
      (((VPreHom.ofRestrictOpen (X := X) U).comp f).toHom) :=
    AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp
      (f := X.toPresheafedSpace.ofRestrict
        (opensIncl_isOpenEmbedding X U))
      (H := AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict
        X.toPresheafedSpace (opensIncl_isOpenEmbedding X U))
      (g := f.toHom)
      (hg := AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso
        (asIso f.toHom))
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    (f := ((VPreHom.ofRestrictOpen (X := X) U).comp f).toHom)
    (g := Y.toPresheafedSpace.ofRestrict
      (openIncl_isOpenEmbedding (X := Y.toPresheafedSpace) (imgOpenOfHom f U)))
    ((range_restrict_comp f U).trans Subtype.range_val.symm)

/-- The restricted morphism and the induced presheafed-space isomorphism have the
same underlying map — both are mathlib's `IsOpenImmersion.lift`, so this is `rfl`. -/
theorem restrictHom_toHom_eq :
    (VPreHom.restrictHom f U).toHom = (restrictHomIso f U).hom := rfl

/-- Consequence of `restrictHom_toHom_eq`: the restricted morphism is invertible. -/
theorem isIso_restrictHom_toHom : IsIso (VPreHom.restrictHom f U).toHom := by
  rw [restrictHom_toHom_eq f U]
  exact (restrictHomIso f U).isIso_hom

/-- **Restriction of a `𝒱^pre`-isomorphism to an open** — so being an adic space
is a local property. -/
noncomputable def VPreHom.restrictIso :
    X.restrictOpen U ≅ Y.restrictOpen (imgOpenOfHom f U) :=
  have := isIso_restrictHom_toHom f U
  VPreHom.asIso (VPreHom.restrictHom f U)

end RestrictIso

/-! ### Restriction transitivity in `𝒱^pre` -/

section RestrictRestrict

variable (X : VPreObj.{u}) (W : Opens ↥(X.toPresheafedSpace.carrier))
  (U : Opens ↥W)

/-- The double restriction inclusion has range the image open. -/
theorem range_double_restrict :
    Set.range (ConcreteCategory.hom
        (((VPreHom.ofRestrictOpen (X := X.restrictOpen W) U).comp
          (VPreHom.ofRestrictOpen (X := X) W)).toHom).base)
      = ((imgOfOpen W U : Opens ↥(X.toPresheafedSpace.carrier))
          : Set ↥(X.toPresheafedSpace.carrier)) :=
  (range_val_val (α := ↥(X.toPresheafedSpace.carrier))
    (W : Set ↥(X.toPresheafedSpace.carrier)) (U : Set ↥W)).trans
    Subtype.range_coe

/-- **Restriction transitivity as a `𝒱^pre`-morphism.** -/
noncomputable def restrictRestrictHom :
    VPreHom ((X.restrictOpen W).restrictOpen U) (X.restrictOpen (imgOfOpen W U)) :=
  VPreHom.corestrict ((VPreHom.ofRestrictOpen (X := X.restrictOpen W) U).comp
      (VPreHom.ofRestrictOpen (X := X) W))
    (imgOfOpen W U) (le_of_eq (range_double_restrict X W U))

/-- The induced presheafed-space isomorphism. -/
noncomputable def restrictRestrictHomIso :
    ((X.restrictOpen W).restrictOpen U).toPresheafedSpace
      ≅ X.toPresheafedSpace.restrict
          (openIncl_isOpenEmbedding (X := X.toPresheafedSpace) (imgOfOpen W U)) :=
  have _h1 : AlgebraicGeometry.PresheafedSpace.IsOpenImmersion
      (((VPreHom.ofRestrictOpen (X := X.restrictOpen W) U).comp
        (VPreHom.ofRestrictOpen (X := X) W)).toHom) :=
    AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp
      (f := (X.restrictOpen W).toPresheafedSpace.ofRestrict
        (opensIncl_isOpenEmbedding (X.restrictOpen W) U))
      (H := AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict
        (X.restrictOpen W).toPresheafedSpace
        (opensIncl_isOpenEmbedding (X.restrictOpen W) U))
      (g := X.toPresheafedSpace.ofRestrict (opensIncl_isOpenEmbedding X W))
      (hg := AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict
        X.toPresheafedSpace (opensIncl_isOpenEmbedding X W))
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    (f := ((VPreHom.ofRestrictOpen (X := X.restrictOpen W) U).comp
      (VPreHom.ofRestrictOpen (X := X) W)).toHom)
    (g := X.toPresheafedSpace.ofRestrict
      (openIncl_isOpenEmbedding (X := X.toPresheafedSpace) (imgOfOpen W U)))
    ((range_double_restrict X W U).trans Subtype.range_val.symm)

/-- The transitivity morphism and its `isoOfRangeEq` counterpart share an underlying
map (both are `IsOpenImmersion.lift`), so this is `rfl`. -/
theorem restrictRestrictHom_toHom_eq :
    (restrictRestrictHom X W U).toHom = (restrictRestrictHomIso X W U).hom := rfl

/-- Consequence of `restrictRestrictHom_toHom_eq`: the transitivity morphism is
invertible. -/
theorem isIso_restrictRestrictHom_toHom :
    IsIso (restrictRestrictHom X W U).toHom := by
  rw [restrictRestrictHom_toHom_eq X W U]
  exact (restrictRestrictHomIso X W U).isIso_hom

/-- **Restriction transitivity in `𝒱^pre`.** -/
noncomputable def VPreObj.restrictRestrictIso :
    (X.restrictOpen W).restrictOpen U ≅ X.restrictOpen (imgOfOpen W U) :=
  have := isIso_restrictRestrictHom_toHom X W U
  VPreHom.asIso (restrictRestrictHom X W U)

end RestrictRestrict

/-! ### The reusable chart step

An open immersion between `𝒱^pre`-objects that respects the stalk valuations
exhibits its source as the restriction of its target to its range.  This is the
form in which Wedhorn 8.15 is consumed: given a chart comparison that is an open
immersion of presheafed spaces plus the valuation identity, one gets a genuine
`𝒱`-isomorphism onto the corresponding open — locality of the stalk maps and
invertibility are both free. -/

section ChartStep

variable {Z X : VPreObj.{u}}
  (f : Z.toPresheafedSpace ⟶ X.toPresheafedSpace)
  (hval : ∀ z : ↥(Z.toTopCat), X.val (ConcreteCategory.hom f.base z)
    = comap (ringStalkMap f z).hom' (Z.val z))

/-- A presheafed-space morphism between `𝒱^pre`-objects that respects the stalk
valuations is a `𝒱^pre`-morphism: locality of the stalk maps is automatic. -/
noncomputable def VPreHom.ofValCompat : VPreHom Z X where
  toHom := f
  isLocalHom_stalkMap := fun z =>
    isLocalHom_of_val_comap (X.isLocalRing_stalk _) (Z.isLocalRing_stalk z)
      _ _ _ (hval z) (X.val_supp _) (Z.val_supp z)
  val_compat := hval

variable (U : Opens ↥(X.toPresheafedSpace.carrier))
  (hU : Set.range (ConcreteCategory.hom f.base)
    = ((U : Opens ↥(X.toPresheafedSpace.carrier))
        : Set ↥(X.toPresheafedSpace.carrier)))

/-- The corestriction of such a morphism onto its range. -/
noncomputable def VPreHom.corestrictOfValCompat :
    VPreHom Z (X.restrictOpen U) :=
  VPreHom.corestrict (VPreHom.ofValCompat f hval) U (le_of_eq hU)

variable [AlgebraicGeometry.PresheafedSpace.IsOpenImmersion f]

/-- The induced presheafed-space isomorphism onto the restriction. -/
noncomputable def openImmersionRestrictIso :
    Z.toPresheafedSpace
      ≅ X.toPresheafedSpace.restrict
          (openIncl_isOpenEmbedding (X := X.toPresheafedSpace) U) :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    (f := f)
    (g := X.toPresheafedSpace.ofRestrict
      (openIncl_isOpenEmbedding (X := X.toPresheafedSpace) U))
    (hU.trans Subtype.range_val.symm)

/-- The corestriction and the induced isomorphism onto the restriction share an
underlying map, so this is `rfl`. This is what makes the chart step's
invertibility free. -/
theorem corestrictOfValCompat_toHom_eq :
    (VPreHom.corestrictOfValCompat f hval U hU).toHom
      = (openImmersionRestrictIso f U hU).hom := rfl

/-- Consequence of `corestrictOfValCompat_toHom_eq`: the corestriction of a
valuation-compatible open immersion is invertible. -/
theorem isIso_corestrictOfValCompat :
    IsIso (VPreHom.corestrictOfValCompat f hval U hU).toHom := by
  rw [corestrictOfValCompat_toHom_eq f hval U hU]
  exact (openImmersionRestrictIso f U hU).isIso_hom

/-- **An open immersion between `𝒱^pre`-objects that respects the stalk
valuations exhibits its source as the restriction of its target to its range.**

This is the reusable form of the Wedhorn-8.15 chart step: given a chart
comparison that is an open immersion of presheafed spaces and satisfies the
valuation identity, one gets a genuine `𝒱`-isomorphism onto the corresponding
open, with locality of the stalk maps and invertibility both for free. -/
noncomputable def VPreObj.isoRestrictOfOpenImmersion : Z ≅ X.restrictOpen U :=
  have := isIso_corestrictOfValCompat f hval U hU
  VPreHom.asIso (VPreHom.corestrictOfValCompat f hval U hU)

end ChartStep

end CorestrictV

end ValuationSpectrum

end
