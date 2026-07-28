/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».SpaVIso
import «Adic spaces».VRestrict

/-!
# Adic spaces (Wedhorn Definition 8.22)

An adic space is an object `X` of Wedhorn's category `𝒱` such that every point
has an open neighbourhood `U` for which `X|_U` is **isomorphic in `𝒱`** to the
adic spectrum of a sheafy affinoid pair.  The isomorphism carries the structure
sheaf and the stalk valuations, not merely the topology — that is exactly what
separates this from the carrier-level `AdicSpacePresentation`.

* `AffinoidVChart` — a sheafy affinoid pair (`AffinoidAdicPresentation`, i.e. NO
  Tate and NO noetherian hypothesis) together with the stalk package that makes
  its `Spa` an object of `𝒱`;
* `AffinoidVChart.toVObj`, `AffinoidVChart.ofTate` — the chart's `𝒱`-object, and
  the strongly-noetherian Tate charts that P5-2 supplies;
* `IsAdicSpace` — Definition 8.22.
-/

open CategoryTheory TopologicalSpace Opposite

noncomputable section

universe u

namespace ValuationSpectrum

/-- **An affinoid chart of `𝒱`** (Wedhorn Definition 8.22): a *sheafy affinoid
pair* — no Tate and no noetherian hypothesis — together with the stalk package
that makes `Spa(A, A⁺)` an object of `𝒱`.

Wedhorn proves the stalk package (local stalks, stalk valuation supported at the
maximal ideal) for every affinoid pair; in this library it is currently available
by the Tate route (`rationalShrink_tate`), so it is carried here as data rather
than derived. That keeps `IsAdicSpace` faithful to 8.22 instead of silently
restricting the charts to the strongly-noetherian Tate case. -/
structure AffinoidVChart extends AffinoidAdicPresentation.{u} where
  /-- The stalks of the structure presheaf are local rings. -/
  isLocalRing_stalk : ∀ v : ↥(Spa Ring (ringPlus Ring)),
    IsLocalRing (ToType ((spaRingPresheaf Ring).stalk v))
  /-- The stalk valuation is supported at the maximal ideal. -/
  val_supp : ∀ v : ↥(Spa Ring (ringPlus Ring)),
    (stalkValue v).supp = @IsLocalRing.maximalIdeal _ _ (isLocalRing_stalk v)

namespace AffinoidVChart

variable (X : AffinoidVChart.{u})

/-- **The `𝒱`-object of an affinoid chart**: `Spa(A, A⁺)` with its structure
presheaf, stalk package and sheaf condition. -/
noncomputable def toVObj : VObj.{u} where
  toPresheafedSpace := SpaVIso.spaSpace (A := X.Ring)
  isLocalRing_stalk := X.isLocalRing_stalk
  val := fun v => stalkValue v
  val_supp := X.val_supp
  isSheafTopRings :=
    (structurePresheaf_isSheafOfTopologicalRings_iff X.Ring).mpr X.sheafy

end AffinoidVChart


/-- **Every sheafy strongly-noetherian complete Tate ring is an affinoid chart** —
the `spaVObjTate` package of P5-2, repackaged as a chart of Definition 8.22. -/
noncomputable def AffinoidVChart.ofTate (A : Type u) [CommRing A]
    [TopologicalSpace A] [PlusSubring A] [IsTateRing A] [T2Space A]
    [NonarchimedeanRing A] [IsRingOfIntegralElements (A⁺ : Subring A)]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    [IsStronglyNoetherian A] : AffinoidVChart.{u} :=
  letI : DecidableEq A := Classical.decEq A
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  haveI : IsNoetherianRing A := IsStronglyNoetherian.isNoetherianRing A
  haveI := hasLocLiftPowerBounded_faithful (A := A)
  haveI : IsSheafy A := isSheafy_of_stronglyNoetherian_828b
  { Ring := A
    sheafy := isLimitSheaf_of_isSheafy
    isLocalRing_stalk := fun v => isLocalRing_stalk_of_shrink (stalkShrink_tate v)
    val_supp := fun v => (maximalIdeal_stalk_eq_supp (stalkShrink_tate v)).symm }

/-- **An adic space** (Wedhorn Definition 8.22): an object of `𝒱` every point of
which has an open neighbourhood `U` with `X|_U` isomorphic **in `𝒱`** to the
adic spectrum of a sheafy affinoid pair.

The isomorphism is one of `𝒱`, so it carries the structure sheaf and the stalk
valuations, not merely the topology — that is what distinguishes this from the
purely topological `AdicSpacePresentation`. -/
def IsAdicSpace (X : VObj.{u}) : Prop :=
  ∀ x : ↥(X.toTopCat), ∃ (U : Opens ↥(X.toTopCat)) (_ : x ∈ U)
    (C : AffinoidVChart.{u}), Nonempty (X.restrictOpen U ≅ C.toVObj)


/-! ### Consistency with the carrier-level definition -/

/-- The underlying continuous map of an isomorphism of `𝒱`-objects, as an
isomorphism of topological spaces. -/
noncomputable def VObj.baseIso {X Y : VObj.{u}} (e : X ≅ Y) :
    X.toVPreObj.toPresheafedSpace.carrier
      ≅ Y.toVPreObj.toPresheafedSpace.carrier where
  hom := e.hom.toHom.base
  inv := e.inv.toHom.base
  hom_inv_id :=
    congrArg (fun f : VPreHom X.toVPreObj X.toVPreObj => f.toHom.base)
      e.hom_inv_id
  inv_hom_id :=
    congrArg (fun f : VPreHom Y.toVPreObj Y.toVPreObj => f.toHom.base)
      e.inv_hom_id

/-- **An isomorphism of `𝒱`-objects is in particular a homeomorphism of
carriers.** -/
noncomputable def VObj.baseHomeo {X Y : VObj.{u}} (e : X ≅ Y) :
    ↥(X.toTopCat) ≃ₜ ↥(Y.toTopCat) :=
  TopCat.homeoOfIso (VObj.baseIso e)

/-- **The `𝒱`-level definition refines the carrier-level one**: an adic space in
the sense of Wedhorn 8.22 is in particular locally homeomorphic to the adic
spectra of sheafy affinoid pairs — the condition recorded by
`AdicSpacePresentation`. -/
theorem exists_homeo_of_isAdicSpace {X : VObj.{u}} (h : IsAdicSpace X)
    (x : ↥(X.toTopCat)) :
    ∃ (U : Opens ↥(X.toTopCat)) (_ : x ∈ U) (C : AffinoidVChart.{u}),
      Nonempty (↥U ≃ₜ ↥(Spa C.Ring (ringPlus C.Ring))) := by
  obtain ⟨U, hxU, C, ⟨e⟩⟩ := h x
  exact ⟨U, hxU, C, ⟨VObj.baseHomeo e⟩⟩


/-- **Every adic space in the sense of Wedhorn 8.22 has an underlying
carrier-level presentation.** This is the formal statement that the `𝒱`-level
definition refines `AdicSpacePresentation`, whose docstring recorded that it
"does not itself implement Wedhorn Definition 8.22". -/
noncomputable def AdicSpacePresentation.ofIsAdicSpace {X : VObj.{u}}
    (h : IsAdicSpace X) : AdicSpacePresentation.{u} where
  carrier := ↥(X.toTopCat)
  isLocallyAffinoid := fun x => by
    obtain ⟨U, hxU, C, ⟨e⟩⟩ := exists_homeo_of_isAdicSpace h x
    exact ⟨U, hxU, C.toAffinoidAdicPresentation, ⟨e⟩⟩

end ValuationSpectrum

end
